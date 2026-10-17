{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- | Package-private owner of the checked conversion facade.  The public
-- module re-exports observations; proof authority remains package-private.
module Felix.Checking.Kernel.Conversion.Checked
    ( ConversionLimit
    , ConversionPool
    , ConversionCost
    , conversionLimit
    , conversionLimitAmount
    , conversionPool
    , conversionPoolAmount
    , conversionCostAmount
    , capConversionLimit
    , debitConversionCost
    , ConversionRecoveryTyping(..)
    , ConversionDecision(..)
    , ConversionInputError(..)
    , ConversionInternalError(..)
    , ConversionFailure(..)
    , ConversionReport
    , conversionResult
    , conversionCost
    , SuccessfulConversion
    , ConversionWitnessResult(..)
    , convertibleChecked
    , betaNormalizeChecked
    , residualizeHeadChecked
    , PreparedSpine
    , PreparedSpineStep(..)
    , preparedSpineSteps
    , preparedSpineTerminal
    , prepareImplicationSpineChecked
    , witnessConversionChecked
    , eliminateSuccessfulConversion
    , replayStoredConversionChecked
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Kernel.Conversion.Pure qualified as Pure

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State.Strict (State, gets, modify', runState)
import Data.Word (Word)
import Numeric.Natural (Natural)


newtype ConversionLimit = ConversionLimit Word
    deriving stock (Show, Eq, Ord)

newtype ConversionPool = ConversionPool Word
    deriving stock (Show, Eq, Ord)

newtype ConversionCost = ConversionCost Word
    deriving stock (Show, Eq, Ord)

conversionLimit :: Word -> ConversionLimit
conversionLimit = ConversionLimit

conversionLimitAmount :: ConversionLimit -> Word
conversionLimitAmount (ConversionLimit amount) = amount

conversionPool :: Word -> ConversionPool
conversionPool = ConversionPool

conversionPoolAmount :: ConversionPool -> Word
conversionPoolAmount (ConversionPool amount) = amount

conversionCostAmount :: ConversionCost -> Word
conversionCostAmount (ConversionCost amount) = amount

capConversionLimit :: ConversionPool -> ConversionLimit -> ConversionLimit
capConversionLimit (ConversionPool pool) (ConversionLimit requested) =
    ConversionLimit (min pool requested)

debitConversionCost :: ConversionCost -> ConversionPool -> Maybe ConversionPool
debitConversionCost (ConversionCost cost) (ConversionPool pool)
    | cost <= pool = Just (ConversionPool (pool - cost))
    | otherwise = Nothing

data ConversionRecoveryTyping global = ConversionRecoveryTyping
    { conversionOperationTyping :: !(GlobalTyping global)
    , conversionDestinationTyping :: !(GlobalTyping global)
    }

type role ConversionRecoveryTyping nominal

data ConversionDecision
    = Convertible
    | NotConvertible
    deriving stock (Show, Eq, Ord)

data ConversionInputError
    = ConversionContextMismatch ![CoreType] ![CoreType]
    | ConversionRootTypeMismatch !CoreType !CoreType
    | ConversionAdmissionFailure !CoreCheckError
    deriving stock (Show, Eq)

data ConversionInternalError
    = ConversionExpectedArrow !CoreType
    | ConversionTypeFlowMismatch !CoreType !CoreType
    | ConversionBoundIndexOutOfScope !Natural !Natural
    | ConversionSemanticLevelOutOfScope !Natural !Natural
    | ConversionReflectedLevelEscaped !Natural !Natural
    | ConversionQuotedCoreRejected !CoreCheckError
    | ConversionRecoveredTypeMismatch !CoreType !CoreType
    | ConversionWitnessReplayMismatch
    | ConversionWitnessReplayCostMismatch !ConversionCost !ConversionCost
    deriving stock (Show, Eq)

data ConversionFailure
    = ConversionInputFailure !ConversionInputError
    | ConversionCheckedRecoveryFailure !CoreCheckError
    | ConversionLimitExhausted !ConversionLimit
    | ConversionInvariantFailure !ConversionInternalError
    deriving stock (Show, Eq)

data ConversionReport result = ConversionReport
    !(Either ConversionFailure result)
    !ConversionCost
    deriving stock (Show, Eq)

conversionResult
    :: ConversionReport result
    -> Either ConversionFailure result
conversionResult (ConversionReport result _cost) = result

conversionCost :: ConversionReport result -> ConversionCost
conversionCost (ConversionReport _result cost) = cost

data SuccessfulConversion global = SuccessfulConversion
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    !ConversionCost

type role SuccessfulConversion nominal

data ConversionWitnessResult global
    = WitnessNotConvertible
    | WitnessConvertible !(SuccessfulConversion global)

-- | A closed observation of one forall/implication path. Each premise retains
-- exactly its preceding binder prefix; the terminal retains the full prefix.
-- Components are independently recovered checked syntax, with no evaluator
-- state or visibility certificate. Proof attachment and replay remain fresh.
data PreparedSpine global = PreparedSpine
    ![PreparedSpineStep global]
    !(ScopedCheckedCore global)

type role PreparedSpine nominal

data PreparedSpineStep global
    = PreparedUniversal !CoreType
    | PreparedPremise !(ScopedCheckedCore global)

type role PreparedSpineStep nominal

preparedSpineSteps :: PreparedSpine global -> [PreparedSpineStep global]
preparedSpineSteps (PreparedSpine steps _terminal) = steps

preparedSpineTerminal :: PreparedSpine global -> ScopedCheckedCore global
preparedSpineTerminal (PreparedSpine _steps terminal) = terminal

data CheckedState = CheckedState
    { checkedOriginalLimit :: !ConversionLimit
    , checkedRemaining :: !Word
    }

type Checked global = ExceptT ConversionFailure (State CheckedState)

runChecked
    :: ConversionLimit
    -> Checked global result
    -> ConversionReport result
runChecked original@(ConversionLimit amount) action =
    let initial = CheckedState original amount
        (result, final) = runState (runExceptT action) initial
        cost = ConversionCost (amount - checkedRemaining final)
    in ConversionReport result cost

exhausted :: Checked global value
exhausted = do
    original <- gets checkedOriginalLimit
    throwError (ConversionLimitExhausted original)

setRemainder :: Word -> Checked global ()
setRemainder remaining =
    modify' \state -> state{checkedRemaining = remaining}

translateVoidFailure
    :: CountedCoreFailure Void
    -> Checked global value
translateVoidFailure = \case
    CountedCoreStructuralWorkExhausted -> exhausted
compareTypes
    :: CoreType
    -> CoreType
    -> Checked global Bool
compareTypes left right = do
    before <- gets checkedRemaining
    let (result, after) = countedCoreTypeIdentity before left right
    setRemainder after
    either translateVoidFailure pure result

compareContexts
    :: [CoreType]
    -> [CoreType]
    -> Checked global Bool
compareContexts left right = do
    before <- gets checkedRemaining
    let (result, after) = countedCoreTypeListIdentity before left right
    setRemainder after
    either translateVoidFailure pure result

compareCanonicalRoots
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> Checked global Bool
compareCanonicalRoots left right = do
    before <- gets checkedRemaining
    let (result, after) = countedCanonicalIdentity before left right
    setRemainder after
    either translateVoidFailure pure result

admit
    :: GlobalTyping global
    -> ScopedCheckedCore global
    -> Checked global (ScopedCheckedCore global)
admit globalTyping checked = do
    before <- gets checkedRemaining
    let (result, after) =
            countedAdmitScopedCheckedCore globalTyping before checked
    setRemainder after
    case result of
        Right admitted -> pure admitted
        Left CountedCoreStructuralWorkExhausted -> exhausted
        Left (CountedCoreOperationFailed cause) ->
            throwError
                (ConversionInputFailure
                    (ConversionAdmissionFailure cause))

requirePairCompatibility
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Checked global ()
requirePairCompatibility left right = do
    contextsMatch <- compareContexts
        (scopedCoreContext left) (scopedCoreContext right)
    unless contextsMatch
        (throwError
            (ConversionInputFailure
                (ConversionContextMismatch
                    (scopedCoreContext left)
                    (scopedCoreContext right))))
    typesMatch <- compareTypes (scopedCoreType left) (scopedCoreType right)
    unless typesMatch
        (throwError
            (ConversionInputFailure
                (ConversionRootTypeMismatch
                    (scopedCoreType left)
                    (scopedCoreType right))))

translateEngineFailure
    :: Pure.EngineFailure
    -> Checked global value
translateEngineFailure = \case
    Pure.EngineLimitExhausted -> exhausted
    Pure.EngineExpectedArrow coreType ->
        invariant (ConversionExpectedArrow coreType)
    Pure.EngineTypeFlowMismatch expected actual ->
        invariant (ConversionTypeFlowMismatch expected actual)
    Pure.EngineBoundIndexOutOfScope depth index ->
        invariant (ConversionBoundIndexOutOfScope depth index)
    Pure.EngineSemanticLevelOutOfScope depth level ->
        invariant (ConversionSemanticLevelOutOfScope depth level)
    Pure.EngineReflectedLevelEscaped depth level ->
        invariant (ConversionReflectedLevelEscaped depth level)
  where
    invariant = throwError . ConversionInvariantFailure

runEngine
    :: (Word -> (Either Pure.EngineFailure value, Word))
    -> Checked global value
runEngine runner = do
    remaining <- gets checkedRemaining
    let (result, after) = runner remaining
    setRemainder after
    either translateEngineFailure pure result

recoverQuoted
    :: GlobalTyping global
    -> Pure.QuotedCore global
    -> Checked global (ScopedCheckedCore global)
recoverQuoted destination (Pure.QuotedCore context expected term) = do
    beforeCheck <- gets checkedRemaining
    let (checkedResult, afterCheck) =
            countedCheckScopedCanonicalCore destination beforeCheck context term
    setRemainder afterCheck
    checked <- case checkedResult of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> exhausted
        Left (CountedCoreOperationFailed UnknownCoreGlobal) ->
            throwError
                (ConversionCheckedRecoveryFailure UnknownCoreGlobal)
        Left (CountedCoreOperationFailed cause) ->
            throwError
                (ConversionInvariantFailure
                    (ConversionQuotedCoreRejected cause))
    matches <- compareTypes expected (scopedCoreType checked)
    unless matches
        (throwError
            (ConversionInvariantFailure
                (ConversionRecoveredTypeMismatch expected
                    (scopedCoreType checked))))
    pure checked

convertibleChecked
    :: Eq global
    => GlobalTyping global
    -> ConversionLimit
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ConversionReport ConversionDecision
convertibleChecked globalTyping limit left right =
    runChecked limit do
        requirePairCompatibility left right
        left' <- admit globalTyping left
        right' <- admit globalTyping right
        identical <- compareCanonicalRoots
            (scopedCoreTerm left') (scopedCoreTerm right')
        if identical
            then pure Convertible
            else do
                matches <- runEngine \remaining ->
                    Pure.runConvertible globalTyping remaining
                        (scopedCoreContext left') (scopedCoreType left')
                        (scopedCoreTerm left') (scopedCoreTerm right')
                pure (if matches then Convertible else NotConvertible)

betaNormalizeChecked
    :: ConversionRecoveryTyping global
    -> ConversionLimit
    -> ScopedCheckedCore global
    -> ConversionReport (ScopedCheckedCore global)
betaNormalizeChecked typing limit checked =
    runChecked limit do
        admitted <- admit (conversionOperationTyping typing) checked
        quoted <- runEngine \remaining ->
            Pure.runBetaNormalize
                (conversionOperationTyping typing) remaining
                (scopedCoreContext admitted) (scopedCoreType admitted)
                (scopedCoreTerm admitted)
        recoverQuoted (conversionDestinationTyping typing) quoted

-- | Recover the weak head at the input type, preserving delayed redexes in
-- arguments and binder bodies. Global admission and checked recovery remain
-- complete; this operation does not request the whole normal form.
residualizeHeadChecked
    :: ConversionRecoveryTyping global
    -> ConversionLimit
    -> ScopedCheckedCore global
    -> ConversionReport (ScopedCheckedCore global)
residualizeHeadChecked typing limit checked =
    runChecked limit (residualizeHead typing checked)

residualizeHead
    :: ConversionRecoveryTyping global
    -> ScopedCheckedCore global
    -> Checked global (ScopedCheckedCore global)
residualizeHead typing checked = do
    admitted <- admit (conversionOperationTyping typing) checked
    quoted <- runEngine \remaining ->
        Pure.runResidualizeHead
            (conversionOperationTyping typing) remaining
            (scopedCoreContext admitted) (scopedCoreType admitted)
            (scopedCoreTerm admitted)
    recoverQuoted (conversionDestinationTyping typing) quoted

-- | Admit the complete proposition, follow its logical path with the existing
-- evaluator, and recover only nonoverlapping output components. All stages,
-- including failures, share this single operation allowance.
prepareImplicationSpineChecked
    :: ConversionRecoveryTyping global
    -> ConversionLimit
    -> ScopedCheckedCore global
    -> ConversionReport (PreparedSpine global)
prepareImplicationSpineChecked typing limit checked =
    runChecked limit do
        proposition <- compareTypes TyProp (scopedCoreType checked)
        unless proposition (throwError (ConversionInputFailure
            (ConversionRootTypeMismatch TyProp (scopedCoreType checked))))
        admitted <- admit (conversionOperationTyping typing) checked
        Pure.QuotedSpine steps terminal <- runEngine \remaining ->
            Pure.runPrepareImplicationSpine (conversionOperationTyping typing)
                remaining (scopedCoreContext admitted) (scopedCoreTerm admitted)
        recovered <- traverse recoverStep steps
        result <- recoverQuoted (conversionDestinationTyping typing) terminal
        pure (PreparedSpine recovered result)
  where
    recoverStep step = do
        remaining <- gets checkedRemaining
        if remaining == 0 then exhausted else setRemainder (remaining - 1)
        case step of
            Pure.QuotedUniversal binderType -> pure (PreparedUniversal binderType)
            Pure.QuotedPremise premise -> PreparedPremise
                <$> recoverQuoted (conversionDestinationTyping typing) premise

witnessConversionChecked
    :: Eq global
    => GlobalTyping global
    -> ConversionLimit
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ConversionReport (ConversionWitnessResult global)
witnessConversionChecked globalTyping limit left right =
    let report = convertibleChecked globalTyping limit left right
        result = case conversionResult report of
            Left failure -> Left failure
            Right NotConvertible -> Right WitnessNotConvertible
            Right Convertible ->
                Right
                    (WitnessConvertible
                        (SuccessfulConversion left right
                            (conversionCost report)))
    in ConversionReport result (conversionCost report)

-- Only the package-private derivation sealing bridge may consume this
-- capability. The witness supplies all three correlated fields.
eliminateSuccessfulConversion
    :: SuccessfulConversion global
    -> ( ScopedCheckedCore global
         -> ScopedCheckedCore global
         -> ConversionCost
         -> result
       )
    -> result
eliminateSuccessfulConversion
        (SuccessfulConversion source target cost) consume =
    consume source target cost

-- Replay one stored pair from fresh state with exactly its recorded cost.
-- Exhaustion cannot reveal a new cost without a second, unauthorized run.
replayStoredConversionChecked
    :: Eq global
    => GlobalTyping global
    -> ConversionCost
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ConversionReport ConversionDecision
replayStoredConversionChecked globalTyping recordedCost source target =
    let limit = ConversionLimit (conversionCostAmount recordedCost)
        report = convertibleChecked globalTyping limit source target
        mismatch = Left
            (ConversionInvariantFailure ConversionWitnessReplayMismatch)
        result = case conversionResult report of
            Left ConversionLimitExhausted{} -> mismatch
            Left failure@ConversionInputFailure{} -> Left failure
            Left failure@ConversionCheckedRecoveryFailure{} -> Left failure
            Left failure@ConversionInvariantFailure{} -> Left failure
            Right NotConvertible -> mismatch
            Right Convertible
                | conversionCost report == recordedCost -> Right Convertible
                | otherwise -> Left
                    (ConversionInvariantFailure
                        (ConversionWitnessReplayCostMismatch
                            recordedCost (conversionCost report)))
    in ConversionReport result (conversionCost report)
