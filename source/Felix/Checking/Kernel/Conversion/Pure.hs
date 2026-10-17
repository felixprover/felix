{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

-- | Package-private, pure call-by-name conversion machine.  The machine
-- consumes only checked roots and never constructs checked evidence itself.
module Felix.Checking.Kernel.Conversion.Pure
    ( EngineFailure(..)
    , QuotedCore(..)
    , runConvertible
    , runBetaNormalize
    , runResidualizeHead
    , QuotedSpine(..)
    , QuotedSpineStep(..)
    , runPrepareImplicationSpine
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping, lookupGlobalType)

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad (foldM, unless)
import Control.Monad.State.Strict (State, gets, modify', runState)
import Data.Sequence qualified as Seq
import Data.Word (Word)
import Numeric.Natural (Natural)


newtype Depth = Depth Natural
    deriving stock (Show, Eq, Ord)

newtype Lvl = Lvl Natural
    deriving stock (Show, Eq, Ord)

data EngineFailure
    = EngineLimitExhausted
    | EngineExpectedArrow !CoreType
    | EngineTypeFlowMismatch !CoreType !CoreType
    | EngineBoundIndexOutOfScope !Natural !Natural
    | EngineSemanticLevelOutOfScope !Natural !Natural
    | EngineReflectedLevelEscaped !Natural !Natural
    deriving stock (Show, Eq)

data QuotedCore global = QuotedCore
    ![CoreType]
    !CoreType
    !(CanonicalTerm global)
    deriving stock (Show, Eq)

-- These closed outputs contain syntax only, never a semantic suspension.
data QuotedSpine global = QuotedSpine
    ![QuotedSpineStep global]
    !(QuotedCore global)

data QuotedSpineStep global
    = QuotedUniversal !CoreType
    | QuotedPremise !(QuotedCore global)

data Transition
    = BuildRootEnvironment
    | ObserveCode
    | CompareType
    | FollowEnvironmentLink
    | ApplyValue
    | ForceSuspension
    | EnterBeta
    | ExtendNeutral
    | TraverseNeutralArgument
    | ReflectBinder
    | CompareSemanticValue
    | MaterializeConstructor
    | QuoteConstructor
    | EmitSpineStep

data MachineState = MachineState
    { machineRemaining :: !Word
    }

type Machine global = ExceptT EngineFailure (State MachineState)

data Environment global = Environment
    !Depth
    ![TypedSuspension global]

data TypedSuspension global = TypedSuspension
    !CoreType
    !(SuspensionContent global)

data SuspensionContent global
    = SuspendedTerm
        !Depth
        !(Environment global)
        !(CanonicalTerm global)
    | SuspendedValue !(Value global)

data PendingArgument global = PendingArgument
    !Depth
    !(Environment global)
    !(CanonicalTerm global)

data Value global
    = ValueLambda
        !CoreType
        !CoreType
        !Depth
        !(Environment global)
        !(CanonicalTerm global)
    | ValueNeutral !(Neutral global)
    | ValueFalsum
    | ValueTruth
    | ValueNegation !(TypedSuspension global)
    | ValueConjunction
        !(TypedSuspension global)
        !(TypedSuspension global)
    | ValueDisjunction
        !(TypedSuspension global)
        !(TypedSuspension global)
    | ValueImplication
        !(TypedSuspension global)
        !(TypedSuspension global)
    | ValueEquality
        !CoreType
        !(TypedSuspension global)
        !(TypedSuspension global)
    | ValueUniversal !(BinderClosure global)
    | ValueExistential !(BinderClosure global)

data BinderClosure global = BinderClosure
    !CoreType
    !Depth
    !(Environment global)
    !(CanonicalTerm global)

data Neutral global = Neutral
    !(SemanticHead global)
    !CoreType
    !(Seq (NeutralArgument global))
    !CoreType

data NeutralArgument global = NeutralArgument
    !CoreType
    !(TypedSuspension global)

data SemanticHead global
    = SemanticLocal !Lvl
    | SemanticGlobal !global
    | SemanticIntrinsic !CoreIntrinsicTag
    | SemanticLogicalSelect !CoreType
    | SemanticOpaqueInteger !Integer
    deriving stock (Show)


runMachine
    :: Word
    -> Machine global result
    -> (Either EngineFailure result, Word)
runMachine limit action =
    let (result, final) = runState (runExceptT action) (MachineState limit)
    in (result, machineRemaining final)

charge :: Transition -> Machine global ()
charge _transition = do
    remaining <- gets machineRemaining
    if remaining == 0
        then throwError EngineLimitExhausted
        else modify' \state -> state{machineRemaining = remaining - 1}

newTermSuspension
    :: CoreType
    -> Depth
    -> Environment global
    -> CanonicalTerm global
    -> Machine global (TypedSuspension global)
newTermSuspension coreType depth environment term =
    pure
        (TypedSuspension coreType
            (SuspendedTerm depth environment term))

newValueSuspension
    :: CoreType
    -> Value global
    -> Machine global (TypedSuspension global)
newValueSuspension coreType value =
    pure (TypedSuspension coreType (SuspendedValue value))

force
    :: GlobalTyping global
    -> TypedSuspension global
    -> Machine global (Value global)
force globalTyping (TypedSuspension coreType content) = do
    charge ForceSuspension
    case content of
        SuspendedTerm depth environment term ->
            evaluateExact globalTyping depth environment coreType term
        SuspendedValue value ->
            pure value

depthAmount :: Depth -> Natural
depthAmount (Depth depth) = depth

incrementDepth :: Depth -> Depth
incrementDepth (Depth depth) = Depth (depth + 1)

levelToIndex :: Depth -> Lvl -> Either EngineFailure Natural
levelToIndex (Depth depth) (Lvl level)
    | level < depth = Right (depth - level - 1)
    | otherwise = Left (EngineSemanticLevelOutOfScope depth level)

buildRootEnvironment
    :: [CoreType]
    -> Machine global (Depth, Environment global)
buildRootEnvironment = go
  where
    go [] =
        pure (Depth 0, Environment (Depth 0) [])
    go (coreType : rest) = do
        charge BuildRootEnvironment
        (Depth tailDepth, Environment _tailEnvironmentDepth tailEntries) <-
            go rest
        let depth = Depth (tailDepth + 1)
            neutral = Neutral (SemanticLocal (Lvl tailDepth)) coreType
                Seq.empty coreType
        suspension <- newValueSuspension coreType (ValueNeutral neutral)
        let entries = suspension : tailEntries
        entries `seq` pure (depth, Environment depth entries)

lookupEnvironment
    :: Natural
    -> Environment global
    -> Machine global (TypedSuspension global)
lookupEnvironment index (Environment depth entries) =
    go index entries
  where
    go _ [] =
        throwError
            (EngineBoundIndexOutOfScope (depthAmount depth) index)
    go 0 (entry : _rest) = do
        charge FollowEnvironmentLink
        pure entry
    go remaining (_entry : rest) = do
        charge FollowEnvironmentLink
        go (remaining - 1) rest

compareCoreType
    :: CoreType
    -> CoreType
    -> Machine global Bool
compareCoreType left right = do
    charge CompareType
    case left of
        TyProp ->
            case right of
                TyProp -> pure True
                TySet -> pure False
                TyArrow{} -> pure False
        TySet ->
            case right of
                TyProp -> pure False
                TySet -> pure True
                TyArrow{} -> pure False
        TyArrow leftDomain leftResult ->
            case right of
                TyProp -> pure False
                TySet -> pure False
                TyArrow rightDomain rightResult -> do
                    domains <- compareCoreType leftDomain rightDomain
                    if domains
                        then compareCoreType leftResult rightResult
                        else pure False

requireCoreType
    :: CoreType
    -> CoreType
    -> Machine global ()
requireCoreType expected actual = do
    matches <- compareCoreType expected actual
    unless matches
        (throwError (EngineTypeFlowMismatch expected actual))

collectApplicationSpine
    :: Depth
    -> Environment global
    -> CanonicalTerm global
    -> [PendingArgument global]
    -> Machine global (CanonicalTerm global, [PendingArgument global])
collectApplicationSpine depth environment term arguments = do
    charge ObserveCode
    case term of
        CApp function argument ->
            collectApplicationSpine depth environment function
                (PendingArgument depth environment argument : arguments)
        headTerm -> pure (headTerm, arguments)

evaluateExact
    :: GlobalTyping global
    -> Depth
    -> Environment global
    -> CoreType
    -> CanonicalTerm global
    -> Machine global (Value global)
evaluateExact globalTyping depth environment expected term =
    evaluateWithArguments globalTyping depth environment expected term []

evaluateWithArguments
    :: GlobalTyping global
    -> Depth
    -> Environment global
    -> CoreType
    -> CanonicalTerm global
    -> [PendingArgument global]
    -> Machine global (Value global)
evaluateWithArguments globalTyping depth environment expected term extra = do
    (headTerm, arguments) <-
        collectApplicationSpine depth environment term extra
    case headTerm of
        CBound index -> do
            entry <- lookupEnvironment index environment
            value <- force globalTyping entry
            applyArguments globalTyping depth expected value arguments
        CGlobal global ->
            case lookupGlobalType globalTyping global of
                Just actual ->
                    neutralHead (SemanticGlobal global) actual arguments
                Nothing ->
                    throwError (EngineTypeFlowMismatch expected expected)
        CIntrinsic intrinsic ->
            neutralHead (SemanticIntrinsic intrinsic)
                (coreIntrinsicType intrinsic) arguments
        CLogicalSelect coreType ->
            neutralHead (SemanticLogicalSelect coreType)
                (logicalSelectionType coreType) arguments
        COpaqueInteger integer ->
            neutralHead (SemanticOpaqueInteger integer) TySet arguments
        CLam binderType body ->
            case arguments of
                [] ->
                    case expected of
                        TyArrow expectedBinder bodyType -> do
                            requireCoreType expectedBinder binderType
                            pure
                                (ValueLambda binderType bodyType depth
                                    environment body)
                        _ -> throwError (EngineExpectedArrow expected)
                PendingArgument argumentDepth argumentEnvironment argument : rest -> do
                    charge ApplyValue
                    suspended <- newTermSuspension
                        binderType argumentDepth argumentEnvironment argument
                    charge EnterBeta
                    let extended = extendEnvironment binderType suspended
                            environment
                    evaluateWithArguments globalTyping (incrementDepth depth)
                        extended expected body rest
        CFalsum -> proposition ValueFalsum arguments
        CTruth -> proposition ValueTruth arguments
        CNot child -> do
            ensureNoArguments expected arguments
            suspended <- newTermSuspension TyProp depth environment child
            pure (ValueNegation suspended)
        CAnd left right -> do
            ensureNoArguments expected arguments
            left' <- newTermSuspension TyProp depth environment left
            right' <- newTermSuspension TyProp depth environment right
            pure (ValueConjunction left' right')
        COr left right -> do
            ensureNoArguments expected arguments
            left' <- newTermSuspension TyProp depth environment left
            right' <- newTermSuspension TyProp depth environment right
            pure (ValueDisjunction left' right')
        CImp premise conclusion -> do
            ensureNoArguments expected arguments
            premise' <- newTermSuspension TyProp depth environment premise
            conclusion' <- newTermSuspension TyProp depth environment conclusion
            pure (ValueImplication premise' conclusion')
        CEq operandType left right -> do
            ensureNoArguments expected arguments
            left' <- newTermSuspension operandType depth environment left
            right' <- newTermSuspension operandType depth environment right
            pure (ValueEquality operandType left' right')
        CForall binderType body -> do
            ensureNoArguments expected arguments
            pure
                (ValueUniversal
                    (BinderClosure binderType depth environment body))
        CExists binderType body -> do
            ensureNoArguments expected arguments
            pure
                (ValueExistential
                    (BinderClosure binderType depth environment body))
        CApp{} ->
            throwError (EngineTypeFlowMismatch expected expected)
  where
    neutralHead semanticHead actual arguments = do
        let neutral = Neutral semanticHead actual Seq.empty actual
        applyArguments globalTyping depth expected (ValueNeutral neutral)
            arguments

    proposition value arguments = do
        ensureNoArguments expected arguments
        pure value

    ensureNoArguments expectedType arguments = do
        requireCoreType TyProp expectedType
        unless (null arguments)
            (throwError (EngineExpectedArrow TyProp))

extendEnvironment
    :: CoreType
    -> TypedSuspension global
    -> Environment global
    -> Environment global
extendEnvironment _coreType suspension (Environment depth entries) =
    Environment (incrementDepth depth) (suspension : entries)

valueType :: Value global -> CoreType
valueType = \case
    ValueLambda binderType bodyType _depth _environment _body ->
        TyArrow binderType bodyType
    ValueNeutral (Neutral _head _headType _arguments resultType) ->
        resultType
    ValueFalsum -> TyProp
    ValueTruth -> TyProp
    ValueNegation{} -> TyProp
    ValueConjunction{} -> TyProp
    ValueDisjunction{} -> TyProp
    ValueImplication{} -> TyProp
    ValueEquality{} -> TyProp
    ValueUniversal{} -> TyProp
    ValueExistential{} -> TyProp

applyArguments
    :: GlobalTyping global
    -> Depth
    -> CoreType
    -> Value global
    -> [PendingArgument global]
    -> Machine global (Value global)
applyArguments globalTyping depth expected value = \case
    [] -> do
        requireCoreType expected (valueType value)
        pure value
    PendingArgument argumentDepth argumentEnvironment argument : rest -> do
        charge ApplyValue
        case valueType value of
            TyArrow domain _result -> do
                suspended <- newTermSuspension domain
                    argumentDepth argumentEnvironment argument
                value' <- applyValue globalTyping depth value suspended
                applyArguments globalTyping depth expected value' rest
            actual -> throwError (EngineExpectedArrow actual)

applyValue
    :: GlobalTyping global
    -> Depth
    -> Value global
    -> TypedSuspension global
    -> Machine global (Value global)
applyValue globalTyping _callerDepth value argument =
    case value of
        ValueLambda binderType bodyType closureDepth closureEnvironment body -> do
            let TypedSuspension argumentType _content = argument
            requireCoreType binderType argumentType
            charge EnterBeta
            evaluateExact globalTyping (incrementDepth closureDepth)
                (extendEnvironment binderType argument closureEnvironment)
                bodyType body
        ValueNeutral
                (Neutral headValue headCoreType arguments currentResult) -> do
            charge ExtendNeutral
            let TypedSuspension argumentType _content = argument
            case currentResult of
                TyArrow domain codomain -> do
                    requireCoreType domain argumentType
                    pure
                        (ValueNeutral
                            (Neutral headValue headCoreType
                                (arguments Seq.|>
                                    NeutralArgument domain argument)
                                codomain))
                other -> throwError (EngineExpectedArrow other)
        _ -> throwError (EngineExpectedArrow (valueType value))

reflect
    :: Depth
    -> CoreType
    -> Machine global (TypedSuspension global)
reflect depth coreType = do
    charge ReflectBinder
    let level = Lvl (depthAmount depth)
        neutral = Neutral (SemanticLocal level) coreType Seq.empty coreType
    newValueSuspension coreType (ValueNeutral neutral)

compareSuspensions
    :: Eq global
    => GlobalTyping global
    -> Depth
    -> CoreType
    -> TypedSuspension global
    -> TypedSuspension global
    -> Machine global Bool
compareSuspensions globalTyping depth coreType left right = do
    let TypedSuspension _leftType leftContent = left
        TypedSuspension _rightType rightContent = right
    leftRedex <- hasHeadRedex leftContent
    mayReduce <- if leftRedex then pure True else hasHeadRedex rightContent
    congruent <- if mayReduce
        then congruentContents depth leftContent rightContent
        else pure False
    if congruent
        then pure True
        else do
            leftValue <- force globalTyping left
            rightValue <- force globalTyping right
            compareValues globalTyping depth coreType leftValue rightValue

-- Exposed constructors are already compared incrementally by compareValues.
-- Probing their entire subtrees would repeatedly scan a common neutral or
-- logical prefix on the way to a mismatch. Inspect only the function spine and
-- bound aliases here; arguments stay suspended and no beta reduction occurs.
hasHeadRedex :: SuspensionContent global -> Machine global Bool
hasHeadRedex = go False
  where
    go applied content =
        case content of
            SuspendedTerm closureDepth environment term -> do
                charge ObserveCode
                case term of
                    CApp function _argument ->
                        go True (SuspendedTerm closureDepth environment function)
                    CBound index -> do
                        TypedSuspension _coreType captured <-
                            lookupEnvironment index environment
                        go applied captured
                    CLam{} -> pure applied
                    _ -> pure False
            SuspendedValue value -> do
                charge CompareSemanticValue
                case value of
                    ValueLambda{} -> pure applied
                    _ -> pure False

-- A sufficient equality check, not a negative conversion decision. Compare
-- compact written syntax under its captured environments before beta reduction
-- can duplicate it. Only referenced bindings are followed. A failed attempt
-- keeps its cost before ordinary conversion resumes.
congruentContents
    :: Eq global
    => Depth
    -> SuspensionContent global
    -> SuspensionContent global
    -> Machine global Bool
congruentContents depth left right = do
    leftHead <- resolve left
    rightHead <- resolve right
    case (leftHead, rightHead) of
        (SuspendedTerm leftDepth leftEnvironment leftTerm,
         SuspendedTerm rightDepth rightEnvironment rightTerm) ->
            let child leftChild rightChild =
                    congruentContents depth
                        (SuspendedTerm leftDepth leftEnvironment leftChild)
                        (SuspendedTerm rightDepth rightEnvironment rightChild)
                pair leftFirst rightFirst leftSecond rightSecond = do
                    sameFirst <- child leftFirst rightFirst
                    if sameFirst
                        then child leftSecond rightSecond
                        else pure False
                binder leftType leftBody rightType rightBody = do
                    sameType <- compareCoreType leftType rightType
                    if not sameType
                        then pure False
                        else do
                            -- The shared fresh local aligns both written binders
                            -- and cannot coincide with any captured local. These
                            -- temporary extensions never escape the check.
                            argument <- reflect depth leftType
                            congruentContents (incrementDepth depth)
                                (SuspendedTerm (incrementDepth leftDepth)
                                    (extendEnvironment leftType argument leftEnvironment)
                                    leftBody)
                                (SuspendedTerm (incrementDepth rightDepth)
                                    (extendEnvironment rightType argument rightEnvironment)
                                    rightBody)
            in case (leftTerm, rightTerm) of
                (CGlobal leftGlobal, CGlobal rightGlobal) ->
                    pure (leftGlobal == rightGlobal)
                (CIntrinsic leftIntrinsic, CIntrinsic rightIntrinsic) ->
                    pure (leftIntrinsic == rightIntrinsic)
                (CLogicalSelect leftType, CLogicalSelect rightType) ->
                    compareCoreType leftType rightType
                (COpaqueInteger leftInteger, COpaqueInteger rightInteger) ->
                    pure (leftInteger == rightInteger)
                (CApp leftFunction leftArgument, CApp rightFunction rightArgument) ->
                    pair leftFunction rightFunction leftArgument rightArgument
                (CLam leftType leftBody, CLam rightType rightBody) ->
                    binder leftType leftBody rightType rightBody
                (CFalsum, CFalsum) -> pure True
                (CTruth, CTruth) -> pure True
                (CNot leftChild, CNot rightChild) -> child leftChild rightChild
                (CAnd leftFirst leftSecond, CAnd rightFirst rightSecond) ->
                    pair leftFirst rightFirst leftSecond rightSecond
                (COr leftFirst leftSecond, COr rightFirst rightSecond) ->
                    pair leftFirst rightFirst leftSecond rightSecond
                (CImp leftFirst leftSecond, CImp rightFirst rightSecond) ->
                    pair leftFirst rightFirst leftSecond rightSecond
                (CEq leftType leftFirst leftSecond,
                 CEq rightType rightFirst rightSecond) -> do
                    sameType <- compareCoreType leftType rightType
                    if sameType
                        then pair leftFirst rightFirst leftSecond rightSecond
                        else pure False
                (CForall leftType leftBody, CForall rightType rightBody) ->
                    binder leftType leftBody rightType rightBody
                (CExists leftType leftBody, CExists rightType rightBody) ->
                    binder leftType leftBody rightType rightBody
                _ -> pure False
        (SuspendedValue (ValueNeutral (Neutral (SemanticLocal leftLevel) leftType leftArgs _)),
         SuspendedValue (ValueNeutral (Neutral (SemanticLocal rightLevel) rightType rightArgs _)))
            | Seq.null leftArgs && Seq.null rightArgs && leftLevel == rightLevel ->
                compareCoreType leftType rightType
        _ -> pure False
  where
    resolve content =
        case content of
            SuspendedTerm _closureDepth environment term -> do
                charge ObserveCode
                case term of
                    CBound index -> do
                        TypedSuspension _coreType captured <-
                            lookupEnvironment index environment
                        resolve captured
                    _ -> pure content
            SuspendedValue{} -> do
                charge CompareSemanticValue
                pure content

compareValues
    :: Eq global
    => GlobalTyping global
    -> Depth
    -> CoreType
    -> Value global
    -> Value global
    -> Machine global Bool
compareValues globalTyping depth coreType left right = do
    charge CompareSemanticValue
    case coreType of
        TyArrow domain result ->
            -- Both values have the admitted arrow type. Applying either closure
            -- or neutral to a fresh comparison-level argument is capture avoiding
            -- and implements eta; two rigid neutrals only need spine comparison.
            case (left, right) of
                (ValueLambda{}, ValueLambda{}) -> compareApplied domain result
                (ValueLambda{}, ValueNeutral{}) -> compareApplied domain result
                (ValueNeutral{}, ValueLambda{}) -> compareApplied domain result
                (ValueNeutral leftNeutral, ValueNeutral rightNeutral) ->
                    compareNeutrals globalTyping depth
                        leftNeutral rightNeutral
                _ -> throwError (EngineTypeFlowMismatch coreType
                    (case left of
                        ValueLambda{} -> valueType right
                        ValueNeutral{} -> valueType right
                        _ -> valueType left))
        TySet -> compareSetValues
        TyProp -> comparePropositions
  where
    compareApplied domain result = do
        reflected <- reflect depth domain
        charge ApplyValue
        leftResult <- applyValue globalTyping depth left reflected
        requireCoreType result (valueType leftResult)
        charge ApplyValue
        rightResult <- applyValue globalTyping depth right reflected
        requireCoreType result (valueType rightResult)
        compareValues globalTyping (incrementDepth depth) result
            leftResult rightResult

    compareSetValues =
        case (left, right) of
            (ValueNeutral leftNeutral, ValueNeutral rightNeutral) ->
                compareNeutrals globalTyping depth leftNeutral rightNeutral
            _ -> pure False

    comparePropositions =
        case (left, right) of
            (ValueTruth, ValueTruth) -> pure True
            (ValueFalsum, ValueFalsum) -> pure True
            (ValueNegation leftChild, ValueNegation rightChild) ->
                compareSuspensions globalTyping depth TyProp
                    leftChild rightChild
            (ValueConjunction leftFirst leftSecond,
             ValueConjunction rightFirst rightSecond) ->
                comparePair TyProp leftFirst rightFirst
                    TyProp leftSecond rightSecond
            (ValueDisjunction leftFirst leftSecond,
             ValueDisjunction rightFirst rightSecond) ->
                comparePair TyProp leftFirst rightFirst
                    TyProp leftSecond rightSecond
            (ValueImplication leftFirst leftSecond,
             ValueImplication rightFirst rightSecond) ->
                comparePair TyProp leftFirst rightFirst
                    TyProp leftSecond rightSecond
            (ValueEquality leftType leftFirst leftSecond,
             ValueEquality rightType rightFirst rightSecond) -> do
                sameType <- compareCoreType leftType rightType
                if sameType
                    then comparePair leftType leftFirst rightFirst
                        leftType leftSecond rightSecond
                    else pure False
            (ValueUniversal leftClosure, ValueUniversal rightClosure) ->
                compareBinders leftClosure rightClosure
            (ValueExistential leftClosure, ValueExistential rightClosure) ->
                compareBinders leftClosure rightClosure
            (ValueNeutral leftNeutral, ValueNeutral rightNeutral) ->
                compareNeutrals globalTyping depth leftNeutral rightNeutral
            _ -> pure False

    comparePair firstType leftFirst rightFirst secondType leftSecond rightSecond = do
        firstMatches <- compareSuspensions globalTyping depth firstType
            leftFirst rightFirst
        if firstMatches
            then compareSuspensions globalTyping depth secondType
                leftSecond rightSecond
            else pure False

    compareBinders leftClosure rightClosure = do
        let BinderClosure leftType _ _ _ = leftClosure
            BinderClosure rightType _ _ _ = rightClosure
        domainsMatch <- compareCoreType leftType rightType
        if not domainsMatch
            then pure False
            else do
                argument <- reflect depth leftType
                leftBody <- enterBinder globalTyping leftClosure argument
                rightBody <- enterBinder globalTyping rightClosure argument
                compareValues globalTyping (incrementDepth depth) TyProp
                    leftBody rightBody

enterBinder
    :: GlobalTyping global
    -> BinderClosure global
    -> TypedSuspension global
    -> Machine global (Value global)
enterBinder globalTyping
        (BinderClosure binderType closureDepth environment body) argument = do
    let TypedSuspension argumentType _content = argument
    requireCoreType binderType argumentType
    evaluateExact globalTyping (incrementDepth closureDepth)
        (extendEnvironment binderType argument environment) TyProp body

-- Head dispatch belongs to CompareSemanticValue; recursive payload work
-- consumes its own type-comparison transitions.
compareSemanticHeads
    :: Eq global
    => SemanticHead global
    -> SemanticHead global
    -> Machine global Bool
compareSemanticHeads left right =
    case left of
        SemanticLocal leftLevel ->
            case right of
                SemanticLocal rightLevel -> pure (leftLevel == rightLevel)
                SemanticGlobal{} -> pure False
                SemanticIntrinsic{} -> pure False
                SemanticLogicalSelect{} -> pure False
                SemanticOpaqueInteger{} -> pure False
        SemanticGlobal leftGlobal ->
            case right of
                SemanticLocal{} -> pure False
                SemanticGlobal rightGlobal -> pure (leftGlobal == rightGlobal)
                SemanticIntrinsic{} -> pure False
                SemanticLogicalSelect{} -> pure False
                SemanticOpaqueInteger{} -> pure False
        SemanticIntrinsic leftIntrinsic ->
            case right of
                SemanticLocal{} -> pure False
                SemanticGlobal{} -> pure False
                SemanticIntrinsic rightIntrinsic ->
                    pure (leftIntrinsic == rightIntrinsic)
                SemanticLogicalSelect{} -> pure False
                SemanticOpaqueInteger{} -> pure False
        SemanticLogicalSelect leftType ->
            case right of
                SemanticLocal{} -> pure False
                SemanticGlobal{} -> pure False
                SemanticIntrinsic{} -> pure False
                SemanticLogicalSelect rightType ->
                    compareCoreType leftType rightType
                SemanticOpaqueInteger{} -> pure False
        SemanticOpaqueInteger leftInteger ->
            case right of
                SemanticLocal{} -> pure False
                SemanticGlobal{} -> pure False
                SemanticIntrinsic{} -> pure False
                SemanticLogicalSelect{} -> pure False
                SemanticOpaqueInteger rightInteger ->
                    pure (leftInteger == rightInteger)

compareNeutrals
    :: Eq global
    => GlobalTyping global
    -> Depth
    -> Neutral global
    -> Neutral global
    -> Machine global Bool
compareNeutrals globalTyping depth
        (Neutral leftHead leftHeadType leftArguments leftResult)
        (Neutral rightHead rightHeadType rightArguments rightResult) = do
    sameHead <- compareSemanticHeads leftHead rightHead
    if not sameHead
        then pure False
        else do
            sameHeadType <- compareCoreType leftHeadType rightHeadType
            sameResult <- if sameHeadType
                then compareCoreType leftResult rightResult
                else pure False
            if sameResult
                then compareArguments leftArguments rightArguments
                else pure False
  where
    compareArguments left right =
        case (Seq.viewl left, Seq.viewl right) of
            (Seq.EmptyL, Seq.EmptyL) -> pure True
            (NeutralArgument leftType leftArgument Seq.:< leftRest,
             NeutralArgument rightType rightArgument Seq.:< rightRest) -> do
                charge TraverseNeutralArgument
                sameType <- compareCoreType leftType rightType
                if not sameType
                    then pure False
                    else do
                        sameArgument <- compareSuspensions globalTyping depth
                            leftType leftArgument rightArgument
                        if sameArgument
                            then compareArguments leftRest rightRest
                            else pure False
            (Seq.EmptyL, _rightRow Seq.:< _rightRest) -> do
                charge TraverseNeutralArgument
                pure False
            (_leftRow Seq.:< _leftRest, Seq.EmptyL) -> do
                charge TraverseNeutralArgument
                pure False

quoteSuspension
    :: GlobalTyping global
    -> Depth
    -> CoreType
    -> TypedSuspension global
    -> Machine global (CanonicalTerm global)
quoteSuspension globalTyping depth coreType suspension = do
    value <- force globalTyping suspension
    quoteValue globalTyping depth coreType value

quoteValue
    :: GlobalTyping global
    -> Depth
    -> CoreType
    -> Value global
    -> Machine global (CanonicalTerm global)
quoteValue globalTyping depth coreType value =
    case coreType of
        TyArrow domain result ->
            case value of
                ValueLambda{} -> do
                    charge QuoteConstructor
                    argument <- reflect depth domain
                    charge ApplyValue
                    bodyValue <- applyValue globalTyping depth value argument
                    requireCoreType result (valueType bodyValue)
                    body <- quoteValue globalTyping (incrementDepth depth)
                        result bodyValue
                    pure (CLam domain body)
                ValueNeutral neutral ->
                    quoteNeutral globalTyping depth neutral
                _ -> throwError (EngineExpectedArrow coreType)
        TySet ->
            case value of
                ValueNeutral neutral -> quoteNeutral globalTyping depth neutral
                _ -> throwError (EngineTypeFlowMismatch TySet TyProp)
        TyProp -> quoteProposition
  where
    quoteProposition =
        case value of
            ValueFalsum -> atom CFalsum
            ValueTruth -> atom CTruth
            ValueNegation child -> do
                charge QuoteConstructor
                CNot <$> quoteSuspension globalTyping depth TyProp child
            ValueConjunction left right -> do
                charge QuoteConstructor
                CAnd
                    <$> quoteSuspension globalTyping depth TyProp left
                    <*> quoteSuspension globalTyping depth TyProp right
            ValueDisjunction left right -> do
                charge QuoteConstructor
                COr
                    <$> quoteSuspension globalTyping depth TyProp left
                    <*> quoteSuspension globalTyping depth TyProp right
            ValueImplication premise conclusion -> do
                charge QuoteConstructor
                CImp
                    <$> quoteSuspension globalTyping depth TyProp premise
                    <*> quoteSuspension globalTyping depth TyProp conclusion
            ValueEquality operandType left right -> do
                charge QuoteConstructor
                CEq operandType
                    <$> quoteSuspension globalTyping depth operandType left
                    <*> quoteSuspension globalTyping depth operandType right
            ValueUniversal closure@(BinderClosure binderType _ _ _) -> do
                charge QuoteConstructor
                argument <- reflect depth binderType
                bodyValue <- enterBinder globalTyping closure argument
                body <- quoteValue globalTyping (incrementDepth depth) TyProp
                    bodyValue
                pure (CForall binderType body)
            ValueExistential closure@(BinderClosure binderType _ _ _) -> do
                charge QuoteConstructor
                argument <- reflect depth binderType
                bodyValue <- enterBinder globalTyping closure argument
                body <- quoteValue globalTyping (incrementDepth depth) TyProp
                    bodyValue
                pure (CExists binderType body)
            ValueNeutral neutral -> quoteNeutral globalTyping depth neutral
            _ -> throwError (EngineTypeFlowMismatch TyProp coreType)

    atom term = do
        charge QuoteConstructor
        pure term

quoteNeutral
    :: GlobalTyping global
    -> Depth
    -> Neutral global
    -> Machine global (CanonicalTerm global)
quoteNeutral globalTyping depth
        (Neutral semanticHead _headType arguments _resultType) = do
    charge QuoteConstructor
    headTerm <- case semanticHead of
        SemanticLocal level ->
            CBound <$> either throwError pure (levelToIndex depth level)
        SemanticGlobal global -> pure (CGlobal global)
        SemanticIntrinsic intrinsic -> pure (CIntrinsic intrinsic)
        SemanticLogicalSelect coreType -> pure (CLogicalSelect coreType)
        SemanticOpaqueInteger integer -> pure (COpaqueInteger integer)
    foldM quoteArgument headTerm arguments
  where
    quoteArgument function (NeutralArgument argumentType argument) = do
        charge QuoteConstructor
        CApp function
            <$> quoteSuspension globalTyping depth argumentType argument

-- | Materialize a suspension into the destination scope without evaluating
-- its delayed term.  This is the weak-head residualization path: beta entries
-- already taken to expose the head are reflected through environments, while
-- beta redexes inside retained children remain syntax.
materializeSuspension
    :: GlobalTyping global
    -> Depth
    -> TypedSuspension global
    -> Machine global (CanonicalTerm global)
materializeSuspension globalTyping targetDepth
        (TypedSuspension coreType content) =
    case content of
        SuspendedTerm _captureDepth environment term ->
            materializeTerm globalTyping targetDepth 0 environment term
        SuspendedValue value ->
            quoteValue globalTyping targetDepth coreType value

materializeTerm
    :: GlobalTyping global
    -> Depth
    -> Natural
    -> Environment global
    -> CanonicalTerm global
    -> Machine global (CanonicalTerm global)
materializeTerm globalTyping targetDepth localBinders environment term = do
    charge MaterializeConstructor
    case term of
        CBound index
            | index < localBinders -> emit (CBound index)
            | otherwise -> do
                suspension <- lookupEnvironment
                    (index - localBinders) environment
                materializeSuspension globalTyping targetDepth suspension
        CGlobal global -> emit (CGlobal global)
        CIntrinsic intrinsic -> emit (CIntrinsic intrinsic)
        CLogicalSelect coreType -> emit (CLogicalSelect coreType)
        COpaqueInteger integer -> emit (COpaqueInteger integer)
        CApp function argument -> do
            charge QuoteConstructor
            CApp
                <$> descend function
                <*> descend argument
        CLam binderType body -> do
            charge QuoteConstructor
            CLam binderType
                <$> materializeTerm globalTyping
                    (incrementDepth targetDepth) (localBinders + 1)
                    environment body
        CFalsum -> emit CFalsum
        CTruth -> emit CTruth
        CNot proposition -> do
            charge QuoteConstructor
            CNot <$> descend proposition
        CAnd left right -> do
            charge QuoteConstructor
            CAnd <$> descend left <*> descend right
        COr left right -> do
            charge QuoteConstructor
            COr <$> descend left <*> descend right
        CImp premise conclusion -> do
            charge QuoteConstructor
            CImp <$> descend premise <*> descend conclusion
        CEq operandType left right -> do
            charge QuoteConstructor
            CEq operandType <$> descend left <*> descend right
        CForall binderType body -> do
            charge QuoteConstructor
            CForall binderType
                <$> materializeTerm globalTyping
                    (incrementDepth targetDepth) (localBinders + 1)
                    environment body
        CExists binderType body -> do
            charge QuoteConstructor
            CExists binderType
                <$> materializeTerm globalTyping
                    (incrementDepth targetDepth) (localBinders + 1)
                    environment body
  where
    descend =
        materializeTerm globalTyping targetDepth localBinders environment
    emit emitted = charge QuoteConstructor >> pure emitted

residualizeValueHead
    :: GlobalTyping global
    -> Depth
    -> Value global
    -> Machine global (CanonicalTerm global)
residualizeValueHead globalTyping depth = \case
    ValueFalsum -> atom CFalsum
    ValueTruth -> atom CTruth
    ValueNegation child -> do
        charge QuoteConstructor
        CNot <$> materializeSuspension globalTyping depth child
    ValueConjunction left right -> do
        charge QuoteConstructor
        CAnd
            <$> materializeSuspension globalTyping depth left
            <*> materializeSuspension globalTyping depth right
    ValueDisjunction left right -> do
        charge QuoteConstructor
        COr
            <$> materializeSuspension globalTyping depth left
            <*> materializeSuspension globalTyping depth right
    ValueImplication premise conclusion -> do
        charge QuoteConstructor
        CImp
            <$> materializeSuspension globalTyping depth premise
            <*> materializeSuspension globalTyping depth conclusion
    ValueEquality operandType left right -> do
        charge QuoteConstructor
        CEq operandType
            <$> materializeSuspension globalTyping depth left
            <*> materializeSuspension globalTyping depth right
    ValueUniversal
            (BinderClosure binderType _closureDepth environment body) -> do
        charge QuoteConstructor
        CForall binderType
            <$> materializeTerm globalTyping (incrementDepth depth) 1
                environment body
    ValueExistential
            (BinderClosure binderType _closureDepth environment body) -> do
        charge QuoteConstructor
        CExists binderType
            <$> materializeTerm globalTyping (incrementDepth depth) 1
                environment body
    ValueNeutral neutral -> residualizeNeutral globalTyping depth neutral
    ValueLambda binderType _bodyType _closureDepth environment body -> do
        charge QuoteConstructor
        CLam binderType
            <$> materializeTerm globalTyping (incrementDepth depth) 1
                environment body
  where
    atom term = charge QuoteConstructor >> pure term

residualizeNeutral
    :: GlobalTyping global
    -> Depth
    -> Neutral global
    -> Machine global (CanonicalTerm global)
residualizeNeutral globalTyping depth
        (Neutral semanticHead _headType arguments _resultType) = do
    charge QuoteConstructor
    headTerm <- case semanticHead of
        SemanticLocal level ->
            CBound <$> either throwError pure (levelToIndex depth level)
        SemanticGlobal global -> pure (CGlobal global)
        SemanticIntrinsic intrinsic -> pure (CIntrinsic intrinsic)
        SemanticLogicalSelect coreType -> pure (CLogicalSelect coreType)
        SemanticOpaqueInteger integer -> pure (COpaqueInteger integer)
    foldM materializeArgument headTerm arguments
  where
    materializeArgument function (NeutralArgument _argumentType argument) = do
        charge QuoteConstructor
        CApp function <$> materializeSuspension globalTyping depth argument

runOperation
    :: Word
    -> [CoreType]
    -> (Depth -> Environment global -> Machine global result)
    -> (Either EngineFailure result, Word)
runOperation limit context action =
    runMachine limit do
        (depth, environment) <- buildRootEnvironment context
        action depth environment

runConvertible
    :: Eq global
    => GlobalTyping global
    -> Word
    -> [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> (Either EngineFailure Bool, Word)
runConvertible globalTyping limit context coreType left right =
    runOperation limit context \depth environment -> do
        leftValue <- evaluateExact globalTyping depth environment
            coreType left
        rightValue <- evaluateExact globalTyping depth environment
            coreType right
        compareValues globalTyping depth coreType leftValue rightValue

runBetaNormalize
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> (Either EngineFailure (QuotedCore global), Word)
runBetaNormalize globalTyping limit context coreType term =
    runOperation limit context \depth environment -> do
        value <- evaluateExact globalTyping depth environment coreType term
        quoted <- quoteValue globalTyping depth coreType value
        pure (QuotedCore context coreType quoted)

runResidualizeHead
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> (Either EngineFailure (QuotedCore global), Word)
runResidualizeHead globalTyping limit context coreType term =
    runOperation limit context \depth environment -> do
        value <- evaluateExact globalTyping depth environment coreType term
        quoted <- residualizeValueHead globalTyping depth value
        pure (QuotedCore context coreType quoted)

-- Follow one requested implication/universal spine with one environment and
-- allowance. Recover each premise at its own lexical prefix, never a suffix.
runPrepareImplicationSpine
    :: GlobalTyping global
    -> Word
    -> [CoreType]
    -> CanonicalTerm global
    -> (Either EngineFailure (QuotedSpine global), Word)
runPrepareImplicationSpine globalTyping limit context term =
    runOperation limit context \depth environment -> do
        value <- evaluateExact globalTyping depth environment TyProp term
        follow context depth value
  where
    follow scoped depth = \case
        ValueUniversal closure@(BinderClosure binderType _ _ _) -> do
            argument <- reflect depth binderType
            body <- enterBinder globalTyping closure argument
            QuotedSpine steps terminal <-
                follow (binderType : scoped) (incrementDepth depth) body
            charge EmitSpineStep
            pure (QuotedSpine (QuotedUniversal binderType : steps) terminal)
        ValueImplication premise conclusion -> do
            quoted <- materializeSuspension globalTyping depth premise
            body <- force globalTyping conclusion
            QuotedSpine steps terminal <- follow scoped depth body
            charge EmitSpineStep
            pure (QuotedSpine
                (QuotedPremise (QuotedCore scoped TyProp quoted) : steps) terminal)
        terminal -> do
            quoted <- residualizeValueHead globalTyping depth terminal
            charge EmitSpineStep
            pure (QuotedSpine [] (QuotedCore scoped TyProp quoted))
