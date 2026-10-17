{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Private provisional proof trees and independent kernel replay.  Generic
-- replay establishes a checked conclusion but grants no fact authority: an
-- authorizing owner must separately establish the import environment and
-- bind the replay result to its candidate or declaration capability.
module Felix.Checking.Kernel.Derivation
    ( ImportIx
    , importIx
    , importIxValue
    , HypothesisIx
    , hypothesisIx
    , hypothesisIxValue
    , DerivationImportJudgement
    , derivationImportJudgement
    , derivationImportStatement
    , KernelDerivation
    , eliminateKernelDerivationVoid
    , remapKernelDerivationImports
    , putKernelDerivationCache
    , importedFactDerivation
    , localHypothesisDerivation
    , foundationFactDerivation
    , truthIntroductionDerivation
    , negationIntroductionDerivation
    , negationEliminationDerivation
    , conjunctionIntroductionDerivation
    , conjunctionLeftEliminationDerivation
    , conjunctionRightEliminationDerivation
    , disjunctionLeftIntroductionDerivation
    , disjunctionRightIntroductionDerivation
    , disjunctionEliminationDerivation
    , existentialIntroductionDerivation
    , existentialEliminationDerivation
    , implicationEliminationDerivation
    , forallEliminationDerivation
    , falsumEliminationDerivation
    , implicationIntroductionDerivation
    , forallIntroductionDerivation
    , equalityReflexivityDerivation
    , scopedEqualityReflexivityDerivation
    , equalityCongruenceApplicationDerivation
    , equalityCongruenceLambdaDerivation
    , equalityModusPonensDerivation
    , setLfpBoundDerivation
    , setLfpLeastDerivation
    , setLfpFixedDerivation
    , setLfpInductDerivation
    , remapDerivationExternalHypotheses
    , weakenDerivationHypotheses
    , countedWeakenDerivationHypotheses
    , KernelSourceUses
    , kernelSourceImportUses
    , kernelSourceExternalHypothesisUses
    , countedKernelDerivationSourceUses
    , KernelReplayLimits
    , kernelReplayLimits
    , defaultKernelReplayLimits
    , KernelReplayLimitError(..)
    , ReplayedKernelDerivation
    , replayKernelDerivation
    , replayKernelDerivationMeasured
    , ReplayWork(..)
    , replayedKernelTarget
    , replayedKernelImportUses
    , replayedKernelFoundationUses
    , replayedKernelRuleUses
    , replayedKernelNodeCount
    , replayedKernelMaximumDepth
    , ReplayedScopedKernelDerivation
    , replayScopedKernelDerivation
    , replayScopedKernelDerivationMeasured
    , replayedScopedKernelTarget
    , replayedScopedKernelImportUses
    , replayedScopedKernelExternalHypothesisUses
    , replayedScopedKernelFoundationUses
    , replayedScopedKernelRuleUses
    , replayedScopedKernelNodeCount
    , replayedScopedKernelMaximumDepth
    , DerivationImportError(..)
    , KernelReplayError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Conversion.Checked (replayStoredConversionChecked)
import Felix.Checking.Kernel.Derivation.Internal
import Felix.Checking.Kernel.Semantics qualified as Semantics
import Felix.Checking.Kernel.SetLfp qualified as SetLfp
import Felix.Cache.Codec

import Control.Monad (unless)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)


importIx :: Natural -> ImportIx
importIx = ImportIx

importIxValue :: ImportIx -> Natural
importIxValue (ImportIx index) =
    index

hypothesisIx :: Natural -> HypothesisIx
hypothesisIx = HypothesisIx

hypothesisIxValue :: HypothesisIx -> Natural
hypothesisIxValue (HypothesisIx index) =
    index

newtype DerivationImportJudgement global =
    DerivationImportJudgement
        (FrozenCheckedCore global)
    deriving stock (Eq)

type role DerivationImportJudgement nominal

data DerivationImportError =
    DerivationImportIsNotProposition !CoreType
    deriving stock (Show, Eq)

derivationImportJudgement
    :: FrozenCheckedCore global
    -> Either
        DerivationImportError
        (DerivationImportJudgement global)
derivationImportJudgement statement
    | frozenCoreType statement == TyProp =
        Right (DerivationImportJudgement statement)
    | otherwise =
        Left
            (DerivationImportIsNotProposition
                (frozenCoreType statement))

derivationImportStatement
    :: DerivationImportJudgement global
    -> FrozenCheckedCore global
derivationImportStatement
        (DerivationImportJudgement statement) =
    statement

-- | Canonical prepared-proof identity for the complete checked derivation.
-- A decoder is unnecessary because prepared proof trees are not persisted.
putKernelDerivationCache
    :: (global -> CachePut)
    -> KernelDerivation global
    -> CachePut
putKernelDerivationCache putGlobal = go
  where
    go = \case
        UseImportedFact (ImportIx index) -> do
            putCacheTag 0x00
            putCacheNatural index
        UseLocalHypothesis (HypothesisIx index) -> do
            putCacheTag 0x01
            putCacheNatural index
        UseFoundationFact tag -> do
            putCacheTag 0x02
            putFoundationAxiomTagCache tag
        TruthIntroduction ->
            putCacheTag 0x03
        NegationIntroduction premise body -> do
            putCacheTag 0x04
            putScoped premise
            go body
        NegationElimination premise negation -> do
            putCacheTag 0x05
            go premise
            go negation
        ConjunctionIntroduction left right -> do
            putCacheTag 0x06
            go left
            go right
        ConjunctionLeftElimination conjunction -> do
            putCacheTag 0x07
            go conjunction
        ConjunctionRightElimination conjunction -> do
            putCacheTag 0x08
            go conjunction
        DisjunctionLeftIntroduction left right -> do
            putCacheTag 0x09
            go left
            putScoped right
        DisjunctionRightIntroduction left right -> do
            putCacheTag 0x0a
            putScoped left
            go right
        DisjunctionElimination disjunction leftBranch rightBranch -> do
            putCacheTag 0x0b
            go disjunction
            go leftBranch
            go rightBranch
        ExistentialIntroduction body witness premise -> do
            putCacheTag 0x0c
            putScoped body
            putScoped witness
            go premise
        ExistentialElimination existential result branch -> do
            putCacheTag 0x0d
            go existential
            putScoped result
            go branch
        ImplicationElimination implication premise -> do
            putCacheTag 0x0e
            go implication
            go premise
        ForallElimination quantified argument -> do
            putCacheTag 0x0f
            go quantified
            putScoped argument
        FalsumElimination falsum target -> do
            putCacheTag 0x10
            go falsum
            putScoped target
        ImplicationIntroduction premise body -> do
            putCacheTag 0x11
            putScoped premise
            go body
        ForallIntroduction binderType body -> do
            putCacheTag 0x12
            putCoreTypeCache binderType
            go body
        ConvertJudgement source target cost -> do
            putCacheTag 0x13
            go source
            putScoped target
            putCacheNatural
                (fromIntegral (Conversion.conversionCostAmount cost))
        EqualityReflexivity operand -> do
            putCacheTag 0x14
            putScoped operand
        EqualityCongruenceApplication function argument -> do
            putCacheTag 0x15
            go function
            go argument
        EqualityCongruenceLambda binderType body -> do
            putCacheTag 0x16
            putCoreTypeCache binderType
            go body
        EqualityModusPonens equality premise -> do
            putCacheTag 0x17
            go equality
            go premise
        ApplySetLfpBound domain operator -> do
            putCacheTag 0x18
            putScoped domain
            putScoped operator
        ApplySetLfpLeast domain operator candidate closed bounded -> do
            putCacheTag 0x19
            putScoped domain
            putScoped operator
            putScoped candidate
            go closed
            go bounded
        ApplySetLfpFixed domain operator monotone -> do
            putCacheTag 0x1a
            putScoped domain
            putScoped operator
            go monotone
        ApplySetLfpInduct
                domain operator predicate element monotone member closed -> do
            putCacheTag 0x1b
            putScoped domain
            putScoped operator
            putScoped predicate
            putScoped element
            go monotone
            go member
            go closed

    putScoped value = do
        putCacheList putCoreTypeCache (scopedCoreContext value)
        putCoreTypeCache (scopedCoreType value)
        putCanonicalTermCache putGlobal (scopedCoreTerm value)

importedFactDerivation
    :: ImportIx
    -> KernelDerivation global
importedFactDerivation =
    UseImportedFact

localHypothesisDerivation
    :: HypothesisIx
    -> KernelDerivation global
localHypothesisDerivation =
    UseLocalHypothesis

foundationFactDerivation
    :: FoundationAxiomTag
    -> KernelDerivation global
foundationFactDerivation =
    UseFoundationFact

truthIntroductionDerivation :: KernelDerivation global
truthIntroductionDerivation =
    TruthIntroduction

negationIntroductionDerivation
    :: ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
negationIntroductionDerivation =
    NegationIntroduction

negationEliminationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
negationEliminationDerivation =
    NegationElimination

conjunctionIntroductionDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
conjunctionIntroductionDerivation =
    ConjunctionIntroduction

conjunctionLeftEliminationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
conjunctionLeftEliminationDerivation =
    ConjunctionLeftElimination

conjunctionRightEliminationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
conjunctionRightEliminationDerivation =
    ConjunctionRightElimination

disjunctionLeftIntroductionDerivation
    :: KernelDerivation global
    -> ScopedCheckedCore global
    -> KernelDerivation global
disjunctionLeftIntroductionDerivation =
    DisjunctionLeftIntroduction

disjunctionRightIntroductionDerivation
    :: ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
disjunctionRightIntroductionDerivation =
    DisjunctionRightIntroduction

disjunctionEliminationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
disjunctionEliminationDerivation =
    DisjunctionElimination

existentialIntroductionDerivation
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
existentialIntroductionDerivation =
    ExistentialIntroduction

existentialEliminationDerivation
    :: KernelDerivation global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
existentialEliminationDerivation =
    ExistentialElimination

implicationEliminationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
implicationEliminationDerivation =
    ImplicationElimination

forallEliminationDerivation
    :: KernelDerivation global
    -> ScopedCheckedCore global
    -> KernelDerivation global
forallEliminationDerivation =
    ForallElimination

falsumEliminationDerivation
    :: KernelDerivation global
    -> ScopedCheckedCore global
    -> KernelDerivation global
falsumEliminationDerivation =
    FalsumElimination

implicationIntroductionDerivation
    :: ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
implicationIntroductionDerivation =
    ImplicationIntroduction

forallIntroductionDerivation
    :: CoreType
    -> KernelDerivation global
    -> KernelDerivation global
forallIntroductionDerivation =
    ForallIntroduction

equalityReflexivityDerivation
    :: FrozenCheckedCore global
    -> KernelDerivation global
equalityReflexivityDerivation =
    EqualityReflexivity . embedClosedCore []

scopedEqualityReflexivityDerivation
    :: ScopedCheckedCore global
    -> KernelDerivation global
scopedEqualityReflexivityDerivation =
    EqualityReflexivity

equalityCongruenceApplicationDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
equalityCongruenceApplicationDerivation =
    EqualityCongruenceApplication

equalityCongruenceLambdaDerivation
    :: CoreType
    -> KernelDerivation global
    -> KernelDerivation global
equalityCongruenceLambdaDerivation =
    EqualityCongruenceLambda

equalityModusPonensDerivation
    :: KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
equalityModusPonensDerivation =
    EqualityModusPonens

setLfpBoundDerivation
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
setLfpBoundDerivation =
    ApplySetLfpBound

setLfpLeastDerivation
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
setLfpLeastDerivation =
    ApplySetLfpLeast

setLfpFixedDerivation
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
setLfpFixedDerivation =
    ApplySetLfpFixed

setLfpInductDerivation
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
    -> KernelDerivation global
setLfpInductDerivation =
    ApplySetLfpInduct

-- | References actually present in a derivation.  This is a read-only summary,
-- not replay or source authority: the consumer must retain the producer's exact
-- import environment and proof-hypothesis association.
data KernelSourceUses = KernelSourceUses
    { kernelSourceImportUses :: !(Set ImportIx)
    , kernelSourceExternalHypothesisUses :: !(Set HypothesisIx)
    }
    deriving stock (Show, Eq)

-- | Charge one structural unit per visited proof node.  Proof binders hide
-- their own hypotheses; term binders leave hypothesis indices unchanged.
-- No term inspection, conversion or inference is performed.
countedKernelDerivationSourceUses
    :: Word
    -> KernelDerivation global
    -> (Maybe KernelSourceUses, Word)
countedKernelDerivationSourceUses available derivation =
    go available (KernelSourceUses Set.empty Set.empty) [(0, derivation)]
  where
    go remaining uses [] = (Just uses, remaining)
    go 0 _uses (_ : _) = (Nothing, 0)
    go remaining uses ((cutoff, current) : rest) =
        case current of
            UseImportedFact index ->
                continue uses
                    {kernelSourceImportUses = Set.insert index (kernelSourceImportUses uses)} []
            UseLocalHypothesis (HypothesisIx index)
                | index < cutoff -> continue uses []
                | otherwise -> continue uses
                    { kernelSourceExternalHypothesisUses =
                        Set.insert (HypothesisIx (index - cutoff))
                            (kernelSourceExternalHypothesisUses uses)
                    } []
            UseFoundationFact{} -> continue uses []
            TruthIntroduction -> continue uses []
            NegationIntroduction _premise body -> underHypothesis body
            NegationElimination premise negation -> children [premise, negation]
            ConjunctionIntroduction left right -> children [left, right]
            ConjunctionLeftElimination conjunction -> children [conjunction]
            ConjunctionRightElimination conjunction -> children [conjunction]
            DisjunctionLeftIntroduction left _right -> children [left]
            DisjunctionRightIntroduction _left right -> children [right]
            DisjunctionElimination source left right -> continue uses
                [(cutoff, source), (cutoff + 1, left), (cutoff + 1, right)]
            ExistentialIntroduction _body _witness premise -> children [premise]
            ExistentialElimination source _result body -> continue uses
                [(cutoff, source), (cutoff + 1, body)]
            ImplicationElimination implication premise -> children [implication, premise]
            ForallElimination quantified _argument -> children [quantified]
            FalsumElimination falsum _target -> children [falsum]
            ImplicationIntroduction _premise body -> underHypothesis body
            ForallIntroduction _binderType body -> children [body]
            ConvertJudgement source _target _cost -> children [source]
            EqualityReflexivity{} -> continue uses []
            EqualityCongruenceApplication function argument -> children [function, argument]
            EqualityCongruenceLambda _binderType body -> children [body]
            EqualityModusPonens equality premise -> children [equality, premise]
            ApplySetLfpBound{} -> continue uses []
            ApplySetLfpLeast _domain _operator _candidate bounded closed -> children [bounded, closed]
            ApplySetLfpFixed _domain _operator monotone -> children [monotone]
            ApplySetLfpInduct _domain _operator _predicate _element monotone member closed ->
                children [monotone, member, closed]
      where
        continue updated pending = go (remaining - 1) updated (pending <> rest)
        children proofs = continue uses [(cutoff, proof) | proof <- proofs]
        underHypothesis body = continue uses [(cutoff + 1, body)]

data KernelReplayLimits = KernelReplayLimits
    !Natural
    !Natural
    deriving stock (Show, Eq)

data KernelReplayLimitError
    = KernelReplayNodeLimitIsZero
    | KernelReplayNodeLimitTooLarge !Natural
    | KernelReplayDepthLimitTooLarge !Natural
    deriving stock (Show, Eq)

maximumKernelReplayNodes :: Natural
maximumKernelReplayNodes =
    1000000

maximumKernelReplayDepth :: Natural
maximumKernelReplayDepth =
    4096

kernelReplayLimits
    :: Natural
    -> Natural
    -> Either KernelReplayLimitError KernelReplayLimits
kernelReplayLimits nodeLimit depthLimit
    | nodeLimit == 0 =
        Left KernelReplayNodeLimitIsZero
    | nodeLimit > maximumKernelReplayNodes =
        Left (KernelReplayNodeLimitTooLarge nodeLimit)
    | depthLimit > maximumKernelReplayDepth =
        Left (KernelReplayDepthLimitTooLarge depthLimit)
    | otherwise =
        Right
            (KernelReplayLimits
                nodeLimit
                depthLimit)

defaultKernelReplayLimits :: KernelReplayLimits
defaultKernelReplayLimits =
    KernelReplayLimits
        200000
        2048

data ReplaySummary = ReplaySummary
    { summaryImportUses :: !(Set ImportIx)
    , summaryHypothesisUses :: !(Set HypothesisIx)
    , summaryFoundationUses :: !(Set FoundationAxiomTag)
    , summaryRuleUses :: !(Set KernelRuleTag)
    , summaryNodeCount :: !Natural
    , summaryMaximumDepth :: !Natural
    }
    deriving stock (Eq)

data ReplayedKernelDerivation global = ReplayedKernelDerivation
    !(FrozenCheckedCore global)
    !ReplaySummary
    deriving stock (Eq)

type role ReplayedKernelDerivation nominal

replayedKernelTarget :: ReplayedKernelDerivation global -> FrozenCheckedCore global
replayedKernelTarget (ReplayedKernelDerivation target _summary) = target

replayedKernelImportUses :: ReplayedKernelDerivation global -> Set ImportIx
replayedKernelImportUses (ReplayedKernelDerivation _target summary) = summaryImportUses summary

replayedKernelFoundationUses :: ReplayedKernelDerivation global -> Set FoundationAxiomTag
replayedKernelFoundationUses (ReplayedKernelDerivation _target summary) = summaryFoundationUses summary

replayedKernelRuleUses :: ReplayedKernelDerivation global -> Set KernelRuleTag
replayedKernelRuleUses (ReplayedKernelDerivation _target summary) = summaryRuleUses summary

-- Includes expanded conversion/transport nodes already visited by replay.
replayedKernelNodeCount :: ReplayedKernelDerivation global -> Natural
replayedKernelNodeCount (ReplayedKernelDerivation _target summary) = summaryNodeCount summary

replayedKernelMaximumDepth :: ReplayedKernelDerivation global -> Natural
replayedKernelMaximumDepth (ReplayedKernelDerivation _target summary) = summaryMaximumDepth summary

data ReplayedScopedKernelDerivation global = ReplayedScopedKernelDerivation
    !(ScopedCheckedCore global)
    !ReplaySummary
    deriving stock (Eq)

type role ReplayedScopedKernelDerivation nominal

replayedScopedKernelTarget :: ReplayedScopedKernelDerivation global -> ScopedCheckedCore global
replayedScopedKernelTarget (ReplayedScopedKernelDerivation target _summary) = target

replayedScopedKernelImportUses :: ReplayedScopedKernelDerivation global -> Set ImportIx
replayedScopedKernelImportUses (ReplayedScopedKernelDerivation _target summary) = summaryImportUses summary

replayedScopedKernelExternalHypothesisUses :: ReplayedScopedKernelDerivation global -> Set HypothesisIx
replayedScopedKernelExternalHypothesisUses (ReplayedScopedKernelDerivation _target summary) = summaryHypothesisUses summary

replayedScopedKernelFoundationUses :: ReplayedScopedKernelDerivation global -> Set FoundationAxiomTag
replayedScopedKernelFoundationUses (ReplayedScopedKernelDerivation _target summary) = summaryFoundationUses summary

replayedScopedKernelRuleUses :: ReplayedScopedKernelDerivation global -> Set KernelRuleTag
replayedScopedKernelRuleUses (ReplayedScopedKernelDerivation _target summary) = summaryRuleUses summary

-- Includes expanded conversion/transport nodes already visited by replay.
replayedScopedKernelNodeCount :: ReplayedScopedKernelDerivation global -> Natural
replayedScopedKernelNodeCount (ReplayedScopedKernelDerivation _target summary) = summaryNodeCount summary

replayedScopedKernelMaximumDepth :: ReplayedScopedKernelDerivation global -> Natural
replayedScopedKernelMaximumDepth (ReplayedScopedKernelDerivation _target summary) = summaryMaximumDepth summary

data ReplayStep global = ReplayStep
    { stepValue :: !(ScopedCheckedCore global)
    , stepSummary :: !ReplaySummary
    }

data ReplayHypothesis global = ReplayHypothesis
    !(Maybe HypothesisIx)
    !(ScopedCheckedCore global)

data KernelReplayError
    = KernelReplaySemanticsError
        !Semantics.KernelSemanticsError
    | KernelReplayConversionFailed !Conversion.ConversionFailure
    | KernelReplaySetLfpRuleError
        !SetLfp.SetLfpRuleError
    | KernelReplayImportOutOfBounds !ImportIx
    | KernelReplayHypothesisOutOfBounds !HypothesisIx
    | KernelReplayStoredContextMismatch
        ![CoreType]
        ![CoreType]
    | KernelReplayStoredTermIllTyped !CoreCheckError
    | KernelReplayStoredTypeMismatch
        !CoreType
        !CoreType
    | KernelReplayWeakeningError !CoreCheckError
    | KernelReplayNodeLimitExceeded !Natural
    | KernelReplayDepthLimitExceeded !Natural
    | KernelReplayRootRemainedOpen
    | KernelReplayTargetMismatch
    deriving stock (Show, Eq)

-- | Physical replay work, retained even when replay rejects the derivation.
-- Core work includes conversion. These counters confer no proof authority.
data ReplayWork = ReplayWork
    { replayWorkNodes :: !Natural
    , replayWorkDepth :: !Natural
    , replayWorkCore :: !Natural
    } deriving stock (Show, Eq)

data ReplayAccounting m = ReplayAccounting
    { replayNode :: Natural -> m ()
    , replayCore :: forall failure value. (failure -> KernelReplayError)
        -> Either failure value
        -> (Word -> (Either (CountedCoreFailure failure) value, Word))
        -> m value
    , replayConversionWork :: Word -> m ()
    }

ordinaryReplay :: ReplayAccounting (Either KernelReplayError)
ordinaryReplay = ReplayAccounting (const (pure ()))
    (\failure ordinary _counted -> first failure ordinary) (const (pure ()))

measuredReplay :: ReplayAccounting (Except.ExceptT KernelReplayError (State.State ReplayWork))
measuredReplay = ReplayAccounting node core conversion
  where
    node depth = State.modify' (\work -> work
        { replayWorkNodes = replayWorkNodes work + 1
        , replayWorkDepth = max depth (replayWorkDepth work) })
    core failure _ordinary counted = do
        let (result, remaining) = counted maxBound
        conversion (maxBound - remaining)
        case result of
            Right value -> pure value
            Left (CountedCoreOperationFailed problem) -> throwError (failure problem)
            Left CountedCoreStructuralWorkExhausted ->
                impossible "one replay operation exhausted the machine-word measurement range"
    conversion amount = State.modify' (\work -> work
        { replayWorkCore = replayWorkCore work + fromIntegral amount })

-- | Replay one closed provisional tree. Stored syntax is checked against the
-- current typing snapshot before the reconstructed conclusion is compared
-- with the expected target. Replay checks only imports reached by
-- 'UseImportedFact'; it does not authenticate their origin.
replayKernelDerivation
    :: Eq global
    => CheckedFoundation
    -> KernelReplayLimits
    -> GlobalTyping global
    -> Vector (DerivationImportJudgement global)
    -> FrozenCheckedCore global
    -> KernelDerivation global
    -> Either
        KernelReplayError
        (ReplayedKernelDerivation global)
replayKernelDerivation
        checkedFoundationValue
        limits
        globalType
        imports
        expectedTarget
        derivation = do
    replayed <-
        replayScopedKernelDerivation
            checkedFoundationValue
            limits
            globalType
            imports
            Vector.empty
            (embedClosedCore [] expectedTarget)
            derivation
    let ReplayedScopedKernelDerivation synthesized summary = replayed
    closed <-
        maybe
            (Left KernelReplayRootRemainedOpen)
            Right
            (closeScopedCore synthesized)
    pure (ReplayedKernelDerivation closed summary)

replayKernelDerivationMeasured
    :: Eq global => CheckedFoundation -> KernelReplayLimits -> GlobalTyping global
    -> Vector (DerivationImportJudgement global) -> FrozenCheckedCore global
    -> KernelDerivation global
    -> (Either KernelReplayError (ReplayedKernelDerivation global), ReplayWork)
replayKernelDerivationMeasured foundation limits globalType imports target derivation =
    let (result, work) = replayScopedKernelDerivationMeasured foundation limits globalType
            imports Vector.empty (embedClosedCore [] target) derivation
        close (ReplayedScopedKernelDerivation synthesized summary) =
            maybe (Left KernelReplayRootRemainedOpen)
                (\closed -> Right (ReplayedKernelDerivation closed summary)) (closeScopedCore synthesized)
    in (result >>= close, work)

replayScopedKernelDerivation
    :: Eq global
    => CheckedFoundation
    -> KernelReplayLimits
    -> GlobalTyping global
    -> Vector (DerivationImportJudgement global)
    -> Vector (ScopedCheckedCore global)
    -> ScopedCheckedCore global
    -> KernelDerivation global
    -> Either
        KernelReplayError
        (ReplayedScopedKernelDerivation global)
replayScopedKernelDerivation = replayScopedWith ordinaryReplay

replayScopedKernelDerivationMeasured
    :: Eq global => CheckedFoundation -> KernelReplayLimits -> GlobalTyping global
    -> Vector (DerivationImportJudgement global) -> Vector (ScopedCheckedCore global)
    -> ScopedCheckedCore global -> KernelDerivation global
    -> (Either KernelReplayError (ReplayedScopedKernelDerivation global), ReplayWork)
replayScopedKernelDerivationMeasured foundation limits globalType imports hypotheses target derivation =
    State.runState (Except.runExceptT
        (replayScopedWith measuredReplay foundation limits globalType imports hypotheses target derivation))
        (ReplayWork 0 0 0)

replayScopedWith
    :: forall global m. (Eq global, MonadError KernelReplayError m)
    => ReplayAccounting m -> CheckedFoundation -> KernelReplayLimits -> GlobalTyping global
    -> Vector (DerivationImportJudgement global) -> Vector (ScopedCheckedCore global)
    -> ScopedCheckedCore global -> KernelDerivation global
    -> m (ReplayedScopedKernelDerivation global)
replayScopedWith accounting
        checkedFoundationValue
        limits
        globalType
        imports
        externalHypotheses
        expectedTarget
        derivation =
    checkedFoundationValue `seq` do
        let lexicalContext = scopedCoreContext expectedTarget
        checkedHypotheses <-
            traverse
                (recheckStored lexicalContext)
                (Vector.toList externalHypotheses)
        let hypotheses = Seq.fromList $
                zipWith
                    (\index hypothesis ->
                        ReplayHypothesis
                            (Just
                                (hypothesisIx
                                    (fromIntegral (index :: Int))))
                            hypothesis)
                    [0..]
                    checkedHypotheses
        ReplayStep synthesized summary <-
            replay lexicalContext hypotheses 0 derivation
        same <- replayCore accounting absurd (Right (synthesized == expectedTarget))
            (\work -> countedScopedCoreIdentity work synthesized expectedTarget)
        unless same
            (throwError KernelReplayTargetMismatch)
        pure (ReplayedScopedKernelDerivation synthesized summary)
  where
    replay context hypotheses depth derivationNode
        | depth > replayDepthLimit =
            throwError
                (KernelReplayDepthLimitExceeded
                    replayDepthLimit)
        | otherwise = do
            replayNode accounting depth
            step <-
                replayWithin
                    context
                    hypotheses
                    depth
                    derivationNode
            if summaryNodeCount (stepSummary step) > replayNodeLimit
                then
                    throwError
                        (KernelReplayNodeLimitExceeded
                            replayNodeLimit)
                else
                    pure step

    replayWithin context hypotheses depth = \case
        UseImportedFact index -> do
            judgement <-
                lookupImport index
            statement <-
                recheckStored
                    context
                    (embedClosedCore context
                        (derivationImportStatement
                            judgement))
            pure
                (leaf
                    depth
                    statement
                    (Set.singleton index)
                    mempty
                    mempty)
        UseLocalHypothesis index -> do
            ReplayHypothesis externalIndex hypothesis <-
                lookupHypothesis index hypotheses
            -- This private environment contains only hypotheses checked at
            -- entry, at introduction, or after binder weakening. Reusing one
            -- in that identical context needs no further term validation.
            requireContext context hypothesis
            pure
                (leaf
                    depth
                    hypothesis
                    mempty
                    (foldMap Set.singleton externalIndex)
                    mempty)
        UseFoundationFact tag -> do
            statement <-
                recheckStored
                    context
                    (embedClosedCore context
                        (eliminateFrozenVoid
                            (foundationAxiomFrozen
                                checkedFoundationValue
                                tag)))
            pure
                (leaf
                    depth
                    statement
                    mempty
                    mempty
                    (Set.singleton tag))
        TruthIntroduction -> do
            value <-
                (rule1 (Semantics.truthIntroduction globalType) (Semantics.countedTruthIntroduction globalType)
                        context)
            pure (leaf depth value mempty mempty mempty)
        NegationIntroduction premise body -> do
            premise' <-
                recheckStored context premise
            bodyStep <-
                replay
                    context
                    (ReplayHypothesis Nothing premise' Seq.<| hypotheses)
                    (depth + 1)
                    body
            combine1 depth
                (rule2 (Semantics.negationIntroduction globalType) (Semantics.countedNegationIntroduction globalType)
                    premise'
                    (stepValue bodyStep))
                bodyStep
        NegationElimination premise negation -> do
            premiseStep <-
                replay context hypotheses (depth + 1) premise
            negationStep <-
                replay context hypotheses (depth + 1) negation
            combine2 depth
                (rule2 (Semantics.negationElimination globalType) (Semantics.countedNegationElimination globalType)
                    (stepValue premiseStep)
                    (stepValue negationStep))
                premiseStep
                negationStep
        ConjunctionIntroduction left right -> do
            leftStep <-
                replay context hypotheses (depth + 1) left
            rightStep <-
                replay context hypotheses (depth + 1) right
            combine2 depth
                (rule2 Semantics.conjunctionIntroduction (Semantics.countedConjunctionIntroduction)
                    (stepValue leftStep)
                    (stepValue rightStep))
                leftStep
                rightStep
        ConjunctionLeftElimination conjunction -> do
            conjunctionStep <-
                replay context hypotheses (depth + 1) conjunction
            combine1 depth
                (rule1 Semantics.conjunctionLeftElimination (Semantics.countedProjectConjunction True)
                    (stepValue conjunctionStep))
                conjunctionStep
        ConjunctionRightElimination conjunction -> do
            conjunctionStep <-
                replay context hypotheses (depth + 1) conjunction
            combine1 depth
                (rule1 Semantics.conjunctionRightElimination (Semantics.countedProjectConjunction False)
                    (stepValue conjunctionStep))
                conjunctionStep
        DisjunctionLeftIntroduction left right -> do
            right' <-
                recheckStored context right
            leftStep <-
                replay context hypotheses (depth + 1) left
            combine1 depth
                (rule2 (Semantics.disjunctionLeftIntroduction globalType) (Semantics.countedDisjunctionLeftIntroduction globalType)
                    (stepValue leftStep)
                    right')
                leftStep
        DisjunctionRightIntroduction left right -> do
            left' <-
                recheckStored context left
            rightStep <-
                replay context hypotheses (depth + 1) right
            combine1 depth
                (rule2 (Semantics.disjunctionRightIntroduction globalType) (Semantics.countedDisjunctionRightIntroduction globalType)
                    left'
                    (stepValue rightStep))
                rightStep
        DisjunctionElimination disjunction leftBranch rightBranch -> do
            disjunctionStep <-
                replay context hypotheses (depth + 1) disjunction
            (left, right) <-
                case scopedCoreTerm (stepValue disjunctionStep) of
                    COr left right ->
                        pure (left, right)
                    _ ->
                        throwError
                            (KernelReplaySemanticsError
                                Semantics.KernelExpectedDisjunction)
            leftHypothesis <-
                checkedTerm context left
            rightHypothesis <-
                checkedTerm context right
            leftStep <-
                replay
                    context
                    (ReplayHypothesis Nothing leftHypothesis Seq.<| hypotheses)
                    (depth + 1)
                    leftBranch
            rightStep <-
                replay
                    context
                    (ReplayHypothesis Nothing rightHypothesis Seq.<| hypotheses)
                    (depth + 1)
                    rightBranch
            combine3 depth
                (rule3 (Semantics.disjunctionElimination globalType) (Semantics.countedDisjunctionElimination globalType)
                    (stepValue disjunctionStep)
                    (stepValue leftStep)
                    (stepValue rightStep))
                disjunctionStep
                leftStep
                rightStep
        ExistentialIntroduction body witness premise -> do
            body' <-
                recheckStored
                    (scopedCoreContext body)
                    body
            witness' <-
                recheckStored context witness
            premiseStep <-
                replay context hypotheses (depth + 1) premise
            combine1 depth
                (rule3 (Semantics.existentialIntroduction globalType) (Semantics.countedExistentialIntroduction globalType)
                    body'
                    witness'
                    (stepValue premiseStep))
                premiseStep
        ExistentialElimination existential result branch -> do
            result' <-
                recheckStored context result
            existentialStep <-
                replay context hypotheses (depth + 1) existential
            (binderType, body) <-
                case scopedCoreTerm (stepValue existentialStep) of
                    CExists binderType body ->
                        pure (binderType, body)
                    _ ->
                        throwError
                            (KernelReplaySemanticsError
                                Semantics.KernelExpectedExists)
            let branchContext = binderType : context
            bodyHypothesis <-
                checkedTerm branchContext body
            weakenedHypotheses <-
                traverse (weakenReplayHypothesis binderType) hypotheses
            branchStep <-
                replay
                    branchContext
                    (ReplayHypothesis Nothing bodyHypothesis
                        Seq.<| weakenedHypotheses)
                    (depth + 1)
                    branch
            combine2 depth
                (rule3 (Semantics.existentialElimination globalType) (Semantics.countedExistentialElimination globalType)
                    (stepValue existentialStep)
                    result'
                    (stepValue branchStep))
                existentialStep
                branchStep
        ImplicationElimination implication premise -> do
            implicationStep <-
                replay context hypotheses (depth + 1) implication
            premiseStep <-
                replay context hypotheses (depth + 1) premise
            combine2 depth
                (rule2 Semantics.implicationElimination (Semantics.countedImplicationElimination)
                    (stepValue implicationStep)
                    (stepValue premiseStep))
                implicationStep
                premiseStep
        ForallElimination quantified argument -> do
            argument' <-
                recheckStored context argument
            quantifiedStep <-
                replay context hypotheses (depth + 1) quantified
            combine1 depth
                (rule2 Semantics.forallElimination (Semantics.countedForallElimination)
                    (stepValue quantifiedStep)
                    argument')
                quantifiedStep
        FalsumElimination falsum target -> do
            target' <-
                recheckStored context target
            falsumStep <-
                replay context hypotheses (depth + 1) falsum
            combine1 depth
                (rule2 (Semantics.falsumElimination globalType) (Semantics.countedFalsumElimination globalType)
                    (stepValue falsumStep)
                    target')
                falsumStep
        ImplicationIntroduction premise body -> do
            premise' <-
                recheckStored context premise
            bodyStep <-
                replay
                    context
                    (ReplayHypothesis Nothing premise' Seq.<| hypotheses)
                    (depth + 1)
                    body
            combine1 depth
                (rule2 Semantics.implicationIntroduction (Semantics.countedComposeImplication)
                    premise'
                    (stepValue bodyStep))
                bodyStep
        ForallIntroduction binderType body -> do
            weakenedHypotheses <-
                traverse (weakenReplayHypothesis binderType) hypotheses
            bodyStep <-
                replay
                    (binderType : context)
                    weakenedHypotheses
                    (depth + 1)
                    body
            combine1 depth
                (rule2 (Semantics.forallIntroduction globalType) (Semantics.countedForallIntroduction globalType)
                    binderType
                    (stepValue bodyStep))
                bodyStep
        ConvertJudgement source target cost -> do
            sourceStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    source
            let sourceValue = stepValue sourceStep
            unless (scopedCoreType sourceValue == TyProp)
                (throwError
                    (KernelReplaySemanticsError
                        (Semantics.KernelExpectedProposition
                            (scopedCoreType sourceValue))))
            let report = replayStoredConversionChecked globalType cost sourceValue target
            replayConversionWork accounting (Conversion.conversionCostAmount (Conversion.conversionCost report))
            decision <- liftReplay KernelReplayConversionFailed (Conversion.conversionResult report)
            case decision of
                Conversion.Convertible ->
                    combine1 depth (pure target) sourceStep
                Conversion.NotConvertible ->
                    throwError
                        (KernelReplayConversionFailed
                            (Conversion.ConversionInvariantFailure
                                Conversion.ConversionWitnessReplayMismatch))
        EqualityReflexivity operand -> do
            operand' <-
                recheckStored context operand
            value <-
                (rule1 Semantics.equalityReflexivity (Semantics.countedComposeReflexivity)
                        operand')
            pure (leaf depth value mempty mempty mempty)
        EqualityCongruenceApplication
                functionEquality
                argumentEquality -> do
            functionStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    functionEquality
            argumentStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    argumentEquality
            combine2 depth
                (rule2 Semantics.equalityCongruenceApplication (Semantics.countedComposeApplicationEquality)
                    (stepValue functionStep)
                    (stepValue argumentStep))
                functionStep
                argumentStep
        EqualityCongruenceLambda binderType bodyEquality -> do
            weakenedHypotheses <-
                traverse (weakenReplayHypothesis binderType) hypotheses
            bodyStep <-
                replay
                    (binderType : context)
                    weakenedHypotheses
                    (depth + 1)
                    bodyEquality
            combine1 depth
                (rule2 Semantics.equalityCongruenceLambda (Semantics.countedEqualityCongruenceLambda)
                    binderType
                    (stepValue bodyStep))
                bodyStep
        EqualityModusPonens equality premise -> do
            equalityStep <-
                replay context hypotheses (depth + 1) equality
            premiseStep <-
                replay context hypotheses (depth + 1) premise
            combine2 depth
                (rule2 Semantics.equalityModusPonens (Semantics.countedComposeEqualityModusPonens)
                    (stepValue equalityStep)
                    (stepValue premiseStep))
                equalityStep
                premiseStep
        ApplySetLfpBound domain operator -> do
            domain' <-
                recheckStored context domain
            operator' <-
                recheckStored context operator
            value <-
                liftReplay KernelReplaySetLfpRuleError
                    (SetLfp.setLfpBound
                        checkedFoundationValue
                        globalType
                        domain'
                        operator')
            pure
                (ruleLeaf
                    depth
                    SetLfpBound
                    value)
        ApplySetLfpLeast
                domain
                operator
                candidate
                closedPremise
                boundedPremise -> do
            domain' <-
                recheckStored context domain
            operator' <-
                recheckStored context operator
            candidate' <-
                recheckStored context candidate
            closedStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    closedPremise
            boundedStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    boundedPremise
            combineRule depth SetLfpLeast
                (SetLfp.setLfpLeast
                    checkedFoundationValue
                    globalType
                    domain'
                    operator'
                    candidate'
                    (stepValue closedStep)
                    (stepValue boundedStep))
                [closedStep, boundedStep]
        ApplySetLfpFixed domain operator monotonePremise -> do
            domain' <-
                recheckStored context domain
            operator' <-
                recheckStored context operator
            monotoneStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    monotonePremise
            combineRule depth SetLfpFixed
                (SetLfp.setLfpFixed
                    checkedFoundationValue
                    globalType
                    domain'
                    operator'
                    (stepValue monotoneStep))
                [monotoneStep]
        ApplySetLfpInduct
                domain
                operator
                predicate
                element
                monotonePremise
                memberPremise
                closurePremise -> do
            domain' <-
                recheckStored context domain
            operator' <-
                recheckStored context operator
            predicate' <-
                recheckStored context predicate
            element' <-
                recheckStored context element
            monotoneStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    monotonePremise
            memberStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    memberPremise
            closureStep <-
                replay
                    context
                    hypotheses
                    (depth + 1)
                    closurePremise
            combineRule depth SetLfpInduct
                (SetLfp.setLfpInduct
                    checkedFoundationValue
                    globalType
                    domain'
                    operator'
                    predicate'
                    element'
                    (stepValue monotoneStep)
                    (stepValue memberStep)
                    (stepValue closureStep))
                [ monotoneStep
                , memberStep
                , closureStep
                ]

    lookupImport index@(ImportIx naturalIndex)
        | naturalIndex
            > fromIntegral (maxBound :: Int) =
                throwError
                    (KernelReplayImportOutOfBounds
                        index)
        | otherwise =
            maybe
                (throwError
                    (KernelReplayImportOutOfBounds
                        index))
                pure
                (imports
                    Vector.!?
                        (fromIntegral naturalIndex))

    lookupHypothesis
            index@(HypothesisIx naturalIndex)
            hypotheses =
        maybe
            (throwError
                (KernelReplayHypothesisOutOfBounds
                    index))
            pure
            (if naturalIndex < fromIntegral (Seq.length hypotheses)
                then Seq.lookup (fromIntegral naturalIndex) hypotheses else Nothing)

    requireContext expected value = do
        same <- replayCore accounting absurd (Right (scopedCoreContext value == expected))
            (\work -> countedCoreTypeListIdentity work (scopedCoreContext value) expected)
        unless same (throwError (KernelReplayStoredContextMismatch expected (scopedCoreContext value)))

    checkedTerm context term = replayCore accounting KernelReplayStoredTermIllTyped
        (checkScopedCanonicalCore globalType context term)
        (\work -> countedCheckScopedCanonicalCore globalType work context term)

    recheckStored expectedContext stored = do
        requireContext expectedContext stored
        checked <- checkedTerm expectedContext (scopedCoreTerm stored)
        same <- replayCore accounting absurd (Right (scopedCoreType checked == scopedCoreType stored))
            (\work -> countedCoreTypeIdentity work (scopedCoreType checked) (scopedCoreType stored))
        unless same (throwError (KernelReplayStoredTypeMismatch (scopedCoreType stored) (scopedCoreType checked)))
        pure checked

    weakenReplayHypothesis binderType (ReplayHypothesis externalIndex statement) =
        ReplayHypothesis externalIndex <$> replayCore accounting KernelReplayWeakeningError
            (weakenScopedCore globalType binderType statement)
            (\work -> countedWeakenScopedCore globalType work binderType statement)

    rule1 :: (a -> Either Semantics.KernelSemanticsError value)
        -> (Word -> a -> (Either (CountedCoreFailure Semantics.KernelSemanticsError) value, Word))
        -> a -> m value
    rule1 ordinary counted a = replayCore accounting KernelReplaySemanticsError
        (ordinary a) (\work -> counted work a)
    rule2 :: (a -> b -> Either Semantics.KernelSemanticsError value)
        -> (Word -> a -> b -> (Either (CountedCoreFailure Semantics.KernelSemanticsError) value, Word))
        -> a -> b -> m value
    rule2 ordinary counted a b = replayCore accounting KernelReplaySemanticsError
        (ordinary a b) (\work -> counted work a b)
    rule3 :: (a -> b -> c -> Either Semantics.KernelSemanticsError value)
        -> (Word -> a -> b -> c -> (Either (CountedCoreFailure Semantics.KernelSemanticsError) value, Word))
        -> a -> b -> c -> m value
    rule3 ordinary counted a b c = replayCore accounting KernelReplaySemanticsError
        (ordinary a b c) (\work -> counted work a b c)

    replayNodeLimit =
        case limits of
            KernelReplayLimits nodeLimit _depthLimit ->
                nodeLimit

    replayDepthLimit =
        case limits of
            KernelReplayLimits _nodeLimit depthLimit ->
                depthLimit

leaf
    :: Natural
    -> ScopedCheckedCore global
    -> Set ImportIx
    -> Set HypothesisIx
    -> Set FoundationAxiomTag
    -> ReplayStep global
leaf depth value importUses hypothesisUses foundationUses =
    ReplayStep value (singleNodeSummary depth)
        { summaryImportUses = importUses
        , summaryHypothesisUses = hypothesisUses
        , summaryFoundationUses = foundationUses
        }

ruleLeaf :: Natural -> KernelRuleTag -> ScopedCheckedCore global -> ReplayStep global
ruleLeaf depth tag value =
    ReplayStep value (singleNodeSummary depth) { summaryRuleUses = Set.singleton tag }

singleNodeSummary :: Natural -> ReplaySummary
singleNodeSummary depth = ReplaySummary mempty mempty mempty mempty 1 depth

-- Depths are absolute traversal depths. The seed contains only this node's
-- contribution; children already include their replayed expansions.
replayNodeSummary :: ReplaySummary -> [ReplayStep global] -> ReplaySummary
replayNodeSummary = foldl' addChild
  where
    addChild own (ReplayStep _value child) = ReplaySummary
        { summaryImportUses = summaryImportUses own <> summaryImportUses child
        , summaryHypothesisUses = summaryHypothesisUses own <> summaryHypothesisUses child
        , summaryFoundationUses = summaryFoundationUses own <> summaryFoundationUses child
        , summaryRuleUses = summaryRuleUses own <> summaryRuleUses child
        , summaryNodeCount = summaryNodeCount own + summaryNodeCount child
        , summaryMaximumDepth = max (summaryMaximumDepth own) (summaryMaximumDepth child)
        }

combine1
    :: Monad m => Natural
    -> m (ScopedCheckedCore global)
    -> ReplayStep global
    -> m (ReplayStep global)
combine1 depth synthesized child = combine depth synthesized [child]

combine2
    :: Monad m => Natural
    -> m (ScopedCheckedCore global)
    -> ReplayStep global
    -> ReplayStep global
    -> m (ReplayStep global)
combine2 depth synthesized left right = combine depth synthesized [left, right]

combine3
    :: Monad m => Natural
    -> m (ScopedCheckedCore global)
    -> ReplayStep global
    -> ReplayStep global
    -> ReplayStep global
    -> m (ReplayStep global)
combine3 depth synthesized firstStep secondStep thirdStep =
    combine depth synthesized [firstStep, secondStep, thirdStep]

combine
    :: Monad m => Natural
    -> m (ScopedCheckedCore global)
    -> [ReplayStep global]
    -> m (ReplayStep global)
combine depth synthesized children = do
    value <- synthesized
    pure (ReplayStep value (replayNodeSummary (singleNodeSummary depth) children))

combineRule
    :: MonadError KernelReplayError m => Natural
    -> KernelRuleTag
    -> Either SetLfp.SetLfpRuleError (ScopedCheckedCore global)
    -> [ReplayStep global]
    -> m (ReplayStep global)
combineRule depth tag synthesized children = do
    value <- liftReplay KernelReplaySetLfpRuleError synthesized
    let own = (singleNodeSummary depth) { summaryRuleUses = Set.singleton tag }
    pure (ReplayStep value (replayNodeSummary own children))


liftReplay :: MonadError KernelReplayError m => (failure -> KernelReplayError) -> Either failure value -> m value
liftReplay failure = either (throwError . failure) pure
