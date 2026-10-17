{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Package-private derivation representation and preserving transformations.
-- Conversion sealing has its own private bridge; the facade owns other smart
-- construction, encoding and replay.
module Felix.Checking.Kernel.Derivation.Internal
    ( KernelDerivation(..)
    , ImportIx(..)
    , HypothesisIx(..)
    , eliminateKernelDerivationVoid
    , remapKernelDerivationImports
    , remapDerivationExternalHypotheses
    , weakenDerivationHypotheses
    , countedWeakenDerivationHypotheses
    ) where

import Base
import Felix.Checking.Core (CoreType, ScopedCheckedCore, eliminateScopedVoid)
import Felix.Checking.Foundation (FoundationAxiomTag)
import Felix.Checking.Kernel.Conversion (ConversionCost)

import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Data.Word (Word)
import Numeric.Natural (Natural)


newtype ImportIx = ImportIx Natural
    deriving stock (Show, Eq, Ord)

newtype HypothesisIx = HypothesisIx Natural
    deriving stock (Show, Eq, Ord)

data KernelDerivation global
    = UseImportedFact !ImportIx
    | UseLocalHypothesis !HypothesisIx
    | UseFoundationFact !FoundationAxiomTag
    | TruthIntroduction
    | NegationIntroduction
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | NegationElimination
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ConjunctionIntroduction
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ConjunctionLeftElimination
        !(KernelDerivation global)
    | ConjunctionRightElimination
        !(KernelDerivation global)
    | DisjunctionLeftIntroduction
        !(KernelDerivation global)
        !(ScopedCheckedCore global)
    | DisjunctionRightIntroduction
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | DisjunctionElimination
        !(KernelDerivation global)
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ExistentialIntroduction
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | ExistentialElimination
        !(KernelDerivation global)
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | ImplicationElimination
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ForallElimination
        !(KernelDerivation global)
        !(ScopedCheckedCore global)
    | FalsumElimination
        !(KernelDerivation global)
        !(ScopedCheckedCore global)
    | ImplicationIntroduction
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | ForallIntroduction
        !CoreType
        !(KernelDerivation global)
    | ConvertJudgement
        !(KernelDerivation global)
        !(ScopedCheckedCore global)
        !ConversionCost
    | EqualityReflexivity
        !(ScopedCheckedCore global)
    | EqualityCongruenceApplication
        !(KernelDerivation global)
        !(KernelDerivation global)
    | EqualityCongruenceLambda
        !CoreType
        !(KernelDerivation global)
    | EqualityModusPonens
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ApplySetLfpBound
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
    | ApplySetLfpLeast
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
        !(KernelDerivation global)
    | ApplySetLfpFixed
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
    | ApplySetLfpInduct
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(KernelDerivation global)
        !(KernelDerivation global)
        !(KernelDerivation global)
    deriving stock (Eq)

type role KernelDerivation nominal

-- | Eliminate the impossible global namespace of a closed derivation.
-- General transport of a derivation would also have to justify every checked
-- term embedded in the tree, so it is deliberately not provided.
eliminateKernelDerivationVoid
    :: KernelDerivation Void
    -> KernelDerivation global
eliminateKernelDerivationVoid = go
  where
    scoped = eliminateScopedVoid
    go = \case
        UseImportedFact index ->
            UseImportedFact index
        UseLocalHypothesis index ->
            UseLocalHypothesis index
        UseFoundationFact tag ->
            UseFoundationFact tag
        TruthIntroduction ->
            TruthIntroduction
        NegationIntroduction premise proof ->
            NegationIntroduction (scoped premise) (go proof)
        NegationElimination premise negation ->
            NegationElimination (go premise) (go negation)
        ConjunctionIntroduction left right ->
            ConjunctionIntroduction (go left) (go right)
        ConjunctionLeftElimination conjunction ->
            ConjunctionLeftElimination (go conjunction)
        ConjunctionRightElimination conjunction ->
            ConjunctionRightElimination (go conjunction)
        DisjunctionLeftIntroduction left right ->
            DisjunctionLeftIntroduction (go left) (scoped right)
        DisjunctionRightIntroduction left right ->
            DisjunctionRightIntroduction (scoped left) (go right)
        DisjunctionElimination disjunction leftBranch rightBranch ->
            DisjunctionElimination
                (go disjunction)
                (go leftBranch)
                (go rightBranch)
        ExistentialIntroduction body witness premise ->
            ExistentialIntroduction
                (scoped body)
                (scoped witness)
                (go premise)
        ExistentialElimination existential result branch ->
            ExistentialElimination
                (go existential)
                (scoped result)
                (go branch)
        ImplicationElimination premise implication ->
            ImplicationElimination (go premise) (go implication)
        ForallElimination proof argument ->
            ForallElimination (go proof) (scoped argument)
        FalsumElimination proof target ->
            FalsumElimination (go proof) (scoped target)
        ImplicationIntroduction premise proof ->
            ImplicationIntroduction (scoped premise) (go proof)
        ForallIntroduction binderType proof ->
            ForallIntroduction binderType (go proof)
        ConvertJudgement proof target cost ->
            ConvertJudgement (go proof) (scoped target) cost
        EqualityReflexivity term ->
            EqualityReflexivity (scoped term)
        EqualityCongruenceApplication function argument ->
            EqualityCongruenceApplication (go function) (go argument)
        EqualityCongruenceLambda binderType proof ->
            EqualityCongruenceLambda binderType (go proof)
        EqualityModusPonens equality proof ->
            EqualityModusPonens (go equality) (go proof)
        ApplySetLfpBound domain operator ->
            ApplySetLfpBound (scoped domain) (scoped operator)
        ApplySetLfpLeast domain operator candidate bounded closed ->
            ApplySetLfpLeast
                (scoped domain)
                (scoped operator)
                (scoped candidate)
                (go bounded)
                (go closed)
        ApplySetLfpFixed domain operator monotone ->
            ApplySetLfpFixed
                (scoped domain)
                (scoped operator)
                (go monotone)
        ApplySetLfpInduct domain operator predicate element
                monotone member closed ->
            ApplySetLfpInduct
                (scoped domain)
                (scoped operator)
                (scoped predicate)
                (scoped element)
                (go monotone)
                (go member)
                (go closed)

-- | Reindex the import leaves of a retained derivation.  Returning 'Nothing'
-- for a used leaf rejects the remapping; unused source imports are absent
-- from the tree and therefore need no entry.
remapKernelDerivationImports
    :: (ImportIx -> Maybe ImportIx)
    -> KernelDerivation global
    -> Maybe (KernelDerivation global)
remapKernelDerivationImports remap = go
  where
    go = \case
        UseImportedFact index ->
            UseImportedFact <$> remap index
        UseLocalHypothesis index ->
            pure (UseLocalHypothesis index)
        UseFoundationFact tag ->
            pure (UseFoundationFact tag)
        TruthIntroduction ->
            pure TruthIntroduction
        NegationIntroduction premise body ->
            NegationIntroduction premise <$> go body
        NegationElimination premise negation ->
            NegationElimination <$> go premise <*> go negation
        ConjunctionIntroduction left right ->
            ConjunctionIntroduction <$> go left <*> go right
        ConjunctionLeftElimination conjunction ->
            ConjunctionLeftElimination <$> go conjunction
        ConjunctionRightElimination conjunction ->
            ConjunctionRightElimination <$> go conjunction
        DisjunctionLeftIntroduction left right ->
            (`DisjunctionLeftIntroduction` right) <$> go left
        DisjunctionRightIntroduction left right ->
            DisjunctionRightIntroduction left <$> go right
        DisjunctionElimination disjunction leftBranch rightBranch ->
            DisjunctionElimination
                <$> go disjunction
                <*> go leftBranch
                <*> go rightBranch
        ExistentialIntroduction body witness premise ->
            ExistentialIntroduction body witness <$> go premise
        ExistentialElimination existential result branch ->
            ExistentialElimination
                <$> go existential
                <*> pure result
                <*> go branch
        ImplicationElimination implication premise ->
            ImplicationElimination <$> go implication <*> go premise
        ForallElimination quantified argument ->
            (`ForallElimination` argument) <$> go quantified
        FalsumElimination falsum target ->
            (`FalsumElimination` target) <$> go falsum
        ImplicationIntroduction premise body ->
            ImplicationIntroduction premise <$> go body
        ForallIntroduction binderType body ->
            ForallIntroduction binderType <$> go body
        ConvertJudgement source target cost ->
            ConvertJudgement <$> go source <*> pure target <*> pure cost
        EqualityReflexivity operand ->
            pure (EqualityReflexivity operand)
        EqualityCongruenceApplication function argument ->
            EqualityCongruenceApplication <$> go function <*> go argument
        EqualityCongruenceLambda binderType body ->
            EqualityCongruenceLambda binderType <$> go body
        EqualityModusPonens equality premise ->
            EqualityModusPonens <$> go equality <*> go premise
        ApplySetLfpBound domain operator ->
            pure (ApplySetLfpBound domain operator)
        ApplySetLfpLeast domain operator candidate closed bounded ->
            ApplySetLfpLeast domain operator candidate
                <$> go closed
                <*> go bounded
        ApplySetLfpFixed domain operator monotone ->
            ApplySetLfpFixed domain operator <$> go monotone
        ApplySetLfpInduct
                domain operator predicate element monotone member closed ->
            ApplySetLfpInduct domain operator predicate element
                <$> go monotone
                <*> go member
                <*> go closed

-- | Add hypotheses outside a derivation while preserving hypotheses introduced
-- by implication nodes inside it.
weakenDerivationHypotheses
    :: Natural
    -> KernelDerivation global
    -> KernelDerivation global
weakenDerivationHypotheses amount =
    shift 0
  where
    shift cutoff = \case
        UseImportedFact index ->
            UseImportedFact index
        UseLocalHypothesis (HypothesisIx index) ->
            UseLocalHypothesis
                (HypothesisIx
                    (if index >= cutoff
                        then index + amount
                        else index))
        UseFoundationFact tag ->
            UseFoundationFact tag
        TruthIntroduction ->
            TruthIntroduction
        NegationIntroduction premise body ->
            NegationIntroduction
                premise
                (shift (cutoff + 1) body)
        NegationElimination premise negation ->
            NegationElimination
                (shift cutoff premise)
                (shift cutoff negation)
        ConjunctionIntroduction left right ->
            ConjunctionIntroduction
                (shift cutoff left)
                (shift cutoff right)
        ConjunctionLeftElimination conjunction ->
            ConjunctionLeftElimination
                (shift cutoff conjunction)
        ConjunctionRightElimination conjunction ->
            ConjunctionRightElimination
                (shift cutoff conjunction)
        DisjunctionLeftIntroduction left right ->
            DisjunctionLeftIntroduction
                (shift cutoff left)
                right
        DisjunctionRightIntroduction left right ->
            DisjunctionRightIntroduction
                left
                (shift cutoff right)
        DisjunctionElimination disjunction leftBranch rightBranch ->
            DisjunctionElimination
                (shift cutoff disjunction)
                (shift (cutoff + 1) leftBranch)
                (shift (cutoff + 1) rightBranch)
        ExistentialIntroduction body witness premise ->
            ExistentialIntroduction
                body
                witness
                (shift cutoff premise)
        ExistentialElimination existential result branch ->
            ExistentialElimination
                (shift cutoff existential)
                result
                (shift (cutoff + 1) branch)
        ImplicationElimination implication premise ->
            ImplicationElimination
                (shift cutoff implication)
                (shift cutoff premise)
        ForallElimination quantified argument ->
            ForallElimination
                (shift cutoff quantified)
                argument
        FalsumElimination falsum target ->
            FalsumElimination
                (shift cutoff falsum)
                target
        ImplicationIntroduction premise body ->
            ImplicationIntroduction
                premise
                (shift (cutoff + 1) body)
        ForallIntroduction binderType body ->
            ForallIntroduction
                binderType
                (shift cutoff body)
        ConvertJudgement source target cost ->
            ConvertJudgement
                (shift cutoff source)
                target
                cost
        EqualityReflexivity operand ->
            EqualityReflexivity operand
        EqualityCongruenceApplication function argument ->
            EqualityCongruenceApplication
                (shift cutoff function)
                (shift cutoff argument)
        EqualityCongruenceLambda binderType body ->
            EqualityCongruenceLambda
                binderType
                (shift cutoff body)
        EqualityModusPonens equality premise ->
            EqualityModusPonens
                (shift cutoff equality)
                (shift cutoff premise)
        ApplySetLfpBound domain operator ->
            ApplySetLfpBound domain operator
        ApplySetLfpLeast
                domain operator candidate
                closed bounded ->
            ApplySetLfpLeast
                domain
                operator
                candidate
                (shift cutoff closed)
                (shift cutoff bounded)
        ApplySetLfpFixed domain operator monotone ->
            ApplySetLfpFixed
                domain
                operator
                (shift cutoff monotone)
        ApplySetLfpInduct
                domain operator predicate element
                monotone member closure ->
            ApplySetLfpInduct
                domain
                operator
                predicate
                element
                (shift cutoff monotone)
                (shift cutoff member)
                (shift cutoff closure)

countedWeakenDerivationHypotheses
    :: Word
    -> Natural
    -> KernelDerivation global
    -> (Maybe (KernelDerivation global), Word)
countedWeakenDerivationHypotheses available 0 derivation =
    (Just derivation, available)
countedWeakenDerivationHypotheses available amount derivation =
    case State.runStateT (shift 0 derivation) available of
        Nothing -> (Nothing, 0)
        Just (weakened, remaining) -> (Just weakened, remaining)
  where
    shift cutoff current = do
        consume
        case current of
            UseImportedFact index -> pure (UseImportedFact index)
            UseLocalHypothesis (HypothesisIx index) ->
                pure
                    (UseLocalHypothesis
                        (HypothesisIx
                            (if index >= cutoff
                                then index + amount
                                else index)))
            UseFoundationFact tag -> pure (UseFoundationFact tag)
            TruthIntroduction -> pure TruthIntroduction
            NegationIntroduction premise body ->
                NegationIntroduction premise
                    <$> shift (cutoff + 1) body
            NegationElimination premise negation ->
                NegationElimination
                    <$> shift cutoff premise
                    <*> shift cutoff negation
            ConjunctionIntroduction left right ->
                ConjunctionIntroduction
                    <$> shift cutoff left
                    <*> shift cutoff right
            ConjunctionLeftElimination conjunction ->
                ConjunctionLeftElimination
                    <$> shift cutoff conjunction
            ConjunctionRightElimination conjunction ->
                ConjunctionRightElimination
                    <$> shift cutoff conjunction
            DisjunctionLeftIntroduction left right ->
                (`DisjunctionLeftIntroduction` right)
                    <$> shift cutoff left
            DisjunctionRightIntroduction left right ->
                DisjunctionRightIntroduction left
                    <$> shift cutoff right
            DisjunctionElimination disjunction leftBranch rightBranch ->
                DisjunctionElimination
                    <$> shift cutoff disjunction
                    <*> shift (cutoff + 1) leftBranch
                    <*> shift (cutoff + 1) rightBranch
            ExistentialIntroduction body witness premise ->
                ExistentialIntroduction body witness
                    <$> shift cutoff premise
            ExistentialElimination existential result branch ->
                ExistentialElimination
                    <$> shift cutoff existential
                    <*> pure result
                    <*> shift (cutoff + 1) branch
            ImplicationElimination implication premise ->
                ImplicationElimination
                    <$> shift cutoff implication
                    <*> shift cutoff premise
            ForallElimination quantified argument ->
                (`ForallElimination` argument)
                    <$> shift cutoff quantified
            FalsumElimination falsum target ->
                (`FalsumElimination` target)
                    <$> shift cutoff falsum
            ImplicationIntroduction premise body ->
                ImplicationIntroduction premise
                    <$> shift (cutoff + 1) body
            ForallIntroduction binderType body ->
                ForallIntroduction binderType
                    <$> shift cutoff body
            ConvertJudgement source target cost ->
                (\source' -> ConvertJudgement source' target cost)
                    <$> shift cutoff source
            EqualityReflexivity operand ->
                pure (EqualityReflexivity operand)
            EqualityCongruenceApplication function argument ->
                EqualityCongruenceApplication
                    <$> shift cutoff function
                    <*> shift cutoff argument
            EqualityCongruenceLambda binderType body ->
                EqualityCongruenceLambda binderType
                    <$> shift cutoff body
            EqualityModusPonens equality premise ->
                EqualityModusPonens
                    <$> shift cutoff equality
                    <*> shift cutoff premise
            ApplySetLfpBound domain operator ->
                pure (ApplySetLfpBound domain operator)
            ApplySetLfpLeast domain operator candidate closed bounded ->
                ApplySetLfpLeast domain operator candidate
                    <$> shift cutoff closed
                    <*> shift cutoff bounded
            ApplySetLfpFixed domain operator monotone ->
                ApplySetLfpFixed domain operator
                    <$> shift cutoff monotone
            ApplySetLfpInduct
                    domain operator predicate element
                    monotone member closure ->
                ApplySetLfpInduct domain operator predicate element
                    <$> shift cutoff monotone
                    <*> shift cutoff member
                    <*> shift cutoff closure

    consume = do
        remaining <- State.get
        if remaining == 0
            then lift Nothing
            else State.put (remaining - 1)

-- | Reindex only the hypotheses supplied by the surrounding replay context.
-- Hypotheses introduced inside the derivation keep their local indices.
--
-- The callback sees an external index relative to that surrounding context;
-- the current introduction depth is removed before the callback and restored
-- afterwards.  This is the scope-safe operation needed when an independently
-- checked derivation is embedded into a larger external hypothesis vector.
remapDerivationExternalHypotheses
    :: (HypothesisIx -> HypothesisIx)
    -> KernelDerivation global
    -> KernelDerivation global
remapDerivationExternalHypotheses remap =
    go 0
  where
    go cutoff = \case
        UseImportedFact index ->
            UseImportedFact index
        UseLocalHypothesis (HypothesisIx index)
            | index < cutoff ->
                UseLocalHypothesis (HypothesisIx index)
            | otherwise ->
                let HypothesisIx mapped =
                        remap (HypothesisIx (index - cutoff))
                in UseLocalHypothesis (HypothesisIx (cutoff + mapped))
        UseFoundationFact tag ->
            UseFoundationFact tag
        TruthIntroduction ->
            TruthIntroduction
        NegationIntroduction premise body ->
            NegationIntroduction premise (go (cutoff + 1) body)
        NegationElimination premise negation ->
            NegationElimination
                (go cutoff premise)
                (go cutoff negation)
        ConjunctionIntroduction left right ->
            ConjunctionIntroduction
                (go cutoff left)
                (go cutoff right)
        ConjunctionLeftElimination conjunction ->
            ConjunctionLeftElimination (go cutoff conjunction)
        ConjunctionRightElimination conjunction ->
            ConjunctionRightElimination (go cutoff conjunction)
        DisjunctionLeftIntroduction left right ->
            DisjunctionLeftIntroduction (go cutoff left) right
        DisjunctionRightIntroduction left right ->
            DisjunctionRightIntroduction left (go cutoff right)
        DisjunctionElimination disjunction leftBranch rightBranch ->
            DisjunctionElimination
                (go cutoff disjunction)
                (go (cutoff + 1) leftBranch)
                (go (cutoff + 1) rightBranch)
        ExistentialIntroduction body witness premise ->
            ExistentialIntroduction body witness (go cutoff premise)
        ExistentialElimination existential result branch ->
            ExistentialElimination
                (go cutoff existential)
                result
                (go (cutoff + 1) branch)
        ImplicationElimination implication premise ->
            ImplicationElimination
                (go cutoff implication)
                (go cutoff premise)
        ForallElimination quantified argument ->
            ForallElimination (go cutoff quantified) argument
        FalsumElimination falsum target ->
            FalsumElimination (go cutoff falsum) target
        ImplicationIntroduction premise body ->
            ImplicationIntroduction premise (go (cutoff + 1) body)
        ForallIntroduction binderType body ->
            ForallIntroduction binderType (go cutoff body)
        ConvertJudgement source target cost ->
            ConvertJudgement (go cutoff source) target cost
        EqualityReflexivity operand ->
            EqualityReflexivity operand
        EqualityCongruenceApplication function argument ->
            EqualityCongruenceApplication
                (go cutoff function)
                (go cutoff argument)
        EqualityCongruenceLambda binderType body ->
            EqualityCongruenceLambda binderType (go cutoff body)
        EqualityModusPonens equality premise ->
            EqualityModusPonens
                (go cutoff equality)
                (go cutoff premise)
        ApplySetLfpBound domain operator ->
            ApplySetLfpBound domain operator
        ApplySetLfpLeast domain operator candidate closed bounded ->
            ApplySetLfpLeast
                domain operator candidate
                (go cutoff closed)
                (go cutoff bounded)
        ApplySetLfpFixed domain operator monotone ->
            ApplySetLfpFixed domain operator (go cutoff monotone)
        ApplySetLfpInduct
                domain operator predicate element
                monotone member closure ->
            ApplySetLfpInduct
                domain operator predicate element
                (go cutoff monotone)
                (go cutoff member)
                (go cutoff closure)
