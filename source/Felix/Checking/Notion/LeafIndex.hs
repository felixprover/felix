{-# LANGUAGE NoImplicitPrelude #-}

-- | Scope-owned identities for whole opaque checked set terms. These keys are
-- syntax, not evidence. The owner must release the table at its nominal scope
-- boundary; equal binder-type lists do not establish equal lexical authority.
module Felix.Checking.Notion.LeafIndex
    ( OpaqueLeaf
    , OpaqueLeaves
    , OpaqueLeafFailure(..)
    , emptyOpaqueLeaves
    , extendOpaqueLeaves
    , internOpaqueLeaf
    , lookupOpaqueLeaf
    , countedLookupOpaqueLeaf
    ) where

import Base
import Control.Monad (unless)
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.TermIndex qualified as Terms
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Sequence qualified as Seq
import Data.Word (Word)
import Numeric.Natural (Natural)

newtype OpaqueLeaf = OpaqueLeaf Int
    deriving (Show, Eq, Ord)

-- Stable encounter-order IDs are separate from the sorted comparison index.
-- Both sequences retain the same checked values, without copying their syntax.
data OpaqueLeaves = OpaqueLeaves
    ![CoreType]
    !(Seq (CanonicalTerm (Either Natural ObjectId), OpaqueLeaf))
    !(Seq (ScopedCheckedCore ObjectId))

data OpaqueLeafFailure
    = OpaqueLeafScopeMismatch
    | OpaqueLeafNotSet
    | OpaqueLeafWorkExhausted
    deriving (Show, Eq)

emptyOpaqueLeaves :: [CoreType] -> OpaqueLeaves
emptyOpaqueLeaves context = OpaqueLeaves context Seq.empty Seq.empty

lookupOpaqueLeaf :: OpaqueLeaf -> OpaqueLeaves -> Maybe (ScopedCheckedCore ObjectId)
lookupOpaqueLeaf (OpaqueLeaf identifier) (OpaqueLeaves _ _ values) = Seq.lookup identifier values

-- The caller establishes nominal descent; this checks the corresponding type
-- prefix once. Stored terms retain their original contexts and encounter IDs.
extendOpaqueLeaves
    :: Word -> [CoreType] -> OpaqueLeaves
    -> (Either OpaqueLeafFailure OpaqueLeaves, Word)
extendOpaqueLeaves allowance context (OpaqueLeaves original sorted values) =
    State.runState (Except.runExceptT do
        charge (fromIntegral (length context + length original))
        let difference = length context - length original
        unless (difference >= 0) (Except.throwE OpaqueLeafScopeMismatch)
        same <- step (\work -> countedCoreTypeListIdentity work original (drop difference context))
        unless same (Except.throwE OpaqueLeafScopeMismatch)
        pure (OpaqueLeaves context sorted values)) allowance

countedLookupOpaqueLeaf
    :: Word -> OpaqueLeaf -> OpaqueLeaves
    -> (Either OpaqueLeafFailure (Maybe (ScopedCheckedCore ObjectId)), Word)
countedLookupOpaqueLeaf allowance identifier table@(OpaqueLeaves context _ values) =
    State.runState (Except.runExceptT do
        charge (Terms.indexWork (Seq.length values) 1)
        case lookupOpaqueLeaf identifier table of
            Nothing -> pure Nothing
            Just scoped -> step (\work -> countedAlignScopedCore work context scoped)) allowance

type LeafWork = Except.ExceptT OpaqueLeafFailure (State.State Word)

step :: (Word -> (Either (CountedCoreFailure Void) value, Word)) -> LeafWork value
step operation = do
    available <- State.get
    let (result, remaining) = operation available
    State.put remaining
    case result of
        Left CountedCoreStructuralWorkExhausted -> Except.throwE OpaqueLeafWorkExhausted
        Right value -> pure value

charge :: Natural -> LeafWork ()
charge amount = do
    available <- State.get
    if amount <= fromIntegral available
    then State.put (available - fromIntegral amount)
    else State.put 0 >> Except.throwE OpaqueLeafWorkExhausted

-- Scope/type rejection and exhaustion return no updated index. Sequence
-- navigation is charged separately from bounded structural Core comparisons.
internOpaqueLeaf
    :: Word -> ScopedCheckedCore ObjectId -> OpaqueLeaves
    -> (Either OpaqueLeafFailure (OpaqueLeaf, OpaqueLeaves), Word)
internOpaqueLeaf allowance term table@(OpaqueLeaves context sorted values) =
    State.runState (Except.runExceptT admit) allowance
  where
    navigation = Terms.indexWork (Seq.length sorted) 1
    admit = do
        charge 1
        sameScope <- step (\available -> countedCoreTypeListIdentity available context (scopedCoreContext term))
        unless sameScope (Except.throwE OpaqueLeafScopeMismatch)
        unless (scopedCoreType term == TySet) (Except.throwE OpaqueLeafNotSet)
        key <- step (\available -> countedScopedLevelKey available term)
        search key 0 (Seq.length sorted)
    search key lower upper
        | lower == upper = do
            charge (2 * navigation)
            let identifier = OpaqueLeaf (Seq.length values)
            pure (identifier, OpaqueLeaves context
                (Seq.insertAt lower (key, identifier) sorted) (values Seq.|> term))
        | otherwise = do
            charge navigation
            let middle = lower + (upper - lower) `div` 2
                -- The half-open interval is contained in the immutable index.
                (candidate, identifier) = Seq.index sorted middle
            ordering <- step (\available -> countedCanonicalOrdering available
                key candidate)
            case ordering of
                EQ -> pure (identifier, table)
                LT -> search key lower middle
                GT -> search key (middle + 1) upper
