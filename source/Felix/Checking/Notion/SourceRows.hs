{-# LANGUAGE NoImplicitPrelude #-}

-- | Encode an owner's admitted source view without manufacturing evidence.
-- Origins, alias replay, and the exact enclosing source remain with the owner.
module Felix.Checking.Notion.SourceRows (encodeSourceRow, encodeSourceTerm) where

import Base
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity(..))
import Data.Word (Word)
import Numeric.Natural (Natural)
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.LeafIndex qualified as Leaves
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as Source

encodeSourceRow
    :: Word
    -> [CoreType]
    -> Notion.SourceNotionOccurrence presentation
        (Source.SourceTermOccurrence termPresentation (ScopedCheckedCore ObjectId))
        (ScopedCheckedCore ObjectId)
    -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Source.SourceTemplateFailure)
        (AtomTemplate (SetTermTemplate Leaves.OpaqueLeaf), Leaves.OpaqueLeaves), Word)
encodeSourceRow allowance context assertion initial =
    let (same, remaining) = countedCoreTypeListIdentity allowance context
            (scopedCoreContext (Notion.sourceAssertionFormula assertion))
    in case same of
        Left failure -> (Left (fmap absurd failure), remaining)
        Right False -> (Left (CountedCoreOperationFailed Source.SourceTemplateScopeMismatch), remaining)
        Right True -> encodeSourceTerms remaining context (Notion.sourceAssertionAtom assertion) initial

encodeSourceTerm
    :: Word -> [CoreType]
    -> Source.SourceTermOccurrence presentation (ScopedCheckedCore ObjectId)
    -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Source.SourceTemplateFailure)
        (SetTermTemplate Leaves.OpaqueLeaf, Leaves.OpaqueLeaves), Word)
encodeSourceTerm allowance context occurrence initial =
    let (result, remaining) = encodeSourceTerms allowance context (Identity occurrence) initial
    in (first runIdentity <$> result, remaining)

encodeSourceTerms
    :: Traversable terms => Word -> [CoreType]
    -> terms (Source.SourceTermOccurrence presentation (ScopedCheckedCore ObjectId))
    -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Source.SourceTemplateFailure)
        (terms (SetTermTemplate Leaves.OpaqueLeaf), Leaves.OpaqueLeaves), Word)
encodeSourceTerms allowance context occurrences initial =
    let (result, (remaining, leaves)) = State.runState (Except.runExceptT encode) (allowance, initial)
    in (fmap (\row -> (row, leaves)) result, remaining)
  where
    step :: (Word -> (Either (CountedCoreFailure Void) value, Word))
        -> Except.ExceptT (CountedCoreFailure Source.SourceTemplateFailure)
            (State.State (Word, Leaves.OpaqueLeaves)) value
    step operation = do
        (available, leaves) <- State.get
        let (result, remaining) = operation available
        State.put (remaining, leaves)
        either (Except.throwE . fmap absurd) pure result
    charge :: Natural -> Except.ExceptT (CountedCoreFailure Source.SourceTemplateFailure)
        (State.State (Word, Leaves.OpaqueLeaves)) ()
    charge amount = step \available ->
        if amount <= fromIntegral available
        then (Right (), available - fromIntegral amount)
        else (Left CountedCoreStructuralWorkExhausted, 0)
    reject = Except.throwE . CountedCoreOperationFailed
    equalContexts left right = step (\available -> countedCoreTypeListIdentity available left right)
    intern core = do
        (available, leaves) <- State.get
        let (result, remaining) = Leaves.internOpaqueLeaf available core leaves
        State.put (remaining, leaves)
        case result of
            Left Leaves.OpaqueLeafWorkExhausted -> Except.throwE CountedCoreStructuralWorkExhausted
            Left Leaves.OpaqueLeafScopeMismatch -> reject Source.SourceTemplateScopeMismatch
            Left Leaves.OpaqueLeafNotSet -> reject Source.SourceTemplateNotSet
            Right (identifier, next) -> State.put (remaining, next) >> pure identifier
    term occurrence = Source.encodeScopedSourceTemplate charge equalContexts context intern occurrence
        >>= either reject pure
    encode = do
        charge 1
        traverse term occurrences
