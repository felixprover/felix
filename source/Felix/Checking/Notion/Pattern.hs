{-# LANGUAGE NoImplicitPrelude #-}

-- | Finite partial-request syntax over one frozen formation support domain.
-- Admission is not evidence and does not establish an anchor for a join.
module Felix.Checking.Notion.Pattern
    ( PatternVariable(..)
    , CanonicalPattern
    , canonicalPatternAtom
    , PatternRejection(..)
    , normalizeFormationPattern
    , normalizeFormationPatternWith
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Notion.Support
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)

data PatternVariable variable = Pinned !variable | Output !Natural
    deriving (Show, Eq, Ord)

-- No Ord instance: the relational table uses interned identities, not implicit
-- recursive comparison of full syntax. Only this module constructs the form.
newtype CanonicalPattern variable = CanonicalPattern
    { canonicalPatternAtom :: AtomTemplate (SetTermTemplate (PatternVariable variable)) }
    deriving (Show, Eq)

data PatternRejection = PatternSkeletonExceeded | PatternOutsideSupport
    deriving (Show, Eq)

-- | A placeholder needs at least one ground node. Bound each argument by the
-- largest supported term, then number outputs in first-occurrence order across
-- the whole atom. Repeated outputs retain their equality constraint. Only
-- maximal ground fragments need membership checks because support is closed
-- under subterms. Neither this operation nor its memo updates can reseed it.
--
-- The owning request supplies an aborting shared charge callback. Rejection is
-- separate from budget exhaustion in that outer effect. Constructor/head/type
-- associations and allowed atom arities are validated by the caller's snapshot.
normalizeFormationPattern
    :: (Monad m, Ord variable) => (Natural -> m ()) -> SymbolicSupport variable
    -> AtomTemplate (SetTermTemplate (PatternVariable variable))
    -> m (Either PatternRejection (CanonicalPattern variable, SymbolicSupport variable))
normalizeFormationPattern = normalizeFormationPatternWith Nothing

normalizeFormationPatternWith
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable)
    -> (Natural -> m ()) -> SymbolicSupport variable
    -> AtomTemplate (SetTermTemplate (PatternVariable variable))
    -> m (Either PatternRejection (CanonicalPattern variable, SymbolicSupport variable))
normalizeFormationPatternWith interpreter charge support source = Except.runExceptT do
    lift (charge 1)
    canonical <- State.evalStateT (traverseAtomTemplateArguments argument source) (bound, Map.empty, 0)
    collected <- traverseAtomTemplateArguments fragments canonical
    grounded <- foldM admit support (concatMap (\(_, collect) -> collect []) (atomTerms collected))
    final <- foldM admitPartial grounded
        [term | (term,(Nothing,_)) <- zip (atomTerms canonical) (atomTerms collected)]
    pure (CanonicalPattern canonical, final)
  where
    bound = symbolicSupportMaximumTermSize support
    argument term = do
        State.modify' (\(_, known, next) -> (bound, known, next))
        visit term
    visit term = do
        lift (lift (charge 1))
        (remaining, known, next) <- State.get
        when (remaining == 0) (lift (Except.throwE PatternSkeletonExceeded))
        State.put (remaining - 1, known, next)
        case term of
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateVariable (Pinned variable) -> pure (TemplateVariable (Pinned variable))
            TemplateVariable (Output variable) -> case Map.lookup variable known of
                Just canonical -> pure (TemplateVariable (Output canonical))
                Nothing -> do
                    State.put (remaining - 1, Map.insert variable next known, next + 1)
                    pure (TemplateVariable (Output next))
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse visit arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> visit left <*> visit right
    fragments term = do
        lift (charge 1)
        case term of
            TemplateClosed value -> pure (complete (TemplateClosed value))
            TemplateVariable (Pinned variable) -> pure (complete (TemplateVariable variable))
            TemplateVariable Output{} -> pure (Nothing, id)
            TemplateProvider provider arguments -> do
                parts <- traverse fragments arguments
                pure (combine (TemplateProvider provider <$> traverse fst parts) (snd <$> toList parts))
            TemplateOrderedPair left right -> do
                (a, first) <- fragments left
                (b, second) <- fragments right
                pure (combine (TemplateOrderedPair <$> a <*> b) [first,second])
    complete term = (Just term, (term :))
    combine (Just term) _ = complete term
    combine Nothing parts = (Nothing, foldr (.) id parts)
    admit current term = do
        (present, updated) <- lift (symbolicSupportContainsWith interpreter charge term current)
        unless present (Except.throwE PatternOutsideSupport)
        pure updated
    admitPartial current term = do
        let shape = fmap (\case Pinned value -> Just value; Output _ -> Nothing) term
        (possible, updated) <- lift (symbolicSupportMayContain charge shape current)
        unless possible (Except.throwE PatternOutsideSupport)
        pure updated
    atomTerms = toList
