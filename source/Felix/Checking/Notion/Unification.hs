{-# LANGUAGE NoImplicitPrelude #-}

-- | First-order constraints for formation producer activation and row joins.
-- This module supplies neither evidence, support admission, nor an anchor.
module Felix.Checking.Notion.Unification
    ( Substitution
    , emptySubstitution
    , pinnedSubstitution
    , unifyPatterns
    , unifyTerms
    , mayUnifyPartialTerm
    , matchCompleteRow
    , applyPatternSubstitution
    , applyTermSubstitution
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Core (compareCanonicalWith)
import Felix.Checking.Notion.Pattern (PatternVariable(..), PatternRejection(..))
import Control.Monad (foldM, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

type Term variable = SetTermTemplate (PatternVariable variable)

-- Only occurs-checked bindings can be installed. Keep aliases and compound
-- terms shared; matching dereferences roots rather than expanding both trees
-- at every comparison. There is deliberately no structural Ord instance.
newtype Substitution variable = Substitution (Map Natural (Term variable))

emptySubstitution :: Substitution variable
emptySubstitution = Substitution Map.empty

-- A partial support template has independent holes. Freshen them away from
-- the existing request outputs, then use the ordinary unifier as a Boolean
-- filter. The substitution is discarded: this supplies no argument view.
mayUnifyPartialTerm
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Term variable
    -> SetTermTemplate (Maybe variable) -> m Bool
mayUnifyPartialTerm charge pattern' candidate = do
    firstHole <- foldM (\next variable -> charge 1 >> pure (case variable of
        Pinned{} -> next
        Output index -> max next (index+1))) 0 (toList pattern')
    fresh <- State.evalStateT (prepare candidate) firstHole
    isJust <$> unifyTerms charge emptySubstitution [(pattern',fresh)]
  where
    prepare term = lift (charge 1) >> case term of
        TemplateVariable Nothing -> TemplateVariable <$> State.state (\index -> (Output index,index+1))
        TemplateVariable (Just value) -> pure (TemplateVariable (Pinned value))
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateProvider provider children -> TemplateProvider provider <$> traverse prepare children
        TemplateOrderedPair a b -> TemplateOrderedPair <$> prepare a <*> prepare b

-- Captured source terms contain no output slots and therefore cannot create
-- cyclic substitutions. They remain rigid throughout producer activation.
pinnedSubstitution
    :: Monad m => (Natural -> m ()) -> Map Natural (SetTermTemplate variable)
    -> m (Substitution variable)
pinnedSubstitution charge bindings = Substitution <$> traverse pin bindings
  where
    pin term = do
        charge 1
        case term of
            TemplateVariable value -> pure (TemplateVariable (Pinned value))
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse pin arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> pin left <*> pin right

root :: Monad m => (Natural -> m ()) -> Substitution variable -> Term variable -> m (Term variable)
root charge substitution@(Substitution bindings) term = do
    charge 1
    case term of
        TemplateVariable (Output index) -> case Map.lookup index bindings of
            Just replacement -> root charge substitution replacement
            Nothing -> pure term
        _ -> pure term

-- Callers freshen the query/rule output namespaces before producer matching.
-- A completed-row join uses the existing substitution, so every known column
-- and repeated output is checked against the same complete answer.
unifyPatterns
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Substitution variable
    -> AtomTemplate (Term variable) -> AtomTemplate (Term variable)
    -> m (Maybe (Substitution variable))
unifyPatterns charge initial left right = do
    charge 1
    case (left,right) of
        (NegativeAtomTemplate a,NegativeAtomTemplate b) -> unifyPatterns charge initial a b
        (GlobalAtomTemplate head' arguments, GlobalAtomTemplate other actual)
            | head' == other -> argumentsMatch arguments actual
        (StructureAtomTemplate head' arguments, StructureAtomTemplate other actual)
            | head' == other -> argumentsMatch arguments actual
        (MembershipAtomTemplate element set, MembershipAtomTemplate other domain) ->
            unifyTerms charge initial [(element,other),(set,domain)]
        (ExactStructureAtomTemplate shape subject, ExactStructureAtomTemplate other value)
            | shape == other -> unifyTerms charge initial [(subject,value)]
        _ -> pure Nothing
  where
    argumentsMatch arguments actual
        | Vector.length arguments /= Vector.length actual = pure Nothing
        | otherwise = do
            charge (fromIntegral (Vector.length arguments))
            unifyTerms charge initial (toList (Vector.zip arguments actual))
-- The same occurs-checked constraints serve row joins and finite parameter
-- assignments; enumeration does not invent a second instantiation semantics.
unifyTerms
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Substitution variable
    -> [(Term variable, Term variable)] -> m (Maybe (Substitution variable))
unifyTerms charge initial equations = solve initial equations
  where
    solve substitution [] = pure (Just substitution)
    solve substitution ((a,b) : rest) = do
        charge 1
        first <- root charge substitution a
        second <- root charge substitution b
        case (first,second) of
            (TemplateVariable (Output index), _) -> bind substitution index second rest
            (_, TemplateVariable (Output index)) -> bind substitution index first rest
            (TemplateClosed value,TemplateClosed other) -> do
                same <- compareCanonicalWith (charge 1) (closedSetValueTerm value) (closedSetValueTerm other)
                if same == EQ then solve substitution rest else pure Nothing
            (TemplateVariable (Pinned value), TemplateVariable (Pinned other))
                | value == other -> solve substitution rest
            (TemplateProvider provider arguments, TemplateProvider other actual)
                | provider == other, Vector.length arguments == Vector.length actual -> do
                    charge (fromIntegral (Vector.length arguments))
                    solve substitution (toList (Vector.zip arguments actual) <> rest)
            (TemplateOrderedPair x y, TemplateOrderedPair z w) -> solve substitution ((x,z) : (y,w) : rest)
            _ -> pure Nothing
    bind substitution index term rest = case term of
        TemplateVariable (Output other) | index == other -> solve substitution rest
        _ -> do
            cyclic <- occurs charge substitution index term
            if cyclic then pure Nothing else
                let Substitution bindings = substitution
                in solve (Substitution (Map.insert index term bindings)) rest

-- Visit each bound output at most once during the occurs check. This examines
-- the substitution graph without constructing its potentially expanded tree.
occurs :: Monad m => (Natural -> m ()) -> Substitution variable -> Natural -> Term variable -> m Bool
occurs charge (Substitution bindings) needle term = State.evalStateT (visit term) Set.empty
  where
    visit value = do
        lift (charge 1)
        case value of
            TemplateClosed{} -> pure False
            TemplateVariable (Pinned _) -> pure False
            TemplateVariable (Output index)
                | index == needle -> pure True
                | otherwise -> do
                    seen <- State.get
                    if Set.member index seen then pure False else do
                        State.put (Set.insert index seen)
                        maybe (pure False) visit (Map.lookup index bindings)
            TemplateProvider _ arguments -> anyChild (toList arguments)
            TemplateOrderedPair left right -> anyChild [left,right]
    anyChild [] = pure False
    anyChild (child : rest) = do
        found <- visit child
        if found then pure True else anyChild rest

applyPatternSubstitution
    :: Monad m => (Natural -> m ()) -> Natural -> Substitution variable -> AtomTemplate (Term variable)
    -> m (Either PatternRejection (AtomTemplate (Term variable)))
applyPatternSubstitution charge maximumSize substitution atom = Except.runExceptT do
    lift (charge 1)
    traverseAtomTemplateArguments (Except.ExceptT . applyTermSubstitution charge maximumSize substitution) atom

applyTermSubstitution
    :: Monad m => (Natural -> m ()) -> Natural -> Substitution variable -> Term variable
    -> m (Either PatternRejection (Term variable))
applyTermSubstitution charge maximumSize substitution term =
    Except.runExceptT (State.evalStateT (expand term) maximumSize)
  where
    -- The caller supplies its frozen support's bound. Reject before expanding
    -- the next node, rather than materializing a shared exponential tree and
    -- asking the pattern normalizer to discard it afterward.
    expand term = do
        lift (lift (charge 1))
        remaining <- State.get
        when (remaining == 0) (lift (Except.throwE PatternSkeletonExceeded))
        State.put (remaining - 1)
        resolved <- lift (lift (root charge substitution term))
        case resolved of
            TemplateClosed value -> pure (TemplateClosed value)
            variable@TemplateVariable{} -> pure variable
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse expand arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> expand left <*> expand right

matchCompleteRow
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Substitution variable
    -> AtomTemplate (Term variable) -> AtomTemplate (SetTermTemplate variable)
    -> m (Maybe (Substitution variable))
matchCompleteRow charge substitution pattern' row = do
    charge 1
    pinned <- traverseAtomTemplateArguments pin row
    unifyPatterns charge substitution pattern' pinned
  where
    pin term = do
        charge 1
        case term of
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateVariable variable -> pure (TemplateVariable (Pinned variable))
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse pin arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> pin left <*> pin right
