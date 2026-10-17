{-# LANGUAGE NoImplicitPrelude #-}

-- | First-order producer activation and complete-row join transitions. The owner
-- selects admitted rule associations, schedules every legal pending premise,
-- retains its proof witnesses, and checks support when interning requests.
module Felix.Checking.Notion.Join
    ( JoinState
    , JoinPremise
    , JoinFailure(..)
    , RowCapability(..)
    , startJoin
    , startCapturedJoin
    , startWholeJoin
    , bindJoinVariable
    , startGroundJoin
    , prepareJoinPremise
    , joinPremisePattern
    , joinPremiseIsGround, joinPremiseBindings
    , resumeJoinPremise
    , joinSubstitution
    , JoinInstantiation(..)
    , instantiateJoin
    , joinVariableValues, joinVariablePattern, instantiateJoinVariables
    , matchSourceParameters
    , instantiateSourceRule
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Notion.Pattern
import Felix.Checking.Notion.Unification
import Control.Monad (foldM, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)

data JoinState variable = JoinState
    { joinArity :: !Natural
    , joinSubstitution :: !(Substitution variable)
    , joinConclusion :: !(NotionLeaf (AtomTemplate (SetTermTemplate (PatternVariable variable))) ResidualTemplate)
    }

data JoinPremise variable = JoinPremise
    { joinPremisePattern :: !(AtomTemplate (SetTermTemplate (PatternVariable variable)))
    , joinPremiseIsGround :: !Bool
    -- Per operand: completely determined, contains a pinned parameter.
    , joinPremiseBindings :: ![(Bool,Bool)]
    , premiseState :: !(JoinState variable)
    }

data JoinFailure
    = JoinInvalidVariable !Natural
    | JoinPatternRejected !PatternRejection
    | JoinSourceShapeRequired
    | JoinUndeterminedVariable !Natural
    | JoinInvalidForwardSource
    | JoinWholeConclusionUndetermined
    | JoinUnresolvedResult
    deriving (Show, Eq)

data RowCapability = SourceRow | ExactAnswer
    deriving (Show, Eq)

startJoin
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> Natural
    -> AtomTemplate RuleTermTemplate -> CanonicalPattern variable
    -> m (Either JoinFailure (Maybe (JoinState variable)))
startJoin charge maximumSize arity conclusion requested =
    startCapturedJoin charge maximumSize arity Map.empty conclusion requested

startCapturedJoin
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> Natural
    -> Map ViewVariableIx (SetTermTemplate variable)
    -> AtomTemplate RuleTermTemplate -> CanonicalPattern variable
    -> m (Either JoinFailure (Maybe (JoinState variable)))
startCapturedJoin charge maximumSize arity captures conclusion requested = Except.runExceptT do
    indexed <- traverse (\(ViewVariableIx index, term) -> do
        lift (charge 1)
        when (index >= arity) (Except.throwE (JoinInvalidVariable index))
        pure (index, term)) (Map.toAscList captures)
    initial <- lift (pinnedSubstitution charge (Map.fromDistinctAscList indexed))
    Except.ExceptT (startPatternJoin charge maximumSize arity initial conclusion (canonicalPatternAtom requested))

-- Ground requests use only their own seed subterms. Their rule instances are
-- admitted without enumerating the larger template closure.
startGroundJoin
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> Natural
    -> AtomTemplate RuleTermTemplate -> AtomTemplate (SetTermTemplate variable)
    -> m (Either JoinFailure (Maybe (JoinState variable)))
startGroundJoin charge maximumSize arity conclusion requested = do
    pinned <- traverseAtomTemplateArguments (mapTerm charge (pure . Pinned)) requested
    startPatternJoin charge maximumSize arity emptySubstitution conclusion pinned

startPatternJoin
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> Natural
    -> Substitution variable -> AtomTemplate RuleTermTemplate -> AtomTemplate (SetTermTemplate (PatternVariable variable))
    -> m (Either JoinFailure (Maybe (JoinState variable)))
startPatternJoin charge maximumSize arity initial conclusion requested = Except.runExceptT do
    prepared <- rulePattern charge arity conclusion
    -- Rule binders occupy [0,arity); request outputs occupy the disjoint suffix.
    fresh <- traverseAtomTemplateArguments (mapTerm (lift . charge) (pure . \case
        Pinned value -> Pinned value
        Output index -> Output (index + arity))) requested
    candidate <- lift (unifyPatterns charge initial prepared fresh)
    traverse (\substitution -> do
        _ <- apply charge maximumSize substitution prepared
        pure (JoinState arity substitution (AtomicLeaf prepared))) candidate

-- Conditional instantiation only: the rule owner must still account for every
-- premise and replay the selected theorem with these exact binder values.
data JoinInstantiation variable = JoinInstantiation
    { joinBinderValues :: !(Map ViewVariableIx (SetTermTemplate variable))
    , joinResultLeaf :: !(NotionLeaf (AtomTemplate (SetTermTemplate variable)) ResidualTemplate)
    }
    deriving (Show, Eq)

instantiateJoin
    :: Monad m => (Natural -> m ()) -> Natural -> JoinState variable
    -> m (Either JoinFailure (JoinInstantiation variable))
instantiateJoin charge maximumSize state = instantiateSubstitution charge maximumSize
    (joinArity state) (joinSubstitution state) (joinConclusion state)

-- Private component plans inspect only their own parameters. Missing values
-- remain unresolved; this operation supplies no proof and never guesses one.
joinVariableValues
    :: Monad m => (Natural -> m ()) -> Natural -> [ViewVariableIx] -> JoinState variable
    -> m (Either JoinFailure (Map ViewVariableIx (Maybe (SetTermTemplate variable))))
joinVariableValues charge maximumSize slots state = Except.runExceptT $
    Map.fromDistinctAscList <$> traverse (\slot@(ViewVariableIx index) -> do
        lift (charge 1)
        value <- Except.ExceptT (first JoinPatternRejected <$>
            applyTermSubstitution charge maximumSize (joinSubstitution state) (TemplateVariable (Output index)))
        (\grounded -> (slot,grounded)) <$> groundTerm charge value) slots

-- Retain known constructors when a parameter still contains request outputs.
-- Enumeration can reject incompatible templates before visiting assignments.
joinVariablePattern
    :: Monad m => (Natural -> m ()) -> Natural -> Natural -> JoinState variable
    -> m (Either JoinFailure (SetTermTemplate (PatternVariable variable)))
joinVariablePattern charge maximumSize slot state = first JoinPatternRejected <$>
    applyTermSubstitution charge maximumSize (joinSubstitution state) (TemplateVariable (Output slot))

instantiateJoinVariables
    :: Monad m => (Natural -> m ()) -> Natural -> [ViewVariableIx] -> JoinState variable
    -> m (Either JoinFailure (Map ViewVariableIx (SetTermTemplate variable)))
instantiateJoinVariables charge bound slots state = Except.runExceptT do
    values <- Except.ExceptT (joinVariableValues charge bound slots state)
    Map.traverseWithKey (\(ViewVariableIx index) ->
        maybe (Except.throwE (JoinUndeterminedVariable index)) pure) values

-- Forward views match actual source operands; no requested conclusion is used
-- to determine a binder or to manufacture a premise.
instantiateSourceRule
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> Natural
    -> AtomTemplate RuleTermTemplate -> AtomTemplate RuleTermTemplate
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either JoinFailure (Maybe (JoinInstantiation variable)))
instantiateSourceRule charge maximumSize arity source conclusion row = Except.runExceptT do
    pattern' <- rulePattern charge arity source
    prepared <- rulePattern charge arity conclusion
    candidate <- lift (matchCompleteRow charge emptySubstitution pattern' row)
    traverse (\substitution -> Except.ExceptT
        (instantiateSubstitution charge maximumSize arity substitution (AtomicLeaf prepared))) candidate

instantiateSubstitution
    :: Monad m => (Natural -> m ()) -> Natural -> Natural -> Substitution variable
    -> NotionLeaf (AtomTemplate (SetTermTemplate (PatternVariable variable))) ResidualTemplate
    -> m (Either JoinFailure (JoinInstantiation variable))
instantiateSubstitution charge maximumSize arity substitution conclusion = Except.runExceptT do
    bindings <- instantiateBindings charge maximumSize arity substitution
    result <- case conclusion of
        WholeLeaf residual -> pure (WholeLeaf residual)
        AtomicLeaf pattern' -> do
            instantiated <- apply charge maximumSize substitution pattern'
            grounded <- traverseAtomTemplateArguments (groundTerm charge) instantiated
            maybe (Except.throwE JoinUnresolvedResult) (pure . AtomicLeaf) (sequence grounded)
    pure (JoinInstantiation bindings result)

-- Whole heads constrain truth only. Relational premises collectively determine
-- their parameters; fixed captures use the same substitution as atomic rules.
startWholeJoin
    :: Monad m => (Natural -> m ()) -> Natural
    -> Map ViewVariableIx (SetTermTemplate variable) -> ResidualTemplate
    -> m (JoinState variable)
startWholeJoin charge arity captures conclusion = do
    initial <- pinnedSubstitution charge (Map.fromList [(index,value) | (ViewVariableIx index,value) <- Map.toList captures])
    pure (JoinState arity initial (WholeLeaf conclusion))

bindJoinVariable
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> SetTermTemplate variable
    -> JoinState variable -> m (Maybe (JoinState variable))
bindJoinVariable charge index value state = do
    pinned <- mapTerm charge (pure . Pinned) value
    candidate <- unifyTerms charge (joinSubstitution state) [(TemplateVariable (Output index),pinned)]
    pure ((\substitution -> state {joinSubstitution = substitution}) <$> candidate)

matchSourceParameters
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> Natural
    -> AtomTemplate RuleTermTemplate -> AtomTemplate (SetTermTemplate variable)
    -> m (Either JoinFailure (Maybe (Map ViewVariableIx (SetTermTemplate variable))))
matchSourceParameters charge maximumSize arity source row = Except.runExceptT do
    pattern' <- rulePattern charge arity source
    candidate <- lift (matchCompleteRow charge emptySubstitution pattern' row)
    traverse (instantiateBindings charge maximumSize arity) candidate

instantiateBindings
    :: Monad m => (Natural -> m ()) -> Natural -> Natural -> Substitution variable
    -> Except.ExceptT JoinFailure m (Map ViewVariableIx (SetTermTemplate variable))
instantiateBindings charge maximumSize arity substitution = gather 0 Map.empty
  where
    -- Walk observed work, never allocate a range from the declared arity.
    gather index known
        | index == arity = pure known
        | otherwise = do
            lift (charge 1)
            value <- Except.ExceptT (first JoinPatternRejected <$>
                applyTermSubstitution charge maximumSize substitution (TemplateVariable (Output index)))
            actual <- groundTerm charge value
            case actual of
                Nothing -> Except.throwE (JoinUndeterminedVariable index)
                Just term -> gather (index + 1) (Map.insert (ViewVariableIx index) term known)

groundTerm
    :: Monad m => (Natural -> m ()) -> SetTermTemplate (PatternVariable variable)
    -> Except.ExceptT JoinFailure m (Maybe (SetTermTemplate variable))
groundTerm charge term = do
    lift (charge 1)
    case term of
        TemplateClosed value -> pure (Just (TemplateClosed value))
        TemplateVariable (Pinned value) -> pure (Just (TemplateVariable value))
        TemplateVariable Output{} -> pure Nothing
        TemplateProvider provider arguments -> fmap (TemplateProvider provider) . sequence <$> traverse (groundTerm charge) arguments
        TemplateOrderedPair left right -> liftA2 TemplateOrderedPair <$> groundTerm charge left <*> groundTerm charge right

prepareJoinPremise
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> JoinState variable
    -> AtomTemplate RuleTermTemplate -> m (Either JoinFailure (JoinPremise variable))
prepareJoinPremise charge maximumSize state premise = Except.runExceptT do
    pattern' <- rulePattern charge (joinArity state) premise
    instantiated <- apply charge maximumSize (joinSubstitution state) pattern'
    bindings <- traverse (binding . toList) instantiated
    pure (JoinPremise instantiated (all fst bindings) (toList bindings) state)
  where
    -- Retain pins inside a partial operand, such as (b, ?y). Discarding these
    -- anchors makes a recursive membership join look wholly unconstrained.
    binding = foldM (\(grounded,anchored) variable -> do
        lift (charge 1)
        pure $ case variable of
            Output{} -> (False,anchored)
            Pinned{} -> (grounded,True)) (True,False)

-- A denotation-only answer can discharge a ground guard, but cannot reveal
-- source operands for unknown outputs. The supplied row must already be a
-- checked complete answer; this transition itself creates no proof authority.
resumeJoinPremise
    :: (Monad m, Ord variable) => (Natural -> m ()) -> RowCapability
    -> JoinPremise variable -> AtomTemplate (SetTermTemplate variable)
    -> m (Either JoinFailure (Maybe (JoinState variable)))
resumeJoinPremise charge capability premise row = do
    charge 1
    if capability == ExactAnswer && not (joinPremiseIsGround premise) then pure (Left JoinSourceShapeRequired) else do
        let state = premiseState premise
        candidate <- matchCompleteRow charge (joinSubstitution state) (joinPremisePattern premise) row
        pure (Right ((\substitution -> state {joinSubstitution = substitution}) <$> candidate))

rulePattern
    :: Monad m => (Natural -> m ()) -> Natural -> AtomTemplate RuleTermTemplate
    -> Except.ExceptT JoinFailure m (AtomTemplate (SetTermTemplate (PatternVariable variable)))
rulePattern charge arity = traverseAtomTemplateArguments (mapTerm (lift . charge) (\(ViewVariableIx index) ->
    if index < arity then pure (Output index) else Except.throwE (JoinInvalidVariable index)))

apply
    :: Monad m => (Natural -> m ()) -> Natural -> Substitution variable
    -> AtomTemplate (SetTermTemplate (PatternVariable variable))
    -> Except.ExceptT JoinFailure m (AtomTemplate (SetTermTemplate (PatternVariable variable)))
apply charge maximumSize substitution pattern' = Except.ExceptT
    (first JoinPatternRejected <$> applyPatternSubstitution charge maximumSize substitution pattern')

mapTerm :: Monad m => (Natural -> m ()) -> (a -> m b) -> SetTermTemplate a -> m (SetTermTemplate b)
mapTerm charge variable term = do
    charge 1
    case term of
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateVariable value -> TemplateVariable <$> variable value
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse (mapTerm charge variable) arguments
        TemplateOrderedPair left right -> TemplateOrderedPair <$> mapTerm charge variable left <*> mapTerm charge variable right
