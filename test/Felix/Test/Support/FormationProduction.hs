{-# LANGUAGE NoImplicitPrelude #-}

-- Production scheduling with fixture-owned eligibility keys and replay recipes.
-- The independent reference interpreter does not call this adapter.
module Felix.Test.Support.FormationProduction
    ( evaluateProduction, prepareProductionSupport, atomicEvaluator, atomicAnswer, completedAtom, freeTermsMayAgree ) where

import Base
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Data.Word (Word)
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Notion.Composite qualified as Composite
import Felix.Checking.Notion.Catalog qualified as Catalog
import Felix.Checking.Notion.Evaluation qualified as Evaluation
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Notion.Join qualified as Join
import Felix.Checking.Notion.Relational qualified as Relational
import Felix.Checking.Notion.Rule qualified as Rule
import Felix.Checking.Notion.Support qualified as Support
import Felix.Test.Support.FormationReference qualified as Reference
import Numeric.Natural (Natural)

-- Atomic fixtures do not need a formula owner. Whole-fragment comparisons
-- supply their own checked formula identities and adapter callbacks.
atomicEvaluator
    :: Monad m => (Natural -> m (Rule.RuleInputs variable)) -> (Natural -> m ())
    -> (Semantic.AtomTemplate (Semantic.SetTermTemplate variable) -> m bucket)
    -> (Text -> m ()) -> (Diagnostics.RuleEvent -> m ())
    -> (Natural -> Rule.CompletedRule variable witness -> m (Maybe (key, witness)))
    -> (Semantic.AtomTemplate (Semantic.SetTermTemplate variable) -> Evaluation.RuleAnswer variable key witness -> m (Maybe (key,witness)))
    -> (variable -> m variable)
    -> (Join.JoinFailure -> m ()) -> Evaluation.RuleEvaluator m variable bucket key witness
atomicEvaluator inputs charge bucket phase event completed converted argumentClass rejected =
    Evaluation.RuleEvaluator
        { Evaluation.ruleInputs = inputs
        , Evaluation.ruleCharge = charge
        , Evaluation.ruleGroundBucket = bucket
        , Evaluation.rulePhase = phase
        , Evaluation.ruleEvent = event
        , Evaluation.ruleCompleted = \ordinal value _ -> completed ordinal value
        , Evaluation.ruleConverted = converted
        , Evaluation.ruleArgumentClass = \value -> (\key -> (key,False)) <$> argumentClass value
        -- Fixture denotations can identify different written operands.
        , Evaluation.ruleHasEqualityTransport = True
        , Evaluation.ruleRejected = rejected
        , Evaluation.ruleWholeRequest = \_ _ _ _ -> error "atomic fixture materialized a whole request"
        , Evaluation.ruleWholeEvidence = \_ -> error "atomic fixture requested whole evidence"
        , Evaluation.ruleWholeBindings = \_ _ -> pure Nothing
        , Evaluation.ruleWholeCandidates = \_ _ -> pure Nothing
        , Evaluation.ruleFormulaShape = \_ -> error "atomic fixture requested a whole shape"
        , Evaluation.ruleWholeSources = const (pure [])
        , Evaluation.ruleAtomicFormula = const (pure Nothing)
        , Evaluation.ruleWholeTruthAvailable = const (pure False)
        , Evaluation.ruleSourcePossible = \_ _ known -> pure (True,known)
        , Evaluation.ruleOpaqueIsRigid = const (pure True)
        , Evaluation.ruleArgumentValue = const (pure Nothing)
        -- Whole-fragment fixtures replace these discovery operations.
        , Evaluation.ruleMatchWhole = \_ _ -> pure (Just Map.empty)
        , Evaluation.ruleMatchPartialWhole = \_ _ _ _ -> pure (Just Map.empty)
        , Evaluation.rulePreparePartialWhole = \_ _ _ _ _ -> pure (const (pure True))
        , Evaluation.rulePrepareWholeMatch = \_ _ _ _ _ -> pure (const (pure True))
        , Evaluation.ruleAtomicInputs = \_ _ -> pure (Just Map.empty)
        , Evaluation.ruleTermsMayAgree = \_ _ -> pure True
        , Evaluation.ruleOpaqueSupport = Nothing
        , Evaluation.ruleSupportTemplates = const (pure [])
        }

-- The free-constructor fixture can certify more rejections than the Core
-- owner. Models with provider aliases must supply their own conservative test.
freeTermsMayAgree :: (Monad m, Eq variable) => (Natural -> m ())
    -> Semantic.SetTermTemplate (Maybe variable) -> Semantic.SetTermTemplate (Maybe variable) -> m Bool
freeTermsMayAgree charge left right = charge 1 >> case (left,right) of
    (Semantic.TemplateVariable Nothing,_) -> pure True
    (_,Semantic.TemplateVariable Nothing) -> pure True
    (Semantic.TemplateVariable a,Semantic.TemplateVariable b) -> pure (a == b)
    (Semantic.TemplateClosed a,Semantic.TemplateClosed b) -> pure (a == b)
    (Semantic.TemplateProvider a xs,Semantic.TemplateProvider b ys)
        | a == b && length xs == length ys -> and <$> sequence (Vector.zipWith (freeTermsMayAgree charge) xs ys)
    (Semantic.TemplateOrderedPair a b,Semantic.TemplateOrderedPair c d) ->
        (&&) <$> freeTermsMayAgree charge a c <*> freeTermsMayAgree charge b d
    _ -> pure False

atomicAnswer :: Evaluation.RuleAnswer variable key witness -> Semantic.AtomTemplate (Semantic.SetTermTemplate variable)
atomicAnswer answer = case Evaluation.ruleAnswerLeaf answer of
    Semantic.AtomicLeaf row -> row
    Semantic.WholeLeaf{} -> error "atomic fixture received a whole answer"

completedAtom :: Rule.CompletedRule variable witness -> Semantic.AtomTemplate (Semantic.SetTermTemplate variable)
completedAtom completed = case Rule.ruleResult (Rule.completedInstantiation completed) of
    Semantic.AtomicLeaf atom -> atom
    Semantic.WholeLeaf{} -> error "atomic fixture received a whole conclusion"

evaluateProduction
    :: (Ord origin, Ord denotation) => (Semantic.SetTermTemplate (Maybe Reference.OpaqueSeed)
        -> Semantic.SetTermTemplate (Maybe Reference.OpaqueSeed) -> Reference.Reference Bool)
    -> (Reference.GroundTerm -> Reference.Reference denotation)
    -> (denotation -> denotation -> Reference.Reference Bool)
    -> Map Natural Reference.ReferenceRegistration -> [Reference.ReferenceFact origin]
    -> Set Reference.GroundTerm -> Reference.GroundAtom
    -> Reference.Reference (Reference.ReferenceEvaluation origin)
evaluateProduction compatible denote equal registrations facts aliases target = do
    (result,(_,witnesses)) <- withProduction denote equal registrations facts target \owner catalog snapshot initial ->
        Evaluation.evaluateCatalogRules owner {Evaluation.ruleTermsMayAgree = \a b -> lift (compatible a b)}
            catalog snapshot initial (Set.toAscList aliases) target >>=
            either (lift . Reference.invalidReferenceInput . Text.pack . show) (pure . fst)
    let retained = Map.fromListWith min
            [((atomicAnswer answer, Reference.referenceWitnessSummary (witnesses Map.! identifier)),
                (Evaluation.ruleAnswerCapability answer == Join.ExactAnswer,identifier))
            | answer <- Map.elems (Relational.relationalAnswers result), let identifier = Evaluation.ruleAnswerWitness answer]
    pure (Reference.ReferenceEvaluation Set.empty (snd <$> retained) witnesses Set.empty)

-- The initial rows and their evidence come from production preparation, not
-- from the reference seed closure. Tests independently compare both domains.
prepareProductionSupport
    :: Ord origin => Map Natural Reference.ReferenceRegistration -> [Reference.ReferenceFact origin]
    -> Set Reference.GroundTerm -> Reference.GroundAtom
    -> Reference.Reference (Support.FrozenSupport Reference.OpaqueSeed, [Reference.GroundAtom], Rule.SnapshotCounts)
prepareProductionSupport registrations facts aliases target = fst <$>
    withProduction pure (\left right -> pure (left == right)) registrations facts target
        (\owner _catalog snapshot initial ->
            Evaluation.prepareRuleSupport False owner snapshot initial (Set.toAscList aliases) target >>= \case
                Left _ -> lift (Reference.invalidReferenceInput "exhaustive preparation stopped early")
                Right (support,rows) -> pure (support,atomicAnswer <$> rows,Rule.snapshotCounts snapshot))

type ProductionState origin =
    ( Map (Reference.GroundAtom, Bool) Reference.WitnessId
    , Map Reference.WitnessId (Reference.ReferenceWitness origin))
type Production origin = State.StateT (ProductionState origin)
    (Except.ExceptT Reference.ReferenceFailure (State.State Word))

withProduction
    :: Ord origin => (Reference.GroundTerm -> Reference.Reference denotation)
    -> (denotation -> denotation -> Reference.Reference Bool)
    -> Map Natural Reference.ReferenceRegistration -> [Reference.ReferenceFact origin]
    -> Reference.GroundAtom
    -> (Evaluation.RuleEvaluator (Production origin) Reference.OpaqueSeed (Semantic.AtomTemplate denotation) Reference.WitnessId Reference.WitnessId
        -> Catalog.Catalog Natural
        -> Rule.RuleSnapshot
        -> [Evaluation.RuleAnswer Reference.OpaqueSeed Reference.WitnessId Reference.WitnessId]
        -> Production origin result)
    -> Reference.Reference (result, ProductionState origin)
withProduction denote equal registrations facts target action = State.runStateT run (Map.empty,Map.empty)
  where
    charge = lift . Reference.chargeReferenceWork . fromIntegral
    admit checked = checked >>= either (lift . Reference.invalidReferenceInput . Text.pack . show) pure
    intern row summary exactOnly recipe = do
        charge 1
        (known,witnesses) <- State.get
        let key = (row,exactOnly)
        case Map.lookup key known of
            Just identifier -> pure (identifier,identifier)
            Nothing -> do
                let identifier = Reference.WitnessId (fromIntegral (Map.size witnesses))
                State.put (Map.insert key identifier known,
                    Map.insert identifier (Reference.ReferenceWitness row summary recipe) witnesses)
                pure (identifier,identifier)
    tree = \case
        Composite.CompositePremiseTruth -> error "atomic reference received neutral premise"
        Composite.CompositePremiseLeaf witness -> Reference.PremiseLeaf witness
        Composite.CompositePremiseAnd left right -> Reference.PremiseConjunction (tree left) (tree right)
    leaves = \case
        Composite.CompositePremiseTruth -> []
        Composite.CompositePremiseLeaf witness -> [witness]
        Composite.CompositePremiseAnd left right -> leaves left <> leaves right
    terms = toList
    same [] [] = pure True
    same (left:ls) (right:rs) = do
        matched <- equal left right
        if matched then same ls rs else pure False
    same _ _ = pure False
    owner = atomicEvaluator (const (pure Rule.OpenRuleInputs)) charge (lift . traverse denote) (\_ -> pure ()) (\_ -> pure ())
        (\ordinal completed -> do
            (_,witnesses) <- State.get
            let row = completedAtom completed
                prerequisites = concatMap leaves (Rule.completedPremises completed)
                summaries = [Reference.referenceWitnessSummary (witnesses Map.! identifier) | identifier <- prerequisites]
                summary = Reference.WitnessSummary
                    (Set.unions (Reference.witnessOrigins <$> summaries))
                    (Set.insert ordinal (Set.unions (Reference.witnessOccurrences <$> summaries)))
                    (Reference.referenceRuleSupport (Reference.registrationRule (registrations Map.! ordinal))
                        <> Set.unions (Reference.witnessSupport <$> summaries))
            Just <$> intern row summary False (Reference.AppliedRule ordinal
                (Rule.ruleBinderValues (Rule.completedInstantiation completed)) (tree <$> Rule.completedPremises completed)))
        (\requested answer -> do
            expected <- lift (traverse denote (terms requested))
            actual <- lift (traverse denote (terms (atomicAnswer answer)))
            matches <- if Rule.atomSignature requested == Rule.atomSignature (atomicAnswer answer)
                then lift (same expected actual) else pure False
            if not matches then pure Nothing else do
                (_,witnesses) <- State.get
                let prior = Evaluation.ruleAnswerWitness answer
                Just <$> intern requested (Reference.referenceWitnessSummary (witnesses Map.! prior)) True
                    (Reference.SameDenotation prior))
        pure
        (const (pure ()))
    run = do
        rules <- traverse (\entry -> do
            let rule = Reference.registrationRule entry
            case entry of
                Reference.DefinitionRule{} -> case Reference.referenceRulePremises rule of
                    [Semantic.RulePremiseAtom source] -> Rule.RegisteredDefinition <$> admit
                        (Rule.compileForwardRule charge (Reference.referenceRuleArity rule) source (Reference.referenceRuleConclusion rule))
                    _ -> lift (Reference.invalidReferenceInput "invalid definition fixture")
                Reference.ClassificationRule{} -> Rule.RegisteredClassification <$> admit
                    (Rule.compileRule charge (Reference.referenceRuleArity rule) (Reference.referenceRulePremises rule)
                        (Reference.referenceRuleConclusion rule))) registrations
        initial <- forM (zip [0..] facts) \(ordinal,Reference.ReferenceFact row summary) -> do
            (key,witness) <- intern row summary False (Reference.ObservedRow ordinal)
            pure (Evaluation.RuleAnswer (Semantic.AtomicLeaf row) key Join.SourceRow witness)
        catalog <- Catalog.insertRules charge (Map.toAscList rules) Catalog.emptyCatalog
        snapshot <- admit (Catalog.selectSnapshot charge (Rule.atomSignature target) catalog)
        let withOrdinals = owner {Evaluation.ruleCompleted = \ordinal completed leaf ->
                case Catalog.lookupSource ordinal catalog of
                    Nothing -> lift (Reference.invalidReferenceInput "production rule lost its fixture owner")
                    Just original -> Evaluation.ruleCompleted owner original completed leaf}
        action withOrdinals catalog snapshot initial
