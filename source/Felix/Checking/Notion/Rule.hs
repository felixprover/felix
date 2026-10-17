{-# LANGUAGE NoImplicitPrelude #-}

-- | Premise ownership and conditional completion for relational formation.
-- The snapshot owner supplies admitted rule parts and checked answer witnesses.
-- Completed values are replay recipes, not kernel judgements.
module Felix.Checking.Notion.Rule
    ( Rule
    , compileRule
    , compileDescribedRule
    , RulePrefix, rulePrefix, scopedRulePrefix, ruleAmbientTypes, extendRulePrefix, compileRuleFromPrefix
    , compileRuleFromPrefixWithInputs, ruleWholeTemplates, ruleSupportSources, inheritRuleSupport
    , asWholeElimination, ruleIsElimination, ruleElimination
    , asIntroduction, ruleIsIntroduction
    , WholeWaiting(..), wholeRuleOptions, constrainWholePremise, ruleWholeSelections
    , ruleBindings, rulePremiseSlots, rulePremiseDescription, consumeAtomicPremise, ruleAtomicPremise, ruleExactConclusion
    , WholeElimination(..), bindEliminationInputs, constrainElimination, ruleWholeConstraint
    , compileConclusionRule
    , compileDescribedForwardRule
    , describeRuleFormulas, describeRuleConclusion, ruleFormulaHeads, rulePrimitiveHeads
    , RuleHead, ruleHeadWork
    , RuleInstantiation(..)
    , wholeProducerEntries
    , compileScopedRule
    , ruleCapturedSlots
    , ruleIsScoped
    , ruleDescription
    , AtomSignature
    , atomSignature
    , ruleSignature
    , rulePremiseSignatures
    , rulePremiseCount
    , ruleIsInitial
    , RuleState
    , activeRule, ruleConclusionPattern, ruleNeedsHeadDiscovery, bindWholeRuleInputs
    , ruleArgumentConstraints, constrainRule, ruleConstraintValues, ruleHeadValues, partialRuleAtom, ruleWaitingConstraints, ruleHeadConstraints, rulePremiseConstraints
    , BodyComponent, componentIndex, componentPositions, componentVariables, componentOutputs, componentInputs
    , pendingRuleComponents, ruleComponentsPlanned, planRuleComponents
    , ruleStateComponent, ruleComponentValues, startRuleComponent, resumeRuleComponent
    , prepareGroundRuleState
    , RuleWaiting
    , startRule
    , RuleInputs(..)
    , startRuleWithInputs
    , startWholeRule
    , ruleUndeterminedVariable, ruleVariablePattern, bindRuleVariable, ruleNeedsInputEnumeration
    , ruleOptions
    , ruleWaitingPattern
    , ruleWaitingIsGround, ruleWaitingBindingPriority, ruleWaitingNeedsDiscovery
    , resumeRule
    , finishRule
    , groundRuleInstantiation
    , GroundRule
    , prepareGroundRule
    , groundRuleLeaves
    , groundRuleSubstitution
    , completeGroundRule
    , RegisteredRule(..)
    , registeredRule
    , RuleRegistry
    , prepareRuleRegistry
    , selectRuleSnapshot
    , RuleSnapshot
    , snapshotRules
    , snapshotHeads
    , snapshotForwardOrder
    , snapshotForwardGroups
    , snapshotProducers
    , snapshotForwardSources
    , snapshotForwardPredecessors
    , snapshotSourceRanks
    , snapshotInitialRules
    , snapshotWholeProducers
    , snapshotTemplateSupport
    , snapshotCounts
    , SnapshotCounts(..)
    , preparedRuleSnapshot
    , RuleSnapshotFailure(..)
    , prepareRuleSnapshot
    , ForwardRule
    , compileForwardRule
    , forwardSourceSignature
    , applyForwardRule
    , applyInitialForwardRule
    , completeInitialRule
    , ruleTermTemplates
    , CompletedRule(..)
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Core (CanonicalTerm(..), CoreType(..), compareCanonicalWith, canonicalFreeIndicesWith, shiftCanonicalWith)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.FormulaIndex (FormulaId, ResidualShape, residualShape, residualShapeWork)
import Felix.Checking.Notion.SourceEvidence (UniversalBody(..), UniversalOperand(..))
import Felix.Checking.Notion.SourceEvidence qualified as Source
import Felix.Checking.Notion.Composite (CompositePremiseTree(..))
import Felix.Checking.Notion.Join
import Felix.Checking.Notion.Pattern
import Felix.Checking.Notion.Goal qualified as Goal
import Felix.Checking.Notion.Support (TemplateSupportView)
import Control.Monad (filterM, foldM, when, zipWithM)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Data.List (sortOn)
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.WholePattern (WholePattern, compileWholePattern)
import Numeric.Natural (Natural)

data Rule = Rule
    { ruleArity :: !Natural
    , ruleCapturedParameters :: !(Maybe (Set ViewVariableIx))
    , ruleConclusion :: !RuleConclusion
    , ruleResultHead :: !RuleHead
    , ruleWholeHeads :: ![ResidualShape]
    , ruleFormulaHeads :: ![(AtomSignature, ResidualShape)]
    , rulePrefix :: !RulePrefix
    , ruleBodyComponents :: ![BodyComponent]
    , ruleConclusionPattern :: !(Maybe WholePattern)
    , ruleInputParameters :: ![ViewVariableIx]
    , ruleRole :: !RuleRole
    , ruleInheritedSupport :: ![(Natural,ResidualTemplate)]
    , ruleNeedsHeadDiscovery :: !Bool
    , rulePremisePlans :: !(Map Natural PremisePlan)
    , ruleExactConclusion :: !(Maybe ResidualTemplate)
    }

data PremisePlan = PremisePlan
    !(WholeTemplate RuleTermTemplate) !ResidualTemplate !WholePattern !ResidualShape
    !(Set ViewVariableIx) !Bool

data WholeWaiting variable = WholeWaiting
    { wholeWaitingPosition :: !Natural
    , wholeWaitingTemplate :: !(WholeTemplate RuleTermTemplate)
    , wholeWaitingPattern :: !WholePattern
    , wholeWaitingShape :: !ResidualShape
    , wholeWaitingInputs :: !(Map ViewVariableIx (Maybe (SetTermTemplate variable)))
    , wholeWaitingDescription :: !ResidualTemplate
    , wholeWaitingNeedsGroundInputs :: !Bool
    }

data WholeElimination = WholeElimination
    { eliminationShape :: !ResidualShape
    , eliminationPattern :: !WholePattern
    }

data RuleRole = SourceRule | EliminationRule !WholeElimination | IntroductionRule

asWholeElimination :: WholeElimination -> Rule -> Rule
asWholeElimination source rule = rule {ruleRole = EliminationRule source}

asIntroduction :: Rule -> Rule
asIntroduction rule = rule {ruleRole = IntroductionRule}

ruleIsIntroduction :: Rule -> Bool
ruleIsIntroduction rule = case ruleRole rule of IntroductionRule -> True; _ -> False

ruleElimination :: Rule -> Maybe WholeElimination
ruleElimination rule = case ruleRole rule of EliminationRule source -> Just source; _ -> Nothing

ruleIsElimination :: Rule -> Bool
ruleIsElimination = isJust . ruleElimination

-- Persistent premise prefixes are shared by sibling projections. A new guard
-- extends only its own rows and proof block; no branch copies its ancestors.
data RulePrefix = RulePrefix
    { prefixAmbient :: ![CoreType]
    , prefixAtoms :: !(Map Natural (AtomTemplate RuleTermTemplate))
    , prefixWholes :: !(Map Natural (WholeTemplate RuleTermTemplate))
    , prefixShapes :: ![ResidualShape]
    , prefixForest :: !(Seq CompositePremiseBlock)
    , prefixVariables :: !(Set ViewVariableIx)
    , prefixPositiveParameters :: !(Set ViewVariableIx)
    , prefixFormulaHeads :: ![(AtomSignature,ResidualShape)]
    , prefixAllDescribed :: !Bool
    , prefixWholeTemplates :: ![(Natural,ResidualTemplate)]
    , prefixWholeArities :: !(Map Natural Natural)
    , prefixExactPremises :: !(Map Natural PremisePlan)
    , prefixCompoundOperands :: !Bool
    , prefixFaithfulAtoms :: !(Set Natural)
    }

type CompositePremiseBlock = CompositePremiseTree Natural

emptyRulePrefix :: RulePrefix
emptyRulePrefix = scopedRulePrefix []

scopedRulePrefix :: [CoreType] -> RulePrefix
scopedRulePrefix ambient = RulePrefix
    { prefixAmbient = ambient
    , prefixAtoms = Map.empty
    , prefixWholes = Map.empty
    , prefixShapes = []
    , prefixForest = Seq.empty
    , prefixVariables = Set.empty
    , prefixPositiveParameters = Set.empty
    , prefixFormulaHeads = []
    , prefixAllDescribed = True
    , prefixWholeTemplates = []
    , prefixWholeArities = Map.empty
    , prefixExactPremises = Map.empty
    , prefixCompoundOperands = False
    , prefixFaithfulAtoms = Set.empty
    }

ruleAmbientTypes :: Rule -> [CoreType]
ruleAmbientTypes = prefixAmbient . rulePrefix

ruleLeaves :: Rule -> Map Natural (AtomTemplate RuleTermTemplate)
ruleLeaves = prefixAtoms . rulePrefix

ruleWholeLeaves :: Rule -> Map Natural (WholeTemplate RuleTermTemplate)
ruleWholeLeaves = prefixWholes . rulePrefix

ruleWholeTemplates :: Rule -> [ResidualTemplate]
ruleWholeTemplates rule = case ruleConclusion rule of
    AtomicLeaf{} -> snd <$> prefixWholeTemplates (rulePrefix rule)
    WholeLeaf template -> template : (snd <$> prefixWholeTemplates (rulePrefix rule))

-- Domain descriptions survive projection independently of proof premises.
-- Each prefix keeps its original parameter width as later binders are opened.
ruleSupportSources :: Rule -> [(Natural,ResidualTemplate)]
ruleSupportSources rule = ruleInheritedSupport rule <> prefixWholeTemplates (rulePrefix rule)
    <> case ruleConclusion rule of AtomicLeaf{} -> []; WholeLeaf template -> [(ruleArity rule,template)]

inheritRuleSupport :: Rule -> Rule -> Rule
inheritRuleSupport original projected = projected
    {ruleInheritedSupport = ruleSupportSources original <> ruleInheritedSupport projected}

ruleForest :: Rule -> [CompositePremiseBlock]
ruleForest = toList . prefixForest . rulePrefix

-- Components are execution subqueries, not logical predicates. Head
-- occurrences mark escaping variables without connecting independent bodies.
data BodyComponent = BodyComponent
    { componentIndex :: !Int
    , componentPositions :: !(Set Natural)
    , componentVariables :: !(Set ViewVariableIx)
    , componentOutputs :: !(Set ViewVariableIx)
    , componentInputs :: !(Set ViewVariableIx)
    }

compileBodyComponents
    :: Monad m => (Natural -> m ()) -> Natural -> Set ViewVariableIx -> Set ViewVariableIx -> RuleConclusion
    -> Map Natural (AtomTemplate RuleTermTemplate) -> Map Natural (WholeTemplate RuleTermTemplate)
    -> m [BodyComponent]
compileBodyComponents _ _ _ _ _ atoms wholes | Map.size atoms + Map.size wholes <= 1 = pure []
compileBodyComponents charge arity captures external conclusion atoms wholes = do
    resultVariables <- case conclusion of
        AtomicLeaf atom -> atomVariables atom
        WholeLeaf residual -> residualVariables residual
    -- The founded whole source is also an observable output of a generated
    -- elimination. A component must not discard a parameter that selects it.
    headVariables <- union resultVariables external
    charge (fromIntegral (Set.size headVariables + Set.size captures))
    if fromIntegral (Set.size (headVariables <> captures)) == arity then pure [] else do
        relational <- traverse atomVariables atoms
        residuals <- traverse wholeVariables wholes
        let variables = relational <> residuals
        allVariables <- foldM union Set.empty (Map.elems variables)
        hidden <- difference allVariables (headVariables <> captures)
        if Set.null hidden || Map.size variables <= 1 then pure [] else do
            incidence <- foldM (\known (position,slots) -> foldM (\table slot -> do
                charge (indexWork (Map.size table) 1)
                pure (Map.insertWith (<>) slot [position] table)) known
                (Set.toAscList (Set.difference slots captures))) Map.empty (Map.toAscList variables)
            let constantPositions = Map.keysSet (Map.filter (Set.null . (`Set.difference` captures)) variables)
                visit seen bound pending = case Set.minView pending of
                    Nothing -> pure (seen,bound)
                    Just (position,rest) -> do
                        charge (indexWork (Set.size seen) 1)
                        if Set.member position seen then visit seen bound rest else do
                            charge (indexWork (Map.size variables) 1)
                            let slots = variables Map.! position
                            connected <- foldM (\next slot -> do
                                charge (indexWork (Set.size bound) 1)
                                if Set.member slot bound then pure next else do
                                    charge (indexWork (Map.size incidence) 1)
                                    foldM (\queue neighbor -> do
                                        charge (indexWork (Set.size queue) 1)
                                        pure (Set.insert neighbor queue)) next
                                        (Map.findWithDefault [] slot incidence)) rest
                                (Set.toAscList (Set.difference slots captures))
                            bound' <- union bound slots
                            visit (Set.insert position seen) bound' connected
                split remaining = case Set.lookupMin remaining of
                    Nothing -> pure []
                    Just position -> do
                        let start = if Set.member position constantPositions then constantPositions else Set.singleton position
                        (positions,slots) <- visit Set.empty Set.empty start
                        remaining' <- foldM (\known position' -> do
                            charge (indexWork (Set.size known) 1)
                            pure (Set.delete position' known)) remaining (Set.toAscList positions)
                        rest <- split remaining'
                        pure ((positions,slots):rest)
            components <- split (Map.keysSet variables)
            if length components <= 1 then pure [] else for (zip [0..] components) \(index,(positions,slots)) -> do
                charge (fromIntegral (Set.size slots))
                let external = Set.intersection slots headVariables
                pure (BodyComponent index positions slots (Set.difference external captures)
                    (external <> Set.intersection slots captures))
  where
    union left right = foldM (\known slot -> do
        charge (indexWork (Set.size known) 1)
        pure (Set.insert slot known)) left (Set.toAscList right)
    difference left right = charge (fromIntegral (Set.size left + Set.size right)) >> pure (Set.difference left right)
    collectVariables known term = charge 1 >> case term of
        TemplateVariable slot -> charge (indexWork (Set.size known) 1) >> pure (Set.insert slot known)
        TemplateClosed{} -> pure known
        TemplateProvider _ children -> foldM collectVariables known children
        TemplateOrderedPair left right -> collectVariables known left >>= (\next -> collectVariables next right)
    atomVariables = foldM collectVariables Set.empty
    residualVariables = residualRuleParameters charge arity
    wholeVariables = \case
        WholeResidual residual -> residualVariables residual
        WholeUniversal body -> universe Set.empty body
    universe known body = charge 1 >> case body of
        UniversalBind nested -> universe known nested
        UniversalRequire premises nested -> tree known premises >>= (\next -> universe next nested)
        UniversalReturn result -> tree known result
    tree = foldM (\known atom -> foldM (\accumulated term ->
        foldM (\present -> \case
            UniversalBound{} -> pure present
            UniversalOuter value -> collectVariables present value)
            accumulated term) known atom)

ruleCapturedSlots :: Rule -> Set ViewVariableIx
ruleCapturedSlots = fromMaybe Set.empty . ruleCapturedParameters

ruleIsScoped :: Rule -> Bool
ruleIsScoped = isJust . ruleCapturedParameters

-- Shallow head/arity keys keep scheduler comparisons independent of row size.
data AtomSignature
    = GlobalSignature !GlobalNotionHead !Int
    | StructureSignature !SemanticStructureNotionHead !Int
    | MembershipSignature
    | ExactStructureSignature !SemanticRecordShapeKey
    | NegativeGlobalSignature !GlobalNotionHead !Int
    | NegativeStructureSignature !SemanticStructureNotionHead !Int
    | NegativeMembershipSignature
    | NegativeExactStructureSignature !SemanticRecordShapeKey
    deriving (Show, Eq, Ord)

atomSignature :: AtomTemplate term -> AtomSignature
atomSignature = \case
    GlobalAtomTemplate head' arguments -> GlobalSignature head' (length arguments)
    StructureAtomTemplate head' arguments -> StructureSignature head' (length arguments)
    MembershipAtomTemplate{} -> MembershipSignature
    ExactStructureAtomTemplate shape _ -> ExactStructureSignature shape
    NegativeGlobalAtomTemplate head' arguments -> NegativeGlobalSignature head' (length arguments)
    NegativeStructureAtomTemplate head' arguments -> NegativeStructureSignature head' (length arguments)
    NegativeMembershipAtomTemplate{} -> NegativeMembershipSignature
    NegativeExactStructureAtomTemplate shape _ -> NegativeExactStructureSignature shape

type RuleHead = NotionLeaf AtomSignature ResidualShape

ruleHeadWork :: RuleHead -> Natural
ruleHeadWork (AtomicLeaf _) = 3
ruleHeadWork (WholeLeaf shape) = 1 + residualShapeWork shape

ruleSignature :: Rule -> RuleHead
ruleSignature = ruleResultHead

rulePremiseSignatures :: Rule -> [RuleHead]
rulePremiseSignatures rule = (AtomicLeaf . atomSignature <$> Map.elems (ruleLeaves rule))
    <> (WholeLeaf <$> ruleWholeHeads rule)

-- Ground construction belongs to the compiled goal plan. Source analysis may
-- conservatively assume these operations can succeed; it never proves them.
rulePrimitiveHeads :: Monad m => (Natural -> m ()) -> Rule -> m [ResidualShape]
rulePrimitiveHeads charge rule = do
    charge (fromIntegral (Map.size (rulePremisePlans rule)))
    let premises = [shape | PremisePlan _ _ _ shape _ True <- Map.elems (rulePremisePlans rule)]
    case ruleConclusion rule of
        AtomicLeaf{} -> pure premises
        WholeLeaf residual -> do
            goal <- Goal.compileGoal (charge 1) (residualTemplateFormula residual)
                (fromMaybe (Source.SourceResidual Nothing) (residualTemplateEvidence residual))
            pure (case ruleSignature rule of
                WholeLeaf shape | Goal.goalNeedsGroundInputs goal -> shape : premises
                _ -> premises)

rulePremiseCount :: Rule -> Int
rulePremiseCount rule = Map.size (ruleLeaves rule) + Map.size (ruleWholeLeaves rule)

ruleIsInitial :: Rule -> Bool
ruleIsInitial rule = ruleArity rule == 0 && null (ruleForest rule)

compileRule
    :: Monad m => (Natural -> m ()) -> Natural -> [RulePremiseTree RuleTermTemplate]
    -> AtomTemplate RuleTermTemplate -> m (Either JoinFailure Rule)
compileRule charge arity premises = compileConclusionRule charge arity premises . AtomicLeaf

-- Atomic/residual descriptions contain their own complete matching metadata.
-- Supplied universals additionally need their checked proposition, supplied by
-- declaration admission through compileDescribedRule.
compileConclusionRule
    :: Monad m => (Natural -> m ()) -> Natural -> [RulePremiseTree RuleTermTemplate]
    -> RuleConclusion -> m (Either JoinFailure Rule)
compileConclusionRule charge arity premises = compileRuleParts charge Nothing arity [(p, Nothing) | p <- premises]

compileDescribedRule
    :: Monad m => (Natural -> m ()) -> Natural
    -> [(RulePremiseTree RuleTermTemplate, CanonicalTerm ObjectId)]
    -> RuleConclusion -> m (Either JoinFailure Rule)
compileDescribedRule charge arity premises = compileRuleParts charge Nothing arity [(p, Just core) | (p, core) <- premises]

compileRuleParts
    :: Monad m => (Natural -> m ()) -> Maybe (Set ViewVariableIx) -> Natural
    -> [(RulePremiseTree RuleTermTemplate, Maybe (CanonicalTerm ObjectId))]
    -> RuleConclusion -> m (Either JoinFailure Rule)
compileRuleParts charge captures arity premises conclusion = Except.runExceptT do
    prefix <- foldM (\known (premise,formula) -> Except.ExceptT
        (extendRulePrefix charge arity known premise formula)) emptyRulePrefix premises
    Except.ExceptT (compileRuleFromPrefix charge captures arity prefix conclusion)

compileRuleFromPrefix
    :: Monad m => (Natural -> m ()) -> Maybe (Set ViewVariableIx) -> Natural
    -> RulePrefix -> RuleConclusion -> m (Either JoinFailure Rule)
compileRuleFromPrefix charge = compileRuleFromPrefixWithInputs charge Set.empty

-- Generated elimination schemas may have external inputs that appear only in
-- their exact whole source. They use the same finite input cursor as head-only
-- parameters; ordinary user rule admission remains range restricted.
compileRuleFromPrefixWithInputs
    :: Monad m => (Natural -> m ()) -> Set ViewVariableIx -> Maybe (Set ViewVariableIx) -> Natural
    -> RulePrefix -> RuleConclusion -> m (Either JoinFailure Rule)
compileRuleFromPrefixWithInputs charge external captures arity prefix conclusion = Except.runExceptT do
    let pinned = fromMaybe Set.empty captures
    for_ (Set.toAscList (pinned <> external)) \(ViewVariableIx index) -> do
        lift (charge 1)
        when (index >= arity) (Except.throwE (JoinInvalidVariable index))
    pattern' <- case conclusion of
        AtomicLeaf{} -> pure Nothing
        WholeLeaf template -> Just <$> lift (compileWholePattern charge arity (residualTemplateFormula template))
    headVariables <- case conclusion of
        AtomicLeaf atom -> traverse_ (validateRuleTerm charge arity) atom >> lift (collectRuleVariables charge Set.empty (toList atom))
        WholeLeaf residual -> do
            validateRuleResidual charge (arity + fromIntegral (length (prefixAmbient prefix))) residual
            lift (residualRuleParameters charge arity residual)
    variables <- lift (foldM (\known slot -> charge (indexWork (Set.size known) 1) >> pure (Set.insert slot known))
        (prefixVariables prefix) (Set.toAscList (pinned <> headVariables <> external <> prefixPositiveParameters prefix)))
    when (fromIntegral (Set.size variables) /= arity) $ case conclusion of
        WholeLeaf{} -> Except.throwE JoinWholeConclusionUndetermined
        AtomicLeaf{} -> do
            missing <- lift (firstMissing 0 (Set.toAscList variables))
            Except.throwE (JoinUndeterminedVariable missing)
    resultHead <- case conclusion of
        AtomicLeaf atom -> pure (AtomicLeaf (atomSignature atom))
        WholeLeaf template ->
            WholeLeaf <$> lift (residualShape (charge 1)
                (replicate (fromIntegral arity) TySet <> prefixAmbient prefix) (residualTemplateFormula template))
    components <- lift (compileBodyComponents charge arity pinned external conclusion (prefixAtoms prefix) (prefixWholes prefix))
    lift (charge (fromIntegral (Set.size headVariables + Set.size (prefixVariables prefix) + Set.size pinned)))
    let inputs = Set.toAscList ((headVariables <> external <> prefixPositiveParameters prefix) `Set.difference` (prefixVariables prefix <> pinned))
    let compound = prefixCompoundOperands prefix || case conclusion of
            WholeLeaf{} -> False
            AtomicLeaf atom -> any compoundOperand atom
    pure Rule
        { ruleArity = arity
        , ruleCapturedParameters = captures
        , ruleConclusion = conclusion
        , ruleResultHead = resultHead
        , ruleWholeHeads = prefixShapes prefix
        , ruleFormulaHeads = prefixFormulaHeads prefix
        , rulePrefix = prefix
        , ruleBodyComponents = components
        , ruleConclusionPattern = pattern'
        , ruleInputParameters = inputs
        , ruleRole = SourceRule
        , ruleInheritedSupport = []
        , ruleNeedsHeadDiscovery = compound
        , rulePremisePlans = prefixExactPremises prefix
        , ruleExactConclusion = case conclusion of WholeLeaf residual -> Just residual; AtomicLeaf{} -> Nothing
        }
  where
    firstMissing expected [] = pure expected
    firstMissing expected (ViewVariableIx actual:rest) = do
        charge 1
        if actual == expected then firstMissing (expected+1) rest else pure expected

collectRuleVariables :: Monad m => (Natural -> m ()) -> Set ViewVariableIx -> [RuleTermTemplate] -> m (Set ViewVariableIx)
collectRuleVariables charge = foldM collect
  where
    collect known value = charge 1 >> case value of
        TemplateVariable slot -> charge (indexWork (Set.size known) 1) >> pure (Set.insert slot known)
        TemplateClosed{} -> pure known
        TemplateProvider _ children -> foldM collect known children
        TemplateOrderedPair a b -> collect known a >>= (`collect` b)

-- Occurrence controls admission and component interfaces. It includes written
-- parameters erased by expansion; it does not certify inverse matching access.
residualRuleParameters :: Monad m => (Natural -> m ()) -> Natural -> ResidualTemplate -> m (Set ViewVariableIx)
residualRuleParameters charge arity residual = do
    parameters <- residualTemplateParametersWith (charge 1) residual
    charge (fromIntegral (Set.size parameters))
    pure (Set.filter (\(ViewVariableIx index) -> index < arity) parameters)

preparePremisePlan :: Monad m => (Natural -> m ()) -> Natural -> [CoreType]
    -> WholeTemplate RuleTermTemplate -> ResidualTemplate -> m PremisePlan
preparePremisePlan charge arity ambient template residual = do
        let formula = residualTemplateFormula residual
        parameters <- residualRuleParameters charge arity residual
        pattern' <- compileWholePattern charge arity formula
        shape <- residualShape (charge 1) (replicate (fromIntegral arity) TySet <> ambient) formula
        goal <- Goal.compileGoal (charge 1) formula
            (fromMaybe (Source.SourceResidual Nothing) (residualTemplateEvidence residual))
        pure (PremisePlan template residual pattern' shape parameters (Goal.goalNeedsGroundInputs goal))

-- Prefix descriptions are compiled once, shared by every projected conclusion.
-- Only a live request needs to align an ambient scope under later clause slots.
alignPremisePlan :: Monad m => (Natural -> m ()) -> Rule -> Natural -> PremisePlan -> m PremisePlan
alignPremisePlan charge rule position plan@(PremisePlan template description _ _ _ _) =
    if null (prefixAmbient prefix) || Map.lookup position (prefixWholeArities prefix) == Just arity
      then pure plan else do
        residual <- alignRuleWhole charge arity prefix position (WholeResidual description) >>= \case
            WholeResidual value -> pure value
            _ -> error "a residual description changed kind while aligning"
        aligned <- alignRuleWhole charge arity prefix position template
        preparePremisePlan charge arity (prefixAmbient prefix) aligned residual
  where
    prefix = rulePrefix rule
    arity = ruleArity rule

compoundOperand :: SetTermTemplate variable -> Bool
compoundOperand = \case
    TemplateProvider{} -> True
    TemplateOrderedPair{} -> True
    _ -> False

validateRuleTerm :: Monad m => (Natural -> m ()) -> Natural -> RuleTermTemplate -> Except.ExceptT JoinFailure m ()
validateRuleTerm charge arity term = lift (charge 1) >> case term of
    TemplateClosed value -> void (compareCanonicalWith (lift (charge 1)) (closedSetValueTerm value) (closedSetValueTerm value))
    TemplateVariable (ViewVariableIx index) -> when (index >= arity) (Except.throwE (JoinInvalidVariable index))
    TemplateProvider _ arguments -> traverse_ (validateRuleTerm charge arity) arguments
    TemplateOrderedPair left right -> validateRuleTerm charge arity left >> validateRuleTerm charge arity right

validateRuleResidual :: Monad m => (Natural -> m ()) -> Natural -> ResidualTemplate -> Except.ExceptT JoinFailure m ()
validateRuleResidual charge arity template = do
    variables <- lift (canonicalFreeIndicesWith (charge 1) (residualTemplateFormula template))
    for_ variables \index -> when (index >= arity) (Except.throwE (JoinInvalidVariable index))
    for_ (residualTemplateEvidence template) (Source.traverseSourceAtDepth
        (\depth -> traverse \term -> do
            slots <- lift (canonicalFreeIndicesWith (charge 1) term)
            for_ slots \index -> when (index >= arity + depth) (Except.throwE (JoinInvalidVariable index))
            pure term)
        (\depth atom -> traverse_ (validateRuleTerm charge (arity + depth)) atom >> pure atom))

extendRulePrefix
    :: Monad m => (Natural -> m ()) -> Natural -> RulePrefix -> RulePremiseTree RuleTermTemplate
    -> Maybe (CanonicalTerm ObjectId) -> m (Either JoinFailure RulePrefix)
extendRulePrefix charge arity prefix premise formula = Except.runExceptT do
    (block,next) <- State.runStateT (tree premise formula) prefix
    lift (charge 1)
    pure next {prefixForest = prefixForest next Seq.|> block}
  where
    debit = lift . lift . charge
    shape = residualShape (charge 1) (replicate (fromIntegral arity) TySet <> prefixAmbient prefix)
    tree premise' formula' = do
        debit 1
        case premise' of
            RulePremiseAnd left right -> case formula' of
                Just (CAnd a b) -> CompositePremiseAnd <$> tree left (Just a) <*> tree right (Just b)
                Nothing -> CompositePremiseAnd <$> tree left Nothing <*> tree right Nothing
                _ -> lift (Except.throwE JoinUnresolvedResult)
            RulePremiseResidual (ResidualTemplate CTruth) -> pure CompositePremiseTruth
            RulePremiseUniversal body -> do
                case body of UniversalBind{} -> pure (); _ -> lift (Except.throwE JoinUnresolvedResult)
                lift (universal 0 body)
                exact <- maybe (lift (Except.throwE JoinUnresolvedResult)) pure formula'
                whole exact (WholeUniversal body)
            RulePremiseResidual template -> do
                lift (validateRuleResidual charge (arity + fromIntegral (length (prefixAmbient prefix))) template)
                whole (residualTemplateFormula template) (WholeResidual template)
            RulePremiseAtom atom -> do
                lift (traverse_ (validateRuleTerm charge arity) atom)
                known <- State.get
                let position = Map.size (prefixAtoms known) + Map.size (prefixWholes known)
                variables <- lift (lift (collectRuleVariables charge (prefixVariables known) (toList atom)))
                described <- case formula' of
                    Nothing -> pure []
                    Just exact -> (\head' -> [(atomSignature atom,head')]) <$> lift (lift (shape exact))
                faithful <- lift (lift (atomInputsSurvive charge atom formula'))
                exactPlan <- lift (lift (for formula' (\exact -> do
                    let residual = describedResidualTemplate exact (Source.SourceAtom atom)
                    preparePremisePlan charge arity (prefixAmbient known) (WholeResidual residual) residual)))
                debit (indexWork (Map.size (prefixAtoms known)) 1)
                debit (indexWork (Set.size (prefixFaithfulAtoms known)) 1)
                State.put known {prefixAtoms = Map.insert (fromIntegral position) atom (prefixAtoms known),
                    prefixVariables = variables, prefixFormulaHeads = described <> prefixFormulaHeads known,
                    prefixExactPremises = maybe (prefixExactPremises known) (\plan -> Map.insert (fromIntegral position)
                        plan (prefixExactPremises known)) exactPlan,
                    prefixWholeArities = Map.insert (fromIntegral position) arity (prefixWholeArities known),
                    prefixAllDescribed = prefixAllDescribed known && isJust formula',
                    prefixCompoundOperands = prefixCompoundOperands known || any compoundOperand atom,
                    prefixFaithfulAtoms = if faithful then Set.insert (fromIntegral position) (prefixFaithfulAtoms known)
                        else prefixFaithfulAtoms known}
                pure (CompositePremiseLeaf (fromIntegral position))
    whole formula' template = do
        head' <- lift (lift (shape formula'))
        description <- case template of
            WholeResidual residual -> pure residual
            WholeUniversal body -> do
                evidence <- lift (lift (Source.universalEvidenceWith (charge 1) body))
                described <- lift (lift (Source.traverseAtDepth (\depth -> traverse (term depth)) evidence))
                pure (describedResidualTemplate formula' described)
        known <- State.get
        plan <- lift (lift (preparePremisePlan charge arity (prefixAmbient known) template description))
        positive <- lift (lift (positiveResidualParametersWith (charge 1) description))
        let parameters = Set.filter (\(ViewVariableIx index) -> index < arity) (fromMaybe Set.empty positive)
        debit (fromIntegral (Set.size parameters + Set.size (prefixPositiveParameters known)))
        let position = fromIntegral (Map.size (prefixAtoms known) + Map.size (prefixWholes known))
        debit (2 * indexWork (Map.size (prefixWholes known)) 1)
        State.put known {prefixWholes = Map.insert position template (prefixWholes known),prefixShapes = head':prefixShapes known,
            prefixPositiveParameters = prefixPositiveParameters known <> parameters,
            prefixWholeTemplates = (arity,description) : prefixWholeTemplates known,
            prefixExactPremises = Map.insert position plan (prefixExactPremises known),
            prefixWholeArities = Map.insert position arity (prefixWholeArities known)}
        pure (CompositePremiseLeaf position)
    term depth value = charge 1 >> case value of
        TemplateVariable (UniversalBound index) -> pure (TemplateVariable (ViewVariableIx (depth-index-1)))
        TemplateVariable (UniversalOuter outer) -> traverse (\(ViewVariableIx index) -> charge 1 >> pure (ViewVariableIx (index+depth))) outer
        TemplateClosed value' -> pure (TemplateClosed value')
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse (term depth) arguments
        TemplateOrderedPair a b -> TemplateOrderedPair <$> term depth a <*> term depth b
    universal depth = \case
        UniversalBind nested -> lift (charge 1) >> universal (depth + 1) nested
        UniversalRequire guard nested -> traverse_ (universalAtom depth) guard >> universal depth nested
        UniversalReturn result -> do
            when (depth == 0) (Except.throwE JoinUnresolvedResult)
            traverse_ (universalAtom depth) result
    universalAtom depth = traverse_ (universalTerm depth)
    universalTerm depth value = do
        lift (charge 1)
        case value of
            TemplateClosed closed -> validateRuleTerm charge arity (TemplateClosed closed)
            TemplateVariable (UniversalBound index) -> when (index >= depth) (Except.throwE (JoinInvalidVariable index))
            TemplateVariable (UniversalOuter outer) -> validateRuleTerm charge arity outer
            TemplateProvider _ arguments -> traverse_ (universalTerm depth) arguments
            TemplateOrderedPair left right -> universalTerm depth left >> universalTerm depth right

compileScopedRule
    :: Monad m => (Natural -> m ()) -> Natural -> Set ViewVariableIx
    -> [RulePremiseTree RuleTermTemplate] -> AtomTemplate RuleTermTemplate
    -> m (Either JoinFailure Rule)
compileScopedRule charge arity captures premises conclusion =
    compileRuleParts charge (Just captures) arity [(p,Nothing) | p <- premises] (AtomicLeaf conclusion)

data RuleState variable witness = RuleState
    { activeRule :: !Rule
    , activeJoin :: !(JoinState variable)
    , pendingLeaves :: !(Map Natural (AtomTemplate RuleTermTemplate))
    , consumedLeaves :: !(Map Natural witness)
    , ruleStateComponent :: !(Maybe BodyComponent)
    , remainingRuleComponents :: !(Maybe [BodyComponent])
    , ruleArgumentConstraints :: !(Map ViewVariableIx variable)
    , ruleWholeSelections :: !(Map Natural FormulaId)
    }

constrainElimination :: FormulaId -> RuleState variable witness -> RuleState variable witness
constrainElimination = constrainWholePremise 0

ruleWholeConstraint :: RuleState variable witness -> Maybe FormulaId
ruleWholeConstraint = Map.lookup 0 . ruleWholeSelections

constrainWholePremise :: Natural -> FormulaId -> RuleState variable witness -> RuleState variable witness
constrainWholePremise position formula state = state
    {ruleWholeSelections = Map.insert position formula (ruleWholeSelections state)}

wholeRuleOptions
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m [(Natural, Either JoinFailure (WholeWaiting variable))]
wholeRuleOptions charge bound state = fmap catMaybes $ for (Map.toAscList (rulePremisePlans (activeRule state)))
    \(position,plan) -> do
        charge (indexWork (Map.size (ruleWholeSelections state)) 1)
        if Map.member position (ruleWholeSelections state) || Map.member position (consumedLeaves state) || maybe False
            (not . Set.member position . componentPositions) (ruleStateComponent state)
        then pure Nothing else do
            PremisePlan template description pattern' shape variables needsGround <- alignPremisePlan charge (activeRule state) position plan
            inputs <- joinVariableValues charge bound (Set.toAscList variables) (activeJoin state)
            pure (Just (position,(\values -> WholeWaiting position template pattern' shape values description needsGround) <$> inputs))

ruleBindings :: Monad m => (Natural -> m ()) -> Natural -> [ViewVariableIx] -> RuleState variable witness
    -> m (Either JoinFailure (Map ViewVariableIx (Maybe (SetTermTemplate variable))))
ruleBindings charge bound slots = joinVariableValues charge bound slots . activeJoin

rulePremiseSlots :: Monad m => (Natural -> m ()) -> Natural -> Rule -> m [ViewVariableIx]
rulePremiseSlots charge position rule = do
    charge (indexWork (Map.size (rulePremisePlans rule)) 1)
    case Map.lookup position (rulePremisePlans rule) of
        Just (PremisePlan _ _ _ _ slots _) -> pure (Set.toAscList slots)
        Nothing -> maybe (pure []) (fmap Set.toAscList . collectRuleVariables charge Set.empty . toList)
            (ruleAtomicPremise position rule)

ruleAtomicPremise :: Natural -> Rule -> Maybe (AtomTemplate RuleTermTemplate)
ruleAtomicPremise position = Map.lookup position . ruleLeaves

rulePremiseDescription :: Monad m => (Natural -> m ()) -> Natural -> Rule -> m (Maybe ResidualTemplate)
rulePremiseDescription charge position rule = for (Map.lookup position (rulePremisePlans rule)) (\plan -> do
    PremisePlan _ residual _ _ _ _ <- alignPremisePlan charge rule position plan
    pure residual)

consumeAtomicPremise :: Natural -> witness -> RuleState variable witness -> RuleState variable witness
consumeAtomicPremise position witness state = state
    { pendingLeaves = Map.delete position (pendingLeaves state)
    , consumedLeaves = Map.insert position witness (consumedLeaves state) }

-- Constraints filter complete operand denotations while joins retain the
-- original source views. They are neither substitutions nor evidence.
constrainRule :: Map ViewVariableIx variable -> RuleState variable witness -> RuleState variable witness
constrainRule values state = state {ruleArgumentConstraints = values}

-- Only parameters absent from relational premises may be supplied as opaque
-- whole-head inputs. Body parameters keep the admitted views of their rows.
bindWholeRuleInputs
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Map ViewVariableIx variable
    -> RuleState variable witness -> m (Maybe (RuleState variable witness))
bindWholeRuleInputs charge values state = foldM bind (Just state) (ruleInputParameters (activeRule state))
  where
    bind Nothing _ = pure Nothing
    bind (Just current) slot@(ViewVariableIx index) = do
        charge (indexWork (Map.size values) 1)
        case Map.lookup slot values of
            Nothing -> pure (Just current)
            Just value -> bindRuleVariable charge index (TemplateVariable value) current

ruleConstraintValues
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (Map ViewVariableIx (Maybe (SetTermTemplate variable))))
ruleConstraintValues charge bound state = joinVariableValues charge bound
    (Map.keys (ruleArgumentConstraints state)) (activeJoin state)

-- Partial head denotations are filters only. Unresolved variables stay holes;
-- no opaque operand is opened to recover a source view.
ruleHeadValues
    :: Monad m => (Natural -> m ()) -> Natural -> Map ViewVariableIx (SetTermTemplate variable) -> RuleState variable witness
    -> m (Either JoinFailure (Maybe (AtomTemplate (SetTermTemplate (Maybe variable)))))
ruleHeadValues charge bound forced state = case ruleConclusion (activeRule state) of
    WholeLeaf{} -> pure (Right Nothing)
    AtomicLeaf atom -> do
        slots <- collectRuleVariables charge Set.empty (toList atom)
        values <- joinVariableValues charge bound (Set.toAscList slots) (activeJoin state)
        traverse (\known -> do
            charge (fromIntegral (Map.size known + Map.size forced))
            Just <$> partialRuleAtom charge (Map.union (Map.mapMaybe id known) forced) atom) values

-- Interpret necessary denotations without installing substitutions. Callers
-- retain actual bindings ahead of forced singleton values; other slots stay
-- unknown. The result has no source-row or proof capability.
partialRuleAtom
    :: Monad m => (Natural -> m ()) -> Map ViewVariableIx (SetTermTemplate variable)
    -> AtomTemplate RuleTermTemplate -> m (AtomTemplate (SetTermTemplate (Maybe variable)))
partialRuleAtom charge bindings = traverse (substitute bindings)
  where
    substitute values term = charge 1 >> case term of
        TemplateVariable slot -> do
            charge (indexWork (Map.size values) 1)
            pure (maybe (TemplateVariable Nothing) (fmap Just) (Map.lookup slot values))
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse (substitute values) arguments
        TemplateOrderedPair a b -> TemplateOrderedPair <$> substitute values a <*> substitute values b

-- Complete outer operands of a founded whole instance can specialize its
-- generated projection. Known rich bindings survive; opaque interiors never
-- supply a slot. The caller admits each new value against the frozen domain.
bindEliminationInputs
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> Map ViewVariableIx variable
    -> RuleState variable witness -> m (Either JoinFailure (Maybe (RuleState variable witness)))
bindEliminationInputs charge bound values state = do
    existing <- joinVariableValues charge bound (Map.keys values) (activeJoin state)
    traverse (foldM bind (Just state) . Map.toAscList) existing
  where
    bind Nothing _ = pure Nothing
    bind found (_,Just _) = pure found
    bind (Just current) (slot@(ViewVariableIx index),Nothing) = do
        charge (indexWork (Map.size values) 1)
        bindRuleVariable charge index (TemplateVariable (values Map.! slot)) current

ruleHeadConstraints
    :: Monad m => (Natural -> m ()) -> Rule -> Map Int variable -> m [(ViewVariableIx,variable)]
ruleHeadConstraints charge rule constraints
    | Map.null constraints = pure []
    | otherwise = case ruleConclusion rule of
        WholeLeaf{} -> pure []
        AtomicLeaf atom -> fmap catMaybes $ for (zip [0..] (toList atom)) \(position,term) -> do
            charge (indexWork (Map.size constraints) 1)
            pure $ case term of
                TemplateVariable slot -> (\value -> (slot,value)) <$> Map.lookup position constraints
                _ -> Nothing

-- Candidate truth constrains complete operands only. This never inverts a
-- provider or supplies a row view; finite assignments still undergo every guard.
rulePremiseConstraints
    :: Monad m => (Natural -> m ()) -> Natural -> Map Int variable
    -> RuleState term witness -> m [(ViewVariableIx,variable)]
rulePremiseConstraints charge position values state = do
    charge (indexWork (Map.size (ruleLeaves (activeRule state))) 1)
    case Map.lookup position (ruleLeaves (activeRule state)) of
        Nothing -> pure []
        Just atom -> fmap catMaybes $ for (zip [0..] (toList atom)) \(argument,term) -> do
            charge (indexWork (Map.size values) 1)
            pure $ case term of
                TemplateVariable slot -> (\value -> (slot,value)) <$> Map.lookup argument values
                _ -> Nothing

ruleWaitingConstraints :: RuleWaiting variable witness -> Map Int variable
ruleWaitingConstraints (RuleWaiting _ _ _ constraints _) = constraints

pendingRuleComponents :: RuleState variable witness -> [BodyComponent]
pendingRuleComponents state = case ruleStateComponent state of
    Just _ -> []
    Nothing -> fromMaybe (ruleBodyComponents (activeRule state)) (remainingRuleComponents state)

ruleComponentsPlanned :: RuleState variable witness -> Bool
ruleComponentsPlanned = isJust . remainingRuleComponents

planRuleComponents :: [BodyComponent] -> RuleState variable witness -> RuleState variable witness
planRuleComponents components state = state {remainingRuleComponents = Just components}

ruleComponentValues
    :: Monad m => (Natural -> m ()) -> Natural -> BodyComponent -> RuleState variable witness
    -> m (Either JoinFailure (Map ViewVariableIx (Maybe (SetTermTemplate variable))))
ruleComponentValues charge bound component state =
    joinVariableValues charge bound (Set.toAscList (componentInputs component)) (activeJoin state)

startRuleComponent
    :: Monad m => (Natural -> m ()) -> Rule -> BodyComponent
    -> Map ViewVariableIx (SetTermTemplate variable) -> m (RuleState variable witness)
startRuleComponent charge rule component inputs = do
    joined <- startWholeJoin charge (ruleArity rule) inputs (ResidualTemplate CTruth)
    pure (RuleState rule joined (Map.restrictKeys (ruleLeaves rule) (componentPositions component)) Map.empty (Just component) (Just []) Map.empty Map.empty)

resumeRuleComponent
    :: (Monad m, Eq variable) => (Natural -> m ()) -> RuleState variable witness
    -> Map ViewVariableIx (SetTermTemplate variable) -> Map Natural witness
    -> m (Maybe (RuleState variable witness))
resumeRuleComponent charge initial values witnesses = do
    joined <- foldM (\known (ViewVariableIx slot,value) -> case known of
        Nothing -> pure Nothing
        Just state -> bindRuleVariable charge slot value state) (Just initial) (Map.toAscList values)
    charge (fromIntegral (Map.size witnesses))
    pure ((\state -> state {pendingLeaves = Map.difference (pendingLeaves state) witnesses
        , consumedLeaves = Map.union (consumedLeaves state) witnesses
        , remainingRuleComponents = case remainingRuleComponents state of
            Just (_:rest) -> Just rest
            _ -> error "a component result lost its installed plan"}) <$> joined)

data RuleWaiting variable witness = RuleWaiting
    !Natural !(JoinPremise variable) !(RuleState variable witness) !(Map Int variable) !(Int,Int,Bool)

startRule
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> Rule -> CanonicalPattern variable
    -> m (Either JoinFailure (Maybe (RuleState variable witness)))
startRule charge bound = startRuleWithInputs charge bound OpenRuleInputs

-- A local source's captures are fixed inputs. The common instantiator
-- determines its other parameters from requested arguments, rows, or U.
data RuleInputs variable
    = OpenRuleInputs
    | ScopedRuleInputs !(Map ViewVariableIx (SetTermTemplate variable))

startRuleWithInputs
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> RuleInputs variable
    -> Rule -> CanonicalPattern variable -> m (Either JoinFailure (Maybe (RuleState variable witness)))
startRuleWithInputs charge bound inputs rule requested = Except.runExceptT do
    let captures = case inputs of OpenRuleInputs -> Map.empty; ScopedRuleInputs values -> values
    lift (charge (fromIntegral (Map.size captures + Set.size (ruleCapturedSlots rule))))
    when (Map.keysSet captures /= ruleCapturedSlots rule) (Except.throwE JoinUnresolvedResult)
    conclusion <- case ruleConclusion rule of
        AtomicLeaf atom -> pure atom
        WholeLeaf{} -> Except.throwE JoinUnresolvedResult
    joined <- Except.ExceptT (startCapturedJoin charge bound (ruleArity rule) captures conclusion requested)
    pure ((\state -> RuleState rule state (ruleLeaves rule) Map.empty Nothing Nothing Map.empty Map.empty) <$> joined)

startWholeRule
    :: Monad m => (Natural -> m ()) -> RuleInputs variable -> Rule
    -> m (Either JoinFailure (RuleState variable witness))
startWholeRule charge inputs rule = Except.runExceptT do
    let captures = case inputs of OpenRuleInputs -> Map.empty; ScopedRuleInputs values -> values
    lift (charge (fromIntegral (Map.size captures + Set.size (ruleCapturedSlots rule))))
    when (Map.keysSet captures /= ruleCapturedSlots rule) (Except.throwE JoinUnresolvedResult)
    case ruleConclusion rule of
        AtomicLeaf{} -> Except.throwE JoinUnresolvedResult
        WholeLeaf residual -> do
            joined <- lift (startWholeJoin charge (ruleArity rule) captures residual)
            pure (RuleState rule joined (ruleLeaves rule) Map.empty Nothing Nothing Map.empty Map.empty)

ruleUndeterminedVariable
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (Maybe Natural))
ruleUndeterminedVariable charge bound state = instantiateRuleState charge bound state >>= \case
    Left (JoinUndeterminedVariable slot) -> pure (Right (Just slot))
    Left failure -> pure (Left failure)
    Right _ -> pure (Right Nothing)

ruleVariablePattern
    :: Monad m => (Natural -> m ()) -> Natural -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (SetTermTemplate (PatternVariable variable)))
ruleVariablePattern charge bound slot = joinVariablePattern charge bound slot . activeJoin

bindRuleVariable
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> SetTermTemplate variable
    -> RuleState variable witness -> m (Maybe (RuleState variable witness))
bindRuleVariable charge slot value state = fmap (\joined -> state {activeJoin = joined})
    <$> bindJoinVariable charge slot value (activeJoin state)

-- Body-covered parameters are discovered from rows. Only undetermined inputs
-- absent from relational premises require enumeration before a candidate has
-- demonstrated a missing argument view.
ruleNeedsInputEnumeration
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure Bool)
ruleNeedsInputEnumeration charge bound state = fmap (any isNothing) <$>
    joinVariableValues charge bound inputs (activeJoin state)
  where
    inputs = case ruleStateComponent state of
        Nothing -> ruleInputParameters (activeRule state)
        Just component -> [slot | slot <- ruleInputParameters (activeRule state), Set.member slot (componentVariables component)]

-- Return every remaining premise's status for the deterministic join order.
-- Missing views retain finite instantiation as an alternative to row binding.
ruleOptions
    :: (Monad m, Ord variable) => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m [(Natural, Either JoinFailure (RuleWaiting variable witness))]
ruleOptions charge bound state = traverse (\(position, premise) -> do
    charge 1
    prepared <- prepareJoinPremise charge bound (activeJoin state) premise
    waiting <- for prepared \joined -> do
        constraints <- if Map.null (ruleArgumentConstraints state) then pure Map.empty else
            fmap (Map.fromDistinctAscList . catMaybes) $ for (zip [0..] (toList premise)) \(argument,term) -> do
                charge (indexWork (Map.size (ruleArgumentConstraints state)) 1)
                pure $ case term of
                    TemplateVariable slot -> (\value -> (argument,value)) <$> Map.lookup slot (ruleArgumentConstraints state)
                    _ -> Nothing
        selected <- for (zip [0..] (joinPremiseBindings joined)) \(argument,binding) -> do
            if Map.null constraints then charge 1 >> pure binding else do
                charge (indexWork (Map.size constraints) 1)
                pure (if Map.member argument constraints then (True,True) else binding)
        let anchored = [grounded || pinned | (grounded,pinned) <- selected]
            priority = (length [() | (True,_) <- selected],length [() | True <- anchored],
                case anchored of first:_ -> first; [] -> False)
        pure (RuleWaiting position joined state constraints priority)
    pure (position,waiting)) (Map.toAscList (pendingLeaves state))

ruleWaitingPattern :: RuleWaiting variable witness -> AtomTemplate (SetTermTemplate (PatternVariable variable))
ruleWaitingPattern (RuleWaiting _ premise _ _ _) = joinPremisePattern premise

ruleWaitingIsGround :: RuleWaiting variable witness -> Bool
ruleWaitingIsGround (RuleWaiting _ premise _ _ _) = joinPremiseIsGround premise

-- More determined operands first, then operands containing pinned parameters.
-- On a tie, preserve an anchored leading operand
-- (the usual notion subject) before discovering arbitrary subjects through a
-- shared parameter. This orders joins only; every remaining guard is required.
ruleWaitingBindingPriority :: RuleWaiting variable witness -> (Int,Int,Bool)
ruleWaitingBindingPriority (RuleWaiting _ _ _ _ priority) = priority

-- A source spelling can bind erased arguments without determining their
-- denotations. Keep finite alternatives unless the checked premise preserves
-- all its formal inputs. This certificate supplies no inverse bindings.
ruleWaitingNeedsDiscovery :: Monad m => (Natural -> m ()) -> RuleWaiting variable witness -> m Bool
ruleWaitingNeedsDiscovery charge (RuleWaiting position premise state _ _)
    | joinPremiseIsGround premise = pure False
    | otherwise = do
        let faithful = prefixFaithfulAtoms (rulePrefix (activeRule state))
        charge (indexWork (Set.size faithful) 1)
        pure (Set.notMember position faithful)

resumeRule
    :: (Monad m, Ord variable) => (Natural -> m ()) -> RowCapability -> RuleWaiting variable witness
    -> AtomTemplate (SetTermTemplate variable) -> witness
    -> m (Either JoinFailure (Maybe (RuleState variable witness)))
resumeRule charge capability (RuleWaiting position premise state _ _) row witness = do
    charge 1
    candidate <- resumeJoinPremise charge capability premise row
    pure (fmap (fmap (\joined -> state
        { activeJoin = joined
        , pendingLeaves = Map.delete position (pendingLeaves state)
        , consumedLeaves = Map.insert position witness (consumedLeaves state) })) candidate)

data RuleInstantiation variable = RuleInstantiation
    { ruleBinderValues :: !(Map ViewVariableIx (SetTermTemplate variable))
    , ruleResult :: !(NotionLeaf (AtomTemplate (SetTermTemplate variable)) ResidualTemplate)
    }
    deriving (Show, Eq)

fromJoin :: JoinInstantiation variable -> RuleInstantiation variable
fromJoin (JoinInstantiation values result) = RuleInstantiation values result

data CompletedRule variable witness = CompletedRule
    { completedInstantiation :: !(RuleInstantiation variable)
    , completedPremises :: ![CompositePremiseTree witness]
    }
    deriving (Show, Eq)

-- Nothing means premises remain. Empty forests are ordinary unconditional
-- rules; unresolved binders are an explicit rejection, never guessed values.
finishRule
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (Maybe (CompletedRule variable witness)))
finishRule charge bound state = do
    charge 1
    if not (Map.null (pendingLeaves state)) || not (Map.null (ruleWholeLeaves (activeRule state)))
    then pure (Right Nothing) else Except.runExceptT do
        instantiated <- Except.ExceptT (instantiateJoin charge bound (activeJoin state))
        forest <- traverse rebuild (ruleForest (activeRule state))
        pure (Just (CompletedRule (fromJoin instantiated) forest))
  where
    -- The private transitions partition every source leaf into pending or
    -- consumed. With pending empty, every forest position has a witness.
    rebuild premise = do
        lift (charge 1)
        case premise of
            CompositePremiseTruth -> pure CompositePremiseTruth
            CompositePremiseLeaf position -> pure (CompositePremiseLeaf (consumedLeaves state Map.! position))
            CompositePremiseAnd left right -> CompositePremiseAnd <$> rebuild left <*> rebuild right

-- A complete substitution ends relational parameter discovery. The evaluator
-- interns it before preparing the forest, so every instance does this work once.
groundRuleInstantiation
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (Maybe (RuleInstantiation variable)))
groundRuleInstantiation charge bound state = instantiateRuleState charge bound state >>= \case
    Left JoinUndeterminedVariable{} -> pure (Right Nothing)
    Left JoinUnresolvedResult -> pure (Right Nothing)
    Left failure -> pure (Left failure)
    Right instantiated -> pure (Right (Just (fromJoin instantiated)))

instantiateRuleState
    :: Monad m => (Natural -> m ()) -> Natural -> RuleState variable witness
    -> m (Either JoinFailure (JoinInstantiation variable))
instantiateRuleState charge bound state = case ruleStateComponent state of
    Nothing -> instantiateJoin charge bound (activeJoin state)
    Just component -> fmap (\values -> JoinInstantiation values (WholeLeaf (ResidualTemplate CTruth))) <$>
        instantiateJoinVariables charge bound (Set.toAscList (componentVariables component)) (activeJoin state)

data GroundRule variable = GroundRule
    !(RuleInstantiation variable)
    !(Map Natural (NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeTemplate RuleTermTemplate)))
    ![CompositePremiseTree Natural]

groundRuleLeaves :: GroundRule variable -> Map Natural (NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeTemplate RuleTermTemplate))
groundRuleLeaves (GroundRule _ leaves _) = leaves

groundRuleSubstitution :: GroundRule variable -> Map ViewVariableIx (SetTermTemplate variable)
groundRuleSubstitution (GroundRule instantiated _ _) = ruleBinderValues instantiated

prepareGroundRule
    :: Monad m => (Natural -> m ()) -> Rule -> RuleInstantiation variable
    -> m (Either JoinFailure (GroundRule variable))
prepareGroundRule charge rule instantiated = Except.runExceptT do
    leaves <- traverse (fmap AtomicLeaf . traverseAtomTemplateArguments substitute) (ruleLeaves rule)
    lift (charge (fromIntegral (Map.size leaves + Map.size (ruleWholeLeaves rule))))
    wholes <- lift (Map.traverseWithKey (alignRuleWhole charge (ruleArity rule) (rulePrefix rule)) (ruleWholeLeaves rule))
    pure (GroundRule instantiated (leaves <> (WholeLeaf <$> wholes))
        (ruleForest rule))
  where
    substitute term = do
        lift (charge 1)
        case term of
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateVariable slot -> maybe (Except.throwE JoinUnresolvedResult) pure
                (Map.lookup slot (ruleBinderValues instantiated))
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse substitute arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> substitute left <*> substitute right

-- Prefixes remain shared while projections add parameters. Align their lexical
-- captures when preparing a matcher or ground instance, at the final width.
alignRuleWhole
    :: Monad m => (Natural -> m ()) -> Natural -> RulePrefix -> Natural
    -> WholeTemplate RuleTermTemplate -> m (WholeTemplate RuleTermTemplate)
alignRuleWhole charge arity prefix position template = case template of
    WholeResidual residual | not (null (prefixAmbient prefix)) -> do
        charge (indexWork (Map.size (prefixWholeArities prefix)) 1)
        let original = prefixWholeArities prefix Map.! position
        if original == arity then pure template else do
            let amount = arity-original
            formula <- shiftCanonicalWith (charge 1) amount original (residualTemplateFormula residual)
            metadata <- traverse (Source.traverseSourceAtDepth
                (\depth -> traverse (shiftCanonicalWith (charge 1) amount (original+depth)))
                (\depth -> traverse (traverse (\(ViewVariableIx slot) -> charge 1 >> pure
                    (ViewVariableIx (if slot < original+depth then slot else slot+amount))))))
                (residualTemplateEvidence residual)
            pure (WholeResidual (maybe (ResidualTemplate formula) (describedResidualTemplate formula) metadata))
    _ -> pure template

-- A private component has no mathematical conclusion or replay forest of its
-- own. Its selected witnesses return to the original clause, which retains the
-- complete source forest. Only the component's leaves are prepared here.
prepareGroundRuleState
    :: Monad m => (Natural -> m ()) -> RuleState variable witness -> RuleInstantiation variable
    -> m (Either JoinFailure (GroundRule variable))
prepareGroundRuleState charge state instantiated = case ruleStateComponent state of
    Nothing -> prepareGroundRule charge (activeRule state) instantiated
    Just component -> prepareGroundRule charge (activeRule state)
        { rulePrefix = (rulePrefix (activeRule state))
            { prefixAtoms = Map.restrictKeys (ruleLeaves (activeRule state)) (componentPositions component)
            , prefixWholes = Map.restrictKeys (ruleWholeLeaves (activeRule state)) (componentPositions component)
            , prefixForest = Seq.empty } } instantiated

-- Every position is present in a scheduled tuple. Repeated requests retain
-- their distinct forest positions and therefore their distinct proof uses.
completeGroundRule
    :: Monad m => (Natural -> m ()) -> GroundRule variable -> Map Natural witness
    -> m (CompletedRule variable witness)
completeGroundRule charge (GroundRule instantiated _ forest) witnesses =
    CompletedRule instantiated <$> traverse tree forest
  where
    tree premise = do
        charge 1
        case premise of
            CompositePremiseTruth -> pure CompositePremiseTruth
            CompositePremiseLeaf position -> do
                charge (indexWork (Map.size witnesses) 1)
                pure (CompositePremiseLeaf (witnesses Map.! position))
            CompositePremiseAnd left right -> CompositePremiseAnd <$> tree left <*> tree right

-- The source must determine every binder. prepareRuleSnapshot checks acyclic
-- definition dependencies before these views construct initial seeds.
data ForwardRule = ForwardRule !Rule !(AtomTemplate RuleTermTemplate)

compileForwardRule
    :: Monad m => (Natural -> m ()) -> Natural -> AtomTemplate RuleTermTemplate
    -> AtomTemplate RuleTermTemplate -> m (Either JoinFailure ForwardRule)
compileForwardRule charge arity source = compileDescribedForwardRule charge arity source . AtomicLeaf

compileDescribedForwardRule
    :: Monad m => (Natural -> m ()) -> Natural -> AtomTemplate RuleTermTemplate
    -> RuleConclusion -> m (Either JoinFailure ForwardRule)
compileDescribedForwardRule charge arity source conclusion = Except.runExceptT do
    lift (charge 1)
    case source of
        MembershipAtomTemplate{} -> Except.throwE JoinInvalidForwardSource
        _ -> pure ()
    rule <- Except.ExceptT (compileConclusionRule charge arity [RulePremiseAtom source] conclusion)
    supplied <- State.execStateT (traverseAtomTemplateArguments variables source) Set.empty
    cover 0 (Set.toAscList supplied)
    pure (ForwardRule rule source)
  where
    variables term = do
        lift (lift (charge 1))
        case term of
            TemplateVariable (ViewVariableIx index) -> State.modify' (Set.insert index)
            TemplateClosed{} -> pure ()
            TemplateProvider _ arguments -> traverse_ variables arguments
            TemplateOrderedPair left right -> variables left >> variables right
    cover expected remaining = do
        lift (charge 1)
        case remaining of
            [] -> when (expected /= arity) (Except.throwE (JoinUndeterminedVariable expected))
            actual : rest -> if actual == expected then cover (expected + 1) rest
                else Except.throwE (JoinUndeterminedVariable expected)

forwardSourceSignature :: ForwardRule -> AtomSignature
forwardSourceSignature (ForwardRule _ source) = atomSignature source

applyForwardRule
    :: (Monad m, Eq variable) => (Natural -> m ()) -> Natural -> ForwardRule
    -> RowCapability -> AtomTemplate (SetTermTemplate variable) -> witness
    -> m (Either JoinFailure (Maybe (CompletedRule variable witness)))
applyForwardRule charge bound (ForwardRule rule source) capability row witness = do
    charge 1
    case capability of
        ExactAnswer -> pure (Left JoinSourceShapeRequired)
        SourceRow -> case ruleConclusion rule of
            AtomicLeaf atom -> fmap (fmap (\instantiated ->
                CompletedRule (fromJoin instantiated) [CompositePremiseLeaf witness]))
                <$> instantiateSourceRule charge bound (ruleArity rule) source atom row
            WholeLeaf template -> fmap (fmap (\values ->
                CompletedRule (RuleInstantiation values (WholeLeaf template)) [CompositePremiseLeaf witness]))
                <$> matchSourceParameters charge bound (ruleArity rule) source row

-- Definition registrations retain their ordinary forward implication meaning
-- for demand propagation as well as their eager observation-elimination view.
data RegisteredRule = RegisteredClassification !Rule | RegisteredDefinition !ForwardRule

-- Every admitted whole head is an ordinary producer. Discovery and exact
-- guards run through the same joins as relational heads; no covering row owns
-- activation or adds a logical premise.
wholeProducerEntries :: Natural -> RegisteredRule -> Map Natural RegisteredRule
wholeProducerEntries ordinal entry = case ruleConclusion (registeredRule entry) of
    WholeLeaf{} -> Map.singleton ordinal entry
    AtomicLeaf{} -> Map.empty

registeredRule :: RegisteredRule -> Rule
registeredRule (RegisteredClassification rule) = rule
registeredRule (RegisteredDefinition (ForwardRule rule _)) = rule

-- Checked source formulas connect relational views with compatible whole
-- propositions. These conservative shapes are derived execution metadata;
-- they grant no operand decomposition and never narrow the fixed domain.
describeRuleFormulas
    :: Monad m => (Natural -> m ())
    -> [([CoreType], CanonicalTerm ObjectId)] -> ([CoreType], CanonicalTerm ObjectId)
    -> RegisteredRule -> m (Either JoinFailure RegisteredRule)
describeRuleFormulas charge premises conclusion entry = Except.runExceptT do
    when (length premises /= length (ruleForest rule)) (Except.throwE JoinUnresolvedResult)
    (inputs,faithful,exact) <- if prefixAllDescribed (rulePrefix rule)
        then pure (prefixFormulaHeads (rulePrefix rule),prefixFaithfulAtoms (rulePrefix rule),prefixExactPremises (rulePrefix rule))
        else do
            described <- concat <$> zipWithM tree (ruleForest rule) premises
            certified <- foldM (\known (position,_,survives,_) -> do
                lift (charge (indexWork (Set.size known) 1))
                pure (if survives then Set.insert position known else known)) Set.empty described
            pure ([head' | (_,head',_,_) <- described],certified,
                Map.union (Map.fromList [(position,residual) | (position,_,_,residual) <- described]) (prefixExactPremises (rulePrefix rule)))
    let prefix = (rulePrefix rule) {prefixFormulaHeads = inputs,prefixAllDescribed = True,prefixFaithfulAtoms = faithful,
            prefixExactPremises = exact}
    described <- lift (describeRuleConclusion charge conclusion rule {rulePrefix = prefix,rulePremisePlans = exact})
    pure $ case entry of
        RegisteredClassification{} -> RegisteredClassification described
        RegisteredDefinition (ForwardRule _ source) -> RegisteredDefinition (ForwardRule described source)
  where
    rule = registeredRule entry
    shape (context,formula) = lift (residualShape (charge 1) context formula)
    tree forest (context,formula) = do
        lift (charge 1)
        case forest of
            CompositePremiseTruth -> pure []
            CompositePremiseAnd left right -> case formula of
                CAnd a b -> (<>) <$> tree left (context,a) <*> tree right (context,b)
                _ -> Except.throwE JoinUnresolvedResult
            CompositePremiseLeaf position -> do
                lift (charge (indexWork (Map.size (ruleLeaves rule)) 1))
                case Map.lookup position (ruleLeaves rule) of
                    Nothing -> pure []
                    Just atom -> do
                        head' <- shape (context,formula)
                        faithful <- lift (atomInputsSurvive charge atom (Just formula))
                        let residual = describedResidualTemplate formula (Source.SourceAtom atom)
                        plan <- lift (preparePremisePlan charge (ruleArity rule) (ruleAmbientTypes rule) (WholeResidual residual) residual)
                        pure [(position,(atomSignature atom,head'),faithful,plan)]

atomInputsSurvive
    :: Monad m => (Natural -> m ()) -> AtomTemplate RuleTermTemplate
    -> Maybe (CanonicalTerm ObjectId) -> m Bool
atomInputsSurvive charge atom = \case
    Nothing -> foldM (\known term -> if known then rigid term else pure False) True (toList atom)
    Just formula -> do
        slots <- collectRuleVariables charge Set.empty (toList atom)
        free <- canonicalFreeIndicesWith (charge 1) formula
        charge (fromIntegral (Set.size slots + Set.size free))
        pure (Set.isSubsetOf (Set.map (\(ViewVariableIx index) -> index) slots) free)
  where
    -- Pair construction has no expansion that can erase a slot. A named
    -- provider needs its checked formula before receiving that certificate.
    rigid term = charge 1 >> case term of
        TemplateProvider{} -> pure False
        TemplateOrderedPair a b -> rigid a >>= \left -> if left then rigid b else pure False
        _ -> pure True

describeRuleConclusion
    :: Monad m => (Natural -> m ()) -> ([CoreType],CanonicalTerm ObjectId) -> Rule -> m Rule
describeRuleConclusion charge (context,formula) rule = do
    (outputs,discovery) <- case ruleConclusion rule of
        WholeLeaf{} -> pure ([],False)
        AtomicLeaf atom -> do
            shape <- residualShape (charge 1) context formula
            -- Substitution into a first-order set slot is syntactically
            -- injective if that slot survives in checked Core. This Boolean
            -- certificate recovers no binding or view from an opaque operand.
            -- A matching head then fixes those parameter denotations. Missing
            -- premise views use their own exact-truth/finite fallback; reopening
            -- head discovery would discard these already determined inputs.
            faithful <- atomInputsSurvive charge atom (Just formula)
            pure ([(atomSignature atom,shape)],not faithful)
    pattern' <- Just <$> compileWholePattern charge (ruleArity rule) formula
    pure rule {ruleFormulaHeads = outputs <> prefixFormulaHeads (rulePrefix rule),
        ruleConclusionPattern = pattern',ruleNeedsHeadDiscovery = discovery,
        ruleExactConclusion = Just (case ruleConclusion rule of
            WholeLeaf residual -> residual
            AtomicLeaf atom -> describedResidualTemplate formula (Source.SourceAtom atom))}

-- Pure rule relevance and view order, not scoped evidence or proof authority.
-- A later owner expands initial evidence before freezing term support.
data RuleSnapshot = RuleSnapshot
    { selectedRules :: !(Map Natural RegisteredRule)
    , selectedHeads :: !(Set AtomSignature)
    , snapshotProducers :: !(Map AtomSignature (Map Natural RegisteredRule))
    , snapshotForwardSources :: !(Map AtomSignature (Map Natural ForwardRule))
    , snapshotForwardPredecessors :: !(Map AtomSignature (Set AtomSignature))
    , snapshotSourceRanks :: !(Map AtomSignature Int)
    , snapshotInitialRules :: !(Map Natural RegisteredRule)
    , snapshotWholeProducers :: !(Map Natural RegisteredRule)
    , snapshotTemplateSupport :: !(Maybe TemplateSupportView)
    , snapshotCounts :: !SnapshotCounts
    }

data SnapshotCounts = SnapshotCounts
    { snapshotRuleCount :: !Natural
    , snapshotPremiseCount :: !Natural
    , snapshotViewCount :: !Natural
    } deriving (Show, Eq)

-- All source-independent fields are already prepared by the owning catalogue.
-- Global postings are shared; the complete selected head set bounds their use.
preparedRuleSnapshot
    :: Map Natural RegisteredRule -> Set AtomSignature
    -> Map AtomSignature (Map Natural RegisteredRule)
    -> Map AtomSignature (Map Natural ForwardRule)
    -> Map AtomSignature (Set AtomSignature)
    -> Map AtomSignature Int -> Map Natural RegisteredRule
    -> Map Natural RegisteredRule
    -> TemplateSupportView -> SnapshotCounts -> RuleSnapshot
preparedRuleSnapshot rules heads producers sources predecessors ranks initial wholes support counts =
    RuleSnapshot rules heads producers sources predecessors ranks initial wholes (Just support) counts

snapshotRules :: RuleSnapshot -> Map Natural RegisteredRule
snapshotRules = selectedRules

snapshotHeads :: RuleSnapshot -> Set AtomSignature
snapshotHeads = selectedHeads

snapshotForwardOrder :: RuleSnapshot -> [(Natural, ForwardRule)]
snapshotForwardOrder = concatMap snd . snapshotForwardGroups

snapshotForwardGroups :: RuleSnapshot -> [(AtomSignature, [(Natural, ForwardRule)])]
-- An explicit enumeration for the exhaustive/test interface. Production E0
-- visits only actual source rows using the prepared ranks and source postings.
snapshotForwardGroups snapshot = sortOn (\(head',_) -> Map.findWithDefault 0 head' (snapshotSourceRanks snapshot))
    [(head',kept) | (head',views) <- Map.toAscList (snapshotForwardSources snapshot),
        let kept = Map.toAscList views,
        not (null kept)]

data RuleSnapshotFailure = CyclicDefinitionDependency !AtomSignature
    deriving (Show, Eq)

prepareRuleSnapshot
    :: Monad m => (Natural -> m ()) -> AtomSignature -> Map Natural RegisteredRule
    -> m (Either RuleSnapshotFailure RuleSnapshot)
prepareRuleSnapshot charge target registrations = do
    registry <- prepareRuleRegistry charge registrations
    selectRuleSnapshot charge target registry

-- Compiled descriptions and their producer index depend only on the admitted
-- registration set. They contain neither query support nor checked evidence.
data RuleRegistry = RuleRegistry
    !(Map RuleHead [(Natural, RegisteredRule)])
    ![(AtomSignature, [(Natural, ForwardRule, RuleHead)])]
    ![AtomSignature]

prepareRuleRegistry
    :: Monad m => (Natural -> m ()) -> Map Natural RegisteredRule -> m RuleRegistry
prepareRuleRegistry charge registrations = do
    (indexed,edges) <- foldM (\(known,sources) (ordinal,entry) -> do
        charge 1
        let (destination,forward) = case entry of
                RegisteredClassification rule -> (ruleSignature rule, Nothing)
                RegisteredDefinition view@(ForwardRule rule _) -> (ruleSignature rule, Just view)
        charge (indexWork (Map.size known) 3)
        let producers = Map.insertWith (<>) destination [(ordinal,entry)] known
        next <- case forward of
            Nothing -> pure sources
            Just view -> do
                charge (indexWork (Map.size sources) 3)
                pure (Map.insertWith (<>) (forwardSourceSignature view) [(ordinal,view,destination)] sources)
        pure (producers,next)) (Map.empty,Map.empty) (Map.toDescList registrations)
    (_,ordered,cycles) <- foldM (visit edges Set.empty) (Set.empty,[],[]) (Map.keys edges)
    charge (fromIntegral (length cycles))
    pure (RuleRegistry indexed ordered (reverse cycles))
  where
    -- Record cycle heads without rejecting unrelated queries. A selected result
    -- includes every definition predecessor, hence either the entire cycle or
    -- none of it. Filtering this order preserves the selected acyclic DFS order.
    visit edges active (finished,ordered,cycles) head' = do
        charge (indexWork (Set.size finished) 3)
        if Set.member head' finished then pure (finished,ordered,cycles) else do
            charge (indexWork (Set.size active) 3)
            if Set.member head' active then pure (finished,ordered,head' : cycles) else do
                charge (indexWork (Map.size edges) 3)
                let outgoing = Map.findWithDefault [] head' edges
                (done,sequence',found) <- foldM (\state (_,_,destination) -> case destination of
                    AtomicLeaf target -> visit edges (Set.insert head' active) state target
                    WholeLeaf{} -> pure state) (finished,ordered,cycles) outgoing
                pure (Set.insert head' done,(head',outgoing) : sequence',found)

selectRuleSnapshot
    :: Monad m => (Natural -> m ()) -> AtomSignature -> RuleRegistry
    -> m (Either RuleSnapshotFailure RuleSnapshot)
selectRuleSnapshot charge target (RuleRegistry indexed ordered cycles) = Except.runExceptT do
    (producers,selected) <- lift (reachable Map.empty Map.empty (Seq.singleton (AtomicLeaf target)))
    lift (charge (fromIntegral (Map.size producers)))
    let heads = Set.fromList [head' | AtomicLeaf head' <- Map.keys producers]
    for_ cycles \head' -> do
        lift (charge (indexWork (Set.size heads) 3))
        when (Set.member head' heads) (Except.throwE (CyclicDefinitionDependency head'))
    (edges,groups) <- lift $ foldM (\(known,groups) (head',outgoing) -> do
        kept <- filterM (\(ordinal,_,_) -> do
            charge (indexWork (Map.size selected) 1)
            pure (Map.member ordinal selected)) outgoing
        if null kept then charge 1 >> pure (known,groups) else do
            charge (indexWork (Map.size known) 3)
            views <- traverse (\(ordinal,view,_) -> charge 1 >> pure (ordinal,view)) kept
            pure (Map.insert head' kept known,(head',views) : groups)) (Map.empty,[]) ordered
    lift (charge (fromIntegral (length groups)))
    let ranks = Map.fromList [(head',rank) | (rank,(head',_)) <- zip [0..] (reverse groups)]
    (initial,counts) <- lift $ foldM (\(initial,SnapshotCounts rules premises views) (ordinal,entry) -> do
        charge 1
        let rule = registeredRule entry
        pure (if ruleIsInitial rule then Map.insert ordinal entry initial else initial,
            SnapshotCounts (rules+1) (premises + fromIntegral (rulePremiseCount rule))
                (views + case entry of RegisteredDefinition{} -> 1; _ -> 0)))
        (Map.empty,SnapshotCounts 0 0 0) (Map.toAscList selected)
    producerPostings <- lift $ traverse (\bucket -> charge (fromIntegral (length bucket)) >> pure (Map.fromDistinctAscList bucket))
        (Map.fromList [(head',bucket) | (AtomicLeaf head',bucket) <- Map.toAscList producers])
    sources <- lift $ traverse (\bucket -> charge (fromIntegral (length bucket)) >>
        pure (Map.fromList [(ordinal,view) | (ordinal,view,_) <- bucket])) edges
    predecessors <- lift $ foldM (\known (source, outgoing) ->
        foldM (\indexed (_,_,result) -> case result of
            WholeLeaf{} -> pure indexed
            AtomicLeaf atom -> do
                charge (2 * indexWork (Map.size indexed) 3)
                let prior = Map.findWithDefault Set.empty atom indexed
                charge (indexWork (Set.size prior) 3)
                pure (Map.insert atom (Set.insert source prior) indexed)) known outgoing)
        Map.empty (Map.toAscList edges)
    wholeProducers <- lift $ foldM (\known (ordinal,entry) -> do
        charge (indexWork (Map.size known) 1)
        pure (Map.union (wholeProducerEntries ordinal entry) known)) Map.empty (Map.toAscList selected)
    pure (RuleSnapshot selected heads producerPostings sources predecessors ranks initial wholeProducers Nothing counts)
  where
    reachable seen selected queue = case Seq.viewl queue of
        Seq.EmptyL -> pure (seen,selected)
        head' Seq.:< rest -> do
            charge (indexWork (Map.size seen) 3)
            if Map.member head' seen then reachable seen selected rest else do
                charge (indexWork (Map.size indexed) 3)
                let bucket = Map.findWithDefault [] head' indexed
                (more,pending) <- foldM (\(known,waiting) (ordinal,entry) -> do
                    charge (indexWork (Map.size known) 1)
                    next <- foldM (\queries premise -> charge 1 >> pure (queries Seq.|> premise))
                        waiting (rulePremiseSignatures (registeredRule entry))
                    pure (Map.insert ordinal entry known,next)) (selected,rest)
                    bucket
                reachable (Map.insert head' bucket seen) more pending

ruleTermTemplates :: Rule -> [RuleTermTemplate]
ruleTermTemplates rule = concatMap atomTerms (conclusionAtoms (ruleConclusion rule) <> Map.elems (ruleLeaves rule))

conclusionAtoms :: NotionLeaf atom whole -> [atom]
conclusionAtoms (AtomicLeaf atom) = [atom]
conclusionAtoms WholeLeaf{} = []

atomTerms :: AtomTemplate term -> [term]
atomTerms = toList

-- Before support is frozen, the actual source row bounds every matched binder.
-- A template variable can therefore expand to at most the largest source term.
-- This bounds reconstruction without imposing the later fixed seed domain.
applyInitialForwardRule
    :: (Monad m, Eq variable) => (Natural -> m ()) -> ForwardRule
    -> RowCapability -> AtomTemplate (SetTermTemplate variable) -> witness
    -> m (Either JoinFailure (Maybe (CompletedRule variable witness)))
applyInitialForwardRule charge view@(ForwardRule rule _) capability row witness = do
    supplied <- traverse (expandedSize charge 1) (atomTerms row)
    let largest = maximum (0 : supplied)
    results <- traverse (expandedSize charge largest) (concatMap atomTerms (conclusionAtoms (ruleConclusion rule)))
    applyForwardRule charge (maximum (largest : results)) view capability row witness

expandedSize :: Monad m => (Natural -> m ()) -> Natural -> SetTermTemplate variable -> m Natural
expandedSize charge variableSize term = do
    charge 1
    case term of
        TemplateVariable{} -> pure variableSize
        TemplateClosed{} -> pure 1
        TemplateProvider _ arguments -> (1 +) . sum <$> traverse (expandedSize charge variableSize) arguments
        TemplateOrderedPair left right -> (\a b -> 1 + a + b)
            <$> expandedSize charge variableSize left <*> expandedSize charge variableSize right

completeInitialRule
    :: Monad m => (Natural -> m ()) -> Rule
    -> m (Either JoinFailure (Maybe (CompletedRule variable witness)))
completeInitialRule charge rule = do
    charge 1
    if not (ruleIsInitial rule) then pure (Right Nothing)
    else Except.runExceptT do
        result <- case ruleConclusion rule of
            AtomicLeaf atom -> AtomicLeaf <$> traverseAtomTemplateArguments closed atom
            WholeLeaf residual -> pure (WholeLeaf residual)
        pure (Just (CompletedRule (RuleInstantiation Map.empty result) []))
  where
    closed term = do
        lift (charge 1)
        case term of
            TemplateVariable (ViewVariableIx index) -> Except.throwE (JoinInvalidVariable index)
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse closed arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> closed left <*> closed right

-- Recover the exact source forest, rather than exposing the physical leaf map.
ruleDescription :: Rule -> (Natural, [RulePremiseTree RuleTermTemplate], RuleConclusion)
ruleDescription rule = (ruleArity rule, rebuild <$> ruleForest rule, ruleConclusion rule)
  where
    rebuild CompositePremiseTruth = RulePremiseResidual (ResidualTemplate CTruth)
    rebuild (CompositePremiseLeaf position) = case Map.lookup position (ruleLeaves rule) of
        Just atom -> RulePremiseAtom atom
        Nothing -> case ruleWholeLeaves rule Map.! position of
            WholeUniversal body -> RulePremiseUniversal body
            WholeResidual template -> RulePremiseResidual template
    rebuild (CompositePremiseAnd left right) = RulePremiseAnd (rebuild left) (rebuild right)
