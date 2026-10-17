{-# LANGUAGE NoImplicitPrelude #-}

-- | Finite rule scheduling over an immutable support and admitted rule snapshot.
-- Evidence keys belong to the caller: they must retain source-row capability
-- and all observable eligibility distinctions, but never proof history. Use
-- interned/atomic keys so scheduler comparisons do not traverse source terms.
module Felix.Checking.Notion.Evaluation
    ( RuleAnswer(..)
    , RuleEvaluator(..), WholeCandidates(..)
    , evaluateRules
    , solveRules
    , solveCatalogRules, solveCatalogLeaves
    , evaluateCatalogRules
    , prepareRuleSupport
    , RuleOutcome(..)
    , RuleSession, RuleStart(..), initializeCatalogLeaves
    , ruleSessionStatus, ruleSessionAnswer, focusRuleSession, advanceRuleSession, deliverRuleSession, finishRuleSession
    , queryRuleSession
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Notion.Catalog qualified as Catalog
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Notion.Ground qualified as Ground
import Felix.Checking.Notion.TermIndex qualified as Terms
import Felix.Checking.Notion.Join
import Felix.Checking.Notion.Pattern
import Felix.Checking.Notion.Relational
import Felix.Checking.Notion.Request
import Felix.Checking.Notion.FormulaIndex (FormulaId, ResidualShape)
import Felix.Checking.Notion.FormulaIndex qualified as Formulas
import Felix.Checking.Notion.WholePattern (WholePattern)
import Felix.Checking.Notion.Rule
import Felix.Checking.Notion.Support
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.Unification
import Control.Monad (foldM, join, unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.IntMap.Strict qualified as IntMap
import Data.List (lookup, partition, sortOn)
import Data.Maybe (catMaybes)
import Data.Ord (Down(..))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Numeric.Natural (Natural)

data RuleAnswer variable key witness = RuleAnswer
    { ruleAnswerLeaf :: !(NotionLeaf (AtomTemplate (SetTermTemplate variable)) FormulaId)
    , ruleAnswerKey :: !key
    , ruleAnswerCapability :: !RowCapability
    , ruleAnswerWitness :: !witness
    }

data RuleEvaluator m variable bucket key witness = RuleEvaluator
    { ruleInputs :: Natural -> m (RuleInputs variable)
    , ruleCharge :: Natural -> m ()
    -- Equality-class tuple of complete operands; concrete substitutions remain exact.
    -- This filters candidates only; ruleConverted still checks actual evidence.
    , ruleGroundBucket :: AtomTemplate (SetTermTemplate variable) -> m bucket
    -- Diagnostic phase boundaries only: no charge, evidence, or search policy.
    , rulePhase :: Text -> m ()
    , ruleEvent :: Diagnostics.RuleEvent -> m ()
    -- The callback retains the exact occurrence and acquired witness recipes.
    -- Its key is a finite atom/eligibility identity, not a new derivation ID.
    , ruleCompleted :: Natural -> CompletedRule variable witness
        -> NotionLeaf (AtomTemplate (SetTermTemplate variable)) FormulaId -> m (Maybe (key, witness))
    -- Called only for a fully ground request, with an eligible argument row
    -- or identical whole truth. The owner checks denotation and its evidence.
    -- A successful key must distinguish ExactAnswer from source-capable rows.
    , ruleConverted :: AtomTemplate (SetTermTemplate variable) -> RuleAnswer variable key witness
        -> m (Maybe (key, witness))
    -- Representative and whether another endpoint exists. These describe
    -- candidate lookup only; neither supplies a concrete clause binding.
    , ruleArgumentClass :: variable -> m (variable,Bool)
    -- False certifies that structural incompatibility needs no equality
    -- fallback. With transport, complete operand constraints still filter
    -- partial producers through ruleTermsMayAgree and the supplied relation.
    -- Two incomplete operands may instead require a conservative answer.
    , ruleHasEqualityTransport :: !Bool
    , ruleRejected :: JoinFailure -> m ()
    , ruleWholeRequest :: Natural -> Maybe Natural -> Map ViewVariableIx (SetTermTemplate variable)
        -> WholeTemplate RuleTermTemplate -> m (WholeRequest variable)
    , ruleWholeEvidence :: WholeRequest variable -> m (Maybe (key, witness))
    -- A complete finite access path for the primitive alternative of an open
    -- whole premise. Ordinary exact sources and producers remain subscribed.
    , ruleWholeBindings :: Rule -> WholeWaiting variable
        -> m (Maybe (ViewVariableIx,[SetTermTemplate variable]))
    , ruleWholeCandidates :: Set AtomSignature -> ResidualShape -> m (Maybe WholeCandidates)
    , ruleFormulaShape :: FormulaId -> m ResidualShape
    , ruleWholeSources :: ResidualShape -> m [FormulaId]
    , ruleAtomicFormula :: AtomTemplate (SetTermTemplate variable) -> m (Maybe FormulaId)
    , ruleWholeTruthAvailable :: AtomSignature -> m Bool
    , ruleSourcePossible :: Set AtomSignature -> RuleHead -> Map Int Bool
        -> m (Bool,Map Int Bool)
    -- True certifies a nominal leaf whose denotation cannot hide a constructor.
    , ruleOpaqueIsRigid :: SetTermTemplate variable -> m Bool
    , ruleArgumentValue :: SetTermTemplate variable -> m (Maybe variable)
    , ruleMatchWhole :: WholePattern -> FormulaId -> m (Maybe (Map ViewVariableIx variable))
    -- Compare checked partial formulas; only complete requested operands may
    -- constrain producer slots. This never supplies evidence or opens operands.
    , ruleMatchPartialWhole :: Rule -> WholeWaiting variable -> Rule
        -> Map ViewVariableIx (SetTermTemplate (Maybe variable))
        -> m (Maybe (Map ViewVariableIx variable))
    -- A support cursor varies one slot. Prepare its fixed formula operands
    -- once; the returned filter grants neither bindings nor proof evidence.
    , rulePreparePartialWhole :: Rule -> WholeWaiting variable -> Rule
        -> Map ViewVariableIx (SetTermTemplate (Maybe variable)) -> ViewVariableIx
        -> m (SetTermTemplate (Maybe variable) -> m Bool)
    , rulePrepareWholeMatch :: Rule -> ResidualTemplate
        -> Map ViewVariableIx (SetTermTemplate (Maybe variable)) -> ViewVariableIx -> FormulaId
        -> m (SetTermTemplate (Maybe variable) -> m Bool)
    -- Complete atomic operand positions certified by the whole formula. No
    -- clause variable is recovered from inside an opaque operand.
    , ruleAtomicInputs :: AtomTemplate () -> FormulaId -> m (Maybe (Map Int variable))
    -- Atomic heads retain all their operand positions in Core: declaration
    -- admission rejects abbreviation heads, whose expanded bodies instead
    -- supply their own atomic or whole descriptions.
    -- A rejection must hold for every completion of the holes. This compares
    -- denotations only; it cannot return bindings or manufacture a row view.
    , ruleTermsMayAgree :: SetTermTemplate (Maybe variable) -> SetTermTemplate (Maybe variable) -> m Bool
    , ruleOpaqueSupport :: !(Maybe (OpaqueInterpreter m variable))
    , ruleSupportTemplates :: Rule -> m [(Natural,[SupportTermTemplate])]
    }

data WholeCandidates = WholeCandidates
    { wholeCandidateRules :: !Catalog.CandidateRules
    , atomicCandidateRules :: !(Map Natural RegisteredRule)
    }

data Query = LeafQuery !(NotionLeaf AtomSignature FormulaId) !RequestId
    | ComponentQuery !Int | WholeSchemaQuery !Int | ProducerQuery !Int | OpenWholeQuery !Int
    deriving (Show, Eq, Ord)

data TableKey key = LogicalKey !key | ComponentKey !Int ![Int]
    deriving (Eq, Ord)

data TableAnswer variable key witness
    = LogicalAnswer !(RuleAnswer variable key witness)
    | ComponentAnswer !Int ![Int] !(Map ViewVariableIx (SetTermTemplate variable)) !(Map Natural witness)

type SelectedPremise key = (TableKey key, [(ViewVariableIx,Int)])
type Selection key = Map Natural (SelectedPremise key)

-- Each selected premise tuple retains its own finite fallback. Candidate
-- constraints narrow assignments without discarding different argument views.
type DiscoveryKey key = (Query, Natural, [(Natural,SelectedPremise key)])

data ComponentDemand variable = ComponentDemand
    { demandOrdinal :: !Natural
    , demandRule :: !Rule
    , demandComponent :: !BodyComponent
    , demandInputs :: !(Map ViewVariableIx (SetTermTemplate variable))
    , demandConstraints :: !(Map ViewVariableIx variable)
    , demandWholeSource :: !(Maybe FormulaId)
    , demandBoolean :: !Bool
    , demandResults :: !(Set [Int])
    }

data ComponentWaiter variable key witness = ComponentWaiter
    !Query !Natural !(Selection key) !(RuleState variable witness)

data SearchBucket variable bucket
    = ComponentBucket !Int
    | ProducerBucket !Int
    | WholeSchemaBucket !Int
    | LogicalBucket !(NotionLeaf (Either AtomSignature bucket) FormulaId)
    | ArgumentBucket !AtomSignature !Int !variable
    deriving (Eq,Ord)
type TableResult variable key witness = RelationalResult Query (TableAnswer variable key witness) (TableKey key)

logicalAnswer :: TableAnswer variable key witness -> RuleAnswer variable key witness
logicalAnswer (LogicalAnswer answer) = answer
logicalAnswer ComponentAnswer{} = error "a private component result entered a mathematical request"

leafIdentifier :: Query -> RequestId
leafIdentifier (LeafQuery _ identifier) = identifier
leafIdentifier _ = error "a private discovery query entered a mathematical premise"


data Continuation = PartialContinuation !Int | GroundContinuation !Int !RequestId
    | ExactContinuation !RequestId | ComponentContinuation !Int | EliminationContinuation !Int | WholeContinuation !Int
    deriving (Eq, Ord)

data GroundEntry variable witness = GroundEntry
    !Query !Natural !(Ground.GroundInstance variable witness)

data Waiting variable key witness = Waiting
    !Query !RequestId !Natural !(Selection key) !Natural !(RuleWaiting variable witness)

data RuleWork m variable key witness
    = ProducerWork !RequestId !Catalog.CandidateRules
    | AlternateHeadWork !RequestId !Natural !RegisteredRule
    | ForwardWork !(AtomTemplate (SetTermTemplate variable)) !(RuleAnswer variable key witness)
        !(Map Natural ForwardRule)
    | ConversionWork !(AtomTemplate (SetTermTemplate variable)) !(RuleAnswer variable key witness)
    | GroundWork !Int
    | WholeSourceWork !Query ![FormulaId]
    | WholeProducerWork !RequestId !Catalog.CandidateRules
    | OpenWholeWork !Int !Catalog.CandidateRules
    | OpenAtomicWork !Int !(Map Natural RegisteredRule)
    | ExactPremiseWork !Query !Natural !(Selection key) !(RuleState variable witness) !(WholeWaiting variable)
    | BindWholeWork !Query !Natural !(Selection key) !(RuleState variable witness)
        !ViewVariableIx ![SetTermTemplate variable]
    | AtomicTruthWork !RequestId !(Map Natural RegisteredRule)
    | EnumerateWork !Query !Natural !(RuleState variable witness) ![ViewVariableIx] !(Assignment variable key witness) !Natural
        !(Maybe (SetTermTemplate (PatternVariable variable))) !(Maybe (AssignmentFilter m variable)) !(SupportCursor variable)
    | MissingViewWork !RequestId !(RuleAnswer variable key witness)
    | FallbackWork !(Map (DiscoveryKey key) Natural) !(RuleAnswer variable key witness)

-- Prepared lazily on the cursor's first turn, then retained across resumptions.
-- These query-local filters share interpretation work, not logical answers.
type AssignmentFilter m variable = SetTermTemplate (Maybe variable) -> m Bool

data Assignment variable key witness
    = MatchAssignment !(Selection key) !Natural !(RuleAnswer variable key witness)
    | RequestAssignment !(Selection key) !(WholeWaiting variable)
    | CompleteAssignment

data OpenDemand variable = OpenDemand
    { openDemandRule :: !Rule
    , openDemandWaiting :: !(WholeWaiting variable)
    , openDemandShape :: !Int
    , openDemandConstraints :: !(Map ViewVariableIx variable)
    , openDemandFormulas :: !(Set FormulaId)
    }

data Evaluation variable key witness = Evaluation
    { queries :: !(RequestTable variable)
    , continuationIds :: !(Map (Query, Natural, [(Natural,SelectedPremise key)], Natural) Int)
    , continuations :: !(IntMap.IntMap (Waiting variable key witness))
    , advancedSelections :: !(Set (Query,Natural,[(Natural,SelectedPremise key)]))
    , fallbackStates :: !(Map (DiscoveryKey key) (RuleState variable witness))
    , fallbackWaiters :: !(Map RequestId (Map (DiscoveryKey key) Natural))
    , missingViewRequests :: !(Map RequestId (Map key (RuleAnswer variable key witness)))
    , wholeTruthHeads :: !(Map AtomSignature Bool)
    , possibleHeads :: !(Map Int Bool)
    , possibleRules :: !(Map Natural Bool)
    , atomicInputMatches :: !(Map (AtomSignature,FormulaId) (Maybe (Map Int variable)))
    , requestInputKeys :: !(Map RequestId (Map Int variable))
    , requestHeadFormulas :: !(Map RequestId (Maybe FormulaId))
    , activeSourceHeads :: !(Set AtomSignature)
    , activeSourceArguments :: !(Set (AtomSignature,Int,variable))
    , instanceTerms :: !(Terms.Nodes variable)
    , instanceIds :: !(Map (Natural, Maybe Int, [Int]) Int)
    , groundInstances :: !(IntMap.IntMap (GroundEntry variable witness))
    , truthProducersOpened :: !(Map (Natural, Map Int variable, Map ViewVariableIx variable) Int)
    , producerDemands :: !(IntMap.IntMap (Natural,Rule,RequestId,Map ViewVariableIx variable))
    , componentIds :: !(Map (Natural, Int, [(ViewVariableIx,Maybe Int)], [(ViewVariableIx,variable)], Maybe FormulaId) Int)
    , componentDemands :: !(IntMap.IntMap (ComponentDemand variable))
    , componentWaiters :: !(IntMap.IntMap (ComponentWaiter variable key witness))
    , eliminationWaiters :: !(IntMap.IntMap (Query, Natural, WholeElimination, RuleState variable witness))
    , wholeShapeIds :: !(Map Int [(ResidualShape,Int)])
    , wholeShapes :: !(IntMap.IntMap ResidualShape)
    , openWholeIds :: !(Map (Natural,Natural,[(ViewVariableIx,Maybe Int)],[(ViewVariableIx,variable)]) Int)
    , openWholeDemands :: !(IntMap.IntMap (OpenDemand variable))
    , openWholeWaiters :: !(IntMap.IntMap (Query,Natural,Selection key,RuleState variable witness,WholeWaiting variable))
    }

-- The session owns both the mathematical request table and its private join
-- state. Its callbacks belong to the same immutable scope and evidence policy.
-- Advancing or focusing it preserves its prepared domain and selected program.
type RuleRelations m variable bucket key witness =
    RelationalEvaluator (State.StateT (Evaluation variable key witness) m) Query
        (TableAnswer variable key witness) (TableKey key) (Maybe Continuation) (RuleWork m variable key witness)
        (SearchBucket variable bucket)

type RuleTable m variable bucket key witness =
    RelationalSession Query (TableAnswer variable key witness) (TableKey key) (Maybe Continuation)
        (RuleWork m variable key witness) (SearchBucket variable bucket)

type RuleLeaf variable = NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeRequest variable)

data RuleSession m variable bucket key witness = RuleSession
    { sessionEvaluator :: !(RuleRelations m variable bucket key witness)
    , sessionRequest :: RuleLeaf variable -> State.StateT (Evaluation variable key witness) m (Either PatternRejection Query)
    , sessionMissing :: TableResult variable key witness
        -> State.StateT (Evaluation variable key witness) m [(Natural, AtomTemplate (SetTermTemplate variable))]
    , sessionTable :: !(RuleTable m variable bucket key witness)
    , sessionJoins :: !(Evaluation variable key witness)
    }

data RuleStart m variable bucket key witness
    = PreparedAnswer !(RuleAnswer variable key witness)
    | StartedRules !(RuleSession m variable bucket key witness)

ruleSessionStatus :: RuleSession m variable bucket key witness -> RelationalStatus
ruleSessionStatus = relationalStatus . sessionTable

ruleSessionAnswer
    :: (Monad m, Ord key) => RuleSession m variable bucket key witness
    -> m (Maybe (RuleAnswer variable key witness))
ruleSessionAnswer session = fmap logicalAnswer <$> State.evalStateT
    (relationalRootAnswer (sessionEvaluator session) (sessionTable session)) (sessionJoins session)

focusRuleSession
    :: Monad m => RuleLeaf variable -> RuleSession m variable bucket key witness
    -> m (Either PatternRejection (RuleSession m variable bucket key witness))
focusRuleSession goal session = do
    (requested,joins) <- State.runStateT (sessionRequest session goal >>= traverse
        (\root -> focusRelational (sessionEvaluator session) root (sessionTable session))) (sessionJoins session)
    pure ((\table -> session {sessionTable = table, sessionJoins = joins}) <$> requested)

queryRuleSession
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleLeaf variable -> RuleSession m variable bucket key witness
    -> m (Either PatternRejection (Maybe (RuleAnswer variable key witness), RuleSession m variable bucket key witness))
queryRuleSession goal session = do
    (requested,joins) <- State.runStateT (sessionRequest session goal >>= traverse
        (\root -> queryRelational (sessionEvaluator session) root (sessionTable session))) (sessionJoins session)
    pure ((\(answer,table) -> (logicalAnswer <$> answer,session {sessionTable = table, sessionJoins = joins})) <$> requested)

advanceRuleSession
    :: (Monad m, Ord variable, Ord bucket, Ord key) => Natural -> RuleSession m variable bucket key witness
    -> m (RuleSession m variable bucket key witness)
advanceRuleSession quantum session = do
    (table,joins) <- State.runStateT
        (advanceRelational quantum (sessionEvaluator session) (sessionTable session)) (sessionJoins session)
    pure session {sessionTable = table, sessionJoins = joins}

deliverRuleSession
    :: Monad m => [RuleAnswer variable key witness] -> RuleSession m variable bucket key witness
    -> m (RuleSession m variable bucket key witness)
deliverRuleSession answers session = do
    (table,joins) <- State.runStateT (deliverRelational (sessionEvaluator session)
        (RelationalStep (LogicalAnswer <$> answers) [] []) (sessionTable session)) (sessionJoins session)
    pure session {sessionTable = table, sessionJoins = joins}

finishRuleSession
    :: Monad m => RuleSession m variable bucket key witness
    -> m (RelationalResult Query (RuleAnswer variable key witness) key,
        [(Natural, AtomTemplate (SetTermTemplate variable))])
finishRuleSession session = State.evalStateT (do
    result <- finishRelational (sessionEvaluator session) (sessionTable session)
    missing <- sessionMissing session result
    let public = RelationalResult (relationalSaturated result) (relationalRequests result)
            (Map.fromDistinctAscList [(key,answer) | (LogicalKey key,LogicalAnswer answer) <- Map.toAscList (relationalAnswers result)])
            (Set.fromDistinctAscList [key | LogicalKey key <- Set.toAscList (relationalRootAnswers result)])
            (relationalUnansweredRequests result) (relationalDeliveryCount result)
    pure (public,missing)) (sessionJoins session)

-- | The owner supplies scope/policy-eligible facts and alias terms. Relevant
-- observations, closed results, and acyclic initial views establish the seed
-- domain before support is frozen. Search queries and subsequent rows are then
-- support-admitted; joins retain their original filter across shared requests.
-- Rejections are reported to the owner; exhaustion aborts through its shared
-- account and is never returned as completed absence. On completed absence,
-- report ground missing premises with their actual requesting rule ordinals.
evaluateRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either PatternRejection
        (RelationalResult Query (RuleAnswer variable key witness) key, [(Natural, AtomTemplate (SetTermTemplate variable))]))
evaluateRules owner snapshot facts aliases goal =
    runRules False owner snapshot facts aliases goal >>= \case
        Left failure -> pure (Left failure)
        Right (FoundAnswer _) -> error "exhaustive formation stopped at an initial answer"
        Right (SearchAnswers result missing) -> pure (Right (result, missing))

data RuleOutcome variable key witness
    = FoundAnswer !(RuleAnswer variable key witness)
    | SearchAnswers !(RelationalResult Query (RuleAnswer variable key witness) key)
        ![(Natural, AtomTemplate (SetTermTemplate variable))]

-- | Stop at a checked root answer; retain exhaustive evaluation for parity.
solveRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either PatternRejection (RuleOutcome variable key witness))
solveRules = runRules True

-- Direct and initial answers still short-circuit through the common admission
-- path. Every nontrivial chain uses the same founded, tabled evaluator; an
-- unrelated catalogue cycle never switches the query to another algorithm.
solveCatalogRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> Catalog.Catalog source
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable) -> m RuleSnapshot
    -> m (Either PatternRejection (RuleOutcome variable key witness))
solveCatalogRules owner catalog facts aliases goal = solveCatalogLeaves owner catalog facts aliases (AtomicLeaf goal)

solveCatalogLeaves
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> Catalog.Catalog source
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeRequest variable) -> m RuleSnapshot
    -> m (Either PatternRejection (RuleOutcome variable key witness))
solveCatalogLeaves owner catalog facts aliases goal prepareSnapshot = do
    snapshot <- prepareSnapshot
    runRulesWith True owner (\active pattern' -> Catalog.matchingPossiblePatternRules (ruleCharge owner) active (ruleOpaqueIsRigid owner)
        (canonicalPatternAtom pattern') catalog) snapshot facts aliases goal

-- All roots are supplied before preparation. Later focusing changes demand,
-- never support or evidence: even directly solved siblings remain domain inputs.
-- The input action describes only the original scope. Delay materializing it
-- until freezing support; an initial founded answer does not need that domain.
initializeCatalogLeaves
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> Catalog.Catalog source -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> m [SetTermTemplate variable]
    -> [RuleLeaf variable] -> RuleLeaf variable
    -> m (Either PatternRejection (RuleStart m variable bucket key witness))
initializeCatalogLeaves owner catalog snapshot facts prepareInputs roots goal =
    prepareGroupSupport True owner snapshot facts prepareInputs roots goal >>= \case
        Left answer -> pure (Right (PreparedAnswer answer))
        Right (support,answers) -> fmap StartedRules <$> initializeSupportedRules True owner
            (\active pattern' -> Catalog.matchingPossiblePatternRules (ruleCharge owner) active (ruleOpaqueIsRigid owner)
                (canonicalPatternAtom pattern') catalog) support snapshot answers goal

evaluateCatalogRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => RuleEvaluator m variable bucket key witness -> Catalog.Catalog source -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either PatternRejection
        (RelationalResult Query (RuleAnswer variable key witness) key, [(Natural, AtomTemplate (SetTermTemplate variable))]))
evaluateCatalogRules owner catalog snapshot facts aliases goal =
    runRulesWith False owner (\active pattern' -> Catalog.matchingPossiblePatternRules (ruleCharge owner) active (ruleOpaqueIsRigid owner)
        (canonicalPatternAtom pattern') catalog) snapshot facts aliases (AtomicLeaf goal) >>= \case
            Left failure -> pure (Left failure)
            Right (SearchAnswers result missing) -> pure (Right (result,missing))
            Right FoundAnswer{} -> error "exhaustive catalogue evaluation stopped at an initial answer"

runRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either PatternRejection (RuleOutcome variable key witness))
runRules stopOnAnswer owner snapshot facts aliases goal = runRulesWith stopOnAnswer owner candidates snapshot facts aliases (AtomicLeaf goal)
  where
    candidates _active requested = do
        let indexed = snapshotProducers snapshot
        ruleCharge owner (indexWork (Map.size indexed) 3)
        Catalog.candidateRulesFromMap (ruleCharge owner)
            (Map.findWithDefault Map.empty (atomSignature (canonicalPatternAtom requested)) indexed)

runRulesWith
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> (Set AtomSignature -> CanonicalPattern variable -> m Catalog.CandidateRules)
    -> RuleSnapshot -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeRequest variable)
    -> m (Either PatternRejection (RuleOutcome variable key witness))
runRulesWith stopOnAnswer owner candidates snapshot facts aliases goal = do
    prepareLeafSupport stopOnAnswer owner snapshot facts aliases goal >>= \case
        Left answer -> pure (Right (FoundAnswer answer))
        Right (support, answers) ->
            fmap (uncurry SearchAnswers) <$> evaluateSupportedRules stopOnAnswer owner candidates support snapshot answers goal

-- | Complete the initial row closure and freeze its exact support before
-- ordinary search. The exhaustive adapter uses this same evidence-producing
-- path; it does not reconstruct seeds from a separate description of rules.
prepareRuleSupport
    :: (Monad m, Ord variable, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> AtomTemplate (SetTermTemplate variable)
    -> m (Either (RuleAnswer variable key witness)
        (FrozenSupport variable, [RuleAnswer variable key witness]))
prepareRuleSupport stopOnAnswer owner snapshot facts aliases goal = prepareLeafSupport stopOnAnswer owner snapshot facts aliases (AtomicLeaf goal)

prepareLeafSupport
    :: (Monad m, Ord variable, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> [SetTermTemplate variable]
    -> NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeRequest variable)
    -> m (Either (RuleAnswer variable key witness) (FrozenSupport variable, [RuleAnswer variable key witness]))
prepareLeafSupport stopOnAnswer owner snapshot facts aliases goal =
    prepareGroupSupport stopOnAnswer owner snapshot facts (pure aliases) [goal] goal

prepareGroupSupport
    :: (Monad m, Ord variable, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> RuleSnapshot
    -> [RuleAnswer variable key witness] -> m [SetTermTemplate variable]
    -> [RuleLeaf variable] -> RuleLeaf variable
    -> m (Either (RuleAnswer variable key witness) (FrozenSupport variable, [RuleAnswer variable key witness]))
prepareGroupSupport stopOnAnswer owner snapshot facts prepareInputs roots goal = do
    rulePhase owner "initial-rows-start"
    initial <- Except.runExceptT do
        ancestors <- viewAncestors Set.empty (case goal of AtomicLeaf atom -> [atomSignature atom]; WholeLeaf{} -> [])
        pinned <- case goal of
            AtomicLeaf atom | stopOnAnswer -> Just <$> traverseAtomTemplateArguments pin atom
            _ -> pure Nothing
        direct <- foldM (\known (row,answer) -> do
            charge (indexWork (Set.size (snapshotHeads snapshot)) 3)
            if Set.member (atomSignature row) (snapshotHeads snapshot)
                then insert ancestors pinned known row answer else pure known) (Map.empty,Set.empty,Map.empty) (atomicRows facts)
        lift (rulePhase owner "initial-closed-start")
        closed <- foldM (\known (ordinal,entry) -> do
            event (Diagnostics.Count Diagnostics.InitialResult 1)
            event (Diagnostics.EnterRegistration ordinal)
            completed <- completeInitialRule charge (registeredRule entry)
            next <- publish ancestors pinned known ordinal completed
            event Diagnostics.LeaveRegistration
            pure next) direct (Map.toAscList (snapshotInitialRules snapshot))
        lift (rulePhase owner "initial-views-start")
        (initial,_,wholes) <- initialViews ancestors pinned closed
        lift (rulePhase owner "initial-views-finished")
        answers <- fmap concat (traverse (\bucket -> do
            charge (fromIntegral (Map.size bucket))
            pure (Map.elems bucket)) (Map.elems initial))
        pure (answers <> Map.elems wholes <> [answer | answer@RuleAnswer{ruleAnswerLeaf = WholeLeaf{}} <- facts])
    case initial of
        Left answer -> pure (Left answer)
        Right answers -> do
            aliases <- prepareInputs
            let seeds = aliases <> concat [atomTerms atom | AtomicLeaf atom <- roots] <> concatMap (atomTerms . fst) (atomicRows answers)
            rulePhase owner "support-start"
            scoped <- for [(ordinal,registeredRule entry) | (ordinal,entry) <- Map.toAscList (snapshotRules snapshot),
                    ruleIsScoped (registeredRule entry)] \(ordinal,rule) -> do
                ruleCharge owner 1
                inputs <- ruleInputs owner ordinal
                let captures = case inputs of OpenRuleInputs -> Map.empty; ScopedRuleInputs values -> values
                pure (ruleTermTemplates rule, captures)
            base <- case snapshotTemplateSupport snapshot of
                Just prepared -> freezeSelectedSupportWithCaptures (ruleCharge owner) scoped seeds prepared
                Nothing -> do
                    prepared <- prepareTemplateSupport (ruleCharge owner)
                        (concat [ruleTermTemplates rule | entry <- Map.elems (snapshotRules snapshot),
                            let rule = registeredRule entry, not (ruleIsScoped rule)])
                    freezeSupportWithCaptures (ruleCharge owner) scoped seeds prepared
            wholeInputs <- fmap concat $ for (Map.toAscList (snapshotRules snapshot)) \(ordinal,entry) -> do
                let rule = registeredRule entry
                described <- ruleSupportTemplates owner rule
                if null described then pure [] else do
                    inputs <- ruleInputs owner ordinal
                    let captures = case inputs of OpenRuleInputs -> Map.empty; ScopedRuleInputs values -> values
                    pure [(arity,terms,captures) | (arity,terms) <- described, not (null terms)]
            support <- if null wholeInputs then pure base else case ruleOpaqueSupport owner of
                Nothing -> error "whole support requires its owning interpreter"
                Just interpreter -> extendWholeSupport (ruleCharge owner) interpreter wholeInputs base
            rulePhase owner "support-finished"
            pure (Right (support, answers))
  where
    charge = lift . ruleCharge owner
    event = lift . ruleEvent owner
    atomicRows values = [(row,answer) | answer@RuleAnswer{ruleAnswerLeaf = AtomicLeaf row} <- values]
    atomTerms = toList
    pin term = do
        charge 1
        case term of
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateVariable value -> pure (TemplateVariable (Pinned value))
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse pin arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> pin left <*> pin right
    -- Only definition views belong to the initial closure. Their backwards
    -- head closure is a scheduling priority, not a restriction on support or
    -- evidence. Prepared view postings avoid scanning classification bodies.
    viewAncestors known [] = pure known
    viewAncestors known (head':rest) = do
        charge (2 * indexWork (Set.size known) 3)
        if Set.member head' known then viewAncestors known rest else do
            charge (indexWork (Map.size (snapshotForwardPredecessors snapshot)) 3)
            next <- foldM (\pending predecessor -> do
                charge 1
                pure (predecessor : pending)) rest
                (Map.findWithDefault Set.empty head' (snapshotForwardPredecessors snapshot))
            viewAncestors (Set.insert head' known) next
    -- Goal ancestors precede other heads, with prepared ranks within each
    -- group. Since the first group contains all its predecessors, this is
    -- still a topological order: every bucket is complete when visited.
    -- A miss expands both groups and freezes the same complete seed domain.
    -- Exact-only rows stay available but never activate a view.
    initialViews ancestors pinned current@(known,pending,wholes) = case Set.minView pending of
        Nothing -> pure current
        Just ((_,_,head'),rest) -> do
            charge (indexWork (Set.size pending) 1 + indexWork (Map.size known) 3
                + indexWork (Map.size (snapshotForwardSources snapshot)) 3)
            let rows = Map.elems (Map.findWithDefault Map.empty head' known)
                views = Map.toAscList (Map.findWithDefault Map.empty head' (snapshotForwardSources snapshot))
            next <- foldM (\accumulated (ordinal,view) ->
                    foldM (\next (row,answer) -> case ruleAnswerCapability answer of
                        ExactAnswer -> pure next
                        SourceRow -> do
                            event (Diagnostics.Count Diagnostics.InitialView 1)
                            event (Diagnostics.EnterRegistration ordinal)
                            completed <- applyInitialForwardRule charge view SourceRow row (ruleAnswerWitness answer)
                            updated <- publish ancestors pinned next ordinal completed
                            event Diagnostics.LeaveRegistration
                            pure updated) accumulated (atomicRows rows)) (known,rest,wholes) views
            initialViews ancestors pinned next
    insert ancestors pinned (known,pending,wholes) row answer = do
        let head' = atomSignature row
            bucket = Map.findWithDefault Map.empty head' known
        -- The goal and every initial row are seeds by construction. Exact
        -- ground matching here needs no synthesized term or support search.
        -- Exhaustive evaluation still constructs the entire frozen domain.
        for_ pinned \requested -> do
            charge 1
            when (head' == atomSignature requested) do
                event (Diagnostics.Count Diagnostics.CandidatePair 1)
                matched <- matchCompleteRow charge emptySubstitution requested row
                when (isJust matched) (Except.throwE answer)
        charge (2 * indexWork (Map.size known) 3 + indexWork (Map.size bucket) 1)
        if Map.member (ruleAnswerKey answer) bucket then pure (known,pending,wholes) else do
            event (Diagnostics.Count Diagnostics.InitialRow 1)
            pending' <- case ruleAnswerCapability answer of
                ExactAnswer -> pure pending
                SourceRow -> do
                    charge (indexWork (Map.size (snapshotSourceRanks snapshot)) 3
                        + indexWork (Set.size ancestors) 3 + indexWork (Set.size pending) 1)
                    pure (Set.insert (Set.notMember head' ancestors,
                        Map.findWithDefault 0 head' (snapshotSourceRanks snapshot),head') pending)
            pure (Map.insert head' (Map.insert (ruleAnswerKey answer) answer bucket) known,pending',wholes)
    publish ancestors pinned known ordinal = \case
        Left failure -> lift (ruleRejected owner failure) >> pure known
        Right Nothing -> pure known
        Right (Just completed) -> do
            result <- lift (completedLeaf owner ordinal completed)
            lift (ruleCompleted owner ordinal completed result) >>= \case
                Nothing -> pure known
                Just (key,witness) -> do
                    event (Diagnostics.Count Diagnostics.CompletedRule 1)
                    case result of
                        AtomicLeaf row -> insert ancestors pinned known row (RuleAnswer result key SourceRow witness)
                        WholeLeaf formula -> do
                            let answer = RuleAnswer result key ExactAnswer witness
                                (rows,pending,wholes) = known
                            case goal of
                                WholeLeaf requested | stopOnAnswer && wholeRequestFormula requested == formula -> Except.throwE answer
                                _ -> pure ()
                            charge (indexWork (Map.size wholes) 1)
                            pure (rows,pending,Map.insertWith (\_ prior -> prior) key answer wholes)

evaluateSupportedRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness -> (Set AtomSignature -> CanonicalPattern variable -> m Catalog.CandidateRules)
    -> SymbolicSupport variable
    -> RuleSnapshot -> [RuleAnswer variable key witness]
    -> NotionLeaf (AtomTemplate (SetTermTemplate variable)) (WholeRequest variable)
    -> m (Either PatternRejection
        (RelationalResult Query (RuleAnswer variable key witness) key, [(Natural, AtomTemplate (SetTermTemplate variable))]))
evaluateSupportedRules stopOnAnswer owner candidates support snapshot facts goal =
    initializeSupportedRules stopOnAnswer owner candidates support snapshot facts goal >>= traverse drain
  where
    drain session = case ruleSessionStatus session of
        RelationalRunnable -> advanceRuleSession 64 session >>= drain
        _ -> finishRuleSession session

initializeSupportedRules
    :: (Monad m, Ord variable, Ord bucket, Ord key)
    => Bool -> RuleEvaluator m variable bucket key witness
    -> (Set AtomSignature -> CanonicalPattern variable -> m Catalog.CandidateRules)
    -> SymbolicSupport variable -> RuleSnapshot -> [RuleAnswer variable key witness] -> RuleLeaf variable
    -> m (Either PatternRejection (RuleSession m variable bucket key witness))
initializeSupportedRules stopOnAnswer owner candidates support snapshot facts goal = State.evalStateT run
    Evaluation
        { queries = emptyRequestTable support
        , continuationIds = Map.empty
        , continuations = IntMap.empty
        , advancedSelections = Set.empty
        , fallbackStates = Map.empty
        , fallbackWaiters = Map.empty
        , missingViewRequests = Map.empty
        , wholeTruthHeads = Map.empty
        , possibleHeads = Map.empty
        , possibleRules = Map.empty
        , atomicInputMatches = Map.empty
        , requestInputKeys = Map.empty
        , requestHeadFormulas = Map.empty
        , activeSourceHeads = Set.empty
        , activeSourceArguments = Set.empty
        , instanceTerms = Terms.emptyNodes
        , instanceIds = Map.empty
        , groundInstances = IntMap.empty
        , truthProducersOpened = Map.empty
        , producerDemands = IntMap.empty
        , componentIds = Map.empty
        , componentDemands = IntMap.empty
        , componentWaiters = IntMap.empty
        , eliminationWaiters = IntMap.empty
        , wholeShapeIds = Map.empty
        , wholeShapes = IntMap.empty
        , openWholeIds = Map.empty
        , openWholeDemands = IntMap.empty
        , openWholeWaiters = IntMap.empty
        }
  where
    charge = lift . ruleCharge owner
    event = lift . ruleEvent owner
    -- One attempt per returned candidate, including later matching/eligibility
    -- rejection. Catalogue exclusions and resumed registrations are not selections.
    -- Necessary-source analysis gates discovery, not already determined ground
    -- instances. Ground prerequisites retain their ordinary checking and failure
    -- provenance without opening any finite assignment cursor.
    nextProducer allowGround selected = Catalog.nextCandidateRule charge selected >>= \case
        Nothing -> pure Nothing
        Just candidate@((ordinal,entry),rest) -> do
            event (Diagnostics.Count Diagnostics.AttemptedProducer 1)
            possible <- possibleRule ordinal (registeredRule entry)
            if possible || allowGround then pure (Just (possible,candidate)) else nextProducer allowGround rest
    withRegistration ordinal action = do
        event (Diagnostics.EnterRegistration ordinal)
        lift (rulePhase owner ("registration-start ordinal=" <> Text.pack (show ordinal)))
        result <- action
        lift (rulePhase owner ("registration-finished ordinal=" <> Text.pack (show ordinal)))
        event Diagnostics.LeaveRegistration
        pure result
    bound = symbolicSupportMaximumTermSize support
    supportOwner = fmap (\operations -> OpaqueInterpreter
        (lift . opaqueValue operations)
        (\arity template value -> lift (opaqueMatch operations arity template value))
        (\arity template values -> lift (opaqueInstantiate operations arity template values))) (ruleOpaqueSupport owner)
    internShape shape = do
        known <- State.gets wholeShapeIds
        let digest = Formulas.residualShapeHash shape
            bucket = Map.findWithDefault [] digest known
        charge (indexWork (Map.size known) 1)
        let findShape [] = pure Nothing
            findShape ((candidate,identifier):rest) = do
                charge (Formulas.residualShapeWork shape)
                if shape == candidate then pure (Just identifier) else findShape rest
        findShape bucket >>= \case
            Just identifier -> pure identifier
            Nothing -> do
                identifier <- State.gets (IntMap.size . wholeShapes)
                charge (1 + indexWork (Map.size known) 1)
                State.modify' (\current -> current
                    { wholeShapeIds = Map.insert digest ((shape,identifier):bucket) known
                    , wholeShapes = IntMap.insert identifier shape (wholeShapes current) })
                pure identifier
    formulaSchema formula = lift (ruleFormulaShape owner formula) >>= internShape
    shapeFor identifier = do
        shapes <- State.gets wholeShapes
        charge (indexWork (IntMap.size shapes) 1)
        pure (shapes IntMap.! identifier)
    getOpenWhole identifier = do
        demands <- State.gets openWholeDemands
        charge (indexWork (IntMap.size demands) 1)
        pure (demands IntMap.! identifier)
    wholeAnswerFormula answer = case ruleAnswerLeaf answer of
        WholeLeaf value -> pure value
        AtomicLeaf row -> lift (ruleAtomicFormula owner row) >>=
            maybe (error "an atomic whole answer lost its formula identity") pure
    matchWholeWaiting waiting answer = do
        formula <- wholeAnswerFormula answer
        lift (ruleMatchWhole owner (wholeWaitingPattern waiting) formula) >>= \case
            Nothing -> pure Nothing
            Just values -> do
                compatible <- foldM (\ready (slot,binding) -> if not ready then pure False else do
                    charge (indexWork (Map.size values) 1)
                    case (binding,Map.lookup slot values) of
                        (Just term,Just expected) -> lift (ruleArgumentValue owner term) >>= \case
                            Just actual -> pure (actual == expected)
                            Nothing -> pure True
                        _ -> pure True) True (Map.toAscList (wholeWaitingInputs waiting))
                pure (if compatible then Just values else Nothing)
    subscribeWhole request ordinal selected state waiting = do
        let bindings = wholeWaitingInputs waiting
            position = wholeWaitingPosition waiting
            introduce = position /= 0 || not (ruleIsElimination (activeRule state))
        child <- case traverse id bindings of
            Just concrete -> wholeQuery ordinal (Just position) introduce concrete (wholeWaitingTemplate waiting)
            Nothing -> do
                keyTerms <- traverse (traverse internInstanceTerm) bindings
                known <- State.gets openWholeIds
                let constraints = Map.restrictKeys (ruleArgumentConstraints state) (Map.keysSet bindings)
                    key = (ordinal,position,Map.toAscList keyTerms,Map.toAscList constraints)
                charge (indexWork (Map.size known) (2 + fromIntegral (Map.size bindings + Map.size constraints)))
                identifier <- case Map.lookup key known of
                    Just existing -> pure existing
                    Nothing -> do
                        shape <- internShape (wholeWaitingShape waiting)
                        let fresh = Map.size known
                        charge (indexWork fresh (2 + fromIntegral (Map.size bindings + Map.size constraints)))
                        State.modify' (\current -> current
                            {openWholeIds = Map.insert key fresh known,
                             openWholeDemands = IntMap.insert fresh
                                (OpenDemand (activeRule state) waiting shape constraints Set.empty) (openWholeDemands current)})
                        pure fresh
                pure (OpenWholeQuery identifier)
        waiters <- State.gets openWholeWaiters
        let identifier = IntMap.size waiters
        charge (indexWork identifier 1)
        State.modify' (\current -> current {openWholeWaiters = IntMap.insert identifier
            (request,ordinal,selected,state,waiting) waiters})
        let step = emptyStep {relationalSubscriptions = [(child,Just (WholeContinuation identifier))]}
        if all isJust bindings || not introduce || not (wholeWaitingNeedsGroundInputs waiting)
          then pure step else lift (ruleWholeBindings owner (activeRule state) waiting) >>= \case
            Just (slot,values) -> pure step {relationalDeferred =
                [(Just request,BindWholeWork request ordinal selected state slot values)]}
            Nothing -> assign request ordinal state (Map.keys bindings) (RequestAssignment selected waiting) step
    supported value = do
        table <- State.gets queries
        (admitted,updated) <- requestSupportsTermWith supportOwner charge value table
        State.modify' (\current -> current {queries = updated})
        pure admitted
    selectWhole shape = do
        active <- State.gets activeSourceHeads
        lift (ruleWholeCandidates owner active shape) >>= \case
            Just selected -> pure selected
            Nothing -> (\selected -> WholeCandidates selected (snapshotRules snapshot)) <$>
                Catalog.candidateRulesFromMap charge (snapshotWholeProducers snapshot)
    -- All producer entry points have passed the template-only source check.
    -- Resumed joins inherit that decision; it does not depend on assignments.
    discoverRule request ordinal state = case ruleElimination (activeRule state) of
        Nothing -> advance request ordinal Map.empty state
        Just source -> do
            shape <- internShape (eliminationShape source)
            waiting <- State.gets eliminationWaiters
            let identifier = IntMap.size waiting
            charge (indexWork identifier 1)
            State.modify' (\current -> current {eliminationWaiters = IntMap.insert identifier
                (request,ordinal,source,state) waiting})
            pure emptyStep {relationalSubscriptions =
                [(WholeSchemaQuery shape,Just (EliminationContinuation identifier))]}
    discoveryKey request ordinal selected = (request,ordinal,Map.toAscList selected)
    reject failure = lift (ruleRejected owner failure)
    emptyStep = RelationalStep [] [] []
    query pattern' = queryConstrained pattern' Map.empty
    queryConstrained pattern' constraints = do
        table <- State.gets queries
        internConstrainedRequestWith supportOwner charge pattern' constraints table >>= \case
            Left failure -> pure (Left failure)
            Right (identifier, updated) -> do
                State.modify' (\state -> state {queries = updated})
                let shape = fmap (\case Pinned _ -> Left (); Output slot -> Right slot) <$> pattern'
                lift (rulePhase owner ("request=" <> Text.pack (show identifier)
                    <> " pattern=" <> Text.pack (take 768 (show shape))))
                pure (Right (LeafQuery (AtomicLeaf (atomSignature pattern')) identifier))
    constraintsFor identifier = do
        table <- State.gets queries
        requestConstraints charge identifier table
    classKeys = traverse (fmap fst . lift . ruleArgumentClass owner)
    transportable row = foldM (\found term -> if found then pure True else
        lift (ruleArgumentValue owner term) >>= maybe (pure False)
            (fmap snd . lift . ruleArgumentClass owner)) False (toList row)
    argumentsAgree a b = lift (ruleTermsMayAgree owner
        (TemplateVariable (Just a)) (TemplateVariable (Just b)))
    argumentKeys row = fmap Map.fromDistinctAscList . fmap catMaybes $
        for (zip [0..] (toList row)) \(position,term) -> do
            charge 1
            fmap ((,) position) <$> lift (ruleArgumentValue owner term)
    requestArguments identifier requested = do
        known <- State.gets requestInputKeys
        charge (indexWork (Map.size known) 1)
        case Map.lookup identifier known of
            Just values -> pure values
            Nothing -> do
                exact <- constraintsFor identifier
                grounded <- traverse ground (canonicalPatternAtom requested)
                keys <- fmap Map.fromDistinctAscList . fmap catMaybes $
                    for (zip [0..] (toList grounded)) \(position,term) -> case term of
                        Nothing -> pure Nothing
                        Just value -> fmap ((,) position) <$> lift (ruleArgumentValue owner value)
                charge (fromIntegral (Map.size exact + Map.size keys) + indexWork (Map.size known) 1)
                let values = Map.union exact keys
                State.modify' (\state -> state {requestInputKeys = Map.insert identifier values known})
                pure values
    requestHeadFormula identifier row = do
        known <- State.gets requestHeadFormulas
        charge (indexWork (Map.size known) 1)
        case Map.lookup identifier known of
            Just formula -> pure formula
            Nothing -> do
                formula <- lift (ruleAtomicFormula owner row)
                charge (indexWork (Map.size known) 1)
                State.modify' (\state -> state {requestHeadFormulas = Map.insert identifier formula known})
                pure formula
    constraintsMatch identifier row = do
        constraints <- constraintsFor identifier
        if Map.null constraints then pure True else do
            foldM (\matches (position,value) -> if not matches then pure False else do
                charge (indexWork (Map.size constraints) 1)
                case Map.lookup position constraints of
                    Nothing -> pure True
                    Just expected -> lift (ruleArgumentValue owner value) >>= maybe (pure True) (argumentsAgree expected))
                True (zip [0..] (toList row))
    constrainHead identifier rule state = do
        constraints <- constraintsFor identifier
        values <- ruleHeadConstraints charge rule constraints
        fmap (`constrainRule` state) <$> mergeConstraints Map.empty values
    mergeConstraints initial extra = foldM (\known (slot,value) -> case known of
        Nothing -> pure Nothing
        Just found -> do
            charge (2 * indexWork (Map.size found) 1)
            case Map.lookup slot found of
                Just previous -> argumentsAgree previous value >>= \same -> pure (if same then Just found else Nothing)
                Nothing -> pure (Just (Map.insert slot value found))) (Just initial) extra
    -- An equality class constrains a complete operand. Only a singleton can
    -- fix an otherwise unknown parameter inside another operand.
    singletonConstraints = Map.traverseMaybeWithKey (\_ value -> do
        charge 1
        (_,alternate) <- lift (ruleArgumentClass owner value)
        pure (if alternate then Nothing else Just (TemplateVariable value)))
    bindingsMeet constraints values = foldM (\matches (slot,expected) -> if not matches then pure False else do
        charge (indexWork (Map.size values) 1)
        case Map.lookup slot values >>= id of
            Nothing -> pure True
            Just term -> lift (ruleArgumentValue owner term) >>= maybe (pure True) (argumentsAgree expected))
        True (Map.toAscList constraints)
    compatibleBindings state
        | Map.null (ruleArgumentConstraints state) = pure True
        | otherwise = ruleConstraintValues charge bound state >>= \case
            Left failure -> reject failure >> pure False
            Right values -> bindingsMeet (ruleArgumentConstraints state) values
    matchDemand identifier state = do
        let rule = activeRule state
            (arity,_,_) = ruleDescription rule
        forced <- singletonConstraints (ruleArgumentConstraints state)
        ruleBindings charge bound (map ViewVariableIx (take (fromIntegral arity) [0..])) state >>= \case
            Left failure -> reject failure >> pure Nothing
            Right values -> matchPartialDemand identifier rule
                (partialBindings (Map.unionWith (<|>) values (Just <$> forced)))
    partialBindings = fmap (maybe (TemplateVariable Nothing) (fmap Just))
    matchPartialDemand identifier rule values = do
        demand <- getOpenWhole identifier
        requested <- singletonConstraints (openDemandConstraints demand)
        let waiting = openDemandWaiting demand
        lift (ruleMatchPartialWhole owner (openDemandRule demand)
            waiting {wholeWaitingInputs = Map.unionWith (<|>) (wholeWaitingInputs waiting) (Just <$> requested)} rule values)
    specializeDemand identifier state = matchDemand identifier state >>= \case
        Nothing -> pure Nothing
        Just constraints -> mergeConstraints (ruleArgumentConstraints state) (Map.toAscList constraints) >>= \case
            Nothing -> pure Nothing
            Just merged -> do
                admitted <- Map.traverseMaybeWithKey (\_ value -> do
                    allowed <- supported (TemplateVariable value)
                    pure (if allowed then Just value else Nothing)) constraints
                bindWholeRuleInputs charge admitted (constrainRule merged state)
    compatibleState request state = do
        bindings <- compatibleBindings state
        if not bindings || isJust (ruleStateComponent state) then pure bindings else case request of
          OpenWholeQuery identifier -> isJust <$> matchDemand identifier state
          _ -> do
            -- These constraints describe complete arguments modulo the fixed
            -- supplied equality relation. A pinned request's spelling alone
            -- does not authorize opening its opaque arguments for matching.
            constraints <- case request of
                LeafQuery (AtomicLeaf _) identifier -> constraintsFor identifier
                ProducerQuery identifier -> getProducer identifier >>= \(_,_,underlying,_) -> constraintsFor underlying
                _ -> pure Map.empty
            if Map.null constraints then pure True else do
              forced <- singletonConstraints (ruleArgumentConstraints state)
              ruleHeadValues charge bound forced state >>= \case
                Left failure -> reject failure >> pure False
                Right Nothing -> pure True
                Right (Just head') -> foldM (\matches (position,partial) -> if not matches then pure False else do
                    charge (indexWork (Map.size constraints) 1)
                    case Map.lookup position constraints of
                        Nothing -> pure True
                        Just expected -> lift (ruleTermsMayAgree owner partial (TemplateVariable (Just expected))))
                    True (zip [0..] (toList head'))
    prepareAssignmentFilter request state completion slot = do
        let rule = activeRule state
            (arity,_,conclusion) = ruleDescription rule
        ruleBindings charge bound (map ViewVariableIx (take (fromIntegral arity) [0..])) state >>= \case
            Left failure -> reject failure >> pure Nothing
            Right values -> do
                forced <- singletonConstraints (ruleArgumentConstraints state)
                let bindings = partialBindings (Map.unionWith (<|>) values (Just <$> forced))
                    atomic identifier = do
                        constraints <- constraintsFor identifier
                        pure (\partial -> case conclusion of
                            WholeLeaf{} -> pure True
                            AtomicLeaf atom -> do
                                head' <- fmap (fmap join) <$> partialRuleAtom (ruleCharge owner)
                                    (Map.insert slot partial bindings) atom
                                foldM (\matches (position,term) -> if not matches then pure False else
                                    maybe (pure True) (\expected -> ruleTermsMayAgree owner term
                                        (TemplateVariable (Just expected))) (Map.lookup position constraints))
                                    True (zip [0..] (toList head')))
                headMatch <- if isJust (ruleStateComponent state) then pure (const (pure True)) else case request of
                    OpenWholeQuery identifier -> do
                        demand <- getOpenWhole identifier
                        requested <- singletonConstraints (openDemandConstraints demand)
                        let waiting = openDemandWaiting demand
                        lift (rulePreparePartialWhole owner (openDemandRule demand)
                            waiting {wholeWaitingInputs = Map.unionWith (<|>) (wholeWaitingInputs waiting) (Just <$> requested)}
                            rule bindings slot)
                    LeafQuery (WholeLeaf _) identifier -> case ruleExactConclusion rule of
                        Nothing -> pure (const (pure True))
                        Just description -> canonical identifier >>= \case
                            WholeLeaf requested -> lift (rulePrepareWholeMatch owner rule description bindings slot
                                (wholeRequestFormula requested))
                            AtomicLeaf{} -> error "a whole demand lost its formula"
                    LeafQuery (AtomicLeaf _) identifier -> atomic identifier
                    ProducerQuery identifier -> getProducer identifier >>= \(_,_,underlying,_) -> atomic underlying
                    _ -> pure (const (pure True))
                premiseMatch <- case completion of
                    MatchAssignment _ position answer
                      | not (ruleHasEqualityTransport owner && isJust (ruleAtomicPremise position rule)) ->
                        rulePremiseDescription charge position rule >>= \case
                            Nothing -> pure (const (pure True))
                            Just description -> do
                                formula <- wholeAnswerFormula answer
                                lift (rulePrepareWholeMatch owner rule description (partialBindings values) slot formula)
                    _ -> pure (const (pure True))
                pure (Just (\partial -> headMatch partial >>= \matches ->
                    if matches then premiseMatch partial else pure False))
    canonical identifier = do
        table <- State.gets queries
        -- IDs only enter this driver through query in this same table.
        pure (fromMaybe (error "formation request identity escaped its table") (lookupRequest identifier table))
    atomicRequest identifier = canonical identifier >>= \case
        AtomicLeaf pattern' -> pure pattern'
        WholeLeaf{} -> error "a whole request entered atomic parameter discovery"
    wholeTruthAvailable signature = do
        known <- State.gets wholeTruthHeads
        charge (indexWork (Map.size known) 3)
        case Map.lookup signature known of
            Just available -> pure available
            Nothing -> do
                available <- lift (ruleWholeTruthAvailable owner signature)
                charge (indexWork (Map.size known) 3)
                State.modify' (\state -> state {wholeTruthHeads = Map.insert signature available known})
                pure available
    possibleSource head' = do
        known <- State.gets possibleHeads
        active <- State.gets activeSourceHeads
        (available,updated) <- lift (ruleSourcePossible owner active head' known)
        State.modify' (\state -> state {possibleHeads = updated})
        pure available
    possibleRule ordinal rule = do
        known <- State.gets possibleRules
        charge (indexWork (Map.size known) 1)
        case Map.lookup ordinal known of
            Just possible -> pure possible
            Nothing -> do
                possible <- foldM (\available head' ->
                    if available then possibleSource head' else pure False) True (rulePremiseSignatures rule)
                charge (indexWork (Map.size known) 1)
                State.modify' (\state -> state {possibleRules = Map.insert ordinal possible known})
                pure possible
    requestKey identifier = canonical identifier >>= \case
        AtomicLeaf pattern' -> pure (LeafQuery (AtomicLeaf (atomSignature (canonicalPatternAtom pattern'))) identifier)
        WholeLeaf whole -> pure (LeafQuery (WholeLeaf (wholeRequestFormula whole)) identifier)
    wholeQuery ordinal position introduce substitution template = do
        requested <- lift (ruleWholeRequest owner ordinal position substitution template)
        wholeRequest (if introduce then requested else evidenceOnlyRequest requested)
    wholeRequest requested = do
        table <- State.gets queries
        (identifier, updated) <- internWholeRequest charge requested table
        State.modify' (\state -> state {queries = updated})
        pure (LeafQuery (WholeLeaf (wholeRequestFormula requested)) identifier)
    pin = traverseAtomTemplateArguments pinTerm
    pinTerm term = do
        charge 1
        case term of
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateVariable value -> pure (TemplateVariable (Pinned value))
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse pinTerm arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> pinTerm left <*> pinTerm right
    ground term = do
        charge 1
        case term of
            TemplateClosed value -> pure (Just (TemplateClosed value))
            TemplateVariable (Pinned value) -> pure (Just (TemplateVariable value))
            TemplateVariable Output{} -> pure Nothing
            TemplateProvider provider arguments -> fmap (TemplateProvider provider) . sequence <$> traverse ground arguments
            TemplateOrderedPair left right -> liftA2 TemplateOrderedPair <$> ground left <*> ground right
    requestLeaf = \case
        AtomicLeaf atom -> pin atom >>= query
        WholeLeaf requested -> Right <$> wholeRequest requested
    run = do
        rootQuery <- requestLeaf goal
        case rootQuery of
            Left failure -> pure (Left failure)
            Right root -> do
                -- runRules built this frozen support from every initial row.
                -- They are ground seeds, not requests: interning them again
                -- repeats admission and allocates unused request identities.
                let forward = snapshotForwardSources snapshot
                initialKeys <- foldM (\known answer -> do
                    charge (indexWork (Set.size known) 1)
                    pure (Set.insert (ruleAnswerKey answer) known)) Set.empty facts
                let runtime = evaluator forward initialKeys
                table <- initializeRelational stopOnAnswer runtime (LogicalAnswer <$> facts) root
                joins <- State.get
                pure (Right (RuleSession runtime requestLeaf missingPremises table joins))
    missingPremises result = do
                missing <- if not (Set.null (relationalRootAnswers result)) then pure [] else do
                    unresolved <- foldM (\known request -> case request of
                        ComponentQuery{} -> pure known
                        ProducerQuery{} -> pure known
                        WholeSchemaQuery{} -> pure known
                        OpenWholeQuery{} -> pure known
                        LeafQuery _ identifier -> canonical identifier >>= \case
                          WholeLeaf{} -> pure known
                          AtomicLeaf pattern' -> do
                              grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom pattern')
                              case traverseAtomTemplateArguments id grounded of
                                  Nothing -> pure known
                                  Just atom -> do
                                      charge (indexWork (Map.size known) 1)
                                      pure (Map.insert identifier atom known)) Map.empty
                        (Set.toAscList (relationalUnansweredRequests result))
                    waiting <- State.gets continuations
                    -- Retain the actual requesting rule. An unrelated missing
                    -- definition view is not a failed provider prerequisite.
                    partialMissing <- fmap catMaybes $ traverse (\(Waiting _ child ordinal _ _ _) -> do
                        charge (indexWork (Map.size unresolved) 1)
                        pure ((\atom -> (ordinal, atom)) <$> Map.lookup child unresolved))
                        (IntMap.elems waiting)
                    grounded <- State.gets groundInstances
                    groundMissing <- fmap concat $ for (IntMap.elems grounded) \(GroundEntry _ ordinal instance') ->
                        fmap catMaybes $ for (Map.keys (Ground.instanceRequests instance')) \child -> do
                            charge (indexWork (Map.size unresolved) 1)
                            pure ((\atom -> (ordinal, atom)) <$> Map.lookup child unresolved)
                    pure (partialMissing <> groundMissing)
                pure missing
    evaluator forward initialKeys = RelationalEvaluator
        { relationalCharge = charge 1
        , relationalRequestBucket = \request -> do
            event (Diagnostics.Count Diagnostics.UniqueRequest 1)
            case request of
                ComponentQuery identifier -> pure (ComponentBucket identifier)
                ProducerQuery identifier -> pure (ProducerBucket identifier)
                WholeSchemaQuery identifier -> pure (WholeSchemaBucket identifier)
                OpenWholeQuery identifier -> do
                    demand <- getOpenWhole identifier
                    pure (WholeSchemaBucket (openDemandShape demand))
                LeafQuery _ identifier -> canonical identifier >>= \case
                    WholeLeaf requested -> pure (LogicalBucket (WholeLeaf (wholeRequestFormula requested)))
                    AtomicLeaf requested -> do
                        grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom requested)
                        case traverseAtomTemplateArguments id grounded of
                            Just row -> LogicalBucket . AtomicLeaf . Right <$> lift (ruleGroundBucket owner row)
                            Nothing -> do
                                arguments <- requestArguments identifier requested >>= classKeys
                                let signature = atomSignature (canonicalPatternAtom requested)
                                pure $ case Map.lookupMin arguments of
                                    Just (position,value) -> ArgumentBucket signature position value
                                    Nothing -> LogicalBucket (AtomicLeaf (Left signature))
        , relationalAnswerBuckets = \case
            ComponentAnswer identifier _ _ _ -> pure [ComponentBucket identifier]
            LogicalAnswer answer -> case ruleAnswerLeaf answer of
                WholeLeaf formula -> do
                    shape <- formulaSchema formula
                    pure [LogicalBucket (WholeLeaf formula),WholeSchemaBucket shape]
                AtomicLeaf row -> do
                    bucket <- lift (ruleGroundBucket owner row)
                    formula <- lift (ruleAtomicFormula owner row)
                    arguments <- argumentKeys row >>= classKeys
                    when (ruleAnswerCapability answer == SourceRow) $ do
                        known <- State.gets activeSourceArguments
                        updated <- foldM (\seen (position,value) -> do
                            charge (indexWork (Set.size seen) 5)
                            pure (Set.insert (atomSignature row,position,value) seen)) known (Map.toAscList arguments)
                        State.modify' (\state -> state {activeSourceArguments = updated})
                    -- Partial exact consumers also need late atomic answers,
                    -- independently of whether any elimination rule is selected.
                    shape <- case formula of
                        Just value -> (\identifier -> [WholeSchemaBucket identifier]) <$> formulaSchema value
                        Nothing -> pure []
                    pure (shape <> [LogicalBucket (AtomicLeaf (Left (atomSignature row))), LogicalBucket (AtomicLeaf (Right bucket))]
                        <> [LogicalBucket (WholeLeaf value) | value <- maybe [] pure formula] <>
                        [ArgumentBucket (atomSignature row) position value | (position,value) <- Map.toAscList arguments])
        , relationalAnswerKey = \case
            LogicalAnswer answer -> LogicalKey (ruleAnswerKey answer)
            ComponentAnswer identifier values _ _ -> ComponentKey identifier values
        , relationalMatches = \request result -> do
            event (Diagnostics.Count Diagnostics.CandidatePair 1)
            case request of
                ComponentQuery{} -> pure DirectMatch
                ProducerQuery{} -> pure NoMatch
                WholeSchemaQuery{} -> pure DirectMatch
                OpenWholeQuery identifier -> do
                    demand <- getOpenWhole identifier
                    let waiting = openDemandWaiting demand
                        answer = logicalAnswer result
                        origin = atomSignature <$> ruleAtomicPremise (wholeWaitingPosition waiting) (openDemandRule demand)
                        sameOrigin = case ruleAnswerLeaf answer of
                            AtomicLeaf row -> Just (atomSignature row) == origin
                            WholeLeaf{} -> False
                    -- The row join and its missing-view fallback own this
                    -- spelling. Exact access adds whole truth and peer heads.
                    if sameOrigin then pure NoMatch else do
                        formula <- wholeAnswerFormula answer
                        let seen = openDemandFormulas demand
                        charge (indexWork (Set.size seen) 1)
                        if Set.member formula seen then pure NoMatch else do
                            matches <- matchWholeWaiting waiting answer
                            if isNothing matches then pure NoMatch else do
                                charge (indexWork (Set.size seen) 1)
                                State.modify' (\current -> current {openWholeDemands = IntMap.adjust
                                    (\found -> found {openDemandFormulas = Set.insert formula seen})
                                    identifier (openWholeDemands current)})
                                pure DirectMatch
                LeafQuery _ identifier -> do
                    let answer = logicalAnswer result
                    canonical identifier >>= \case
                        WholeLeaf{} -> pure DirectMatch
                        AtomicLeaf requested -> case ruleAnswerLeaf answer of
                            WholeLeaf{} -> pure NoMatch
                            AtomicLeaf row -> constraintsMatch identifier row >>= \compatible ->
                              if not compatible then pure NoMatch else do
                                matched <- matchCompleteRow charge emptySubstitution (canonicalPatternAtom requested) row
                                grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom requested)
                                case (traverseAtomTemplateArguments id grounded,ruleAnswerCapability answer,matched) of
                                    (Nothing,ExactAnswer,_) -> missingView identifier requested answer row
                                    (_,_,Just{}) -> pure DirectMatch
                                    (Nothing,_,_) -> missingView identifier requested answer row
                                    (Just target,SourceRow,_) -> pure (DeferredMatch (ConversionWork target answer))
                                    _ -> pure NoMatch

        , relationalObserve = \case
            LogicalAnswer answer | AtomicLeaf row <- ruleAnswerLeaf answer, SourceRow <- ruleAnswerCapability answer -> do
                active <- State.gets activeSourceHeads
                charge (indexWork (Set.size active) 3)
                State.modify' (\current -> current
                    {activeSourceHeads = Set.insert (atomSignature row) active})
                charge (indexWork (Set.size initialKeys) 1)
                if Set.member (ruleAnswerKey answer) initialKeys
                    then pure emptyStep
                    else do
                        charge (indexWork (Map.size forward) 3)
                        continue (ForwardWork row answer (Map.findWithDefault Map.empty (atomSignature row) forward))
            _ -> pure emptyStep
        , relationalExpand = \request -> case request of
            -- Ordinary producers already have their static projection clauses.
            -- This subscription adds supplied/introduced Gs without recursively
            -- rediscovering those same producers through a generic G demand.
            WholeSchemaQuery identifier -> do
                shape <- shapeFor identifier
                sources <- lift (ruleWholeSources owner shape)
                continue (WholeSourceWork request sources)
            OpenWholeQuery identifier -> do
                waiting <- openDemandWaiting <$> getOpenWhole identifier
                sources <- lift (ruleWholeSources owner (wholeWaitingShape waiting))
                producers <- selectWhole (wholeWaitingShape waiting)
                pure emptyStep {relationalDeferred =
                    [(Just request,WholeSourceWork request sources),
                     (Just request,OpenWholeWork identifier (wholeCandidateRules producers)),
                     (Just request,OpenAtomicWork identifier (atomicCandidateRules producers))]}
            ComponentQuery identifier -> do
                demand <- getComponent identifier
                state <- startRuleComponent charge (demandRule demand) (demandComponent demand) (demandInputs demand)
                let sourced = maybe state (`constrainElimination` state) (demandWholeSource demand)
                advance request (demandOrdinal demand) Map.empty (constrainRule (demandConstraints demand) sourced)
            ProducerQuery identifier -> do
                (ordinal,rule,underlying,values) <- getProducer identifier
                inputs <- lift (ruleInputs owner ordinal)
                requested <- atomicRequest underlying
                constraints <- requestArguments underlying requested
                possible <- headMayMatch underlying inputs rule requested constraints
                if not possible then pure emptyStep else startRuleWithInputs charge bound inputs rule requested >>= \case
                    Left failure -> reject failure >> pure emptyStep
                    Right Nothing -> pure emptyStep
                    Right (Just state) -> constrainHead underlying rule state >>= \case
                        Nothing -> pure emptyStep
                        Just constrained -> mergeConstraints (ruleArgumentConstraints constrained) (Map.toAscList values) >>= \case
                            Nothing -> pure emptyStep
                            Just exact -> discoverRule request ordinal (constrainRule exact constrained)
            LeafQuery _ identifier -> do
                step <- canonical identifier >>= \case
                    WholeLeaf requested -> do
                        evidence <- lift (ruleWholeEvidence owner requested)
                        shape <- lift (ruleFormulaShape owner (wholeRequestFormula requested))
                        producers <- selectWhole shape
                        step <- continue (WholeProducerWork identifier (wholeCandidateRules producers))
                        pure step
                            { relationalEmissions = [LogicalAnswer (RuleAnswer (WholeLeaf (wholeRequestFormula requested)) key ExactAnswer witness)
                                | (key,witness) <- maybe [] pure evidence] <> relationalEmissions step
                            , relationalDeferred = relationalDeferred step <>
                                [(Just request,AtomicTruthWork identifier (atomicCandidateRules producers))] }
                    AtomicLeaf requested -> do
                        active <- State.gets activeSourceHeads
                        selected <- lift (candidates active requested)
                        event (Diagnostics.Count Diagnostics.SelectedProducer (Catalog.candidateRuleCount selected))
                        step <- continue (ProducerWork identifier selected)
                        -- Initial exposure may already have published whole
                        -- answers; these remain available to a ground demand
                        -- independently of unresolved-discovery summaries.
                        wholeTruth <- wholeTruthAvailable (atomSignature (canonicalPatternAtom requested))
                        let exactTruth = wholeTruth || not (Map.null (snapshotWholeProducers snapshot))
                        if not exactTruth then pure step else do
                            grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom requested)
                            case traverseAtomTemplateArguments id grounded of
                                Nothing -> pure step
                                Just row -> do
                                    exact <- exactSubscription identifier row
                                    pure step {relationalSubscriptions = relationalSubscriptions step <> exact}
                pure step
        , relationalContinue = continue
        , relationalDiscovery = \case
            ProducerWork{} -> True
            WholeSourceWork{} -> True
            WholeProducerWork{} -> True
            OpenWholeWork{} -> True
            OpenAtomicWork{} -> True
            AtomicTruthWork{} -> True
            -- Matching a retained proof is an evidence-producing join. Give
            -- it ordinary discovery service; free-input enumeration remains
            -- an alternative behind available prerequisites.
            EnumerateWork _ _ _ _ MatchAssignment{} _ _ _ _ -> True
            _ -> False
        , relationalNeedsMoreAnswers = \case
            LeafQuery _ identifier -> canonical identifier >>= \case
                WholeLeaf{} -> pure False
                AtomicLeaf requested -> do
                    operands <- traverse ground (canonicalPatternAtom requested)
                    pure (any isNothing operands)
            _ -> pure True
        , relationalResume = \continuation result -> do
            event (Diagnostics.Count Diagnostics.Delivery 1)
            case continuation of
                Nothing -> pure emptyStep
                Just (WholeContinuation identifier) -> do
                    waiters <- State.gets openWholeWaiters
                    charge (indexWork (IntMap.size waiters) 1)
                    let (request,ordinal,selected,state,waiting) = waiters IntMap.! identifier
                        answer = logicalAnswer result
                    matchWholeWaiting waiting answer >>= \case
                        Nothing -> pure emptyStep
                        Just values -> do
                            mergeConstraints (ruleArgumentConstraints state) (Map.toAscList values) >>= \case
                                Nothing -> pure emptyStep
                                Just constraints -> assign request ordinal (constrainRule constraints state)
                                    (Map.keys (wholeWaitingInputs waiting))
                                    (MatchAssignment selected (wholeWaitingPosition waiting) answer) emptyStep
                Just (EliminationContinuation identifier) -> do
                    waiting <- State.gets eliminationWaiters
                    charge (indexWork (IntMap.size waiting) 1)
                    let (request,ordinal,source,state) = waiting IntMap.! identifier
                        answer = logicalAnswer result
                    formula <- case ruleAnswerLeaf answer of
                        WholeLeaf value -> pure value
                        AtomicLeaf row -> lift (ruleAtomicFormula owner row) >>=
                            maybe (error "an atomic schema answer lost its formula identity") pure
                    lift (ruleMatchWhole owner (eliminationPattern source) formula) >>= \case
                        Nothing -> pure emptyStep
                        Just values -> do
                            admitted <- Map.traverseMaybeWithKey (\_ value -> do
                                allowed <- supported (TemplateVariable value)
                                pure (if allowed then Just value else Nothing)) values
                            bindEliminationInputs charge bound admitted state >>= \case
                                Left failure -> reject failure >> pure emptyStep
                                Right Nothing -> pure emptyStep
                                Right (Just specialized) -> do
                                    constraints <- mergeConstraints (ruleArgumentConstraints specialized) (Map.toAscList values)
                                    case constraints of
                                        Nothing -> pure emptyStep
                                        Just exact -> advance request ordinal
                                            (Map.singleton 0 (LogicalKey (ruleAnswerKey answer),[]))
                                            (constrainElimination formula (constrainRule exact specialized))
                Just (ComponentContinuation identifier) -> case result of
                    LogicalAnswer{} -> error "mathematical evidence entered a component subscription"
                    ComponentAnswer component projection values witnesses -> do
                        waiting <- State.gets componentWaiters
                        charge (indexWork (IntMap.size waiting) 1)
                        let ComponentWaiter request ordinal selected state = waiting IntMap.! identifier
                        resumeRuleComponent charge state values witnesses >>= \case
                            Nothing -> pure emptyStep
                            Just updated -> advance request ordinal
                                (Map.union selected ((ComponentKey component projection,[]) <$ witnesses)) updated
                Just (ExactContinuation identifier) -> do
                    requested <- atomicRequest identifier
                    grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom requested)
                    case traverseAtomTemplateArguments id grounded of
                        Nothing -> error "an exact truth subscription lost its ground request"
                        Just row -> continue (ConversionWork row (logicalAnswer result))
                Just (GroundContinuation identifier request) -> do
                    GroundEntry parent ordinal instance' <- getInstance identifier
                    event (Diagnostics.Count Diagnostics.GroundDelivery 1)
                    (updated, ready) <- Ground.deliverInstance charge request (ruleAnswerWitness (logicalAnswer result)) instance'
                    putInstance identifier (GroundEntry parent ordinal updated)
                    deferGround identifier emptyStep ready
                Just (PartialContinuation identifier) -> do
                    waiting <- State.gets ((IntMap.! identifier) . continuations)
                    let Waiting request child ordinal selected position premise = waiting
                        answer = logicalAnswer result
                    case ruleAnswerLeaf answer of
                        WholeLeaf{} -> error "a whole answer entered an atomic join"
                        AtomicLeaf row -> withRegistration ordinal do
                            step <- resumeRule charge (ruleAnswerCapability answer) premise row (ruleAnswerWitness answer) >>= \case
                                Left failure -> reject failure >> pure emptyStep
                                Right Nothing -> pure emptyStep
                                Right (Just state) -> advance request ordinal (Map.insert position (LogicalKey (ruleAnswerKey answer),[]) selected) state
                            erased <- ruleWaitingNeedsDiscovery charge premise
                            transported <- if erased || ruleWaitingIsGround premise || not (ruleHasEqualityTransport owner)
                                then pure False else transportable row
                            pure step {relationalDeferred = relationalDeferred step <>
                                [(Just request,MissingViewWork child answer) | erased || transported]}
        }
    missingView identifier requested answer row = do
        let compatible candidate = foldM (\same (pattern',actual) -> if not same then pure False else
                lift (ruleTermsMayAgree owner
                    (fmap (\case Pinned value -> Just value; Output{} -> Nothing) pattern')
                    (Just <$> actual))) True (zip (toList (canonicalPatternAtom requested)) (toList candidate))
        possible <- compatible row
        pure (if possible then DeferredMatch (MissingViewWork identifier answer) else NoMatch)
    getProducer identifier = do
        known <- State.gets producerDemands
        charge (indexWork (IntMap.size known) 1)
        pure (known IntMap.! identifier)
    discoverHead ordinal rule constraints values = case ruleDescription rule of
        (_,_,WholeLeaf{}) -> pure []
        (_,_,AtomicLeaf atom) -> do
            opened <- State.gets truthProducersOpened
            let key = (ordinal,constraints,values)
            charge (2 * indexWork (Map.size opened) (1 + fromIntegral (Map.size constraints + Map.size values)))
            if Map.member key opened then pure [] else do
                -- Share the generic pattern, but advance only this producer.
                -- Opening an ordinary head demand here would rediscover every
                -- same-head clause for each alternative argument description.
                pattern' <- State.evalStateT (traverseAtomTemplateArguments
                    (\_ -> do
                        lift (charge 1)
                        position <- State.get
                        State.put (position+1)
                        pure (TemplateVariable (Output position))) atom) 0
                queryConstrained pattern' constraints >>= \case
                    Left failure -> reject (JoinPatternRejected failure) >> pure []
                    Right demanded -> do
                        let identifier = Map.size opened
                        charge (indexWork identifier 1 + fromIntegral (Map.size values))
                        State.modify' (\current -> current
                            { truthProducersOpened = Map.insert key identifier opened
                            , producerDemands = IntMap.insert identifier (ordinal,rule,leafIdentifier demanded,values) (producerDemands current) })
                        pure [(ProducerQuery identifier,Nothing)]
    discoverOpaqueHead identifier ordinal inputs rule requested = do
        grounded <- traverseAtomTemplateArguments ground (canonicalPatternAtom requested)
        constraints <- requestArguments identifier requested
        possible <- headMayMatch identifier inputs rule requested constraints
        if not possible then pure emptyStep else do
            case traverseAtomTemplateArguments id grounded of
                Nothing -> do
                    children <- discoverHead ordinal rule constraints Map.empty
                    pure emptyStep {relationalSubscriptions = children}
                Just row -> do
                    values <- case ruleConclusionPattern rule of
                        Nothing -> pure (Just Map.empty)
                        Just pattern' -> lift (ruleAtomicFormula owner row) >>= \case
                            Nothing -> pure (Just Map.empty)
                            Just formula -> lift (ruleMatchWhole owner pattern' formula)
                    children <- case values of
                        Just found -> discoverHead ordinal rule constraints found
                        Nothing | ruleHasEqualityTransport owner -> discoverHead ordinal rule constraints Map.empty
                        Nothing -> pure []
                    exact <- exactSubscription identifier row
                    pure (RelationalStep [] (exact <> children) [])
    -- Check each complete operand against the fixed equality relation.
    -- No product of endpoint tuples is constructed.
    headMayMatch identifier inputs rule requested constraints = case ruleDescription rule of
      (_,_,WholeLeaf{}) -> pure False
      (_,_,AtomicLeaf head') -> do
        values <- ruleHeadConstraints charge rule constraints
        mergeConstraints Map.empty values >>= \case
          Nothing -> pure False
          Just required -> do
            let captured = case inputs of
                    OpenRuleInputs -> Map.empty
                    ScopedRuleInputs bindings -> bindings
            fixed <- bindingsMeet required (Just <$> captured)
            if not fixed then pure False else do
              forced <- singletonConstraints required
              charge (fromIntegral (Map.size captured + Map.size forced))
              partial <- partialRuleAtom charge (Map.union captured forced) head'
              grounded <- traverse ground (canonicalPatternAtom requested)
              let operands = [case Map.lookup position constraints of
                        Just value -> Just (TemplateVariable value)
                        Nothing -> actual | (position,actual) <- zip [0..] (toList grounded)]
              case sequence operands of
                Nothing -> foldM (\same (position,template,target) ->
                    if not same then pure False else do
                        let actual = case Map.lookup position constraints of
                                Just value -> TemplateVariable (Just value)
                                Nothing -> fmap (\case Pinned value -> Just value; Output{} -> Nothing) target
                        lift (ruleTermsMayAgree owner template actual)) True
                    (zip3 [0..] (toList partial) (toList (canonicalPatternAtom requested)))
                Just concrete -> do
                    -- Complete argument constraints also determine an exact target
                    -- when its discovery pattern still contains output holes.
                    let actual = State.evalState (traverse (const (State.state (\case
                            x:xs -> (x,xs)
                            [] -> error "an atomic request lost an operand"))) head') concrete
                    matches <- if ruleHasEqualityTransport owner then pure True else case ruleConclusionPattern rule of
                        Nothing -> pure True
                        Just pattern' -> requestHeadFormula identifier actual >>= \case
                            Nothing -> pure True
                            Just formula -> isJust <$> lift (ruleMatchWhole owner pattern' formula)
                    if not matches then pure False else foldM (\same (template,target) -> if not same then pure False else
                        lift (ruleTermsMayAgree owner template (Just <$> target))) True (zip (toList partial) concrete)
    matchAtomicInputs atom formula = do
        let key = (atomSignature atom,formula)
        known <- State.gets atomicInputMatches
        charge (indexWork (Map.size known) 4)
        case Map.lookup key known of
            Just result -> pure result
            Nothing -> do
                result <- lift (ruleAtomicInputs owner (() <$ atom) formula)
                charge (indexWork (Map.size known) 4 + maybe 1 (\values -> 1 + 2 * fromIntegral (Map.size values)) result)
                State.modify' (\state -> state {atomicInputMatches = Map.insert key result known})
                pure result
    exactSubscription identifier row = lift (ruleAtomicFormula owner row) >>= \case
        Nothing -> pure []
        Just formula -> do
            exact <- wholeRequest (atomicTruthRequest (atomSignature row) formula)
            pure [(exact,Just (ExactContinuation identifier))]
    continue = \case
        BindWholeWork request ordinal selected state slot@(ViewVariableIx index) values -> case values of
            [] -> pure emptyStep
            value:rest -> do
                charge 1
                allowed <- supported value
                step <- if not allowed then pure emptyStep else bindRuleVariable charge index value state >>= \case
                    Nothing -> pure emptyStep
                    Just boundState -> advanceOnce request ordinal selected boundState
                pure step {relationalDeferred = relationalDeferred step <>
                    [(Just request,BindWholeWork request ordinal selected state slot rest) | not (null rest)]}
        MissingViewWork identifier answer -> do
            seen <- State.gets missingViewRequests
            let candidates' = Map.findWithDefault Map.empty identifier seen
                key = ruleAnswerKey answer
            charge (indexWork (Map.size seen) 1 + indexWork (Map.size candidates') 1)
            if Map.member key candidates' then pure emptyStep else do
                State.modify' (\current -> current {missingViewRequests = Map.insert identifier
                    (Map.insert key answer candidates') seen})
                waiting <- State.gets fallbackWaiters
                charge (indexWork (Map.size waiting) 1)
                pure emptyStep {relationalDeferred =
                    [(Nothing,FallbackWork (Map.findWithDefault Map.empty identifier waiting) answer)]}
        FallbackWork pending answer -> do
            charge (indexWork (Map.size pending) 1)
            case Map.minViewWithKey pending of
                Nothing -> pure emptyStep
                Just ((key@(request,ordinal,selection),position),rest) -> do
                    known <- State.gets fallbackStates
                    charge (indexWork (Map.size known) 1)
                    step <- case Map.lookup key known of
                        Nothing -> pure emptyStep
                        Just state -> do
                            values <- case ruleAnswerLeaf answer of
                                AtomicLeaf row -> argumentKeys row
                                WholeLeaf{} -> error "a whole proof entered atomic view discovery"
                            constraints <- rulePremiseConstraints charge position values state
                            mergeConstraints (ruleArgumentConstraints state) constraints >>= \case
                                Nothing -> pure emptyStep
                                Just exact -> do
                                    slots <- rulePremiseSlots charge position (activeRule state)
                                    assign request ordinal (constrainRule exact state) slots
                                        (MatchAssignment (Map.fromAscList selection) position answer) emptyStep
                    pure step {relationalDeferred = relationalDeferred step <>
                        [(Nothing,FallbackWork rest answer) | not (Map.null rest)]}
        AtomicTruthWork request producers -> do
            charge (indexWork (Map.size producers) 1)
            case Map.minViewWithKey producers of
                Nothing -> pure emptyStep
                Just ((ordinal,entry),rest) -> do
                    event (Diagnostics.Count Diagnostics.AttemptedProducer 1)
                    let rule = registeredRule entry
                    requested <- canonical request >>= \case
                        WholeLeaf whole -> pure whole
                        AtomicLeaf{} -> error "atomic truth discovery lost its whole request"
                    children <- case ruleDescription rule of
                        (_,_,AtomicLeaf atom) | Just (atomSignature atom) /= wholeRequestAtomicOrigin requested -> do
                            possible <- possibleRule ordinal rule
                            if not possible then pure [] else do
                              matches <- case ruleConclusionPattern rule of
                                  Nothing -> pure (Just Map.empty)
                                  Just pattern' -> lift (ruleMatchWhole owner pattern' (wholeRequestFormula requested))
                              case matches of
                                  Nothing -> pure []
                                  Just values -> do
                                      matchAtomicInputs atom (wholeRequestFormula requested) >>= \case
                                          Nothing -> pure []
                                          Just operands -> do
                                              let constraints = Map.union operands $ Map.fromList
                                                      [(position,value) | (position,TemplateVariable slot) <- zip [0..] (toList atom)
                                                          , value <- maybe [] pure (Map.lookup slot values)]
                                              charge (fromIntegral (length (toList atom)))
                                              discoverHead ordinal rule constraints values
                        _ -> pure []
                    parent <- requestKey request
                    pure (RelationalStep [] children
                        [(Just parent,AtomicTruthWork request rest) | not (Map.null rest)])
        ConversionWork target answer -> lift (ruleConverted owner target answer) >>= \case
            Nothing -> pure emptyStep
            Just (key,witness) -> pure (RelationalStep [LogicalAnswer (RuleAnswer (AtomicLeaf target) key ExactAnswer witness)] [] [])
        AlternateHeadWork identifier ordinal entry -> do
            requested <- atomicRequest identifier
            inputs <- lift (ruleInputs owner ordinal)
            discoverOpaqueHead identifier ordinal inputs (registeredRule entry) requested
        ProducerWork identifier selected -> do
          requested <- atomicRequest identifier
          grounded <- all isJust <$> traverse ground (canonicalPatternAtom requested)
          nextProducer grounded selected >>= \case
            Nothing -> pure emptyStep
            Just (possible,((ordinal,entry),rest)) -> do
                lift (rulePhase owner ("producer-request=" <> Text.pack (show identifier)
                    <> " ordinal=" <> Text.pack (show ordinal)))
                charge 1
                inputs <- lift (ruleInputs owner ordinal)
                -- Structural agreement already certifies compatible operand
                -- denotations. Reserve the more expensive Core filter for
                -- alternative views after ordinary unification fails.
                step <- withRegistration ordinal $ startRuleWithInputs charge bound inputs (registeredRule entry) requested >>= \case
                    Left failure -> reject failure >> pure emptyStep
                    Right Nothing -> if possible then discoverOpaqueHead identifier ordinal inputs (registeredRule entry) requested
                        else pure emptyStep
                    Right (Just state) -> do
                        primary <- constrainHead identifier (registeredRule entry) state >>= \case
                            Nothing -> pure emptyStep
                            Just constrained -> do
                                request <- requestKey identifier
                                if possible then discoverRule request ordinal constrained else
                                    groundRuleInstantiation charge bound constrained >>= \case
                                        Right (Just instantiated) -> activateGround request ordinal constrained instantiated
                                        Right Nothing -> pure emptyStep
                                        Left failure -> reject failure >> pure emptyStep
                        parent <- requestKey identifier
                        -- A structural head match is a useful first candidate,
                        -- but erased arguments and alternate views can denote
                        -- the same operand. Discover those through the ordinary
                        -- clause plan, retaining complete-operand constraints.
                        -- Admission can certify that a faithful head fixes
                        -- the parameter values even with compound premises.
                        pure primary {relationalDeferred = relationalDeferred primary <>
                            [(Just parent,AlternateHeadWork identifier ordinal entry)
                                | possible && ruleNeedsHeadDiscovery (registeredRule entry)]}
                pure step {relationalDeferred = relationalDeferred step <>
                    [(Just (LeafQuery (AtomicLeaf (atomSignature (canonicalPatternAtom requested))) identifier),ProducerWork identifier rest)]}
        ForwardWork row answer views -> do
            charge (indexWork (Map.size views) 1)
            case Map.minViewWithKey views of
                Nothing -> pure emptyStep
                Just ((ordinal,view),rest) -> do
                    event (Diagnostics.Count Diagnostics.ForwardView 1)
                    step <- withRegistration ordinal $
                        applyForwardRule charge bound view SourceRow row (ruleAnswerWitness answer) >>= \case
                            Left failure -> reject failure >> pure emptyStep
                            Right Nothing -> pure emptyStep
                            Right (Just completed) -> publish ordinal completed
                    pure step {relationalDeferred = [(Nothing,ForwardWork row answer rest) | not (Map.null rest)]}
        WholeSourceWork request sources -> case sources of
            [] -> pure emptyStep
            formula:rest -> do
                charge 1
                evidence <- lift (ruleWholeEvidence owner (evidenceOnlyRequest (WholeRequest formula Nothing)))
                pure (RelationalStep
                    [LogicalAnswer (RuleAnswer (WholeLeaf formula) key ExactAnswer witness) | (key,witness) <- maybe [] pure evidence]
                    [] [(Just request,WholeSourceWork request rest) | not (null rest)])
        OpenWholeWork identifier producers -> nextProducer False producers >>= \case
            Nothing -> pure emptyStep
            Just (_,((ordinal,entry),rest)) -> do
                let request = OpenWholeQuery identifier
                    rule = registeredRule entry
                inputs <- lift (ruleInputs owner ordinal)
                demand <- getOpenWhole identifier
                let waiting = openDemandWaiting demand
                    introduce = wholeWaitingPosition waiting /= 0 || not (ruleIsElimination (openDemandRule demand))
                step <- if ruleIsIntroduction rule && not introduce then pure emptyStep else
                  withRegistration ordinal $ startWholeRule charge inputs rule >>= \case
                    Left failure -> reject failure >> pure emptyStep
                    Right state -> specializeDemand identifier state >>= maybe (pure emptyStep) (discoverRule request ordinal)
                pure step {relationalDeferred = relationalDeferred step <>
                    [(Just request,OpenWholeWork identifier rest)]}
        ExactPremiseWork request ordinal selected state waiting ->
            subscribeWhole request ordinal selected state waiting
        OpenAtomicWork identifier producers -> case Map.minViewWithKey producers of
            Nothing -> pure emptyStep
            Just ((ordinal,entry),rest) -> do
                charge (indexWork (Map.size producers) 1)
                event (Diagnostics.Count Diagnostics.AttemptedProducer 1)
                let request = OpenWholeQuery identifier
                    rule = registeredRule entry
                demand <- getOpenWhole identifier
                let waiting = openDemandWaiting demand
                    origin = atomSignature <$> ruleAtomicPremise (wholeWaitingPosition waiting) (openDemandRule demand)
                step <- case ruleDescription rule of
                    (_,_,AtomicLeaf atom) | Just (atomSignature atom) /= origin -> do
                        possible <- possibleRule ordinal rule
                        if not possible then pure emptyStep else do
                          pattern' <- State.evalStateT (traverseAtomTemplateArguments (\_ -> do
                              lift (charge 1)
                              position <- State.get
                              State.put (position+1)
                              pure (TemplateVariable (Output position))) atom) 0
                          query pattern' >>= \case
                              Left failure -> reject (JoinPatternRejected failure) >> pure emptyStep
                              Right requested -> do
                                  canonical' <- atomicRequest (leafIdentifier requested)
                                  inputs <- lift (ruleInputs owner ordinal)
                                  withRegistration ordinal $ startRuleWithInputs charge bound inputs rule canonical' >>= \case
                                      Left failure -> reject failure >> pure emptyStep
                                      Right Nothing -> pure emptyStep
                                      Right (Just state) -> specializeDemand identifier state >>= maybe (pure emptyStep) (discoverRule request ordinal)
                    _ -> pure emptyStep
                pure step {relationalDeferred = relationalDeferred step <>
                    [(Just request,OpenAtomicWork identifier rest) | not (Map.null rest)]}
        WholeProducerWork identifier producers -> nextProducer False producers >>= \case
            Nothing -> pure emptyStep
            Just (_,((ordinal,entry),rest)) -> do
                let rule = registeredRule entry
                request <- requestKey identifier
                requestedWhole <- canonical identifier >>= \case
                    WholeLeaf requested -> pure requested
                    AtomicLeaf{} -> error "a whole producer lost its whole demand"
                inputs <- lift (ruleInputs owner ordinal)
                step <- if ruleIsIntroduction rule && not (wholeRequestIntroducible requestedWhole)
                  then pure emptyStep else withRegistration ordinal $ startWholeRule charge inputs rule >>= \case
                    Left failure -> reject failure >> pure emptyStep
                    Right state -> do
                        constraints <- case ruleConclusionPattern rule of
                            Just pattern' -> lift (ruleMatchWhole owner pattern' (wholeRequestFormula requestedWhole))
                            Nothing -> pure (Just Map.empty)
                        case constraints of
                            Nothing -> pure emptyStep
                            Just values -> do
                                admitted <- Map.traverseMaybeWithKey (\_ value -> do
                                    allowed <- supported (TemplateVariable value)
                                    pure (if allowed then Just value else Nothing)) values
                                bindWholeRuleInputs charge admitted state >>= \case
                                    Nothing -> pure emptyStep
                                    Just boundState -> discoverRule request ordinal (constrainRule values boundState)
                pure step {relationalDeferred = relationalDeferred step <>
                    [(Just request,WholeProducerWork identifier rest)]}
        EnumerateWork request ordinal state slots completion slot pattern' prepared cursor -> componentClosed request >>= \closed ->
          if closed then pure emptyStep else do
            comparison <- case prepared of
                Just existing -> pure (Just existing)
                Nothing -> prepareAssignmentFilter request state completion (ViewVariableIx slot)
            case comparison of
                Nothing -> pure emptyStep
                Just check -> do
                    let argument = Map.lookup (ViewVariableIx slot) (ruleArgumentConstraints state)
                        compatible partial = do
                            structural <- maybe (pure True) (\known -> mayUnifyPartialTerm charge known partial) pattern'
                            operand <- if not structural then pure False else maybe (pure True)
                                (\value -> lift (ruleTermsMayAgree owner partial (TemplateVariable (Just value)))) argument
                            if operand then lift (check partial) else pure False
                    nextMatchingSupportTerm supportOwner charge (Just compatible) cursor >>= \case
                        Nothing -> pure emptyStep
                        Just (candidate,next) -> do
                            step <- case candidate of
                                Nothing -> pure emptyStep
                                Just value -> bindRuleVariable charge slot value state >>= \case
                                    Nothing -> pure emptyStep
                                    Just boundState -> compatibleState request boundState >>= \compatible' ->
                                      if not compatible' then pure emptyStep else assign request ordinal boundState slots completion emptyStep
                            pure step {relationalDeferred = relationalDeferred step <>
                                [(Just request,EnumerateWork request ordinal state slots completion slot pattern' comparison next)]}
        GroundWork identifier -> do
            GroundEntry request ordinal instance' <- getInstance identifier
            event (Diagnostics.Count Diagnostics.AnswerTuple 1)
            withRegistration ordinal do
                witnesses <- Ground.instanceWitnesses charge instance'
                case request of
                    ComponentQuery component -> publishComponent component
                        (groundRuleSubstitution (Ground.instanceRule instance')) witnesses
                    _ -> do
                        completed <- completeGroundRule charge (Ground.instanceRule instance') witnesses
                        publish ordinal completed
    getComponent identifier = do
        demands <- State.gets componentDemands
        charge (indexWork (IntMap.size demands) 1)
        pure (demands IntMap.! identifier)
    componentClosed = \case
        LeafQuery{} -> pure False
        WholeSchemaQuery{} -> pure False
        OpenWholeQuery{} -> pure False
        ProducerQuery{} -> pure False
        ComponentQuery identifier -> do
            demand <- getComponent identifier
            pure (demandBoolean demand && not (Set.null (demandResults demand)))
    internInstanceTerm term = do
        terms <- State.gets instanceTerms
        (identifier,next) <- Terms.intern charge term terms
        State.modify' (\current -> current {instanceTerms = next})
        pure identifier
    -- Separate components share no free body variable. Order them once from
    -- the requested head; each result advances the retained cursor. Replanning
    -- every remaining component would make a wide conjunction quadratic.
    subscribeComponent request ordinal selected state = do
        let pending = pendingRuleComponents state
            candidates = if ruleComponentsPlanned state then take 1 pending else pending
        plans <- fmap catMaybes $ for candidates \component ->
            ruleComponentValues charge bound component state >>= \case
                Left failure -> reject failure >> pure Nothing
                Right values -> do
                    let pinned = Map.mapMaybe id values
                        ready = componentVariables component `Set.isSubsetOf` Map.keysSet pinned
                    charge (fromIntegral (Map.size values))
                    pure (Just (component,values,(not ready,Down (Map.size pinned),componentIndex component)))
        case sortOn (\(_,_,priority) -> priority) plans of
            [] -> pure emptyStep
            (component,values,_):rest -> do
                let ordered = if ruleComponentsPlanned state then pending else component : [next | (next,_,_) <- rest]
                    waitingState = planRuleComponents ordered state
                keyValues <- traverse (traverse internInstanceTerm) values
                known <- State.gets componentIds
                let constraints = Map.restrictKeys (ruleArgumentConstraints state) (componentVariables component)
                    source = if Set.member 0 (componentPositions component) then ruleWholeConstraint state else Nothing
                    key = (ordinal,componentIndex component,Map.toAscList keyValues,Map.toAscList constraints,source)
                charge (2 * indexWork (Map.size known) (2 + fromIntegral (Map.size keyValues + Map.size constraints)))
                identifier <- case Map.lookup key known of
                    Just identifier -> pure identifier
                    Nothing -> do
                        event (Diagnostics.Count Diagnostics.ComponentRequest 1)
                        let identifier = Map.size known
                            inputs = Map.mapMaybe id values
                            boolean = componentOutputs component `Set.isSubsetOf` Map.keysSet inputs
                            demand = ComponentDemand ordinal (activeRule state) component inputs constraints source boolean Set.empty
                        State.modify' (\current -> current
                            { componentIds = Map.insert key identifier known
                            , componentDemands = IntMap.insert identifier demand (componentDemands current) })
                        pure identifier
                waiting <- State.gets componentWaiters
                let subscriber = IntMap.size waiting
                charge (indexWork subscriber 1)
                State.modify' (\current -> current {componentWaiters = IntMap.insert subscriber
                    (ComponentWaiter request ordinal selected waitingState) waiting})
                pure (RelationalStep [] [(ComponentQuery identifier,Just (ComponentContinuation subscriber))] [])
    publishComponent identifier values witnesses = do
        demand <- getComponent identifier
        projection <- traverse (\slot -> do
            charge (indexWork (Map.size values) 1)
            internInstanceTerm (values Map.! slot)) (Set.toAscList (componentOutputs (demandComponent demand)))
        charge (2 * indexWork (Set.size (demandResults demand)) (1 + fromIntegral (length projection)))
        if Set.member projection (demandResults demand) then pure emptyStep else do
            State.modify' (\current -> current {componentDemands = IntMap.insert identifier
                demand {demandResults = Set.insert projection (demandResults demand)} (componentDemands current)})
            event (Diagnostics.Count Diagnostics.ComponentResult 1)
            pure (RelationalStep [ComponentAnswer identifier projection values witnesses] [] [])
    getInstance identifier = do
        count <- State.gets (Map.size . instanceIds)
        charge (indexWork count 1)
        State.gets ((IntMap.! identifier) . groundInstances)
    putInstance identifier entry = do
        count <- State.gets (Map.size . instanceIds)
        charge (indexWork count 1)
        State.modify' (\current -> current {groundInstances = IntMap.insert identifier entry (groundInstances current)})
    deferGround identifier step ready =
        pure step {relationalDeferred = relationalDeferred step <>
            [(Nothing,GroundWork identifier) | ready]}
    activateGround request ordinal state instantiated = do
        admitted <- foldM (\ready value -> if ready then supported value else pure False)
            True (Map.elems (ruleBinderValues instantiated))
        if admitted then activateAdmitted request ordinal state instantiated else pure emptyStep
    activateAdmitted request ordinal state instantiated = do
        knownTerms <- State.gets instanceTerms
        (terms, updatedTerms) <- State.runStateT
            (traverse (\term -> State.StateT (Terms.intern charge term)) (Map.elems (ruleBinderValues instantiated))) knownTerms
        State.modify' (\current -> current {instanceTerms = updatedTerms})
        known <- State.gets instanceIds
        let component = case request of ComponentQuery identifier -> Just identifier; _ -> Nothing
            key = (ordinal, component, terms)
        charge (2 * indexWork (Map.size known) (1 + fromIntegral (length terms)))
        case Map.lookup key known of
            Just _ -> pure emptyStep
            Nothing -> prepareGroundRuleState charge state instantiated >>= \case
                Left failure -> reject failure >> pure emptyStep
                Right prepared -> do
                    compatible <- foldM (\matches (position,expected) -> if not matches then pure False else
                        case Map.lookup position (groundRuleLeaves prepared) of
                            Just (WholeLeaf template) -> do
                                actual <- lift (ruleWholeRequest owner ordinal (Just position) (groundRuleSubstitution prepared) template)
                                pure (expected == wholeRequestFormula actual)
                            _ -> error "a whole selection lost its premise") True (Map.toAscList (ruleWholeSelections state))
                    if compatible then activatePrepared known key prepared else pure emptyStep
      where
        activatePrepared known key prepared = do
            planned <- Map.traverseWithKey (\position -> \case
                AtomicLeaf row -> pin row >>= query
                WholeLeaf whole -> Right <$> wholeQuery ordinal (Just position)
                    (position /= 0 || not (ruleIsElimination (activeRule state)))
                    (groundRuleSubstitution prepared) whole) (groundRuleLeaves prepared)
            case sequence planned of
                Left failure -> reject (JoinPatternRejected failure) >> pure emptyStep
                Right requests -> do
                    instance' <- Ground.prepareInstance charge prepared (leafIdentifier <$> requests)
                    let identifier = Map.size known
                    State.modify' (\current -> current {instanceIds = Map.insert key identifier (instanceIds current)})
                    event (Diagnostics.Count Diagnostics.GroundInstance 1)
                    event (Diagnostics.Count Diagnostics.PreparedGroundPremise (fromIntegral (Map.size requests)))
                    putInstance identifier (GroundEntry request ordinal instance')
                    subscriptions <- for (Map.keys (Ground.instanceRequests instance')) \child -> do
                        requested <- requestKey child
                        pure (requested, Just (GroundContinuation identifier child))
                    deferGround identifier (RelationalStep [] subscriptions []) (Ground.instanceReady instance')
    advance request ordinal selected state = do
      closed <- componentClosed request
      compatible <- compatibleState request state
      if closed || not compatible then pure emptyStep else do
        let identity = (request,ordinal,Map.toAscList selected)
        seen <- State.gets advancedSelections
        charge (indexWork (Set.size seen) (3 + 2 * fromIntegral (Map.size selected)))
        if Set.member identity seen then event (Diagnostics.Count Diagnostics.RepeatedJoin 1) >> pure emptyStep else do
            charge (indexWork (Set.size seen) (3 + 2 * fromIntegral (Map.size selected)))
            State.modify' (\current -> current {advancedSelections = Set.insert identity seen})
            advanceOnce request ordinal selected state
    -- Different premise arrival orders can reach the same checked selection.
    -- The request, original rule, and exact answer keys determine its join
    -- state, including the structural views used for binding. Expand it
    -- once, rather than rebuilding all remaining subscriptions per ordering.
    advanceOnce request ordinal selected state
      | not (null (pendingRuleComponents state)) = subscribeComponent request ordinal selected state
      | otherwise = groundRuleInstantiation charge bound state >>= \case
        Left failure -> reject failure >> pure emptyStep
        Right (Just instantiated) -> activateGround request ordinal state instantiated
        Right Nothing -> advancePartial request ordinal selected state
    advancePartial request ordinal selected state = do
        wholeOptions <- wholeRuleOptions charge bound state
        atomicOptions <- ruleOptions charge bound state
        let whole = [waiting | (position,Right waiting) <- wholeOptions,
                isNothing (ruleAtomicPremise position (activeRule state))]
            ready = [waiting | waiting <- whole, all isJust (wholeWaitingInputs waiting)]
            grounded = any (either (const False) ruleWaitingIsGround . snd) atomicOptions
        case ready of
            waiting:_ -> subscribeWhole request ordinal selected state waiting
            [] | grounded -> advanceAtomic request ordinal selected state atomicOptions
               | null wholeOptions && null atomicOptions -> do
                    let slots = case ruleStateComponent state of
                            Just component -> Set.toAscList (componentVariables component)
                            Nothing -> let (arity,_,_) = ruleDescription (activeRule state)
                                in ViewVariableIx <$> take (fromIntegral arity) [0..]
                    assign request ordinal state slots CompleteAssignment emptyStep
               | otherwise -> do
                    source <- advanceAtomic request ordinal selected state atomicOptions
                    foldM (\step (position,option) -> case option of
                        Left failure -> reject failure >> pure step
                        Right waiting -> do
                            possible <- case ruleAtomicPremise position (activeRule state) of
                                Nothing -> pure True
                                Just atom -> wholeTruthAvailable (atomSignature atom)
                            if not possible then pure step else case relationalSubscriptions source of
                                -- This branch has no ground atomic premise.
                                -- A partial row request can postpone its exact
                                -- alternatives after an answer, but cannot discard
                                -- them: the table drains them at saturation.
                                (prerequisite,_):_ -> pure step {relationalDeferred = relationalDeferred step <>
                                    [(Just prerequisite,ExactPremiseWork request ordinal selected state waiting)]}
                                [] -> appendSteps step <$> subscribeWhole request ordinal selected state waiting)
                        source wholeOptions
    appendSteps first second = RelationalStep
        (relationalEmissions first <> relationalEmissions second)
        (relationalSubscriptions first <> relationalSubscriptions second)
        (relationalDeferred first <> relationalDeferred second)
    advanceAtomic request ordinal selected state options = do
        charge (fromIntegral (length options))
        let (grounded,other) = partition (either (const False) ruleWaitingIsGround . snd) options
        case grounded of
            ready:_ -> subscribeNext request ordinal selected (discoveryKey request ordinal selected) [ready]
            [] -> do
                active <- State.gets activeSourceHeads
                ordered <- fmap (snd <$>) . fmap (sortOn fst) $ for other \option@(_,candidate) -> do
                    available <- case candidate of
                        Left{} -> pure False
                        Right premise -> do
                            charge (indexWork (Set.size active) 3)
                            let pattern' = ruleWaitingPattern premise
                                signature = atomSignature pattern'
                            if Set.notMember signature active then pure False else do
                                postings <- State.gets activeSourceArguments
                                foldM (\found (position,term) -> if not found then pure False else do
                                    value <- case Map.lookup position (ruleWaitingConstraints premise) of
                                        Just known -> pure (Just known)
                                        Nothing -> ground term >>= maybe (pure Nothing) (lift . ruleArgumentValue owner)
                                    case value of
                                        Nothing -> pure True
                                        Just key -> do
                                            charge (indexWork (Set.size postings) 5)
                                            indexed <- fst <$> lift (ruleArgumentClass owner key)
                                            pure (Set.member (signature,position,indexed) postings))
                                    True (zip [0..] (toList pattern'))
                    let (complete,anchored,leading) = either (const (0,0,False)) ruleWaitingBindingPriority candidate
                    -- A compatible existing source precedes finer
                    -- syntactic tie-breaks. Pins guide discovery when
                    -- neither premise already has a usable row.
                    pure ((Down complete,Down available,Down anchored,Down leading),option)
                known <- State.gets fallbackStates
                let key = discoveryKey request ordinal selected
                charge (indexWork (Map.size known) 2)
                unless (Map.member key known) $
                    State.modify' (\current -> current {fallbackStates = Map.insert key state known})
                step <- subscribeNext request ordinal selected key ordered
                pure step
    -- Evidence matching, primitive construction and final rule inputs share U.
    -- The caller owns the finite slot set and the action after it is assigned.
    assign request ordinal state slots completion step = ruleBindings charge bound slots state >>= \case
        Left failure -> reject failure >> pure step
        Right values -> case [(index,value) | (ViewVariableIx index,value) <- Map.toAscList values, isNothing value] of
            [] -> appendSteps step <$> finishAssignment request ordinal state values completion
            (slot,_):_ -> ruleVariablePattern charge bound slot state >>= \case
                Left failure -> reject failure >> pure step
                Right known -> do
                    let pattern' = case known of TemplateVariable Output{} -> Nothing; _ -> Just known
                        action = case completion of
                            MatchAssignment _ position _ -> "match:" <> Text.pack (show position)
                            RequestAssignment _ waiting -> "construct:" <> Text.pack (show (wholeWaitingPosition waiting))
                            CompleteAssignment -> "complete"
                    lift (rulePhase owner ("assign ordinal=" <> Text.pack (show ordinal) <> " action=" <> action
                        <> " slot=" <> Text.pack (show slot) <> " constrained=" <>
                        Text.pack (show (Map.member (ViewVariableIx slot) (ruleArgumentConstraints state)))))
                    pure step {relationalDeferred = relationalDeferred step <>
                        [(Just request,EnumerateWork request ordinal state slots completion slot pattern' Nothing (supportCursor support))]}
    finishAssignment request ordinal state values = \case
        CompleteAssignment -> groundRuleInstantiation charge bound state >>= \case
            Left failure -> reject failure >> pure emptyStep
            Right Nothing -> error "completed assignments left an unresolved clause input"
            Right (Just instantiated) -> activateGround request ordinal state instantiated
        RequestAssignment selected waiting -> subscribeWhole request ordinal selected state
            waiting {wholeWaitingInputs = values}
        MatchAssignment selected position answer -> do
            let bindings = Map.mapMaybe id values
            projection <- traverse (\(slot,term) -> (,) slot <$> internInstanceTerm term) (Map.toAscList bindings)
            let resume key updated = advance request ordinal
                    (Map.insert position (LogicalKey key,projection) selected) updated
            case ruleAtomicPremise position (activeRule state) of
                Just _ -> do
                    options <- ruleOptions charge bound state
                    case lookup position options of
                        Just (Right waiting) -> do
                            arguments <- traverseAtomTemplateArguments ground (ruleWaitingPattern waiting)
                            case traverseAtomTemplateArguments id arguments of
                                Nothing -> error "a matched atomic premise lost a finite input"
                                Just atom -> do
                                    joined <- case ruleAnswerLeaf answer of
                                        WholeLeaf{} -> pure (Right Nothing)
                                        AtomicLeaf row -> resumeRule charge (ruleAnswerCapability answer) waiting row (ruleAnswerWitness answer)
                                    case joined of
                                        Left failure -> reject failure >> pure emptyStep
                                        Right (Just updated) -> resume (ruleAnswerKey answer) updated
                                        Right Nothing -> lift (ruleConverted owner atom answer) >>= \case
                                            Nothing -> pure emptyStep
                                            Just (key,witness) -> resume key (consumeAtomicPremise position witness state)
                        Just (Left failure) -> reject failure >> pure emptyStep
                        Nothing -> pure emptyStep
                Nothing -> do
                    options <- wholeRuleOptions charge bound state
                    case lookup position options of
                        Just (Right waiting) -> do
                            requested <- lift (ruleWholeRequest owner ordinal (Just position) bindings (wholeWaitingTemplate waiting))
                            formula <- wholeAnswerFormula answer
                            if formula /= wholeRequestFormula requested then pure emptyStep else
                                resume (ruleAnswerKey answer) (constrainWholePremise position formula state)
                        Just (Left failure) -> reject failure >> pure emptyStep
                        Nothing -> pure emptyStep
    -- A determined guard is required by every remaining assignment. Its own
    -- demand has all eligible producers in this fixed domain, so other body
    -- joins cannot supply an additional assumption or enlarge its universe.
    -- Check it before discovering parameters. Retain the first unresolved
    -- state for finite fallback; later row mismatches activate that same cursor.
    subscribeNext request ordinal selected key = \case
        [] -> pure emptyStep
        (position,candidate):rest -> case candidate of
            Left failure -> reject failure >> subscribeNext request ordinal selected key rest
            Right premise -> queryConstrained (ruleWaitingPattern premise) (ruleWaitingConstraints premise) >>= \case
                Left failure -> reject (JoinPatternRejected failure) >> subscribeNext request ordinal selected key rest
                Right requested -> do
                    let identity = (request,ordinal,Map.toAscList selected,position)
                    current <- State.get
                    charge (2 * indexWork (Map.size (continuationIds current)) (4 + 2 * fromIntegral (Map.size selected)))
                    identifier <- case Map.lookup identity (continuationIds current) of
                        Just existing -> pure existing
                        Nothing -> do
                            let fresh = IntMap.size (continuations current)
                            State.put current
                                { continuationIds = Map.insert identity fresh (continuationIds current)
                                , continuations = IntMap.insert fresh (Waiting request (leafIdentifier requested) ordinal selected position premise)
                                    (continuations current) }
                            pure fresh
                    let step = RelationalStep [] [(requested,Just (PartialContinuation identifier))] []
                    if ruleWaitingIsGround premise then pure step else do
                        waiting <- State.gets fallbackWaiters
                        charge (indexWork (Map.size waiting) 2)
                        let child = leafIdentifier requested
                            producers = Map.findWithDefault Map.empty child waiting
                        charge (indexWork (Map.size producers) 1)
                        State.modify' (\state' -> state' {fallbackWaiters = Map.insert child
                            (Map.insert key position producers) waiting})
                        missing <- State.gets missingViewRequests
                        charge (indexWork (Map.size missing) 1)
                        let prior = Map.findWithDefault Map.empty child missing
                        charge (fromIntegral (Map.size prior))
                        pure step {relationalDeferred =
                            [(Just request,FallbackWork (Map.singleton key position) answer) | answer <- Map.elems prior]}
    publish ordinal completed = do
        result <- lift (completedLeaf owner ordinal completed)
        admitted <- case result of
            AtomicLeaf atom -> fmap (fmap (const ())) (pin atom >>= query)
            WholeLeaf{} -> pure (Right ())
        case admitted of
            Left failure -> reject (JoinPatternRejected failure) >> pure emptyStep
            Right () -> lift (ruleCompleted owner ordinal completed result) >>= \case
                Nothing -> pure emptyStep
                Just (key,witness) -> do
                    event (Diagnostics.Count Diagnostics.CompletedRule 1)
                    let capability = case result of AtomicLeaf{} -> SourceRow; WholeLeaf{} -> ExactAnswer
                    pure (RelationalStep [LogicalAnswer (RuleAnswer result key capability witness)] [] [])

completedLeaf
    :: Monad m => RuleEvaluator m variable bucket key witness -> Natural -> CompletedRule variable witness
    -> m (NotionLeaf (AtomTemplate (SetTermTemplate variable)) FormulaId)
completedLeaf owner ordinal completed = case ruleResult instantiated of
    AtomicLeaf atom -> pure (AtomicLeaf atom)
    WholeLeaf template -> WholeLeaf . wholeRequestFormula <$>
        ruleWholeRequest owner ordinal Nothing (ruleBinderValues instantiated) (WholeResidual template)
  where
    instantiated = completedInstantiation completed
