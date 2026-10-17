{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

-- | General source elaboration into checked core.
module Felix.Checking.Elaboration
    ( LocalId
    , localId
    , localIdValue
    , concreteTypeCoreType
    , ElaborationState
    , Elaborate
    , ResolvedStructureApplication(..)
    , AssertableStructureApplication(..)
    , structureAnnotationPredicate
    , structureAnnotationArguments
    , initialBindingElaborationState
    , beginAbbreviationExpansion
    , elaborationExpansionAllowance
    , initialStructureElaborationState
    , initialElaborationStateLowering
    , setElaborationDefinitionProvider
    , initializeDefinitionElaboration
    , setElaborationStructureAnnotation
    , elaborationRequiredContextualFields
    , elaborationFormationContract
    , PreparedDefinitionResult
    , PreparedDefinitionResults, preparedDefinitionResultItems, preparedDefinitionCompletion
    , preparedDefinitionResultHeaders
    , preparedDefinitionResultBody
    , preparedDefinitionResultProposition
    , preparedDefinitionResultPredicate
    , preparedDefinitionResultEvidence
    , preparedDefinitionResultProvider
    , preparedDefinitionResultPremises
    , preparedDefinitionResultConclusion
    , elaborationDefinitionResults
    , DefinitionBaseProjection
    , definitionBaseProjectionTemplate
    , definitionBaseProjectionFormula
    , definitionBaseProjectionPath
    , elaborationDefinitionBaseProjections
    , compilePredicateDefinition
    , compileHostedSetTermDefinition
    , compileHostedConstructionDefinition
    , compileHostedSetTermDefinitionWithFormationObservation
    , annotateBinderContext
    , binderIndices
    , binderStructures
    , compileIntroducedVariable
    , applyStructureAnnotation
    , checkEnvelopeProposition
    , compileHeaderAssumption
    , compileHeaderAssumptionPropositions
    , compileStructureNotionProposition
    , retainStructureFormationComponent
    , retainCheckedStructureFormationComponent
    , CompiledProposition
    , compiledPropositionCore
    , compiledPropositionAssertions
    , compiledPropositionEvidence
    , compiledPropositionEqualities
    , ScopedSourceNotionOccurrence
    , ScopedSourceNotionAssertion
    , ScopedSourceEqualityOccurrence
    , ScopedSourceTerm
    , CompiledBody(..)
    , CompiledBodySource(..)
    , CompiledSourceTerm
    , CompiledNamedSetConstruction(..)
    , checkElaboratedNamedSetConstruction
    , preparedSetConstructionClosedBody
    , compileExpressionAsSet
    , compileNamedSetExpression
    , compileNamedSetExpressionWithSource
    , compileNamedSetTerm
    , compileNamedSetTermWithSource
    , ordinaryCompiledBody
    , sourceTermCompiledBody
    , propositionCompiledBody
    , compileTermAsSet
    , compileSourceExpressionAsSetTerm
    , compileSourceTermAsSet
    , compileStatement
    , compileTypedExpression
    , ElaborationContext
    , FormationPremiseSource
    , FormationEqualitySource
    , FormationProofLocalKind(..)
    , FormationSourceOrigin(..)
    , NotionQueryConsumer(..)
    , notionQueryAdmitsOrigin
    , FormationObservation
    , formationObservationSource
    , formationObservationAssertion
    , formationObservationOrigin
    , formationObservationOrdinal
    , FormationObservationError(..)
    , formationObservationsFor
    , countedFormationObservationsFor
    , countedElaborationFormationObservations
    , formationEvidenceSource
    , rebaseEvidenceOntoLocal
    , formationEqualitySource
    , addFormationPremiseSource
    , addFormationEqualitySource
    , prepareFormationPremiseSource, prepareFormationEqualitySource
    , runFormationScopePreparation, runFormationScopePreparationWithWork, finishFormationScopePreparation
    , extendElaborationContextWithFormationAlias
    , extendElaborationContextWithFormationAliasLowering
    , AlignedFormationAliases
    , FormationAliasNormalization
    , FormationAliasReplayStep
    , FormationAliasNormalizationError(..)
    , alignFormationAliases
    , formationAliasesFor
    , countedFormationAliasesFor
    , formationAliasTerms
    , formationAliasDefinitions
    , viewFormationAliases
    , countedViewFormationAliases
    , normalizeFormationAliases
    , countedNormalizeFormationAliases
    , formationAliasNormalizationOriginal
    , formationAliasNormalizationResult
    , formationAliasNormalizationReplaySteps
    , formationAliasReplayStepDefinition
    , formationAliasReplayStepLocation
    , formationAliasReplayStepOrdinal
    , formationAliasReplayStepAbstraction
    , emptyElaborationContext
    , extendElaborationContext
    , extendTypedElaborationContext
    , extendAnonymousElaborationContext
    , extendTypedAnonymousElaborationContext
    , DatatypeElaborationEnvironment
    , datatypeElaborationEnvironment
    , elaborateDatatypeExpression
    , RecursiveBranch(..)
    , elaborateRecursiveBranches
    , elaborationContextSupport
    , elaborationContextIndex
    , projectProofElaborationContext
    , ElaboratedProposition
    , elaboratedPropositionCore
    , elaboratedPropositionAssertions
    , elaboratedPropositionEvidence
    , elaboratedPropositionEqualities
    , rebaseAssertionsOntoLocal
    , rebaseEqualitiesOntoLocal
    , forgetSourceNotionProviders
    , elaborateProposition
    , elaborateCalculationGuard
    , elaborateSymbolicBoundConstraints
    , elaborateSymbolicWitnessConstraints
    , elaborateNounWitnessConstraints
    , ElaboratedSetExpression
    , elaboratedSetExpressionSource
    , ElaboratedExpression
    , elaboratedExpressionCore
    , elaboratedExpressionSource
    , elaborateExpression
    , ElaboratedRecordAggregate
    , elaboratedAggregateStructure
    , elaboratedAggregateCore
    , elaboratedAggregatePredicate
    , elaboratedAggregateFields
    , RecordFieldOrigin(..)
    , ElaboratedRecordField(..)
    , elaborateRecordAggregate
    , elaborateReconstructionWithBudget
    , ReconstructionCandidate(..)
    , ReconstructionAttempt(..)
    , ReconstructionFailure(..)
    , ReconstructionInterface(..)
    , RecordInterfaceStatus(..)
    , CheckedCalculationApplication, calculationRelator, calculationLeft, calculationRight
    , calculationLeftSource, calculationRightSource, calculationProposition, calculationOpenProposition
    , transportCalculationApplication, abstractCalculationSource, abstractPropositionSource
    , instantiateCompositionApplication, conjoinElaboratedPropositions, closeCalculationProposition
    , equalityCalculationApplication
    , elaborateRelationCalculation
    , ElaboratedSetConstruction(..)
    , elaboratedSetExpressionCore
    , elaboratedSetExpressionConstruction
    , elaborateSetExpression
    , ElaboratedLocalFunctionGraph
    , elaboratedLocalFunctionGraphCore
    , elaboratedLocalFunctionGraphDomain
    , elaboratedLocalFunctionGraphMap
    , elaborateLocalFunctionGraph
    , ElaboratedClaimEnvelope
    , CompiledHeaderAntecedent
    , compiledHeaderCore
    , compiledHeaderLocation
    , compiledHeaderAssertions
    , compiledHeaderEvidence
    , compiledHeaderEqualities
    , compiledHeaderSourceOrdinal
    , compiledHeaderVariableOrdinal
    , elaboratedClaimTarget
    , elaboratedClaimVariables
    , elaboratedClaimContext
    , elaboratedClaimAntecedentCount
    , elaboratedClaimAntecedents
    , elaboratedClaimConclusionAssertions
    , elaboratedClaimConclusionEvidence
    , elaboratedClaimConclusionEqualities
    , elaborateClaimEnvelope
    , elaborateClaimEnvelopeWithFormationObservation
    , elaborateClaimEnvelopeWithLocalTransparentObject
    , interpretFormationTemplate
    , SourceTermPresentation(..)
    , sourceTermPresentation
    , FormationRequirementFailure(..)
    , RichFormationFailureDetail(..)
    , ProviderFailureSource(..)
    , ProviderFormationFailure(..)
    , NullaryClassificationFailure(..)
    , NotionQueryOutcome(..)
    , NotionQueryFailure
    , notionQueryFailurePath
    , renderNotionQueryFailure
    , elaborateProofNotionEvidence
    , elaborateProofNotionEvidenceWithBudget
    , prepareProofNotionEvidence
    , prepareProofNotionGoalWithBudget
    , prepareProofNotionGoalAttemptWithBudget
    , ElaborationError(..)
    , elaborationErrorLocation
    , renderElaborationError
    ) where

import Base hiding (Empty)

import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Predicate qualified as StructurePredicate
import Felix.Checking.Structure.Interface qualified as StructureInterface
import Felix.Checking.Structure.Environment qualified as StructureEnvironment
import Felix.Checking.Structure.Builtin qualified as StructureBuiltin
import Felix.Checking.Calculation qualified as Calculation
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration.Vocabulary
import Felix.Checking.GlobalTyping (GlobalTyping, lookupGlobalType)
import Felix.Checking.Identity
import Felix.Checking.Notion
import Felix.Checking.Notion.Composite qualified as Composite
import Felix.Checking.Notion.Evaluation qualified as FormationEvaluation
import Felix.Checking.Notion.Request qualified as FormationRequest
import Felix.Checking.Notion.Goal qualified as FormationGoal
import Felix.Checking.Notion.Rule qualified as FormationRule
import Felix.Checking.Notion.Premise qualified as NotionPremise
import Felix.Checking.Notion.Join qualified as FormationJoin
import Felix.Checking.Notion.Relational qualified as FormationRelational
import Felix.Checking.Notion.Catalog qualified as FormationCatalog
import Felix.Checking.Notion.Diagnostics qualified as FormationDiagnostics
import Felix.Checking.Notion.SourceEvidence (SourceEvidence(..), SourceInput(..))
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Notion.UniversalTemplate qualified as UniversalTemplate
import Felix.Checking.Notion.SuppliedUniversal qualified as SuppliedUniversal
import Felix.Checking.Notion.ScopedSource qualified as ScopedSource
import Felix.Checking.Notion.SourceRows qualified as FormationRows
import Felix.Checking.Notion.LeafIndex qualified as FormationLeaves
import Felix.Checking.Notion.EqualityIndex qualified as FormationEqualities
import Felix.Checking.Notion.TermIndex qualified as FormationTerms
import Felix.Checking.Notion.FormulaIndex qualified as FormationFormulas
import Felix.Checking.Notion.WholePattern qualified as WholePattern
import Felix.Checking.Notion.Support qualified as FormationSupport
import Felix.Checking.Obvious.Template qualified as CoreTemplate
import Felix.Checking.Notion.ProviderResult qualified as ProviderResult
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic
import Felix.Checking.SetConstruction
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.SourceTemplate qualified as SourceTemplate

import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Lexicon qualified as Lexicon
import Felix.Syntax.Token qualified as Token

import Data.Word (Word)
import Control.Monad.Except (ExceptT)
import Control.Monad.Except qualified as Except
import Control.Monad (filterM, foldM, replicateM_, unless, when)
import Control.Monad.State.Strict (StateT)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class qualified as Trans
import Data.Ord (Down(..))
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


-- | A disposable identity allocated in source order within one proof.
newtype LocalId = LocalId Natural
    deriving stock (Show, Eq, Ord)

localId :: Natural -> LocalId
localId = LocalId

localIdValue :: LocalId -> Natural
localIdValue (LocalId value) = value

data ElaborationBinder = ElaborationBinder
    !LocalId
    !(Maybe Raw.VarSymbol)
    !CoreType
    !(Maybe ResolvedStructureApplication)

data ResolvedStructureApplication = ResolvedStructureApplication
    !Schema.StructurePhrase
    !(Map.Map Raw.StructSymbol (FieldId, ObjectId))
    ![CompiledSourceTerm]

-- | One active designated receiver, kept distinct from the field or
-- contextual resource selected from it.  Receiver identity is the binder
-- index: two binders remain different candidates even when their structures
-- share one inherited projection object.
data StructureReceiverCandidate selected = StructureReceiverCandidate
    !Natural
    !Text
    !ResolvedStructureApplication
    !selected

data AssertableStructureApplication = AssertableStructureApplication
    !ResolvedStructureApplication
    !StructurePredicate.PendingStructureRegistration

data ResolvedStructureAggregate = ResolvedStructureAggregate
    !Location
    !AssertableStructureApplication
    ![ElaboratedRecordField Raw.Expr]

data LocalGlobalDefinition
    = LocalObjectReference !AssertedObject
    | LocalTransparentExpansion !AssertedObject
    | LocalRecursiveResults !Natural ![Natural] ![(Natural, Natural)] !CoreType

-- | The active nearest-first binders of one elaboration scope, together with
-- invocation-local transparent names.  The latter let an instance proof use
-- its newly introduced name definitionally without publishing its equation
-- as an ordinary searchable premise.
data ElaborationContext = ElaborationContext
    ![ElaborationBinder]
    !(Map.Map SemanticGlobalKey LocalGlobalDefinition)
    !FormationScope

data DatatypeElaborationEnvironment = DatatypeElaborationEnvironment
    !CheckedObjectClosure
    !ElaborationContext

data FormationPremiseSource = FormationPremiseSource
    !(Maybe (Vector (LocalId, CoreType)))
    !(ScopedCheckedCore ObjectId)
    !(SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
    !FormationSourceOrigin

-- | One positive source equality retained independently of notion-head
-- evidence.  N6-D indexes these sources lazily by checked Core endpoints;
-- until that operational stage they are checked sidecars only.
data FormationEqualitySource = FormationEqualitySource
    !(Maybe (Vector (LocalId, CoreType)))
    !(ScopedCheckedCore ObjectId)
    !(NonEmpty ScopedSourceEqualityOccurrence)
    !FormationSourceOrigin

-- | One compiler-owned local definition available for narrow notion
-- transport.  Every retained term and equality is scoped at the support in
-- which the alias itself was introduced.  The root is normalized eagerly, so
-- lookup never searches an equality graph.  The enclosing context keeps these
-- sources strictly newest-definition-first with decreasing own ordinals; this
-- module's atomic extension is the only operation which grows that list.
data FormationAliasSource = FormationAliasSource
    !LocalId
    !(Vector (LocalId, CoreType))
    !ScopedSourceTerm
    !(NonEmpty (MaterializedNotionHypothesis FormationSourceOrigin))
    !Location

data AlignedFormationAlias = AlignedFormationAlias
    !(ScopedCheckedCore ObjectId)
    !ScopedSourceTerm
    !(NonEmpty (MaterializedNotionHypothesis FormationSourceOrigin))
    !Location

newtype AlignedFormationAliases = AlignedFormationAliases
    [AlignedFormationAlias]

data FormationAliasNormalization = FormationAliasNormalization
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)
    ![FormationAliasReplayStep]

data FormationAliasReplayStep = FormationAliasReplayStep
    !(MaterializedNotionHypothesis FormationSourceOrigin)
    !Location
    !Natural
    !(ScopedCheckedCore ObjectId)

data FormationAliasNormalizationError
    = FormationAliasReplacementInvariantFailed
        !Location
        !Natural
        !ScopedOccurrenceReplacementError
    deriving stock (Show, Eq)

data FormationProofLocalKind
    = FormationProofAssumption
    | FormationProofDerivedClaim
    | FormationProofLocalDefinition
    | FormationProofLocalConstructionExtensional
    | FormationProofLocalConstructionEquation
    deriving stock (Show, Eq, Ord)

data FormationGuardKind
    = FormationClaimHeader
    | FormationHostedDefinitionConjunct
    | FormationStructureDeclarationComponent
    | FormationStructurePhraseCore
    | FormationSeparationGenerator
    | FormationRelationalReplacementGenerator
    | FormationReplacementGenerator
    | FormationQuantifiedTermRestriction
    | FormationSymbolicQuantifierRestriction
    | FormationSymbolicQuantifierResidual
    | FormationSymbolicQuantifierBound
    | FormationNounPhraseCore
    | FormationBoundedNounHead
    | FormationPhraseHead
    | FormationQuantifiedNounRestriction
    | FormationImplicationAntecedent
    | FormationExistentialWitnessRestriction
    deriving stock (Show, Eq, Ord)

data FormationSourceOrigin
    = FormationFromProofLocal !Natural !FormationProofLocalKind
    | FormationFromDefinitionHeader
        !Natural
        !(Maybe Natural)
        !Location
    | FormationFromCheckedGuard !FormationGuardKind !Location
    | FormationFromPhraseCore !FormationGuardKind !Location
    | FormationFromGoalAssumption !Natural !Location
    deriving stock (Show, Eq, Ord)

-- A scoped observation remains a premise, not a theorem. Its source origin
-- and enclosing proposition are retained for the eventual consumer to resolve.
-- In particular, exposing this snapshot cannot promote a provisional guard.
data FormationObservation = FormationObservation
    !(ScopedCheckedCore ObjectId)
    !ScopedSourceNotionOccurrence
    !FormationSourceOrigin
    !Natural

formationObservationSource :: FormationObservation -> ScopedCheckedCore ObjectId
formationObservationSource (FormationObservation source _ _ _) = source

formationObservationAssertion :: FormationObservation -> ScopedSourceNotionOccurrence
formationObservationAssertion (FormationObservation _ assertion _ _) = assertion

formationObservationOrigin :: FormationObservation -> FormationSourceOrigin
formationObservationOrigin (FormationObservation _ _ origin _) = origin

formationObservationOrdinal :: FormationObservation -> Natural
formationObservationOrdinal (FormationObservation _ _ _ ordinal) = ordinal

data FormationObservationError
    = FormationObservationScopeError !Text
    | FormationObservationExhausted !FormationSearchError
    | FormationScopePreparationLimitExceeded !Natural
    deriving stock (Show, Eq)

formationObservationsFor
    :: FormationSearchLimits
    -> NotionQueryConsumer
    -> ElaborationContext
    -> Either FormationObservationError ([FormationObservation], FormationSearchStatistics)
formationObservationsFor limits consumer context = do
    (observations, _, budget) <- foldM source
        ([], 0, initialFormationSearchBudget limits) (contextFormationSources context)
    pure (reverse observations, formationSearchBudgetStatistics budget)
  where
    currentTypes = binderTypes context
    currentSupport = elaborationContextSupport context
    source state (FormationPremiseSource support proposition assertions origin) =
        let alignedSource = alignFormationSource currentTypes currentSupport support proposition
        in foldM (observe alignedSource origin) state
            (formationSourceAtoms (SourceEvidence.sourceViews assertions))
    observe alignedSource origin (observations, ordinal, budget) assertion = do
        inspected <- first FormationObservationExhausted
            (consumeFormationSearchStatistics emptyFormationSearchStatistics
                {formationSearchSourceIndexInspections = 1} budget)
        if not (notionQueryAdmitsOrigin consumer origin)
            then pure (observations, ordinal + 1, inspected)
            else do
                parent <- first FormationObservationScopeError alignedSource
                aligned <- first FormationObservationScopeError (alignFormationAssertion currentTypes assertion)
                unless (projectConjunctionPath (sourceAssertionPath aligned) (scopedCoreTerm parent)
                        == Just (scopedCoreTerm (sourceAssertionFormula aligned)))
                    (Left (FormationObservationScopeError "a formation observation does not project its retained source"))
                pure (FormationObservation parent aligned origin ordinal : observations, ordinal + 1, inspected)

-- | The observation snapshot with structural work shared across nominal scope
-- checks, source alignment, projection, and exact formula comparison. Existing
-- formation source-inspection limits still apply independently.
countedFormationObservationsFor
    :: Word -> FormationSearchLimits -> NotionQueryConsumer -> ElaborationContext
    -> (Either (CountedCoreFailure FormationObservationError)
        ([FormationObservation], FormationSearchStatistics), Word)
countedFormationObservationsFor allowance limits consumer context =
    countedFormationObservationsInScope allowance limits consumer (binderTypes context)
        (elaborationContextSupport context) (contextFormationSources context)

-- Read the actual active scope without manufacturing a proof context or
-- promoting provisional guards. The state remains opaque and immutable here.
countedElaborationFormationObservations
    :: Word -> FormationSearchLimits -> NotionQueryConsumer -> ElaborationState
    -> (Either (CountedCoreFailure FormationObservationError)
        ([FormationObservation], FormationSearchStatistics), Word)
countedElaborationFormationObservations allowance limits consumer state =
    countedFormationObservationsInScope allowance limits consumer
        (binderStackTypes (lexicalBinderStack (elaborationScope state))) (elaborationProofSupport state)
        (formationScopeSources (lexicalFormationScope (elaborationScope state)))

countedFormationObservationsInScope
    :: Word -> FormationSearchLimits -> NotionQueryConsumer -> [CoreType]
    -> Vector (LocalId, CoreType) -> [FormationPremiseSource]
    -> (Either (CountedCoreFailure FormationObservationError)
        ([FormationObservation], FormationSearchStatistics), Word)
countedFormationObservationsInScope allowance limits consumer currentTypes currentSupport sources =
    State.runState (Except.runExceptT action) allowance
  where
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    step :: (Word -> (Either (CountedCoreFailure Void) value, Word))
        -> Except.ExceptT (CountedCoreFailure FormationObservationError) (State.State Word) value
    step operation = do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either (Except.throwError . fmap absurd) pure result
    scopeFailure :: Text -> Except.ExceptT (CountedCoreFailure FormationObservationError) (State.State Word) value
    scopeFailure = Except.throwError . CountedCoreOperationFailed . FormationObservationScopeError
    require message = maybe (scopeFailure message) pure
    alignCore scoped = step (\work -> countedAlignScopedCore work currentTypes scoped)
        >>= require "a formation source is outside the current lexical scope"
    alignTerm occurrence = step (\work -> SourceTerm.countedAlignScopedSourceTermOccurrence work currentTypes occurrence)
        >>= require "a formation source term is outside the current lexical scope"
    alignParent support proposition = do
        for_ support \original -> do
            let difference = Vector.length currentSupport - Vector.length original
            when (difference < 0) (scopeFailure "a formation source is outside the current proof binder prefix")
            for_ (zip (toList original) (toList (Vector.drop difference currentSupport))) \((oldId, oldType), (newId, newType)) -> do
                charge
                unless (oldId == newId) (scopeFailure "a formation source is outside the current proof binder prefix")
                matches <- step (\work -> countedCoreTypeIdentity work oldType newType)
                unless matches (scopeFailure "a formation source is outside the current proof binder prefix")
            matches <- step (\work -> countedCoreTypeListIdentity work (scopedCoreContext proposition) (snd <$> toList original))
            unless matches (scopeFailure "a formation source proposition disagrees with its proof binder support")
        alignCore proposition
    project path proposition = do
        charge
        case (path, proposition) of
            (ConjunctionHere, _) -> pure proposition
            (ConjunctionLeft rest, CAnd left _) -> project rest left
            (ConjunctionRight rest, CAnd _ right) -> project rest right
            _ -> scopeFailure "a formation observation does not project its retained source"
    action = do
        (observations, _, budget) <- foldM source
            ([], 0, initialFormationSearchBudget limits) sources
        pure (reverse observations, formationSearchBudgetStatistics budget)
    source (observations, ordinal, budget) (FormationPremiseSource support proposition assertions origin) = do
        charge
        (result, next, finalBudget, _) <- foldM (\state view -> do
            charge
            case view of
                SourceEvidence.AtomicSource path atom -> observe support proposition origin state
                    (mapSourceNotionAssertionPath (appendConjunctionPath path) atom)
                SourceEvidence.UniversalSource{} -> pure state)
            (observations, ordinal, budget, Nothing) (SourceEvidence.sourceViews assertions)
        pure (result, next, finalBudget)
    observe support proposition origin (observations, ordinal, budget, cachedParent) assertion = do
        charge
        inspected <- either (Except.throwError . CountedCoreOperationFailed . FormationObservationExhausted) pure
            (consumeFormationSearchStatistics emptyFormationSearchStatistics
                {formationSearchSourceIndexInspections = 1} budget)
        if not (notionQueryAdmitsOrigin consumer origin)
            then pure (observations, ordinal + 1, inspected, cachedParent)
            else do
                parent <- maybe (alignParent support proposition) pure cachedParent
                aligned <- traverseSourceNotionAssertionParts alignTerm alignCore assertion
                projected <- project (sourceAssertionPath aligned) (scopedCoreTerm parent)
                matches <- step (\work -> countedCanonicalIdentity work projected (scopedCoreTerm (sourceAssertionFormula aligned)))
                unless matches (scopeFailure "a formation observation does not project its retained source")
                pure (FormationObservation parent aligned origin ordinal : observations, ordinal + 1, inspected, Just parent)

-- A nominal proof prefix distinguishes siblings even when all binders have
-- identical Core types. Provisional elaborator-owned sources instead rely on
-- their bracketed lexical lifetime; they carry no proof-prefix authorization.
alignFormationSource
    :: [CoreType] -> Vector (LocalId, CoreType)
    -> Maybe (Vector (LocalId, CoreType)) -> ScopedCheckedCore ObjectId
    -> Either Text (ScopedCheckedCore ObjectId)
alignFormationSource currentTypes currentSupport support proposition = do
    for_ support \sourceSupport -> do
        let current = toList currentSupport
            original = toList sourceSupport
            difference = length current - length original
        unless (difference >= 0 && drop difference current == original)
            (Left "a formation source is outside the current proof binder prefix")
        unless (scopedCoreContext proposition == (snd <$> original))
            (Left "a formation source proposition disagrees with its proof binder support")
    alignFormationCore currentTypes proposition

alignFormationCore :: [CoreType] -> ScopedCheckedCore ObjectId -> Either Text (ScopedCheckedCore ObjectId)
alignFormationCore currentTypes proposition = do
    let original = scopedCoreContext proposition
        difference = length currentTypes - length original
    unless (difference >= 0 && drop difference currentTypes == original)
        (Left "a formation source is outside the current lexical scope")
    pure (foldr weakenCheckedScopedCore proposition (take difference currentTypes))

alignFormationTerm :: [CoreType] -> ScopedSourceTerm -> Either Text ScopedSourceTerm
alignFormationTerm currentTypes = maybe
    (Left "a formation source term is outside the current lexical scope") Right
    . SourceTerm.alignScopedSourceTermOccurrence currentTypes

alignFormationAssertion :: [CoreType] -> ScopedSourceNotionOccurrence -> Either Text ScopedSourceNotionOccurrence
alignFormationAssertion currentTypes = traverseSourceNotionAssertionParts
    (alignFormationTerm currentTypes) (alignFormationCore currentTypes)

formationSourceAtoms
    :: [SourceEvidence.SourceView ScopedSourceNotionOccurrence] -> [ScopedSourceNotionOccurrence]
formationSourceAtoms views =
    [mapSourceNotionAssertionPath (appendConjunctionPath path) atom
    | SourceEvidence.AtomicSource path atom <- views]

formationEvidenceSource
    :: Vector (LocalId, CoreType)
    -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> Natural
    -> FormationProofLocalKind
    -> FormationPremiseSource
formationEvidenceSource support proposition evidence ordinal kind =
    FormationPremiseSource (Just support) proposition evidence
        (FormationFromProofLocal ordinal kind)

formationEqualitySource
    :: Vector (LocalId, CoreType)
    -> ScopedCheckedCore ObjectId
    -> NonEmpty ScopedSourceEqualityOccurrence
    -> Natural
    -> FormationProofLocalKind
    -> FormationEqualitySource
formationEqualitySource support proposition equalities ordinal kind =
    FormationEqualitySource
        (Just support)
        proposition
        equalities
        (FormationFromProofLocal ordinal kind)

checkedGuardFormationSource
    :: ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> FormationGuardKind
    -> FormationPremiseSource
checkedGuardFormationSource proposition assertions kind =
    FormationPremiseSource
        Nothing
        proposition
        assertions
        (guardOrigin kind (fromMaybe Nowhere (evidenceLocation assertions)))
  where
    evidenceLocation = \case
        SourceAtom assertion -> Just (sourceAssertionLocation assertion)
        SourceResidual origin -> SourceEvidence.writtenOriginLocation <$> origin
        SourceInputs origin _ -> SourceEvidence.writtenOriginLocation <$> origin
        SourceWithInputs _ body -> evidenceLocation body
        SourceAnd left right -> evidenceLocation left <|> evidenceLocation right
        SourceBind body -> evidenceLocation body
        SourceExists body -> evidenceLocation body
        SourceOr a b -> evidenceLocation a <|> evidenceLocation b
        SourceIff a b -> evidenceLocation a <|> evidenceLocation b
        SourceRequire premise body -> evidenceLocation premise <|> evidenceLocation body
    guardOrigin = \case
        kind'@FormationStructurePhraseCore -> FormationFromPhraseCore kind'
        kind'@FormationNounPhraseCore -> FormationFromPhraseCore kind'
        kind' -> FormationFromCheckedGuard kind'

definitionHeaderFormationSource
    :: Natural
    -> Maybe Natural
    -> Location
    -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> FormationPremiseSource
definitionHeaderFormationSource sourceOrdinal variableOrdinal location
        proposition assertions =
    FormationPremiseSource
        Nothing
        proposition
        assertions
        (FormationFromDefinitionHeader
            sourceOrdinal variableOrdinal location)

checkedGuardFormationEqualitySource
    :: ScopedCheckedCore ObjectId
    -> NonEmpty ScopedSourceEqualityOccurrence
    -> FormationGuardKind
    -> FormationEqualitySource
checkedGuardFormationEqualitySource proposition equalities kind =
    FormationEqualitySource
        Nothing
        proposition
        equalities
        (guardOrigin
            kind
            (sourceEqualityLocation (NonEmpty.head equalities)))
  where
    guardOrigin = \case
        kind'@FormationStructurePhraseCore -> FormationFromPhraseCore kind'
        kind'@FormationNounPhraseCore -> FormationFromPhraseCore kind'
        kind' -> FormationFromCheckedGuard kind'

definitionHeaderFormationEqualitySource
    :: Natural
    -> Maybe Natural
    -> Location
    -> ScopedCheckedCore ObjectId
    -> NonEmpty ScopedSourceEqualityOccurrence
    -> FormationEqualitySource
definitionHeaderFormationEqualitySource sourceOrdinal variableOrdinal location
        proposition equalities =
    FormationEqualitySource
        Nothing
        proposition
        equalities
        (FormationFromDefinitionHeader
            sourceOrdinal variableOrdinal location)

addFormationPremiseSource
    :: FormationPremiseSource
    -> ElaborationContext
    -> Either FormationObservationError ElaborationContext
addFormationPremiseSource source context = fst (runFormationScopePreparation (prepareFormationPremiseSource source context))

prepareFormationPremiseSource :: FormationPremiseSource -> ElaborationContext -> FormationScopePreparation ElaborationContext
prepareFormationPremiseSource source context@(ElaborationContext binders overrides scope) = do
    prepared <- extendFormationScope (binderTypes context)
        (elaborationContextSupport context) source scope
    pure (ElaborationContext binders overrides prepared)

addFormationEqualitySource
    :: FormationEqualitySource
    -> ElaborationContext
    -> Either FormationObservationError ElaborationContext
addFormationEqualitySource source context = fst (runFormationScopePreparation (prepareFormationEqualitySource source context))

prepareFormationEqualitySource :: FormationEqualitySource -> ElaborationContext -> FormationScopePreparation ElaborationContext
prepareFormationEqualitySource source context@(ElaborationContext binders overrides scope) = do
    prepared <- extendFormationEqualityScope (binderTypes context)
        (elaborationContextSupport context) source scope
    pure (ElaborationContext binders overrides prepared)

-- | Atomically retain one freshly generated local definition and eagerly
-- collapse a right-hand side which is itself an eligible whole-term alias.
-- The supplied context already contains the fresh binder at index zero; the
-- right-hand occurrence still lives in the preceding outer context.
extendElaborationContextWithFormationAlias
    :: LocalId -> ScopedSourceTerm -> ScopedCheckedCore ObjectId -> Natural -> Location
    -> ElaborationContext -> Either Text (Maybe ElaborationContext)
extendElaborationContextWithFormationAlias identity body equality ordinal location context = do
    source <- checkedFormationAliasSource identity body equality ordinal location context
    traverse (`insertFormationAliasSource` context) source

extendElaborationContextWithFormationAliasLowering
    :: LocalId -> ScopedSourceTerm -> ScopedCheckedCore ObjectId -> Natural -> Location
    -> ElaborationContext -> Declaration.LoweringDriver (Either Text (Maybe ElaborationContext))
extendElaborationContextWithFormationAliasLowering identity body equality ordinal location context =
    case checkedFormationAliasSource identity body equality ordinal location context of
        Left failure -> pure (Left failure)
        Right Nothing -> pure (Right Nothing)
        Right (Just source) -> fmap (first (Text.pack . show) . fmap Just)
            (finishFormationScopePreparation (prepareFormationAliasContext source context))

checkedFormationAliasSource
    :: LocalId -> ScopedSourceTerm -> ScopedCheckedCore ObjectId -> Natural -> Location
    -> ElaborationContext -> Either Text (Maybe FormationAliasSource)
checkedFormationAliasSource identity body equality ordinal location context = do
    prepared <- prepareFormationAliasSource identity body equality ordinal location context
    for_ prepared \source -> do
        traverse_ requireOlder (contextFormationAliases context)
        validateFormationAliasSource source
    pure prepared
  where
    requireOlder existing = do
        existingOrdinal <- formationAliasSourceOwnOrdinal existing
        unless (ordinal > existingOrdinal)
            (Left
                "a local alias definition ordinal is not newer than every active alias")

prepareFormationAliasSource
    :: LocalId
    -> ScopedSourceTerm
    -> ScopedCheckedCore ObjectId
    -> Natural
    -> Location
    -> ElaborationContext
    -> Either Text (Maybe FormationAliasSource)
prepareFormationAliasSource identity body equality ordinal location context = do
    (binderType, outerBinders) <-
        case context of
            ElaborationContext
                    (ElaborationBinder actual _variable coreType _structure : rest)
                    _overrides _scope
                | actual == identity -> Right (coreType, rest)
            _ -> Left "a local alias is not the nearest context binder"
    unless (binderType == TySet && SourceTerm.sourceTermOccurrenceType body == TySet)
        (Left "a notion alias must denote a set")
    let outerSupport = supportOf outerBinders
        newSupport = elaborationContextSupport context
        aliases = contextFormationAliases context
        bodyRoot = scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore body)
        previous = do
            index <- case bodyRoot of
                CBound candidate -> Just candidate
                _ -> Nothing
            ElaborationBinder previousIdentity _variable _type _structure <-
                nth index outerBinders
            find (hasIdentity previousIdentity) aliases
    (rootInOuter, chainInOuter) <-
        case previous of
            Nothing -> pure (body, [])
            Just (FormationAliasSource
                    _previousIdentity previousSupport root chain
                    _previousLocation) -> do
                root' <- alignSourceTerm outerSupport previousSupport root
                chain' <- traverse
                    (alignHypothesis outerSupport previousSupport)
                    (toList chain)
                pure (root', chain')
    let weakenSource = SourceTerm.weakenScopedSourceTermOccurrence binderType
        root = weakenSource rootInOuter
        priorChain = weakenHypothesis binderType <$> chainInOuter
        ownHypothesis =
            materializedNotionHypothesis
                equality
                (FormationFromProofLocal
                    ordinal FormationProofLocalDefinition)
    let expectedEquality =
            scopedCoreContext equality
                == (snd <$> toList newSupport)
            && scopedCoreTerm equality
                == CEq TySet
                    (CBound 0)
                    (scopedCoreTerm
                        (SourceTerm.sourceTermOccurrenceCore
                            (weakenSource body)))
    if not expectedEquality
    then pure Nothing
    else do
        pure
            (Just
                (FormationAliasSource
                    identity newSupport root
                    (appendOwnHypothesis priorChain ownHypothesis)
                    location))
  where
    hasIdentity expected
            (FormationAliasSource actual _support _root _chain
                _location) =
        actual == expected

    supportOf binders = Vector.fromList
        [ (localIdentity, coreType)
        | ElaborationBinder localIdentity _variable coreType _structure <- binders
        ]

    alignSourceTerm current source root = do
        let currentList = toList current
            sourceList = toList source
            difference = length currentList - length sourceList
        unless
            ( difference >= 0
              && drop difference currentList == sourceList
            )
            (Left "a local alias escaped its binder prefix")
        maybe
            (Left "a local alias source term escaped its checked scope")
            Right
            (SourceTerm.alignScopedSourceTermOccurrence
                (snd <$> currentList)
                root)

    alignHypothesis current source hypothesis =
        materializedNotionHypothesis
            <$> alignScopedCore current source
                (materializedNotionHypothesisProposition hypothesis)
            <*> pure (materializedNotionHypothesisOrigin hypothesis)

    weakenHypothesis binderType' hypothesis =
        materializedNotionHypothesis
            (weakenCheckedScopedCore binderType'
                (materializedNotionHypothesisProposition hypothesis))
            (materializedNotionHypothesisOrigin hypothesis)

    alignScopedCore current source scoped = do
        let currentList = toList current
            sourceList = toList source
            difference = length currentList - length sourceList
        unless
            ( difference >= 0
              && drop difference currentList == sourceList
              && scopedCoreContext scoped == (snd <$> sourceList)
            )
            (Left "a local alias escaped its binder prefix")
        pure
            (foldr weakenCheckedScopedCore scoped
                (snd <$> take difference currentList))

    appendOwnHypothesis [] own = own :| []
    appendOwnHypothesis (firstHypothesis : remaining) own =
        firstHypothesis :| (remaining <> [own])

insertFormationAliasSource
    :: FormationAliasSource -> ElaborationContext -> Either Text ElaborationContext
insertFormationAliasSource source context = first (Text.pack . show)
    (fst (runFormationScopePreparation (prepareFormationAliasContext source context)))

prepareFormationAliasContext
    :: FormationAliasSource -> ElaborationContext -> FormationScopePreparation ElaborationContext
prepareFormationAliasContext source context@(ElaborationContext binders overrides scope) = do
    scopePreparationCount FormationDiagnostics.ScopeInsertion 1
    prepared <- prepareScopeAlias (binderTypes context) (elaborationContextSupport context)
        (formationScopeAliases scope) source (formationScopeEvidence scope)
    pure (ElaborationContext binders overrides scope
        { formationScopeAliases = source : formationScopeAliases scope
        , formationScopeEvidence = prepared
        })

formationAliasSourceOwnHypothesis
    :: FormationAliasSource
    -> MaterializedNotionHypothesis FormationSourceOrigin
formationAliasSourceOwnHypothesis
        (FormationAliasSource _identity _support _root chain _location) =
    NonEmpty.last chain

formationAliasSourceOwnOrdinal
    :: FormationAliasSource
    -> Either Text Natural
formationAliasSourceOwnOrdinal source =
    case materializedNotionHypothesisOrigin
            (formationAliasSourceOwnHypothesis source) of
        FormationFromProofLocal ordinal FormationProofLocalDefinition ->
            Right ordinal
        _ ->
            Left "a local alias own equality has invalid proof-local provenance"

validateFormationAliasSource
    :: FormationAliasSource
    -> Either Text ()
validateFormationAliasSource
        source@(FormationAliasSource
            _identity support root chain _location) = do
    let expectedContext = snd <$> toList support
        rootCore = SourceTerm.sourceTermOccurrenceCore root
    unless
        ( scopedCoreContext rootCore == expectedContext
          && scopedCoreType rootCore == TySet
        )
        (Left "a local alias root has invalid checked scope or type")
    edges <- traverse checkedDefinitionEdge (toList chain)
    case edges of
        [] -> impossible "a nonempty local alias chain became empty"
        firstEdge : remainingEdges -> do
            unless
                (snd firstEdge == scopedCoreTerm rootCore)
                (Left "a local alias chain does not end at its retained root")
            unless
                (and
                    [ olderLeft == newerRight
                    | ((olderLeft, _olderRight), (_newerLeft, newerRight)) <-
                        zip edges remainingEdges
                    ])
                (Left "adjacent local alias equality endpoints do not join")
    void (formationAliasSourceOwnOrdinal source)
  where
    checkedDefinitionEdge hypothesis = do
        unless
            (scopedCoreContext proposition == (snd <$> toList support))
            (Left "a local alias equality has escaped its checked scope")
        case (scopedCoreType proposition, scopedCoreTerm proposition, origin) of
            ( TyProp
              , CEq TySet left right
              , FormationFromProofLocal _ordinal FormationProofLocalDefinition
              ) ->
                Right (left, right)
            _ ->
                Left "a local alias chain contains a non-definition equality"
      where
        proposition = materializedNotionHypothesisProposition hypothesis
        origin = materializedNotionHypothesisOrigin hypothesis

alignFormationAliases
    :: ElaborationContext
    -> AlignedFormationAliases
alignFormationAliases context =
    either
        (impossible . Text.unpack)
        id
        (alignFormationAliasSources
            (binderTypes context)
            (elaborationContextSupport context)
            (contextFormationAliases context))

-- Retain only aliases whose complete definition chain is eligible for this
-- consumer. Source normalization cannot turn a proof-local definition into a
-- declaration-header observation.
formationAliasesFor :: NotionQueryConsumer -> AlignedFormationAliases -> AlignedFormationAliases
formationAliasesFor consumer (AlignedFormationAliases aliases) = AlignedFormationAliases
    [alias | alias@(AlignedFormationAlias _ _ chain _) <- aliases
    , all (notionQueryAdmitsOrigin consumer . materializedNotionHypothesisOrigin) chain]

-- | Align compiler-owned alias sources and filter their complete definition
-- chains under a single structural allowance. Alignment still validates every
-- source before consumer filtering, as the ordinary composed operations do.
countedFormationAliasesFor
    :: Word -> NotionQueryConsumer -> ElaborationContext
    -> (Either (CountedCoreFailure Text) AlignedFormationAliases, Word)
countedFormationAliasesFor allowance consumer context =
    countedFormationAliasSources allowance consumer (binderTypes context)
        (elaborationContextSupport context) (contextFormationAliases context)

countedFormationAliasSources
    :: Word -> NotionQueryConsumer -> [CoreType] -> Vector (LocalId, CoreType)
    -> [FormationAliasSource]
    -> (Either (CountedCoreFailure Text) AlignedFormationAliases, Word)
countedFormationAliasSources allowance consumer currentTypes currentSupport sources =
    State.runState (Except.runExceptT action) allowance
  where
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    step :: (Word -> (Either (CountedCoreFailure Void) value, Word))
        -> Except.ExceptT (CountedCoreFailure Text) (State.State Word) value
    step operation = do
        remaining <- State.get
        let (result, after) = operation remaining
        State.put after
        either (Except.throwError . fmap absurd) pure result
    failed :: Text -> Except.ExceptT (CountedCoreFailure Text) (State.State Word) value
    failed = Except.throwError . CountedCoreOperationFailed
    failure location detail = failed (locationToText location <> ": " <> detail)
    action = do
        lexicalSize <- foldM (\size _ -> charge >> pure (size + 1 :: Int)) 0 currentTypes
        let difference = lexicalSize - Vector.length currentSupport
            atFirst detail = case sources of
                FormationAliasSource _ _ _ _ location : _ -> locationToText location <> ": " <> detail
                [] -> detail
        when (difference < 0) (failed (atFirst "the current alias support is not a lexical-context suffix"))
        suffix <- dropPrefix difference currentTypes
        matches <- step (\work -> countedCoreTypeListIdentity work suffix (snd <$> toList currentSupport))
        unless matches (failed (atFirst "the current alias support is not a lexical-context suffix"))
        aligned <- traverse align sources
        retained <- filterM eligible aligned
        pure (AlignedFormationAliases retained)
    dropPrefix 0 rest = pure rest
    dropPrefix count (_ : rest) = charge >> dropPrefix (count - 1) rest
    dropPrefix _ [] = impossible "a measured alias context prefix exceeds its list"
    align (FormationAliasSource identity support root chain location) = do
        charge
        targetAtSource <- case Vector.uncons support of
            Just ((actual, TySet), outer) | actual == identity -> pure (scopedBound (snd <$> toList outer) TySet)
            _ -> failure location "a local alias identity is not its nearest set binder"
        let difference = Vector.length currentSupport - Vector.length support
        when (difference < 0) (failure location "a local alias escaped its proof-prefix support")
        for_ (zip (toList support) (toList (Vector.drop difference currentSupport))) \((oldId, oldType), (newId, newType)) -> do
            charge
            unless (oldId == newId) (failure location "a local alias escaped its proof-prefix support")
            matches <- step (\work -> countedCoreTypeIdentity work oldType newType)
            unless matches (failure location "a local alias escaped its proof-prefix support")
        target <- alignCore location targetAtSource
        root' <- step (\work -> SourceTerm.countedAlignScopedSourceTermOccurrence work currentTypes root)
            >>= maybe (failure location "a local alias source term escaped its checked scope") pure
        chain' <- for chain \hypothesis -> do
            charge
            proposition <- alignCore location (materializedNotionHypothesisProposition hypothesis)
            pure (materializedNotionHypothesis proposition (materializedNotionHypothesisOrigin hypothesis))
        pure (AlignedFormationAlias target root' chain' location)
    alignCore location scoped = step (\work -> countedAlignScopedCore work currentTypes scoped)
        >>= maybe (failure location "a local alias equality escaped its checked scope") pure
    eligible (AlignedFormationAlias _ _ chain _) =
        foldM (\accepted definition -> do
            charge
            pure (accepted && notionQueryAdmitsOrigin consumer (materializedNotionHypothesisOrigin definition))) True chain

-- Both endpoints contribute to the fixed support independently of which alias
-- a later lookup happens to use. Roots retain their original source sidecars;
-- alias binders are opaque terms, never inferred provider applications.
formationAliasTerms :: AlignedFormationAliases -> [ScopedSourceTerm]
formationAliasTerms (AlignedFormationAliases aliases) = concat
    [[SourceTerm.sourceTermOccurrence target TySet (LocatedSourceTerm location), root]
    | AlignedFormationAlias target root _ location <- aliases]

formationAliasDefinitions
    :: AlignedFormationAliases -> [MaterializedNotionHypothesis FormationSourceOrigin]
formationAliasDefinitions (AlignedFormationAliases aliases) =
    reverse [NonEmpty.last chain | AlignedFormationAlias _ _ chain _ <- aliases]

alignFormationAliasSources
    :: [CoreType]
    -> Vector (LocalId, CoreType)
    -> [FormationAliasSource]
    -> Either Text AlignedFormationAliases
alignFormationAliasSources currentTypes currentSupport sources = do
    let supportTypes = snd <$> toList currentSupport
        lexicalDifference = length currentTypes - length supportTypes
    unless
        ( lexicalDifference >= 0
          && drop lexicalDifference currentTypes == supportTypes
        )
        (Left
            (atFirstSource
                "the current alias support is not a lexical-context suffix"))
    AlignedFormationAliases <$> traverse alignSource sources
  where
    alignSource
            (FormationAliasSource identity support root chain location) = do
        let sourceSupport = toList support
        targetAtSource <-
            case sourceSupport of
                (actual, TySet) : outer
                    | actual == identity ->
                        Right (scopedBound (snd <$> outer) TySet)
                _ ->
                    failure location
                        "a local alias identity is not its nearest set binder"
        target <- alignChecked location support targetAtSource
        root' <- alignSourceTerm location support root
        chain' <- traverse
            (alignHypothesis location support)
            chain
        pure (AlignedFormationAlias target root' chain' location)

    alignSourceTerm location support root = do
        _ <- validateSupport location support
        maybe
            (failure location
                "a local alias source term escaped its checked scope")
            Right
            (SourceTerm.alignScopedSourceTermOccurrence currentTypes root)

    alignHypothesis location support hypothesis =
        materializedNotionHypothesis
            <$> alignChecked location support
                (materializedNotionHypothesisProposition hypothesis)
            <*> pure (materializedNotionHypothesisOrigin hypothesis)

    alignChecked location support scoped = do
        _ <- validateSupport location support
        let sourceTypes = scopedCoreContext scoped
            difference = length currentTypes - length sourceTypes
        unless
            ( difference >= 0
              && drop difference currentTypes == sourceTypes
            )
            (failure location
                "a local alias equality escaped its checked scope")
        pure
            (foldr weakenCheckedScopedCore scoped
                (take difference currentTypes))

    validateSupport location support = do
        let sourceSupport = toList support
            current = toList currentSupport
            difference = length current - length sourceSupport
        unless
            ( difference >= 0
              && drop difference current == sourceSupport
            )
            (failure location
                "a local alias escaped its proof-prefix support")
        pure ()

    failure location detail =
        Left (locationToText location <> ": " <> detail)

    atFirstSource detail =
        case sources of
            FormationAliasSource _ _ _ _ location : _ ->
                locationToText location <> ": " <> detail
            [] -> detail

-- | View source terms through compiler-owned definitions in decreasing
-- definition order. The substitution keeps written provider identities and
-- supplies the original checked sidecar when an opaque alias is replaced.
-- Dependencies include aliases in erased source arguments, even if no change
-- to the enclosing Core proposition would be visible to logical transport.
viewFormationAliases
    :: AlignedFormationAliases
    -> ScopedSourceTerm
    -> Either FormationAliasNormalizationError
        (ScopedSourceTerm, [MaterializedNotionHypothesis FormationSourceOrigin])
viewFormationAliases (AlignedFormationAliases aliases) original = do
    (result, definitions) <- foldM replaceOne (original, Map.empty) aliases
    pure (result, Map.elems definitions)
  where
    replaceOne (current, used) (AlignedFormationAlias target root chain location) = do
        let ordinal = definitionOrdinal (NonEmpty.last chain)
        replaced <- first (FormationAliasReplacementInvariantFailed location ordinal)
            (SourceTerm.replaceScopedSourceTermOccurrence target root current)
        pure case replaced of
            Nothing -> (current, used)
            Just result -> (result, foldl' (\retained definition ->
                Map.insert (definitionOrdinal definition) definition retained) used chain)
    definitionOrdinal definition = case materializedNotionHypothesisOrigin definition of
        FormationFromProofLocal ordinal FormationProofLocalDefinition -> ordinal
        _ -> impossible "an aligned alias lost its compiler-owned definition origin"

-- A physical occurrence index, not formation evidence. Binder-local variables
-- are excluded; indices refer to the enclosing checked lexical context.
countedCanonicalFreeBounds
    :: Word -> CanonicalTerm global
    -> (Either (CountedCoreFailure Void) (Set Natural), Word)
countedCanonicalFreeBounds allowance term =
    State.runState (Except.runExceptT (walk 0 Set.empty term)) allowance
  where
    charge :: Natural -> ExceptT (CountedCoreFailure Void) (State.State Word) ()
    charge amount = do
        remaining <- State.get
        if amount <= fromIntegral remaining
            then State.put (remaining - fromIntegral amount)
            else State.put 0 >> Except.throwError CountedCoreStructuralWorkExhausted
    walk depth known value = do
        charge 1
        let unary = walk depth known
            binary left right = walk depth known left >>= \next -> walk depth next right
        case value of
            CBound index | index >= depth -> do
                charge (FormationTerms.indexWork (Set.size known) 1)
                pure (Set.insert (index - depth) known)
            CApp left right -> binary left right
            CNot child -> unary child
            CAnd left right -> binary left right
            COr left right -> binary left right
            CImp left right -> binary left right
            CEq _ left right -> binary left right
            CLam _ child -> walk (depth + 1) known child
            CForall _ child -> walk (depth + 1) known child
            CExists _ child -> walk (depth + 1) known child
            CBound{} -> pure known
            CGlobal{} -> pure known
            CIntrinsic{} -> pure known
            CLogicalSelect{} -> pure known
            COpaqueInteger{} -> pure known
            CTruth -> pure known
            CFalsum -> pure known

-- Aligned aliases share a checked context. Validate each input source node
-- once, including nodes whose variables exclude every replacement target.
countedAliasInputContext
    :: Word -> AlignedFormationAliases -> ScopedCheckedCore ObjectId
    -> (Either (CountedCoreFailure FormationAliasNormalizationError) (), Word)
countedAliasInputContext allowance (AlignedFormationAliases []) _ = (Right (), allowance)
countedAliasInputContext allowance (AlignedFormationAliases (AlignedFormationAlias target _ chain location : _)) original =
    case countedCoreTypeListIdentity allowance (scopedCoreContext target) (scopedCoreContext original) of
        (Left failure, remaining) -> (Left (absurd <$> failure), remaining)
        (Right True, remaining) -> (Right (), remaining)
        (Right False, remaining) ->
            let origin = materializedNotionHypothesisOrigin (NonEmpty.last chain)
                ordinal = case origin of
                    FormationFromProofLocal index FormationProofLocalDefinition -> index
                    _ -> impossible "an aligned alias lost its compiler-owned origin"
            in (Left (CountedCoreOperationFailed (FormationAliasReplacementInvariantFailed location ordinal
                    ScopedOccurrenceReplacementContextMismatch)), remaining)

countedViewFormationAliases
    :: Word -> AlignedFormationAliases -> ScopedSourceTerm
    -> (Either (CountedCoreFailure FormationAliasNormalizationError)
        (ScopedSourceTerm, [MaterializedNotionHypothesis FormationSourceOrigin]), Word)
countedViewFormationAliases allowance (AlignedFormationAliases []) original = (Right (original, []), allowance)
countedViewFormationAliases allowance aligned@(AlignedFormationAliases aliases) original =
    State.runState (Except.runExceptT action) allowance
  where
    action = do
        bounds <- sourceBounds original
        (result, definitions, _) <- foldM replaceOne (original, Map.empty, bounds) aliases
        pure (result, Map.elems definitions)
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    sourceBounds occurrence = do
        before <- State.get
        let (valid, afterContext) = countedAliasInputContext before aligned (SourceTerm.sourceTermOccurrenceCore occurrence)
        State.put afterContext
        either Except.throwError pure valid
        available <- State.get
        let (result, after) = countedCanonicalFreeBounds available
                (scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore occurrence))
        State.put after
        own <- either (Except.throwError . fmap absurd) pure result
        let children = case SourceTerm.sourceTermOccurrenceProvider occurrence of
                Just provider -> toList (SourceTerm.sourceTermProviderArguments provider)
                Nothing -> maybe [] (\(left,right) -> [left,right])
                    (SourceTerm.sourceTermOccurrenceOrderedPair occurrence)
        foldM (\known child -> do
            nested <- sourceBounds child
            foldM (\entries index -> do
                let amount = FormationTerms.indexWork (Set.size entries) 1
                replicateM_ (fromIntegral amount) charge
                pure (Set.insert index entries)) known (Set.toAscList nested)) own children
    replaceOne state@(current, used, bounds) alias@(AlignedFormationAlias target _ _ _) = do
        let amount = FormationTerms.indexWork (Set.size bounds) 1
        replicateM_ (fromIntegral amount) charge
        case scopedCoreTerm target of
            CBound index | Set.notMember index bounds -> pure state
            _ -> replacePresent current used bounds alias
    replacePresent current used bounds (AlignedFormationAlias target root chain location) = do
        charge
        definition <- foldM (\_ next -> charge >> pure next) (NonEmpty.head chain) (NonEmpty.tail chain)
        available <- State.get
        let ordinal = definitionOrdinal definition
            (result, after) = SourceTerm.countedReplaceScopedSourceTermOccurrence available target root current
        State.put after
        replaced <- either
            (Except.throwError . fmap (FormationAliasReplacementInvariantFailed location ordinal)) pure result
        case replaced of
            Nothing -> pure (current, used, bounds)
            Just viewed -> do
                retained <- foldM (\entries item -> charge >> pure (Map.insert (definitionOrdinal item) item entries)) used chain
                next <- sourceBounds viewed
                pure (viewed, retained, next)
    definitionOrdinal definition = case materializedNotionHypothesisOrigin definition of
        FormationFromProofLocal ordinal FormationProofLocalDefinition -> ordinal
        _ -> impossible "an aligned alias lost its compiler-owned definition origin"

normalizeFormationAliases
    :: AlignedFormationAliases
    -> ScopedCheckedCore ObjectId
    -> Either FormationAliasNormalizationError FormationAliasNormalization
normalizeFormationAliases aligned@(AlignedFormationAliases aliases) original = do
    (result, reversedSteps) <- foldM replaceOne (original, []) aliases
    pure (FormationAliasNormalization original result (reverse reversedSteps))
  where
    replaceOne (current, steps) alias = do
        let (definition, location, ordinal, target, replacement) =
                alignedFormationAliasDefinition aligned alias
        replaced <-
            first
                (FormationAliasReplacementInvariantFailed location ordinal)
                (replaceScopedCoreOccurrence
                    target replacement current)
        case replaced of
            Nothing -> pure (current, steps)
            Just checked ->
                pure
                    ( scopedCoreReplacementResult checked
                    , FormationAliasReplayStep
                        definition location ordinal
                        (scopedCoreReplacementAbstraction checked)
                        : steps
                    )

-- Count replacement lookup as well as Core traversal. Like counted Core
-- operations, return the remaining allowance on both success and exhaustion.
countedNormalizeFormationAliases
    :: Word -> AlignedFormationAliases -> ScopedCheckedCore ObjectId
    -> (Either (CountedCoreFailure FormationAliasNormalizationError) FormationAliasNormalization, Word)
countedNormalizeFormationAliases allowance (AlignedFormationAliases []) original =
    (Right (FormationAliasNormalization original original []), allowance)
countedNormalizeFormationAliases allowance aligned@(AlignedFormationAliases aliases) original =
    State.runState (Except.runExceptT action) allowance
  where
    action = do
        bounds <- freeBounds original
        (result, reversed, _) <- foldM replaceOne (original, [], bounds) aliases
        pure (FormationAliasNormalization original result (reverse reversed))
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    step :: (Word -> (Either (CountedCoreFailure FormationAliasNormalizationError) value, Word))
        -> ExceptT (CountedCoreFailure FormationAliasNormalizationError) (State.State Word) value
    step operation = do
        available <- State.get
        let (result, after) = operation available
        State.put after
        either Except.throwError pure result
    identical left right = step (\available ->
        first (first (fmap absurd)) (countedCanonicalIdentity available left right))
    freeBounds scoped = do
        step (\available -> countedAliasInputContext available aligned scoped)
        step (\available -> first (first (fmap absurd))
            (countedCanonicalFreeBounds available (scopedCoreTerm scoped)))
    replaceOne state@(current, steps, bounds) alias@(AlignedFormationAlias target _ _ _) = do
        replicateM_ (fromIntegral (FormationTerms.indexWork (Set.size bounds) 1)) charge
        case scopedCoreTerm target of
            CBound index | Set.notMember index bounds -> pure state
            _ -> replacePresent current steps bounds alias
    replacePresent current steps bounds (AlignedFormationAlias target root chain location) = do
        charge
        definition <- foldM (\_ next -> charge >> pure next) (NonEmpty.head chain) (NonEmpty.tail chain)
        let proposition = materializedNotionHypothesisProposition definition
            origin = materializedNotionHypothesisOrigin definition
        (ordinal, expected) <- case (scopedCoreTerm proposition, origin) of
            (CEq TySet left right, FormationFromProofLocal ordinal FormationProofLocalDefinition) -> do
                same <- identical left (scopedCoreTerm target)
                unless same (impossible "an aligned alias lost its definition target")
                pure (ordinal, right)
            _ -> impossible "an aligned alias lost its compiler-owned definition"
        replacement <- findReplacement expected
            (SourceTerm.sourceTermOccurrenceCore root : [candidate | AlignedFormationAlias candidate _ _ _ <- aliases])
        replaced <- step (\available -> first
            (first (fmap (FormationAliasReplacementInvariantFailed location ordinal)))
            (countedReplaceScopedCoreOccurrence available target replacement current))
        case replaced of
            Nothing -> pure (current, steps, bounds)
            Just checked -> do
                let result = scopedCoreReplacementResult checked
                next <- freeBounds result
                pure (result, FormationAliasReplayStep definition location ordinal
                    (scopedCoreReplacementAbstraction checked) : steps, next)
    findReplacement _ [] = impossible "an aligned alias lost its checked replacement"
    findReplacement expected (candidate : remaining) = do
        charge
        same <- identical expected (scopedCoreTerm candidate)
        if same then pure candidate else findReplacement expected remaining

alignedFormationAliasDefinition
    :: AlignedFormationAliases
    -> AlignedFormationAlias
    -> ( MaterializedNotionHypothesis FormationSourceOrigin
       , Location
       , Natural
       , ScopedCheckedCore ObjectId
       , ScopedCheckedCore ObjectId
       )
alignedFormationAliasDefinition
        (AlignedFormationAliases aliases)
        (AlignedFormationAlias target root chain location) =
    case (scopedCoreTerm proposition, origin) of
        ( CEq TySet left right
          , FormationFromProofLocal ordinal FormationProofLocalDefinition
          )
            | left == scopedCoreTerm target ->
                (definition, location, ordinal, target, replacement right)
        _ ->
            impossible "an aligned local alias lost its own definition equality"
  where
    definition = NonEmpty.last chain
    proposition = materializedNotionHypothesisProposition definition
    origin = materializedNotionHypothesisOrigin definition

    replacement expected =
        fromMaybe
            (impossible
                "an aligned local alias definition lost its checked right-hand side")
            (find ((== expected) . scopedCoreTerm) candidates)

    candidates =
        SourceTerm.sourceTermOccurrenceCore root
            : [ candidate
              | AlignedFormationAlias candidate _root _chain _location <- aliases
              ]

formationAliasNormalizationOriginal
    :: FormationAliasNormalization
    -> ScopedCheckedCore ObjectId
formationAliasNormalizationOriginal
        (FormationAliasNormalization original _result _steps) =
    original

formationAliasNormalizationResult
    :: FormationAliasNormalization
    -> ScopedCheckedCore ObjectId
formationAliasNormalizationResult
        (FormationAliasNormalization _original result _steps) =
    result

formationAliasNormalizationReplaySteps
    :: FormationAliasNormalization
    -> [FormationAliasReplayStep]
formationAliasNormalizationReplaySteps
        (FormationAliasNormalization _original _result steps) =
    steps

formationAliasReplayStepDefinition
    :: FormationAliasReplayStep
    -> MaterializedNotionHypothesis FormationSourceOrigin
formationAliasReplayStepDefinition
        (FormationAliasReplayStep definition _location _ordinal _predicate) =
    definition

formationAliasReplayStepLocation
    :: FormationAliasReplayStep
    -> Location
formationAliasReplayStepLocation
        (FormationAliasReplayStep _definition location _ordinal _predicate) =
    location

formationAliasReplayStepOrdinal
    :: FormationAliasReplayStep
    -> Natural
formationAliasReplayStepOrdinal
        (FormationAliasReplayStep _definition _location ordinal _predicate) =
    ordinal

formationAliasReplayStepAbstraction
    :: FormationAliasReplayStep
    -> ScopedCheckedCore ObjectId
formationAliasReplayStepAbstraction
        (FormationAliasReplayStep _definition _location _ordinal predicate) =
    predicate

emptyElaborationContext :: ElaborationContext
emptyElaborationContext = ElaborationContext [] Map.empty emptyFormationScope

extendElaborationContext
    :: NonEmpty (LocalId, Raw.VarSymbol)
    -> ElaborationContext
    -> Either ElaborationError ElaborationContext
extendElaborationContext additions =
    extendTypedElaborationContext
        ((\(identity, variable) -> (identity, variable, TySet))
            <$> additions)

extendTypedElaborationContext
    :: NonEmpty (LocalId, Raw.VarSymbol, CoreType)
    -> ElaborationContext
    -> Either ElaborationError ElaborationContext
extendTypedElaborationContext additions
        (ElaborationContext initial overrides scope) = do
    binders <- foldM add initial (toList additions)
    pure (ElaborationContext binders overrides scope)
  where
    add binders (identity, variable, coreType)
        | any (sameVariable variable) binders =
            Left (ElaborationDuplicateLocalBinder (locate variable) variable)
        | any (sameIdentity identity) binders =
            Left (ElaborationDuplicateLocalIdentity (locate variable) identity)
        | otherwise =
            Right
                (ElaborationBinder
                    identity
                    (Just variable)
                    coreType
                    Nothing
                    : (weakenBinderAnnotation 1 <$> binders))

    sameVariable variable (ElaborationBinder _identity existing _coreType _structure) =
        existing == Just variable

    sameIdentity identity (ElaborationBinder existing _variable _coreType _structure) =
        existing == identity

    weakenBinderAnnotation amount
            (ElaborationBinder identity variable coreType annotation) =
        ElaborationBinder identity variable coreType
            (weakenStructureAnnotation amount <$> annotation)

weakenStructureAnnotation
    :: Natural
    -> ResolvedStructureApplication
    -> ResolvedStructureApplication
weakenStructureAnnotation amount
        (ResolvedStructureApplication phrase fields arguments) =
    ResolvedStructureApplication phrase fields
        (SourceTerm.shiftCanonicalSourceTermOccurrence amount 0 <$> arguments)

-- | Add one proof-owned binder which deliberately has no source-resolvable
-- spelling.  This is used for a nameless singular witness; it participates in
-- checked support and de Bruijn weakening but cannot shadow or be looked up by
-- a later source variable.
extendAnonymousElaborationContext
    :: LocalId
    -> ElaborationContext
    -> Either ElaborationError ElaborationContext
extendAnonymousElaborationContext = extendTypedAnonymousElaborationContext TySet

-- | A proof-owned binder of any Core type, with no source-resolvable spelling.
extendTypedAnonymousElaborationContext
    :: CoreType -> LocalId -> ElaborationContext
    -> Either ElaborationError ElaborationContext
extendTypedAnonymousElaborationContext binderType identity
        (ElaborationContext binders overrides scope)
    | any sameIdentity binders =
        Left (ElaborationDuplicateLocalIdentity Nowhere identity)
    | otherwise =
        Right
            (ElaborationContext
                ( ElaborationBinder identity Nothing binderType Nothing
                    : (weakenAnonymousAnnotation <$> binders)
                )
                overrides
                scope)
  where
    sameIdentity (ElaborationBinder existing _variable _coreType _structure) =
        existing == identity

    weakenAnonymousAnnotation
            (ElaborationBinder existing variable coreType annotation) =
        ElaborationBinder existing variable coreType
            (weakenStructureAnnotation 1 <$> annotation)

datatypeElaborationEnvironment
    :: CheckedObjectClosure
    -> NonEmpty
        ( Location
        , Raw.FunctionSymbol
        , AssertedObject
        )
    -> [Raw.VarSymbol]
    -> Either ElaborationError DatatypeElaborationEnvironment
datatypeElaborationEnvironment closure additions parameters = do
    definitions <- foldM add Map.empty (toList additions)
    let emptyContext = ElaborationContext [] definitions emptyFormationScope
    context <- case NonEmpty.nonEmpty (zip (localId <$> [0 ..]) parameters) of
        Nothing -> pure emptyContext
        Just binders -> extendElaborationContext binders emptyContext
    pure (DatatypeElaborationEnvironment closure context)
  where
    add definitions (location, symbol, asserted)
        | lookupCheckedObjectContent identity closure /= Just content =
            Left
                (ElaborationProspectiveObjectMissing
                    location identity)
        | semanticGlobalKeyType key /= Just actualType =
            Left
                (ElaborationObjectTypeMismatch
                    location expectedType actualType)
        | Map.member key definitions =
            Left (ElaborationGlobalAlreadyVisible location key)
        | otherwise =
            Right
                (Map.insert
                    key
                    (LocalObjectReference asserted)
                    definitions)
      where
        key = SemanticExpressionFunction (Raw.mixfixPattern symbol)
        expectedType = fromMaybe
            (impossible "a datatype constructor has no semantic type")
            (semanticGlobalKeyType key)
        identity = assertedObjectId asserted
        content = assertedObjectContent asserted
        actualType = objectContentType content

elaborationContextSupport
    :: ElaborationContext
    -> Vector (LocalId, CoreType)
elaborationContextSupport
        (ElaborationContext binders _overrides _scope) =
    Vector.fromList
        [ (identity, coreType)
        | ElaborationBinder identity _variable coreType _structure <- binders
        ]

elaborationContextIndex
    :: Raw.VarSymbol
    -> ElaborationContext
    -> Maybe Natural
elaborationContextIndex variable
        (ElaborationContext binders _overrides _scope) =
    go 0 binders
  where
    go _index [] =
        Nothing
    go index (ElaborationBinder _identity candidate _coreType _structure : rest)
        | candidate == Just variable = Just index
        | otherwise = go (index + 1) rest

-- Keep the checked binder support, but hide the induction focus from source
-- lookup and rebuild all notion indexes from retained proof locals. In
-- particular, cached universal producers and equality edges cannot survive
-- the removal of the assumptions that justified them.
projectProofElaborationContext
    :: LocalId -> Set.Set Natural
    -> [(Natural, Natural, ScopedCheckedCore ObjectId)]
    -> ElaborationContext -> FormationScopePreparation ElaborationContext
projectProofElaborationContext hidden allowed projections context@(ElaborationContext binders overrides scope) = do
    let hide (ElaborationBinder identity variable coreType annotation)
            | identity == hidden = ElaborationBinder identity Nothing coreType Nothing
            | otherwise = ElaborationBinder identity variable coreType annotation
        initial = ElaborationContext (hide <$> binders) overrides emptyFormationScope
        keep = \case
            FormationFromProofLocal ordinal _ -> ordinal `Set.member` allowed
            _ -> False
        aliases = [source | source@(FormationAliasSource _ _ _ chain _) <- reverse (formationScopeAliases scope)
            , all (keep . materializedNotionHypothesisOrigin) chain]
    premises <- fmap catMaybes $ for (reverse (formationScopeSources scope)) \source@(FormationPremiseSource _ proposition evidence origin) ->
        if keep origin then pure (Just source) else case projection origin of
            Nothing -> pure Nothing
            Just (ordinal, residual) -> do
                let difference = length types - length (scopedCoreContext proposition)
                aligned <- align 0 proposition
                evidence' <- SourceEvidence.traverseSourceAtDepth
                    (\depth -> traverse (\term -> scopePreparationCore (\work ->
                        countedShiftCanonical work (fromIntegral difference) depth term)))
                    (\depth -> traverseSourceNotionAssertionParts (alignTerm depth) (align depth)) evidence
                pure (Just (formationEvidenceSource support residual
                    (prune (scopedCoreTerm aligned) (scopedCoreTerm residual) evidence')
                    ordinal FormationProofDerivedClaim))
    equalities <- fmap catMaybes $ for (reverse (formationScopeEqualities scope)) \source@(FormationEqualitySource _ _ occurrences origin) ->
        if keep origin then pure (Just source) else case projection origin of
            Nothing -> pure Nothing
            Just (ordinal, residual) -> do
                aligned <- traverse (traverseSourceEqualityOccurrenceParts (alignTerm 0) (align 0)) occurrences
                pure (Just (formationEqualitySource support residual aligned ordinal FormationProofDerivedClaim))
    withAliases <- foldM (flip prepareFormationAliasContext) initial aliases
    withPremises <- foldM (flip prepareFormationPremiseSource) withAliases premises
    foldM (flip prepareFormationEqualitySource) withPremises equalities
  where
    types = binderTypes context
    support = elaborationContextSupport context
    replacements = Map.fromList [(old, (new, residual)) | (old, new, residual) <- projections]
    projection (FormationFromProofLocal ordinal _) = Map.lookup ordinal replacements
    projection _ = Nothing
    align depth value = scopePreparationCore (\work ->
        countedAlignScopedCoreAt work depth (replicate (fromIntegral depth) TySet <> types) value)
        >>= maybe (Except.throwError (FormationObservationScopeError "induction projection escaped its scope")) pure
    alignTerm depth value = scopePreparationCore (\work ->
        SourceTerm.countedAlignScopedSourceTermOccurrenceAt work depth
            (replicate (fromIntegral depth) TySet <> types) value)
        >>= maybe (Except.throwError (FormationObservationScopeError "induction operand escaped its scope")) pure
    -- Projection replaces only selected conjunction leaves by truth. Keep the
    -- evidence and equality paths of every independent conjunct unchanged.
    prune original residual evidence
        | original == residual = evidence
    prune _ CTruth _ = SourceEvidence.SourceResidual Nothing
    prune original residual (SourceEvidence.SourceWithInputs _ body) = prune original residual body
    prune (CAnd a b) (CAnd x y) (SourceEvidence.SourceAnd left right) =
        SourceEvidence.SourceAnd (prune a x left) (prune b y right)
    prune _ _ _ = SourceEvidence.SourceResidual Nothing

type ScopedSourceNotionAssertion =
    SourceNotionOccurrence
        SourceTermPresentation
        (ScopedCheckedCore ObjectId)
        (ScopedCheckedCore ObjectId)

type ScopedSourceEqualityOccurrence =
    SourceEqualityOccurrence
        ScopedSourceTerm
        (ScopedCheckedCore ObjectId)

type ScopedSourceTerm =
    SourceTerm.SourceTermOccurrence
        SourceTermPresentation
        (ScopedCheckedCore ObjectId)

type ScopedSourceNotionOccurrence =
    SourceNotionOccurrence
        SourceTermPresentation
        ScopedSourceTerm
        (ScopedCheckedCore ObjectId)

data ElaboratedProposition = ElaboratedProposition
    !(ScopedCheckedCore ObjectId)
    !(SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
    ![ScopedSourceEqualityOccurrence]

elaboratedPropositionCore
    :: ElaboratedProposition
    -> ScopedCheckedCore ObjectId
elaboratedPropositionCore
        (ElaboratedProposition proposition _assertions _equalities) =
    proposition

elaboratedPropositionAssertions
    :: ElaboratedProposition
    -> [ScopedSourceNotionOccurrence]
elaboratedPropositionAssertions = sourceEvidenceAssertions . elaboratedPropositionEvidence

elaboratedPropositionEvidence
    :: ElaboratedProposition
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
elaboratedPropositionEvidence
        (ElaboratedProposition _proposition assertions _equalities) =
    assertions

elaboratedPropositionEqualities
    :: ElaboratedProposition
    -> [ScopedSourceEqualityOccurrence]
elaboratedPropositionEqualities
        (ElaboratedProposition _proposition _assertions equalities) =
    equalities

rebaseEvidenceOntoLocal
    :: ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> Either Text (SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
rebaseEvidenceOntoLocal proposition evidence = do
    validate (scopedCoreContext proposition) (scopedCoreTerm proposition) evidence
    pure evidence
  where
    validate context core = \case
        SourceResidual{} -> pure ()
        SourceInputs{} -> pure ()
        SourceWithInputs _ body -> validate context core body
        SourceAtom atom -> unless
            (scopedCoreContext (sourceAssertionFormula atom) == context
                && projectConjunctionPath (sourceAssertionPath atom) core
                    == Just (scopedCoreTerm (sourceAssertionFormula atom)))
            (Left "a source atom does not belong to its retained local")
        SourceAnd left right | CAnd a b <- core -> validate context a left >> validate context b right
        SourceBind body | CForall TySet b <- core -> validate (TySet : context) b body
        SourceExists body | CExists TySet b <- core -> validate (TySet : context) b body
        SourceOr left right | COr a b <- core -> validate context a left >> validate context b right
        SourceIff left right | CEq TyProp a b <- core -> validate context a left >> validate context b right
        SourceRequire guard body | CImp g b <- core -> validate context g guard >> validate context b body
        _ -> Left "a source evidence tree does not belong to its retained local"

rebaseAssertionsOntoLocal
    :: ScopedCheckedCore ObjectId
    -> [ScopedSourceNotionOccurrence]
    -> Either Text [ScopedSourceNotionOccurrence]
rebaseAssertionsOntoLocal proposition assertions = do
    traverse_ validate assertions
    pure assertions
  where
    validate assertion =
        unless
            ( scopedCoreContext (sourceAssertionFormula assertion)
                == scopedCoreContext proposition
              && projectConjunctionPath
                    (sourceAssertionPath assertion)
                    (scopedCoreTerm proposition)
                == Just
                    (scopedCoreTerm (sourceAssertionFormula assertion))
            )
            (Left
                "source notion assertions do not project from the admitted local")

rebaseEqualitiesOntoLocal
    :: ScopedCheckedCore ObjectId
    -> [ScopedSourceEqualityOccurrence]
    -> Either Text [ScopedSourceEqualityOccurrence]
rebaseEqualitiesOntoLocal proposition equalities = do
    traverse_ validate equalities
    pure equalities
  where
    validate equality =
        unless
            ( scopedCoreContext (sourceEqualityFormula equality)
                == scopedCoreContext proposition
              && projectConjunctionPath
                    (sourceEqualityPath equality)
                    (scopedCoreTerm proposition)
                == Just
                    (scopedCoreTerm (sourceEqualityFormula equality))
            )
            (Left
                "source equalities do not project from the admitted local")

data ElaboratedSetExpression = ElaboratedSetExpression
    !ScopedSourceTerm
    !(Maybe ElaboratedSetConstruction)

data ElaboratedExpression = ElaboratedExpression
    !(ScopedCheckedCore ObjectId)
    !(Maybe ScopedSourceTerm)

-- A checked aggregate view shared by instances and parameterized
-- constructions. Source spelling stays in the parsed declaration; consumers
-- use these canonical fields rather than reverse-engineering a record graph.
data ElaboratedRecordAggregate = ElaboratedRecordAggregate
    { elaboratedAggregateStructure :: !Declaration.ResolvedStructure
    , elaboratedAggregateCore :: !(ScopedCheckedCore ObjectId)
    , elaboratedAggregatePredicate :: !(ScopedCheckedCore ObjectId)
    , elaboratedAggregateFields :: ![ElaboratedRecordField (ScopedCheckedCore ObjectId)]
    }

data RecordFieldOrigin
    = WrittenRecordField !Location
    | CopiedRecordField !Location
    deriving stock (Show, Eq)

-- The value advances from written syntax to checked Core; field identity and
-- diagnostic origin remain unchanged throughout aggregate preparation.
data ElaboratedRecordField value = ElaboratedRecordField
    { elaboratedRecordField :: !Schema.ResolvedField
    , elaboratedRecordValue :: !value
    , elaboratedRecordOrigin :: !RecordFieldOrigin
    } deriving stock (Functor, Foldable, Traversable)

elaborateRecordAggregate
    :: ElaborationContext -> Raw.Expr -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedRecordAggregate)
elaborateRecordAggregate context expression = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    ((structure, body, predicate, fields), final) <- State.runStateT compile initial
    let check term = either
            (Except.throwError . ElaborationCoreCheckFailed (locate expression)) pure
            (checkScopedCanonicalCore (elaborationGlobalTyping final) (binderTypes context) term)
    ElaboratedRecordAggregate structure <$> check body <*> check predicate
        <*> traverse (traverse check) fields
  where
    compile = do
        (structure, annotation, values) <- case expression of
            Raw.ExprStructAggregate location schema entries -> do
                application <- maybe
                    (Except.throwError (ElaborationStructureAggregateSchemaRequired location)) pure schema
                (structure, annotation) <- resolveExpressionStructureApplication location application
                resolved <- resolveStructureAggregate location structure annotation entries
                values <- compileStructureAggregateValues resolved
                pure (structure, annotation, values)
            Raw.ExprStructReconstruction location schema base entries ->
                compileReconstructionParts location schema base entries
            _ -> Except.throwError (ElaborationRecordAggregateRequired (locate expression))
        let body = aggregatePartsTerm values
        predicate <- applyStructureAnnotation body annotation
        pure (structure, body, predicate, values)

elaboratedExpressionCore
    :: ElaboratedExpression
    -> ScopedCheckedCore ObjectId
elaboratedExpressionCore (ElaboratedExpression expression _source) =
    expression

elaboratedExpressionSource
    :: ElaboratedExpression
    -> Maybe ScopedSourceTerm
elaboratedExpressionSource (ElaboratedExpression _expression source) =
    source

data ElaboratedSetConstruction
    = ElaboratedUnconditionalSetConstruction
        !(NamedSetConstruction ObjectId)
    | ElaboratedRelationalSetConstruction
        !(CheckedRelationalSetConstruction ObjectId)

elaboratedSetExpressionCore
    :: ElaboratedSetExpression
    -> ScopedCheckedCore ObjectId
elaboratedSetExpressionCore (ElaboratedSetExpression expression _construction) =
    SourceTerm.sourceTermOccurrenceCore expression

elaboratedSetExpressionSource
    :: ElaboratedSetExpression
    -> ScopedSourceTerm
elaboratedSetExpressionSource
        (ElaboratedSetExpression expression _construction) =
    expression

elaboratedSetExpressionConstruction
    :: ElaboratedSetExpression
    -> Maybe ElaboratedSetConstruction
elaboratedSetExpressionConstruction
        (ElaboratedSetExpression _expression construction) =
    construction

-- | A checked replacement graph and the two checked arguments used to
-- specialize its foundation characteristic. This is transient proof
-- preparation data, not a declaration or durable object.
data ElaboratedLocalFunctionGraph = ElaboratedLocalFunctionGraph
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)

elaboratedLocalFunctionGraphCore
    :: ElaboratedLocalFunctionGraph
    -> ScopedCheckedCore ObjectId
elaboratedLocalFunctionGraphCore
        (ElaboratedLocalFunctionGraph graph _domain _function) =
    graph

elaboratedLocalFunctionGraphDomain
    :: ElaboratedLocalFunctionGraph
    -> ScopedCheckedCore ObjectId
elaboratedLocalFunctionGraphDomain
        (ElaboratedLocalFunctionGraph _graph domain _function) =
    domain

elaboratedLocalFunctionGraphMap
    :: ElaboratedLocalFunctionGraph
    -> ScopedCheckedCore ObjectId
elaboratedLocalFunctionGraphMap
        (ElaboratedLocalFunctionGraph _graph _domain function) =
    function

-- | One authoritative closed proposition prepared from a top-level claim
-- header and conclusion. The remaining fields are transient opening data for
-- the proof compiler.
data ElaboratedClaimEnvelope = ElaboratedClaimEnvelope
    !(ScopedCheckedCore ObjectId)
    ![Raw.VarSymbol]
    !ElaborationContext
    ![CompiledHeaderAntecedent]
    !(SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
    ![ScopedSourceEqualityOccurrence]

data CompiledHeaderAntecedent = CompiledHeaderAntecedent
    !ElaboratedProposition
    !Natural
    !(Maybe Natural)
    !Location

-- | One unchecked row produced by a source header. A grouped header may
-- produce several subject rows and one shared residual row.
data CompiledHeaderRow = CompiledHeaderRow
    !Natural
    !(Maybe Natural)
    !Location
    !CompiledProposition

-- | One source header transaction. Structure designations are committed only
-- after every row in this batch has crossed the checked-proposition boundary.
data CompiledHeaderBatch = CompiledHeaderBatch
    ![CompiledHeaderRow]
    !(Map.Map Natural ResolvedStructureApplication)

compiledHeaderBatchRows :: CompiledHeaderBatch -> [CompiledHeaderRow]
compiledHeaderBatchRows (CompiledHeaderBatch rows _designations) = rows

compiledHeaderRowProposition :: CompiledHeaderRow -> CompiledProposition
compiledHeaderRowProposition
        (CompiledHeaderRow _source _variable _location proposition) = proposition

compiledHeaderCore
    :: CompiledHeaderAntecedent
    -> ScopedCheckedCore ObjectId
compiledHeaderCore = elaboratedPropositionCore . checkedHeaderProposition

compiledHeaderAssertions
    :: CompiledHeaderAntecedent
    -> [ScopedSourceNotionOccurrence]
compiledHeaderAssertions = sourceEvidenceAssertions . compiledHeaderEvidence

compiledHeaderEvidence
    :: CompiledHeaderAntecedent
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
compiledHeaderEvidence = elaboratedPropositionEvidence . checkedHeaderProposition

compiledHeaderEqualities
    :: CompiledHeaderAntecedent
    -> [ScopedSourceEqualityOccurrence]
compiledHeaderEqualities = elaboratedPropositionEqualities . checkedHeaderProposition

compiledHeaderSourceOrdinal
    :: CompiledHeaderAntecedent
    -> Natural
compiledHeaderSourceOrdinal
        (CompiledHeaderAntecedent
            _proposition source _variable _location) =
    source

compiledHeaderVariableOrdinal
    :: CompiledHeaderAntecedent
    -> Maybe Natural
compiledHeaderVariableOrdinal
        (CompiledHeaderAntecedent
            _proposition _source variable _location) =
    variable

compiledHeaderLocation :: CompiledHeaderAntecedent -> Location
compiledHeaderLocation (CompiledHeaderAntecedent _ _ _ location) = location

elaboratedClaimTarget
    :: ElaboratedClaimEnvelope
    -> ScopedCheckedCore ObjectId
elaboratedClaimTarget
        (ElaboratedClaimEnvelope target _variables _context _antecedents
            _conclusionAssertions _conclusionEqualities) =
    target

elaboratedClaimVariables
    :: ElaboratedClaimEnvelope
    -> [Raw.VarSymbol]
elaboratedClaimVariables
        (ElaboratedClaimEnvelope _target variables _context _antecedents
            _conclusionAssertions _conclusionEqualities) =
    variables

elaboratedClaimContext
    :: ElaboratedClaimEnvelope
    -> ElaborationContext
elaboratedClaimContext
        (ElaboratedClaimEnvelope _target _variables context _antecedents
            _conclusionAssertions _conclusionEqualities) =
    context

elaboratedClaimAntecedentCount
    :: ElaboratedClaimEnvelope
    -> Natural
elaboratedClaimAntecedentCount
        (ElaboratedClaimEnvelope _target _variables _context antecedents
            _conclusionAssertions _conclusionEqualities) =
    fromIntegral (length antecedents)

elaboratedClaimAntecedents
    :: ElaboratedClaimEnvelope
    -> [CompiledHeaderAntecedent]
elaboratedClaimAntecedents
        (ElaboratedClaimEnvelope _target _variables _context antecedents
            _conclusionAssertions _conclusionEqualities) =
    antecedents

elaboratedClaimConclusionAssertions
    :: ElaboratedClaimEnvelope
    -> [ScopedSourceNotionOccurrence]
elaboratedClaimConclusionAssertions = sourceEvidenceAssertions . elaboratedClaimConclusionEvidence

elaboratedClaimConclusionEvidence
    :: ElaboratedClaimEnvelope
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
elaboratedClaimConclusionEvidence
        (ElaboratedClaimEnvelope _target _variables _context _antecedents
            conclusionAssertions _conclusionEqualities) =
    conclusionAssertions

elaboratedClaimConclusionEqualities
    :: ElaboratedClaimEnvelope
    -> [ScopedSourceEqualityOccurrence]
elaboratedClaimConclusionEqualities
        (ElaboratedClaimEnvelope _target _variables _context _antecedents
            _conclusionAssertions conclusionEqualities) =
    conclusionEqualities

data SourceTermPresentation
    = PresentedSourceTerm !Location !Text
    | LocatedSourceTerm !Location
    deriving stock (Show, Eq)

-- | Compiled Core with its inferred source sort and diagnostic presentation,
-- awaiting the surrounding scoped-Core sealing boundary.  Core and sort are
-- strict; presentation is intentionally lazy so successful or uncontracted
-- occurrences do not render source text.  A formation diagnostic demands only
-- its selected operands.
type CompiledSourceTerm =
    SourceTerm.SourceTermOccurrence
        SourceTermPresentation
        (CanonicalTerm ObjectId)

-- | One checked, explicitly received structure field.  The field identity and
-- projection are selected together with the rich receiver occurrence; this
-- value is never constructed for omitted or contextual field notation.
data ResolvedExplicitFieldSelection = ResolvedExplicitFieldSelection
    !FieldId
    !ObjectId
    !CompiledSourceTerm
    !(CanonicalTerm ObjectId)

data RichSourceTermKey
    = RichOpaqueTerm !(CanonicalTerm ObjectId)
    | RichProviderTerm
        !SourceProviderHead !(Vector RichSourceTermKey)
    | RichOrderedPairTerm !RichSourceTermKey !RichSourceTermKey
    deriving stock (Show, Eq, Ord)

type RichFormationGoalKey = AtomTemplate RichSourceTermKey

richFormationGoalKey
    :: AtomTemplate CompiledSourceTerm
    -> RichFormationGoalKey
richFormationGoalKey = fmap richSourceTermKey

richSourceTermKey :: CompiledSourceTerm -> RichSourceTermKey
richSourceTermKey occurrence =
    case SourceTerm.sourceTermOccurrenceProvider occurrence of
        Just provider ->
            RichProviderTerm
                (SourceTerm.sourceTermProviderHead provider)
                (richSourceTermKey
                    <$> SourceTerm.sourceTermProviderArguments provider)
        Nothing ->
            case SourceTerm.sourceTermOccurrenceOrderedPair occurrence of
                Just (left, right) ->
                    RichOrderedPairTerm
                        (richSourceTermKey left)
                        (richSourceTermKey right)
                Nothing -> RichOpaqueTerm (compiledSourceTermCore occurrence)

compiledSourceTermCore
    :: CompiledSourceTerm
    -> CanonicalTerm ObjectId
compiledSourceTermCore = SourceTerm.sourceTermOccurrenceCore

compiledSourceTermType :: CompiledSourceTerm -> CoreType
compiledSourceTermType = SourceTerm.sourceTermOccurrenceType

compiledSourceTermPresentation
    :: CompiledSourceTerm
    -> SourceTermPresentation
compiledSourceTermPresentation = SourceTerm.sourceTermOccurrencePresentation

globalProviderSourceTerm
    :: GlobalBindingRef
    -> Vector CompiledSourceTerm
    -> CanonicalTerm ObjectId
    -> SourceTermPresentation
    -> CompiledSourceTerm
globalProviderSourceTerm reference arguments core presentation =
    fromMaybe
        (impossible "a checked global provider lost its set-valued signature")
        (SourceTerm.sourceGlobalProviderTermOccurrence
            reference arguments core presentation)

structureFieldProviderSourceTerm
    :: FieldId
    -> ObjectId
    -> CompiledSourceTerm
    -> SourceTermPresentation
    -> CompiledSourceTerm
structureFieldProviderSourceTerm identity projection receiver presentation =
    fromMaybe
        (impossible "a checked structure-field provider lost its set receiver")
        (SourceTerm.sourceStructureFieldProviderTermOccurrence
            identity projection receiver presentation)

intrinsicProviderSourceTerm
    :: IntrinsicProviderId
    -> Vector CompiledSourceTerm
    -> SourceTermPresentation
    -> CompiledSourceTerm
intrinsicProviderSourceTerm provider arguments presentation =
    fromMaybe
        (impossible "a checked intrinsic provider lost its exact first-order set shape")
        (SourceTerm.sourceIntrinsicProviderTermOccurrence
            provider arguments presentation)

finiteSetLiteralProviderSourceTerm
    :: NonEmpty CompiledSourceTerm
    -> SourceTermPresentation
    -> CompiledSourceTerm
finiteSetLiteralProviderSourceTerm elements presentation =
    fromMaybe
        (impossible
            "a checked finite-set literal lost its nonempty set-valued spine")
        (SourceTerm.sourceFiniteSetLiteralTermOccurrence elements presentation)

-- Private materializers call this only after their formation contract or
-- visible provider-result rule has validated the variadic provider spine.
requiredMaterializedFiniteSetSpine :: Vector value -> NonEmpty value
requiredMaterializedFiniteSetSpine arguments =
    fromMaybe
        (impossible "a materialized finite-set provider has an empty spine")
        (NonEmpty.nonEmpty (toList arguments))

data FormationRequirementFailure = FormationRequirementFailure
    { formationRequirementStructureNames :: !(Map StructureId Schema.StructurePhrase)
    , formationRequirementFailureBinding :: !ResolvedGlobalBinding
    , formationRequirementFailureRequirement
        :: !(AtomTemplate SourceTermPresentation)
    , formationRequirementFailureExplanation
        :: !(FormationFailureExplanation FormationSourceOrigin)
    , formationRequirementFailureDetail
        :: !(Maybe RichFormationFailureDetail)
    , formationRequirementFailureSearchStatistics
        :: !FormationSearchStatistics
    }
    | WholeFormationRequirementFailure
        { formationRequirementFailureBinding :: !ResolvedGlobalBinding
        , formationWholeRequirement :: !(ScopedCheckedCore ObjectId)
        , formationRequirementFailureSearchStatistics :: !FormationSearchStatistics
        }
    deriving stock (Show, Eq)


data ElaborationError
    = ElaborationUnsupportedDeclaration !Location
    | ElaborationRecursiveDefinitionInvalid !Location !Text
    | ElaborationUnsupportedDeclarationBody !Location
    | ElaborationGuardedTransparentDefinition !Location
    | ElaborationGuardedOpaqueSignature !Location
    | ElaborationDefinitionCombinedSymbolicAlias !Location
    | ElaborationRelationalReplacementRequiresNamedDefinition !Location
    | ElaborationDeclarationOccurrenceMissing !Location
    | ElaborationDeclarationOccurrenceAmbiguous !Location
    | ElaborationDeclarationHeadMismatch !Location
    | ElaborationFixedSemanticCollision !Location !SemanticGlobalKey
    | ElaborationGlobalAlreadyVisible !Location !SemanticGlobalKey
    | ElaborationGlobalNotVisible !Location !SemanticGlobalKey
    | ElaborationAdjectiveReadingAmbiguous
        !Location !(NonEmpty SemanticGlobalKey)
    | ElaborationFormationRequirementMissing
        !Location !FormationRequirementFailure
    | ElaborationFormationReplayFailed
        !Location !Declaration.TransientFormationReplayError
    | ElaborationFormationSearchFailed !Location !FormationSearchError
    | ElaborationFormationScopeFailed !Location !FormationObservationError
    | ElaborationDefinitionResultShapeUnsupported !Location
    | ElaborationExpansionFailed !Location !SemanticGlobalKey !ExpansionFailure
    | ElaborationDefinitionResultRequiresGuardedProvider !Location
    | ElaborationDefinitionResultShapeInvalid !Location !Text
    | ElaborationDefinitionResultUnavailable !Location !NotionQueryFailure
    | ElaborationGroupedNounNameUnsupported !Location
    | ElaborationNounBoundUnsupported !Location
    | ElaborationNounBoundScope !Location !Raw.VarSymbol
    | ElaborationDuplicateParameter !Location !Raw.VarSymbol
    | ElaborationDuplicateLocalBinder !Location !Raw.VarSymbol
    | ElaborationDuplicateLocalIdentity !Location !LocalId
    | ElaborationFreeVariable !Location !Raw.VarSymbol
    | ElaborationApplicationExpectedFunction !Location !CoreType
    | ElaborationApplicationArgumentMismatch
        !Location !CoreType !CoreType
    | ElaborationSelectionExpectedPredicate !Location !CoreType
    | ElaborationSelectionTypeMismatch !Location !CoreType !CoreType
    | ElaborationEqualityOperandMismatch
        !Location !CoreType !CoreType
    | ElaborationExpressionExpectedSet !Location !CoreType
    | ElaborationNaturalNumeralBasisUnavailable !Location
    | ElaborationNaturalNumeralMagnitudeExceeded !Location !Natural !Natural
    | ElaborationFormulaExpectedProposition !Location !CoreType
    | ElaborationCalculationFailed !Location !Calculation.CalculationError
    | ElaborationCoreCheckFailed !Location !CoreCheckError
    | ElaborationCoreGlobalsMissing !Location !(NonEmpty ObjectId)
    | ElaborationProspectiveObjectInvalid !ObjectValidationError
    | ElaborationProspectiveObjectMissing !Location !ObjectId
    | ElaborationObjectTypeMismatch !Location !CoreType !CoreType
    | ElaborationUnsupportedHeaderAssumption !Location
    | ElaborationQuantifiedTermRequiresPropositionContext !Location
    | ElaborationStructureNotVisible !Location !Schema.StructurePhrase
    | ElaborationStructureParameterArityMismatch
        !Location !Schema.StructurePhrase !Natural !Natural
    | ElaborationStructureParameterPreambleMismatch
        !Location ![Raw.VarSymbol] ![Raw.VarSymbol]
    | ElaborationStructureParameterDependencyViolation
        !Location !Natural !Natural
    | ElaborationBaseStructureNotAssertable !Location !Schema.StructurePhrase
    | ElaborationDuplicateStructureAnnotation !Location !Raw.VarSymbol
    | ElaborationStructureFieldNotAvailable !Location !Raw.StructSymbol
    | ElaborationStructureFieldAmbiguous
        !Location !Raw.StructSymbol ![ObjectId]
    | ElaborationStructureReceiverAmbiguous
        !Location !Raw.StructSymbol !(NonEmpty Text)
    | ElaborationContextualExpansionNotAvailable
        !Location !SemanticGlobalKey
    | ElaborationContextualReceiverAmbiguous
        !Location !SemanticGlobalKey !(NonEmpty Text)
    | ElaborationContextualRequirementConflict
        !Location !Raw.StructSymbol !(FieldId, ObjectId) !(FieldId, ObjectId)
    | ElaborationStructureOccurrenceMismatch !Location
    | ElaborationStructureSelfParent !Location !Schema.StructurePhrase
    | ElaborationStructureDuplicateParent !Location !Schema.StructurePhrase
    | ElaborationStructureAlreadyVisible !Location !Schema.StructurePhrase
    | ElaborationStructureDuplicateField !Location !Raw.StructSymbol
    | ElaborationStructureFieldAlreadyInherited !Location !Raw.StructSymbol
    | ElaborationStructureFieldConflict
        !Location !Raw.StructSymbol
        !Schema.StructurePhrase !Schema.StructurePhrase
    | ElaborationStructureCarrierUnavailable !Location !Schema.StructurePhrase
    | ElaborationStructureSchemaInvalid !Location !Schema.LocalStructureSchemaError
    | ElaborationStructureInterfaceNotVisible !Location !StructureId
    | ElaborationStructureObjectNotVisible !Location !ObjectId
    | ElaborationStructureAggregateSchemaRequired !Location
    | ElaborationRecordAggregateRequired !Location
    | ElaborationStructureAggregateMixedEntries !Location
    | ElaborationStructureAggregateFieldArityMismatch
        !Location !Schema.StructurePhrase !Natural !Natural
    | ElaborationStructureAggregateUnknownField
        !Location !Schema.StructurePhrase !Raw.StructSymbol
    | ElaborationStructureAggregateDuplicateField
        !Location !Schema.StructurePhrase !Raw.StructSymbol
    | ElaborationStructureAggregateMissingFields
        !Location !Schema.StructurePhrase !(NonEmpty Raw.StructSymbol)
    | ElaborationReconstructionBaseUnavailable
        !Location !(Raw.StructApplication Raw.Expr) !Raw.Expr !ReconstructionFailure
    deriving stock (Show, Eq)

elaborationErrorLocation :: ElaborationError -> Location
elaborationErrorLocation = \case
    ElaborationUnsupportedDeclaration location -> location
    ElaborationRecursiveDefinitionInvalid location _ -> location
    ElaborationUnsupportedDeclarationBody location -> location
    ElaborationGuardedTransparentDefinition location -> location
    ElaborationGuardedOpaqueSignature location -> location
    ElaborationDefinitionCombinedSymbolicAlias location -> location
    ElaborationRelationalReplacementRequiresNamedDefinition location -> location
    ElaborationDeclarationOccurrenceMissing location -> location
    ElaborationDeclarationOccurrenceAmbiguous location -> location
    ElaborationDeclarationHeadMismatch location -> location
    ElaborationFixedSemanticCollision location _key -> location
    ElaborationGlobalAlreadyVisible location _key -> location
    ElaborationGlobalNotVisible location _key -> location
    ElaborationAdjectiveReadingAmbiguous location _keys -> location
    ElaborationFormationRequirementMissing location _requirement -> location
    ElaborationFormationReplayFailed location _failure -> location
    ElaborationFormationSearchFailed location _failure -> location
    ElaborationFormationScopeFailed location _failure -> location
    ElaborationDefinitionResultShapeUnsupported location -> location
    ElaborationExpansionFailed location _ _ -> location
    ElaborationDefinitionResultRequiresGuardedProvider location -> location
    ElaborationDefinitionResultShapeInvalid location _failure -> location
    ElaborationDefinitionResultUnavailable location _failure -> location
    ElaborationGroupedNounNameUnsupported location -> location
    ElaborationNounBoundUnsupported location -> location
    ElaborationNounBoundScope location _variable -> location
    ElaborationDuplicateParameter location _parameter -> location
    ElaborationDuplicateLocalBinder location _variable -> location
    ElaborationDuplicateLocalIdentity location _identity -> location
    ElaborationFreeVariable location _variable -> location
    ElaborationApplicationExpectedFunction location _actual -> location
    ElaborationApplicationArgumentMismatch location _expected _actual -> location
    ElaborationSelectionExpectedPredicate location _actual -> location
    ElaborationSelectionTypeMismatch location _expected _actual -> location
    ElaborationEqualityOperandMismatch location _left _right -> location
    ElaborationExpressionExpectedSet location _actual -> location
    ElaborationNaturalNumeralBasisUnavailable location -> location
    ElaborationNaturalNumeralMagnitudeExceeded location _actual _maximum ->
        location
    ElaborationFormulaExpectedProposition location _actual -> location
    ElaborationCalculationFailed location _reason -> location
    ElaborationCoreCheckFailed location _failure -> location
    ElaborationCoreGlobalsMissing location _identities -> location
    ElaborationProspectiveObjectInvalid{} -> Nowhere
    ElaborationProspectiveObjectMissing location _identity -> location
    ElaborationObjectTypeMismatch location _expected _actual -> location
    ElaborationUnsupportedHeaderAssumption location -> location
    ElaborationQuantifiedTermRequiresPropositionContext location -> location
    ElaborationStructureNotVisible location _phrase -> location
    ElaborationStructureParameterArityMismatch location _phrase _expected _actual ->
        location
    ElaborationStructureParameterPreambleMismatch location _declared _introduced ->
        location
    ElaborationStructureParameterDependencyViolation location _available _total ->
        location
    ElaborationBaseStructureNotAssertable location _phrase -> location
    ElaborationDuplicateStructureAnnotation location _variable -> location
    ElaborationStructureFieldNotAvailable location _symbol -> location
    ElaborationStructureFieldAmbiguous location _symbol _objects -> location
    ElaborationStructureReceiverAmbiguous location _symbol _receivers -> location
    ElaborationContextualExpansionNotAvailable location _key -> location
    ElaborationContextualReceiverAmbiguous location _key _receivers -> location
    ElaborationContextualRequirementConflict location _symbol _first _second -> location
    ElaborationStructureOccurrenceMismatch location -> location
    ElaborationStructureSelfParent location _phrase -> location
    ElaborationStructureDuplicateParent location _phrase -> location
    ElaborationStructureAlreadyVisible location _phrase -> location
    ElaborationStructureDuplicateField location _symbol -> location
    ElaborationStructureFieldAlreadyInherited location _symbol -> location
    ElaborationStructureFieldConflict location _symbol _first _second -> location
    ElaborationStructureCarrierUnavailable location _phrase -> location
    ElaborationStructureSchemaInvalid location _failure -> location
    ElaborationStructureInterfaceNotVisible location _identity -> location
    ElaborationStructureObjectNotVisible location _object -> location
    ElaborationStructureAggregateSchemaRequired location -> location
    ElaborationRecordAggregateRequired location -> location
    ElaborationStructureAggregateMixedEntries location -> location
    ElaborationStructureAggregateFieldArityMismatch
            location _phrase _expected _actual -> location
    ElaborationStructureAggregateUnknownField location _phrase _field -> location
    ElaborationStructureAggregateDuplicateField location _phrase _field -> location
    ElaborationStructureAggregateMissingFields location _phrase _fields -> location
    ElaborationReconstructionBaseUnavailable location _target _base _reason -> location

renderElaborationError :: ElaborationError -> Text
renderElaborationError = \case
    ElaborationUnsupportedDeclaration location ->
        at location <> "this declaration is not yet supported by the typed checker"
    ElaborationRecursiveDefinitionInvalid location problem ->
        at location <> "invalid recursive definition: " <> problem
    ElaborationUnsupportedDeclarationBody location ->
        at location <> "this source form is not yet supported by elaboration"
    ElaborationGuardedTransparentDefinition location ->
        at location
            <> "this transparent definition header is unsupported; "
            <> "use only noun, symbolic membership, or open structure assumptions whose terms are direct declaration arguments"
    ElaborationGuardedOpaqueSignature location ->
        at location
            <> "an opaque signature cannot have a header assumption; "
            <> "state the condition in a following explicit axiom"
    ElaborationDefinitionCombinedSymbolicAlias location ->
        at location
            <> "a functional definition cannot declare a symbolic equivalent at the same time; "
            <> "define the symbolic operator first, then define the functional phrase as an abbreviation applying it"
    ElaborationRelationalReplacementRequiresNamedDefinition location ->
        at location
            <> "relational replacement is supported only as the outer body of a named definition"
    ElaborationDeclarationOccurrenceMissing location ->
        at location <> "the declaration has no associated syntax occurrence"
    ElaborationDeclarationOccurrenceAmbiguous location ->
        at location <> "the declaration has more than one semantic head"
    ElaborationDeclarationHeadMismatch location ->
        at location <> "the parsed declaration head does not match its syntax occurrence"
    ElaborationFixedSemanticCollision location key ->
        at location <> "the declaration collides with fixed semantics for "
            <> shown key
    ElaborationGlobalAlreadyVisible location key ->
        at location <> "the global " <> shown key <> " is already declared"
    ElaborationGlobalNotVisible location key ->
        at location <> "the global " <> shown key <> " is not visible"
    ElaborationAdjectiveReadingAmbiguous location keys ->
        at location <> renderAdjectiveReadingAmbiguity keys
    ElaborationFormationRequirementMissing location failure ->
        at location <> renderFormationRequirementFailure failure
    ElaborationFormationReplayFailed location
            (Declaration.TransientFormationProofFailed (FormationProofDerivationLimitExceeded failure)) ->
        at location <> renderFormationSearchError failure
    ElaborationFormationReplayFailed location failure ->
        at location <> "internal notion evidence failed kernel replay: "
            <> shown failure
    ElaborationFormationSearchFailed location failure ->
        at location <> renderFormationSearchError failure
    ElaborationFormationScopeFailed location failure ->
        at location <> "notion source preparation failed: " <> case failure of
            FormationObservationScopeError reason -> reason
            FormationObservationExhausted reason -> renderFormationSearchError reason
            FormationScopePreparationLimitExceeded limit ->
                "scope preparation exceeded " <> shown limit <> " work units"
    ElaborationExpansionFailed location key failure ->
        at location <> "abbreviation expansion failed for " <> shown key <> ": " <> renderExpansionFailure failure
    ElaborationDefinitionResultShapeUnsupported location ->
        at location
            <> "a definition result annotation must be an ordinary noun phrase expressing a nontrivial notion condition"
    ElaborationDefinitionResultRequiresGuardedProvider location ->
        at location
            <> "a definition result annotation requires a provider with at least one argument and at least one checked definition header"
    ElaborationDefinitionResultShapeInvalid location failure ->
        at location <> "this definition result cannot become a bounded provider-result classification: "
            <> failure
    ElaborationDefinitionResultUnavailable location failure ->
        at location
            <> "the definition headers do not establish the annotated result notion. "
            <> renderNotionQueryFailure failure
    ElaborationGroupedNounNameUnsupported location ->
        at location
            <> "one embedded noun name cannot describe several displayed subjects; "
            <> "repeat the noun phrase for each subject"
    ElaborationNounBoundUnsupported location ->
        at location <> "a noun bound requires named variables in a quantified or Take phrase"
    ElaborationNounBoundScope location variable ->
        at location <> "the noun bound endpoint contains its own group name " <> shown variable
    ElaborationDuplicateParameter location parameter ->
        at location <> "the declaration parameter " <> shown parameter <> " is repeated"
    ElaborationDuplicateLocalBinder location variable ->
        at location <> "the proof binder " <> shown variable <> " is already active"
    ElaborationDuplicateLocalIdentity location identity ->
        at location <> "the proof-local identity " <> shown identity <> " is already active"
    ElaborationFreeVariable location variable ->
        at location <> "the source form contains the free variable " <> shown variable
    ElaborationApplicationExpectedFunction location actual ->
        at location <> "an application expected a function, but found " <> shown actual
    ElaborationApplicationArgumentMismatch location expected actual ->
        at location <> "an application expected " <> shown expected
            <> ", but found " <> shown actual
    ElaborationSelectionExpectedPredicate location actual ->
        at location <> "logical selection expected a predicate, but found "
            <> shown actual
    ElaborationSelectionTypeMismatch location expected actual ->
        at location <> "logical selection was annotated at " <> shown expected
            <> ", but its predicate selects " <> shown actual
    ElaborationEqualityOperandMismatch location leftType rightType ->
        at location <> "equality operands have different types: "
            <> shown leftType <> " and " <> shown rightType
    ElaborationExpressionExpectedSet location actual ->
        at location <> "an expression has type " <> shown actual <> " instead of Set"
    ElaborationNaturalNumeralBasisUnavailable location ->
        at location
            <> "a positive natural numeral requires the validated final-prelude successor"
    ElaborationNaturalNumeralMagnitudeExceeded location actual supportedMaximum ->
        at location <> "the natural numeral " <> shown actual
            <> " exceeds the supported maximum " <> shown supportedMaximum
    ElaborationFormulaExpectedProposition location actual ->
        at location <> "a formula has type " <> shown actual <> " instead of Prop"
    ElaborationCalculationFailed location failure ->
        at location <> "calculation elaboration failed: " <> Calculation.renderCalculationError failure

    ElaborationCoreCheckFailed location failure ->
        at location <> "the checked declaration core is invalid: " <> shown failure
    ElaborationCoreGlobalsMissing location identities ->
        at location
            <> "the checked declaration core refers to globals absent from its object closure: "
            <> shown (toList identities)
    ElaborationProspectiveObjectInvalid failure ->
        "an invocation-local object is invalid: " <> shown failure
    ElaborationProspectiveObjectMissing location identity ->
        at location <> "the datatype constructor object is absent from its local closure: "
            <> shown identity
    ElaborationObjectTypeMismatch location expected actual ->
        at location <> "the declaration object has type " <> shown actual
            <> " instead of " <> shown expected
    ElaborationUnsupportedHeaderAssumption location ->
        at location <> "this top-level header assumption is not yet supported by elaboration"
    ElaborationQuantifiedTermRequiresPropositionContext location ->
        at location
            <> "a quantified term requires a containing proposition"
    ElaborationStructureNotVisible location structurePhrase ->
        at location <> "the structure " <> shown structurePhrase <> " is not visible"
    ElaborationStructureParameterArityMismatch location structurePhrase expected actual ->
        at location <> "the structure " <> shown structurePhrase
            <> " expects " <> shown expected <> " parameters, but received "
            <> shown actual
    ElaborationStructureParameterPreambleMismatch location declared introduced ->
        at location <> "the structure phrase declares parameters "
            <> shown declared <> ", but its preamble introduces "
            <> shown introduced
    ElaborationStructureParameterDependencyViolation location available total ->
        at location <> "a structure-parameter premise may use only its "
            <> shown available <> " already introduced parameters, out of "
            <> shown total
    ElaborationBaseStructureNotAssertable location structurePhrase ->
        at location <> "the metadata-only structure " <> shown structurePhrase
            <> " cannot be asserted"
    ElaborationDuplicateStructureAnnotation location variable ->
        at location <> "the structure binder " <> shown variable
            <> " is annotated more than once"
    ElaborationStructureFieldNotAvailable location symbol ->
        at location <> "the structure field " <> shown symbol
            <> " is not available in the active structure scope"
    ElaborationStructureFieldAmbiguous location symbol objects ->
        at location <> "the structure field " <> shown symbol
            <> " is ambiguous between " <> shown objects
    ElaborationStructureReceiverAmbiguous location symbol receivers ->
        at location <> "the omitted structure field " <> shown symbol
            <> " is ambiguous between the active receivers "
            <> Text.intercalate ", " (NonEmpty.toList receivers)
            <> "; write an explicit structure receiver"
    ElaborationContextualExpansionNotAvailable location key ->
        at location <> "the contextual abbreviation " <> shown key
            <> " has no compatible active structure"
    ElaborationContextualReceiverAmbiguous location key receivers ->
        at location <> "the contextual abbreviation " <> shown key
            <> " is ambiguous between the active receivers "
            <> Text.intercalate ", " (NonEmpty.toList receivers)
            <> "; use an explicitly indexed underlying structure operation"
    ElaborationContextualRequirementConflict location symbol firstObject secondObject ->
        at location <> "the contextual abbreviation requires incompatible "
            <> shown symbol <> " field projections " <> shown firstObject
            <> " and " <> shown secondObject
    ElaborationStructureOccurrenceMismatch location ->
        at location <> "the structure syntax occurrences do not match the declaration"
    ElaborationStructureSelfParent location structurePhrase ->
        at location <> "the structure " <> shown structurePhrase
            <> " cannot inherit from itself"
    ElaborationStructureDuplicateParent location structurePhrase ->
        at location <> "the parent structure " <> shown structurePhrase
            <> " is repeated"
    ElaborationStructureAlreadyVisible location structurePhrase ->
        at location <> "the structure " <> shown structurePhrase
            <> " is already declared"
    ElaborationStructureDuplicateField location symbol ->
        at location <> "the structure field " <> shown symbol
            <> " is repeated"
    ElaborationStructureFieldAlreadyInherited location symbol ->
        at location <> "the structure field " <> shown symbol
            <> " is already inherited"
    ElaborationStructureFieldConflict location symbol firstOrigin secondOrigin ->
        at location <> "the inherited structure field " <> shown symbol
            <> " conflicts between " <> shown firstOrigin
            <> " and " <> shown secondOrigin
    ElaborationStructureCarrierUnavailable location structurePhrase ->
        at location <> "the structure " <> shown structurePhrase
            <> " has no carrier capability; name an explicit set-valued component"
    ElaborationStructureSchemaInvalid location Schema.LocalStructureReservedCarrier{} ->
        at location <> "the carrier field must be inherited from onesorted structure"
    ElaborationStructureSchemaInvalid location failure ->
        at location <> "the structure schema is inconsistent: " <> shown failure
    ElaborationStructureInterfaceNotVisible location identity ->
        at location <> "the structure notion refers to an unavailable interface "
            <> shown identity
    ElaborationStructureObjectNotVisible location identity ->
        at location <> "the structure fact mentions unavailable object "
            <> shown identity
    ElaborationStructureAggregateSchemaRequired location ->
        at location
            <> "an unannotated structure aggregate requires an immediate structure-predicate context"
    ElaborationRecordAggregateRequired location ->
        at location <> "expected a structure aggregate or a schema-directed reconstruction"
    ElaborationStructureAggregateMixedEntries location ->
        at location
            <> "a structure aggregate cannot mix positional and named fields"
    ElaborationStructureAggregateFieldArityMismatch
            location structurePhrase expected actual ->
        at location <> "the " <> shown structurePhrase
            <> " aggregate expects " <> shown expected
            <> " positional fields, but received " <> shown actual
    ElaborationStructureAggregateUnknownField location structurePhrase field ->
        at location <> "the " <> shown structurePhrase
            <> " aggregate has no field named " <> shown field
    ElaborationStructureAggregateDuplicateField location structurePhrase field ->
        at location <> "the " <> shown structurePhrase
            <> " aggregate repeats the field " <> shown field
    ElaborationStructureAggregateMissingFields location structurePhrase fields ->
        at location <> "the " <> shown structurePhrase
            <> " aggregate is missing the fields "
            <> shown (NonEmpty.toList fields)
    ElaborationReconstructionBaseUnavailable location target base reason ->
        at location <> "cannot reconstruct " <> fromMaybe "the requested structure" (renderSourceStructureApplication target)
            <> " from " <> fromMaybe "this base" (renderSourceExpression base) <> ". "
            <> renderReconstructionFailure reason
            <> " Establish the base's structure explicitly if formation cannot infer it."
  where
    at location = locationToText location <> ": "
    shown :: Show value => value -> Text
    shown = Text.pack . show

newtype BinderStack = BinderStack [CoreType]

binderStackTypes :: BinderStack -> [CoreType]
binderStackTypes (BinderStack types) = types

binderStackDepth :: BinderStack -> Natural
binderStackDepth = fromIntegral . length . binderStackTypes

data FormationScope = FormationScope
    { formationScopeSources :: ![FormationPremiseSource]
    , formationScopeEqualities :: ![FormationEqualitySource]
    , formationScopeAliases :: ![FormationAliasSource]
    , formationScopeEvidence :: !FormationEvidenceIndex
    , formationScopeCatalogs :: !(Maybe FormationScopeCatalogs)
    }

type ScopedFormationCatalog = FormationCatalog.Catalog
    (Either FormationRuleSource FormationCatalog.LocalProducerIx)

data FormationScopeCatalogs = FormationScopeCatalogs
    !PrefixContextId
    !ScopedFormationCatalog
    !ScopedFormationCatalog
    !ScopedFormationCatalog

-- Posting order is independent of query-time ordinals. Inserting a source
-- preserves all earlier entries and the order of views within that source.
type ObservationPosition = (Down Natural, Natural)

data FormationEvidenceIndex = FormationEvidenceIndex
    { evidenceLeaves :: !FormationLeaves.OpaqueLeaves
    , evidencePaths :: !ConjunctionProjections
    , evidenceFormulas :: !FormationFormulas.Formulas
    , evidenceSourceCount :: !Natural
    , evidenceWhole :: !(Map FormationFormulas.FormulaId (Map ObservationPosition WholeFormationObservation))
    -- Nothing admits an opaque source; Just retains the available atomic views.
    , evidenceWholeShapes :: !(Map Int [(FormationFormulas.ResidualShape, Maybe (Set FormationRule.AtomSignature), Set FormationFormulas.FormulaId)])
    , evidenceAtomicCount :: !Natural
    , evidenceExact :: !(Map (AtomTemplate FormationLeaves.OpaqueLeaf)
        (Map ObservationPosition (FormationObservation, ConjunctionProjection)))
    , evidenceHeads :: !(Map FormationRule.AtomSignature
        (Map ObservationPosition (FormationObservation, ConjunctionProjection)))
    , evidenceUniversals :: !(Seq.Seq PreparedFormationUniversal)
    , evidenceProducers :: !(Seq.Seq ScopedFormationProducer)
    , evidenceSupplied :: !(SuppliedUniversal.SuppliedIndex FormationLeaves.OpaqueLeaf Int)
    , evidenceEqualityCount :: !Natural
    , evidenceNextEquality :: !Natural
    , evidenceAllEqualities :: !ScopedEqualities
    , evidenceProofEqualities :: !ScopedEqualities
    , evidenceIntroducedEqualities :: !ScopedEqualities
    }

-- Whole identity never carries a rich row capability. Atomic and whole
-- postings select the same parent hypothesis and shared projection path.
data WholeFormationObservation = WholeFormationObservation
    !(ScopedCheckedCore ObjectId) !FormationSourceOrigin !ConjunctionProjection
    !(ScopedCheckedCore ObjectId, SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
    !(Maybe (ScopedCheckedCore ObjectId, SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence))

data EqualityPosition = ObservedEquality !ObservationPosition | AliasEquality !(Down Natural)
    deriving stock (Eq, Ord)

type FormationEqualityGraph = FormationEqualities.EqualityIndex FormationLeaves.OpaqueLeaf EqualityPosition
    (Natural, FormationEqualityTransport FormationSourceOrigin)

data ScopedEqualities = ScopedEqualities
    { scopedEqualityGraph :: !FormationEqualityGraph
    , scopedEqualityTerms :: !(Map EqualityPosition
        [(FormationLeaves.OpaqueLeaf, SetTermTemplate FormationLeaves.OpaqueLeaf)])
    , scopedOrdinaryEqualities :: !Natural
    }

emptyScopedEqualities :: ScopedEqualities
emptyScopedEqualities = ScopedEqualities FormationEqualities.emptyEqualityIndex Map.empty 0

consumerEqualities :: NotionQueryConsumer -> FormationEvidenceIndex -> ScopedEqualities
consumerEqualities = \case
    FormationNotionQuery -> evidenceAllEqualities
    DefinitionResultNotionQuery -> evidenceIntroducedEqualities
    ProofNotionQuery -> evidenceProofEqualities

data PreparedFormationUniversal = PreparedFormationUniversal
    ![CoreType]
    !FormationSourceOrigin
    !(FormationSourceEvidence FormationSourceOrigin)

data ScopePreparation = ScopePreparation
    { scopeWorkLimit :: !Word
    , scopeWorkRemaining :: !Word
    , scopeWorkDiagnostics :: !FormationDiagnostics.Diagnostics
    , scopeRejectedDebit :: !(Maybe Natural)
    }

type FormationScopePreparation = ExceptT FormationObservationError (State.State ScopePreparation)

scopePreparationExhausted :: FormationScopePreparation value
scopePreparationExhausted = do
    limit <- State.gets scopeWorkLimit
    Except.throwError (FormationScopePreparationLimitExceeded (fromIntegral limit))

scopePreparationCharge :: Natural -> FormationScopePreparation ()
scopePreparationCharge amount = do
    available <- State.gets scopeWorkRemaining
    if amount <= fromIntegral available
    then State.modify' (\current -> current {scopeWorkRemaining = available - fromIntegral amount})
    else do
        State.modify' (\current -> current {scopeRejectedDebit = Just amount})
        scopePreparationExhausted

scopePreparationCount :: FormationDiagnostics.Operation -> Natural -> FormationScopePreparation ()
scopePreparationCount operation amount = State.modify' (\current -> current
    {scopeWorkDiagnostics = FormationDiagnostics.countOperation operation amount (scopeWorkDiagnostics current)})

scopePreparationCore
    :: Show failure => (Word -> (Either (CountedCoreFailure failure) value, Word))
    -> FormationScopePreparation value
scopePreparationCore operation = do
    available <- State.gets scopeWorkRemaining
    let (result, remaining) = operation available
    scopePreparationCoreSpent available remaining
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> scopePreparationExhausted
        Left (CountedCoreOperationFailed failure) -> Except.throwError
            (FormationObservationScopeError (Text.pack (show failure)))

scopePreparationCoreSpent :: Word -> Word -> FormationScopePreparation ()
scopePreparationCoreSpent available remaining = State.modify' (\current -> current
    { scopeWorkRemaining = remaining
    , scopeWorkDiagnostics = FormationDiagnostics.countCoreWork FormationDiagnostics.ScopePreparation
        (fromIntegral (available - remaining)) (scopeWorkDiagnostics current) })

scopePreparationLeaves
    :: (Word -> (Either FormationLeaves.OpaqueLeafFailure value, Word))
    -> FormationScopePreparation value
scopePreparationLeaves operation = do
    available <- State.gets scopeWorkRemaining
    let (result, remaining) = operation available
    State.modify' (\current -> current {scopeWorkRemaining = remaining})
    case result of
        Right value -> pure value
        Left FormationLeaves.OpaqueLeafWorkExhausted -> scopePreparationExhausted
        Left _ -> Except.throwError (FormationObservationScopeError
            "a formation index term disagrees with its scope")

scopePreparationFormulas
    :: (Word -> (Either FormationFormulas.FormulaFailure value, Word))
    -> FormationScopePreparation value
scopePreparationFormulas operation = do
    available <- State.gets scopeWorkRemaining
    let (result, remaining) = operation available
    State.modify' (\current -> current {scopeWorkRemaining = remaining})
    case result of
        Right value -> pure value
        Left (FormationFormulas.FormulaWorkExhausted debit) -> do
            State.modify' (\current -> current {scopeRejectedDebit = Just debit})
            scopePreparationExhausted
        Left _ -> Except.throwError (FormationObservationScopeError
            "a whole proposition index disagrees with its checked source scope")

runFormationScopePreparation
    :: FormationScopePreparation value -> (Either FormationObservationError value, FormationDiagnostics.Measurement)
runFormationScopePreparation = runFormationScopePreparationWithWork defaultScopePreparationWork

runFormationScopePreparationWithWork
    :: Word -> FormationScopePreparation value -> (Either FormationObservationError value, FormationDiagnostics.Measurement)
runFormationScopePreparationWithWork limit action =
    let (result, final) = State.runState (Except.runExceptT action)
            (ScopePreparation limit limit FormationDiagnostics.emptyDiagnostics Nothing)
        used = fromIntegral (scopeWorkLimit final - scopeWorkRemaining final)
        measured = FormationDiagnostics.emptyMeasurement
            { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork
                FormationDiagnostics.ScopePreparation used (scopeWorkDiagnostics final)
            , FormationDiagnostics.limitHighWater = Map.fromList
                ([ ("scope-preparation.used", used)
                 , ("scope-preparation.cap", fromIntegral (scopeWorkLimit final)) ]
                    <> maybe [] (\debit -> [("scope-preparation.rejected", debit)]) (scopeRejectedDebit final)) }
    in (result, measured)

finishFormationScopePreparation
    :: FormationScopePreparation value -> Declaration.LoweringDriver (Either FormationObservationError value)
finishFormationScopePreparation action = Declaration.withFormationPhaseLowering FormationDiagnostics.ScopePreparation do
    let (result, measured) = runFormationScopePreparation action
    recorder <- Declaration.formationRecorderLowering
    -- Demand the owner even when reporting is disabled, before returning its
    -- immutable index. No preparation thunk is moved into a later query.
    result `seq` liftIO (FormationDiagnostics.recordMeasurement recorder measured)
    pure result

emptyFormationEvidenceIndex :: FormationEvidenceIndex
emptyFormationEvidenceIndex = FormationEvidenceIndex
    (FormationLeaves.emptyOpaqueLeaves []) emptyConjunctionProjections
    (FormationFormulas.emptyFormulas []) 0 Map.empty Map.empty 0 Map.empty Map.empty
    Seq.empty Seq.empty SuppliedUniversal.emptySuppliedIndex
    0 0 emptyScopedEqualities emptyScopedEqualities emptyScopedEqualities

defaultScopePreparationWork :: Word
defaultScopePreparationWork = 262144

-- Source admission and index preparation share one allowance. A failure
-- returns no partially prepared scope. Query alignment uses these admitted
-- observations instead of revalidating every source and conjunction path.
indexFormationSource
    :: [CoreType] -> Vector (LocalId, CoreType) -> [FormationAliasSource] -> FormationPremiseSource
    -> FormationEvidenceIndex
    -> FormationScopePreparation FormationEvidenceIndex
indexFormationSource types support aliases
        source@(FormationPremiseSource sourceSupport proposition evidence origin) initial = prepare
  where
    prepare = do
        parent <- prepareScopeSourceParent types support sourceSupport proposition
        annotations <- SourceEvidence.sourceInputAnnotationsWith (scopePreparationCharge 1) evidence
        let inputOwner = if null annotations then Nothing else Just (proposition,SourceInputs Nothing annotations)
        (views, paths) <- State.runStateT
            (SourceEvidence.notionLeaves (State.lift (scopePreparationCharge 1))
                (extendConjunctionProjection scopePreparationCharge)
                rootConjunctionProjection proposition evidence) (evidencePaths initial)
        -- Admission aligns each selected formula once. Both exact indexes use
        -- that value; the universal body retains its original binder context.
        prepared <- for views \view -> do
            let align scoped = scopePreparationCore (\work -> countedAlignScopedCore work types scoped)
                    >>= maybe (invalid "a source leaf escaped its scope") pure
                alignTerm term = scopePreparationCore (\work ->
                    SourceTerm.countedAlignScopedSourceTermOccurrence work types term)
                    >>= maybe (invalid "a source argument escaped its scope") pure
                path = SourceEvidence.sourceLeafPath view
            selected <- align (SourceEvidence.sourceLeafFormula view)
            observation <- case SourceEvidence.sourceLeafDescription view of
                SourceEvidence.LeafAtom atom -> do
                    aligned <- traverseSourceNotionAssertionParts alignTerm align atom
                    same <- scopePreparationCore (\work -> countedScopedCoreIdentity work selected (sourceAssertionFormula aligned))
                    unless (same && sourceAssertionPath atom == ConjunctionHere)
                        (invalid "a source atom does not denote its selected Core leaf")
                    pure (Just (path, mapSourceNotionAssertionPath
                        (const (conjunctionProjectionPath path)) aligned))
                _ -> pure Nothing
            let inputs = (SourceEvidence.sourceLeafFormula view,SourceEvidence.sourceLeafEvidence view)
            pure ((selected, path, inputs), observation)
        let observations = mapMaybe snd prepared
        leaves <- scopePreparationLeaves (\work -> FormationLeaves.extendOpaqueLeaves work types (evidenceLeaves initial))
        let finalCount = evidenceAtomicCount initial + fromIntegral (length observations)
        atomic <- foldM (insert parent finalCount) initial
            { evidenceLeaves = leaves, evidenceAtomicCount = finalCount, evidencePaths = paths }
            (zip [0..] observations)
        formulas <- scopePreparationFormulas (\work -> FormationFormulas.extendFormulas work types (evidenceFormulas atomic))
        let sourceOrdinal = evidenceSourceCount atomic
        whole <- foldM (insertWhole parent inputOwner sourceOrdinal) atomic
            { evidenceFormulas = formulas
            , evidenceSourceCount = sourceOrdinal + if null views then 0 else 1 }
            (zip [0..] prepared)
        prepareScopeSources types support aliases parent source views whole
    insertWhole parent inputOwner sourceOrdinal index (ordinal, ((formula, path, inputs), atomic)) = do
        (identifier, formulas) <- scopePreparationFormulas (\work ->
            FormationFormulas.internFormula work formula (evidenceFormulas index))
        (shape,preparedFormulas) <- scopePreparationFormulas (\work ->
            FormationFormulas.prepareFormulaShape work identifier formulas)
        value <- maybe (invalid "a supplied whole proposition lost its formula") pure shape
        let digest = FormationFormulas.residualShapeHash value
            known = evidenceWholeShapes index
            shapes = Map.findWithDefault [] digest known
            views = Set.singleton . FormationRule.atomSignature . sourceAssertionAtom . snd <$> atomic
            insertShape [] = do
                scopePreparationCharge 1
                pure [(value,views,Set.singleton identifier)]
            insertShape ((candidate,knownViews,identifiers):rest) = do
                scopePreparationCharge (FormationFormulas.residualShapeWork value)
                if candidate == value then do
                    scopePreparationCharge (FormationTerms.indexWork (Set.size identifiers) 1)
                    scopePreparationCharge (maybe 0 (\heads -> FormationTerms.indexWork (Set.size heads) 3) knownViews)
                    pure ((candidate,Set.union <$> knownViews <*> views,Set.insert identifier identifiers):rest)
                else ((candidate,knownViews,identifiers):) <$> insertShape rest
        scopePreparationCharge (2 * FormationTerms.indexWork (Map.size known) 1)
        updatedShapes <- insertShape shapes
        let postings = evidenceWhole index
            bucket = Map.findWithDefault Map.empty identifier postings
            position = (Down sourceOrdinal, ordinal)
            observation = WholeFormationObservation parent origin path inputs inputOwner
        scopePreparationCharge (FormationTerms.indexWork (Map.size postings) 1
            + FormationTerms.indexWork (Map.size bucket) 1)
        pure index { evidenceFormulas = preparedFormulas
            , evidenceWholeShapes = Map.insert digest updatedShapes known
            , evidenceWhole = Map.insert identifier (Map.insert position observation bucket) postings }
    invalid = Except.throwError . FormationObservationScopeError
    insert parent finalCount index (ordinal, (path, assertion)) = do
        let observation = FormationObservation parent assertion origin ordinal
        (key, leaves) <- State.runStateT
            (traverseAtomTemplateArguments (\argument -> do
                known <- State.get
                (identifier, next) <- Trans.lift (scopePreparationLeaves (\work ->
                    FormationLeaves.internOpaqueLeaf work
                        (SourceTerm.sourceTermOccurrenceCore argument) known))
                State.put next
                pure identifier) (sourceAssertionAtom assertion)) (evidenceLeaves index)
        let signature = FormationRule.atomSignature key
            position = (Down finalCount, formationObservationOrdinal observation)
            exact = evidenceExact index
            heads = evidenceHeads index
            exactBucket = Map.findWithDefault Map.empty key exact
            headBucket = Map.findWithDefault Map.empty signature heads
        scopePreparationCharge (FormationTerms.indexWork (Map.size exact) (1 + fromIntegral (length (toList key)))
            + FormationTerms.indexWork (Map.size heads) 1
            + FormationTerms.indexWork (Map.size exactBucket) 1
            + FormationTerms.indexWork (Map.size headBucket) 1)
        pure index
            { evidenceLeaves = leaves
            , evidenceExact = Map.insert key (Map.insert position (observation, path) exactBucket) exact
            , evidenceHeads = Map.insert signature (Map.insert position (observation, path) headBucket) heads
            }

prepareScopeSourceParent
    :: [CoreType] -> Vector (LocalId, CoreType) -> Maybe (Vector (LocalId, CoreType))
    -> ScopedCheckedCore ObjectId -> FormationScopePreparation (ScopedCheckedCore ObjectId)
prepareScopeSourceParent types support sourceSupport proposition = do
    for_ sourceSupport \original -> do
        let difference = Vector.length support - Vector.length original
        require (difference >= 0) "a formation source escaped its proof binder scope"
        for_ (Vector.zip original (Vector.drop difference support)) \((oldId, oldType), (newId, newType)) -> do
            scopePreparationCharge 1
            same <- scopePreparationCore (\work -> countedCoreTypeIdentity work oldType newType)
            require (oldId == newId && same) "a formation source escaped its nominal proof scope"
        same <- scopePreparationCore (\work -> countedCoreTypeListIdentity work
            (scopedCoreContext proposition) (snd <$> toList original))
        require same "a formation source disagrees with its nominal scope"
    scopePreparationCore (\work -> countedAlignScopedCore work types proposition)
        >>= maybe (invalid "a formation source is outside the current scope") pure
  where
    invalid = Except.throwError . FormationObservationScopeError
    require valid message = unless valid (invalid message)

prepareScopeEqualities
    :: [CoreType] -> Vector (LocalId, CoreType) -> [FormationAliasSource]
    -> FormationEqualitySource -> FormationEvidenceIndex
    -> FormationScopePreparation FormationEvidenceIndex
prepareScopeEqualities types support aliasSources
        (FormationEqualitySource sourceSupport proposition equalities origin) initial = do
    parent <- prepareScopeSourceParent types support sourceSupport proposition
    aliases <- scopePreparationCore (\work -> countedFormationAliasSources work FormationNotionQuery
        types support aliasSources)
    leaves <- scopePreparationLeaves (\work -> FormationLeaves.extendOpaqueLeaves work types (evidenceLeaves initial))
    let total = evidenceEqualityCount initial + fromIntegral (NonEmpty.length equalities)
    foldM (insert parent aliases total)
        initial {evidenceLeaves = leaves, evidenceEqualityCount = total} (zip [0..] (toList equalities))
  where
    invalid = Except.throwError . FormationObservationScopeError
    insert parent aliases total index (offset, occurrence) = do
        let align scoped = scopePreparationCore (\work -> countedAlignScopedCore work types scoped)
                >>= maybe (invalid "an equality escaped its source scope") pure
            alignTerm term = scopePreparationCore (\work -> SourceTerm.countedAlignScopedSourceTermOccurrence work types term)
                >>= maybe (invalid "an equality endpoint escaped its source scope") pure
        aligned <- traverseSourceEqualityOccurrenceParts alignTerm align occurrence
        let equality = sourceEqualityFormula aligned
            left = sourceEqualityLeft aligned
            right = sourceEqualityRight aligned
        projected <- projectScopeConjunction (sourceEqualityPath aligned) parent
        same <- scopePreparationCore (\work -> countedScopedCoreIdentity work projected equality)
        unless same (invalid "an equality view does not select its source")
        case splitScopedEquality equality of
            Just (TySet, actualLeft, actualRight) -> do
                matchesLeft <- scopePreparationCore (\work -> countedScopedCoreIdentity work
                    actualLeft (SourceTerm.sourceTermOccurrenceCore left))
                matchesRight <- scopePreparationCore (\work -> countedScopedCoreIdentity work
                    actualRight (SourceTerm.sourceTermOccurrenceCore right))
                unless (matchesLeft && matchesRight) (invalid "an equality view has different source operands")
            _ -> invalid "a formation equality must compare sets"
        insertScopeEquality types aliases (ObservedEquality (Down total, offset))
            (DirectFormationSource parent (sourceEqualityPath aligned) origin (evidenceNextEquality index))
            equality [left, right] index

prepareScopeAlias
    :: [CoreType] -> Vector (LocalId, CoreType) -> [FormationAliasSource]
    -> FormationAliasSource -> FormationEvidenceIndex
    -> FormationScopePreparation FormationEvidenceIndex
prepareScopeAlias types support prior source@(FormationAliasSource _ sourceSupport root _ location) initial = do
    let hypothesis = formationAliasSourceOwnHypothesis source
        ordinal = formationDefinitionOrdinal hypothesis
    equality <- prepareScopeSourceParent types support (Just sourceSupport)
        (materializedNotionHypothesisProposition hypothesis)
    aliases <- scopePreparationCore (\work -> countedFormationAliasSources work FormationNotionQuery
        types support (source : prior))
    leaves <- scopePreparationLeaves (\work -> FormationLeaves.extendOpaqueLeaves work types (evidenceLeaves initial))
    case splitScopedEquality equality of
        Just (TySet, target, _) -> do
            let occurrence = SourceTerm.sourceTermOccurrence target TySet (LocatedSourceTerm location)
            insertScopeEquality types aliases (AliasEquality (Down ordinal))
                (DirectFormationSource equality ConjunctionHere
                    (materializedNotionHypothesisOrigin hypothesis) (evidenceNextEquality initial))
                equality [occurrence, root] initial {evidenceLeaves = leaves}
        _ -> impossible "an admitted local alias lost its defining equality"

insertScopeEquality
    :: [CoreType] -> AlignedFormationAliases -> EqualityPosition
    -> DirectFormationSource FormationSourceOrigin -> ScopedCheckedCore ObjectId
    -> [ScopedSourceTerm] -> FormationEvidenceIndex
    -> FormationScopePreparation FormationEvidenceIndex
insertScopeEquality types aliases position source equality terms index = do
    let ordinal = evidenceNextEquality index
        transport direction = fromMaybe (impossible "an admitted equality lost its source path")
            (formationEqualityTransport source equality direction)
        forward = transport FormationEqualityLeftToRight
        backward = transport FormationEqualityRightToLeft
    (left, right) <- case splitScopedEquality equality of
        Just (TySet, firstTerm, secondTerm) -> pure (firstTerm, secondTerm)
        _ -> impossible "an admitted equality ceased to compare sets"
    ((leftId, rightId, represented), leaves) <- State.runStateT (do
        firstId <- intern left
        secondId <- intern right
        represented <- for terms \term -> do
            (viewed, _) <- State.lift (scopePreparationCore (\work -> countedViewFormationAliases work aliases term))
            identifier <- intern (SourceTerm.sourceTermOccurrenceCore viewed)
            known <- State.get
            (template, next) <- State.lift (scopePreparationCore (\work -> FormationRows.encodeSourceTerm work types viewed known))
            State.put next
            pure (identifier, template)
        pure (firstId, secondId, represented)) (evidenceLeaves index)
    let insert original = do
            graph <- FormationEqualities.insertEquality scopePreparationCharge position leftId rightId
                (ordinal, forward) (ordinal, backward) (scopedEqualityGraph original)
            scopePreparationCharge (FormationTerms.indexWork (Map.size (scopedEqualityTerms original)) 1)
            pure original
                { scopedEqualityGraph = graph
                , scopedEqualityTerms = Map.insert position represented (scopedEqualityTerms original)
                , scopedOrdinaryEqualities = scopedOrdinaryEqualities original + case position of
                    ObservedEquality{} -> 1
                    AliasEquality{} -> 0
                }
    allSources <- insert (evidenceAllEqualities index)
    proofSources <- if notionQueryAdmitsOrigin ProofNotionQuery (directSourceOrigin source)
        then insert (evidenceProofEqualities index) else pure (evidenceProofEqualities index)
    introducedSources <- case directSourceOrigin source of
        FormationFromGoalAssumption{} -> insert (evidenceIntroducedEqualities index)
        _ -> pure (evidenceIntroducedEqualities index)
    pure index
        { evidenceLeaves = leaves, evidenceNextEquality = ordinal + 1
        , evidenceAllEqualities = allSources, evidenceProofEqualities = proofSources
        , evidenceIntroducedEqualities = introducedSources
        }
  where
    intern scoped = do
        known <- State.get
        (identifier, next) <- State.lift (scopePreparationLeaves (\work -> FormationLeaves.internOpaqueLeaf work scoped known))
        State.put next
        pure identifier

-- Local clauses retain their checked source and fixed lexical captures. The
-- supplied-universal adapter is optional execution data for the same source.
prepareScopeSources
    :: [CoreType] -> Vector (LocalId, CoreType) -> [FormationAliasSource]
    -> ScopedCheckedCore ObjectId -> FormationPremiseSource
    -> [SourceEvidence.SourceLeaf ConjunctionProjection (ScopedCheckedCore ObjectId) SupportTermTemplate ScopedSourceNotionOccurrence]
    -> FormationEvidenceIndex -> FormationScopePreparation FormationEvidenceIndex
prepareScopeSources types support aliasSources parent source views initial = do
    sources <- fmap catMaybes $ for views \view -> do
        scopePreparationCharge 1
        pure (case SourceEvidence.sourceLeafEvidence view of
            SourceEvidence.SourceBind{} -> Just view
            SourceEvidence.SourceRequire{} -> Just view
            SourceEvidence.SourceIff{} -> Just view
            _ -> Nothing)
    if null sources then pure initial else do
        aliases <- scopePreparationCore (\work -> countedFormationAliasSources work FormationNotionQuery types support aliasSources)
        (prepared,described) <- foldM (insert aliases) (initial,[]) sources
        supplied <- SuppliedUniversal.insertSuppliedSources scopePreparationCharge (reverse described) (evidenceSupplied initial)
        pure prepared {evidenceSupplied = supplied}
  where
    insert aliases (index,descriptions) view = do
        let identifier = Seq.length (evidenceUniversals index)
            path = conjunctionProjectionPath (SourceEvidence.sourceLeafPath view)
            selected = SourceEvidence.sourceLeafFormula view
            retained = DirectFormationSource parent path origin (fromIntegral identifier)
            origin = case source of FormationPremiseSource _ _ _ value -> value
        (proof,formula,evidence) <- normalizeScopeSource types aliases retained selected (SourceEvidence.sourceLeafEvidence view)
        (projections,introductions,described,leaves) <- scopePreparationCore (\work -> ScopedSource.compileScopedSource work types
            (scopedCoreContext formula) (scopedCoreTerm formula) evidence (evidenceLeaves index))
        let producers = Seq.fromList
                ([ScopedFormationProducer identifier projection | projection <- projections] <>
                 [ScopedFormationIntroduction (Just identifier) introduction | introduction <- introductions])
            count = fromIntegral (Seq.length producers)
        scopePreparationCount FormationDiagnostics.ProducerCompilation count
        -- Compilation has already paid its internal work. Publication pays
        -- for the source entry and every producer installed from that source.
        scopePreparationCharge (1 + count)
        pure (index
            { evidenceLeaves = leaves
            , evidenceUniversals = evidenceUniversals index Seq.|> PreparedFormationUniversal types origin proof
            , evidenceProducers = evidenceProducers index Seq.>< producers }
            , maybe descriptions (\body -> (identifier,body):descriptions) described)

projectScopeConjunction
    :: ConjunctionPath -> ScopedCheckedCore ObjectId
    -> FormationScopePreparation (ScopedCheckedCore ObjectId)
projectScopeConjunction path proposition = do
    scopePreparationCharge 1
    case path of
        ConjunctionHere -> pure proposition
        ConjunctionLeft rest -> select fst rest
        ConjunctionRight rest -> select snd rest
  where
    select side rest = case splitScopedConjunction proposition of
        Nothing -> Except.throwError (FormationObservationScopeError
            "a universal view does not project its source")
        Just pair -> projectScopeConjunction rest (side pair)

normalizeScopeSource
    :: [CoreType] -> AlignedFormationAliases -> DirectFormationSource FormationSourceOrigin
    -> ScopedCheckedCore ObjectId -> SourceEvidence.SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> FormationScopePreparation (FormationSourceEvidence FormationSourceOrigin,
        ScopedCheckedCore ObjectId,SourceEvidence.SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
normalizeScopeSource _ (AlignedFormationAliases []) retained original evidence =
    pure (directFormationSourceEvidence retained,original,evidence)
normalizeScopeSource ambient aliases@(AlignedFormationAliases entries) retained original evidence = do
    let rootDefinitions = Map.fromList
            [(formationDefinitionOrdinal definition, definition) | AlignedFormationAlias _ _ chain _ <- entries,
                definition <- toList chain]
    (viewed, used) <- State.runStateT (SourceEvidence.traverseSourceAtDepth
        (\depth -> traverse (\term -> State.lift (scopePreparationCore (\work -> countedShiftCanonical work
            (fromIntegral (length ambient - length (scopedCoreContext original))) depth term)))) (\depth occurrence -> do
        let targetContext = replicate (fromIntegral depth) TySet <> ambient
            align scoped = scopePreparationCore (\work -> countedAlignScopedCoreAt work depth targetContext scoped)
                >>= maybe (impossible "a universal alias escaped its source scope") pure
            alignTerm term = scopePreparationCore (\work -> SourceTerm.countedAlignScopedSourceTermOccurrenceAt work depth targetContext term)
                >>= maybe (impossible "a universal term escaped its source scope") pure
        aligned <- State.lift (traverseSourceNotionAssertionParts alignTerm align occurrence)
        nestedAliases <- State.lift $ AlignedFormationAliases <$> for entries (\(AlignedFormationAlias target root chain at) -> do
            let alignAmbient scoped = scopePreparationCore (\work -> countedAlignScopedCore work targetContext scoped)
                    >>= maybe (impossible "an alias lost its ambient scope") pure
            target' <- alignAmbient target
            root' <- scopePreparationCore (\work -> SourceTerm.countedAlignScopedSourceTermOccurrence work targetContext root)
                >>= maybe (impossible "an alias root lost its ambient scope") pure
            chain' <- for chain (\definition -> do
                proposition <- alignAmbient (materializedNotionHypothesisProposition definition)
                pure (materializedNotionHypothesis proposition (materializedNotionHypothesisOrigin definition)))
            pure (AlignedFormationAlias target' root' chain' at))
        (atom, definitions) <- State.lift (prepareAliasAtom nestedAliases (sourceAssertionAtom aligned))
        for_ (Map.keys definitions) \ordinal -> do
            known <- State.get
            State.lift (scopePreparationCharge (FormationTerms.indexWork (Set.size known) 1))
            State.put (Set.insert ordinal known)
        normalized <- State.lift (scopePreparationCore (\work -> countedNormalizeFormationAliases work nestedAliases (sourceAssertionFormula aligned)))
        let rebuilt = sourceNotionAssertionFromTemplate atom (formationAliasNormalizationResult normalized)
                (sourceAssertionPath aligned) (sourceAssertionLocation aligned)
        pure (maybe rebuilt (`withSourceNotionOrigin` rebuilt) (sourceNotionWrittenOrigin aligned))) evidence) Set.empty
    definitions <- fmap Map.fromList $ for (Set.toAscList used) \ordinal -> do
        scopePreparationCharge (FormationTerms.indexWork (Map.size rootDefinitions) 1)
        definition <- maybe (impossible "a universal alias lost its root definition") pure (Map.lookup ordinal rootDefinitions)
        pure (ordinal, definition)
    (normalization, steps) <- prepareAliasSteps aliases original definitions
    substitutions <- prepareAliasSubstitutions FormationEqualityLeftToRight steps
    proof <- case NonEmpty.nonEmpty substitutions of
        Nothing -> pure (directFormationSourceEvidence retained)
        Just nonempty -> either (Except.throwError . FormationObservationExhausted) pure
            (transportFormationSourceWithLimits defaultFormationSearchLimits retained nonempty original
                (formationAliasNormalizationResult normalization))
    pure (proof,formationAliasNormalizationResult normalization,viewed)

formationDefinitionOrdinal :: MaterializedNotionHypothesis FormationSourceOrigin -> Natural
formationDefinitionOrdinal definition = case materializedNotionHypothesisOrigin definition of
    FormationFromProofLocal ordinal FormationProofLocalDefinition -> ordinal
    _ -> impossible "a formation alias lost its definition origin"

prepareAliasAtom
    :: AlignedFormationAliases -> AtomTemplate ScopedSourceTerm
    -> FormationScopePreparation (AtomTemplate ScopedSourceTerm, Map Natural (MaterializedNotionHypothesis FormationSourceOrigin))
prepareAliasAtom aliases atom = State.runStateT
    (traverseAtomTemplateArguments (\term -> do
        (viewed, definitions) <- State.lift (scopePreparationCore (\work -> countedViewFormationAliases work aliases term))
        for_ definitions \definition -> do
            retained <- State.get
            State.lift (scopePreparationCharge (FormationTerms.indexWork (Map.size retained) 1))
            State.put (Map.insert (formationDefinitionOrdinal definition) definition retained)
        pure viewed) atom) Map.empty

prepareAliasSteps
    :: AlignedFormationAliases -> ScopedCheckedCore ObjectId
    -> Map Natural (MaterializedNotionHypothesis FormationSourceOrigin)
    -> FormationScopePreparation (FormationAliasNormalization,
        [(MaterializedNotionHypothesis FormationSourceOrigin, ScopedCheckedCore ObjectId)])
prepareAliasSteps aliases original definitions = do
    normalization <- scopePreparationCore (\work -> countedNormalizeFormationAliases work aliases original)
    let logical = formationAliasNormalizationReplaySteps normalization
        steps = [(formationAliasReplayStepDefinition step, formationAliasReplayStepAbstraction step) | step <- logical]
    used <- foldM (\known (definition, _) -> do
        scopePreparationCharge (FormationTerms.indexWork (Set.size known) 1)
        pure (Set.insert (formationDefinitionOrdinal definition) known)) Set.empty steps
    missing <- fmap catMaybes $ for (Map.toAscList definitions) \(ordinal, definition) -> do
        scopePreparationCharge (FormationTerms.indexWork (Set.size used) 1)
        pure (if Set.member ordinal used then Nothing else Just definition)
    -- An erased source argument still underwent a checked substitution.
    -- Its erased predicate is constant, but replay must retain the equality
    -- that authorized exposing the argument's source construction.
    extra <- if null missing then pure [] else do
        weakened <- scopePreparationCore (\work -> countedWeakenCheckedScopedCore work TySet
            (formationAliasNormalizationResult normalization))
        scopePreparationCharge 1
        predicate <- maybe (impossible "an alias predicate could not be abstracted") pure
            (abstractScopedCore TySet weakened)
        pure [(definition, predicate) | definition <- missing]
    pure (normalization, steps <> extra)

prepareAliasSubstitutions
    :: FormationEqualityDirection
    -> [(MaterializedNotionHypothesis FormationSourceOrigin, ScopedCheckedCore ObjectId)]
    -> FormationScopePreparation [(FormationEqualityTransport FormationSourceOrigin, ScopedCheckedCore ObjectId)]
prepareAliasSubstitutions direction steps = for steps \(definition, predicate) -> do
    scopePreparationCharge 1
    let proposition = materializedNotionHypothesisProposition definition
        source = DirectFormationSource proposition ConjunctionHere
            (materializedNotionHypothesisOrigin definition) (formationDefinitionOrdinal definition)
    transport <- maybe (impossible "a checked alias ceased to be a set equality") pure
        (formationEqualityTransport source proposition direction)
    pure (transport, predicate)

-- | The source-lifetime boundary of one notion query. Ordinary formation may
-- reuse the active lexical scope caches. Retained proof and definition-result
-- queries receive fresh scopes whose sources have already been filtered.
data NotionQueryConsumer
    = FormationNotionQuery
    | DefinitionResultNotionQuery
    | ProofNotionQuery
    deriving stock (Show, Eq)

formationScopeFromContext :: ElaborationContext -> FormationScope
formationScopeFromContext (ElaborationContext _ _ scope) = scope

emptyFormationScope :: FormationScope
emptyFormationScope = FormationScope [] [] [] emptyFormationEvidenceIndex Nothing

extendFormationScope
    :: [CoreType]
    -> Vector (LocalId, CoreType)
    -> FormationPremiseSource
    -> FormationScope
    -> FormationScopePreparation FormationScope
extendFormationScope types support source scope = do
    scopePreparationCount FormationDiagnostics.ScopeInsertion 1
    let original = formationScopeEvidence scope
    prepared <- indexFormationSource types support (formationScopeAliases scope) source original
    catalogs <- traverse (extendScopeCatalogs (Seq.length (evidenceProducers original)) prepared)
        (formationScopeCatalogs scope)
    pure $ if evidenceSourceCount prepared == evidenceSourceCount original then scope else scope
        { formationScopeSources = source : formationScopeSources scope
        , formationScopeEvidence = prepared
        , formationScopeCatalogs = catalogs
        }

-- Physical slots belong to this prefix. Source handles remain stable when a
-- new declaration base is installed. Local producers use introduction order
-- in every overlay; direct and supplied-source preference use their postings.
extendScopeCatalogs
    :: Int -> FormationEvidenceIndex -> FormationScopeCatalogs
    -> FormationScopePreparation FormationScopeCatalogs
extendScopeCatalogs start index (FormationScopeCatalogs prefix allSources definitionSources proofSources) = do
    entries <- for (zip [start..] (toList (Seq.drop start (evidenceProducers index))))
        \(identifier, producer) -> do
            let source = case producer of
                    ScopedFormationProducer source' _ -> source'
                    ScopedFormationIntroduction (Just source') _ -> source'
                    ScopedFormationIntroduction Nothing _ -> impossible "a query introduction escaped into the lexical source index"
                    WholeFormationElimination{} -> impossible "a query elimination escaped into the lexical source index"
            scopePreparationCharge (FormationTerms.indexWork (Seq.length (evidenceUniversals index)) 1)
            let PreparedFormationUniversal _ origin _ = Seq.index (evidenceUniversals index) source
            pure (origin, (Right (FormationCatalog.LocalProducerIx identifier),
                FormationRule.RegisteredClassification (scopedProducerRule producer)))
    allSources' <- FormationCatalog.insertRules scopePreparationCharge (snd <$> entries) allSources
    definitionSources' <- insert DefinitionResultNotionQuery entries definitionSources
    proofSources' <- insert ProofNotionQuery entries proofSources
    pure (FormationScopeCatalogs prefix allSources' definitionSources' proofSources')
  where
    insert consumer entries catalog = do
        selected <- fmap catMaybes $ for entries \(origin, entry) -> do
            scopePreparationCharge 1
            pure (if notionQueryAdmitsOrigin consumer origin then Just entry else Nothing)
        FormationCatalog.insertRules scopePreparationCharge selected catalog

prepareFormationScopeCatalogs
    :: PrefixContextId -> ScopedFormationCatalog -> FormationScope
    -> FormationScopePreparation FormationScope
prepareFormationScopeCatalogs prefix base scope = case formationScopeCatalogs scope of
    Just (FormationScopeCatalogs admitted _ _ _) | admitted == prefix -> pure scope
    _ -> do
        scopePreparationCount FormationDiagnostics.ScopeRebase 1
        catalogs <- extendScopeCatalogs 0 (formationScopeEvidence scope)
            (FormationScopeCatalogs prefix base base base)
        pure scope {formationScopeCatalogs = Just catalogs}

prepareFormationContext
    :: Location -> ElaborationContext
    -> ExceptT ElaborationError Declaration.LoweringDriver ElaborationContext
prepareFormationContext location (ElaborationContext binders overrides scope) = do
    (prefix, base) <- Trans.lift Declaration.formationCatalogSnapshotLowering
    prepared <- Trans.lift (finishFormationScopePreparation (prepareFormationScopeCatalogs prefix base scope))
        >>= either (Except.throwError . ElaborationFormationScopeFailed location) pure
    pure (ElaborationContext binders overrides prepared)

acquireFormationCatalogs :: Location -> Elaborate (FormationScopeCatalogs, ScopedFormationCatalog)
acquireFormationCatalogs location = do
    (prefix, base) <- State.lift (Trans.lift Declaration.formationCatalogSnapshotLowering)
    scope <- State.gets (lexicalFormationScope . elaborationScope)
    prepared <- State.lift (Trans.lift (finishFormationScopePreparation (prepareFormationScopeCatalogs prefix base scope)))
        >>= either (Except.throwError . ElaborationFormationScopeFailed location) pure
    modifyLexicalScope (\lexical -> lexical {lexicalFormationScope = prepared})
    case formationScopeCatalogs prepared of
        Just catalogs -> pure (catalogs, base)
        Nothing -> impossible "formation catalogue preparation returned no owner"

extendFormationEqualityScope
    :: [CoreType]
    -> Vector (LocalId, CoreType)
    -> FormationEqualitySource
    -> FormationScope
    -> FormationScopePreparation FormationScope
extendFormationEqualityScope types support source scope = do
    scopePreparationCount FormationDiagnostics.ScopeInsertion 1
    prepared <- prepareScopeEqualities types support (formationScopeAliases scope)
        source (formationScopeEvidence scope)
    pure scope {formationScopeEvidence = prepared, formationScopeEqualities = source : formationScopeEqualities scope}

withNotionQueryScope
    :: NotionQueryConsumer
    -> Elaborate result
    -> Elaborate result
withNotionQueryScope FormationNotionQuery action = action
withNotionQueryScope consumer action =
    withFormationScope (notionQueryScope consumer) action

withFormationScope
    :: (FormationScope -> FormationScope)
    -> Elaborate result
    -> Elaborate result
withFormationScope change action = do
    previous <- State.gets (lexicalFormationScope . elaborationScope)
    modifyLexicalScope \scope ->
        scope { lexicalFormationScope = change previous }
    result <- action
    modifyLexicalScope \scope ->
        scope { lexicalFormationScope = previous }
    pure result

notionQueryScope
    :: NotionQueryConsumer
    -> FormationScope
    -> FormationScope
notionQueryScope consumer scope =
    scope
            { formationScopeSources =
                [ source
                | source <- formationScopeSources scope
                , notionQueryAdmitsOrigin consumer (premiseOrigin source)
                ]
            , formationScopeAliases = case consumer of
                ProofNotionQuery -> formationScopeAliases scope
                FormationNotionQuery -> formationScopeAliases scope
                DefinitionResultNotionQuery -> []
            }
  where
    premiseOrigin
            (FormationPremiseSource _support _proposition _assertions origin) =
        origin

notionQueryAdmitsOrigin
    :: NotionQueryConsumer
    -> FormationSourceOrigin
    -> Bool
notionQueryAdmitsOrigin _ FormationFromGoalAssumption{} = True
notionQueryAdmitsOrigin consumer origin =
    case consumer of
        FormationNotionQuery -> True
        DefinitionResultNotionQuery -> case origin of
            FormationFromDefinitionHeader{} -> True
            _ -> False
        ProofNotionQuery -> case origin of
            FormationFromProofLocal{} -> True
            _ -> False

data LexicalScope = LexicalScope
    { lexicalBinders :: !(Map.Map Raw.VarSymbol (Natural, CoreType))
    -- Authoritative nearest-first context, including anonymous and contextual
    -- binders which have no entry in the name map.
    , lexicalBinderStack :: !BinderStack
    , lexicalStructures :: !(Map.Map Natural ResolvedStructureApplication)
    , lexicalContextualBinder :: !(Maybe Natural)
    -- The equality index belongs to this exact binder and guarded-premise scope.
    , lexicalFormationScope :: !FormationScope
    }

data ElaborationState = ElaborationState
    { elaborationScope :: !LexicalScope
    , elaborationObjectClosure :: !CheckedObjectClosure
    , elaborationNaturalNumeralBasis
        :: !(Maybe Declaration.NaturalNumeralBasis)
    , elaborationLocalGlobalDefinitions
        :: !(Map.Map SemanticGlobalKey LocalGlobalDefinition)
    , elaborationContextualRequirements
        :: !(Map.Map Raw.StructSymbol (FieldId, ObjectId))
    , elaborationProofSupport :: !(Vector (LocalId, CoreType))
    , elaborationDefinitionContract :: !(Maybe FormationContract)
    , elaborationDefinitionBaseProjections :: ![DefinitionBaseProjection]
    , elaborationPreparedDefinitionResults
        :: !(Maybe PreparedDefinitionResults)
    , elaborationDefinitionProvider :: !(Maybe GlobalBindingRef)
    , elaborationExpansionAllowance :: !(Maybe Word)
    , elaborationCalculationAllowance :: !(Maybe Word)
    }

modifyLexicalScope :: (LexicalScope -> LexicalScope) -> Elaborate ()
modifyLexicalScope change = State.modify' \state ->
    state { elaborationScope = change (elaborationScope state) }

-- | The complete transient proof input for one checked result annotation.
-- It is prepared while the exact definition headers are active, before the
-- definition receives its global provider identity.  The later binding phase
-- may therefore transport this proved body notion to the provider application
-- without letting the annotation bootstrap itself.
data PreparedDefinitionResults = PreparedDefinitionResults
    { preparedDefinitionResultItems :: !(NonEmpty PreparedDefinitionResult)
    , preparedDefinitionCompletion :: !FormationDiagnostics.Completion
    }

data PreparedDefinitionResult = PreparedDefinitionResult
    ![CompiledHeaderAntecedent]
    !ScopedSourceTerm
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)
    !(MaterializedFormationEvidence FormationSourceOrigin)
    !ResultProviderTemplate
    !(RulePremiseBundles RuleTermTemplate)
    !(NotionLeaf ResultNotionRuleTemplate ResidualTemplate)

preparedDefinitionResultHeaders
    :: PreparedDefinitionResult
    -> [CompiledHeaderAntecedent]
preparedDefinitionResultHeaders
        (PreparedDefinitionResult headers _body _assertion _predicate _evidence
            _provider _premises _conclusion) =
    headers

preparedDefinitionResultBody
    :: PreparedDefinitionResult
    -> ScopedSourceTerm
preparedDefinitionResultBody
        (PreparedDefinitionResult _headers body _assertion _predicate _evidence
            _provider _premises _conclusion) =
    body

preparedDefinitionResultProposition
    :: PreparedDefinitionResult
    -> ScopedCheckedCore ObjectId
preparedDefinitionResultProposition
        (PreparedDefinitionResult _headers _body assertion _predicate _evidence
            _provider _premises _conclusion) =
    assertion

preparedDefinitionResultPredicate
    :: PreparedDefinitionResult
    -> ScopedCheckedCore ObjectId
preparedDefinitionResultPredicate
        (PreparedDefinitionResult _headers _body _assertion predicate _evidence
            _provider _premises _conclusion) =
    predicate

preparedDefinitionResultEvidence
    :: PreparedDefinitionResult
    -> MaterializedFormationEvidence FormationSourceOrigin
preparedDefinitionResultEvidence
        (PreparedDefinitionResult _headers _body _assertion _predicate evidence
            _provider _premises _conclusion) =
    evidence

preparedDefinitionResultProvider
    :: PreparedDefinitionResult
    -> ResultProviderTemplate
preparedDefinitionResultProvider
        (PreparedDefinitionResult _headers _body _assertion _predicate _evidence
            provider _premises _conclusion) = provider

preparedDefinitionResultPremises
    :: PreparedDefinitionResult
    -> RulePremiseBundles RuleTermTemplate
preparedDefinitionResultPremises
        (PreparedDefinitionResult _headers _body _assertion _predicate _evidence
            _provider premises _conclusion) = premises

preparedDefinitionResultConclusion
    :: PreparedDefinitionResult
    -> NotionLeaf ResultNotionRuleTemplate ResidualTemplate
preparedDefinitionResultConclusion
        (PreparedDefinitionResult _headers _body _assertion _predicate _evidence
            _provider _premises conclusion) = conclusion

elaborationDefinitionResults
    :: ElaborationState
    -> Maybe PreparedDefinitionResults
elaborationDefinitionResults = elaborationPreparedDefinitionResults

setElaborationDefinitionProvider
    :: GlobalBindingRef
    -> Elaborate ()
setElaborationDefinitionProvider provider =
    State.modify' \state ->
        state { elaborationDefinitionProvider = Just provider }

data DefinitionBaseProjection = DefinitionBaseProjection
    !(NotionLeaf NotionTemplate ResidualTemplate)
    !(CanonicalTerm ObjectId)
    !ConjunctionPath

definitionBaseProjectionTemplate
    :: DefinitionBaseProjection
    -> NotionLeaf NotionTemplate ResidualTemplate
definitionBaseProjectionTemplate
        (DefinitionBaseProjection template _formula _path) =
    template

definitionBaseProjectionFormula
    :: DefinitionBaseProjection
    -> CanonicalTerm ObjectId
definitionBaseProjectionFormula
        (DefinitionBaseProjection _template formula _path) =
    formula

definitionBaseProjectionPath
    :: DefinitionBaseProjection
    -> ConjunctionPath
definitionBaseProjectionPath
        (DefinitionBaseProjection _template _formula path) =
    path

elaborationGlobalTyping :: ElaborationState -> GlobalTyping ObjectId
elaborationGlobalTyping =
    globalTypingFromClosure . elaborationObjectClosure

elaborationRequiredContextualFields
    :: ElaborationState
    -> Map.Map Raw.StructSymbol (FieldId, ObjectId)
elaborationRequiredContextualFields = elaborationContextualRequirements

elaborationFormationContract
    :: ElaborationState
    -> Maybe FormationContract
elaborationFormationContract = elaborationDefinitionContract

initializeDefinitionElaboration
    :: Map.Map Raw.VarSymbol (Natural, CoreType)
    -> Natural
    -> Bool
    -> Elaborate ()
initializeDefinitionElaboration binders parameterCount contextual =
    modifyLexicalScope \scope ->
        scope
            { lexicalBinders = binders
            , lexicalBinderStack =
                BinderStack
                    ( replicate (fromIntegral parameterCount) TySet
                      <> [TySet | contextual]
                    )
            , lexicalContextualBinder =
                if contextual then Just parameterCount else Nothing
            }

setElaborationStructureAnnotation
    :: Natural
    -> ResolvedStructureApplication
    -> Elaborate ()
setElaborationStructureAnnotation index annotation =
    modifyLexicalScope \scope ->
        scope
            { lexicalStructures =
                Map.insert index annotation (lexicalStructures scope)
            }

type Elaborate =
    StateT
        ElaborationState
        (ExceptT ElaborationError (Declaration.LoweringDriver))

data CompiledBody = CompiledBody
    !(CanonicalTerm ObjectId)
    !(Maybe CompiledNamedSetConstruction)
    !(Maybe CompiledBodySource)

data CompiledBodySource
    = CompiledTermBody !CompiledSourceTerm
    | CompiledPropositionBody !CompiledProposition

type CompiledSourceNotionAssertion =
    SourceNotionOccurrence
        SourceTermPresentation
        CompiledSourceTerm
        (CanonicalTerm ObjectId)

type CompiledSourceEqualityOccurrence =
    SourceEqualityOccurrence
        CompiledSourceTerm
        (CanonicalTerm ObjectId)

-- | Retain source syntax without promoting a guarded body to a fact. Atomic
-- projections stop at binders and implications; eligible universals publish
-- separate source views after the whole proposition has formed. Equality
-- sidecars still record only conjunction-eliminable occurrences.
data CompiledProposition = CompiledProposition
    !(CanonicalTerm ObjectId)
    !(SourceEvidence SupportTermTemplate CompiledSourceNotionAssertion)
    ![CompiledSourceEqualityOccurrence]

newtype PhraseComponentOrdinal = PhraseComponentOrdinal Natural
    deriving newtype (Show, Eq, Ord)

data PhraseComponentKind
    = PhraseHardSet
    | PhraseRegular
    deriving stock (Show, Eq, Ord)

data CompiledPhraseComponent = CompiledPhraseComponent
    { phraseComponentKind :: !PhraseComponentKind
    , phraseComponentSourceOrder :: !PhraseComponentOrdinal
    , phraseComponentProposition :: !CompiledProposition
    }

data PhraseAssertionCoordinate = PhraseAssertionCoordinate
    { phraseAssertionComponent :: !PhraseComponentOrdinal
    , phraseAssertionOffset :: !Natural
    }
    deriving stock (Show, Eq, Ord)

phraseLeftComponentOrdinal
    :: Natural -> Natural -> Natural -> PhraseComponentOrdinal
phraseLeftComponentOrdinal subjectCount subjectOrdinal modifierOrdinal =
    PhraseComponentOrdinal
        (modifierOrdinal * subjectCount + subjectOrdinal)

phraseCoreComponentOrdinal
    :: Natural -> Natural -> Natural -> PhraseComponentOrdinal
phraseCoreComponentOrdinal subjectCount leftCount subjectOrdinal =
    PhraseComponentOrdinal
        (leftCount * subjectCount + subjectOrdinal)

phraseRightComponentOrdinal
    :: Natural -> Natural -> Natural -> Natural -> PhraseComponentOrdinal
phraseRightComponentOrdinal subjectCount leftCount subjectOrdinal
        modifierOrdinal =
    PhraseComponentOrdinal
        ((leftCount + 1 + modifierOrdinal) * subjectCount + subjectOrdinal)

phraseResidualComponentOrdinal
    :: Natural -> Natural -> Natural -> PhraseComponentOrdinal
phraseResidualComponentOrdinal subjectCount leftCount rightCount =
    PhraseComponentOrdinal
        ((leftCount + 1 + rightCount) * subjectCount)

data CompiledPhraseComponents = CompiledPhraseComponents
    { phraseCoreComponents :: ![CompiledPhraseComponent]
    , phraseBoundComponents :: ![CompiledPhraseComponent]
    , phraseLeftComponents :: ![[CompiledPhraseComponent]]
    , phraseRightComponents :: ![[CompiledPhraseComponent]]
    , phraseResidualComponent :: !(Maybe CompiledPhraseComponent)
    }

compiledPropositionCore
    :: CompiledProposition
    -> CanonicalTerm ObjectId
compiledPropositionCore
        (CompiledProposition core _assertions _equalities) = core

compiledPropositionAssertions
    :: CompiledProposition
    -> [CompiledSourceNotionAssertion]
compiledPropositionAssertions = sourceEvidenceAssertions . compiledPropositionEvidence

compiledPropositionEvidence
    :: CompiledProposition
    -> SourceEvidence SupportTermTemplate CompiledSourceNotionAssertion
compiledPropositionEvidence
        (CompiledProposition _core assertions _equalities) = assertions

compiledPropositionEqualities
    :: CompiledProposition
    -> [CompiledSourceEqualityOccurrence]
compiledPropositionEqualities
        (CompiledProposition _core _assertions equalities) = equalities

plainCompiledProposition
    :: CanonicalTerm ObjectId
    -> CompiledProposition
plainCompiledProposition core = CompiledProposition core (SourceResidual Nothing) []

-- Raw HOL propositions have no source notion view. Retain their complete
-- set operands before an enclosing opaque connective combines source metadata.
-- A set-valued operand stays opaque; its Core children do not become views.
opaqueCompiledProposition :: Location -> CanonicalTerm ObjectId -> Elaborate CompiledProposition
opaqueCompiledProposition location formula = do
    context <- currentSourceTermCheckingContext
    root <- either (Except.throwError . ElaborationCoreCheckFailed location) pure
        (analyseCanonicalOccurrences (SourceTerm.sourceTermGlobalTyping context)
            (SourceTerm.sourceTermBinderTypes context) formula)
    let inputs = collect [] root
        evidence = if null inputs then SourceResidual Nothing else SourceInputs Nothing inputs
    pure (CompiledProposition formula evidence [])
  where
    collect binders occurrence
        | checkedOccurrenceType occurrence == TySet =
            [SourceInput binders (TemplateVariable
                (scopedCoreTerm (checkedOccurrenceScopedCore occurrence)))]
        | otherwise = case checkedOccurrenceView occurrence of
            OccurrenceApplication left right -> collect binders left <> collect binders right
            OccurrenceLambda binder body -> collect (binder : binders) body
            OccurrenceNegation body -> collect binders body
            OccurrenceConjunction left right -> collect binders left <> collect binders right
            OccurrenceDisjunction left right -> collect binders left <> collect binders right
            OccurrenceImplication left right -> collect binders left <> collect binders right
            OccurrenceEquality _ left right -> collect binders left <> collect binders right
            OccurrenceUniversal binder body -> collect (binder : binders) body
            OccurrenceExistential binder body -> collect (binder : binders) body
            _ -> []

wholeCompiledOperands :: CanonicalTerm ObjectId -> [CompiledSourceTerm] -> CompiledProposition
wholeCompiledOperands formula terms = CompiledProposition formula
    (SourceInputs Nothing [SourceInput [] (SourceTerm.sourceSupportTemplate id term)
        | term <- terms, compiledSourceTermType term == TySet]) []

atomicCompiledProposition
    :: CompiledSourceNotionAssertion
    -> CompiledProposition
atomicCompiledProposition assertion =
    CompiledProposition (sourceAssertionFormula assertion) (SourceAtom assertion) []

-- Explicit negation preserves an atomic argument view, but does not distribute
-- over connectives or cancel a second negation. No equality edge is introduced.
negatedCompiledProposition :: CompiledProposition -> CompiledProposition
negatedCompiledProposition proposition = case compiledPropositionEvidence proposition of
    SourceWithInputs inputs body ->
        let negated = negatedCompiledProposition (CompiledProposition (compiledPropositionCore proposition) body [])
        in CompiledProposition (compiledPropositionCore negated)
            (SourceEvidence.withSourceInputs inputs (compiledPropositionEvidence negated)) []
    SourceAtom assertion | atomPolarity (sourceAssertionAtom assertion) == PositivePolarity ->
        let negated = sourceNotionAssertionFromTemplate
                (withAtomPolarity NegativePolarity (sourceAssertionAtom assertion)) formula
                (sourceAssertionPath assertion) (sourceAssertionLocation assertion)
        in atomicCompiledProposition (maybe negated (`withSourceNotionOrigin` negated) (sourceNotionWrittenOrigin assertion))
    _ -> residualCompiledProposition formula [] [proposition]
  where
    formula = logicalNot (compiledPropositionCore proposition)

atomicCompiledEquality
    :: CompiledSourceEqualityOccurrence
    -> CompiledProposition
atomicCompiledEquality equality =
    CompiledProposition (sourceEqualityFormula equality)
        (SourceInputs Nothing (SourceInput [] . SourceTerm.sourceSupportTemplate id <$>
            [sourceEqualityLeft equality,sourceEqualityRight equality])) [equality]

-- Keep whole operands when the logical connective has no elimination view.
-- Keep private binders and complete written operands together. Preparation
-- later selects independent inputs without granting them inference authority.
residualCompiledProposition :: CanonicalTerm ObjectId -> [CoreType] -> [CompiledProposition] -> CompiledProposition
residualCompiledProposition formula binders propositions = CompiledProposition formula evidence []
  where
    operands = [SourceInput (nested <> binders) term | proposition <- propositions,
        SourceInput nested term <- SourceEvidence.sourceInputsAtDepth
            (fmap (SourceTerm.sourceSupportTemplate id) . toList . sourceAssertionAtom)
            (compiledPropositionEvidence proposition)]
    evidence = if null operands then SourceResidual Nothing else SourceInputs Nothing operands

sourceEvidenceAssertions
    :: SourceEvidence term (SourceNotionOccurrence presentation argument formula)
    -> [SourceNotionOccurrence presentation argument formula]
sourceEvidenceAssertions evidence =
    [ mapSourceNotionAssertionPath (appendConjunctionPath path) atom
    | (path, atom) <- SourceEvidence.directAtoms evidence
    ]

appendConjunctionPath :: ConjunctionPath -> ConjunctionPath -> ConjunctionPath
appendConjunctionPath prefix suffix = case prefix of
    ConjunctionHere -> suffix
    ConjunctionLeft rest -> ConjunctionLeft (appendConjunctionPath rest suffix)
    ConjunctionRight rest -> ConjunctionRight (appendConjunctionPath rest suffix)

mapEqualityPath
    :: (ConjunctionPath -> ConjunctionPath)
    -> CompiledSourceEqualityOccurrence
    -> CompiledSourceEqualityOccurrence
mapEqualityPath transform equality =
    mapSourceEqualityOccurrencePath transform equality

conjoinCompiled
    :: Foldable collection
    => collection CompiledProposition
    -> CompiledProposition
conjoinCompiled =
    foldr combine (plainCompiledProposition logicalTruth)
  where
    combine proposition remaining
        | isNeutralCompiled proposition = remaining
        | isNeutralCompiled remaining = proposition
        | otherwise = conjoinCompiledPair proposition remaining

conjoinCompiledPair :: CompiledProposition -> CompiledProposition -> CompiledProposition
conjoinCompiledPair left right = CompiledProposition
    (logicalAnd (compiledPropositionCore left) (compiledPropositionCore right))
    (SourceAnd (compiledPropositionEvidence left) (compiledPropositionEvidence right))
    ((mapEqualityPath leftConjunctionPath <$> compiledPropositionEqualities left)
        <> (mapEqualityPath rightConjunctionPath <$> compiledPropositionEqualities right))

isNeutralCompiled :: CompiledProposition -> Bool
isNeutralCompiled proposition =
    compiledPropositionCore proposition == logicalTruth
        && null (compiledPropositionAssertions proposition)
        && null (compiledPropositionEqualities proposition)

assemblePhraseComponents
    :: [CompiledPhraseComponent]
    -> (CompiledProposition, [PhraseAssertionCoordinate])
assemblePhraseComponents components
    | length ordinals /= Set.size (Set.fromList ordinals) =
        impossible "phrase component ordinals are not unique"
    | any invalidHardSetComponent components =
        impossible "the hard set phrase component is not logically neutral"
    | length coordinates
        /= length (compiledPropositionAssertions proposition) =
        impossible "phrase assertion coordinates are not aligned"
    | otherwise = (proposition, coordinates)
  where
    proposition =
        conjoinCompiled (phraseComponentProposition <$> components)
    ordinals = phraseComponentSourceOrder <$> components
    coordinates = concatMap componentCoordinates components

    componentCoordinates component =
        [ PhraseAssertionCoordinate
            (phraseComponentSourceOrder component)
            (fromIntegral offset)
        | offset <-
            [0 .. length
                (compiledPropositionAssertions
                    (phraseComponentProposition component)) - 1]
        ]

    invalidHardSetComponent component =
        phraseComponentKind component == PhraseHardSet
            && not
                (isNeutralCompiled
                    (phraseComponentProposition component))

phraseLogicalComponents
    :: CompiledPhraseComponents
    -> [CompiledPhraseComponent]
phraseLogicalComponents components =
    heads <> maybeToList (phraseResidualComponent components)
  where
    heads
        | null (phraseBoundComponents components) =
            phraseCoreComponents components
                <> concat (phraseLeftComponents components)
                <> concat (phraseRightComponents components)
        | otherwise = concat (phraseSubjectComponentRows components)

phraseSubjectComponentRows
    :: CompiledPhraseComponents
    -> [[CompiledPhraseComponent]]
phraseSubjectComponentRows components =
    case phraseBoundComponents components of
        [] -> zipWith3 (\core left right -> core : left <> right) cores lefts rights
        bounds -> zipWith
            (\(core, (left, right)) bound -> core : bound : left <> right)
            (zip cores (zip lefts rights)) bounds
  where
    cores = phraseCoreComponents components
    lefts = phraseLeftComponents components
    rights = phraseRightComponents components

-- Only the explicit residual receives all completed, independently checked heads.
withCompletedPhraseHead
    :: Location
    -> [CompiledPhraseComponent]
    -> Elaborate value
    -> Elaborate value
withCompletedPhraseHead location components action = do
    checked <- sealCompiledPropositionHere location
        (fst (assemblePhraseComponents components))
    withCheckedFormationGuard FormationPhraseHead checked action

sealCompiledPropositionHere
    :: Location -> CompiledProposition -> Elaborate ElaboratedProposition
sealCompiledPropositionHere location compiled = do
    context <- currentSourceTermCheckingContext
    sealCompiledPropositionWith (pure ()) checkSourceTermHere sealSourceOccurrenceHere
        (\left right -> pure (left == right)) context location compiled

-- One completed occurrence is the sealing boundary. Bounded expansion uses
-- the same alignment checks as ordinary elaboration, with counted primitives.
sealCompiledPropositionWith
    :: Monad m => m ()
    -> (Location -> SourceTerm.SourceTermCheckingContext ObjectId -> CoreType -> CanonicalTerm ObjectId -> m (ScopedCheckedCore ObjectId))
    -> (Location -> SourceTerm.SourceTermCheckingContext ObjectId -> CompiledSourceTerm -> m ScopedSourceTerm)
    -> (CanonicalTerm ObjectId -> CanonicalTerm ObjectId -> m Bool)
    -> SourceTerm.SourceTermCheckingContext ObjectId -> Location -> CompiledProposition -> m ElaboratedProposition
sealCompiledPropositionWith visit check seal same context location compiled = do
    checkedProposition <- check location context TyProp (compiledPropositionCore compiled)
    checkedAssertions <- sealEvidence context (compiledPropositionCore compiled) (compiledPropositionEvidence compiled)
    checkedEqualities <- traverse (sealEquality context checkedProposition) (compiledPropositionEqualities compiled)
    pure (ElaboratedProposition checkedProposition checkedAssertions checkedEqualities)
  where
    sealEvidence current proposition evidence = visit >> case evidence of
        SourceResidual origin -> pure (SourceResidual (origin <|> Just
            (SourceEvidence.WrittenOrigin location Nothing ConjunctionHere)))
        SourceInputs origin terms -> do
            for_ terms \(SourceInput binders term) -> traverse_ (check location
                current {SourceTerm.sourceTermBinderTypes = binders <> SourceTerm.sourceTermBinderTypes current} TySet) term
            pure (SourceInputs (origin <|> Just (SourceEvidence.WrittenOrigin location Nothing ConjunctionHere)) terms)
        SourceWithInputs terms body -> do
            for_ terms \(SourceInput binders term) -> traverse_ (check location
                current {SourceTerm.sourceTermBinderTypes = binders <> SourceTerm.sourceTermBinderTypes current} TySet) term
            SourceEvidence.withSourceInputs terms <$> sealEvidence current proposition body
        SourceAtom assertion -> do
            checked <- check location current TyProp proposition
            SourceAtom <$> sealAssertion current checked assertion
        SourceAnd left right | CAnd leftCore rightCore <- proposition ->
            SourceAnd <$> sealEvidence current leftCore left <*> sealEvidence current rightCore right
        SourceBind body | CForall TySet bodyCore <- proposition ->
            SourceBind <$> sealEvidence
                current { SourceTerm.sourceTermBinderTypes = TySet : SourceTerm.sourceTermBinderTypes current } bodyCore body
        SourceExists body | CExists TySet bodyCore <- proposition ->
            SourceExists <$> sealEvidence
                current { SourceTerm.sourceTermBinderTypes = TySet : SourceTerm.sourceTermBinderTypes current } bodyCore body
        SourceOr a b | COr left right <- proposition ->
            SourceOr <$> sealEvidence current left a <*> sealEvidence current right b
        SourceIff a b | CEq TyProp left right <- proposition ->
            SourceIff <$> sealEvidence current left a <*> sealEvidence current right b
        SourceRequire premise body | CImp guardCore bodyCore <- proposition ->
            SourceRequire <$> sealEvidence current guardCore premise <*> sealEvidence current bodyCore body
        _ -> impossible "retained source evidence disagrees with its proposition"
    projection path term expected = do
        visit
        case (path, term) of
            (ConjunctionHere, _) -> same term expected
            (ConjunctionLeft rest, CAnd left _) -> projection rest left expected
            (ConjunctionRight rest, CAnd _ right) -> projection rest right expected
            _ -> pure False
    sealAssertion current checkedProposition assertion = do
        let assertionLocation = sourceAssertionLocation assertion
        sealed <- traverseSourceNotionAssertionParts
            (seal assertionLocation current) (check assertionLocation current TyProp) assertion
        aligned <- projection (sourceAssertionPath sealed) (scopedCoreTerm checkedProposition)
            (scopedCoreTerm (sourceAssertionFormula sealed))
        unless aligned (impossible "a source notion assertion does not project from its proposition")
        pure sealed
    sealEquality current checkedProposition equality = do
        visit
        let equalityLocation = sourceEqualityLocation equality
        sealed <- traverseSourceEqualityOccurrenceParts
            (seal equalityLocation current) (check equalityLocation current TyProp) equality
        aligned <- projection (sourceEqualityPath sealed) (scopedCoreTerm checkedProposition)
            (scopedCoreTerm (sourceEqualityFormula sealed))
        unless aligned (impossible "a source equality does not project from its proposition")
        pure sealed

currentSourceTermCheckingContext
    :: Elaborate (SourceTerm.SourceTermCheckingContext ObjectId)
currentSourceTermCheckingContext = do
    state <- State.get
    pure (SourceTerm.SourceTermCheckingContext
        (elaborationGlobalTyping state)
        (binderStackTypes (lexicalBinderStack (elaborationScope state))))

checkSourceTermHere
    :: Location
    -> SourceTerm.SourceTermCheckingContext ObjectId
    -> CoreType
    -> CanonicalTerm ObjectId
    -> Elaborate (ScopedCheckedCore ObjectId)
checkSourceTermHere location context expected =
    either (Except.throwError . sourceTermSealError location context) pure
        . SourceTerm.checkCanonicalSourceTerm context expected

sealSourceOccurrenceHere
    :: Location
    -> SourceTerm.SourceTermCheckingContext ObjectId
    -> CompiledSourceTerm
    -> Elaborate ScopedSourceTerm
sealSourceOccurrenceHere location context =
    either (Except.throwError . sourceTermSealError location context) pure
        . SourceTerm.sealCanonicalSourceTermOccurrence context

sourceTermSealError
    :: Location
    -> SourceTerm.SourceTermCheckingContext ObjectId
    -> SourceTerm.SourceTermSealError ObjectId
    -> ElaborationError
sourceTermSealError location context = \case
    SourceTerm.SourceTermSealCoreCheckFailed term failure ->
        -- Successful inference already checks every global. Only a failure
        -- needs the complete scan to retain missing-global error precedence.
        case missingCanonicalGlobalTypes
                (SourceTerm.sourceTermGlobalTyping context) term of
            Just missing -> ElaborationCoreGlobalsMissing location missing
            Nothing -> ElaborationCoreCheckFailed location failure
    SourceTerm.SourceTermSealTypeMismatch expected actual -> case expected of
        TyProp -> ElaborationFormulaExpectedProposition location actual
        TySet -> ElaborationExpressionExpectedSet location actual
        _ -> impossible "a notion assertion requested a non-source type"

-- These entry points historically report ordinary Core/type errors rather
-- than the source-formula diagnostics used inside a header transaction.
sourceTermCoreCheckError
    :: SourceTerm.SourceTermSealError global -> CoreCheckError
sourceTermCoreCheckError = \case
    SourceTerm.SourceTermSealCoreCheckFailed _ failure -> failure
    SourceTerm.SourceTermSealTypeMismatch expected actual ->
        ExpectedCoreType expected actual

-- | Seal one complete source-header transaction and only then publish its
-- pending structure designations to following headers and the guarded body.
sealAndCommitHeaderBatch
    :: CompiledHeaderBatch
    -> Elaborate [(Location, CompiledHeaderAntecedent)]
sealAndCommitHeaderBatch (CompiledHeaderBatch rows pending) = do
    checked <- traverse sealRow rows
    unless (Map.null pending) do
        existing <- State.gets (lexicalStructures . elaborationScope)
        unless (Map.null (Map.intersection existing pending))
            (impossible
                "a checked structure header overwrote an active designation")
        modifyLexicalScope \scope ->
            scope
                { lexicalStructures =
                    Map.union pending (lexicalStructures scope)
                }
    pure checked
  where
    sealRow (CompiledHeaderRow source variable location proposition) = do
        sealed <- sealCompiledPropositionHere location proposition
        pure
            ( location
            , CompiledHeaderAntecedent
                sealed
                source
                variable
                location
            )

checkedHeaderProposition
    :: CompiledHeaderAntecedent
    -> ElaboratedProposition
checkedHeaderProposition
        (CompiledHeaderAntecedent proposition _source _variable _location) =
    proposition

withCheckedFormationGuard
    :: FormationGuardKind
    -> ElaboratedProposition
    -> Elaborate result
    -> Elaborate result
withCheckedFormationGuard kind checked action =
    withNotions (withEqualities action)
  where
    withNotions =
        withFormationSource
            (checkedGuardFormationSource
                (elaboratedPropositionCore checked)
                (elaboratedPropositionEvidence checked)
                kind)
    withEqualities =
        case NonEmpty.nonEmpty
                (elaboratedPropositionEqualities checked) of
            Nothing -> id
            Just equalities ->
                withFormationEqualitySource
                    (checkedGuardFormationEqualitySource
                        (elaboratedPropositionCore checked)
                        equalities
                        kind)

withCheckedDefinitionHeaderGuard
    :: Natural
    -> Maybe Natural
    -> Location
    -> ElaboratedProposition
    -> Elaborate result
    -> Elaborate result
withCheckedDefinitionHeaderGuard sourceOrdinal variableOrdinal location
        checked action =
    withNotions (withEqualities action)
  where
    withNotions =
        withFormationSource
            (definitionHeaderFormationSource
                sourceOrdinal
                variableOrdinal
                location
                (elaboratedPropositionCore checked)
                (elaboratedPropositionEvidence checked))
    withEqualities =
        case NonEmpty.nonEmpty
                (elaboratedPropositionEqualities checked) of
            Nothing -> id
            Just equalities ->
                withFormationEqualitySource
                    (definitionHeaderFormationEqualitySource
                        sourceOrdinal
                        variableOrdinal
                        location
                        (elaboratedPropositionCore checked)
                        equalities)

prepareFormationScopeHere :: Location -> FormationScopePreparation value -> Elaborate value
prepareFormationScopeHere location action = State.lift (Trans.lift (finishFormationScopePreparation action))
    >>= either (Except.throwError . ElaborationFormationScopeFailed location) pure

withFormationSource
    :: FormationPremiseSource
    -> Elaborate result
    -> Elaborate result
withFormationSource source action = do
    void (acquireFormationCatalogs (formationSourceLocation source))
    current <- State.get
    let scope = elaborationScope current
    prepared <- prepareFormationScopeHere (formationSourceLocation source)
        (extendFormationScope (binderStackTypes (lexicalBinderStack scope))
            (elaborationProofSupport current) source (lexicalFormationScope scope))
    withFormationScope (const prepared) action

formationSourceLocation :: FormationPremiseSource -> Location
formationSourceLocation (FormationPremiseSource _ _ views origin) = case origin of
    FormationFromDefinitionHeader _ _ location -> location
    FormationFromCheckedGuard _ location -> location
    FormationFromPhraseCore _ location -> location
    FormationFromGoalAssumption _ location -> location
    FormationFromProofLocal{} -> maybe Nowhere sourceAssertionLocation
        (listToMaybe (formationSourceAtoms (SourceEvidence.sourceViews views)))

withFormationEqualitySource
    :: FormationEqualitySource
    -> Elaborate result
    -> Elaborate result
withFormationEqualitySource source action = do
    current <- State.get
    prepared <- prepareFormationScopeHere (equalitySourceLocation source)
        (extendFormationEqualityScope (binderStackTypes (lexicalBinderStack (elaborationScope current)))
            (elaborationProofSupport current) source (lexicalFormationScope (elaborationScope current)))
    withFormationScope (const prepared) action

equalitySourceLocation :: FormationEqualitySource -> Location
equalitySourceLocation (FormationEqualitySource _ _ equalities _) = sourceEqualityLocation (NonEmpty.head equalities)

forgetSourceNotionProviders
    :: ScopedSourceNotionOccurrence
    -> ScopedSourceNotionAssertion
forgetSourceNotionProviders =
    runIdentity
        . traverseSourceNotionAssertionParts
            (Identity . SourceTerm.sourceTermOccurrenceCore)
            Identity

data CompiledNamedSetConstruction
    = CompiledSeparationConstruction
        !(CanonicalTerm ObjectId)
        !(CanonicalTerm ObjectId)
    | CompiledFunctionalReplacementConstruction
        !(NonEmpty (CanonicalTerm ObjectId))
        !(CanonicalTerm ObjectId)
        !(Maybe (CanonicalTerm ObjectId))
    | CompiledRelationalReplacementConstruction
        !(CanonicalTerm ObjectId)
        !(CanonicalTerm ObjectId)

elaborateProposition
    :: ElaborationContext
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedProposition)
elaborateProposition context statement =
    elaborateCompiledPropositionTerm
        context
        (locate statement)
        (compileStatement statement)

-- | Compile the source bound of already-opened symbolic binders.  This is the
-- shared checked constraint seam used by quantified statements and proof
-- binders, so relation signs, carrier casts, and global occurrences are
-- elaborated exactly once by the ordinary expression compiler.
elaborateSymbolicBoundConstraints
    :: ElaborationContext
    -> NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedProposition)
elaborateSymbolicBoundConstraints context variables bound =
    elaborateCompiledPropositionTerm
        context
        (case bound of
            Raw.Unbounded -> locate (NonEmpty.head variables)
            _ -> locate bound)
        (conjoinCompiled
            <$> compileSymbolicBoundConstraintList variables bound)

elaborateCalculationGuard
    :: ElaborationContext -> NonEmpty Raw.VarSymbol -> Raw.Bound -> Maybe Raw.Stmt
    -> Declaration.LoweringDriver (Either ElaborationError ElaboratedProposition)
elaborateCalculationGuard context variables bound suchThat = elaborateCompiledPropositionTerm context (locate bound) do
    restriction <- conjoinCompiled <$> compileSymbolicBoundConstraintList variables bound
    checked <- sealCompiledPropositionHere (locate bound) restriction
    remainder <- traverse (withCheckedFormationGuard FormationSymbolicQuantifierBound checked . compileStatement) suchThat
    pure (conjoinCompiled (restriction : maybeToList remainder))

-- | Compile the opened body used by a symbolic existential witness.  Its
-- grouping is deliberately identical to 'SymbolicExists': all bound
-- constraints form the existential restriction and the stated proposition is
-- its body.
elaborateSymbolicWitnessConstraints
    :: ElaborationContext
    -> NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedProposition)
elaborateSymbolicWitnessConstraints context variables bound statement =
    elaborateCompiledPropositionTerm context (locate statement) do
        constraints <-
            conjoinCompiled
                <$> compileSymbolicBoundConstraintList variables bound
        checkedConstraints <-
            sealCompiledPropositionHere (locate bound) constraints
        body <-
            withCheckedFormationGuard
                FormationExistentialWitnessRestriction
                checkedConstraints
                (compileStatement statement)
        pure (conjoinCompiled [constraints, body])

-- | Compile the checked constraint of an already-opened noun witness.  Named
-- binders are resolved normally; a nameless singular noun uses the nearest
-- anonymous binder and therefore introduces no lookup spelling.
elaborateNounWitnessConstraints
    :: ElaborationContext
    -> ElaborationContext
    -> Raw.NounPhrase []
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedProposition)
elaborateNounWitnessConstraints outerContext context
        (Raw.NounPhrase left noun (Raw.NounBinder variables bound) right suchThat) = do
    prepared <- case bound of
        Raw.Unbounded -> pure (Right Nothing)
        _ -> Except.runExceptT do
            initial <- prepareInitialElaborationState outerContext
            fst <$> State.runStateT (prepareNounBound variables bound) initial
    case prepared of
        Left failure -> pure (Left failure)
        Right captured ->
            elaborateCompiledPropositionTerm context (locate noun) do
                subjects <- case NonEmpty.nonEmpty variables of
                    Just binders -> toList <$> traverse compileIntroducedVariable binders
                    Nothing -> pure [CBound 0]
                compileBoundedNounConstraints captured
                    subjects left noun right suchThat

elaborateCompiledPropositionTerm
    :: ElaborationContext
    -> Location
    -> Elaborate CompiledProposition
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedProposition)
elaborateCompiledPropositionTerm context location compile =
    Except.runExceptT do
        initialElaboration <- prepareInitialElaborationState context
        State.evalStateT
            (compile >>= sealCompiledPropositionHere location)
            initialElaboration

elaborateSetExpression
    :: ElaborationContext
    -> Raw.Expr
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedSetExpression)
elaborateSetExpression context expression =
    Except.runExceptT do
        initialElaboration <- prepareInitialElaborationState context
        ((compiled, source), finalElaboration) <-
            State.runStateT
                (compileNamedSetExpressionWithSource expression)
                initialElaboration
        let CompiledBody term rawConstruction _proposition = compiled
            globalTyping = elaborationGlobalTyping finalElaboration
            contextTypes = binderTypes context
            checkingContext = SourceTerm.SourceTermCheckingContext globalTyping contextTypes
        unless (SourceTerm.sourceTermOccurrenceCore source == term)
            (impossible
                "a named expression disagrees with its source occurrence")
        -- Compilation has required a set result. Sealing checks the root first
        -- under this same snapshot, then every retained source child.
        checkedSource <- either
            (Except.throwError . ElaborationCoreCheckFailed (locate expression)
                . sourceTermCoreCheckError)
            pure
            (SourceTerm.sealCanonicalSourceTermOccurrence checkingContext source)
        let checked = SourceTerm.sourceTermOccurrenceCore checkedSource
        unless (scopedCoreType checked == TySet)
            (Except.throwError
                (ElaborationExpressionExpectedSet
                    (locate expression)
                    (scopedCoreType checked)))
        construction <-
            Except.liftEither
                (traverse
                    (checkCompiledNamedSetConstruction
                        globalTyping
                        contextTypes)
                    rawConstruction)
        traverse_
            (\checkedConstruction ->
                unless
                    (preparedSetConstructionTerm checkedConstruction == checked)
                    (impossible
                        "exact named construction disagrees with its checked expression"))
            construction
        pure (ElaboratedSetExpression checkedSource construction)

elaborateExpression
    :: ElaborationContext
    -> Raw.TypedExpression
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedExpression)
elaborateExpression context expression =
    Except.runExceptT do
        initialElaboration <- prepareInitialElaborationState context
        elaborateExpressionFromState context expression initialElaboration

-- Domains are in the fixed-parameter context. Unstored premise witnesses
-- license a branch existentially; they never become source variables or inputs.
data RecursiveBranch = RecursiveBranch
    { recursiveBranchFields :: ![(Raw.VarSymbol, CompiledSourceTerm, Bool)]
    , recursiveBranchWitnesses :: ![CompiledSourceTerm]
    , recursiveBranchBody :: !(Either Raw.Expr Raw.Stmt)
    }

elaborateRecursiveBranches
    :: Location -> SemanticGlobalKey -> [Raw.VarSymbol] -> [Raw.Asm]
    -> NonEmpty RecursiveBranch
    -> Declaration.LoweringDriver
        (Either ElaborationError ([ResidualTemplate], NonEmpty (ScopedCheckedCore ObjectId, AbbreviationExpansion)))
elaborateRecursiveBranches location key parameters assumptions branches = Except.runExceptT do
    context <- Except.liftEither $ case NonEmpty.nonEmpty (zip (localId <$> [0..]) parameters) of
        Nothing -> pure emptyElaborationContext
        Just binders -> extendElaborationContext binders emptyElaborationContext
    initial <- prepareInitialElaborationState context
    State.evalStateT (do
        beginAbbreviationExpansion
        (_, _, _, prepared) <- compileHostedDefinitionHeaders location assumptions \antecedents -> do
            headers <- traverse (\header -> either (Except.throwError . invalid) pure
                (NotionPremise.describeResidual (fromIntegral (length parameters))
                    (compiledHeaderCore header) (compiledHeaderEvidence header))) antecedents
            values <- traverse prepareBranch branches
            pure (headers, values)
        pure prepared) initial
  where
    invalid = ElaborationRecursiveDefinitionInvalid location
    resultType = case semanticGlobalKeyType key >>= firstOrderSymbolShape of
        Just (_, ty) -> ty
        _ -> impossible "a recursive head lost its first-order type"
    prepareBranch (RecursiveBranch fields witnesses body) = do
        let fieldCount = length fields
            recursive = [i | (i,(_,_,True)) <- zip [0..] fields]
            resultCount = length recursive
            count = fieldCount + resultCount
            layout = Vector.fromList (fromIntegral <$> reverse [0..length parameters+count-1])
            binders = [(Just variable,TySet) | (variable,_,_) <- fields]
                <> replicate resultCount (Nothing,resultType)
            indices = fromIntegral <$> reverse [0..count-1]
            results = zip [fromIntegral (count-1-i) | i <- recursive]
                (fromIntegral <$> reverse [0..resultCount-1])
            fixed = fromIntegral <$> reverse [count..count+length parameters-1]
            withBinders = maybe id withLexicalBinders (NonEmpty.nonEmpty binders)
            fieldGuards = [membership (CBound index) (shiftDomain (fromIntegral count) domain)
                | (index,(_,domain,_)) <- zip indices fields]
            witnessGuard = witnessConditions (fromIntegral count) witnesses
            guards = conjoinCompiled (fieldGuards <> [witnessGuard])
        (value,description) <- withBinders do
            checked <- sealCompiledPropositionHere location guards
            -- All headers are fixed-parameter assumptions; every selected field
            -- has its exact descriptor membership here. Consequently the exact
            -- unchanged-parameter/field match below discharges the complete call
            -- contract before replacing the call. No induction hypothesis or
            -- propositionally equal surrogate is used as formation evidence.
            withCheckedFormationGuard FormationHostedDefinitionConjunct checked do
                previous <- State.gets elaborationLocalGlobalDefinitions
                State.modify' (\state -> state {elaborationLocalGlobalDefinitions = Map.insert key
                    (LocalRecursiveResults (fromIntegral (length parameters + count)) fixed results resultType) previous})
                (term,source) <- case body of
                    Left expression | resultType == TySet -> do
                        written <- compileSourceExpressionAsSetTerm expression
                        description <- withAbbreviationExpansion location key
                            (TermExpansion <$> SourceTemplate.abstractSourceTerm layout 0 written)
                        pure (compiledSourceTermCore written,description)
                    Right statement | resultType == TyProp -> do
                        proposition <- compileStatement statement
                        description <- withAbbreviationExpansion location key
                            (SourceTemplate.abstractSourceProposition layout
                                (compiledPropositionEvidence proposition) (compiledPropositionEqualities proposition))
                        pure (compiledPropositionCore proposition,description)
                    _ -> Except.throwError (invalid "all clauses must have the head's result type")
                State.modify' (\state -> state {elaborationLocalGlobalDefinitions = previous})
                pure (term,source)
        typing <- State.gets elaborationGlobalTyping
        checked <- either (Except.throwError . ElaborationCoreCheckFailed location) pure
            (checkScopedCanonicalCore typing (replicate (length parameters) TySet)
                (foldr CLam value (snd <$> binders)))
        pure (checked,description)
    shiftDomain amount = SourceTerm.shiftCanonicalSourceTermOccurrence amount 0
    membership element domain = atomicCompiledProposition
        (sourceNotionAssertionFromTemplate
            (MembershipAtomTemplate (locatedSetSourceTerm location element) domain)
            (CApp (CApp (CIntrinsic Member) element) (compiledSourceTermCore domain))
            ConjunctionHere location)
    witnessConditions count domains =
        let size = fromIntegral (length domains)
            propositions = [membership (CBound index) (shiftDomain (count+size) domain)
                | (index,domain) <- zip (reverse [0..size-1]) domains]
            combined = conjoinCompiled propositions
        in if null domains then plainCompiledProposition CTruth else CompiledProposition
            (foldr (const (CExists TySet)) (compiledPropositionCore combined) domains)
            (foldr (const SourceExists) (compiledPropositionEvidence combined) domains) []

elaborateDatatypeExpression
    :: DatatypeElaborationEnvironment
    -> Raw.TypedExpression
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedExpression)
elaborateDatatypeExpression
        (DatatypeElaborationEnvironment closure context) expression =
    Except.runExceptT do
        initial <- Trans.lift
            (initialElaborationStateLowering closure context)
        elaborateExpressionFromState context expression initial

elaborateExpressionFromState
    :: ElaborationContext
    -> Raw.TypedExpression
    -> ElaborationState
    -> ExceptT
        ElaborationError
        Declaration.LoweringDriver
        ElaboratedExpression
elaborateExpressionFromState context expression initialElaboration = do
        ((canonical, inferredType, source), finalElaboration) <-
            State.runStateT
                (case expression of
                    Raw.TypedExpressionExpr raw -> do
                        compiled <- compileSourceExpression raw
                        pure
                            ( compiledSourceTermCore compiled
                            , compiledSourceTermType compiled
                            , Just compiled
                            )
                    Raw.TypedExpressionFormula formula -> do
                        compiled <- compileFormula formula
                        pure
                            ( compiledPropositionCore compiled
                            , TyProp
                            , Nothing
                            ))
                initialElaboration
        checked <-
            either
                (Except.throwError
                    . ElaborationCoreCheckFailed (locate expression))
                pure
                (checkScopedCanonicalCore
                    (elaborationGlobalTyping finalElaboration)
                    (binderTypes context)
                    canonical)
        unless (scopedCoreType checked == inferredType)
            (impossible
                "typed expression inference disagrees with core checking")
        let checkingContext = SourceTerm.SourceTermCheckingContext
                (elaborationGlobalTyping finalElaboration) (binderTypes context)
        checkedSource <- traverse
            (either
                (Except.throwError . ElaborationCoreCheckFailed (locate expression)
                    . sourceTermCoreCheckError)
                pure
                . SourceTerm.sealCanonicalSourceTermOccurrence checkingContext)
            source
        pure (ElaboratedExpression checked checkedSource)

-- The template keeps endpoint slots separate from captured source operands.
-- Its body and source description are scoped under two fresh endpoint binders.
data CalculationTemplate = CalculationTemplate
    !(ScopedCheckedCore ObjectId)
    !CompiledProposition
    !AbbreviationExpansion
    !(Map SourceProviderHead ObjectId)
    ![CompiledSourceTerm] -- frozen operands, including erased captures
    ![CompiledSourceTerm] -- available written views for later folds

data CheckedCalculationApplication = CheckedCalculationApplication
    !Calculation.Relator
    !CalculationTemplate
    !ScopedSourceTerm
    !ScopedSourceTerm
    !ElaboratedProposition

calculationRelator :: CheckedCalculationApplication -> Calculation.Relator
calculationRelator (CheckedCalculationApplication relation _ _ _ _) = relation
calculationLeftSource, calculationRightSource :: CheckedCalculationApplication -> ScopedSourceTerm
calculationLeftSource (CheckedCalculationApplication _ _ left _ _) = left
calculationRightSource (CheckedCalculationApplication _ _ _ right _) = right
calculationLeft, calculationRight :: CheckedCalculationApplication -> ScopedCheckedCore ObjectId
calculationLeft = SourceTerm.sourceTermOccurrenceCore . calculationLeftSource
calculationRight = SourceTerm.sourceTermOccurrenceCore . calculationRightSource
calculationProposition :: CheckedCalculationApplication -> ElaboratedProposition
calculationProposition (CheckedCalculationApplication _ _ _ _ proposition) = proposition
calculationOpenProposition :: CheckedCalculationApplication -> ScopedCheckedCore ObjectId
calculationOpenProposition = elaboratedPropositionCore . calculationProposition

calculationWork :: Location -> Calculation.CalculationWork Elaborate value -> Elaborate value
calculationWork location action = do
    allowance <- fromMaybe Calculation.defaultCalculationWork <$> State.gets elaborationCalculationAllowance
    (result,remaining) <- Calculation.runCalculationWork allowance action
    State.modify' (\state -> state{elaborationCalculationAllowance = Just remaining})
    either (Except.throwError . ElaborationCalculationFailed location) pure result

calculationExpansion :: Location -> ExpansionWork Elaborate value -> Elaborate value
calculationExpansion location = calculationWork location . Calculation.calculationExpansionWork

elaborateRelationCalculation
    :: Word -> ElaborationContext -> Raw.Expr -> NonEmpty Raw.CalcRelationLink
    -> Declaration.LoweringDriver
        (Either ElaborationError (NonEmpty CheckedCalculationApplication, Word))
elaborateRelationCalculation allowance context initialExpression links = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    (applications,final) <- State.runStateT (do
        left <- compileSourceExpression initialExpression
        compileCalculationChain left links) initial{elaborationCalculationAllowance = Just allowance}
    pure (applications, fromMaybe allowance (elaborationCalculationAllowance final))

compileCalculationChain
    :: CompiledSourceTerm -> NonEmpty Raw.CalcRelationLink
    -> Elaborate (NonEmpty CheckedCalculationApplication)
compileCalculationChain initial (firstLink :| remaining) = do
    firstApplication <- compileCalculationLink initial firstLink
    rest <- go (SourceTerm.forgetScopedSourceTermOccurrence (calculationRightSource firstApplication)) remaining
    pure (firstApplication :| rest)
  where
    go _ [] = pure []
    go left (link:rest) = do
        application <- compileCalculationLink left link
        later <- go (SourceTerm.forgetScopedSourceTermOccurrence (calculationRightSource application)) rest
        pure (application:later)

compileCalculationLink :: CompiledSourceTerm -> Raw.CalcRelationLink -> Elaborate CheckedCalculationApplication
compileCalculationLink left (Raw.CalcRelationLink sign relation destination _) = do
    (resolved,right) <- case relation of
        Raw.Relation location symbol parameters -> do
            captured <- traverse compileSourceExpressionAsSetTerm parameters
            right <- compileSourceExpression destination
            resolved <- resolveNamedRelationTerms location symbol captured left right
            pure (resolved,right)
        Raw.RelationExpr location expression -> do
            right <- compileSourceExpressionAsSetTerm destination
            resolved <- resolveTermRelation location expression left right
            pure (resolved,right)
    compileResolvedCalculation (locate relation) sign resolved left right

compileResolvedCalculation
    :: Location -> Raw.Sign -> ResolvedSourceRelation -> CompiledSourceTerm -> CompiledSourceTerm
    -> Elaborate CheckedCalculationApplication
compileResolvedCalculation location sign resolved left right = do
    let leftType = compiledSourceTermType left
        rightType = compiledSourceTermType right
        formal index ty = SourceTerm.sourceTermOccurrence (CBound index) ty (LocatedSourceTerm location)
    symbolic <- withLexicalBinders ((Nothing,leftType) :| [(Nothing,rightType)]) do
        proposition <- instantiateResolvedRelation resolved 2 (formal 1 leftType) (formal 0 rightType)
        pure (case sign of Raw.Positive -> proposition; Raw.Negative -> negatedCompiledProposition proposition)
    checking <- currentSourceTermCheckingContext
    predicate <- calculationWork location (Calculation.calculationCoreWork (\work -> countedCheckScopedCanonicalCore
        (SourceTerm.sourceTermGlobalTyping checking) work (SourceTerm.sourceTermBinderTypes checking)
        (CLam leftType (CLam rightType (compiledPropositionCore symbolic)))))
    description <- calculationExpansion location (SourceTemplate.abstractSourceProposition (Vector.fromList [1,0])
        (compiledPropositionEvidence symbolic) (compiledPropositionEqualities symbolic))
    providers <- calculationExpansion location (resolveSourceTemplateProviders location description)
    let ResolvedSourceRelation captures _ = resolved
        template = CalculationTemplate predicate symbolic description providers captures captures
    applyCalculationTemplateHere location template left right

applyCalculationTemplateHere
    :: Location -> CalculationTemplate -> CompiledSourceTerm -> CompiledSourceTerm
    -> Elaborate CheckedCalculationApplication
applyCalculationTemplateHere location template@(CalculationTemplate predicate symbolic description providers _ _) left right = do
    checking <- currentSourceTermCheckingContext
    instantiated <- calculationExpansion location (SourceTemplate.instantiateSourceTemplate checking providers location
        (LocatedSourceTerm location) (SourceEvidence.WrittenOrigin location Nothing)
        (Vector.fromList [1,0]) (Vector.fromList [left,right]) (compiledPropositionCore symbolic) description)
    proposition <- case instantiated of
        SourceTemplate.InstantiatedProposition formula evidence equalities ->
            sealCompiledPropositionHere location (CompiledProposition formula evidence equalities)
        SourceTemplate.InstantiatedTerm{} -> impossible "a calculation template returned a term"
    left' <- sealSourceOccurrenceHere location checking left
    right' <- sealSourceOccurrenceHere location checking right
    relation <- calculationWork location (Calculation.prepareRelator (SourceTerm.sourceTermGlobalTyping checking) predicate)
    expected <- calculationWork location (Calculation.applyRelator (SourceTerm.sourceTermGlobalTyping checking) relation
        (SourceTerm.sourceTermOccurrenceCore left') (SourceTerm.sourceTermOccurrenceCore right'))
    actual <- calculationWork location (Calculation.normalizeCalculationCore (SourceTerm.sourceTermGlobalTyping checking)
        (elaboratedPropositionCore proposition))
    same <- calculationWork location (Calculation.calculationCoreWork (\work -> countedScopedCoreIdentity work expected actual))
    unless same (impossible "a calculation template changed its denotation")
    retained <- calculationWrittenOperands location checking proposition
    let CalculationTemplate original originalSource originalDescription originalProviders captures _ = template
        completed = CalculationTemplate original originalSource originalDescription originalProviders captures (captures <> retained)
    pure (CheckedCalculationApplication relation completed left' right' proposition)

-- Reuse the scoped source collector, with residual discovery disabled. Only
-- already written operands and their provider/pair children become captures.
calculationWrittenOperands
    :: Location -> SourceTerm.SourceTermCheckingContext ObjectId -> ElaboratedProposition -> Elaborate [CompiledSourceTerm]
calculationWrittenOperands location checking proposition = do
    let portable = fmap (fmap (SourceTerm.sourceSupportTemplate scopedCoreTerm) . sourceAssertionAtom)
            (SourceEvidence.writtenSourceEvidence (elaboratedPropositionEvidence proposition))
    inputs <- calculationWork location (Calculation.calculationCoreWork (\work -> ScopedSource.sourceTemplateInputs
        (SourceTerm.sourceTermGlobalTyping checking) work (SourceTerm.sourceTermBinderTypes checking)
        (scopedCoreTerm (elaboratedPropositionCore proposition)) portable))
    for inputs \input -> calculationExpansion location do
        description <- SourceTemplate.abstractSourceProposition Vector.empty (SourceInputs Nothing [SourceInput [] input]) []
        term <- case description of
            PropositionExpansion (SourceInputs _ [SourceInput [] value]) [] -> pure value
            _ -> impossible "a complete source operand changed shape during abstraction"
        let expansion = TermExpansion term
        providers <- resolveSourceTemplateProviders location expansion
        SourceTemplate.instantiateSourceTemplate checking providers location (LocatedSourceTerm location)
            (SourceEvidence.WrittenOrigin location Nothing) Vector.empty Vector.empty CTruth expansion >>= \case
                SourceTemplate.InstantiatedTerm value -> pure value
                _ -> impossible "a source operand instantiated to a proposition"

transportCalculationApplication
    :: Word -> Location -> ElaborationContext -> CheckedCalculationApplication
    -> ScopedSourceTerm -> ScopedSourceTerm
    -> Declaration.LoweringDriver (Either ElaborationError (CheckedCalculationApplication, Word))
transportCalculationApplication allowance location context (CheckedCalculationApplication _ template _ _ _) left right = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    (application,final) <- State.runStateT (applyCalculationTemplateHere location template
        (SourceTerm.forgetScopedSourceTermOccurrence left) (SourceTerm.forgetScopedSourceTermOccurrence right))
        initial{elaborationCalculationAllowance = Just allowance}
    pure (application,fromMaybe allowance (elaborationCalculationAllowance final))

abstractCalculationSource
    :: Vector Natural -> CheckedCalculationApplication -> ExpansionWork Identity SemanticRelationSource
abstractCalculationSource layout (CheckedCalculationApplication _ (CalculationTemplate _ symbolic _ _ captures _) _ _ _) = do
    body <- SourceTemplate.abstractSourceProposition layout (compiledPropositionEvidence symbolic) (compiledPropositionEqualities symbolic)
    operands <- for captures \capture -> do
        shifted <- expansionCoreWork (\work -> SourceTerm.countedShiftCanonicalSourceTermOccurrence work 2 0 capture)
        SourceTemplate.abstractSourceTerm layout 0 shifted
    pure (SemanticRelationSource body (Vector.fromList operands))


instantiateCompositionApplication
    :: Word -> Location -> ElaborationContext -> Calculation.CheckedCompositionLaw
    -> Map Natural (ScopedCheckedCore ObjectId)
    -> CheckedCalculationApplication -> CheckedCalculationApplication
    -> Declaration.LoweringDriver
        (Either ElaborationError ((CheckedCalculationApplication, [ElaboratedProposition], [ScopedCheckedCore ObjectId]), Word))
instantiateCompositionApplication allowance location context law bindings previous next = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    (result,final) <- State.runStateT instantiate initial{elaborationCalculationAllowance = Just allowance}
    pure (result,fromMaybe allowance (elaborationCalculationAllowance final))
  where
    metadata = Calculation.compositionLawMetadata law
    types = Calculation.compositionLawTypes law
    count = Vector.length types
    (x,y,z) = compositionEndpointPositions metadata
    written (CheckedCalculationApplication _ (CalculationTemplate _ _ _ _ _ views) left right _) =
        [SourceTerm.forgetScopedSourceTermOccurrence left, SourceTerm.forgetScopedSourceTermOccurrence right] <> views
    source value = SourceTerm.sourceTermOccurrence (scopedCoreTerm value) (scopedCoreType value) (LocatedSourceTerm location)
    instantiate = do
        checking <- currentSourceTermCheckingContext
        normalized <- calculationExpansion location (traverse (SourceTerm.normalizeCanonicalSourceTermOccurrence checking)
            (written previous <> written next))
        views <- calculationExpansion location (concat <$> traverse collect normalized)
        let endpoint position
                | position == x = Just (calculationLeftSource previous)
                | position == y = Just (calculationRightSource previous)
                | position == z = Just (calculationRightSource next)
                | otherwise = Nothing
        actuals <- Vector.imapM (\index _ -> case endpoint (fromIntegral index) of
            Just value -> pure (SourceTerm.forgetScopedSourceTermOccurrence value)
            Nothing -> maybe (impossible "a selected law left a parameter undetermined") (pure . source)
                (Map.lookup (fromIntegral (count-index-1)) bindings)) types
        associated <- fmap Map.fromList $ for (zip [0..] (toList actuals)) \(position,actual) -> do
            matches <- if isJust (endpoint position) || compiledSourceTermType actual /= TySet then pure []
                else filterM (sameOperand actual) views
            pure (position,matches)
        let conditionLayout = Vector.fromList (reverse (take count [0..]))
        conditions <- for (zip (toList (Calculation.compositionLawConditions law)) (toList (compositionConditions metadata)))
            \(condition,description) -> do
                proposition <- instantiateSource checking conditionLayout actuals associated (scopedCoreTerm condition) description
                sealCompiledPropositionHere location proposition
        let (leftType,rightType) = Calculation.relatorEndpointTypes (Calculation.compositionLawResult law)
            outputBody = case scopedCoreTerm (Calculation.compositionLawOutputTemplate law) of
                CLam _ (CLam _ body) -> body
                _ -> impossible "a composition output lost its endpoint binders"
            outputLayout = Vector.fromList ([1,0] <> reverse (take count [2..]))
            formal index ty = SourceTerm.sourceTermOccurrence (CBound index) ty (LocatedSourceTerm location)
        symbolic <- withLexicalBinders ((Nothing,leftType) :| [(Nothing,rightType)]) do
            checking' <- currentSourceTermCheckingContext
            captured <- traverse (shiftRelationOperand location 2) actuals
            extras <- traverse (traverse (shiftRelationOperand location 2)) associated
            instantiateSource checking' outputLayout
                (Vector.fromList [formal 1 leftType,formal 0 rightType] <> captured)
                (Map.mapKeysMonotonic (+2) extras) outputBody (relationSourceBody (compositionResultSource metadata))
        predicate <- calculationWork location (Calculation.calculationCoreWork (\work -> countedCheckScopedCanonicalCore
            (SourceTerm.sourceTermGlobalTyping checking) work (SourceTerm.sourceTermBinderTypes checking)
            (CLam leftType (CLam rightType (compiledPropositionCore symbolic)))))
        description <- calculationExpansion location (SourceTemplate.abstractSourceProposition (Vector.fromList [1,0])
            (compiledPropositionEvidence symbolic) (compiledPropositionEqualities symbolic))
        providers <- calculationExpansion location (resolveSourceTemplateProviders location description)
        used <- calculationWork location (canonicalFreeIndicesWith (Calculation.chargeCalculationWork 1)
            (scopedCoreTerm (Calculation.compositionLawOutputTemplate law)))
        let captures = [actual
                | (position,actual) <- zip [0..] (toList actuals)
                , Set.member (fromIntegral (count-position-1)) used]
            template = CalculationTemplate predicate symbolic description providers captures captures
        application <- applyCalculationTemplateHere location template
            (SourceTerm.forgetScopedSourceTermOccurrence (calculationLeftSource previous))
            (SourceTerm.forgetScopedSourceTermOccurrence (calculationRightSource next))
        checkedActuals <- traverse (sealSourceOccurrenceHere location checking) actuals
        pure (application,conditions,SourceTerm.sourceTermOccurrenceCore <$> toList checkedActuals)
    collect value = do
        chargeExpansion 1
        nested <- case SourceTerm.sourceTermOccurrenceProvider value of
            Just provider -> concat <$> traverse collect (toList (SourceTerm.sourceTermProviderArguments provider))
            Nothing -> case SourceTerm.sourceTermOccurrenceOrderedPair value of
                Just (left,right) -> (<>) <$> collect left <*> collect right
                Nothing -> pure []
        pure ([value | compiledSourceTermType value == TySet] <> nested)
    sameOperand actual view = calculationWork location do
        sameType <- Calculation.calculationCoreWork (\work -> countedCoreTypeIdentity work
            (compiledSourceTermType actual) (compiledSourceTermType view))
        if not sameType then pure False else Calculation.calculationCoreWork (\work -> countedCanonicalIdentity work
            (compiledSourceTermCore actual) (compiledSourceTermCore view))
    instantiateSource checking layout actuals views body description = calculationExpansion location do
        providers <- resolveSourceTemplateProviders location description
        extras <- SourceTemplate.sourceTemplateInputAnnotations layout views body
        SourceTemplate.instantiateSourceTemplate checking providers location (LocatedSourceTerm location)
            (SourceEvidence.WrittenOrigin location Nothing) layout actuals body description >>= \case
                SourceTemplate.InstantiatedProposition formula evidence equalities ->
                    pure (CompiledProposition formula (SourceEvidence.withSourceInputs extras evidence) equalities)
                SourceTemplate.InstantiatedTerm{} -> impossible "a composition template returned a term"

abstractPropositionSource
    :: Vector Natural -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> [ScopedSourceEqualityOccurrence] -> ExpansionWork Identity AbbreviationExpansion
abstractPropositionSource layout evidence equalities = do
    described <- SourceEvidence.traverseAtDepth (\_ atom -> chargeExpansion 1 >>
        traverseSourceNotionAssertionParts (pure . SourceTerm.forgetScopedSourceTermOccurrence) (pure . scopedCoreTerm) atom) evidence
    equations <- traverse (traverseSourceEqualityOccurrenceParts
        (pure . SourceTerm.forgetScopedSourceTermOccurrence) (pure . scopedCoreTerm)) equalities
    SourceTemplate.abstractSourceProposition layout described equations

conjoinElaboratedPropositions :: ElaboratedProposition -> ElaboratedProposition -> ElaboratedProposition
conjoinElaboratedPropositions (ElaboratedProposition left a leftEqualities) (ElaboratedProposition right b rightEqualities) =
    ElaboratedProposition (fromMaybe (impossible "source conjunction changed scope") (conjoinScopedCore left right))
        (SourceAnd (prefixWrittenOrigin ConjunctionLeft a) (prefixWrittenOrigin ConjunctionRight b))
        ((mapSourceEqualityOccurrencePath ConjunctionLeft <$> leftEqualities)
            <> (mapSourceEqualityOccurrencePath ConjunctionRight <$> rightEqualities))

prefixWrittenOrigin
    :: (ConjunctionPath -> ConjunctionPath)
    -> SourceEvidence term ScopedSourceNotionOccurrence -> SourceEvidence term ScopedSourceNotionOccurrence
prefixWrittenOrigin prefix = go
  where
    origin written = written{SourceEvidence.writtenOriginBodyPath = prefix (SourceEvidence.writtenOriginBodyPath written)}
    go = \case
        SourceResidual written -> SourceResidual (origin <$> written)
        SourceInputs written inputs -> SourceInputs (origin <$> written) inputs
        SourceWithInputs inputs body -> SourceEvidence.withSourceInputs inputs (go body)
        SourceAtom atom -> SourceAtom (maybe atom (\written -> withSourceNotionOrigin (origin written) atom) (sourceNotionWrittenOrigin atom))
        SourceAnd a b -> SourceAnd (go a) (go b)
        SourceBind body -> SourceBind (go body)
        SourceExists body -> SourceExists (go body)
        SourceOr a b -> SourceOr (go a) (go b)
        SourceIff a b -> SourceIff (go a) (go b)
        SourceRequire a b -> SourceRequire (go a) (go b)

sourceEvidenceWrittenOrigin :: SourceEvidence term ScopedSourceNotionOccurrence -> Maybe SourceEvidence.WrittenOrigin
sourceEvidenceWrittenOrigin = \case
    SourceResidual origin -> origin
    SourceInputs origin _ -> origin
    SourceWithInputs _ body -> sourceEvidenceWrittenOrigin body
    SourceAtom atom -> sourceNotionWrittenOrigin atom
    SourceAnd a b -> sourceEvidenceWrittenOrigin a <|> sourceEvidenceWrittenOrigin b
    SourceBind body -> sourceEvidenceWrittenOrigin body
    SourceExists body -> sourceEvidenceWrittenOrigin body
    SourceOr a b -> sourceEvidenceWrittenOrigin a <|> sourceEvidenceWrittenOrigin b
    SourceIff a b -> sourceEvidenceWrittenOrigin a <|> sourceEvidenceWrittenOrigin b
    SourceRequire a b -> sourceEvidenceWrittenOrigin a <|> sourceEvidenceWrittenOrigin b

closeCalculationProposition
    :: ScopedCheckedCore ObjectId -> Int -> Maybe ElaboratedProposition -> ElaboratedProposition -> ElaboratedProposition
closeCalculationProposition target binders condition (ElaboratedProposition _ evidence equalities) =
    ElaboratedProposition target (iterate SourceBind guarded !! binders)
        (if binders == 0 && isNothing condition then equalities else [])
  where
    guarded = maybe evidence (\premise -> SourceRequire (elaboratedPropositionEvidence premise) evidence) condition

equalityCalculationApplication
    :: Word -> Location -> ElaborationContext -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> Declaration.LoweringDriver (Either ElaborationError (CheckedCalculationApplication,Word))
equalityCalculationApplication allowance location context left right = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    (result,final) <- State.runStateT (do
        let operand value = SourceTerm.sourceTermOccurrence (scopedCoreTerm value) (scopedCoreType value) (LocatedSourceTerm location)
            a = operand left
            b = operand right
        resolved <- resolveNamedRelationTerms location Raw.EqSymbol [] a b
        compileResolvedCalculation location Raw.Positive resolved a b)
        initial{elaborationCalculationAllowance = Just allowance}
    pure (result,fromMaybe allowance (elaborationCalculationAllowance final))

checkElaboratedNamedSetConstruction
    :: ElaborationState
    -> [CoreType]
    -> CompiledNamedSetConstruction
    -> Either ElaborationError ElaboratedSetConstruction
checkElaboratedNamedSetConstruction state =
    checkCompiledNamedSetConstruction (elaborationGlobalTyping state)

checkCompiledNamedSetConstruction
    :: GlobalTyping ObjectId
    -> [CoreType]
    -> CompiledNamedSetConstruction
    -> Either ElaborationError ElaboratedSetConstruction
checkCompiledNamedSetConstruction globalTyping context = \case
    CompiledSeparationConstruction bound predicate -> do
        checkedBound <- checkAt context TySet bound
        checkedPredicate <- checkAt (TySet : context) TyProp predicate
        maybe
            (Left
                (ElaborationCoreCheckFailed
                    Nowhere
                    (ExpectedCoreType TySet TyProp)))
            (Right . ElaboratedUnconditionalSetConstruction)
            (checkedSeparationConstruction
                globalTyping checkedBound checkedPredicate)
    CompiledFunctionalReplacementConstruction domains value condition -> do
        let domainList = NonEmpty.toList domains
            fullContext = replicate (length domainList) TySet <> context
        checkedDomains <-
            traverse
                (\(depth, domain) ->
                    checkAt
                        (replicate depth TySet <> context)
                        TySet
                        domain)
                (zip [0..] domainList)
        checkedValue <- checkAt fullContext TySet value
        checkedCondition <- traverse (checkAt fullContext TyProp) condition
        maybe
            (Left
                (ElaborationCoreCheckFailed
                    Nowhere
                    (ExpectedCoreType TySet TyProp)))
            (Right . ElaboratedUnconditionalSetConstruction)
            (checkedFunctionalReplacementConstruction
                globalTyping
                (NonEmpty.fromList checkedDomains)
                checkedValue
                checkedCondition)
    CompiledRelationalReplacementConstruction domain relation -> do
        checkedDomain <- checkAt context TySet domain
        checkedRelation <- checkAt (TySet : TySet : context) TyProp relation
        maybe
            (Left
                (ElaborationCoreCheckFailed
                    Nowhere
                    (ExpectedCoreType TySet TyProp)))
            (Right . ElaboratedRelationalSetConstruction)
            (checkedRelationalReplacementConstruction
                globalTyping checkedDomain checkedRelation)
  where
    checkAt expectedContext expectedType term = do
        checked <-
            first
                (ElaborationCoreCheckFailed Nowhere)
                (checkScopedCanonicalCore globalTyping expectedContext term)
        unless
            (scopedCoreType checked == expectedType)
            (Left
                (ElaborationCoreCheckFailed
                    Nowhere
                    (ExpectedCoreType
                        expectedType
                        (scopedCoreType checked))))
        pure checked

preparedSetConstructionTerm
    :: ElaboratedSetConstruction
    -> ScopedCheckedCore ObjectId
preparedSetConstructionTerm = \case
    ElaboratedUnconditionalSetConstruction construction ->
        namedSetConstructionTerm construction
    ElaboratedRelationalSetConstruction construction ->
        relationalSetConstructionTerm construction

preparedSetConstructionClosedBody
    :: ElaboratedSetConstruction
    -> FrozenCheckedCore ObjectId
preparedSetConstructionClosedBody = \case
    ElaboratedUnconditionalSetConstruction construction ->
        namedSetConstructionClosedBody construction
    ElaboratedRelationalSetConstruction construction ->
        relationalSetConstructionClosedBody construction

elaborateLocalFunctionGraph
    :: Location
    -> ElaborationContext
    -> ElaborationContext
    -> Raw.Expr
    -> Raw.Expr
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedLocalFunctionGraph)
elaborateLocalFunctionGraph
        location context argumentContext domainExpression valueExpression =
    Except.runExceptT do
        domain <-
            elaboratedSetExpressionCore
                <$> ( Trans.lift
                        (elaborateSetExpression context domainExpression)
                        >>= Except.liftEither
                    )
        value <-
            elaboratedSetExpressionCore
                <$> ( Trans.lift
                        (elaborateSetExpression
                            argumentContext valueExpression)
                        >>= Except.liftEither
                    )
        pair <- prepareOrderedPair
        case scopedReplacementGraph pair domain value of
            Just (graph, checkedDomain, function) ->
                pure
                    (ElaboratedLocalFunctionGraph
                        graph checkedDomain function)
            Nothing ->
                impossible
                    "checked local-function components did not form a replacement graph"
  where
    prepareOrderedPair = do
        initialElaboration <- prepareInitialElaborationState context
        either
            (Except.throwError . ElaborationCoreCheckFailed location)
            pure
            (checkScopedCanonicalCore
                (elaborationGlobalTyping initialElaboration)
                (binderTypes context)
                (CIntrinsic OrderedPair))

elaborateClaimEnvelope
    :: [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedClaimEnvelope)
elaborateClaimEnvelope assumptions statement =
    elaborateClaimEnvelopeFromContext
        Nothing emptyElaborationContext assumptions statement

-- Observe the immutable formation snapshot while claim headers are active.
-- Ordinary claim envelopes deliberately retain only their outer binder context.
-- This callback supplies no proof authority and cannot alter elaboration state.
elaborateClaimEnvelopeWithFormationObservation
    :: (ElaborationContext -> observation)
    -> [Raw.Asm] -> Raw.Stmt
    -> Declaration.LoweringDriver (Either ElaborationError (ElaboratedClaimEnvelope, observation))
elaborateClaimEnvelopeWithFormationObservation observe =
    elaborateClaimEnvelopeObservedFromContext observe Nothing emptyElaborationContext

elaborateClaimEnvelopeWithLocalTransparentObject
    :: Location
    -> SemanticGlobalKey
    -> AssertedObject
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedClaimEnvelope)
elaborateClaimEnvelopeWithLocalTransparentObject
        location key asserted assumptions statement =
    case content of
        TransparentObjectContent{}
            | semanticGlobalKeyType key == Just actualType ->
                elaborateClaimEnvelopeFromContext
                    (Just asserted)
                    (ElaborationContext
                        []
                        (Map.singleton
                            key
                            (LocalTransparentExpansion asserted))
                        emptyFormationScope)
                    assumptions
                    statement
            | Just expectedType <- semanticGlobalKeyType key ->
                pure
                    (Left
                        (ElaborationObjectTypeMismatch
                            location expectedType actualType))
        _ ->
            pure (Left (ElaborationUnsupportedDeclaration location))
  where
    content = assertedObjectContent asserted
    actualType = objectContentType content

elaborateClaimEnvelopeFromContext
    :: Maybe AssertedObject
    -> ElaborationContext
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either ElaborationError ElaboratedClaimEnvelope)
elaborateClaimEnvelopeFromContext localObject initial assumptions statement =
    fmap (fmap fst) (elaborateClaimEnvelopeObservedFromContext (const ()) localObject initial assumptions statement)

elaborateClaimEnvelopeObservedFromContext
    :: (ElaborationContext -> observation)
    -> Maybe AssertedObject
    -> ElaborationContext
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver (Either ElaborationError (ElaboratedClaimEnvelope, observation))
elaborateClaimEnvelopeObservedFromContext observe localObject initial assumptions statement =
    Except.runExceptT (prepareFormationContext (locate statement) initial)
        >>= either (pure . Left) (discover [])
  where
    discover variables context = do
        attempted <-
            elaborateClaimAttempt observe localObject context assumptions statement
        case attempted of
            Left (ElaborationFreeVariable _location variable)
                | variable `elem` variables ->
                    impossible
                        "exact claim discovery repeated an active free variable"
                | otherwise ->
                    case extendElaborationContext
                            ( ( localId
                                    (fromIntegral (length variables))
                              , variable
                              ) :| []
                            )
                            context of
                        Left failure ->
                            pure (Left failure)
                        Right extended ->
                            discover (variables <> [variable]) extended
            Left failure ->
                pure (Left failure)
            Right
                    ( target
                    , antecedents
                    , conclusionAssertions
                    , conclusionEqualities
                    , structures
                    , observation
                    ) ->
                pure
                    (Right
                        (ElaboratedClaimEnvelope
                            target
                            variables
                            (annotateBinderContext structures context)
                            antecedents
                            conclusionAssertions
                            conclusionEqualities, observation))

elaborateClaimAttempt
    :: (ElaborationContext -> observation)
    -> Maybe AssertedObject
    -> ElaborationContext
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Declaration.LoweringDriver
        (Either
            ElaborationError
            ( ScopedCheckedCore ObjectId
            , [CompiledHeaderAntecedent]
            , SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
            , [ScopedSourceEqualityOccurrence]
            , Map.Map Natural ResolvedStructureApplication
            , observation
            ))
elaborateClaimAttempt observe localObject context assumptions statement =
    Except.runExceptT do
        initialElaboration <-
            prepareOwnerLocalElaborationState localObject context
        (((antecedents, conclusion), observation), finalElaboration) <-
            State.runStateT
                (compileClaimHeaders 0 assumptions [])
                initialElaboration
        let checkedAntecedents = compiledHeaderCore <$> antecedents
            checkedConclusion = elaboratedPropositionCore conclusion
        let implication =
                foldr
                    (\antecedent continuation ->
                        fromMaybe
                            (impossible
                                "checked claim antecedents have unequal contexts")
                            (implyScopedCore antecedent continuation))
                    checkedConclusion
                    checkedAntecedents
            closed = closeClaimBinders implication
        unless (null (scopedCoreContext closed))
            (impossible "exact claim closure retained a binder")
        pure
            ( closed
            , antecedents
            , elaboratedPropositionEvidence conclusion
            , elaboratedPropositionEqualities conclusion
            , lexicalStructures (elaborationScope finalElaboration)
            , observation
            )
  where
    compileClaimHeaders _sourceOrdinal [] reversed = do
        conclusion <-
            compileStatement statement
                >>= sealCompiledPropositionHere (locate statement)
        state <- State.get
        let scope = lexicalFormationScope (elaborationScope state)
            ElaborationContext binders overrides _ = annotateBinderContext (lexicalStructures (elaborationScope state)) context
            snapshot = ElaborationContext binders overrides scope
        pure ((reverse reversed, conclusion), observe snapshot)
    compileClaimHeaders sourceOrdinal (assumption : remaining) reversed = do
        batch <-
            compileHeaderAssumptionCompiled sourceOrdinal assumption
        checkedRows <- sealAndCommitHeaderBatch batch
        let checked = snd <$> checkedRows
        withHeaderGuards checked
            (compileClaimHeaders
                (sourceOrdinal + 1)
                remaining
                (reverse checked <> reversed))

    withHeaderGuards [] action = action
    withHeaderGuards (header : remaining) action =
        withCheckedFormationGuard
            FormationClaimHeader
            (checkedHeaderProposition header)
            (withHeaderGuards remaining action)

checkEnvelopeProposition
    :: ElaborationState
    -> ElaborationContext
    -> Location
    -> CanonicalTerm ObjectId
    -> ExceptT
        ElaborationError
        (Declaration.LoweringDriver)
        (ScopedCheckedCore ObjectId)
checkEnvelopeProposition elaboration context location term = do
    let globalTyping = elaborationGlobalTyping elaboration
    traverse_
        (Except.throwError . ElaborationCoreGlobalsMissing location)
        (missingCanonicalGlobalTypes globalTyping term)
    checked <-
        either
            (Except.throwError . ElaborationCoreCheckFailed location)
            pure
            (checkScopedCanonicalCore
                (elaborationGlobalTyping elaboration)
                (binderTypes context)
                term)
    unless (scopedCoreType checked == TyProp)
        (Except.throwError
            (ElaborationFormulaExpectedProposition
                location
                (scopedCoreType checked)))
    pure checked

closeClaimBinders
    :: ScopedCheckedCore global
    -> ScopedCheckedCore global
closeClaimBinders scoped =
    case scopedCoreContext scoped of
        [] -> scoped
        _binder : _remaining ->
            closeClaimBinders
                (fromMaybe
                    (impossible
                        "a checked claim binder could not be closed")
                    (closeScopedForall scoped))

binderIndices
    :: ElaborationContext
    -> Map.Map Raw.VarSymbol (Natural, CoreType)
binderIndices
        (ElaborationContext binders _overrides _scope) =
    Map.fromList
        [ (variable, (fromIntegral index, coreType))
        | (index, ElaborationBinder _identity (Just variable) coreType _structure) <-
            zip [0 :: Int ..] binders
        ]

binderStructures
    :: ElaborationContext
    -> Map.Map Natural ResolvedStructureApplication
binderStructures
        (ElaborationContext binders _overrides _scope) =
    Map.fromList
        [ (fromIntegral index, structure)
        | (index, ElaborationBinder _identity _variable _coreType (Just structure)) <-
            zip [0 :: Int ..] binders
        ]

binderTypes :: ElaborationContext -> [CoreType]
binderTypes
        (ElaborationContext binders _overrides _scope) =
    [ coreType
    | ElaborationBinder _identity _variable coreType _structure <- binders
    ]

initialElaborationState
    :: CheckedObjectClosure
    -> ElaborationContext
    -> ElaborationState
initialElaborationState closure context =
    initialElaborationStateWithNaturalNumeralBasis Nothing closure context

initialElaborationStateWithNaturalNumeralBasis
    :: Maybe Declaration.NaturalNumeralBasis
    -> CheckedObjectClosure
    -> ElaborationContext
    -> ElaborationState
initialElaborationStateWithNaturalNumeralBasis basis closure context =
    ElaborationState
        { elaborationScope = LexicalScope
            { lexicalBinders = binderIndices context
            , lexicalBinderStack = BinderStack (binderTypes context)
            , lexicalStructures = binderStructures context
            , lexicalContextualBinder = Nothing
            , lexicalFormationScope = formationScopeFromContext context
            }
        , elaborationObjectClosure = closure
        , elaborationNaturalNumeralBasis = basis
        , elaborationLocalGlobalDefinitions =
            contextLocalGlobalDefinitions context
        , elaborationContextualRequirements = mempty
        , elaborationProofSupport = elaborationContextSupport context
        , elaborationDefinitionContract = Nothing
        , elaborationDefinitionBaseProjections = []
        , elaborationPreparedDefinitionResults = Nothing
        , elaborationDefinitionProvider = Nothing
        , elaborationExpansionAllowance = Nothing
        , elaborationCalculationAllowance = Nothing
        }

beginAbbreviationExpansion :: Elaborate ()
beginAbbreviationExpansion = State.modify' (\state -> state {elaborationExpansionAllowance = Just formationMaximumExpansionWork})

initialBindingElaborationState
    :: CheckedObjectClosure
    -> ElaborationState
initialBindingElaborationState closure =
    initialElaborationState closure emptyElaborationContext

initialStructureElaborationState
    :: CheckedObjectClosure
    -> ElaborationContext
    -> ElaborationState
initialStructureElaborationState =
    initialElaborationState

initialElaborationStateLowering
    :: CheckedObjectClosure
    -> ElaborationContext
    -> Declaration.LoweringDriver ElaborationState
initialElaborationStateLowering closure context = do
    basis <- Declaration.naturalNumeralBasisLowering
    case basis of
        Nothing ->
            pure
                (initialElaborationStateWithNaturalNumeralBasis
                    Nothing closure context)
        Just checked
            | isJust
                (lookupCheckedObjectContent
                    (Declaration.naturalNumeralBasisObject checked)
                    closure) ->
                pure
                    (initialElaborationStateWithNaturalNumeralBasis
                        (Just checked) closure context)
            | otherwise ->
                liftIO
                    (throwIO
                        (Declaration.PlanningIntegrityError
                            "the natural-numeral basis object is absent from the selected elaboration closure"))

prepareInitialElaborationState
    :: ElaborationContext
    -> Except.ExceptT
        ElaborationError
        Declaration.LoweringDriver
        ElaborationState
prepareInitialElaborationState context = do
    prepared <- prepareFormationContext Nowhere context
    baseClosure <-
        Trans.lift Declaration.checkedObjectClosureLowering
    Trans.lift (initialElaborationStateLowering baseClosure prepared)

-- | A narrow single-object exception to committed visibility.  The
-- declaration owner supplies one exact asserted object; extending the
-- validated base closure rechecks its identity, content, dependencies, and
-- type before any checked syntax can mention it.  No reusable overlay or
-- snapshot escapes.
prepareOwnerLocalElaborationState
    :: Maybe AssertedObject
    -> ElaborationContext
    -> Except.ExceptT
        ElaborationError
        Declaration.LoweringDriver
        ElaborationState
prepareOwnerLocalElaborationState localObject context = do
    prepared <- prepareFormationContext Nowhere context
    baseClosure <-
        Trans.lift Declaration.checkedObjectClosureLowering
    closure <-
        case localObject of
            Nothing ->
                pure baseClosure
            Just asserted
                | lookupCheckedObjectContent
                        (assertedObjectId asserted) baseClosure
                    == Just (assertedObjectContent asserted) ->
                    pure baseClosure
                | otherwise ->
                    Except.liftEither
                        (first ElaborationProspectiveObjectInvalid
                            (extendObjectClosure baseClosure [asserted]))
    Trans.lift (initialElaborationStateLowering closure prepared)

annotateBinderContext
    :: Map.Map Natural ResolvedStructureApplication
    -> ElaborationContext
    -> ElaborationContext
annotateBinderContext structures
        (ElaborationContext binders overrides scope) =
    ElaborationContext
        [ ElaborationBinder identity variable coreType
            (Map.lookup (fromIntegral index) structures)
        | (index, ElaborationBinder identity variable coreType _old) <-
            zip [0 :: Int ..] binders
        ]
        overrides
        scope

contextLocalGlobalDefinitions
    :: ElaborationContext
    -> Map.Map SemanticGlobalKey LocalGlobalDefinition
contextLocalGlobalDefinitions
        (ElaborationContext
            _binders overrides _scope) =
    overrides

contextFormationSources
    :: ElaborationContext
    -> [FormationPremiseSource]
contextFormationSources = formationScopeSources . formationScopeFromContext

contextFormationAliases
    :: ElaborationContext
    -> [FormationAliasSource]
contextFormationAliases = formationScopeAliases . formationScopeFromContext

compileHeaderAssumption
    :: Raw.Asm
    -> Elaborate [(Location, CanonicalTerm ObjectId)]
compileHeaderAssumption assumption =
    fmap (fmap (scopedCoreTerm . elaboratedPropositionCore))
        <$> compileHeaderAssumptionPropositions assumption

-- | Compile one declaration header without erasing its source-notion
-- assertions.  Structure lowering uses this boundary so each checked preamble
-- conjunct can license vocabulary in later structure components while the
-- ordinary predicate body retains its existing Core ordering.
compileHeaderAssumptionPropositions
    :: Raw.Asm
    -> Elaborate [(Location, ElaboratedProposition)]
compileHeaderAssumptionPropositions assumption = do
    batch <- compileHeaderAssumptionCompiled 0 assumption
    fmap (fmap checkedHeaderProposition)
        <$> sealAndCommitHeaderBatch batch

-- | Compile a transparent predicate's complete logical definition. Positive
-- atoms have the same forward-view policy for every grammatical surface.
-- The noun's distinguished base affects its source contract, not projection.
compilePredicateDefinition
    :: Maybe OccurrenceArgumentIx
    -> [Raw.Asm]
    -> Raw.Stmt
    -> Elaborate CompiledBody
compilePredicateDefinition distinguishedBase assumptions statement = do
    parameterCount <-
        State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
    (headers, templates, _antecedents, body) <-
        compileHostedDefinitionHeaders
            (locate statement)
            assumptions
            (const (compileHostedPredicateStatement statement))
    let uniqueTemplates =
            stableNubTemplates
                [ template
                | template <- templates
                , not (isPreservedNounBase template)
                ]
        contract = formationContract <$> NonEmpty.nonEmpty uniqueTemplates
        compiled = conjoinCompiled (headers <> [body])
    checked <- sealCompiledPropositionHere (locate statement) compiled
    leaves <- prepareFormationScopeHere (locate statement) $ SourceEvidence.notionLeaves (scopePreparationCharge 1)
        (\right path -> pure (path . if right then ConjunctionRight else ConjunctionLeft)) id
        (elaboratedPropositionCore checked) (elaboratedPropositionEvidence checked)
    candidates <- fmap catMaybes (traverse (definitionProjection parameterCount) leaves)
    let projections = stableDefinitionProjections candidates
    State.modify' \state ->
        state
            { elaborationDefinitionContract = contract
            , elaborationDefinitionBaseProjections = projections
            }
    pure (ordinaryCompiledBody (compiledPropositionCore compiled))
  where
    isPreservedNounBase (AtomicLeaf template) =
        maybe False (`isDistinguishedBase` template) distinguishedBase
    isPreservedNounBase WholeLeaf{} = False

    isDistinguishedBase subject = \case
        NegativeAtomTemplate{} -> False
        GlobalAtomTemplate head' arguments ->
            globalNotionHeadRole head' == HostedGlobalNotion
                && arguments Vector.!? 0
                    == Just (TemplateVariable subject)
        StructureAtomTemplate _head arguments ->
            arguments Vector.!? 0
                == Just (TemplateVariable subject)
        MembershipAtomTemplate element _set ->
            element == TemplateVariable subject
        ExactStructureAtomTemplate _ focus -> focus == TemplateVariable subject

    stableDefinitionProjections =
        reverse . snd . foldl' retainFirst (Set.empty, [])
      where
        retainFirst (seen, retained) candidate
            | key `Set.member` seen = (seen, retained)
            | otherwise =
                (Set.insert key seen, candidate : retained)
          where
            key = definitionBaseProjectionTemplate candidate

    definitionProjection parameterCount leaf = do
        template <- case SourceEvidence.sourceLeafDescription leaf of
            SourceEvidence.LeafAtom assertion -> fmap (fmap AtomicLeaf)
                (traverseAtomTemplateArgumentsM
                    (projectionTermTemplate parameterCount . SourceTerm.forgetScopedSourceTermOccurrence)
                    (sourceAssertionAtom assertion))
            _ -> pure (either (const Nothing) (Just . WholeLeaf) (NotionPremise.describeResidual parameterCount
                (SourceEvidence.sourceLeafFormula leaf) (SourceEvidence.sourceLeafEvidence leaf)))
        pure ((\value -> DefinitionBaseProjection value
            (scopedCoreTerm (SourceEvidence.sourceLeafFormula leaf))
            (SourceEvidence.sourceLeafPath leaf ConjunctionHere)) <$> template)

    projectionTermTemplate parameterCount occurrence
        | compiledSourceTermType occurrence /= TySet = pure Nothing
        | Just provider <- SourceTerm.sourceTermOccurrenceProvider occurrence = do
            let providerHead = SourceTerm.sourceTermProviderHead provider
            approved <- templateProviderApproved (locate statement) providerHead
            if approved
            then do
                arguments <- traverse
                    (projectionTermTemplate parameterCount)
                    (SourceTerm.sourceTermProviderArguments provider)
                pure (TemplateProvider providerHead <$> sequenceA arguments)
            else pure Nothing
        | Just (left, right) <-
                SourceTerm.sourceTermOccurrenceOrderedPair occurrence = do
            leftTemplate <- projectionTermTemplate parameterCount left
            rightTemplate <- projectionTermTemplate parameterCount right
            pure (TemplateOrderedPair <$> leftTemplate <*> rightTemplate)
        | CBound index <- compiledSourceTermCore occurrence
        , index < parameterCount =
            pure
                (Just
                    (TemplateVariable
                        (OccurrenceArgumentIx (parameterCount - index - 1))))
        | otherwise = fmap TemplateClosed <$> compileClosedFormationValue (locate statement) occurrence

compileClosedFormationValue :: Location -> CompiledSourceTerm -> Elaborate (Maybe ClosedSetValue)
compileClosedFormationValue location occurrence = do
    context <- currentSourceTermCheckingContext
    checked <- checkSourceTermHere location context TySet (compiledSourceTermCore occurrence)
    pure (closedSetValue checked)

-- | Compile only the outer positive conjunction spine of a hosted predicate
-- from left to right.  Earlier conjuncts are formation guards for later
-- conjuncts, but remain ordinary logical conjuncts of the definition body.
compileHostedPredicateStatement
    :: Raw.Stmt
    -> Elaborate CompiledProposition
compileHostedPredicateStatement = \case
    Raw.StmtConnected Raw.Conjunction _location left right -> do
        compiledLeft <- compileHostedPredicateStatement left
        checkedLeft <-
            sealCompiledPropositionHere (locate left) compiledLeft
        compiledRight <-
            withCheckedFormationGuard
                FormationHostedDefinitionConjunct
                checkedLeft
                (compileHostedPredicateStatement right)
        pure (conjoinCompiled [compiledLeft, compiledRight])
    statement -> compileStatement statement

-- | Compile a total set-valued definition under checked source headers.  The
-- headers constrain written applications and guard the body during
-- elaboration, but they are not logical conjuncts of the resulting set term.
compileHostedSetTermDefinition
    :: Location
    -> [Raw.Asm]
    -> Maybe Raw.DefinitionResultPhrase
    -> Elaborate (CompiledBody, CompiledSourceTerm)
    -> Elaborate CompiledBody
compileHostedSetTermDefinition location assumptions maybeResult compileBody =
    fst <$> compileHostedSetTermDefinitionWithFormationObservation (const ()) location assumptions maybeResult compileBody

-- Construction hypotheses guard the body and its proved results. The named
-- set term remains total: these hypotheses are not a source-call contract.
-- Result registration separately checks the claim's complete premise forest.
compileHostedConstructionDefinition
    :: Location -> [Raw.Asm] -> Raw.Expr -> Elaborate CompiledBody
compileHostedConstructionDefinition _location assumptions expression = do
    (_headers, _antecedents, body) <-
        compileHostedHeaders ConstructionHeaders assumptions
            (const (fst <$> compileNamedSetExpressionWithSource expression))
    pure body

-- Observe after result preparation, before the checked header guards leave
-- scope. The callback cannot alter elaboration or supply evidence to it.
compileHostedSetTermDefinitionWithFormationObservation
    :: (ElaborationState -> observation)
    -> Location -> [Raw.Asm] -> Maybe Raw.DefinitionResultPhrase
    -> Elaborate (CompiledBody, CompiledSourceTerm)
    -> Elaborate (CompiledBody, observation)
compileHostedSetTermDefinitionWithFormationObservation observe location assumptions maybeResult compileBody = do
    (_headers, templates, _antecedents, body) <-
        compileHostedDefinitionHeaders location assumptions
            \antecedents -> do
                (compiledBody, bodySource) <- compileBody
                preparedResults <- traverse
                    (prepareDefinitionResults
                        location antecedents bodySource)
                    maybeResult
                State.modify' \state ->
                    state
                        { elaborationPreparedDefinitionResults = preparedResults }
                observation <- State.gets observe
                pure (compiledBody, observation)
    State.modify' \state ->
        state
            { elaborationDefinitionContract =
                formationContract
                    <$> NonEmpty.nonEmpty (stableNubTemplates templates)
            }
    pure body

compileHostedDefinitionHeaders
    :: Location
    -> [Raw.Asm]
    -> ([CompiledHeaderAntecedent] -> Elaborate body)
    -> Elaborate
        ( [CompiledProposition]
        , [FormationRequirement]
        , [CompiledHeaderAntecedent]
        , body
        )
compileHostedDefinitionHeaders location assumptions compileBody = do
    parameterCount <-
        State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
    (headers, antecedents, body) <-
        compileHostedHeaders DefinitionHeaders assumptions compileBody
    templates <- compileFormationHeaderRequirements location parameterCount antecedents
    pure (headers, templates, antecedents, body)

data HostedHeaderPolicy = DefinitionHeaders | ConstructionHeaders

compileHostedHeaders
    :: HostedHeaderPolicy -> [Raw.Asm]
    -> ([CompiledHeaderAntecedent] -> Elaborate body)
    -> Elaborate ([CompiledProposition], [CompiledHeaderAntecedent], body)
compileHostedHeaders policy assumptions compileBody = compileHeaders 0 assumptions [] []
  where
    compileHeaders _sourceOrdinal [] reversed reversedAntecedents = do
        let antecedents = reverse reversedAntecedents
        body <- compileBody antecedents
        pure (reverse reversed, antecedents, body)
    compileHeaders sourceOrdinal (assumption : remaining)
            reversed reversedAntecedents = do
        case (policy, assumption) of
            (ConstructionHeaders, _) -> pure ()
            (_, Raw.AsmLetNoun{}) -> pure ()
            (_, Raw.AsmLetIn{}) -> pure ()
            (_, Raw.AsmLetRelation{}) -> pure ()
            (_, Raw.AsmLetStruct{}) -> pure ()
            _ ->
                Except.throwError
                    (ElaborationGuardedTransparentDefinition
                        (headerAssumptionLocation assumption))
        batch <-
            compileHeaderAssumptionCompiled sourceOrdinal assumption
        let propositions =
                compiledHeaderRowProposition
                    <$> compiledHeaderBatchRows batch
        checked <- sealAndCommitHeaderBatch batch
        let antecedents = snd <$> checked
        withGuards checked
            (compileHeaders
                (sourceOrdinal + 1)
                remaining
                (reverse propositions <> reversed)
                (reverse antecedents <> reversedAntecedents))

    withGuards [] action = action
    withGuards
            ((headerLocation, header) : remaining)
            action =
        withCheckedDefinitionHeaderGuard
            (compiledHeaderSourceOrdinal header)
            (compiledHeaderVariableOrdinal header)
            headerLocation
            (checkedHeaderProposition header)
            (withGuards remaining action)

compileFormationHeaderRequirements
    :: Location -> Natural -> [CompiledHeaderAntecedent]
    -> Elaborate [FormationRequirement]
compileFormationHeaderRequirements location parameterCount antecedents = do
    leaves <- prepareFormationScopeHere location $ concat <$> for antecedents (\header -> SourceEvidence.notionLeaves (scopePreparationCharge 1)
        (\_ _ -> pure ()) () (compiledHeaderCore header) (compiledHeaderEvidence header))
    for leaves \leaf -> case SourceEvidence.sourceLeafDescription leaf of
        SourceEvidence.LeafAtom assertion -> AtomicLeaf <$> assertionTemplate assertion
        SourceEvidence.LeafUniversal universal -> WholeLeaf . WholeUniversal <$>
            UniversalTemplate.traverseBodyAtDepth (\depth assertion ->
                traverse (sourceTemplate (universalVariable parameterCount depth)
                    . SourceTerm.forgetScopedSourceTermOccurrence) (sourceAssertionAtom assertion)) universal
        SourceEvidence.LeafResidual{} -> pure (WholeLeaf (WholeResidual
            (ResidualTemplate (scopedCoreTerm (SourceEvidence.sourceLeafFormula leaf)))))
  where
    assertionTemplate = traverse
        (sourceTemplate (formalVariable parameterCount) . SourceTerm.forgetScopedSourceTermOccurrence)
        . sourceAssertionAtom

    formalVariable count index
        | index < count = pure (OccurrenceArgumentIx (count - index - 1))
        | otherwise = rejectUnsupported
    universalVariable count depth index
        | index < depth = pure (SourceEvidence.UniversalBound (depth - index - 1))
        | otherwise = SourceEvidence.UniversalOuter . TemplateVariable <$> formalVariable count (index - depth)

    sourceTemplate :: (Natural -> Elaborate variable) -> CompiledSourceTerm
        -> Elaborate (SetTermTemplate variable)
    sourceTemplate variable occurrence
        | compiledSourceTermType occurrence /= TySet = rejectUnsupported
        | Just provider <- SourceTerm.sourceTermOccurrenceProvider occurrence =
            providerTemplate provider
        | Just _ <- SourceTerm.sourceTermOccurrenceOrderedPair occurrence = rejectUnsupported
        | otherwise =
            case compiledSourceTermCore occurrence of
                CBound index -> TemplateVariable <$> variable index
                _ -> compileClosedFormationValue termLocation occurrence >>= \case
                    Just value -> pure (TemplateClosed value)
                    Nothing -> rejectUnsupported
      where
        termLocation = case compiledSourceTermPresentation occurrence of
            PresentedSourceTerm here _ -> here
            LocatedSourceTerm here -> here
        providerTemplate provider = do
            let providerHead = SourceTerm.sourceTermProviderHead provider
                providerArguments =
                    SourceTerm.sourceTermProviderArguments provider
            approved <- templateProviderApproved termLocation providerHead
            unless approved rejectUnsupported
            TemplateProvider providerHead
                <$> traverse
                    (sourceTemplate variable)
                    providerArguments

    rejectUnsupported :: Elaborate result
    rejectUnsupported = Except.throwError (ElaborationGuardedTransparentDefinition location)

templateProviderApproved
    :: Location
    -> SourceProviderHead
    -> Elaborate Bool
templateProviderApproved location providerHead = case providerHead of
    GlobalSourceProvider reference -> do
        let key = globalBindingRefKey reference
        (resolved, _content) <-
            resolveVisibleSourceGlobalContent location key
        pure
            ( resolvedBindingRef resolved == reference
              && resolvedBindingSourceProviderHead resolved
                    == Just providerHead
              && isNothing (resolvedBindingContract resolved)
            )
    StructureFieldSourceProvider identity projection -> do
        visible <-
            State.lift
                (Trans.lift
                    (Declaration.resolveVisibleStructureFieldProviderLowering
                        identity))
        pure (visible == Just projection)
    IntrinsicSourceProvider provider ->
        pure case firstOrderSymbolShape
                (coreIntrinsicType (intrinsicProviderCoreTag provider)) of
            Just (_arity, TySet) -> True
            _ -> False
    FiniteSetLiteralSourceProvider -> pure True

data DefinitionResultOccurrence = DefinitionResultOccurrence
    !PhraseAssertionCoordinate
    !ScopedSourceNotionOccurrence
    !CompiledSourceNotionAssertion
    !(AtomTemplate CompiledSourceTerm)
    !RichFormationGoalKey

definitionResultOccurrenceCoordinate
    :: DefinitionResultOccurrence
    -> PhraseAssertionCoordinate
definitionResultOccurrenceCoordinate
        (DefinitionResultOccurrence coordinate _assertion _compiled _atom _key) =
    coordinate

definitionResultOccurrenceAssertion
    :: DefinitionResultOccurrence
    -> ScopedSourceNotionOccurrence
definitionResultOccurrenceAssertion
        (DefinitionResultOccurrence _coordinate assertion _compiled _atom _key) =
    assertion

definitionResultOccurrenceCompiled
    :: DefinitionResultOccurrence
    -> CompiledSourceNotionAssertion
definitionResultOccurrenceCompiled
        (DefinitionResultOccurrence _coordinate _assertion compiled _atom _key) =
    compiled

definitionResultOccurrenceAtom
    :: DefinitionResultOccurrence
    -> AtomTemplate CompiledSourceTerm
definitionResultOccurrenceAtom
        (DefinitionResultOccurrence _coordinate _assertion _compiled atom _key) =
    atom

definitionResultOccurrenceKey
    :: DefinitionResultOccurrence
    -> RichFormationGoalKey
definitionResultOccurrenceKey
        (DefinitionResultOccurrence _coordinate _assertion _compiled _atom key) =
    key

-- | Require every nontrivial written phrase component to be exactly covered
-- by its own positive source-notion assertions. Canonical rich keys are
-- deduplicated only after this unreduced coverage check succeeds.
validateDefinitionResultOccurrences
    :: Raw.DefinitionResultPhrase
    -> [CompiledPhraseComponent]
    -> [PhraseAssertionCoordinate]
    -> ElaboratedProposition
    -> CompiledSourceTerm
    -> Elaborate (NonEmpty DefinitionResultOccurrence)
validateDefinitionResultOccurrences phrase components coordinates sealed
        bodySource = do
    traverse_ validateComponent components
    let assertions = elaboratedPropositionAssertions sealed
    unless (length coordinates == length assertions)
        (impossible
            "definition-result coordinates do not match checked assertions")
    occurrences <- traverse prepareOccurrence (zip coordinates assertions)
    retained <- stableDeduplicate occurrences
    maybe
        (Except.throwError
            (ElaborationDefinitionResultShapeUnsupported location))
        pure
        (NonEmpty.nonEmpty retained)
  where
    location = definitionResultPhraseLocation phrase

    validateComponent component =
        case phraseComponentKind component of
            PhraseHardSet ->
                unless (isNeutralCompiled proposition)
                    (impossible
                        "a definition result hard-set component is nonneutral")
            PhraseRegular ->
                unless
                    ( not (isNeutralCompiled proposition)
                      && null (compiledPropositionEqualities proposition)
                      && componentIsFullyCovered proposition
                    )
                    (Except.throwError
                        (ElaborationDefinitionResultShapeUnsupported location))
      where
        proposition = phraseComponentProposition component

    componentIsFullyCovered proposition =
        not (null assertions)
            && all projects assertions
            && covers
                (sourceAssertionPath <$> assertions)
                (compiledPropositionCore proposition)
      where
        assertions = compiledPropositionAssertions proposition
        projects assertion =
            projectConjunctionPath
                (sourceAssertionPath assertion)
                (compiledPropositionCore proposition)
                == Just (sourceAssertionFormula assertion)

    covers paths proposition
        | not (null paths) && all (== ConjunctionHere) paths = True
        | CAnd left right <- proposition =
            let leftPaths =
                    [ remaining
                    | ConjunctionLeft remaining <- paths
                    ]
                rightPaths =
                    [ remaining
                    | ConjunctionRight remaining <- paths
                    ]
            in length paths == length leftPaths + length rightPaths
                && covers leftPaths left
                && covers rightPaths right
        | otherwise = False

    prepareOccurrence (coordinate, assertion) = do
        let compiledAssertion = runIdentity
                (traverseSourceNotionAssertionParts
                    (Identity . SourceTerm.forgetScopedSourceTermOccurrence)
                    (Identity . scopedCoreTerm)
                    assertion)
            atom = sourceAssertionAtom compiledAssertion
            key = richFormationGoalKey atom
        focus <- maybe
            (impossible "a definition result notion has no distinguished term")
            pure
            (notionFocusTerm atom)
        unless (richSourceTermKey focus == richSourceTermKey bodySource)
            (impossible
                "a definition result phrase changed its rich distinguished term")
        pure
            (DefinitionResultOccurrence
                coordinate assertion compiledAssertion atom key)

    stableDeduplicate occurrences = do
        (_nextOrdinal, retained) <- foldM retain (0 :: Natural, Map.empty)
            occurrences
        pure
            (snd
                <$> List.sortOn fst (Map.elems retained))

    retain (nextOrdinal, retained) occurrence =
        case Map.lookup key retained of
            Nothing ->
                pure
                    ( nextOrdinal + 1
                    , Map.insert key (nextOrdinal, occurrence) retained
                    )
            Just (ordinal, previous) -> do
                unless (sameFormula previous occurrence)
                    (impossible
                        "one canonical definition-result atom has inconsistent formulas")
                let selected
                        | definitionResultOccurrenceCoordinate occurrence
                            < definitionResultOccurrenceCoordinate previous =
                            occurrence
                        | otherwise = previous
                pure (nextOrdinal, Map.insert key (ordinal, selected) retained)
      where
        key = definitionResultOccurrenceKey occurrence

    sameFormula left right =
        sourceAssertionFormula
            (definitionResultOccurrenceAssertion left)
            == sourceAssertionFormula
                (definitionResultOccurrenceAssertion right)

definitionResultPhraseLocation :: Raw.DefinitionResultPhrase -> Location
definitionResultPhraseLocation (Raw.NounPhrase _ noun _ _ _) = locate noun

-- | Prove an annotation about the written definiens before publishing its
-- equation-transported result. All leaves share one sealed requirement group.
-- The current formation scope contains all checked definition headers; the
-- dedicated query policy excludes every other source class.
prepareDefinitionResults
    :: Location
    -> [CompiledHeaderAntecedent]
    -> CompiledSourceTerm
    -> Raw.DefinitionResultPhrase
    -> Elaborate PreparedDefinitionResults
prepareDefinitionResults _definitionLocation antecedents bodySource phrase = do
    parameterCount <-
        State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
    when (parameterCount == 0 || null antecedents)
        (Except.throwError
            (ElaborationDefinitionResultRequiresGuardedProvider
                (definitionResultPhraseLocation phrase)))
    providerReference <-
        State.gets elaborationDefinitionProvider >>= maybe
            (impossible
                "a definition result was compiled without its owner-bearing provider")
            pure
    (left, noun, right) <- case phrase of
        Raw.NounPhrase left noun (Raw.NounBinder Raw.Nameless Raw.Unbounded) right Nothing ->
            pure (left, noun, right)
        _ ->
            Except.throwError
                (ElaborationDefinitionResultShapeUnsupported
                    (definitionResultPhraseLocation phrase))
    components <-
        compileNounPhraseComponentsPresented
            [bodySource] left noun right Nothing
    let logicalComponents = phraseLogicalComponents components
        (compiled, coordinates) = assemblePhraseComponents logicalComponents
    sealed <- sealCompiledPropositionHere (locate noun) compiled
    checkingContext <- currentSourceTermCheckingContext
    body <- either
        (Except.throwError . resultSealError (definitionResultPhraseLocation phrase))
        pure (SourceTerm.sealCanonicalSourceTermOccurrence checkingContext bodySource)
    let providerArguments = Vector.fromList
            [ TemplateVariable (ViewVariableIx (parameterCount - index - 1))
            | index <- [0 .. parameterCount - 1]
            ]
        provider = resultProviderTemplate
            (GlobalSourceProvider providerReference)
            providerArguments
        premiseSources =
            [ ( compiledHeaderCore antecedent
              , compiledHeaderEvidence antecedent
              )
            | antecedent <- antecedents
            ]
    types <- State.gets (binderStackTypes . lexicalBinderStack . elaborationScope)
    if atomicDescription (elaboratedPropositionEvidence sealed)
    then do
        retained <- validateDefinitionResultOccurrences phrase logicalComponents coordinates sealed bodySource
        let memoize = NonEmpty.length retained > 1
            roots = AtomicLeaf . definitionResultOccurrenceAtom <$> toList retained
        withNotionQueryScope DefinitionResultNotionQuery (withFormationWitnessArena \arena -> do
            (results, _, completion) <- prepareFormationQuery DefinitionResultNotionQuery (definitionResultPhraseLocation phrase)
                (Just (fromIntegral (NonEmpty.length retained))) (initialFormationSearchBudget defaultFormationSearchLimits)
                (State.evalStateT
                    (traverse (prepareAtom memoize parameterCount body provider premiseSources) retained)
                    (initialFormationGroup DefinitionResultNotionQuery arena types) {groupRoots = roots})
            pure (PreparedDefinitionResults results completion))
    else do
        for_ logicalComponents \component -> case phraseComponentKind component of
            PhraseHardSet -> pure ()
            PhraseRegular -> when (isNeutralCompiled (phraseComponentProposition component))
                (Except.throwError (ElaborationDefinitionResultShapeUnsupported (definitionResultPhraseLocation phrase)))
        when (isNeutralCompiled compiled)
            (Except.throwError (ElaborationDefinitionResultShapeUnsupported (definitionResultPhraseLocation phrase)))
        -- Recompile at a fresh focus, keeping equal-valued phrase parameters
        -- distinct from the result position. The named provider is introduced
        -- only after Binding has checked its defining equation.
        (predicate,description) <- withAnonymousSetBinder \focus -> do
            parts <- compileNounPhraseComponentsPresented [locatedSetSourceTerm (locate noun) focus] left noun right Nothing
            described <- sealCompiledPropositionHere (locate noun) (fst (assemblePhraseComponents (phraseLogicalComponents parts)))
            let proposition = elaboratedPropositionCore described
            predicate <- maybe (impossible "a result predicate cannot close its fresh focus") pure (abstractScopedCore TySet proposition)
            template <- either (Except.throwError . ElaborationDefinitionResultShapeInvalid (locate noun)) pure
                (NotionPremise.describeResidual (parameterCount+1) proposition (elaboratedPropositionEvidence described))
            pure (predicate,template)
        premises <- RulePremiseBundles <$> traverse (\(formula,evidence) -> either
            (Except.throwError . ElaborationDefinitionResultShapeInvalid (locate noun)) pure
            (NotionPremise.compilePremise parameterCount formula evidence))
            (fromMaybe (impossible "a guarded result lost its headers") (NonEmpty.nonEmpty premiseSources))
        withNotionQueryScope DefinitionResultNotionQuery (withFormationWitnessArena \arena -> do
            (result, _, completion) <- prepareFormationQuery DefinitionResultNotionQuery (locate noun) Nothing
                (initialFormationSearchBudget defaultFormationSearchLimits)
                (State.evalStateT (prepareWhole body provider premises predicate description sealed)
                    (initialFormationGroup DefinitionResultNotionQuery arena types))
            pure (PreparedDefinitionResults (result :| []) completion))
  where
    elaborate :: Elaborate value -> FormationGroup scope value
    elaborate = State.lift . formationElaborate
    prepareAtom :: Bool -> Natural -> ScopedSourceTerm -> ResultProviderTemplate
        -> [(ScopedCheckedCore ObjectId, SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)]
        -> DefinitionResultOccurrence -> FormationGroup scope PreparedDefinitionResult
    prepareAtom memoize parameterCount body provider premiseSources occurrence = do
        let assertion = definitionResultOccurrenceAssertion occurrence
            compiledAssertion = definitionResultOccurrenceCompiled occurrence
            requestedAtom = definitionResultOccurrenceAtom occurrence
            location = definitionResultPhraseLocation phrase
        outcome <- queryFormationGroupLeaf memoize location requestedAtom
        witness <- case outcome of
            Right found -> pure found
            Left failure -> do
                finalBudget <- State.lift State.get
                names <- elaborate structureDiagnosticNames
                elaborate (Except.throwError (ElaborationDefinitionResultUnavailable location
                    (NotionQueryFailure names
                        (compiledSourceTermPresentation <$> requestedAtom)
                        (sourceNotionWrittenOrigin compiledAssertion) failure
                        (formationSearchBudgetStatistics finalBudget))))
        arena <- State.gets groupArena
        (selected, _) <- State.lift (withFormationSearchPhase FormationDiagnostics.Proof
            (runFormationConstruction recordFormationAllocation
                (selectFormationEvidence (chargeFormationWork location) defaultFormationSearchLimits witness) arena))
        evidence <- either (elaborate . Except.throwError . ElaborationFormationSearchFailed location) pure selected
        let materialized = materializeFormationEvidence defaultFormationSearchLimits evidence
        predicate <- elaborate (deriveNotionFocusPredicate location requestedAtom)
        (checkedProvider, premises, conclusion) <-
            either
                (elaborate . Except.throwError
                    . ElaborationDefinitionResultShapeInvalid location
                    . ProviderResult.providerResultErrorReason)
                pure
                (ProviderResult.prepareGuardedDefinitionResultRuleTemplates
                    parameterCount
                    premiseSources
                    assertion
                    (ProviderResult.definitionProviderResultSubject
                        provider body))
        pure
            (PreparedDefinitionResult
                antecedents body (sourceAssertionFormula assertion) predicate materialized
                checkedProvider premises (AtomicLeaf conclusion))

    atomicDescription = \case
        SourceWithInputs _ body -> atomicDescription body
        SourceAtom{} -> True
        SourceAnd a b -> atomicDescription a && atomicDescription b
        _ -> False

    prepareWhole
        :: ScopedSourceTerm -> ResultProviderTemplate -> RulePremiseBundles RuleTermTemplate
        -> ScopedCheckedCore ObjectId -> ResidualTemplate -> ElaboratedProposition
        -> FormationGroup scope PreparedDefinitionResult
    prepareWhole body provider premises predicate description sealed = do
        let location = definitionResultPhraseLocation phrase
            formula = elaboratedPropositionCore sealed
            evidence = elaboratedPropositionEvidence sealed
        leaves <- SourceEvidence.notionLeaves (State.lift (chargeFormationWork location 1))
            (\_ _ -> pure ()) () formula evidence
        let root view = case SourceEvidence.sourceLeafDescription view of
                SourceEvidence.LeafAtom assertion -> AtomicLeaf (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion)
                _ -> WholeLeaf (WholeNotionGoal (SourceEvidence.sourceLeafFormula view) (SourceEvidence.sourceLeafEvidence view))
        annotations <- SourceEvidence.sourceInputAnnotationsWith (State.lift (chargeFormationWork location 1)) evidence
        let inputRoots = annotationInputRoots formula annotations
        State.modify' (\group -> group {groupRoots = (root <$> leaves) <> inputRoots})
        found <- Except.runExceptT (queryFormationGroupGoal True location formula evidence)
        (forest,_) <- either (elaborate . Except.throwError . ElaborationDefinitionResultUnavailable location) pure found
        proved <- groupConstruct location (materializeFormationPremiseEvidence (chargeFormationWork location)
            defaultFormationSearchLimits forest)
        pure (PreparedDefinitionResult antecedents body formula predicate proved provider premises (WholeLeaf description))

    resultSealError location = \case
        SourceTerm.SourceTermSealCoreCheckFailed _ failure ->
            ElaborationCoreCheckFailed location failure
        SourceTerm.SourceTermSealTypeMismatch expected actual ->
            ElaborationObjectTypeMismatch location expected actual


stableNubTemplates :: Ord value => [value] -> [value]
stableNubTemplates =
    reverse . snd . foldl' retainFirst (Set.empty, [])
  where
    retainFirst (seen, retained) candidate
        | candidate `Set.member` seen = (seen, retained)
        | otherwise =
            (Set.insert candidate seen, candidate : retained)

headerAssumptionLocation :: Raw.Asm -> Location
headerAssumptionLocation = \case
    Raw.AsmSuppose statement -> locate statement
    Raw.AsmLetNoun variables _phrase -> locate variables
    Raw.AsmLetIn variables _domain -> locate variables
    Raw.AsmLetRelation variables _relation _right -> locate variables
    Raw.AsmLetThe variable _function -> locate variable
    Raw.AsmLetEq variable _expression -> locate variable
    Raw.AsmLetStruct variables _structure -> locate variables

compileHeaderAssumptionCompiled
    :: Natural
    -> Raw.Asm
    -> Elaborate CompiledHeaderBatch
compileHeaderAssumptionCompiled sourceOrdinal = \case
    Raw.AsmSuppose statement -> do
        proposition <- compileStatement statement
        pure
            (CompiledHeaderBatch
                [CompiledHeaderRow
                    sourceOrdinal Nothing (locate statement) proposition]
                Map.empty)
    Raw.AsmLetNoun variables nounPhrase
        | isSetNounPhrase nounPhrase -> do
            traverse_ compileIntroducedVariable variables
            pure (CompiledHeaderBatch [] Map.empty)
        | otherwise ->
            (`CompiledHeaderBatch` Map.empty)
                <$> compileNounHeader variables nounPhrase
    Raw.AsmLetIn variables domain -> do
        variableTerms <- traverse compileIntroducedVariable variables
        domainTerm <- compileSourceExpressionAsSetTerm domain
        rows <- traverse
            (\(variableOrdinal, (variable, variableTerm)) -> do
                proposition <-
                    compileMembershipPropositionTerms
                        (locate domain)
                        Raw.Positive
                        (compiledSourceTermForTerm
                            (Raw.TermExpr (Raw.ExprVar variable))
                            TySet
                            variableTerm)
                        domainTerm
                pure
                    (CompiledHeaderRow
                        sourceOrdinal
                        (Just (fromIntegral variableOrdinal))
                        (locate variable)
                        proposition))
            (zip [0 :: Int ..]
                (zip (toList variables) (toList variableTerms)))
        pure (CompiledHeaderBatch rows Map.empty)
    Raw.AsmLetRelation variables relation right -> do
        variableTerms <- traverse compileIntroducedVariable variables
        case relation of
            Raw.Relation relationLocation symbol parameters -> do
                let key = SemanticRelation
                        (Raw.relationSymbolToken symbol)
                        (Raw.relationSymbolParameterArity symbol)
                when (isJust (fixedSemanticMeaning key))
                    (Except.throwError
                        (ElaborationUnsupportedHeaderAssumption
                            relationLocation))
                compiledParameters <-
                    traverse compileSourceExpressionAsSetTerm parameters
                rightTerm <- compileSourceExpressionAsSetTerm right
                rows <- traverse
                    (\(variableOrdinal, (variable, variableTerm)) -> do
                        proposition <-
                            compileNamedRelationTerms
                                relationLocation
                                symbol
                                compiledParameters
                                (compiledSourceTermForTerm
                                    (Raw.TermExpr (Raw.ExprVar variable))
                                    TySet
                                    variableTerm)
                                rightTerm
                        pure
                            (CompiledHeaderRow
                                sourceOrdinal
                                (Just (fromIntegral variableOrdinal))
                                (locate variable)
                                proposition))
                    (zip [0 :: Int ..]
                        (zip (toList variables) (toList variableTerms)))
                pure (CompiledHeaderBatch rows Map.empty)
            Raw.RelationExpr relationLocation _expression ->
                Except.throwError
                    (ElaborationUnsupportedHeaderAssumption relationLocation)
    Raw.AsmLetEq variable expression -> do
        variableTerm <- compileIntroducedVariable variable
        expressionTerm <- compileSourceExpressionAsSetTerm expression
        let variableSource =
                compiledSourceTermForTerm
                    (Raw.TermExpr (Raw.ExprVar variable))
                    TySet
                    variableTerm
        pure
            (CompiledHeaderBatch
                [ CompiledHeaderRow
                    sourceOrdinal
                    (Just 0)
                    (locate variable)
                    (compileSetEqualityProposition
                        (locate variable)
                        variableSource
                        expressionTerm)
                ]
                Map.empty)
    Raw.AsmLetThe variable _function ->
        Except.throwError
            (ElaborationUnsupportedHeaderAssumption (locate variable))
    Raw.AsmLetStruct variables
            (Raw.StructNounPhrase left structure right residual) -> do
        annotation <-
            resolveStructureAnnotation
                (locate variables)
                structure
        let AssertableStructureApplication resolvedAnnotation _predicate =
                annotation
        subjects <- traverse compileIntroducedVariable variables
        indices <- traverse structureVariableIndex variables
        case firstDuplicate (toList variables) of
            Just duplicate ->
                Except.throwError
                    (ElaborationDuplicateStructureAnnotation
                        (locate duplicate) duplicate)
            Nothing -> pure ()
        outerStructures <- State.gets (lexicalStructures . elaborationScope)
        traverse_
            (\(variable, index) ->
                when
                    (Map.member index outerStructures)
                    (Except.throwError
                        (ElaborationDuplicateStructureAnnotation
                            (locate variable) variable)))
            (zip (toList variables) (toList indices))
        let subjectInputs =
                [ ( locate variable
                  , SourceTerm.sourceTermOccurrence
                        subject
                        TySet
                        (PresentedSourceTerm
                            (locate variable)
                            (renderSourceVariable variable))
                  , Just index
                  )
                | (variable, subject, index) <-
                    zip3
                        (toList variables)
                        (toList subjects)
                        (toList indices)
                ]
        components <-
            compileStructurePhraseComponents
                subjectInputs annotation left right residual
        let subjectRows = phraseSubjectComponentRows components
            subjectAntecedents =
                [ CompiledHeaderRow
                    sourceOrdinal
                    (Just (fromIntegral variableOrdinal))
                    (locate variable)
                    proposition
                | (variableOrdinal, (variable, row)) <-
                    zip [0 :: Int ..]
                        (zip (toList variables) subjectRows)
                , let proposition = fst (assemblePhraseComponents row)
                , not (isNeutralCompiled proposition)
                ]
            residualAntecedent =
                case phraseResidualComponent components of
                    Nothing -> []
                    Just residualComponent
                        | isNeutralCompiled proposition -> []
                        | otherwise ->
                            [ CompiledHeaderRow
                                sourceOrdinal
                                Nothing
                                (maybe (locate variables) locate residual)
                                proposition
                            ]
                      where
                        proposition =
                            fst
                                (assemblePhraseComponents
                                    [residualComponent])
            pending = Map.fromList
                [ (index, resolvedAnnotation)
                | index <- toList indices
                ]
        pure
            (CompiledHeaderBatch
                (subjectAntecedents <> residualAntecedent)
                pending)
  where
    compileNounHeader variables phrase@(Raw.NounPhrase
            left noun (Raw.NounBinder named bound) right suchThat) = do
        requireUnboundedNoun bound
        subjects <- traverse compileIntroducedVariable variables
        let sourceSubjects =
                [ compiledSourceTermForTerm
                    (Raw.TermExpr (Raw.ExprVar variable))
                    TySet
                    subject
                | (variable, subject) <-
                    toList (NonEmpty.zip variables subjects)
                ]
        case named of
            Nothing -> do
                components <-
                    compileNounPhraseComponentsPresented
                        sourceSubjects left noun right suchThat
                let subjectRows =
                        phraseSubjectComponentRows components
                    subjectAntecedents =
                        [ CompiledHeaderRow
                            sourceOrdinal
                            (Just (fromIntegral variableOrdinal))
                            (locate variable)
                            proposition
                        | (variableOrdinal, (variable, row)) <-
                            zip [0 :: Int ..]
                                (zip (toList variables) subjectRows)
                        , let proposition =
                                fst (assemblePhraseComponents row)
                        , not (isNeutralCompiled proposition)
                        ]
                    residualAntecedent =
                        case phraseResidualComponent components of
                            Nothing -> []
                            Just residual
                                | isNeutralCompiled proposition -> []
                                | otherwise ->
                                    [ CompiledHeaderRow
                                        sourceOrdinal
                                        Nothing
                                        (maybe (locate noun) locate suchThat)
                                        proposition
                                    ]
                              where
                                proposition =
                                    fst (assemblePhraseComponents [residual])
                pure (subjectAntecedents <> residualAntecedent)
            Just{} ->
                case (toList variables, sourceSubjects) of
                    ([variable], [subject]) -> do
                        proposition <- compileNounPhraseMaybe subject phrase
                        pure
                            [ CompiledHeaderRow
                                sourceOrdinal
                                (Just 0)
                                (locate variable)
                                proposition
                            | not (isNeutralCompiled proposition)
                            ]
                    _ ->
                        Except.throwError
                            (ElaborationGroupedNounNameUnsupported (locate noun))

structureVariableIndex :: Raw.VarSymbol -> Elaborate Natural
structureVariableIndex variable =
    maybe
        (impossible "an introduced structure variable is unbound")
        (pure . fst)
        =<< Map.lookup variable <$> State.gets (lexicalBinders . elaborationScope)

structureSubjectBinderIndex :: Raw.Term -> Elaborate (Maybe Natural)
structureSubjectBinderIndex = \case
    Raw.TermExpr (Raw.ExprVar variable) ->
        fmap fst . Map.lookup variable <$> State.gets (lexicalBinders . elaborationScope)
    _ -> pure Nothing

withTemporaryStructureAnnotation
    :: Natural
    -> ResolvedStructureApplication
    -> Elaborate value
    -> Elaborate value
withTemporaryStructureAnnotation index annotation action = do
    outer <- State.gets (lexicalStructures . elaborationScope)
    modifyLexicalScope \scope ->
        scope
            { lexicalStructures =
                Map.insert index annotation outer
            }
    result <- action
    modifyLexicalScope \scope -> scope{lexicalStructures = outer}
    pure result

compileIntroducedVariable
    :: Raw.VarSymbol
    -> Elaborate (CanonicalTerm ObjectId)
compileIntroducedVariable variable =
    compileExpressionAsSet (Raw.ExprVar variable)

resolveStructureAnnotation
    :: Location
    -> Raw.StructApplication Raw.Term
    -> Elaborate AssertableStructureApplication
resolveStructureAnnotation location application =
    snd
        <$> resolveStructureApplicationWith
            compileSourceTermAsSet
            location
            application

resolveExpressionStructureApplication
    :: Location
    -> Raw.StructApplication Raw.Expr
    -> Elaborate
        (Declaration.ResolvedStructure, AssertableStructureApplication)
resolveExpressionStructureApplication =
    resolveStructureApplicationWith compileSourceExpressionAsSetTerm

resolveStructureApplicationWith
    :: (argument -> Elaborate CompiledSourceTerm)
    -> Location
    -> Raw.StructApplication argument
    -> Elaborate
        (Declaration.ResolvedStructure, AssertableStructureApplication)
resolveStructureApplicationWith compileArgument location
        (Raw.StructApplication rawPhrase rawArguments) = do
    let structurePhrase = Schema.structurePhrase rawPhrase
    resolved <-
        State.lift
            (Trans.lift
                (Declaration.resolveVisibleStructureLowering structurePhrase))
    structure <-
        maybe
            (Except.throwError
                (ElaborationStructureNotVisible location structurePhrase))
            pure
            resolved
    let registration = Declaration.resolvedStructureRegistration structure
    let descriptor = Declaration.resolvedStructureSchema structure
        expected = Schema.resolvedSchemaParameterCount descriptor
        actual = fromIntegral (length rawArguments)
    unless
        (expected == actual)
        (Except.throwError
            (ElaborationStructureParameterArityMismatch
                location structurePhrase expected actual))
    arguments <- traverse compileArgument rawArguments
    pure
        ( structure
        , AssertableStructureApplication
            (ResolvedStructureApplication
                structurePhrase
                (Declaration.resolvedStructureFields structure)
                arguments)
            registration
        )

resolveStructureAggregate
    :: Location
    -> Declaration.ResolvedStructure
    -> AssertableStructureApplication
    -> [Raw.StructAggregateEntry]
    -> Elaborate ResolvedStructureAggregate
resolveStructureAggregate location structure annotation entries = do
    let descriptor = Declaration.resolvedStructureSchema structure
        structurePhrase = Schema.resolvedSchemaPhrase descriptor
        order = Declaration.resolvedStructureFieldOrder structure
        resources = Map.fromList
            [(Schema.resolvedFieldSymbol field, field)
            | field <- Map.elems (Schema.resolvedSchemaFields descriptor)]
        expected = fromIntegral (length order)
        actual = fromIntegral (length entries)
        resourceFor symbol =
            fromMaybe
                (impossible
                    "resolved structure presentation names a missing field")
                (Map.lookup symbol resources)
        resolvedEntry symbol (entryLocation, expression) =
            ElaboratedRecordField (resourceFor symbol) expression (WrittenRecordField entryLocation)
        finish resolved = pure (ResolvedStructureAggregate location annotation resolved)
    case entries of
        []
            | expected == 0 -> finish []
            | otherwise -> Except.throwError
                (ElaborationStructureAggregateFieldArityMismatch location structurePhrase expected 0)
        firstEntry : remaining ->
            case firstEntry of
                Raw.StructAggregatePositional firstValue -> do
                    case findNamed remaining of
                        Just namedLocation ->
                            Except.throwError
                                (ElaborationStructureAggregateMixedEntries
                                    namedLocation)
                        Nothing -> pure ()
                    unless (actual == expected)
                        (Except.throwError
                            (ElaborationStructureAggregateFieldArityMismatch
                                location structurePhrase expected actual))
                    finish
                        (zipWith
                            resolvedEntry
                            order
                            ( (locate firstValue, firstValue)
                                : [ (locate value, value)
                                  | Raw.StructAggregatePositional value <-
                                        remaining
                                  ]
                            ))
                Raw.StructAggregateNamed
                        firstLocation firstSymbol firstValue -> do
                    case findPositional remaining of
                        Just positionalLocation ->
                            Except.throwError
                                (ElaborationStructureAggregateMixedEntries
                                    positionalLocation)
                        Nothing -> pure ()
                    named <-
                        foldM
                            (insertNamed structurePhrase resources)
                            Map.empty
                            ( (firstLocation, firstSymbol, firstValue)
                                : [ (entryLocation, symbol, value)
                                  | Raw.StructAggregateNamed
                                        entryLocation symbol value <- remaining
                                  ]
                            )
                    let missing =
                            [ symbol
                            | symbol <- order
                            , Map.notMember symbol named
                            ]
                    case NonEmpty.nonEmpty missing of
                        Just missingFields ->
                            Except.throwError
                                (ElaborationStructureAggregateMissingFields
                                    location structurePhrase missingFields)
                        Nothing ->
                            finish
                                [ resolvedEntry symbol
                                    (fromMaybe
                                        (impossible
                                            "complete named aggregate lost a field")
                                        (Map.lookup symbol named))
                                | symbol <- order
                                ]
  where
    findNamed = \case
        [] -> Nothing
        Raw.StructAggregateNamed entryLocation _symbol _value : _ ->
            Just entryLocation
        _entry : remaining -> findNamed remaining

    findPositional = \case
        [] -> Nothing
        Raw.StructAggregatePositional value : _ ->
            Just (locate value)
        _entry : remaining -> findPositional remaining

    insertNamed structurePhrase resources named
            (entryLocation, symbol, value) = do
        unless (Map.member symbol resources)
            (Except.throwError
                (ElaborationStructureAggregateUnknownField
                    entryLocation structurePhrase symbol))
        when (Map.member symbol named)
            (Except.throwError
                (ElaborationStructureAggregateDuplicateField
                    entryLocation structurePhrase symbol))
        pure (Map.insert symbol (entryLocation, value) named)

compileStructureAggregate
    :: ResolvedStructureAggregate
    -> Elaborate (CanonicalTerm ObjectId, AssertableStructureApplication)
compileStructureAggregate
        resolved@(ResolvedStructureAggregate _location annotation _entries) = do
    values <- compileStructureAggregateValues resolved
    pure (aggregatePartsTerm values, annotation)

compileStructureAggregateValues
    :: ResolvedStructureAggregate
    -> Elaborate [ElaboratedRecordField (CanonicalTerm ObjectId)]
compileStructureAggregateValues (ResolvedStructureAggregate _ _ entries) =
    traverse compileEntry (List.sortOn (Schema.resolvedFieldIdentity . elaboratedRecordField) entries)
  where
    compileEntry entry = do
        requireGlobalType (Schema.resolvedFieldSelector (elaboratedRecordField entry)) TySet
        traverse compileExpressionAsSet entry

aggregatePartsTerm
    :: [ElaboratedRecordField (CanonicalTerm ObjectId)]
    -> CanonicalTerm ObjectId
aggregatePartsTerm values = Record.recordAggregate
    [(CGlobal (Schema.resolvedFieldSelector (elaboratedRecordField entry)), elaboratedRecordValue entry)
    | entry <- values]

compileAnnotatedStructureAggregate
    :: Location
    -> Maybe (Raw.StructApplication Raw.Expr)
    -> [Raw.StructAggregateEntry]
    -> Elaborate (CanonicalTerm ObjectId, AssertableStructureApplication)
compileAnnotatedStructureAggregate location maybeSchema entries = do
    schema <-
        maybe
            (Except.throwError
                (ElaborationStructureAggregateSchemaRequired location))
            pure
            maybeSchema
    (structure, annotation) <-
        resolveExpressionStructureApplication location schema
    resolved <-
        resolveStructureAggregate
            location structure annotation entries
    compileStructureAggregate resolved

structureAnnotationPredicate :: AssertableStructureApplication -> ObjectId
structureAnnotationPredicate
        (AssertableStructureApplication _resolved registration) =
    StructurePredicate.pendingStructurePredicate registration

structureAnnotationArguments
    :: ResolvedStructureApplication
    -> [CanonicalTerm ObjectId]
structureAnnotationArguments
        (ResolvedStructureApplication _ _ arguments) =
    compiledSourceTermCore <$> arguments

structureAnnotationField
    :: Raw.StructSymbol
    -> ResolvedStructureApplication
    -> Maybe (FieldId, ObjectId)
structureAnnotationField symbol
        (ResolvedStructureApplication _phrase fields _arguments) =
    Map.lookup symbol fields

applyStructureAnnotation
    :: CanonicalTerm ObjectId
    -> AssertableStructureApplication
    -> Elaborate (CanonicalTerm ObjectId)
applyStructureAnnotation subject annotation = do
    let AssertableStructureApplication resolved registration = annotation
        predicate = StructurePredicate.pendingStructurePredicate registration
        arguments = structureAnnotationArguments resolved
        applicationArguments = subject : arguments
        predicateType =
            foldr
                (const (TyArrow TySet))
                TyProp
                applicationArguments
    requireGlobalType predicate predicateType
    pure
        (foldl'
            CApp
            (CGlobal predicate)
            applicationArguments)

compileStructureNotionApplication
    :: Location
    -> CompiledSourceTerm
    -> AssertableStructureApplication
    -> Elaborate CompiledProposition
compileStructureNotionApplication location subject annotation = do
    proposition <- applyStructureAnnotation
        (compiledSourceTermCore subject) annotation
    let AssertableStructureApplication
            (ResolvedStructureApplication _phrase _fields parameters)
            registration = annotation
    pure
        (atomicCompiledProposition
            (structureSourceNotionAssertion
                (pendingStructureNotionHead registration)
                (Vector.fromList
                    (subject : parameters))
                proposition
                ConjunctionHere
                location))

-- | The source-preserving form used for a declared parent structure.  Parent
-- applications are logical conjuncts of the child predicate and therefore
-- become formation evidence for subsequent field specifications and laws.
compileStructureNotionProposition
    :: Location
    -> CanonicalTerm ObjectId
    -> AssertableStructureApplication
    -> Elaborate CompiledProposition
compileStructureNotionProposition location subject =
    compileStructureNotionApplication
        location
        (locatedSetSourceTerm location subject)

-- | Check and retain one already compiled structure-predicate conjunct for
-- the remainder of the current structure elaboration transaction.  The
-- transaction has a private state and ends after the declaration, so no
-- source assertion can leak into a later declaration.
retainStructureFormationComponent
    :: Location
    -> CompiledProposition
    -> Elaborate ()
retainStructureFormationComponent location proposition = do
    checked <- sealCompiledPropositionHere location proposition
    retainCheckedStructureFormationComponent checked

retainCheckedStructureFormationComponent
    :: ElaboratedProposition
    -> Elaborate ()
retainCheckedStructureFormationComponent checked = do
    void (acquireFormationCatalogs Nowhere)
    current <- State.get
    previous <- State.gets (lexicalFormationScope . elaborationScope)
    let source = checkedGuardFormationSource
            (elaboratedPropositionCore checked)
            (elaboratedPropositionEvidence checked)
            FormationStructureDeclarationComponent
    withNotions <- prepareFormationScopeHere (formationSourceLocation source) (extendFormationScope
        (binderStackTypes (lexicalBinderStack (elaborationScope current)))
        (elaborationProofSupport current) source previous)
    withEqualities <-
            case NonEmpty.nonEmpty
                    (elaboratedPropositionEqualities checked) of
                Nothing -> pure withNotions
                Just equalities ->
                    let source = checkedGuardFormationEqualitySource
                            (elaboratedPropositionCore checked)
                            equalities
                            FormationStructureDeclarationComponent
                    in prepareFormationScopeHere (equalitySourceLocation source)
                        (extendFormationEqualityScope
                            (binderStackTypes (lexicalBinderStack (elaborationScope current)))
                            (elaborationProofSupport current) source withNotions)
    modifyLexicalScope \scope ->
        scope { lexicalFormationScope = withEqualities }

compileStructurePhraseComponents
    :: [(Location, CompiledSourceTerm, Maybe Natural)]
    -> AssertableStructureApplication
    -> [Raw.AdjL]
    -> [Raw.AdjR]
    -> Maybe Raw.Stmt
    -> Elaborate CompiledPhraseComponents
compileStructurePhraseComponents subjects annotation left right residual = do
    rows <- traverse compileSubject (zip [0 :: Natural ..] subjects)
    let cores = firstOf3 <$> rows
        leftComponents = secondOf3 <$> rows
        rightComponents = thirdOf3 <$> rows
        designations =
            [ (index, resolvedAnnotation)
            | (_location, _subject, Just index) <- subjects
            ]
    residualComponent <-
        withTemporaryStructureAnnotations designations
            (for residual \statement ->
                withCompletedPhraseHead (locate statement)
                    (cores <> concat leftComponents <> concat rightComponents)
                    (compileResidual statement))
    pure
        CompiledPhraseComponents
            { phraseCoreComponents = cores
            , phraseBoundComponents = []
            , phraseLeftComponents = leftComponents
            , phraseRightComponents = rightComponents
            , phraseResidualComponent = residualComponent
            }
  where
    AssertableStructureApplication resolvedAnnotation _predicate = annotation
    subjectCount = fromIntegral (length subjects)
    leftCount = fromIntegral (length left)
    rightCount = fromIntegral (length right)

    compileSubject
            (subjectOrdinal, (location, subject, maybeBinderIndex)) = do
        open <- compileStructureNotionApplication location subject annotation
        checkedOpen <- sealCompiledPropositionHere location open
        let withOwnDesignation =
                case maybeBinderIndex of
                    Nothing -> id
                    Just index ->
                        withTemporaryStructureAnnotation
                            index resolvedAnnotation
            withCore = withCheckedFormationGuard
                FormationStructurePhraseCore checkedOpen
        leftComponents <- withOwnDesignation (withCore
            (for (zip [0 :: Natural ..] left)
                \(modifierOrdinal, modifier) ->
                    CompiledPhraseComponent
                        PhraseRegular
                        (phraseLeftComponentOrdinal
                            subjectCount subjectOrdinal modifierOrdinal)
                        <$> compileStructureLeftAdjectiveProposition
                            subject modifier))
        rightComponents <- withOwnDesignation (withCore
            (for (zip [0 :: Natural ..] right)
                \(modifierOrdinal, modifier) ->
                    CompiledPhraseComponent
                        PhraseRegular
                        (phraseRightComponentOrdinal
                            subjectCount leftCount subjectOrdinal
                            modifierOrdinal)
                        <$> compileRightAdjectivePropositionWithReading
                            StructureAdjectiveReading subject modifier))
        pure
            ( CompiledPhraseComponent
                PhraseRegular
                (phraseCoreComponentOrdinal
                    subjectCount leftCount subjectOrdinal)
                open
            , leftComponents
            , rightComponents
            )

    compileResidual statement =
        CompiledPhraseComponent
            PhraseRegular
            (phraseResidualComponentOrdinal
                subjectCount leftCount rightCount)
            <$> compileStatement statement

    firstOf3 (firstValue, _second, _third) = firstValue
    secondOf3 (_first, second, _third) = second
    thirdOf3 (_first, _second, third) = third

withTemporaryStructureAnnotations
    :: [(Natural, ResolvedStructureApplication)]
    -> Elaborate value
    -> Elaborate value
withTemporaryStructureAnnotations [] action = action
withTemporaryStructureAnnotations ((index, annotation) : remaining) action =
    withTemporaryStructureAnnotation index annotation
        (withTemporaryStructureAnnotations remaining action)

resolvedStructureSelectorTerms
    :: Declaration.ResolvedStructure -> Elaborate [CanonicalTerm ObjectId]
resolvedStructureSelectorTerms structure =
    for (Map.elems (Schema.resolvedSchemaFields (Declaration.resolvedStructureSchema structure))) \field -> do
        let selector = Schema.resolvedFieldSelector field
        requireGlobalType selector TySet
        pure (CGlobal selector)

requireGlobalType :: ObjectId -> CoreType -> Elaborate ()
requireGlobalType identity expected = do
    globalTyping <- State.gets elaborationGlobalTyping
    case lookupGlobalType globalTyping identity of
        Just actual
            | actual == expected -> pure ()
            | otherwise ->
                impossible "one exact global acquired two checked types"
        Nothing ->
            impossible "an owner-resolved global is absent from its checked closure"

compileExpressionAsSet
    :: Raw.Expr
    -> Elaborate (CanonicalTerm ObjectId)
compileExpressionAsSet expression =
    compiledSourceTermCore <$> compileSourceExpressionAsSetTerm expression

compileSourceExpression
    :: Raw.Expr
    -> Elaborate CompiledSourceTerm
compileSourceExpression expression =
    case expression of
        Raw.ExprTypedConstant location token concreteType
            | concreteTypeCoreType concreteType == TySet ->
                compileSourceGlobalApplication location
                    (SemanticTypedConstant token TySet) []
                    (sourceTermPresentation (Raw.TermExpr expression))
        Raw.ExprOp location symbol arguments -> do
            let key =
                    SemanticExpressionFunction
                        (Raw.mixfixPattern symbol)
                presentation =
                    sourceTermPresentation (Raw.TermExpr expression)
            compiled <- traverse compileSourceExpression arguments
            case fixedSemanticMeaning key of
                Just (FixedIntrinsic intrinsic) -> do
                    (term, coreType) <- applyTyped
                        location
                        (CIntrinsic intrinsic)
                        (coreIntrinsicType intrinsic)
                        (compiledSourceTermArguments compiled)
                    case (intrinsic, compiled) of
                        (OrderedPair, [left, right]) ->
                            maybe
                                (impossible
                                    "the checked ordered-pair source path lost set arguments")
                                pure
                                (SourceTerm.sourceOrderedPairTermOccurrence
                                    left right term presentation)
                        (PowerSet, [_argument]) ->
                            exactIntrinsic
                                PowerSetProvider compiled term presentation
                        (GlobalChoice, [_argument]) ->
                            exactIntrinsic
                                GlobalChoiceProvider compiled term presentation
                        (Empty, []) ->
                            exactIntrinsic
                                EmptySetProvider compiled term presentation
                        (FirstProjection, [_argument]) ->
                            exactIntrinsic
                                FirstProjectionProvider compiled term presentation
                        (SecondProjection, [_argument]) ->
                            exactIntrinsic
                                SecondProjectionProvider compiled term presentation
                        _ ->
                            pure
                                (SourceTerm.sourceTermOccurrence
                                    term coreType presentation)
                Just (FixedNegatedIntrinsic _intrinsic) ->
                    impossible
                        "expression key resolved to a negated intrinsic"
                Just FixedEquality ->
                    impossible
                        "expression key resolved to fixed equality"
                Just FixedDisequality ->
                    impossible
                        "expression key resolved to fixed disequality"
                Nothing ->
                    compileSourceGlobalApplication
                        location key compiled presentation
        Raw.ExprStructOp location symbol (Just receiverExpression) -> do
            ResolvedExplicitFieldSelection identity projection receiver term <-
                compileExplicitStructureFieldProjection
                    location symbol receiverExpression
            let occurrence = structureFieldProviderSourceTerm
                    identity projection receiver
                    (sourceTermPresentation (Raw.TermExpr expression))
            unless (compiledSourceTermCore occurrence == term)
                (impossible
                    "explicit structure-field source Core disagrees with its projection")
            pure occurrence
        Raw.ExprFiniteSet _location elements -> do
            compiled <- traverse compileSourceExpressionAsSetTerm elements
            pure
                (finiteSetLiteralProviderSourceTerm
                    compiled
                    (sourceTermPresentation (Raw.TermExpr expression)))
        Raw.ExprVar variable -> plain do
            binders <- State.gets (lexicalBinders . elaborationScope)
            case Map.lookup variable binders of
                Just (index, coreType) ->
                    pure (CBound index, coreType)
                Nothing ->
                    Except.throwError
                        (ElaborationFreeVariable (locate variable) variable)
        Raw.ExprNaturalNumeral location magnitude
            | magnitude > maxNaturalNumeral ->
                Except.throwError
                    (ElaborationNaturalNumeralMagnitudeExceeded
                        location magnitude maxNaturalNumeral)
            | magnitude == 0 -> plain (pure (CIntrinsic Empty, TySet))
            | otherwise -> plain do
                basis <- State.gets elaborationNaturalNumeralBasis
                successor <- maybe
                    (Except.throwError
                        (ElaborationNaturalNumeralBasisUnavailable location))
                    (pure . Declaration.naturalNumeralBasisObject)
                    basis
                pure (naturalNumeralCore successor magnitude, TySet)
        Raw.ExprOpaqueInteger _location integer ->
            plain (pure (COpaqueInteger integer, TySet))
        Raw.ExprTypedConstant location constantToken concreteType -> plain $
            applyContextualGlobalApplication
                location
                (SemanticTypedConstant
                    constantToken
                    (concreteTypeCoreType concreteType))
                []
        Raw.ExprHigherApply location rawFunction rawArgument -> plain do
            function <- compileTypedExpression rawFunction
            argument <- compileTypedExpression rawArgument
            applyTyped location (fst function) (snd function) [argument]
        Raw.ExprLambda _location variables concreteType body -> plain do
            let binderType = concreteTypeCoreType concreteType
            (bodyTerm, bodyType) <-
                withTypedBinders variables binderType
                    (compileTypedExpression body)
            pure
                ( foldr (const (CLam binderType)) bodyTerm variables
                , foldr (const (TyArrow binderType)) bodyType variables
                )
        Raw.ExprSelect location maybeConcreteType rawPredicate -> plain do
            (predicate, predicateType) <- compileTypedExpression rawPredicate
            selectedType <- case predicateType of
                TyArrow candidate TyProp -> pure candidate
                actual ->
                    Except.throwError
                        (ElaborationSelectionExpectedPredicate location actual)
            traverse_
                (\concreteType ->
                    let expected = concreteTypeCoreType concreteType
                    in unless (expected == selectedType)
                        (Except.throwError
                            (ElaborationSelectionTypeMismatch
                                location expected selectedType)))
                maybeConcreteType
            pure
                (CApp (CLogicalSelect selectedType) predicate, selectedType)
        Raw.ExprStructOp location symbol Nothing ->
            compileImplicitStructureFieldProjection location symbol
        Raw.ExprSep _location variable bound predicate -> plain do
            (term, _bound, _predicate) <-
                compileSeparation variable bound predicate
            pure (term, TySet)
        Raw.ExprReplace _location value bounds condition -> plain do
            replacement <-
                compileFunctionalReplacement value bounds condition
            pure (compiledFunctionalReplacementTerm replacement, TySet)
        Raw.ExprReplacePred location _value _variable _bound _predicate ->
            Except.throwError
                (ElaborationRelationalReplacementRequiresNamedDefinition location)
        Raw.ExprStructAggregate location maybeSchema entries -> plain do
            (aggregate, _annotation) <-
                compileAnnotatedStructureAggregate
                    location maybeSchema entries
            pure (aggregate, TySet)
        Raw.ExprStructReduct location schema record -> plain do
            (reduct, _annotation) <-
                compileStructureReduct location schema record
            pure (reduct, TySet)
        Raw.ExprStructReconstruction location schema record entries -> plain do
            (aggregate, _annotation) <-
                compileStructureReconstruction location schema record entries
            pure (aggregate, TySet)
  where
    plain action = do
        (term, coreType) <- action
        pure (compiledSourceTermForTerm (Raw.TermExpr expression) coreType term)

    exactIntrinsic provider arguments term presentation = do
        let occurrence = intrinsicProviderSourceTerm
                provider (Vector.fromList arguments) presentation
        unless (compiledSourceTermCore occurrence == term)
            (impossible
                "fixed intrinsic source Core disagrees with its provider identity")
        pure occurrence

compileSourceExpressionAsSetTerm
    :: Raw.Expr
    -> Elaborate CompiledSourceTerm
compileSourceExpressionAsSetTerm expression = do
    argument <- compileSourceExpression expression
    unless (compiledSourceTermType argument == TySet)
        (Except.throwError
            (ElaborationExpressionExpectedSet
                (locate expression)
                (compiledSourceTermType argument)))
    pure argument

-- | Compile one set expression once while retaining the checked-source shape
-- needed only when that expression is subsequently named by a definition.
-- Nested constructions remain ordinary exact terms.
compileNamedSetExpression
    :: Raw.Expr
    -> Elaborate CompiledBody
compileNamedSetExpression expression =
    fst <$> compileNamedSetExpressionWithSource expression

compileNamedSetExpressionWithSource
    :: Raw.Expr
    -> Elaborate (CompiledBody, CompiledSourceTerm)
compileNamedSetExpressionWithSource expression = case expression of
    Raw.ExprSep _location variable bound predicate -> do
        (term, bound', predicate') <-
            compileSeparation variable bound predicate
        pure
            ( CompiledBody term
                (Just
                    (CompiledSeparationConstruction
                        bound' predicate'))
                Nothing
            , opaque term
            )
    Raw.ExprReplace _location value bounds condition -> do
        replacement <-
            compileFunctionalReplacement value bounds condition
        let term = compiledFunctionalReplacementTerm replacement
        pure
            ( CompiledBody
                term
                (Just
                    (CompiledFunctionalReplacementConstruction
                        (compiledFunctionalReplacementDomains replacement)
                        (compiledFunctionalReplacementValue replacement)
                        (compiledFunctionalReplacementCondition replacement)))
                Nothing
            , opaque term
            )
    Raw.ExprReplacePred _location range domainVariable bound predicate -> do
        (term, domain, relation) <-
            compileRelationalReplacement
                range domainVariable bound predicate
        pure
            ( CompiledBody term
                (Just
                    (CompiledRelationalReplacementConstruction
                        domain relation))
                Nothing
            , opaque term
            )
    _ -> do
        source <- compileSourceExpressionAsSetTerm expression
        pure
            ( CompiledBody (compiledSourceTermCore source) Nothing Nothing
            , source
            )
  where
    opaque term =
        SourceTerm.sourceTermOccurrence
            term
            TySet
            (sourceTermPresentation (Raw.TermExpr expression))

compileNamedSetTerm :: Raw.Term -> Elaborate CompiledBody
compileNamedSetTerm term = fst <$> compileNamedSetTermWithSource term

compileNamedSetTermWithSource
    :: Raw.Term
    -> Elaborate (CompiledBody, CompiledSourceTerm)
compileNamedSetTermWithSource = \case
    Raw.TermExpr expression -> compileNamedSetExpressionWithSource expression
    term -> do
        source <- compileSourceTermAsSet term
        pure (ordinaryCompiledBody (compiledSourceTermCore source), source)

ordinaryCompiledBody :: CanonicalTerm ObjectId -> CompiledBody
ordinaryCompiledBody term = CompiledBody term Nothing Nothing

sourceTermCompiledBody :: CompiledSourceTerm -> CompiledBody
sourceTermCompiledBody term = CompiledBody (compiledSourceTermCore term) Nothing (Just (CompiledTermBody term))

propositionCompiledBody :: CompiledProposition -> CompiledBody
propositionCompiledBody proposition =
    CompiledBody
        (compiledPropositionCore proposition)
        Nothing
        (Just (CompiledPropositionBody proposition))

compileTermAsSet
    :: Raw.Term
    -> Elaborate (CanonicalTerm ObjectId)
compileTermAsSet term =
    compiledSourceTermCore <$> compileSourceTermAsSet term

compileSourceTermAsSet
    :: Raw.Term
    -> Elaborate CompiledSourceTerm
compileSourceTermAsSet = \case
    Raw.TermExpr expression ->
        compileSourceExpressionAsSetTerm expression
    term@(Raw.TermFun (Raw.Fun location item arguments)) -> do
        let patterns = Raw.lexicalItemSgPlPattern item
            key = SemanticFunctionPhrase (Raw.sg patterns) (Raw.pl patterns)
        compiled <- traverse compileSourceTermAsSet arguments
        occurrence <- compileSourceGlobalApplication
            location key compiled (sourceTermPresentation term)
        unless (compiledSourceTermType occurrence == TySet)
            (Except.throwError
                (ElaborationExpressionExpectedSet
                    location
                    (compiledSourceTermType occurrence)))
        pure occurrence
    Raw.TermQuantified _quantifier location _nounPhrase ->
        Except.throwError
            (ElaborationQuantifiedTermRequiresPropositionContext location)
    term ->
        Except.throwError
            (ElaborationUnsupportedDeclarationBody (locate term))

-- | Compile a written proposition term together with its diagnostic
-- presentation. A quantified term binds the whole consuming proposition, so
-- its source view retains that binder around the consuming proposition.
compileTermInCompiledProposition
    :: Raw.Term
    -> (CompiledSourceTerm -> Elaborate CompiledProposition)
    -> Elaborate CompiledProposition
compileTermInCompiledProposition term continuation =
    case term of
        Raw.TermExpr expression -> do
            compiled <- compileSourceExpressionAsSetTerm expression
            continuation compiled
        Raw.TermFun (Raw.Fun location item arguments) -> do
            let patterns = Raw.lexicalItemSgPlPattern item
                key =
                    SemanticFunctionPhrase
                        (Raw.sg patterns)
                        (Raw.pl patterns)
            compileTermsInCompiledProposition arguments \compiled -> do
                occurrence <- compileSourceGlobalApplication
                    location key compiled (sourceTermPresentation term)
                unless (compiledSourceTermType occurrence == TySet)
                    (Except.throwError
                        (ElaborationExpressionExpectedSet
                            location
                            (compiledSourceTermType occurrence)))
                continuation occurrence
        Raw.TermQuantified quantifier _location nounPhrase ->
            compileQuantifiedTermInProposition quantifier nounPhrase
                (continuation . compiledSourceTermForTerm term TySet)
        Raw.TermIota location _variable _statement ->
            Except.throwError
                (ElaborationUnsupportedDeclarationBody location)

compileTermsInCompiledProposition
    :: [Raw.Term]
    -> ([CompiledSourceTerm] -> Elaborate CompiledProposition)
    -> Elaborate CompiledProposition
compileTermsInCompiledProposition terms continuation =
    case terms of
        [] -> continuation []
        term : remaining ->
            compileTermInCompiledProposition term \compiled -> do
                compiledDepth <-
                    State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
                compileTermsInCompiledProposition remaining \rest -> do
                    currentDepth <-
                        State.gets
                            (binderStackDepth . lexicalBinderStack . elaborationScope)
                    when (currentDepth < compiledDepth)
                        (impossible
                            "a proposition term escaped its binder scope")
                    let compiled' =
                            SourceTerm.shiftCanonicalSourceTermOccurrence
                                (currentDepth - compiledDepth)
                                0
                                compiled
                    continuation (compiled' : rest)

compileExpression
    :: Raw.Expr
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
compileExpression expression = do
    compiled <- compileSourceExpression expression
    pure
        ( compiledSourceTermCore compiled
        , compiledSourceTermType compiled
        )

compileTypedExpression
    :: Raw.TypedExpression
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
compileTypedExpression = \case
    Raw.TypedExpressionExpr expression ->
        compileExpression expression
    Raw.TypedExpressionFormula formula ->
        (\term -> (compiledPropositionCore term, TyProp))
            <$> compileFormula formula

activeStructureReceiverCandidates
    :: (ResolvedStructureApplication -> Maybe selected)
    -> Elaborate [StructureReceiverCandidate selected]
activeStructureReceiverCandidates select = do
    structures <- State.gets (lexicalStructures . elaborationScope)
    binders <- State.gets (lexicalBinders . elaborationScope)
    let presentations =
            Map.fromList
                [ (index, renderSourceVariable variable)
                | (variable, (index, _coreType)) <- Map.toList binders
                ]
    pure
        [ StructureReceiverCandidate
            index
            (Map.findWithDefault
                ("binder #" <> Text.pack (show index))
                index
                presentations)
            structure
            selected
        | (index, structure) <- Map.toAscList structures
        , Just selected <- [select structure]
        ]

ambiguousStructureReceivers
    :: StructureReceiverCandidate selected
    -> StructureReceiverCandidate selected
    -> [StructureReceiverCandidate selected]
    -> NonEmpty Text
ambiguousStructureReceivers firstCandidate secondCandidate remaining =
    receiverPresentation firstCandidate
        :| ( receiverPresentation secondCandidate
           : fmap receiverPresentation remaining
           )
  where
    receiverPresentation
            (StructureReceiverCandidate _index presentation _structure _selected) =
        presentation

compileImplicitStructureFieldProjection
    :: Location -> Raw.StructSymbol -> Elaborate CompiledSourceTerm
compileImplicitStructureFieldProjection location symbol = do
    candidates <- activeStructureReceiverCandidates (structureAnnotationField symbol)
    (receiver, (identity, projection)) <- case candidates of
        [StructureReceiverCandidate index _presentation _structure field] -> pure (CBound index, field)
        firstCandidate : secondCandidate : remaining ->
            Except.throwError (ElaborationStructureReceiverAmbiguous location symbol
                (ambiguousStructureReceivers firstCandidate secondCandidate remaining))
        [] -> do
            contextual <- State.gets (lexicalContextualBinder . elaborationScope)
            case contextual of
                Nothing -> Except.throwError (ElaborationStructureFieldNotAvailable location symbol)
                Just index -> do
                    field <- resolveUniqueStructureField location symbol
                    recordContextualRequirement location symbol field
                    pure (CBound index, field)
    requireGlobalType projection (TyArrow TySet TySet)
    pure (structureFieldProviderSourceTerm identity projection
        (SourceTerm.sourceTermOccurrence receiver TySet (LocatedSourceTerm location))
        (LocatedSourceTerm location))

compileExplicitStructureFieldProjection
    :: Location
    -> Raw.StructSymbol
    -> Raw.Expr
    -> Elaborate ResolvedExplicitFieldSelection
compileExplicitStructureFieldProjection location symbol expression = do
    (receiver, selected) <- case expression of
        Raw.ExprStructAggregate aggregateLocation schema entries -> do
            (term, annotation) <-
                compileAnnotatedStructureAggregate
                    aggregateLocation schema entries
            let receiver = compiledSourceTermForTerm
                    (Raw.TermExpr expression) TySet term
            field <- projectionFromAssertable annotation
            pure (receiver, field)
        Raw.ExprStructReduct reductLocation schema record -> do
            (term, annotation) <-
                compileStructureReduct reductLocation schema record
            let receiver = compiledSourceTermForTerm
                    (Raw.TermExpr expression) TySet term
            field <- projectionFromAssertable annotation
            pure (receiver, field)
        Raw.ExprStructReconstruction reconstructionLocation schema record entries -> do
            (term, annotation) <-
                compileStructureReconstruction reconstructionLocation schema record entries
            let receiver = compiledSourceTermForTerm (Raw.TermExpr expression) TySet term
            field <- projectionFromAssertable annotation
            pure (receiver, field)
        _ -> do
            receiver <- compileSourceExpressionAsSetTerm expression
            structures <- State.gets (lexicalStructures . elaborationScope)
            field <- case termStructureAnnotation
                    (compiledSourceTermCore receiver) structures of
                Just annotation -> projectionFromResolved annotation
                Nothing -> resolveUniqueStructureField location symbol
            pure (receiver, field)
    let (identity, projection) = selected
    requireGlobalType projection (TyArrow TySet TySet)
    pure
        (ResolvedExplicitFieldSelection
            identity
            projection
            receiver
            (CApp (CGlobal projection) (compiledSourceTermCore receiver)))
  where
    projectionFromAssertable
            (AssertableStructureApplication resolved _predicate) =
        projectionFromResolved resolved

    projectionFromResolved annotation@(ResolvedStructureApplication phrase _ _) =
        maybe
            (Except.throwError
                (if symbol == Raw.CarrierSymbol
                    then ElaborationStructureCarrierUnavailable location phrase
                    else ElaborationStructureFieldNotAvailable location symbol))
            pure
            (structureAnnotationField symbol annotation)

    termStructureAnnotation term structures =
        case term of
            CBound index -> Map.lookup index structures
            _ -> Nothing

compileStructureReduct
    :: Location
    -> Raw.StructApplication Raw.Expr
    -> Raw.Expr
    -> Elaborate (CanonicalTerm ObjectId, AssertableStructureApplication)
compileStructureReduct location schema rawRecord = do
    (structure, annotation) <-
        resolveExpressionStructureApplication location schema
    record <- compileExpressionAsSet rawRecord
    selectors <- resolvedStructureSelectorTerms structure
    pure (Record.recordReduct selectors record, annotation)

-- The record interface is an elaboration prerequisite, not a target-structure
-- theorem. All replacements are compiled in the same surrounding context.
-- Canonical field identities select both copied projections and output order.
compileStructureReconstruction
    :: Location -> Raw.StructApplication Raw.Expr -> Raw.Expr
    -> [Raw.StructAggregateEntry]
    -> Elaborate (CanonicalTerm ObjectId, AssertableStructureApplication)
compileStructureReconstruction location schema rawBase entries = do
    (_, annotation, values) <- compileReconstructionParts location schema rawBase entries
    pure (aggregatePartsTerm values, annotation)

compileReconstructionParts
    :: Location -> Raw.StructApplication Raw.Expr -> Raw.Expr -> [Raw.StructAggregateEntry]
    -> Elaborate (Declaration.ResolvedStructure, AssertableStructureApplication,
        [ElaboratedRecordField (CanonicalTerm ObjectId)])
compileReconstructionParts location schema rawBase entries = do
    (result, _, _, _) <- compileReconstructionPartsWithBudget
        (initialFormationSearchBudget defaultFormationSearchLimits) location schema rawBase entries
    pure result

-- A read-only observation seam over the production resolver, not a second
-- resolver or a configurable source policy. Replay still gates success.
elaborateReconstructionWithBudget
    :: FormationSearchBudget -> ElaborationContext -> Raw.Expr
    -> Declaration.LoweringDriver (Either ElaborationError
        ([ElaboratedRecordField (CanonicalTerm ObjectId)], [ReconstructionCandidate],
            [ReconstructionAttempt], FormationSearchBudget))
elaborateReconstructionWithBudget budget context expression = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    State.evalStateT (case expression of
        Raw.ExprStructReconstruction location schema base entries -> do
            ((_, _, fields), candidates, attempts, remaining) <-
                compileReconstructionPartsWithBudget budget location schema base entries
            pure (fields, candidates, attempts, remaining)
        _ -> Except.throwError (ElaborationRecordAggregateRequired (locate expression))) initial

data ReconstructionCandidate = ReconstructionCandidate
    { reconstructionCandidateBranch :: !SemanticFactBranch
    , reconstructionCandidateStructure :: !StructureId
    , reconstructionCandidateAssertion :: !(Maybe (AtomTemplate (CanonicalTerm ObjectId)))
    } deriving stock (Show, Eq)

data ReconstructionAttempt = ReconstructionAttempt
    { reconstructionAttemptCandidate :: !(Maybe SemanticFactBranch)
    , reconstructionAttemptAssertion :: !(AtomTemplate (CanonicalTerm ObjectId))
    , reconstructionAttemptOutcome :: !(Either RichFormationFailure (Maybe SemanticFactBranch))
    , reconstructionAttemptWork :: !Natural
    } deriving stock (Show, Eq)

data RecordInterfaceStatus = CheckedRecordInterface | RegisteredRecordCandidate
    deriving stock (Show, Eq)

data ReconstructionInterface = ReconstructionInterface
    { reconstructionInterfacePhrase :: !Schema.StructurePhrase
    , reconstructionInterfaceParameters :: ![SourceTermPresentation]
    , reconstructionInterfaceFields :: ![(FieldId, Raw.StructSymbol)]
    } deriving stock (Show, Eq)

data ReconstructionFailure
    = NoRecordEvidence
    | MissingCopiedFields !RecordInterfaceStatus !ReconstructionInterface ![Raw.StructSymbol]
    | UndeterminedResultParameters !Schema.StructurePhrase
    | UnprovedRecordInterface !NotionQueryFailure
    deriving stock (Show, Eq)

renderReconstructionFailure :: ReconstructionFailure -> Text
renderReconstructionFailure = \case
    NoRecordEvidence -> "The base has no active structure assertion or fully instantiated registered provider result."
    MissingCopiedFields status interface missing ->
        (case status of
            CheckedRecordInterface -> "The checked "
            RegisteredRecordCandidate -> "The registered candidate ")
        <> renderPatternApplication (Schema.structurePhraseSingular (reconstructionInterfacePhrase interface))
            (renderSourceTermPresentation <$> reconstructionInterfaceParameters interface)
        <> " interface supplies " <> fields (snd <$> reconstructionInterfaceFields interface)
        <> "; missing copied fields: " <> fields missing <> "."
    UndeterminedResultParameters phrase ->
        "A registered " <> renderPatternSurface (Schema.structurePhraseSingular phrase)
            <> " result has schema parameters not determined by the written provider arguments."
    UnprovedRecordInterface failure ->
        "The candidate interface's formation premises could not be established. " <> renderNotionQueryFailure failure
  where
    fields [] = "no fields"
    fields symbols = Text.intercalate ", " (Raw.unStructSymbol <$> symbols)

compileReconstructionPartsWithBudget
    :: FormationSearchBudget -> Location -> Raw.StructApplication Raw.Expr -> Raw.Expr
    -> [Raw.StructAggregateEntry]
    -> Elaborate ((Declaration.ResolvedStructure, AssertableStructureApplication,
        [ElaboratedRecordField (CanonicalTerm ObjectId)]), [ReconstructionCandidate],
        [ReconstructionAttempt], FormationSearchBudget)
compileReconstructionPartsWithBudget initial location schema rawBase entries = do
    ((result, candidates, attempts), remaining) <- finishFormationQuery FormationNotionQuery location Nothing initial
        (compileReconstructionPartsIn location schema rawBase entries)
    pure (result, candidates, attempts, remaining)

compileReconstructionPartsIn
    :: Location -> Raw.StructApplication Raw.Expr -> Raw.Expr -> [Raw.StructAggregateEntry]
    -> FormationQuery ((Declaration.ResolvedStructure, AssertableStructureApplication,
        [ElaboratedRecordField (CanonicalTerm ObjectId)]), [ReconstructionCandidate], [ReconstructionAttempt])
compileReconstructionPartsIn location schema rawBase entries = do
    (target, annotation) <- formationElaborate (resolveExpressionStructureApplication location schema)
    let descriptor = Declaration.resolvedStructureSchema target
        fields = Schema.resolvedSchemaFields descriptor
        phrase = Schema.resolvedSchemaPhrase descriptor
        roles = Schema.resolvedSchemaFieldRoles descriptor
    replacements <- foldM (insertReplacement phrase roles) Map.empty entries
    let copied = Map.map Schema.resolvedFieldSymbol
            (Map.withoutKeys fields (Map.keysSet replacements))
    (base, candidates, attempts) <- checkedRecordBase (locate rawBase) schema copied rawBase
    values <- for (Map.toAscList fields) \(identity, field) -> do
        let selector = Schema.resolvedFieldSelector field
            projection = Schema.resolvedFieldProjection field
        formationElaborate (requireGlobalType selector TySet)
        (value, origin) <- case Map.lookup identity replacements of
            Just (entryLocation, rawValue) -> do
                value <- formationElaborate (compileExpressionAsSet rawValue)
                pure (value, WrittenRecordField entryLocation)
            Nothing -> do
                formationElaborate (requireGlobalType projection (TyArrow TySet TySet))
                pure (CApp (CGlobal projection) base, CopiedRecordField (locate rawBase))
        pure (ElaboratedRecordField field value origin)
    pure ((target, annotation, values), candidates, attempts)
  where
    insertReplacement phrase roles known = \case
        Raw.StructAggregatePositional value -> Except.throwError
            (ElaborationStructureAggregateMixedEntries (locate value))
        Raw.StructAggregateNamed entryLocation symbol value -> do
            identity <- maybe
                (Except.throwError (ElaborationStructureAggregateUnknownField entryLocation phrase symbol))
                pure (Map.lookup symbol roles)
            when (Map.member identity known)
                (Except.throwError (ElaborationStructureAggregateDuplicateField entryLocation phrase symbol))
            pure (Map.insert identity (entryLocation, value) known)

type ReconstructionSearch = FormationQuery

chargeReconstruction :: Location -> Natural -> ReconstructionSearch ()
chargeReconstruction = chargeFormationWork

sameReconstructionCore
    :: Location -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
    -> ReconstructionSearch Bool
sameReconstructionCore location left right = formationCoreWork location
    (\allowance -> countedCanonicalIdentity allowance left right)

checkedRecordBase
    :: Location -> Raw.StructApplication Raw.Expr -> Map FieldId Raw.StructSymbol -> Raw.Expr
    -> ReconstructionSearch (CanonicalTerm ObjectId, [ReconstructionCandidate], [ReconstructionAttempt])
checkedRecordBase location target needed expression = case expression of
    Raw.ExprStructAggregate at schema entries -> do
        (term, annotation) <- formationElaborate (compileAnnotatedStructureAggregate at schema entries)
        annotated term annotation
    Raw.ExprStructReconstruction at schema base entries -> do
        ((_, annotation, fields), candidates, attempts) <-
            compileReconstructionPartsIn at schema base entries
        (term, _, _) <- annotated (aggregatePartsTerm fields) annotation
        pure (term, candidates, attempts)
    Raw.ExprStructReduct at schema base -> do
        (structure, annotation) <- formationElaborate (resolveExpressionStructureApplication at schema)
        let retained = Schema.resolvedFieldSymbol <$>
                Schema.resolvedSchemaFields (Declaration.resolvedStructureSchema structure)
        (term, candidates, attempts) <- checkedRecordBase (locate base) schema retained base
        selectors <- formationElaborate (resolvedStructureSelectorTerms structure)
        (result, _, _) <- annotated (Record.recordReduct selectors term) annotation
        pure (result, candidates, attempts)
    _ -> do
        source <- formationElaborate (compileSourceExpressionAsSetTerm expression)
        designated <- formationElaborate (State.gets (lexicalStructures . elaborationScope))
        let term = compiledSourceTermCore source
            designation = case term of
                CBound index -> Map.lookup index designated
                _ -> Nothing
        case term of
            CBound index | Just resolved <- Map.lookup index designated,
                supplies resolved -> pure (term, [], [])
            _ -> do
                direct <- directRecordAssertions location source
                directInterfaces <- for direct \(identity, atom) -> do
                    interface <- candidateInterface identity (Just atom)
                    pure (atom, interface)
                let candidates = [(atom, interface) | (atom, interface) <- directInterfaces, suppliesInterface interface]
                (found, directFailure, directAttempts) <- firstReplayed [(Nothing, atom) | (atom, _) <- candidates]
                if found then pure (term, [], directAttempts) else do
                    discovered <- providerRecordAssertions location source
                    providerInterfaces <- for discovered \(branch, identity, atom) -> do
                        interface <- candidateInterface identity atom
                        pure (branch, atom, interface)
                    let usable = [(branch, atom, interface) | (branch, atom, interface) <- providerInterfaces,
                            suppliesInterface interface]
                    (success, providerFailure, attempts) <- firstReplayed
                        [(Just branch, atom) | (branch, Just atom, _) <- usable]
                    let observations = [ReconstructionCandidate branch identity (fmap compiledSourceTermCore <$> atom)
                            | (branch, identity, atom) <- discovered]
                    if success then pure (term, observations, directAttempts <> attempts) else do
                        -- Diagnostic selection uses only interfaces and query
                        -- failures already observed; it never adds proof work.
                        let established = (interfaceOf <$> designation) <|>
                                listToMaybe [interface | (_, interface) <- directInterfaces]
                        case established of
                            Just interface | not (suppliesInterface interface) ->
                                unavailable (missingFields CheckedRecordInterface interface)
                            _ -> case providerInterfaces of
                                (_, Nothing, interface) : _ -> unavailable
                                    (UndeterminedResultParameters (reconstructionInterfacePhrase interface))
                                (_, _, interface) : _ | not (suppliesInterface interface) ->
                                    unavailable (missingFields RegisteredRecordCandidate interface)
                                _ -> case directFailure <|> providerFailure of
                                    Just (atom, failure) -> do
                                        names <- formationElaborate structureDiagnosticNames
                                        statistics <- formationSearchBudgetStatistics <$> State.get
                                        unavailable (UnprovedRecordInterface (NotionQueryFailure names
                                            (compiledSourceTermPresentation <$> atom) Nothing failure statistics))
                                    Nothing -> unavailable NoRecordEvidence
  where
    supplies (ResolvedStructureApplication _ fields _) =
        Map.keysSet needed `Set.isSubsetOf` Set.fromList (fst <$> Map.elems fields)
    annotated term (AssertableStructureApplication resolved _) =
        if supplies resolved then pure (term, [], [])
        else unavailable (missingFields CheckedRecordInterface (interfaceOf resolved))
    interfaceOf (ResolvedStructureApplication phrase fields parameters) = ReconstructionInterface phrase
        (compiledSourceTermPresentation <$> parameters)
        (Map.toAscList (Map.fromList [(identity, symbol) | (symbol, (identity, _)) <- Map.toList fields]))
    suppliesInterface interface = null (missing interface)
    missing interface = Map.elems (Map.withoutKeys needed
        (Set.fromList (fst <$> reconstructionInterfaceFields interface)))
    missingFields status interface = MissingCopiedFields status interface (missing interface)
    candidateInterface identity atom = do
        chargeReconstruction location 1
        resolved <- formationElaborate (State.lift (Trans.lift
            (Declaration.resolveVisibleStructureIdLowering identity)))
        let structure = fromMaybe (impossible "visible reconstruction candidate lost its schema") resolved
            descriptor = Declaration.resolvedStructureSchema structure
            parameters = case atom of
                Just (StructureAtomTemplate _ arguments) -> compiledSourceTermPresentation <$> drop 1 (toList arguments)
                _ -> []
        pure (ReconstructionInterface (Schema.resolvedSchemaPhrase descriptor) parameters
            (Map.toAscList (Schema.resolvedFieldSymbol <$> Schema.resolvedSchemaFields descriptor)))
    firstReplayed [] = pure (False, Nothing, [])
    firstReplayed ((candidate, atom):rest) = do
        before <- formationInferenceWorkRemaining <$> State.get
        outcome <- replayReconstructionAssertion location atom
        after <- formationInferenceWorkRemaining <$> State.get
        let attempt = ReconstructionAttempt candidate (compiledSourceTermCore <$> atom) outcome (before - after)
        case outcome of
            Right _ -> pure (True, Nothing, [attempt])
            Left failure -> do
                (found, _, attempts) <- firstReplayed rest
                pure (found, if found then Nothing else Just (atom, failure), attempt : attempts)
    unavailable reason = formationElaborate (Except.throwError
        (ElaborationReconstructionBaseUnavailable location target expression reason))

-- Retained assertions are aligned and projected by the same checked scope
-- adapter as ordinary formation. An equality alone supplies no interface.
directRecordAssertions
    :: Location -> CompiledSourceTerm
    -> ReconstructionSearch [(StructureId, AtomTemplate CompiledSourceTerm)]
directRecordAssertions location source = do
    current <- formationElaborate State.get
    budget <- State.get
    let allowance = fromIntegral (min (fromIntegral (maxBound :: Word))
            (formationInferenceWorkRemaining budget))
        (result, remaining) = countedElaborationFormationObservations allowance
            (remainingFormationSearchLimits budget) FormationNotionQuery current
    let spent = fromIntegral (allowance - remaining)
    State.modify' (recordFormationCoreWork spent)
    chargeReconstruction location spent
    observations <- case result of
        Right (values, statistics) -> do
            consumeFormationStatistics location statistics
            pure values
        Left CountedCoreStructuralWorkExhausted ->
            chargeReconstruction location 1 >> impossible "exhausted reconstruction work was admitted"
        Left (CountedCoreOperationFailed (FormationObservationExhausted failure)) ->
            formationElaborate (Except.throwError (ElaborationFormationSearchFailed location failure))
        Left (CountedCoreOperationFailed _) ->
            impossible "a reconstruction assertion lost its checked scope"
    fmap catMaybes $ for observations \observation -> do
        chargeReconstruction location 1
        let atom = SourceTerm.forgetScopedSourceTermOccurrence <$>
                sourceAssertionAtom (formationObservationAssertion observation)
        case atom of
            StructureAtomTemplate head' arguments
                | Just (subject, _) <- Vector.uncons arguments -> do
                    matches <- sameReconstructionCore location
                        (compiledSourceTermCore subject) (compiledSourceTermCore source)
                    pure (if matches then Just (structureNotionHeadId head', atom) else Nothing)
            _ -> pure Nothing

providerRecordAssertions
    :: Location -> CompiledSourceTerm
    -> ReconstructionSearch [(SemanticFactBranch, StructureId, Maybe (AtomTemplate CompiledSourceTerm))]
providerRecordAssertions location source = case SourceTerm.sourceTermOccurrenceProvider source of
    Nothing -> pure []
    Just provider -> do
        catalog <- formationElaborate (State.lift (Trans.lift Declaration.formationCatalogLowering))
        results <- FormationCatalog.providerStructureResults (chargeReconstruction location)
            (SourceTerm.sourceTermProviderHead provider) catalog
        let candidates = [registered | Left (FormationProviderRule registered) <- results]
            count = fromIntegral (length candidates)
            orderingWork 0 = 0
            orderingWork n = 1 + orderingWork (n `div` 2)
        chargeReconstruction location (count * orderingWork count)
        fmap catMaybes $ for
            (List.sortOn visibleProviderResultRuleSource candidates)
            \registered -> do
                let declaration = visibleProviderResultRulePayload registered
                    providerTemplate = providerResultProvider declaration
                    providerTerm = TemplateProvider (resultProviderTemplateHead providerTemplate)
                        (resultProviderTemplateArguments providerTemplate)
                    rule = (\case
                        ResultRuleTerm term -> term
                        ResultRuleProviderValue -> providerTerm)
                        <$> providerResultConclusion declaration
                case rule of
                    StructureAtomTemplate head' arguments
                        | Just (subject, _) <- Vector.uncons arguments -> do
                            matched <- matchTemplate Map.empty subject source
                            case matched of
                                Nothing -> pure Nothing
                                Just bindings -> do
                                    _ <- traverseAtomTemplateArguments
                                        (\term -> chargeTemplate term >> pure term) rule
                                    chargeReconstruction location (fromIntegral (Map.size bindings))
                                    let ordered = Map.toAscList bindings
                                        indices = Map.fromList
                                            [(variable, OccurrenceArgumentIx index)
                                            | (index, (variable, _)) <- zip [0..] ordered]
                                    -- Result-only variables are not guessed. The author
                                    -- can establish a fully instantiated assertion instead.
                                    case traverseAtomTemplateArguments
                                            (traverseSetTermTemplateVariables (`Map.lookup` indices)) rule of
                                        Nothing -> pure (Just (visibleProviderResultRuleSource registered,
                                            structureNotionHeadId head', Nothing))
                                        Just template -> do
                                            atom <- instantiateFormationAtom location
                                                (Vector.fromList (snd <$> ordered)) template
                                            pure (Just (visibleProviderResultRuleSource registered,
                                                structureNotionHeadId head', Just atom))
                    _ -> pure Nothing
  where
    matchTemplate known template actual = do
        chargeReconstruction location 1
        case template of
            TemplateClosed value -> do
                matches <- sameReconstructionCore location (closedSetValueTerm value) (compiledSourceTermCore actual)
                pure (if matches then Just known else Nothing)
            TemplateVariable variable -> case Map.lookup variable known of
                Nothing -> pure (Just (Map.insert variable actual known))
                Just previous -> do
                    matches <- sameReconstructionCore location
                        (compiledSourceTermCore previous) (compiledSourceTermCore actual)
                    pure (if matches then Just known else Nothing)
            TemplateProvider head' arguments -> case SourceTerm.sourceTermOccurrenceProvider actual of
                Just provider | SourceTerm.sourceTermProviderHead provider == head',
                    length arguments == length (SourceTerm.sourceTermProviderArguments provider) ->
                        matchMany (Just known) (zip (toList arguments)
                            (toList (SourceTerm.sourceTermProviderArguments provider)))
                _ -> pure Nothing
            TemplateOrderedPair left right -> case SourceTerm.sourceTermOccurrenceOrderedPair actual of
                Just (firstTerm, secondTerm) -> matchMany (Just known) [(left, firstTerm), (right, secondTerm)]
                Nothing -> pure Nothing
    matchMany = foldM (\known (template, actual) ->
        maybe (pure Nothing) (\bindings -> matchTemplate bindings template actual) known)
    chargeTemplate template = do
        chargeReconstruction location 1
        case template of
            TemplateClosed value -> void (canonicalClosedWith (chargeReconstruction location 1) (closedSetValueTerm value))
            TemplateVariable{} -> pure ()
            TemplateProvider _ arguments -> traverse_ chargeTemplate arguments
            TemplateOrderedPair left right -> chargeTemplate left >> chargeTemplate right

replayReconstructionAssertion
    :: Location -> AtomTemplate CompiledSourceTerm
    -> ReconstructionSearch (Either RichFormationFailure (Maybe SemanticFactBranch))
replayReconstructionAssertion location atom = do
    result <- queryRegisteredFormation FormationNotionQuery location atom
    case result of
        Left failure -> pure (Left failure)
        Right evidence -> formationElaborate do
            target <- deriveNotionAtomProposition location (compiledSourceTermCore <$> atom)
            let materialized = materializeFormationEvidence defaultFormationSearchLimits evidence
            closure <- State.gets elaborationObjectClosure
            replayed <- State.lift (Trans.lift
                (Declaration.replayTransientFormationLowering closure materialized target))
            either (Except.throwError . ElaborationFormationReplayFailed location)
                (const (pure (Right (formationEvidenceBranch evidence)))) replayed

resolveUniqueStructureField
    :: Location
    -> Raw.StructSymbol
    -> Elaborate (FieldId, ObjectId)
resolveUniqueStructureField location symbol = do
    fields <-
        State.lift
            (Trans.lift
                (Declaration.resolveVisibleStructureFieldsLowering symbol))
    case fields of
        [] ->
            Except.throwError
                (ElaborationStructureFieldNotAvailable location symbol)
        [field] -> pure field
        _ ->
            Except.throwError
                (ElaborationStructureFieldAmbiguous
                    location symbol (snd <$> fields))

recordContextualRequirement
    :: Location
    -> Raw.StructSymbol
    -> (FieldId, ObjectId)
    -> Elaborate ()
recordContextualRequirement location symbol object = do
    existing <-
        State.gets
            (Map.lookup symbol . elaborationContextualRequirements)
    case existing of
        Nothing ->
            State.modify' \state ->
                state
                    { elaborationContextualRequirements =
                        Map.insert symbol object
                            (elaborationContextualRequirements state)
                    }
        Just actual
            | actual == object -> pure ()
            | otherwise ->
                Except.throwError
                    (ElaborationContextualRequirementConflict
                        location symbol actual object)

structureCarrierCast
    :: Location
    -> CanonicalTerm ObjectId
    -> Elaborate (CanonicalTerm ObjectId)
structureCarrierCast location term =
    case term of
        CBound index -> do
            annotation <- State.gets (Map.lookup index . lexicalStructures . elaborationScope)
            case annotation of
                Nothing -> pure term
                Just structure@(ResolvedStructureApplication phrase _ _) -> do
                    environment <- State.lift (Trans.lift Declaration.structureEnvironmentLowering)
                    let carrierProjection = do
                            manifest <- StructureEnvironment.structureEnvironmentManifest environment
                            (identity, projection) <- structureAnnotationField Raw.CarrierSymbol structure
                            guard (identity == StructureBuiltin.builtinCarrierFieldId manifest)
                            pure projection
                    carrier <-
                        maybe
                            (Except.throwError
                                (ElaborationStructureCarrierUnavailable location phrase))
                            pure
                            carrierProjection
                    requireGlobalType carrier (TyArrow TySet TySet)
                    pure (CApp (CGlobal carrier) term)
        _ -> pure term

compileMembershipProposition
    :: Location
    -> Raw.Sign
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Elaborate CompiledProposition
compileMembershipProposition location sign element set = do
    compileMembershipPropositionTerms
        location
        sign
        (locatedSetSourceTerm location element)
        (locatedSetSourceTerm location set)

compileMembershipPropositionTerms
    :: Location
    -> Raw.Sign
    -> CompiledSourceTerm
    -> CompiledSourceTerm
    -> Elaborate CompiledProposition
compileMembershipPropositionTerms location sign element set = do
    checkedSetCore <-
        structureCarrierCast location (compiledSourceTermCore set)
    let checkedSet
            | checkedSetCore == compiledSourceTermCore set = set
            | otherwise = SourceTerm.sourceTermOccurrence
                checkedSetCore
                TySet
                (compiledSourceTermPresentation set)
    let proposition =
            CApp
                (CApp (CIntrinsic Member) (compiledSourceTermCore element))
                checkedSetCore
    pure case sign of
        Raw.Positive ->
            atomicCompiledProposition
                (membershipSourceNotionAssertion
                    element checkedSet proposition ConjunctionHere location)
        Raw.Negative ->
            atomicCompiledProposition (sourceNotionAssertionFromTemplate
                (NegativeMembershipAtomTemplate element checkedSet) (logicalNot proposition) ConjunctionHere location)

compileSeparation
    :: Raw.VarSymbol
    -> Raw.Expr
    -> Raw.Stmt
    -> Elaborate
        ( CanonicalTerm ObjectId
        , CanonicalTerm ObjectId
        , CanonicalTerm ObjectId
        )
compileSeparation variable bound predicate = do
    bound' <- compileExpressionAsSet bound
    predicate' <-
        withSetBinders (variable :| []) do
            subject <- compileIntroducedVariable variable
            membershipGuard <-
                compileMembershipProposition
                    (locate bound)
                    Raw.Positive
                    subject
                    (shiftCanonical 1 0 bound')
            checked <-
                sealCompiledPropositionHere (locate bound) membershipGuard
            withCheckedFormationGuard
                FormationSeparationGenerator
                checked
                (compileStatement predicate)
    let predicateCore = compiledPropositionCore predicate'
    pure
        ( CApp
            (CApp (CIntrinsic Sep) bound')
            (CLam TySet predicateCore)
        , bound'
        , predicateCore
        )

compileRelationalReplacement
    :: Raw.VarSymbol
    -> Raw.VarSymbol
    -> Raw.Expr
    -> Raw.Stmt
    -> Elaborate
        ( CanonicalTerm ObjectId
        , CanonicalTerm ObjectId
        , CanonicalTerm ObjectId
        )
compileRelationalReplacement range domainVariable bound predicate = do
    domain <- compileExpressionAsSet bound
    relation <-
        withSetBinders (domainVariable :| [range]) do
            subject <- compileIntroducedVariable domainVariable
            membershipGuard <-
                compileMembershipProposition
                    (locate bound)
                    Raw.Positive
                    subject
                    (shiftCanonical 2 0 domain)
            checked <-
                sealCompiledPropositionHere (locate bound) membershipGuard
            withCheckedFormationGuard
                FormationRelationalReplacementGenerator
                checked
                (compileStatement predicate)
    let relationCore = compiledPropositionCore relation
    let restrictedDomain =
            CApp
                (CApp (CIntrinsic Sep) domain)
                (CLam TySet (logicalExists relationCore))
        choiceFunction =
            CLam TySet
                (CApp (CLogicalSelect TySet) (CLam TySet relationCore))
        replacement =
            CApp
                (CApp (CIntrinsic Repl) restrictedDomain)
                choiceFunction
    pure (replacement, domain, relationCore)

data CompiledFunctionalReplacement = CompiledFunctionalReplacement
    !(CanonicalTerm ObjectId)
    !(NonEmpty (CanonicalTerm ObjectId))
    !(CanonicalTerm ObjectId)
    !(Maybe (CanonicalTerm ObjectId))

compiledFunctionalReplacementTerm
    :: CompiledFunctionalReplacement
    -> CanonicalTerm ObjectId
compiledFunctionalReplacementTerm
        (CompiledFunctionalReplacement term _domains _value _condition) =
    term

compiledFunctionalReplacementDomains
    :: CompiledFunctionalReplacement
    -> NonEmpty (CanonicalTerm ObjectId)
compiledFunctionalReplacementDomains
        (CompiledFunctionalReplacement _term domains _value _condition) =
    domains

compiledFunctionalReplacementValue
    :: CompiledFunctionalReplacement
    -> CanonicalTerm ObjectId
compiledFunctionalReplacementValue
        (CompiledFunctionalReplacement _term _domains value _condition) =
    value

compiledFunctionalReplacementCondition
    :: CompiledFunctionalReplacement
    -> Maybe (CanonicalTerm ObjectId)
compiledFunctionalReplacementCondition
        (CompiledFunctionalReplacement _term _domains _value condition) =
    condition

compileFunctionalReplacement
    :: Raw.Expr
    -> NonEmpty (Raw.VarSymbol, Raw.Expr)
    -> Maybe Raw.Stmt
    -> Elaborate CompiledFunctionalReplacement
compileFunctionalReplacement
        value ((variable, domain) :| remaining) condition = do
    domain' <- compileExpressionAsSet domain
    case remaining of
        [] -> do
            (value', condition') <-
                withSetBinders (variable :| []) do
                    subject <- compileIntroducedVariable variable
                    membershipGuard <-
                        compileMembershipProposition
                            (locate domain)
                            Raw.Positive
                            subject
                            (shiftCanonical 1 0 domain')
                    checked <-
                        sealCompiledPropositionHere
                            (locate domain) membershipGuard
                    value' <-
                        withCheckedFormationGuard
                            FormationReplacementGenerator
                            checked
                            (compileExpressionAsSet value)
                    condition' <-
                        withCheckedFormationGuard
                            FormationReplacementGenerator
                            checked
                            (traverse compileStatement condition)
                    pure (value', condition')
            let filteredDomain =
                    case condition' of
                        Nothing -> domain'
                        Just predicate ->
                            CApp
                                (CApp (CIntrinsic Sep) domain')
                                (CLam TySet
                                    (compiledPropositionCore predicate))
            pure
                (CompiledFunctionalReplacement
                    (CApp
                        (CApp (CIntrinsic Repl) filteredDomain)
                        (CLam TySet value'))
                    (domain' :| [])
                    value'
                    (compiledPropositionCore <$> condition'))
        next : rest -> do
            nested <-
                withSetBinders (variable :| []) do
                    subject <- compileIntroducedVariable variable
                    membershipGuard <-
                        compileMembershipProposition
                            (locate domain)
                            Raw.Positive
                            subject
                            (shiftCanonical 1 0 domain')
                    checked <-
                        sealCompiledPropositionHere
                            (locate domain) membershipGuard
                    withCheckedFormationGuard
                        FormationReplacementGenerator
                        checked
                        (compileFunctionalReplacement
                            value (next :| rest) condition)
            pure
                (CompiledFunctionalReplacement
                    (CApp
                        (CIntrinsic FamilyUnion)
                        (CApp
                            (CApp (CIntrinsic Repl) domain')
                            (CLam TySet
                                (compiledFunctionalReplacementTerm nested))))
                    (domain'
                        NonEmpty.<|
                            compiledFunctionalReplacementDomains nested)
                    (compiledFunctionalReplacementValue nested)
                    (compiledFunctionalReplacementCondition nested))

compileStatement
    :: Raw.Stmt
    -> Elaborate CompiledProposition
compileStatement = \case
    Raw.StmtFormula formula ->
        compileFormula formula
    Raw.StmtVerbPhrase terms verbPhrase ->
        compileTermsInCompiledProposition (toList terms) \subjects ->
            conjoinCompiled
                <$> traverse (`compileVerbPhrase` verbPhrase) subjects
    Raw.StmtNoun sign terms nounPhrase ->
        compileTermsInCompiledProposition (toList terms) \subjects ->
            compileNounPhraseStatement sign subjects nounPhrase
    Raw.StmtExists _location nounPhrase ->
        compileExistentialNounPhrase nounPhrase
    Raw.StmtQuantPhrase
            _location
            (Raw.QuantPhrase quantifier nounPhrase)
            statement ->
        compileQuantifiedNounPhrase quantifier nounPhrase statement
    Raw.StmtConnected connective location left right ->
        compileConnective
            (fromMaybe (locate left) location)
            connective
            compileStatement
            left
            right
    Raw.StmtNeg _location statement ->
        negatedCompiledProposition <$> compileStatement statement
    Raw.SymbolicQuantified
            _location quantifier variables bound suchThat statement ->
        compileSymbolicQuantified
            quantifier variables bound suchThat (compileStatement statement)
    Raw.StmtStruct subject
            (Raw.StructNounPhrase left structure right residual) ->
        case subject of
            Raw.TermExpr
                    (Raw.ExprStructAggregate
                        location Nothing entries) -> do
                (resolved, annotation) <-
                    resolveStructureApplicationWith
                        compileSourceTermAsSet
                        location
                        structure
                aggregate <-
                    resolveStructureAggregate
                        location resolved annotation entries
                (term, aggregateAnnotation) <-
                    compileStructureAggregate aggregate
                components <- compileStructurePhraseComponents
                    [ ( location
                      , compiledSourceTermForTerm subject TySet term
                      , Nothing
                      )
                    ]
                    aggregateAnnotation left right residual
                pure
                    (fst
                        (assemblePhraseComponents
                            (phraseLogicalComponents components)))
            _ ->
                compileTermInCompiledProposition subject \compiledSubject -> do
                    annotation <-
                        resolveStructureAnnotation (locate subject) structure
                    binderIndex <- structureSubjectBinderIndex subject
                    components <- compileStructurePhraseComponents
                        [(locate subject, compiledSubject, binderIndex)]
                        annotation left right residual
                    pure
                        (fst
                            (assemblePhraseComponents
                                (phraseLogicalComponents components)))
    Raw.StmtExactStruct subject structure ->
        case subject of
            Raw.TermExpr
                    (Raw.ExprStructAggregate
                        location Nothing entries) -> do
                (resolved, annotation) <-
                    resolveStructureApplicationWith
                        compileSourceTermAsSet
                        location
                        structure
                aggregate <-
                    resolveStructureAggregate
                        location resolved annotation entries
                (term, aggregateAnnotation) <-
                    compileStructureAggregate aggregate
                open <- compileStructureNotionApplication
                    location
                    (locatedSetSourceTerm location term)
                    aggregateAnnotation
                selectors <- resolvedStructureSelectorTerms resolved
                pure
                    (conjoinCompiled
                        [ open
                        , atomicCompiledProposition
                            (exactStructureSourceNotionAssertion
                                (semanticRecordShapeKey (Declaration.resolvedStructureSchema resolved))
                                (locatedSetSourceTerm location term)
                                (Record.recordExactShape selectors term)
                                ConjunctionHere location)
                        ])
            _ ->
                compileTermInCompiledProposition subject \compiledSubject -> do
                    (resolved, annotation) <-
                        resolveStructureApplicationWith
                            compileSourceTermAsSet
                            (locate subject)
                            structure
                    open <- compileStructureNotionApplication
                        (locate subject)
                        compiledSubject
                        annotation
                    selectors <- resolvedStructureSelectorTerms resolved
                    pure
                        (conjoinCompiled
                            [ open
                            , atomicCompiledProposition
                                (exactStructureSourceNotionAssertion
                                    (semanticRecordShapeKey (Declaration.resolvedStructureSchema resolved))
                                    compiledSubject
                                    (Record.recordExactShape selectors
                                        (compiledSourceTermCore compiledSubject))
                                    ConjunctionHere (locate subject))
                            ])

compileQuantifiedTermInProposition
    :: Raw.Quantifier
    -> Raw.NounPhrase Maybe
    -> (CanonicalTerm ObjectId -> Elaborate CompiledProposition)
    -> Elaborate CompiledProposition
compileQuantifiedTermInProposition quantifier
        (Raw.NounPhrase left noun (Raw.NounBinder named bound) right suchThat)
        compileBody = do
    captured <- prepareNounBound (maybeToList named) bound
    case named of
        Nothing ->
            withAnonymousSetBinder (compileFor captured)
        Just variable ->
            withSetBinders (variable :| []) do
                subject <- compileIntroducedVariable variable
                compileFor captured subject
  where
    compileFor captured subject = do
        constraints <-
            compileBoundedNounConstraints captured
                [subject] left noun right suchThat
        checked <- sealCompiledPropositionHere (locate noun) constraints
        body <-
            withCheckedFormationGuard
                FormationQuantifiedTermRestriction
                checked
                (compileBody subject)
        pure (quantifyCompiledNounPhrase quantifier 1 constraints body)

compileSymbolicQuantified
    :: Raw.Quantifier
    -> NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Maybe Raw.Stmt
    -> Elaborate CompiledProposition
    -> Elaborate CompiledProposition
compileSymbolicQuantified Raw.Universally variables bound suchThat compileBody =
    compileUniversalSymbolicQuantified
        variables bound suchThat compileBody
compileSymbolicQuantified quantifier variables bound suchThat compileBody =
    withSetBinders variables do
        boundConstraints <-
            compileSymbolicBoundConstraintList variables bound
        suchThatConstraints <-
            maybeToList <$> traverse compileStatement suchThat
        let constraints =
                conjoinCompiled
                    (boundConstraints <> suchThatConstraints)
        checked <-
            sealCompiledPropositionHere
                (locate (NonEmpty.head variables)) constraints
        body <-
            withCheckedFormationGuard
                FormationSymbolicQuantifierRestriction
                checked
                compileBody
        pure (quantifyCompiledNounPhrase quantifier (length variables) constraints body)

compileUniversalSymbolicQuantified
    :: NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Maybe Raw.Stmt
    -> Elaborate CompiledProposition
    -> Elaborate CompiledProposition
compileUniversalSymbolicQuantified variables bound suchThat compileBody =
    go (toList variables)
  where
    go [] = do
        condition <- traverse compileStatement suchThat
        body <- case condition of
            Nothing -> compileBody
            Just restriction -> do
                checked <-
                    sealCompiledPropositionHere
                        (locate (NonEmpty.head variables)) restriction
                withCheckedFormationGuard
                    FormationSymbolicQuantifierResidual
                    checked
                    compileBody
        pure (maybe body (`implyCompiled` body) condition)
    go (variable : remaining) =
        withSetBinders (variable :| []) do
            subject <- compileSourceExpressionAsSetTerm
                (Raw.ExprVar variable)
            constraint <- compileSymbolicBoundConstraint subject bound
            checked <-
                sealCompiledPropositionHere (locate variable) constraint
            nested <-
                withCheckedFormationGuard
                    FormationSymbolicQuantifierBound
                    checked
                    (go remaining)
            pure (bindCompiled (implyCompiled constraint nested))

-- Keep the exact positive syntax; only compiler-elided truth is neutral.
implyCompiled :: CompiledProposition -> CompiledProposition -> CompiledProposition
implyCompiled guard body
    | isNeutralCompiled guard = body
    | otherwise = CompiledProposition
        (CImp (compiledPropositionCore guard) (compiledPropositionCore body))
        (SourceRequire (compiledPropositionEvidence guard) (compiledPropositionEvidence body)) []

bindCompiled :: CompiledProposition -> CompiledProposition
bindCompiled body = CompiledProposition
    (CForall TySet (compiledPropositionCore body))
    (SourceBind (compiledPropositionEvidence body)) []

existCompiled :: CompiledProposition -> CompiledProposition
existCompiled body = CompiledProposition
    (CExists TySet (compiledPropositionCore body))
    (SourceExists (compiledPropositionEvidence body)) []

compileSymbolicBoundConstraint
    :: CompiledSourceTerm
    -> Raw.Bound
    -> Elaborate CompiledProposition
compileSymbolicBoundConstraint subject = \case
    Raw.Unbounded ->
        pure (plainCompiledProposition logicalTruth)
    Raw.Bounded _location sign relation domain -> do
        domain' <- compileSourceExpressionAsSetTerm domain
        proposition <-
            compileAtomicRelationTerms subject relation domain'
        pure case sign of
            Raw.Positive -> proposition
            Raw.Negative ->
                negatedCompiledProposition proposition

compileSymbolicBoundConstraintList
    :: NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Elaborate [CompiledProposition]
compileSymbolicBoundConstraintList variables = \case
    Raw.Unbounded ->
        pure []
    Raw.Bounded _location sign relation domain -> do
        subjects <- traverse
            (compileSourceExpressionAsSetTerm . Raw.ExprVar)
            variables
        domain' <- compileSourceExpressionAsSetTerm domain
        traverse
            (\subject -> do
                proposition <-
                    compileAtomicRelationTerms subject relation domain'
                pure case sign of
                    Raw.Positive -> proposition
                    Raw.Negative ->
                        negatedCompiledProposition proposition)
            (toList subjects)

compileAtomicRelationTerms
    :: CompiledSourceTerm
    -> Raw.Relation
    -> CompiledSourceTerm
    -> Elaborate CompiledProposition
compileAtomicRelationTerms left relation right =
    case relation of
        Raw.Relation location symbol parameters -> do
            compiledParameters <-
                traverse compileSourceExpressionAsSetTerm parameters
            compileNamedRelationTerms
                location symbol compiledParameters left right
        Raw.RelationExpr location expression -> do
            resolved <- resolveTermRelation location expression left right
            instantiateResolvedRelation resolved 0 left right

-- Resolution owns formation and the choice of receiver or carrier. The small
-- instantiator below is pure with respect to those choices: fresh endpoints
-- never initiate a second formation query or receiver search.
data ResolvedSourceRelation = ResolvedSourceRelation
    ![CompiledSourceTerm]
    (Natural -> CompiledSourceTerm -> CompiledSourceTerm -> Elaborate CompiledProposition)

instantiateResolvedRelation
    :: ResolvedSourceRelation -> Natural -> CompiledSourceTerm -> CompiledSourceTerm
    -> Elaborate CompiledProposition
instantiateResolvedRelation (ResolvedSourceRelation _ instantiate) = instantiate

shiftRelationOperand :: Location -> Natural -> CompiledSourceTerm -> Elaborate CompiledSourceTerm
shiftRelationOperand _ 0 term = pure term
shiftRelationOperand location depth term = withAbbreviationExpansion location relationTemplateKey
    (expansionCoreWork (\work -> SourceTerm.countedShiftCanonicalSourceTermOccurrence work depth 0 term))

relationTemplateKey :: SemanticGlobalKey
relationTemplateKey = SemanticRelation (Raw.relationSymbolToken Raw.EqSymbol) Raw.zeroParameterArity

resolveNamedRelationTerms
    :: Location -> Raw.RelationSymbol -> [CompiledSourceTerm]
    -> CompiledSourceTerm -> CompiledSourceTerm -> Elaborate ResolvedSourceRelation
resolveNamedRelationTerms location symbol parameters left right = do
    let key = SemanticRelation (Raw.relationSymbolToken symbol) (Raw.relationSymbolParameterArity symbol)
        equality negateResult = do
            unless (compiledSourceTermType left == compiledSourceTermType right)
                (Except.throwError (ElaborationEqualityOperandMismatch location
                    (compiledSourceTermType left) (compiledSourceTermType right)))
            pure (ResolvedSourceRelation [] \_ a b -> do
                let proposition
                        | compiledSourceTermType a == TySet = compileSetEqualityProposition location a b
                        | otherwise = wholeCompiledOperands (CEq (compiledSourceTermType a)
                            (compiledSourceTermCore a) (compiledSourceTermCore b)) [a,b]
                pure (if negateResult then negatedCompiledProposition proposition else proposition))
        intrinsic identity negateResult = do
            adjusted <- if identity == Member then structureCarrierCast location (compiledSourceTermCore right)
                else pure (compiledSourceTermCore right)
            let adjustment = case adjusted of
                    CApp (CGlobal projection) operand | operand == compiledSourceTermCore right -> Just projection
                    _ -> Nothing
            pure (ResolvedSourceRelation parameters \depth a b -> do
                captured <- traverse (shiftRelationOperand location depth) parameters
                let b' = case adjustment of
                        Nothing -> b
                        Just projection -> SourceTerm.sourceTermOccurrence
                            (CApp (CGlobal projection) (compiledSourceTermCore b)) TySet (compiledSourceTermPresentation b)
                    arguments = captured <> [a,b']
                (formula, actual) <- applyTyped location (CIntrinsic identity) (coreIntrinsicType identity)
                    (compiledSourceTermArguments arguments)
                unless (actual == TyProp) (Except.throwError (ElaborationFormulaExpectedProposition location actual))
                let proposition = if identity == Member && null captured then atomicCompiledProposition
                        (membershipSourceNotionAssertion a b' formula ConjunctionHere location)
                        else wholeCompiledOperands formula arguments
                pure (if negateResult then negatedCompiledProposition proposition else proposition))
    case fixedSemanticMeaning key of
        Just FixedEquality | null parameters -> equality False
        Just FixedDisequality | null parameters -> equality True
        meaning -> do
            for_ (parameters <> [left,right]) \operand -> unless (compiledSourceTermType operand == TySet)
                (Except.throwError (ElaborationExpressionExpectedSet location (compiledSourceTermType operand)))
            case meaning of
                Just (FixedIntrinsic identity) -> intrinsic identity False
                Just (FixedNegatedIntrinsic identity) -> intrinsic identity True
                Just _ -> impossible "a fixed relation has an invalid source arity"
                Nothing -> do
                    override <- State.gets (Map.lookup key . elaborationLocalGlobalDefinitions)
                    case override of
                        Just internal -> pure (ResolvedSourceRelation parameters \depth a b -> do
                            captured <- traverse (shiftRelationOperand location depth) parameters
                            (formula, actual) <- applyLocalGlobalDefinition location key internal
                                (compiledSourceTermArguments (captured <> [a,b]))
                            unless (actual == TyProp) (Except.throwError (ElaborationFormulaExpectedProposition location actual))
                            pure (wholeCompiledOperands formula (captured <> [a,b])))
                        Nothing -> do
                            (binding, content) <- resolveVisibleSourceGlobalContent location key
                            traverse_ (dischargeFormationContract location binding (Vector.fromList (parameters <> [left,right])))
                                (resolvedBindingContract binding)
                            receiver <- resolveBindingReceiver location binding
                            pure (ResolvedSourceRelation (parameters <> maybeToList receiver) \depth a b -> do
                                captured <- traverse (shiftRelationOperand location depth) parameters
                                received <- traverse (shiftRelationOperand location depth) receiver
                                let arguments = Vector.fromList (captured <> [a,b])
                                case resolvedBindingExpansion binding of
                                    Just expansion -> instantiateBindingExpansionResolved location binding content arguments received expansion >>= \case
                                        CompiledPropositionBody proposition -> pure proposition
                                        CompiledTermBody{} -> impossible "a relation abbreviation returned a term"
                                    Nothing -> do
                                        let target = semanticGlobalBindingTarget (resolvedBindingDeclaration binding)
                                        (formula, actual) <- applyResolvedContent location key target content
                                            (compiledSourceTermArguments (toList arguments))
                                        unless (actual == TyProp) (Except.throwError (ElaborationFormulaExpectedProposition location actual))
                                        pure (atomicCompiledProposition (globalSourceNotionAssertion
                                            (RelationNotionHead (resolvedBindingRef binding))
                                            (Vector.fromList (a : captured <> [b])) formula ConjunctionHere location)))

resolveTermRelation
    :: Location -> Raw.Expr -> CompiledSourceTerm -> CompiledSourceTerm -> Elaborate ResolvedSourceRelation
resolveTermRelation location expression left right = do
    for_ [left,right] \operand -> unless (compiledSourceTermType operand == TySet)
        (Except.throwError (ElaborationExpressionExpectedSet location (compiledSourceTermType operand)))
    relation <- compileSourceExpressionAsSetTerm expression
    adjusted <- structureCarrierCast location (compiledSourceTermCore relation)
    let captured = if adjusted == compiledSourceTermCore relation then relation
            else SourceTerm.sourceTermOccurrence adjusted TySet (compiledSourceTermPresentation relation)
    pure (ResolvedSourceRelation [relation,captured] \depth a b -> do
        value <- shiftRelationOperand location depth captured
        let formula = CApp (CApp (CIntrinsic Member)
                (CApp (CApp (CIntrinsic OrderedPair) (compiledSourceTermCore a)) (compiledSourceTermCore b)))
                (compiledSourceTermCore value)
        pure (wholeCompiledOperands formula [a,b,value]))

compileNamedRelationTerms
    :: Location -> Raw.RelationSymbol -> [CompiledSourceTerm]
    -> CompiledSourceTerm -> CompiledSourceTerm -> Elaborate CompiledProposition
compileNamedRelationTerms location symbol parameters left right = do
    resolved <- resolveNamedRelationTerms location symbol parameters left right
    instantiateResolvedRelation resolved 0 left right

compileVerbPhrase
    :: CompiledSourceTerm
    -> Raw.VerbPhrase
    -> Elaborate CompiledProposition
compileVerbPhrase subject = \case
    Raw.VPVerb verb ->
        compileVerbProposition subject verb
    Raw.VPVerbNot verb -> do
        proposition <- compileVerbProposition subject verb
        pure
            (negatedCompiledProposition proposition)
    Raw.VPAdj adjectives ->
        conjoinCompiled
            <$> traverse (compileAdjectiveProposition subject) adjectives
    Raw.VPAdjNot adjectives ->
        negatedCompiledProposition
            . conjoinCompiled
            <$> traverse (compileAdjectiveProposition subject) adjectives

compileVerbPhraseWithAdjectiveReading
    :: AdjectiveReadingKind
    -> CompiledSourceTerm
    -> Raw.VerbPhrase
    -> Elaborate CompiledProposition
compileVerbPhraseWithAdjectiveReading reading subject = \case
    Raw.VPVerb verb ->
        compileVerbProposition subject verb
    Raw.VPVerbNot verb -> do
        proposition <- compileVerbProposition subject verb
        pure
            (negatedCompiledProposition proposition)
    Raw.VPAdj adjectives ->
        conjoinCompiled
            <$> traverse
                (compileAdjectivePropositionWithReading reading subject)
                adjectives
    Raw.VPAdjNot adjectives ->
        negatedCompiledProposition
            . conjoinCompiled
            <$> traverse
                (compileAdjectivePropositionWithReading reading subject)
                adjectives

compilePredicateArgumentsCompiled
    :: CompiledSourceTerm
    -> [Raw.Term]
    -> ( CompiledSourceTerm
        -> [CompiledSourceTerm]
        -> Elaborate CompiledProposition
       )
    -> Elaborate CompiledProposition
compilePredicateArgumentsCompiled subject arguments continuation = do
    subjectDepth <- State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
    compileTermsInCompiledProposition arguments \compiled -> do
        currentDepth <-
            State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
        when (currentDepth < subjectDepth)
            (impossible
                "a predicate subject escaped its binder scope")
        continuation
            (SourceTerm.shiftCanonicalSourceTermOccurrence
                (currentDepth - subjectDepth) 0 subject)
            compiled

compileVerbProposition
    :: CompiledSourceTerm
    -> Raw.Verb
    -> Elaborate CompiledProposition
compileVerbProposition subject (Raw.Verb location item arguments) =
    compilePredicateArgumentsCompiled
        subject arguments \subject' arguments' ->
            compileGlobalNotionApplication
                location
                VerbNotionHead
                (SemanticVerb (Raw.verbLexicalSurfaces item))
                (subject' : arguments')

compileAdjectiveProposition
    :: CompiledSourceTerm
    -> Raw.Adj
    -> Elaborate CompiledProposition
compileAdjectiveProposition subject (Raw.Adj location item arguments) =
    compilePredicateArgumentsCompiled subject arguments \subject' compiled ->
        lowerResolvedPredicateChoice location (ordinaryKey :| [structureKey]) (subject' : compiled)
            >>= \(term, resolved, expanded) -> case expanded of
                Just (CompiledPropositionBody proposition) -> pure proposition
                Just CompiledTermBody{} -> impossible "a proposition abbreviation returned a term"
                Nothing -> pure case resolved of
                        Nothing -> wholeCompiledOperands term (subject' : compiled)
                        Just binding -> atomicCompiledProposition
                            (globalSourceNotionAssertion (AdjectiveNotionHead (resolvedBindingRef binding))
                                (Vector.fromList (subject' : compiled)) term ConjunctionHere location)
  where
    ordinaryKey =
        semanticAdjectiveKey
            OrdinaryAdjectiveReading
            (Raw.adjectiveLexicalSide item)
            (Raw.adjectiveLexicalPattern item)
    structureKey =
        semanticAdjectiveKey
            StructureAdjectiveReading
            (Raw.adjectiveLexicalSide item)
            (Raw.adjectiveLexicalPattern item)

compileAdjectivePropositionWithReading
    :: AdjectiveReadingKind
    -> CompiledSourceTerm
    -> Raw.Adj
    -> Elaborate CompiledProposition
compileAdjectivePropositionWithReading reading subject
        (Raw.Adj location item arguments) =
    compilePredicateArgumentsCompiled subject arguments \subject' compiled ->
        compileGlobalNotionApplication
            location
            AdjectiveNotionHead
            (adjectiveKeyForPhraseReading reading item)
            (subject' : compiled)

-- Fixed intrinsic adjective syntax is mode-invariant. User adjectives alone
-- select an ordinary or structural reading from the containing phrase.
adjectiveKeyForPhraseReading
    :: AdjectiveReadingKind
    -> Raw.AdjectiveLexicalItem
    -> SemanticGlobalKey
adjectiveKeyForPhraseReading reading item =
    semanticAdjectiveKey selected
        (Raw.adjectiveLexicalSide item)
        (Raw.adjectiveLexicalPattern item)
  where
    selected = case Raw.adjectiveLexicalIdentity item of
        Raw.IntrinsicAdjectiveIdentity{} -> OrdinaryAdjectiveReading
        Raw.UserAdjectiveIdentity{} -> reading

compileLeftAdjectiveProposition
    :: CompiledSourceTerm
    -> Raw.AdjL
    -> Elaborate CompiledProposition
compileLeftAdjectiveProposition =
    compileLeftAdjectivePropositionWithReading OrdinaryAdjectiveReading

compileLeftAdjectivePropositionWithReading
    :: AdjectiveReadingKind
    -> CompiledSourceTerm
    -> Raw.AdjL
    -> Elaborate CompiledProposition
compileLeftAdjectivePropositionWithReading reading subject
        (Raw.AdjL location item arguments) =
    compilePredicateArgumentsCompiled subject arguments \subject' compiled ->
        compileGlobalNotionApplication
            location AdjectiveNotionHead
            (adjectiveKeyForPhraseReading reading item)
            (subject' : compiled)

compileStructureLeftAdjectiveProposition
    :: CompiledSourceTerm
    -> Raw.AdjL
    -> Elaborate CompiledProposition
compileStructureLeftAdjectiveProposition subject
        modifier =
    compileLeftAdjectivePropositionWithReading
        StructureAdjectiveReading subject modifier

compileRightAdjectiveProposition
    :: CompiledSourceTerm
    -> Raw.AdjR
    -> Elaborate CompiledProposition
compileRightAdjectiveProposition =
    compileRightAdjectivePropositionWithReading OrdinaryAdjectiveReading

compileRightAdjectivePropositionWithReading
    :: AdjectiveReadingKind
    -> CompiledSourceTerm
    -> Raw.AdjR
    -> Elaborate CompiledProposition
compileRightAdjectivePropositionWithReading reading subject = \case
    Raw.AdjR location item arguments ->
        compilePredicateArgumentsCompiled subject arguments \subject' compiled ->
            compileGlobalNotionApplication
                location AdjectiveNotionHead key (subject' : compiled)
          where
            key = adjectiveKeyForPhraseReading reading item
    Raw.AttrRThat verbPhrase ->
        compileVerbPhraseWithAdjectiveReading
            reading subject verbPhrase

compileNounProposition
    :: CompiledSourceTerm
    -> Raw.Noun
    -> Elaborate CompiledProposition
compileNounProposition subject (Raw.Noun location item arguments)
    | Lexicon.isBuiltinSetNoun item =
        pure (plainCompiledProposition logicalTruth)
    | otherwise = do
        let patterns = Raw.lexicalItemSgPlPattern item
            key = SemanticNoun (Raw.sg patterns) (Raw.pl patterns)
        compilePredicateArgumentsCompiled subject arguments \subject' compiled ->
            case fixedSemanticMeaning key of
                Just (FixedIntrinsic Member) ->
                    case compiled of
                        [set] ->
                            compileMembershipPropositionTerms
                                location Raw.Positive subject' set
                        _ ->
                            impossible
                                "the fixed element noun does not have one argument"
                Just (FixedIntrinsic intrinsic) -> do
                    (term, actual) <-
                        applyTyped
                            location
                            (CIntrinsic intrinsic)
                            (coreIntrinsicType intrinsic)
                            (compiledSourceTermArguments (subject' : compiled))
                    unless (actual == TyProp)
                        (Except.throwError
                            (ElaborationFormulaExpectedProposition location actual))
                    pure (wholeCompiledOperands term (subject' : compiled))
                Just{} ->
                    impossible "a fixed noun is not a predicate intrinsic"
                Nothing ->
                    compileGlobalNotionApplication
                        location NounNotionHead key (subject' : compiled)

-- The endpoint is checked before the group is introduced. Keeping its scoped
-- source occurrence retains provider arguments and makes later weakening exact.
data PreparedNounBound = PreparedNounBound
    !Raw.Sign !Raw.Relation !ScopedSourceTerm

requireUnboundedNoun :: Raw.Bound -> Elaborate ()
requireUnboundedNoun = \case
    Raw.Unbounded -> pure ()
    bound -> Except.throwError (ElaborationNounBoundUnsupported (locate bound))

prepareNounBound
    :: [Raw.VarSymbol] -> Raw.Bound -> Elaborate (Maybe PreparedNounBound)
prepareNounBound _ Raw.Unbounded = pure Nothing
prepareNounBound names (Raw.Bounded location sign relation endpoint) = do
    when (null names)
        (Except.throwError (ElaborationNounBoundUnsupported location))
    bindings <- State.gets (lexicalBinders . elaborationScope)
    -- A free group name is forbidden even when an outer binder has that name.
    -- Removing only lookup spellings preserves all other de Bruijn indices.
    modifyLexicalScope \scope -> scope
        { lexicalBinders = foldr Map.delete bindings names }
    source <- compileSourceExpressionAsSetTerm endpoint
        `Except.catchError` \case
            ElaborationFreeVariable occurrence variable | variable `elem` names ->
                Except.throwError (ElaborationNounBoundScope occurrence variable)
            failure -> Except.throwError failure
    modifyLexicalScope \scope -> scope { lexicalBinders = bindings }
    context <- currentSourceTermCheckingContext
    checked <- sealSourceOccurrenceHere (locate endpoint) context source
    pure (Just (PreparedNounBound sign relation checked))

compilePreparedNounBound
    :: CompiledSourceTerm -> PreparedNounBound -> Elaborate CompiledProposition
compilePreparedNounBound subject (PreparedNounBound sign relation endpoint) = do
    context <- State.gets (binderStackTypes . lexicalBinderStack . elaborationScope)
    lifted <- maybe
        (impossible "a noun bound escaped its captured lexical context")
        pure (SourceTerm.alignScopedSourceTermOccurrence context endpoint)
    proposition <- compileAtomicRelationTerms subject relation
        (SourceTerm.forgetScopedSourceTermOccurrence lifted)
    pure case sign of
        Raw.Positive -> proposition
        Raw.Negative -> negatedCompiledProposition proposition

compileBoundedNounConstraints
    :: Maybe PreparedNounBound
    -> [CanonicalTerm ObjectId]
    -> [Raw.AdjL]
    -> Raw.Noun
    -> [Raw.AdjR]
    -> Maybe Raw.Stmt
    -> Elaborate CompiledProposition
compileBoundedNounConstraints bound subjects left noun right residual = do
    components <- compileNounPhraseComponentsWithBound bound
        (locatedSetSourceTerm (locate noun) <$> subjects)
        left noun right residual
    pure (fst (assemblePhraseComponents (phraseLogicalComponents components)))

compileNounPhraseConstraintsPresented
    :: [CompiledSourceTerm]
    -> [Raw.AdjL]
    -> Raw.Noun
    -> [Raw.AdjR]
    -> Maybe Raw.Stmt
    -> Elaborate CompiledProposition
compileNounPhraseConstraintsPresented subjects left noun right suchThat = do
    components <-
        compileNounPhraseComponentsPresented subjects left noun right suchThat
    pure
        (fst
            (assemblePhraseComponents
                (phraseLogicalComponents components)))

compileNounPhraseComponentsPresented
    :: [CompiledSourceTerm]
    -> [Raw.AdjL]
    -> Raw.Noun
    -> [Raw.AdjR]
    -> Maybe Raw.Stmt
    -> Elaborate CompiledPhraseComponents
compileNounPhraseComponentsPresented = compileNounPhraseComponentsWithBound Nothing

compileNounPhraseComponentsWithBound
    :: Maybe PreparedNounBound
    -> [CompiledSourceTerm]
    -> [Raw.AdjL]
    -> Raw.Noun
    -> [Raw.AdjR]
    -> Maybe Raw.Stmt
    -> Elaborate CompiledPhraseComponents
compileNounPhraseComponentsWithBound captured subjects left noun right suchThat = do
    rows <- traverse compileSubject (zip [0 :: Natural ..] subjects)
    let components = CompiledPhraseComponents
            { phraseCoreComponents = [core | (core, _, _, _) <- rows]
            , phraseBoundComponents = concat [bound | (_, bound, _, _) <- rows]
            , phraseLeftComponents = [modifiers | (_, _, modifiers, _) <- rows]
            , phraseRightComponents = [modifiers | (_, _, _, modifiers) <- rows]
            , phraseResidualComponent = Nothing
            }
    residual <- for suchThat \statement ->
        withCompletedPhraseHead (locate statement)
            (phraseLogicalComponents components)
            (CompiledPhraseComponent PhraseRegular
                (phraseResidualComponentOrdinal subjectCount (leftCount + boundWidth) rightCount)
                <$> compileStatement statement)
    pure components { phraseResidualComponent = residual }
  where
    subjectCount = fromIntegral (length subjects)
    leftCount = fromIntegral (length left)
    rightCount = fromIntegral (length right)
    boundWidth = maybe 0 (const 1) captured

    compileSubject (subjectOrdinal, subject) = do
        core <- compileNounProposition subject noun
        checkedCore <- sealCompiledPropositionHere (locate noun) core
        bounds <- for (maybeToList captured) \bound ->
            withCheckedFormationGuard FormationNounPhraseCore checkedCore
                (CompiledPhraseComponent PhraseRegular
                    (phraseRightComponentOrdinal subjectCount leftCount subjectOrdinal 0)
                    <$> compilePreparedNounBound subject bound)
        let coreComponent = CompiledPhraseComponent
                (if nounIsHardSet noun then PhraseHardSet else PhraseRegular)
                (phraseCoreComponentOrdinal subjectCount leftCount subjectOrdinal)
                core
        (guardKind, checkedHead) <- case bounds of
            [] -> pure (FormationNounPhraseCore, checkedCore)
            _ -> (,) FormationBoundedNounHead
                <$> sealCompiledPropositionHere (locate noun)
                    (fst (assemblePhraseComponents (coreComponent : bounds)))
        leftConstraints <- withCheckedFormationGuard guardKind checkedHead
            (for (zip [0 :: Natural ..] left) \(modifierOrdinal, modifier) ->
                CompiledPhraseComponent PhraseRegular
                    (phraseLeftComponentOrdinal subjectCount subjectOrdinal modifierOrdinal)
                    <$> compileLeftAdjectiveProposition subject modifier)
        rightConstraints <- withCheckedFormationGuard guardKind checkedHead
            (for (zip [0 :: Natural ..] right) \(modifierOrdinal, modifier) ->
                CompiledPhraseComponent PhraseRegular
                    (phraseRightComponentOrdinal subjectCount (leftCount + boundWidth)
                        subjectOrdinal modifierOrdinal)
                    <$> compileRightAdjectiveProposition subject modifier)
        pure (coreComponent, bounds, leftConstraints, rightConstraints)

nounIsHardSet :: Raw.Noun -> Bool
nounIsHardSet (Raw.Noun _ item _arguments) =
    Lexicon.isBuiltinSetNoun item

compileNounPhraseStatement
    :: Raw.Sign
    -> [CompiledSourceTerm]
    -> Raw.NounPhrase Maybe
    -> Elaborate CompiledProposition
compileNounPhraseStatement sign subjects phrase@(Raw.NounPhrase
        left noun (Raw.NounBinder named bound) right suchThat) = do
    requireUnboundedNoun bound
    case named of
        Nothing -> case sign of
            Raw.Positive ->
                compileNounPhraseConstraintsPresented
                    subjects left noun right suchThat
            Raw.Negative ->
                conjoinCompiled <$> traverse
                    (\subject -> withPolarity
                        <$> compileNounPhraseConstraintsPresented
                            [subject] left noun right suchThat)
                    subjects
        Just{} ->
            case subjects of
                [subject] -> withPolarity <$> compileNounPhraseMaybe subject phrase
                _ ->
                    Except.throwError
                        (ElaborationGroupedNounNameUnsupported (locate noun))
  where
    withPolarity proposition = case sign of
        Raw.Positive -> proposition
        Raw.Negative ->
            negatedCompiledProposition proposition

compileNounPhraseMaybe
    :: CompiledSourceTerm
    -> Raw.NounPhrase Maybe
    -> Elaborate CompiledProposition
compileNounPhraseMaybe subject
        (Raw.NounPhrase left noun (Raw.NounBinder named bound) right suchThat) = do
    requireUnboundedNoun bound
    case named of
        Nothing ->
            compileNounPhraseConstraintsPresented
                [subject] left noun right suchThat
        Just variable -> do
            abstracted <-
                withSetBinders (variable :| [])
                    (compileNounPhraseConstraintsPresented
                        [ SourceTerm.sourceTermOccurrence
                            (CBound 0)
                            TySet
                            (PresentedSourceTerm
                                (locate variable)
                                (renderSourceVariable variable))
                        ]
                        left noun right suchThat)
            let subjectCore = compiledSourceTermCore subject
            pure
                (CompiledProposition
                    (instantiateCanonical subjectCore
                        (compiledPropositionCore abstracted))
                    (runIdentity (SourceEvidence.traverseSourceAtDepth
                        (\depth -> instantiateSupportPrefixWith (pure ()) 1
                            (\nested _ -> let shifted = SourceTerm.shiftCanonicalSourceTermOccurrence nested 0 subject
                                in pure (SourceTerm.sourceSupportTemplate id shifted, compiledSourceTermCore shifted)) depth) (\depth ->
                        traverseSourceNotionAssertionParts
                            (Identity . SourceTerm.instantiateCanonicalSourceTermOccurrenceAt depth subject)
                            (Identity . instantiateCanonicalAt depth subjectCore))
                        (compiledPropositionEvidence abstracted)))
                    ( map
                        (runIdentity
                            . traverseSourceEqualityOccurrenceParts
                                (Identity
                                    . SourceTerm.instantiateCanonicalSourceTermOccurrence
                                        subject)
                                (Identity
                                    . instantiateCanonical subjectCore))
                        (compiledPropositionEqualities abstracted)
                    ))

compileExistentialNounPhrase
    :: Raw.NounPhrase []
    -> Elaborate CompiledProposition
compileExistentialNounPhrase
        (Raw.NounPhrase left noun (Raw.NounBinder variables bound) right suchThat) = do
    captured <- prepareNounBound variables bound
    case NonEmpty.nonEmpty variables of
        Just binders ->
            withSetBinders binders do
                subjects <- traverse compileIntroducedVariable binders
                constraints <-
                    compileBoundedNounConstraints captured
                        (toList subjects) left noun right suchThat
                pure (foldr (const existCompiled) constraints binders)
        Nothing ->
            withAnonymousSetBinder \subject -> do
                constraints <- compileBoundedNounConstraints captured [subject] left noun right suchThat
                pure (existCompiled constraints)

compileQuantifiedNounPhrase
    :: Raw.Quantifier
    -> Raw.NounPhrase []
    -> Raw.Stmt
    -> Elaborate CompiledProposition
compileQuantifiedNounPhrase quantifier
        (Raw.NounPhrase left noun (Raw.NounBinder variables bound) right suchThat)
        statement = do
    captured <- prepareNounBound variables bound
    case NonEmpty.nonEmpty variables of
        Just binders ->
            withSetBinders binders do
                subjects <- traverse compileIntroducedVariable binders
                constraints <-
                    compileBoundedNounConstraints captured
                        (toList subjects) left noun right suchThat
                body <- compileStatementUnderGuard
                    FormationQuantifiedNounRestriction constraints statement
                pure
                    (quantifyCompiledNounPhrase quantifier (length (toList binders)) constraints body)
        Nothing ->
            withAnonymousSetBinder \subject -> do
                constraints <-
                    compileBoundedNounConstraints captured
                        [subject] left noun right suchThat
                body <- compileStatementUnderGuard
                    FormationQuantifiedNounRestriction constraints statement
                pure
                    (quantifyCompiledNounPhrase quantifier 1 constraints body)

compileStatementUnderGuard
    :: FormationGuardKind
    -> CompiledProposition
    -> Raw.Stmt
    -> Elaborate CompiledProposition
compileStatementUnderGuard kind restriction statement = do
    checked <- sealCompiledPropositionHere (locate statement) restriction
    withCheckedFormationGuard kind checked (compileStatement statement)

quantifyCompiledNounPhrase
    :: Raw.Quantifier -> Int -> CompiledProposition -> CompiledProposition -> CompiledProposition
quantifyCompiledNounPhrase Raw.Universally count constraints body =
    foldr (const bindCompiled) (implyCompiled constraints body) [1 .. count]
quantifyCompiledNounPhrase Raw.Existentially count constraints body =
    foldr (const existCompiled) restricted [1 .. count]
  where
    -- Preserve quantifyNounPhrase's Core shape, including a trailing truth.
    -- Retaining source capabilities must not simplify statements or ATP tasks.
    restricted
        | compiledPropositionCore constraints == logicalTruth = body
        | otherwise = conjoinCompiledPair constraints body
quantifyCompiledNounPhrase quantifier count constraints body =
    residualCompiledProposition (quantifyNounPhrase quantifier count
        (compiledPropositionCore constraints) (compiledPropositionCore body)) (replicate count TySet) [constraints,body]

quantifyNounPhrase
    :: Raw.Quantifier
    -> Int
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
quantifyNounPhrase quantifier binderCount constraints body =
    case quantifier of
        Raw.Universally ->
            quantify
                (if constraints == logicalTruth
                    then body
                    else CImp constraints body)
        Raw.Existentially ->
            quantify
                (if constraints == logicalTruth
                    then body
                    else logicalAnd constraints body)
        Raw.Nonexistentially ->
            logicalNot
                (quantify
                    (if constraints == logicalTruth
                        then body
                        else logicalAnd constraints body))
  where
    quantify scoped =
        foldr (const binder) scoped [1 .. binderCount]
    binder = case quantifier of
        Raw.Universally -> CForall TySet
        Raw.Existentially -> logicalExists
        Raw.Nonexistentially -> logicalExists

withAnonymousSetBinder
    :: (CanonicalTerm ObjectId -> Elaborate value)
    -> Elaborate value
withAnonymousSetBinder action =
    withLexicalBinders ((Nothing, TySet) :| []) (action (CBound 0))

withSetBinders
    :: NonEmpty Raw.VarSymbol
    -> Elaborate value
    -> Elaborate value
withSetBinders variables =
    withTypedBinders variables TySet

withTypedBinders
    :: NonEmpty Raw.VarSymbol
    -> CoreType
    -> Elaborate value
    -> Elaborate value
withTypedBinders variables binderType =
    withLexicalBinders ((\variable -> (Just variable, binderType)) <$> variables)

withLexicalBinders
    :: NonEmpty (Maybe Raw.VarSymbol, CoreType)
    -> Elaborate value
    -> Elaborate value
withLexicalBinders binders action = do
    outer <- State.gets elaborationScope
    inner <- Except.liftEither (extendLexicalBinders binders outer)
    modifyLexicalScope (const inner)
    result <- action
    modifyLexicalScope (const outer)
    pure result

extendLexicalBinders
    :: NonEmpty (Maybe Raw.VarSymbol, CoreType)
    -> LexicalScope
    -> Either ElaborationError LexicalScope
extendLexicalBinders binders outer = do
    case firstDuplicate names <|> find (`Map.member` lexicalBinders outer) names of
        Just duplicate -> Left
            (ElaborationDuplicateLocalBinder (locate duplicate) duplicate)
        Nothing -> pure ()
    pure outer
        { lexicalBinders = introduced
            <> shiftElaborationBinders binderCount (lexicalBinders outer)
        , lexicalBinderStack = BinderStack
            (reverse (snd <$> toList binders)
                <> binderStackTypes (lexicalBinderStack outer))
        , lexicalStructures =
            shiftElaborationStructures binderCount (lexicalStructures outer)
        , lexicalContextualBinder = (+ binderCount) <$> lexicalContextualBinder outer
        }
  where
    names = catMaybes (fst <$> toList binders)
    binderCount = fromIntegral (length binders)
    introduced = Map.fromList
        [ (variable, (index, binderType))
        | ((Just variable, binderType), index) <-
            zip (toList binders) (reverse [0 .. binderCount - 1])
        ]

shiftElaborationBinders
    :: Natural
    -> Map.Map Raw.VarSymbol (Natural, CoreType)
    -> Map.Map Raw.VarSymbol (Natural, CoreType)
shiftElaborationBinders amount =
    fmap (first (+ amount))

shiftElaborationStructures
    :: Natural
    -> Map.Map Natural ResolvedStructureApplication
    -> Map.Map Natural ResolvedStructureApplication
shiftElaborationStructures amount =
    Map.mapKeysMonotonic (+ amount)
        . fmap (weakenStructureAnnotation amount)

compileFormula
    :: Raw.Formula
    -> Elaborate CompiledProposition
compileFormula = \case
    Raw.FormulaChain chain ->
        compileRelationChain chain
    Raw.FormulaSetMap location function domain codomain ->
        compileRelationChain
            (Raw.setMapFormulaChain location function domain codomain)
    Raw.FormulaExpression expression -> do
        (term, actual) <- compileExpression expression
        unless (actual == TyProp)
            (Except.throwError
                (ElaborationFormulaExpectedProposition
                    (locate expression)
                    actual))
        opaqueCompiledProposition (locate expression) term
    Raw.PropositionalConstant _ Raw.IsBottom ->
        pure (plainCompiledProposition CFalsum)
    Raw.PropositionalConstant _ Raw.IsTop ->
        pure (plainCompiledProposition CTruth)
    Raw.FormulaNeg _ formula ->
        negatedCompiledProposition <$> compileFormula formula
    Raw.FormulaPredicate
            location
            (Raw.PrefixPredicate command arity)
            _marker
            arguments ->
        compileGlobalNotionApplication
            location
            PrefixPredicateNotionHead
            (SemanticPrefixPredicate command (fromIntegral arity))
            =<< traverse compileSourceExpression (toList arguments)
    Raw.Connected location connective left right ->
        compileConnective
            location
            connective
            compileFormula
            left
            right
    Raw.FormulaQuantified
            _location quantifier variables bound formula ->
        compileSymbolicQuantified
            quantifier variables bound Nothing (compileFormula formula)
    Raw.FormulaTypedQuantified
            _location quantifier variables concreteType formula -> do
        let binderType = concreteTypeCoreType concreteType
        body <-
            withTypedBinders variables binderType
                (compileFormula formula)
        let quantify binder =
                foldr
                    (const binder)
                    (compiledPropositionCore body)
                    variables
        pure case quantifier of
            Raw.Universally | binderType == TySet ->
                foldr (const bindCompiled) body variables
            Raw.Universally ->
                residualCompiledProposition (quantify (CForall binderType)) (replicate (length variables) binderType) [body]
            Raw.Existentially | binderType == TySet ->
                foldr (const existCompiled) body variables
            Raw.Existentially ->
                residualCompiledProposition
                    (quantify (logicalExistsAt binderType)) (replicate (length variables) binderType) [body]
            Raw.Nonexistentially ->
                residualCompiledProposition
                    (logicalNot (quantify (logicalExistsAt binderType))) (replicate (length variables) binderType) [body]
compileConnective
    :: Location
    -> Raw.Connective
    -> (input -> Elaborate CompiledProposition)
    -> input
    -> input
    -> Elaborate CompiledProposition
compileConnective _location connective compile left right = do
    left' <- compile left
    case connective of
        Raw.Implication -> do
            checkedLeft <- sealCompiledPropositionHere _location left'
            right' <-
                withCheckedFormationGuard
                    FormationImplicationAntecedent
                    checkedLeft
                    (compile right)
            pure (CompiledProposition
                (CImp (compiledPropositionCore left') (compiledPropositionCore right'))
                (SourceRequire (compiledPropositionEvidence left') (compiledPropositionEvidence right')) [])
        _ -> do
            right' <- compile right
            let leftCore = compiledPropositionCore left'
                rightCore = compiledPropositionCore right'
                plain formula = residualCompiledProposition formula [] [left',right']
            pure case connective of
                Raw.Conjunction -> conjoinCompiled [left', right']
                Raw.Disjunction -> CompiledProposition (COr leftCore rightCore)
                    (SourceOr (compiledPropositionEvidence left') (compiledPropositionEvidence right')) []
                Raw.Equivalence -> CompiledProposition (CEq TyProp leftCore rightCore)
                    (SourceIff (compiledPropositionEvidence left') (compiledPropositionEvidence right')) []
                Raw.ExclusiveOr -> plain
                    (logicalAnd
                        (logicalOr leftCore rightCore)
                        (logicalNot (logicalAnd leftCore rightCore)))
                Raw.NegatedDisjunction ->
                    plain (logicalNot (logicalOr leftCore rightCore))

logicalAnd
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
logicalAnd left right =
    CAnd left right

logicalTruth :: CanonicalTerm global
logicalTruth =
    CTruth

logicalOr
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
logicalOr left right =
    COr left right

logicalExists
    :: CanonicalTerm global
    -> CanonicalTerm global
logicalExists body =
    logicalExistsAt TySet body

logicalExistsAt
    :: CoreType
    -> CanonicalTerm global
    -> CanonicalTerm global
logicalExistsAt binderType body =
    CExists binderType body

compileAtomicRelation
    :: NonEmpty Raw.Expr -> Raw.Relation -> NonEmpty Raw.Expr -> Elaborate CompiledProposition
compileAtomicRelation left relation right = case (toList left, relation, toList right) of
    ([leftExpression], Raw.Relation location symbol parameters, [rightExpression]) -> do
        captured <- traverse compileSourceExpressionAsSetTerm parameters
        a <- compileSourceExpression leftExpression
        b <- compileSourceExpression rightExpression
        compileNamedRelationTerms location symbol captured a b
    ([leftExpression], Raw.RelationExpr location expression, [rightExpression]) -> do
        a <- compileSourceExpressionAsSetTerm leftExpression
        b <- compileSourceExpressionAsSetTerm rightExpression
        resolved <- resolveTermRelation location expression a b
        instantiateResolvedRelation resolved 0 a b
    _ -> Except.throwError (ElaborationUnsupportedDeclarationBody (locate relation))

compileSetEqualityProposition
    :: Location
    -> CompiledSourceTerm
    -> CompiledSourceTerm
    -> CompiledProposition
compileSetEqualityProposition location left right =
    atomicCompiledEquality
        (setSourceEqualityOccurrence
            left
            right
            (CEq TySet
                (compiledSourceTermCore left)
                (compiledSourceTermCore right))
            ConjunctionHere
            location)

compileRelationChain
    :: Raw.Chain
    -> Elaborate CompiledProposition
compileRelationChain chain =
    conjoinCompiled <$> traverse compileLink (chainLinks chain)
  where
    compileLink (sign, relation, left, right) = do
        proposition <-
            compileAtomicRelation
                (left :| []) relation (right :| [])
        pure case sign of
            Raw.Positive -> proposition
            Raw.Negative ->
                negatedCompiledProposition proposition

    chainLinks = \case
        Raw.ChainBase left sign relation right ->
            [ (sign, relation, leftExpression, rightExpression)
            | leftExpression <- toList left
            , rightExpression <- toList right
            ]
        Raw.ChainCons left sign relation rest ->
            let firstRight = chainFirstLeft rest
            in
                [ (sign, relation, leftExpression, rightExpression)
                | leftExpression <- toList left
                , rightExpression <- toList firstRight
                ]
                <> chainLinks rest

    chainFirstLeft = \case
        Raw.ChainBase left _sign _relation _right -> left
        Raw.ChainCons left _sign _relation _rest -> left

applyResolvedPredicate
    :: Location
    -> SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate (CanonicalTerm ObjectId)
applyResolvedPredicate location key =
    applyResolvedPredicateChoice location (key :| [])

applyResolvedPredicateChoice
    :: Location
    -> NonEmpty SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate (CanonicalTerm ObjectId)
applyResolvedPredicateChoice location keys arguments = do
    (term, _binding, _expanded) <-
        lowerResolvedPredicateChoice location keys arguments
    pure term

lowerResolvedPredicateChoice
    :: Location
    -> NonEmpty SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate (CanonicalTerm ObjectId, Maybe ResolvedGlobalBinding, Maybe CompiledBodySource)
lowerResolvedPredicateChoice location keys arguments = do
    case firstFixedMeaning (toList keys) of
        Just meaning ->
            maybe
                (impossible
                    "a fixed equality predicate has an invalid source arity")
                (\term -> pure (term, Nothing, Nothing))
                (lowerFixedEqualityPredicate meaning
                    (compiledSourceTermCore <$> arguments))
        Nothing -> do
            visible <- for (toList keys) \key -> do
                found <-
                    State.lift
                        (Trans.lift
                            (Declaration.resolveVisibleGlobalLowering key))
                pure ((\target -> (key, target)) <$> found)
            case catMaybes visible of
                [(key, (binding, _coreType))] -> do
                    (resolved, term, actual, expanded) <-
                        lowerResolvedSourceApplication
                            location key arguments
                    unless (actual == TyProp)
                        (Except.throwError
                            (ElaborationFormulaExpectedProposition location actual))
                    unless (resolvedBindingRef resolved == resolvedBindingRef binding)
                        (impossible
                            "predicate visibility changed during one elaboration")
                    pure (term, Just resolved, expanded)
                [] ->
                    Except.throwError
                        (ElaborationGlobalNotVisible location (NonEmpty.head keys))
                several ->
                    Except.throwError
                        (ElaborationAdjectiveReadingAmbiguous
                            location
                            (case NonEmpty.nonEmpty (fst <$> several) of
                                Just found -> found
                                Nothing ->
                                    impossible
                                        "ambiguous adjective has no readings"))
  where
    firstFixedMeaning =
        foldr
            (\key found -> fixedSemanticMeaning key <|> found)
            Nothing

compileGlobalNotionApplication
    :: Location
    -> (GlobalBindingRef -> GlobalNotionHead)
    -> SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate CompiledProposition
compileGlobalNotionApplication location notionHead key arguments = do
    let notionArguments = Vector.fromList arguments
    bindingArguments <- maybe
        (impossible "a global notion application has malformed arguments")
        pure
        (globalNotionBindingArguments key notionArguments)
    case fixedSemanticMeaning key of
        Just _meaning ->
            (`wholeCompiledOperands` arguments)
                <$> applyResolvedPredicate
                    location key (toList bindingArguments)
        Nothing -> do
            override <- State.gets (Map.lookup key . elaborationLocalGlobalDefinitions)
            case override of
                Just internal -> do
                    (term,actual) <- applyLocalGlobalDefinition location key internal
                        (compiledSourceTermArguments (toList bindingArguments))
                    unless (actual == TyProp)
                        (Except.throwError (ElaborationFormulaExpectedProposition location actual))
                    pure (case internal of
                        LocalRecursiveResults{} -> plainCompiledProposition term
                        _ -> wholeCompiledOperands term arguments)
                Nothing -> ordinary notionArguments bindingArguments
  where
    ordinary notionArguments bindingArguments = do
        (binding, term, actual, expanded) <-
            lowerResolvedSourceApplication
                location key (toList bindingArguments)
        unless (actual == TyProp)
            (Except.throwError
                (ElaborationFormulaExpectedProposition location actual))
        case expanded of
            Just (CompiledPropositionBody proposition) -> pure proposition
            Just CompiledTermBody{} -> impossible "a proposition abbreviation returned a term"
            Nothing -> pure (atomicCompiledProposition
                (globalSourceNotionAssertion (notionHead (resolvedBindingRef binding))
                    notionArguments term ConjunctionHere location))

-- | Lower an eligible written set-valued provider while retaining the exact
-- owner-bearing binding selected before transparent expansion.  Intrinsics,
-- contextual abbreviations, compiler overrides, and non-set results remain
-- ordinary provider-free source terms.
compileSourceGlobalApplication
    :: Location
    -> SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> SourceTermPresentation
    -> Elaborate CompiledSourceTerm
compileSourceGlobalApplication location key arguments presentation = do
    override <- State.gets
        (Map.lookup key . elaborationLocalGlobalDefinitions)
    case override of
        Just internal -> do
            (term, coreType) <-
                applyLocalGlobalDefinition
                    location key internal (compiledSourceTermArguments arguments)
            pure (SourceTerm.sourceTermOccurrence term coreType presentation)
        Nothing -> do
            (binding, term, coreType, expanded) <-
                lowerResolvedSourceApplication location key arguments
            case expanded of
                Just (CompiledTermBody source) -> pure source
                Just CompiledPropositionBody{} -> impossible "a set abbreviation returned a proposition"
                Nothing -> pure case (coreType, resolvedBindingSourceProviderHead binding) of
                    (TySet, Just (GlobalSourceProvider reference)) ->
                        globalProviderSourceTerm reference (Vector.fromList arguments) term presentation
                    (TySet, Just _) -> impossible "a global binding acquired a nonglobal provider"
                    _ -> SourceTerm.sourceTermOccurrence term coreType presentation

-- | Apply a global occurrence compiled through a compiler-owned elaboration
-- context.  An owner-local definition is the only alternative to visible
-- source resolution; ordinary source contexts contain no such definition.
applyContextualGlobalApplication
    :: Location
    -> SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
applyContextualGlobalApplication location key arguments = do
    override <- State.gets
        (Map.lookup key . elaborationLocalGlobalDefinitions)
    case override of
        Just internal ->
            applyLocalGlobalDefinition
                location key internal (compiledSourceTermArguments arguments)
        Nothing -> do
            (_binding, term, coreType, _expanded) <-
                lowerResolvedSourceApplication location key arguments
            pure (term, coreType)

lowerResolvedSourceApplication
    :: Location
    -> SemanticGlobalKey
    -> [CompiledSourceTerm]
    -> Elaborate
        ( ResolvedGlobalBinding
        , CanonicalTerm ObjectId
        , CoreType
        , Maybe CompiledBodySource
        )
lowerResolvedSourceApplication location key sourceTerms = do
    let arguments = compiledSourceTermArguments sourceTerms
    (binding, content) <-
        resolveVisibleSourceGlobalContent location key
    traverse_
        (dischargeFormationContract
            location
            binding
            (Vector.fromList sourceTerms))
        (resolvedBindingContract binding)
    case resolvedBindingExpansion binding of
        Just expansion -> do
            expanded <- instantiateBindingExpansion location binding content (Vector.fromList sourceTerms) expansion
            let (term, coreType) = case expanded of
                    CompiledTermBody source -> (compiledSourceTermCore source, TySet)
                    CompiledPropositionBody proposition -> (compiledPropositionCore proposition, TyProp)
            pure (binding, term, coreType, Just expanded)
        Nothing -> do
            let target = semanticGlobalBindingTarget (resolvedBindingDeclaration binding)
            (term, coreType) <- applyResolvedContent location key target content arguments
            pure (binding, term, coreType, Nothing)


-- One written application owns one allowance. Nested applications in an
-- abbreviation declaration draw from that declaration's remaining account.
withAbbreviationExpansion
    :: Location -> SemanticGlobalKey -> ExpansionWork Elaborate value -> Elaborate value
withAbbreviationExpansion location key action = do
    active <- State.gets elaborationExpansionAllowance
    calculation <- State.gets elaborationCalculationAllowance
    let allowance = min (fromMaybe formationMaximumExpansionWork active) (fromMaybe maxBound calculation)
        phase = if isJust active then FormationDiagnostics.DeclarationPreparation else FormationDiagnostics.Expansion
    (result, remaining) <- State.StateT \state -> Except.ExceptT $
        Declaration.withFormationPhaseLowering phase
            (Except.runExceptT (State.runStateT (runExpansionWork allowance (atExpansionPath "body" action)) state))
    let usedWork = allowance - remaining
    State.modify' (\state -> state
        { elaborationExpansionAllowance = subtract usedWork <$> active
        , elaborationCalculationAllowance = subtract usedWork <$> calculation })
    recorder <- State.lift (Trans.lift Declaration.formationRecorderLowering)
    let used = fromIntegral (allowance - remaining)
        total = fromIntegral (formationMaximumExpansionWork - remaining)
        rejected = case result of Left failure | Just amount <- expansionRejectedDebit failure -> [("expansion.rejected", amount)]; _ -> []
    liftIO (FormationDiagnostics.recordMeasurement recorder FormationDiagnostics.emptyMeasurement
        { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork phase used FormationDiagnostics.emptyDiagnostics
        , FormationDiagnostics.limitHighWater = Map.fromList
            ([("expansion.cap", fromIntegral formationMaximumExpansionWork), ("expansion.used", total)] <> rejected) })
    either (Except.throwError . ElaborationExpansionFailed location key) pure result

instantiateBindingExpansion
    :: Location -> ResolvedGlobalBinding -> ObjectContent -> Vector CompiledSourceTerm
    -> AbbreviationExpansion -> Elaborate CompiledBodySource
instantiateBindingExpansion location binding content arguments expansion = do
    receiver <- resolveBindingReceiver location binding
    instantiateBindingExpansionResolved location binding content arguments receiver expansion

resolveBindingReceiver :: Location -> ResolvedGlobalBinding -> Elaborate (Maybe CompiledSourceTerm)
resolveBindingReceiver location binding = case semanticGlobalBindingTarget (resolvedBindingDeclaration binding) of
    ContextualTransparentExpansion _ requirements -> Just <$> resolveContextualExpansionArgument
        location (globalBindingRefKey (resolvedBindingRef binding)) requirements
    _ -> pure Nothing

instantiateBindingExpansionResolved
    :: Location -> ResolvedGlobalBinding -> ObjectContent -> Vector CompiledSourceTerm
    -> Maybe CompiledSourceTerm -> AbbreviationExpansion -> Elaborate CompiledBodySource
instantiateBindingExpansionResolved location binding content arguments receiver expansion = do
    context <- currentSourceTermCheckingContext
    let actuals = maybe arguments (Vector.snoc arguments) receiver
        count = Vector.length actuals
        arity = Vector.length arguments
        layout = Vector.fromList (reverse (take arity [0..]) <> [fromIntegral arity | isJust receiver])
        body = case content of
            TransparentObjectContent _ _ term -> term
            _ -> impossible "an admitted abbreviation has opaque content"
    withAbbreviationExpansion location key do
        opened <- open count body
        providers <- resolveSourceTemplateProviders location expansion
        instantiated <- SourceTemplate.instantiateSourceTemplate context providers location
            (LocatedSourceTerm location) origin layout actuals opened expansion
        let core = case instantiated of
                SourceTemplate.InstantiatedTerm term -> compiledSourceTermCore term
                SourceTemplate.InstantiatedProposition proposition _ _ -> proposition
        globals <- expansionCoreWork (\work -> countedCanonicalGlobals work core)
        Trans.lift (State.lift (requireNotionQueryGlobals globals))
        case instantiated of
            SourceTemplate.InstantiatedTerm term -> do
                atExpansionPath "sealing" (void (boundedSeal location context term))
                pure (CompiledTermBody term)
            SourceTemplate.InstantiatedProposition proposition evidence equalities -> do
                let result = CompiledProposition proposition evidence equalities
                atExpansionPath "sealing" (void (sealCompiledPropositionWith (chargeExpansion 1) boundedCheck boundedSeal
                    (\a b -> expansionCoreWork (\work -> countedCanonicalIdentity work a b)) context location result))
                pure (CompiledPropositionBody result)
  where
    boundedCheck _ context expected term = do
        checked <- expansionCoreWork (\work -> countedCheckScopedCanonicalCore
            (SourceTerm.sourceTermGlobalTyping context) work (SourceTerm.sourceTermBinderTypes context) term)
        unless (scopedCoreType checked == expected)
            (Except.throwError (ExpansionInvalid "expanded occurrence has the wrong type"))
        pure checked
    boundedSeal _ context term = expansionCoreWork (\work ->
        SourceTerm.countedSealCanonicalSourceTermOccurrence work context term)
    key = globalBindingRefKey (resolvedBindingRef binding)
    spelling = renderWrittenGlobalApplication key (compiledSourceTermPresentation <$> arguments)
    origin path = spelling `seq` SourceEvidence.WrittenOrigin location (Just spelling) path
    open 0 body = pure body
    open count body = chargeExpansion 1 >> case body of
        CLam TySet rest -> open (count - 1) rest
        _ -> impossible "an admitted abbreviation lost its parameter telescope"

resolveSourceTemplateProviders
    :: Location -> AbbreviationExpansion -> ExpansionWork Elaborate (Map SourceProviderHead ObjectId)
resolveSourceTemplateProviders location expansion = do
    heads <- SourceTemplate.sourceTemplateProviders expansion
    entries <- for (Set.toAscList heads) \provider -> do
        chargeExpansion 1
        case provider of
            GlobalSourceProvider reference -> do
                (resolved, content) <- liftElaboration (resolveVisibleSourceGlobalContent location (globalBindingRefKey reference))
                unless (resolvedBindingRef resolved == reference && resolvedBindingSourceProviderHead resolved == Just provider)
                    (impossible "a source template lost its exact global provider")
                case semanticGlobalBindingTarget (resolvedBindingDeclaration resolved) of
                    GlobalReference identity -> do
                        liftElaboration (requireGlobalType identity (objectContentType content))
                        pure (Just (provider,identity))
                    _ -> impossible "a source template retains a transparent provider"
            StructureFieldSourceProvider identity projection -> do
                visible <- liftElaboration (State.lift (Trans.lift
                    (Declaration.resolveVisibleStructureFieldProviderLowering identity)))
                unless (visible == Just projection)
                    (impossible "a source template lost its exact field provider")
                liftElaboration (requireGlobalType projection (TyArrow TySet TySet))
                pure (Just (provider,projection))
            IntrinsicSourceProvider{} -> pure Nothing
            FiniteSetLiteralSourceProvider -> pure Nothing
    chargeExpansion (fromIntegral (length entries) * FormationTerms.indexWork (length entries) 1)
    pure (Map.fromList (catMaybes entries))
  where
    liftElaboration action = Trans.lift (State.lift action)

dischargeFormationContract
    :: Location
    -> ResolvedGlobalBinding
    -> Vector CompiledSourceTerm
    -> ResolvedFormationContract
    -> Elaborate ()
dischargeFormationContract location binding occurrenceArguments contract = do
    current <- State.get
    let requirements = resolvedFormationContractRequirements contract
        types = binderStackTypes (lexicalBinderStack (elaborationScope current))
        memoize = NonEmpty.length requirements > 1
    void $ withFormationWitnessArena \arena ->
        fst <$> finishFormationQuery FormationNotionQuery location (Just (fromIntegral (NonEmpty.length requirements)))
            (initialFormationSearchBudget defaultFormationSearchLimits)
            (State.evalStateT (do
            roots <- traverse (\case
                AtomicLeaf template -> AtomicLeaf <$> State.lift (instantiateFormationAtom location occurrenceArguments template)
                WholeLeaf template -> WholeLeaf <$> State.lift (instantiateFormationWhole location occurrenceArguments template)) requirements
            State.modify' (\state -> state {groupRoots = toList roots})
            leaves <- traverse (dischargeOne memoize) roots
            (forest, proposition) <- balanced (Vector.fromList (toList leaves))
            owned <- State.gets groupArena
            limits <- formationSearchBudgetLimits <$> State.lift State.get
            (selected, _) <- State.lift (withFormationSearchPhase FormationDiagnostics.Proof
                (runFormationConstruction recordFormationAllocation
                    (materializeFormationPremiseEvidence (chargeFormationWork location) limits forest) owned))
            evidence <- either (elaborate . Except.throwError . ElaborationFormationSearchFailed location) pure selected
            elaborate do
                replayed <- State.lift (Trans.lift (Declaration.replayTransientFormationLowering
                    (elaborationObjectClosure current) evidence proposition))
                either (Except.throwError . ElaborationFormationReplayFailed location) (const (pure ())) replayed)
            (initialFormationGroup FormationNotionQuery arena types))
  where
    elaborate :: Elaborate value -> FormationGroup scope value
    elaborate = State.lift . formationElaborate
    dischargeOne :: Bool -> FormationGroupRoot
        -> FormationGroup scope (FormationWitness scope FormationSourceOrigin, ScopedCheckedCore ObjectId)
    dischargeOne _ (WholeLeaf requested) = do
        found <- queryFormationGroupWhole location requested
        witness <- maybe (do
            statistics <- formationSearchBudgetStatistics <$> State.lift State.get
            elaborate (Except.throwError (ElaborationFormationRequirementMissing location
                (WholeFormationRequirementFailure binding (wholeGoalFormula requested) statistics)))) pure found
        pure (witness, wholeGoalFormula requested)
    dischargeOne memoize (AtomicLeaf sourceAtom) = do
        result <- queryFormationGroupLeaf memoize location sourceAtom
        witness <- case result of
            Right available -> pure available
            Left richFailure -> do
                finalBudget <- State.lift State.get
                names <- elaborate structureDiagnosticNames
                elaborate (Except.throwError (ElaborationFormationRequirementMissing location
                    FormationRequirementFailure
                        { formationRequirementStructureNames = names
                        , formationRequirementFailureBinding = binding
                        , formationRequirementFailureRequirement = compiledSourceTermPresentation <$> sourceAtom
                        , formationRequirementFailureExplanation = richFormationFailureExplanation richFailure
                        , formationRequirementFailureDetail = richFormationFailureDetail richFailure
                        , formationRequirementFailureSearchStatistics = formationSearchBudgetStatistics finalBudget
                        }))
        current <- elaborate State.get
        formula <- elaborate (deriveNotionAtomCore location (compiledSourceTermCore <$> sourceAtom))
        target <- State.lift (formationCoreWork location (\work -> countedCheckScopedCanonicalCore
            (elaborationGlobalTyping current) work (binderStackTypes (lexicalBinderStack (elaborationScope current))) formula))
        pure (witness, target)
    -- Contract entries have source order but no logical association. Balance
    -- their proof so a wide list does not create an artificial depth limit.
    balanced :: Vector (FormationWitness scope FormationSourceOrigin, ScopedCheckedCore ObjectId)
        -> FormationGroup scope (FormationPremiseEvidence scope FormationSourceOrigin, ScopedCheckedCore ObjectId)
    balanced leaves
        | Vector.length leaves == 1 = let (witness, target) = Vector.head leaves
            in pure (FormationPremiseEvidenceLeaf witness, target)
        | otherwise = do
            let (left, right) = Vector.splitAt (Vector.length leaves `div` 2) leaves
            (leftProof, leftTarget) <- balanced left
            (rightProof, rightTarget) <- balanced right
            target <- State.lift (formationCoreWork location (\work -> countedConjoinExactScopedCore work leftTarget rightTarget))
            pure (FormationPremiseEvidenceAnd leftProof rightProof, target)

-- | Instantiate one already materialized formation requirement.  This is an
-- internal semantic operation: provider applications are reconstructed from
-- their exact owner-bearing bindings and never re-enter source contract
-- checking.  Materialization has already proved every provider total,
-- noncontextual, set-valued, and uncontracted.
instantiateFormationAtom
    :: Location
    -> Vector CompiledSourceTerm
    -> NotionTemplate
    -> FormationQuery (AtomTemplate CompiledSourceTerm)
instantiateFormationAtom location occurrenceArguments =
    traverseAtomTemplateArguments (instantiateFormationTerm location occurrenceArguments)

instantiateFormationTerm
    :: Location -> Vector CompiledSourceTerm -> FormationTermTemplate -> FormationQuery CompiledSourceTerm
instantiateFormationTerm location occurrenceArguments = instantiateFormationSourceTerm location argument
  where
    argument (OccurrenceArgumentIx index) = maybe
        (impossible "a materialized formation contract has an invalid argument index") pure
        (occurrenceArguments Vector.!? fromIntegral index)

instantiateFormationSourceTerm
    :: Location -> (variable -> FormationQuery CompiledSourceTerm)
    -> SetTermTemplate variable -> FormationQuery CompiledSourceTerm
instantiateFormationSourceTerm location variable = instantiateTerm
  where
    charge = chargeFormationWork location
    instantiateTerm term = charge 1 >> case term of
        TemplateClosed value -> pure (SourceTerm.sourceTermOccurrence
            (closedSetValueTerm value) TySet (LocatedSourceTerm location))
        TemplateVariable value -> variable value
        TemplateProvider providerHead arguments -> do
            instantiatedArguments <- traverse instantiateTerm arguments
            charge (fromIntegral (Vector.length arguments) + 1)
            formationElaborate (sourceProviderOccurrence location providerHead instantiatedArguments)
        TemplateOrderedPair left right -> do
            left' <- instantiateTerm left
            right' <- instantiateTerm right
            charge 3
            let core = CApp
                    (CApp (CIntrinsic OrderedPair)
                        (compiledSourceTermCore left'))
                    (compiledSourceTermCore right')
            pure
                (fromMaybe
                    (impossible
                        "a materialized notion template has an ill-typed ordered pair")
                    (SourceTerm.sourceOrderedPairTermOccurrence
                        left' right' core (LocatedSourceTerm location)))

-- Checked goals retain their source structure for both supplied matching and
-- logical introduction. The description is never an assumption in this owner.
data WholeNotionGoal = WholeNotionGoal
    { wholeGoalFormula :: !(ScopedCheckedCore ObjectId)
    , wholeGoalEvidence :: !(SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence)
    }

instantiateFormationWhole
    :: Location -> Vector CompiledSourceTerm -> WholeTemplate FormationTermTemplate
    -> FormationQuery WholeNotionGoal
instantiateFormationWhole location arguments template = do
    current <- formationElaborate State.get
    let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
        check depth term = formationCoreWork location (\work -> countedCheckScopedCanonicalCore
            (elaborationGlobalTyping current) work (replicate (fromIntegral depth) TySet <> types) term)
        atom depth description = do
            source <- traverse (instantiateFormationSourceTerm location (operand depth)) description
            formula <- formationElaborate (deriveNotionAtomCore location (compiledSourceTermCore <$> source))
            checked <- check depth formula
            terms <- traverse (\term -> formationCoreWork location (\work ->
                SourceTerm.countedSealCanonicalSourceTermOccurrence work
                    (SourceTerm.SourceTermCheckingContext (elaborationGlobalTyping current)
                        (replicate (fromIntegral depth) TySet <> types)) term)) source
            pure (sourceNotionAssertionFromTemplate terms checked ConjunctionHere location)
        input depth = instantiateSupportPrefixWith (chargeFormationWork location 1)
            (fromIntegral (Vector.length arguments))
            (\nested index -> do
                source <- formationCoreWork location (\work -> SourceTerm.countedShiftCanonicalSourceTermOccurrence
                    work nested 0 (Vector.reverse arguments Vector.! fromIntegral index))
                pure (SourceTerm.sourceSupportTemplate id source, compiledSourceTermCore source)) depth
    case template of
        WholeResidual residual -> do
            formula <- formationCoreWork location (\work -> countedInstantiateCanonicalPrefix work
                (Vector.reverse (compiledSourceTermCore <$> arguments)) (residualTemplateFormula residual))
            evidence <- case residualTemplateEvidence residual of
                Nothing -> pure (SourceResidual Nothing)
                Just description -> SourceEvidence.traverseSourceAtDepth input
                    (\depth -> atom depth . fmap (fmap (residualOperand depth))) description
            WholeNotionGoal <$> check 0 formula <*> pure evidence
        WholeUniversal body -> do
            instantiated <- UniversalTemplate.traverseBodyAtDepth atom body
            let formula = SuppliedUniversal.universalFormula (scopedCoreTerm . sourceAssertionFormula <$> instantiated)
            evidence <- SourceEvidence.universalEvidenceWith (chargeFormationWork location 1) instantiated
            WholeNotionGoal <$> check 0 formula <*> pure evidence
  where
    residualOperand depth (ViewVariableIx index)
        | index < depth = SourceEvidence.UniversalBound (depth-index-1)
        | otherwise = SourceEvidence.UniversalOuter (TemplateVariable
            (OccurrenceArgumentIx (fromIntegral (Vector.length arguments) - (index-depth) - 1)))
    operand depth = \case
        SourceEvidence.UniversalBound index -> pure
            (locatedSetSourceTerm location (CBound (depth - index - 1)))
        SourceEvidence.UniversalOuter term -> do
            source <- instantiateFormationTerm location arguments term
            formationCoreWork location (\work -> SourceTerm.countedShiftCanonicalSourceTermOccurrence work depth 0 source)

-- | Rebuild a provider whose identity and application were checked at admission.
-- Contract templates separately reject contracted providers; abbreviation bodies
-- have already discharged their contracts in their declaration scope.
sourceProviderOccurrence
    :: Location -> SourceProviderHead -> Vector CompiledSourceTerm -> Elaborate CompiledSourceTerm
sourceProviderOccurrence location providerHead@(GlobalSourceProvider reference) arguments = do
    let key = globalBindingRefKey reference
    (resolved, content) <-
        resolveVisibleSourceGlobalContent location key
    unless
        ( resolvedBindingRef resolved == reference
          && resolvedBindingSourceProviderHead resolved
                == Just providerHead
        )
        (impossible
            "a materialized formation provider lost its exact binding")
    (term, coreType) <-
        applyResolvedContent
            location
            key
            (semanticGlobalBindingTarget
                (resolvedBindingDeclaration resolved))
            content
            (compiledSourceTermArguments (toList arguments))
    unless
        (coreType == TySet)
        (impossible
            "a materialized formation provider no longer returns a set")
    pure
        (globalProviderSourceTerm
            reference arguments term (LocatedSourceTerm location))
sourceProviderOccurrence location
        (StructureFieldSourceProvider identity projection)
        arguments = do
    visible <-
        State.lift
            (Trans.lift
                (Declaration.resolveVisibleStructureFieldProviderLowering
                    identity))
    unless
        (visible == Just projection)
        (impossible
            "a materialized formation field provider lost its exact projection")
    requireGlobalType projection (TyArrow TySet TySet)
    case toList arguments of
        [receiver] ->
            pure
                (structureFieldProviderSourceTerm
                    identity projection receiver (LocatedSourceTerm location))
        _ ->
            impossible
                "a materialized formation field provider has the wrong arity"
sourceProviderOccurrence location (IntrinsicSourceProvider provider) arguments =
    pure
        (intrinsicProviderSourceTerm
            provider arguments (LocatedSourceTerm location))
sourceProviderOccurrence location FiniteSetLiteralSourceProvider arguments =
    pure
        (finiteSetLiteralProviderSourceTerm
            (requiredMaterializedFiniteSetSpine arguments)
            (LocatedSourceTerm location))

-- | Run the bounded notion calculus for one exact source-preserved proof goal.
-- The goal is never added to the source scope. Successful evidence is
-- materialized but not replayed here; ordinary proof authorization owns the
-- retained replay.
elaborateProofNotionEvidence
    :: ElaborationContext
    -> Location
    -> ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either ElaborationError NotionQueryOutcome)
elaborateProofNotionEvidence context location assertion =
    fmap (fmap fst)
        (elaborateProofNotionEvidenceWithBudget
            (initialFormationSearchBudget defaultFormationSearchLimits)
            context location assertion)

-- | Internal budget-aware proof-notion query used by focused tests and
-- accounting-sensitive callers. Production proof checking uses the same group
-- path through 'prepareProofNotionEvidence', retaining completion until replay.
elaborateProofNotionEvidenceWithBudget
    :: FormationSearchBudget
    -> ElaborationContext
    -> Location
    -> ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either
            ElaborationError
            (NotionQueryOutcome, FormationSearchBudget))
elaborateProofNotionEvidenceWithBudget initialBudget context location assertion = do
    result <- prepareProofNotionEvidenceWithBudget initialBudget context location assertion
    recorder <- Declaration.formationRecorderLowering
    for result \(outcome, budget, completion) -> do
        liftIO (FormationDiagnostics.complete recorder completion)
        pure (outcome, budget)

-- Retain completion through the consumer's materialization and authorization.
-- Query-only atomic callers use this same spine/group path and close it early.
prepareProofNotionEvidence
    :: ElaborationContext -> Location -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either ElaborationError (NotionQueryOutcome, FormationDiagnostics.Completion))
prepareProofNotionEvidence context location goal evidence =
    fmap (fmap (\(outcome, _, completion) -> (outcome, completion)))
        (prepareProofNotionGoalWithBudget (initialFormationSearchBudget defaultFormationSearchLimits)
            context location goal evidence)

prepareProofNotionEvidenceWithBudget
    :: FormationSearchBudget -> ElaborationContext -> Location -> ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either ElaborationError (NotionQueryOutcome, FormationSearchBudget, FormationDiagnostics.Completion))
prepareProofNotionEvidenceWithBudget initialBudget context location assertion =
    prepareProofNotionGoalWithBudget initialBudget context location
        (sourceAssertionFormula assertion) (SourceAtom assertion)

prepareProofNotionGoalWithBudget
    :: FormationSearchBudget -> ElaborationContext -> Location -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either ElaborationError (NotionQueryOutcome, FormationSearchBudget, FormationDiagnostics.Completion))
prepareProofNotionGoalWithBudget initialBudget context location goal evidence = do
    attempted <- prepareProofNotionGoalAttemptWithBudget initialBudget context location goal evidence
    recorder <- Declaration.formationRecorderLowering
    case attempted of
        Right (Left failure, _, completion) -> liftIO (FormationDiagnostics.complete recorder completion) >> pure (Left failure)
        Right (Right outcome, balance, completion) -> pure (Right (outcome, balance, completion))
        Left failure -> pure (Left failure)

-- Optional consumers retain the actual debit even when a query exhausts.
-- They own completion of both successful and failed attempts; setup failures
-- remain ordinary elaboration errors, before a query account is opened.
prepareProofNotionGoalAttemptWithBudget
    :: FormationSearchBudget -> ElaborationContext -> Location -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> Declaration.LoweringDriver
        (Either ElaborationError
            (Either ElaborationError NotionQueryOutcome, FormationSearchBudget, FormationDiagnostics.Completion))
prepareProofNotionGoalAttemptWithBudget initialBudget context location goal evidence = Except.runExceptT do
    initial <- prepareInitialElaborationState context
    fst <$> State.runStateT query initial
  where
    query = withNotionQueryScope ProofNotionQuery $ withFormationWitnessArena \arena -> do
        types <- State.gets (binderStackTypes . lexicalBinderStack . elaborationScope)
        prepareFormationQueryAttempt ProofNotionQuery location Nothing initialBudget $
            State.evalStateT (do
                roots <- SourceEvidence.notionLeaves (State.lift (chargeFormationWork location 1))
                    (\_ _ -> pure ()) () goal evidence
                annotations <- SourceEvidence.sourceInputAnnotationsWith (State.lift (chargeFormationWork location 1)) evidence
                State.modify' (\state -> state {groupRoots = (sourceRoot <$> roots) <> annotationInputRoots goal annotations})
                result <- Except.runExceptT (queryFormationGroupGoal memoize location goal evidence)
                case result of
                    Left failure -> pure (NotionQueryUnavailable failure)
                    Right (forest, _) -> NotionQueryFound <$> groupConstruct location
                        (materializeFormationPremiseEvidence (chargeFormationWork location)
                            (formationSearchBudgetLimits initialBudget) forest))
                (initialFormationGroup ProofNotionQuery arena types)
    memoize = case sourceEvidenceBody evidence of SourceAtom{} -> False; _ -> True
    sourceRoot leaf = case SourceEvidence.sourceLeafDescription leaf of
        SourceEvidence.LeafAtom assertion -> AtomicLeaf
            (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion)
        _ -> WholeLeaf (WholeNotionGoal (SourceEvidence.sourceLeafFormula leaf) (SourceEvidence.sourceLeafEvidence leaf))
-- Only the outer evidence constructor controls inference capabilities.
-- The owning source retains and accounts for all additive operand views.
sourceEvidenceBody :: SourceEvidence term atom -> SourceEvidence term atom
sourceEvidenceBody (SourceWithInputs _ body) = sourceEvidenceBody body
sourceEvidenceBody evidence = evidence

-- An additive annotation belongs to the unsplit written proposition. Its
-- input-only root retains that ownership without granting a new atomic view.
annotationInputRoots
    :: ScopedCheckedCore ObjectId -> [SourceInput SupportTermTemplate] -> [FormationGroupRoot]
annotationInputRoots _ [] = []
annotationInputRoots formula inputs = [WholeLeaf (WholeNotionGoal formula (SourceInputs Nothing inputs))]

-- Root conjunctions share the prepared group and keep the direct-evidence
-- bypass. Whole leaves use the same scoped driver for every consumer policy.
queryFormationGroupGoal
    :: Bool -> Location -> ScopedCheckedCore ObjectId -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
    -> ExceptT NotionQueryFailure (FormationGroup scope)
        (FormationPremiseEvidence scope FormationSourceOrigin, Natural)
queryFormationGroupGoal memoize location = spine
  where
    spine
        :: ScopedCheckedCore ObjectId -> SourceEvidence SupportTermTemplate ScopedSourceNotionOccurrence
        -> ExceptT NotionQueryFailure (FormationGroup scope)
            (FormationPremiseEvidence scope FormationSourceOrigin, Natural)
    spine proposition expression = do
        Trans.lift (State.lift (chargeFormationWork location 1))
        case expression of
            SourceWithInputs _ body -> spine proposition body
            SourceAtom assertion -> do
                let requested = SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion
                result <- Trans.lift (queryFormationGroupLeaf memoize location requested)
                witness <- case result of
                    Right found -> pure found
                    Left failure -> do
                        statistics <- Trans.lift (State.lift (formationSearchBudgetStatistics <$> State.get))
                        names <- Trans.lift (State.lift (formationElaborate structureDiagnosticNames))
                        Except.throwError (NotionQueryFailure names (compiledSourceTermPresentation <$> requested)
                            (sourceNotionWrittenOrigin assertion)
                            failure statistics)
                pure (FormationPremiseEvidenceLeaf witness, 1 :: Natural)
            SourceAnd left right -> case splitScopedConjunction proposition of
                Just (a, b) -> do
                    (leftForest, leftCount) <- spine a left
                    (rightForest, rightCount) <- spine b right
                    pure (FormationPremiseEvidenceAnd leftForest rightForest, leftCount + rightCount)
                Nothing -> impossible "a proof notion conjunction lost its checked spine"
            SourceResidual{} | CTruth <- scopedCoreTerm proposition -> pure (FormationPremiseEvidenceTruth, 1)
            _ -> do
                found <- Trans.lift (queryFormationGroupWhole location (WholeNotionGoal proposition expression))
                witness <- case found of
                    Just value -> pure value
                    Nothing -> do
                        statistics <- Trans.lift (State.lift (formationSearchBudgetStatistics <$> State.get))
                        let origin = sourceEvidenceWrittenOrigin expression
                        Except.throwError (WholeNotionQueryFailure proposition origin statistics)
                pure (FormationPremiseEvidenceLeaf witness, 1)

requireNotionQueryGlobals :: Set ObjectId -> Elaborate ()
requireNotionQueryGlobals identities = do
    globalTyping <- State.gets elaborationGlobalTyping
    traverse_
        (\identity ->
            when
                (isNothing (lookupGlobalType globalTyping identity))
                (impossible
                    "a checked notion occurrence refers to an unavailable object"))
        (Set.toAscList identities)

data FormationDependency
    = ObservedFormationDependency !Natural
    | WholeFormationDependency !Natural !Natural
    | UniversalFormationDependency !Natural
    | AliasFormationDependency !Natural
    | EqualityFormationDependency !Natural
    deriving stock (Show, Eq, Ord)

data ScopedFormationProducer = ScopedFormationProducer
    !Int
    !ScopedSource.ScopedProjection
    | WholeFormationElimination !ScopedSource.ScopedProjection
    | ScopedFormationIntroduction !(Maybe Int) !ScopedSource.ScopedIntroduction

scopedProducerRule :: ScopedFormationProducer -> FormationRule.Rule
scopedProducerRule = \case
    ScopedFormationProducer _ projection -> ScopedSource.scopedProjectionRule projection
    WholeFormationElimination projection -> ScopedSource.scopedProjectionRule projection
    ScopedFormationIntroduction _ introduction -> ScopedSource.scopedIntroductionRule introduction

scopedProducerCaptures :: ScopedFormationProducer -> Map ViewVariableIx (SetTermTemplate FormationLeaves.OpaqueLeaf)
scopedProducerCaptures = \case
    ScopedFormationProducer _ projection -> ScopedSource.scopedProjectionCaptures projection
    WholeFormationElimination projection -> ScopedSource.scopedProjectionCaptures projection
    ScopedFormationIntroduction _ introduction -> ScopedSource.scopedIntroductionCaptures introduction

data FormationEqualityRuntime = FormationEqualityRuntime
    { runtimeEqualityGraph :: !FormationEqualityGraph
    , runtimeEqualityTerms :: ![SetTermTemplate FormationLeaves.OpaqueLeaf]
    }

-- Roots are sealed at the consumer's existing elaboration boundary. Search
-- realizes one domain and table lazily; direct-only groups never allocate it.
-- Proved siblings can share founded recipes but never become assumptions.
type FormationGroupRoot = NotionLeaf (AtomTemplate CompiledSourceTerm) WholeNotionGoal

-- Every recursive source node contributes both its exact Core and its written
-- construction to memo identity, independently of diagnostic presentation.
data FormationGoalNode
    = FormationOpaqueGoal !FormationLeaves.OpaqueLeaf
    | FormationProviderGoal !FormationLeaves.OpaqueLeaf !SourceProviderHead !(Vector Int)
    | FormationPairGoal !FormationLeaves.OpaqueLeaf !Int !Int
    deriving stock (Eq, Ord)

data FormationGroupState scope = FormationGroupState
    { groupConsumer :: !NotionQueryConsumer
    , groupArena :: !(FormationWitnessArena scope FormationSourceOrigin)
    , groupLeaves :: !FormationLeaves.OpaqueLeaves
    , groupTerms :: !(Map FormationGoalNode Int)
    , groupAnswers :: !(Map (AtomTemplate Int) (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin))
    , groupFormulas :: !(Maybe FormationFormulas.Formulas)
    , groupWholeAnswers :: !(Map FormationFormulas.FormulaId (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin))
    , groupRoots :: ![FormationGroupRoot]
    , groupSearch :: !(Maybe (RegisteredFormationState scope))
    }

initialFormationGroup
    :: NotionQueryConsumer -> FormationWitnessArena scope FormationSourceOrigin
    -> [CoreType] -> FormationGroupState scope
initialFormationGroup consumer arena types = FormationGroupState consumer arena
    (FormationLeaves.emptyOpaqueLeaves types) Map.empty Map.empty Nothing Map.empty [] Nothing

-- Keep the work account outside failure rollback. Lexical state still rolls
-- back through Elaborate, while completion can observe every accepted debit.
type FormationQuery = ExceptT ElaborationError (StateT FormationSearchBudget Elaborate)

formationElaborate :: Elaborate value -> FormationQuery value
formationElaborate action = Except.ExceptT (State.lift
    (Except.catchError (Right <$> action) (pure . Left)))

formationRecorder :: Elaborate FormationDiagnostics.Recorder
formationRecorder = State.lift (Trans.lift Declaration.formationRecorderLowering)

withFormationPhase :: FormationDiagnostics.Phase -> Elaborate value -> Elaborate value
withFormationPhase phase action = State.StateT $ \initial -> Except.ExceptT $
    Declaration.withFormationPhaseLowering phase (Except.runExceptT (State.runStateT action initial))

withFormationMeasurement :: Elaborate value -> Elaborate (value, FormationDiagnostics.Measurement)
withFormationMeasurement action = State.StateT $ \initial -> Except.ExceptT do
    recorder <- Declaration.formationRecorderLowering
    (result, measured) <- FormationDiagnostics.captureMeasurement recorder
        (Except.runExceptT (State.runStateT action initial))
    pure (fmap (\(value, final) -> ((value, measured), final)) result)

finishFormationQuery
    :: NotionQueryConsumer -> Location -> Maybe Natural
    -> FormationSearchBudget -> FormationQuery value -> Elaborate (value, FormationSearchBudget)
finishFormationQuery consumer location leaves initial action = do
    (value, budget, completion) <- prepareFormationQuery consumer location leaves initial action
    recorder <- formationRecorder
    liftIO (FormationDiagnostics.complete recorder completion)
    pure (value, budget)

prepareFormationQuery
    :: NotionQueryConsumer -> Location -> Maybe Natural
    -> FormationSearchBudget -> FormationQuery value
    -> Elaborate (value, FormationSearchBudget, FormationDiagnostics.Completion)
prepareFormationQuery consumer location leaves initial action = do
    (result, balance, completion) <- prepareFormationQueryAttempt consumer location leaves initial action
    case result of
        Left failure -> do
            recorder <- formationRecorder
            liftIO (FormationDiagnostics.complete recorder completion)
            Except.throwError failure
        Right value -> pure (value, balance, completion)

prepareFormationQueryAttempt
    :: NotionQueryConsumer -> Location -> Maybe Natural
    -> FormationSearchBudget -> FormationQuery value
    -> Elaborate (Either ElaborationError value, FormationSearchBudget, FormationDiagnostics.Completion)
prepareFormationQueryAttempt consumer location leaves initial action = do
    recorder <- formationRecorder
    ((result, finalBudget, delta, outcome, rejected), physical) <- withFormationMeasurement do
        (result, final) <- withFormationPhase FormationDiagnostics.Query
            (State.runStateT (Except.runExceptT action) initial)
        let attempted = Map.findWithDefault 0 FormationDiagnostics.LeafSearch
                (FormationDiagnostics.operationCounts (formationSearchBudgetDiagnostics final))
                + Map.findWithDefault 0 FormationDiagnostics.ReusedLeaf
                    (FormationDiagnostics.operationCounts (formationSearchBudgetDiagnostics final))
            completedLeaves = sum (FormationDiagnostics.outcomeCounts (formationSearchBudgetDiagnostics final))
            finalBudget = case result of
                Left (ElaborationFormationSearchFailed _ _) | attempted > completedLeaves ->
                    recordFormationOutcome FormationDiagnostics.Exhausted final
                _ -> final
            delta = FormationDiagnostics.subtractDiagnostics
                (formationSearchBudgetDiagnostics finalBudget) (formationSearchBudgetDiagnostics initial)
            measured = (formationSearchBudgetMeasurement finalBudget)
                { FormationDiagnostics.measuredDiagnostics = delta }
            outcome = case result of
                Left (ElaborationFormationSearchFailed _ _) -> "exhausted"
                Left _ -> "failed"
                Right _ | Map.member FormationDiagnostics.CompletedFailure (FormationDiagnostics.outcomeCounts delta) -> "failed"
                        | otherwise -> "success"
            rejected = maybe [] (\debit -> [("rejected-work", Text.pack (show (formationSearchInferenceInspections debit)))])
                (formationSearchRejectedDebit finalBudget)
        liftIO (FormationDiagnostics.recordMeasurement recorder measured)
        pure (result, finalBudget, delta, outcome, rejected)
    let owns phase _ = phase == FormationDiagnostics.Query || phase == FormationDiagnostics.Proof
        physicalCounts = FormationDiagnostics.measuredDiagnostics physical
        completed = physical
            { FormationDiagnostics.phaseNanoseconds = Map.filterWithKey owns (FormationDiagnostics.phaseNanoseconds physical)
            , FormationDiagnostics.measuredDiagnostics = physicalCounts
                { FormationDiagnostics.phaseInspections = Map.filterWithKey owns (FormationDiagnostics.phaseInspections physicalCounts)
                , FormationDiagnostics.coreInspections = Map.filterWithKey owns (FormationDiagnostics.coreInspections physicalCounts) } }
    let completion = FormationDiagnostics.Completion (Text.pack (show consumer)) (locationToText location)
            (fromMaybe
                (Map.findWithDefault 0 FormationDiagnostics.LeafSearch (FormationDiagnostics.operationCounts delta)
                    + Map.findWithDefault 0 FormationDiagnostics.ReusedLeaf (FormationDiagnostics.operationCounts delta)) leaves)
            (if FormationDiagnostics.hasRejectedDebit physical then "exhausted" else outcome) completed rejected
    pure (result, finalBudget, completion)

withFormationSearchPhase :: FormationDiagnostics.Phase -> FormationQuery value -> FormationQuery value
withFormationSearchPhase phase action = Except.ExceptT $ State.StateT $ \initial -> do
    (result, final) <- withFormationPhase phase (State.runStateT (Except.runExceptT action)
        (setFormationSearchPhase phase initial))
    pure (result, setFormationSearchPhase (formationSearchBudgetPhase initial) final)

type FormationGroup scope = StateT (FormationGroupState scope) FormationQuery

groupConstruct
    :: Location -> FormationConstruction scope FormationSourceOrigin FormationQuery value
    -> FormationGroup scope value
groupConstruct location action = do
    arena <- State.gets groupArena
    (result, next) <- State.lift (withFormationSearchPhase FormationDiagnostics.Proof
        (runFormationConstruction recordFormationAllocation action arena))
    State.modify' (\state -> state {groupArena = next})
    either (State.lift . Except.throwError . ElaborationFormationSearchFailed location) pure result

formationFormulaWork
    :: Location -> (Word -> (Either FormationFormulas.FormulaFailure value, Word))
    -> FormationQuery value
formationFormulaWork location operation = do
    available <- availableFormationWork
    let (result, remaining) = operation available
    chargeFormationWork location (fromIntegral (available - remaining))
    case result of
        Right value -> pure value
        Left (FormationFormulas.FormulaWorkExhausted debit) ->
            chargeFormationWork location debit >> impossible "exhausted formula work was admitted"
        Left _ -> impossible "a checked whole proposition lost its nominal scope or type"

queryFormationGroupWhole
    :: forall scope. Location -> WholeNotionGoal
    -> FormationGroup scope (Maybe (FormationWitness scope FormationSourceOrigin))
queryFormationGroupWhole location requestedGoal = do
    current <- State.lift (formationElaborate State.get)
    let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
        index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
    consumer <- State.gets groupConsumer
    known <- State.gets groupFormulas
    formulas <- case known of
        Just table -> pure table
        Nothing -> formulaWork (\work -> FormationFormulas.extendFormulas work types (evidenceFormulas index))
    (identifier, extended) <- formulaWork (\work -> FormationFormulas.internFormula work requested formulas)
    State.modify' (\state -> state {groupFormulas = Just extended})
    answers <- State.gets groupWholeAnswers
    charge (FormationTerms.indexWork (Map.size answers) 1)
    case Map.lookup identifier answers of
        Just (outcome,witness) -> do
            record consumer outcome True
            pure (Just witness)
        Nothing -> do
            result <- queryRegisteredGroupLeaf location (WholeLeaf requestedGoal)
            let found = either (const Nothing) Just result
            for_ found \answer -> do
                charge (FormationTerms.indexWork (Map.size answers) 1)
                State.modify' (\state -> state {groupWholeAnswers = Map.insert identifier answer answers})
            pure (snd <$> found)
  where
    requested = wholeGoalFormula requestedGoal
    charge = State.lift . chargeFormationWork location
    formulaWork
        :: (Word -> (Either FormationFormulas.FormulaFailure value, Word))
        -> FormationGroup scope value
    formulaWork operation = State.lift (formationFormulaWork location operation)
    record consumer outcome reused = do
        State.lift (State.modify' (recordFormationOutcome outcome .
            if reused then recordFormationOperation FormationDiagnostics.ReusedLeaf 1 else id))
        recorder <- State.lift (formationElaborate formationRecorder)
        liftIO (FormationDiagnostics.recordWholeLeaf recorder (Text.pack (show consumer)) (locationToText location)
            (Text.pack (show (scopedCoreTerm requested))) outcome reused)

queryFormationGroupLeaf
    :: forall scope. Bool -> Location -> AtomTemplate CompiledSourceTerm
    -> FormationGroup scope (Either RichFormationFailure (FormationWitness scope FormationSourceOrigin))
queryFormationGroupLeaf memoize location requested = do
    consumer <- State.gets groupConsumer
    key <- if memoize then Just <$> goalKey else pure Nothing
    answers <- State.gets groupAnswers
    for_ key (const (charge (FormationTerms.indexWork (Map.size answers) 1)))
    case key >>= (`Map.lookup` answers) of
        Just (outcome, evidence) -> do
            State.lift (State.modify' (recordFormationOutcome outcome . recordFormationOperation FormationDiagnostics.ReusedLeaf 1))
            State.lift (recordAtomicFormationLeaf consumer location requested outcome True)
            pure (Right evidence)
        Nothing -> do
            result <- queryRegisteredGroupLeaf location (AtomicLeaf requested)
            for_ ((,) <$> key <*> either (const Nothing) Just result) \(selected, evidence) -> do
                charge (FormationTerms.indexWork (Map.size answers) 1)
                State.modify' (\state -> state {groupAnswers = Map.insert selected evidence answers})
            pure (snd <$> result)
  where
    charge = State.lift . chargeFormationWork location
    core operation = State.lift (formationCoreWork location operation)
    goalKey = do
        current <- State.lift (formationElaborate State.get)
        traverseAtomTemplateArguments (termKey current) requested
    termKey current occurrence = do
        charge 1
        let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
        checked <- core (\work -> countedCheckScopedCanonicalCore
            (elaborationGlobalTyping current) work types (compiledSourceTermCore occurrence))
        leaves <- State.gets groupLeaves
        allowance <- State.lift availableFormationWork
        let (result, remaining) = FormationLeaves.internOpaqueLeaf allowance checked leaves
        charge (fromIntegral (allowance - remaining))
        identifier <- case result of
            Right (identifier, next) -> State.modify' (\state -> state {groupLeaves = next}) >> pure identifier
            Left FormationLeaves.OpaqueLeafWorkExhausted -> charge 1 >> impossible "exhausted group key work was admitted"
            Left _ -> impossible "a checked group goal lost its scope or type"
        node <- case SourceTerm.sourceTermOccurrenceProvider occurrence of
            Just provider -> FormationProviderGoal identifier (SourceTerm.sourceTermProviderHead provider)
                <$> traverse (termKey current) (SourceTerm.sourceTermProviderArguments provider)
            Nothing -> case SourceTerm.sourceTermOccurrenceOrderedPair occurrence of
                Just (left, right) -> FormationPairGoal identifier <$> termKey current left <*> termKey current right
                Nothing -> pure (FormationOpaqueGoal identifier)
        terms <- State.gets groupTerms
        let width = case node of FormationProviderGoal _ _ arguments -> 2 + Vector.length arguments; _ -> 3
        charge (2 * FormationTerms.indexWork (Map.size terms) (fromIntegral width))
        case Map.lookup node terms of
            Just key -> pure key
            Nothing -> do
                let key = Map.size terms
                State.modify' (\state -> state {groupTerms = Map.insert node key terms})
                pure key

queryRegisteredGroupLeaf
    :: Location -> FormationGroupRoot
    -> FormationGroup scope (Either RichFormationFailure (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin))
queryRegisteredGroupLeaf location requested = do
    group <- State.get
    (result,next) <- State.lift (queryRegisteredLeafState (groupArena group) (groupSearch group)
        (groupRoots group) (groupConsumer group) location requested)
    State.modify' (\state -> state {groupArena = registeredArena next, groupSearch = Just next})
    pure result

type FormationRuleSession scope = FormationEvaluation.RuleSession (RegisteredFormationSearch scope)
    FormationLeaves.OpaqueLeaf (AtomTemplate FormationLeaves.OpaqueLeaf) Int
    (Set FormationDependency, FormationWitness scope FormationSourceOrigin)

-- A group fixes its consumer, scope, source catalogue and complete ordered
-- roots. Keep selection independently of the session: initial closure can
-- answer a leaf before there is a running session to retain it.
data PreparedFormationSelection = PreparedFormationSelection
    { selectedFormationCatalog :: !ScopedFormationCatalog
    , selectedFormationSnapshot :: !FormationRule.RuleSnapshot
    , selectedFormationProducers :: !(Seq ScopedFormationProducer)
    , selectedFormationRoots :: ![NotionLeaf
        (AtomTemplate (SetTermTemplate FormationLeaves.OpaqueLeaf))
        (FormationRequest.WholeRequest FormationLeaves.OpaqueLeaf)]
    , selectedFormationHeads :: ![FormationRule.RuleHead]
    }

data RegisteredFormationState scope = RegisteredFormationState
    { registeredLeaves :: !FormationLeaves.OpaqueLeaves
    , registeredTerms :: !(FormationTerms.Nodes FormationLeaves.OpaqueLeaf)
    , registeredTermValues :: !(Map Int FormationLeaves.OpaqueLeaf)
    , registeredAnswers :: !(Map (NotionLeaf (AtomTemplate Int) FormationFormulas.FormulaId, Bool) Int)
    , registeredFormulas :: !(Maybe FormationFormulas.Formulas)
    , registeredFormulaTemplates :: !(Map (Natural,Maybe Natural) (FormationFormulas.FormulaTemplateId,Set ViewVariableIx))
    , registeredWholeRequests :: !(Map (Natural,Maybe Natural,[(ViewVariableIx,Int)]) (FormationRequest.WholeRequest FormationLeaves.OpaqueLeaf))
    , registeredWholeHypotheses :: !(Map Natural (FormationHypothesisReference scope FormationSourceOrigin))
    , registeredEqualities :: !(Maybe FormationEqualityRuntime)
    , registeredArena :: !(FormationWitnessArena scope FormationSourceOrigin)
    , registeredHypotheses :: !(Map Natural (FormationHypothesisReference scope FormationSourceOrigin))
    , registeredWitnesses :: !(Map Int (Set FormationDependency, FormationWitness scope FormationSourceOrigin))
    , registeredOutcome :: !FormationDiagnostics.Outcome
    , registeredSelection :: !(Maybe PreparedFormationSelection)
    , registeredSession :: !(Maybe (FormationRuleSession scope))
    , registeredSearchObservations :: ![FormationObservation]
    , registeredWholeGoals :: !(Map FormationFormulas.FormulaId
        (WholeNotionGoal, FormationGoal.GoalPlan ObjectId SupportTermTemplate ScopedSourceNotionOccurrence))
    , registeredIntroduced :: !(Set FormationFormulas.FormulaId)
    , registeredIntroductions :: !(IntroductionQueue scope)
    }

-- Waiting means only same-owner subscriptions remain. A child consumes its
-- creator's turn; it never joins the parent's queue as an independent worker.
data IntroductionStep scope
    = IntroductionComplete
    | IntroductionRunnable !(RegisteredFormationSearch scope (IntroductionStep scope))
    | IntroductionWaiting !(RegisteredFormationSearch scope (IntroductionStep scope))

data IntroductionQueue scope = IntroductionQueue
    { introductionAlternatives :: !(Seq (RegisteredFormationSearch scope (IntroductionStep scope)))
    , introductionTurn :: !Bool
    , introductionWaitingCount :: !Int
    }

emptyIntroductionQueue :: IntroductionQueue scope
emptyIntroductionQueue = IntroductionQueue Seq.empty False 0

enqueueIntroduction
    :: RegisteredFormationSearch scope (IntroductionStep scope)
    -> IntroductionQueue scope -> IntroductionQueue scope
enqueueIntroduction action queue = queue
    { introductionAlternatives = introductionAlternatives queue Seq.|> action
    , introductionWaitingCount = 0 }

-- A completed miss needs relational quiescence and a full pass of local
-- waiters. Children are runnable even when their last quantum found no answer.
-- Advancing the relation, completing work or enqueueing an alternative makes
-- an earlier waiting pass stale; those transitions reset this count.
introductionsSettled :: IntroductionQueue scope -> Bool
introductionsSettled queue = introductionWaitingCount queue >= Seq.length (introductionAlternatives queue)

resumeIntroduction :: IntroductionStep scope -> IntroductionQueue scope -> IntroductionQueue scope
resumeIntroduction step queue = case step of
    IntroductionComplete -> queue {introductionWaitingCount = 0}
    IntroductionRunnable next -> enqueueIntroduction next queue
    IntroductionWaiting next -> queue
        { introductionAlternatives = introductionAlternatives queue Seq.|> next
        , introductionWaitingCount = introductionWaitingCount queue + 1 }

type RegisteredFormationSearch scope = StateT (RegisteredFormationState scope) FormationQuery

formationCost :: Location -> Text -> Elaborate ()
formationCost location detail = do
    recorder <- formationRecorder
    liftIO (FormationDiagnostics.event recorder (locationToText location) detail)

consumeFormationStatistics :: Location -> FormationSearchStatistics -> FormationQuery ()
consumeFormationStatistics location statistics = do
    budget <- State.get
    case consumeFormationSearchStatistics statistics budget of
        Left failure -> do
            State.modify' (recordFormationRejectedDebit statistics)
            Except.throwError (ElaborationFormationSearchFailed location failure)
        Right next -> State.put next

recordAtomicFormationLeaf
    :: NotionQueryConsumer -> Location -> AtomTemplate CompiledSourceTerm
    -> FormationDiagnostics.Outcome -> Bool -> FormationQuery ()
recordAtomicFormationLeaf consumer location requested outcome reused = do
    recorder <- formationElaborate formationRecorder
    liftIO (FormationDiagnostics.recordLeaf recorder (Text.pack (show consumer)) (locationToText location)
        (Text.pack (show (compiledSourceTermCore <$> requested))) outcome reused)

recordFormationAllocation :: Bool -> FormationQuery ()
recordFormationAllocation projection = State.modify'
    (recordFormationOperation FormationDiagnostics.ProofNode 1 .
        (if projection then recordFormationOperation FormationDiagnostics.ProjectionNode 1 else id))

chargeFormationWork :: Location -> Natural -> FormationQuery ()
chargeFormationWork location amount = consumeFormationStatistics location emptyFormationSearchStatistics
    {formationSearchViewInspections = amount}

availableFormationWork :: FormationQuery Word
availableFormationWork = fromIntegral . min (fromIntegral (maxBound :: Word))
    . formationInferenceWorkRemaining <$> State.get

formationCoreResult
    :: Location -> Word -> (Either (CountedCoreFailure failure) value, Word)
    -> FormationQuery value
formationCoreResult location allowance (result, remaining) = do
    let work = fromIntegral (allowance - remaining)
    State.modify' (recordFormationCoreWork work)
    chargeFormationWork location work
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted ->
            chargeFormationWork location 1 >> impossible "exhausted formation work was admitted"
        Left (CountedCoreOperationFailed _) -> impossible "a checked formation source lost its scope or type"

formationCoreWork
    :: Location -> (Word -> (Either (CountedCoreFailure failure) value, Word))
    -> FormationQuery value
formationCoreWork location operation = do
    allowance <- availableFormationWork
    formationCoreResult location allowance (operation allowance)

-- Registrations execute through one finite evaluator. Its query-local state
-- retains source occurrence eligibility separately from the checked witnesses.
-- Alias normalization and exact equality transport preserve checked witnesses.
queryRegisteredFormation
    :: NotionQueryConsumer -> Location -> AtomTemplate CompiledSourceTerm
    -> FormationQuery (Either RichFormationFailure (FormationEvidence FormationSourceOrigin))
queryRegisteredFormation consumer location requested = withFormationWitnessArena \arena -> do
    (result, next) <- queryRegisteredFormationIn arena consumer location requested
    for result \(_, witness) -> do
        limits <- formationSearchBudgetLimits <$> State.get
        (selected, _) <- withFormationSearchPhase FormationDiagnostics.Proof
            (runFormationConstruction recordFormationAllocation
                (selectFormationEvidence (chargeFormationWork location) limits witness) next)
        either (Except.throwError . ElaborationFormationSearchFailed location) pure selected

queryRegisteredFormationIn
    :: forall scope. FormationWitnessArena scope FormationSourceOrigin
    -> NotionQueryConsumer -> Location -> AtomTemplate CompiledSourceTerm
    -> FormationQuery
        (Either RichFormationFailure (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin), FormationWitnessArena scope FormationSourceOrigin)
queryRegisteredFormationIn initialArena consumer location requested =
    queryRegisteredLeafIn initialArena consumer location (AtomicLeaf requested)

queryRegisteredLeafIn
    :: forall scope. FormationWitnessArena scope FormationSourceOrigin
    -> NotionQueryConsumer -> Location
    -> NotionLeaf (AtomTemplate CompiledSourceTerm) WholeNotionGoal
    -> FormationQuery
        (Either RichFormationFailure (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin), FormationWitnessArena scope FormationSourceOrigin)
queryRegisteredLeafIn initialArena consumer location requestedLeaf = do
    (result,final) <- queryRegisteredLeafState initialArena Nothing [requestedLeaf] consumer location requestedLeaf
    pure (result,registeredArena final)

queryRegisteredLeafState
    :: forall scope. FormationWitnessArena scope FormationSourceOrigin
    -> Maybe (RegisteredFormationState scope) -> [FormationGroupRoot]
    -> NotionQueryConsumer -> Location -> FormationGroupRoot
    -> FormationQuery
        (Either RichFormationFailure (FormationDiagnostics.Outcome, FormationWitness scope FormationSourceOrigin), RegisteredFormationState scope)
queryRegisteredLeafState initialArena prior roots consumer location requestedLeaf = do
    (step, initial) <- startRegisteredLeafState initialArena prior roots [] consumer location requestedLeaf
    (result, final) <- drain step initial
    let outcome = either (const FormationDiagnostics.CompletedFailure) (const (registeredOutcome final)) result
    State.modify' (recordFormationOutcome outcome)
    case requestedLeaf of
        AtomicLeaf requested -> recordAtomicFormationLeaf consumer location requested outcome False
        WholeLeaf requested -> do
            recorder <- formationElaborate formationRecorder
            liftIO (FormationDiagnostics.recordWholeLeaf recorder (Text.pack (show consumer)) (locationToText location)
                (Text.pack (show (scopedCoreTerm (wholeGoalFormula requested)))) outcome False)
    pure ((\witness -> (outcome, witness)) <$> result, final)
  where
    drain (RegisteredFinished result) state = pure (result,state)
    drain (RegisteredPending action) state = do
        (next,updated) <- State.runStateT action state
        drain next updated

-- One continuation advances the same owner by one bounded clause quantum.
-- A scoped goal driver can interleave these continuations with child owners;
-- no pending table is mistaken for a completed miss.
data RegisteredQueryStep scope
    = RegisteredFinished !(Either RichFormationFailure (FormationWitness scope FormationSourceOrigin))
    | RegisteredPending !(RegisteredFormationSearch scope (RegisteredQueryStep scope))

startRegisteredLeafState
    :: forall scope. FormationWitnessArena scope FormationSourceOrigin
    -> Maybe (RegisteredFormationState scope) -> [FormationGroupRoot] -> [CompiledSourceTerm]
    -> NotionQueryConsumer -> Location -> FormationGroupRoot
    -> FormationQuery (RegisteredQueryStep scope, RegisteredFormationState scope)
startRegisteredLeafState initialArena prior groupRoots' groupSeeds consumer location requestedLeaf = do
    current <- formationElaborate State.get
    State.modify' (recordFormationOperation FormationDiagnostics.LeafSearch 1)
    let context = binderStackTypes (lexicalBinderStack (elaborationScope current))
        initial = fromMaybe RegisteredFormationState
            { registeredLeaves = FormationLeaves.emptyOpaqueLeaves context
            , registeredTerms = FormationTerms.emptyNodes
            , registeredTermValues = Map.empty
            , registeredAnswers = Map.empty
            , registeredFormulas = Nothing
            , registeredFormulaTemplates = Map.empty
            , registeredWholeRequests = Map.empty
            , registeredWholeHypotheses = Map.empty
            , registeredEqualities = Nothing
            , registeredArena = initialArena
            , registeredHypotheses = Map.empty
            , registeredWitnesses = Map.empty
            , registeredOutcome = FormationDiagnostics.ExactDirect
            , registeredSelection = Nothing
            , registeredSession = Nothing
            , registeredSearchObservations = []
            , registeredWholeGoals = Map.empty
            , registeredIntroduced = Set.empty
            , registeredIntroductions = emptyIntroductionQueue
            } prior
    (step, final) <- State.runStateT (evaluate current)
        initial {registeredArena = initialArena, registeredOutcome = FormationDiagnostics.ExactDirect}
    pure (step,final)
  where
    consume = consumeFormationStatistics location
    charge amount = State.lift (consume emptyFormationSearchStatistics
        {formationSearchViewInspections = amount})
    elaborate = State.lift . formationElaborate
    report stage = do
        used <- formationSearchInferenceInspections . formationSearchBudgetStatistics <$> State.lift State.get
        elaborate (formationCost location (stage <> " work=" <> Text.pack (show used)))
    -- Bound traversal as well as output: taking a prefix of Show's lazy list
    -- must precede packing it into strict Text.
    summary value = Text.pack (take 768 (show value))
    checked :: Either FormationSearchError value -> RegisteredFormationSearch scope value
    checked result = either
        (elaborate . Except.throwError . ElaborationFormationSearchFailed location) pure result
    construct :: FormationConstruction scope FormationSourceOrigin (RegisteredFormationSearch scope) value
        -> RegisteredFormationSearch scope value
    construct action = do
        arena <- State.gets registeredArena
        (result, next) <- runFormationConstruction (State.lift . recordFormationAllocation) action arena
        State.modify' (\state -> state {registeredArena = next})
        checked result
    -- Dependency sets describe the selected proof; they are not alternative
    -- answer identities. Retain them with the immutable, first founded witness.
    retainWitness key dependencies build = do
        known <- State.gets registeredWitnesses
        charge (FormationTerms.indexWork (Map.size known) 1)
        case Map.lookup key known of
            Just witness -> pure witness
            Nothing -> do
                witness <- (,) dependencies <$> build
                charge (FormationTerms.indexWork (Map.size known) 1)
                State.modify' (\state -> state {registeredWitnesses = Map.insert key witness known})
                pure witness
    available = State.lift availableFormationWork
    coreResult :: Word -> (Either (CountedCoreFailure failure) value, Word)
        -> RegisteredFormationSearch scope value
    coreResult allowance = State.lift . formationCoreResult location allowance
    core :: (Word -> (Either (CountedCoreFailure failure) value, Word))
        -> RegisteredFormationSearch scope value
    core = State.lift . formationCoreWork location
    scopedLeaves :: (Word -> (Either FormationLeaves.OpaqueLeafFailure value, Word))
        -> RegisteredFormationSearch scope value
    scopedLeaves operation = do
        allowance <- available
        let (result, remaining) = operation allowance
        charge (fromIntegral (allowance - remaining))
        case result of
            Right value -> pure value
            Left FormationLeaves.OpaqueLeafWorkExhausted ->
                charge 1 >> impossible "exhausted scope-key work was admitted"
            Left _ -> impossible "an admitted scope index lost its binder context"
    indexedObservation current (Down batchEnd, offset) (observation, path) = do
        let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
            align scoped = core (\work -> countedAlignScopedCore work types scoped)
                >>= maybe (impossible "an indexed observation escaped its scope") pure
            alignTerm occurrence = core (\work ->
                SourceTerm.countedAlignScopedSourceTermOccurrence work types occurrence)
                >>= maybe (impossible "an indexed source term escaped its scope") pure
        roots <- State.gets registeredHypotheses
        charge (FormationTerms.indexWork (Map.size roots) 1)
        root <- case Map.lookup batchEnd roots of
            Just reference -> pure reference
            Nothing -> do
                parent <- align (formationObservationSource observation)
                reference <- construct (prepareFormationHypothesis charge parent (formationObservationOrigin observation))
                State.modify' (\state -> state {registeredHypotheses = Map.insert batchEnd reference roots})
                pure reference
        assertion <- traverseSourceNotionAssertionParts alignTerm align
            (formationObservationAssertion observation)
        pure (FormationObservation (formationHypothesisProposition root) assertion (formationObservationOrigin observation)
            (evidenceAtomicCount index - batchEnd + offset), (root, path))
    selectedObservations current postings = fmap catMaybes $ for (Map.toAscList postings)
        \(position, indexed@(observation, _)) -> do
            charge 1
            if notionQueryAdmitsOrigin consumer (formationObservationOrigin observation)
            then do
                State.lift (consume emptyFormationSearchStatistics {formationSearchSourceIndexInspections = 1})
                Just <$> indexedObservation current position indexed
            else pure Nothing
    internAnswer atom exactOnly = do
        initial <- State.get
        let nodes = registeredTerms initial
        (indexed, nextNodes) <- State.runStateT
            (traverseAtomTemplateArguments (\term -> do
                current <- State.get
                (identifier, next) <- State.lift (FormationTerms.intern charge term current)
                State.put next
                pure identifier) atom) nodes
        State.modify' (\state -> state {registeredTerms = nextNodes})
        internAnswerKey (AtomicLeaf indexed) exactOnly
    internAnswerKey indexed exactOnly = do
        atoms <- State.gets registeredAnswers
        let width = case indexed of
              WholeLeaf{} -> 1
              AtomicLeaf atom -> 1 + fromIntegral (atomArity atom)
        charge (2 * FormationTerms.indexWork (Map.size atoms) (width + 1))
        case Map.lookup (indexed, exactOnly) atoms of
            Just key -> pure key
            Nothing -> do
                State.lift (consume emptyFormationSearchStatistics {formationSearchIndexedRows = 1})
                let key = Map.size atoms
                State.modify' (\state -> state {registeredAnswers = Map.insert (indexed, exactOnly) key atoms})
                pure key
    encodeGoal current occurrence = do
        charge 1
        case SourceTerm.sourceTermOccurrenceProvider occurrence of
            Just provider -> TemplateProvider (SourceTerm.sourceTermProviderHead provider)
                <$> traverse (encodeGoal current) (SourceTerm.sourceTermProviderArguments provider)
            Nothing -> case SourceTerm.sourceTermOccurrenceOrderedPair occurrence of
                Just (left, right) -> TemplateOrderedPair <$> encodeGoal current left <*> encodeGoal current right
                Nothing -> do
                    scoped <- core (\work -> countedCheckScopedCanonicalCore
                        (elaborationGlobalTyping current) work
                        (binderStackTypes (lexicalBinderStack (elaborationScope current))) (compiledSourceTermCore occurrence))
                    closedSetValueWith (charge 1) scoped >>= \case
                        Just value -> pure (TemplateClosed value)
                        Nothing -> do
                            allowance <- available
                            leaves <- State.gets registeredLeaves
                            let (result, remaining) = FormationLeaves.internOpaqueLeaf allowance scoped leaves
                            charge (fromIntegral (allowance - remaining))
                            case result of
                                Left FormationLeaves.OpaqueLeafWorkExhausted -> charge 1 >> impossible "exhausted leaf work was admitted"
                                Left _ -> impossible "a checked formation argument lost its scope or type"
                                Right (identifier, next) -> State.modify' (\state -> state {registeredLeaves = next}) >> pure (TemplateVariable identifier)
    interpret template = do
        leaves <- State.gets registeredLeaves
        allowance <- available
        result <- elaborate (interpretFormationTemplate allowance location
            (\work identifier ->
                let (found, remaining) = FormationLeaves.countedLookupOpaqueLeaf work identifier leaves
                in case found of
                    Left FormationLeaves.OpaqueLeafWorkExhausted -> pure (Left CountedCoreStructuralWorkExhausted, remaining)
                    Left _ -> impossible "a formation leaf escaped its scope"
                    Right Nothing -> impossible "a formation leaf escaped its query"
                    Right (Just scoped) -> pure (Right (scopedCoreTerm scoped), remaining)) template)
        coreResult allowance result
    -- Typing, binders, and leaf identities are fixed by this query owner.
    -- Normalize a written operand once; source views retain separate term IDs
    -- even when they denote the same checked opaque value.
    argumentValue current = \case
        TemplateVariable identifier -> do
            State.lift (State.modify' (recordFormationOperation FormationDiagnostics.OperandValueLeaf 1))
            charge 1
            pure identifier
        template -> do
            nodes <- State.gets registeredTerms
            (identifier,next) <- FormationTerms.intern charge template nodes
            State.modify' (\state -> state {registeredTerms = next})
            values <- State.gets registeredTermValues
            charge (FormationTerms.indexWork (Map.size values) 1)
            case Map.lookup identifier values of
                Just value -> do
                    State.lift (State.modify' (recordFormationOperation FormationDiagnostics.OperandValueMemoHit 1))
                    pure value
                Nothing -> do
                    State.lift (State.modify' (recordFormationOperation FormationDiagnostics.OperandValueNormalization 1))
                    value <- interpret template >>= internEqualityTerm current
                    charge (FormationTerms.indexWork (Map.size values) 1)
                    State.modify' (\state -> state {registeredTermValues = Map.insert identifier value values})
                    pure value
    scopeAction :: FormationScopePreparation value -> RegisteredFormationSearch scope value
    scopeAction action = do
        allowance <- available
        let (result, final) = State.runState (Except.runExceptT action)
                (ScopePreparation allowance allowance FormationDiagnostics.emptyDiagnostics Nothing)
        charge (fromIntegral (allowance - scopeWorkRemaining final))
        State.lift (State.modify' (recordFormationCoreWork
            (sum (FormationDiagnostics.coreInspections (scopeWorkDiagnostics final)))))
        for_ (Map.toAscList (FormationDiagnostics.operationCounts (scopeWorkDiagnostics final))) \(operation,amount) ->
            State.lift (State.modify' (recordFormationOperation operation amount))
        case result of
            Right value -> pure value
            Left FormationScopePreparationLimitExceeded{} ->
                charge (fromMaybe 1 (scopeRejectedDebit final)) >> impossible "exhausted query scope work was admitted"
            Left failure -> impossible ("a checked query source lost its scope: " <> show failure)
    -- Query-created assumptions can add producers. Preparing their catalogue
    -- belongs to this requirement's allowance, including unsuccessful children.
    queryCatalogs = do
        (prefix,base) <- elaborate (State.lift (Trans.lift Declaration.formationCatalogSnapshotLowering))
        scope <- elaborate (State.gets (lexicalFormationScope . elaborationScope))
        prepared <- scopeAction (prepareFormationScopeCatalogs prefix base scope)
        elaborate (modifyLexicalScope (\lexical -> lexical {lexicalFormationScope = prepared}))
        case formationScopeCatalogs prepared of
            Just catalogs -> pure (catalogs,base)
            Nothing -> impossible "a query catalogue lost its prepared owner"
    definitionOrdinal = formationDefinitionOrdinal
    viewAliasTerms aliases atom = scopeAction (prepareAliasAtom aliases atom)
    aliasSteps aliases original definitions = scopeAction (prepareAliasSteps aliases original definitions)
    aliasSubstitutions direction steps = scopeAction (prepareAliasSubstitutions direction steps)
    applyAliasSteps direction normalization steps parent premiseAtom targetAtom = do
        let ordered = case direction of
                FormationEqualityLeftToRight -> steps
                FormationEqualityRightToLeft -> reverse steps
            (premise, target) = case direction of
                FormationEqualityLeftToRight -> (formationAliasNormalizationOriginal normalization, formationAliasNormalizationResult normalization)
                FormationEqualityRightToLeft -> (formationAliasNormalizationResult normalization, formationAliasNormalizationOriginal normalization)
        substitutions <- aliasSubstitutions direction ordered
        case NonEmpty.nonEmpty substitutions of
            Nothing -> pure parent
            Just nonempty -> do
                State.lift (consume emptyFormationSearchStatistics
                    {formationSearchEqualityTransportSteps = fromIntegral (length substitutions)})
                limits <- remainingFormationSearchLimits <$> State.lift State.get
                construct (applyEqualitySubstitutionsWithLimits charge limits nonempty premise target parent premiseAtom targetAtom)
    prepareGoal current aliases requested = case aliases of
        AlignedFormationAliases [] -> do
            goal <- traverseAtomTemplateArguments (encodeGoal current) requested
            pure (goal, pure)
        _ -> do
            let checking = SourceTerm.SourceTermCheckingContext (elaborationGlobalTyping current)
                    (binderStackTypes (lexicalBinderStack (elaborationScope current)))
            sealed <- traverseAtomTemplateArguments (\term -> core
                (\work -> SourceTerm.countedSealCanonicalSourceTermOccurrence work checking term)) requested
            (viewed, definitions) <- viewAliasTerms aliases sealed
            original <- elaborate (deriveNotionAtomProposition location (compiledSourceTermCore <$> requested))
            (normalization, steps) <- aliasSteps aliases original definitions
            let viewedAtom = scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> viewed
            goal <- traverseAtomTemplateArguments
                (encodeGoal current . SourceTerm.forgetScopedSourceTermOccurrence) viewed
            pure (goal, \evidence -> applyAliasSteps FormationEqualityRightToLeft normalization steps evidence
                viewedAtom (compiledSourceTermCore <$> requested))
    normalizeObservation aliases assertion evidence = case aliases of
        AlignedFormationAliases [] -> pure (assertion, Set.empty, evidence)
        _ -> do
            (viewed, definitions) <- viewAliasTerms aliases (sourceAssertionAtom assertion)
            (normalization, steps) <- aliasSteps aliases (sourceAssertionFormula assertion) definitions
            let originalAtom = scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> sourceAssertionAtom assertion
                viewedAtom = scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> viewed
            normalized <- applyAliasSteps FormationEqualityLeftToRight normalization steps evidence originalAtom viewedAtom
            -- Preserve the original head/path/presentation while replacing the
            -- arguments and checked formula together.
            let rebuilt = sourceNotionAssertionFromTemplate viewed
                    (formationAliasNormalizationResult normalization)
                    (sourceAssertionPath assertion) (sourceAssertionLocation assertion)
                result = maybe rebuilt (`withSourceNotionOrigin` rebuilt)
                    (sourceNotionWrittenOrigin assertion)
            dependencies <- foldM (\known (definition, _) -> do
                charge (FormationTerms.indexWork (Set.size known) 1)
                pure (Set.insert (AliasFormationDependency (definitionOrdinal definition)) known)) Set.empty steps
            pure (result, dependencies, normalized)
    sameAtom left right = do
        charge 1
        case (left, right) of
            (NegativeAtomTemplate a,NegativeAtomTemplate b) -> sameAtom a b
            (GlobalAtomTemplate head' arguments, GlobalAtomTemplate otherHead otherArguments)
                | head' == otherHead -> sameArguments arguments otherArguments
            (StructureAtomTemplate head' arguments, StructureAtomTemplate otherHead otherArguments)
                | head' == otherHead -> sameArguments arguments otherArguments
            (ExactStructureAtomTemplate shape subject, ExactStructureAtomTemplate other otherSubject)
                | shape == other -> sameArguments (Vector.singleton subject) (Vector.singleton otherSubject)
            (MembershipAtomTemplate element set, MembershipAtomTemplate otherElement otherSet) ->
                sameArguments (Vector.fromList [element, set]) (Vector.fromList [otherElement, otherSet])
            _ -> pure False
    sameArguments left right
        | Vector.length left /= Vector.length right = pure False
        | otherwise = foldM (\same (firstTerm, secondTerm) ->
            if same then core (\work -> countedCanonicalIdentity work firstTerm secondTerm)
            else pure False) True (Vector.zip left right)
    internEqualityTerm current term = do
        scoped <- core (\work -> countedCheckScopedCanonicalCore
            (elaborationGlobalTyping current) work
            (binderStackTypes (lexicalBinderStack (elaborationScope current))) term)
        allowance <- available
        leaves <- State.gets registeredLeaves
        let (result, remaining) = FormationLeaves.internOpaqueLeaf allowance scoped leaves
        charge (fromIntegral (allowance - remaining))
        case result of
            Right (identifier, next) -> do
                State.modify' (\state -> state {registeredLeaves = next})
                pure identifier
            Left FormationLeaves.OpaqueLeafWorkExhausted -> charge 1 >> impossible "exhausted equality leaf work was admitted"
            Left _ -> impossible "a checked equality endpoint lost its scope or type"
    opaqueSupport current = FormationSupport.OpaqueInterpreter
        (argumentValue current)
        (\arity template identifier -> do
            leaves <- State.gets registeredLeaves
            target <- scopedLeaves (\work -> FormationLeaves.countedLookupOpaqueLeaf work identifier leaves)
                >>= maybe (impossible "a support operand escaped its owner") pure
            let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            charge arity
            let environment = foldr (const (CoreTemplate.extendBinderEnvironment TySet))
                    (CoreTemplate.emptyBinderEnvironment types) (take (fromIntegral arity) (repeat ()))
            pattern' <- core (\work -> CoreTemplate.compileTemplate (elaborationGlobalTyping current) work environment template)
            found <- core (\work -> CoreTemplate.matchTemplateExactly (elaborationGlobalTyping current) work pattern' target)
            for found \substitution -> do
                parameters <- canonicalFreeIndicesWith (charge 1) template
                pairs <- for (Set.toAscList (Set.filter (< arity) parameters)) \index -> do
                    charge (FormationTerms.indexWork (Set.size parameters) 1)
                    value <- maybe (impossible "an exact support match lost a parameter") pure
                        (CoreTemplate.lookupTemplateSubstitution (CoreTemplate.MatcherSlot (arity-index-1)) substitution)
                    identifier' <- internEqualityTerm current (scopedCoreTerm value)
                    pure (ViewVariableIx index,identifier')
                pure (Map.fromDistinctAscList pairs))
        (\arity template values -> do
            arguments <- Map.mapKeysMonotonic (\(ViewVariableIx index) -> index) <$> traverse interpret values
            result <- core (\work -> countedInstantiateCanonicalSlots work arity arguments template)
            checked <- checkedFormula current result
            closedSetValueWith (charge 1) checked >>= \case
                Just value -> pure (TemplateClosed value)
                Nothing -> TemplateVariable <$> internEqualityTerm current result)
    supportTemplates current rule = for (FormationRule.ruleSupportSources rule) \(arity,source) -> do
        charge 1
        let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            ambient = FormationRule.ruleAmbientTypes rule
            difference = length types-length ambient
            shift depth term
                | null ambient || difference == 0 = pure term
                | difference < 0 = impossible "a support template escaped its lexical scope"
                | otherwise = shiftCanonicalWith (charge 1) (fromIntegral difference) (arity+depth) term
            portable = fmap (fmap (fmap (\(ViewVariableIx index) -> CBound index)))
                (fromMaybe (SourceResidual Nothing) (residualTemplateEvidence source))
        formula <- shift 0 (residualTemplateFormula source)
        evidence <- SourceEvidence.traverseSourceAtDepth
            (\depth -> traverse (shift depth)) (\depth -> traverse (traverse (shift depth))) portable
        inputs <- core (\work -> ScopedSource.sourceTemplateInputs (elaborationGlobalTyping current) work
            (replicate (fromIntegral arity) TySet <> types) formula evidence)
        -- A bare parameter contributes only B, which is already retained.
        pure (arity,List.filter (\case TemplateVariable (CBound index) -> index >= arity; _ -> True) inputs)
    equalityGraph current = do
        cached <- State.gets registeredEqualities
        case cached of
            Just prepared -> pure (runtimeEqualityGraph prepared)
            Nothing -> do
                let owned = consumerEqualities consumer
                        (formationScopeEvidence (lexicalFormationScope (elaborationScope current)))
                    graph = scopedEqualityGraph owned
                let terms = [term | endpoints <- Map.elems (scopedEqualityTerms owned), (_,term) <- endpoints]
                charge (fromIntegral (length terms))
                State.modify' (\state -> state {registeredEqualities = Just (FormationEqualityRuntime graph terms)})
                pure graph
    equalityPath graph start target = visit (Set.singleton start) (Seq.singleton (start, []))
      where
        visit seen pending = case Seq.viewl pending of
            Seq.EmptyL -> pure Nothing
            (endpoint, reversed) Seq.:< rest
                | endpoint == target -> pure (Just (reverse reversed))
                | otherwise -> do
                    adjacent <- FormationEqualities.adjacent charge endpoint graph
                    (nextSeen, nextPending) <- foldM (\(known, queue) (next, (ordinal, transport)) -> do
                        State.lift (consume emptyFormationSearchStatistics {formationSearchEqualityEdgeInspections = 1})
                        charge (2 * FormationTerms.indexWork (Set.size known) 1)
                        if Set.member next known then pure (known, queue)
                        else pure (Set.insert next known, queue Seq.|> (next, (ordinal, transport) : reversed)))
                        (seen, rest) adjacent
                    visit nextSeen nextPending
    transportAnswer current expected origins evidence = case groundNotionKeyTemplate (formationWitnessGroundKey evidence) of
        Nothing -> pure Nothing
        Just actual | (() <$ actual) /= (() <$ expected) -> pure Nothing
        Just actual -> do
            graph <- equalityGraph current
            paths <- for (zip (toList actual) (toList expected)) \(sourceTerm,targetTerm) -> do
                fromId <- internEqualityTerm current sourceTerm
                toId <- internEqualityTerm current targetTerm
                equalityPath graph fromId toId
            case sequence paths of
                Nothing -> pure Nothing
                Just positions -> do
                    let steps = concat positions
                    dependencies <- foldM (\known (ordinal,_) -> do
                        charge (FormationTerms.indexWork (Set.size known) 1)
                        pure (Set.insert (EqualityFormationDependency ordinal) known)) origins steps
                    pure (Just (dependencies, do
                        (_,substitutions) <- foldM (\(atom,selected) (position,targetTerm,path) -> do
                            if null path then pure (atom,selected) else do
                                predicate <- elaborate $ withAnonymousSetBinder \bound -> do
                                    let shifted = shiftCanonical 1 0 <$> atom
                                    body <- deriveNotionAtomProposition location (replaceArgument position bound shifted)
                                    maybe (impossible "an equality predicate could not close") pure (abstractScopedCore TySet body)
                                aligned <- traverse (\(_,edge) -> core (\work -> countedAlignFormationEqualityTransport work
                                    (binderStackTypes (lexicalBinderStack (elaborationScope current))) edge)) path
                                pure (replaceArgument position targetTerm atom, selected <> [(edge,predicate) | edge <- aligned]))
                            (actual,[]) (zip3 [0..] (toList expected) positions)
                        premiseFormula <- elaborate (deriveNotionAtomProposition location actual)
                        targetFormula <- elaborate (deriveNotionAtomProposition location expected)
                        case NonEmpty.nonEmpty substitutions of
                            Nothing -> construct (convertFormationEvidence charge targetFormula evidence expected)
                            Just nonempty -> do
                                State.lift (consume emptyFormationSearchStatistics
                                    {formationSearchEqualityTransportSteps = fromIntegral (length substitutions)})
                                limits <- remainingFormationSearchLimits <$> State.lift State.get
                                construct (applyEqualitySubstitutionsWithLimits charge limits nonempty
                                    premiseFormula targetFormula evidence actual expected)))
      where
        -- The same traversal order owns indexing, matching, and the one-hole
        -- predicate. Equal-valued positions still remain distinct slots.
        replaceArgument position replacement atom = State.evalState
            (traverseAtomTemplateArguments (\term -> State.state (\index ->
                (if index == position then replacement else term,index+1))) atom) (0 :: Int)
    mergeOrigins left right = do
        let size = Set.size left + Set.size right
        charge (FormationTerms.indexWork size (1 + fromIntegral size))
        pure (Set.union left right)
    premise tree = do
        charge 1
        case tree of
            Composite.CompositePremiseTruth -> pure (Set.empty, FormationPremiseEvidenceTruth)
            Composite.CompositePremiseLeaf (origins, evidence) ->
                pure (origins, FormationPremiseEvidenceLeaf evidence)
            Composite.CompositePremiseAnd left right -> do
                (leftOrigins, leftEvidence) <- premise left
                (rightOrigins, rightEvidence) <- premise right
                origins <- mergeOrigins leftOrigins rightOrigins
                pure (origins, FormationPremiseEvidenceAnd leftEvidence rightEvidence)
    formulaTable current = State.gets registeredFormulas >>= \case
        Just table -> pure table
        Nothing -> do
            let index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
                types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            table <- State.lift (formationFormulaWork location (\work ->
                FormationFormulas.extendFormulas work types (evidenceFormulas index)))
            State.modify' (\state -> state {registeredFormulas = Just table})
            pure table
    internFormula current formula = do
        table <- formulaTable current
        (identifier, next) <- State.lift (formationFormulaWork location (\work -> FormationFormulas.internFormula work formula table))
        State.modify' (\state -> state {registeredFormulas = Just next})
        pure identifier
    atomicFormula current row = do
        terms <- traverseAtomTemplateArguments interpret row
        formula <- elaborate (deriveNotionAtomProposition location terms)
        internFormula current formula
    formulaShape current identifier = do
        table <- formulaTable current
        (selected,next) <- State.lift (formationFormulaWork location (\work ->
            FormationFormulas.prepareFormulaShape work identifier table))
        State.modify' (\state -> state {registeredFormulas = Just next})
        maybe (impossible "a checked notion goal lost its shape") pure selected
    checkedFormula current formula = core (\work -> countedCheckScopedCanonicalCore
        (elaborationGlobalTyping current) work
        (binderStackTypes (lexicalBinderStack (elaborationScope current))) formula)
    describeWholeGoal current requested = describeWholePlan current requested Nothing
    describeWholePlan current requested prepared = do
        identifier <- internFormula current (wholeGoalFormula requested)
        describeWholeFormula current identifier requested prepared
    describeWholeFormula current identifier requested prepared = do
        leaves <- State.gets registeredLeaves
        let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            formula = wholeGoalFormula requested
        (target,next) <- core (\work -> ScopedSource.describeScopedGoal work types
            (scopedCoreContext formula) (scopedCoreTerm formula) (wholeGoalEvidence requested) leaves)
        goals <- State.gets registeredWholeGoals
        charge (FormationTerms.indexWork (Map.size goals) 1)
        unless (Map.member identifier goals) do
            plan <- maybe (FormationGoal.compileGoal (charge 1) (scopedCoreTerm formula)
                (wholeGoalEvidence requested)) pure prepared
            charge (FormationTerms.indexWork (Map.size goals) 1)
            State.modify' (\state -> state {registeredWholeGoals = Map.insert identifier (requested,plan) goals})
        State.modify' (\state -> state {registeredLeaves = next})
        pure (FormationRequest.WholeRequest identifier target)
    prepareWholeRequest current ordinal position rule values template = do
        case template of
            WholeUniversal{} -> materializeWhole current rule values template Nothing
            WholeResidual residual -> do
                known <- State.gets registeredFormulaTemplates
                charge (FormationTerms.indexWork (Map.size known) 1)
                (node,parameters) <- case Map.lookup (ordinal,position) known of
                    Just prepared -> pure prepared
                    Nothing -> do
                        let (arity,_,_) = FormationRule.ruleDescription rule
                            types = replicate (fromIntegral arity) TySet <> FormationRule.ruleAmbientTypes rule
                        admittedTemplate <- core (\work -> countedCheckScopedCanonicalCore
                            (elaborationGlobalTyping current) work types (residualTemplateFormula residual))
                        formulas <- formulaTable current
                        (node,next) <- State.lift (formationFormulaWork location (\work ->
                            FormationFormulas.prepareFormulaTemplate work arity admittedTemplate formulas))
                        slots <- Set.filter (\(ViewVariableIx index) -> index < arity) <$>
                            residualTemplateParametersWith (charge 1) residual
                        charge (FormationTerms.indexWork (Map.size known) (1 + fromIntegral (Set.size slots)))
                        State.modify' (\owner -> owner {registeredFormulas = Just next,
                            registeredFormulaTemplates = Map.insert (ordinal,position) (node,slots) known})
                        pure (node,slots)
                relevant <- for (Set.toAscList parameters) \slot -> do
                    charge (FormationTerms.indexWork (Map.size values) 1)
                    value <- maybe (impossible "a whole request lost a required assignment") pure (Map.lookup slot values)
                    terms <- State.gets registeredTerms
                    (identifier,next) <- FormationTerms.intern charge value terms
                    State.modify' (\owner -> owner {registeredTerms = next})
                    pure (slot,(identifier,value))
                let requestKey = (ordinal,position,[(slot,identifier) | (slot,(identifier,_)) <- relevant])
                requests <- State.gets registeredWholeRequests
                charge (FormationTerms.indexWork (Map.size requests) (1 + fromIntegral (length relevant)))
                case Map.lookup requestKey requests of
                    Just requested -> pure requested
                    Nothing -> do
                        arguments <- Map.fromList <$> for relevant (\(ViewVariableIx slot,(_,value)) -> do
                            identifier <- argumentValue current value
                            leaves <- State.gets registeredLeaves
                            term <- core (\work -> let (result,remaining) = FormationLeaves.countedLookupOpaqueLeaf work identifier leaves
                                in (case result of
                                    Right (Just found) -> Right found
                                    Left FormationLeaves.OpaqueLeafWorkExhausted -> Left CountedCoreStructuralWorkExhausted
                                    _ -> impossible "a whole assignment escaped its nominal owner",remaining))
                            pure (slot,(identifier,term)))
                        formulas <- formulaTable current
                        (identifier,next) <- State.lift (formationFormulaWork location (\work ->
                            FormationFormulas.instantiateFormulaTemplate work node arguments formulas))
                        State.modify' (\owner -> owner {registeredFormulas = Just next})
                        admitted <- State.lift (formationFormulaWork location (\work ->
                            FormationFormulas.lookupFormula work identifier next))
                            >>= maybe (impossible "an instantiated formula lost its value") pure
                        requested <- materializeWhole current rule values template (Just (identifier,admitted))
                        charge (FormationTerms.indexWork (Map.size requests) (1 + fromIntegral (length relevant)))
                        State.modify' (\owner -> owner {registeredWholeRequests = Map.insert requestKey requested (registeredWholeRequests owner)})
                        pure requested
    materializeWhole current rule values template prepared = do
        sources <- traverse reify values
        let outer slot = do
                charge (FormationTerms.indexWork (Map.size sources) 1)
                maybe (impossible "a determined whole premise lost a parameter") pure (Map.lookup slot sources)
            shifted depth source = State.lift (formationCoreWork location (\work ->
                SourceTerm.countedShiftCanonicalSourceTermOccurrence work depth 0 source))
            variable depth (ViewVariableIx index)
                | index < depth = pure (locatedSetSourceTerm location (CBound index))
                | otherwise = outer (ViewVariableIx (index-depth)) >>= shifted depth
            universalVariable depth = \case
                SourceEvidence.UniversalBound index -> pure (locatedSetSourceTerm location (CBound (depth-index-1)))
                SourceEvidence.UniversalOuter term -> sourceTerm outer term >>= shifted depth
            sourceTerm :: (variable -> RegisteredFormationSearch scope CompiledSourceTerm)
                -> SetTermTemplate variable -> RegisteredFormationSearch scope CompiledSourceTerm
            sourceTerm variable' term = do
                instantiated <- traverse variable' term
                State.lift (instantiateFormationSourceTerm location pure instantiated)
            atom :: Natural -> (Natural -> variable -> RegisteredFormationSearch scope CompiledSourceTerm)
                -> AtomTemplate (SetTermTemplate variable)
                -> RegisteredFormationSearch scope ScopedSourceNotionOccurrence
            atom depth variable' description = do
                terms <- traverse (sourceTerm (variable' depth)) description
                formula <- elaborate (deriveNotionAtomCore location (compiledSourceTermCore <$> terms))
                let context = replicate (fromIntegral depth) TySet <>
                        binderStackTypes (lexicalBinderStack (elaborationScope current))
                checked <- core (\work -> countedCheckScopedCanonicalCore (elaborationGlobalTyping current) work context formula)
                scoped <- traverse (\term -> core (\work -> SourceTerm.countedSealCanonicalSourceTermOccurrence work
                    (SourceTerm.SourceTermCheckingContext (elaborationGlobalTyping current) context) term)) terms
                pure (sourceNotionAssertionFromTemplate scoped checked ConjunctionHere location)
        (formula,evidence) <- case template of
            WholeResidual residual -> do
                let arguments = Map.mapKeysMonotonic (\(ViewVariableIx index) -> index) (compiledSourceTermCore <$> sources)
                    (arity,_,_) = FormationRule.ruleDescription rule
                    ambient = FormationRule.ruleAmbientTypes rule
                    difference = length (binderStackTypes (lexicalBinderStack (elaborationScope current))) - length ambient
                formula <- case prepared of
                    Just (_,admitted) -> pure (scopedCoreTerm admitted)
                    Nothing -> do
                        templateFormula <- if null ambient then pure (residualTemplateFormula residual) else do
                            when (difference < 0) (impossible "a local formula escaped its lexical scope")
                            core (\work -> countedShiftCanonical work (fromIntegral difference) arity (residualTemplateFormula residual))
                        core (\work -> countedInstantiateCanonicalSlots work arity arguments templateFormula)
                let input depth term = do
                        shiftedTerm <- if null ambient then pure term else traverse
                            (\value -> core (\work -> countedShiftCanonical work (fromIntegral difference) (arity+depth) value)) term
                        instantiateSupportPrefixWith (charge 1) arity
                            (\nested index -> do
                                source <- outer (ViewVariableIx index) >>= shifted nested
                                pure (SourceTerm.sourceSupportTemplate id source, compiledSourceTermCore source)) depth shiftedTerm
                evidence <- maybe (pure (SourceResidual Nothing))
                    (SourceEvidence.traverseSourceAtDepth input (\depth -> atom depth variable)) (residualTemplateEvidence residual)
                pure (formula,evidence)
            WholeUniversal body -> do
                instantiated <- UniversalTemplate.traverseBodyAtDepth (\depth -> atom depth universalVariable) body
                evidence <- SourceEvidence.universalEvidenceWith (charge 1) instantiated
                pure (SuppliedUniversal.universalFormula (scopedCoreTerm . sourceAssertionFormula <$> instantiated),evidence)
        case prepared of
            Nothing -> do
                admitted <- checkedFormula current formula
                describeWholeGoal current (WholeNotionGoal admitted evidence)
            Just (identifier,admitted) -> describeWholeFormula current identifier (WholeNotionGoal admitted evidence) Nothing
      where
        reify value = do
            leaves <- traverse (interpret . TemplateVariable) value
            State.lift (instantiateFormationSourceTerm location (pure . locatedSetSourceTerm location) leaves)
    wholeEvidence current suppliedSources requestedWhole = do
        let identifier = FormationRequest.wholeRequestFormula requestedWhole
            index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
        table <- formulaTable current
        formula <- State.lift (formationFormulaWork location (\work -> FormationFormulas.lookupFormula work identifier table))
            >>= maybe (impossible "a whole request escaped its formula owner") pure
        charge (FormationTerms.indexWork (Map.size (evidenceWhole index)) 1)
        exact <- directWhole current formula (Map.toAscList (Map.findWithDefault Map.empty identifier (evidenceWhole index)))
        found <- case (exact, FormationRequest.wholeRequestUniversal requestedWhole) of
            (Just evidence, _) -> pure (Just evidence)
            (Nothing, Nothing) -> pure Nothing
            (Nothing, Just target) -> do
                candidates <- SuppliedUniversal.suppliedCandidates charge target suppliedSources
                lookupSupplied current target candidates >>= traverse (\(origins, source, adapter) -> do
                    State.modify' (\state -> state {registeredOutcome =
                        if registeredOutcome state == FormationDiagnostics.ExactDirect
                        then FormationDiagnostics.FlexibleUniversal else registeredOutcome state})
                    (\witness -> (origins, witness)) <$> construct (suppliedFormationEvidence charge formula source adapter))
        for found \(origins, witness) -> do
            key <- internAnswerKey (WholeLeaf identifier) True
            retained <- retainWitness key origins (pure witness)
            pure (key, retained)
    directWhole _ _ [] = pure Nothing
    directWhole current formula (((Down source, ordinal), WholeFormationObservation parent origin path _inputs _inputOwner) : rest) = do
        charge 1
        if not (notionQueryAdmitsOrigin consumer origin) then directWhole current formula rest else do
            State.lift (consume emptyFormationSearchStatistics {formationSearchSourceIndexInspections = 1})
            roots <- State.gets registeredWholeHypotheses
            charge (FormationTerms.indexWork (Map.size roots) 1)
            root <- case Map.lookup source roots of
                Just reference -> pure reference
                Nothing -> do
                    aligned <- core (\work -> countedAlignScopedCore work
                        (binderStackTypes (lexicalBinderStack (elaborationScope current))) parent)
                        >>= maybe (impossible "a whole source escaped its admitted scope") pure
                    reference <- construct (prepareFormationHypothesis charge aligned origin)
                    State.modify' (\state -> state {registeredWholeHypotheses = Map.insert source reference roots})
                    pure reference
            witness <- construct (directPreparedFormationEvidence charge (groundNotionKeyFromFormula formula) root path ordinal)
            pure (Just (Set.singleton (WholeFormationDependency source ordinal), witness))
    lookupUniversal current identifier = do
        let known = evidenceUniversals (formationScopeEvidence (lexicalFormationScope (elaborationScope current)))
        charge (FormationTerms.indexWork (Seq.length known) 1)
        case Seq.lookup identifier known of
            Just (PreparedFormationUniversal types origin source) -> pure (types, origin, source)
            Nothing -> impossible "a supplied universal escaped its source owner"
    alignUniversal current identifier = do
        (_, _, source) <- lookupUniversal current identifier
        core (\work -> countedAlignFormationSourceEvidence work
            (binderStackTypes (lexicalBinderStack (elaborationScope current))) source)
    lookupSupplied _ _ [] = pure Nothing
    lookupSupplied current target ((identifier, supplied):rest) = do
        charge 1
        (original, origin, _) <- lookupUniversal current identifier
        if not (notionQueryAdmitsOrigin consumer origin)
        then lookupSupplied current target rest
        else do
            State.lift (consume emptyFormationSearchStatistics {formationSearchSourceIndexInspections = 1})
            let difference = length (binderStackTypes (lexicalBinderStack (elaborationScope current))) - length original
            aligned <- UniversalTemplate.traverseBodyAtDepth (\depth (key, formula) ->
                (\value -> (key, value)) <$> core (\work -> countedShiftCanonical work (fromIntegral difference) depth formula)) supplied
            matched <- SuppliedUniversal.matchUniversal charge (SuppliedUniversal.sameUniversalAtom charge) aligned target
            case matched of
                Nothing -> lookupSupplied current target rest
                Just adapter -> do
                    source <- alignUniversal current identifier
                    dependencies <- universalDependencies source
                    pure (Just (dependencies, source, adapter))
    universalDependencies source = foldM (\known ordinal -> do
        charge (FormationTerms.indexWork (Set.size known) 1)
        pure (Set.insert (AliasFormationDependency ordinal) known))
        (Set.singleton (UniversalFormationDependency (formationSourceEvidenceOrdinal source)))
        (formationSourceEvidenceAliasOrdinals source)
    describeFailure current catalog observations answers missing = do
        let sourceTerms = (case requestedLeaf of AtomicLeaf atom -> toList atom; WholeLeaf{} -> []) <> concat
                [toList (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom (formationObservationAssertion observation))
                | observation <- observations]
        presentations <- foldM retainPresentation Map.empty sourceTerms
        charge (fromIntegral (length observations) * FormationTerms.indexWork (length observations) 1)
        let origins = Map.fromList [(formationObservationOrdinal observation, formationObservationOrigin observation)
                | observation <- observations]
        selected <- foldM (\best (atom, answer) -> do
            charge 1
            let (dependencies, evidence) = FormationEvaluation.ruleAnswerWitness answer
                rank = formationWitnessDerivationNodes evidence
            foldM (\current dependency -> do
                charge (FormationTerms.indexWork (Map.size origins) 1)
                pure (case dependency of
                    ObservedFormationDependency ordinal | Just origin <- Map.lookup ordinal origins ->
                        let candidate = (rank, FormationFailureFrontier
                                (atomHead atom) origin)
                        in case current of
                            Just (previous, _) | previous >= rank -> current
                            _ -> Just candidate
                    _ -> current)) best (Set.toAscList dependencies)) Nothing
                [(atom, answer) | answer <- answers, AtomicLeaf atom <- [FormationEvaluation.ruleAnswerLeaf answer]]
        let frontier = snd <$> selected
        detail <- case (case requestedLeaf of AtomicLeaf atom -> notionFocusTerm atom; WholeLeaf{} -> Nothing) >>= SourceTerm.sourceTermOccurrenceProvider of
            Nothing -> pure Nothing
            Just provider -> do
                let head' = SourceTerm.sourceTermProviderHead provider
                case head' of
                    IntrinsicSourceProvider intrinsic
                        | Vector.null (SourceTerm.sourceTermProviderArguments provider) -> do
                            registered <- elaborate (State.lift (Trans.lift
                                (Declaration.firstVisibleNullaryProviderClassificationLowering intrinsic)))
                            pure (Just (RichNullaryClassificationFailure (case registered of
                                Nothing -> NullaryClassificationMissing intrinsic
                                Just entry -> let declaration = visibleNullaryProviderClassificationPayload entry
                                    in NullaryClassificationClosureMissing intrinsic
                                        (semanticFactBranchFact (visibleNullaryProviderClassificationSource entry))
                                        (nullaryConclusion declaration))))
                    _ -> do
                        source <- elaborate (resolveProviderFailureSource head')
                        registrations <- FormationCatalog.providerFocusedSources charge head' catalog
                        let relevant = [(ordinal, entry)
                                | (ordinal, Left (FormationProviderRule entry)) <- registrations
                                , resultProviderTemplateHead (providerResultProvider (visibleProviderResultRulePayload entry)) == head']
                            ruleIds = Set.fromList (fst <$> relevant)
                        charge (fromIntegral (length relevant) * FormationTerms.indexWork (length relevant) 1)
                        candidates <- fmap catMaybes $ for missing \(ordinal, atom) -> do
                            charge (FormationTerms.indexWork (Set.size ruleIds) 1)
                            pure (if Set.member ordinal ruleIds then Just atom else Nothing)
                        missingPremise <- case candidates of
                            [] -> pure Nothing
                            candidate:_ -> Just <$> traverseAtomTemplateArguments (presentTerm presentations) candidate
                        pure (Just (RichProviderFormationFailure (case (relevant, missingPremise) of
                            (_:_, Just premiseAtom) -> ProviderResultPremiseMissing source premiseAtom
                            ((_, entry):_, Nothing) -> ProviderResultUnavailable source
                                (atomHead (providerResultConclusion (visibleProviderResultRulePayload entry)))
                            ([], _) -> ProviderResultRuleMissing source)))
        statistics <- formationSearchBudgetStatistics <$> State.lift State.get
        pure (RichFormationFailure (FormationFailureExplanation statistics frontier False) detail)
      where
        atomHead = templateHead
        retainPresentation known term = do
            charge 1
            case SourceTerm.sourceTermOccurrenceProvider term of
                Just provider -> foldM retainPresentation known (SourceTerm.sourceTermProviderArguments provider)
                Nothing -> case SourceTerm.sourceTermOccurrenceOrderedPair term of
                    Just (left, right) -> retainPresentation known left >>= (`retainPresentation` right)
                    Nothing -> do
                        identifier <- internEqualityTerm current (compiledSourceTermCore term)
                        charge (FormationTerms.indexWork (Map.size known) 1)
                        pure (Map.insertWith (\_ previous -> previous) identifier (compiledSourceTermPresentation term) known)
        presentTerm presentations term = do
            charge 1
            case term of
                TemplateClosed{} -> pure (LocatedSourceTerm location)
                TemplateVariable identifier -> do
                    charge (FormationTerms.indexWork (Map.size presentations) 1)
                    pure (Map.findWithDefault (LocatedSourceTerm location) identifier presentations)
                TemplateOrderedPair left right -> do
                    leftPresentation <- presentTerm presentations left
                    second <- presentTerm presentations right
                    pure (PresentedSourceTerm location ("(" <> renderSourceTermPresentation leftPresentation <> ", " <> renderSourceTermPresentation second <> ")"))
                TemplateProvider provider arguments -> do
                    rendered <- fmap renderSourceTermPresentation <$> traverse (presentTerm presentations) arguments
                    let values = toList rendered
                        text = case provider of
                            GlobalSourceProvider reference -> renderGlobalApplication (globalBindingRefKey reference) values
                            FiniteSetLiteralSourceProvider -> "{" <> Text.intercalate ", " values <> "}"
                            IntrinsicSourceProvider intrinsic -> renderIntrinsicProvider intrinsic <> "(" <> Text.intercalate ", " values <> ")"
                            StructureFieldSourceProvider{} -> "field value at " <> locationToText location
                    pure (PresentedSourceTerm location text)
    evaluate current = do
        report "start"
        let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
            index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
        when (isNothing prior) do
            leaves <- scopedLeaves (\work -> FormationLeaves.extendOpaqueLeaves work types (evidenceLeaves index))
            State.modify' (\state -> state {registeredLeaves = leaves})
        case requestedLeaf of
            WholeLeaf requested -> do
                identifier <- internFormula current (wholeGoalFormula requested)
                found <- wholeEvidence current (evidenceSupplied index) (FormationRequest.WholeRequest identifier Nothing)
                case found of
                    Just (_,(_,witness)) -> pure (RegisteredFinished (Right witness))
                    Nothing -> do
                        whole <- describeWholeGoal current requested
                        adapted <- case FormationRequest.wholeRequestUniversal whole of
                            Nothing -> pure Nothing
                            Just{} -> wholeEvidence current (evidenceSupplied index) whole
                        case adapted of
                            Just (_,(_,witness)) -> pure (RegisteredFinished (Right witness))
                            Nothing -> evaluateRules current (Just whole)
            AtomicLeaf requested -> do
                key <- traverseAtomTemplateArguments (\argument -> do
                    scoped <- core (\work -> countedCheckScopedCanonicalCore
                        (elaborationGlobalTyping current) work types (compiledSourceTermCore argument))
                    known <- State.gets registeredLeaves
                    (identifier, next) <- scopedLeaves (\work -> FormationLeaves.internOpaqueLeaf work scoped known)
                    State.modify' (\state -> state {registeredLeaves = next})
                    pure identifier) requested
                charge (FormationTerms.indexWork (Map.size (evidenceExact index))
                    (1 + fromIntegral (length (toList key))))
                observations <- selectedObservations current (Map.findWithDefault Map.empty key (evidenceExact index))
                -- Exact eligible local evidence needs no source normalization or
                -- equality graph. Preserve the ordinary direct-witness ordering and
                -- charge every comparison before attempting rule search.
                direct <- foldM (\selected (observation, (root, path)) -> do
                    let assertion = formationObservationAssertion observation
                        actual = scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> sourceAssertionAtom assertion
                    evidence <- construct (directPreparedFormationEvidence charge (groundNotionKeyFromTemplate actual) root
                        path (formationObservationOrdinal observation))
                    charge 1
                    pure (Just (maybe evidence (`preferDirectFormationWitness` evidence) selected))) Nothing observations
                case direct of
                    Just evidence -> pure (RegisteredFinished (Right evidence))
                    Nothing -> evaluateRules current Nothing

    chargeSelector ConjunctionHere = pure ()
    chargeSelector (ConjunctionLeft rest) = charge 1 >> chargeSelector rest
    chargeSelector (ConjunctionRight rest) = charge 1 >> chargeSelector rest

    evaluateRules current wholeGoal = do
        State.modify' (\state -> state {registeredOutcome = FormationDiagnostics.SearchedSuccess})
        aliases <- core (\work -> countedFormationAliasSources work consumer
            (binderStackTypes (lexicalBinderStack (elaborationScope current))) (elaborationProofSupport current)
            (formationScopeAliases (lexicalFormationScope (elaborationScope current))))
        (goal, restoreGoal) <- case requestedLeaf of
            AtomicLeaf requested -> do
                (atom,restore) <- prepareGoal current aliases requested
                pure (AtomicLeaf atom,restore)
            WholeLeaf{} -> do
                whole <- maybe (impossible "a whole search lost its prepared root") pure wholeGoal
                pure (WholeLeaf whole,pure)
        result <- State.gets registeredSession >>= \case
            Just session -> FormationEvaluation.focusRuleSession goal session >>= pure . fmap FormationEvaluation.StartedRules
            Nothing -> prepareSearch current aliases goal
        case result of
            Left failure -> finishSearch current restoreGoal (Left failure)
            Right (FormationEvaluation.PreparedAnswer answer) ->
                finishSearch current restoreGoal (Right (FormationEvaluation.FoundAnswer answer))
            Right (FormationEvaluation.StartedRules session) -> finishSession current restoreGoal session

    finishSearch current restoreGoal result = do
        State.lift (State.modify' (setFormationRegistrationFamily Nothing))
        report "search-finished"
        diagnostics <- formationSearchBudgetDiagnostics <$> State.lift State.get
        report ("query-counts=" <> Text.pack (show diagnostics))
        let failure answers missing = do
                (_,globalCatalog) <- queryCatalogs
                observations <- State.gets registeredSearchObservations
                Left <$> describeFailure current globalCatalog observations answers missing
        RegisteredFinished <$> case result of
            Left _ -> failure [] []
            Right (FormationEvaluation.FoundAnswer answer) ->
                Right <$> restoreGoal (snd (FormationEvaluation.ruleAnswerWitness answer))
            Right (FormationEvaluation.SearchAnswers evaluated missing) -> case
                [ snd (FormationEvaluation.ruleAnswerWitness answer)
                | key <- Set.toAscList (FormationRelational.relationalRootAnswers evaluated)
                , Just answer <- [Map.lookup key (FormationRelational.relationalAnswers evaluated)]
                ] of
                    [] -> failure (Map.elems (FormationRelational.relationalAnswers evaluated)) missing
                    initial : _ -> Right <$> restoreGoal initial

    finishSession current restoreGoal session = do
        State.modify' (\state -> state {registeredSession = Just session})
        pure (RegisteredPending (continueSession current restoreGoal))

    continueSession current restoreGoal = do
        session <- currentSession
        case FormationEvaluation.ruleSessionStatus session of
            FormationRelational.RelationalAnswered -> do
                answer <- FormationEvaluation.ruleSessionAnswer session
                    >>= maybe (impossible "an answered formation session lost its witness") pure
                finishSearch current restoreGoal (Right (FormationEvaluation.FoundAnswer answer))
            status -> do
                state <- State.get
                let queue = registeredIntroductions state
                    pending = introductionAlternatives queue
                if status == FormationRelational.RelationalQuiescent && introductionsSettled queue
                then do
                    completed <- uncurry FormationEvaluation.SearchAnswers <$> FormationEvaluation.finishRuleSession session
                    finishSearch current restoreGoal (Right completed)
                else do
                    if not (Seq.null pending) && (introductionTurn queue || status == FormationRelational.RelationalQuiescent)
                    then advanceIntroduction
                    else do
                        next <- FormationEvaluation.advanceRuleSession 64 session
                        State.modify' (\owner -> owner {registeredSession = Just next,
                            registeredIntroductions = (registeredIntroductions owner)
                                {introductionTurn = True, introductionWaitingCount = 0}})
                    pure (RegisteredPending (continueSession current restoreGoal))

    currentSession = State.gets registeredSession
        >>= maybe (impossible "a suspended formation query lost its table") pure

    advanceIntroduction = do
        queue <- State.gets registeredIntroductions
        case Seq.viewl (introductionAlternatives queue) of
            Seq.EmptyL -> pure ()
            action Seq.:< rest -> do
                State.modify' (\owner -> owner {registeredIntroductions = queue
                    {introductionAlternatives = rest, introductionTurn = False}})
                step <- action
                State.modify' (\owner -> owner
                    {registeredIntroductions = resumeIntroduction step (registeredIntroductions owner)})

    requestIntroduction current requested = do
        let identifier = FormationRequest.wholeRequestFormula requested
        known <- State.gets registeredIntroduced
        charge (FormationTerms.indexWork (Set.size known) 1)
        unless (Set.member identifier known) do
            description <- State.gets (Map.lookup identifier . registeredWholeGoals)
            for_ description \goal -> do
                charge 1
                State.modify' (\owner -> owner
                    { registeredIntroduced = Set.insert identifier (registeredIntroduced owner)
                    , registeredIntroductions = enqueueIntroduction (openIntroduction current identifier goal)
                        (registeredIntroductions owner) })

    publishIntroduction identifier witness = do
        key <- internAnswerKey (WholeLeaf identifier) True
        retained <- retainWitness key Set.empty (pure witness)
        session <- currentSession
        next <- FormationEvaluation.deliverRuleSession
            [FormationEvaluation.RuleAnswer (WholeLeaf identifier) key FormationJoin.ExactAnswer retained] session
        State.modify' (\owner -> owner {registeredSession = Just next})
        pure IntroductionComplete

    openIntroduction current identifier (goal,plan) = do
        charge 1
        let formula = wholeGoalFormula goal
        case FormationGoal.goalOperation plan of
            FormationGoal.TruthGoal -> construct (composeFormationEvidence charge formula FormationPremiseEvidenceTruth)
                >>= publishIntroduction identifier
            -- Finite relational introductions are compiled clauses. Only
            -- primitive tests and genuinely scoped operations enter this queue.
            FormationGoal.ConjunctionGoal{} -> pure IntroductionComplete
            FormationGoal.DisjunctionGoal{} -> pure IntroductionComplete
            FormationGoal.BiconditionalGoal a b -> do
                let (_,left,right) = fromMaybe (impossible "a checked biconditional lost its operands") (splitScopedEquality formula)
                    implication antecedent consequent = core (\work -> countedImplyScopedCore work antecedent consequent)
                        >>= maybe (impossible "biconditional operands had different contexts") pure
                    planFor target antecedent consequent = FormationGoal.GoalPlan (scopedCoreTerm target)
                        (SourceRequire (FormationGoal.goalEvidence antecedent) (FormationGoal.goalEvidence consequent))
                        (FormationGoal.ImplicationGoal antecedent consequent) False
                forward <- implication left right
                backward <- implication right left
                forwardGoal <- prepareIntroductionGoal current forward (planFor forward a b)
                backwardGoal <- prepareIntroductionGoal current backward (planFor backward b a)
                pure (IntroductionRunnable (combineIff identifier formula forwardGoal Nothing backwardGoal Nothing))
            FormationGoal.UniversalGoal nested -> do
                let (_,body) = fromMaybe (impossible "a checked universal lost its body") (openScopedForall formula)
                scope <- either (elaborate . Except.throwError) pure
                    (extendLexicalBinders ((Nothing,TySet) :| []) (elaborationScope current))
                roots <- traverse (weakenRoot current) groupRoots'
                seeds <- traverse (\term -> core (\work -> SourceTerm.countedShiftCanonicalSourceTermOccurrence work 1 0 term)) groupSeeds
                startChild current {elaborationScope = scope} roots
                    (locatedSetSourceTerm location (CBound 0) : seeds)
                    FormationSetIntroduction identifier formula (WholeNotionGoal body (FormationGoal.goalEvidence nested))
            FormationGoal.ImplicationGoal premisePlan bodyPlan -> do
                let (assumption,body) = fromMaybe (impossible "a checked implication lost its body") (openScopedImplication formula)
                    a = FormationGoal.goalEvidence premisePlan
                    b = FormationGoal.goalEvidence bodyPlan
                    scope = elaborationScope current
                    formation = lexicalFormationScope scope
                    origin = FormationFromGoalAssumption (evidenceSourceCount (formationScopeEvidence formation)) location
                    source = FormationPremiseSource Nothing assumption a origin
                extended <- scopeAction (extendFormationScope (binderStackTypes (lexicalBinderStack scope))
                    (elaborationProofSupport current) source formation)
                equalities <- introducedEqualities id assumption a
                complete <- case NonEmpty.nonEmpty equalities of
                    Nothing -> pure extended
                    Just occurrences -> scopeAction (extendFormationEqualityScope
                        (binderStackTypes (lexicalBinderStack scope)) (elaborationProofSupport current)
                        (FormationEqualitySource Nothing assumption occurrences origin) extended)
                startChild current {elaborationScope = scope {lexicalFormationScope = complete}}
                    groupRoots' groupSeeds (FormationAssumptionIntroduction origin)
                    identifier formula (WholeNotionGoal body b)
            FormationGoal.ExactGoal -> pure IntroductionComplete
            FormationGoal.AtomicGoal{} -> pure IntroductionComplete
            FormationGoal.EqualityGoal left right -> do
                source <- internEqualityTerm current left
                target <- internEqualityTerm current right
                path <- if source == target then pure (Just []) else do
                    graph <- equalityGraph current
                    equalityPath graph source target
                case path of
                    Nothing -> pure IntroductionComplete
                    Just steps -> do
                        reflexive <- checkedFormula current (CEq TySet left left)
                        witness <- construct (composeFormationEvidence charge reflexive (FormationPremiseEvidenceReflexivity left))
                        result <- case NonEmpty.nonEmpty (snd <$> steps) of
                            Nothing -> pure witness
                            Just edges -> do
                                aligned <- traverse (\edge -> core (\work -> countedAlignFormationEqualityTransport work
                                    (binderStackTypes (lexicalBinderStack (elaborationScope current))) edge)) edges
                                shifted <- core (\work -> countedShiftCanonical work 1 0 left)
                                predicate <- checkedFormula current (CLam TySet (CEq TySet shifted (CBound 0)))
                                limits <- remainingFormationSearchLimits <$> State.lift State.get
                                State.lift (consume emptyFormationSearchStatistics
                                    {formationSearchEqualityTransportSteps = fromIntegral (length steps)})
                                construct (applyWholeEqualitySubstitutionsWithLimits charge limits
                                    ((\edge -> (edge,predicate)) <$> aligned) reflexive formula witness)
                        publishIntroduction identifier result
            FormationGoal.ExistentialGoal{} -> pure IntroductionComplete

    -- Admit explicit positive equalities exactly where ordinary source syntax
    -- supplies them. Atomic encodings and unopened binders are opaque here.
    introducedEqualities path formula expression = do
        charge 1
        case expression of
            SourceAnd a b -> case splitScopedConjunction formula of
                Just (left,right) -> (<>)
                    <$> introducedEqualities (path . ConjunctionLeft) left a
                    <*> introducedEqualities (path . ConjunctionRight) right b
                Nothing -> impossible "an introduced conjunction lost its source spine"
            SourceResidual{} -> equality
            SourceInputs{} -> equality
            SourceWithInputs _ body -> introducedEqualities path formula body
            _ -> pure []
      where
        equality = case splitScopedEquality formula of
                Just (TySet,left,right) -> pure [setSourceEqualityOccurrence
                    (SourceTerm.sourceTermOccurrence left TySet (LocatedSourceTerm location))
                    (SourceTerm.sourceTermOccurrence right TySet (LocatedSourceTerm location))
                    formula (path ConjunctionHere) location]
                _ -> pure []

    prepareIntroductionGoal current formula plan = case FormationGoal.goalOperation plan of
        FormationGoal.AtomicGoal assertion -> do
            aliases <- core (\work -> countedFormationAliasSources work consumer
                (binderStackTypes (lexicalBinderStack (elaborationScope current))) (elaborationProofSupport current)
                (formationScopeAliases (lexicalFormationScope (elaborationScope current))))
            (atom,restore) <- prepareGoal current aliases (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion)
            pure (AtomicLeaf atom,restore)
        _ -> do
            request <- describeWholePlan current (WholeNotionGoal formula (FormationGoal.goalEvidence plan)) (Just plan)
            pure (WholeLeaf request,pure)

    inspectIntroduction (goal,restore) = do
        session <- currentSession
        result <- FormationEvaluation.queryRuleSession goal session
        case result of
            Left _ -> impossible "an admitted introduction goal was rejected"
            Right (answer,next) -> do
                State.modify' (\owner -> owner {registeredSession = Just next})
                traverse (restore . snd . FormationEvaluation.ruleAnswerWitness) answer

    combineIff identifier formula leftGoal knownFirst rightGoal knownSecond = do
        left <- maybe (inspectIntroduction leftGoal) (pure . Just) knownFirst
        right <- maybe (inspectIntroduction rightGoal) (pure . Just) knownSecond
        case (left,right) of
            (Just a,Just b) -> construct (composeFormationEvidence charge formula
                (FormationPremiseEvidenceIff formula (FormationPremiseEvidenceLeaf a) (FormationPremiseEvidenceLeaf b)))
                    >>= publishIntroduction identifier
            _ -> pure ((if isJust left /= isJust knownFirst || isJust right /= isJust knownSecond
                then IntroductionRunnable else IntroductionWaiting)
                (combineIff identifier formula leftGoal left rightGoal right))

    weakenRoot current = \case
        AtomicLeaf atom -> AtomicLeaf <$> traverse (\term -> core (\work ->
            SourceTerm.countedShiftCanonicalSourceTermOccurrence work 1 0 term)) atom
        WholeLeaf goal -> do
            formula <- core (\work -> countedWeakenCheckedScopedCore work TySet (wholeGoalFormula goal))
            evidence <- SourceEvidence.traverseSourceAtDepth
                (\depth -> traverse (\term -> core (\work -> countedShiftCanonical work 1 depth term))) (\depth assertion -> do
                let context = replicate (fromIntegral depth) TySet <> (TySet :
                        binderStackTypes (lexicalBinderStack (elaborationScope current)))
                    align value = core (\work -> countedAlignScopedCoreAt work depth context value)
                        >>= maybe (impossible "a goal description escaped its binder") pure
                    term value = core (\work -> SourceTerm.countedAlignScopedSourceTermOccurrenceAt work depth context value)
                        >>= maybe (impossible "a goal operand escaped its binder") pure
                traverseSourceNotionAssertionParts term align assertion) (wholeGoalEvidence goal)
            pure (WholeLeaf (WholeNotionGoal formula evidence))

    -- The child state is captured existentially by its continuation. Only a
    -- materialized introduction recipe crosses this nominal arena boundary.
    startChild child inherited seeds introduction identifier formula goal =
        pure (IntroductionRunnable (openChild child inherited seeds introduction identifier formula goal))

    openChild child inherited seeds introduction identifier formula goal = withFormationWitnessArena \arena -> do
        charge 1
        leaves <- SourceEvidence.notionLeaves (charge 1) (\_ _ -> pure ()) ()
            (wholeGoalFormula goal) (wholeGoalEvidence goal)
        annotations <- SourceEvidence.sourceInputAnnotationsWith (charge 1) (wholeGoalEvidence goal)
        let root view = case SourceEvidence.sourceLeafDescription view of
                SourceEvidence.LeafAtom assertion -> AtomicLeaf (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion)
                _ -> WholeLeaf (WholeNotionGoal (SourceEvidence.sourceLeafFormula view) (SourceEvidence.sourceLeafEvidence view))
            roots = requested : (root <$> leaves) <> annotationInputRoots (wholeGoalFormula goal) annotations <> inherited
            requested = case sourceEvidenceBody (wholeGoalEvidence goal) of
                SourceAtom assertion -> AtomicLeaf (SourceTerm.forgetScopedSourceTermOccurrence <$> sourceAssertionAtom assertion)
                _ -> WholeLeaf goal
        ((step,state),nextChild) <- State.lift (inChild child
            (startRegisteredLeafState arena Nothing roots seeds consumer location requested))
        pure (IntroductionRunnable (advanceChild nextChild state step introduction identifier formula))

    inChild :: ElaborationState -> FormationQuery value -> FormationQuery (value, ElaborationState)
    inChild child action = do
        parent <- formationElaborate State.get
        formationElaborate (State.put child)
        result <- action
        next <- formationElaborate State.get
        formationElaborate (State.put parent)
        pure (result,next)

    advanceChild :: ElaborationState -> RegisteredFormationState child -> RegisteredQueryStep child
        -> FormationIntroduction FormationSourceOrigin -> FormationFormulas.FormulaId -> ScopedCheckedCore ObjectId
        -> RegisteredFormationSearch scope (IntroductionStep scope)
    advanceChild child state step introduction identifier formula = case step of
        RegisteredFinished (Left _) -> pure IntroductionComplete
        RegisteredFinished (Right witness) -> do
            limits <- formationSearchBudgetLimits <$> State.lift State.get
            (selected,_) <- State.lift (runFormationConstruction recordFormationAllocation
                (selectFormationEvidence (chargeFormationWork location) limits witness) (registeredArena state))
            evidence <- checked selected
            let align parent = case introduction of
                    FormationAssumptionIntroduction{} -> pure parent
                    FormationSetIntroduction -> core (\work -> countedInstantiateScopedPrefix work 1 Map.empty parent) >>= \case
                        ScopedInstantiationClosed result -> pure result
                        ScopedInstantiationOpen{} -> impossible "a fresh goal binder escaped its introduction"
            construct (introduceFormationEvidence charge align introduction formula evidence)
                >>= publishIntroduction identifier
        RegisteredPending action -> do
            ((next,updated),nextChild) <- State.lift (inChild child (State.runStateT action state))
            pure (IntroductionRunnable (advanceChild nextChild updated next introduction identifier formula))

    prepareSelection current aliases goal = do
        charge 1
        State.gets registeredSelection >>= \case
            Just selection -> do
                State.lift (State.modify' (recordFormationOperation FormationDiagnostics.SelectionReuse 1))
                report "selection-reused"
                pure selection
            Nothing -> do
                selection <- selectProblem current aliases goal
                charge 1
                State.modify' (\state -> state {registeredSelection = Just selection})
                State.lift (State.modify' (recordFormationOperation FormationDiagnostics.SelectionPreparation 1))
                pure selection

    selectProblem current aliases goal = do
        (FormationScopeCatalogs _ allSources definitionSources proofSources, _) <- queryCatalogs
        let baseCatalog = case consumer of
                FormationNotionQuery -> allSources
                DefinitionResultNotionQuery -> definitionSources
                ProofNotionQuery -> proofSources
        let preparedIndex = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
            suppliedProducers = evidenceProducers preparedIndex
        eliminations <- fmap concat $ for groupRoots' \case
            AtomicLeaf{} -> pure []
            WholeLeaf requested -> do
                leaves <- State.gets registeredLeaves
                let formula = wholeGoalFormula requested
                    types = binderStackTypes (lexicalBinderStack (elaborationScope current))
                (projections,introductions,next) <- core (\work -> ScopedSource.compileScopedEliminations work types
                    (scopedCoreContext formula) (scopedCoreTerm formula) (wholeGoalEvidence requested) leaves)
                State.modify' (\state -> state {registeredLeaves = next})
                pure ((WholeFormationElimination <$> projections) <> (ScopedFormationIntroduction Nothing <$> introductions))
        let localProducers = suppliedProducers Seq.>< Seq.fromList eliminations
        catalog <- FormationCatalog.insertRules charge
            [(Right (FormationCatalog.LocalProducerIx identifier),FormationRule.RegisteredClassification
                (scopedProducerRule producer))
                | (identifier,producer) <- zip [Seq.length suppliedProducers..] eliminations] baseCatalog
        preparationWork <- elaborate (State.lift (Trans.lift Declaration.formationPreparationWorkLowering))
        report ("owner-preparation=" <> Text.pack (show preparationWork))
        preparationCounts <- elaborate (State.lift (Trans.lift Declaration.formationPreparationDiagnosticsLowering))
        let (visited,interned) = FormationCatalog.templatePreparationCounts catalog
        report ("owner-counts=" <> Text.pack (show (FormationDiagnostics.countOperation FormationDiagnostics.TemplateVisit visited
            (FormationDiagnostics.countOperation FormationDiagnostics.TemplateInterned interned preparationCounts))))
        roots <- if length groupRoots' <= 1 then pure [goal] else for groupRoots' \case
            AtomicLeaf atom -> AtomicLeaf . fst <$> prepareGoal current aliases atom
            WholeLeaf whole -> WholeLeaf <$> describeWholeGoal current whole
        report ("goal=" <> summary (FormationRequest.wholeRequestFormula <$> goal) <> " registrations=" <> Text.pack (show (FormationCatalog.catalogSize catalog)))
        let prepareSnapshot = do
                report "prepared-snapshot-start"
                heads <- fmap concat $ for roots \case
                    AtomicLeaf atom -> do
                        formula <- atomicFormula current atom
                        shape <- formulaShape current formula
                        pure [AtomicLeaf (FormationRule.atomSignature atom), WholeLeaf shape]
                    WholeLeaf requestedWhole -> do
                        plans <- State.gets registeredWholeGoals
                        let identifier = FormationRequest.wholeRequestFormula requestedWhole
                            types = binderStackTypes (lexicalBinderStack (elaborationScope current))
                        charge (FormationTerms.indexWork (Map.size plans) 1)
                        case Map.lookup identifier plans of
                            Nothing -> (\shape -> [WholeLeaf shape]) <$> formulaShape current identifier
                            Just (_,plan) -> do
                                (_,dependencies) <- FormationGoal.foldGoal (\depth formula assertion children -> do
                                    shape <- FormationFormulas.residualShapeFromChildren (charge 1)
                                        (replicate (fromIntegral depth) TySet <> types) formula (fst <$> children)
                                    let own = WholeLeaf shape : [AtomicLeaf (FormationRule.atomSignature (sourceAssertionAtom atom)) | atom <- toList assertion]
                                    pure (shape,(own <>) . foldr ((.) . snd) id children)) plan
                                pure (dependencies [])
                prepared <- FormationCatalog.selectSnapshotHeads charge heads catalog
                snapshot <- either (const (impossible "an admitted formation definition snapshot is invalid")) pure prepared
                let FormationRule.SnapshotCounts selected edges views = FormationRule.snapshotCounts snapshot
                State.lift (consume emptyFormationSearchStatistics
                    { formationSearchRelevantViews = fromIntegral selected
                    , formationSearchRelevantHeadEdges = fromIntegral edges
                    })
                report ("general-snapshot selected=" <> Text.pack (show selected)
                    <> " heads=" <> Text.pack (show (Set.size (FormationRule.snapshotHeads snapshot)))
                    <> " forward-views=" <> Text.pack (show views))
                pure (snapshot,heads)
        (snapshot,rootHeads) <- prepareSnapshot
        pure PreparedFormationSelection
            { selectedFormationCatalog = catalog
            , selectedFormationSnapshot = snapshot
            , selectedFormationProducers = localProducers
            , selectedFormationRoots = roots
            , selectedFormationHeads = rootHeads
            }

    prepareSearch current aliases goal = do
        selection <- prepareSelection current aliases goal
        let catalog = selectedFormationCatalog selection
            snapshot = selectedFormationSnapshot selection
            localProducers = selectedFormationProducers selection
            roots = selectedFormationRoots selection
            rootHeads = selectedFormationHeads selection
            preparedIndex = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
            suppliedSources = evidenceSupplied preparedIndex
            lookupProducer (FormationCatalog.LocalProducerIx identifier) = do
                charge (FormationTerms.indexWork (Seq.length localProducers) 1)
                maybe (impossible "a scoped formation producer escaped its owner") pure
                    (Seq.lookup identifier localProducers)
        let index = formationScopeEvidence (lexicalFormationScope (elaborationScope current))
        postings <- foldM (\retained signature -> do
            charge (FormationTerms.indexWork (Map.size (evidenceHeads index)) 1)
            let selected = Map.findWithDefault Map.empty signature (evidenceHeads index)
            charge (fromIntegral (Map.size selected) * FormationTerms.indexWork (Map.size retained) 1)
            pure (Map.union retained selected)) Map.empty
            (Set.toAscList (FormationRule.snapshotHeads snapshot))
        observations <- selectedObservations current postings
        State.modify' (\state -> state {registeredSearchObservations = fst <$> observations})
        facts <- for observations \(observation, (root, path)) -> do
            let assertion = formationObservationAssertion observation
            evidence <- construct (directPreparedFormationEvidence charge
                (groundNotionKeyFromTemplate (scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$> sourceAssertionAtom assertion))
                root path (formationObservationOrdinal observation))
            (normalizedAssertion, aliasDependencies, normalizedEvidence) <- normalizeObservation aliases assertion evidence
            leaves <- State.gets registeredLeaves
            (row, nextLeaves) <- core (\work -> FormationRows.encodeSourceRow work
                (binderStackTypes (lexicalBinderStack (elaborationScope current))) normalizedAssertion leaves)
            State.modify' (\state -> state {registeredLeaves = nextLeaves})
            charge (FormationTerms.indexWork (Set.size aliasDependencies) 1)
            let origins = Set.insert (ObservedFormationDependency (formationObservationOrdinal observation)) aliasDependencies
            key <- internAnswer row False
            retained <- retainWitness key origins (pure normalizedEvidence)
            pure (FormationEvaluation.RuleAnswer (AtomicLeaf row) key
                FormationJoin.SourceRow retained)
        report "query-prepared"
        -- Source equality endpoints are part of this query's fixed support,
        -- not syntax discovered from later mathematical answers.
        endpointTerms <- if scopedOrdinaryEqualities
                (consumerEqualities consumer (formationScopeEvidence (lexicalFormationScope (elaborationScope current)))) == 0
            then pure [] else do
                _ <- equalityGraph current
                cached <- State.gets registeredEqualities
                pure (maybe [] runtimeEqualityTerms cached)
        let suppliedWhole signature shape = do
                let shapes = evidenceWholeShapes preparedIndex
                    bucket = Map.findWithDefault [] (FormationFormulas.residualShapeHash shape) shapes
                charge (FormationTerms.indexWork (Map.size shapes) 1
                    + fromIntegral (length bucket) * FormationFormulas.residualShapeWork shape)
                if FormationFormulas.residualShapeIntroducible shape then pure True else
                    foldM (\found (candidate,views,_) -> if found || candidate /= shape then pure found else do
                        charge (maybe 0 (\heads -> FormationTerms.indexWork (Set.size heads) 3) views)
                        -- An existing row covers its own signature. Other exact
                        -- spellings still need finite discovery when no row of
                        -- the requested signature exposes their operands.
                        pure (maybe True (\heads -> Set.size heads > 1 || Set.notMember signature heads) views))
                        False bucket
        let matchWhole pattern' identifier = do
                table <- formulaTable current
                target <- State.lift (formationFormulaWork location (\work ->
                    FormationFormulas.lookupFormula work identifier table))
                    >>= maybe (impossible "a whole matcher escaped its formula owner") pure
                values <- WholePattern.matchWholePattern charge pattern' (scopedCoreTerm target)
                traverse (traverse (internEqualityTerm current)) values
        let graph = scopedEqualityGraph (consumerEqualities consumer preparedIndex)
            argumentClass value = FormationEqualities.representative charge value graph
            equalityMembers value = FormationEqualities.classMembers charge value graph
        let firstHole = fromIntegral (length (binderStackTypes (lexicalBinderStack (elaborationScope current))))
            partialOperand template = do
                leaves <- State.gets registeredLeaves
                allowance <- available
                result <- elaborate (interpretFormationTemplate allowance location
                    (\work -> \case
                        Nothing -> pure (Right (CBound firstHole),work)
                        Just identifier -> let (found,remaining) = FormationLeaves.countedLookupOpaqueLeaf work identifier leaves
                            in case found of
                                Left FormationLeaves.OpaqueLeafWorkExhausted -> pure (Left CountedCoreStructuralWorkExhausted,remaining)
                                Right (Just value) -> pure (Right (scopedCoreTerm value),remaining)
                                _ -> impossible "a partial operand escaped its query") template)
                coreResult allowance result
            partialInputs = fmap (maybe (TemplateVariable Nothing) (fmap Just))
            partialFormulaInputs rule residual values = do
                let (arity,_,_) = FormationRule.ruleDescription rule
                    ambient = FormationRule.ruleAmbientTypes rule
                    difference = fromIntegral firstHole - length ambient
                formula <- if null ambient then pure (residualTemplateFormula residual) else do
                    when (difference < 0) (impossible "a partial formula escaped its lexical scope")
                    core (\work -> countedShiftCanonical work (fromIntegral difference) arity (residualTemplateFormula residual))
                arguments <- Map.fromDistinctAscList <$> for (take (fromIntegral arity) [0..]) (\slot -> do
                    charge (FormationTerms.indexWork (Map.size values) 1)
                    value <- maybe (pure (CBound firstHole)) partialOperand (Map.lookup (ViewVariableIx slot) values)
                    pure (slot,value))
                pure (arity,formula,arguments)
            partialFormula rule residual values = do
                (arity,formula,arguments) <- partialFormulaInputs rule residual values
                core (\work -> countedInstantiateCanonicalSlots work arity arguments formula)
            preparePartialComparison rule residual values slot@(ViewVariableIx slotIndex) target = do
                (arity,formula,arguments) <- partialFormulaInputs rule residual (Map.delete slot values)
                -- This fresh outer slot identifies only the cursor's varying
                -- parameter; all other unknown operands use firstHole.
                let varying = firstHole+1
                charge (FormationTerms.indexWork (Map.size arguments) 1)
                template <- core (\work -> countedInstantiateCanonicalSlots work arity
                    (Map.insert slotIndex (CBound varying) arguments) formula)
                comparison <- WholePattern.prepareOperandComparison charge firstHole varying template target
                pure (\partial -> comparison (partialOperand partial))
        let owner = FormationEvaluation.RuleEvaluator
                { FormationEvaluation.ruleInputs = \ordinal -> do
                    charge (FormationTerms.indexWork (FormationCatalog.catalogSize catalog) 1)
                    case FormationCatalog.lookupSource ordinal catalog of
                        Just (Left _) -> pure FormationRule.OpenRuleInputs
                        Just (Right producerIndex) -> do
                            captures <- scopedProducerCaptures <$> lookupProducer producerIndex
                            pure (FormationRule.ScopedRuleInputs captures)
                        Nothing -> impossible "a formation producer lost its input policy"
                , FormationEvaluation.ruleCharge = charge
                , FormationEvaluation.ruleGroundBucket = traverseAtomTemplateArguments
                    (\term -> argumentValue current term >>= argumentClass)
                , FormationEvaluation.rulePhase = report
                , FormationEvaluation.ruleEvent = \case
                    FormationDiagnostics.Count operation amount ->
                        State.lift (State.modify' (recordFormationOperation operation amount))
                    FormationDiagnostics.EnterRegistration ordinal -> do
                        charge (FormationTerms.indexWork (FormationCatalog.catalogSize catalog) 1)
                        source <- maybe (impossible "a formation activity lost its registration") pure
                            (FormationCatalog.lookupSource ordinal catalog)
                        State.lift (State.modify' (setFormationRegistrationFamily (Just (either formationRuleFamily (const FormationDiagnostics.SuppliedUniversalFamily) source))))
                    FormationDiagnostics.LeaveRegistration ->
                        State.lift (State.modify' (setFormationRegistrationFamily Nothing))
                , FormationEvaluation.ruleCompleted = \ordinal completed resultLeaf -> do
                    charge 1
                    charge (FormationTerms.indexWork (FormationCatalog.catalogSize catalog) 1)
                    taggedSource <- maybe (impossible "a completed formation rule lost its registration") pure (FormationCatalog.lookupSource ordinal catalog)
                    source <- traverse lookupProducer taggedSource
                    let instantiation = FormationRule.completedInstantiation completed
                    substitution <- Map.fromDistinctAscList <$> traverse (\(ViewVariableIx variable, term) ->
                        (\value -> (variable, value)) <$> interpret term) (Map.toAscList (FormationRule.ruleBinderValues instantiation))
                    conclusion <- case resultLeaf of
                        AtomicLeaf atom -> AtomicLeaf <$> traverseAtomTemplateArguments interpret atom
                        WholeLeaf identifier -> do
                            table <- formulaTable current
                            WholeLeaf <$> (State.lift (formationFormulaWork location (\work -> FormationFormulas.lookupFormula work identifier table))
                                >>= maybe (impossible "a whole result lost its checked formula") pure)
                    premises <- traverse premise (FormationRule.completedPremises completed)
                    premiseOrigins <- foldM mergeOrigins Set.empty (fst <$> premises)
                    (origins, build) <- case source of
                        Left registered -> pure (premiseOrigins, construct (applyFormationRule charge registered substitution
                            (snd <$> premises) conclusion))
                        Right (ScopedFormationProducer sourceIdentifier projection) -> do
                            retained <- alignUniversal current sourceIdentifier
                            let build = construct (applyProjectedSource charge retained
                                    (ScopedSource.scopedProjectionPlan projection) substitution (snd <$> premises) conclusion)
                            dependencies <- universalDependencies retained
                            origins <- mergeOrigins premiseOrigins dependencies
                            pure (origins,build)
                        Right (WholeFormationElimination projection) -> pure (premiseOrigins,
                            construct (applyProjectedEvidence charge (ScopedSource.scopedProjectionPlan projection)
                                substitution (snd <$> premises) conclusion))
                        Right (ScopedFormationIntroduction _ introduction) -> pure (premiseOrigins,
                            construct (applyIntroductionRule charge (ScopedSource.scopedIntroductionPlan introduction)
                                substitution (snd <$> premises) conclusion))
                    key <- case resultLeaf of
                        AtomicLeaf atom -> internAnswer atom False
                        WholeLeaf identifier -> internAnswerKey (WholeLeaf identifier) True
                    retained <- retainWitness key origins build
                    let sourceBranch = case source of
                            Right _ -> Nothing
                            Left registered -> Just (formationRuleSourceBranch registered)
                    for_ sourceBranch (chargeSelector . semanticFactBranchPath)
                    report ("rule-completed source=" <> maybe "supplied-universal" (Text.pack . show . semanticFactBranchFact) sourceBranch <> " ordinal=" <> Text.pack (show ordinal)
                        <> " binder-count=" <> Text.pack (show (Map.size (FormationRule.ruleBinderValues instantiation)))
                        <> " premises=" <> Text.pack (show (length premises))
                        <> " origin-count=" <> Text.pack (show (Set.size origins)))
                    pure (Just (key, retained))
                , FormationEvaluation.ruleConverted = \requestedRow answer -> do
                    expected <- traverseAtomTemplateArguments interpret requestedRow
                    let (origins, evidence) = FormationEvaluation.ruleAnswerWitness answer
                    converted <- case FormationEvaluation.ruleAnswerLeaf answer of
                        WholeLeaf identifier -> do
                            target <- elaborate (deriveNotionAtomProposition location expected)
                            actual <- internFormula current target
                            pure $ if actual == identifier then Just (origins,
                                construct (convertFormationEvidence charge target evidence expected)) else Nothing
                        AtomicLeaf{} -> do
                            matches <- maybe (pure False) (sameAtom expected) (groundNotionKeyTemplate (formationWitnessGroundKey evidence))
                            if matches then pure (Just (origins, pure evidence))
                                else transportAnswer current expected origins evidence
                    for converted \(dependencies, build) -> do
                        -- Exact transport does not supply new source occurrences.
                        key <- internAnswer requestedRow True
                        retained <- retainWitness key dependencies build
                        pure (key, retained)
                , FormationEvaluation.ruleArgumentClass = \value -> do
                    key <- argumentClass value
                    members <- equalityMembers value
                    pure (key,Set.size members > 1)
                , FormationEvaluation.ruleHasEqualityTransport =
                    scopedOrdinaryEqualities (consumerEqualities consumer preparedIndex) /= 0
                , FormationEvaluation.ruleRejected = \_ -> pure ()
                , FormationEvaluation.ruleWholeRequest = \ordinal position values template -> do
                    charge (FormationTerms.indexWork (FormationCatalog.catalogSize catalog) 1)
                    rule <- maybe (impossible "a whole instance lost its admitted clause") (pure . FormationRule.registeredRule)
                        (FormationCatalog.lookupRule ordinal catalog)
                    prepareWholeRequest current ordinal position rule values template
                , FormationEvaluation.ruleWholeEvidence = \requested -> do
                    found <- wholeEvidence current suppliedSources requested
                    when (isNothing found && FormationRequest.wholeRequestIntroducible requested) (requestIntroduction current requested)
                    pure found
                , FormationEvaluation.ruleWholeBindings = \rule waiting -> case FormationRule.wholeWaitingTemplate waiting of
                    WholeResidual (ResidualTemplate (CEq TySet left right)) -> do
                        let values = FormationRule.wholeWaitingInputs waiting
                            unknown (CBound slotIndex) = case Map.lookup (ViewVariableIx slotIndex) values of
                                Just Nothing -> Just (ViewVariableIx slotIndex)
                                _ -> Nothing
                            unknown _ = Nothing
                            alternatives = [(slot,term) | (candidate,term) <- [(left,right),(right,left)],
                                slot <- maybe [] pure (unknown candidate)]
                        arguments <- Map.mapKeysMonotonic (\(ViewVariableIx slotIndex) -> slotIndex) <$>
                            traverse interpret (Map.mapMaybe id values)
                        let (arity,_,_) = FormationRule.ruleDescription rule
                            ambient = FormationRule.ruleAmbientTypes rule
                            difference = length (binderStackTypes (lexicalBinderStack (elaborationScope current))) - length ambient
                            attempt [] = pure Nothing
                            attempt ((slot,term):rest) = do
                                template <- if null ambient then pure term else
                                    core (\work -> countedShiftCanonical work (fromIntegral difference) arity term)
                                endpoint <- core (\work -> let (result,remaining) = countedInstantiateCanonicalSlots work arity arguments template
                                    in (case result of
                                        Right value -> Right (Just value)
                                        Left CountedCoreStructuralWorkExhausted -> Left CountedCoreStructuralWorkExhausted
                                        Left (CountedCoreOperationFailed _) -> Right Nothing,remaining))
                                case endpoint of
                                    Nothing -> attempt rest
                                    Just term' -> do
                                        identifier <- internEqualityTerm current term'
                                        members <- equalityMembers identifier
                                        charge (fromIntegral (Set.size members))
                                        pure (Just (slot,TemplateVariable <$> Set.toAscList members))
                        attempt alternatives
                    _ -> pure Nothing
                , FormationEvaluation.ruleWholeCandidates = \active shape ->
                    Just . uncurry FormationEvaluation.WholeCandidates <$> FormationCatalog.matchingWholeRules charge active shape catalog
                , FormationEvaluation.ruleFormulaShape = formulaShape current
                , FormationEvaluation.ruleWholeSources = \shape -> do
                    let shapes = evidenceWholeShapes preparedIndex
                        bucket = Map.findWithDefault [] (FormationFormulas.residualShapeHash shape) shapes
                    charge (FormationTerms.indexWork (Map.size shapes) 1)
                    fmap concat $ for bucket \(candidate,_views,identifiers) -> do
                        charge (FormationFormulas.residualShapeWork shape)
                        if candidate /= shape then pure [] else do
                            charge (fromIntegral (Set.size identifiers))
                            pure (Set.toAscList identifiers)
                , FormationEvaluation.ruleAtomicFormula = fmap Just . atomicFormula current
                , FormationEvaluation.ruleWholeTruthAvailable = \signature ->
                    FormationCatalog.atomicWholeTruthPossible charge (suppliedWhole signature) signature catalog
                , FormationEvaluation.ruleSourcePossible = \active head' known ->
                    FormationCatalog.possibleSource charge (\case
                        AtomicLeaf signature -> do
                            charge (FormationTerms.indexWork (Set.size active) 3)
                            pure (Set.member signature active)
                        WholeLeaf shape -> do
                            let shapes = evidenceWholeShapes preparedIndex
                                bucket = Map.findWithDefault [] (FormationFormulas.residualShapeHash shape) shapes
                            charge (FormationTerms.indexWork (Map.size shapes) 1)
                            foldM (\found (candidate,_,identifiers) -> if found then pure True else do
                                charge (FormationFormulas.residualShapeWork shape)
                                pure (candidate == shape && not (Set.null identifiers))) False bucket)
                        head' catalog known
                , FormationEvaluation.ruleOpaqueIsRigid = \value -> do
                    term <- interpret value
                    case term of
                        CBound{} -> do
                            identifier <- internEqualityTerm current term
                            members <- equalityMembers identifier
                            pure (Set.size members == 1)
                        _ -> pure False
                , FormationEvaluation.ruleArgumentValue = fmap Just . argumentValue current
                , FormationEvaluation.ruleMatchWhole = matchWhole
                , FormationEvaluation.ruleMatchPartialWhole = \consumerRule waiting producer values ->
                    case FormationRule.ruleExactConclusion producer of
                        Nothing -> pure (Just Map.empty)
                        Just conclusion -> do
                            requested <- partialFormula consumerRule (FormationRule.wholeWaitingDescription waiting)
                                (partialInputs (FormationRule.wholeWaitingInputs waiting))
                            candidate <- partialFormula producer conclusion values
                            possible <- WholePattern.mayEqualOperands charge firstHole requested candidate
                            if not possible then pure Nothing else case FormationRule.ruleConclusionPattern producer of
                                Nothing -> pure (Just Map.empty)
                                Just pattern' -> do
                                    matched <- WholePattern.matchPartialWholePattern charge firstHole pattern' requested
                                    let (arity,_,_) = FormationRule.ruleDescription producer
                                    traverse (traverse (internEqualityTerm current) . Map.filterWithKey
                                        (\(ViewVariableIx slot) _ -> slot < arity)) matched
                , FormationEvaluation.rulePreparePartialWhole = \consumerRule waiting producer values slot ->
                    case FormationRule.ruleExactConclusion producer of
                        Nothing -> pure (const (pure True))
                        Just conclusion -> do
                            requested <- partialFormula consumerRule (FormationRule.wholeWaitingDescription waiting)
                                (partialInputs (FormationRule.wholeWaitingInputs waiting))
                            compatible <- case FormationRule.ruleConclusionPattern producer of
                                Nothing -> pure True
                                Just pattern' -> isJust <$> WholePattern.matchPartialWholePattern charge firstHole pattern' requested
                            if not compatible then pure (const (pure False)) else
                                preparePartialComparison producer conclusion values slot requested
                , FormationEvaluation.rulePrepareWholeMatch = \rule description values slot identifier -> do
                    table <- formulaTable current
                    target <- State.lift (formationFormulaWork location (\work ->
                        FormationFormulas.lookupFormula work identifier table))
                        >>= maybe (impossible "a partial match escaped its formula owner") pure
                    preparePartialComparison rule description values slot (scopedCoreTerm target)
                , FormationEvaluation.ruleAtomicInputs = \atom identifier -> do
                    -- Give each complete operand its own formal slot. Matching
                    -- this head describes positions independently of any rule's
                    -- constructor pattern or clause-variable numbering.
                    let prototype = State.evalState (traverse (const (State.state
                            (\slot -> (CBound slot,slot+1)))) atom) 0
                    formula <- elaborate (deriveNotionAtomCore location prototype)
                    pattern' <- WholePattern.compileWholePattern charge (fromIntegral (length (toList atom))) formula
                    fmap (Map.mapKeysMonotonic (\(ViewVariableIx slot) -> fromIntegral slot)) <$> matchWhole pattern' identifier
                , FormationEvaluation.ruleTermsMayAgree = \left right -> do
                    a <- partialOperand left
                    b <- partialOperand right
                    direct <- WholePattern.mayEqualOperands charge firstHole a b
                    -- With no supplied equations, incompatible constructors
                    -- stay incompatible even when both operands have holes.
                    if direct || scopedOrdinaryEqualities (consumerEqualities consumer preparedIndex) == 0
                      then pure direct else do
                        -- Only complete operands participate in E. A partial
                        -- constructor may match an endpoint, but this Boolean
                        -- filter never extracts a binding from opaque Core.
                        let complete = all isJust . toList
                            against partialCore concreteCore = do
                                identifier <- internEqualityTerm current concreteCore
                                members <- equalityMembers identifier
                                foldM (\found member -> if found then pure True else do
                                    endpoint <- interpret (TemplateVariable member)
                                    WholePattern.mayEqualOperands charge firstHole partialCore endpoint)
                                    False (Set.toAscList members)
                        if complete right then against a b
                        else if complete left then against b a
                        else pure True
                , FormationEvaluation.ruleOpaqueSupport = Just (opaqueSupport current)
                , FormationEvaluation.ruleSupportTemplates = supportTemplates current
                }
        extraTerms <- traverse (encodeGoal current) groupSeeds
        let collectInputs (formula,evidence) = do
                leaves <- State.gets registeredLeaves
                let types = binderStackTypes (lexicalBinderStack (elaborationScope current))
                (inputs,next) <- core (\work -> ScopedSource.scopedSourceInputs
                    (elaborationGlobalTyping current) work types (scopedCoreContext formula)
                    (scopedCoreTerm formula) evidence leaves)
                State.modify' (\state -> state {registeredLeaves = next})
                pure inputs
        rootInputs <- fmap concat $ for groupRoots' \case
            AtomicLeaf{} -> pure []
            WholeLeaf requested -> collectInputs (wholeGoalFormula requested,wholeGoalEvidence requested)
        -- This action closes over the original scope and clause snapshot.
        -- Initial proof discovery may allocate values, but cannot add inputs.
        let prepareInputs = do
                State.lift (State.modify' (recordFormationOperation FormationDiagnostics.SourceInputMaterialization 1))
                report "source-inputs-start"
                -- Select whole-source postings by the same semantic dependency heads
                -- that own the frozen templates. Optional input filters cannot narrow B.
                let ruleHeads = concat [FormationRule.ruleSignature rule :
                        (FormationRule.rulePremiseSignatures rule <> (WholeLeaf . snd <$> FormationRule.ruleFormulaHeads rule))
                        | entry <- Map.elems (FormationRule.snapshotRules snapshot), let rule = FormationRule.registeredRule entry]
                sourcePostings <- fmap snd $ foldM (\(seen,retained) -> \case
                    AtomicLeaf{} -> pure (seen,retained)
                    WholeLeaf shape -> do
                        let shapes = evidenceWholeShapes preparedIndex
                            shapeHash = FormationFormulas.residualShapeHash shape
                            candidates = Map.findWithDefault [] shapeHash shapes
                        charge (FormationTerms.indexWork (Map.size shapes) 1)
                        -- Only shapes with a possible source need exact comparison.
                        -- Reuse the admission hash buckets; full equality still decides
                        -- membership, including collisions and repeated clause heads.
                        if null candidates then pure (seen,retained) else do
                            charge (FormationTerms.indexWork (Map.size seen) 1)
                            let prior = Map.findWithDefault [] shapeHash seen
                            duplicate <- foldM (\found candidate -> if found then pure True else do
                                charge (max (FormationFormulas.residualShapeWork shape) (FormationFormulas.residualShapeWork candidate))
                                pure (candidate == shape)) False prior
                            if duplicate then pure (seen,retained) else do
                                charge (FormationTerms.indexWork (Map.size seen) 1)
                                found <- foldM (\known (candidate,_views,identifiers) -> do
                                    charge (FormationFormulas.residualShapeWork shape)
                                    if candidate /= shape then pure known else foldM (\selected identifier -> do
                                        charge (FormationTerms.indexWork (Map.size (evidenceWhole preparedIndex)) 1)
                                        let observations' = Map.findWithDefault Map.empty identifier (evidenceWhole preparedIndex)
                                        charge (fromIntegral (Map.size observations') * FormationTerms.indexWork (Map.size selected) 1)
                                        pure (Map.union selected observations')) known (Set.toAscList identifiers)) retained candidates
                                pure (Map.insert shapeHash (shape:prior) seen,found)) (Map.empty,Map.empty) (rootHeads <> ruleHeads)
                -- One parent owns annotations across all its projected leaves.
                -- Select it only when a leaf is relevant, and collect it once.
                inputOwners <- foldM (\owners (key,observation) -> do
                    charge 1
                    case observation of
                        WholeFormationObservation _ origin _ _ (Just inputs) -> do
                            charge (FormationTerms.indexWork (Map.size owners) 1)
                            pure (Map.insert (fst key) (origin,inputs) owners)
                        _ -> pure owners) Map.empty (Map.toAscList sourcePostings)
                annotationInputs <- fmap concat $ for (Map.elems inputOwners) \(origin,inputs) -> do
                    charge 1
                    if notionQueryAdmitsOrigin consumer origin then collectInputs inputs else pure []
                sourceInputs <- fmap concat $ for (Map.elems sourcePostings) \(WholeFormationObservation _ origin _ inputs _inputOwner) -> do
                    charge 1
                    hasSelectedRow <- case snd inputs of
                        SourceAtom assertion -> do
                            let heads = FormationRule.snapshotHeads snapshot
                            charge (FormationTerms.indexWork (Set.size heads) 3)
                            pure (Set.member (FormationRule.atomSignature (sourceAssertionAtom assertion)) heads)
                        _ -> pure False
                    if notionQueryAdmitsOrigin consumer origin && not hasSelectedRow then collectInputs inputs else pure []
                report "source-inputs-finished"
                pure (endpointTerms <> extraTerms <> rootInputs <> annotationInputs <> sourceInputs)
        FormationEvaluation.initializeCatalogLeaves owner catalog snapshot facts prepareInputs roots goal

resolveProviderFailureSource :: SourceProviderHead -> Elaborate ProviderFailureSource
resolveProviderFailureSource = \case
    GlobalSourceProvider reference -> do
        visible <- State.lift
            (Trans.lift
                (Declaration.resolveVisibleGlobalLowering
                    (globalBindingRefKey reference)))
        case visible of
            Just (binding, _type)
                | resolvedBindingRef binding == reference ->
                    pure (ProviderFailureGlobal binding)
            _ -> impossible
                "a source provider lost its owner-bearing visible binding"
    StructureFieldSourceProvider identity projection ->
        pure (ProviderFailureStructureField identity projection)
    IntrinsicSourceProvider provider ->
        pure (ProviderFailureIntrinsic provider)
    FiniteSetLiteralSourceProvider ->
        pure ProviderFailureFiniteSetLiteral


replaceNotionFocus
    :: term
    -> AtomTemplate term
    -> Maybe (AtomTemplate term)
replaceNotionFocus replacement = \case
    NegativeAtomTemplate body -> withAtomPolarity NegativePolarity <$> replaceNotionFocus replacement body
    GlobalAtomTemplate head' arguments -> do
        guard (globalNotionHeadRole head' == HostedGlobalNotion)
        (_focus, rest) <- Vector.uncons arguments
        pure
            (GlobalAtomTemplate head'
                (Vector.cons replacement rest))
    StructureAtomTemplate head' arguments -> do
        (_focus, rest) <- Vector.uncons arguments
        pure
            (StructureAtomTemplate head'
                (Vector.cons replacement rest))
    MembershipAtomTemplate _element set ->
        pure (MembershipAtomTemplate replacement set)
    ExactStructureAtomTemplate shape _ -> pure (ExactStructureAtomTemplate shape replacement)

deriveNotionFocusPredicate
    :: Location
    -> AtomTemplate CompiledSourceTerm
    -> Elaborate (ScopedCheckedCore ObjectId)
deriveNotionFocusPredicate location atom =
    withAnonymousSetBinder \bound -> do
        let shifted =
                shiftCanonical 1 0 . compiledSourceTermCore <$> atom
        body <-
            maybe
                (impossible "a notion atom has no distinguished term")
                (deriveNotionAtomProposition location)
                (replaceNotionFocus bound shifted)
        maybe
            (impossible "a notion-focus predicate cannot close its binder")
            pure
            (abstractScopedCore TySet body)

-- Interpret mathematical templates, without granting source-call permission.
-- The owner supplies already scoped leaves. Traversal, global-reference scans,
-- type comparisons, and beta substitution share one structural allowance.
interpretFormationTemplate
    :: Word
    -> Location
    -> (Word -> variable -> Elaborate (Either (CountedCoreFailure Void) (CanonicalTerm ObjectId), Word))
    -> SetTermTemplate variable
    -> Elaborate (Either (CountedCoreFailure Void) (CanonicalTerm ObjectId), Word)
interpretFormationTemplate allowance location leaf template =
    State.runStateT (Except.runExceptT (go template)) allowance
  where
    step :: (Word -> (Either (CountedCoreFailure Void) value, Word))
        -> ExceptT (CountedCoreFailure Void) (StateT Word Elaborate) value
    step operation = do
        available <- State.get
        let (result, remaining) = operation available
        State.put remaining
        either Except.throwError pure result
    charge amount = step \available ->
        if amount <= available then (Right (), available - amount)
        else (Left CountedCoreStructuralWorkExhausted, 0)
    elaborate = Trans.lift . Trans.lift
    go term = do
        charge 1
        case term of
            TemplateClosed value -> do
                globals <- step (\available -> countedCanonicalGlobals available (closedSetValueTerm value))
                for_ globals \identity -> do
                    charge 1
                    elaborate (requireNotionQueryGlobals (Set.singleton identity))
                current <- elaborate State.get
                available <- State.get
                let (result,remaining) = countedCheckScopedCanonicalCore
                        (elaborationGlobalTyping current) available [] (closedSetValueTerm value)
                State.put remaining
                case result of
                    Left CountedCoreStructuralWorkExhausted -> Except.throwError CountedCoreStructuralWorkExhausted
                    Left (CountedCoreOperationFailed _) -> impossible "an admitted closed value lost its checked objects"
                    Right checked | scopedCoreType checked == TySet -> pure (scopedCoreTerm checked)
                    Right _ -> impossible "an admitted closed value is no longer a set"
            TemplateVariable variable -> do
                available <- State.get
                (result, remaining) <- elaborate (leaf available variable)
                State.put remaining
                either Except.throwError pure result
            TemplateProvider provider arguments -> traverse go arguments >>= applyProvider provider
            TemplateOrderedPair left right -> do
                left' <- go left
                right' <- go right
                charge 2
                pure (CApp (CApp (CIntrinsic OrderedPair) left') right')

    applyProvider providerHead@(GlobalSourceProvider reference) arguments = do
        charge 1
        let key = globalBindingRefKey reference
        (resolved, content) <- elaborate (resolveVisibleSourceGlobalContent location key)
        unless (resolvedBindingRef resolved == reference
            && resolvedBindingSourceProviderHead resolved == Just providerHead)
            (impossible "a formation template lost its exact global provider")
        (body, coreType) <- case semanticGlobalBindingTarget (resolvedBindingDeclaration resolved) of
            GlobalReference identity -> do
                let expected = objectContentType content
                requireType identity expected
                pure (CGlobal identity, expected)
            TransparentExpansion _ -> case content of
                TransparentObjectContent _ coreType body -> do
                    globals <- step (\available -> countedCanonicalGlobals available body)
                    for_ globals \identity -> do
                        charge 1
                        elaborate (requireNotionQueryGlobals (Set.singleton identity))
                    pure (body, coreType)
                _ -> impossible "a checked formation expansion has opaque content"
            ContextualTransparentExpansion{} ->
                impossible "a formation provider unexpectedly became contextual"
        (term, resultType) <- foldM applyArgument (body, coreType) arguments
        unless (resultType == TySet)
            (impossible "a formation template provider no longer returns a set")
        pure term
    applyProvider (StructureFieldSourceProvider field projection) arguments = do
        charge 1
        visible <- elaborate (State.lift (Trans.lift
            (Declaration.resolveVisibleStructureFieldProviderLowering field)))
        unless (visible == Just projection)
            (impossible "a formation template lost its exact structure field")
        requireType projection (TyArrow TySet TySet)
        case toList arguments of
            [receiver] -> charge 1 >> pure (CApp (CGlobal projection) receiver)
            _ -> impossible "a formation template field has the wrong arity"
    applyProvider (IntrinsicSourceProvider provider) arguments = do
        charge (fromIntegral (Vector.length arguments) + 1)
        pure (fromMaybe (impossible "a formation template intrinsic has the wrong arity")
            (intrinsicProviderApplication provider arguments))
    applyProvider FiniteSetLiteralSourceProvider arguments = do
        for_ arguments (const (charge 4))
        pure (finiteSetLiteralProviderApplication
            (fromMaybe (impossible "a formation template literal has no elements")
                (NonEmpty.nonEmpty (toList arguments))))

    requireType identity expected = do
        charge 1
        typing <- elaborate (State.gets elaborationGlobalTyping)
        actual <- maybe (impossible "a formation provider is absent from its checked closure") pure
            (lookupGlobalType typing identity)
        equal <- step (\available -> countedCoreTypeIdentity available actual expected)
        unless equal (impossible "one exact formation provider acquired two checked types")
    applyArgument (current, currentType) argument = do
        charge 1
        case currentType of
            TyArrow TySet result -> do
                applied <- case current of
                    CLam TySet body -> step (\available -> countedInstantiateCanonical available argument body)
                    _ -> pure (CApp current argument)
                pure (applied, result)
            TyArrow expected _ -> elaborate (Except.throwError
                (ElaborationApplicationArgumentMismatch location expected TySet))
            actual -> elaborate (Except.throwError
                (ElaborationApplicationExpectedFunction location actual))

traverseAtomTemplateArgumentsM
    :: Applicative effect
    => (left -> effect (Maybe right))
    -> AtomTemplate left
    -> effect (Maybe (AtomTemplate right))
traverseAtomTemplateArgumentsM transform atom =
    getCompose (traverse (Compose . transform) atom)

data RichFormationFailure = RichFormationFailure
    { richFormationFailureExplanation
        :: !(FormationFailureExplanation FormationSourceOrigin)
    , richFormationFailureDetail :: !(Maybe RichFormationFailureDetail)
    }
    deriving stock (Show, Eq)

data NotionQueryFailure = NotionQueryFailure
    !(Map StructureId Schema.StructurePhrase)
    !(AtomTemplate SourceTermPresentation)
    !(Maybe SourceEvidence.WrittenOrigin)
    !RichFormationFailure
    !FormationSearchStatistics
    | WholeNotionQueryFailure !(ScopedCheckedCore ObjectId)
        !(Maybe SourceEvidence.WrittenOrigin) !FormationSearchStatistics
    deriving stock (Show, Eq)

notionQueryFailurePath :: NotionQueryFailure -> Maybe ConjunctionPath
notionQueryFailurePath failure = SourceEvidence.writtenOriginBodyPath <$> case failure of
    NotionQueryFailure _ _ origin _ _ -> origin
    WholeNotionQueryFailure _ origin _ -> origin

data NotionQueryOutcome
    = NotionQueryFound
        !(MaterializedFormationEvidence FormationSourceOrigin)
    | NotionQueryUnavailable !NotionQueryFailure
    | NotionQueryUnsupported

data RichFormationFailureDetail
    = RichProviderFormationFailure !ProviderFormationFailure
    | RichNullaryClassificationFailure !NullaryClassificationFailure
    deriving stock (Show, Eq)

data ProviderFailureSource
    = ProviderFailureGlobal !ResolvedGlobalBinding
    | ProviderFailureStructureField !FieldId !ObjectId
    | ProviderFailureIntrinsic !IntrinsicProviderId
    | ProviderFailureFiniteSetLiteral
    deriving stock (Show, Eq)

data ProviderFormationFailure
    = ProviderResultRuleMissing !ProviderFailureSource
    | ProviderResultPremiseMissing
        !ProviderFailureSource
        !(AtomTemplate SourceTermPresentation)
    | ProviderResultUnavailable
        !ProviderFailureSource
        !NotionHeadKey
    deriving stock (Show, Eq)

data NullaryClassificationFailure
    = NullaryClassificationMissing !IntrinsicProviderId
    | NullaryClassificationClosureMissing
        !IntrinsicProviderId
        !SemanticFactOccurrenceFingerprint
        !GlobalNotionHead
    deriving stock (Show, Eq)

notionFocusTerm
    :: AtomTemplate term
    -> Maybe term
notionFocusTerm = \case
    NegativeAtomTemplate body -> notionFocusTerm body
    GlobalAtomTemplate head' arguments -> do
        guard (globalNotionHeadRole head' == HostedGlobalNotion)
        fst <$> Vector.uncons arguments
    StructureAtomTemplate _head arguments -> fst <$> Vector.uncons arguments
    MembershipAtomTemplate element _set -> Just element
    ExactStructureAtomTemplate _ subject -> Just subject

-- Error snapshots carry compact presentation only, separate from semantic heads.
structureDiagnosticNames :: Elaborate (Map StructureId Schema.StructurePhrase)
structureDiagnosticNames = do
    environment <- State.lift (Trans.lift Declaration.structureEnvironmentLowering)
    pure (Map.map (Schema.resolvedSchemaPhrase . StructurePredicate.pendingStructureSchema
        . StructureInterface.structureInterfaceRegistration) (StructureEnvironment.structureEnvironmentInterfaces environment))

diagnosticStructurePhrase :: Map StructureId Schema.StructurePhrase -> SemanticStructureNotionHead -> Schema.StructurePhrase
diagnosticStructurePhrase names head' = fromMaybe
    (impossible "a checked notion diagnostic lost its structure presentation")
    (Map.lookup (structureNotionHeadId head') names)

renderFormationRequirementFailure :: FormationRequirementFailure -> Text
renderFormationRequirementFailure (WholeFormationRequirementFailure binding formula _statistics) =
    let declaration = resolvedBindingDeclaration binding
    in "cannot use \"" <> renderGlobalSurface (semanticGlobalBindingKey declaration)
        <> "\" here. The selected declaration \"" <> semanticBindingLabelText (semanticGlobalBindingLabel declaration)
        <> "\" requires the exact proposition " <> Text.pack (show (scopedCoreTerm formula))
        <> ". Supply this proposition or an applicable classification."
renderFormationRequirementFailure failure@FormationRequirementFailure{} =
    let names = formationRequirementStructureNames failure
        binding = formationRequirementFailureBinding failure
        declaration = resolvedBindingDeclaration binding
        selectedKey = semanticGlobalBindingKey declaration
        selectedLabel = semanticBindingLabelText
            (semanticGlobalBindingLabel declaration)
        selectedSurface = renderGlobalSurface selectedKey
        requirement = renderRequirement names
            (formationRequirementFailureRequirement failure)
        explanation = formationRequirementFailureExplanation failure
        viewDetail = case
                ( formationSearchRelevantViews
                    (formationFailureStatistics explanation)
                , formationFailureFrontier explanation
                ) of
            (0, _frontier) ->
                " No relevant registered classification was available."
            (_viewCount, Just frontier) ->
                renderFormationFailureFrontier names
                    (formationFailureConsideredParameterErasure explanation)
                    frontier
            (_viewCount, Nothing)
                | formationFailureConsideredParameterErasure explanation ->
                    " A relevant classification erases one or more parameters, "
                        <> "so Felix cannot infer the erased argument of a "
                        <> "missing premise atom."
                | otherwise ->
                    " No matching premise atom for the relevant registered "
                        <> "classifications was reachable."
        (searchDetail, repair) = case
                formationRequirementFailureDetail failure of
            Nothing ->
                ( viewDetail
                , "establish \"" <> requirement
                    <> "\" in an enclosing assumption."
                )
            Just (RichProviderFormationFailure detail) ->
                let (providerDetail, providerRepair) =
                        renderProviderFormationFailure names requirement detail
                in (" " <> providerDetail, providerRepair)
            Just (RichNullaryClassificationFailure detail) ->
                let (classificationDetail, classificationRepair) =
                        renderNullaryClassificationFailure requirement detail
                in (" " <> classificationDetail, classificationRepair)
    in
        ( "cannot use the " <> renderGlobalFamily selectedKey
          <> " \"" <> selectedSurface <> "\" here. The selected declaration \""
          <> selectedLabel <> "\" requires that " <> requirement
          <> ". No exact active source assertion established this requirement."
          <> searchDetail
          <> " Suggested repair: " <> repair
        )

renderNotionQueryFailure :: NotionQueryFailure -> Text
renderNotionQueryFailure (WholeNotionQueryFailure formula origin _statistics) =
    "notion reasoning could not establish the exact proposition "
        <> maybe "" (\written -> maybe "" (\spelling -> "from \"" <> spelling <> "\" ")
            (SourceEvidence.writtenOriginSpelling written)) origin
        <> Text.pack (show (scopedCoreTerm formula))
        <> " from the retained proof context. Supply this proposition or an applicable classification."
renderNotionQueryFailure
        (NotionQueryFailure names requested writtenOrigin richFailure _statistics) =
    let requirement = renderRequirement names requested
        written = case writtenOrigin >>= SourceEvidence.writtenOriginSpelling of
            Nothing -> ""
            Just spelling -> "; required by \"" <> spelling <> "\""
        explanation = richFormationFailureExplanation richFailure
        viewDetail = case
                ( formationSearchRelevantViews
                    (formationFailureStatistics explanation)
                , formationFailureFrontier explanation
                ) of
            (0, _frontier) ->
                "No relevant registered classification was available."
            (_viewCount, Just frontier) ->
                Text.strip
                    (renderFormationFailureFrontier names
                        (formationFailureConsideredParameterErasure explanation)
                        frontier)
            (_viewCount, Nothing)
                | formationFailureConsideredParameterErasure explanation ->
                    "A relevant classification erases a parameter, so its missing premise could not be reconstructed."
                | otherwise ->
                    "No matching premise atom for the relevant registered classifications was reachable."
        detail = case richFormationFailureDetail richFailure of
            Nothing -> viewDetail
            Just (RichProviderFormationFailure failure) ->
                fst (renderProviderFormationFailure names requirement failure)
            Just (RichNullaryClassificationFailure failure) ->
                fst (renderNullaryClassificationFailure requirement failure)
    in "notion reasoning could not establish \"" <> requirement
        <> "\"" <> written <> " from the retained proof context. " <> detail
        <> " Prove the missing notion explicitly, or add an appropriate classification."

renderProviderFormationFailure
    :: Map StructureId Schema.StructurePhrase -> Text
    -> ProviderFormationFailure
    -> (Text, Text)
renderProviderFormationFailure names requested = \case
    ProviderResultRuleMissing provider ->
        ( "The written provider " <> renderSelectedProvider provider
            <> " has no registered result classification whose conclusion can reach \""
            <> requested <> "\"."
        , "state and prove a suitable classification for the selected provider, or establish \""
            <> requested <> "\" directly in an enclosing assumption."
        )
    ProviderResultPremiseMissing provider missingPremise ->
        let missing = renderRequirement names missingPremise
        in
        ( "A result rule for the written provider "
            <> renderSelectedProvider provider
            <> " is blocked because Felix could not establish that "
            <> missing <> "."
        , "establish \"" <> missing <> "\" in an enclosing assumption."
        )
    ProviderResultUnavailable provider resultHead ->
        ( "The written provider " <> renderSelectedProvider provider
            <> " has a registered result classification for "
            <> renderFormationFrontierHead names resultHead
            <> ", but no applicable classification established the requested notion \""
            <> requested <> "\"."
        , "add an applicable classification reaching \"" <> requested
            <> "\", or establish it directly in an enclosing assumption."
        )

renderNullaryClassificationFailure
    :: Text
    -> NullaryClassificationFailure
    -> (Text, Text)
renderNullaryClassificationFailure requested = \case
    NullaryClassificationMissing provider ->
        ( "The written " <> renderIntrinsicProvider provider
            <> " has no registered closed classification."
        , "state and prove a closed classification for the written provider, or establish \""
            <> requested <> "\" directly in an enclosing assumption."
        )
    NullaryClassificationClosureMissing provider _fingerprint resultHead ->
        ( "A closed classification for the written "
            <> renderIntrinsicProvider provider
            <> " established the registered result notion \""
            <> renderGlobalNotionHeadSurface resultHead
            <> "\", but the registered unary classifications did not reach \""
            <> requested <> "\"."
        , "add a unary classification to \"" <> requested
            <> "\", or establish it directly in an enclosing assumption."
        )

renderGlobalNotionHeadSurface :: GlobalNotionHead -> Text
renderGlobalNotionHeadSurface =
    renderGlobalSurface
        . globalBindingRefKey
        . globalNotionHeadReference

renderSelectedProvider :: ProviderFailureSource -> Text
renderSelectedProvider = \case
    ProviderFailureGlobal binding ->
        "\"" <> renderGlobalSurface key <> "\", selected from declaration \""
            <> providerBindingLabel binding <> "\""
      where
        key = semanticGlobalBindingKey (resolvedBindingDeclaration binding)
    ProviderFailureStructureField _identity _projection ->
        "selected explicit structure field"
    ProviderFailureIntrinsic provider -> renderIntrinsicProvider provider
    ProviderFailureFiniteSetLiteral -> "the written finite-set literal"

renderIntrinsicProvider :: IntrinsicProviderId -> Text
renderIntrinsicProvider = \case
    PowerSetProvider -> "fixed powerset provider"
    GlobalChoiceProvider -> "fixed global-choice provider"
    EmptySetProvider -> "fixed empty-set provider"
    FirstProjectionProvider -> "fixed first-projection provider"
    SecondProjectionProvider -> "fixed second-projection provider"

providerBindingLabel :: ResolvedGlobalBinding -> Text
providerBindingLabel =
    semanticBindingLabelText
        . semanticGlobalBindingLabel
        . resolvedBindingDeclaration

renderFormationFailureFrontier
    :: Map StructureId Schema.StructurePhrase -> Bool
    -> FormationFailureFrontier FormationSourceOrigin
    -> Text
renderFormationFailureFrontier names consideredParameterErasure frontier =
    let source = " from "
            <> renderFormationSourceOrigin
                (formationFailureFrontierOrigin frontier)
        continuation
            | consideredParameterErasure =
                ", but a relevant classification erases one or more parameters, "
                    <> "so Felix cannot infer the erased argument of a "
                    <> "missing premise atom."
            | otherwise =
                ", but no continuation from it established the required "
                    <> "notion."
    in " A retained source-backed "
        <> renderFormationFrontierHead names
            (formationFailureFrontierHead frontier)
        <> source
        <> continuation

renderFormationFrontierHead :: Map StructureId Schema.StructurePhrase -> NotionHeadKey -> Text
renderFormationFrontierHead names = \case
    NegativeGlobalNotionHeadKey head' -> "negative " <> renderFormationFrontierHead names (GlobalNotionHeadKey head')
    NegativeStructureNotionHeadKey head' -> "negative " <> renderFormationFrontierHead names (StructureNotionHeadKey head')
    NegativeMembershipNotionHeadKey -> "negative membership notion"
    NegativeExactStructureNotionHeadKey{} -> "negative exact record shape"
    GlobalNotionHeadKey head' ->
        let reference = globalNotionHeadReference head'
        in "notion head \""
            <> renderGlobalSurface (globalBindingRefKey reference)
            <> "\""
    StructureNotionHeadKey head' -> "structure notion \"" <> renderPatternSurface
        (Schema.structurePhraseSingular (diagnosticStructurePhrase names head')) <> "\""
    MembershipNotionHeadKey -> "membership notion"
    ExactStructureNotionHeadKey{} -> "exact record shape"

renderFormationSourceOrigin :: FormationSourceOrigin -> Text
renderFormationSourceOrigin = \case
    FormationFromProofLocal _ordinal _kind -> "an active proof local"
    FormationFromGoalAssumption _ location -> "a temporary goal assumption at " <> locationToText location
    FormationFromDefinitionHeader _source _variable location ->
        "a checked definition header at " <> locationToText location
    FormationFromCheckedGuard _kind location ->
        "a checked guard at " <> locationToText location
    FormationFromPhraseCore _kind location ->
        "a phrase core at " <> locationToText location

renderRequirement :: Map StructureId Schema.StructurePhrase -> AtomTemplate SourceTermPresentation -> Text
renderRequirement names = \case
    NegativeAtomTemplate body -> "not (" <> renderRequirement names body <> ")"
    GlobalAtomTemplate head' terms ->
        let key = globalBindingRefKey (globalNotionHeadReference head')
            rendered = renderSourceTermPresentation <$> toList terms
        in case (head', rendered) of
            (NounNotionHead{}, subject : arguments) ->
                subject <> " is a " <> renderGlobalApplication key arguments
            (AdjectiveNotionHead{}, subject : arguments) ->
                subject <> " is " <> renderGlobalApplication key arguments
            (VerbNotionHead{}, subject : arguments) ->
                subject <> " " <> renderGlobalApplication key arguments
            (RelationNotionHead{}, left : trailing) ->
                renderRelationNotionApplication key left trailing
            (PrefixPredicateNotionHead{}, arguments) ->
                renderPrefixPredicateApplication key arguments
            (_, []) -> impossible "a checked hosted global notion has no subject"
    StructureAtomTemplate head' terms -> case toList terms of
        subject : arguments -> renderSourceTermPresentation subject <> " is a "
            <> renderPatternApplication (Schema.structurePhraseSingular (diagnosticStructurePhrase names head'))
                (renderSourceTermPresentation <$> arguments)
        [] -> impossible "a checked structure notion has no subject"
    ExactStructureAtomTemplate _ subject ->
        renderSourceTermPresentation subject <> " has the exact record shape"
    MembershipAtomTemplate element set ->
        renderSourceTermPresentation element <> " is an element of "
            <> renderSourceTermPresentation set

-- Binding arguments have source order; relation parameters precede both
-- endpoints. Rendering an abbreviation never creates a semantic notion head.
renderWrittenGlobalApplication :: SemanticGlobalKey -> Vector SourceTermPresentation -> Text
renderWrittenGlobalApplication key terms = case (key, rendered) of
    (SemanticNoun{}, subject : arguments) -> subject <> " is a " <> renderGlobalApplication key arguments
    (SemanticLeftAdjective{}, subject : arguments) -> subject <> " is " <> renderGlobalApplication key arguments
    (SemanticRightAdjective{}, subject : arguments) -> subject <> " is " <> renderGlobalApplication key arguments
    (SemanticVerb{}, subject : arguments) -> subject <> " " <> renderGlobalApplication key arguments
    (SemanticRelation _ arity, arguments) ->
        case splitAt (fromIntegral (Raw.parameterArityValue arity)) arguments of
            (parameters, [left, right]) -> renderRelationNotionApplication key left (parameters <> [right])
            _ -> impossible "a checked relation call has malformed arguments"
    (SemanticPrefixPredicate{}, arguments) -> renderPrefixPredicateApplication key arguments
    _ -> renderGlobalApplication key rendered
  where
    rendered = renderSourceTermPresentation <$> toList terms

renderRelationNotionApplication :: SemanticGlobalKey -> Text -> [Text] -> Text
renderRelationNotionApplication key left trailing = case key of
    SemanticRelation token arity ->
        let parameterCount = fromIntegral (Raw.parameterArityValue arity)
            (parameters, operands) = splitAt parameterCount trailing
            relation = case parameters of
                [] -> Token.tokToText token
                _ -> Token.tokToText token <> "_{"
                    <> Text.intercalate ", " parameters <> "}"
        in case operands of
            [right] -> left <> " " <> relation <> " " <> right
            _ -> impossible "a checked relation notion has malformed arguments"
    _ -> impossible "a relation notion head has a non-relation key"

renderPrefixPredicateApplication
    :: SemanticGlobalKey
    -> [Text]
    -> Text
renderPrefixPredicateApplication key arguments =
    renderGlobalSurface key
        <> Text.concat ["{" <> argument <> "}" | argument <- arguments]

renderSourceTermPresentation :: SourceTermPresentation -> Text
renderSourceTermPresentation = \case
    PresentedSourceTerm _location presentation -> presentation
    LocatedSourceTerm location ->
        "term written at " <> locationToText location

renderAdjectiveReadingAmbiguity :: NonEmpty SemanticGlobalKey -> Text
renderAdjectiveReadingAmbiguity keys =
    "the bare adjective \"" <> renderGlobalSurface (NonEmpty.head keys)
        <> "\" is ambiguous: the visible readings are "
        <> Text.intercalate " and "
            (stableNub (renderGlobalFamily <$> toList keys))
        <> ". Write a complete noun or structure phrase, or name the intended "
        <> "carrier explicitly."
  where
    stableNub = foldr addIfNew []
    addIfNew value values
        | value `elem` values = values
        | otherwise = value : values

renderGlobalFamily :: SemanticGlobalKey -> Text
renderGlobalFamily = \case
    SemanticLeftAdjective reading _pattern -> renderAdjectiveFamily reading
    SemanticRightAdjective reading _pattern -> renderAdjectiveFamily reading
    SemanticNoun{} -> "noun"
    SemanticVerb{} -> "verb"
    SemanticRelation{} -> "relation"
    SemanticPrefixPredicate{} -> "predicate"
    SemanticFunctionPhrase{} -> "function phrase"
    SemanticExpressionFunction{} -> "expression function"
    SemanticTypedConstant{} -> "typed constant"
  where
    renderAdjectiveFamily = \case
        OrdinaryAdjectiveReading -> "ordinary adjective"
        StructureAdjectiveReading -> "structure adjective"

renderGlobalSurface :: SemanticGlobalKey -> Text
renderGlobalSurface key = case key of
    SemanticLeftAdjective _reading pattern' -> renderPatternSurface pattern'
    SemanticRightAdjective _reading pattern' -> renderPatternSurface pattern'
    SemanticFunctionPhrase singular _plural -> renderPatternSurface singular
    SemanticNoun singular _plural -> renderPatternSurface singular
    SemanticVerb surfaces ->
        renderPatternSurface
            (Raw.patternFromHoley
                (Raw.verbSurfaceSingular surfaces))
    SemanticRelation token _arity -> Token.tokToText token
    SemanticExpressionFunction pattern' -> renderPatternSurface pattern'
    SemanticTypedConstant token _type -> Token.tokToText token
    SemanticPrefixPredicate command _arity -> "\\" <> command

renderGlobalApplication :: SemanticGlobalKey -> [Text] -> Text
renderGlobalApplication key arguments = case key of
    SemanticExpressionFunction pattern' -> renderPatternApplication pattern' arguments
    SemanticFunctionPhrase singular _plural -> renderPatternApplication singular arguments
    SemanticLeftAdjective _reading pattern' ->
        renderPatternApplication pattern' arguments
    SemanticRightAdjective _reading pattern' ->
        renderPatternApplication pattern' arguments
    SemanticNoun singular _plural ->
        renderPatternApplication singular arguments
    SemanticVerb surfaces ->
        renderPatternApplication
            (Raw.patternFromHoley
                (Raw.verbSurfaceSingular surfaces))
            arguments
    _ -> renderGlobalSurface key

renderPatternSurface :: Raw.Pattern -> Text
renderPatternSurface pattern' =
    renderPatternApplication pattern' (repeat "_")

renderPatternApplication :: Raw.Pattern -> [Text] -> Text
renderPatternApplication pattern' arguments =
    Text.unwords (go pattern' arguments)
  where
    go Raw.End _remaining = []
    go (Raw.TokenCons token remaining) values =
        Token.tokToText token : go remaining values
    go (Raw.HoleCons remaining) values = case values of
        [] -> "_" : go remaining []
        value : later -> value : go remaining later

compiledSourceTermForTerm
    :: Raw.Term
    -> CoreType
    -> CanonicalTerm ObjectId
    -> CompiledSourceTerm
compiledSourceTermForTerm source coreType term =
    SourceTerm.sourceTermOccurrence
        term
        coreType
        (sourceTermPresentation source)

sourceTermPresentation :: Raw.Term -> SourceTermPresentation
sourceTermPresentation source =
    maybe
        (LocatedSourceTerm (locate source))
        (PresentedSourceTerm (locate source))
        (renderSourceTerm source)

locatedSetSourceTerm
    :: Location
    -> CanonicalTerm ObjectId
    -> CompiledSourceTerm
locatedSetSourceTerm location term =
    SourceTerm.sourceTermOccurrence term TySet (LocatedSourceTerm location)

compiledSourceTermArguments
    :: [CompiledSourceTerm]
    -> [(CanonicalTerm ObjectId, CoreType)]
compiledSourceTermArguments =
    fmap \argument ->
        ( compiledSourceTermCore argument
        , compiledSourceTermType argument
        )

renderSourceTerm :: Raw.Term -> Maybe Text
renderSourceTerm = \case
    Raw.TermExpr expression -> renderSourceExpression expression
    Raw.TermFun (Raw.Fun _location item arguments) ->
        renderPatternApplication
            (Raw.sg (Raw.lexicalItemSgPlPattern item))
            <$> traverse renderSourceTerm arguments
    Raw.TermIota{} -> Nothing
    Raw.TermQuantified{} -> Nothing

renderSourceExpression :: Raw.Expr -> Maybe Text
renderSourceExpression = \case
    Raw.ExprVar variable -> Just (renderSourceVariable variable)
    Raw.ExprNaturalNumeral _location magnitude ->
        Just (Text.pack (show magnitude))
    Raw.ExprOpaqueInteger _location integer ->
        Just ("\\opaqueInteger{" <> Text.pack (show integer) <> "}")
    Raw.ExprTypedConstant _location token _type ->
        Just (Token.tokToText token)
    Raw.ExprHigherApply _location function argument -> do
        functionText <- renderSourceTypedExpression function
        argumentText <- renderSourceTypedExpression argument
        pure (functionText <> "(" <> argumentText <> ")")
    Raw.ExprLambda{} -> Nothing
    Raw.ExprSelect{} -> Nothing
    Raw.ExprApp _location function argument -> do
        functionText <- renderSourceExpression function
        argumentText <- renderSourceExpression argument
        pure (functionText <> "(" <> argumentText <> ")")
    Raw.ExprOp _location item [function, argument]
        | Raw.mixfixPattern item == Raw.mixfixPattern Raw.ApplySymbol -> do
            functionText <- renderSourceExpression function
            argumentText <- renderSourceExpression argument
            pure (functionText <> "(" <> argumentText <> ")")
    Raw.ExprOp _location item arguments ->
        renderPatternApplication
            (Raw.mixfixPattern item)
            <$> traverse renderSourceExpression arguments
    Raw.ExprStructOp _location (Raw.StructSymbol name) maybeRecord ->
        case maybeRecord of
            Nothing -> Just ("\\" <> name)
            Just record -> do
                recordText <- renderSourceExpression record
                pure ("\\" <> name <> "[" <> recordText <> "]")
    Raw.ExprFiniteSet _location elements ->
        (\rendered -> "{" <> Text.intercalate ", " rendered <> "}")
            <$> traverse renderSourceExpression (toList elements)
    Raw.ExprSep{} -> Nothing
    Raw.ExprReplace{} -> Nothing
    Raw.ExprReplacePred{} -> Nothing
    Raw.ExprStructAggregate{} -> Nothing
    Raw.ExprStructReduct _location structure record -> do
        structureText <- renderSourceStructureApplication structure
        recordText <- renderSourceExpression record
        pure ("reduct[" <> structureText <> "](" <> recordText <> ")")
    Raw.ExprStructReconstruction _location structure record entries -> do
        structureText <- renderSourceStructureApplication structure
        recordText <- renderSourceExpression record
        replacements <- traverse (\case
            Raw.StructAggregateNamed _ (Raw.StructSymbol symbol) value ->
                (\text -> "\\" <> symbol <> " = " <> text) <$> renderSourceExpression value
            Raw.StructAggregatePositional{} -> Nothing) entries
        pure ("(" <> structureText <> " based on " <> recordText
            <> (if null replacements then "" else " with " <> Text.intercalate " and " replacements)
            <> ")")

maxNaturalNumeral :: Natural
maxNaturalNumeral = 1024

naturalNumeralCore
    :: ObjectId
    -> Natural
    -> CanonicalTerm ObjectId
naturalNumeralCore successor = go (CIntrinsic Empty)
  where
    go result 0 = result
    go result remaining =
        go (CApp (CGlobal successor) result) (remaining - 1)

renderSourceTypedExpression :: Raw.TypedExpression -> Maybe Text
renderSourceTypedExpression = \case
    Raw.TypedExpressionExpr expression -> renderSourceExpression expression
    Raw.TypedExpressionFormula{} -> Nothing

renderSourceStructureApplication
    :: Raw.StructApplication Raw.Expr
    -> Maybe Text
renderSourceStructureApplication
        (Raw.StructApplication phrase arguments) =
    renderPatternApplication
        (Raw.sg (Raw.lexicalItemSgPlPattern phrase))
        <$> traverse renderSourceExpression arguments

renderSourceVariable :: Raw.VarSymbol -> Text
renderSourceVariable = \case
    Raw.NamedVarAt _location name -> name
    Raw.FreshVarAt _location ordinal ->
        "_" <> Text.pack (show ordinal)

deriveNotionAtomProposition
    :: Location
    -> AtomTemplate (CanonicalTerm ObjectId)
    -> Elaborate (ScopedCheckedCore ObjectId)
deriveNotionAtomProposition location atom = do
    -- A recursive notion query may reach a rich term whose provider did
    -- not occur in the requested source atom.  Such terms have already been
    -- checked against the visible object closure; make precisely their global
    -- types available before reconstructing the logical atom.
    requireNotionQueryGlobals (atomTemplateCoreGlobals atom)
    proposition <- deriveNotionAtomCore location atom
    checkCurrentProposition location proposition

deriveNotionAtomCore :: Location -> AtomTemplate (CanonicalTerm ObjectId) -> Elaborate (CanonicalTerm ObjectId)
deriveNotionAtomCore location atom = do
    requireNotionQueryGlobals (atomTemplateCoreGlobals atom)
    case atom of
        NegativeAtomTemplate body -> CNot <$> deriveNotionAtomCore location body
        GlobalAtomTemplate head' arguments ->
            deriveGlobalNotionProposition location head' arguments
        StructureAtomTemplate head' arguments ->
            deriveStructureNotionProposition location head' arguments
        ExactStructureAtomTemplate shape subject -> do
            let selectors = semanticRecordShapeSelectors shape
            visible <- State.lift (Trans.lift
                (Declaration.resolveVisibleRecordShapesLowering selectors))
            unless (any ((== shape) . Declaration.resolvedRecordShapeKey) visible)
                (impossible "a checked exact-shape atom has no matching visible record shape")
            pure (Record.recordExactShape (CGlobal <$> selectors) subject)
        MembershipAtomTemplate element set ->
            pure
                (CApp
                    (CApp (CIntrinsic Member) element)
                    set)

atomTemplateCoreGlobals
    :: AtomTemplate (CanonicalTerm ObjectId)
    -> Set ObjectId
atomTemplateCoreGlobals = \case
    NegativeAtomTemplate body -> atomTemplateCoreGlobals body
    GlobalAtomTemplate _head arguments ->
        foldMap canonicalTermGlobals arguments
    StructureAtomTemplate _head arguments ->
        foldMap canonicalTermGlobals arguments
    ExactStructureAtomTemplate shape subject ->
        Set.fromList (semanticRecordShapeSelectors shape) <> canonicalTermGlobals subject
    MembershipAtomTemplate element set ->
        canonicalTermGlobals element <> canonicalTermGlobals set

deriveGlobalNotionProposition
    :: Location
    -> GlobalNotionHead
    -> Vector (CanonicalTerm ObjectId)
    -> Elaborate (CanonicalTerm ObjectId)
deriveGlobalNotionProposition location head' arguments = do
    let reference = globalNotionHeadReference head'
        key = globalBindingRefKey reference
    bindingArguments <- maybe
        (impossible "a notion template has malformed global arguments")
        pure
        (globalNotionBindingArguments key arguments)
    (resolved, content) <-
        resolveVisibleSourceGlobalContent location key
    unless (resolvedBindingRef resolved == reference)
        (impossible "a notion template resolved to a different declaration")
    (term, actual) <-
        applyResolvedContent
            location
            key
            (semanticGlobalBindingTarget
                (resolvedBindingDeclaration resolved))
            content
            ((\argument -> (argument, TySet)) <$> toList bindingArguments)
    unless (actual == TyProp)
        (impossible "a global notion head is not proposition-valued")
    pure term

deriveStructureNotionProposition
    :: Location
    -> SemanticStructureNotionHead
    -> Vector (CanonicalTerm ObjectId)
    -> Elaborate (CanonicalTerm ObjectId)
deriveStructureNotionProposition location head' arguments = do
    resolved <- State.lift (Trans.lift (Declaration.resolveVisibleStructureIdLowering (structureNotionHeadId head')))
    structure <- maybe (Except.throwError (ElaborationStructureInterfaceNotVisible location
        (structureNotionHeadId head'))) pure resolved
    let predicate = Declaration.resolvedStructurePredicate structure
        schema = Declaration.resolvedStructureSchema structure
    unless (fromIntegral (Vector.length arguments) == 1 + Schema.resolvedSchemaParameterCount schema)
        (impossible "a checked structure notion head has the wrong arity")
    requireGlobalType predicate (StructurePredicate.structurePredicateType schema)
    pure (foldl' CApp (CGlobal predicate) (toList arguments))

checkCurrentProposition
    :: Location
    -> CanonicalTerm ObjectId
    -> Elaborate (ScopedCheckedCore ObjectId)
checkCurrentProposition location proposition = do
    context <- currentSourceTermCheckingContext
    checkSourceTermHere location context TyProp proposition

missingCanonicalGlobalTypes
    :: GlobalTyping ObjectId
    -> CanonicalTerm ObjectId
    -> Maybe (NonEmpty ObjectId)
missingCanonicalGlobalTypes globalTyping term =
    NonEmpty.nonEmpty
        [ identity
        | identity <- Set.toAscList (canonicalTermGlobals term)
        , isNothing (lookupGlobalType globalTyping identity)
        ]

resolveVisibleSourceGlobalContent
    :: Location
    -> SemanticGlobalKey
    -> Elaborate
        ( ResolvedGlobalBinding
        , ObjectContent
        )
resolveVisibleSourceGlobalContent location key = do
    visible <-
        State.lift
            (Trans.lift
                (Declaration.resolveVisibleGlobalContentLowering key))
    maybe
        (Except.throwError (ElaborationGlobalNotVisible location key))
        pure
        visible

applyLocalGlobalDefinition
    :: Location
    -> SemanticGlobalKey
    -> LocalGlobalDefinition
    -> [(CanonicalTerm ObjectId, CoreType)]
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
applyLocalGlobalDefinition location key
        override =
    case override of
        LocalRecursiveResults depth parameters results resultType -> \arguments -> do
            currentDepth <- State.gets (binderStackDepth . lexicalBinderStack . elaborationScope)
            let offset = currentDepth - depth
                fixed = [(CBound (index+offset),TySet) | index <- parameters]
                reject :: Elaborate a
                reject = Except.throwError (ElaborationRecursiveDefinitionInvalid location
                    "a self-call must be fully applied with unchanged parameters to an immediate stored recursive field")
            unless (length arguments == length parameters+1 && take (length parameters) arguments == fixed) reject
            case drop (length parameters) arguments of
                [(CBound field,TySet)] | Just result <- List.lookup field [(a+offset,b+offset) | (a,b) <- results] ->
                    pure (CBound result,resultType)
                _ -> reject
        LocalObjectReference asserted ->
            applyResolvedContent
                location
                key
                (GlobalReference (assertedObjectId asserted))
                (assertedObjectContent asserted)
        LocalTransparentExpansion asserted ->
            applyResolvedContent
                location
                key
                (TransparentExpansion (assertedObjectId asserted))
                (assertedObjectContent asserted)

applyResolvedContent
    :: Location
    -> SemanticGlobalKey
    -> SemanticGlobalTarget
    -> ObjectContent
    -> [(CanonicalTerm ObjectId, CoreType)]
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
applyResolvedContent location key target content arguments =
    case target of
        GlobalReference identity -> do
            let coreType = objectContentType content
            requireGlobalType identity coreType
            applyTyped location (CGlobal identity) coreType arguments
        TransparentExpansion _identity ->
            case content of
                TransparentObjectContent _theory coreType body ->
                    applyExpandedTyped
                        location key body coreType arguments
                _ ->
                    impossible
                        "validated transparent expansion has opaque content"
        ContextualTransparentExpansion _identity requirements ->
            case content of
                TransparentObjectContent _theory coreType body -> do
                    contextArgument <-
                        resolveContextualExpansionArgument
                            location key requirements
                    applyExpandedTyped
                        location key body coreType
                        ((compiledSourceTermCore contextArgument, TySet) : arguments)
                _ ->
                    impossible
                        "validated contextual expansion has opaque content"

resolveContextualExpansionArgument
    :: Location
    -> SemanticGlobalKey
    -> Map.Map Raw.StructSymbol (FieldId, ObjectId)
    -> Elaborate CompiledSourceTerm
resolveContextualExpansionArgument location key requirements = do
    contextual <- State.gets (lexicalContextualBinder . elaborationScope)
    case contextual of
        Just index -> do
            traverse_
                (uncurry (recordContextualRequirement location))
                (Map.toAscList requirements)
            pure (receiver index)
        Nothing -> do
            candidates <-
                activeStructureReceiverCandidates \structure ->
                    if all
                            (\(symbol, field) ->
                                structureAnnotationField symbol structure == Just field)
                            (Map.toAscList requirements)
                        then Just ()
                        else Nothing
            case candidates of
                [StructureReceiverCandidate index _presentation _structure ()] ->
                    pure (receiver index)
                firstCandidate : secondCandidate : remaining ->
                    Except.throwError
                        (ElaborationContextualReceiverAmbiguous
                            location
                            key
                            (ambiguousStructureReceivers
                                firstCandidate secondCandidate remaining))
                [] ->
                    Except.throwError
                        (ElaborationContextualExpansionNotAvailable location key)
  where
    receiver index = SourceTerm.sourceTermOccurrence (CBound index) TySet (LocatedSourceTerm location)

applyExpandedTyped
    :: Location
    -> SemanticGlobalKey
    -> CanonicalTerm ObjectId
    -> CoreType
    -> [(CanonicalTerm ObjectId, CoreType)]
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
applyExpandedTyped location key body coreType arguments =
    withAbbreviationExpansion location key do
        (opened, resultType, actuals, remaining) <- open body coreType [] arguments
        expanded <- if null actuals then pure opened
            else expansionCoreWork (\work -> countedInstantiateCanonicalPrefix work (Vector.fromList actuals) opened)
        result@(term, _) <- foldM step (expanded, resultType) remaining
        globals <- expansionCoreWork (\work -> countedCanonicalGlobals work term)
        Trans.lift (State.lift (requireNotionQueryGlobals globals))
        pure result
  where
    -- Consume the lambda prefix once, then use the same simultaneous, memoized
    -- substitution as rich expansion. Sequential beta reduction would revisit
    -- earlier actuals at every subsequent argument. A function-valued body may
    -- leave ordinary applications after this prefix.
    open current currentType actuals pending = do
        chargeExpansion 1
        case (current, currentType, pending) of
            (CLam binderType nested, TyArrow expected result, (argument, argumentType) : rest)
                | binderType == expected -> do
                    unless (argumentType == expected)
                        (reject (ElaborationApplicationArgumentMismatch location expected argumentType))
                    open nested result (argument : actuals) rest
            _ -> pure (current, currentType, actuals, pending)
    step (current, currentType) (argument, argumentType) = do
        chargeExpansion 1
        case currentType of
            TyArrow expected result
                | expected == argumentType -> do
                    applied <- case current of
                        CLam binderType nested | binderType == expected ->
                            expansionCoreWork (\work -> countedInstantiateCanonicalPrefix work (Vector.singleton argument) nested)
                        _ -> pure (CApp current argument)
                    pure (applied, result)
                | otherwise ->
                    reject
                        (ElaborationApplicationArgumentMismatch
                            location expected argumentType)
            actual ->
                reject
                    (ElaborationApplicationExpectedFunction location actual)
    reject = Trans.lift . State.lift . Except.throwError

applyTyped
    :: Location
    -> CanonicalTerm ObjectId
    -> CoreType
    -> [(CanonicalTerm ObjectId, CoreType)]
    -> Elaborate (CanonicalTerm ObjectId, CoreType)
applyTyped location function functionType arguments =
    foldM step (function, functionType) arguments
  where
    step (currentFunction, currentType) (argument, argumentType) =
        case currentType of
            TyArrow expected result
                | expected == argumentType ->
                    pure (CApp currentFunction argument, result)
                | otherwise ->
                    Except.throwError
                        (ElaborationApplicationArgumentMismatch
                            location expected argumentType)
            actual ->
                Except.throwError
                    (ElaborationApplicationExpectedFunction location actual)

logicalNot :: CanonicalTerm global -> CanonicalTerm global
logicalNot proposition =
    CNot proposition
