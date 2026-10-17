{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

-- | Builder-confined authorization and atomic typed declaration append.
module Felix.Checking.Declaration
    ( ModuleDriver
    , DriverFailure(..)
    , DriverResult(..)
    , ImportedModuleEvidence
    , ImportedAliasOrigin(..)
    , ImportCheck
    , newImportCheck
    , ImportWork(..)
    , importCheckWork
    , PreparedImports
    , prepareImports
    , preparedImportIds
    , admitCachedModuleEvidence
    , evidenceInterface
    , evidenceClosure
    , evidenceLocalStructureSchemas
    , evidenceLocalStructurePredicates
    , evidenceFactTarget
    , evidenceFinalPrefix
    , nextDeclarationSlotDriver
    , currentTheoryDriver
    , currentFoundationAxiomDriver
    , resolveVisibleFactAliasDriver
    , resolveVisibleFactTargetsDriver
    , resolveVisibleGlobalDriver
    , resolveVisibleGlobalContentDriver
    , ResolvedStructure
    , ResolvedStructurePredicateApplication
    , resolvedStructurePredicateApplicationStructure
    , resolvedStructurePredicateApplicationSubject
    , resolvedStructurePredicateApplicationParameters
    , StructurePredicateResolutionError(..)
    , resolvedStructureSchema
    , resolvedStructureRegistration
    , resolvedStructurePredicate
    , resolvedStructureField
    , resolvedStructureFieldSlot
    , resolvedStructureFieldSelector
    , resolvedStructureFieldOrder
    , resolvedStructureFields
    , resolvedStructureFieldResources
    , resolvedStructureFieldProjection
    , resolvedStructureFieldProjections
    , ResolvedRecordShape
    , ResolvedRecordShapeField
    , resolvedRecordShapeFields
    , resolvedRecordShapeKey
    , resolvedRecordShapeFieldIdentity
    , resolvedRecordShapeFieldSelector
    , resolvedRecordShapeFieldProjection
    , resolvedRecordShapeFieldSymbol
    , resolveVisibleStructureDriver
    , resolveVisibleStructureFieldProjectionObjectsDriver
    , objectAvailableDriver
    , objectTypeDriver
    , LoweringDriver
    , runProspectiveLoweringDriver
    , nextDeclarationSlotLowering
    , currentTheoryLowering
    , currentFoundationLowering
    , currentFoundationAxiomLowering
    , resolveVisibleFactAliasLowering
    , resolveVisibleFactTargetsLowering
    , resolveVisibleFactLowering
    , TransientFormationReplayError(..)
    , replayTransientFormationLowering
    , materializeFormationProofLowering
    , compositionRegistryLowering
    , ResolvedDefinitionView
    , resolvedDefinitionViewObject
    , resolvedDefinitionViewKind
    , resolvedDefinitionViewFingerprint
    , resolvedDefinitionViewProposition
    , resolveVisibleDefinitionViewsLowering
    , resolveVisibleRecursiveDefinitionsLowering
    , recursiveDefinitionLookupLowering
    , pointwiseDefinitionLookupLowering
    , resolveVisibleGlobalLowering
    , resolveVisibleGlobalContentLowering
    , resolveVisibleStructureLowering
    , structureEnvironmentLowering
    , resolveVisibleStructureIdLowering
    , lookupStructureFactLowering
    , resolveVisibleStructurePredicateApplicationLowering
    , resolveVisibleStructureFieldProjectionObjectsLowering
    , resolveVisibleStructureFieldsLowering
    , resolveVisibleStructureFieldProviderLowering
    , resolveVisibleRecordShapesLowering
    , StructureProjectionLawIntegrityError(..)
    , checkStructureProjectionLawTargetLowering
    , resolveStructureProjectionLawLowering
    , objectAvailableLowering
    , objectTypeLowering
    , objectContentLowering
    , checkedObjectClosureLowering
    , NaturalNumeralBasis
    , naturalNumeralBasisObject
    , naturalNumeralBasisLowering
    , runModuleDriverEff
    , runModuleDriverEffWithNaturalNumeralBasis
    , runModuleDriverFreshIO
    , runModuleDriverFreshIOWithNaturalNumeralBasis
    , failModuleDriver
    , failDeclarationDriver
    , VampireResolver
    , VampireSubmission(..)
    , vampireBatchResolver
    , vampireResolver
    , vampireSubmissionResolver
    , Declaration
    , failDeclaration
    , visibleFormationRegistrationsLowering
    , formationCatalogLowering
    , formationCatalogSnapshotLowering
    , formationPreparationWorkLowering
    , formationPreparationDiagnosticsLowering
    , formationRecorderLowering, withFormationPhaseLowering, finishFormationReport
    , completeFormationCandidate, completeFormationDeclaration
    , resolveVisibleFormationSourceLowering
    , firstVisibleNullaryProviderClassificationLowering
    , CandidateSpec
    , candidateSpec
    , structureLawCandidateSpec
    , candidateSpecPurpose
    , candidateSpecWithRelationComposition
    , candidateSpecTarget
    , CandidatePlanningSpec
    , CheckedCandidate
    , checkedCandidate
    , checkedDefinitionEquationPlanning
    , checkedImplementationDefinitionPlanning
    , definitionEquationTarget
    , checkedSourceAxiomPlanning
    , checkedKernelPlanning
    , checkedKernelPlanningReferences
    , checkedKernelPlanningWithStaged
    , checkedStagedKernelPlanning
    , checkedNoExternalSourceProofPlanning
    , checkedNoExternalSourceProofPlanningWithFacts
    , checkedExternalSourceProofPlanning
    , checkedExternalSourceProofPlanningWithFacts
    , checkedOmittedPlanning
    , CheckedPlannedVampireRequest
    , checkedPlannedVampireRequest
    , checkedPlannedVampireTask
    , candidateAtPosition
    , CheckedDeclaration
    , checkedProofDeclaration
    , checkedProofDeclarationWithRegistrations
    , checkedCompiledDeclaration
    , checkedStructureDeclaration
    , checkedCompiledDeclarationWithRegistrations
    , withDatatypeDescriptor
    , withRecursiveDefinitionDescriptor
    , admitCheckedDeclaration
    , PlannedDeclaration
    , planCheckedDeclaration
    , admitPlannedCheckedDeclaration
    , plannedDeclarationPreviousPrefix
    , plannedDeclarationNextPrefix
    , plannedDeclarationDelta
    , PlanningIntegrityError(..)
    , prepareCandidateSpecDriver
    , prepareFrozenCandidateSpecDriver
    , prepareDefinitionEquationSpecDriver
    , prepareUnaryPredicateDefinitionEquationSpecDriver
    , prepareStagedCandidateVampireDriver
    , prepareCandidateSpecLowering
    , prepareFrozenCandidateSpecLowering
    , prepareDefinitionEquationSpecLowering
    , prepareDefinitionEquationSpecWithEligibilityLowering
    , prepareNamedSetConstructionSpecLowering
    , prepareNamedSetConstructionSpecWithEligibilityLowering
    , prepareRelationalSetConstructionSpecLowering
    , prepareUnaryPredicateDefinitionEquationSpecLowering
    , prepareStagedCandidateVampireLowering
    , prepareStagedCandidateVampireWithAuxiliariesLowering
    , prepareStagedCandidatesVampireWithFactsAndAuxiliariesLowering
    , ReservedCandidate
    , reservedCandidateSlot
    , reservedCandidateStage
    , CandidateProof
    , StructuralProofAuthorization
    , locateProofObligation
    , notePreparationExhaustion
    , noteRecordObligations
    , noteProofObligationGoal
    , declarationRecordObligations
    , locatedVampireFailure
    , recordOmittedUse
    , VampireGlobalPremiseSelection(..)
    , VampireLocalPremiseSelection(..)
    , VampirePremisePolicy(..)
    , internalVampirePremisePolicy
    , explicitVampirePremisePolicy
    , citedStructureVampirePremisePolicy
    , CitedStructureViews
    , resolveCitedStructureViewsLowering
    , citedStructureViewFacts
    , citedStructureViewOrigins
    , localVampirePremisePolicy
    , VampireObligationPreparationError(..)
    , ScopedVampirePremise
    , scopedVampirePremise
    , PreparedVampireObligation
    , preparedVampireObligationRoute
    , prepareScopedVampireObligationDriver
    , prepareScopedContradictionObligationDriver
    , prepareScopedVampireObligationLowering
    , prepareScopedVampireObligationExcludingLowering
    , prepareScopedContradictionObligationLowering
    , selectedStructurePredicateResourcesLowering
    , useAuthorizedFact
    , consumeAuthorizedFactDependency
    , ScopedKernelUsage
    , scopedKernelImportUses
    , scopedKernelExternalHypothesisUses
    , scopedKernelFoundationUses
    , scopedKernelRuleUses
    , scopedKernelUsesCanonicalDefinition
    , ScopedKernelMethodPolicy(..)
    , acceptScopedKernelDischarge
    , acceptScopedRecursiveEquation
    , useStagedCandidate
    , LocalClaim
    , proveLocalKernelClaim
    , useLocalClaim
    , authorizeKernelProofCandidate
    , authorizeStructuralSourceProofCandidate
    , authorizeKernelConstructionCandidate
    , authorizeDefinitionEquationCandidate
    , authorizeImplementationDefinitionCandidate
    , authorizeNamedSetConstructionCandidate
    , authorizeRelationalSetConstructionCandidate
    , acceptVampireObligation
    , acceptPreparedVampireObligation
    , acceptCurrentCandidateVampire
    , prepareCurrentCandidateVampire
    , authorizeVampireCandidate
    , authorizeVampireCandidateBatch
    , authorizeSourceAxiomCandidate
    , authorizeOmittedCandidate
    , ValidationIntegrityError(..)
    , renderValidationIntegrityError
    , DeclarationError(..)
    , declarationErrorLocation
    , renderDeclarationError
    , DriverOpenError(..)
    , renderDriverOpenError
    ) where

import Base
import Felix.Checking.Structure.Obligation qualified as Obligation
import Felix.Checking.Preparation qualified as Preparation
import Felix.Checking.Planning (PlannedCandidatePosition(..), PlannedFactReference(..), plannedCandidateStage)
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Laws qualified as StructureLaws
import Felix.Checking.Structure.Predicate qualified as StructurePredicate
import Felix.Checking.Structure.Batch qualified as StructureBatch
import Felix.Checking.Structure.Interface qualified as StructureInterface
import Felix.Checking.Structure.Environment qualified as StructureEnvironment
import Felix.Checking.Structure.Builtin qualified as StructureBuiltin
import Felix.Checking.Authority
import Felix.Checking.Backend.Problem qualified as Backend
import Felix.Checking.Backend.Tptp qualified as Tptp
import Felix.Checking.Calculation qualified as Calculation
import Felix.Checking.SourceTemplate qualified as SourceTemplate
import Felix.Checking.SourceTerm qualified as SourceTerm
import Data.Functor.Identity (Identity, runIdentity)
import Felix.Checking.Core
import Felix.Checking.Datatype.Interface qualified as DatatypeInterface
import Felix.Checking.Recursion.Interface qualified as RecursionInterface
import Felix.Checking.Recursion.Application qualified as RecursionApplication
import Felix.Checking.Elimination (ConjunctionPath, predicateProjectionTarget)
import Felix.Checking.DefinitionView qualified as DefinitionView
import Felix.Checking.Commit
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.NaturalNumeral
    ( NaturalNumeralBasis
    , naturalNumeralBasisObject
    )
import Felix.Checking.NaturalNumeral qualified as NaturalNumeral
import Felix.Checking.Materialization qualified as Materialization
import Felix.Checking.Notion.Catalog qualified as FormationCatalog
import Felix.Cache.Codec (CacheDigest)
import Felix.Checking.Notion.TermIndex qualified as FormationTerms
import Felix.Checking.Notion.Diagnostics qualified as FormationDiagnostics
import Felix.Checking.Notion.Rule qualified as FormationRule
import Felix.Checking.Notion.Projection qualified as Projection
import Felix.Checking.Notion.Introduction qualified as Introduction
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Notion.Registration qualified as Registration
import Felix.Checking.Notion.SourceEvidence (UniversalBody(..), AtomTree(..))
import Felix.Checking.Notion.UniversalTemplate qualified as Universal
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.FormationProof qualified as FormationProof
import Felix.Checking.Proof.Authorization.Internal
    ( StructuralProofAuthorization
    , structuralProofAction
    )
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic
import Felix.Checking.SetConstruction
import Felix.Checking.ValidationCache
    ( ValidationCache
    , runValidationCacheAlwaysMiss
    )
import Felix.Checking.ValidationCache qualified as ValidationCache
import Felix.Module
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Syntax.Abstract (StructSymbol)

import Control.Concurrent.MVar qualified as MVar
import Control.Exception qualified as Exception
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict qualified as PureState
import Control.Monad.Except qualified as Except
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Unique (Unique, newUnique)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Effectful
    ( Eff
    , IOE
    , (:>)
    , inject
    , runEff
    )
import Effectful.Error.Static (Error)
import Effectful.Error.Static qualified as Error
import Effectful.State.Static.Local (State)
import Effectful.State.Static.Local qualified as State
import Numeric.Natural (Natural)


liftEitherEffect
    :: Error error :> es
    => Either error value
    -> Eff es value
liftEitherEffect =
    either Error.throwError_ pure

mapErrorEffect
    :: Error error :> es
    => (error -> error)
    -> Eff es value
    -> Eff es value
mapErrorEffect transform action =
    Error.catchError action
        (\_callStack failure ->
            Error.throwError_ (transform failure))


newtype BuilderIdentity = BuilderIdentity Unique
    deriving stock (Eq)

newtype DeclarationInvocation = DeclarationInvocation Natural
    deriving stock (Eq)

newtype CandidateStage = CandidateStage Natural
    deriving stock (Show, Eq, Ord)

data ValidationIntegrityError
    = CachedValidationIntegrityError
        !Materialization.MaterializationError
    deriving stock (Show, Eq)

instance Exception.Exception ValidationIntegrityError

renderValidationIntegrityError :: ValidationIntegrityError -> Text
renderValidationIntegrityError = \case
    CachedValidationIntegrityError failure ->
        "cached validation does not match its exact contextual input: "
            <> Text.pack (show failure)

throwValidationIntegrity
    :: MonadIO m
    => Materialization.MaterializationError
    -> m value
throwValidationIntegrity =
    liftIO . throwIO . CachedValidationIntegrityError


data BuilderFactAuthorization = BuilderFactAuthorization
    !BuilderIdentity
    !FactSlot
    !ValidationCertificate

data PendingFactAuthorization = PendingFactAuthorization
    !BuilderIdentity
    !PrefixContextId
    !DeclarationInvocation
    !FactSlot
    !FactAuthority
    !CandidateStage
    ![Maybe SemanticFactOccurrenceFingerprint]
    !(Set SemanticFactOccurrenceFingerprint)

-- | Checked fact semantics paired with caller-selected evidence.  Semantic
-- lookup and request preparation deliberately ignore the evidence parameter;
-- only the admitted builder instantiation may consume capabilities.
data FactEntry evidence = FactEntry
    !CheckedPropositionContent
    !SemanticFactOccurrence
    !evidence

-- Compiled descriptions cross import reuse boundaries; proof authority does not.
-- The policy is part of identity: a checked definition view has eager forward
-- meaning which an otherwise identical classification does not acquire.
data FormationRuleDescription
    = ClassificationDescription !RegistrationBody !Natural
    | DefinitionDescription !RegistrationBody !Natural
    deriving stock (Eq, Ord)

-- Hash each immutable description once at its owner. Importers compare compact
-- keys; only a collision or a duplicate inspects a complete description.
-- Policy and binder arity remain part of identity, independently of the body.
type FormationDescriptionKey = (Bool, Natural, CacheDigest)
type FormationDescriptions = Map FormationDescriptionKey [(FormationRuleDescription, Natural)]

data PreparedFormationRule = PreparedFormationRule
    { preparedFormationSlot :: !DeclarationSlot
    , preparedFormationRule :: !FormationRule.RegisteredRule
    , preparedFormationSource :: !Notion.FormationRuleSource
    , preparedFormationConsequences :: ![(FormationRule.RegisteredRule, Notion.FormationRuleSource)]
    , preparedFormationDescription :: !FormationRuleDescription
    , preparedFormationDescriptionKey :: !FormationDescriptionKey
    , preparedFormationDescriptionWork :: !Natural
    }

defaultFormationPreparationWork :: Natural
defaultFormationPreparationWork = 262144

boundedFormationPreparation
    :: DeclarationSlot
    -> ((Natural -> Except.ExceptT DeclarationError (PureState.State Natural) ())
        -> Except.ExceptT DeclarationError (PureState.State Natural) value)
    -> (Either DeclarationError value, Natural)
boundedFormationPreparation slot action = PureState.runState (Except.runExceptT (action charge)) 0
  where
    charge amount = do
        used <- PureState.lift PureState.get
        let next = used + amount
            -- Admission has its own allowance; group calibration must not
            -- silently change the accepted declaration size.
            limit = defaultFormationPreparationWork
        when (next > limit) (Except.throwError
            (FormationRegistrationPreparationLimitExceeded slot limit used amount))
        PureState.lift (PureState.put next)

compileFormationRule
    :: (evidence -> Maybe DirectAuthorization)
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> DeclarationSlot -> Registration SemanticFactOccurrenceFingerprint -> (Natural -> Except.ExceptT DeclarationError (PureState.State Natural) ())
    -> Except.ExceptT DeclarationError (PureState.State Natural) FormationRule.RegisteredRule
compileFormationRule direct facts slot registration charge = do
    compiled <- Registration.compileRegistrationRules charge resolve [registration]
    case compiled of
        Right [(_,rule)] -> pure rule
        Left failure -> Except.throwError (FormationRegistrationPreparationFailed slot
            ("admitted rule failed compilation: " <> Text.pack (show failure)))
        _ -> Except.throwError (FormationRegistrationPreparationFailed slot "admitted rule failed compilation")
  where
    resolve fingerprint = do
        charge (FormationTerms.indexWork (Map.size facts) 1)
        case Map.lookup fingerprint facts of
            Just (FactEntry proposition _ evidence) | Just authority <- direct evidence -> pure (proposition,authority)
            _ -> Except.throwError (FormationRegistrationPreparationFailed slot "admitted rule lost its exact checked source")

lookupFormationSource
    :: DeclarationSlot -> Registration SemanticFactOccurrenceFingerprint
    -> BuilderRegistrationIndex -> Either DeclarationError Notion.FormationRuleSource
lookupFormationSource slot registration (BuilderRegistrationIndex entries _) =
    maybe (Left (FormationRegistrationPreparationFailed slot "admitted rule lost its application description")) Right
        (Map.lookup (OwnedRegistrationKey slot registration) entries)

prepareOwnedFormationRules
    :: (evidence -> Maybe DirectAuthorization) -> DeclarationInterfaceDelta
    -> BuilderState evidence
    -> (Either DeclarationError (BuilderState evidence), FormationDiagnostics.Measurement)
prepareOwnedFormationRules direct delta builder =
    let (result,used) = boundedFormationPreparation slot \charge -> do
            charge (fromIntegral (length registrations))
            (local, diagnostics) <- foldM (prepare charge)
                ([], logicalBuilderFormationPreparationDiagnostics builder) registrations
            (catalog, descriptions, counts) <- prepareFormationBatch slot charge (reverse local)
                (logicalBuilderFormationDescriptions builder) (logicalBuilderFormationCatalog builder) diagnostics
            pure (catalog, descriptions, local <> logicalBuilderLocalFormationRules builder, counts)
        completed = do
            (catalog, descriptions, entries, diagnostics) <- result
            pure builder
                { logicalBuilderFormationCatalog = catalog
                , logicalBuilderFormationDescriptions = descriptions
                , logicalBuilderLocalFormationRules = entries
                , logicalBuilderFormationPreparationDiagnostics = diagnostics
                , logicalBuilderFormationPreparationWork = logicalBuilderFormationPreparationWork builder + used }
        completedCounts = either (const FormationDiagnostics.emptyDiagnostics)
            (\after -> FormationDiagnostics.subtractDiagnostics
                (logicalBuilderFormationPreparationDiagnostics after)
                (logicalBuilderFormationPreparationDiagnostics builder)) completed
    in (completed, declarationPreparationMeasurement used completedCounts (preparationRejectedDebit result))
  where
    slot = declarationDeltaSlot delta
    registrations = declarationDeltaRegistrations delta
    prepare charge (entries, diagnostics) registration = do
        before <- PureState.lift PureState.get
        rule <- compileFormationRule direct (logicalBuilderFacts builder) slot registration charge
        compiled <- PureState.lift PureState.get
        source <- Except.liftEither (lookupFormationSource slot registration (logicalBuilderRegistrations builder))
        prepared <- prepareFormationRule charge slot (registrationBody registration) rule source (compiled - before)
        finished <- PureState.lift PureState.get
        pure (prepared : entries, FormationDiagnostics.countFamilyWork
            (Notion.formationRuleFamily source) (finished - before) diagnostics)

-- One portable description determines the original rule and every generated
-- projection/elimination. Keep that bundle shared across importing consumers;
-- deduplicating its children separately repeats full-description comparisons.
prepareFormationRule
    :: (Natural -> Except.ExceptT DeclarationError (PureState.State Natural) ())
    -> DeclarationSlot -> RegistrationBody -> FormationRule.RegisteredRule -> Notion.FormationRuleSource -> Natural
    -> Except.ExceptT DeclarationError (PureState.State Natural) PreparedFormationRule
prepareFormationRule charge slot body rule source syntaxWork = do
    projections <- Projection.compileProjections charge (FormationRule.registeredRule rule)
        >>= either (Except.throwError . FormationRegistrationPreparationFailed slot . Text.pack . show) pure
    eliminations <- Projection.compileWholeEliminations charge (FormationRule.registeredRule rule)
        >>= either (Except.throwError . FormationRegistrationPreparationFailed slot . Text.pack . show) pure
    introductions <- Introduction.compileIntroductions charge (FormationRule.registeredRule rule)
        >>= either (Except.throwError . FormationRegistrationPreparationFailed slot . Text.pack . show) pure
    charge (1 + fromIntegral (length projections + length eliminations + length introductions))
    let (arity, _, _) = FormationRule.ruleDescription (FormationRule.registeredRule rule)
        description = case rule of
            FormationRule.RegisteredClassification{} -> ClassificationDescription body arity
            FormationRule.RegisteredDefinition{} -> DefinitionDescription body arity
        consequences =
            [(FormationRule.RegisteredClassification consequence, Notion.FormationProjectionRule source plan)
                | (plan, consequence) <- projections] <>
            [(FormationRule.RegisteredClassification consequence, Notion.FormationEliminationRule source template plan)
                | (template, plan, consequence) <- eliminations] <>
            [(FormationRule.RegisteredClassification (Introduction.introductionRule introduction),
                Notion.FormationIntroductionRule source (Introduction.introductionOperation introduction))
                | introduction <- introductions]
        policy = case rule of FormationRule.RegisteredDefinition{} -> True; _ -> False
        digest = registrationBodyCacheDigest body
        key = (policy,arity,digest)
    -- Fingerprinting traverses the original description once. Keep its existing
    -- full structural bound; exact collision checks retain the same bound.
    charge (1 + syntaxWork)
    digest `seq` pure (PreparedFormationRule slot rule source consequences description key (1 + syntaxWork))

-- Only this declaration owner deduplicates execution. Every source survives
-- in the registration index and in checked exports, including later duplicates.
-- Scope-local universal producers never pass through this path.
prepareFormationBatch
    :: DeclarationSlot
    -> (Natural -> Except.ExceptT DeclarationError (PureState.State Natural) ())
    -> [PreparedFormationRule]
    -> FormationDescriptions
    -> FormationCatalog.Catalog (Either Notion.FormationRuleSource FormationCatalog.LocalProducerIx)
    -> FormationDiagnostics.Diagnostics
    -> Except.ExceptT DeclarationError (PureState.State Natural)
        (FormationCatalog.Catalog (Either Notion.FormationRuleSource FormationCatalog.LocalProducerIx),
            FormationDescriptions, FormationDiagnostics.Diagnostics)
prepareFormationBatch slot charge supplied descriptions initial diagnostics = do
    (retained, nextDescriptions, deduplicated) <- foldM select
        ([], descriptions, diagnostics) supplied
    (catalog, counts) <- foldM prepare (initial, deduplicated)
        (List.groupBy (\a b -> family a == family b) (reverse retained))
    pure (catalog, nextDescriptions, counts)
  where
    family = Notion.formationRuleFamily . preparedFormationSource
    select (retained, known, counts) entry = do
        let key = preparedFormationDescription entry
            bucketKey = preparedFormationDescriptionKey entry
            headWork = FormationTerms.indexWork (Map.size known) 8
        charge headWork
        let bucket = Map.findWithDefault [] bucketKey known
            countWork amount = FormationDiagnostics.countOperation FormationDiagnostics.DescriptionLookup 1
                . FormationDiagnostics.countOperation FormationDiagnostics.DescriptionLookupWork amount
                . FormationDiagnostics.countFamilyWork (family entry) amount
            member [] = charge 1 >> pure (False,1)
            member ((other,otherWork):rest) = do
                let amount = 1 + max (preparedFormationDescriptionWork entry) otherWork
                charge amount
                if key == other then pure (True,amount) else do
                    (found,remaining) <- member rest
                    pure (found,amount+remaining)
        (found,descriptionWork) <- member bucket
        if found
            then pure (retained, known,
                FormationDiagnostics.countOperation FormationDiagnostics.DuplicateRegistration 1
                    (countWork (headWork + descriptionWork) counts))
            else do
                charge (headWork + 1)
                pure (entry : retained, Map.insert bucketKey
                    ((key,preparedFormationDescriptionWork entry):bucket) known,
                    countWork (2 * headWork + descriptionWork + 1) counts)
    prepare current [] = pure current
    prepare (catalog, counts) batch@(entry : _) = do
        before <- PureState.lift PureState.get
        let describe = \case
                FormationRegistrationPreparationFailed _ detail -> FormationRegistrationPreparationFailed slot
                    (detail <> "; " <> Text.pack (show (family entry)) <> " batch started at " <> Text.pack (show before))
                failure -> failure
        next <- Except.withExceptT describe (FormationCatalog.insertRules charge
            [(Left source, rule) | value <- batch,
                (rule, source) <- (preparedFormationRule value, preparedFormationSource value)
                    : preparedFormationConsequences value] catalog)
        after <- PureState.lift PureState.get
        pure (next, FormationDiagnostics.countOperation FormationDiagnostics.CatalogExtensionWork (after - before)
            (FormationDiagnostics.countOperation FormationDiagnostics.RegistryVisit
            (fromIntegral (FormationCatalog.catalogSize next - FormationCatalog.catalogSize catalog))
            (FormationDiagnostics.countFamilyWork (family entry) (after - before) counts)))

-- Stable registration order is family, declaration owner, then the entire
-- source branch and payload. Fact fingerprints alone cannot order owners.
data OwnedRegistrationKey = OwnedRegistrationKey
    !DeclarationSlot !(Registration SemanticFactOccurrenceFingerprint)
    deriving stock (Eq)

instance Ord OwnedRegistrationKey where
    compare (OwnedRegistrationKey owner left) (OwnedRegistrationKey owner' right) =
        compare (registrationFamily (registrationBody left)) (registrationFamily (registrationBody right))
            <> compare owner owner' <> compare left right

data BuilderRegistrationIndex = BuilderRegistrationIndex
    !(Map OwnedRegistrationKey Notion.FormationRuleSource)
    !(Map IntrinsicProviderId (Set OwnedRegistrationKey))

emptyBuilderRegistrationIndex :: BuilderRegistrationIndex
emptyBuilderRegistrationIndex = BuilderRegistrationIndex Map.empty Map.empty

insertBuilderRegistration
    :: (OwnedRegistrationKey, Notion.FormationRuleSource)
    -> BuilderRegistrationIndex -> BuilderRegistrationIndex
insertBuilderRegistration (key@(OwnedRegistrationKey _ registration), source)
        (BuilderRegistrationIndex entries providers) =
    BuilderRegistrationIndex (Map.insert key source entries) $
        case registrationBody registration of
            RegisterNullaryProvider rule ->
                Map.insertWith Set.union (nullaryProvider rule) (Set.singleton key) providers
            _ -> providers

lookupFirstBuilderNullaryProviderClassification
    :: IntrinsicProviderId -> BuilderRegistrationIndex
    -> Maybe Notion.VisibleNullaryProviderClassification
lookupFirstBuilderNullaryProviderClassification provider (BuilderRegistrationIndex entries providers) = do
    keys <- Map.lookup provider providers
    key <- Set.lookupMin keys
    Notion.FormationNullaryRule source <- Map.lookup key entries
    pure source

materializeRegistration
    :: (evidence -> Maybe DirectAuthorization)
    -> CheckedObjectClosure -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> Registration SemanticFactOccurrenceFingerprint
    -> Either DeclarationError Notion.FormationRuleSource
materializeRegistration direct closure environment facts registration =
    case registrationBody registration of
        RegisterNotionView rule -> Notion.FormationViewRule <$>
            materializeResolvedNotionView direct closure environment facts branch rule
        RegisterNullaryProvider rule -> Notion.FormationNullaryRule <$>
            materializeResolvedNullaryProviderClassification closure environment facts branch rule
        RegisterProviderResult rule -> Notion.FormationProviderRule <$>
            materializeResolvedProviderResultRule closure environment facts branch rule
        RegisterBackwardNotion rule -> Notion.FormationBackwardRule <$>
            materializeResolvedBackwardNotionRule closure environment facts branch rule
        RegisterFiniteEvidence rule -> Notion.FormationFiniteRule <$>
            materializeResolvedFiniteEvidenceRule closure environment facts branch rule
        RegisterGraphDomain rule -> Notion.FormationGraphRule <$>
            materializeResolvedGraphDomainRule closure environment facts branch rule
        RegisterWholeConclusion rule -> Notion.FormationWholeRule <$> do
            let fingerprint = semanticFactBranchFact branch
                invalid = WholeConclusionRuleMaterializationInvalid fingerprint
            FactEntry proposition _ _ <- maybe (Left (invalid "the supporting fact is not visible")) Right
                (Map.lookup fingerprint facts)
            premises <- traverse (materializeRulePremiseTree closure invalid environment)
                (wholeConclusionPremises rule)
            _ <- materializeResidualTemplate closure invalid environment (wholeConclusionTemplate rule)
            first invalid (Notion.visibleWholeConclusionRule branch rule proposition premises)
  where
    branch = registrationBranch registration

materializeResolvedNotionView
    :: (evidence -> Maybe DirectAuthorization)
    -> CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> NotionViewRule
    -> Either DeclarationError Notion.VisibleNotionView
materializeResolvedNotionView directAuthorization closure environment facts branch view = do
    let fingerprint = semanticFactBranchFact branch
    FactEntry proposition occurrence evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    let premise = case notionViewPremise view of
            GlobalNotionViewPremise head' terms -> GlobalAtomTemplate head' terms
            StructureNotionViewPremise head' terms -> StructureAtomTemplate head' terms
            ExactProviderMembershipPremise element provider arguments ->
                MembershipAtomTemplate element (TemplateProvider provider arguments)
    materializedPremise <- materializeRuleAtomTemplate closure invalid environment premise
    conclusion <- case notionViewConclusion view of
        AtomicLeaf atom -> materializeRuleAtomTemplate closure invalid environment atom
        WholeLeaf template -> materializeResidualTemplate closure invalid environment template
    runtime <- first invalid
        (Notion.visibleNotionView branch view proposition materializedPremise conclusion)
    case (semanticFactPurpose occurrence, directAuthorization evidence) of
        (GeneralFactPurpose, Just CheckedSourceProof{}) -> pure ()
        (GeneralFactPurpose, Just (CheckedKernelConstruction (CheckedDefinitionProjection identity path)))
            | matchesPredicateProjection closure identity path proposition ->
                pure ()
        (StructureFactPurpose (Schema.StructureLawId _ Schema.ParentInheritanceLaw{}),
            Just (CheckedKernelConstruction (CheckedStructureLaw StructurePredicateComponent))) ->
                pure ()
        _ -> Left (invalid "the view has no matching checked source association")
    pure runtime
  where
    invalid = NotionViewMaterializationInvalid (semanticFactBranchFact branch)

materializeResolvedNullaryProviderClassification
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> NullaryProviderRule
    -> Either DeclarationError Notion.VisibleNullaryProviderClassification
materializeResolvedNullaryProviderClassification closure environment facts branch classification = do
    let fingerprint = semanticFactBranchFact branch
        invalid = NullaryProviderClassificationMaterializationInvalid fingerprint
        value = TemplateProvider
            (IntrinsicSourceProvider (nullaryProvider classification))
            Vector.empty
    FactEntry proposition _occurrence _evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    expected <- materializeRuleAtomTemplate closure invalid environment
        (GlobalAtomTemplate (nullaryConclusion classification)
            (Vector.singleton value))
    runtime <- first invalid
        (Notion.visibleNullaryProviderClassification branch classification proposition expected)
    pure runtime

materializeResolvedProviderResultRule
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> ProviderResultRule
    -> Either DeclarationError Notion.VisibleProviderResultRule
materializeResolvedProviderResultRule closure
        environment@(ResolvedEnvironment globals _ structures _ _ _) facts branch rule = do
    let fingerprint = semanticFactBranchFact branch
        provider = providerResultProvider rule
    FactEntry proposition _occurrence _evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    providerValue <- materializeRuleTermTemplate closure invalid environment
        (TemplateProvider (resultProviderTemplateHead provider)
            (resultProviderTemplateArguments provider))
    premises <- case providerResultPremises rule of
        ProviderResultUnconditional -> pure Notion.MaterializedProviderResultUnconditional
        ProviderResultGuarded (RulePremiseBundles premiseBundles) ->
            Notion.MaterializedProviderResultGuarded
                <$> traverse (materializeRulePremiseTree closure invalid environment) premiseBundles
    materializedConclusion <- traverseAtomTemplateArguments
        (\case
            ResultRuleTerm term -> materializeRuleTermTemplate closure invalid environment term
            ResultRuleProviderValue -> pure providerValue)
        (providerResultConclusion rule)
    conclusion <- materializeAtomTemplate closure invalid globals structures id materializedConclusion
    runtime <- first invalid (Notion.visibleProviderResultRule branch rule proposition premises conclusion)
    pure runtime
  where
    invalid = ProviderResultRuleMaterializationInvalid (semanticFactBranchFact branch)

materializeResolvedBackwardNotionRule
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> BackwardNotionRule
    -> Either DeclarationError Notion.VisibleBackwardNotionRule
materializeResolvedBackwardNotionRule closure environment facts branch rule = do
    let fingerprint = semanticFactBranchFact branch
        invalid = BackwardNotionRuleMaterializationInvalid fingerprint
        RulePremiseBundles premiseBundles = backwardNotionPremises rule
    FactEntry proposition _occurrence _evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    premises <- traverse (materializeRulePremiseTree closure invalid environment) premiseBundles
    conclusion <- materializeRuleAtomTemplate closure invalid environment
        (backwardNotionConclusion rule)
    runtime <- first invalid (Notion.visibleBackwardNotionRule branch rule proposition premises conclusion)
    pure runtime

materializeResolvedFiniteEvidenceRule
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> FiniteEvidenceRule
    -> Either DeclarationError Notion.VisibleFiniteEvidenceRule
materializeResolvedFiniteEvidenceRule closure environment facts branch rule = do
    let fingerprint = semanticFactBranchFact branch
        invalid = FiniteEvidenceRuleMaterializationInvalid fingerprint
        skeleton = finiteEvidenceSkeleton rule
        premiseBundles = checkedNotionRulePremises skeleton
    FactEntry proposition _occurrence _evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    premises <- traverse (materializeRulePremiseTree closure invalid environment) premiseBundles
    conclusion <- materializeRuleAtomTemplate closure invalid environment
        (checkedNotionRuleConclusion skeleton)
    runtime <- first invalid (Notion.visibleFiniteEvidenceRule branch rule proposition premises conclusion)
    pure runtime

materializeResolvedGraphDomainRule
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> SemanticFactBranch
    -> GraphDomainRule
    -> Either DeclarationError Notion.VisibleGraphDomainRule
materializeResolvedGraphDomainRule closure
        environment@(ResolvedEnvironment globals _ _ _ _ _) facts branch rule = do
    let fingerprint = semanticFactBranchFact branch
        invalid = GraphDomainRuleMaterializationInvalid fingerprint
        left = TemplateVariable (graphDomainLeft rule)
        right = TemplateVariable (graphDomainRight rule)
        graph = TemplateVariable (graphDomainGraph rule)
        provider = graphDomainProvider rule
    FactEntry proposition _occurrence _evidence <-
        maybe (Left (invalid "the supporting fact is not visible")) Right
            (Map.lookup fingerprint facts)
    -- This is the old graph-domain fragment's eligibility condition, not a
    -- different meaning for provider applications. Remove it with that family
    -- when the common anchored calculus supplies its complete premise policy.
    reference <- case provider of
        GlobalSourceProvider value -> pure value
        _ -> Left (invalid "the graph-domain provider is not a global provider")
    resolved <- maybe (Left (invalid "the registered domain provider is not visible")) Right
        (Map.lookup (globalBindingRefKey reference) globals)
    unless (isNothing (resolvedBindingContract resolved))
        (Left (invalid "the registered domain provider must be uncontracted"))
    premise <- materializeRuleAtomTemplate closure invalid environment
        (MembershipAtomTemplate (TemplateOrderedPair left right) graph)
    conclusion <- materializeRuleAtomTemplate closure invalid environment
        (MembershipAtomTemplate left (TemplateProvider provider (Vector.singleton graph)))
    runtime <- first invalid (Notion.visibleGraphDomainRule branch rule proposition premise conclusion)
    pure runtime

-- All registration families interpret source templates through this boundary.
-- These are reconstructions in a theorem's nearest-first binder context, not
-- fresh written source occurrences or proofs. Each family adapter checks
-- the complete reconstructed proposition against the exact supporting fact.
materializeRuleTermTemplate
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> ResolvedEnvironment evidence
    -> RuleTermTemplate
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeRuleTermTemplate closure invalid environment =
    materializeSetTermTemplate closure invalid environment (\(ViewVariableIx index) -> pure (CBound index))

materializeSetTermTemplate
    :: CheckedObjectClosure -> (Text -> DeclarationError) -> ResolvedEnvironment evidence
    -> (variable -> Either DeclarationError (CanonicalTerm ObjectId))
    -> SetTermTemplate variable -> Either DeclarationError (CanonicalTerm ObjectId)
materializeSetTermTemplate closure invalid environment variable = go
  where
    go = \case
        TemplateClosed value -> first invalid (materializeClosedSetValue closure value)
        TemplateVariable value -> variable value
        TemplateOrderedPair left right ->
            CApp <$> (CApp (CIntrinsic OrderedPair) <$> go left) <*> go right
        TemplateProvider provider arguments ->
            materializeSourceProviderApplication closure invalid environment provider =<< traverse go arguments

materializeRuleAtomTemplate
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> ResolvedEnvironment evidence
    -> AtomTemplate RuleTermTemplate
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeRuleAtomTemplate closure invalid
        environment@(ResolvedEnvironment globals _ structures _ _ _) atom = do
    arguments <- traverseAtomTemplateArguments
        (materializeRuleTermTemplate closure invalid environment) atom
    materializeAtomTemplate closure invalid globals structures id arguments

-- Whole source descriptions are stable semantic data. Every retained atomic
-- view must select the exact checked subformula before it can license a clause.
materializeResidualTemplate
    :: CheckedObjectClosure -> (Text -> DeclarationError) -> ResolvedEnvironment evidence
    -> ResidualTemplate -> Either DeclarationError (CanonicalTerm ObjectId)
materializeResidualTemplate closure invalid environment template = do
    for_ (residualTemplateEvidence template) (validate (residualTemplateFormula template))
    pure (residualTemplateFormula template)
  where
    validate expected = \case
        SourceEvidence.SourceResidual{} -> pure ()
        SourceEvidence.SourceInputs _ inputs -> for_ inputs \(SourceEvidence.SourceInput binders term) -> do
            actual <- materializeSetTermTemplate closure invalid environment pure term
            present <- SourceEvidence.sourceInputOccursWith (pure ()) binders actual expected
            unless present (Left (invalid "a whole support operand does not occur in its source telescope"))
        SourceEvidence.SourceWithInputs inputs body -> do
            validate expected (SourceEvidence.SourceInputs Nothing inputs)
            validate expected body
        SourceEvidence.SourceAtom atom -> do
            actual <- materializeRuleAtomTemplate closure invalid environment atom
            unless (expected == actual) (Left (invalid "a whole atomic view disagrees with its checked source"))
        SourceEvidence.SourceAnd a b | CAnd left right <- expected -> validate left a >> validate right b
        SourceEvidence.SourceBind body | CForall TySet nested <- expected -> validate nested body
        SourceEvidence.SourceExists body | CExists TySet nested <- expected -> validate nested body
        SourceEvidence.SourceOr a b | COr left right <- expected -> validate left a >> validate right b
        SourceEvidence.SourceIff a b | CEq TyProp left right <- expected -> validate left a >> validate right b
        SourceEvidence.SourceRequire a b | CImp left right <- expected -> validate left a >> validate right b
        _ -> Left (invalid "a whole elimination description disagrees with its checked source")

materializeRulePremiseTree
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> ResolvedEnvironment evidence
    -> RulePremiseTree RuleTermTemplate
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeRulePremiseTree closure invalid environment = go
  where
    go = \case
        RulePremiseAtom atom -> materializeRuleAtomTemplate closure invalid environment atom
        RulePremiseUniversal body -> universal 0 body
        RulePremiseResidual template -> materializeResidualTemplate closure invalid environment template
        RulePremiseAnd left right -> CAnd <$> go left <*> go right

    universal depth = \case
        UniversalBind nested -> CForall TySet <$> universal (depth + 1) nested
        UniversalRequire guard nested -> CImp <$> atoms depth guard <*> universal depth nested
        UniversalReturn result -> atoms depth result
    atoms depth = \case
        AtomAnd left right -> CAnd <$> atoms depth left <*> atoms depth right
        AtomLeaf atom -> first invalid (Universal.lowerAtom depth atom)
            >>= materializeRuleAtomTemplate closure invalid environment

materializeSourceProviderApplication
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> ResolvedEnvironment evidence
    -> SourceProviderHead
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeSourceProviderApplication closure invalid
        (ResolvedEnvironment globals _ _ fields _ _) provider arguments = case provider of
    GlobalSourceProvider reference -> do
        resolved <- maybe (Left (invalid "the registered source provider is not visible")) Right
            (Map.lookup (globalBindingRefKey reference) globals)
        unless (resolvedBindingRef resolved == reference
                && resolvedBindingSourceProviderHead resolved == Just provider)
            (Left (invalid "the registered source provider is not exact or has the wrong owner"))
        (value, resultType) <- materializeResolvedGlobalApplication
            closure invalid "registered source provider" resolved arguments
        unless (resultType == TySet)
            (Left (invalid "the registered source provider is not set-valued"))
        pure value
    StructureFieldSourceProvider field projection ->
        materializeStructureFieldProvider closure invalid fields field projection arguments
    IntrinsicSourceProvider providerId -> materializeIntrinsicProvider invalid providerId arguments
    FiniteSetLiteralSourceProvider -> materializeFiniteSetLiteralProvider invalid arguments

materializeStructureFieldProvider
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> Map FieldId ObjectId
    -> FieldId
    -> ObjectId
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeStructureFieldProvider
        closure invalid fields identity projection arguments = do
    unless
        (Map.lookup identity fields == Just projection)
        (Left (invalid "the registered structure field is not visible"))
    projectionType <- maybe
        (Left (invalid "the registered field projection object is missing"))
        Right
        (lookupCheckedObjectType projection closure)
    unless
        (projectionType == TyArrow TySet TySet)
        (Left (invalid "the registered field projection is not unary set-valued"))
    receiver <- case toList arguments of
        [value] -> pure value
        _ -> Left (invalid "a structure-field provider has the wrong arity")
    pure (CApp (CGlobal projection) receiver)

materializeIntrinsicProvider
    :: (Text -> DeclarationError)
    -> IntrinsicProviderId
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeIntrinsicProvider invalid provider arguments =
    maybe
        (Left
            (invalid
                "an intrinsic provider has the wrong Core signature or arity"))
        Right
        (intrinsicProviderApplication provider arguments)

materializeFiniteSetLiteralProvider
    :: (Text -> DeclarationError)
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeFiniteSetLiteralProvider invalid arguments = do
    elements <- maybe
        (Left (invalid "a finite-set literal provider has an empty spine"))
        Right
        (NonEmpty.nonEmpty (toList arguments))
    pure (finiteSetLiteralProviderApplication elements)

materializeAtomTemplate
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> Map SemanticGlobalKey ResolvedGlobalBinding
    -> StructureEnvironment.StructureEnvironment evidence
    -> (term -> CanonicalTerm ObjectId)
    -> AtomTemplate term
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeAtomTemplate closure invalid globals structures materializeTerm = \case
    NegativeAtomTemplate body -> CNot <$> materializeAtomTemplate closure invalid globals structures materializeTerm body
    GlobalAtomTemplate head' terms ->
        materializeGlobalNotionAtom
            closure invalid globals head' (materializeTerm <$> terms)
    StructureAtomTemplate head' terms ->
        materializeStructureNotionAtom
            invalid structures head' (materializeTerm <$> terms)
    ExactStructureAtomTemplate shape subject -> do
        unless (Set.member shape (visibleRecordShapeKeys structures))
            (Left (invalid "the registered exact record shape is not visible"))
        pure (Record.recordExactShape (CGlobal <$> semanticRecordShapeSelectors shape) (materializeTerm subject))
    MembershipAtomTemplate element set ->
        pure
            (CApp
                (CApp (CIntrinsic Member) (materializeTerm element))
                (materializeTerm set))

visibleRecordShapeKeys :: StructureEnvironment.StructureEnvironment evidence -> Set SemanticRecordShapeKey
visibleRecordShapeKeys structures = Set.fromList
    [semanticRecordShapeKey (StructurePredicate.pendingStructureSchema (StructureInterface.structureInterfaceRegistration interface))
    | interface <- Map.elems (StructureEnvironment.structureEnvironmentInterfaces structures)]

materializeGlobalNotionAtom
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> Map SemanticGlobalKey ResolvedGlobalBinding
    -> GlobalNotionHead
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeGlobalNotionAtom closure invalid globals head' arguments = do
    let reference = globalNotionHeadReference head'
        key = globalBindingRefKey reference
    unless (globalNotionHeadMatchesKey head' key)
        (Left
            (invalid
                "a registered global notion head has the wrong predicate family"))
    resolved <- maybe
        (Left (invalid "a registered global notion head is not visible"))
        Right
        (Map.lookup key globals)
    unless (resolvedBindingRef resolved == reference)
        (Left (invalid "a registered global notion head has the wrong owner"))
    bindingArguments <- maybe
        (Left (invalid "a registered global notion head has malformed arguments"))
        Right
        (globalNotionBindingArguments key arguments)
    (proposition, resultType) <-
        materializeResolvedGlobalApplication
            closure
            invalid
            "registered global notion head"
            resolved
            bindingArguments
    unless (resultType == TyProp)
        (Left
            (invalid
                "a registered global notion head is not proposition-valued"))
    pure proposition

-- | Reconstruct a named head or provider for theorem admission. Abbreviations
-- have already expanded and cannot supply a source capability of their own.
materializeResolvedGlobalApplication
    :: CheckedObjectClosure
    -> (Text -> DeclarationError)
    -> Text
    -> ResolvedGlobalBinding
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId, CoreType)
materializeResolvedGlobalApplication closure invalid description resolved arguments = do
    let target = semanticGlobalBindingTarget
            (resolvedBindingDeclaration resolved)
        identity = semanticGlobalTargetObject target
    content <- maybe
        (Left (invalid ("the " <> description <> " object is not visible")))
        Right
        (lookupCheckedObjectContent identity closure)
    (initialTerm, initialType) <- case target of
        GlobalReference object ->
            pure (CGlobal object, objectContentType content)
        _ ->
            Left
                (invalid
                    ("the " <> description
                        <> " is an abbreviation, not a named head or provider"))
    foldM
        (applyMaterializedGlobalArgument invalid description)
        (initialTerm, initialType)
        (toList arguments)

applyMaterializedGlobalArgument
    :: (Text -> DeclarationError)
    -> Text
    -> (CanonicalTerm ObjectId, CoreType)
    -> CanonicalTerm ObjectId
    -> Either DeclarationError (CanonicalTerm ObjectId, CoreType)
applyMaterializedGlobalArgument invalid description
        (function, functionType) argument =
    case functionType of
        TyArrow TySet result ->
            pure (CApp function argument, result)
        TyArrow expected _result ->
            Left
                (invalid
                    ("the " <> description <> " expects "
                        <> Text.pack (show expected) <> " rather than Set"))
        actual ->
            Left
                (invalid
                    ("the " <> description <> " has too many arguments at "
                        <> Text.pack (show actual)))

materializeStructureNotionAtom
    :: (Text -> DeclarationError)
    -> StructureEnvironment.StructureEnvironment evidence
    -> SemanticStructureNotionHead
    -> Vector (CanonicalTerm ObjectId)
    -> Either DeclarationError (CanonicalTerm ObjectId)
materializeStructureNotionAtom invalid structures head' arguments = do
    interface <- maybe (Left (invalid "a registered structure notion head is not visible")) Right
        (StructureEnvironment.lookupStructureById (structureNotionHeadId head') structures)
    let registration = StructureInterface.structureInterfaceRegistration interface
        arity = 1 + Schema.resolvedSchemaParameterCount (StructurePredicate.pendingStructureSchema registration)
    unless (fromIntegral (Vector.length arguments) == arity)
        (Left (invalid "a registered structure notion head has the wrong arity"))
    pure (foldl' CApp (CGlobal (StructurePredicate.pendingStructurePredicate registration)) (toList arguments))

-- | All lookup indexes change together. Only the current declaration's
-- entries are added; an extension shares the inherited maps.
data ResolvedEnvironment evidence = ResolvedEnvironment
    { environmentGlobals :: !(Map SemanticGlobalKey ResolvedGlobalBinding)
    , environmentBindings :: !(Map GlobalBindingRef SemanticGlobalBinding)
    , environmentStructures :: !(StructureEnvironment.StructureEnvironment evidence)
    , environmentFields :: !(Map FieldId ObjectId)
    , environmentOperations :: !(Set (StructSymbol, ObjectId))
    , environmentRecursiveDefinitions :: !(Map ObjectId (Map GlobalBindingRef RecursionInterface.CheckedRecursiveDefinition))
    }

emptyResolvedEnvironment :: ResolvedEnvironment evidence
emptyResolvedEnvironment =
    ResolvedEnvironment Map.empty Map.empty StructureEnvironment.emptyStructureEnvironment Map.empty Set.empty Map.empty

logicalBuilderGlobals
    :: BuilderState evidence -> Map SemanticGlobalKey ResolvedGlobalBinding
logicalBuilderGlobals = environmentGlobals . logicalBuilderEnvironment

logicalBuilderStructures
    :: BuilderState evidence -> StructureEnvironment.StructureEnvironment evidence
logicalBuilderStructures = environmentStructures . logicalBuilderEnvironment

lookupResolvedStructurePhrase
    :: Schema.StructurePhrase -> StructureEnvironment.StructureEnvironment evidence -> Maybe ResolvedStructure
lookupResolvedStructurePhrase phrase environment = ResolvedStructure . StructureInterface.structureInterfaceRegistration
    <$> StructureEnvironment.lookupStructureByPhrase phrase environment

allResolvedStructures :: BuilderState evidence -> [ResolvedStructure]
allResolvedStructures = map (ResolvedStructure . StructureInterface.structureInterfaceRegistration)
    . Map.elems . StructureEnvironment.structureEnvironmentInterfaces . logicalBuilderStructures

resolveVisibleStructureIdLowering :: StructureId -> LoweringDriver (Maybe ResolvedStructure)
resolveVisibleStructureIdLowering identity = withLoweringBuilder \builder ->
    ResolvedStructure . StructureInterface.structureInterfaceRegistration
        <$> StructureEnvironment.lookupStructureById identity (logicalBuilderStructures builder)

structureEnvironmentLowering :: LoweringDriver (StructureEnvironment.StructureEnvironment PlanningEvidence)
structureEnvironmentLowering = withLoweringBuilder logicalBuilderStructures

-- | The shared checked semantic state.  The evidence parameter makes the
-- distinction between admitted authority and future inert planning data
-- visible without duplicating lookup, collision, closure, or delta logic.
data BuilderState evidence = BuilderState
    { logicalBuilderIdentity :: !BuilderIdentity
    , logicalBuilderFoundation :: !CheckedFoundation
    , logicalBuilderTheory :: !TheoryId
    , logicalBuilderOwner :: !ModuleName
    , logicalBuilderDirectSemanticInputs :: ![SemanticInterfaceId]
    , logicalBuilderPrefix :: !PrefixContextId
    , logicalBuilderObjectClosure :: !CheckedObjectClosure
    , logicalBuilderFacts
        :: !(Map
            SemanticFactOccurrenceFingerprint
            (FactEntry evidence))
    , logicalBuilderCompositions :: !Calculation.CompositionRegistry
    , logicalBuilderAliases
        :: !(Map SemanticName ImportedAliasBinding)
    , logicalBuilderEnvironment :: !(ResolvedEnvironment evidence)
    , logicalBuilderDefinitionViews
        :: !(Map
            (ObjectId, DefinitionViewKind)
            SemanticFactOccurrenceFingerprint)
    , logicalBuilderFormationCatalog :: !(FormationCatalog.Catalog
        (Either Notion.FormationRuleSource FormationCatalog.LocalProducerIx))
    , logicalBuilderFormationDescriptions :: !FormationDescriptions
    , logicalBuilderLocalFormationRules :: ![PreparedFormationRule]
    , logicalBuilderFormationPreparationWork :: !Natural
    , logicalBuilderFormationPreparationDiagnostics :: !FormationDiagnostics.Diagnostics
    , logicalBuilderRegistrations :: !BuilderRegistrationIndex
    , logicalBuilderDeltas :: ![DeclarationInterfaceDelta]
    , logicalBuilderNextDeclaration :: !Natural
    , logicalBuilderNextFact :: !Natural
    , logicalBuilderNextInvocation :: !Natural
    }

-- | The only production builder in this milestone.  Capability-consuming
-- operations below accept this admitted instantiation, never a polymorphic
-- 'BuilderState'.
type LogicalBuilder = BuilderState BuilderFactAuthorization

-- | Public semantic contract and strict declaration-stage provenance for a
-- prospective fact.  It deliberately contains no builder identity, prefix,
-- declaration invocation, pending authorization, or minting capability.
data PlanningProvenance = PlanningProvenance
    !DeclarationSlot
    !CandidateStage
    !FactSlot
    deriving stock (Eq)

data PlanningEvidence = PlanningEvidence
    !FactAuthority
    !(Maybe DirectAuthorization)
    !(Maybe PlanningProvenance)

data StructureProjectionLawIntegrityError
    = StablePlanningDirectAuthorizationMissing
        !SemanticFactOccurrenceFingerprint
    | StructureProjectionReconstructedTargetInvalid
    | StructureProjectionReconstructedTargetNotProposition !CoreType
    | StructureProjectionGeneratedLawUnavailable
        !(FrozenCheckedCore ObjectId)
    deriving stock (Show, Eq)

-- Read-only elaboration projection. This carries checked mathematics, not
-- admitted fact evidence; all theorem capabilities still come from a builder.
newtype ResolvedStructure = ResolvedStructure StructurePredicate.PendingStructureRegistration
    deriving stock (Show, Eq)

resolvedStructureRegistration :: ResolvedStructure -> StructurePredicate.PendingStructureRegistration
resolvedStructureRegistration (ResolvedStructure registration) = registration

resolvedStructureSchema :: ResolvedStructure -> Schema.ResolvedStructureSchema
resolvedStructureSchema = StructurePredicate.pendingStructureSchema . resolvedStructureRegistration

resolvedStructurePredicate :: ResolvedStructure -> ObjectId
resolvedStructurePredicate = StructurePredicate.pendingStructurePredicate . resolvedStructureRegistration

-- | One stored field in the complete inherited presentation used by generated
-- record laws.  The symbol is diagnostic metadata; stable object identities
-- form the semantic key.
data ResolvedRecordShapeField = ResolvedRecordShapeField
    !FieldId
    !ObjectId
    !ObjectId
    !StructSymbol
    deriving stock (Show, Eq)

data ResolvedRecordShape = ResolvedRecordShape
    !StructureId !SemanticRecordShapeKey ![ResolvedRecordShapeField]
    deriving stock (Show, Eq)

resolvedRecordShapeFields
    :: ResolvedRecordShape
    -> [ResolvedRecordShapeField]
resolvedRecordShapeFields (ResolvedRecordShape _ _ fields) = fields

resolvedRecordShapeKey
    :: ResolvedRecordShape
    -> SemanticRecordShapeKey
resolvedRecordShapeKey (ResolvedRecordShape _ key _) = key

resolvedRecordShapeFieldIdentity
    :: ResolvedRecordShapeField
    -> FieldId
resolvedRecordShapeFieldIdentity
        (ResolvedRecordShapeField identity _selector _projection _symbol) =
    identity

resolvedRecordShapeFieldSelector
    :: ResolvedRecordShapeField
    -> ObjectId
resolvedRecordShapeFieldSelector
        (ResolvedRecordShapeField _identity selector _projection _symbol) =
    selector

resolvedRecordShapeFieldProjection
    :: ResolvedRecordShapeField
    -> ObjectId
resolvedRecordShapeFieldProjection
        (ResolvedRecordShapeField _identity _selector projection _symbol) =
    projection

resolvedRecordShapeFieldSymbol
    :: ResolvedRecordShapeField
    -> StructSymbol
resolvedRecordShapeFieldSymbol
        (ResolvedRecordShapeField _identity _selector _projection symbol) =
    symbol

data ResolvedStructurePredicateApplication =
    ResolvedStructurePredicateApplication
        !ResolvedStructure
        !(CanonicalTerm ObjectId)
        ![CanonicalTerm ObjectId]
    deriving stock (Show, Eq)

resolvedStructurePredicateApplicationStructure
    :: ResolvedStructurePredicateApplication
    -> ResolvedStructure
resolvedStructurePredicateApplicationStructure
        (ResolvedStructurePredicateApplication structure _subject _parameters) =
    structure

resolvedStructurePredicateApplicationSubject
    :: ResolvedStructurePredicateApplication
    -> CanonicalTerm ObjectId
resolvedStructurePredicateApplicationSubject
        (ResolvedStructurePredicateApplication _structure subject _parameters) =
    subject

resolvedStructurePredicateApplicationParameters
    :: ResolvedStructurePredicateApplication
    -> [CanonicalTerm ObjectId]
resolvedStructurePredicateApplicationParameters
        (ResolvedStructurePredicateApplication _structure _subject parameters) =
    parameters

data StructurePredicateResolutionError
    = AmbiguousVisibleStructurePredicate !ObjectId
    deriving stock (Show, Eq)

resolvedStructureFieldProjection :: StructSymbol -> ResolvedStructure -> Maybe ObjectId
resolvedStructureFieldProjection symbol structure = snd <$> resolvedStructureField symbol structure

resolvedStructureField :: StructSymbol -> ResolvedStructure -> Maybe (FieldId, ObjectId)
resolvedStructureField symbol structure = do
    field <- resolveField symbol structure
    pure (Schema.resolvedFieldIdentity field, Schema.resolvedFieldProjection field)

resolveField :: StructSymbol -> ResolvedStructure -> Maybe Schema.ResolvedField
resolveField symbol structure = do
    let schema = resolvedStructureSchema structure
    identity <- Map.lookup symbol (Schema.resolvedSchemaFieldRoles schema)
    Map.lookup identity (Schema.resolvedSchemaFields schema)

resolvedStructureFieldSlot :: StructSymbol -> ResolvedStructure -> Maybe StructureFieldSlot
resolvedStructureFieldSlot symbol structure = Schema.resolvedFieldSlot <$> resolveField symbol structure

resolvedStructureFieldSelector :: StructSymbol -> ResolvedStructure -> Maybe ObjectId
resolvedStructureFieldSelector symbol structure = Schema.resolvedFieldSelector <$> resolveField symbol structure

resolvedStructureFieldOrder :: ResolvedStructure -> [StructSymbol]
resolvedStructureFieldOrder structure =
    [Schema.resolvedFieldSymbol field
    | identity <- Schema.resolvedPresentationFieldOrder (Schema.resolvedSchemaPresentation schema)
    , field <- maybeToList (Map.lookup identity (Schema.resolvedSchemaFields schema))]
  where
    schema = resolvedStructureSchema structure

resolvedStructureFieldProjections :: ResolvedStructure -> Map StructSymbol ObjectId
resolvedStructureFieldProjections = fmap snd . resolvedStructureFields

resolvedStructureFields :: ResolvedStructure -> Map StructSymbol (FieldId, ObjectId)
resolvedStructureFields structure = Map.fromList
    [(Schema.resolvedFieldSymbol field, (Schema.resolvedFieldIdentity field, Schema.resolvedFieldProjection field))
    | field <- Map.elems (Schema.resolvedSchemaFields (resolvedStructureSchema structure))]

resolvedStructureFieldResources :: ResolvedStructure -> Map StructSymbol (FieldId, ObjectId, ObjectId)
resolvedStructureFieldResources structure = Map.fromList
    [(Schema.resolvedFieldSymbol field,
        (Schema.resolvedFieldIdentity field, Schema.resolvedFieldSelector field, Schema.resolvedFieldProjection field))
    | field <- Map.elems (Schema.resolvedSchemaFields (resolvedStructureSchema structure))]


data VampireResolverMode
    = SynchronousVampireResolution
        (forall local origin.
            NonEmpty
                (Provers.PreparedTypedProverTask
                    SemanticFactOccurrenceFingerprint
                    local
                    origin
                    ObjectId)
            -> IO
                (NonEmpty
                    Provers.VampireResolution))
    | AsynchronousVampireSubmission
        (NonEmpty VampireSubmission
            -> IO (NonEmpty Provers.VampireHandle))

data VampireResolver = VampireResolver !VampireResolverMode

data VampireSubmission = VampireSubmission
    !Location
    !Provers.PreparedVerificationRequest

vampireBatchResolver
    :: (forall local origin.
        NonEmpty
            (Provers.PreparedTypedProverTask
                SemanticFactOccurrenceFingerprint
                local
                origin
                ObjectId)
        -> IO
            (NonEmpty
                Provers.VampireResolution))
    -> VampireResolver
vampireBatchResolver resolve =
    VampireResolver (SynchronousVampireResolution resolve)

-- | Production submission-only resolver.  Retained-plan admission consumes
-- the submitted handles through its private synchronous replay resolver.
vampireSubmissionResolver
    :: (NonEmpty VampireSubmission
        -> IO (NonEmpty Provers.VampireHandle))
    -> VampireResolver
vampireSubmissionResolver submit =
    VampireResolver (AsynchronousVampireSubmission submit)

vampireResolver
    :: (forall local origin.
        Provers.PreparedTypedProverTask
            SemanticFactOccurrenceFingerprint
            local
            origin
            ObjectId
        -> IO
            Provers.VampireResolution)
    -> VampireResolver
vampireResolver resolve =
    vampireBatchResolver (traverse resolve)

resolveSynchronousVampireBatch
    :: VampireResolver
    -> NonEmpty
        (Provers.PreparedTypedProverTask
            SemanticFactOccurrenceFingerprint
            local
            origin
            ObjectId)
    -> IO
        (NonEmpty
            Provers.VampireResolution)
resolveSynchronousVampireBatch
        (VampireResolver mode) tasks =
    case mode of
        SynchronousVampireResolution resolve -> resolve tasks
        AsynchronousVampireSubmission{} ->
            throwPlanningIntegrity
                "asynchronous Vampire resolver reached synchronous admission"

validateVampireResolverResultCount
    :: Int
    -> NonEmpty value
    -> Either DeclarationError [value]
validateVampireResolverResultCount expected results
    | expected == actual =
        Right (NonEmpty.toList results)
    | otherwise =
        Left (VampireResolverBatchSizeMismatch expected actual)
  where
    actual = NonEmpty.length results

data DriverState = DriverState
    { driverResolver :: !VampireResolver
    , driverNaturalNumeralBasis :: !(Maybe NaturalNumeralBasis)
    , driverBuilder :: !LogicalBuilder
    , driverFormationRecorder :: !FormationDiagnostics.Recorder
    , driverPendingPrefix :: !PendingModulePrefix
    }

-- | Authority-free semantic state used while lowering checked declarations.
-- Existing admitted facts are projected to their public contracts; no
-- builder-local authorization capability crosses this boundary.
newtype ProspectiveBuilder = ProspectiveBuilder
    (BuilderState PlanningEvidence)

data LoweringState = LoweringState
    { loweringResolver :: !VampireResolver
    , loweringNaturalNumeralBasis :: !(Maybe NaturalNumeralBasis)
    , loweringFormationRecorder :: !FormationDiagnostics.Recorder
    , loweringBuilder :: !ProspectiveBuilder
    }

type CheckerEffects = '[ValidationCache, IOE]

type DeclarationEffects = Error DeclarationError : CheckerEffects

type LoweringDriver =
    Eff (State LoweringState : CheckerEffects)

newtype DriverDeclarationFailure =
    DriverDeclarationFailure DeclarationError

newtype DriverActionFailure failure =
    DriverActionFailure failure

type ModuleDriver failure =
    Eff
        ( Error (DriverActionFailure failure)
        : Error DriverDeclarationFailure
        : State DriverState
        : CheckerEffects
        )

-- | Run one complete authority-free planning action from the current admitted
-- input projection.  The prospective state advances throughout the action but
-- never mutates the authoritative module builder.
runProspectiveLoweringDriver
    :: LoweringDriver value
    -> ModuleDriver failure value
runProspectiveLoweringDriver action = do
    state <- State.get
    inject
        (State.evalState
            (LoweringState
                { loweringResolver = driverResolver state
                , loweringNaturalNumeralBasis =
                    driverNaturalNumeralBasis state
                , loweringFormationRecorder = driverFormationRecorder state
                , loweringBuilder =
                    projectLogicalBuilder (driverBuilder state)
                })
            action)

projectLogicalBuilder :: LogicalBuilder -> ProspectiveBuilder
projectLogicalBuilder builder = ProspectiveBuilder builder
    { logicalBuilderFacts = projected
    , logicalBuilderEnvironment = checkedEvidenceRebind builderEvidenceDirect planningEvidenceDirect
        projected (logicalBuilderEnvironment builder)
    }
  where
    projected = fmap projectFact (logicalBuilderFacts builder)
    projectFact (FactEntry proposition occurrence (BuilderFactAuthorization _ _ certificate)) =
        FactEntry proposition occurrence (PlanningEvidence (semanticFactAuthority occurrence)
            (Just (validationDirectAuthorization certificate)) Nothing)

-- These transitions preserve metadata and direct contracts from private,
-- already checked registries. They perform no mathematical revalidation.
checkedEvidenceRebind
    :: (old -> Maybe DirectAuthorization) -> (new -> Maybe DirectAuthorization)
    -> Map SemanticFactOccurrenceFingerprint (FactEntry new)
    -> ResolvedEnvironment old -> ResolvedEnvironment new
checkedEvidenceRebind oldDirect newDirect facts environment =
    case StructureEnvironment.rebindStructureEnvironmentEvidence oldDirect newDirect
            (structureOccurrenceRegistry facts) (environmentStructures environment) of
        Left failure -> impossible ("checked structure evidence conversion changed its contract: " <> show failure)
        Right rebound -> environment{environmentStructures = rebound}

data DriverFailure failure
    = DriverDeclarationFailed !DeclarationError
    | DriverActionFailed !failure
    deriving stock (Show, Eq)

data DriverResult failure value
    = DriverSucceeded
        !value
        !ImportedModuleEvidence
        !PendingModulePrefix
    | DriverFailed
        !(DriverFailure failure)
        !PendingModulePrefix
    | DriverSealFailed
        !SemanticInterfaceError
        !PendingModulePrefix

data ImportedAliasOrigin = ImportedAliasOrigin
    !DeclarationSlot
    !SemanticFactOccurrenceFingerprint
    deriving stock (Show, Eq)

data ImportedAliasBinding = ImportedAliasBinding
    !SemanticFactOccurrenceFingerprint
    !ImportedAliasOrigin

-- Runtime identity names one exact admitted payload, including certificates.
-- It has no persisted, source-order, or semantic-identity meaning.
newtype ImportNodeId = ImportNodeId Unique
    deriving stock (Eq, Ord)

data ImportedModuleEvidence = ImportedModuleEvidence
    { evidenceNode :: !ImportNodeId
    , evidenceInterface :: !SemanticInterface
    , evidenceFinalPrefix :: !PrefixContextId
    , evidenceParents :: ![ImportedModuleEvidence]
    , evidenceLocal :: !CheckedImportDelta
    , evidenceContext :: !ImportContext
    }

evidenceClosure :: ImportedModuleEvidence -> CheckedObjectClosure
evidenceClosure = importObjects . evidenceContext

-- | Read-only materialization from sealed admitted evidence, including a warm
-- module whose invocation-local committed prefix need not retain fact rows.
evidenceFactTarget
    :: ImportedModuleEvidence -> SemanticFactOccurrenceFingerprint
    -> Maybe (FrozenCheckedCore ObjectId)
evidenceFactTarget evidence fingerprint = do
    FactEntry proposition _ _ <- Map.lookup fingerprint (importFacts (evidenceContext evidence))
    pure (checkedPropositionTerm proposition)

-- Presentation and diagnostics consume already normalized local schemas.
-- They never reconstruct inherited mathematics from persisted wire claims.
evidenceLocalStructureSchemas :: ImportedModuleEvidence -> [Schema.ResolvedStructureSchema]
evidenceLocalStructureSchemas evidence =
    [StructurePredicate.pendingStructureSchema (StructureInterface.structureInterfaceRegistration interface)
    | (interfaces, _, _) <- importLocalEnvironment (evidenceLocal evidence), interface <- interfaces]

-- Read-only admitted predicate identities, paired with their nominal owners.
evidenceLocalStructurePredicates :: ImportedModuleEvidence -> [(StructureId, ObjectId)]
evidenceLocalStructurePredicates evidence =
    [(Schema.resolvedSchemaId (StructurePredicate.pendingStructureSchema registration),
        StructurePredicate.pendingStructurePredicate registration)
    | (interfaces, _, _) <- importLocalEnvironment (evidenceLocal evidence)
    , interface <- interfaces
    , let registration = StructureInterface.structureInterfaceRegistration interface]

data CheckedDefinitionView = CheckedDefinitionView
    !ObjectId !DefinitionViewKind
    !SemanticFactOccurrenceFingerprint !PropositionId

type CheckedEnvironmentExports evidence =
    ([StructureInterface.CheckedStructureInterface evidence], [ResolvedGlobalBinding], [RecursionInterface.CheckedRecursiveDefinition])

data CheckedImportDelta = CheckedImportDelta
    { importLocalObjects :: !CheckedObjectContribution
    , importLocalFacts :: !(Map SemanticFactOccurrenceFingerprint
        (FactEntry ValidationCertificate))
    , importLocalCompositions :: ![(SemanticFactOccurrenceFingerprint, Calculation.CheckedCompositionLaw)]
    , importLocalAliases :: ![(SemanticAlias, ImportedAliasOrigin)]
    , importLocalEnvironment :: ![CheckedEnvironmentExports ValidationCertificate]
    , importLocalDefinitions :: ![CheckedDefinitionView]
    , importLocalRegistrations :: ![(OwnedRegistrationKey, Notion.FormationRuleSource)]
    , importLocalFormationRules :: ![PreparedFormationRule]
    }

data ImportContext = ImportContext
    { importObjects :: !CheckedObjectClosure
    , importFacts :: !(Map SemanticFactOccurrenceFingerprint
        (FactEntry ValidationCertificate))
    , importCompositions :: !Calculation.CompositionRegistry
    , importAliases :: !(Map SemanticName SemanticFactOccurrenceFingerprint)
    , importEnvironment :: !(ResolvedEnvironment ValidationCertificate)
    , importDefinitions :: !(Map (ObjectId, DefinitionViewKind) PropositionId)
    , importCovered :: !(Set ImportNodeId)
    }

data ImportWork = ImportWork
    { importNodeVisits :: !Int
    , importContributionInsertions :: !Int
    , importParentMemoHits :: !Int
    , importParentMemoMisses :: !Int
    , importObjectClosureChecks :: !Int
    , importPropositionChecks :: !Int
    , importCompositionChecks :: !Int
    , importOccurrenceChecks :: !Int
    , importEnvironmentMaterializations :: !Int
    , importGlobalTargetChecks :: !Int
    , importStructureChecks :: !Int
    , importStructureInputChecks :: !Int
    , importStructurePredicateChecks :: !Int
    , importDefinitionChecks :: !Int
    , importRegistrationChecks :: !Int
    , importFormationPreparationWork :: !Natural
    , importFormationPreparationMaximum :: !Natural
    , importFormationPreparationRejectedDebit :: !Natural
    }
    deriving stock (Show, Eq)

emptyImportWork :: ImportWork
emptyImportWork = ImportWork 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

addImportWork :: ImportWork -> ImportWork -> ImportWork
addImportWork left right = ImportWork
    { importNodeVisits = importNodeVisits left + importNodeVisits right
    , importContributionInsertions = importContributionInsertions left + importContributionInsertions right
    , importParentMemoHits = importParentMemoHits left + importParentMemoHits right
    , importParentMemoMisses = importParentMemoMisses left + importParentMemoMisses right
    , importObjectClosureChecks = importObjectClosureChecks left + importObjectClosureChecks right
    , importPropositionChecks = importPropositionChecks left + importPropositionChecks right
    , importCompositionChecks = importCompositionChecks left + importCompositionChecks right
    , importOccurrenceChecks = importOccurrenceChecks left + importOccurrenceChecks right
    , importEnvironmentMaterializations = importEnvironmentMaterializations left + importEnvironmentMaterializations right
    , importGlobalTargetChecks = importGlobalTargetChecks left + importGlobalTargetChecks right
    , importStructureChecks = importStructureChecks left + importStructureChecks right
    , importStructureInputChecks = importStructureInputChecks left + importStructureInputChecks right
    , importStructurePredicateChecks = importStructurePredicateChecks left + importStructurePredicateChecks right
    , importDefinitionChecks = importDefinitionChecks left + importDefinitionChecks right
    , importRegistrationChecks = importRegistrationChecks left + importRegistrationChecks right
    , importFormationPreparationWork = importFormationPreparationWork left + importFormationPreparationWork right
    , importFormationPreparationMaximum = max (importFormationPreparationMaximum left) (importFormationPreparationMaximum right)
    , importFormationPreparationRejectedDebit = max (importFormationPreparationRejectedDebit left) (importFormationPreparationRejectedDebit right)
    }

data ImportCheck = ImportCheck
    !CheckedFoundation
    !(MVar.MVar (Map [ImportNodeId] ImportContext))
    !(IORef ImportWork)
    !FormationDiagnostics.Report

newImportCheck :: CheckedFoundation -> IO ImportCheck
newImportCheck foundation =
    ImportCheck foundation <$> MVar.newMVar Map.empty <*> newIORef emptyImportWork <*> FormationDiagnostics.newReport

importCheckFoundation :: ImportCheck -> CheckedFoundation
importCheckFoundation (ImportCheck foundation _ _ _) = foundation

importCheckWork :: ImportCheck -> IO ImportWork
importCheckWork (ImportCheck _theory _memo work _) = readIORef work

recordImportWork :: ImportCheck -> ImportWork -> IO ()
recordImportWork (ImportCheck _theory _memo reference _) work =
    atomicModifyIORef' reference (\current -> (addImportWork current work, ()))

finishFormationReport :: ImportCheck -> IO ()
finishFormationReport (ImportCheck _ _ _ report) = FormationDiagnostics.finishReport report

importFormationReport :: ImportCheck -> FormationDiagnostics.Report
importFormationReport (ImportCheck _ _ _ report) = report

-- The session is used only while preparing/checking this consumer. Sealed
-- evidence retains the immutable context and parents, never the session.
data PreparedImports = PreparedImports
    !ImportCheck ![ImportedModuleEvidence] !ImportContext

preparedImportIds :: PreparedImports -> [SemanticInterfaceId]
preparedImportIds (PreparedImports _check parents _context) =
    semanticInterfaceAssertedId . evidenceInterface <$> parents

emptyImportContext :: TheoryId -> ImportContext
emptyImportContext theory =
    case validateObjectClosure theory [] of
        Left _ -> impossible "empty import closure is invalid"
        Right closure -> ImportContext closure Map.empty Calculation.emptyCompositionRegistry Map.empty
            emptyResolvedEnvironment Map.empty Set.empty

prepareImports
    :: ImportCheck
    -> [ImportedModuleEvidence]
    -> IO (Either DeclarationError PreparedImports)
prepareImports check@(ImportCheck foundation memo _work _) parents =
    case traverse_ checkTheory parents of
        Left failure -> pure (Left failure)
        Right () -> do
            cached <- MVar.withMVar memo (pure . Map.lookup key)
            case cached of
                Just context -> do
                    recordImportWork check emptyImportWork{importParentMemoHits = 1}
                    pure (Right (PreparedImports check parents context))
                Nothing -> do
                    let (result, work) = composeParents theory parents
                    recordImportWork check work{importParentMemoMisses = 1}
                    case result of
                        Left _ -> pure (Left (diagnoseImports theory parents Nothing))
                        Right context -> do
                            -- Demand map roots before publication, outside the
                            -- lock. Never deep-force the recursive parent graph.
                            completed <- Exception.evaluate context
                            winner <- MVar.modifyMVar memo \entries ->
                                case Map.lookup key entries of
                                    Just existing -> pure (entries, existing)
                                    Nothing -> pure (Map.insert key completed entries, completed)
                            pure (Right (PreparedImports check parents winner))
  where
    theory = theoryId foundation
    key = evidenceNode <$> parents
    checkTheory parent =
        let actual = checkedObjectClosureTheory (evidenceClosure parent)
        in unless (actual == theory)
            (Left (ImportedEvidenceTheoryMismatch theory actual))

-- Only aliases and definition selections require an ordered diagnostic pass.
-- The successful path carries compatibility identities without provenance.
data ImportConflict
    = ImportAliasDisagreement
    | ImportDefinitionDisagreement
    | ImportContentDisagreement !DeclarationError

composeParents
    :: TheoryId
    -> [ImportedModuleEvidence]
    -> (Either ImportConflict ImportContext, ImportWork)
composeParents theory parents =
    PureState.runState (Except.runExceptT compose) emptyImportWork
  where
    compose = case parents of
        [] -> pure (emptyImportContext theory)
        [parent] -> pure (evidenceContext parent)
        firstParent : remaining ->
            let seed = foldl' larger firstParent remaining
            in foldM addMissing (evidenceContext seed) parents
    larger current candidate
        | contextWeight (evidenceContext candidate) > contextWeight (evidenceContext current) =
            candidate
        | otherwise = current
    addMissing context node = do
        PureState.lift (PureState.modify' \work ->
            work{importNodeVisits = importNodeVisits work + 1})
        if evidenceNode node `Set.member` importCovered context
            then pure context
            else do
                withParents <- foldM addMissing context (evidenceParents node)
                inserted <- Except.liftEither (insertImportDelta withParents (evidenceLocal node))
                PureState.lift (PureState.modify' \work -> work
                    {importContributionInsertions = importContributionInsertions work + 1})
                pure inserted{importCovered = Set.insert (evidenceNode node)
                    (importCovered inserted)}

contextWeight :: ImportContext -> Int
contextWeight context =
    Set.size (importCovered context) + checkedObjectCount (importObjects context)
        + Map.size (importFacts context) + Map.size (importAliases context)
        + Map.size (importDefinitions context)
        + Map.size (environmentGlobals environment)
        + Map.size (environmentBindings environment)
        + Map.size (StructureEnvironment.structureEnvironmentInterfaces (environmentStructures environment))
        + Map.size (environmentFields environment)
        + Set.size (environmentOperations environment)
  where
    environment = importEnvironment context

insertPortableFact
    :: Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate)
    -> FactEntry ValidationCertificate
    -> Either DeclarationError
        (Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate))
insertPortableFact facts incoming@(FactEntry proposition occurrence certificate) =
    case Map.lookup fingerprint facts of
        Nothing -> Right (Map.insert fingerprint incoming facts)
        Just (FactEntry oldProposition oldOccurrence oldCertificate)
            | oldOccurrence == occurrence
              && checkedPropositionId oldProposition == checkedPropositionId proposition
              && oldCertificate == certificate -> Right facts
            | otherwise -> Left (ImportedFactCollision fingerprint)
  where
    fingerprint = semanticFactFingerprint occurrence

insertImportDelta :: ImportContext -> CheckedImportDelta -> Either ImportConflict ImportContext
insertImportDelta context delta = do
    objects <- first (ImportContentDisagreement . DeclarationObjectValidationFailed)
        (insertCheckedObjectContribution (importObjects context) (importLocalObjects delta))
    facts <- first ImportContentDisagreement
        (foldM insertPortableFact (importFacts context) (importLocalFacts delta))
    compositions <- first ImportContentDisagreement
        (mergeCompositionLaws (importCompositions context) (importLocalCompositions delta))
    definitions <- foldM insertDefinition (importDefinitions context)
        (importLocalDefinitions delta)
    aliases <- foldM insertAlias (importAliases context) (importLocalAliases delta)
    environment <- first ImportContentDisagreement
        (foldM insertEnvironment (importEnvironment context) (importLocalEnvironment delta))
    pure context{importObjects = objects, importFacts = facts,
        importDefinitions = definitions, importAliases = aliases,
        importEnvironment = environment, importCompositions = compositions}
  where
    insertDefinition entries (CheckedDefinitionView object kind _target proposition) =
        case Map.lookup (object, kind) entries of
            Nothing -> Right (Map.insert (object, kind) proposition entries)
            Just existing | existing == proposition -> Right entries
            Just _ -> Left ImportDefinitionDisagreement
    insertAlias entries (alias, _origin) =
        case Map.lookup (semanticAliasName alias) entries of
            Nothing -> Right (Map.insert (semanticAliasName alias) (semanticAliasTarget alias) entries)
            Just existing | existing == semanticAliasTarget alias -> Right entries
            Just _ -> Left ImportAliasDisagreement
    insertEnvironment environment (structures, globals, definitions) = do
        withStructures <- insertResolvedEnvironmentStructures environment structures
        withGlobals <- foldM insertResolvedEnvironmentGlobal withStructures globals
        pure (installRecursiveDefinitions definitions withGlobals)

-- Error precedence is source-ordered, parent-before-child, then per node:
-- objects, facts, definitions, aliases, declaration environments. This fold
-- uses checked exports only and never creates a consumer or reruns admission.
diagnoseImports
    :: TheoryId -> [ImportedModuleEvidence] -> Maybe CheckedImportDelta
    -> DeclarationError
diagnoseImports theory parents local =
    case foldM visit (Set.empty, emptyImportContext theory, Map.empty, Map.empty) parents
            >>= \state -> maybe (Right state) (insertLocal state) local of
        Left failure -> failure
        Right _ -> impossible "checked import composition and diagnostics disagree"
  where
    visit state@(seen, _, _, _) node
        | evidenceNode node `Set.member` seen = Right state
        | otherwise = do
            prior <- foldM visit state (evidenceParents node)
            (included, context, aliases, definitions) <- insertLocal prior (evidenceLocal node)
            pure (Set.insert (evidenceNode node) included, context, aliases, definitions)
    insertLocal (seen, context, aliases, definitions) delta = do
        objects <- first DeclarationObjectValidationFailed
            (insertCheckedObjectContribution (importObjects context) (importLocalObjects delta))
        facts <- foldM insertPortableFact (importFacts context) (importLocalFacts delta)
        compositions <- mergeCompositionLaws (importCompositions context) (importLocalCompositions delta)
        selected <- foldM (insertDefinition facts) definitions (importLocalDefinitions delta)
        named <- foldM (insertAlias facts) aliases (importLocalAliases delta)
        environment <- foldM insertEnvironment (importEnvironment context) (importLocalEnvironment delta)
        pure (seen, context{importObjects = objects, importFacts = facts,
            importEnvironment = environment, importCompositions = compositions}, named, selected)
    insertDefinition facts entries (CheckedDefinitionView object kind target proposition) =
        case Map.lookup (object, kind) entries of
            Nothing -> Right (Map.insert (object, kind) target entries)
            Just existing -> case Map.lookup existing facts of
                Just (FactEntry checked _ _) | checkedPropositionId checked == proposition -> Right entries
                _ -> Left (DefinitionViewConflict object kind existing target)
    insertAlias facts entries (alias, origin) = do
        let target = semanticAliasTarget alias
            name = semanticAliasName alias
        unless (Map.member target facts) (Left (ImportedAliasTargetMissing target))
        case Map.lookup name entries of
            Nothing -> Right (Map.insert name (ImportedAliasBinding target origin) entries)
            Just (ImportedAliasBinding old oldOrigin)
                | old == target -> Right entries
                | otherwise -> Left (ImportedAliasCollision name oldOrigin origin)
    insertEnvironment environment (structures, globals, definitions) = do
        withStructures <- insertResolvedEnvironmentStructures environment structures
        withGlobals <- foldM insertResolvedEnvironmentGlobal withStructures globals
        pure (installRecursiveDefinitions definitions withGlobals)

orderedLocalExports :: [ImportedModuleEvidence] -> [CheckedImportDelta]
orderedLocalExports parents = reverse (snd (foldl' visit (Set.empty, []) parents))
  where
    visit state@(seen, _) node
        | evidenceNode node `Set.member` seen = state
        | otherwise =
            let (included, exports) = foldl' visit state (evidenceParents node)
            in (Set.insert (evidenceNode node) included, evidenceLocal node : exports)

initializeImportedConsumer
    :: PreparedImports -> LogicalBuilder
    -> (Either DeclarationError LogicalBuilder, FormationDiagnostics.Measurement)
initializeImportedConsumer (PreparedImports _check parents context) builder =
    PureState.runState (Except.runExceptT (foldM install initialized (orderedLocalExports parents)))
        FormationDiagnostics.emptyMeasurement
  where
    initialized = builder
        { logicalBuilderObjectClosure = importObjects context
        , logicalBuilderEnvironment = checkedEvidenceRebind (Just . validationDirectAuthorization)
            builderEvidenceDirect authorizedFacts (importEnvironment context)
        , logicalBuilderFacts = authorizedFacts
        , logicalBuilderCompositions = importCompositions context
        }
    authorizedFacts = Map.map authorize (importFacts context)
    authorize (FactEntry proposition occurrence certificate) =
        FactEntry proposition occurrence
            (BuilderFactAuthorization (logicalBuilderIdentity builder)
                (semanticFactSlot occurrence) certificate)
    install current delta = do
        -- Checked exports retain declaration order. All registrations from
        -- one real owner share its preparation allowance, including derived
        -- indices; no per-phase or per-registration budget is restarted.
        (catalog, descriptions, work, diagnostics) <- foldM installOwner
            (logicalBuilderFormationCatalog current, logicalBuilderFormationDescriptions current, 0,
                logicalBuilderFormationPreparationDiagnostics current)
            (List.groupBy (\a b -> preparedFormationSlot a == preparedFormationSlot b)
                (importLocalFormationRules delta))
        pure current
            { logicalBuilderFormationCatalog = catalog
            , logicalBuilderFormationDescriptions = descriptions
            , logicalBuilderFormationPreparationWork = logicalBuilderFormationPreparationWork current + work
            , logicalBuilderFormationPreparationDiagnostics = diagnostics
            , logicalBuilderAliases = foldl'
                (\entries (alias, origin) -> Map.insertWith (\_ old -> old)
                    (semanticAliasName alias) (ImportedAliasBinding (semanticAliasTarget alias) origin) entries)
                (logicalBuilderAliases current) (importLocalAliases delta)
            , logicalBuilderDefinitionViews = foldl'
                (\entries (CheckedDefinitionView object kind target _) ->
                    Map.insertWith (\_ old -> old) (object, kind) target entries)
                (logicalBuilderDefinitionViews current) (importLocalDefinitions delta)
            , logicalBuilderRegistrations = foldl' (flip insertBuilderRegistration)
                (logicalBuilderRegistrations current) (importLocalRegistrations delta)
            }
    installOwner state [] = pure state
    installOwner (known, descriptions, total, diagnostics) entries@(entry : _) = do
        let slot = preparedFormationSlot entry
            (result, used) = boundedFormationPreparation slot \charge ->
                prepareFormationBatch slot charge entries descriptions known diagnostics
        let counts = either (const FormationDiagnostics.emptyDiagnostics)
                (\(_, _, after) -> FormationDiagnostics.subtractDiagnostics after diagnostics) result
        PureState.modify' (`FormationDiagnostics.addMeasurement` declarationPreparationMeasurement used counts (preparationRejectedDebit result))
        (next, nextDescriptions, after) <- Except.liftEither result
        pure (next, nextDescriptions, total + used, after)

localAliasExports :: SemanticInterface -> [(SemanticAlias, ImportedAliasOrigin)]
localAliasExports interface =
    [ (alias, ImportedAliasOrigin (declarationDeltaSlot delta) (semanticAliasTarget alias))
    | delta <- semanticInterfaceDeclarations interface
    , alias <- declarationDeltaAliases delta
    ]

localEnvironmentExports
    :: SemanticInterface -> ResolvedEnvironment evidence
    -> Either DeclarationError [CheckedEnvironmentExports evidence]
localEnvironmentExports interface environment = traverse
    (localDeclarationEnvironmentExports environment) (semanticInterfaceDeclarations interface)

localDeclarationEnvironmentExports
    :: ResolvedEnvironment evidence -> DeclarationInterfaceDelta
    -> Either DeclarationError (CheckedEnvironmentExports evidence)
localDeclarationEnvironmentExports environment delta = do
    let owned = declarationDeltaEnvironment delta
        slot = declarationDeltaSlot delta
    structures <- for (semanticEnvironmentStructures owned) \wire -> do
        let identity = structureId (StructureOrigin (declarationSlotModule slot) (declarationSlotOrdinal slot) (structureWireSlot wire))
        case StructureEnvironment.lookupStructureById identity (environmentStructures environment) of
            Just resolved
                | StructurePredicate.pendingStructurePredicate (StructureInterface.structureInterfaceRegistration resolved) == structureWirePredicate wire
                  && StructureInterface.structureInterfaceLawIndex resolved == structureWireLawIndex wire
                  && StructureInterface.structureInterfaceResourceIndex resolved == structureWireResourceIndex wire -> Right resolved
            _ -> Left (ImportedEvidenceLocalInvariant "local structure association")
    globals <- for (semanticEnvironmentBindings owned) \binding ->
        case Map.lookup (semanticGlobalBindingKey binding) (environmentGlobals environment) of
            Just resolved
                | resolvedBindingRef resolved == globalBindingRef slot (semanticGlobalBindingKey binding)
                  && resolvedBindingDeclaration resolved == binding -> Right resolved
            _ -> Left (ImportedEvidenceLocalInvariant "local global association")
    definitions <- for [resolved | resolved <- globals,
            isJust (semanticGlobalBindingRecursion (resolvedBindingDeclaration resolved))] \resolved ->
        maybe (Left (ImportedEvidenceLocalInvariant "local recursive definition association")) pure
            (Map.lookup (semanticGlobalTargetObject (semanticGlobalBindingTarget (resolvedBindingDeclaration resolved)))
                (environmentRecursiveDefinitions environment) >>= Map.lookup (resolvedBindingRef resolved))
    pure (structures, globals, definitions)

admitCachedModuleEvidence
    :: PreparedImports -> SemanticInterface -> [AssertedObject]
    -> [StoredPropositionCandidate] -> [ValidationCertificate]
    -> IO (Either DeclarationError ImportedModuleEvidence)
admitCachedModuleEvidence prepared@(PreparedImports check parents context)
        interface objects propositions certificates = do
    let restored = for [(declarationDeltaSlot delta, wire) | delta <- declarations
            , wire <- semanticEnvironmentStructures (declarationDeltaEnvironment delta)] \(slot, wire) ->
            ((,) (slot, structureWireSlot wire)) <$>
                first StructureDeclarationInvalid (materializeStructureWirePresentation wire)
    case restored of
        Left failure -> pure (Left failure)
        Right presentations -> do
            (result, work) <- FormationDiagnostics.withRecorder (importFormationReport check) \recorder ->
                FormationDiagnostics.withPhase recorder FormationDiagnostics.DeclarationPreparation do
                    let completed@(result, work) = PureState.runState
                            (Except.runExceptT (admitLocal (Map.fromList presentations))) emptyImportWork
                    result `seq` FormationDiagnostics.recordMeasurement recorder
                        ((declarationPreparationMeasurement (importFormationPreparationMaximum work) FormationDiagnostics.emptyDiagnostics (importFormationPreparationRejectedDebit work))
                            { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork
                                FormationDiagnostics.DeclarationPreparation (importFormationPreparationWork work)
                                FormationDiagnostics.emptyDiagnostics })
                    pure completed
            recordImportWork check work
            case result of
                Left failure -> pure (Left failure)
                Right (local, admitted) -> do
                    identity <- ImportNodeId <$> newUnique
                    pure (Right (ImportedModuleEvidence identity interface final parents local
                        admitted{importCovered = Set.insert identity (importCovered admitted)}))
  where
    declarations = semanticInterfaceDeclarations interface
    final = finalImportPrefix prepared interface
    theory = checkedObjectClosureTheory (importObjects context)
    objectMap = Map.fromList [(assertedObjectId object, object) | object <- objects]
    propositionMap = Map.fromList [(storedPropositionCandidateId candidate, candidate) | candidate <- propositions]
    admitLocal presentations = do
        unless (semanticInterfaceDirectInputs interface == preparedImportIds prepared)
            (Except.throwError (ImportedEvidenceDirectMismatch (semanticInterfaceDirectInputs interface) (preparedImportIds prepared)))
        localObjects <- for (concatMap declarationDeltaObjects declarations) \identity ->
            maybe (Except.throwError (ImportedEvidenceObjectMissing identity)) pure (Map.lookup identity objectMap)
        closure <- admissionCheck emptyImportWork{importObjectClosureChecks = 1}
            (first DeclarationObjectValidationFailed (extendObjectClosure (importObjects context) localObjects))
        checkedPropositions <- for (Set.toAscList (Set.fromList (concatMap declarationDeltaPropositions declarations))) \identity -> do
            candidate <- maybe (Except.throwError (ImportedEvidencePropositionMissing identity)) pure (Map.lookup identity propositionMap)
            checked <- admissionCheck emptyImportWork{importPropositionChecks = 1}
                (first DeclarationPropositionValidationFailed (validateStoredPropositionCandidate closure candidate))
            pure (identity, checked)
        let occurrences = concatMap declarationDeltaFacts declarations
            checked = Map.fromList checkedPropositions
        unless (length occurrences == length certificates) (Except.throwError ImportedEvidenceCertificateCountMismatch)
        facts <- for (zip occurrences certificates) \(occurrence, certificate) -> do
            let fingerprint = semanticFactFingerprint occurrence
            unless (validationTarget certificate == semanticFactAuthority occurrence)
                (Except.throwError (ImportedEvidenceCertificateTargetMismatch fingerprint))
            proposition <- maybe (Except.throwError (ImportedEvidencePropositionMissing (semanticFactProposition occurrence))) pure
                (Map.lookup (semanticFactProposition occurrence) checked)
            _ <- admissionCheck emptyImportWork{importOccurrenceChecks = 1}
                (first ImportedFactMaterializationFailed (Materialization.checkImportedOccurrence theory fingerprint occurrence proposition
                    (semanticFactAuthority occurrence)))
            pure (fingerprint, FactEntry proposition occurrence certificate)
        (admitted, reversedParts) <- foldM (admitDeclaration closure (Map.fromList facts) presentations)
            (context, []) declarations
        contribution <- Except.liftEither (first DeclarationObjectValidationFailed
            (checkedObjectContribution closure (concatMap declarationDeltaObjects declarations)))
        pure (combineLocalImportDeltas contribution (reverse reversedParts), admitted)
    admitDeclaration complete allFacts presentations (prior, parts) delta = do
        contribution <- Except.liftEither (first DeclarationObjectValidationFailed
            (checkedObjectContribution complete (declarationDeltaObjects delta)))
        closure <- Except.liftEither (first DeclarationObjectValidationFailed
            (insertCheckedObjectContribution (importObjects prior) contribution))
        let ownFingerprints = Set.fromList (semanticFactFingerprint <$> declarationDeltaFacts delta)
            ownFacts = Map.restrictKeys allFacts ownFingerprints
        facts <- Except.liftEither (foldM insertPortableFact (importFacts prior) ownFacts)
        environment <- materializeImportedEnvironmentDelta (importCheckFoundation check) closure facts
            presentations (importEnvironment prior) delta
        registry <- admissionCheck emptyImportWork{importCompositionChecks = Map.size ownFacts}
            (admitCompositionFacts closure environment (importCompositions prior) (Map.elems ownFacts))
        let compositions = List.filter (\(fingerprint,_) -> Set.member fingerprint ownFingerprints)
                (Calculation.compositionRegistryEntries registry)
        exports <- Except.liftEither (localDeclarationEnvironmentExports environment delta)
        definitions <- traverse (admissionCheck emptyImportWork{importDefinitionChecks = 1}
            . checkImportedDefinitionView closure facts . (,) delta) (declarationDeltaDefinitionViews delta)
        let slot = declarationDeltaSlot delta
        sources <- for (declarationDeltaRegistrations delta) \registration -> do
            source <- admissionCheck emptyImportWork{importRegistrationChecks = 1}
                (checkImportedRegistration closure facts environment registration)
            pure (registration, source)
        let (prepared, used) = boundedFormationPreparation slot \charge ->
                traverse (prepareRegistration facts slot charge) sources
        pairs <- admissionCheck emptyImportWork
            { importFormationPreparationWork = used
            , importFormationPreparationMaximum = used
            , importFormationPreparationRejectedDebit = preparationRejectedDebit prepared } prepared
        let aliases = [(alias, ImportedAliasOrigin slot (semanticAliasTarget alias)) | alias <- declarationDeltaAliases delta]
        for_ aliases \(alias, _) -> unless (Map.member (semanticAliasTarget alias) facts)
            (Except.throwError (ImportedAliasTargetMissing (semanticAliasTarget alias)))
        let local = CheckedImportDelta contribution ownFacts compositions aliases [exports] definitions
                (fst <$> pairs) (snd <$> pairs)
        case insertImportDelta prior local of
            Left _ -> do
                prefixContribution <- Except.liftEither (first DeclarationObjectValidationFailed
                    (checkedObjectContribution closure (concatMap (Set.toList . checkedObjectContributionIds . importLocalObjects) (local : parts))))
                Except.throwError (diagnoseImports theory parents (Just (combineLocalImportDeltas prefixContribution (reverse (local : parts)))))
            Right admitted -> pure (admitted, local : parts)
    prepareRegistration facts slot charge (registration, source) = do
        charge 1
        before <- PureState.lift PureState.get
        rule <- compileFormationRule (Just . validationDirectAuthorization) facts slot registration charge
        after <- PureState.lift PureState.get
        prepared <- prepareFormationRule charge slot (registrationBody registration) rule source (after - before)
        pure ((OwnedRegistrationKey slot registration, source), prepared)

combineLocalImportDeltas :: CheckedObjectContribution -> [CheckedImportDelta] -> CheckedImportDelta
combineLocalImportDeltas contribution parts = CheckedImportDelta contribution (Map.unions (importLocalFacts <$> parts))
    (concatMap importLocalCompositions parts) (concatMap importLocalAliases parts) (concatMap importLocalEnvironment parts)
    (concatMap importLocalDefinitions parts) (concatMap importLocalRegistrations parts)
    (concatMap importLocalFormationRules parts)

-- Count entry into the pure admission checks, including a rejected check.
-- Updates stay in a strict local state; the IO boundary publishes one total.
admissionCheck
    :: ImportWork
    -> Either DeclarationError value
    -> Except.ExceptT DeclarationError (PureState.State ImportWork) value
admissionCheck work result = do
    PureState.lift (PureState.modify' (`addImportWork` work))
    Except.liftEither result

finalImportPrefix :: PreparedImports -> SemanticInterface -> PrefixContextId
finalImportPrefix prepared interface =
    case initialPrefixContextId theory (semanticInterfaceOwner interface) (preparedImportIds prepared) of
        Left _ -> impossible "checked interface has invalid direct inputs"
        Right initial -> foldl' nextPrefixContextId initial (semanticInterfaceDeclarations interface)
  where
    PreparedImports _check _parents context = prepared
    theory = checkedObjectClosureTheory (importObjects context)

sealImportedModuleEvidence
    :: PreparedImports -> SemanticInterface -> PendingModulePrefix -> LogicalBuilder
    -> IO ImportedModuleEvidence
sealImportedModuleEvidence (PreparedImports _check parents context)
        interface prefix builder =
    case collectLocal of
        Left failure -> impossible ("fresh import sealing: " <> show failure)
        Right local -> do
            unless (pendingModulePrefixCurrent prefix == logicalBuilderPrefix builder)
                (impossible "fresh import prefix differs from its checked builder")
            -- The final builder already owns the extended closure/environment.
            -- Reuse them while adding only local portable facts and selections.
            facts <- either (impossible . show) pure
                (foldM insertPortableFact (importFacts context) (importLocalFacts local))
            identity <- ImportNodeId <$> newUnique
            let admitted = context
                    { importObjects = logicalBuilderObjectClosure builder
                    , importEnvironment = portableEnvironment
                    , importFacts = facts
                    , importCompositions = logicalBuilderCompositions builder
                    , importAliases = foldl'
                        (\entries (alias, _) -> Map.insert (semanticAliasName alias) (semanticAliasTarget alias) entries)
                        (importAliases context) (importLocalAliases local)
                    , importDefinitions = foldl'
                        (\entries (CheckedDefinitionView object kind _ proposition) ->
                            Map.insert (object, kind) proposition entries)
                        (importDefinitions context) (importLocalDefinitions local)
                    , importCovered = Set.insert identity (importCovered context)
                    }
            pure (ImportedModuleEvidence identity interface (logicalBuilderPrefix builder) parents local admitted)
  where
    declarations = semanticInterfaceDeclarations interface
    portableFacts = Map.map (\(FactEntry proposition occurrence (BuilderFactAuthorization _ _ certificate)) ->
        FactEntry proposition occurrence certificate) (logicalBuilderFacts builder)
    portableEnvironment = checkedEvidenceRebind builderEvidenceDirect (Just . validationDirectAuthorization)
        portableFacts (logicalBuilderEnvironment builder)
    collectLocal = do
        objects <- first DeclarationObjectValidationFailed
            (checkedObjectContribution (logicalBuilderObjectClosure builder)
                (concatMap declarationDeltaObjects declarations))
        facts <- for (concatMap declarationDeltaFacts declarations) \occurrence ->
            case Map.lookup (semanticFactFingerprint occurrence) (logicalBuilderFacts builder) of
                Just (FactEntry proposition actual (BuilderFactAuthorization owner slot certificate))
                    | actual == occurrence && owner == logicalBuilderIdentity builder
                      && slot == semanticFactSlot occurrence ->
                        Right (semanticFactFingerprint occurrence, FactEntry proposition occurrence certificate)
                _ -> Left (ImportedEvidenceLocalInvariant "local fact association")
        let portable = Map.fromList facts
        environment <- localEnvironmentExports interface portableEnvironment
        definitions <- for
            [view | delta <- declarations, view <- declarationDeltaDefinitionViews delta] \view ->
                case Map.lookup (semanticDefinitionViewTarget view) portable of
                    Just (FactEntry proposition _ _) -> Right (CheckedDefinitionView
                        (semanticDefinitionViewObject view) (semanticDefinitionViewKind view)
                        (semanticDefinitionViewTarget view) (checkedPropositionId proposition))
                    Nothing -> Left (ImportedEvidenceLocalInvariant "local definition association")
        let BuilderRegistrationIndex entries _ = logicalBuilderRegistrations builder
        registrations <- for
            [OwnedRegistrationKey (declarationDeltaSlot delta) registration
            | delta <- declarations, registration <- declarationDeltaRegistrations delta] \key ->
                (\source -> (key, source)) <$> maybe (Left (ImportedEvidenceLocalInvariant "local registration association")) Right
                    (Map.lookup key entries)
        let compositions = List.filter (\(fingerprint,_) -> Map.member fingerprint portable)
                (Calculation.compositionRegistryEntries (logicalBuilderCompositions builder))
        pure (CheckedImportDelta objects portable compositions (localAliasExports interface) environment definitions
            registrations (reverse (logicalBuilderLocalFormationRules builder)))

-- Fresh declarations and portable imports share this admission boundary.
-- The template interpreter owns substitution; this owner authenticates the
-- binding/provider views against the visible semantic environment.
prepareCheckedComposition
    :: CheckedObjectClosure -> ResolvedEnvironment evidence
    -> SemanticFactOccurrenceFingerprint -> FactSlot -> ScopedCheckedCore ObjectId -> SemanticRelationComposition
    -> Calculation.CalculationWork Identity Calculation.CheckedCompositionLaw
prepareCheckedComposition closure environment fingerprint origin =
    Calculation.prepareCompositionLaw (globalTypingFromClosure closure)
        (\context layout body expansion -> void (validateSourceTemplate closure environment
            (ImportedCompositionMetadataInvalid fingerprint) context layout body expansion)) origin

-- Authenticate written providers and their exact denotations before a source
-- description can participate in formation reasoning. Both compositions and
-- recursive branches use the existing source-template interpreter.
validateSourceTemplate
    :: CheckedObjectClosure -> ResolvedEnvironment evidence -> (Text -> DeclarationError)
    -> [CoreType] -> Vector Natural -> CanonicalTerm ObjectId -> AbbreviationExpansion
    -> Calculation.CalculationWork Identity (CanonicalTerm ObjectId)
validateSourceTemplate closure environment sourceError context layout body expansion = validateSource
  where
    typing = globalTypingFromClosure closure
    invalid message = Except.throwError (Calculation.CalculationInvalid message)
    charge = Calculation.chargeCalculationWork
    core operation = Calculation.calculationCoreWork operation
    liftExpansion operation = Calculation.calculationExpansionWork operation
    fromDeclaration result = either (invalid . Text.pack . show) pure result
    validateSource = do
        heads <- liftExpansion (SourceTemplate.sourceTemplateProviders expansion)
        entries <- for (Set.toAscList heads) \provider -> do
            charge 1
            case provider of
                GlobalSourceProvider reference -> do
                    let globals = environmentGlobals environment
                    charge (FormationTerms.indexWork (Map.size globals) 1)
                    binding <- maybe (invalid "a source provider is not visible") pure
                        (Map.lookup (globalBindingRefKey reference) globals)
                    unless (resolvedBindingRef binding == reference && resolvedBindingSourceProviderHead binding == Just provider)
                        (invalid "a source provider changed owner or family")
                    pure (Just (provider, semanticGlobalTargetObject (semanticGlobalBindingTarget (resolvedBindingDeclaration binding))))
                StructureFieldSourceProvider field projection -> do
                    charge (FormationTerms.indexWork (Map.size (environmentFields environment)) 1)
                    unless (Map.lookup field (environmentFields environment) == Just projection)
                        (invalid "a source field provider is not visible")
                    pure (Just (provider,projection))
                _ -> pure Nothing
        charge (fromIntegral (length context + Vector.length layout + length entries))
        let checking = SourceTerm.SourceTermCheckingContext typing context
            ordered = Map.fromList [(slot, SourceTerm.sourceTermOccurrence (CBound (fromIntegral index)) ty ())
                | (index,(slot,ty)) <- zip [0 :: Natural ..] (zip (toList layout) context)]
            actuals = Vector.fromList (Map.elems ordered)
            providers = Map.fromList (catMaybes entries)
        instance' <- liftExpansion (SourceTemplate.instantiateSourceTemplate checking providers Nowhere ()
            (SourceEvidence.WrittenOrigin Nowhere Nothing) layout actuals body expansion)
        case instance' of
            SourceTemplate.InstantiatedTerm value -> do
                validateTerm checking value
                pure (SourceTerm.sourceTermOccurrenceCore value)
            SourceTemplate.InstantiatedProposition formula evidence equalities -> do
                checkSame context formula body
                validateEvidence checking formula evidence
                for_ equalities \equality -> do
                    charge 1
                    selected <- select (Notion.sourceEqualityPath equality) formula
                    validateTerm checking (Notion.sourceEqualityLeft equality)
                    validateTerm checking (Notion.sourceEqualityRight equality)
                    checkSame context selected (Notion.sourceEqualityFormula equality)
                pure formula
    validateTerm checking term = void (core (\work -> SourceTerm.countedSealCanonicalSourceTermOccurrence work checking term))
    validateEvidence checking expected expression = charge 1 >> case expression of
        SourceEvidence.SourceResidual{} -> pure ()
        SourceEvidence.SourceInputs _ inputs -> for_ inputs \(SourceEvidence.SourceInput binders term) -> do
            charge (fromIntegral (length binders))
            -- The instantiated support description retains the same provider
            -- vocabulary as ordinary whole-source admission.
            actual <- fromDeclaration (materializeSetTermTemplate closure sourceError environment Right term)
            checked <- core (\work -> countedCheckScopedCanonicalCore typing work
                (binders <> SourceTerm.sourceTermBinderTypes checking) actual)
            unless (scopedCoreType checked == TySet) (invalid "a source support input is not set-valued")
            present <- SourceEvidence.sourceInputOccursWith (charge 1) binders actual expected
            unless present (invalid "a source support input does not occur in its formula")
        SourceEvidence.SourceWithInputs inputs body -> do
            validateEvidence checking expected (SourceEvidence.SourceInputs Nothing inputs)
            validateEvidence checking expected body
        SourceEvidence.SourceAtom assertion -> do
            let atom = Notion.sourceAssertionAtom assertion
            traverse_ (validateTerm checking) atom
            actual <- fromDeclaration (materializeAtomTemplate closure sourceError
                (environmentGlobals environment) (environmentStructures environment) SourceTerm.sourceTermOccurrenceCore atom)
            checkSame (SourceTerm.sourceTermBinderTypes checking) expected actual
        SourceEvidence.SourceAnd a b | CAnd left right <- expected ->
            validateEvidence checking left a >> validateEvidence checking right b
        SourceEvidence.SourceBind body | CForall TySet value <- expected ->
            validateEvidence checking{SourceTerm.sourceTermBinderTypes = TySet : SourceTerm.sourceTermBinderTypes checking} value body
        SourceEvidence.SourceExists body | CExists TySet value <- expected ->
            validateEvidence checking{SourceTerm.sourceTermBinderTypes = TySet : SourceTerm.sourceTermBinderTypes checking} value body
        SourceEvidence.SourceOr a b | COr left right <- expected ->
            validateEvidence checking left a >> validateEvidence checking right b
        SourceEvidence.SourceIff a b | CEq TyProp left right <- expected ->
            validateEvidence checking left a >> validateEvidence checking right b
        SourceEvidence.SourceRequire a b | CImp left right <- expected ->
            validateEvidence checking left a >> validateEvidence checking right b
        _ -> invalid "source evidence disagrees with its formula"
    checkSame context a b = do
        left <- core (\work -> countedCheckScopedCanonicalCore typing work context a) >>= Calculation.normalizeCalculationCore typing
        right <- core (\work -> countedCheckScopedCanonicalCore typing work context b) >>= Calculation.normalizeCalculationCore typing
        same <- core (\work -> countedScopedCoreIdentity work left right)
        unless same (invalid "source metadata disagrees with its checked term")
    select path formula = charge 1 >> case (path,formula) of
        (Notion.ConjunctionHere,_) -> pure formula
        (Notion.ConjunctionLeft rest,CAnd a _) -> select rest a
        (Notion.ConjunctionRight rest,CAnd _ b) -> select rest b
        _ -> invalid "a source equality is not a conjunct of its formula"

compositionAdmission
    :: SemanticFactOccurrenceFingerprint -> Calculation.CalculationWork Identity value
    -> Either DeclarationError value
compositionAdmission fingerprint action = first
    (ImportedCompositionMetadataInvalid fingerprint . Calculation.renderCalculationError)
    (fst (runIdentity (Calculation.runCalculationWork Calculation.defaultCompositionAdmissionWork action)))

admitCompositionFacts
    :: CheckedObjectClosure -> ResolvedEnvironment evidence -> Calculation.CompositionRegistry
    -> [FactEntry evidence] -> Either DeclarationError Calculation.CompositionRegistry
admitCompositionFacts closure environment = foldM add
  where
    add registry (FactEntry proposition occurrence _) = case semanticFactRelationComposition occurrence of
        Nothing -> pure registry
        Just _ | Calculation.compositionRegistryMember (semanticFactFingerprint occurrence) registry -> pure registry
        Just metadata -> compositionAdmission (semanticFactFingerprint occurrence) do
            law <- prepareCheckedComposition closure environment (semanticFactFingerprint occurrence) (semanticFactSlot occurrence)
                (embedClosedCore [] (checkedPropositionTerm proposition)) metadata
            Calculation.insertCompositionLaw (semanticFactFingerprint occurrence) law registry

mergeCompositionLaws
    :: Calculation.CompositionRegistry -> [(SemanticFactOccurrenceFingerprint, Calculation.CheckedCompositionLaw)]
    -> Either DeclarationError Calculation.CompositionRegistry
mergeCompositionLaws registry entries = foldM add registry (List.sortOn fst entries)
  where
    add current (fingerprint,law)
        | Calculation.compositionRegistryMember fingerprint current = Right current
        | otherwise = compositionAdmission fingerprint (Calculation.insertCompositionLaw fingerprint law current)

extendBuilderCompositions :: BuilderState evidence -> [FactEntry evidence] -> Either DeclarationError (BuilderState evidence)
extendBuilderCompositions builder facts = do
    registry <- first (\case
        ImportedCompositionMetadataInvalid fingerprint reason -> CompositionRegistrationInvalid fingerprint reason
        failure -> failure) (admitCompositionFacts (logicalBuilderObjectClosure builder) (logicalBuilderEnvironment builder)
            (logicalBuilderCompositions builder) facts)
    pure builder{logicalBuilderCompositions = registry}

checkImportedRegistration
    :: CheckedObjectClosure
    -> Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate)
    -> ResolvedEnvironment ValidationCertificate
    -> Registration SemanticFactOccurrenceFingerprint
    -> Either DeclarationError Notion.FormationRuleSource
checkImportedRegistration closure facts environment registration = do
    FactEntry _ occurrence certificate <- maybe (Left (missing fingerprint)) Right
        (Map.lookup fingerprint facts)
    let direct = validationDirectAuthorization certificate
        sourceProof = case direct of CheckedSourceProof{} -> True; _ -> False
        allowed = case registrationBody registration of
            RegisterProviderResult{} -> providerResultAuthority direct
            RegisterNotionView{} -> case semanticFactPurpose occurrence of
                GeneralFactPurpose -> case direct of
                    CheckedSourceProof{} -> True
                    CheckedKernelConstruction CheckedDefinitionProjection{} -> True
                    _ -> False
                StructureFactPurpose (Schema.StructureLawId identity key@Schema.ParentInheritanceLaw{}) ->
                    case (uncurry CheckedNotionViewTheorem <$> checkedIndexedStructureFact
                            (environmentStructures environment) facts (Just . validationDirectAuthorization) identity (Schema.StructureLawFact key)) of
                        Just (CheckedNotionViewTheorem _ indexed) -> indexed == occurrence
                        Nothing -> False
                StructureFactPurpose _ -> False
            _ -> sourceProof
    unless (semanticFactFingerprint occurrence == fingerprint
        && factAuthoritySafety (semanticFactAuthority occurrence) == cleanAuthoritySafety
        && allowed) (Left (invalid fingerprint))
    materializeRegistration (Just . validationDirectAuthorization) closure environment facts registration
  where
    fingerprint = registrationSource registration
    (missing, invalid) = case registrationBody registration of
        RegisterNotionView{} -> (ImportedNotionViewFactMissing, ImportedNotionViewAuthorityInvalid)
        RegisterNullaryProvider{} -> (ImportedNullaryProviderClassificationFactMissing, ImportedNullaryProviderClassificationAuthorityInvalid)
        RegisterProviderResult{} -> (ImportedProviderResultRuleFactMissing, ImportedProviderResultRuleAuthorityInvalid)
        RegisterBackwardNotion{} -> (ImportedBackwardNotionRuleFactMissing, ImportedBackwardNotionRuleAuthorityInvalid)
        RegisterFiniteEvidence{} -> (ImportedFiniteEvidenceRuleFactMissing, ImportedFiniteEvidenceRuleAuthorityInvalid)
        RegisterGraphDomain{} -> (ImportedGraphDomainRuleFactMissing, ImportedGraphDomainRuleAuthorityInvalid)
        RegisterWholeConclusion{} -> (ImportedWholeConclusionRuleFactMissing, ImportedWholeConclusionRuleAuthorityInvalid)

validateCanonicalViewCertificate
    :: CheckedObjectClosure -> ObjectId -> DefinitionViewKind
    -> CheckedPropositionContent -> ValidationCertificate
    -> Either DeclarationError ()
validateCanonicalViewCertificate closure object kind proposition certificate =
    -- Local occurrence admission has tied the certificate authority to
    -- this occurrence, and 'checkImportedOccurrence' ties that authority's
    -- theorem reference to the exact checked proposition id.  The direct
    -- descriptor below was minted only after the fresh declaration
    -- validator checked the corresponding generated equation or
    -- extensional construction fact.  In particular, membership views do
    -- not try to reconstruct source-construction syntax that transparent
    -- object content deliberately no longer retains.
    case validationDirectAuthorization certificate of
        CheckedKernelConstruction
                (CheckedDefinitionEquation certifiedObject)
            | certifiedObject == object -> do
                (coreType, body) <-
                    case lookupCheckedObjectContent object closure of
                        Just (TransparentObjectContent _theory type' body') ->
                            pure (type', body')
                        _ -> Left (DefinitionViewObjectMissing object)
                let expectedKind =
                        case firstOrderSymbolShape coreType of
                            Just{} -> DefinitionPointwiseView
                            Nothing -> DefinitionExactView
                unless
                    ( kind == expectedKind
                      && frozenCoreTerm
                            (checkedPropositionTerm proposition)
                            == definitionEquationTarget
                                object coreType body
                    )
                    (Left
                        (DefinitionViewCertificateMismatch object kind))
        CheckedKernelConstruction
                (CheckedSetConstructionExtensionality certifiedObject _)
            | certifiedObject == object
              && kind == DefinitionMembershipView ->
                pure ()
        _ ->
            Left (DefinitionViewCertificateMismatch object kind)

checkImportedDefinitionView
    :: CheckedObjectClosure
    -> Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate)
    -> (DeclarationInterfaceDelta, SemanticDefinitionView)
    -> Either DeclarationError CheckedDefinitionView
checkImportedDefinitionView closure facts (delta, view) = do
    let object = semanticDefinitionViewObject view
        kind = semanticDefinitionViewKind view
        target = semanticDefinitionViewTarget view
    unless (target `elem` (semanticFactFingerprint <$> declarationDeltaFacts delta))
        (Left (DefinitionViewProvenanceMismatch object kind target))
    unless (checkedObjectMember object closure) (Left (DefinitionViewObjectMissing object))
    case Map.lookup target facts of
        Nothing -> Left (DefinitionViewConflict object kind target target)
        Just (FactEntry proposition _occurrence certificate) -> do
            validateCanonicalViewCertificate closure object kind proposition certificate
            pure (CheckedDefinitionView object kind target (checkedPropositionId proposition))

data DriverOpenError
    = DriverFormationPreparationFailed !DeclarationError
    | DriverInitialPrefixError !PrefixContextError
    | DriverNaturalNumeralBasisTheoryMismatch !TheoryId !TheoryId
    | DriverImportTheoryMismatch !TheoryId !TheoryId
    deriving stock (Show, Eq)

renderDriverOpenError :: DriverOpenError -> Text
renderDriverOpenError = \case
    DriverFormationPreparationFailed failure -> renderDeclarationError failure
    DriverInitialPrefixError{} ->
        "the initial semantic prefix is inconsistent"
    DriverImportTheoryMismatch expected actual ->
        "imports belong to foundation theory " <> shown actual
            <> ", but the module uses " <> shown expected
    DriverNaturalNumeralBasisTheoryMismatch expected actual ->
        "the natural-numeral basis belongs to foundation theory "
            <> shown actual <> ", but the module uses " <> shown expected
  where
    shown :: Show value => value -> Text
    shown = Text.pack . show

runModuleDriverEff
    :: forall es failure value.
       (ValidationCache :> es, IOE :> es)
    => CheckedFoundation
    -> ModuleName
    -> PreparedImports
    -> VampireResolver
    -> ModuleDriver failure value
    -> Eff es
        (Either
            DriverOpenError
            (DriverResult failure value))
runModuleDriverEff foundation owner direct resolver action =
    runModuleDriverEffWithMaybeNaturalNumeralBasis
        foundation Nothing owner direct resolver action

runModuleDriverEffWithNaturalNumeralBasis
    :: forall es failure value.
       (ValidationCache :> es, IOE :> es)
    => CheckedFoundation
    -> NaturalNumeralBasis
    -> ModuleName
    -> PreparedImports
    -> VampireResolver
    -> ModuleDriver failure value
    -> Eff es
        (Either
            DriverOpenError
            (DriverResult failure value))
runModuleDriverEffWithNaturalNumeralBasis foundation basis owner direct resolver
        action
    | actualTheory /= expectedTheory =
        pure
            (Left
                (DriverNaturalNumeralBasisTheoryMismatch
                    expectedTheory actualTheory))
    | otherwise =
        runModuleDriverEffWithMaybeNaturalNumeralBasis
            foundation (Just basis) owner direct resolver action
  where
    expectedTheory = theoryId foundation
    actualTheory = NaturalNumeral.naturalNumeralBasisTheory basis

runModuleDriverEffWithMaybeNaturalNumeralBasis
    :: forall es failure value.
       (ValidationCache :> es, IOE :> es)
    => CheckedFoundation
    -> Maybe NaturalNumeralBasis
    -> ModuleName
    -> PreparedImports
    -> VampireResolver
    -> ModuleDriver failure value
    -> Eff es
        (Either
            DriverOpenError
            (DriverResult failure value))
runModuleDriverEffWithMaybeNaturalNumeralBasis foundation basis owner prepared resolver
        action = do
    let PreparedImports check _ _ = prepared
    FormationDiagnostics.withRecorder (importFormationReport check) run
  where
    run recorder = do
        unique <- liftIO (BuilderIdentity <$> newUnique)
        let theory = theoryId foundation
            direct = preparedImportIds prepared
            PreparedImports _check _parents context = prepared
        case (,) <$>
                first DriverInitialPrefixError
                    (initialPrefixContextId theory owner direct)
                <*>
                (if checkedObjectClosureTheory (importObjects context) == theory
                    then Right (importObjects context)
                    else Left (DriverImportTheoryMismatch theory
                        (checkedObjectClosureTheory (importObjects context)))) of
            Left err ->
                pure (Left err)
            Right (prefix, closure) -> do
                let builder =
                        BuilderState
                            { logicalBuilderIdentity = unique
                            , logicalBuilderFoundation = foundation
                            , logicalBuilderTheory = theory
                            , logicalBuilderOwner = owner
                            , logicalBuilderDirectSemanticInputs = direct
                            , logicalBuilderPrefix = prefix
                            , logicalBuilderObjectClosure = closure
                            , logicalBuilderFacts = Map.empty
                            , logicalBuilderCompositions = Calculation.emptyCompositionRegistry
                            , logicalBuilderAliases = Map.empty
                            , logicalBuilderEnvironment = emptyResolvedEnvironment
                            , logicalBuilderDefinitionViews = Map.empty
                            , logicalBuilderRegistrations = emptyBuilderRegistrationIndex
                            , logicalBuilderFormationCatalog = FormationCatalog.emptyCatalog
                            , logicalBuilderFormationDescriptions = Map.empty
                            , logicalBuilderLocalFormationRules = []
                            , logicalBuilderFormationPreparationWork = 0
                            , logicalBuilderFormationPreparationDiagnostics = FormationDiagnostics.emptyDiagnostics
                            , logicalBuilderDeltas = []
                            , logicalBuilderNextDeclaration = 0
                            , logicalBuilderNextFact = 0
                            , logicalBuilderNextInvocation = 0
                            }
                initializedResult <- FormationDiagnostics.withPhase recorder FormationDiagnostics.DeclarationPreparation
                    (recordPreparedFormation recorder (initializeImportedConsumer prepared builder))
                case initializedResult of
                    Left failure -> pure (Left (DriverFormationPreparationFailed failure))
                    Right initialized -> do
                        let initialState =
                                DriverState
                                    { driverResolver = resolver
                                    , driverNaturalNumeralBasis = basis
                                    , driverFormationRecorder = recorder
                                    , driverBuilder = initialized
                                    , driverPendingPrefix = emptyPendingModulePrefix prefix
                                    }
                        (result, finalState) <- inject
                            (State.runState initialState
                                (Error.runErrorNoCallStack @DriverDeclarationFailure
                                    (Error.runErrorNoCallStack
                                        @(DriverActionFailure failure)
                                        action)))
                        let finalBuilder = driverBuilder finalState
                            finalPrefix = driverPendingPrefix finalState
                        case result of
                            Left (DriverDeclarationFailure err) ->
                                pure
                                    (Right
                                        (DriverFailed
                                            (DriverDeclarationFailed err)
                                            finalPrefix))
                            Right (Left (DriverActionFailure err)) ->
                                pure
                                    (Right
                                        (DriverFailed
                                            (DriverActionFailed err)
                                            finalPrefix))
                            Right (Right value) -> do
                                case semanticInterface
                                        owner
                                        direct
                                        (reverse
                                            (logicalBuilderDeltas
                                                finalBuilder)) of
                                    Left err ->
                                        pure
                                            (Right
                                                (DriverSealFailed
                                                    err
                                                    finalPrefix))
                                    Right interface -> do
                                        evidence <- liftIO
                                            (sealImportedModuleEvidence prepared interface finalPrefix finalBuilder)
                                        pure (Right (DriverSucceeded value evidence finalPrefix))

runModuleDriverFreshIO
    :: CheckedFoundation
    -> ModuleName
    -> PreparedImports
    -> VampireResolver
    -> ModuleDriver failure value
    -> IO
        (Either
            DriverOpenError
            (DriverResult failure value))
runModuleDriverFreshIO foundation owner direct resolver action =
    runEff
        (runValidationCacheAlwaysMiss
            (runModuleDriverEff
                foundation owner direct resolver action))

runModuleDriverFreshIOWithNaturalNumeralBasis
    :: CheckedFoundation
    -> NaturalNumeralBasis
    -> ModuleName
    -> PreparedImports
    -> VampireResolver
    -> ModuleDriver failure value
    -> IO
        (Either
            DriverOpenError
            (DriverResult failure value))
runModuleDriverFreshIOWithNaturalNumeralBasis foundation basis owner direct resolver
        action =
    runEff
        (runValidationCacheAlwaysMiss
            (runModuleDriverEffWithNaturalNumeralBasis
                foundation basis owner direct resolver action))

failModuleDriver
    :: failure
    -> ModuleDriver failure value
failModuleDriver err =
    Error.throwError_ (DriverActionFailure err)

failDeclarationDriver
    :: DeclarationError
    -> ModuleDriver failure value
failDeclarationDriver err =
    Error.throwError_ (DriverDeclarationFailure err)

nextDeclarationSlotDriver
    :: ModuleDriver failure DeclarationSlot
nextDeclarationSlotDriver = do
    builder <- State.gets driverBuilder
    pure
        (declarationSlot
            (logicalBuilderOwner builder)
            (localDeclarationOrdinal
                (logicalBuilderNextDeclaration builder)))

currentTheoryDriver :: ModuleDriver failure TheoryId
currentTheoryDriver =
    State.gets (logicalBuilderTheory . driverBuilder)

currentFoundationAxiomDriver
    :: FoundationAxiomTag
    -> ModuleDriver failure (FrozenCheckedCore Void)
currentFoundationAxiomDriver tag =
    State.gets
        (\state ->
            foundationAxiomFrozen
                (logicalBuilderFoundation (driverBuilder state))
                tag)

resolveVisibleFactAliasDriver
    :: SemanticName
    -> ModuleDriver failure
        (Maybe SemanticFactOccurrenceFingerprint)
resolveVisibleFactAliasDriver alias = do
    builder <- State.gets driverBuilder
    pure do
        ImportedAliasBinding fingerprint _origin <-
            Map.lookup alias (logicalBuilderAliases builder)
        pure fingerprint

resolveVisibleFactTargetsDriver
    :: FrozenCheckedCore ObjectId
    -> ModuleDriver failure
        [SemanticFactOccurrenceFingerprint]
resolveVisibleFactTargetsDriver target = do
    builder <- State.gets driverBuilder
    pure
        [ fingerprint
        | (fingerprint, FactEntry proposition _occurrence _authorization) <-
            Map.toAscList (logicalBuilderFacts builder)
        , checkedPropositionTerm proposition == target
        ]

resolveVisibleGlobalDriver
    :: SemanticGlobalKey
    -> ModuleDriver failure (Maybe (ResolvedGlobalBinding, CoreType))
resolveVisibleGlobalDriver key = do
    builder <- State.gets driverBuilder
    pure
        ( (\(binding, _content) ->
                ( binding
                , fromMaybe
                    (impossible "visible semantic key has no source type")
                    (semanticGlobalKeyType key)
                ))
            <$> resolveVisibleGlobalContent builder key
        )

resolveVisibleGlobalContentDriver
    :: SemanticGlobalKey
    -> ModuleDriver failure
        (Maybe
            ( ResolvedGlobalBinding
            , ObjectContent
            ))
resolveVisibleGlobalContentDriver key = do
    builder <- State.gets driverBuilder
    pure (resolveVisibleGlobalContent builder key)

resolveVisibleStructureDriver
    :: Schema.StructurePhrase
    -> ModuleDriver failure (Maybe ResolvedStructure)
resolveVisibleStructureDriver structurePhrase = do
    builder <- State.gets driverBuilder
    pure (lookupResolvedStructurePhrase structurePhrase (logicalBuilderStructures builder))

resolveVisibleStructureFieldProjectionObjectsDriver
    :: StructSymbol
    -> ModuleDriver failure [ObjectId]
resolveVisibleStructureFieldProjectionObjectsDriver symbol = do
    builder <- State.gets driverBuilder
    pure
        ( Set.toAscList
            (Set.fromList
                (mapMaybe
                    (resolvedStructureFieldProjection symbol)
                    (allResolvedStructures builder)))
        )

resolveVisibleGlobalContent
    :: BuilderState evidence
    -> SemanticGlobalKey
    -> Maybe
        ( ResolvedGlobalBinding
        , ObjectContent
        )
resolveVisibleGlobalContent builder key = do
    binding <- Map.lookup key (logicalBuilderGlobals builder)
    let target = semanticGlobalBindingTarget
            (resolvedBindingDeclaration binding)
    content <-
        lookupCheckedObjectContent
            (semanticGlobalTargetObject target)
            closure
    pure
        ( binding
        , content
        )
  where
    closure = logicalBuilderObjectClosure builder

objectAvailableDriver
    :: ObjectId
    -> ModuleDriver failure Bool
objectAvailableDriver identity =
    State.gets
        (\state ->
            isJust
                (lookupCheckedObjectType
                    identity
                    (logicalBuilderObjectClosure (driverBuilder state))))

objectTypeDriver
    :: ObjectId
    -> ModuleDriver failure (Maybe CoreType)
objectTypeDriver identity =
    State.gets
        (\state ->
            lookupCheckedObjectType
                identity
                (logicalBuilderObjectClosure (driverBuilder state)))

nextDeclarationSlotLowering :: LoweringDriver DeclarationSlot
nextDeclarationSlotLowering =
    withLoweringBuilder \builder ->
        declarationSlot
            (logicalBuilderOwner builder)
            (localDeclarationOrdinal
                (logicalBuilderNextDeclaration builder))

currentTheoryLowering :: LoweringDriver TheoryId
currentTheoryLowering =
    withLoweringBuilder logicalBuilderTheory

currentFoundationLowering :: LoweringDriver CheckedFoundation
currentFoundationLowering =
    withLoweringBuilder logicalBuilderFoundation

currentFoundationAxiomLowering
    :: FoundationAxiomTag
    -> LoweringDriver (FrozenCheckedCore Void)
currentFoundationAxiomLowering tag =
    withLoweringBuilder
        (\builder ->
            foundationAxiomFrozen
                (logicalBuilderFoundation builder)
                tag)

resolveVisibleFactAliasLowering
    :: SemanticName
    -> LoweringDriver (Maybe SemanticFactOccurrenceFingerprint)
resolveVisibleFactAliasLowering alias =
    withLoweringBuilder \builder -> do
        ImportedAliasBinding fingerprint _origin <-
            Map.lookup alias (logicalBuilderAliases builder)
        pure fingerprint

resolveVisibleFactTargetsLowering
    :: FrozenCheckedCore ObjectId
    -> LoweringDriver [SemanticFactOccurrenceFingerprint]
resolveVisibleFactTargetsLowering target =
    withLoweringBuilder \builder ->
        [ fingerprint
        | (fingerprint, FactEntry proposition _occurrence _evidence) <-
            Map.toAscList (logicalBuilderFacts builder)
        , checkedPropositionTerm proposition == target
        ]

resolveVisibleFactLowering
    :: SemanticFactOccurrenceFingerprint
    -> LoweringDriver (Maybe CheckedPropositionContent)
resolveVisibleFactLowering fingerprint =
    withLoweringBuilder \builder -> do
        FactEntry proposition _occurrence _evidence <-
            Map.lookup fingerprint (logicalBuilderFacts builder)
        pure proposition

checkStructureProjectionLawTargetLowering
    :: CanonicalTerm ObjectId
    -> LoweringDriver
        (Either
            StructureProjectionLawIntegrityError
            (FrozenCheckedCore ObjectId))
checkStructureProjectionLawTargetLowering target =
    withLoweringBuilder \builder ->
        case checkCanonicalCore
                (globalTypingFromClosure
                    (logicalBuilderObjectClosure builder))
                target of
            Left _failure ->
                Left StructureProjectionReconstructedTargetInvalid
            Right checked
                | frozenCoreType checked == TyProp -> Right checked
                | otherwise ->
                    Left
                        (StructureProjectionReconstructedTargetNotProposition
                            (frozenCoreType checked))

-- Planning selects the exact indexed occurrence of the recovered schema.
-- Admission independently constructs the theorem capability from its registry.
resolveStructureProjectionLawLowering
    :: ResolvedRecordShape -> FrozenCheckedCore ObjectId
    -> LoweringDriver (Either StructureProjectionLawIntegrityError SemanticFactOccurrenceFingerprint)
resolveStructureProjectionLawLowering (ResolvedRecordShape owner _ _) target =
    withLoweringBuilder \builder -> do
        let key = Schema.RecordSchemaLaw Record.RecordProjectionExtensionalityLaw
        (_, metadata) <- maybe (Left (StructureProjectionGeneratedLawUnavailable target)) Right
            (checkedIndexedStructureFact (logicalBuilderStructures builder) (logicalBuilderFacts builder)
                planningEvidenceDirect owner (Schema.StructureLawFact key))
        FactEntry proposition _ _ <- maybe (Left (StructureProjectionGeneratedLawUnavailable target)) Right
            (Map.lookup (semanticFactFingerprint metadata) (logicalBuilderFacts builder))
        unless (checkedPropositionTerm proposition == target)
            (Left (StructureProjectionGeneratedLawUnavailable target))
        pure (semanticFactFingerprint metadata)

lookupStructureFactLowering
    :: StructureId -> Schema.StructureFactKey
    -> LoweringDriver (Maybe (SemanticFactOccurrenceFingerprint, CheckedPropositionContent))
lookupStructureFactLowering owner key = withLoweringBuilder \builder -> do
    (proposition, metadata) <- checkedIndexedStructureFact (logicalBuilderStructures builder)
        (logicalBuilderFacts builder) planningEvidenceDirect owner key
    pure (semanticFactFingerprint metadata, proposition)

-- Context-sensitive evidence is checked against both the complete interface
-- and the actual occurrence registry. No certificate alone supplies a law.
checkedIndexedStructureFact
    :: StructureEnvironment.StructureEnvironment evidence
    -> Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> (evidence -> Maybe DirectAuthorization)
    -> StructureId -> Schema.StructureFactKey
    -> Maybe (CheckedPropositionContent, SemanticFactOccurrence)
checkedIndexedStructureFact environment facts direct owner key = do
    interface <- StructureEnvironment.lookupStructureById owner environment
    indexed <- StructureInterface.lookupStructureOccurrence key interface
    let metadata = StructureInterface.structureOccurrenceMetadata indexed
        fingerprint = semanticFactFingerprint metadata
        proposition = StructureInterface.structureOccurrenceProposition indexed
        purpose = case key of
            Schema.StructureLawFact law -> structureLawPurpose (Schema.StructureLawId owner law)
            Schema.StructureResourceFact _ -> GeneralFactPurpose
    FactEntry actual occurrence evidence <- Map.lookup fingerprint facts
    mechanism <- direct evidence
    guard (actual == proposition && occurrence == metadata
        && semanticFactPurpose metadata == purpose
        && factAuthoritySafety (semanticFactAuthority metadata) == cleanAuthoritySafety
        && direct (StructureInterface.structureOccurrenceEvidence indexed) == Just mechanism)
    pure (proposition, metadata)

-- An inert selection, not proof authority. Keep the cited resource and exact
-- owner/application beside each law so admission can recheck the association.
data CitedStructureViews = CitedStructureViews
    !(NonEmpty SemanticFactOccurrenceFingerprint)
    ![(StructureId, SemanticFactOccurrenceFingerprint, Schema.StructureApplicationKey,
        SemanticFactOccurrenceFingerprint, CheckedPropositionContent)]
    deriving stock (Show, Eq)

citedStructureViewFacts
    :: CitedStructureViews
    -> [(SemanticFactOccurrenceFingerprint, CheckedPropositionContent)]
citedStructureViewFacts (CitedStructureViews _ views) =
    stableUniqueBy fst [(fingerprint, proposition) | (_, _, _, fingerprint, proposition) <- views]

citedStructureViewOrigins
    :: CitedStructureViews
    -> [(SemanticFactOccurrenceFingerprint, SemanticFactOccurrenceFingerprint)]
citedStructureViewOrigins (CitedStructureViews _ views) =
    stableUniqueBy fst [(fingerprint, definition) | (_, definition, _, fingerprint, _) <- views]

resolveCitedStructureViewsLowering
    :: NonEmpty SemanticFactOccurrenceFingerprint
    -> LoweringDriver (Either Text CitedStructureViews)
resolveCitedStructureViewsLowering selected = withLoweringBuilder \builder ->
    resolveCitedStructureViews planningEvidenceDirect builder selected

resolveCitedStructureViews
    :: (evidence -> Maybe DirectAuthorization)
    -> BuilderState evidence
    -> NonEmpty SemanticFactOccurrenceFingerprint
    -> Either Text CitedStructureViews
resolveCitedStructureViews direct builder selected = do
    -- Inspect only resource-index occurrences, never equal proposition targets.
    -- Shared predicate resources expose every compatible owner in identity order.
    let selectedSet = Set.fromList (toList selected)
        environment = logicalBuilderStructures builder
        providers =
            [(owner, interface, fingerprint)
            | (owner, interface) <- Map.toAscList (StructureEnvironment.structureEnvironmentInterfaces environment)
            , Just fingerprint <- [Map.lookup Schema.PredicateDefinitionResource
                (StructureInterface.structureInterfaceResourceIndex interface)]
            , fingerprint `Set.member` selectedSet]
        applications =
            [(owner, fingerprint, application)
            | (owner, interface, fingerprint) <- providers
            , application <- Schema.resolvedSchemaSemanticDirectParentOrder
                (StructurePredicate.pendingStructureSchema (StructureInterface.structureInterfaceRegistration interface))]
        checked owner key = maybe (Left "a cited structure view lost its checked occurrence") Right
            (checkedIndexedStructureFact environment (logicalBuilderFacts builder) direct owner key)
    unless (length applications <= 64)
        (Left "cited structure definitions expose more than 64 direct-parent views; select fewer definitions or cite the needed inheritance laws")
    traverse_ (\(owner, _, fingerprint) -> do
        (_, metadata) <- checked owner (Schema.StructureResourceFact Schema.PredicateDefinitionResource)
        unless (semanticFactFingerprint metadata == fingerprint)
            (Left "a cited structure definition changed its resource occurrence")) providers
    views <- for applications \(owner, definition, application) -> do
        (proposition, metadata) <- checked owner (Schema.StructureLawFact (Schema.ParentInheritanceLaw application))
        pure (owner, definition, application, semanticFactFingerprint metadata, proposition)
    pure (CitedStructureViews selected views)

validateCitedStructureViews :: LogicalBuilder -> CitedStructureViews -> Either DeclarationError ()
validateCitedStructureViews builder views@(CitedStructureViews selected _) = do
    actual <- first StructureDeclarationInvalid
        (resolveCitedStructureViews builderEvidenceDirect builder selected)
    unless (actual == views)
        (Left (StructureDeclarationInvalid "a cited structure view changed between planning and admission"))

data CheckedProjectionExtensionality = CheckedProjectionExtensionality
    !CheckedPropositionContent !SemanticFactOccurrence

data CheckedNotionViewTheorem = CheckedNotionViewTheorem
    !CheckedPropositionContent !SemanticFactOccurrence

-- Pair visible descriptions with their declaration-checked application values.
-- This enumeration supports the independent registration parity oracle.
-- Production uses the admitted catalog and replays exact source occurrences.
visibleFormationRegistrationsLowering
    :: LoweringDriver [(Registration SemanticFactOccurrenceFingerprint, Notion.FormationRuleSource)]
visibleFormationRegistrationsLowering = withLoweringBuilder \builder ->
    let BuilderRegistrationIndex entries _ = logicalBuilderRegistrations builder
    in [(registration, source) | (OwnedRegistrationKey _ registration, source) <- Map.toAscList entries]

formationCatalogLowering :: LoweringDriver (FormationCatalog.Catalog
    (Either Notion.FormationRuleSource FormationCatalog.LocalProducerIx))
formationCatalogLowering = withLoweringBuilder logicalBuilderFormationCatalog

formationCatalogSnapshotLowering :: LoweringDriver (PrefixContextId,
    FormationCatalog.Catalog (Either Notion.FormationRuleSource FormationCatalog.LocalProducerIx))
formationCatalogSnapshotLowering = withLoweringBuilder \builder ->
    (logicalBuilderPrefix builder, logicalBuilderFormationCatalog builder)

formationPreparationWorkLowering :: LoweringDriver Natural
formationPreparationWorkLowering = withLoweringBuilder logicalBuilderFormationPreparationWork

formationPreparationDiagnosticsLowering :: LoweringDriver FormationDiagnostics.Diagnostics
formationPreparationDiagnosticsLowering = withLoweringBuilder logicalBuilderFormationPreparationDiagnostics

formationRecorderLowering :: LoweringDriver FormationDiagnostics.Recorder
formationRecorderLowering = State.gets loweringFormationRecorder

withFormationPhaseLowering :: FormationDiagnostics.Phase -> LoweringDriver value -> LoweringDriver value
withFormationPhaseLowering phase action = do
    recorder <- formationRecorderLowering
    FormationDiagnostics.withPhase recorder phase action

preparationRejectedDebit :: Either DeclarationError value -> Natural
preparationRejectedDebit (Left (FormationRegistrationPreparationLimitExceeded _ _ _ amount)) = amount
preparationRejectedDebit _ = 0

declarationPreparationMeasurement :: Natural -> FormationDiagnostics.Diagnostics -> Natural -> FormationDiagnostics.Measurement
declarationPreparationMeasurement used counts rejected = FormationDiagnostics.emptyMeasurement
    { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork FormationDiagnostics.DeclarationPreparation used counts
    , FormationDiagnostics.limitHighWater = Map.fromList
        [("declaration-preparation.used", used), ("declaration-preparation.cap", defaultFormationPreparationWork)]
        <> if rejected == 0 then Map.empty else Map.singleton "declaration-preparation.rejected" rejected }

-- Expansion admission is performed once at the declaration boundary (or cold
-- import), not at use sites. Preserve accepted debits even when admission fails.
expansionAdmissionMeasurement :: Natural -> FormationDiagnostics.Measurement
expansionAdmissionMeasurement used = FormationDiagnostics.emptyMeasurement
    { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countPhaseWork
        FormationDiagnostics.DeclarationPreparation used FormationDiagnostics.emptyDiagnostics }

recordPreparedFormation
    :: MonadIO m => FormationDiagnostics.Recorder
    -> (Either failure value, FormationDiagnostics.Measurement) -> m (Either failure value)
recordPreparedFormation recorder (result, measured) = do
    result `seq` liftIO (FormationDiagnostics.recordMeasurement recorder measured)
    pure result

-- A provisional fact without a checked direct contract cannot classify a
-- registration as definition-origin. Do not infer that contract from its term.
resolveVisibleFormationSourceLowering
    :: SemanticFactOccurrenceFingerprint
    -> LoweringDriver (Maybe (CheckedPropositionContent, DirectAuthorization))
resolveVisibleFormationSourceLowering fingerprint = withLoweringBuilder \builder -> do
    FactEntry proposition _ evidence <- Map.lookup fingerprint (logicalBuilderFacts builder)
    direct <- planningEvidenceDirect evidence
    pure (proposition, direct)

firstVisibleNullaryProviderClassificationLowering
    :: IntrinsicProviderId
    -> LoweringDriver (Maybe Notion.VisibleNullaryProviderClassification)
firstVisibleNullaryProviderClassificationLowering provider =
    withLoweringBuilder
        (lookupFirstBuilderNullaryProviderClassification provider
            . logicalBuilderRegistrations)

data TransientFormationReplayError
    = TransientFormationFactMissing
        !SemanticFactOccurrenceFingerprint
    | TransientFormationTheoryMismatch !TheoryId !TheoryId
    | TransientFormationCommittedObjectMissing !ObjectId
    | TransientFormationGlobalTypeMismatch
        !ObjectId !CoreType !CoreType
    | TransientFormationImportInvalid !DerivationImportError
    | TransientFormationKernelReplayFailed !KernelReplayError
    | TransientFormationProofFailed !Notion.FormationProofError
    | TransientFormationProofTargetMismatch
    | TransientFormationImportUseMismatch
        !(Set ImportIx) !(Set ImportIx)
    | TransientFormationHypothesisUseMismatch
        !(Set HypothesisIx) !(Set HypothesisIx)
    | TransientFormationUsedFoundation
    | TransientFormationUsedGuardedRule
    deriving stock (Show, Eq)

materializeFormationProofLowering
    :: KernelProof.ProofContext ObjectId -> Notion.MaterializedFormationEvidence origin
    -> Vector (DerivationImportJudgement ObjectId)
    -> LoweringDriver (Either Notion.FormationProofError (KernelProof.BuiltProof ObjectId))
materializeFormationProofLowering context evidence imports = withFormationPhaseLowering FormationDiagnostics.Proof do
    recorder <- formationRecorderLowering
    let (result, _, measured) = FormationProof.materializeFormationProofWithDiagnostics
            FormationProof.defaultFormationProofConversionPool context evidence imports
    recordPreparedFormation recorder (result, measured)

-- | Replay a formation witness against its exact transient hypotheses and any
-- checked objects local to the declaration currently being lowered. This
-- inspects the prospective builder but creates no candidate authority or
-- persistent dependency.
replayTransientFormationLowering
    :: CheckedObjectClosure
    -> Notion.MaterializedFormationEvidence origin
    -> ScopedCheckedCore ObjectId
    -> LoweringDriver
        (Either TransientFormationReplayError (ReplayedScopedKernelDerivation ObjectId))
replayTransientFormationLowering localClosure evidence target = withFormationPhaseLowering FormationDiagnostics.Proof do
    builder <- withLoweringBuilder id
    Except.runExceptT do
        (proofContext, imports) <- Except.liftEither do
            let committedClosure = logicalBuilderObjectClosure builder
                expectedTheory = checkedObjectClosureTheory committedClosure
                actualTheory = checkedObjectClosureTheory localClosure
            unless
                (actualTheory == expectedTheory)
                (Left
                    (TransientFormationTheoryMismatch
                        expectedTheory actualTheory))
            traverse_
                (\identity ->
                    case
                        ( lookupCheckedObjectType identity committedClosure
                        , lookupCheckedObjectType identity localClosure
                        ) of
                        (Just expected, Just actual)
                            | actual == expected -> pure ()
                            | otherwise ->
                                Left
                                    (TransientFormationGlobalTypeMismatch
                                        identity expected actual)
                        (Just{}, Nothing) ->
                            Left
                                (TransientFormationCommittedObjectMissing identity)
                        (Nothing, _) ->
                            impossible
                                "a checked closure omitted one of its own object identifiers")
                (Set.toAscList (checkedObjectIds committedClosure))
            propositions <-
                for (toList fingerprints) \fingerprint ->
                    maybe
                        (Left (TransientFormationFactMissing fingerprint))
                        (Right . factEntryProposition)
                        (Map.lookup fingerprint (logicalBuilderFacts builder))
            imports <-
                traverse
                    (first TransientFormationImportInvalid
                        . derivationImportJudgement
                        . checkedPropositionTerm)
                    propositions
            proofContext <-
                first (TransientFormationProofFailed . Notion.FormationProofKernelError)
                    (KernelProof.scopedProofContext
                        (logicalBuilderFoundation builder)
                        (globalTypingFromClosure localClosure)
                        (scopedCoreContext target)
                        (toList hypotheses))
            pure (proofContext, imports)
        built <- Except.ExceptT (fmap (first TransientFormationProofFailed)
            (materializeFormationProofLowering proofContext evidence (Vector.fromList imports)))
        Except.liftEither do
            unless (KernelProof.builtProofStatement built == target)
                (Left TransientFormationProofTargetMismatch)
        replayed <- Except.ExceptT (withFormationPhaseLowering FormationDiagnostics.Proof do
            recorder <- formationRecorderLowering
            let run :: (CheckedFoundation -> KernelReplayLimits -> GlobalTyping ObjectId
                    -> Vector (DerivationImportJudgement ObjectId) -> Vector (ScopedCheckedCore ObjectId)
                    -> ScopedCheckedCore ObjectId -> KernelDerivation ObjectId -> value) -> value
                run replay = replay (logicalBuilderFoundation builder) defaultKernelReplayLimits
                    (globalTypingFromClosure localClosure) (Vector.fromList imports) hypotheses target
                    (KernelProof.builtProofDerivation built)
            result <- liftIO (measureFormationReplay recorder
                (run replayScopedKernelDerivation) (run replayScopedKernelDerivationMeasured))
            pure (first TransientFormationKernelReplayFailed result))
        Except.liftEither do
            let expectedImports =
                    Set.fromList
                        [ importIx (fromIntegral index)
                        | index <- [0 .. Vector.length fingerprints - 1]
                        ]
                actualImports = replayedScopedKernelImportUses replayed
                expectedHypotheses = Set.fromList
                    [ hypothesisIx (fromIntegral index)
                    | index <- [0 .. Vector.length hypotheses - 1]
                    ]
                actualHypotheses =
                    replayedScopedKernelExternalHypothesisUses replayed
            unless (actualImports == expectedImports)
                (Left
                    (TransientFormationImportUseMismatch
                        expectedImports actualImports))
            unless (actualHypotheses == expectedHypotheses)
                (Left
                    (TransientFormationHypothesisUseMismatch
                        expectedHypotheses actualHypotheses))
            unless
                (replayedScopedKernelFoundationUses replayed `Set.isSubsetOf` Set.singleton PropositionalExtensionality)
                (Left TransientFormationUsedFoundation)
            unless
                (Set.null (replayedScopedKernelRuleUses replayed))
                (Left TransientFormationUsedGuardedRule)
            pure replayed
  where
    fingerprints = Notion.materializedFormationImports evidence
    hypotheses = Notion.materializedFormationHypothesisPropositions evidence
    factEntryProposition (FactEntry proposition _occurrence _evidence) =
        proposition

compositionRegistryLowering :: LoweringDriver Calculation.CompositionRegistry
compositionRegistryLowering = withLoweringBuilder logicalBuilderCompositions

data ResolvedDefinitionView = ResolvedDefinitionView
    !ObjectId
    !DefinitionViewKind
    !SemanticFactOccurrenceFingerprint
    !CheckedPropositionContent

resolvedDefinitionViewObject
    :: ResolvedDefinitionView
    -> ObjectId
resolvedDefinitionViewObject
        (ResolvedDefinitionView object _kind _fingerprint _proposition) =
    object

resolvedDefinitionViewKind
    :: ResolvedDefinitionView
    -> DefinitionViewKind
resolvedDefinitionViewKind
        (ResolvedDefinitionView _object kind _fingerprint _proposition) =
    kind

resolvedDefinitionViewFingerprint
    :: ResolvedDefinitionView
    -> SemanticFactOccurrenceFingerprint
resolvedDefinitionViewFingerprint
        (ResolvedDefinitionView _object _kind fingerprint _proposition) =
    fingerprint

resolvedDefinitionViewProposition
    :: ResolvedDefinitionView
    -> CheckedPropositionContent
resolvedDefinitionViewProposition
        (ResolvedDefinitionView _object _kind _fingerprint proposition) =
    proposition

resolveVisibleDefinitionViewsLowering
    :: ObjectId
    -> LoweringDriver [ResolvedDefinitionView]
resolveVisibleDefinitionViewsLowering object =
    withLoweringBuilder \builder ->
        mapMaybe (resolveDefinitionView builder object) [minBound .. maxBound]

resolveVisibleRecursiveDefinitionsLowering
    :: ObjectId -> LoweringDriver [RecursionInterface.CheckedRecursiveDefinition]
resolveVisibleRecursiveDefinitionsLowering object = withLoweringBuilder $ \builder ->
    maybe [] Map.elems (Map.lookup object
        (environmentRecursiveDefinitions (logicalBuilderEnvironment builder)))

recursiveDefinitionLookupLowering
    :: LoweringDriver (ObjectId -> [RecursionInterface.CheckedRecursiveDefinition])
recursiveDefinitionLookupLowering = withLoweringBuilder $ \builder ->
    let entries = environmentRecursiveDefinitions (logicalBuilderEnvironment builder)
    in \object -> maybe [] Map.elems (Map.lookup object entries)

-- | A constant-cost snapshot of the admitted pointwise association index.
-- Lookup remains lazy and preserves the registry's exact fact occurrence.
pointwiseDefinitionLookupLowering
    :: LoweringDriver (ObjectId -> Maybe ResolvedDefinitionView)
pointwiseDefinitionLookupLowering =
    withLoweringBuilder \builder object ->
        resolveDefinitionView builder object DefinitionPointwiseView

resolveDefinitionView
    :: BuilderState evidence -> ObjectId -> DefinitionViewKind -> Maybe ResolvedDefinitionView
resolveDefinitionView builder object kind = do
    fingerprint <- Map.lookup (object, kind) (logicalBuilderDefinitionViews builder)
    FactEntry proposition _occurrence _evidence <- Map.lookup fingerprint (logicalBuilderFacts builder)
    pure (ResolvedDefinitionView object kind fingerprint proposition)

resolveVisibleGlobalLowering
    :: SemanticGlobalKey
    -> LoweringDriver (Maybe (ResolvedGlobalBinding, CoreType))
resolveVisibleGlobalLowering key =
    withLoweringBuilder \builder ->
        ( (\(binding, _content) ->
                ( binding
                , fromMaybe
                    (impossible "visible semantic key has no source type")
                    (semanticGlobalKeyType key)
                ))
            <$> resolveVisibleGlobalContent builder key
        )

resolveVisibleGlobalContentLowering
    :: SemanticGlobalKey
    -> LoweringDriver
        (Maybe
            ( ResolvedGlobalBinding
            , ObjectContent
            ))
resolveVisibleGlobalContentLowering key =
    withLoweringBuilder (\builder -> resolveVisibleGlobalContent builder key)

resolveVisibleStructureLowering
    :: Schema.StructurePhrase
    -> LoweringDriver (Maybe ResolvedStructure)
resolveVisibleStructureLowering phrase =
    withLoweringBuilder (lookupResolvedStructurePhrase phrase . logicalBuilderStructures)

-- | Recognize one fully applied visible structure predicate by checked object
-- identity.  Surface phrases are deliberately absent here: proof lowering
-- sees canonical Core, and a predicate identity is the stable semantic key.
resolveVisibleStructurePredicateApplicationLowering
    :: CanonicalTerm ObjectId
    -> LoweringDriver
        (Either
            StructurePredicateResolutionError
            (Maybe ResolvedStructurePredicateApplication))
resolveVisibleStructurePredicateApplicationLowering term =
    withLoweringBuilder \builder ->
        case canonicalApplicationSpine term of
            (CGlobal predicate, arguments) ->
                resolveApplication builder predicate arguments
            _ -> Right Nothing
  where
    resolveApplication builder predicate arguments =
        case
            [ structure
            | structure <- List.nub
                [ structure
                | structure <- allResolvedStructures builder
                , resolvedStructurePredicate structure == predicate
                ]
            , _subject : parameters <- [arguments]
            , length parameters
                == fromIntegral
                    (Schema.resolvedSchemaParameterCount
                        (resolvedStructureSchema structure))
            ] of
            [] -> Right Nothing
            structure : equivalent
                | all (sameOperationalStructure structure) equivalent
                , subject : parameters <- arguments ->
                    Right
                        (Just
                            (ResolvedStructurePredicateApplication
                                structure subject parameters))
            _ -> Left (AmbiguousVisibleStructurePredicate predicate)

    sameOperationalStructure left right =
        -- Surface structure aliases may share one content-addressed
        -- transparent predicate.  They are interchangeable at the Core-only
        -- proof boundary precisely when their argument and field interfaces
        -- also coincide.
        Schema.resolvedSchemaParameterCount
            (resolvedStructureSchema left)
            == Schema.resolvedSchemaParameterCount
                (resolvedStructureSchema right)
        && operationalFields left == operationalFields right
    operationalFields = fmap (\field ->
        (Schema.resolvedFieldIdentity field, Schema.resolvedFieldSelector field, Schema.resolvedFieldProjection field))
        . Map.elems . Schema.resolvedSchemaFields . resolvedStructureSchema

resolveVisibleStructureFieldProjectionObjectsLowering
    :: StructSymbol
    -> LoweringDriver [ObjectId]
resolveVisibleStructureFieldProjectionObjectsLowering symbol =
    withLoweringBuilder \builder ->
        Set.toAscList
            (Set.fromList
                (mapMaybe
                    (resolvedStructureFieldProjection symbol)
                    (allResolvedStructures builder)))

-- | All exact visible identities for one field spelling.  Equal inherited
-- presentations coalesce; a genuinely overloaded spelling remains
-- distinguishable until elaboration has selected a receiver structure.
resolveVisibleStructureFieldsLowering
    :: StructSymbol
    -> LoweringDriver [(FieldId, ObjectId)]
resolveVisibleStructureFieldsLowering symbol =
    withLoweringBuilder \builder ->
        Set.toAscList
            (Set.fromList
                (mapMaybe
                    (resolvedStructureField symbol)
                    (allResolvedStructures builder)))

-- | Resolve one exact field-provider identity to its checked unary projection.
-- Inherited presentations repeat the same pair and therefore coalesce; the
-- projection object is itself derived canonically from the field identity.
resolveVisibleStructureFieldProviderLowering
    :: FieldId
    -> LoweringDriver (Maybe ObjectId)
resolveVisibleStructureFieldProviderLowering identity =
    withLoweringBuilder \builder ->
        Map.lookup identity
            (environmentFields (logicalBuilderEnvironment builder))

-- Recover exact record shapes in canonical field order. Equivalent schemas
-- share a shape; the least structure identity supplies its indexed theorem.
resolveVisibleRecordShapesLowering :: [ObjectId] -> LoweringDriver [ResolvedRecordShape]
resolveVisibleRecordShapesLowering selectors = withLoweringBuilder \builder ->
    Map.elems (Map.fromListWith coalesce
        [(resolvedRecordShapeKey shape, shape)
        | structure <- allResolvedStructures builder
        , let schema = resolvedStructureSchema structure
              fields = [ResolvedRecordShapeField (Schema.resolvedFieldIdentity field)
                    (Schema.resolvedFieldSelector field) (Schema.resolvedFieldProjection field) (Schema.resolvedFieldSymbol field)
                  | field <- Map.elems (Schema.resolvedSchemaFields schema)]
              shape = ResolvedRecordShape (Schema.resolvedSchemaId schema) (semanticRecordShapeKey schema) fields
        , (resolvedRecordShapeFieldSelector <$> fields) == selectors])
  where
    coalesce left@(ResolvedRecordShape a _ _) right@(ResolvedRecordShape b _ _)
        | a <= b = left
        | otherwise = right

objectAvailableLowering :: ObjectId -> LoweringDriver Bool
objectAvailableLowering identity =
    withLoweringBuilder
        (isJust
            . lookupCheckedObjectType identity
            . logicalBuilderObjectClosure)

objectTypeLowering :: ObjectId -> LoweringDriver (Maybe CoreType)
objectTypeLowering identity =
    withLoweringBuilder
        (lookupCheckedObjectType identity
            . logicalBuilderObjectClosure)

-- | Read the checked content of an already visible object while preparing a
-- prospective declaration.  This is the content analogue of
-- 'objectTypeLowering': callers may inspect a transparent definition, but
-- cannot mutate the builder or manufacture visibility for a new object.
objectContentLowering :: ObjectId -> LoweringDriver (Maybe ObjectContent)
objectContentLowering identity =
    withLoweringBuilder
        (lookupCheckedObjectContent identity
            . logicalBuilderObjectClosure)

checkedObjectClosureLowering
    :: LoweringDriver CheckedObjectClosure
checkedObjectClosureLowering =
    withLoweringBuilder logicalBuilderObjectClosure

naturalNumeralBasisLowering
    :: LoweringDriver (Maybe NaturalNumeralBasis)
naturalNumeralBasisLowering =
    State.gets loweringNaturalNumeralBasis

withLoweringBuilder
    :: (BuilderState PlanningEvidence -> value)
    -> LoweringDriver value
withLoweringBuilder action = do
    ProspectiveBuilder builder <- State.gets loweringBuilder
    pure (action builder)


data CandidateSpec = CandidateSpec
    !CheckedPropositionContent
    !FactPurpose
    !FactSearchEligibility
    ![SemanticName]
    !(Maybe SemanticRelationComposition)

candidateSpec
    :: CheckedPropositionContent
    -> FactSearchEligibility
    -> [SemanticName]
    -> CandidateSpec
candidateSpec =
    \proposition eligibility aliases ->
        CandidateSpec proposition GeneralFactPurpose eligibility aliases Nothing

structureLawCandidateSpec
    :: StructureLaws.GeneratedLawSpec -> FactSearchEligibility -> [SemanticName] -> CandidateSpec
structureLawCandidateSpec law eligibility aliases = CandidateSpec
    (StructureLaws.generatedLawProposition law)
    (structureLawPurpose (StructureLaws.generatedLawId law)) eligibility aliases Nothing

candidateSpecPurpose :: CandidateSpec -> FactPurpose
candidateSpecPurpose (CandidateSpec _ purpose _ _ _) = purpose

candidateSpecWithRelationComposition
    :: SemanticRelationComposition
    -> CandidateSpec
    -> CandidateSpec
candidateSpecWithRelationComposition composition
        (CandidateSpec proposition purpose eligibility aliases _old) =
    CandidateSpec proposition purpose eligibility aliases (Just composition)

candidateSpecOccurrence
    :: FactSlot
    -> FactAuthority
    -> CandidateSpec
    -> SemanticFactOccurrence
candidateSpecOccurrence
        slot authority
        (CandidateSpec _proposition purpose eligibility _aliases composition) =
    maybe
        (semanticFactOccurrence purpose slot authority eligibility)
        (semanticFactOccurrenceWithRelationComposition
            purpose slot authority eligibility)
        composition

candidateSpecTarget :: CandidateSpec -> FrozenCheckedCore ObjectId
candidateSpecTarget (CandidateSpec proposition _purpose _eligibility _aliases _composition) =
    checkedPropositionTerm proposition

data CandidatePlanningDirect
    = PlanningDefinitionEquation !ObjectId
    | PlanningSourceAxiom
    | PlanningKernelConstruction !KernelConstructionDescriptor
    | PlanningCheckedSourceProof
        !(ExternalProofUse CheckedPlannedVampireRequest)
    | PlanningOmitted ![CheckedPlannedVampireRequest]

-- | Erased exact request data needed by scheduling and public-contract
-- planning.  The family body retains the typed obligation used by admission;
-- this projection carries only its one canonical request and exact global
-- premise fingerprints.
data CheckedPlannedVampireRequest = CheckedPlannedVampireRequest
    !Location
    !Provers.PreparedVerificationRequest
    ![SemanticFactOccurrenceFingerprint]

data CandidatePlanningSpec = CandidatePlanningSpec
    !CandidatePlanningDirect
    ![PlannedFactReference]

-- | One authority-free checked candidate and its exact planning contract.
-- The two parts are constructed together by the declaration-family lowerer
-- and retain no builder capability or publication path.
data CheckedCandidate = CheckedCandidate
    !CandidateSpec
    !CandidatePlanningSpec

checkedCandidate
    :: CandidateSpec
    -> CandidatePlanningSpec
    -> CheckedCandidate
checkedCandidate = CheckedCandidate

checkedDefinitionEquationPlanning :: ObjectId -> CandidatePlanningSpec
checkedDefinitionEquationPlanning identity =
    CandidatePlanningSpec
        (PlanningDefinitionEquation identity) []

-- | A conservative implementation equation without an automatic source view.
checkedImplementationDefinitionPlanning :: ObjectId -> CandidatePlanningSpec
checkedImplementationDefinitionPlanning identity =
    checkedKernelPlanningReferences (CheckedImplementationDefinition identity) []

checkedSourceAxiomPlanning :: CandidatePlanningSpec
checkedSourceAxiomPlanning =
    CandidatePlanningSpec PlanningSourceAxiom []

checkedKernelPlanning
    :: KernelConstructionDescriptor
    -> [SemanticFactOccurrenceFingerprint]
    -> CandidatePlanningSpec
checkedKernelPlanning descriptor facts =
    CandidatePlanningSpec
        (PlanningKernelConstruction descriptor)
        (EnvironmentOccurrenceReference <$> facts)

checkedKernelPlanningWithStaged
    :: KernelConstructionDescriptor
    -> [SemanticFactOccurrenceFingerprint]
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedKernelPlanningWithStaged descriptor facts staged =
    CandidatePlanningSpec
        (PlanningKernelConstruction descriptor)
        (planningReferences facts staged)

checkedStagedKernelPlanning
    :: KernelConstructionDescriptor
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedStagedKernelPlanning descriptor staged =
    CandidatePlanningSpec
        (PlanningKernelConstruction descriptor)
        (LocalCandidateReference <$> staged)

checkedNoExternalSourceProofPlanning
    :: [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedNoExternalSourceProofPlanning =
    checkedNoExternalSourceProofPlanningWithFacts []

checkedNoExternalSourceProofPlanningWithFacts
    :: [SemanticFactOccurrenceFingerprint]
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedNoExternalSourceProofPlanningWithFacts facts staged =
    CandidatePlanningSpec
        (PlanningCheckedSourceProof NoExternalProofUse)
        (planningReferences facts staged)

checkedExternalSourceProofPlanning
    :: NonEmpty CheckedPlannedVampireRequest
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedExternalSourceProofPlanning requests =
    checkedExternalSourceProofPlanningWithFacts requests []

checkedExternalSourceProofPlanningWithFacts
    :: NonEmpty CheckedPlannedVampireRequest
    -> [SemanticFactOccurrenceFingerprint]
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedExternalSourceProofPlanningWithFacts requests facts staged =
    CandidatePlanningSpec
        (PlanningCheckedSourceProof (UsesExternalProof requests))
        (planningReferences facts staged)

-- Omission changes direct authorization and adds an escape; it does not
-- remove dependencies from the checked remainder of the proof.
checkedOmittedPlanning
    :: [CheckedPlannedVampireRequest]
    -> [SemanticFactOccurrenceFingerprint]
    -> [PlannedCandidatePosition]
    -> CandidatePlanningSpec
checkedOmittedPlanning requests facts staged =
    CandidatePlanningSpec (PlanningOmitted requests) (planningReferences facts staged)

planningReferences :: [SemanticFactOccurrenceFingerprint] -> [PlannedCandidatePosition] -> [PlannedFactReference]
planningReferences facts staged = (EnvironmentOccurrenceReference <$> facts) <> (LocalCandidateReference <$> staged)

checkedKernelPlanningReferences :: KernelConstructionDescriptor -> [PlannedFactReference] -> CandidatePlanningSpec
checkedKernelPlanningReferences descriptor = CandidatePlanningSpec (PlanningKernelConstruction descriptor)

checkedPlannedVampireRequest
    :: Location
    -> PreparedVampireObligation local origin
    -> CheckedPlannedVampireRequest
checkedPlannedVampireRequest location
        (PreparedVampireObligation _views _expected task) =
    checkedPlannedVampireTask location task

checkedPlannedVampireTask
    :: Location
    -> Provers.PreparedTypedProverTask SemanticFactOccurrenceFingerprint local origin ObjectId
    -> CheckedPlannedVampireRequest
checkedPlannedVampireTask location task =
    CheckedPlannedVampireRequest
        location
        (Provers.preparedTypedProverRequest task)
        ( Backend.typedBackendFactReference
            <$> Vector.toList
                (Backend.typedProblemGlobalPremises (Provers.preparedTypedProverLogicalProblem task))
        )

data CheckedDeclarationMode
    = CheckedProofMode !ProofSyntaxId
    | CheckedCompiledMode !DeclarationSyntaxId

data DeclarationObjects
    = AssertedDeclarationObjects ![AssertedObject]
    | CheckedDeclarationObjects !CheckedObjectContribution

declarationObjectAssertions :: DeclarationObjects -> [AssertedObject]
declarationObjectAssertions = \case
    AssertedDeclarationObjects objects -> objects
    CheckedDeclarationObjects contribution -> checkedObjectContributionAssertions contribution

extendDeclarationObjects :: CheckedObjectClosure -> DeclarationObjects -> Either ObjectValidationError CheckedObjectClosure
extendDeclarationObjects closure = \case
    AssertedDeclarationObjects objects -> extendObjectClosure closure objects
    CheckedDeclarationObjects contribution -> insertCheckedObjectContribution closure contribution

-- | One completely lowered, authority-free declaration transaction.  The
-- family body is a closed checked authorization recipe owned by its exact
-- lowerer; structural effects and stable source-ordered candidate stages are
-- common.  This value is invocation-local and never serialized.
data CheckedDeclaration body = CheckedDeclaration
    !CheckedDeclarationMode
    !DeclarationObjects
    ![CheckedPropositionContent]
    ![SemanticGlobalBinding]
    !(Maybe StructureBatch.PendingStructureBatch)
    ![Registration PlannedCandidatePosition]
    !(Maybe (SemanticGlobalKey, BindingConstruction PlannedCandidatePosition))
    ![NonEmpty CheckedCandidate]
    !body

checkedProofDeclaration
    :: ProofSyntaxId
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> [SemanticGlobalBinding]
    -> Maybe StructureBatch.PendingStructureBatch
    -> [NonEmpty CheckedCandidate]
    -> body
    -> CheckedDeclaration body
checkedProofDeclaration
        syntax objects propositions globals structures stages =
    CheckedDeclaration
        (CheckedProofMode syntax) (AssertedDeclarationObjects objects) propositions globals structures
        [] Nothing stages

checkedProofDeclarationWithRegistrations
    :: ProofSyntaxId
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> [SemanticGlobalBinding]
    -> Maybe StructureBatch.PendingStructureBatch
    -> [Registration PlannedCandidatePosition]
    -> [NonEmpty CheckedCandidate]
    -> body
    -> CheckedDeclaration body
checkedProofDeclarationWithRegistrations syntax objects propositions
        globals structures registrations stages =
    CheckedDeclaration
        (CheckedProofMode syntax) (AssertedDeclarationObjects objects) propositions globals structures
        (normalizeRegistrations registrations) Nothing stages

checkedCompiledDeclaration
    :: DeclarationSyntaxId
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> [SemanticGlobalBinding]
    -> Maybe StructureBatch.PendingStructureBatch
    -> [NonEmpty CheckedCandidate]
    -> body
    -> CheckedDeclaration body
checkedCompiledDeclaration
        syntax objects propositions globals structures stages =
    CheckedDeclaration
        (CheckedCompiledMode syntax) (AssertedDeclarationObjects objects) propositions globals structures
        [] Nothing stages

checkedCompiledDeclarationWithRegistrations
    :: DeclarationSyntaxId
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> [SemanticGlobalBinding]
    -> Maybe StructureBatch.PendingStructureBatch
    -> [Registration PlannedCandidatePosition]
    -> [NonEmpty CheckedCandidate]
    -> body
    -> CheckedDeclaration body
checkedCompiledDeclarationWithRegistrations syntax objects propositions
        globals structures registrations stages =
    CheckedDeclaration
        (CheckedCompiledMode syntax) (AssertedDeclarationObjects objects) propositions globals structures
        (normalizeRegistrations registrations) Nothing stages

checkedStructureDeclaration
    :: DeclarationSyntaxId -> CheckedObjectContribution -> StructureBatch.PendingStructureBatch
    -> [Registration PlannedCandidatePosition] -> [NonEmpty CheckedCandidate] -> body -> CheckedDeclaration body
checkedStructureDeclaration syntax contribution batch views stages = CheckedDeclaration
    (CheckedCompiledMode syntax) (CheckedDeclarationObjects contribution) [] [] (Just batch)
    (normalizeRegistrations views) Nothing stages

withDatatypeDescriptor
    :: SemanticGlobalKey -> DatatypeDescriptor PlannedCandidatePosition
    -> CheckedDeclaration body -> CheckedDeclaration body
withDatatypeDescriptor key descriptor
        (CheckedDeclaration mode objects propositions globals structures registrations _ stages body) =
    CheckedDeclaration mode objects propositions globals structures registrations
        (Just (key, DatatypeConstruction descriptor)) stages body

withRecursiveDefinitionDescriptor
    :: SemanticGlobalKey -> RecursiveDefinitionDescriptor PlannedCandidatePosition
    -> CheckedDeclaration body -> CheckedDeclaration body
withRecursiveDefinitionDescriptor key descriptor
        (CheckedDeclaration mode objects propositions globals structures registrations _ stages body) =
    CheckedDeclaration mode objects propositions globals structures registrations
        (Just (key, RecursiveConstruction descriptor)) stages body

resolvePlannedRegistrations
    :: [Registration PlannedCandidatePosition] -> [NonEmpty PreparedCandidate]
    -> Either DeclarationError [Registration SemanticFactOccurrenceFingerprint]
resolvePlannedRegistrations pending stages = for pending \registration -> do
    let position = registrationSource registration
    PreparedCandidate candidate authority direct _ _ <- maybe
        (Left (NotionViewCandidateMissing position)) Right (candidateAtPosition position stages)
    let occurrence = candidateOccurrence candidate authority
    validateRegistrationAuthority position occurrence direct (registrationBody registration)
    pure (semanticFactFingerprint occurrence <$ registration)

validateRegistrationAuthority
    :: PlannedCandidatePosition -> SemanticFactOccurrence -> DirectAuthorization
    -> RegistrationBody -> Either DeclarationError ()
validateRegistrationAuthority position occurrence direct = \case
    RegisterNotionView{} -> validateGeneratedOrSourceViewAuthority position
        (semanticFactPurpose occurrence) (semanticFactAuthority occurrence) direct
    RegisterProviderResult{} -> unless
        (factAuthoritySafety (semanticFactAuthority occurrence) == cleanAuthoritySafety
            && providerResultAuthority direct)
        (Left (NotionViewAuthorityInvalid position))
    _ -> validateNotionViewAuthority position (semanticFactAuthority occurrence) direct

-- Compiler-generated introductions use the same exact theorem-shape checks
-- as source classifications. Their authority remains an ordinary kernel proof.
providerResultAuthority :: DirectAuthorization -> Bool
providerResultAuthority = \case
    CheckedSourceProof{} -> True
    CheckedKernelConstruction CheckedDerivedConstruction -> True
    _ -> False

candidateAtPosition
    :: PlannedCandidatePosition
    -> [NonEmpty candidate]
    -> Maybe candidate
candidateAtPosition (PlannedCandidatePosition stage index) stages =
    nth stage stages >>= nth index . toList

validateNotionViewAuthority
    :: PlannedCandidatePosition
    -> FactAuthority
    -> DirectAuthorization
    -> Either DeclarationError ()
validateNotionViewAuthority position authority direct =
    unless
        ( factAuthoritySafety authority == cleanAuthoritySafety
          && case direct of
                CheckedSourceProof{} -> True
                _ -> False
        )
        (Left (NotionViewAuthorityInvalid position))

validateGeneratedOrSourceViewAuthority
    :: PlannedCandidatePosition -> FactPurpose -> FactAuthority -> DirectAuthorization -> Either DeclarationError ()
validateGeneratedOrSourceViewAuthority position purpose authority direct = case purpose of
    GeneralFactPurpose -> case direct of
        CheckedKernelConstruction CheckedDefinitionProjection{} ->
            unless (factAuthoritySafety authority == cleanAuthoritySafety)
                (Left (NotionViewAuthorityInvalid position))
        _ -> validateNotionViewAuthority position authority direct
    StructureFactPurpose (Schema.StructureLawId _ Schema.ParentInheritanceLaw{}) ->
        unless (factAuthoritySafety authority == cleanAuthoritySafety
            && direct == CheckedKernelConstruction (CheckedStructureLaw StructurePredicateComponent))
            (Left (NotionViewAuthorityInvalid position))
    StructureFactPurpose _ -> Left (NotionViewAuthorityInvalid position)

prepareCandidateSpecDriver
    :: [AssertedObject]
    -> ScopedCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> ModuleDriver failure (Either DeclarationError CandidateSpec)
prepareCandidateSpecDriver objects scoped eligibility aliases =
    prepareCandidateSpecWithDriverClosure objects
        (\closure ->
            prepareScopedCandidateSpec
                closure scoped eligibility aliases)

prepareFrozenCandidateSpecDriver
    :: [AssertedObject]
    -> FrozenCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> ModuleDriver failure (Either DeclarationError CandidateSpec)
prepareFrozenCandidateSpecDriver objects frozen eligibility aliases =
    prepareCandidateSpecWithDriverClosure objects
        (\closure ->
            prepareFrozenCandidateSpec
                closure frozen eligibility aliases)

prepareDefinitionEquationSpecDriver
    :: [AssertedObject]
    -> ObjectId
    -> SemanticName
    -> ModuleDriver failure (Either DeclarationError CandidateSpec)
prepareDefinitionEquationSpecDriver objects identity alias =
    prepareCandidateSpecWithDriverClosure objects
        (\closure ->
            prepareDefinitionEquationSpec closure identity alias)

prepareUnaryPredicateDefinitionEquationSpecDriver
    :: [AssertedObject]
    -> ObjectId
    -> SemanticName
    -> ModuleDriver failure (Either DeclarationError CandidateSpec)
prepareUnaryPredicateDefinitionEquationSpecDriver objects identity alias =
    prepareCandidateSpecWithDriverClosure objects
        (\closure ->
            prepareUnaryPredicateDefinitionEquationSpec
                closure identity alias)

prepareCandidateSpecLowering
    :: [AssertedObject]
    -> ScopedCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> LoweringDriver (Either DeclarationError CandidateSpec)
prepareCandidateSpecLowering objects scoped eligibility aliases =
    prepareCandidateSpecWithLoweringClosure objects
        (\closure ->
            prepareScopedCandidateSpec
                closure scoped eligibility aliases)

prepareFrozenCandidateSpecLowering
    :: [AssertedObject]
    -> FrozenCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> LoweringDriver (Either DeclarationError CandidateSpec)
prepareFrozenCandidateSpecLowering objects frozen eligibility aliases =
    prepareCandidateSpecWithLoweringClosure objects
        (\closure ->
            prepareFrozenCandidateSpec
                closure frozen eligibility aliases)

prepareDefinitionEquationSpecLowering
    :: [AssertedObject]
    -> ObjectId
    -> SemanticName
    -> LoweringDriver (Either DeclarationError CandidateSpec)
prepareDefinitionEquationSpecLowering objects identity alias =
    prepareDefinitionEquationSpecWithEligibilityLowering
        objects identity SearchEligible [alias]

prepareDefinitionEquationSpecWithEligibilityLowering
    :: [AssertedObject]
    -> ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> LoweringDriver (Either DeclarationError CandidateSpec)
prepareDefinitionEquationSpecWithEligibilityLowering
        objects identity eligibility aliases =
    prepareCandidateSpecWithLoweringClosure objects
        (\closure ->
            prepareDefinitionEquationSpecWithEligibility
                closure identity eligibility aliases)

-- | Prepare the public flattened extensional view of one checked, named set
-- construction.  The returned descriptor binds direct authorization to the
-- transparent object and the complete checked source decomposition.
prepareNamedSetConstructionSpecLowering
    :: [AssertedObject]
    -> ObjectId
    -> NamedSetConstruction ObjectId
    -> SemanticName
    -> LoweringDriver
        (Either
            DeclarationError
            (CandidateSpec, KernelConstructionDescriptor))
prepareNamedSetConstructionSpecLowering objects identity construction alias =
    prepareNamedSetConstructionSpecWithEligibilityLowering
        objects identity construction SearchEligible [alias]

prepareNamedSetConstructionSpecWithEligibilityLowering
    :: [AssertedObject]
    -> ObjectId
    -> NamedSetConstruction ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> LoweringDriver
        (Either
            DeclarationError
            (CandidateSpec, KernelConstructionDescriptor))
prepareNamedSetConstructionSpecWithEligibilityLowering
        objects identity construction eligibility aliases =
    withLoweringBuilder \builder -> do
        closure <-
            first DeclarationObjectValidationFailed
                (extendObjectClosure
                    (logicalBuilderObjectClosure builder)
                    objects)
        (proposition, descriptor) <-
            prepareNamedSetConstruction
                (logicalBuilderFoundation builder)
                closure identity construction
        spec <-
            prepareFrozenCandidateSpec
                closure proposition eligibility aliases
        pure (spec, descriptor)

prepareRelationalSetConstructionSpecLowering
    :: [AssertedObject]
    -> ObjectId
    -> CheckedRelationalSetConstruction ObjectId
    -> FrozenCheckedCore ObjectId
    -> SemanticName
    -> LoweringDriver
        (Either
            DeclarationError
            (CandidateSpec, KernelConstructionDescriptor))
prepareRelationalSetConstructionSpecLowering
        objects identity construction functionality alias =
    withLoweringBuilder \builder -> do
        closure <-
            first DeclarationObjectValidationFailed
                (extendObjectClosure
                    (logicalBuilderObjectClosure builder)
                    objects)
        (proposition, descriptor) <-
            prepareRelationalSetConstruction
                (logicalBuilderFoundation builder)
                closure identity construction functionality
        spec <-
            prepareFrozenCandidateSpec
                closure proposition SearchEligible [alias]
        pure (spec, descriptor)

prepareUnaryPredicateDefinitionEquationSpecLowering
    :: [AssertedObject]
    -> ObjectId
    -> SemanticName
    -> LoweringDriver (Either DeclarationError CandidateSpec)
prepareUnaryPredicateDefinitionEquationSpecLowering
        objects identity alias =
    prepareCandidateSpecWithLoweringClosure objects
        (\closure ->
            prepareUnaryPredicateDefinitionEquationSpec
                closure identity alias)

-- | Prepare one closed Vampire obligation whose only premise is a
-- conditionally available fact from a strictly earlier candidate stage of
-- the same declaration.  The temporary checked stage contains public fact
-- semantics and structural provenance only; admission must still consume the
-- corresponding real reserved candidate before accepting this request.
prepareStagedCandidateVampireDriver
    :: Location
    -> [AssertedObject]
    -> CandidateSpec
    -> CandidateSpec
    -> ModuleDriver failure
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidateVampireDriver
        location objects premiseSpec targetSpec =
    do
        builder <- State.gets driverBuilder
        liftIO
            (prepareStagedCandidateVampireWith
                builder location objects premiseSpec targetSpec [])

prepareStagedCandidateVampireLowering
    :: Location
    -> [AssertedObject]
    -> CandidateSpec
    -> CandidateSpec
    -> LoweringDriver
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidateVampireLowering
        location objects premiseSpec targetSpec =
    prepareStagedCandidateVampireWithAuxiliariesLowering
        location objects premiseSpec targetSpec []

-- | Prepare a staged generated proof with the explicitly required foundation
-- interface.  Ordinary source proofs continue to discover or cite their own
-- auxiliaries; compiler-derived facts use this only when their construction
-- has a fixed, auditable dependency such as set extensionality.
prepareStagedCandidateVampireWithAuxiliariesLowering
    :: Location
    -> [AssertedObject]
    -> CandidateSpec
    -> CandidateSpec
    -> [FoundationAxiomTag]
    -> LoweringDriver
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidateVampireWithAuxiliariesLowering
        location objects premiseSpec targetSpec auxiliaryTags =
    do
        ProspectiveBuilder builder <- State.gets loweringBuilder
        liftIO
            (prepareStagedCandidateVampireWith
                builder location objects premiseSpec targetSpec auxiliaryTags)

-- | Prepare a generated proof from several strictly earlier candidates and
-- an exact set of already visible facts.  The former become local premises
-- whose authority is consumed when the declaration is admitted; the latter
-- remain ordinary fingerprinted global premises and are validated by the
-- normal Vampire obligation boundary.
prepareStagedCandidatesVampireWithFactsAndAuxiliariesLowering
    :: Location
    -> [AssertedObject]
    -> [CandidateSpec]
    -> [SemanticFactOccurrenceFingerprint]
    -> CandidateSpec
    -> [FoundationAxiomTag]
    -> LoweringDriver
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidatesVampireWithFactsAndAuxiliariesLowering
        location objects premiseSpecs visibleFacts targetSpec auxiliaryTags =
    do
        ProspectiveBuilder builder <- State.gets loweringBuilder
        liftIO
            (prepareStagedCandidatesVampireWithFactsAndAuxiliaries
                builder location objects premiseSpecs visibleFacts targetSpec
                auxiliaryTags)

prepareStagedCandidateVampireWith
    :: BuilderState evidence
    -> Location
    -> [AssertedObject]
    -> CandidateSpec
    -> CandidateSpec
    -> [FoundationAxiomTag]
    -> IO
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidateVampireWith
        builder location objects premiseSpec targetSpec auxiliaryTags = do
    prepareStagedCandidatesVampireWithFactsAndAuxiliaries
        builder location objects [premiseSpec] [] targetSpec
        auxiliaryTags

prepareStagedCandidatesVampireWithFactsAndAuxiliaries
    :: BuilderState evidence
    -> Location
    -> [AssertedObject]
    -> [CandidateSpec]
    -> [SemanticFactOccurrenceFingerprint]
    -> CandidateSpec
    -> [FoundationAxiomTag]
    -> IO
        (Either
            DeclarationError
            (PreparedVampireObligation Void ()))
prepareStagedCandidatesVampireWithFactsAndAuxiliaries
        builder location objects premiseSpecs visibleFacts targetSpec
        auxiliaryTags = do
    let staged = do
            closure <-
                first DeclarationObjectValidationFailed
                    (extendObjectClosure
                        (logicalBuilderObjectClosure builder)
                        objects)
            premises <-
                prospectiveStagePremises
                    builder closure premiseSpecs targetSpec
            pure (closure, premises)
    case staged of
        Left failure -> pure (Left failure)
        Right (closure, premises) -> do
            prepared <-
                forceVampirePreparation
                    (prepareClosedCandidateVampireWithFactsAndAuxiliaries
                        builder closure (candidateSpecProposition targetSpec)
                        premises visibleFacts auxiliaryTags)
            pure
                (first
                    (ProofObligationFailedAt location
                        . CurrentCandidateVampirePreparationFailed)
                    prepared)

candidateSpecProposition :: CandidateSpec -> CheckedPropositionContent
candidateSpecProposition
        (CandidateSpec proposition _purpose _eligibility _aliases _composition) =
    proposition

prospectiveStagePremises
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> [CandidateSpec]
    -> CandidateSpec
    -> Either DeclarationError [CheckedPropositionContent]
prospectiveStagePremises builder closure premiseSpecs targetSpec = do
    let owner = logicalBuilderOwner builder
        declaration =
            declarationSlot owner
                (localDeclarationOrdinal
                    (logicalBuilderNextDeclaration builder))
        firstFact = logicalBuilderNextFact builder
        indexedPremises = zip [0 :: Natural ..] premiseSpecs
        premiseSlots =
            [ factSlot owner (localFactOrdinal (firstFact + index))
            | (index, _spec) <- indexedPremises
            ]
        targetSlot =
            factSlot owner
                (localFactOrdinal
                    (firstFact + fromIntegral (length premiseSpecs)))
        premiseStage = CandidateStage 0
        targetStage = CandidateStage 1
        makeEntry premiseSlot premiseSpec =
            let proposition = candidateSpecProposition premiseSpec
                authority =
                    factAuthority
                        (theoremRef
                            (logicalBuilderTheory builder)
                            (checkedPropositionId proposition))
                        cleanAuthoritySafety
                occurrence =
                    candidateSpecOccurrence
                        premiseSlot authority premiseSpec
            in ( premiseSlot
               , FactEntry proposition occurrence
                    (PlanningEvidence
                        authority
                        Nothing
                        (Just
                            (PlanningProvenance
                                declaration premiseStage premiseSlot)))
               )
        stage =
            CheckedDeclarationStage declaration closure
                (Map.fromList
                    (zipWith makeEntry premiseSlots premiseSpecs))
    unless
        (propositionMatchesClosure closure
            (candidateSpecProposition targetSpec))
        (Left (PlanningFactContractMismatch targetSlot))
    traverse
        (useProspectiveStageFact
            stage targetStage targetSlot premiseStage)
        premiseSlots

useProspectiveStageFact
    :: CheckedDeclarationStage
    -> CandidateStage
    -> FactSlot
    -> CandidateStage
    -> FactSlot
    -> Either DeclarationError CheckedPropositionContent
useProspectiveStageFact
        (CheckedDeclarationStage ownSlot closure entries)
        currentStage currentSlot expectedStage premiseSlot = do
    FactEntry proposition occurrence
        (PlanningEvidence authority _direct provenance) <-
            maybe
                (Left (PlanningFactContractMismatch premiseSlot))
                Right
                (Map.lookup premiseSlot entries)
    unless
        ( provenance
            == Just
                (PlanningProvenance
                    ownSlot expectedStage premiseSlot)
          && expectedStage < currentStage
          && semanticFactSlot occurrence == premiseSlot
          && semanticFactAuthority occurrence == authority
          && propositionMatchesClosure closure proposition
        )
        (Left (PlanningFactContractMismatch currentSlot))
    pure proposition

prepareCandidateSpecWithDriverClosure
    :: [AssertedObject]
    -> (CheckedObjectClosure -> Either DeclarationError CandidateSpec)
    -> ModuleDriver failure (Either DeclarationError CandidateSpec)
prepareCandidateSpecWithDriverClosure objects prepare = do
    builder <- State.gets driverBuilder
    pure do
        closure <-
            first DeclarationObjectValidationFailed
                (extendObjectClosure
                    (logicalBuilderObjectClosure builder)
                    objects)
        prepare closure

prepareCandidateSpecWithLoweringClosure
    :: [AssertedObject]
    -> (CheckedObjectClosure -> Either DeclarationError value)
    -> LoweringDriver (Either DeclarationError value)
prepareCandidateSpecWithLoweringClosure objects prepare =
    withLoweringBuilder \builder -> do
        closure <-
            first DeclarationObjectValidationFailed
                (extendObjectClosure
                    (logicalBuilderObjectClosure builder)
                    objects)
        prepare closure

data ReservedCandidate = ReservedCandidate
    !BuilderIdentity
    !PrefixContextId
    !DeclarationInvocation
    !CandidateStage
    !FactSlot
    !CandidateSpec

reservedCandidateSlot :: ReservedCandidate -> FactSlot
reservedCandidateSlot
        (ReservedCandidate _ _ _ _ slot _) =
    slot

reservedCandidateStage :: ReservedCandidate -> Natural
reservedCandidateStage
        (ReservedCandidate _ _ _ (CandidateStage stage) _ _) =
    stage

candidateCheckedProposition
    :: ReservedCandidate
    -> CheckedPropositionContent
candidateCheckedProposition
        (ReservedCandidate _ _ _ _ _
            (CandidateSpec proposition _ _ _ _)) =
    proposition

candidateTheoremReference
    :: BuilderState evidence
    -> ReservedCandidate
    -> TheoremRef
candidateTheoremReference builder candidate =
    theoremRef
        (logicalBuilderTheory builder)
        (checkedPropositionId
            (candidateCheckedProposition candidate))


data PendingCandidate = PendingCandidate
    !ReservedCandidate
    !ValidationCertificate
    !PendingFactAuthorization

data DeclarationState = DeclarationState
    { declarationVampireResolver :: !VampireResolver
    , declarationFormationRecorder :: !FormationDiagnostics.Recorder
    , declarationPlannedRequests :: !PlannedRequestCursor
    , declarationCandidateValidations :: !(Map FactSlot Materialization.CandidateValidation)
    , declarationBuilder :: !LogicalBuilder
    , declarationPreparedResult :: !(PreparedDeclaration ())
    , declarationObjectClosure :: !CheckedObjectClosure
    , declarationReservations :: !(Map FactSlot ReservedCandidate)
    , declarationPending :: !(Map FactSlot PendingCandidate)
    , declarationAuthorizationFrontier :: !Natural
    }

declarationOwnSlot :: DeclarationState -> DeclarationSlot
declarationOwnSlot = declarationDeltaSlot . preparedDeclarationDelta . declarationPreparedResult

declarationInvocation :: DeclarationState -> DeclarationInvocation
declarationInvocation = DeclarationInvocation . logicalBuilderNextInvocation . declarationBuilder

declarationNextStage :: DeclarationState -> Natural
declarationNextStage = fromIntegral . length . preparedDeclarationCandidates . declarationPreparedResult

-- | Authority-free view of checked declaration-local semantics.  This is the
-- narrow staging substrate for later lowerers: it carries the exact object
-- closure and conditional public fact contracts, but no builder identity,
-- prefix, invocation, pending authorization, admitted alias, or published
-- occurrence.
data CheckedDeclarationStage = CheckedDeclarationStage
    !DeclarationSlot
    !CheckedObjectClosure
    !(Map FactSlot (FactEntry PlanningEvidence))

type Declaration =
    Eff (State DeclarationState : DeclarationEffects)

failDeclaration :: DeclarationError -> Declaration value
failDeclaration failure =
    Error.throwError_ failure

prepareScopedCandidateSpec
    :: CheckedObjectClosure
    -> ScopedCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> Either DeclarationError CandidateSpec
prepareScopedCandidateSpec closure scoped eligibility aliases = do
    frozen <-
        maybe (Left CandidatePropositionNotClosed) Right
            (closeScopedCore scoped)
    prepareFrozenCandidateSpec closure frozen eligibility aliases

prepareFrozenCandidateSpec
    :: CheckedObjectClosure
    -> FrozenCheckedCore ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> Either DeclarationError CandidateSpec
prepareFrozenCandidateSpec closure frozen eligibility aliases = do
    unless
        (frozenCoreType frozen == TyProp)
        (Left
            (CandidatePropositionNotProposition
                (frozenCoreType frozen)))
    proposition <-
        first DeclarationPropositionValidationFailed
            (validatePropositionContent closure (frozenCoreTerm frozen))
    pure (candidateSpec proposition eligibility aliases)

prepareDefinitionEquationSpec
    :: CheckedObjectClosure
    -> ObjectId
    -> SemanticName
    -> Either DeclarationError CandidateSpec
prepareDefinitionEquationSpec closure identity alias = do
    prepareDefinitionEquationSpecWithEligibility
        closure identity SearchEligible [alias]

prepareDefinitionEquationSpecWithEligibility
    :: CheckedObjectClosure
    -> ObjectId
    -> FactSearchEligibility
    -> [SemanticName]
    -> Either DeclarationError CandidateSpec
prepareDefinitionEquationSpecWithEligibility
        closure identity eligibility aliases = do
    content <-
        maybe
            (Left (DefinitionEquationObjectMissing identity))
            Right
            (lookupCheckedObjectContent identity closure)
    (coreType, body) <-
        case content of
            TransparentObjectContent _theory objectType objectBody ->
                Right (objectType, objectBody)
            _ ->
                Left (DefinitionEquationObjectNotTransparent identity)
    proposition <-
        first DeclarationPropositionValidationFailed
            (validatePropositionContent
                closure
                (definitionEquationTarget identity coreType body))
    pure (candidateSpec proposition eligibility aliases)

-- | The canonical equation view of a transparent definition.  Objects whose
-- type is an ordinary first-order symbol type are presented pointwise, while
-- the authoritative transparent object itself remains the exact curried HOL
-- object.  Definitions with a genuinely higher-order argument retain their
-- exact object equation.  Named set constructions may expose their separately
-- derived extensional view as the source-level definition fact instead.
definitionEquationTarget
    :: ObjectId
    -> CoreType
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
definitionEquationTarget =
    canonicalDefinitionEquationTarget

prepareNamedSetConstruction
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> NamedSetConstruction ObjectId
    -> Either
        DeclarationError
        (FrozenCheckedCore ObjectId, KernelConstructionDescriptor)
prepareNamedSetConstruction foundation closure identity construction = do
    derived <-
        maybe
            (Left KernelConstructionDescriptorMismatch)
            Right
            (namedSetConstructionObjectFact
                (checkedFoundationSetConstruction foundation)
                closure
                identity
                construction)
    pure
        ( namedSetConstructionFactProposition derived
        , CheckedSetConstructionExtensionality
            identity
            (namedSetConstructionFactDescriptor derived)
        )

prepareRelationalSetConstruction
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> CheckedRelationalSetConstruction ObjectId
    -> FrozenCheckedCore ObjectId
    -> Either
        DeclarationError
        (FrozenCheckedCore ObjectId, KernelConstructionDescriptor)
prepareRelationalSetConstruction
        foundation closure identity construction functionality = do
    derived <-
        maybe
            (Left KernelConstructionDescriptorMismatch)
            Right
            (relationalSetConstructionObjectFact
                (checkedFoundationSetConstruction foundation)
                closure
                identity
                construction
                functionality)
    pure
        ( relationalSetConstructionFactProposition derived
        , CheckedSetConstructionExtensionality
            identity
            (relationalSetConstructionFactDescriptor derived)
        )

prepareUnaryPredicateDefinitionEquationSpec
    :: CheckedObjectClosure
    -> ObjectId
    -> SemanticName
    -> Either DeclarationError CandidateSpec
prepareUnaryPredicateDefinitionEquationSpec closure identity alias = do
    content <-
        maybe
            (Left (DefinitionEquationObjectMissing identity))
            Right
            (lookupCheckedObjectContent identity closure)
    case content of
        TransparentObjectContent _theory
                (TyArrow TySet TyProp) (CLam TySet _predicate) ->
            prepareDefinitionEquationSpec closure identity alias
        _ ->
            Left
                (DefinitionEquationObjectNotUnaryPredicate identity)

data CandidatePremise = CandidatePremise
    !(Maybe SemanticFactOccurrenceFingerprint) !CheckedPropositionContent

-- | The production owner boundary for one candidate proof.  The state keeps
-- the exact checked-object closure, ordered admitted premises, accumulated
-- safety, and owner-reserved candidate together.  Generic replay receives
-- only projections of this state and therefore remains provisional until the
-- enclosing authorization path completes the candidate.
data CandidateProofState = CandidateProofState
    { candidateProofDeclaration :: !DeclarationState
    , candidateProofCandidate :: !ReservedCandidate
    , candidateProofCachedValidation
        :: !(Maybe Materialization.CandidateValidation)
    , candidateProofPremisesReversed :: ![CandidatePremise]
    , candidateProofPremiseCount :: !Natural
    , candidateProofSafety :: !CandidateSafety
    , candidateProofDependencies :: !(Set SemanticFactOccurrenceFingerprint)
    , candidateProofAcceptedRequestsReversed
        :: ![PreparedRequestId]
    }

candidateProofObjectClosure :: CandidateProofState -> CheckedObjectClosure
candidateProofObjectClosure = declarationObjectClosure . candidateProofDeclaration

candidateProofBuilder :: CandidateProofState -> LogicalBuilder
candidateProofBuilder =
    declarationBuilder . candidateProofDeclaration

type CandidateProof =
    Eff (State CandidateProofState : DeclarationEffects)

completeFormationCandidate :: FormationDiagnostics.Completion -> CandidateProof value -> CandidateProof value
completeFormationCandidate completion action = do
    recorder <- State.gets (declarationFormationRecorder . candidateProofDeclaration)
    finishFormationCompletion recorder completion action

completeFormationDeclaration :: FormationDiagnostics.Completion -> Declaration value -> Declaration value
completeFormationDeclaration completion action = do
    recorder <- State.gets declarationFormationRecorder
    finishFormationCompletion recorder completion action

finishFormationCompletion
    :: (Error DeclarationError :> es, IOE :> es)
    => FormationDiagnostics.Recorder -> FormationDiagnostics.Completion -> Eff es value -> Eff es value
finishFormationCompletion recorder completion action = do
    result <- FormationDiagnostics.finishCompletion recorder completion
        (Error.catchError (Right <$> action) (\_ failure -> pure (Left (failure :: DeclarationError))))
    liftEitherEffect result

type DeclarationBase = Eff DeclarationEffects

-- | Attach source trivia to a proof-obligation failure.  The location does
-- not participate in validation or request identity.
locateProofObligation
    :: Location
    -> CandidateProof value
    -> CandidateProof value
locateProofObligation location =
    mapErrorEffect (ProofObligationFailedAt location)

-- | Record that the current source proof discharged one goal with @Omitted@.
recordOmittedUse :: CandidateProof ()
recordOmittedUse = do
    state <- State.get
    State.put
        state
            { candidateProofSafety =
                addCandidateEscape
                    Omitted
                    (candidateProofSafety state)
            }

-- Preparation limits do not change the eventual prover failure or its
-- classification. Retain the observation as a diagnostic sidecar only.
notePreparationExhaustion
    :: Preparation.PreparationStatistics -> CandidateProof value -> CandidateProof value
notePreparationExhaustion statistics =
    mapErrorEffect (ProofPreparationExhausted statistics)

noteProofObligationGoal :: ScopedCheckedCore ObjectId -> CandidateProof value -> CandidateProof value
noteProofObligationGoal goal = mapErrorEffect (ProofObligationGoal goal)

noteRecordObligations :: [Obligation.RecordObligation] -> CandidateProof value -> CandidateProof value
noteRecordObligations requirements = mapErrorEffect $ \failure ->
    let underlying = forgetGoal failure
    in if null requirements then underlying
       else RecordObligationFailure (Obligation.obligationContext (failedGoal failure) requirements) underlying
  where
    -- The goal is only a handoff to this diagnostic owner. Ordinary proof
    -- errors retain their existing shape, and record errors keep the selected
    -- context rather than a redundant copy of the complete failed goal.
    forgetGoal = \case
        ProofObligationGoal _ failure -> forgetGoal failure
        ProofObligationFailedAt location failure -> ProofObligationFailedAt location (forgetGoal failure)
        ProofPreparationExhausted statistics failure -> ProofPreparationExhausted statistics (forgetGoal failure)
        failure -> failure
    failedGoal = \case
        ProofObligationGoal goal _ -> Just goal
        ProofObligationFailedAt _ failure -> failedGoal failure
        ProofPreparationExhausted _ failure -> failedGoal failure
        _ -> Nothing

declarationRecordObligations :: DeclarationError -> [Obligation.ObligationContext]
declarationRecordObligations = \case
    RecordObligationFailure context failure -> context : declarationRecordObligations failure
    ProofObligationFailedAt _ failure -> declarationRecordObligations failure
    ProofObligationGoal _ failure -> declarationRecordObligations failure
    ProofPreparationExhausted _ failure -> declarationRecordObligations failure
    _ -> []

data VampireGlobalPremiseSelection
    = VampireEligiblePremises
    | VampireExplicitPremises
        !(NonEmpty SemanticFactOccurrenceFingerprint)
    | VampireCitedStructurePremises !CitedStructureViews
    | VampireNoGlobalPremises
    deriving stock (Show, Eq)

data VampireLocalPremiseSelection
    = VampireFirstOrderLocalProjection
    | VampireRouteSensitiveLocalProjection
    | VampireCompleteLocalContext
    deriving stock (Show, Eq)

data VampirePremisePolicy = VampirePremisePolicy
    { vampireGlobalPremiseSelection :: !VampireGlobalPremiseSelection
    , vampireLocalPremiseSelection :: !VampireLocalPremiseSelection
    } deriving stock (Show, Eq)

-- | Compiler-generated ATP obligations retain their established eligible
-- global pool and first-order local projection.  Source omissions never use
-- this policy.
internalVampirePremisePolicy :: VampirePremisePolicy
internalVampirePremisePolicy =
    VampirePremisePolicy
        VampireEligiblePremises
        VampireFirstOrderLocalProjection

explicitVampirePremisePolicy
    :: NonEmpty SemanticFactOccurrenceFingerprint
    -> VampirePremisePolicy
explicitVampirePremisePolicy fingerprints =
    VampirePremisePolicy
        (VampireExplicitPremises fingerprints)
        VampireRouteSensitiveLocalProjection

-- Source citations may expose checked structural views. Compiler-generated
-- explicit selections keep their exact dependency lists.
citedStructureVampirePremisePolicy :: CitedStructureViews -> VampirePremisePolicy
citedStructureVampirePremisePolicy views = VampirePremisePolicy
    (VampireCitedStructurePremises views) VampireRouteSensitiveLocalProjection

-- | Plain @\auto@ selects no ordinary global facts. Complete locals retain
-- higher-order evidence even when the goal itself looks first-order.
localVampirePremisePolicy :: VampirePremisePolicy
localVampirePremisePolicy =
    VampirePremisePolicy
        VampireNoGlobalPremises
        VampireCompleteLocalContext

data VampireObligationPreparationError local
    = VampireObligationClaimProjectionFailed
        !(Backend.SupportedPropositionProjectionError local)
    | VampireObligationLocalProjectionFailed
        !Backend.LocalPremiseOrdinal
        !(Backend.SupportedPropositionProjectionError local)
    | VampireObligationLocalClassificationFailed
        !Backend.LocalPremiseOrdinal
        !(Backend.BackendClassificationError ObjectId)
    | VampireObligationFactNotVisible
        !SemanticFactOccurrenceFingerprint
    | VampireObligationFactInvalid
        !SemanticFactOccurrenceFingerprint
    | VampireObligationExcludedFactNotSelected
        !SemanticFactOccurrenceFingerprint
    | VampireObligationPlanningFailed
        !(Backend.TypedProblemError local ObjectId)
    | VampireObligationEncodingFailed
        !(Tptp.TypedTptpPreparationError local ObjectId)
    deriving stock (Show, Eq)

data ScopedVampirePremise local origin = ScopedVampirePremise
    !Backend.LocalPremiseOrdinal
    !origin
    !(Vector (local, CoreType))
    !(ScopedCheckedCore ObjectId)

scopedVampirePremise
    :: Backend.LocalPremiseOrdinal
    -> origin
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> ScopedVampirePremise local origin
scopedVampirePremise =
    ScopedVampirePremise

data PreparedVampireObligation local origin =
    PreparedVampireObligation
        !(Maybe CitedStructureViews)
        !(Backend.TypedProblem
            SemanticFactOccurrenceFingerprint
            local
            origin
            ObjectId)
        !(Provers.PreparedTypedProverTask
            SemanticFactOccurrenceFingerprint
            local
            origin
            ObjectId)

preparedVampireObligationRoute
    :: PreparedVampireObligation local origin
    -> Backend.TypedProblemRoute
preparedVampireObligationRoute
        (PreparedVampireObligation _views problem _task) =
    Backend.typedProblemRoute problem

-- | Prepare a scoped task for a trusted structural proof checker.  This
-- validates the typed problem but does not establish how its local judgements
-- derive from the enclosing theorem.  'Checking.Proof' owns that
-- composition on the production path.
prepareScopedVampireObligationDriver
    :: Ord local
    => Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> ModuleDriver failure
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationDriver
        claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForMode
        Provers.DirectTask
        claimSupport
        claim
        scopedLocals
        auxiliaryTags
        selection

-- | Prepare a task in an indirect proof scope owned by the source proof
-- compiler.  Its target may be an intermediate claim: the compiler keeps the
-- negated goal among the local premises and confines this mode to that proof
-- subtree.
prepareScopedContradictionObligationDriver
    :: Ord local
    => Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> ModuleDriver failure
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedContradictionObligationDriver
        claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForMode
        Provers.IndirectTask
        claimSupport
        claim
        scopedLocals
        auxiliaryTags
        selection

prepareScopedVampireObligationLowering
    :: Ord local
    => Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> LoweringDriver
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationLowering
        claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForModeExcludingLowering
        Provers.DirectTask
        Set.empty
        claimSupport claim scopedLocals auxiliaryTags selection

prepareScopedVampireObligationExcludingLowering
    :: Ord local
    => Set SemanticFactOccurrenceFingerprint
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> LoweringDriver
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationExcludingLowering
        excluded claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForModeExcludingLowering
        Provers.DirectTask excluded
        claimSupport claim scopedLocals auxiliaryTags selection

prepareScopedContradictionObligationLowering
    :: Ord local
    => Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> LoweringDriver
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedContradictionObligationLowering
        claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForModeLowering
        Provers.IndirectTask
        claimSupport claim scopedLocals auxiliaryTags selection

prepareScopedVampireObligationForModeLowering
    :: Ord local
    => Provers.VampireTaskMode
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> LoweringDriver
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationForModeLowering
        taskMode claimSupport claim scopedLocals auxiliaryTags selection =
    prepareScopedVampireObligationForModeExcludingLowering
        taskMode Set.empty
        claimSupport claim scopedLocals auxiliaryTags selection

prepareScopedVampireObligationForModeExcludingLowering
    :: Ord local
    => Provers.VampireTaskMode
    -> Set SemanticFactOccurrenceFingerprint
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> LoweringDriver
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationForModeExcludingLowering
        taskMode excluded claimSupport claim scopedLocals
        auxiliaryTags selection =
    do
        ProspectiveBuilder builder <- State.gets loweringBuilder
        liftIO
            (prepareScopedVampireObligationExcludingWith
                builder taskMode excluded claimSupport claim scopedLocals
                auxiliaryTags selection)

prepareScopedVampireObligationForMode
    :: Ord local
    => Provers.VampireTaskMode
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> ModuleDriver failure
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationForMode
        taskMode claimSupport claim scopedLocals auxiliaryTags selection =
    do
        builder <- State.gets driverBuilder
        liftIO
            (prepareScopedVampireObligationWith
                builder taskMode claimSupport claim scopedLocals
                auxiliaryTags selection)

prepareScopedVampireObligationWith
    :: (Ord local)
    => BuilderState evidence
    -> Provers.VampireTaskMode
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> IO
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationWith
        builder taskMode claimSupport claim scopedLocals
        auxiliaryTags selection =
    prepareScopedVampireObligationExcludingWith
        builder taskMode Set.empty claimSupport claim scopedLocals
        auxiliaryTags selection

prepareScopedVampireObligationExcludingWith
    :: Ord local
    => BuilderState evidence
    -> Provers.VampireTaskMode
    -> Set SemanticFactOccurrenceFingerprint
    -> Vector (local, CoreType)
    -> ScopedCheckedCore ObjectId
    -> [ScopedVampirePremise local origin]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> IO
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
prepareScopedVampireObligationExcludingWith
        builder taskMode excluded claimSupport claim scopedLocals
        auxiliaryTags selection =
    forceVampirePreparation preparation
  where
    closure = logicalBuilderObjectClosure builder
    globalTyping = globalTypingFromClosure closure
    preparation = do
        supportedClaim <-
            first VampireObligationClaimProjectionFailed
                (Backend.projectSupportedProposition
                    globalTyping
                    claimSupport
                    claim)
        locals <- traverse prepareLocal scopedLocals
        prepareVampireObligationExcludingWith
            taskMode
            builder
            closure
            excluded
            supportedClaim
            locals
            auxiliaryTags
            selection

    prepareLocal
            (ScopedVampirePremise
                ordinal origin support proposition) = do
        supported <-
            first
                (VampireObligationLocalProjectionFailed ordinal)
                (Backend.projectSupportedProposition
                    globalTyping
                    support
                    proposition)
        first
            (VampireObligationLocalClassificationFailed ordinal)
            (Backend.typedLocalPremise
                globalTyping
                ordinal
                origin
                supported)

prepareVampireObligationWith
    :: Ord local
    => Provers.VampireTaskMode
    -> BuilderState evidence
    -> CheckedObjectClosure
    -> Backend.SupportedProposition local ObjectId
    -> [Backend.TypedLocalPremise local origin ObjectId]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> Either
        (VampireObligationPreparationError local)
        (PreparedVampireObligation local origin)
prepareVampireObligationWith
        taskMode builder closure claim locals auxiliaryTags selection = do
    prepareVampireObligationExcludingWith
        taskMode builder closure Set.empty claim locals auxiliaryTags selection

prepareVampireObligationExcludingWith
    :: Ord local
    => Provers.VampireTaskMode
    -> BuilderState evidence
    -> CheckedObjectClosure
    -> Set SemanticFactOccurrenceFingerprint
    -> Backend.SupportedProposition local ObjectId
    -> [Backend.TypedLocalPremise local origin ObjectId]
    -> [FoundationAxiomTag]
    -> VampirePremisePolicy
    -> Either
        (VampireObligationPreparationError local)
        (PreparedVampireObligation local origin)
prepareVampireObligationExcludingWith
        taskMode builder closure excluded claim locals
        auxiliaryTags policy = do
    let globalTyping = globalTypingFromClosure closure
    originallySelected <-
        selectVampireFacts
            globalTyping
            builder
            (vampireGlobalPremiseSelection policy)
    let selectedReferences =
            Set.fromList
                ( Backend.typedBackendFactReference
                    <$> Vector.toList originallySelected
                )
    traverse_
        (\fingerprint ->
            unless
                (fingerprint `Set.member` selectedReferences)
                (Left
                    (VampireObligationExcludedFactNotSelected
                        fingerprint)))
        excluded
    let retainedReferences = case vampireGlobalPremiseSelection policy of
            VampireCitedStructurePremises (CitedStructureViews cited views) ->
                Set.fromList
                    ([fingerprint | fingerprint <- toList cited, fingerprint `Set.notMember` excluded]
                    <> [fingerprint | (_, definition, _, fingerprint, _) <- views,
                        definition `Set.notMember` excluded, fingerprint `Set.notMember` excluded])
            _ -> selectedReferences `Set.difference` excluded
        -- A consumed definition does not leave its derived views behind as
        -- apparently independent premises in a residual child obligation.
        selected =
            Vector.filter
                ((`Set.member` retainedReferences)
                    . Backend.typedBackendFactReference)
                originallySelected
    claimCapability <-
        first
            ( VampireObligationPlanningFailed
                . Backend.TypedProblemClaimClassificationFailed
            )
            (Backend.classifySupportedProposition
                globalTyping
                claim)
    let claimRequiresTh0 =
            case claimCapability of
                Backend.FofProjectable{} -> False
                Backend.RequiresTh0{} -> True
        localPremisePolicy =
            case vampireLocalPremiseSelection policy of
                VampireFirstOrderLocalProjection ->
                    Backend.FirstOrderLocals
                VampireRouteSensitiveLocalProjection
                    | claimRequiresTh0
                        || any
                        (\fact ->
                            case Backend.typedBackendFactCapability fact of
                                Backend.FofProjectable{} -> False
                                Backend.RequiresTh0{} -> True)
                        selected ->
                            Backend.CompleteLocals
                    | otherwise ->
                        Backend.FirstOrderLocals
                VampireCompleteLocalContext ->
                    Backend.CompleteLocals
        propositionDependencies =
            foundationAxiomDependencies
                . Backend.supportedPropositionTerm
        requiredAuxiliaryTags =
            Set.toAscList
                ( Set.fromList auxiliaryTags
                    <> propositionDependencies claim
                    <> foldMap
                        (propositionDependencies
                            . Backend.typedBackendFactProposition)
                        selected
                    <> foldMap
                        (propositionDependencies
                            . Backend.typedLocalPremiseProposition)
                        (Backend.selectTypedLocalPremises
                            localPremisePolicy
                            locals)
                )
        auxiliaries =
            Backend.typedFoundationAuxiliaryInput
                (logicalBuilderFoundation builder)
                <$> requiredAuxiliaryTags
    problem <-
        first VampireObligationPlanningFailed
            (Backend.planTypedProblem
                globalTyping
                selected
                claim
                locals
                auxiliaries
                localPremisePolicy)
    task <-
        first VampireObligationEncodingFailed
            (Provers.prepareTypedProverTask
                taskMode
                problem)
    let views = case vampireGlobalPremiseSelection policy of
            VampireCitedStructurePremises cited -> Just cited
            _ -> Nothing
    pure (PreparedVampireObligation views problem task)

forceVampirePreparation
    :: Either
        (VampireObligationPreparationError local)
        (PreparedVampireObligation local origin)
    -> IO
        (Either
            (VampireObligationPreparationError local)
            (PreparedVampireObligation local origin))
forceVampirePreparation preparation =
    Exception.evaluate (forcePrepared preparation)
  where
    forcePrepared result =
        case result of
            Left err -> err `seq` result
            Right prepared@(PreparedVampireObligation _ _ task) ->
                let request = Provers.preparedTypedProverRequest task
                in Provers.preparedVerificationByteCount request `seq`
                    Provers.preparedVerificationRequestId request `seq`
                    prepared `seq`
                    result

selectVampireFacts
    :: GlobalTyping ObjectId
    -> BuilderState evidence
    -> VampireGlobalPremiseSelection
    -> Either
        (VampireObligationPreparationError local)
        (Vector
            (Backend.TypedBackendFact
                SemanticFactOccurrenceFingerprint
                ObjectId))
selectVampireFacts globalTyping builder selection =
    Vector.fromList <$> case selection of
        VampireEligiblePremises ->
            mapMaybeM prepareEligible
                (Map.toAscList (logicalBuilderFacts builder))
        VampireExplicitPremises fingerprints ->
            traverse prepareExplicit
                (stableUniqueBy id (toList fingerprints))
        VampireCitedStructurePremises views@(CitedStructureViews fingerprints _) ->
            traverse prepareExplicit
                (stableUniqueBy id (toList fingerprints <> (fst <$> citedStructureViewFacts views)))
        VampireNoGlobalPremises ->
            Right []
  where
    prepareEligible (fingerprint, authorized@(FactEntry
            _proposition occurrence _authorization))
        | semanticFactSearchEligibility occurrence
            /= SearchEligible =
                Right Nothing
        | otherwise = do
            fact <- prepareFact fingerprint authorized
            pure case Backend.typedBackendFactCapability fact of
                Backend.FofProjectable{} -> Just fact
                Backend.RequiresTh0{} -> Nothing

    prepareExplicit fingerprint =
        case Map.lookup fingerprint (logicalBuilderFacts builder) of
            Nothing ->
                Left (VampireObligationFactNotVisible fingerprint)
            Just authorized ->
                prepareFact fingerprint authorized

    prepareFact fingerprint
            (FactEntry proposition occurrence _authorization)
        | semanticFactFingerprint occurrence /= fingerprint =
            Left (VampireObligationFactInvalid fingerprint)
        | otherwise = do
            supported <-
                first
                    (const
                        (VampireObligationFactInvalid fingerprint))
                    (Backend.supportedProposition
                        Vector.empty
                        (embedClosedCore
                            []
                            (checkedPropositionTerm proposition)))
            capability <-
                first
                    (const
                        (VampireObligationFactInvalid fingerprint))
                    (Backend.classifySupportedProposition
                        globalTyping
                        supported)
            pure
                (Backend.typedBackendFact
                    fingerprint
                    supported
                    capability)

    mapMaybeM action =
        fmap catMaybes . traverse action

-- | Representation exclusions follow the selected resource occurrences, not
-- whichever equivalent schema recognized the goal or supplied its canonical
-- equation. Equal ordinary theorems are not structure resources.
selectedStructurePredicateResourcesLowering
    :: VampirePremisePolicy
    -> ObjectId
    -> LoweringDriver (Either (VampireObligationPreparationError local)
        (Set SemanticFactOccurrenceFingerprint))
selectedStructurePredicateResourcesLowering selection predicate = do
    ProspectiveBuilder builder <- State.gets loweringBuilder
    let globalTyping = globalTypingFromClosure (logicalBuilderObjectClosure builder)
        environment = logicalBuilderStructures builder
    pure do
        selected <- selectVampireFacts globalTyping builder
            (vampireGlobalPremiseSelection selection)
        let selectedSet = Set.fromList (Backend.typedBackendFactReference <$> Vector.toList selected)
            providers = [(owner, fingerprint)
                | (owner, interface) <- Map.toAscList (StructureEnvironment.structureEnvironmentInterfaces environment)
                , StructurePredicate.pendingStructurePredicate
                    (StructureInterface.structureInterfaceRegistration interface) == predicate
                , Just fingerprint <- [Map.lookup Schema.PredicateDefinitionResource
                    (StructureInterface.structureInterfaceResourceIndex interface)]
                , fingerprint `Set.member` selectedSet]
        for_ providers \(owner, fingerprint) -> do
            (_, metadata) <- maybe (Left (VampireObligationFactInvalid fingerprint)) Right
                (checkedIndexedStructureFact environment (logicalBuilderFacts builder) planningEvidenceDirect
                    owner (Schema.StructureResourceFact Schema.PredicateDefinitionResource))
            unless (semanticFactFingerprint metadata == fingerprint)
                (Left (VampireObligationFactInvalid fingerprint))
        pure (Set.fromList (snd <$> providers))

data LocalClaim = LocalClaim
    !BuilderIdentity
    !DeclarationInvocation
    !FactSlot
    !CheckedPropositionContent

-- | Authenticate and admit one previously accepted fact, accumulate its
-- safety, and only then register it as a kernel import.  Backend and
-- structural consumers share the first two steps without registration.
useAuthorizedFact
    :: SemanticFactOccurrenceFingerprint
    -> CandidateProof ImportIx
useAuthorizedFact fingerprint = do
    proposition <- consumeAuthorizedFact fingerprint
    state <- State.get
    appendCandidatePremise (Just fingerprint) proposition state

-- | Consume a checked dependency for its authority effect without recording a
-- kernel import.  Structural compositions use facts at the composition node,
-- rather than inside a closed kernel construction.
consumeAuthorizedFactDependency
    :: SemanticFactOccurrenceFingerprint
    -> CandidateProof ()
consumeAuthorizedFactDependency fingerprint =
    void (consumeAuthorizedFact fingerprint)

-- | Consume exactly the cited facts and independently replay one scoped
-- source-level discharge against the complete active local context.  Imports
-- are numbered only within this proof object; they do not leak into the
-- candidate-wide import table used by closed kernel constructions.
data ScopedKernelUsage = ScopedKernelUsage
    !(Set ImportIx)
    !(Set HypothesisIx)
    !(Set FoundationAxiomTag)
    !(Set KernelRuleTag)
    deriving stock (Show, Eq)

scopedKernelImportUses :: ScopedKernelUsage -> Set ImportIx
scopedKernelImportUses (ScopedKernelUsage imports _hypotheses _foundation _rules) =
    imports

scopedKernelExternalHypothesisUses
    :: ScopedKernelUsage
    -> Set HypothesisIx
scopedKernelExternalHypothesisUses
        (ScopedKernelUsage _imports hypotheses _foundation _rules) =
    hypotheses

scopedKernelFoundationUses
    :: ScopedKernelUsage
    -> Set FoundationAxiomTag
scopedKernelFoundationUses
        (ScopedKernelUsage _imports _hypotheses foundation _rules) =
    foundation

scopedKernelRuleUses :: ScopedKernelUsage -> Set KernelRuleTag
scopedKernelRuleUses (ScopedKernelUsage _imports _hypotheses _foundation rules) =
    rules

scopedKernelUsesCanonicalDefinition
    :: [SemanticFactOccurrenceFingerprint] -> Set HypothesisIx
    -> ScopedKernelUsage -> CandidateProof Bool
scopedKernelUsesCanonicalDefinition fingerprints localDefinitions usage = do
    canonical <- State.gets (Set.fromList . Map.elems . logicalBuilderDefinitionViews . candidateProofBuilder)
    pure (any (`Set.member` canonical)
        [fingerprint | (index,fingerprint) <- zip [0..] fingerprints
            , importIx index `Set.member` scopedKernelImportUses usage]
        || not (Set.null (localDefinitions `Set.intersection` scopedKernelExternalHypothesisUses usage)))

data ScopedKernelMethodPolicy
    = KernelImplicitObvious
    | KernelCitedObvious
        !(Set SemanticFactOccurrenceFingerprint)
    | KernelAssumption
    | KernelStructuralComposition
    | KernelDefinition
        !(Set HypothesisIx)
    | KernelNotion
        !(Set HypothesisIx)
    | KernelSetExtensionality
        !(Set HypothesisIx)
    | KernelRecordExtensionality
        !(Set HypothesisIx)
    deriving stock (Show, Eq)

-- Only the declaration owner can classify an application as a definition step.
-- Reconstruct its exact target and joint guard from the admitted association;
-- the ordinary scoped replayer still owns its mathematical authority.
acceptScopedRecursiveEquation
    :: GlobalBindingRef -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> KernelDerivation ObjectId -> CandidateProof ()
acceptScopedRecursiveEquation owner call guardGoal target derivation = do
    state <- State.get
    let builder = candidateProofBuilder state
        environment = logicalBuilderEnvironment builder
        invalid :: Text -> CandidateProof value
        invalid = Error.throwError_ . BindingConstructionInvalid
        required :: Text -> Maybe value -> CandidateProof value
        required message = maybe (invalid message) pure
    binding <- required "a recursive equation owner is no longer visible"
        (Map.lookup owner (environmentBindings environment))
    let object = semanticGlobalTargetObject (semanticGlobalBindingTarget binding)
    definition <- required "a recursive equation association is unavailable"
        (Map.lookup object (environmentRecursiveDefinitions environment) >>= Map.lookup owner)
    context <- either (invalid . Text.pack . show) pure (KernelProof.scopedProofContext
        (logicalBuilderFoundation builder) (globalTypingFromClosure (candidateProofObjectClosure state))
        (scopedCoreContext call) [guardGoal])
    matched <- case fst (RecursionApplication.matchRecursiveApplication
            Preparation.defaultPreparationWork context definition call) of
        Left failure -> invalid (Text.pack (show failure))
        Right application -> required "an owned equation does not apply to this call" application
    unless (guardGoal == RecursionApplication.applicationGuard matched
        && target == RecursionApplication.applicationEquality matched)
        (invalid "a prepared recursive application changed its guard or equality")
    let fingerprint = fst (RecursionApplication.applicationEquation matched)
    usage <- acceptScopedKernelDischarge (KernelCitedObvious (Set.singleton fingerprint))
        [fingerprint] (Vector.singleton guardGoal) target derivation
    unless (importIx 0 `Set.member` scopedKernelImportUses usage)
        (Error.throwError_ KernelDefinitionEvidenceMissing)
    unless (Set.null (scopedKernelFoundationUses usage))
        (Error.throwError_ KernelDischargeFoundationUse)

acceptScopedKernelDischarge
    :: ScopedKernelMethodPolicy
    -> [SemanticFactOccurrenceFingerprint]
    -> Vector (ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId
    -> KernelDerivation ObjectId
    -> CandidateProof ScopedKernelUsage
acceptScopedKernelDischarge
        policy fingerprints hypotheses target derivation = do
    propositions <- traverse consumeAuthorizedFact fingerprints
    imports <- liftEitherEffect
        (Vector.fromList
            <$> traverse
                (first DerivationImportFailed
                    . derivationImportJudgement
                    . checkedPropositionTerm)
                propositions)
    state <- State.get
    let builder = candidateProofBuilder state
        closure = candidateProofObjectClosure state
        run :: (CheckedFoundation -> KernelReplayLimits -> GlobalTyping ObjectId
            -> Vector (DerivationImportJudgement ObjectId) -> Vector (ScopedCheckedCore ObjectId)
            -> ScopedCheckedCore ObjectId -> KernelDerivation ObjectId -> value) -> value
        run replay = replay (logicalBuilderFoundation builder) defaultKernelReplayLimits
            (globalTypingFromClosure closure) imports hypotheses target derivation
    result <- liftIO (measureFormationReplay (declarationFormationRecorder (candidateProofDeclaration state))
        (run replayScopedKernelDerivation) (run replayScopedKernelDerivationMeasured))
    replayed <- liftEitherEffect (first KernelCompletionFailed result)
    let expectedImports =
            Set.fromList
                [ importIx (fromIntegral index)
                | index <- [0 .. length fingerprints - 1]
                ]
        actualImports = replayedScopedKernelImportUses replayed
    unless
        (actualImports == expectedImports)
        (Error.throwError_
            (KernelDischargeImportMismatch
                expectedImports actualImports))
    let usage =
            ScopedKernelUsage
                actualImports
                (replayedScopedKernelExternalHypothesisUses replayed)
                (replayedScopedKernelFoundationUses replayed)
                (replayedScopedKernelRuleUses replayed)
    enforceScopedKernelMethodPolicy policy fingerprints usage
    pure usage

-- | Enforce source-method authority from independently replayed leaves.  The
-- prepared method and its complete reference selection are inputs; canonical
-- status is resolved afresh from the admitted builder rather than trusted from
-- search metadata.
enforceScopedKernelMethodPolicy
    :: ScopedKernelMethodPolicy
    -> [SemanticFactOccurrenceFingerprint]
    -> ScopedKernelUsage
    -> CandidateProof ()
enforceScopedKernelMethodPolicy policy fingerprints usage = do
    state <- State.get
    let builder = candidateProofBuilder state
        canonicalFingerprints =
            Set.fromList
                (Map.elems (logicalBuilderDefinitionViews builder))
        pointwiseFingerprints =
            Set.fromList
                [ fingerprint
                | ((_object, kind), fingerprint) <-
                    Map.toList (logicalBuilderDefinitionViews builder)
                , kind == DefinitionPointwiseView
                ]
        usedFingerprintSet = Set.fromList fingerprints
        onlyCanonicalImports =
            usedFingerprintSet `Set.isSubsetOf` canonicalFingerprints
        noImports = Set.null (scopedKernelImportUses usage)
        noFoundation = Set.null (scopedKernelFoundationUses usage)
        obviousFoundation =
            scopedKernelFoundationUses usage
                `Set.isSubsetOf` Set.fromList [DoubleNegationElim, PropositionalExtensionality]
        noGuardedRules = Set.null (scopedKernelRuleUses usage)
        usedHypotheses = scopedKernelExternalHypothesisUses usage
        reject condition failure =
            unless condition (Error.throwError_ failure)
    reject noGuardedRules KernelDischargeGuardedRuleUse
    case policy of
        KernelImplicitObvious -> do
            reject obviousFoundation KernelDischargeFoundationUse
            reject onlyCanonicalImports KernelObviousImportPolicyMismatch
        KernelCitedObvious selected -> do
            reject obviousFoundation KernelDischargeFoundationUse
            views <- case NonEmpty.nonEmpty (Set.toAscList selected) of
                Nothing -> pure Set.empty
                Just cited -> do
                    resolved <- either (Error.throwError_ . StructureDeclarationInvalid) pure
                        (resolveCitedStructureViews builderEvidenceDirect builder cited)
                    pure (Set.fromList (fst <$> citedStructureViewFacts resolved))
            reject
                ( usedFingerprintSet
                    `Set.isSubsetOf`
                        (selected <> canonicalFingerprints <> views)
                )
                KernelObviousImportPolicyMismatch
        KernelStructuralComposition -> do
            reject noFoundation KernelDischargeFoundationUse
            reject (case fingerprints of
                [] -> True
                [fingerprint] -> Calculation.compositionRegistryMember fingerprint (logicalBuilderCompositions builder)
                _ -> False)
                KernelCompositionImportPolicyMismatch
        KernelAssumption -> do
            reject noFoundation KernelDischargeFoundationUse
            reject noImports KernelAssumptionImportUse
            reject
                (not (Set.null usedHypotheses))
                KernelAssumptionEvidenceMissing
        KernelDefinition canonicalHypotheses -> do
            reject obviousFoundation KernelDischargeFoundationUse
            reject onlyCanonicalImports KernelObviousImportPolicyMismatch
            reject
                ( not (Set.null usedFingerprintSet)
                  || not
                        (Set.null
                            (usedHypotheses `Set.intersection` canonicalHypotheses))
                )
                KernelDefinitionEvidenceMissing
        KernelNotion selectedHypotheses -> do
            reject (scopedKernelFoundationUses usage `Set.isSubsetOf` Set.singleton PropositionalExtensionality)
                KernelDischargeFoundationUse
            reject
                (usedHypotheses == selectedHypotheses)
                KernelNotionEvidenceMismatch
        KernelSetExtensionality selectedHypotheses -> do
            reject
                (usedFingerprintSet `Set.isSubsetOf` pointwiseFingerprints)
                KernelExtensionalityImportMismatch
            reject
                ( scopedKernelFoundationUses usage
                    == Set.singleton SetExtensionality
                )
                KernelDischargeFoundationUse
            reject
                (usedHypotheses == selectedHypotheses)
                KernelExtensionalityEvidenceMismatch
        KernelRecordExtensionality selectedHypotheses -> do
            reject noFoundation KernelDischargeFoundationUse
            reject
                (length fingerprints == 1)
                KernelExtensionalityImportMismatch
            reject
                (usedHypotheses == selectedHypotheses)
                KernelExtensionalityEvidenceMismatch
            reject
                (authoritativeStructureProjectionConstruction builder fingerprints)
                KernelExtensionalityAuthorityMismatch

authoritativeStructureProjectionConstruction
    :: LogicalBuilder -> [SemanticFactOccurrenceFingerprint] -> Bool
authoritativeStructureProjectionConstruction builder = \case
    [fingerprint] -> case checkedProjectionExtensionality builder fingerprint of
        Just (CheckedProjectionExtensionality _ metadata) -> semanticFactFingerprint metadata == fingerprint
        Nothing -> False
    _ -> False

checkedProjectionExtensionality
    :: LogicalBuilder -> SemanticFactOccurrenceFingerprint -> Maybe CheckedProjectionExtensionality
checkedProjectionExtensionality builder fingerprint = do
    FactEntry _ occurrence _ <- Map.lookup fingerprint (logicalBuilderFacts builder)
    StructureFactPurpose (Schema.StructureLawId owner key@(Schema.RecordSchemaLaw Record.RecordProjectionExtensionalityLaw))
        <- pure (semanticFactPurpose occurrence)
    (proposition, metadata) <- checkedIndexedStructureFact (logicalBuilderStructures builder)
        (logicalBuilderFacts builder) builderEvidenceDirect owner (Schema.StructureLawFact key)
    guard (semanticFactFingerprint metadata == fingerprint)
    pure (CheckedProjectionExtensionality proposition metadata)

checkedNotionViewTheorem
    :: LogicalBuilder -> SemanticFactOccurrenceFingerprint -> Maybe CheckedNotionViewTheorem
checkedNotionViewTheorem builder fingerprint = do
    FactEntry _ occurrence _ <- Map.lookup fingerprint (logicalBuilderFacts builder)
    StructureFactPurpose (Schema.StructureLawId owner key@Schema.ParentInheritanceLaw{})
        <- pure (semanticFactPurpose occurrence)
    (proposition, metadata) <- checkedIndexedStructureFact (logicalBuilderStructures builder)
        (logicalBuilderFacts builder) builderEvidenceDirect owner (Schema.StructureLawFact key)
    guard (semanticFactFingerprint metadata == fingerprint)
    pure (CheckedNotionViewTheorem proposition metadata)

-- | Validate one fact capability and accumulate only its safety effect.
-- Backend use does not register a kernel import.
consumeAuthorizedFact
    :: SemanticFactOccurrenceFingerprint
    -> CandidateProof CheckedPropositionContent
consumeAuthorizedFact fingerprint = do
    state <- State.get
    let builder = candidateProofBuilder state
        declaration = candidateProofDeclaration state
        staged =
            findPendingByFingerprint
                fingerprint
                (declarationPending declaration)
    case staged of
        Just pending ->
            consumePendingFact pending state
        Nothing ->
            case Map.lookup
                    fingerprint
                    (logicalBuilderFacts builder) of
                Nothing ->
                    Error.throwError_
                        (AuthorizedFactNotVisible fingerprint)
                Just authorized ->
                    consumeBuilderAuthorizedFact authorized state

-- | Materialize one sealed direct import and its transitive parents.  The
-- interface DAG is folded imported-before-importer and each producer
-- occurrence receives a fresh capability for this consuming builder.
insertResolvedEnvironmentGlobal
    :: ResolvedEnvironment evidence
    -> ResolvedGlobalBinding
    -> Either DeclarationError (ResolvedEnvironment evidence)
insertResolvedEnvironmentGlobal environment resolved = do
    let binding = resolvedBindingDeclaration resolved
        key = semanticGlobalBindingKey binding
    case Map.lookup key (environmentGlobals environment) of
        Just existing
            | existing == resolved -> pure environment
            | otherwise -> Left (ImportedGlobalCollision key existing resolved)
        Nothing -> pure environment
            { environmentGlobals = Map.insert key resolved
                (environmentGlobals environment)
            , environmentBindings = Map.insert (resolvedBindingRef resolved) binding
                (environmentBindings environment)
            }

checkRecursiveBindings
    :: CheckedObjectClosure -> ResolvedEnvironment evidence -> DeclarationSlot
    -> [SemanticGlobalBinding] -> [(SemanticFactOccurrence, CheckedPropositionContent)]
    -> Either DeclarationError [RecursionInterface.CheckedRecursiveDefinition]
checkRecursiveBindings closure environment owner bindings facts =
    for [(binding,descriptor) | binding <- bindings,
        Just descriptor <- [semanticGlobalBindingRecursion binding]] $ \(binding,descriptor) ->
        do
            definition <- first BindingConstructionInvalid (RecursionInterface.checkRecursiveDefinition closure
                (`Map.lookup` environmentBindings environment) (`Map.lookup` targets)
                (globalBindingRef owner (semanticGlobalBindingKey binding)) binding descriptor)
            first (BindingConstructionInvalid . Calculation.renderCalculationError)
                (fst (runIdentity (Calculation.runCalculationWork Calculation.defaultCompositionAdmissionWork do
                    for_ (toList (RecursionInterface.recursiveSources definition) <> toList (RecursionInterface.recursiveGuardSources definition)) \(context,body,description) -> do
                        actual <- validateSourceTemplate closure environment BindingConstructionInvalid context
                            (Vector.fromList (fromIntegral <$> reverse [0 .. length context - 1])) body description
                        same <- Calculation.calculationCoreWork (\work -> countedCanonicalIdentity work actual body)
                        unless same (Except.throwError (Calculation.CalculationInvalid
                            "recursive source metadata disagrees with its checked body")))))
            pure definition
  where
    targets = Map.fromList [(semanticFactFingerprint occurrence, checkedPropositionTerm proposition)
        | (occurrence,proposition) <- facts]

installRecursiveDefinitions
    :: [RecursionInterface.CheckedRecursiveDefinition] -> ResolvedEnvironment evidence
    -> ResolvedEnvironment evidence
installRecursiveDefinitions definitions environment = environment
    { environmentRecursiveDefinitions = foldl' insert (environmentRecursiveDefinitions environment) definitions }
  where
    insert registry definition = Map.insertWith Map.union (RecursionInterface.recursiveObject definition)
        (Map.singleton (RecursionInterface.recursiveBinding definition) definition) registry

insertResolvedEnvironmentStructures
    :: ResolvedEnvironment evidence -> [StructureInterface.CheckedStructureInterface evidence]
    -> Either DeclarationError (ResolvedEnvironment evidence)
insertResolvedEnvironmentStructures environment = \case
    [] -> pure environment
    firstInterface : rest ->
        let origin = Schema.resolvedSchemaOrigin (StructurePredicate.pendingStructureSchema
                (StructureInterface.structureInterfaceRegistration firstInterface))
        in insertResolvedStructureInterfaces
            (declarationSlot (structureOriginModule origin) (structureOriginDeclaration origin))
            environment (firstInterface :| rest)

insertResolvedStructureInterfaces
    :: DeclarationSlot -> ResolvedEnvironment evidence
    -> NonEmpty (StructureInterface.CheckedStructureInterface evidence)
    -> Either DeclarationError (ResolvedEnvironment evidence)
insertResolvedStructureInterfaces slot environment interfaces = do
    let schemas = StructurePredicate.pendingStructureSchema . StructureInterface.structureInterfaceRegistration <$> interfaces
        hasRoot = any ((== Schema.GeneralRecordRoot) . Schema.resolvedSchemaRole) schemas
        prior = environmentStructures environment
    traverse_ (\schema -> unless
        (structureOriginModule (Schema.resolvedSchemaOrigin schema) == declarationSlotModule slot
            && structureOriginDeclaration (Schema.resolvedSchemaOrigin schema) == declarationSlotOrdinal slot)
        (Left (StructureDeclarationInvalid "a structure interface belongs to a different declaration"))) schemas
    structures <- first StructureEnvironmentInvalid $
        if hasRoot then do
            unless (declarationSlotModule slot == preludeModuleName)
                (Left (StructureEnvironment.StructureEnvironmentManifestInvalid "the manifest belongs to the reserved prelude"))
            sealed <- StructureEnvironment.installBuiltinStructureInterfaces
                (StructureBuiltin.builtinStructureManifest (declarationSlotOrdinal slot)) interfaces
            StructureEnvironment.mergeStructureEnvironments prior sealed
        else do
            unless (length schemas == 1 && all ((== structureSlot 0) . structureOriginSlot . Schema.resolvedSchemaOrigin) schemas)
                (Left (StructureEnvironment.StructureEnvironmentManifestInvalid "an ordinary structure declaration owns only slot zero"))
            StructureEnvironment.extendStructureEnvironment interfaces prior
    let fields = concatMap (Map.elems . Schema.resolvedSchemaFields) (toList schemas)
    pure environment
        { environmentStructures = structures
        , environmentFields = foldl' (\entries field -> Map.insert
            (Schema.resolvedFieldIdentity field) (Schema.resolvedFieldProjection field) entries)
            (environmentFields environment) fields
        , environmentOperations = foldl' (\entries field -> Set.insert
            (Schema.resolvedFieldSymbol field, Schema.resolvedFieldProjection field) entries)
            (environmentOperations environment) fields
        }

materializeImportedEnvironmentDelta
    :: CheckedFoundation -> CheckedObjectClosure
    -> Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate)
    -> Map (DeclarationSlot, StructureSlot) Schema.StructurePresentation
    -> ResolvedEnvironment ValidationCertificate -> DeclarationInterfaceDelta
    -> Except.ExceptT DeclarationError (PureState.State ImportWork) (ResolvedEnvironment ValidationCertificate)
materializeImportedEnvironmentDelta foundation closure facts presentations prior delta = do
    let environment = declarationDeltaEnvironment delta
        owner = declarationDeltaSlot delta
        bindings = semanticEnvironmentBindings environment
        localLaws = [(occurrence, proposition)
            | occurrence <- declarationDeltaFacts delta
            , Just (FactEntry proposition _ _) <- [Map.lookup (semanticFactFingerprint occurrence) facts]]
    Except.liftEither $ first DatatypeInterfaceInvalid (DatatypeInterface.checkDatatypeBindings closure bindings localLaws)
    withStructures <- checkCachedStructureEffect foundation closure facts presentations prior delta
    traverse_ (\binding -> admissionCheck emptyImportWork{importGlobalTargetChecks = 1} $ first
        (ImportedGlobalTargetInvalid (semanticGlobalBindingKey binding) (semanticGlobalBindingTarget binding))
        (validateSemanticGlobalBindingTarget (environmentOperations withStructures) closure binding)) bindings
    let (materialized, used) = materializeSemanticEnvironmentDeltaMeasured
            (`Map.lookup` environmentBindings withStructures)
            (lookupEnvironmentRegistration (environmentStructures withStructures))
            (`Map.lookup` environmentFields withStructures)
            (visibleRecordShapeKeys (environmentStructures withStructures)) closure owner environment
    PureState.modify' (\work -> work{importFormationPreparationWork = importFormationPreparationWork work + used})
    resolved <- admissionCheck emptyImportWork{importEnvironmentMaterializations = 1} $ first
        (\(SemanticEnvironmentBindingMaterializationFailed reference failure) -> GlobalFormationContractInvalid reference failure)
        materialized
    definitions <- Except.liftEither (checkRecursiveBindings closure prior owner bindings localLaws)
    withGlobals <- Except.liftEither (foldM insertResolvedEnvironmentGlobal withStructures resolved)
    pure (installRecursiveDefinitions definitions withGlobals)

checkCachedStructureEffect
    :: CheckedFoundation -> CheckedObjectClosure
    -> Map SemanticFactOccurrenceFingerprint (FactEntry ValidationCertificate)
    -> Map (DeclarationSlot, StructureSlot) Schema.StructurePresentation
    -> ResolvedEnvironment ValidationCertificate -> DeclarationInterfaceDelta
    -> Except.ExceptT DeclarationError (PureState.State ImportWork) (ResolvedEnvironment ValidationCertificate)
checkCachedStructureEffect foundation closure facts presentations prior delta = case wires of
    [] -> do
        Except.liftEither $ unless (all ((== GeneralFactPurpose) . semanticFactPurpose) (declarationDeltaFacts delta))
            (invalid "a cached structural law has no local interface")
        pure prior
    firstWire : rest -> do
        raw <- Except.liftEither $ traverse (first StructureDeclarationInvalid . structureWireLocalInput) (firstWire :| rest)
        let manifest = declarationSlotModule owner == preludeModuleName
                && any (\input -> Schema.localWireSlot input == structureSlot 0 && null (Schema.localWireParents input)) raw
        inputs <- traverse (admissionCheck emptyImportWork{importStructureInputChecks = 1} . checkInput manifest) raw
        schemas <- Except.liftEither $ first (StructureDeclarationInvalid . Text.pack . show)
            (Schema.resolveStructureBatch (fmap StructurePredicate.pendingStructureSchema . lookupEnvironmentRegistration incoming) inputs)
        registrations <- traverse (admissionCheck emptyImportWork{importStructurePredicateChecks = 1} . checkRegistration) schemas
        supplied <- Except.liftEither $ Map.fromList . toList <$> traverse resolveWire (firstWire :| rest)
        (interfaces, dependencies) <- admissionCheck emptyImportWork{importStructureChecks = length wires} $ first StructureInterfaceInvalid
            (StructureInterface.checkStructureInterfacesWithDependencies foundation closure
                (Just . validationDirectAuthorization)
                (\identity -> StructureEnvironment.lookupStructureById identity incoming) inputs registrations supplied)
        let lawFingerprints = Set.fromList (concatMap (Map.elems . structureWireLawIndex) wires)
        Except.liftEither $ unless (lawFingerprints == Set.fromList [semanticFactFingerprint occurrence | occurrence <- declarationDeltaFacts delta
                , StructureFactPurpose{} <- [semanticFactPurpose occurrence]])
            (invalid "cached structural purposes and local interface laws disagree")
        Except.liftEither $ traverse_ (checkResourceProviders supplied) interfaces
        Except.liftEither $ for_ (Map.toAscList dependencies) \(Schema.StructureLawId identity law, needs) -> do
            consumer <- requireFact supplied identity (Schema.StructureLawFact law)
            for_ needs \dependency -> do
                premise <- case dependency of
                    StructureLaws.BatchDependency provider key -> requireFact supplied provider key
                    StructureLaws.EnvironmentDependency provider key -> requireIncoming provider key
                let fingerprint = occurrenceFingerprint premise
                when (Set.member fingerprint ownFacts) $ unless
                    (factSlotOrdinal (semanticFactSlot (StructureInterface.structureOccurrenceMetadata premise))
                        < factSlotOrdinal (semanticFactSlot (StructureInterface.structureOccurrenceMetadata consumer)))
                    (invalid "a cached law depends on a later or identical local occurrence")
        Except.liftEither $ validateGeneratedStructureViews incoming interfaces (declarationDeltaRegistrations delta)
        Except.liftEither $ validateGeneratedStructureAliases interfaces (declarationDeltaAliases delta)
        Except.liftEither $ insertResolvedStructureInterfaces owner prior interfaces
  where
    owner = declarationDeltaSlot delta
    wires = semanticEnvironmentStructures (declarationDeltaEnvironment delta)
    wireIndex = Map.fromList [(structureWireSlot wire, wire) | wire <- wires]
    incoming = environmentStructures prior
    ownFacts = Set.fromList (semanticFactFingerprint <$> declarationDeltaFacts delta)
    invalid = Left . StructureDeclarationInvalid
    checkInput manifest input = do
        presentation <- maybe (invalid "a cached structure has no reconstructed presentation") Right
            (Map.lookup (owner, Schema.localWireSlot input) presentations)
        let origin = StructureOrigin (declarationSlotModule owner) (declarationSlotOrdinal owner) (Schema.localWireSlot input)
        first (StructureDeclarationInvalid . Text.pack . show) $
            if manifest then Schema.checkManifestLocalStructureSchema closure origin
                (if Schema.localWireSlot input == structureSlot 0 then Schema.GeneralRecordRoot else Schema.OrdinaryStructure) input presentation
            else Schema.checkLocalStructureSchema closure origin input presentation
    checkRegistration schema = do
        wire <- maybe (invalid "a resolved cached schema has no local wire") Right
            (Map.lookup (structureOriginSlot (Schema.resolvedSchemaOrigin schema)) wireIndex)
        unless (structureWirePresentationMatches wire schema) (invalid "cached structure presentation differs from canonical resolution")
        first (StructureDeclarationInvalid . Text.pack . show)
            (StructurePredicate.checkPendingStructureRegistration closure schema (structureWirePredicate wire))
    resolveWire wire = do
        let identity = structureId (StructureOrigin (declarationSlotModule owner) (declarationSlotOrdinal owner) (structureWireSlot wire))
            references = Map.union (Map.mapKeys Schema.StructureLawFact (structureWireLawIndex wire))
                (Map.mapKeys Schema.StructureResourceFact (structureWireResourceIndex wire))
        rows <- Map.traverseWithKey (\key fingerprint -> do
            case key of
                Schema.StructureLawFact _ -> unless (Set.member fingerprint ownFacts)
                    (invalid "a cached local law is not owned by this declaration")
                Schema.StructureResourceFact _ -> pure ()
            case Map.lookup fingerprint facts of
                Just (FactEntry proposition metadata evidence) -> pure (StructureInterface.StructureOccurrence proposition metadata evidence)
                Nothing -> invalid "a cached interface references an occurrence outside its declaration prefix") references
        pure (identity, rows)
    requireFact supplied identity key = maybe (invalid "a cached dependency has no exact local association") Right
        (Map.lookup identity supplied >>= Map.lookup key)
    requireIncoming identity key = maybe (invalid "a cached dependency has no exact incoming association") Right
        (StructureEnvironment.lookupStructureById identity incoming >>= StructureInterface.lookupStructureOccurrence key)
    checkResourceProviders supplied interface = do
        let schema = StructurePredicate.pendingStructureSchema (StructureInterface.structureInterfaceRegistration interface)
            identity = Schema.resolvedSchemaId schema
        definition <- requireFact supplied identity (Schema.StructureResourceFact Schema.PredicateDefinitionResource)
        unless (Set.member (occurrenceFingerprint definition) ownFacts) $
            case canonicalPredicateResource incoming
                    (StructurePredicate.pendingStructurePredicate (StructureInterface.structureInterfaceRegistration interface)) of
                Just expected | occurrenceFingerprint expected == occurrenceFingerprint definition -> pure ()
                _ -> invalid "a cached reused predicate definition names a different indexed provider"
        for_ (Map.elems (Schema.resolvedSchemaFields schema)) \field ->
            when (Schema.resolvedFieldOwner field /= identity) $
                for_ [Schema.SelectorDefinitionResource (Schema.resolvedFieldIdentity field),
                    Schema.ProjectionMembershipResource (Schema.resolvedFieldIdentity field)] \resource -> do
                    let provider = Schema.resolvedFieldOwner field
                        key = Schema.StructureResourceFact resource
                    expected <- if Map.member provider supplied then requireFact supplied provider key else requireIncoming provider key
                    actual <- requireFact supplied identity key
                    unless (occurrenceFingerprint expected == occurrenceFingerprint actual)
                        (invalid "a cached inherited resource uses a different provider occurrence")

useStagedCandidate
    :: ReservedCandidate
    -> CandidateProof ImportIx
useStagedCandidate premise = do
    state <- State.get
    let current = candidateProofCandidate state
        declaration = candidateProofDeclaration state
    liftEitherEffect
        (validateReservedCandidate declaration premise)
    liftEitherEffect
        (validateStrictCandidateStage premise current)
    pending <-
        maybe
            (Error.throwError_
                (StagedPremiseNotAuthorized
                    (reservedCandidateSlot premise)))
            pure
            (Map.lookup
                (reservedCandidateSlot premise)
                (declarationPending declaration))
    let proposedAuthority =
            validationTarget (pendingCandidateCertificate pending)
    checkedStage <- liftEitherEffect
        (prepareCheckedDeclarationStage
            declaration
            (candidateProofObjectClosure state)
            [(premise, proposedAuthority)])
    stagedProposition <- liftEitherEffect
        (useCheckedStageFact checkedStage current premise)
    proposition <- consumePendingFact pending state
    unless
        (checkedPropositionId stagedProposition
            == checkedPropositionId proposition)
        (Error.throwError_
            (PlanningFactContractMismatch
                (reservedCandidateSlot premise)))
    updated <- State.get
    appendCandidatePremise (Just (semanticFactFingerprint (candidateOccurrence premise proposedAuthority))) proposition updated

validateStrictCandidateStage
    :: ReservedCandidate
    -> ReservedCandidate
    -> Either DeclarationError ()
validateStrictCandidateStage premise current =
    unless
        (reservedStage premise < reservedStage current)
        (Left
            (StagedPremiseNotEarlier
                (reservedCandidateSlot premise)
                (reservedCandidateStage premise)
                (reservedCandidateSlot current)
                (reservedCandidateStage current)))

prepareCheckedDeclarationStage
    :: DeclarationState
    -> CheckedObjectClosure
    -> [(ReservedCandidate, FactAuthority)]
    -> Either DeclarationError CheckedDeclarationStage
prepareCheckedDeclarationStage declaration closure candidates = do
    entries <- foldM insertCandidate Map.empty candidates
    pure (CheckedDeclarationStage ownSlot closure entries)
  where
    builder = declarationBuilder declaration
    ownSlot = declarationOwnSlot declaration

    insertCandidate entries (candidate, authority) = do
        validateReservedCandidate declaration candidate
        let slot = reservedCandidateSlot candidate
        unless
            (factAuthorityTheorem authority
                == candidateTheoremReference builder candidate)
            (Left (PlanningFactContractMismatch slot))
        when
            (Map.member slot entries)
            (Left (PlanningFactContractMismatch slot))
        let occurrence = candidateOccurrence candidate authority
            evidence = PlanningEvidence
                authority
                Nothing
                (Just
                    (PlanningProvenance
                        ownSlot
                        (reservedStage candidate)
                        slot))
        pure
            (Map.insert
                slot
                (FactEntry
                    (candidateCheckedProposition candidate)
                    occurrence
                    evidence)
                entries)

useCheckedStageFact
    :: CheckedDeclarationStage
    -> ReservedCandidate
    -> ReservedCandidate
    -> Either DeclarationError CheckedPropositionContent
useCheckedStageFact
        (CheckedDeclarationStage ownSlot closure entries)
        current
        premise = do
    validateStrictCandidateStage premise current
    let slot = reservedCandidateSlot premise
    FactEntry proposition occurrence
        (PlanningEvidence authority _direct provenance) <-
            maybe
                (Left (PlanningFactContractMismatch slot))
                Right
                (Map.lookup slot entries)
    unless
        ( provenance
            == Just
                (PlanningProvenance
                    ownSlot
                    (reservedStage premise)
                    slot)
          && semanticFactSlot occurrence == slot
          && semanticFactAuthority occurrence == authority
          && checkedPropositionId proposition
                == checkedPropositionId
                    (candidateCheckedProposition premise)
          && propositionMatchesClosure closure proposition
        )
        (Left (PlanningFactContractMismatch slot))
    pure proposition

propositionMatchesClosure
    :: CheckedObjectClosure
    -> CheckedPropositionContent
    -> Bool
propositionMatchesClosure closure proposition =
    case validateAssertedPropositionContent
            closure
            (checkedPropositionId proposition)
            (frozenCoreTerm (checkedPropositionTerm proposition)) of
        Right _ -> True
        Left _ -> False

candidateOccurrence
    :: ReservedCandidate
    -> FactAuthority
    -> SemanticFactOccurrence
candidateOccurrence
        (ReservedCandidate _ _ _ _ slot
            spec)
        authority =
    candidateSpecOccurrence slot authority spec

candidateAliases :: ReservedCandidate -> [SemanticName]
candidateAliases
        (ReservedCandidate _ _ _ _ _
            (CandidateSpec _ _ _ aliases _composition)) =
    aliases

-- | Establish a candidate-local claim by owner-bound replay.  Unlike accepted
-- fact use, this creates no public fact authority and accumulates no safety:
-- the stamped claim can be consumed only by the same builder invocation and
-- candidate slot.
proveLocalKernelClaim
    :: CheckedPropositionContent
    -> KernelDerivation ObjectId
    -> CandidateProof LocalClaim
proveLocalKernelClaim proposition derivation = do
    state <- State.get
    void (replayOwnedCandidateKernel proposition derivation state)
    let candidate = candidateProofCandidate state
        declaration = candidateProofDeclaration state
    pure
        (LocalClaim
            (logicalBuilderIdentity
                (candidateProofBuilder state))
            (declarationInvocation declaration)
            (reservedCandidateSlot candidate)
            proposition)

-- | Register a replayed local claim after authenticating its candidate-local
-- stamp.  No safety is accumulated because no external or previously accepted
-- fact capability is consumed.
useLocalClaim :: LocalClaim -> CandidateProof ImportIx
useLocalClaim
        (LocalClaim identity invocation slot proposition) =
    do
        state <- State.get
        let builder = candidateProofBuilder state
            declaration = candidateProofDeclaration state
            candidate = candidateProofCandidate state
        unless
            ( identity == logicalBuilderIdentity builder
              && invocation == declarationInvocation declaration
              && slot == reservedCandidateSlot candidate
            )
            (Error.throwError_ LocalClaimOutsideCandidate)
        appendCandidatePremise Nothing proposition state


authorizeKernelProofCandidate
    :: ReservedCandidate
    -> CandidateProof (KernelDerivation ObjectId)
    -> Declaration ()
authorizeKernelProofCandidate candidate proof =
    authorizeOneCandidate candidate \initial -> do
        (derivation, final) <-
            State.runState initial proof
        when
            (isNothing (candidateProofCachedValidation final))
            (void (replayOwnedCandidateKernel
                (candidateCheckedProposition candidate) derivation final))
        completeCandidateWithValidation
                candidate
                (CheckedSourceProof
                    (acceptedExternalProofUse final))
                (candidateProofSafety final)
                final

-- | Complete a source proof whose opaque owner authorization carries the
-- structurally checked discharge recipe and plans no external prover request.
-- This is separate from 'authorizeVampireCandidate': neither an arbitrary
-- candidate action nor an accidentally empty ATP proof may acquire authority.
authorizeStructuralSourceProofCandidate
    :: ReservedCandidate
    -> StructuralProofAuthorization (CandidateProof ())
    -> Declaration ()
authorizeStructuralSourceProofCandidate candidate proof =
    authorizeOneCandidate candidate \initial -> do
        ((), final) <- State.runState initial (structuralProofAction proof)
        unless (null (acceptedRequestIds final))
            (Error.throwError_ VampireRequestMismatch)
        completeCandidateWithValidation
            candidate
            (CheckedSourceProof NoExternalProofUse)
            (candidateProofSafety final)
            final

authorizeKernelConstructionCandidate
    :: KernelConstructionDescriptor
    -> ReservedCandidate
    -> CandidateProof (KernelDerivation ObjectId)
    -> Declaration ()
authorizeKernelConstructionCandidate descriptor candidate proof =
    authorizeOneCandidate candidate \initial -> do
        (derivation, final) <-
            State.runState initial proof
        when
            (isNothing (candidateProofCachedValidation final)) do
                replayed <- replayOwnedCandidateKernel
                    (candidateCheckedProposition candidate) derivation final
                liftEitherEffect
                    (validateKernelConstruction
                        descriptor
                        (candidateCheckedProposition candidate)
                        replayed
                        final)
        completeCandidateWithValidation
                candidate
                (CheckedKernelConstruction descriptor)
                (candidateProofSafety final)
                final

authorizeDefinitionEquationCandidate
    :: ObjectId
    -> ReservedCandidate
    -> Declaration ()
authorizeDefinitionEquationCandidate identity candidate =
    authorizeDefinitionEquationWith CheckedDefinitionEquation identity candidate

authorizeImplementationDefinitionCandidate
    :: ObjectId -> ReservedCandidate -> Declaration ()
authorizeImplementationDefinitionCandidate =
    authorizeDefinitionEquationWith CheckedImplementationDefinition

authorizeDefinitionEquationWith
    :: (ObjectId -> KernelConstructionDescriptor)
    -> ObjectId -> ReservedCandidate -> Declaration ()
authorizeDefinitionEquationWith descriptor identity candidate =
    authorizeOneCandidate candidate \initial -> do
        when
            (isNothing (candidateProofCachedValidation initial))
            (unless
                (matchesDefinitionEquation
                    identity
                    (candidateCheckedProposition candidate)
                    initial)
                (Error.throwError_
                    DefinitionEquationCandidateMismatch))
        completeCandidateWithValidation
            candidate
            (CheckedKernelConstruction
                (descriptor identity))
            (candidateProofSafety initial)
            initial

-- | Authorize only the extensional fact deterministically derived from the
-- checked source construction and its committed transparent object.
authorizeNamedSetConstructionCandidate
    :: ObjectId
    -> NamedSetConstruction ObjectId
    -> ReservedCandidate
    -> Declaration ()
authorizeNamedSetConstructionCandidate identity construction candidate =
    authorizeOneCandidate candidate \initial -> do
        let builder = candidateProofBuilder initial
        (expected, descriptor) <-
            liftEitherEffect
                (prepareNamedSetConstruction
                    (logicalBuilderFoundation builder)
                    (candidateProofObjectClosure initial)
                    identity
                    construction)
        unless
            (frozenCoreTerm expected
                    == frozenCoreTerm
                        (checkedPropositionTerm
                            (candidateCheckedProposition candidate))
            )
            (Error.throwError_
                KernelConstructionDescriptorMismatch)
        completeCandidateWithValidation
            candidate
            (CheckedKernelConstruction descriptor)
            (candidateProofSafety initial)
            initial

-- | Authorize the relational extensional view only after consuming the exact
-- strictly-earlier functionality candidate.  The consumed candidate supplies
-- both real authority safety and the proposition rechecked by the confined
-- construction schema; a caller cannot substitute an arbitrary theorem.
authorizeRelationalSetConstructionCandidate
    :: ObjectId
    -> CheckedRelationalSetConstruction ObjectId
    -> ReservedCandidate
    -> ReservedCandidate
    -> Declaration ()
authorizeRelationalSetConstructionCandidate
        identity construction functionality candidate =
    authorizeOneCandidate candidate \initial -> do
        (_used, final) <-
            State.runState initial
                (useStagedCandidate functionality)
        let builder = candidateProofBuilder final
            functionalityTerm =
                checkedPropositionTerm
                    (candidateCheckedProposition functionality)
        (expected, descriptor) <-
            liftEitherEffect
                (prepareRelationalSetConstruction
                    (logicalBuilderFoundation builder)
                    (candidateProofObjectClosure final)
                    identity
                    construction
                    functionalityTerm)
        unless
            (frozenCoreTerm expected
                == frozenCoreTerm
                    (checkedPropositionTerm
                        (candidateCheckedProposition candidate)))
            (Error.throwError_
                KernelConstructionDescriptorMismatch)
        completeCandidateWithValidation
            candidate
            (CheckedKernelConstruction descriptor)
            (candidateProofSafety final)
            final

authorizeSourceAxiomCandidate
    :: ReservedCandidate
    -> Declaration ()
authorizeSourceAxiomCandidate candidate =
    authorizeOneCandidate candidate \initial ->
        let safety =
                addCandidateEscape
                    SourceAxiom
                    initialCandidateSafety
        in completeCandidateWithValidation
                candidate
                SourceAxiomAuthorization
                safety
                initial

authorizeOmittedCandidate
    :: ReservedCandidate
    -> CandidateProof ()
    -> Declaration ()
authorizeOmittedCandidate candidate proof =
    authorizeOneCandidate candidate \initial -> do
        ((), final) <- State.runState initial proof
        let safety = candidateProofSafety final
        unless
            (Omitted
                `elem` escapeKindsToList
                    (authoritySafetyEscapeKinds
                        (candidateSafetyAuthority safety)))
            (Error.throwError_ OmittedProofDidNotRecordUse)
        completeCandidateWithValidation
                candidate
                OmittedAuthorization
                safety
                final

-- | Retain the closed candidate-target path while scoped proof composition is
-- introduced. It uses the same environment validation as local obligations.
acceptVampireObligation
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        Void
        origin
        ObjectId
    -> CandidateProof ()
acceptVampireObligation prepared =
    acceptValidatedVampireTask
        (validateCandidateVampireProblem prepared)
        prepared

-- | Validate one internally prepared scoped obligation, then retain its exact
-- accepted request.  The trusted caller remains responsible for structural
-- local-proof composition.
acceptPreparedVampireObligation
    :: (Eq local, Eq origin)
    => PreparedVampireObligation local origin
    -> CandidateProof ()
acceptPreparedVampireObligation
        (PreparedVampireObligation views expected prepared) =
    acceptValidatedVampireTask
        (validatePreparedVampireProblem views expected prepared)
        prepared

-- | Prepare and execute the current closed candidate using exactly the
-- staged premises already consumed by its trusted declaration compiler.
acceptCurrentCandidateVampire :: CandidateProof ()
acceptCurrentCandidateVampire =
    prepareCurrentCandidateVampire
        >>= acceptPreparedVampireObligation

-- | Prepare the current closed candidate without executing its request.  The
-- declaration-owned batch authorizer uses this seam only after all strictly
-- earlier staged premises have been consumed.
prepareCurrentCandidateVampire
    :: CandidateProof (PreparedVampireObligation Void ())
prepareCurrentCandidateVampire = do
    initial <- State.get
    let builder = candidateProofBuilder initial
        closure = candidateProofObjectClosure initial
        target = candidateCheckedProposition
            (candidateProofCandidate initial)
        premises =
            [ proposition
            | CandidatePremise _ proposition <-
                reverse (candidateProofPremisesReversed initial)
            ]
        preparation =
            prepareClosedCandidateVampire
                builder closure target premises
    preparedResult <- liftIO
        (forceVampirePreparation preparation)
    prepared <- liftEitherEffect
        (first
            CurrentCandidateVampirePreparationFailed
            preparedResult)
    pure prepared

prepareClosedCandidateVampire
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> CheckedPropositionContent
    -> [CheckedPropositionContent]
    -> Either
        (VampireObligationPreparationError Void)
        (PreparedVampireObligation Void ())
prepareClosedCandidateVampire builder closure target premises =
    prepareClosedCandidateVampireWithAuxiliaries
        builder closure target premises []

prepareClosedCandidateVampireWithAuxiliaries
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> CheckedPropositionContent
    -> [CheckedPropositionContent]
    -> [FoundationAxiomTag]
    -> Either
        (VampireObligationPreparationError Void)
        (PreparedVampireObligation Void ())
prepareClosedCandidateVampireWithAuxiliaries
        builder closure target premises auxiliaryTags = do
    prepareClosedCandidateVampireWithFactsAndAuxiliaries
        builder closure target premises [] auxiliaryTags

prepareClosedCandidateVampireWithFactsAndAuxiliaries
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> CheckedPropositionContent
    -> [CheckedPropositionContent]
    -> [SemanticFactOccurrenceFingerprint]
    -> [FoundationAxiomTag]
    -> Either
        (VampireObligationPreparationError Void)
        (PreparedVampireObligation Void ())
prepareClosedCandidateVampireWithFactsAndAuxiliaries
        builder closure target premises visibleFacts auxiliaryTags = do
    supportedTarget <-
        first
            VampireObligationClaimProjectionFailed
            (Backend.projectSupportedProposition
                globalTyping
                (Vector.empty :: Vector (Void, CoreType))
                (closed target))
    locals <-
        traverse
            prepareLocal
            (zip [0 :: Natural ..] premises)
    prepareVampireObligationWith
        Provers.DirectTask
        builder
        closure
        supportedTarget
        locals
        auxiliaryTags
        (maybe
            localVampirePremisePolicy
            explicitVampirePremisePolicy
            (NonEmpty.nonEmpty visibleFacts))
  where
    globalTyping = globalTypingFromClosure closure
    closed proposition =
        embedClosedCore []
            (checkedPropositionTerm proposition)

    prepareLocal (index, proposition) = do
        let ordinal = Backend.localPremiseOrdinal index
        supported <-
            first
                (VampireObligationLocalProjectionFailed ordinal)
                (Backend.projectSupportedProposition
                    globalTyping
                    (Vector.empty :: Vector (Void, CoreType))
                    (closed proposition))
        first
            (VampireObligationLocalClassificationFailed ordinal)
            (Backend.typedLocalPremise
                globalTyping ordinal () supported)

acceptValidatedVampireTask
    :: (CandidateProofState
        -> DeclarationBase CandidateProofState)
    -> Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> CandidateProof ()
acceptValidatedVampireTask validate prepared = do
    initial <- State.get
    validated <- inject (validate initial)
    results <- inject (resolveDeclarationVampireRequests (candidateProofDeclaration initial)
        ((prepared, isJust (candidateProofCachedValidation initial)) :| []))
    final <- inject
        (acceptVampireBatchMemberResult prepared (listToMaybe results) validated)
    State.put final

-- | Complete one checked source candidate after all of its obligations have
-- been accepted in source order.  The enclosing proof declaration owns the
-- exact syntax key and selects live or cached execution before this action.
authorizeVampireCandidate
    :: ReservedCandidate
    -> CandidateProof ()
    -> Declaration ()
authorizeVampireCandidate candidate proof =
    authorizeOneCandidate candidate \initial -> do
        ((), final) <- State.runState initial proof
        case acceptedRequestIds final of
            [] ->
                Error.throwError_
                    VampireProofHasNoAcceptedObligations
            request : requests ->
                completeCandidateWithValidation
                    candidate
                    (CheckedSourceProof
                        (UsesExternalProof (request :| requests)))
                    (candidateProofSafety final)
                    final

data PreparedVampireCandidateBatchMember =
    PreparedVampireCandidateBatchMember
        !Location
        !ReservedCandidate
        !(Provers.PreparedTypedProverTask
            SemanticFactOccurrenceFingerprint
            Void
            ()
            ObjectId)
        !CandidateProofState

data ResolvedVampireCandidateBatchMember =
    ResolvedVampireCandidateBatchMember
        !PreparedVampireCandidateBatchMember
        !(Maybe Provers.VampireResolution)

-- | Authorize one complete, source-ordered candidate stage whose members are
-- mutually independent and each require exactly one closed Vampire request.
-- Every member is prepared and validated against the same declaration
-- baseline.  Results are applied only after the complete live batch returns,
-- so no same-stage sibling can become authority for another member.
authorizeVampireCandidateBatch
    :: NonEmpty
        ( Location
        , ReservedCandidate
        , CandidateProof (PreparedVampireObligation Void ())
        )
    -> Declaration ()
authorizeVampireCandidateBatch inputs = do
    baseline <- State.get
    let supplied =
            [ candidate
            | (_location, candidate, _prepare) <- NonEmpty.toList inputs
            ]
        frontier = declarationAuthorizationFrontier baseline
        expected =
            List.filter
                ((== CandidateStage frontier) . reservedStage)
                (Map.elems (declarationReservations baseline))
    traverse_
        (liftEitherEffect . validateReservedCandidate baseline)
        supplied
    traverse_
        (\candidate ->
            when
                (Map.member
                    (reservedCandidateSlot candidate)
                    (declarationPending baseline))
                (Error.throwError_
                    (CandidateAlreadyAuthorized
                        (reservedCandidateSlot candidate))))
        supplied
    unless (supplied == expected)
        (Error.throwError_
            (VampireCandidateBatchMismatch
                (reservedCandidateSlot <$> expected)
                (reservedCandidateSlot <$> supplied)))
    prepared <-
        traverse
            (inject . prepareVampireCandidateBatchMember baseline)
            inputs
    inject
        (validateCachedVampireCandidateBatch
            (NonEmpty.toList prepared))
    liveResults <- inject (resolveDeclarationVampireRequests baseline
        (fmap (\(PreparedVampireCandidateBatchMember _ _ task final) ->
            (task, isJust (candidateProofCachedValidation final))) prepared))
    pending <- inject
        (completeVampireCandidateBatch
            (NonEmpty.toList prepared)
            liveResults)
    let withPending =
            baseline
                { declarationPending =
                    foldl'
                        (\entries item@(PendingCandidate candidate _ _) ->
                            Map.insert
                                (reservedCandidateSlot
                                    candidate)
                                item
                                entries)
                        (declarationPending baseline)
                        pending
                }
    State.put (advanceAuthorizationFrontier withPending)

prepareVampireCandidateBatchMember
    :: DeclarationState
    -> ( Location
       , ReservedCandidate
       , CandidateProof (PreparedVampireObligation Void ())
       )
    -> DeclarationBase PreparedVampireCandidateBatchMember
prepareVampireCandidateBatchMember
        baseline (location, candidate, prepare) = do
    let initial = initialCandidateProofState baseline candidate
    (obligation, preparedState) <-
        State.runState initial
            (locateProofObligation location prepare)
    unless (null (acceptedRequestIds preparedState))
        (Error.throwError_
            (VampireCandidateBatchProofShapeMismatch
                (reservedCandidateSlot candidate)))
    let PreparedVampireObligation views expected task = obligation
    validated <-
        mapErrorEffect (ProofObligationFailedAt location)
            (validatePreparedVampireProblem
                views expected task preparedState)
    pure
        (PreparedVampireCandidateBatchMember
            location candidate task validated)

completeVampireCandidateBatch
    :: [PreparedVampireCandidateBatchMember]
    -> [Provers.VampireResolution]
    -> DeclarationBase [PendingCandidate]
completeVampireCandidateBatch members liveResults = do
    resolved <-
        liftEitherEffect
            (associateVampireCandidateBatchResults
                members liveResults)
    -- Integrity dominates ranked proof failure: validate every accepted run
    -- before inspecting any ordinary process or prover rejection.
    traverse_ validateAcceptedVampireBatchMember resolved
    traverse_ rejectOrdinaryVampireBatchMember resolved
    traverse completeVampireCandidateBatchMember resolved

validateCachedVampireCandidateBatch
    :: [PreparedVampireCandidateBatchMember]
    -> DeclarationBase ()
validateCachedVampireCandidateBatch =
    traverse_ \member ->
        when
            (preparedVampireCandidateBatchMemberIsCached member)
            (void
                (completeVampireCandidateBatchMember
                    (ResolvedVampireCandidateBatchMember member Nothing)))

associateVampireCandidateBatchResults
    :: [PreparedVampireCandidateBatchMember]
    -> [Provers.VampireResolution]
    -> Either
        DeclarationError
        [ResolvedVampireCandidateBatchMember]
associateVampireCandidateBatchResults members =
    go members
  where
    go [] [] = Right []
    go [] results =
        Left
            (VampireResolverBatchSizeMismatch
                0
                (length results))
    go (member : remaining) results
        | preparedVampireCandidateBatchMemberIsCached member =
                (ResolvedVampireCandidateBatchMember member Nothing :)
                    <$> go remaining results
        | otherwise =
            case results of
                [] ->
                    Left (VampireResolverBatchSizeMismatch 1 0)
                current : later ->
                    (ResolvedVampireCandidateBatchMember
                        member (Just current) :)
                        <$> go remaining later

preparedVampireCandidateBatchMemberIsCached
    :: PreparedVampireCandidateBatchMember
    -> Bool
preparedVampireCandidateBatchMemberIsCached
        (PreparedVampireCandidateBatchMember
            _location _candidate _task state) =
    isJust (candidateProofCachedValidation state)

validateAcceptedVampireBatchMember
    :: ResolvedVampireCandidateBatchMember
    -> DeclarationBase ()
validateAcceptedVampireBatchMember
        (ResolvedVampireCandidateBatchMember
            (PreparedVampireCandidateBatchMember
                location _candidate task _validated)
            result) =
    mapErrorEffect (ProofObligationFailedAt location)
        (validateVampireResultIdentity task result)

rejectOrdinaryVampireBatchMember
    :: ResolvedVampireCandidateBatchMember
    -> DeclarationBase ()
rejectOrdinaryVampireBatchMember
        (ResolvedVampireCandidateBatchMember
            (PreparedVampireCandidateBatchMember
                location _candidate _task _validated)
            result) =
    traverse_
        (Error.throwError_ . ProofObligationFailedAt location)
        (result >>= vampireResultFailure)

completeVampireCandidateBatchMember
    :: ResolvedVampireCandidateBatchMember
    -> DeclarationBase PendingCandidate
completeVampireCandidateBatchMember
        (ResolvedVampireCandidateBatchMember
            (PreparedVampireCandidateBatchMember
                location candidate task validated)
            result) = do
    final <-
        mapErrorEffect (ProofObligationFailedAt location)
            (applyAcceptedVampireResult task result validated)
    completeCandidateWithValidation
        candidate
        (CheckedSourceProof
            (acceptedBatchExternalProofUse task validated))
        (candidateProofSafety final)
        final

acceptVampireBatchMemberResult
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> Maybe Provers.VampireResolution
    -> CandidateProofState
    -> DeclarationBase CandidateProofState
acceptVampireBatchMemberResult prepared result validated = do
    validateVampireResultIdentity prepared result
    traverse_ Error.throwError_ (result >>= vampireResultFailure)
    applyAcceptedVampireResult prepared result validated

validateVampireResultIdentity
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> Maybe Provers.VampireResolution
    -> DeclarationBase ()
validateVampireResultIdentity prepared result = do
    let request = Provers.preparedTypedProverRequest prepared
    traverse_
        (\resolved ->
            unless
                (Provers.vampireResolutionRequestId resolved
                    == Provers.preparedVerificationRequestId request)
                (Error.throwError_ VampireRequestMismatch))
        result

vampireResultFailure
    :: Provers.VampireResolution
    -> Maybe DeclarationError
vampireResultFailure =
    fmap VampireObligationFailed . Provers.vampireResolutionFailure

applyAcceptedVampireResult
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> Maybe Provers.VampireResolution
    -> CandidateProofState
    -> DeclarationBase CandidateProofState
applyAcceptedVampireResult prepared result validated = do
    traverse_
        (\resolved ->
            case vampireResultFailure resolved of
                Just failure ->
                    Error.throwError_ failure
                Nothing ->
                    pure ())
        result
    let request = Provers.preparedTypedProverRequest prepared
        requestId = Provers.preparedVerificationRequestId request
    pure
        validated
            { candidateProofAcceptedRequestsReversed =
                requestId
                    : candidateProofAcceptedRequestsReversed validated
            }

completeCandidateWithValidation
    :: ReservedCandidate
    -> DirectAuthorization
    -> CandidateSafety
    -> CandidateProofState
    -> DeclarationBase PendingCandidate
completeCandidateWithValidation candidate direct safety final = do
    pending <-
        liftEitherEffect
            (freshCompletion
                candidate
                direct
                safety
                final)
    traverse_
        (\validation ->
            case Materialization.checkCandidateValidation
                    (logicalBuilderTheory
                        (candidateProofBuilder final))
                    (logicalBuilderPrefix
                        (candidateProofBuilder final))
                    (candidateCheckedProposition candidate)
                    (validationTarget
                        (pendingCandidateCertificate pending))
                    direct
                    validation of
                Left failure ->
                    throwValidationIntegrity failure
                Right () ->
                    pure ())
        (candidateProofCachedValidation final)
    pure pending

pendingCandidateCertificate :: PendingCandidate -> ValidationCertificate
pendingCandidateCertificate
        (PendingCandidate _ certificate _) =
    certificate

acceptedRequestIds :: CandidateProofState -> [PreparedRequestId]
acceptedRequestIds =
    reverse . candidateProofAcceptedRequestsReversed

acceptedExternalProofUse
    :: CandidateProofState
    -> ExternalProofUse PreparedRequestId
acceptedExternalProofUse state =
    case acceptedRequestIds state of
        [] -> NoExternalProofUse
        request : requests ->
            UsesExternalProof (request :| requests)

acceptedBatchExternalProofUse
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> CandidateProofState
    -> ExternalProofUse PreparedRequestId
acceptedBatchExternalProofUse task state =
    UsesExternalProof
        case acceptedRequestIds state of
            [] -> requestId :| []
            request : requests ->
                request :| (requests <> [requestId])
  where
    requestId =
        Provers.preparedVerificationRequestId
            (Provers.preparedTypedProverRequest task)

freshCompletion
    :: ReservedCandidate
    -> DirectAuthorization
    -> CandidateSafety
    -> CandidateProofState
    -> Either DeclarationError PendingCandidate
freshCompletion candidate direct safety proofState = do
    let builder = candidateProofBuilder proofState
        declaration = candidateProofDeclaration proofState
        reference = candidateTheoremReference builder candidate
        authority = candidateFactAuthority reference safety
    certificate <-
        first ValidationCertificateFailed
            (validationCertificate authority direct)
    let authorization =
            PendingFactAuthorization
                (logicalBuilderIdentity builder)
                (logicalBuilderPrefix builder)
                (declarationInvocation declaration)
                (reservedCandidateSlot candidate)
                authority
                (reservedStage candidate)
                [source | CandidatePremise source _ <- reverse (candidateProofPremisesReversed proofState)]
                (candidateProofDependencies proofState)
    pure
        (PendingCandidate
            candidate
            certificate
            authorization)

authorizeOneCandidate
    :: ReservedCandidate
    -> (CandidateProofState
        -> DeclarationBase PendingCandidate)
    -> Declaration ()
authorizeOneCandidate candidate complete = do
    state <- State.get
    liftEitherEffect (validateReservedCandidate state candidate)
    when
        (Map.member
            (reservedCandidateSlot candidate)
            (declarationPending state))
        (Error.throwError_
            (CandidateAlreadyAuthorized
                (reservedCandidateSlot candidate)))
    unless
        (reservedStage candidate
            == CandidateStage
                (declarationAuthorizationFrontier state))
        (Error.throwError_
            (CandidateOutsideAuthorizationFrontier
                (reservedCandidateSlot candidate)
                (reservedCandidateStage candidate)
                (declarationAuthorizationFrontier state)))
    let initial = initialCandidateProofState state candidate
    pending <- inject (complete initial)
    let state' =
            state
                { declarationPending =
                    Map.insert
                        (reservedCandidateSlot candidate)
                        pending
                        (declarationPending state)
                }
    State.put (advanceAuthorizationFrontier state')

advanceAuthorizationFrontier
    :: DeclarationState
    -> DeclarationState
advanceAuthorizationFrontier state
    | all stageCompleted currentCandidates =
        state
            { declarationAuthorizationFrontier =
                frontier + 1
            }
    | otherwise =
        state
  where
    frontier = declarationAuthorizationFrontier state
    currentCandidates =
        List.filter
            ((== CandidateStage frontier) . reservedStage)
            (Map.elems (declarationReservations state))
    stageCompleted candidate =
        Map.member
            (reservedCandidateSlot candidate)
            (declarationPending state)

initialCandidateProofState :: DeclarationState -> ReservedCandidate -> CandidateProofState
initialCandidateProofState declaration candidate = CandidateProofState
    { candidateProofDeclaration = declaration
    , candidateProofCandidate = candidate
    , candidateProofCachedValidation = Map.lookup (reservedCandidateSlot candidate)
        (declarationCandidateValidations declaration)
    , candidateProofPremisesReversed = []
    , candidateProofPremiseCount = 0
    , candidateProofSafety = initialCandidateSafety
    , candidateProofDependencies = Set.empty
    , candidateProofAcceptedRequestsReversed = []
    }

reservedStage :: ReservedCandidate -> CandidateStage
reservedStage
        (ReservedCandidate _ _ _ stage _ _) =
    stage

validateReservedCandidate
    :: DeclarationState
    -> ReservedCandidate
    -> Either DeclarationError ()
validateReservedCandidate declaration candidate = do
    let builder = declarationBuilder declaration
        ReservedCandidate
            identity prefix invocation _stage slot _spec = candidate
    unless
        ( identity == logicalBuilderIdentity builder
          && prefix == logicalBuilderPrefix builder
          && invocation == declarationInvocation declaration
          && Map.lookup slot
                (declarationReservations declaration)
                == Just candidate
        )
        (Left (CandidateOutsideDeclaration slot))

instance Eq ReservedCandidate where
    left == right =
        reservedCandidateKey left == reservedCandidateKey right

reservedCandidateKey
    :: ReservedCandidate
    -> (BuilderIdentity, PrefixContextId, DeclarationInvocation, CandidateStage, FactSlot)
reservedCandidateKey
        (ReservedCandidate identity prefix invocation stage slot _spec) =
    (identity, prefix, invocation, stage, slot)


consumeBuilderAuthorizedFact
    :: FactEntry BuilderFactAuthorization
    -> CandidateProofState
    -> CandidateProof CheckedPropositionContent
consumeBuilderAuthorizedFact
        (FactEntry proposition occurrence authorization)
        state = do
    let builder = candidateProofBuilder state
        BuilderFactAuthorization
            identity slot certificate = authorization
        authority = validationTarget certificate
    unless
        ( identity == logicalBuilderIdentity builder
          && slot == semanticFactSlot occurrence
          && authority == semanticFactAuthority occurrence
        )
        (Error.throwError_ BuilderFactAuthorizationMismatch)
    admitAndAccumulateAuthorizedFact
        (semanticFactFingerprint occurrence)
        proposition
        authority
        state
    pure proposition

consumePendingFact
    :: PendingCandidate
    -> CandidateProofState
    -> CandidateProof CheckedPropositionContent
consumePendingFact
        (PendingCandidate premise certificate authorization)
        state = do
    let builder = candidateProofBuilder state
        declaration = candidateProofDeclaration state
        PendingFactAuthorization
            identity prefix invocation slot authority
            premiseStageValue _imports _dependencies = authorization
        current = candidateProofCandidate state
    unless
        ( identity == logicalBuilderIdentity builder
          && prefix == logicalBuilderPrefix builder
          && invocation == declarationInvocation declaration
          && slot == reservedCandidateSlot premise
          && authority == validationTarget certificate
          && premiseStageValue == reservedStage premise
        )
        (Error.throwError_ PendingFactAuthorizationMismatch)
    unless
        (reservedStage premise < reservedStage current)
        (Error.throwError_
            (StagedPremiseNotEarlier
                (reservedCandidateSlot premise)
                (reservedCandidateStage premise)
                (reservedCandidateSlot current)
                (reservedCandidateStage current)))
    let proposition = candidateCheckedProposition premise
    admitAndAccumulateAuthorizedFact
        (semanticFactFingerprint (candidateOccurrence premise authority))
        proposition
        authority
        state
    pure proposition

-- | Complete destination-side consumption after the caller has authenticated
-- the opaque builder or pending-fact capability.  Admission deliberately
-- precedes safety accumulation, so every fact consumed by kernel, scoped,
-- structural, and backend gates follows the same owner path whether or not a
-- later proof uses it as a kernel import.
admitAndAccumulateAuthorizedFact
    :: SemanticFactOccurrenceFingerprint
    -> CheckedPropositionContent
    -> FactAuthority
    -> CandidateProofState
    -> CandidateProof ()
admitAndAccumulateAuthorizedFact fingerprint proposition authority state = do
    void
        (liftEitherEffect
            (first DeclarationPropositionValidationFailed
                (validateAssertedPropositionContent
                    (candidateProofObjectClosure state)
                    (checkedPropositionId proposition)
                    (frozenCoreTerm
                        (checkedPropositionTerm proposition)))))
    let expected =
            theoremRef
                (logicalBuilderTheory
                    (candidateProofBuilder state))
                (checkedPropositionId proposition)
    safety <- liftEitherEffect
        (first FactSafetyFailed
            (accumulateFactSafety
                expected
                authority
                (candidateProofSafety state)))
    State.put state
        { candidateProofSafety = safety
        , candidateProofDependencies = Set.insert fingerprint (candidateProofDependencies state)
        }

appendCandidatePremise
    :: Maybe SemanticFactOccurrenceFingerprint
    -> CheckedPropositionContent
    -> CandidateProofState
    -> CandidateProof ImportIx
appendCandidatePremise source proposition state = do
    let index = candidateProofPremiseCount state
    State.put
        state
            { candidateProofPremisesReversed =
                CandidatePremise source proposition
                    : candidateProofPremisesReversed state
            , candidateProofPremiseCount = index + 1
            }
    pure (importIx index)

findPendingByFingerprint
    :: SemanticFactOccurrenceFingerprint
    -> Map FactSlot PendingCandidate
    -> Maybe PendingCandidate
findPendingByFingerprint fingerprint =
    find
        (\(PendingCandidate candidate certificate _authorization) ->
            semanticFactFingerprint
                (candidateOccurrence candidate (validationTarget certificate))
                == fingerprint)
        . Map.elems

candidateImportJudgements
    :: CandidateProofState
    -> Either DeclarationError (Vector (DerivationImportJudgement ObjectId))
candidateImportJudgements state =
    Vector.fromList
        <$> traverse
            (\(CandidatePremise _ proposition) ->
                first DerivationImportFailed
                    (derivationImportJudgement
                        (checkedPropositionTerm proposition)))
            (reverse
                (candidateProofPremisesReversed state))

-- | Complete owner-bound replay.  The caller supplies only the provisional
-- proof tree and expected proposition; the declaration owner derives both the
-- typing snapshot and ordered logical import environment from this state.
replayOwnedCandidateKernel
    :: (Error DeclarationError :> es, IOE :> es)
    => CheckedPropositionContent -> KernelDerivation ObjectId -> CandidateProofState
    -> Eff es (ReplayedKernelDerivation ObjectId)
replayOwnedCandidateKernel proposition derivation state = do
    imports <- liftEitherEffect (candidateImportJudgements state)
    let builder = candidateProofBuilder state
        closure = candidateProofObjectClosure state
        run :: (CheckedFoundation -> KernelReplayLimits -> GlobalTyping ObjectId
            -> Vector (DerivationImportJudgement ObjectId) -> FrozenCheckedCore ObjectId
            -> KernelDerivation ObjectId -> value) -> value
        run replay = replay (logicalBuilderFoundation builder) defaultKernelReplayLimits
            (globalTypingFromClosure closure) imports (checkedPropositionTerm proposition) derivation
    result <- liftIO (measureFormationReplay (declarationFormationRecorder (candidateProofDeclaration state))
        (run replayKernelDerivation) (run replayKernelDerivationMeasured))
    liftEitherEffect (first KernelCompletionFailed result)

-- Select the counted interpreter only for a formation owner with reporting on.
-- Failed replay retains its physical work before the ordinary error is raised.
measureFormationReplay
    :: FormationDiagnostics.Recorder -> Either KernelReplayError value
    -> (Either KernelReplayError value, ReplayWork) -> IO (Either KernelReplayError value)
measureFormationReplay recorder ordinary counted = do
    enabled <- FormationDiagnostics.measuringPhase recorder FormationDiagnostics.Proof
    if not enabled then pure ordinary else do
        let (result, work) = counted
            nodes = replayWorkNodes work
            measured = FormationDiagnostics.emptyMeasurement
                { FormationDiagnostics.measuredDiagnostics = FormationDiagnostics.countOperation FormationDiagnostics.ReplayNode nodes
                    (FormationDiagnostics.countCoreWork FormationDiagnostics.Proof (replayWorkCore work)
                    (FormationDiagnostics.countPhaseWork FormationDiagnostics.Proof (nodes + replayWorkCore work)
                        FormationDiagnostics.emptyDiagnostics))
                , FormationDiagnostics.limitHighWater = Map.fromList
                    [("replay-nodes.used", nodes), ("replay-depth.used", replayWorkDepth work),
                     ("replay-nodes.cap", 200000), ("replay-depth.cap", 2048)]
                    <> case result of
                        Left (KernelReplayNodeLimitExceeded cap) -> Map.singleton "replay-nodes.rejected" (max 1 (nodes - cap))
                        Left KernelReplayDepthLimitExceeded{} -> Map.singleton "replay-depth.rejected" 1
                        Left (KernelReplayConversionFailed Conversion.ConversionLimitExhausted{}) ->
                            Map.singleton "replay-conversion.rejected" 1
                        _ -> Map.empty }
        FormationDiagnostics.recordMeasurement recorder measured
        pure result

validateKernelConstruction
    :: KernelConstructionDescriptor
    -> CheckedPropositionContent
    -> ReplayedKernelDerivation ObjectId
    -> CandidateProofState
    -> Either DeclarationError ()
validateKernelConstruction descriptor proposition replayed proofState =
    unless matches
        (Left KernelConstructionDescriptorMismatch)
  where
    builder = candidateProofBuilder proofState
    noImports = Set.null (replayedKernelImportUses replayed)
    noFoundation = Set.null (replayedKernelFoundationUses replayed)
    noRules = Set.null (replayedKernelRuleUses replayed)

    matches =
        case descriptor of
            FoundationLeaf tag ->
                noImports
                    && replayedKernelFoundationUses replayed
                        == Set.singleton tag
                    && noRules
                    && checkedPropositionTerm proposition
                        == eliminateFrozenVoid
                            (foundationAxiomFrozen
                                (logicalBuilderFoundation builder)
                                tag)
            GuardedFoundationRules rules ->
                replayedKernelRuleUses replayed
                    == guardedRuleTags rules
            CheckedDefinitionEquation identity ->
                definitionEquation identity
            CheckedImplementationDefinition identity ->
                definitionEquation identity
            CheckedDerivedConstruction -> True
            CheckedDefinitionProjection identity path ->
                noFoundation && noRules
                    && replayedKernelImportUses replayed == Set.singleton (importIx 0)
                    && matchesPredicateProjection (candidateProofObjectClosure proofState) identity path proposition
                    && case candidateProofPremisesReversed proofState of
                        [CandidatePremise (Just fingerprint) _premise] ->
                            definitionImport identity fingerprint
                        _ -> False
            CheckedSetConstructionExtensionality{} ->
                False
            CheckedStructureLaw family ->
                replayedKernelImportUses replayed
                    == contiguousImportUses proofState
                    && Just (replayedKernelFoundationUses replayed)
                        == expectedStructureFoundation family
                    && noRules

    expectedStructureFoundation family = do
        let ReservedCandidate _ _ _ _ _ spec = candidateProofCandidate proofState
        StructureFactPurpose (Schema.StructureLawId owner law) <- pure (candidateSpecPurpose spec)
        guard (StructureLaws.structureLawFamily law == family)
        let prepared = declarationPreparedResult (candidateProofDeclaration proofState)
            PreparedDeclarationEnvironment interfaces _ _ = preparedDeclarationEnvironment prepared
        registration <- List.find
            ((== owner) . Schema.resolvedSchemaId . StructurePredicate.pendingStructureSchema)
            (StructureInterface.structureInterfaceRegistration <$> interfaces)
        pure (StructureLaws.structureLawFoundationTags
            (StructurePredicate.pendingStructureSchema registration) law)

    definitionEquation identity =
        noImports && noFoundation && noRules
            && matchesDefinitionEquation identity proposition proofState

    contiguousImportUses state =
        Set.fromList
            [ importIx index
            | (index, _premise) <-
                zip [0 ..] (candidateProofPremisesReversed state)
            ]

    definitionImport identity fingerprint =
        let existing = Map.lookup fingerprint (logicalBuilderFacts builder)
                >>= \(FactEntry _ _ evidence) -> builderEvidenceDirect evidence
            staged = validationDirectAuthorization . pendingCandidateCertificate
                <$> findPendingByFingerprint fingerprint
                    (declarationPending (candidateProofDeclaration proofState))
        in case existing <|> staged of
            Just (CheckedKernelConstruction (CheckedDefinitionEquation source)) -> source == identity
            _ -> False

matchesPredicateProjection
    :: CheckedObjectClosure -> ObjectId -> ConjunctionPath -> CheckedPropositionContent -> Bool
matchesPredicateProjection closure identity path proposition =
    case lookupCheckedObjectContent identity closure of
        Just (TransparentObjectContent _theory coreType body) ->
            predicateProjectionTarget identity coreType body path
                == Just (frozenCoreTerm (checkedPropositionTerm proposition))
        _ -> False

matchesDefinitionEquation
    :: ObjectId
    -> CheckedPropositionContent
    -> CandidateProofState
    -> Bool
matchesDefinitionEquation identity proposition proofState =
    case lookupCheckedObjectContent
            identity
            (candidateProofObjectClosure proofState) of
        Just
                (TransparentObjectContent
                    contentTheory coreType body) ->
            contentTheory
                == logicalBuilderTheory
                    (candidateProofBuilder proofState)
                && frozenCoreTerm (checkedPropositionTerm proposition)
                    == definitionEquationTarget identity coreType body
        _ ->
            False


validateCandidateVampireProblem
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        Void
        origin
        ObjectId
    -> CandidateProofState
    -> DeclarationBase CandidateProofState
validateCandidateVampireProblem prepared initial = do
    let problem = Provers.preparedTypedProverLogicalProblem prepared
        claim = Backend.typedProblemClaim problem
        target = candidateCheckedProposition
            (candidateProofCandidate initial)
    liftEitherEffect do
        unless
            ( Vector.null (Backend.supportedPropositionSupport claim)
              && Backend.supportedPropositionTerm claim
                    == frozenCoreTerm (checkedPropositionTerm target)
            )
            (Left VampireTargetMismatch)
        unless
            (Vector.null (Backend.typedProblemLocalPremises problem))
            (Left VampireLocalPremisesNotSupported)
    validateVampireProblemEnvironment prepared initial

validatePreparedVampireProblem
    :: (Eq local, Eq origin)
    => Maybe CitedStructureViews
    -> Backend.TypedProblem
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> CandidateProofState
    -> DeclarationBase CandidateProofState
validatePreparedVampireProblem views expectedProblem prepared initial = do
    liftEitherEffect (traverse_ (validateCitedStructureViews (candidateProofBuilder initial)) views)
    let problem = Provers.preparedTypedProverLogicalProblem prepared
    liftEitherEffect
        (unless (problem == expectedProblem)
            (Left VampireTargetMismatch)
        )
    validateVampireProblemEnvironment prepared initial

validateVampireProblemEnvironment
    :: Provers.PreparedTypedProverTask
        SemanticFactOccurrenceFingerprint
        local
        origin
        ObjectId
    -> CandidateProofState
    -> DeclarationBase CandidateProofState
validateVampireProblemEnvironment prepared initial = do
    let problem = Provers.preparedTypedProverLogicalProblem prepared
        builder = candidateProofBuilder initial
        closure = candidateProofObjectClosure initial
    liftEitherEffect do
        traverse_
            (\(identity, reportedType) ->
                unless
                    (lookupCheckedObjectType identity closure
                        == Just reportedType)
                    (Left (VampireGlobalTypeMismatch identity)))
            (Map.toList (Backend.typedProblemGlobalTypes problem))
        traverse_
            (validateFoundationAuxiliary builder)
            (Backend.typedProblemAuxiliaries problem)
        traverse_
            validateLogicalSelectionAuxiliary
            (Backend.typedProblemLogicalSelections problem)
    execCandidateProof initial do
        traverse_
            validatePremise
            (Backend.typedProblemGlobalPremises problem)
  where
    validatePremise selected = do
        let fingerprint = Backend.typedBackendFactReference selected
        proposition <- consumeAuthorizedFact fingerprint
        state <- State.get
        unless
            ( Backend.supportedPropositionTerm
                (Backend.typedBackendFactProposition selected)
                == frozenCoreTerm
                    (checkedPropositionTerm proposition)
            )
            (failCandidateProof
                (VampirePremiseMismatch fingerprint))
        let closure =
                candidateProofObjectClosure state
        supported <-
            either
                (const
                    (failCandidateProof
                        (VampirePremiseCapabilityMismatch
                            fingerprint)))
                pure
                (Backend.supportedProposition
                    Vector.empty
                    (embedClosedCore
                        []
                        (checkedPropositionTerm proposition)))
        capability <-
            either
                (const
                    (failCandidateProof
                        (VampirePremiseCapabilityMismatch
                            fingerprint)))
                pure
                (Backend.classifySupportedProposition
                    (globalTypingFromClosure closure)
                    supported)
        unless
            (capability
                == Backend.typedBackendFactCapability selected)
            (failCandidateProof
                (VampirePremiseCapabilityMismatch fingerprint))

    validateFoundationAuxiliary builder auxiliary = do
        let tag = Backend.typedProblemAuxiliaryTag auxiliary
            actual =
                Backend.supportedPropositionTerm
                    (Backend.typedProblemAuxiliaryProposition auxiliary)
            expectedTerm =
                frozenCoreTerm
                    (eliminateFrozenVoid
                        (foundationAxiomFrozen
                            (logicalBuilderFoundation builder)
                            tag))
        unless (actual == expectedTerm)
            (Left (VampireFoundationMismatch tag))

    validateLogicalSelectionAuxiliary auxiliary = do
        let coreType =
                Backend.typedLogicalSelectionAuxiliaryType auxiliary
            actual =
                Backend.supportedPropositionTerm
                    (Backend.typedLogicalSelectionAuxiliaryProposition
                        auxiliary)
            expectedTerm =
                frozenCoreTerm
                    (eliminateFrozenVoid
                        (logicalSelectionWitness coreType))
        unless (actual == expectedTerm)
            (Left (VampireLogicalSelectionMismatch coreType))

execCandidateProof
    :: CandidateProofState
    -> CandidateProof value
    -> DeclarationBase CandidateProofState
execCandidateProof initial action =
    snd <$> State.runState initial action

failCandidateProof
    :: DeclarationError
    -> CandidateProof value
failCandidateProof failure =
    Error.throwError_ failure

data PlannedVampireDisposition
    = PlannedRequestCoveredByValidation
    | PlannedLiveRequest !Provers.VampireHandle
    | PlannedSynchronousRequest

-- The contracts contain inert source identities, never builder permissions.
data PreparedCandidate = PreparedCandidate
    { preparedCandidateReservation :: !ReservedCandidate
    , preparedCandidateAuthority :: !FactAuthority
    , preparedCandidateDirect :: !DirectAuthorization
    , preparedCandidateDependencies :: ![SemanticFactOccurrenceFingerprint]
    , preparedCandidateRequests :: ![CheckedPlannedVampireRequest]
    }

type PlannedRequestCursor = IORef [(Provers.PreparedVerificationRequest, PlannedVampireDisposition)]

data PlannedValidationSelection
    = PlannedFreshValidation
    | PlannedProofValidation !ProofValidationRecord
    | PlannedCompiledValidation !DeclarationValidationRecord

-- Retain only declaration-local checked additions. Neither this product nor
-- its body keeps a predecessor builder, closure, catalog or resolver alive.
data PreparedDeclaration body = PreparedDeclaration
    { preparedDeclarationMode :: !CheckedDeclarationMode
    , preparedDeclarationIdentity :: !BuilderIdentity
    , preparedDeclarationTheory :: !TheoryId
    , preparedDeclarationPrevious :: !PrefixContextId
    , preparedDeclarationNext :: !PrefixContextId
    , preparedDeclarationDelta :: !DeclarationInterfaceDelta
    , preparedDeclarationObjects :: !CheckedObjectContribution
    , preparedDeclarationPropositions :: ![CheckedPropositionContent]
    , preparedDeclarationCandidates :: ![NonEmpty PreparedCandidate]
    , preparedDeclarationEnvironment :: !(PreparedDeclarationEnvironment PlanningEvidence)
    , preparedDeclarationBody :: !body
    }

data PreparedDeclarationEnvironment evidence = PreparedDeclarationEnvironment
    ![StructureInterface.CheckedStructureInterface evidence]
    ![ResolvedGlobalBinding]
    ![RecursionInterface.CheckedRecursiveDefinition]

-- Execution choices belong to this invocation, outside the semantic product.
data PlannedDeclaration body = PlannedDeclaration
    !(PreparedDeclaration body)
    !PlannedValidationSelection
    ![PlannedVampireDisposition]

plannedDeclarationPreviousPrefix :: PlannedDeclaration body -> PrefixContextId
plannedDeclarationPreviousPrefix (PlannedDeclaration prepared _ _) = preparedDeclarationPrevious prepared

plannedDeclarationNextPrefix :: PlannedDeclaration body -> PrefixContextId
plannedDeclarationNextPrefix (PlannedDeclaration prepared _ _) = preparedDeclarationNext prepared

plannedDeclarationDelta :: PlannedDeclaration body -> DeclarationInterfaceDelta
plannedDeclarationDelta (PlannedDeclaration prepared _ _) = preparedDeclarationDelta prepared

preparedObjectAssertions :: PreparedDeclaration body -> [AssertedObject]
preparedObjectAssertions prepared =
    [ assertions Map.! identity
    | identity <- declarationDeltaObjects (preparedDeclarationDelta prepared)
    ]
  where
    assertions = Map.fromList [(assertedObjectId object, object)
        | object <- checkedObjectContributionAssertions (preparedDeclarationObjects prepared)]

newtype PlanningIntegrityError = PlanningIntegrityError Text
    deriving stock (Show)

instance Exception.Exception PlanningIntegrityError

throwPlanningIntegrity :: MonadIO m => Text -> m value
throwPlanningIntegrity =
    liftIO . throwIO . PlanningIntegrityError

-- | Advance the authority-free semantic projection through one complete
-- checked declaration.  Validation selection and every deterministic check
-- finish before the first live request is submitted.
planCheckedDeclaration
    :: CheckedDeclaration body
    -> LoweringDriver (Either DeclarationError (PlannedDeclaration body))
planCheckedDeclaration checked = do
    state <- State.get
    let ProspectiveBuilder builder = loweringBuilder state
    result <- Error.runErrorNoCallStack do
        preparation <- inject (prepareDeclaration builder checked)
        (prepared, closure, environment) <- liftEitherEffect preparation
        selection <- inject (selectPlannedValidation (preparedDeclarationMode prepared)
            builder (preparedObjectAssertions prepared) (preparedDeclarationCandidates prepared))
        registered <- liftEitherEffect (appendProspectiveBuilder closure environment
            (preparedDeclarationDelta prepared) (preparedDeclarationNext prepared)
            (preparedDeclarationCandidates prepared) builder)
        compiled <- inject (withFormationPhaseLowering FormationDiagnostics.DeclarationPreparation
            (recordPreparedFormation (loweringFormationRecorder state)
                (prepareOwnedFormationRules planningEvidenceDirect (preparedDeclarationDelta prepared) registered)))
        nextBuilder <- liftEitherEffect compiled
        dispositions <- inject (submitPlannedRequests (loweringResolver state) selection
            (concatMap preparedCandidateRequests (concatMap toList (preparedDeclarationCandidates prepared))))
        pure (PlannedDeclaration prepared selection dispositions, nextBuilder)
    case result of
        Left failure -> pure (Left failure)
        Right (declaration, nextBuilder) -> do
            State.put state{loweringBuilder = ProspectiveBuilder nextBuilder}
            pure (Right declaration)

prepareDeclaration
    :: BuilderState PlanningEvidence -> CheckedDeclaration body
    -> LoweringDriver (Either DeclarationError (PreparedDeclaration body, CheckedObjectClosure, ResolvedEnvironment PlanningEvidence))
prepareDeclaration builder (CheckedDeclaration mode objectInput explicitPropositions globals structureBatch registrations datatype stages body) = Except.runExceptT do
    closure <- Except.liftEither $ first DeclarationObjectValidationFailed
        (extendDeclarationObjects (logicalBuilderObjectClosure builder) objectInput)
    candidates <- Except.liftEither $ preparePlannedCandidates builder closure (reservePlanningStages builder stages)
    let ordered = concatMap toList candidates
        occurrences = [candidateOccurrence (preparedCandidateReservation candidate)
            (preparedCandidateAuthority candidate) | candidate <- ordered]
        aliases = [semanticAlias alias (semanticFactFingerprint occurrence)
            | (candidate, occurrence) <- zip ordered occurrences
            , alias <- candidateAliases (preparedCandidateReservation candidate)]
        propositions = stableUniqueBy checkedPropositionId
            (explicitPropositions <> (candidateCheckedProposition . preparedCandidateReservation <$> ordered))
        objectIds = assertedObjectId <$> declarationObjectAssertions objectInput
        ownSlot = declarationSlot (logicalBuilderOwner builder)
            (localDeclarationOrdinal (logicalBuilderNextDeclaration builder))
    objects <- Except.liftEither $ first DeclarationObjectValidationFailed (checkedObjectContribution closure objectIds)
    definitionViews <- Except.liftEither $ deriveCanonicalDefinitionViews builder closure
        [(preparedCandidateReservation candidate, preparedCandidateAuthority candidate, preparedCandidateDirect candidate)
        | candidate <- ordered]
    resolvedRegistrations <- Except.liftEither $ resolvePlannedRegistrations registrations candidates
    describedGlobals <- Except.liftEither $ case datatype of
        Nothing -> pure globals
        Just (key, pending) -> do
            descriptor <- for pending \position -> do
                candidate <- maybe (Left (BindingConstructionInvalid "a construction law candidate is missing")) Right
                    (candidateAtPosition position candidates)
                pure (semanticFactFingerprint (candidateOccurrence
                    (preparedCandidateReservation candidate) (preparedCandidateAuthority candidate)))
            unless (length [() | binding <- globals, semanticGlobalBindingKey binding == key] == 1)
                (Left (BindingConstructionInvalid "a construction binding is missing or repeated"))
            pure [if semanticGlobalBindingKey binding == key then withSemanticConstruction descriptor binding else binding | binding <- globals]
    Except.liftEither $ first DatatypeInterfaceInvalid (DatatypeInterface.checkDatatypeBindings closure describedGlobals
        (zip occurrences (candidateCheckedProposition . preparedCandidateReservation <$> ordered)))
    Except.liftEither $ traverse_ (\proposition -> void (first DeclarationPropositionValidationFailed
        (validateAssertedPropositionContent closure (checkedPropositionId proposition)
            (frozenCoreTerm (checkedPropositionTerm proposition))))) propositions
    structureCandidates <- Except.liftEither $ case structureBatch of
        Nothing -> pure Map.empty
        Just _ -> plannedStructureCandidates builder candidates
    definitions <- Except.liftEither (checkRecursiveBindings closure (logicalBuilderEnvironment builder) ownSlot describedGlobals
        (zip occurrences (candidateCheckedProposition . preparedCandidateReservation <$> ordered)))
    (environment, additions, delta, next) <- buildCheckedDeclarationDelta
        builder closure ownSlot occurrences aliases objectIds (checkedPropositionId <$> propositions)
        definitionViews resolvedRegistrations (reverse describedGlobals) definitions planningEvidenceDirect structureCandidates structureBatch
    pure (PreparedDeclaration mode (logicalBuilderIdentity builder) (logicalBuilderTheory builder)
        (logicalBuilderPrefix builder) next delta objects propositions candidates additions body, closure, environment)

reservePlanningStages
    :: BuilderState PlanningEvidence
    -> [NonEmpty CheckedCandidate]
    -> [NonEmpty (ReservedCandidate, CandidatePlanningSpec)]
reservePlanningStages builder =
    snd . mapAccumPlanning reserveStage (logicalBuilderNextFact builder)
  where
    invocation = DeclarationInvocation (logicalBuilderNextInvocation builder)
    reserveStage nextFact (stageIndex, specs) =
        let candidates =
                NonEmpty.zipWith
                    (\offset (CheckedCandidate spec planning) ->
                        ( ReservedCandidate
                            (logicalBuilderIdentity builder)
                            (logicalBuilderPrefix builder)
                            invocation
                            (CandidateStage stageIndex)
                            (factSlot
                                (logicalBuilderOwner builder)
                                (localFactOrdinal (nextFact + offset)))
                            spec
                        , planning
                        ))
                    (0 :| [1..])
                    specs
        in ( nextFact + fromIntegral (NonEmpty.length specs)
           , candidates
           )

    mapAccumPlanning action initial values =
        go initial (zip [0..] values)
      where
        go accumulator [] = (accumulator, [])
        go accumulator (value : remaining) =
            let (next, result) = action accumulator value
                (final, results) = go next remaining
            in (final, result : results)

preparePlannedCandidates
    :: BuilderState PlanningEvidence
    -> CheckedObjectClosure
    -> [NonEmpty (ReservedCandidate, CandidatePlanningSpec)]
    -> Either
        DeclarationError
        [NonEmpty PreparedCandidate]
preparePlannedCandidates builder closure stages =
    snd <$> mapAccumM prepareStage Map.empty (zip [0..] stages)
  where
    prepareStage earlier (stageIndex, stage) = do
        (sameStage, planned) <-
            mapAccumM
                (prepareCandidate stageIndex earlier)
                Map.empty
                (zip [0..] (toList stage))
        pure (Map.union earlier sameStage, NonEmpty.fromList planned)

    prepareCandidate stageIndex earlier sameStage
            (candidateIndex, (candidate, contract)) = do
        let position = PlannedCandidatePosition stageIndex candidateIndex
        (direct, safety, dependencies, requests) <-
            prepareCandidatePlanningContract
                builder closure earlier position candidate contract
        let authority =
                candidateFactAuthority
                    (candidateTheoremReference builder candidate)
                    safety
            planned = PreparedCandidate candidate authority direct dependencies requests
        pure
            ( Map.insert position (candidate, authority) sameStage
            , planned
            )

prepareCandidatePlanningContract
    :: BuilderState PlanningEvidence
    -> CheckedObjectClosure
    -> Map PlannedCandidatePosition (ReservedCandidate, FactAuthority)
    -> PlannedCandidatePosition
    -> ReservedCandidate
    -> CandidatePlanningSpec
    -> Either
        DeclarationError
        ( DirectAuthorization
        , CandidateSafety
        , [SemanticFactOccurrenceFingerprint]
        , [CheckedPlannedVampireRequest]
        )
prepareCandidatePlanningContract builder closure earlier current candidate
        (CandidatePlanningSpec direct references) = do
    let requests = planningDirectRequests direct
        extraFacts = [fingerprint | EnvironmentOccurrenceReference fingerprint <- references]
        staged = [position | LocalCandidateReference position <- references]
    safetyWithFacts <-
        foldM (accumulatePlanningFact builder closure)
            initialCandidateSafety
            (stableUniqueBy id
                ( extraFacts
                    <> concatMap requestFacts requests
                ))
    safetyWithStages <-
        foldM consumeStage safetyWithFacts staged
    let safety = case direct of
            PlanningSourceAxiom ->
                addCandidateEscape SourceAxiom safetyWithStages
            PlanningOmitted{} ->
                addCandidateEscape Omitted safetyWithStages
            _ -> safetyWithStages
        directAuthorization = case direct of
            PlanningDefinitionEquation identity ->
                CheckedKernelConstruction
                    (CheckedDefinitionEquation identity)
            PlanningSourceAxiom -> SourceAxiomAuthorization
            PlanningKernelConstruction descriptor ->
                CheckedKernelConstruction descriptor
            PlanningCheckedSourceProof proofUse ->
                CheckedSourceProof (fmap requestIdentity proofUse)
            PlanningOmitted{} -> OmittedAuthorization
    validatePlanningDirect directAuthorization safety
    dependencies <- traverse referenceFingerprint references
    pure (directAuthorization, safety, dependencies <> concatMap requestFacts requests, requests)
  where
    referenceFingerprint = \case
        EnvironmentOccurrenceReference fingerprint -> pure fingerprint
        LocalCandidateReference position -> do
            (premise, authority) <- maybe
                (Left (PlanningFactContractMismatch (reservedCandidateSlot candidate))) Right
                (Map.lookup position earlier)
            pure (semanticFactFingerprint (candidateOccurrence premise authority))
    requestFacts
            (CheckedPlannedVampireRequest _location _request facts) = facts
    requestIdentity
            (CheckedPlannedVampireRequest _location request _facts) =
        Provers.preparedVerificationRequestId request

    planningDirectRequests = \case
        PlanningCheckedSourceProof proofUse ->
            externalProofUseRequests proofUse
        PlanningOmitted omittedRequests -> omittedRequests
        PlanningDefinitionEquation{} -> []
        PlanningSourceAxiom -> []
        PlanningKernelConstruction{} -> []

    consumeStage safety position = do
        (premise, authority) <-
            maybe
                (Left
                    (PlanningFactContractMismatch
                        (reservedCandidateSlot candidate)))
                Right
                (Map.lookup position earlier)
        let PlannedCandidatePosition premiseStage _premiseIndex = position
            PlannedCandidatePosition currentStage _currentIndex = current
        unless (premiseStage < currentStage)
            (Left
                (StagedPremiseNotEarlier
                    (reservedCandidateSlot premise)
                    premiseStage
                    (reservedCandidateSlot candidate)
                    currentStage))
        first FactSafetyFailed
            (accumulateFactSafety
                (candidateTheoremReference builder premise)
                authority
                safety)

accumulatePlanningFact
    :: BuilderState PlanningEvidence
    -> CheckedObjectClosure
    -> CandidateSafety
    -> SemanticFactOccurrenceFingerprint
    -> Either DeclarationError CandidateSafety
accumulatePlanningFact builder closure safety fingerprint = do
    FactEntry proposition occurrence
            (PlanningEvidence authority _direct _provenance) <-
        maybe
            (Left (AuthorizedFactNotVisible fingerprint))
            Right
            (Map.lookup fingerprint (logicalBuilderFacts builder))
    unless
        ( semanticFactFingerprint occurrence == fingerprint
          && semanticFactAuthority occurrence == authority
          && propositionMatchesClosure closure proposition
        )
        (Left (PlanningFactContractMismatch (semanticFactSlot occurrence)))
    first FactSafetyFailed
        (accumulateFactSafety
            (theoremRef
                (logicalBuilderTheory builder)
                (checkedPropositionId proposition))
            authority
            safety)

validatePlanningDirect
    :: DirectAuthorization
    -> CandidateSafety
    -> Either DeclarationError ()
validatePlanningDirect direct safety =
    case direct of
        SourceAxiomAuthorization ->
            unless
                (candidateSafetyAuthority safety
                    == authoritySafety (singletonEscapeKind SourceAxiom))
                (Left
                    (ValidationCertificateFailed
                        (SourceAxiomSafetyMismatch
                            (candidateSafetyAuthority safety))))
        OmittedAuthorization ->
            unless
                (Omitted `elem` escapeKindsToList
                    (authoritySafetyEscapeKinds
                        (candidateSafetyAuthority safety)))
                (Left
                    (ValidationCertificateFailed
                        (OmittedSafetyMissing
                            (candidateSafetyAuthority safety))))
        _ -> pure ()

selectPlannedValidation
    :: CheckedDeclarationMode
    -> BuilderState PlanningEvidence
    -> [AssertedObject]
    -> [NonEmpty PreparedCandidate]
    -> DeclarationBase PlannedValidationSelection
selectPlannedValidation mode builder objects stages =
    case mode of
        CheckedProofMode syntax ->
            case concatMap toList stages of
                [planned@(PreparedCandidate _candidate authority _direct _ _)] -> do
                    let key = proofValidationKey
                            (theoremId (factAuthorityTheorem authority))
                            syntax
                            (logicalBuilderPrefix builder)
                    cached <- ValidationCache.lookupProofValidation key
                    traverse_
                        (validateProof planned syntax)
                        cached
                    pure case cached of
                        Nothing -> PlannedFreshValidation
                        Just record -> PlannedProofValidation record
                candidates ->
                    Error.throwError_
                        (CheckedProofCandidateCountMismatch
                            (length candidates))
        CheckedCompiledMode syntax -> do
            let planned = concatMap toList stages
                objectIds = assertedObjectId <$> objects
                theorems =
                    theoremId . factAuthorityTheorem . plannedAuthority
                        <$> planned
                key = declarationValidationKey syntax
                    (logicalBuilderPrefix builder) objectIds theorems
            cached <- ValidationCache.lookupDeclarationValidation key
            traverse_
                (validateCompiled planned syntax objectIds theorems)
                cached
            pure case cached of
                Nothing -> PlannedFreshValidation
                Just record -> PlannedCompiledValidation record
  where
    plannedAuthority (PreparedCandidate _ authority _ _ _) = authority

    validateProof
            (PreparedCandidate candidate authority direct _ _)
            syntax record =
        case Materialization.checkCandidateValidation
                (logicalBuilderTheory builder)
                (logicalBuilderPrefix builder)
                (candidateCheckedProposition candidate)
                authority direct
                (Materialization.candidateProofValidation record syntax) of
            Left failure ->
                throwValidationIntegrity failure
            Right () -> pure ()

    validateCompiled planned syntax objectIds theorems record = do
        case Materialization.checkDeclarationValidationRecord
                (logicalBuilderPrefix builder)
                syntax objectIds theorems record of
            Left failure ->
                throwValidationIntegrity failure
            Right () -> pure ()
        traverse_
            (\(ordinal,
                PreparedCandidate candidate authority direct _ _) ->
                case Materialization.checkCandidateValidation
                        (logicalBuilderTheory builder)
                        (logicalBuilderPrefix builder)
                        (candidateCheckedProposition candidate)
                        authority direct
                        (Materialization.candidateDeclarationValidation
                            record syntax objectIds theorems ordinal) of
                    Left failure ->
                        throwValidationIntegrity failure
                    Right () -> pure ())
            (zip [0..] planned)

submitPlannedRequests
    :: VampireResolver -> PlannedValidationSelection -> [CheckedPlannedVampireRequest]
    -> DeclarationBase [PlannedVampireDisposition]
submitPlannedRequests resolver selection requests = case selection of
    PlannedFreshValidation -> case resolver of
        VampireResolver SynchronousVampireResolution{} -> pure (PlannedSynchronousRequest <$ requests)
        VampireResolver (AsynchronousVampireSubmission submit) -> do
            handles <- case NonEmpty.nonEmpty submissions of
                Nothing -> pure []
                Just nonempty -> toList <$> liftIO (submit nonempty)
            unless (length handles == length requests)
                (Error.throwError_ (VampireResolverBatchSizeMismatch (length requests) (length handles)))
            pure (PlannedLiveRequest <$> handles)
    _ -> pure (PlannedRequestCoveredByValidation <$ requests)
  where
    submissions = [VampireSubmission location request
        | CheckedPlannedVampireRequest location request _facts <- requests]

-- Phase owners construct fact evidence before this common state extension.
-- Updating semantic indexes never creates a builder authorization.
extendDeclarationBuilder
    :: CheckedObjectClosure
    -> ResolvedEnvironment evidence
    -> DeclarationInterfaceDelta
    -> PrefixContextId
    -> [FactEntry evidence]
    -> BuilderState evidence
    -> BuilderState evidence
extendDeclarationBuilder closure environment delta next additions builder =
    builder
        { logicalBuilderPrefix = next
        , logicalBuilderObjectClosure = closure
        , logicalBuilderFacts = foldl' insertFact (logicalBuilderFacts builder) additions
        , logicalBuilderNextFact = logicalBuilderNextFact builder
            + fromIntegral (length (declarationDeltaFacts delta))
        , logicalBuilderAliases =
            foldl'
                (\entries alias ->
                    Map.insert
                        (semanticAliasName alias)
                        (ImportedAliasBinding
                            (semanticAliasTarget alias)
                            (ImportedAliasOrigin
                                (declarationDeltaSlot delta)
                                (semanticAliasTarget alias)))
                        entries)
                (logicalBuilderAliases builder)
                (declarationDeltaAliases delta)
        , logicalBuilderEnvironment = environment
        , logicalBuilderDefinitionViews =
            foldl'
                (\entries view ->
                    Map.insert
                        ( semanticDefinitionViewObject view
                        , semanticDefinitionViewKind view
                        )
                        (semanticDefinitionViewTarget view)
                        entries)
                (logicalBuilderDefinitionViews builder)
                (declarationDeltaDefinitionViews delta)
        , logicalBuilderDeltas = delta : logicalBuilderDeltas builder
        , logicalBuilderNextDeclaration =
            logicalBuilderNextDeclaration builder + 1
        , logicalBuilderNextInvocation =
            logicalBuilderNextInvocation builder + 1
        }
  where
    insertFact entries entry@(FactEntry _ occurrence _) =
        Map.insert (semanticFactFingerprint occurrence) entry entries

installDeclarationRegistrations
    :: (Registration SemanticFactOccurrenceFingerprint -> Either DeclarationError Notion.FormationRuleSource)
    -> DeclarationInterfaceDelta -> BuilderState evidence
    -> Either DeclarationError (BuilderState evidence)
installDeclarationRegistrations materialize delta builder = do
    entries <- foldM insert (logicalBuilderRegistrations builder) (declarationDeltaRegistrations delta)
    pure builder{logicalBuilderRegistrations = entries}
  where
    insert entries registration = do
        source <- materialize registration
        pure (insertBuilderRegistration (OwnedRegistrationKey (declarationDeltaSlot delta) registration, source) entries)

appendProspectiveBuilder
    :: CheckedObjectClosure
    -> ResolvedEnvironment PlanningEvidence
    -> DeclarationInterfaceDelta
    -> PrefixContextId
    -> [NonEmpty PreparedCandidate]
    -> BuilderState PlanningEvidence
    -> Either DeclarationError (BuilderState PlanningEvidence)
appendProspectiveBuilder closure environment delta next planned builder = do
    let additions = zipWith planningEntry (declarationDeltaFacts delta) (concatMap toList planned)
    base <- extendBuilderCompositions (extendDeclarationBuilder closure environment delta next additions builder) additions
    registered <- installDeclarationRegistrations
        (materializeRegistration planningEvidenceDirect (logicalBuilderObjectClosure base)
            (logicalBuilderEnvironment base) (logicalBuilderFacts base)) delta base
    pure registered
  where
    planningEntry occurrence
            (PreparedCandidate candidate authority direct _ _requests) =
        let evidence = PlanningEvidence authority
                (Just direct)
                (Just
                    (PlanningProvenance
                        (declarationDeltaSlot delta)
                        (reservedStageValue candidate)
                        (reservedCandidateSlot candidate)))
        in FactEntry (candidateCheckedProposition candidate) occurrence evidence

    -- Keep the constructor match private while storing exact stage provenance.
    reservedStageValue
            (ReservedCandidate _identity _prefix _invocation stage _slot _spec) =
        stage

-- | Admit one checked declaration through the existing authoritative
-- source-order cursor.  The callback interprets a closed family recipe over
-- freshly reserved stage slots; it is not retained in the checked value.
admitCheckedDeclaration
    :: CheckedDeclaration body
    -> (body -> [NonEmpty ReservedCandidate] -> Declaration value)
    -> ModuleDriver failure (value, CommittedDeclarationBatch)
admitCheckedDeclaration checked authorize = do
    planned <- runProspectiveLoweringDriver (planCheckedDeclaration checked)
        >>= either failDeclarationDriver pure
    admitPlannedCheckedDeclaration planned authorize

-- | Admit one retained plan against the real authorized builder.  The family
-- callback performs the existing authority checks, but every live resolver
-- result comes from the handle submitted during planning and every validation
-- lookup is the inert selection retained by the plan.
admitPlannedCheckedDeclaration
    :: PlannedDeclaration body
    -> (body -> [NonEmpty ReservedCandidate] -> Declaration value)
    -> ModuleDriver failure (value, CommittedDeclarationBatch)
admitPlannedCheckedDeclaration (PlannedDeclaration prepared selection dispositions) authorize = do
    state <- State.get
    let builder = driverBuilder state
        candidates = fmap (fmap preparedCandidateReservation) (preparedDeclarationCandidates prepared)
        requests = [request
            | candidate <- concatMap toList (preparedDeclarationCandidates prepared)
            , CheckedPlannedVampireRequest _ request _ <- preparedCandidateRequests candidate]
    validatePreparedPredecessor prepared builder
    closure <- either failDeclarationDriver pure (first DeclarationObjectValidationFailed
        (insertCheckedObjectContribution (logicalBuilderObjectClosure builder) (preparedDeclarationObjects prepared)))
    cursor <- liftIO (newIORef (zip requests dispositions))
    let initial = DeclarationState
            { declarationVampireResolver = driverResolver state
            , declarationFormationRecorder = driverFormationRecorder state
            , declarationPlannedRequests = cursor
            , declarationCandidateValidations = plannedCandidateValidations prepared selection
            , declarationBuilder = builder
            , declarationPreparedResult = prepared{preparedDeclarationBody = ()}
            , declarationObjectClosure = closure
            , declarationReservations = Map.fromList
                [(reservedCandidateSlot candidate, candidate) | candidate <- concatMap toList candidates]
            , declarationPending = Map.empty
            , declarationAuthorizationFrontier = 0
            }
        action = do
            value <- authorize (preparedDeclarationBody prepared) candidates
            validatePreparedAuthorization prepared
            pure value
    result <- inject (Error.runErrorNoCallStack (State.runState initial action))
    case result of
        Left failure -> failDeclarationDriver failure
        Right (value, completed) -> do
            remaining <- liftIO (readIORef cursor)
            unless (null remaining)
                (throwPlanningIntegrity "admission did not consume every planned request")
            (registered, batch) <- either failDeclarationDriver pure (appendPreparedDeclaration completed)
            compiled <- FormationDiagnostics.withPhase (driverFormationRecorder state) FormationDiagnostics.DeclarationPreparation
                (recordPreparedFormation (driverFormationRecorder state)
                    (prepareOwnedFormationRules builderEvidenceDirect (preparedDeclarationDelta prepared) registered))
            builder' <- either failDeclarationDriver pure compiled
            validateSelectedValidation selection batch
            State.put state{driverBuilder = builder', driverPendingPrefix = appendPendingBatch batch (driverPendingPrefix state)}
            pure (value, batch)

-- The plan has already checked these records against its fixed inventory.
-- Admission derives each candidate's view once; actual proof authority is
-- checked against that view when the candidate completes.
plannedCandidateValidations
    :: PreparedDeclaration body -> PlannedValidationSelection
    -> Map FactSlot Materialization.CandidateValidation
plannedCandidateValidations prepared selection =
    case (preparedDeclarationMode prepared, selection) of
        (_, PlannedFreshValidation) -> Map.empty
        (CheckedProofMode syntax, PlannedProofValidation record) ->
            Map.fromList [(slot, Materialization.candidateProofValidation record syntax) | slot <- slots]
        (CheckedCompiledMode syntax, PlannedCompiledValidation record) ->
            let objects = declarationDeltaObjects (preparedDeclarationDelta prepared)
                theorems = theoremId . factAuthorityTheorem . preparedCandidateAuthority <$> candidates
            in Map.fromList
                [(slot, Materialization.candidateDeclarationValidation record syntax objects theorems ordinal)
                | (slot, ordinal) <- zip slots [0 ..]]
        _ -> impossible "a prepared declaration changed its validation mode"
  where
    candidates = concatMap toList (preparedDeclarationCandidates prepared)
    slots = reservedCandidateSlot . preparedCandidateReservation <$> candidates

validatePreparedPredecessor :: MonadIO m => PreparedDeclaration body -> LogicalBuilder -> m ()
validatePreparedPredecessor prepared builder =
    unless (preparedDeclarationIdentity prepared == logicalBuilderIdentity builder
        && preparedDeclarationTheory prepared == logicalBuilderTheory builder
        && preparedDeclarationPrevious prepared == logicalBuilderPrefix builder
        && declarationDeltaSlot (preparedDeclarationDelta prepared)
            == declarationSlot (logicalBuilderOwner builder) (localDeclarationOrdinal (logicalBuilderNextDeclaration builder)))
        (throwPlanningIntegrity "planned declaration predecessor does not match the admitted builder")

validatePreparedAuthorization :: PreparedDeclaration body -> Declaration ()
validatePreparedAuthorization prepared = do
    declaration <- State.get
    let pending = Map.elems (declarationPending declaration)
        contracts = concatMap toList (preparedDeclarationCandidates prepared)
    unless (Map.keysSet (declarationPending declaration) == Map.keysSet (declarationReservations declaration))
        (failDeclaration DeclarationHasUnauthorizedCandidates)
    unless (declarationAuthorizationFrontier declaration == declarationNextStage declaration)
        (failDeclaration DeclarationAuthorizationFrontierIncomplete)
    traverse_ (liftEitherEffect . validatePendingAuthorization declaration) pending
    unless (length contracts == length pending)
        (throwPlanningIntegrity "admission changed the reserved candidate inventory")
    traverse_ validateContract (zip contracts pending)
  where
    validateContract (contract, PendingCandidate actual certificate (PendingFactAuthorization _ _ _ _ _ _ imports consumed)) = do
        let expected = preparedCandidateReservation contract
            dependencies = preparedCandidateDependencies contract
            ReservedCandidate _ _ _ _ _ spec = expected
        unless (actual == expected
            && validationTarget certificate == preparedCandidateAuthority contract
            && validationDirectAuthorization certificate == preparedCandidateDirect contract
            && candidateOccurrence actual (validationTarget certificate)
                == candidateOccurrence expected (preparedCandidateAuthority contract)
            && candidateAliases actual == candidateAliases expected
            && consumed == Set.fromList dependencies
            && case candidateSpecPurpose spec of
                StructureFactPurpose{} -> imports == (Just <$> dependencies)
                GeneralFactPurpose -> True)
            (throwPlanningIntegrity "admitted declaration differs from its prospective contract")

-- Candidate execution carries the declaration's cursor explicitly. Cached
-- tasks consume exact descriptions too; they do not call a resolver.
resolveDeclarationVampireRequests
    :: DeclarationState
    -> NonEmpty (Provers.PreparedTypedProverTask SemanticFactOccurrenceFingerprint local origin ObjectId, Bool)
    -> DeclarationBase [Provers.VampireResolution]
resolveDeclarationVampireRequests declaration inputs = do
    expected <- liftIO (atomicModifyIORef' (declarationPlannedRequests declaration) \remaining ->
        let (selected, later) = splitAt (NonEmpty.length inputs) remaining
        in (later, selected))
    unless (length expected == NonEmpty.length inputs)
        (throwPlanningIntegrity "admission requested a different number of planned Vampire results")
    traverse_ validateExpected (zip (toList inputs) expected)
    let live = [(task, request, disposition)
            | ((task, cached), (request, disposition)) <- zip (toList inputs) expected, not cached]
    case NonEmpty.nonEmpty live of
        Nothing -> pure []
        Just tasks
            | all isLive tasks -> liftIO (traverse awaitOne (toList tasks))
            | all isSynchronous tasks -> do
                results <- liftIO (resolveSynchronousVampireBatch (declarationVampireResolver declaration)
                    (fmap (\(task, _, _) -> task) tasks))
                liftEitherEffect (validateVampireResolverResultCount (NonEmpty.length tasks) results)
            | otherwise -> throwPlanningIntegrity "planned resolver batch mixed execution modes"
  where
    validateExpected ((task, cached), (request, disposition)) = do
        unless (Provers.preparedTypedProverRequest task == request)
            (throwPlanningIntegrity "admission request differs from its planned exact request")
        let covered = case disposition of
                PlannedRequestCoveredByValidation -> True
                _ -> False
        unless (cached == covered)
            (throwPlanningIntegrity "admission changed a planned request's validation disposition")
    awaitOne (_, request, PlannedLiveRequest handle) = Provers.awaitPreparedVampireRequest request handle
    awaitOne _ = impossible "validated live resolver batch changed execution mode"
    isLive (_, _, PlannedLiveRequest{}) = True
    isLive _ = False
    isSynchronous (_, _, PlannedSynchronousRequest) = True
    isSynchronous _ = False

validateSelectedValidation
    :: MonadIO m => PlannedValidationSelection -> CommittedDeclarationBatch -> m ()
validateSelectedValidation selection batch =
    unless (case selection of
        PlannedFreshValidation -> True
        PlannedProofValidation record -> committedBatchProofValidations batch == [record]
        PlannedCompiledValidation record -> committedBatchDeclarationValidation batch == Just record)
        (throwPlanningIntegrity "admission changed the selected validation record")

appendPreparedDeclaration
    :: DeclarationState -> Either DeclarationError (LogicalBuilder, CommittedDeclarationBatch)
appendPreparedDeclaration declaration = do
    let prepared = declarationPreparedResult declaration
        builder = declarationBuilder declaration
        delta = preparedDeclarationDelta prepared
        pending = Map.elems (declarationPending declaration)
        previous = preparedDeclarationPrevious prepared
        next = preparedDeclarationNext prepared
    let closure = declarationObjectClosure declaration
    let attach occurrence (contract, PendingCandidate _ certificate _) =
            FactEntry (candidateCheckedProposition (preparedCandidateReservation contract)) occurrence
                (BuilderFactAuthorization (logicalBuilderIdentity builder) (semanticFactSlot occurrence) certificate)
        entries = zipWith attach (declarationDeltaFacts delta)
            (zip (concatMap toList (preparedDeclarationCandidates prepared)) pending)
        base = extendDeclarationBuilder closure (logicalBuilderEnvironment builder) delta next entries builder
        PreparedDeclarationEnvironment structures globals definitions = preparedDeclarationEnvironment prepared
    rebound <- first StructureInterfaceInvalid (traverse
        (StructureInterface.rebindStructureInterfaceEvidence planningEvidenceDirect builderEvidenceDirect
            (structureOccurrenceRegistry (logicalBuilderFacts base))) structures)
    withStructures <- insertResolvedEnvironmentStructures (logicalBuilderEnvironment base) rebound
    withGlobals <- foldM insertResolvedEnvironmentGlobal withStructures globals
    let environment = installRecursiveDefinitions definitions withGlobals
    (proofs, compiled) <- buildValidationRecords (preparedDeclarationMode prepared)
        previous (declarationDeltaObjects delta) pending
    withCompositions <- extendBuilderCompositions base{logicalBuilderEnvironment = environment} entries
    complete <- installAdmittedRegistrations delta withCompositions
    pure (complete, committedDeclarationBatch (logicalBuilderOwner builder) (declarationDeltaSlot delta)
        previous next delta (preparedObjectAssertions prepared) (preparedDeclarationPropositions prepared) proofs compiled)

-- Canonical views are derived from the checked direct-authorization
-- contract, rather than separately declared metadata.  This keeps one source
-- of truth for which facts are definition evidence.
deriveCanonicalDefinitionViews
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> [(ReservedCandidate, FactAuthority, DirectAuthorization)]
    -> Either DeclarationError [SemanticDefinitionView]
deriveCanonicalDefinitionViews builder closure candidates =
    fmap (List.sortOn viewKey . reverse . snd)
        (foldM insertView (Map.empty, []) candidates)
  where
    viewKey view =
        ( semanticDefinitionViewObject view
        , semanticDefinitionViewKind view
        )

    insertView accumulator@(current, views)
            (candidate, authority, direct) = do
        resolved <- directView direct
        case resolved of
            Nothing -> pure accumulator
            Just (object, kind) -> do
                unless
                    (isJust (lookupCheckedObjectContent object closure))
                    (Left (DefinitionViewObjectMissing object))
                let occurrence = candidateOccurrence candidate authority
                    fingerprint = semanticFactFingerprint occurrence
                    proposition = candidateCheckedProposition candidate
                    key = (object, kind)
                    view = DefinitionView.definitionView object kind fingerprint
                case Map.lookup key current of
                    Just (existing, existingProposition) -> do
                        requireEquivalent
                            object kind existing fingerprint
                            existingProposition proposition
                        pure accumulator
                    Nothing ->
                        case Map.lookup key
                                (logicalBuilderDefinitionViews builder) of
                            Nothing ->
                                pure
                                    ( Map.insert key
                                        (fingerprint, proposition)
                                        current
                                    , view : views
                                    )
                            Just existing -> do
                                existingProposition <-
                                    maybe
                                        (Left
                                            (DefinitionViewConflict
                                                object kind
                                                existing fingerprint))
                                        (\(FactEntry checked
                                                _occurrence _evidence) ->
                                            pure checked)
                                        (Map.lookup existing
                                            (logicalBuilderFacts builder))
                                requireEquivalent
                                    object kind existing fingerprint
                                    existingProposition proposition
                                pure accumulator

    requireEquivalent object kind existing supplied
            existingProposition suppliedProposition =
        unless
            (checkedPropositionId existingProposition
                == checkedPropositionId suppliedProposition)
            (Left
                (DefinitionViewConflict
                    object kind existing supplied))

    directView = \case
        CheckedKernelConstruction
                (CheckedDefinitionEquation object) ->
            case lookupCheckedObjectContent object closure of
                Nothing -> Left (DefinitionViewObjectMissing object)
                Just content ->
                    case content of
                        TransparentObjectContent _theory coreType _body ->
                            pure
                                (Just
                                    ( object
                                    , case firstOrderSymbolShape coreType of
                                        Just{} -> DefinitionPointwiseView
                                        Nothing -> DefinitionExactView
                                    ))
                        _ -> Left (DefinitionViewObjectMissing object)
        CheckedKernelConstruction
                (CheckedSetConstructionExtensionality object _descriptor) ->
            pure (Just (object, DefinitionMembershipView))
        _ -> pure Nothing

-- Each adapter supplies evidence from its own private registry. Structural
-- contracts and globals are completed together before any builder is published.
buildCheckedDeclarationDelta
    :: BuilderState evidence
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> [SemanticFactOccurrence]
    -> [SemanticAlias]
    -> [ObjectId]
    -> [PropositionId]
    -> [SemanticDefinitionView]
    -> [Registration SemanticFactOccurrenceFingerprint]
    -> [SemanticGlobalBinding]
    -> [RecursionInterface.CheckedRecursiveDefinition]
    -> (evidence -> Maybe DirectAuthorization)
    -> StructureCandidateMap evidence
    -> Maybe StructureBatch.PendingStructureBatch
    -> Except.ExceptT DeclarationError LoweringDriver (ResolvedEnvironment evidence, PreparedDeclarationEnvironment evidence, DeclarationInterfaceDelta, PrefixContextId)
buildCheckedDeclarationDelta builder closure slot occurrences aliases objectIds propositionIds
        definitionViews registrations
        reversedBindings definitions direct candidates batch = do
    let bindings = List.sortOn semanticGlobalBindingKey (reverse reversedBindings)
    Except.liftEither $ traverse_ (\view -> unless (checkedObjectMember (semanticDefinitionViewObject view) closure)
        (Left (DefinitionViewObjectMissing (semanticDefinitionViewObject view)))) definitionViews
    (withStructures, wires, interfaces) <- Except.liftEither $ case batch of
        Nothing -> do
            unless (all ((== GeneralFactPurpose) . semanticFactPurpose) occurrences)
                (Left (StructureDeclarationInvalid "a structural law occurrence has no owning batch"))
            pure (logicalBuilderEnvironment builder, [], [])
        Just pending -> checkFreshStructureEffect builder closure slot direct candidates occurrences aliases registrations pending
    Except.liftEither $ traverse_ (\binding -> first
        (DeclarationGlobalTargetInvalid (semanticGlobalBindingKey binding) (semanticGlobalBindingTarget binding))
        (validateSemanticGlobalBindingTarget (environmentOperations withStructures) closure binding)) bindings
    environment <- Except.liftEither $ first DeclarationEnvironmentFailed (semanticEnvironmentWithStructures bindings wires)
    delta <- Except.liftEither $ first DeclarationInterfaceFailed (declarationInterfaceDelta slot occurrences aliases objectIds propositionIds
        definitionViews registrations environment)
    Except.liftEither (validateBuilderCollisions builder delta)
    let (materialized, used) = materializeSemanticEnvironmentDeltaMeasured
            (`Map.lookup` environmentBindings withStructures)
            (lookupEnvironmentRegistration (environmentStructures withStructures))
            (`Map.lookup` environmentFields withStructures)
            (visibleRecordShapeKeys (environmentStructures withStructures)) closure slot environment
    let measure = do
            recorder <- formationRecorderLowering
            recordPreparedFormation recorder (materialized, expansionAdmissionMeasurement used)
    admittedBindings <- Trans.lift $ if any (isJust . semanticGlobalBindingExpansion) bindings
        then withFormationPhaseLowering FormationDiagnostics.DeclarationPreparation measure
        else pure materialized
    resolved <- Except.liftEither $ first (\(SemanticEnvironmentBindingMaterializationFailed reference failure) ->
        GlobalFormationContractInvalid reference failure) admittedBindings
    admitted <- Except.liftEither $ foldM insertResolvedEnvironmentGlobal withStructures resolved
    pure (installRecursiveDefinitions definitions admitted, PreparedDeclarationEnvironment interfaces resolved definitions,
        delta, nextPrefixContextId (logicalBuilderPrefix builder) delta)

planningEvidenceDirect :: PlanningEvidence -> Maybe DirectAuthorization
planningEvidenceDirect (PlanningEvidence _ direct _) = direct

builderEvidenceDirect :: BuilderFactAuthorization -> Maybe DirectAuthorization
builderEvidenceDirect (BuilderFactAuthorization _ _ certificate) = Just (validationDirectAuthorization certificate)

structureOccurrenceRegistry
    :: Map SemanticFactOccurrenceFingerprint (FactEntry evidence)
    -> Map SemanticFactOccurrenceFingerprint (StructureInterface.StructureOccurrence evidence)
structureOccurrenceRegistry = Map.map (\(FactEntry proposition occurrence evidence) ->
    StructureInterface.StructureOccurrence proposition occurrence evidence)

plannedStructureCandidates
    :: BuilderState PlanningEvidence -> [NonEmpty PreparedCandidate]
    -> Either DeclarationError (StructureCandidateMap PlanningEvidence)
plannedStructureCandidates builder planned = pure (Map.fromList
    [(PlannedCandidatePosition stage index,
        (StructureInterface.StructureOccurrence (candidateCheckedProposition candidate)
            (candidateOccurrence candidate authority)
            (PlanningEvidence authority (Just direct) (Just (PlanningProvenance
                (declarationSlot (logicalBuilderOwner builder) (localDeclarationOrdinal (logicalBuilderNextDeclaration builder)))
                (CandidateStage stage) (reservedCandidateSlot candidate)))), Just <$> dependencies))
    | (stage, candidates) <- zip [0 ..] planned
    , (index, PreparedCandidate candidate authority direct dependencies _) <- zip [0 ..] (toList candidates)])

type StructureCandidateMap evidence = Map PlannedCandidatePosition
    (StructureInterface.StructureOccurrence evidence, [Maybe SemanticFactOccurrenceFingerprint])

lookupEnvironmentRegistration
    :: StructureEnvironment.StructureEnvironment evidence -> StructureId
    -> Maybe StructurePredicate.PendingStructureRegistration
lookupEnvironmentRegistration environment identity = StructureInterface.structureInterfaceRegistration
    <$> StructureEnvironment.lookupStructureById identity environment

canonicalPredicateResource
    :: StructureEnvironment.StructureEnvironment evidence -> ObjectId
    -> Maybe (StructureInterface.StructureOccurrence evidence)
canonicalPredicateResource environment predicate = listToMaybe
    [occurrence | interface <- Map.elems (StructureEnvironment.structureEnvironmentInterfaces environment)
    , StructurePredicate.pendingStructurePredicate (StructureInterface.structureInterfaceRegistration interface) == predicate
    , occurrence <- maybeToList (StructureInterface.lookupStructureOccurrence
        (Schema.StructureResourceFact Schema.PredicateDefinitionResource) interface)]

checkFreshStructureEffect
    :: BuilderState evidence -> CheckedObjectClosure -> DeclarationSlot
    -> (evidence -> Maybe DirectAuthorization) -> StructureCandidateMap evidence
    -> [SemanticFactOccurrence] -> [SemanticAlias] -> [Registration SemanticFactOccurrenceFingerprint] -> StructureBatch.PendingStructureBatch
    -> Either DeclarationError (ResolvedEnvironment evidence, [StructureInterfaceWire], [StructureInterface.CheckedStructureInterface evidence])
checkFreshStructureEffect builder closure slot direct candidates occurrences aliases views batch = do
    let registrations = StructureBatch.pendingBatchRegistrations batch
        positions = StructureBatch.pendingBatchLawPositions batch
        resources = StructureBatch.pendingBatchResourceReferences batch
        indexed = Map.fromList [(Schema.resolvedSchemaId (StructurePredicate.pendingStructureSchema registration), registration)
            | registration <- toList registrations]
    traverse_ (\input -> unless
        (Schema.localSchemaOrigin input == StructureOrigin (declarationSlotModule slot) (declarationSlotOrdinal slot)
            (structureOriginSlot (Schema.localSchemaOrigin input)))
        (invalid "a structure batch belongs to another declaration")) (StructureBatch.pendingBatchInputs batch)
    resourceRows <- Map.traverseWithKey (resolveResources indexed) resources
    lawRows <- Map.traverseWithKey (\_ position -> fst <$> requireCandidate position) positions
    let supplied = Map.unionWith Map.union
            (Map.fromListWith Map.union [(owner, Map.singleton (Schema.StructureLawFact key) occurrence)
                | (Schema.StructureLawId owner key, occurrence) <- Map.toAscList lawRows])
            (Map.map (Map.mapKeys Schema.StructureResourceFact) resourceRows)
        indexedLawFingerprints = Set.fromList (occurrenceFingerprint <$> Map.elems lawRows)
    unless (Set.fromList [semanticFactFingerprint occurrence | occurrence <- occurrences
            , StructureFactPurpose{} <- [semanticFactPurpose occurrence]] == indexedLawFingerprints)
        (invalid "structural fact purposes and the local law inventory disagree")
    (interfaces, dependencies) <- first StructureInterfaceInvalid
        (StructureInterface.checkStructureInterfacesWithDependencies (logicalBuilderFoundation builder) closure direct
            (\identity -> StructureEnvironment.lookupStructureById identity incoming)
            (StructureBatch.pendingBatchInputs batch) registrations supplied)
    for_ (Map.toAscList dependencies) \(law, expected) -> do
        position <- maybe (invalid "a generated law lost its candidate position") Right (Map.lookup law positions)
        (_, actual) <- requireCandidate position
        for_ expected \dependency -> do
            let earlier = case dependency of
                    StructureLaws.EnvironmentDependency _ _ -> Nothing
                    StructureLaws.BatchDependency owner (Schema.StructureLawFact key) ->
                        Map.lookup (Schema.StructureLawId owner key) positions
                    StructureLaws.BatchDependency owner (Schema.StructureResourceFact key) ->
                        case Map.lookup owner resources >>= Map.lookup key of
                            Just (LocalCandidateReference dependencyPosition) -> Just dependencyPosition
                            _ -> Nothing
            for_ earlier \dependencyPosition -> unless
                (plannedCandidateStage dependencyPosition < plannedCandidateStage position)
                (invalid "a generated law depends on a resource or law outside an earlier stage")
        fingerprints <- traverse (resolveDependency supplied) expected
        unless (actual == (Just <$> fingerprints)) (invalid "a generated law used different ordered proof imports")
    validateGeneratedStructureViews incoming interfaces views
    validateGeneratedStructureAliases interfaces aliases
    environment <- insertResolvedStructureInterfaces slot (logicalBuilderEnvironment builder) interfaces
    wires <- for (toList (StructureBatch.pendingBatchInputs batch)) \input -> do
        interface <- maybe (invalid "a checked local interface disappeared") Right
            (find ((== Schema.localSchemaId input) . Schema.resolvedSchemaId . StructurePredicate.pendingStructureSchema
                . StructureInterface.structureInterfaceRegistration) interfaces)
        first StructureDeclarationInvalid (structureInterfaceWire input (StructureInterface.structureInterfaceRegistration interface)
            (StructureInterface.structureInterfaceLawIndex interface) (StructureInterface.structureInterfaceResourceIndex interface))
    pure (environment, List.sortOn structureWireSlot wires, toList interfaces)
  where
    incoming = logicalBuilderStructures builder
    invalid = Left . StructureDeclarationInvalid
    requireCandidate position = maybe (invalid "a structure reference names a missing candidate") Right (Map.lookup position candidates)
    resolveReference = \case
        LocalCandidateReference position -> fst <$> requireCandidate position
        EnvironmentOccurrenceReference fingerprint -> case Map.lookup fingerprint (logicalBuilderFacts builder) of
            Just (FactEntry proposition metadata evidence) -> pure (StructureInterface.StructureOccurrence proposition metadata evidence)
            Nothing -> invalid "a structure resource occurrence is not visible in this evidence phase"
    resolveResources indexed owner references = do
        registration <- maybe (invalid "a resource index has no owning registration") Right (Map.lookup owner indexed)
        Map.traverseWithKey (resolveResource registration) references
    resolveResource registration key reference = do
        occurrence <- resolveReference reference
        let schema = StructurePredicate.pendingStructureSchema registration
            owner = Schema.resolvedSchemaId schema
        case key of
            Schema.PredicateDefinitionResource -> case reference of
                LocalCandidateReference position -> requireNoImports position
                EnvironmentOccurrenceReference fingerprint -> do
                    case canonicalPredicateResource incoming (StructurePredicate.pendingStructurePredicate registration) of
                        Just selected -> unless (occurrenceFingerprint selected == fingerprint)
                            (invalid "a reused predicate definition names a different indexed provider")
                        Nothing -> invalid "a reused predicate definition has no indexed provider"
            _ -> do
                let fieldId' = case key of
                        Schema.SelectorDefinitionResource field -> field
                        Schema.ProjectionMembershipResource field -> field
                field <- maybe (invalid "a resource names a field outside its schema") Right (Map.lookup fieldId' (Schema.resolvedSchemaFields schema))
                if Schema.resolvedFieldOwner field == owner then case reference of
                    LocalCandidateReference position -> requireNoImports position
                    EnvironmentOccurrenceReference{} -> invalid "a fresh field resource cannot come from the incoming environment"
                else do
                    let provider = Schema.resolvedFieldOwner field
                    expected <- case Map.lookup provider (StructureBatch.pendingBatchResourceReferences batch) >>= Map.lookup key of
                        Just providerReference -> resolveReference providerReference
                        Nothing -> requireEnvironmentFact provider (Schema.StructureResourceFact key)
                    unless (occurrenceFingerprint expected == occurrenceFingerprint occurrence)
                        (invalid "an inherited field resource names a different indexed occurrence")
        pure occurrence
    requireNoImports position = do
        (_, imports) <- requireCandidate position
        unless (null imports) (invalid "a canonical structure resource has unexpected fact imports")
    requireEnvironmentFact owner key = maybe (invalid "an incoming structure dependency has no exact indexed occurrence") Right
        (StructureEnvironment.lookupStructureById owner incoming >>= StructureInterface.lookupStructureOccurrence key)
    resolveDependency supplied = \case
        StructureLaws.BatchDependency owner key -> occurrenceFingerprint <$>
            maybe (invalid "a generated law has no batch dependency association") Right (Map.lookup owner supplied >>= Map.lookup key)
        StructureLaws.EnvironmentDependency owner key -> occurrenceFingerprint <$> requireEnvironmentFact owner key

occurrenceFingerprint :: StructureInterface.StructureOccurrence evidence -> SemanticFactOccurrenceFingerprint
occurrenceFingerprint = semanticFactFingerprint . StructureInterface.structureOccurrenceMetadata

validateGeneratedStructureAliases
    :: NonEmpty (StructureInterface.CheckedStructureInterface evidence)
    -> [SemanticAlias] -> Either DeclarationError ()
validateGeneratedStructureAliases interfaces aliases =
    for_ interfaces \interface -> do
        let schema = StructurePredicate.pendingStructureSchema (StructureInterface.structureInterfaceRegistration interface)
        for_ (Map.toAscList (StructureInterface.structureInterfaceLawIndex interface)) \(law, fingerprint) -> do
            let expected = snd (StructureLaws.structureLawPresentation schema law)
                actual = [semanticAliasName alias | alias <- aliases, semanticAliasTarget alias == fingerprint]
            unless (List.sort actual == List.sort expected)
                (Left (StructureDeclarationInvalid "generated law aliases differ from checked source presentation"))

validateGeneratedStructureViews
    :: StructureEnvironment.StructureEnvironment evidence
    -> NonEmpty (StructureInterface.CheckedStructureInterface evidence)
    -> [Registration SemanticFactOccurrenceFingerprint] -> Either DeclarationError ()
validateGeneratedStructureViews incoming interfaces supplied = do
    expected <- fmap concat (traverse viewsFor interfaces)
    unless (List.sort expected == List.sort [registration | registration <- supplied, RegisterNotionView{} <- [registrationBody registration]])
        (Left (StructureDeclarationInvalid "generated notion views differ from the exact eligible direct-parent inventory"))
  where
    registrations = Map.fromList [(Schema.resolvedSchemaId (StructurePredicate.pendingStructureSchema registration), registration)
        | interface <- toList interfaces, let registration = StructureInterface.structureInterfaceRegistration interface]
    viewsFor interface = do
        let registration = StructureInterface.structureInterfaceRegistration interface
            schema = StructurePredicate.pendingStructureSchema registration
            arguments = Vector.fromList [TemplateVariable (ViewVariableIx ordinal)
                | ordinal <- reverse [0 .. Schema.resolvedSchemaParameterCount schema]]
        fmap catMaybes $ for (Set.toAscList (Schema.resolvedSchemaDirectParents schema)) \application -> do
            variables <- first (StructureDeclarationInvalid . Text.pack . show) (StructureLaws.inheritanceViewVariables schema application)
            for variables \parentArguments -> do
                parent <- maybe (Left (StructureDeclarationInvalid "a direct-parent view has no registration")) Right
                    (Map.lookup (Schema.structureApplicationId application) registrations
                        <|> lookupEnvironmentRegistration incoming (Schema.structureApplicationId application))
                fingerprint <- maybe (Left (StructureDeclarationInvalid "a direct-parent view has no indexed theorem")) Right
                    (Map.lookup (Schema.ParentInheritanceLaw application) (StructureInterface.structureInterfaceLawIndex interface))
                pure (Registration fingerprint Notion.ConjunctionHere (RegisterNotionView (NotionViewRule
                    (StructureNotionViewPremise (pendingStructureNotionHead registration) arguments)
                    (AtomicLeaf (StructureAtomTemplate (pendingStructureNotionHead parent)
                        (Vector.cons (TemplateVariable (ViewVariableIx (Schema.resolvedSchemaParameterCount schema))) (TemplateVariable <$> parentArguments)))))))

validatePendingAuthorization
    :: DeclarationState
    -> PendingCandidate
    -> Either DeclarationError ()
validatePendingAuthorization declaration
        (PendingCandidate candidate certificate authorization) = do
    validateReservedCandidate declaration candidate
    let builder = declarationBuilder declaration
        PendingFactAuthorization
            identity prefix invocation slot authority stage _imports _dependencies =
                authorization
    unless
        ( identity == logicalBuilderIdentity builder
          && prefix == logicalBuilderPrefix builder
          && invocation == declarationInvocation declaration
          && slot == reservedCandidateSlot candidate
          && authority == validationTarget certificate
          && stage == reservedStage candidate
        )
        (Left PendingFactAuthorizationMismatch)

buildValidationRecords
    :: CheckedDeclarationMode
    -> PrefixContextId
    -> [ObjectId]
    -> [PendingCandidate]
    -> Either
        DeclarationError
        ([ProofValidationRecord], Maybe DeclarationValidationRecord)
buildValidationRecords mode prefix objects pending =
    case mode of
        CheckedProofMode syntax ->
            case pending of
                [PendingCandidate _ certificate _] ->
                    let authority = validationTarget certificate
                        key =
                            proofValidationKey
                                (theoremId
                                    (factAuthorityTheorem authority))
                                syntax
                                prefix
                    in Right
                        ( [proofValidationRecord key certificate]
                        , Nothing
                        )
                _ ->
                    Left ProofDeclarationMustProduceOneFact
        CheckedCompiledMode syntax ->
            let certificates =
                    [ certificate
                    | PendingCandidate _ certificate _ <- pending
                    ]
                theorems =
                    theoremId
                        . factAuthorityTheorem
                        . validationTarget
                        <$> certificates
                key =
                    declarationValidationKey
                        syntax prefix objects theorems
            in Right
                ( []
                , Just
                    (declarationValidationRecord
                        key certificates)
                )

validateBuilderCollisions
    :: BuilderState evidence
    -> DeclarationInterfaceDelta
    -> Either DeclarationError ()
validateBuilderCollisions builder delta = do
    traverse_
        (\occurrence ->
            when
                (Map.member
                    (semanticFactFingerprint occurrence)
                    (logicalBuilderFacts builder))
                (Left
                    (BuilderFactCollision
                        (semanticFactFingerprint occurrence))))
        (declarationDeltaFacts delta)
    traverse_
        (\alias ->
            when
                (Map.member
                    (semanticAliasName alias)
                    (logicalBuilderAliases builder))
                (Left
                    (BuilderAliasCollision
                        (semanticAliasName alias))))
        (declarationDeltaAliases delta)
    traverse_
        (\identity ->
            when
                (checkedObjectMember identity
                    (logicalBuilderObjectClosure builder))
                (Left (BuilderObjectCollision identity)))
        (declarationDeltaObjects delta)
    traverse_
        (\binding ->
            case Map.lookup
                    (semanticGlobalBindingKey binding)
                    (logicalBuilderGlobals builder) of
                Nothing -> pure ()
                Just existing ->
                    Left
                        (BuilderGlobalCollision
                            (semanticGlobalBindingKey binding)
                            existing))
        (semanticEnvironmentBindings
            (declarationDeltaEnvironment delta))

installAdmittedRegistrations :: DeclarationInterfaceDelta -> LogicalBuilder -> Either DeclarationError LogicalBuilder
installAdmittedRegistrations delta base = do
    registered <- installDeclarationRegistrations materializeAdmitted delta base
    pure registered
  where
    materializeAdmitted registration = do
        case registrationBody registration of
            RegisterNotionView{} -> do
                let fingerprint = registrationSource registration
                FactEntry _ occurrence _ <- maybe (Left (ImportedNotionViewFactMissing fingerprint)) Right
                    (Map.lookup fingerprint (logicalBuilderFacts base))
                case semanticFactPurpose occurrence of
                    GeneralFactPurpose -> pure ()
                    StructureFactPurpose _ -> case checkedNotionViewTheorem base fingerprint of
                        Just (CheckedNotionViewTheorem _ metadata) | metadata == occurrence -> pure ()
                        _ -> Left (ImportedNotionViewAuthorityInvalid fingerprint)
            _ -> pure ()
        materializeRegistration builderEvidenceDirect (logicalBuilderObjectClosure base)
            (logicalBuilderEnvironment base) (logicalBuilderFacts base) registration

stableUniqueBy :: Ord key => (value -> key) -> [value] -> [value]
stableUniqueBy key =
    reverse . snd
        . foldl'
            (\(seen, values) value ->
                let identity = key value
                in if identity `Set.member` seen
                    then (seen, values)
                    else
                        ( Set.insert identity seen
                        , value : values
                        ))
            (Set.empty, [])


data DeclarationError
    = FormationRegistrationPreparationFailed !DeclarationSlot !Text
    | FormationRegistrationPreparationLimitExceeded !DeclarationSlot !Natural !Natural !Natural
    | ImportedEvidenceTheoryMismatch !TheoryId !TheoryId
    | ImportedEvidenceLocalInvariant !Text
    | CandidateOutsideDeclaration !FactSlot
    | CandidateAlreadyAuthorized !FactSlot
    | CandidateOutsideAuthorizationFrontier
        !FactSlot !Natural !Natural
    | DeclarationHasUnauthorizedCandidates
    | DeclarationAuthorizationFrontierIncomplete
    | CandidatePropositionNotClosed
    | CandidatePropositionNotProposition !CoreType
    | StagedPremiseNotEarlier
        !FactSlot !Natural !FactSlot !Natural
    | StagedPremiseNotAuthorized !FactSlot
    | AuthorizedFactNotVisible
        !SemanticFactOccurrenceFingerprint
    | BuilderFactAuthorizationMismatch
    | PendingFactAuthorizationMismatch
    | PlanningFactContractMismatch !FactSlot
    | CheckedAuthorizationCandidateShapeMismatch !Int !Int
    | CheckedProofCandidateCountMismatch !Int
    | LocalClaimOutsideCandidate
    | FactSafetyFailed !FactSafetyError
    | ValidationCertificateFailed !ValidationCertificateError
    | DerivationImportFailed !DerivationImportError
    | KernelCompletionFailed !KernelReplayError
    | KernelDischargeImportMismatch !(Set ImportIx) !(Set ImportIx)
    | KernelDischargeFoundationUse
    | KernelDischargeGuardedRuleUse
    | KernelObviousImportPolicyMismatch
    | KernelCompositionImportPolicyMismatch
    | KernelAssumptionImportUse
    | KernelAssumptionEvidenceMissing
    | KernelDefinitionEvidenceMissing
    | KernelNotionEvidenceMismatch
    | KernelExtensionalityEvidenceMismatch
    | KernelExtensionalityImportMismatch
    | KernelExtensionalityAuthorityMismatch
    | KernelProofBuildFailed !KernelProof.KernelProofBuildError
    | DefinitionResultFormationProofFailed !Notion.FormationProofError
    | DefinitionResultFormationTargetMismatch
    | KernelConstructionDescriptorMismatch
    | DefinitionEquationObjectMissing !ObjectId
    | DefinitionEquationObjectNotTransparent !ObjectId
    | DefinitionEquationObjectNotUnaryPredicate !ObjectId
    | DefinitionEquationCandidateMismatch
    | DefinitionViewObjectMissing !ObjectId
    | DefinitionViewConflict
        !ObjectId !DefinitionViewKind
        !SemanticFactOccurrenceFingerprint
        !SemanticFactOccurrenceFingerprint
    | NotionViewCandidateMissing !PlannedCandidatePosition
    | NotionViewAuthorityInvalid !PlannedCandidatePosition
    | GeneratedFactNotVisible !(FrozenCheckedCore ObjectId)
    | ProofObligationFailedAt !Location !DeclarationError
    | ProofObligationGoal !(ScopedCheckedCore ObjectId) !DeclarationError
    | RecordObligationFailure !Obligation.ObligationContext !DeclarationError
    | ProofPreparationExhausted !Preparation.PreparationStatistics !DeclarationError
    | VampireObligationFailed !Provers.FailedVampireResolution
    | VampireProofHasNoAcceptedObligations
    | VampireCandidateBatchMismatch ![FactSlot] ![FactSlot]
    | VampireCandidateBatchProofShapeMismatch !FactSlot
    | VampireResolverBatchSizeMismatch !Int !Int
    | OmittedProofDidNotRecordUse
    | VampireRequestMismatch
    | VampireTargetMismatch
    | VampireLocalPremisesNotSupported
    | VampireGlobalTypeMismatch !ObjectId
    | VampirePremiseMismatch
        !SemanticFactOccurrenceFingerprint
    | VampirePremiseCapabilityMismatch
        !SemanticFactOccurrenceFingerprint
    | VampireFoundationMismatch !FoundationAxiomTag
    | VampireLogicalSelectionMismatch !CoreType
    | CurrentCandidateVampirePreparationFailed
        !(VampireObligationPreparationError Void)
    | ImportedModuleNotDirect !SemanticInterfaceId
    | ImportedFactMaterializationFailed
        !Materialization.MaterializationError
    | ImportedCompositionMetadataInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | CompositionRegistrationInvalid !SemanticFactOccurrenceFingerprint !Text
    | ImportedFactCollision
        !SemanticFactOccurrenceFingerprint
    | ImportedAliasCollision
        !SemanticName !ImportedAliasOrigin !ImportedAliasOrigin
    | ImportedAliasTargetMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedGlobalCollision
        !SemanticGlobalKey !ResolvedGlobalBinding !ResolvedGlobalBinding
    | ImportedGlobalTargetInvalid
        !SemanticGlobalKey
        !SemanticGlobalTarget
        !SemanticGlobalTargetError
    | GlobalFormationContractInvalid
        !GlobalBindingRef
        !FormationContractMaterializationError
    | StructureDeclarationInvalid !Text
    | DatatypeInterfaceInvalid !Text
    | BindingConstructionInvalid !Text
    | StructureInterfaceInvalid !StructureInterface.StructureInterfaceError
    | StructureEnvironmentInvalid !StructureEnvironment.StructureEnvironmentError
    | ImportedEvidenceDirectMismatch
        ![SemanticInterfaceId] ![SemanticInterfaceId]
    | ImportedEvidenceInterfaceFailed !SemanticInterfaceError
    | ImportedEvidenceObjectMissing !ObjectId
    | ImportedEvidencePropositionMissing !PropositionId
    | ImportedEvidenceCertificateCountMismatch
    | ImportedEvidenceCertificateTargetMismatch
        !SemanticFactOccurrenceFingerprint
    | DefinitionViewProvenanceMismatch
        !ObjectId !DefinitionViewKind !SemanticFactOccurrenceFingerprint
    | DefinitionViewCertificateMismatch !ObjectId !DefinitionViewKind
    | ImportedNotionViewFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedNotionViewAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | NotionViewMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedNullaryProviderClassificationFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedNullaryProviderClassificationAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | NullaryProviderClassificationMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedProviderResultRuleFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedProviderResultRuleAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | ProviderResultRuleMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedBackwardNotionRuleFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedBackwardNotionRuleAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | BackwardNotionRuleMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedFiniteEvidenceRuleFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedFiniteEvidenceRuleAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | FiniteEvidenceRuleMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedGraphDomainRuleFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedGraphDomainRuleAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | GraphDomainRuleMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedWholeConclusionRuleFactMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedWholeConclusionRuleAuthorityInvalid
        !SemanticFactOccurrenceFingerprint
    | WholeConclusionRuleMaterializationInvalid
        !SemanticFactOccurrenceFingerprint !Text
    | ImportedModuleAfterAuthorization
    | DeclarationObjectValidationFailed !ObjectValidationError
    | DeclarationPropositionValidationFailed
        !PropositionValidationError
    | DeclarationInterfaceFailed !DeclarationInterfaceError
    | DeclarationEnvironmentFailed !SemanticEnvironmentError
    | DeclarationStructureAlreadyStaged !Schema.StructurePhrase
    | DeclarationGlobalTargetInvalid
        !SemanticGlobalKey
        !SemanticGlobalTarget
        !SemanticGlobalTargetError
    | ProofDeclarationMustProduceOneFact
    | BuilderFactCollision
        !SemanticFactOccurrenceFingerprint
    | BuilderAliasCollision !SemanticName
    | BuilderObjectCollision !ObjectId
    | BuilderGlobalCollision !SemanticGlobalKey !ResolvedGlobalBinding
    | BuilderStructureCollision !Schema.StructurePhrase
    deriving stock (Show, Eq)

declarationErrorLocation :: DeclarationError -> Maybe Location
declarationErrorLocation = \case
    RecordObligationFailure _ failure -> declarationErrorLocation failure
    ProofObligationGoal _ failure -> declarationErrorLocation failure
    ProofPreparationExhausted _statistics failure -> declarationErrorLocation failure
    ProofObligationFailedAt location _failure ->
        Just location
    _failure ->
        Nothing

-- | Recognize only the existing prover-failure wrappers. Unknown declaration
-- failures remain integrity errors, even when preparation exhausted earlier.
locatedVampireFailure
    :: DeclarationError
    -> Maybe (Location, Provers.FailedVampireResolution, [Preparation.PreparationStatistics])
locatedVampireFailure = go Nothing []
  where
    go location statistics = \case
        RecordObligationFailure _ failure -> go location statistics failure
        ProofObligationGoal _ failure -> go location statistics failure
        ProofObligationFailedAt here failure -> go (Just here) statistics failure
        ProofPreparationExhausted observation failure -> go location (observation : statistics) failure
        VampireObligationFailed resolution ->
            (\here -> (here, resolution, reverse statistics)) <$> location
        _ -> Nothing

renderDeclarationError :: DeclarationError -> Text
renderDeclarationError = \case
    RecordObligationFailure context failure -> renderDeclarationError failure <> "\n"
        <> Text.intercalate "\n" (Obligation.renderObligationContext context)
    ProofObligationGoal _ failure -> renderDeclarationError failure
    FormationRegistrationPreparationFailed slot detail ->
        "formation registration preparation at " <> shown slot <> ": " <> detail
    FormationRegistrationPreparationLimitExceeded slot limit used debit ->
        "formation registration preparation at " <> shown slot <> ": observed " <> shown (used + debit)
            <> " inspections, exceeding " <> shown limit
    ProofPreparationExhausted statistics failure ->
        renderDeclarationError failure <> "\n"
            <> Preparation.renderPreparationExhaustion statistics
    ImportedEvidenceTheoryMismatch expected actual ->
        "import theory differs: expected " <> Text.pack (show expected)
            <> ", found " <> Text.pack (show actual)
    ImportedEvidenceLocalInvariant detail ->
        "checked local export association failed: " <> detail
    CandidateOutsideDeclaration slot ->
        "candidate " <> shown slot <> " does not belong to this declaration"
    CandidateAlreadyAuthorized slot ->
        "candidate " <> shown slot <> " was authorized more than once"
    CandidateOutsideAuthorizationFrontier slot expected actual ->
        "candidate " <> shown slot <> " is outside authorization frontier "
            <> shown expected <> " (found " <> shown actual <> ")"
    DeclarationHasUnauthorizedCandidates ->
        "the declaration has unauthorized candidates"
    DeclarationAuthorizationFrontierIncomplete ->
        "the declaration authorization frontier is incomplete"
    CandidatePropositionNotClosed ->
        "the candidate proposition still has open local binders"
    CandidatePropositionNotProposition actual ->
        "the candidate has type " <> shown actual <> " instead of Prop"
    StagedPremiseNotEarlier candidate candidateOrdinal premise premiseOrdinal ->
        "candidate " <> shown candidate <> " at stage " <> shown candidateOrdinal
            <> " depends on non-earlier premise " <> shown premise
            <> " at stage " <> shown premiseOrdinal
    StagedPremiseNotAuthorized slot ->
        "staged premise " <> shown slot <> " is not authorized"
    AuthorizedFactNotVisible fingerprint ->
        "authorized fact " <> shown fingerprint <> " is not visible"
    BuilderFactAuthorizationMismatch ->
        "builder fact authority does not match the checked declaration"
    PendingFactAuthorizationMismatch ->
        "pending fact authority does not match the checked declaration"
    PlanningFactContractMismatch slot ->
        "checked declaration-stage fact " <> shown slot
            <> " has inconsistent semantic provenance"
    CheckedAuthorizationCandidateShapeMismatch expected actual ->
        "checked declaration recipe expected " <> shown expected
            <> " candidate stages but received " <> shown actual
    CheckedProofCandidateCountMismatch actual ->
        "checked proof declaration requires exactly one candidate but received "
            <> shown actual
    LocalClaimOutsideCandidate ->
        "proof-local claim was used outside a candidate proof"
    FactSafetyFailed{} ->
        "fact-safety validation failed"
    ValidationCertificateFailed{} ->
        "validation-certificate checking failed"
    DerivationImportFailed{} ->
        "kernel derivation import failed"
    KernelCompletionFailed{} ->
        "kernel replay failed"
    KernelDischargeImportMismatch{} ->
        "scoped kernel discharge used a different set of cited facts"
    KernelDischargeFoundationUse ->
        "the selected source proof method cannot use foundation facts"
    KernelDischargeGuardedRuleUse ->
        "the selected source proof method cannot use guarded kernel rules"
    KernelObviousImportPolicyMismatch ->
        "obvious inference used a fact outside its selected authority"
    KernelCompositionImportPolicyMismatch ->
        "structural composition may import only its registered composition law"
    KernelAssumptionImportUse ->
        "a proof by assumption cannot use imported facts"
    KernelAssumptionEvidenceMissing ->
        "a proof by assumption did not use an active local proposition"
    KernelDefinitionEvidenceMissing ->
        "a proof by definition did not use canonical definition evidence"
    KernelNotionEvidenceMismatch ->
        "a proof by notion did not use exactly its selected local evidence"
    KernelExtensionalityEvidenceMismatch ->
        "an extensionality proof did not use exactly its selected local evidence"
    KernelExtensionalityImportMismatch ->
        "an extensionality proof used a different imported-fact footprint"
    KernelExtensionalityAuthorityMismatch ->
        "record extensionality did not use an authorized generated projection law"
    KernelProofBuildFailed failure ->
        "kernel proof construction failed: " <> shown failure
    DefinitionResultFormationProofFailed failure ->
        "definition-result formation proof failed: " <> shown failure
    DefinitionResultFormationTargetMismatch ->
        "definition-result formation proof established a different premise"
    KernelConstructionDescriptorMismatch ->
        "kernel construction does not match its checked descriptor"
    DefinitionEquationObjectMissing identity ->
        "definition equation references missing object " <> shown identity
    DefinitionEquationObjectNotTransparent identity ->
        "definition equation references non-transparent object " <> shown identity
    DefinitionEquationObjectNotUnaryPredicate identity ->
        "definition equation object " <> shown identity
            <> " is not a unary predicate definition"
    DefinitionEquationCandidateMismatch ->
        "definition equation does not match its checked object content"
    DefinitionViewObjectMissing identity ->
        "canonical definition view references missing object "
            <> shown identity
    DefinitionViewConflict identity kind existing supplied ->
        "canonical definition view " <> shown (identity, kind)
            <> " conflicts between " <> shown existing
            <> " and " <> shown supplied
    NotionViewCandidateMissing position ->
        "notion view refers to missing declaration candidate "
            <> shown position
    NotionViewAuthorityInvalid position ->
        "notion view candidate must be a clean checked source proof: "
            <> shown position
    GeneratedFactNotVisible _target ->
        "a checked generated-fact dependency is not visible"
    ProofObligationFailedAt location failure ->
        locationToText location <> ": " <> renderDeclarationError failure
    VampireObligationFailed{} ->
        "Vampire did not accept a declaration obligation"
    VampireProofHasNoAcceptedObligations ->
        "Vampire proof contains no accepted obligations"
    VampireCandidateBatchMismatch expected actual ->
        "Vampire candidate batch does not match the complete authorization "
            <> "stage (expected " <> shown expected
            <> ", found " <> shown actual <> ")"
    VampireCandidateBatchProofShapeMismatch slot ->
        "Vampire candidate " <> shown slot
            <> " performed execution before its ready batch"
    VampireResolverBatchSizeMismatch expected actual ->
        "Vampire resolver returned " <> shown actual
            <> " results for " <> shown expected <> " requests"
    OmittedProofDidNotRecordUse ->
        "omitted proof completion did not record an omission"
    VampireRequestMismatch ->
        "accepted Vampire run does not match the prepared request"
    VampireTargetMismatch ->
        "Vampire request target does not match the candidate theorem"
    VampireLocalPremisesNotSupported ->
        "typed Vampire requests do not yet support local premises"
    VampireGlobalTypeMismatch object ->
        "Vampire request has the wrong type for global object " <> shown object
    VampirePremiseMismatch fingerprint ->
        "Vampire request premise does not match visible fact " <> shown fingerprint
    VampirePremiseCapabilityMismatch fingerprint ->
        "Vampire request lacks authority for premise " <> shown fingerprint
    VampireFoundationMismatch tag ->
        "Vampire request has inconsistent foundation axiom " <> shown tag
    VampireLogicalSelectionMismatch coreType ->
        "Vampire request has inconsistent logical selection witness at type "
            <> shown coreType
    CurrentCandidateVampirePreparationFailed failure ->
        "the staged Vampire obligation could not be prepared: " <> shown failure
    ImportedModuleNotDirect interface ->
        "sealed semantic interface is not a direct import: " <> shown interface
    ImportedFactMaterializationFailed{} ->
        "imported fact failed materialization checks"
    CompositionRegistrationInvalid fingerprint reason ->
        "composition " <> shown fingerprint <> " cannot be registered: " <> reason
    ImportedCompositionMetadataInvalid fingerprint reason ->
        "imported fact " <> shown fingerprint
            <> " has invalid composition metadata: " <> reason
    ImportedFactCollision fingerprint ->
        "imported fact " <> shown fingerprint <> " is already registered"
    ImportedAliasCollision alias earlier later ->
        "imported semantic alias " <> shown alias
            <> " conflicts between " <> shown earlier
            <> " and " <> shown later
    ImportedAliasTargetMissing fingerprint ->
        "imported alias targets missing fact " <> shown fingerprint
    ImportedGlobalCollision key earlier later ->
        "imported global " <> shown key
            <> " has conflicting owning bindings " <> shown earlier
            <> " and " <> shown later
    ImportedGlobalTargetInvalid key target _failure ->
        "imported global " <> shown key
            <> " has invalid target " <> shown target
    GlobalFormationContractInvalid reference failure ->
        "global " <> shown reference
            <> " has an invalid formation contract: " <> shown failure
    ImportedEvidenceDirectMismatch expected actual ->
        "imported semantic parents differ: expected " <> shown expected
            <> ", found " <> shown actual
    StructureDeclarationInvalid message -> "invalid structure declaration: " <> message
    DatatypeInterfaceInvalid message -> "invalid datatype description: " <> message
    BindingConstructionInvalid message -> "invalid binding construction: " <> message
    StructureInterfaceInvalid failure -> "invalid structure interface: " <> shown failure
    StructureEnvironmentInvalid failure -> "invalid structure environment: " <> shown failure
    ImportedEvidenceInterfaceFailed failure ->
        "imported semantic interface is invalid: " <> shown failure
    ImportedEvidenceObjectMissing identity ->
        "imported semantic interface is missing object " <> shown identity
    ImportedEvidencePropositionMissing identity ->
        "imported semantic interface is missing proposition " <> shown identity
    ImportedEvidenceCertificateCountMismatch ->
        "imported semantic interface has the wrong validation-certificate inventory"
    ImportedEvidenceCertificateTargetMismatch fingerprint ->
        "imported validation certificate targets another fact: "
            <> shown fingerprint
    DefinitionViewProvenanceMismatch object kind fingerprint ->
        "canonical definition view has invalid declaration provenance: "
            <> shown (object, kind, fingerprint)
    DefinitionViewCertificateMismatch object kind ->
        "canonical definition view lacks matching direct authorization: "
            <> shown (object, kind)
    ImportedNotionViewFactMissing fingerprint ->
        "imported notion view references missing fact "
            <> shown fingerprint
    ImportedNotionViewAuthorityInvalid fingerprint ->
        "imported notion view is not backed by a clean checked source proof: "
            <> shown fingerprint
    NotionViewMaterializationInvalid fingerprint reason ->
        "notion view " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedNullaryProviderClassificationFactMissing fingerprint ->
        "imported nullary classification references missing fact "
            <> shown fingerprint
    ImportedNullaryProviderClassificationAuthorityInvalid fingerprint ->
        "imported nullary classification is not backed by a clean checked source proof: "
            <> shown fingerprint
    NullaryProviderClassificationMaterializationInvalid fingerprint reason ->
        "nullary classification " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedProviderResultRuleFactMissing fingerprint ->
        "imported provider-result rule references missing fact "
            <> shown fingerprint
    ImportedProviderResultRuleAuthorityInvalid fingerprint ->
        "imported provider-result rule is not backed by a clean checked source proof: "
            <> shown fingerprint
    ProviderResultRuleMaterializationInvalid fingerprint reason ->
        "provider-result rule " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedBackwardNotionRuleFactMissing fingerprint ->
        "imported backward notion rule references missing fact "
            <> shown fingerprint
    ImportedBackwardNotionRuleAuthorityInvalid fingerprint ->
        "imported backward notion rule is not backed by a clean checked source proof: "
            <> shown fingerprint
    BackwardNotionRuleMaterializationInvalid fingerprint reason ->
        "backward notion rule " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedFiniteEvidenceRuleFactMissing fingerprint ->
        "imported finite-evidence rule references missing fact "
            <> shown fingerprint
    ImportedFiniteEvidenceRuleAuthorityInvalid fingerprint ->
        "imported finite-evidence rule is not backed by a clean checked source proof: "
            <> shown fingerprint
    FiniteEvidenceRuleMaterializationInvalid fingerprint reason ->
        "finite-evidence rule " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedGraphDomainRuleFactMissing fingerprint ->
        "imported graph-domain rule references missing fact "
            <> shown fingerprint
    ImportedGraphDomainRuleAuthorityInvalid fingerprint ->
        "imported graph-domain rule is not backed by a clean checked source proof: "
            <> shown fingerprint
    GraphDomainRuleMaterializationInvalid fingerprint reason ->
        "graph-domain rule " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedWholeConclusionRuleFactMissing fingerprint ->
        "imported whole-conclusion rule references missing fact " <> shown fingerprint
    ImportedWholeConclusionRuleAuthorityInvalid fingerprint ->
        "imported whole-conclusion rule is not backed by a clean checked source proof: " <> shown fingerprint
    WholeConclusionRuleMaterializationInvalid fingerprint reason ->
        "whole-conclusion rule " <> shown fingerprint
            <> " is inconsistent with its supporting theorem: " <> reason
    ImportedModuleAfterAuthorization ->
        "a sealed module was imported after candidate authorization"
    DeclarationObjectValidationFailed{} ->
        "declaration object validation failed"
    DeclarationPropositionValidationFailed{} ->
        "declaration proposition validation failed"
    DeclarationInterfaceFailed{} ->
        "declaration interface validation failed"
    DeclarationEnvironmentFailed{} ->
        "declaration environment delta is inconsistent"
    DeclarationStructureAlreadyStaged structurePhrase ->
        "structure " <> shown structurePhrase <> " was staged more than once"
    DeclarationGlobalTargetInvalid key target _failure ->
        "global " <> shown key <> " has invalid target " <> shown target
    ProofDeclarationMustProduceOneFact ->
        "a proof declaration must produce exactly one fact"
    BuilderFactCollision fingerprint ->
        "fact " <> shown fingerprint <> " is already registered"
    BuilderAliasCollision alias ->
        "semantic alias " <> shown alias <> " is already registered"
    BuilderObjectCollision object ->
        "object " <> shown object <> " is already registered"
    BuilderGlobalCollision key binding ->
        "global " <> shown key <> " is already bound by " <> shown binding
    BuilderStructureCollision structurePhrase ->
        "structure " <> shown structurePhrase <> " is already registered"
  where
    shown :: Show value => value -> Text
    shown = Text.pack . show
