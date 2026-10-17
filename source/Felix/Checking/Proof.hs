{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Elaboration and checked lowering for ordinary theorem proofs.
--
-- This module is the trusted owner of structural local-proof composition.  Its
-- private prepared tree controls when assumptions and proved local claims
-- become available and executes discharges depth-first.  The declaration
-- boundary validates typed tasks and authority. Compositions retain ordinary
-- kernel derivations, replayed there against the proved children.
module Felix.Checking.Proof
    ( PreparedProof
    , preparedProofSyntaxId
    , preparedProofTarget
    , preparedProofFirstOmission
    , preparedProofPreparationStatistics
    , prepareProof
    , prepareProofWithObviousFailureFixture
    , prepareProofWithPreparationWork
    , prepareGeneratedProofWithTransparentDefinition
    , prepareGeneratedProofWithTransparentDefinitionTarget
    , prepareProofWithTransparentDefinitionTarget
    , CheckedProofAuthorization
    , lowerPreparedProofCandidate
    , lowerPreparedProof
    , authorizeCheckedProofCandidate
    , authorizeCheckedProof
    , PreparedFinalPreludeFoundationClaim
    , prepareFinalPreludeFoundationClaim
    , CheckedFinalPreludeFoundationAuthorization
    , lowerPreparedFinalPreludeFoundationClaim
    , authorizeCheckedFinalPreludeFoundationClaim
    , PreparedFinalPreludeGuardedRuleClaim
    , prepareFinalPreludeGuardedRuleClaim
    , CheckedFinalPreludeGuardedRuleAuthorization
    , lowerPreparedFinalPreludeGuardedRuleClaim
    , authorizeCheckedFinalPreludeGuardedRuleClaim
    , ProofError(..)
    , ProofErrorDisposition(..)
    , proofErrorDisposition
    , GoalShape(..)
    , proofErrorLocation
    , renderProofError
    , proofErrorDiagnostic
    ) where

import Data.Functor.Identity (Identity, runIdentity)
import Base hiding (Empty)
import Felix.Checking.Planning qualified as Planning
import Felix.Checking.Preparation qualified as Preparation
import Felix.Checking.Recursion.Application qualified as Recursive
import Felix.Checking.Recursion.Interface qualified as RecursiveInterface
import Felix.Checking.Recursion.Source qualified as RecursiveSource
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Backend.Problem qualified as Backend
import Felix.Checking.Binding qualified as Binding
import Felix.Checking.Calculation qualified as Calculation
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping, lookupGlobalType)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation
    ( ImportIx
    , HypothesisIx
    , KernelDerivation
    , derivationImportJudgement
    , DerivationImportError(..)
    , foundationFactDerivation
    , conjunctionIntroductionDerivation
    , localHypothesisDerivation
    , hypothesisIx
    , importIx
    , eliminateKernelDerivationVoid
    , putKernelDerivationCache
    , remapKernelDerivationImports
    , countedKernelDerivationSourceUses
    , kernelSourceExternalHypothesisUses
    )
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Semantics qualified as KernelSemantics
import Felix.Checking.LooseDeduction qualified as LooseDeduction
import Felix.Checking.Notion.Diagnostics qualified as FormationDiagnostics
import Felix.Checking.Notion.SourceEvidence (SourceEvidence)
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Notion (ConjunctionPath(..))
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.Premise qualified as Premise
import Felix.Checking.Notion.ProviderResult qualified as ProviderResult
import Felix.Checking.Notion.RuleTerm qualified as RuleTerm
import Felix.Checking.Notion.Rule qualified as FormationRule
import Felix.Checking.Notion.Join qualified as FormationJoin
import Felix.Checking.Obvious qualified as Obvious
import Felix.Checking.Proof.Authorization.Internal qualified as Authorization
import Felix.Checking.Record qualified as Record
import Felix.Checking.SetConstruction
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.Structure.Predicate qualified as StructurePredicate
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Obligation qualified as Obligation
import Felix.Cache.Codec
import Felix.Math.Codec (mathematicalDigestHex)
import Felix.Report.Location
import Felix.Report.Diagnostic
import Felix.Syntax.Abstract qualified as Raw

import Control.Monad.Except (ExceptT)
import Control.Monad.Except qualified as Except
import Control.Monad (foldM, join, unless, when)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Reader qualified as Reader
import Control.Monad.State.Strict (StateT)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class qualified as Trans
import Effectful.Error.Static qualified as Error
import Data.ByteString (ByteString)
import Data.Bifunctor qualified as Bifunctor
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import Data.Word (Word)
import Prettyprinter (Doc)


data GoalShape
    = UniversalGoal
    | ImplicationGoal
    | NegationGoal
    | EqualityGoal
    | ConjunctionGoal
    | DisjunctionGoal
    | ExistentialGoal
    | OtherPropositionGoal
    deriving stock (Show, Eq)

data ObviousInvocationSite
    = ImplicitTheoremClose
    | ImplicitInstanceObligation
    | FinalFollows
    | ContradictionObligation
    | InlineObviousInference
    deriving stock (Show, Eq, Ord)

data ObviousInvocationMethod
    = ImplicitObvious
    | CitedObvious
    | DefinitionObvious
    deriving stock (Show, Eq, Ord)

data ObviousCitationGroup = ObviousCitationGroup
    !SemanticFactOccurrenceFingerprint
    !Raw.Marker
    !Natural
    !Natural
    ![Raw.Marker]
    deriving stock (Show, Eq)

data ObviousInvocation = ObviousInvocation
    !ObviousInvocationSite
    !ObviousInvocationMethod
    ![ObviousCitationGroup]
    deriving stock (Show, Eq)

data ProofObviousInputOrigin
    = ProofObviousLocalOrigin !Natural !Text
    | ProofObviousCitedOrigin !ImportIx !ObviousCitationGroup
    | ProofObviousStructuralOrigin !ImportIx !ObviousCitationGroup
    | ProofObviousLocalDefinitionOrigin !Natural !Text
    | ProofObviousImportedDefinitionOrigin
        !Natural !SemanticFactOccurrenceFingerprint !ObjectId
    deriving stock (Show, Eq)

data ProofObviousCandidateOrigin = ProofObviousCandidateOrigin
    !Text
    ![Text]
    ![Text]
    deriving stock (Show, Eq)

data ProofObviousDiagnostic = ProofObviousDiagnostic
    !ObviousInvocation
    !(Obvious.ObviousFailureReport ObjectId)
    ![ProofObviousInputOrigin]
    ![ProofObviousInputOrigin]
    ![ProofObviousInputOrigin]
    ![ProofObviousInputOrigin]
    ![ProofObviousCandidateOrigin]
    ![Text]
    deriving stock (Show, Eq)

proofObviousFailureReport
    :: ProofObviousDiagnostic
    -> Obvious.ObviousFailureReport ObjectId
proofObviousFailureReport
        (ProofObviousDiagnostic _invocation report
            _hypotheses _imports _localDefinitions _importedDefinitions
            _candidateOrigins _preparationNotes) =
    report

data ActiveDefinitionReconciliationMismatch
    = ActiveDefinitionRetainedOriginMismatch
        !Elaboration.FormationSourceOrigin
    | ActiveDefinitionMissing
    | ActiveDefinitionLocalOriginMismatch !ProofLocalOrigin
    | ActiveDefinitionPropositionMismatch
    deriving stock (Show, Eq)

data FormationAliasNormalizationIntegrityFailure
    = FormationAliasCheckedReplacementFailed
        !ScopedOccurrenceReplacementError
    | FormationAliasReplayHypothesisUnavailable
    | FormationAliasReplayHypothesisMismatch
    | FormationAliasReplayKernelFailed
        !KernelProof.KernelProofBuildError
    | FormationAliasReplayResultMismatch
    deriving stock (Show, Eq)

data RecordExtensionalityIntegrityError
    = RecordExtensionalityProjectionLawIntegrity
        !Declaration.StructureProjectionLawIntegrityError
    | RecordExtensionalityActiveDefinitionMismatch
        !Location
        !Natural
        !ActiveDefinitionReconciliationMismatch
    | RecordExtensionalityAliasNormalizationIntegrity
        !Location
        !Natural
        !FormationAliasNormalizationIntegrityFailure
    deriving stock (Show, Eq)

data RecordExtensionalityProofBuildFailure
    = RecordExtensionalityProofStructural
        !KernelProof.KernelProofBuildError
    | RecordExtensionalityProofIntegrity
        !RecordExtensionalityIntegrityError
    deriving stock (Show, Eq)

data FormationAliasReplayDirection
    = ReplayFormationAliasesForward
    | ReplayFormationAliasesReverse
    deriving stock (Show, Eq)

data ProofError
    = ProofRecordObligations !Obligation.ObligationContext !ProofError
    | ProofUnsupportedClaim !Location
    | ProofUnsupportedStep !Location
    | ProofStructuralInductionInvalid !Location !Text
    | ProofSetInductionVariableRequired !Location
    | ProofSetInductionVariableNotActive
        !Location !Raw.VarSymbol
    | ProofSetInductionFocusAmbiguous
        !Location !(NonEmpty Raw.VarSymbol)
    | ProofSetInductionActiveBinderIneligible
        !Location !Raw.VarSymbol
    | ProofSetInductionBinderConflict
        !Location !Raw.VarSymbol
    | ProofSetInductionGoalMismatch !Location
    | ProofTransfiniteInductionGoalMismatch !Location
    | ProofTransfiniteInductionFocusAmbiguous
        !Location !(NonEmpty Raw.VarSymbol)
    | ProofTransfiniteInductionHeredityUnavailable !Location
    | ProofSetExtensionalityGoalMismatch !Location
    | ProofSetExtensionalityLeftToRightUnavailable !Location
    | ProofSetExtensionalityRightToLeftUnavailable !Location
    | ProofRecordExtensionalityGoalMismatch !Location
    | ProofRecordExtensionalityLeftShapeUnavailable !Location
    | ProofRecordExtensionalityRightShapeUnavailable !Location
    | ProofRecordExtensionalityCommonShapeUnavailable !Location
    | ProofRecordExtensionalityFieldUnavailable
        !Location !Raw.StructSymbol
    | ProofRecordExtensionalityIntegrityFailure
        !Location !RecordExtensionalityIntegrityError
    | ProofExpectedUniversalGoal !Location !GoalShape
    | ProofExpectedImplicationGoal !Location !GoalShape
    | ProofExpectedAssumptiveGoal !Location !GoalShape
    | ProofGoalStatementMismatch !Location
    | ProofAssumptionOpeningFailed
        !Location
        !(LooseDeduction.AssumptionOpeningMismatch ObjectId)
    | ProofEmptyCaseSplit !Location
    | ProofStructuralCompositionFailed
        !Location !KernelProof.KernelProofBuildError
    | ProofObviousInferenceFailed
        !Location !(Obvious.ObviousFailure ObjectId)
    | ProofObviousInferenceReported
        !Location !ProofObviousDiagnostic
    | ProofObviousDiagnosticIntegrityFailure !Location !Text
    | ProofAssumptionUnavailable !Location
    | ProofLocalFunctionBinderMismatch !Location
    | ProofLocalFunctionNameConflict !Location
    | ProofUnknownReference !Location !Raw.Marker
    | ProofElaborationFailed !Elaboration.ElaborationError
    | ProofCompositionDeclarationInvalid !Location !Text
    | ProofCalculationFailed !Location !Calculation.CalculationError
    | ProofCalculationConditionUnavailable !Location !SemanticFactOccurrenceFingerprint !Natural
        !(ScopedCheckedCore ObjectId) !Elaboration.NotionQueryFailure
    | ProofCalculationCompositionMissing
        !Location !(ScopedCheckedCore ObjectId) !(ScopedCheckedCore ObjectId)
    | ProofCalculationCompositionAmbiguous
        !Location
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(NonEmpty SemanticFactOccurrenceFingerprint)
    | ProofObligationPreparationFailed
        !Location
        !(Declaration.VampireObligationPreparationError
            Elaboration.LocalId)
    | ProofStructurePredicateResolutionFailed
        !Location !Declaration.StructurePredicateResolutionError
    | ProofStructureMetadataMismatch !Location
    | ProofStructureIntroductionFailed
        !Location !KernelProof.KernelProofBuildError
    | ProofFoundationLeafRequiresImplicitAuto !Location
    | ProofFoundationLeafTargetMismatch !Location
    | ProofFoundationLeafTargetAmbiguous !Location
    | ProofGuardedRuleTargetMismatch !Location
    | ProofGuardedRuleTargetAmbiguous !Location
    | ProofClassificationInvalid !Location !Text
    | ProofNotionGoalUnsupported !Location
    | ProofNotionUnavailable !Location !Elaboration.NotionQueryFailure
    | ProofNotionFormationFailed !Location !Notion.FormationProofError
    | ProofNotionFormationTargetMismatch !Location
    deriving stock (Show, Eq)

data ProofErrorDisposition
    = ProofSourceRejection
    | ProofInfrastructureFailure
    deriving stock (Show, Eq)

-- | Whether a proof failure belongs to checked source or to the checker.
-- Keep this match total so adding a proof-error constructor forces an explicit
-- policy decision at the owning boundary.
proofErrorDisposition :: ProofError -> ProofErrorDisposition
proofErrorDisposition = \case
    ProofRecordObligations _ failure -> proofErrorDisposition failure
    ProofUnsupportedClaim{} -> ProofSourceRejection
    ProofUnsupportedStep{} -> ProofSourceRejection
    ProofStructuralInductionInvalid{} -> ProofSourceRejection
    ProofSetInductionVariableRequired{} -> ProofSourceRejection
    ProofSetInductionVariableNotActive{} -> ProofSourceRejection
    ProofSetInductionFocusAmbiguous{} -> ProofSourceRejection
    ProofSetInductionActiveBinderIneligible{} -> ProofSourceRejection
    ProofSetInductionBinderConflict{} -> ProofSourceRejection
    ProofSetInductionGoalMismatch{} -> ProofSourceRejection
    ProofTransfiniteInductionGoalMismatch{} -> ProofSourceRejection
    ProofTransfiniteInductionFocusAmbiguous{} -> ProofSourceRejection
    ProofTransfiniteInductionHeredityUnavailable{} -> ProofSourceRejection
    ProofSetExtensionalityGoalMismatch{} -> ProofSourceRejection
    ProofSetExtensionalityLeftToRightUnavailable{} -> ProofSourceRejection
    ProofSetExtensionalityRightToLeftUnavailable{} -> ProofSourceRejection
    ProofRecordExtensionalityGoalMismatch{} -> ProofSourceRejection
    ProofRecordExtensionalityLeftShapeUnavailable{} -> ProofSourceRejection
    ProofRecordExtensionalityRightShapeUnavailable{} -> ProofSourceRejection
    ProofRecordExtensionalityCommonShapeUnavailable{} -> ProofSourceRejection
    ProofRecordExtensionalityFieldUnavailable{} -> ProofSourceRejection
    ProofRecordExtensionalityIntegrityFailure{} -> ProofInfrastructureFailure
    ProofExpectedUniversalGoal{} -> ProofSourceRejection
    ProofExpectedImplicationGoal{} -> ProofSourceRejection
    ProofExpectedAssumptiveGoal{} -> ProofSourceRejection
    ProofGoalStatementMismatch{} -> ProofSourceRejection
    ProofAssumptionOpeningFailed{} -> ProofSourceRejection
    ProofEmptyCaseSplit{} -> ProofSourceRejection
    ProofStructuralCompositionFailed{} -> ProofSourceRejection
    ProofObviousInferenceFailed _location failure ->
        obviousFailureDisposition failure
    ProofObviousInferenceReported _location diagnostic ->
        obviousFailureDisposition
            (Obvious.obviousFailureFinal
                (proofObviousFailureReport diagnostic))
    ProofObviousDiagnosticIntegrityFailure{} -> ProofInfrastructureFailure
    ProofAssumptionUnavailable{} -> ProofSourceRejection
    ProofLocalFunctionBinderMismatch{} -> ProofSourceRejection
    ProofLocalFunctionNameConflict{} -> ProofSourceRejection
    ProofUnknownReference{} -> ProofSourceRejection
    ProofElaborationFailed{} -> ProofSourceRejection
    ProofCompositionDeclarationInvalid{} -> ProofSourceRejection
    ProofCalculationConditionUnavailable{} -> ProofSourceRejection
    ProofCalculationFailed{} -> ProofSourceRejection
    ProofCalculationCompositionMissing{} -> ProofSourceRejection
    ProofCalculationCompositionAmbiguous{} -> ProofSourceRejection
    ProofObligationPreparationFailed{} -> ProofSourceRejection
    ProofStructurePredicateResolutionFailed{} -> ProofSourceRejection
    ProofStructureMetadataMismatch{} -> ProofInfrastructureFailure
    ProofStructureIntroductionFailed{} -> ProofSourceRejection
    ProofFoundationLeafRequiresImplicitAuto{} -> ProofSourceRejection
    ProofFoundationLeafTargetMismatch{} -> ProofSourceRejection
    ProofFoundationLeafTargetAmbiguous{} -> ProofSourceRejection
    ProofGuardedRuleTargetMismatch{} -> ProofSourceRejection
    ProofGuardedRuleTargetAmbiguous{} -> ProofSourceRejection
    ProofClassificationInvalid{} -> ProofSourceRejection
    ProofNotionGoalUnsupported{} -> ProofSourceRejection
    ProofNotionUnavailable{} -> ProofSourceRejection
    ProofNotionFormationFailed _ Notion.FormationProofDerivationLimitExceeded{} -> ProofSourceRejection
    ProofNotionFormationFailed{} -> ProofInfrastructureFailure
    ProofNotionFormationTargetMismatch{} -> ProofInfrastructureFailure

obviousFailureDisposition
    :: Obvious.ObviousFailure global
    -> ProofErrorDisposition
obviousFailureDisposition = \case
    Obvious.ObviousNoMatchingConclusion{} -> ProofSourceRejection
    Obvious.ObviousAntecedentUnavailable{} -> ProofSourceRejection
    Obvious.ObviousUndeterminedParameter{} -> ProofSourceRejection
    Obvious.ObviousFalsityPairUnavailable -> ProofSourceRejection
    Obvious.ObviousUnsupportedHigherOrderInstantiation ->
        ProofSourceRejection
    Obvious.ObviousUnsupportedTermOutsideUniverse -> ProofSourceRejection
    Obvious.ObviousCanonicalDefinitionEvidenceRequired ->
        ProofSourceRejection
    Obvious.ObviousRefutationSaturated -> ProofSourceRejection
    Obvious.ObviousResourceExhausted{} -> ProofSourceRejection
    Obvious.ObviousMalformedInput{} -> ProofInfrastructureFailure
    Obvious.ObviousRepeatedState{} -> ProofSourceRejection
    Obvious.ObviousIntegrityFailure{} -> ProofInfrastructureFailure
    Obvious.ObviousConversionFailed{} -> ProofInfrastructureFailure
    Obvious.ObviousRequiredConversionNotConvertible -> ProofInfrastructureFailure
    Obvious.ObviousConversionAccountingInvariant{} -> ProofInfrastructureFailure

proofErrorLocation :: ProofError -> Location
proofErrorLocation = \case
    ProofRecordObligations _ failure -> proofErrorLocation failure
    ProofUnsupportedClaim location -> location
    ProofUnsupportedStep location -> location
    ProofStructuralInductionInvalid location _reason -> location
    ProofSetInductionVariableRequired location -> location
    ProofSetInductionVariableNotActive location _variable ->
        location
    ProofSetInductionFocusAmbiguous location _names -> location
    ProofSetInductionActiveBinderIneligible location _variable ->
        location
    ProofSetInductionBinderConflict location _variable ->
        location
    ProofSetInductionGoalMismatch location -> location
    ProofTransfiniteInductionGoalMismatch location -> location
    ProofTransfiniteInductionFocusAmbiguous location _names -> location
    ProofTransfiniteInductionHeredityUnavailable location -> location
    ProofSetExtensionalityGoalMismatch location -> location
    ProofSetExtensionalityLeftToRightUnavailable location -> location
    ProofSetExtensionalityRightToLeftUnavailable location -> location
    ProofRecordExtensionalityGoalMismatch location -> location
    ProofRecordExtensionalityLeftShapeUnavailable location -> location
    ProofRecordExtensionalityRightShapeUnavailable location -> location
    ProofRecordExtensionalityCommonShapeUnavailable location -> location
    ProofRecordExtensionalityFieldUnavailable location _field -> location
    ProofRecordExtensionalityIntegrityFailure location _failure -> location
    ProofExpectedUniversalGoal location _shape -> location
    ProofExpectedImplicationGoal location _shape -> location
    ProofExpectedAssumptiveGoal location _shape -> location
    ProofGoalStatementMismatch location -> location
    ProofAssumptionOpeningFailed location _mismatch -> location
    ProofEmptyCaseSplit location -> location
    ProofStructuralCompositionFailed location _failure -> location
    ProofObviousInferenceFailed location _failure -> location
    ProofObviousInferenceReported location _diagnostic -> location
    ProofObviousDiagnosticIntegrityFailure location _reason -> location
    ProofAssumptionUnavailable location -> location
    ProofLocalFunctionBinderMismatch location -> location
    ProofLocalFunctionNameConflict location -> location
    ProofUnknownReference location _marker -> location
    ProofElaborationFailed failure ->
        Elaboration.elaborationErrorLocation failure
    ProofCompositionDeclarationInvalid location _message -> location
    ProofCalculationConditionUnavailable location _law _ordinal _condition _failure -> location
    ProofCalculationFailed location _reason -> location
    ProofCalculationCompositionMissing location _left _right -> location
    ProofCalculationCompositionAmbiguous location _left _right _facts -> location
    ProofObligationPreparationFailed location _failure -> location
    ProofStructurePredicateResolutionFailed location _failure -> location
    ProofStructureMetadataMismatch location -> location
    ProofStructureIntroductionFailed location _failure -> location
    ProofFoundationLeafRequiresImplicitAuto location -> location
    ProofFoundationLeafTargetMismatch location -> location
    ProofFoundationLeafTargetAmbiguous location -> location
    ProofGuardedRuleTargetMismatch location -> location
    ProofGuardedRuleTargetAmbiguous location -> location
    ProofClassificationInvalid location _reason -> location
    ProofNotionGoalUnsupported location -> location
    ProofNotionUnavailable location _failure -> location
    ProofNotionFormationFailed location _failure -> location
    ProofNotionFormationTargetMismatch location -> location

renderProofError :: ProofError -> Text
renderProofError = \case
    ProofRecordObligations context failure -> renderProofError failure <> "\n"
        <> Text.intercalate "\n" (Obligation.renderObligationContext context)
    ProofUnsupportedClaim location ->
        at location <> "this claim is not yet supported by the typed checker"
    ProofUnsupportedStep location ->
        at location <> "this proof step is not yet supported by the typed checker"
    ProofStructuralInductionInvalid location reason ->
        at location <> "structural induction: " <> reason
    ProofSetInductionVariableRequired location ->
        at location <> "exact set induction requires a named set variable"
    ProofSetInductionVariableNotActive location variable ->
        at location <> "the set-induction variable " <> shown variable
            <> " is not an eligible exact focus"
    ProofSetInductionFocusAmbiguous location names ->
        at location
            <> "set induction without an explicit variable has no unique focus among "
            <> renderVariableNames names
    ProofSetInductionActiveBinderIneligible location variable ->
        at location <> "the active binder " <> shown variable
            <> " is not an eligible set-induction focus"
    ProofSetInductionBinderConflict location variable ->
        at location <> "the leading set-induction binder " <> shown variable
            <> " conflicts with an active proof binder"
    ProofSetInductionGoalMismatch location ->
        at location <> "the set-induction variable does not belong to this goal"
    ProofTransfiniteInductionGoalMismatch location ->
        at location
            <> "transfinite induction requires a theorem guarded by a unary ordinal predicate"
    ProofTransfiniteInductionFocusAmbiguous location names ->
        at location
            <> "transfinite induction has more than one eligible ordinal focus among "
            <> renderVariableNames names
    ProofTransfiniteInductionHeredityUnavailable location ->
        at location
            <> "transfinite induction requires a visible theorem saying that elements of the guarded ordinals satisfy the same predicate"
    ProofSetExtensionalityGoalMismatch location ->
        at location <> "set extensionality requires a set-equality goal"
    ProofSetExtensionalityLeftToRightUnavailable location ->
        at location
            <> "set extensionality requires the left-to-right inclusion as an active checked premise"
    ProofSetExtensionalityRightToLeftUnavailable location ->
        at location
            <> "set extensionality requires the right-to-left inclusion as an active checked premise"
    ProofRecordExtensionalityGoalMismatch location ->
        at location <> "structure extensionality requires a set-equality goal"
    ProofRecordExtensionalityLeftShapeUnavailable location ->
        at location
            <> "structure extensionality requires an active exact shape for the left operand"
    ProofRecordExtensionalityRightShapeUnavailable location ->
        at location
            <> "structure extensionality requires an active exact shape for the right operand"
    ProofRecordExtensionalityCommonShapeUnavailable location ->
        at location
            <> "structure extensionality requires a common visible flattened record shape"
    ProofRecordExtensionalityFieldUnavailable location field ->
        at location
            <> "structure extensionality requires equality of the stored projection "
            <> shown field
    ProofRecordExtensionalityIntegrityFailure location failure ->
        at location
            <> "record extensionality metadata is inconsistent: "
            <> shown failure
    ProofExpectedUniversalGoal location shape ->
        at location <> "this fix step requires a universal goal, but the goal is "
            <> renderGoalShape shape
    ProofExpectedImplicationGoal location shape ->
        at location <> "this proof step requires an implication goal, but the goal is "
            <> renderGoalShape shape
    ProofExpectedAssumptiveGoal location shape ->
        at location
            <> "this assume step requires an implication, negation, or classically opened disjunction goal, but the goal is "
            <> renderGoalShape shape
    ProofGoalStatementMismatch location ->
        at location <> "the proof step does not match the current goal"
    ProofAssumptionOpeningFailed location mismatch ->
        at location <> renderAssumptionOpeningMismatch mismatch
    ProofEmptyCaseSplit location ->
        at location <> "case analysis requires at least one case"
    ProofStructuralCompositionFailed location failure ->
        at location <> "invalid structural proof composition: " <> shown failure
    ProofObviousInferenceFailed location failure ->
        at location <> renderObviousFailure failure
    ProofObviousInferenceReported location diagnostic ->
        at location
            <> renderObviousFailure
                (Obvious.obviousFailureFinal
                    (proofObviousFailureReport diagnostic))
    ProofObviousDiagnosticIntegrityFailure location reason ->
        at location
            <> "could not assemble trustworthy obvious-inference diagnostics: "
            <> reason
    ProofAssumptionUnavailable location ->
        at location
            <> "no active local proposition matches the goal up to conversion"
    ProofLocalFunctionBinderMismatch location ->
        at location <> "the function argument must match its domain binder"
    ProofLocalFunctionNameConflict location ->
        at location <> "the function and argument names must be distinct"
    ProofUnknownReference location marker ->
        at location <> "the cited fact " <> shown marker <> " is not visible"
    ProofElaborationFailed failure ->
        Elaboration.renderElaborationError failure
    ProofCompositionDeclarationInvalid location message ->
        at location <> "invalid composition declaration: " <> message
    ProofCalculationConditionUnavailable location law ordinal condition failure ->
        at location <> "composition condition " <> shown ordinal <> " of " <> shown law
            <> " (" <> shown condition <> "): " <> Elaboration.renderNotionQueryFailure failure
    ProofCalculationFailed location reason ->
        at location <> "calculation preparation failed: " <> Calculation.renderCalculationError reason
    ProofCalculationCompositionMissing location left right ->
        at location
            <> "no composition theorem is registered for "
            <> shown left <> " followed by " <> shown right
    ProofCalculationCompositionAmbiguous location left right facts ->
        at location
            <> "more than one composition theorem is visible for "
            <> shown left <> " followed by " <> shown right
            <> ": " <> shown facts
    ProofObligationPreparationFailed location failure ->
        at location <> "the proof obligation is invalid: " <> shown failure
    ProofStructurePredicateResolutionFailed location failure ->
        at location <> "the structure predicate is ambiguous: " <> shown failure
    ProofStructureMetadataMismatch location ->
        at location <> "the registered structure metadata is inconsistent with its predicate"
    ProofStructureIntroductionFailed location failure ->
        at location <> "invalid checked structure decomposition: " <> shown failure
    ProofFoundationLeafRequiresImplicitAuto location ->
        at location
            <> "a confined foundation claim requires an implicit Auto proof"
    ProofFoundationLeafTargetMismatch location ->
        at location <> "the claim does not exactly match a foundation axiom"
    ProofFoundationLeafTargetAmbiguous location ->
        at location <> "the claim matches more than one foundation axiom"
    ProofGuardedRuleTargetMismatch location ->
        at location <> "the claim does not exactly match a guarded kernel rule"
    ProofGuardedRuleTargetAmbiguous location ->
        at location <> "the claim matches more than one guarded kernel rule"
    ProofClassificationInvalid location reason ->
        at location <> "invalid classification: " <> reason
    ProofNotionGoalUnsupported location ->
        at location
            <> "`by notion` requires a non-neutral source goal"
    ProofNotionUnavailable location failure ->
        at location <> Elaboration.renderNotionQueryFailure failure
    ProofNotionFormationFailed location (Notion.FormationProofDerivationLimitExceeded failure) ->
        at location <> "notion proof construction exhausted: " <> Notion.renderFormationSearchError failure
    ProofNotionFormationFailed location failure ->
        at location <> "notion proof construction failed: " <> shown failure
    ProofNotionFormationTargetMismatch location ->
        at location <> "notion proof established a different goal"
  where
    at location = locationToText location <> ": "
    shown :: Show value => value -> Text
    shown = Text.pack . show

renderObviousFailure :: Obvious.ObviousFailure global -> Text
renderObviousFailure = \case
    Obvious.ObviousNoMatchingConclusion{} ->
        "obvious inference found no local or cited fact whose conclusion matches the goal"
    Obvious.ObviousAntecedentUnavailable{} ->
        "obvious inference matched a theorem, but could not prove its first unresolved antecedent"
    Obvious.ObviousUndeterminedParameter parameter ->
        "obvious inference could not determine theorem parameter #"
            <> Text.pack (show parameter)
            <> " from the conclusion"
    Obvious.ObviousFalsityPairUnavailable ->
        "obvious inference could not find both a proposition and its negation"
    Obvious.ObviousUnsupportedHigherOrderInstantiation ->
        "obvious inference would require unsupported higher-order instantiation"
    Obvious.ObviousUnsupportedTermOutsideUniverse ->
        "obvious inference selected a rule instance containing a term outside its frozen search universe"
    Obvious.ObviousCanonicalDefinitionEvidenceRequired ->
        "the proposition is derivable, but the selected proof does not use canonical definition evidence"
    Obvious.ObviousRefutationSaturated ->
        "obvious inference saturated its supported deterministic fragment without finding a proof"
    Obvious.ObviousResourceExhausted limit ->
        "obvious inference exhausted its " <> renderObviousLimit limit
    Obvious.ObviousRepeatedState{} ->
        "obvious inference encountered a repeated proof-search state"
    Obvious.ObviousMalformedInput malformed ->
        "obvious inference received malformed checked input or configuration: "
            <> Text.pack (show malformed)
    Obvious.ObviousIntegrityFailure failure ->
        "obvious inference could not construct a kernel proof: "
            <> Text.pack (show failure)
    Obvious.ObviousConversionFailed failure ->
        "obvious inference conversion failed: " <> Text.pack (show failure)
    Obvious.ObviousRequiredConversionNotConvertible ->
        "obvious inference required a conversion between non-convertible terms"
    Obvious.ObviousConversionAccountingInvariant cost pool ->
        "obvious inference conversion cost exceeded its remaining pool: "
            <> Text.pack (show cost) <> "; " <> Text.pack (show pool)

renderObviousLimit :: Obvious.ObviousLimit -> Text
renderObviousLimit = \case
    Obvious.ObviousFocusedWorkLimit ->
        "focused-work limit"
    Obvious.ObviousRefutationWorkLimit ->
        "refutation-work limit"
    Obvious.ObviousConversionOperationLimit ->
        "conversion operation limit"
    Obvious.ObviousConversionPoolLimit ->
        "conversion pool"
    Obvious.ObviousGroundTermLimit ->
        "ground-term limit"
    Obvious.ObviousBranchNodeLimit ->
        "branch-node limit"
    Obvious.ObviousRuleInstanceLimit ->
        "rule-instance limit"

renderAssumptionOpeningMismatch
    :: LooseDeduction.AssumptionOpeningMismatch global
    -> Text
renderAssumptionOpeningMismatch = \case
    LooseDeduction.AssumptionNoSupportedFrontier ->
        "the goal has no supported assumption frontier"
    LooseDeduction.AssumptionClassicalDisjunctionMismatch{} ->
        "classical disjunction opening requires the negation of its left alternative"
    LooseDeduction.AssumptionPartUnavailable{} ->
        "the supplied assumption contains a proposition unavailable in the goal frontier"
    LooseDeduction.AssumptionInsufficientMultiplicity
            _part required available ->
        "the supplied assumption repeats a proposition too many times (required "
            <> Text.pack (show required)
            <> ", available "
            <> Text.pack (show available)
            <> ")"

proofErrorDiagnostic :: ProofError -> Maybe Diagnostic
proofErrorDiagnostic = \case
    ProofRecordObligations context failure -> do
        diagnostic <- proofErrorDiagnostic failure
        pure diagnostic{diagnosticNotes = diagnosticNotes diagnostic
            <> (pretty <$> Obligation.renderObligationContext context)}
    ProofObviousInferenceReported location diagnostic ->
        Just (proofObviousDiagnostic location diagnostic)
    ProofObviousInferenceFailed location failure ->
        Just (legacyObviousDiagnostic location failure)
    ProofObviousDiagnosticIntegrityFailure location reason ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode =
                    DiagnosticProofObviousDiagnosticIntegrity
                , diagnosticTitle =
                    "obvious-inference diagnostics are inconsistent"
                , diagnosticPrimary = Just location
                , diagnosticMessage = pretty reason
                , diagnosticNotes = []
                , diagnosticHelp = []
                }
    ProofExpectedUniversalGoal location shape ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofExpectedUniversal
                , diagnosticTitle = "this fix step cannot be used for the current goal"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty case shape of
                        UniversalGoal ->
                            ("the goal is universally quantified, but its binder type does not match this fix step"
                                :: Text)
                        _ ->
                            "actual goal shape: " <> renderGoalShape shape
                                <> "; expected universal quantification"
                , diagnosticNotes = []
                , diagnosticHelp =
                    [pretty ("use a proof step that applies to the current goal" :: Text)]
                }
    ProofExpectedImplicationGoal location shape ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofExpectedImplication
                , diagnosticTitle =
                    "this proof step requires an implication goal"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("actual goal shape: " <> renderGoalShape shape
                            <> "; expected an implication")
                , diagnosticNotes = []
                , diagnosticHelp =
                    [pretty ("use a proof step that applies to the current goal" :: Text)]
                }
    ProofExpectedAssumptiveGoal location shape ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofExpectedAssumptiveGoal
                , diagnosticTitle =
                    "this assume step cannot open the current goal"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("actual goal shape: " <> renderGoalShape shape
                            <> "; expected an implication, negation, or suitable disjunction")
                , diagnosticNotes = []
                , diagnosticHelp =
                    [pretty ("use a proof step that applies to the current goal" :: Text)]
                }
    ProofAssumptionOpeningFailed location mismatch ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofAssumptionMismatch
                , diagnosticTitle = "this assumption does not match the current goal"
                , diagnosticPrimary = Just location
                , diagnosticMessage = pretty (renderAssumptionOpeningMismatch mismatch)
                , diagnosticNotes = []
                , diagnosticHelp =
                    [ pretty
                        ("supply an assumption supported by the goal's implication or negation structure"
                            :: Text)
                    ]
                }
    ProofSetInductionFocusAmbiguous location names ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofSetInductionAmbiguous
                , diagnosticTitle = "set induction has no unique focus"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("more than one set binder is eligible for induction"
                            :: Text)
                , diagnosticNotes = inductionNameNotes names
                , diagnosticHelp =
                    [ pretty
                        ("write `Proof by \\in-induction on $...$` with one eligible binder"
                            :: Text)
                    ]
                }
    ProofTransfiniteInductionFocusAmbiguous location names ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode =
                    DiagnosticProofTransfiniteInductionAmbiguous
                , diagnosticTitle =
                    "transfinite induction has no unique ordinal focus"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("more than one ordinal guard supports transfinite induction"
                            :: Text)
                , diagnosticNotes = inductionNameNotes names
                , diagnosticHelp = []
                }
    ProofUnknownReference location (Raw.Marker marker) ->
        Just
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticProofUnknownReference
                , diagnosticTitle = "the cited fact is not visible"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty ("unknown proof reference `" <> marker <> "`")
                , diagnosticNotes = []
                , diagnosticHelp =
                    [pretty ("check the reference label and its imports" :: Text)]
                }
    _failure -> Nothing

proofObviousDiagnostic
    :: Location
    -> ProofObviousDiagnostic
    -> Diagnostic
proofObviousDiagnostic location
        (ProofObviousDiagnostic invocation report
            hypothesisOrigins importOrigins
            localDefinitionOrigins importedDefinitionOrigins
            candidateOrigins preparationNotes) =
    Diagnostic
        { diagnosticSeverity = DiagnosticError
        , diagnosticCode = obviousDiagnosticCode primary
        , diagnosticTitle = obviousDiagnosticTitle primary
        , diagnosticPrimary = Just location
        , diagnosticMessage =
            pretty
                (if primary == finalClass
                    then renderObviousFailure final
                    else obviousDiagnosticMessage primary)
        , diagnosticNotes = pretty <$> notes
        , diagnosticHelp = pretty <$> obviousDiagnosticHelp primary report
        }
  where
    final = Obvious.obviousFailureFinal report
    finalClass = obviousFailureDiagnosticClass final
    primary = Obvious.obviousFailurePrimaryClass report
    statistics = Obvious.obviousFailureStatistics report
    notes =
        [ "obligation: " <> renderObviousInvocationSite invocation
            <> "; method: " <> renderObviousInvocationMethod invocation
        , "checked goal: "
            <> renderObviousCoreSummary
                (Obvious.obviousFailureCheckedGoal report)
        , "focused goal: "
            <> renderFocusedGoalView
                (Obvious.obviousFailureFocusedGoalView report)
        ]
        <> [ "final semantic result: " <> renderObviousFailure final
           | primary /= finalClass
           ]
        <> renderHypothesisSection
            report hypothesisOrigins
        <> renderImportSection
            report importOrigins
        <> renderDefinitionSection
            "local definition views"
            (Obvious.obviousFailureLocalDefinitionViewCount report)
            (Obvious.obviousFailureLocalDefinitionViews report)
            localDefinitionOrigins
        <> renderDefinitionSection
            "imported definition views"
            (Obvious.obviousFailureImportedDefinitionViewCount report)
            (Obvious.obviousFailureImportedDefinitionViews report)
            importedDefinitionOrigins
        <> [ "focused tier: "
                <> renderObviousTierOutcome
                    (Obvious.obviousFocusedTierOutcome statistics)
           , "refutation tier: "
                <> renderObviousTierOutcome
                    (Obvious.obviousRefutationTierOutcome statistics)
                <> renderFailurePathSuffix
                    (Obvious.obviousFailurePath report)
           ]
        <> concatMap renderObviousBreadthObservation
            (Obvious.obviousBreadthObservations statistics)
        <> renderCandidateSection report candidateOrigins
        <> preparationNotes

-- These are request-wide observations, including alternatives later canceled.
-- They do not replace the final failure or identify its blocking consumer.
renderObviousBreadthObservation :: Obvious.ObviousBreadthObservation -> [Text]
renderObviousBreadthObservation = \case
    Obvious.ObviousFactDomainBreadth limit used deferred ->
        observed "selected fact-domain search" limit used deferred "; existing domains were retained"
    Obvious.ObviousWitnessBreadth local limit used deferred ->
        observed "existing-witness search" limit used deferred
            ("; per-obligation cap " <> count local)
    Obvious.ObviousPremiseQueryBreadth limit used deferred ->
        observed "theorem-premise queries" limit used deferred ""
    Obvious.ObviousUniversalBreadth limit used deferred ->
        observed "generic universal instances" limit used deferred ""
    Obvious.ObviousUniversalHintEffort limit used ->
        [ "universal hint effort: " <> count used <> "/" <> count limit
            <> " turns used; existing-term fallback candidates were retained"
        | limit > 0 && used == limit ]
    Obvious.ObviousExistentialBreadth limit used deferred ->
        observed "supplied-existential openings" limit used deferred ""
    Obvious.ObviousExtensionalityBreadth limit used deferred ->
        observed "membership-extensionality applications" limit used deferred ""
    Obvious.ObviousEndpointBreadth limit used deferred ->
        observed "endpoint equality applications" limit used deferred ""
  where
    count = Text.pack . show
    observed label limit used deferred detail =
        [ label <> ": breadth deferral observed during this request ("
            <> count used <> " used; request cap " <> count limit <> ")" <> detail
        | deferred ]

legacyObviousDiagnostic
    :: Location
    -> Obvious.ObviousFailure ObjectId
    -> Diagnostic
legacyObviousDiagnostic location failure =
    Diagnostic
        { diagnosticSeverity = DiagnosticError
        , diagnosticCode = obviousDiagnosticCode failureClass
        , diagnosticTitle = obviousDiagnosticTitle failureClass
        , diagnosticPrimary = Just location
        , diagnosticMessage = pretty (renderObviousFailure failure)
        , diagnosticNotes = []
        , diagnosticHelp = []
        }
  where
    failureClass = obviousFailureDiagnosticClass failure

obviousFailureDiagnosticClass
    :: Obvious.ObviousFailure global
    -> Obvious.ObviousFailureClass
obviousFailureDiagnosticClass = Obvious.obviousFailureClass

obviousDiagnosticCode :: Obvious.ObviousFailureClass -> DiagnosticCode
obviousDiagnosticCode = \case
    Obvious.ObviousNoMatchClass -> DiagnosticProofObviousNoMatch
    Obvious.ObviousAntecedentUnavailableClass ->
        DiagnosticProofObviousAntecedentUnavailable
    Obvious.ObviousParameterUndeterminedClass ->
        DiagnosticProofObviousParameterUndetermined
    Obvious.ObviousFalsityPairUnavailableClass ->
        DiagnosticProofObviousFalsityPairUnavailable
    Obvious.ObviousHigherOrderUnsupportedClass ->
        DiagnosticProofObviousHigherOrderUnsupported
    Obvious.ObviousTermOutsideUniverseClass ->
        DiagnosticProofObviousTermOutsideUniverse
    Obvious.ObviousDefinitionEvidenceRequiredClass ->
        DiagnosticProofObviousDefinitionEvidenceRequired
    Obvious.ObviousSaturatedClass -> DiagnosticProofObviousSaturated
    Obvious.ObviousResourceExhaustedClass{} ->
        DiagnosticProofObviousResourceExhausted
    Obvious.ObviousRepeatedStateClass -> DiagnosticProofObviousRepeatedState
    Obvious.ObviousMalformedClass -> DiagnosticProofObviousMalformed
    Obvious.ObviousIntegrityClass -> DiagnosticProofObviousIntegrity

obviousDiagnosticTitle :: Obvious.ObviousFailureClass -> Text
obviousDiagnosticTitle = \case
    Obvious.ObviousNoMatchClass ->
        "obvious inference found no matching conclusion"
    Obvious.ObviousAntecedentUnavailableClass ->
        "a matching theorem has an unavailable antecedent"
    Obvious.ObviousParameterUndeterminedClass ->
        "a theorem parameter could not be determined"
    Obvious.ObviousFalsityPairUnavailableClass ->
        "obvious inference found no contradiction pair"
    Obvious.ObviousHigherOrderUnsupportedClass ->
        "obvious inference does not support this higher-order instance"
    Obvious.ObviousTermOutsideUniverseClass ->
        "a selected term is outside the supported search universe"
    Obvious.ObviousDefinitionEvidenceRequiredClass ->
        "the proof did not use canonical definition evidence"
    Obvious.ObviousSaturatedClass ->
        "obvious inference saturated without a proof"
    Obvious.ObviousResourceExhaustedClass{} ->
        "obvious inference exhausted a bounded resource"
    Obvious.ObviousRepeatedStateClass ->
        "obvious inference reached a repeated state"
    Obvious.ObviousMalformedClass ->
        "obvious inference received malformed checked input"
    Obvious.ObviousIntegrityClass ->
        "obvious inference encountered an internal proof failure"

obviousDiagnosticMessage :: Obvious.ObviousFailureClass -> Text
obviousDiagnosticMessage = \case
    Obvious.ObviousNoMatchClass ->
        "no available local or cited fact had a conclusion matching the checked goal"
    failureClass -> obviousDiagnosticTitle failureClass

obviousDiagnosticHelp
    :: Obvious.ObviousFailureClass
    -> Obvious.ObviousFailureReport ObjectId
    -> [Text]
obviousDiagnosticHelp failureClass report =
    case failureClass of
        Obvious.ObviousNoMatchClass
            | Obvious.obviousFailureHypothesisCount report > 0
                || Obvious.obviousFailureImportCount report > 0 ->
                ["state or cite a fact whose conclusion matches the checked goal"]
        Obvious.ObviousAntecedentUnavailableClass ->
            ["prove or cite the first unresolved theorem antecedent"]
        Obvious.ObviousParameterUndeterminedClass ->
            ["make the theorem parameter explicit in an earlier premise or the goal"]
        Obvious.ObviousFalsityPairUnavailableClass ->
            ["provide both a proposition and its negation in the available evidence"]
        Obvious.ObviousDefinitionEvidenceRequiredClass ->
            ["use a canonical definition equation that participates in the proof"]
        Obvious.ObviousSaturatedClass ->
            ["add an explicit proof step or cite more directly relevant facts"]
        Obvious.ObviousRepeatedStateClass ->
            ["break the recursive proof dependency with an intermediate fact"]
        _failureClass -> []

renderObviousInvocationSite :: ObviousInvocation -> Text
renderObviousInvocationSite
        (ObviousInvocation site _method _groups) =
    case site of
        ImplicitTheoremClose -> "implicit theorem close"
        ImplicitInstanceObligation -> "implicit instance obligation"
        FinalFollows -> "final Follows"
        ContradictionObligation -> "contradiction obligation"
        InlineObviousInference -> "inline inference"

renderObviousInvocationMethod :: ObviousInvocation -> Text
renderObviousInvocationMethod
        (ObviousInvocation _site method _groups) =
    case method of
        ImplicitObvious -> "implicit Obvious"
        CitedObvious -> "cited Obvious"
        DefinitionObvious -> "definition-aware Obvious"

renderHypothesisSection
    :: Obvious.ObviousFailureReport ObjectId
    -> [ProofObviousInputOrigin]
    -> [Text]
renderHypothesisSection report origins =
    renderBoundedInputSection
        "available local facts"
        (Obvious.obviousFailureHypothesisCount report)
        [ "#" <> Text.pack (show index) <> " (" <> description <> "): "
            <> renderObviousCoreSummary summary
        | ( Obvious.ObviousHypothesisObservation _reportedIndex summary
          , ProofObviousLocalOrigin index description
          ) <- zip (Obvious.obviousFailureHypotheses report) origins
        ]

renderImportSection
    :: Obvious.ObviousFailureReport ObjectId
    -> [ProofObviousInputOrigin]
    -> [Text]
renderImportSection report origins =
    renderBoundedInputSection
        "cited facts"
        (Obvious.obviousFailureImportCount report)
        [ description <> " [import "
            <> Text.pack (show index) <> "]: "
            <> renderObviousCoreSummary summary
        | ( Obvious.ObviousImportObservation _reportedIndex summary
          , origin
          ) <- zip (Obvious.obviousFailureImports report) origins
        , (index, description) <- case origin of
            ProofObviousCitedOrigin index group -> [(index, renderCitationGroup group)]
            ProofObviousStructuralOrigin index group -> [(index, "direct-parent view of " <> renderCitationGroup group)]
            _ -> []
        ]

renderDefinitionSection
    :: Text
    -> Natural
    -> [Obvious.ObviousInputObservation ObjectId]
    -> [ProofObviousInputOrigin]
    -> [Text]
renderDefinitionSection title total observations origins =
    renderBoundedInputSection
        title
        total
        [ "#" <> Text.pack (show ordinal) <> " (" <> origin <> ", "
            <> renderDefinitionViewKind kind <> ")"
            <> maybe "" ((": " <>) . renderObviousCoreSummary) summary
        | ( Obvious.ObviousDefinitionObservation
                _reportedOrdinal kind _source summary
          , (ordinal, origin)
          ) <- zip
                observations
                (renderDefinitionOrigin <$> origins)
        ]
  where
    renderDefinitionOrigin = \case
        ProofObviousLocalDefinitionOrigin ordinal description ->
            (ordinal, description)
        ProofObviousImportedDefinitionOrigin ordinal _fingerprint object ->
            (ordinal, "imported " <> renderObjectId object)
        _origin ->
            impossible "validated Obvious definition provenance changed shape"

renderBoundedInputSection :: Text -> Natural -> [Text] -> [Text]
renderBoundedInputSection _title 0 _rows = []
renderBoundedInputSection title total rows =
    [ title <> " (showing " <> Text.pack (show (length rows))
        <> " of " <> Text.pack (show total) <> "): "
        <> Text.intercalate "; " rows
    ]

renderCitationGroup :: ObviousCitationGroup -> Text
renderCitationGroup
        (ObviousCitationGroup _fingerprint first occurrences distinct additional) =
    "`" <> renderMarker first <> "`"
        <> " (" <> Text.pack (show occurrences) <> " occurrence(s), "
        <> Text.pack (show distinct) <> " spelling(s)"
        <> if null additional
            then ")"
            else "; also "
                <> Text.intercalate ", "
                    ["`" <> renderMarker marker <> "`" | marker <- additional]
                <> ")"

renderMarker :: Raw.Marker -> Text
renderMarker (Raw.Marker marker) = marker

renderDefinitionViewKind :: DefinitionViewKind -> Text
renderDefinitionViewKind = \case
    DefinitionExactView -> "exact"
    DefinitionPointwiseView -> "pointwise"
    DefinitionMembershipView -> "membership"

renderFocusedGoalView :: Obvious.ObviousFocusedGoalView ObjectId -> Text
renderFocusedGoalView = \case
    Obvious.ObviousFocusedViewUnavailable -> "unavailable before exposure"
    Obvious.ObviousFocusedExposureFailed failureClass ->
        "exposure failed (" <> obviousDiagnosticTitle failureClass <> ")"
    Obvious.ObviousFocusedViewRetained -> "retained the checked goal"
    Obvious.ObviousFocusedViewChanged summary ->
        "changed by checked beta exposure to "
            <> renderObviousCoreSummary summary

renderFailurePathSuffix :: Obvious.ObviousFailurePath ObjectId -> Text
renderFailurePathSuffix = \case
    Obvious.ObviousValidationFailure ->
        " (not started: validation stopped the run)"
    Obvious.ObviousFocusedOnlyFailure reason ->
        " (not started: " <> case reason of
            Obvious.ObviousRefutationQueryNotStarted ->
                "no ground query was started)"
    Obvious.ObviousCoordinatedFailure ->
        " (ran as part of the scoped search)"

renderCandidateSection
    :: Obvious.ObviousFailureReport ObjectId
    -> [ProofObviousCandidateOrigin]
    -> [Text]
renderCandidateSection report origins =
    [ "focused candidate coverage: "
        <> renderCandidateCoverage
            (Obvious.obviousFailureCandidateCoverage report)
        <> "; retained " <> Text.pack (show (length candidates))
        <> " best observed root comparison(s)"
    ]
    <> [ "best observed focused candidate #"
            <> Text.pack (show index) <> ": "
            <> renderCandidate candidate origin
       | (index, (candidate, origin)) <-
            zip [1 :: Int ..] (zip candidates origins)
       ]
    <> [ "canonical-definition requirement rejected a completed root proof at "
            <> renderCandidateRootView rootView
       | rootView <- Obvious.obviousFailureRootRequirementRejections report
       ]
    <> [ "auxiliary requirement rejection: "
            <> renderCandidateAuxiliaryCause cause
       | cause <- Obvious.obviousFailureAuxiliaryCauses report
       ]
    <> [ "additional auxiliary requirement rejections: "
            <> Text.pack (show additional)
       | let additional =
                Obvious.obviousFailureAdditionalAuxiliaryCauseCount report
       , additional > 0
       ]
  where
    candidates = Obvious.obviousFailureCandidates report

renderCandidateCoverage :: Obvious.CandidateCoverage -> Text
renderCandidateCoverage = \case
    Obvious.CandidateObservationNotStarted -> "not started"
    Obvious.CandidateObservationFinished -> "finished"
    Obvious.CandidateObservationStoppedEarly -> "stopped early (partial)"

renderCandidate
    :: Obvious.ObviousCandidateObservation ObjectId
    -> ProofObviousCandidateOrigin
    -> Text
renderCandidate candidate
        (ProofObviousCandidateOrigin base factDefinitions goalDefinitions) =
    base
        <> "; view: " <> renderCandidateView (Obvious.obviousCandidateView candidate)
        <> "; root: "
        <> renderCandidateRootView (Obvious.obviousCandidateRootView candidate)
        <> "; compared: "
        <> renderObviousCoreSummary (Obvious.obviousCandidateProposition candidate)
        <> "; outcome: "
        <> renderCandidateOutcome (Obvious.obviousCandidateOutcome candidate)
        <> "; progress: "
        <> Text.pack (show (Obvious.obviousCandidateProgress candidate))
        <> renderCandidateDifference
            (Obvious.obviousCandidateStructuralDifference candidate)
        <> renderCandidateDefinitionParticipation
            (Obvious.obviousCandidateDefinitionParticipation candidate)
            factDefinitions goalDefinitions
        <> maybe "" (("; auxiliary cause: " <>) . renderCandidateAuxiliaryCause)
            (Obvious.obviousCandidateAuxiliaryCause candidate)

renderCandidateView :: Obvious.CandidateComparisonView -> Text
renderCandidateView = \case
    Obvious.CandidateDirectView -> "direct exact"
    Obvious.CandidateProjectedView depth ->
        "conjunction projection depth " <> Text.pack (show depth)
    Obvious.CandidatePreparedTheoremView depth ->
        "prepared theorem conclusion"
            <> projectionSuffix depth
    Obvious.CandidateEqualityTransportView depth ->
        "equality transport"
            <> projectionSuffix depth
  where
    projectionSuffix 0 = ""
    projectionSuffix depth =
        " after projection depth " <> Text.pack (show depth)

renderCandidateRootView :: Obvious.CandidateRootGoalView -> Text
renderCandidateRootView = \case
    Obvious.CandidateOriginalGoalView -> "original goal"
    Obvious.CandidateDefinitionGoalView ordinals truncated ->
        "goal-definition view " <> renderOrdinalLineage ordinals truncated

renderCandidateOutcome :: Obvious.CandidateOutcome -> Text
renderCandidateOutcome = \case
    Obvious.ComparisonRejected mismatch ->
        "comparison rejected (" <> case mismatch of
            Obvious.SyntacticMismatch -> "syntactic mismatch)"
            Obvious.ConversionMismatch -> "conversion mismatch)"
            Obvious.BinderMismatch -> "binder mismatch)"
            Obvious.MismatchDetailUnavailable -> "detail unavailable)"
    Obvious.ProofIncomplete reason ->
        "root matched; proof incomplete (" <> case reason of
            Obvious.ParameterUndetermined -> "parameter undetermined)"
            Obvious.AntecedentUnavailable -> "antecedent unavailable)"
            Obvious.TransportPremiseUnavailable ->
                "transport premise unavailable)"
    Obvious.ProofRejectedByRequirement ->
        "completed proof rejected by canonical-definition requirement"

renderCandidateDifference
    :: Maybe Obvious.CandidateStructuralDifference
    -> Text
renderCandidateDifference Nothing = ""
renderCandidateDifference
        (Just (Obvious.CandidateStructuralDifference path truncated)) =
    "; first structural difference: "
        <> (if null path
            then "root"
            else Text.intercalate "." (renderStep <$> path))
        <> if truncated then ".…" else ""
  where
    renderStep = \case
        Obvious.CandidateFirstChild -> "first"
        Obvious.CandidateSecondChild -> "second"
        Obvious.CandidateBodyChild -> "body"

renderCandidateDefinitionParticipation
    :: Obvious.CandidateDefinitionParticipation
    -> [Text]
    -> [Text]
    -> Text
renderCandidateDefinitionParticipation participation fact goal =
    case participation of
        Obvious.CandidateNoDefinitionParticipation ->
            "; definition participation: none"
        Obvious.CandidateFactDefinitionParticipation{} ->
            "; fact-definition participation: " <> renderLabels fact
        Obvious.CandidateGoalDefinitionParticipation{} ->
            "; goal-definition participation: " <> renderLabels goal
        Obvious.CandidateFactAndGoalDefinitionParticipation{} ->
            "; fact-definition participation: " <> renderLabels fact
                <> "; goal-definition participation: " <> renderLabels goal
  where
    renderLabels labels
        | null labels = "<none retained>"
        | otherwise = Text.intercalate ", " labels

renderOrdinalLineage :: [Natural] -> Bool -> Text
renderOrdinalLineage ordinals truncated =
    "[" <> Text.intercalate ", "
        ["#" <> Text.pack (show ordinal) | ordinal <- ordinals]
        <> (if truncated then ", …" else "") <> "]"

renderCandidateAuxiliaryCause :: Obvious.CandidateAuxiliaryCause -> Text
renderCandidateAuxiliaryCause
        (Obvious.CandidateAuxiliaryRequirementRejected kind) =
    "canonical-definition evidence was unavailable in "
        <> case kind of
            Obvious.AuxiliaryIntroductionComponent -> "an introduction component"
            Obvious.AuxiliaryDisjunctionBranch -> "a disjunction branch"
            Obvious.AuxiliaryImplicationBody -> "an implication body"
            Obvious.AuxiliaryNegationBody -> "a negation body"
            Obvious.AuxiliaryUniversalBody -> "a universal body"
            Obvious.AuxiliaryExistentialBranch -> "an existential elimination branch"
            Obvious.AuxiliaryTheoremAntecedent -> "a theorem antecedent"
            Obvious.AuxiliaryTransportPremise -> "a transport premise"

renderObviousTierOutcome :: Obvious.ObviousTierOutcome -> Text
renderObviousTierOutcome = \case
    Obvious.ObviousTierNotStarted -> "not started"
    Obvious.ObviousTierNotCompleted -> "not completed"
    Obvious.ObviousTierCandidateBuilt -> "candidate built"
    Obvious.ObviousTierNoProof -> "no proof"
    Obvious.ObviousTierUnsupported -> "unsupported"
    Obvious.ObviousTierResourceExhausted limit ->
        "resource exhausted (" <> renderObviousLimit limit <> ")"
    Obvious.ObviousTierIntegrityFailure -> "integrity failure"

renderObviousCoreSummary
    :: Obvious.ObviousCoreSummary ObjectId
    -> Text
renderObviousCoreSummary
        (Obvious.ObviousCoreSummary context contextTruncated coreType term) =
    contextPrefix
        <> renderObviousTermSummary term
        <> " : " <> renderObviousTypeSummary coreType
  where
    contextPrefix
        | null context && not contextTruncated = ""
        | otherwise =
            "[" <> Text.intercalate ", "
                (renderObviousTypeSummary <$> context)
                <> (if contextTruncated then ", …" else "")
                <> "] |- "

renderObviousTypeSummary :: Obvious.ObviousTypeSummary -> Text
renderObviousTypeSummary = \case
    Obvious.ObviousTypeProposition -> "Prop"
    Obvious.ObviousTypeSet -> "Set"
    Obvious.ObviousTypeArrow argument result ->
        "(" <> renderObviousTypeSummary argument
            <> " -> " <> renderObviousTypeSummary result <> ")"
    Obvious.ObviousTypeTruncated -> "…"

renderObviousTermSummary
    :: Obvious.ObviousTermSummary ObjectId
    -> Text
renderObviousTermSummary = \case
    Obvious.ObviousBoundVariable index -> "$" <> Text.pack (show index)
    Obvious.ObviousGlobal object -> renderObjectId object
    Obvious.ObviousGlobalTruncated -> "<global …>"
    Obvious.ObviousIntrinsic intrinsic -> renderIntrinsic intrinsic
    Obvious.ObviousLogicalSelection coreType ->
        "logical-select[" <> renderObviousTypeSummary coreType <> "]"
    Obvious.ObviousOpaqueInteger integer _truncated -> integer
    Obvious.ObviousApplication function argument ->
        "app(" <> renderObviousTermSummary function <> ", "
            <> renderObviousTermSummary argument <> ")"
    Obvious.ObviousLambda binderType body ->
        "lambda[" <> renderObviousTypeSummary binderType <> "]. "
            <> renderObviousTermSummary body
    Obvious.ObviousFalsum -> "false"
    Obvious.ObviousTruth -> "true"
    Obvious.ObviousNegation proposition ->
        "not(" <> renderObviousTermSummary proposition <> ")"
    Obvious.ObviousConjunction left right ->
        binary "and" left right
    Obvious.ObviousDisjunction left right ->
        binary "or" left right
    Obvious.ObviousImplication premise conclusion ->
        binary "implies" premise conclusion
    Obvious.ObviousEquality operandType left right ->
        "equals[" <> renderObviousTypeSummary operandType <> "]("
            <> renderObviousTermSummary left <> ", "
            <> renderObviousTermSummary right <> ")"
    Obvious.ObviousUniversal binderType body ->
        "forall[" <> renderObviousTypeSummary binderType <> "]. "
            <> renderObviousTermSummary body
    Obvious.ObviousExistential binderType body ->
        "exists[" <> renderObviousTypeSummary binderType <> "]. "
            <> renderObviousTermSummary body
    Obvious.ObviousTermTruncated -> "…"
  where
    binary name left right =
        name <> "(" <> renderObviousTermSummary left <> ", "
            <> renderObviousTermSummary right <> ")"

renderObjectId :: ObjectId -> Text
renderObjectId object =
    family <> ":" <> Text.take 12
        (mathematicalDigestHex (objectIdDigest object))
  where
    family = case objectIdFamily object of
        IntrinsicObject -> "intrinsic"
        TransparentObject -> "transparent"
        OpaqueObject -> "opaque"

renderIntrinsic :: CoreIntrinsicTag -> Text
renderIntrinsic = \case
    Member -> "member"
    Felix.Checking.Core.Empty -> "empty"
    PairSet -> "pair-set"
    FamilyUnion -> "family-union"
    PowerSet -> "power-set"
    Sep -> "separation"
    Repl -> "replacement"
    UnivOf -> "universe-of"
    ISetLfp -> "bounded-lfp"
    GlobalChoice -> "global-choice"
    OrderedPair -> "ordered-pair"
    FirstProjection -> "first-projection"
    SecondProjection -> "second-projection"

goalShape :: ScopedCheckedCore global -> GoalShape
goalShape goal =
    case scopedCoreTerm goal of
        CForall{} -> UniversalGoal
        CEq{} -> EqualityGoal
        CNot{} -> NegationGoal
        CAnd{} -> ConjunctionGoal
        COr{} -> DisjunctionGoal
        CExists{} -> ExistentialGoal
        CImp{} -> ImplicationGoal
        _ -> OtherPropositionGoal

isAssumptiveGoal :: ScopedCheckedCore global -> Bool
isAssumptiveGoal goal =
    case scopedCoreTerm goal of
        CImp{} -> True
        CNot{} -> True
        COr{} -> True
        _ -> False

renderGoalShape :: GoalShape -> Text
renderGoalShape = \case
    UniversalGoal -> "universal quantification"
    ImplicationGoal -> "implication"
    NegationGoal -> "negation"
    EqualityGoal -> "equality"
    ConjunctionGoal -> "conjunction"
    DisjunctionGoal -> "disjunction"
    ExistentialGoal -> "existential quantification"
    OtherPropositionGoal -> "another proposition"

renderVariableNames :: NonEmpty Raw.VarSymbol -> Text
renderVariableNames =
    Text.intercalate ", " . fmap renderVariableName . NonEmpty.toList

renderVariableName :: Raw.VarSymbol -> Text
renderVariableName = \case
    Raw.NamedVarAt _location name -> "`" <> name <> "`"
    Raw.FreshVarAt _location ordinal ->
        "an implicit binder #" <> Text.pack (show ordinal)

inductionNameNotes :: NonEmpty Raw.VarSymbol -> [Doc ()]
inductionNameNotes names =
    pretty
        ("eligible binders: "
            <> Text.intercalate ", " (renderVariableName <$> retained))
        : [ pretty
                (Text.pack (show omitted)
                    <> " additional eligible binders omitted")
          | omitted > 0
          ]
  where
    displayLimit = 8
    complete = NonEmpty.toList names
    retained = take displayLimit complete
    omitted = length complete - length retained

data ProofLocalOrigin
    = ProofAssumption
    | ProofDerivedClaim
    | ProofLocalDefinition
    | ProofLocalConstructionExtensional
    | ProofLocalConstructionEquation
    deriving stock (Show, Eq, Ord)

data PreparedLocal = PreparedLocal
    !Backend.LocalPremiseOrdinal
    !ProofLocalOrigin
    !(Vector (Elaboration.LocalId, CoreType))
    !(ScopedCheckedCore ObjectId)

data EvidenceProjection
    = EvidenceProjectionLeft
    | EvidenceProjectionRight
    deriving stock (Show, Eq, Ord)

data EvidenceRow = EvidenceRow
    !PreparedLocal
    !(ScopedCheckedCore ObjectId)
    ![EvidenceProjection]

data ExactEvidenceView = ExactEvidenceView
    ![EvidenceRow]
    !(Map (ScopedCheckedCore ObjectId) (NonEmpty EvidenceRow))

data NormalizedEvidenceRow = NormalizedEvidenceRow
    !EvidenceRow
    !Elaboration.FormationAliasNormalization

data NormalizedExactEvidenceView = NormalizedExactEvidenceView
    ![NormalizedEvidenceRow]
    !(Map
        (ScopedCheckedCore ObjectId)
        (NonEmpty NormalizedEvidenceRow))

-- | Preserve the source spine alongside its checked target. Logical proof
-- transformations may forget rich occurrences while keeping whole identity.
data PreparedProofGoal = PreparedProofGoal
    !(ScopedCheckedCore ObjectId)
    !(SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence)

plainPreparedProofGoal
    :: ScopedCheckedCore ObjectId -> PreparedProofGoal
plainPreparedProofGoal goal = PreparedProofGoal goal (SourceEvidence.SourceResidual Nothing)

sourcePreparedProofGoal
    :: ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence
    -> PreparedProofGoal
sourcePreparedProofGoal = PreparedProofGoal

preparedProofGoalCore
    :: PreparedProofGoal
    -> ScopedCheckedCore ObjectId
preparedProofGoalCore (PreparedProofGoal goal _notion) = goal

data PreparedJustification
    = PreparedInternalAuto
    | PreparedAuto
        !(Maybe (NonEmpty SemanticFactOccurrenceFingerprint))
    | PreparedImplicitObvious
    | PreparedObviousReferences
        !(NonEmpty SemanticFactOccurrenceFingerprint)
    | PreparedAssumption
    | PreparedDefinition
    | PreparedNotion
    | PreparedSetExtensionality
    | PreparedRecordExtensionality

data PreparedDischarge
    = PreparedPreparationLimit !Preparation.PreparationStatistics !PreparedDischarge
    | PreparedDefinitionDischarge !PreparedDischarge
    | PreparedRecursiveEquation !Location !Recursive.RecursiveApplication
        !PreparedDischarge !(KernelDerivation ObjectId)
    | PreparedFormationDischarge !FormationDiagnostics.Completion !PreparedDischarge
    | PreparedEqualityDischarge !Location !(ScopedCheckedCore ObjectId)
        !PreparedLocal !PreparedDischarge !PreparedDischarge
    | PreparedEvidenceDischarge !Location !(ScopedCheckedCore ObjectId)
        !PreparedLocal !PreparedDischarge !PreparedDischarge
    | PreparedUniversalDischarge !Location !(ScopedCheckedCore ObjectId)
        !CoreType !Elaboration.LocalId !PreparedDischarge
    | PreparedImplicationDischarge !Location !(ScopedCheckedCore ObjectId)
        !PreparedLocal !PreparedDischarge
    | PreparedVampireDischarge
        !Location
        !PreparedJustification
        !(ScopedCheckedCore ObjectId)
        !(Declaration.PreparedVampireObligation
            Elaboration.LocalId
            ProofLocalOrigin)
    | PreparedExcludedMiddle
        !Location
        !(ScopedCheckedCore ObjectId)
    | PreparedKernelDischarge
        !Location
        !PreparedJustification
        !(ScopedCheckedCore ObjectId)
        ![PreparedLocal]
        ![SemanticFactOccurrenceFingerprint]
        !(KernelDerivation ObjectId)
    | PreparedKernelComposition
        !Location
        !(ScopedCheckedCore ObjectId)
        -- Direct facts justify the composition itself.  Children may
        -- intentionally exclude them from their Vampire premise vectors.
        ![SemanticFactOccurrenceFingerprint]
        !(NonEmpty PreparedDischarge)
        !(KernelDerivation ObjectId)

data PreparedCase = PreparedCase
    !(ScopedCheckedCore ObjectId)
    !PreparedProofTree

data PreparedCaseAnalysis = PreparedCaseAnalysis
    !(ScopedCheckedCore ObjectId)
    !(NonEmpty PreparedCase)
    !(ScopedCheckedCore ObjectId)
    !PreparedDischarge

data InitialSetInductionFocus = InitialSetInductionFocus
    !Raw.VarSymbol
    !Elaboration.LocalId
    !Natural

data InitialSetInductionView = InitialSetInductionView
    ![InitialSetInductionFocus]
    !(Vector (Elaboration.LocalId, CoreType))
    !(ScopedCheckedCore ObjectId)
    ![ScopedCheckedCore ObjectId]
    !(ScopedCheckedCore ObjectId)
    !(Maybe Raw.VarSymbol)

data SetInductionBoundary
    = InitialClaimInduction !InitialSetInductionView
    -- A direct source-statement goal may retain only its leading binder name.
    -- Recursive proof transformations deliberately discard this hint.
    | SourceStatementInduction !(Maybe Raw.VarSymbol)
    | RecursiveProofInduction

data SelectedSetInductionFocus
    = SelectedInitialSetInduction !InitialSetInductionFocus
    | SelectedLeadingSetInduction !(Maybe Raw.VarSymbol)

data PreparedSetInductionFocus
    = PreparedInitialSetInductionFocus
        !Elaboration.LocalId
        !Natural
    | PreparedLeadingSetInductionFocus
        !Elaboration.LocalId

data PreparedSetInduction = PreparedCheckedSetInduction
    !PreparedSetInductionFocus
    !(ScopedCheckedCore ObjectId)
    ![ScopedCheckedCore ObjectId]
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)
    !(ScopedCheckedCore ObjectId)
    !PreparedProofTree

data PreparedProofTree
    = PreparedImplicitDischarge !PreparedDischarge
    | PreparedQed !PreparedDischarge
    | PreparedOmitted
        !Location
        !(ScopedCheckedCore ObjectId)
    | PreparedFix ![Elaboration.LocalId] !PreparedProofTree
    | PreparedAssume
        !(LooseDeduction.AssumptionOpening ObjectId)
        !PreparedProofTree
    | PreparedGuardAssume
        !(ScopedCheckedCore ObjectId)
        !PreparedProofTree
    | PreparedTake
        ![Elaboration.LocalId]
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !PreparedProofTree
    | PreparedSetInduction !PreparedSetInduction
    | PreparedHave
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !PreparedProofTree
    | PreparedSuffices
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !PreparedProofTree
    | PreparedCalculate
        !PreparedDischarge
        !PreparedProofTree
    | PreparedSince
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !PreparedLocal
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !PreparedProofTree
    | PreparedSubclaim
        !(ScopedCheckedCore ObjectId)
        !PreparedProofTree
        !PreparedProofTree
    | PreparedDefine
        !Elaboration.LocalId
        !(ScopedCheckedCore ObjectId)
        !(NonEmpty (ScopedCheckedCore ObjectId))
        !PreparedProofTree
    | PreparedDefineRelational
        !Elaboration.LocalId
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge
        !(NonEmpty (ScopedCheckedCore ObjectId))
        !PreparedProofTree
    | PreparedDefineFunction
        !Elaboration.LocalId
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !PreparedProofTree
    | PreparedByCase !PreparedCaseAnalysis
    | PreparedByContradiction
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !PreparedProofTree
    | PreparedContradiction
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !PreparedDischarge

data PreparedProof = PreparedProof
    !Location
    !SemanticName
    !(ScopedCheckedCore ObjectId)
    !PreparedProofTree
    !ProofPlanningSummary
    !(Maybe SemanticRelationComposition)
    !(Maybe [(Notion.ConjunctionPath, RegistrationBody)])
    !ProofSyntaxId
    ![(Location, Preparation.PreparationStatistics)]
    ![Obligation.RecordObligation]

data ProofPlanningSummary = ProofPlanningSummary
    { proofPlanningFirstOmission :: !(Maybe Location)
    , proofPlanningRequests :: ![Declaration.CheckedPlannedVampireRequest]
    , proofPlanningFacts :: ![SemanticFactOccurrenceFingerprint]
    }

data PreparedFinalPreludeFoundationClaim =
    PreparedFinalPreludeFoundationClaim
    !Location
    !SemanticName
    !(ScopedCheckedCore ObjectId)
    !FoundationAxiomTag
    !ProofSyntaxId

data PreparedFinalPreludeGuardedRuleClaim =
    PreparedFinalPreludeGuardedRuleClaim
    !Location
    !SemanticName
    !(ScopedCheckedCore ObjectId)
    !KernelRuleTag
    !(KernelDerivation ObjectId)
    !ProofSyntaxId

preparedProofSyntaxId :: PreparedProof -> ProofSyntaxId
preparedProofSyntaxId
        (PreparedProof _location _alias _target _proof _summary _composition
            _notionRegistration syntax _statistics _obligations) =
    syntax

preparedProofTarget
    :: PreparedProof
    -> ScopedCheckedCore ObjectId
preparedProofTarget
        (PreparedProof _location _alias target _proof _summary _composition
            _notionRegistration _syntax _statistics _obligations) =
    target

preparedProofFirstOmission :: PreparedProof -> Maybe Location
preparedProofFirstOmission
        (PreparedProof _location _alias _target _proof summary _composition
            _notionRegistration _syntax _statistics _obligations) =
    proofPlanningFirstOmission summary

preparedProofPreparationStatistics :: PreparedProof -> [(Location, Preparation.PreparationStatistics)]
preparedProofPreparationStatistics (PreparedProof _ _ _ _ _ _ _ _ statistics _) = statistics

data PrepareState = PrepareState
    { prepareNextLocal :: !Natural
    , prepareNextPremise :: !Natural
    , prepareAutomaticStatistics :: ![(Location, Preparation.PreparationStatistics)]
    , prepareRecursiveRequest :: !(Maybe RecursiveRequest)
    }

data RecursiveRequest = RecursiveRequest
    { requestAllowance :: !Obvious.ObviousAllowance
    , requestPreparation :: !Preparation.PreparationSession
    , requestFormation :: !Notion.FormationSearchBudget
    , requestOriginalGoal :: !(ScopedCheckedCore ObjectId)
    , requestDefinitions :: !(ObjectId -> [RecursiveInterface.CheckedRecursiveDefinition])
    , requestPriorObvious :: ![Obvious.ObviousStatistics]
    , requestSelectedFacts :: ![(SemanticFactOccurrenceFingerprint, CheckedPropositionContent)]
    , requestApplications :: !(Map
        (GlobalBindingRef,Vector (Elaboration.LocalId,CoreType),[Natural])
        [(ScopedCheckedCore ObjectId,(Recursive.RecursiveApplication,PreparedDischarge))])
    , requestFormationFailure :: !(Maybe Notion.FormationSearchError)
    , requestGuardQueries :: !Natural
    , requestReusedApplications :: !Natural
    }

currentRecursiveRequest :: Prepare RecursiveRequest
currentRecursiveRequest = State.gets prepareRecursiveRequest >>= maybe
    (impossible "recursive preparation escaped its source request") pure

modifyRecursiveRequest :: (RecursiveRequest -> RecursiveRequest) -> Prepare ()
modifyRecursiveRequest change = State.modify' (\state -> state
    {prepareRecursiveRequest = change <$> prepareRecursiveRequest state})

recursiveRequestNotes :: RecursiveRequest -> [Text]
recursiveRequestNotes request =
    [ "Obvious phase " <> count index <> ": focused "
        <> renderObviousTierOutcome (Obvious.obviousFocusedTierOutcome statistics)
        <> "; refutation " <> renderObviousTierOutcome (Obvious.obviousRefutationTierOutcome statistics)
        <> "; work " <> count (Obvious.obviousFocusedWorkConsumed statistics)
        <> "/" <> count (Obvious.obviousRefutationWorkConsumed statistics)
        <> "/" <> count (Obvious.obviousConversionWorkConsumed statistics)
    | (index,statistics) <- zip [1 :: Int ..] (requestPriorObvious request)]
    <> ["recursive preparation: " <> count (Preparation.preparationUsedWork preparation)
        <> "/" <> count (Preparation.preparationWorkLimit preparation) <> " work"]
    <> ["recursive guards queried: " <> count (requestGuardQueries request)
        <> "; applications reused: " <> count (requestReusedApplications request)]
    <> [Preparation.renderPreparationExhaustion preparation | Preparation.preparationExhausted preparation]
    <> ["recursive guard preparation exhausted: " <> Notion.renderFormationSearchError failure
        | failure <- toList (requestFormationFailure request)]
  where
    count :: Show value => value -> Text
    count = Text.pack . show
    preparation = Preparation.preparationStatistics (requestPreparation request)

prepareRecursiveCore
    :: Location -> (Word -> (Either (CountedCoreFailure Text) value, Word))
    -> Prepare (Maybe value)
prepareRecursiveCore location operation = do
    request <- currentRecursiveRequest
    let (result,balance) = Preparation.runPreparationWork operation (requestPreparation request)
    modifyRecursiveRequest (\current -> current {requestPreparation = balance})
    either (structuralFailure location) pure result

prepareRecursiveSource
    :: Location -> ExpansionWork Declaration.LoweringDriver value -> Prepare (Maybe value)
prepareRecursiveSource location action = do
    request <- currentRecursiveRequest
    (result,balance) <- liftDriver (Preparation.runPreparationWorkM
        (\work -> do
            (answer,remaining) <- runExpansionWork work action
            pure (Bifunctor.first (\failure -> case expansionRejectedDebit failure of
                Just _ -> CountedCoreStructuralWorkExhausted
                Nothing -> CountedCoreOperationFailed (renderExpansionFailure failure)) answer,remaining))
        (requestPreparation request))
    modifyRecursiveRequest (\current -> current {requestPreparation = balance})
    either (structuralFailure location) pure result

prepareRecursiveKernel
    :: Location -> KernelProof.CountedProof ObjectId value -> Prepare (Maybe value)
prepareRecursiveKernel location operation = do
    request <- currentRecursiveRequest
    let pool = Obvious.obviousConversionPool (Obvious.obviousRemainingBudget (requestAllowance request))
        (result,balance,remaining) = Preparation.runPreparationProof pool operation (requestPreparation request)
        consumed = Conversion.conversionPoolAmount pool - Conversion.conversionPoolAmount remaining
    allowance <- maybe (impossible "recursive preparation overspent its conversion pool") pure
        (Obvious.debitObviousConversion consumed (requestAllowance request))
    modifyRecursiveRequest (\current -> current {requestPreparation = balance,requestAllowance = allowance})
    either (throwProof . ProofStructuralCompositionFailed location) pure result

-- Logical introductions belong to the source host: its proof context and
-- formation context advance together, with the same local origins.
prepareRecursiveScopes
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> (Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal -> Prepare PreparedDischarge)
    -> Prepare PreparedDischarge
prepareRecursiveScopes location context locals prepared@(PreparedProofGoal target evidence) residual = do
    foundation <- liftDriver Declaration.currentFoundationLowering
    typing <- prepareGlobalTyping
    checked <- prepareRecursiveKernel location (KernelProof.countedScopedProofContext
        foundation typing (scopedCoreContext target) (preparedLocalProposition <$> locals))
    case checked of
        Nothing -> residual context locals prepared
        Just proofContext -> do
            request <- currentRecursiveRequest
            let (opened,balance) = Preparation.openPreparationGoal (requestPreparation request) proofContext target
            modifyRecursiveRequest (\current -> current {requestPreparation = balance})
            plan <- either (throwProof . ProofStructuralCompositionFailed location) pure opened
            case Preparation.preparationView plan of
                Preparation.PreparationConjunction _ left right -> do
                    let (a,b) = case sourceBody evidence of
                            SourceEvidence.SourceAnd x y -> (x,y)
                            _ -> (opaque,opaque)
                    leftGoal <- retainInputs 0 (Preparation.preparationGoal left) a
                    rightGoal <- retainInputs 0 (Preparation.preparationGoal right) b
                    l <- recur context locals leftGoal
                    r <- recur context locals rightGoal
                    pure (PreparedKernelComposition location target [] (l :| [r]) conjunctionDerivation)
                Preparation.PreparationUniversal _ ty nested child -> do
                    identity <- allocateLocalIdentity
                    extended <- either (throwProof . ProofElaborationFailed) pure
                        (Elaboration.extendTypedAnonymousElaborationContext ty identity context)
                    let support = Elaboration.elaborationContextSupport extended
                        weakened = zipWith (\(PreparedLocal ordinal origin _ _) proposition ->
                            PreparedLocal ordinal origin support proposition) locals (KernelProof.proofContextHypotheses nested)
                        description = case sourceBody evidence of
                            SourceEvidence.SourceBind body -> body
                            _ -> opaque
                    childGoal <- retainInputs 1 (Preparation.preparationGoal child) description
                    proof <- recur extended weakened childGoal
                    pure (PreparedUniversalDischarge location target ty identity proof)
                Preparation.PreparationImplication _ premise _ child -> do
                    let (condition,body) = case sourceBody evidence of
                            SourceEvidence.SourceRequire a b -> (a,b)
                            _ -> (opaque,opaque)
                    local <- allocateLocal ProofAssumption context premise
                    PreparedProofGoal _ conditionEvidence <- retainInputs 0 premise condition
                    extended <- extendContextWithSourceLocal local conditionEvidence [] context
                    childGoal <- retainInputs 0 (Preparation.preparationGoal child) body
                    proof <- recur extended (local:locals) childGoal
                    pure (PreparedImplicationDischarge location target local proof)
                Preparation.PreparationHole{} -> do
                    evaluated <- evaluateRecursiveExpression location context locals prepared proofContext target
                    case evaluated of
                        Nothing -> prepareRecursiveFacts location context locals prepared proofContext residual
                        Just (rewritten,equality) -> do
                            local <- allocateLocal ProofDerivedClaim context (preparedDischargeGoal equality)
                            child <- recur context locals rewritten
                            pure (PreparedEqualityDischarge location target local equality child)
                _ -> impossible "a single logical opening produced an unrelated refinement"
  where
    recur = \nested nestedLocals child -> prepareRecursiveScopes location nested nestedLocals child residual
    opaque = SourceEvidence.SourceResidual Nothing
    sourceBody (SourceEvidence.SourceWithInputs _ body) = sourceBody body
    sourceBody body = body
    -- Additive written operands survive logical projection. Only genuine
    -- binder introduction shifts them; the child's own evidence stays scoped.
    retainInputs depth child description = case evidence of
        SourceEvidence.SourceWithInputs{} -> carry
        SourceEvidence.SourceInputs{} -> carry
        _ -> pure (PreparedProofGoal child description)
      where
        carry = do
            typing <- prepareGlobalTyping
            retained <- prepareRecursiveSource location do
                written <- RecursiveSource.writtenOperands typing location target evidence
                shifted <- traverse (\term -> expansionCoreWork (\work ->
                    SourceTerm.countedShiftCanonicalSourceTermOccurrence work depth 0 term)) written
                pure (PreparedProofGoal child (SourceEvidence.withSourceInputs
                    [SourceEvidence.SourceInput [] (SourceTerm.sourceSupportTemplate id term) | term <- shifted] description))
            pure (fromMaybe (PreparedProofGoal child description) retained)

prepareRecursiveCall
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> KernelProof.ProofContext ObjectId -> ScopedCheckedCore ObjectId
    -> Prepare (Maybe (PreparedProofGoal,PreparedDischarge))
prepareRecursiveCall location context locals source proofContext call = do
    request <- currentRecursiveRequest
    headTerm <- prepareRecursiveCore location (\work -> headWithin work (scopedCoreTerm call))
    case headTerm of
        Just (CGlobal object) -> case requestDefinitions request object of
            families@(_:_:_) -> do
                let PreparedProofGoal sourceGoal sourceEvidence = source
                preferred <- prepareRecursiveSource location (RecursiveSource.preferredBindings
                    (KernelProof.proofContextGlobalTyping proofContext) location call sourceGoal sourceEvidence)
                let (written,others) = List.partition
                        ((`elem` fromMaybe [] preferred) . RecursiveInterface.recursiveBinding) families
                select (written <> others)
            families -> select families
        _ -> pure Nothing
  where
    headWithin 0 _ = (Left CountedCoreStructuralWorkExhausted,0)
    headWithin work (CApp function _) = headWithin (work - 1) function
    headWithin work term = (Right term,work - 1)
    select [] = pure Nothing
    select (definition:rest) = do
        let key = (RecursiveInterface.recursiveBinding definition,Elaboration.elaborationContextSupport context,
                preparedLocalOrdinalValue <$> locals)
        charged <- prepareRecursiveCore location \work ->
            let amount = fromIntegral (1 + Vector.length (Elaboration.elaborationContextSupport context) + length locals)
            in if work < amount then (Left CountedCoreStructuralWorkExhausted,0) else (Right (),work - amount)
        case charged of
          Nothing -> pure Nothing
          Just () -> do
            request <- currentRecursiveRequest
            reused <- cached definition (Map.findWithDefault [] key (requestApplications request))
            case reused of
              Just result -> pure (Just result)
              Nothing -> do
                matched <- prepareRecursiveCore location (\work -> Recursive.matchRecursiveApplication work proofContext definition call)
                case join matched of
                  Nothing -> select rest
                  Just application -> apply key definition application rest
    cached _ [] = pure Nothing
    cached definition ((previous,(application,proof)):rest) = do
        same <- prepareRecursiveCore location (\work -> Bifunctor.first (Bifunctor.first (fmap absurd))
            (countedScopedCoreIdentity work previous call))
        case same of
            Nothing -> pure Nothing
            Just False -> cached definition rest
            Just True -> do
                copied <- copyRecursiveDischarge location proof
                branch <- describe definition application
                case (copied,branch) of
                    (Just retained,Just (body,evidence)) -> case splitScopedEquality (preparedDischargeGoal retained) of
                        Just (_,_,expected) -> do
                            sameBody <- prepareRecursiveCore location (\work -> Bifunctor.first (Bifunctor.first (fmap absurd))
                                (countedScopedCoreIdentity work body expected))
                            case sameBody of
                                Just True -> do
                                    modifyRecursiveRequest (\request -> request
                                        {requestReusedApplications = requestReusedApplications request + 1})
                                    pure (Just (PreparedProofGoal body evidence,retained))
                                Nothing -> pure Nothing
                                _ -> structuralFailure location "a cached recursive application changed its branch"
                        _ -> impossible "a cached recursive application lost its equality"
                    _ -> pure Nothing
    describe definition application = prepareRecursiveSource location do
        let PreparedProofGoal sourceGoal sourceEvidence = source
            typing = KernelProof.proofContextGlobalTyping proofContext
        written <- RecursiveSource.writtenOperands typing location sourceGoal sourceEvidence
        RecursiveSource.branchSource typing location definition application written
    apply key definition application rest = do
        guardProof <- prepareRecursiveGuard location context locals source definition application
        case guardProof of
            Nothing -> select rest
            Just child -> do
                foundation <- liftDriver Declaration.currentFoundationLowering
                applied <- prepareRecursiveKernel location do
                    applicationContext <- KernelProof.countedScopedProofContext
                        foundation (KernelProof.proofContextGlobalTyping proofContext)
                        (scopedCoreContext call) [Recursive.applicationGuard application]
                    premise <- KernelProof.countedIndexedHypothesisProof applicationContext (hypothesisIx 0)
                    Recursive.applyRecursiveEquation applicationContext (importIx 0) application premise
                case applied of
                    Nothing -> completeDiscardedRecursiveEvidence child >> pure Nothing
                    Just proof -> do
                        let equation = PreparedRecursiveEquation location application child (KernelProof.builtProofDerivation proof)
                        branch <- describe definition application
                        case branch of
                            Nothing -> completeDiscardedRecursiveEvidence equation >> pure Nothing
                            Just (body,evidence) -> do
                                converted <- prepareRecursiveComposition location (equation :| []) \current -> do
                                    premise <- KernelProof.countedIndexedHypothesisProof current (hypothesisIx 0)
                                    target <- KernelProof.countedScopedTerm current
                                        (CEq (scopedCoreType call) (scopedCoreTerm call) (scopedCoreTerm body))
                                    KernelProof.countedConversionProof current premise target
                                when (isNothing converted) (completeDiscardedRecursiveEvidence equation)
                                let result = (,) (PreparedProofGoal body evidence) <$> converted
                                for_ converted \completed -> modifyRecursiveRequest (\request -> request
                                    {requestApplications = Map.insertWith (<>) key [(call,(application,completed))] (requestApplications request)})
                                pure result

-- A reused recipe is still a proof tree: charge its targets and derivations.
-- The first occurrence owns the formation diagnostic completion. Copies have
-- their own ordinary kernel replay and do not recount the original query.
copyRecursiveDischarge :: Location -> PreparedDischarge -> Prepare (Maybe PreparedDischarge)
copyRecursiveDischarge location original = do
    charged <- prepareRecursiveCore location (\work -> Bifunctor.first (Bifunctor.first (fmap absurd))
        (countedScopedCoreIdentity work (preparedDischargeGoal original) (preparedDischargeGoal original)))
    case charged of
        Nothing -> pure Nothing
        Just _ -> case original of
            PreparedKernelDischarge _ _ _ _ _ derivation -> scan derivation >> retained
            PreparedRecursiveEquation site application child derivation -> do
                scan derivation
                fmap (\c -> PreparedRecursiveEquation site application c derivation) <$> copy child
            PreparedKernelComposition site goal facts children derivation -> do
                scan derivation
                nested <- traverse copy children
                pure ((\c -> PreparedKernelComposition site goal facts c derivation) <$> sequenceA nested)
            PreparedEvidenceDischarge site goal local a b -> binary (PreparedEvidenceDischarge site goal local) a b
            PreparedEqualityDischarge site goal local a b -> binary (PreparedEqualityDischarge site goal local) a b
            PreparedUniversalDischarge site goal ty identity child -> fmap (PreparedUniversalDischarge site goal ty identity) <$> copy child
            PreparedImplicationDischarge site goal local child -> fmap (PreparedImplicationDischarge site goal local) <$> copy child
            PreparedFormationDischarge _ child -> copy child
            PreparedPreparationLimit statistics child -> fmap (PreparedPreparationLimit statistics) <$> copy child
            PreparedDefinitionDischarge child -> fmap PreparedDefinitionDischarge <$> copy child
            PreparedExcludedMiddle{} -> retained
            PreparedVampireDischarge{} -> impossible "recursive application reuse encountered ATP"
  where
    copy = copyRecursiveDischarge location
    retained = do
        request <- currentRecursiveRequest
        pure (if Preparation.preparationExhausted (Preparation.preparationStatistics (requestPreparation request)) then Nothing else Just original)
    scan derivation = void (prepareRecursiveCore location \work ->
        let (answer,remaining) = countedKernelDerivationSourceUses work derivation
        in (maybe (Left CountedCoreStructuralWorkExhausted) (const (Right ())) answer,remaining))
    binary constructor a b = do
        left <- copy a
        right <- copy b
        pure (constructor <$> left <*> right)

prepareRecursiveComposition
    :: Location -> NonEmpty PreparedDischarge
    -> (KernelProof.ProofContext ObjectId -> KernelProof.CountedProof ObjectId (KernelProof.BuiltProof ObjectId))
    -> Prepare (Maybe PreparedDischarge)
prepareRecursiveComposition location children build = do
    foundation <- liftDriver Declaration.currentFoundationLowering
    typing <- prepareGlobalTyping
    proof <- prepareRecursiveKernel location do
        current <- KernelProof.countedScopedProofContext foundation typing
            (scopedCoreContext (preparedDischargeGoal (NonEmpty.head children))) (preparedDischargeGoal <$> toList children)
        build current
    pure ((\checked -> PreparedKernelComposition location (KernelProof.builtProofStatement checked) [] children
        (KernelProof.builtProofDerivation checked)) <$> proof)

composeRecursiveEqualities
    :: Location -> PreparedDischarge -> PreparedDischarge -> Prepare (Maybe PreparedDischarge)
composeRecursiveEqualities location firstEquality secondEquality =
    prepareRecursiveComposition location (firstEquality :| [secondEquality]) \current -> do
        firstProof <- KernelProof.countedIndexedHypothesisProof current (hypothesisIx 0)
        secondProof <- KernelProof.countedIndexedHypothesisProof current (hypothesisIx 1)
        KernelProof.countedComposeEqualityProof current firstProof secondProof

-- Outside-in evaluation returns only checked progress. A blocked child stays
-- in the expression; no assumption is introduced by traversing a connective.
evaluateRecursiveExpression
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> KernelProof.ProofContext ObjectId -> ScopedCheckedCore ObjectId
    -> Prepare (Maybe (PreparedProofGoal,PreparedDischarge))
evaluateRecursiveExpression location context locals source proofContext original = do
    equalEndpoints <- case scopedCoreTerm original of
        CEq _ left right -> prepareRecursiveCore location (\work ->
            Bifunctor.first (Bifunctor.first (fmap absurd)) (countedCanonicalIdentity work left right))
        _ -> pure (Just False)
    case equalEndpoints of
        Nothing -> pure Nothing
        Just True -> pure Nothing
        Just False -> do
            beta <- betaStep original
            case beta of
                Just step -> continue step
                Nothing -> do
                    application <- prepareRecursiveCall location context locals source proofContext original
                    case application of
                        Just step -> continue step
                        Nothing -> case scopedCoreTerm original of
                            CLam ty body -> binder CLam ty body
                            CForall ty body -> binder CForall ty body
                            CExists ty body -> binder CExists ty body
                            _ -> children (childTerms (scopedCoreTerm original))
  where
    typing = KernelProof.proofContextGlobalTyping proofContext
    evaluate = evaluateRecursiveExpression location context locals
    continue step@(described,equality) = do
        let residual = preparedProofGoalCore described
        progress <- prepareRecursiveCore location (\work ->
            Bifunctor.first (Bifunctor.first (fmap absurd)) (countedScopedCoreIdentity work original residual))
        case progress of
            Just False -> do
                next <- evaluate described proofContext residual
                case next of
                    Nothing -> pure (Just step)
                    Just (result,secondEquality) -> do
                        joined <- composeRecursiveEqualities location equality secondEquality
                        when (isNothing joined) (completeDiscardedRecursiveEvidence secondEquality)
                        pure (Just (maybe step ((,) result) joined))
            _ -> completeDiscardedRecursiveEvidence equality >> pure Nothing
    check types term = prepareRecursiveCore location (\work ->
        Bifunctor.first (Bifunctor.first (fmap (Text.pack . show)))
            (countedCheckScopedCanonicalCore typing work types term))

    -- Remove a head beta redex before inspecting its arguments. In particular,
    -- an unused branch formal must not force evaluation of its argument.
    betaStep term = do
        headView <- prepareRecursiveCore location (\work -> spine work [] (scopedCoreTerm term))
        case join headView of
            Nothing -> pure Nothing
            Just (body,argument,arguments) -> do
                substituted <- prepareRecursiveCore location (\work ->
                    Bifunctor.first (Bifunctor.first (fmap absurd)) (countedInstantiateCanonical work argument body))
                residual <- maybe (pure Nothing)
                    (\value -> check (scopedCoreContext term) (foldl' CApp value arguments)) substituted
                case residual of
                    Nothing -> pure Nothing
                    Just result -> do
                        description <- mergeRecursiveSources location typing result [source]
                        proof <- prepareRecursiveKernel location do
                            reflexive <- KernelProof.countedEqualityReflexivityProof proofContext term
                            target <- KernelProof.countedScopedTerm proofContext
                                (CEq (scopedCoreType term) (scopedCoreTerm term) (scopedCoreTerm result))
                            KernelProof.countedConversionProof proofContext reflexive target
                        pure ((\checked -> (fromMaybe (plainPreparedProofGoal result) description,PreparedKernelDischarge location PreparedImplicitObvious
                            (KernelProof.builtProofStatement checked) locals [] (KernelProof.builtProofDerivation checked))) <$> proof)
    spine 0 _ _ = (Left CountedCoreStructuralWorkExhausted,0)
    spine work arguments (CApp function argument) = spine (work - 1) (argument:arguments) function
    spine work (argument:arguments) (CLam _ body) = (Right (Just (body,argument,arguments)),work - 1)
    spine work _ _ = (Right Nothing,work - 1)

    children [] = pure Nothing
    children (term:remaining) = do
        checked <- check (scopedCoreContext original) term
        case checked of
            Nothing -> pure Nothing
            Just child -> do
                reduced <- evaluate source proofContext child
                case reduced of
                    Nothing -> children remaining
                    Just (childSource,equality) -> do
                        transported <- prepareRecursiveReplacement location original equality
                        case transported of
                            Nothing -> completeDiscardedRecursiveEvidence equality >> pure Nothing
                            Just (result,transport) -> do
                                described <- mergeRecursiveSources location typing result [source,childSource]
                                maybe (pure (Just (plainPreparedProofGoal result,transport)))
                                    (\view -> continue (view,transport)) described
    childTerms = \case
        CApp a b -> [a,b]
        CNot a -> [a]
        CAnd a b -> [a,b]
        COr a b -> [a,b]
        CImp a b -> [a,b]
        CEq _ a b -> [a,b]
        _ -> []

    binder constructor ty body = do
        opened <- prepareRecursiveKernel location (KernelProof.countedExtendProofContextBinder proofContext ty)
        case opened of
            Nothing -> pure Nothing
            Just (nested,_) -> do
                identity <- allocateLocalIdentity
                extended <- either (throwProof . ProofElaborationFailed) pure
                    (Elaboration.extendTypedAnonymousElaborationContext ty identity context)
                let support = Elaboration.elaborationContextSupport extended
                    weakened = zipWith (\(PreparedLocal ordinal origin _ _) proposition ->
                        PreparedLocal ordinal origin support proposition) locals (KernelProof.proofContextHypotheses nested)
                checkedBody <- check (ty:scopedCoreContext original) body
                case checkedBody of
                    Nothing -> pure Nothing
                    Just child -> do
                        shifted <- prepareRecursiveSource location do
                            let PreparedProofGoal sourceGoal sourceEvidence = source
                            written <- RecursiveSource.writtenOperands typing location sourceGoal sourceEvidence
                            terms <- traverse (\term -> expansionCoreWork (\work ->
                                SourceTerm.countedShiftCanonicalSourceTermOccurrence work 1 0 term)) written
                            pure (PreparedProofGoal child (SourceEvidence.SourceInputs Nothing
                                [SourceEvidence.SourceInput [] (SourceTerm.sourceSupportTemplate id term) | term <- terms]))
                        evaluated <- maybe (pure Nothing) (\description ->
                            evaluateRecursiveExpression location extended weakened description nested child) shifted
                        case evaluated of
                            Nothing -> pure Nothing
                            Just (childSource,equality) -> do
                                let residual = constructor ty (scopedCoreTerm (preparedProofGoalCore childSource))
                                result <- check (scopedCoreContext original) residual
                                universal <- check (scopedCoreContext original) (CForall ty (scopedCoreTerm (preparedDischargeGoal equality)))
                                case (result,universal) of
                                    (Just after,Just quantified) -> do
                                        let closed = PreparedUniversalDischarge location quantified ty identity equality
                                        description <- mergeRecursiveSources location typing after [source]
                                        lifted <- prepareRecursiveComposition location (closed :| []) \current -> do
                                            (inside,_) <- KernelProof.countedExtendProofContextBinder current ty
                                            allEqual <- KernelProof.countedIndexedHypothesisProof inside (hypothesisIx 0)
                                            variable <- KernelProof.countedScopedTerm inside (CBound 0)
                                            pointwise <- KernelProof.countedForallEliminationProof inside allEqual variable
                                            lambdaEquality <- KernelProof.countedEqualityCongruenceLambdaProof ty pointwise
                                            lifted <- case scopedCoreTerm original of
                                                CLam{} -> pure lambdaEquality
                                                _ -> do
                                                    operator <- KernelProof.countedScopedTerm current
                                                        (CLam (TyArrow ty TyProp) (constructor ty (CApp (CBound 1) (CBound 0))))
                                                    function <- KernelProof.countedEqualityReflexivityProof current operator
                                                    KernelProof.countedEqualityCongruenceApplicationProof current function lambdaEquality
                                            expected <- KernelProof.countedScopedTerm current (CEq (scopedCoreType original)
                                                (scopedCoreTerm original) (scopedCoreTerm after))
                                            KernelProof.countedConversionProof current lifted expected
                                        when (isNothing lifted) (completeDiscardedRecursiveEvidence closed)
                                        pure ((,) (fromMaybe (plainPreparedProofGoal after) description) <$> lifted)
                                    _ -> completeDiscardedRecursiveEvidence equality >> pure Nothing

mergeRecursiveSources
    :: Location -> GlobalTyping ObjectId -> ScopedCheckedCore ObjectId -> [PreparedProofGoal]
    -> Prepare (Maybe PreparedProofGoal)
mergeRecursiveSources location typing target sources = prepareRecursiveSource location do
    terms <- concat <$> traverse (\(PreparedProofGoal goal evidence) ->
        RecursiveSource.writtenOperands typing location goal evidence) sources
    pure (PreparedProofGoal target (SourceEvidence.SourceInputs Nothing
        [SourceEvidence.SourceInput [] (SourceTerm.sourceSupportTemplate id term) | term <- terms]))

-- Visit supplied evidence in order, retaining its original proof. The cursor
-- is a fallback after the initial ordinary search and never adds citations.
prepareRecursiveFacts
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> KernelProof.ProofContext ObjectId
    -> (Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal -> Prepare PreparedDischarge)
    -> Prepare PreparedDischarge
prepareRecursiveFacts location context locals goal proofContext residual = do
    request <- currentRecursiveRequest
    let localSources = [(preparedLocalProposition local,localProof index)
            | (index,local) <- zip [0..] locals]
        citedSources = [(embedClosedCore (scopedCoreContext target) (checkedPropositionTerm proposition),citedProof fingerprint proposition)
            | (fingerprint,proposition) <- requestSelectedFacts request]
    visit context locals proofContext (localSources <> citedSources)
  where
    target = preparedProofGoalCore goal
    localProof index = do
        proof <- prepareRecursiveKernel location (KernelProof.countedIndexedHypothesisProof proofContext (hypothesisIx index))
        pure ((\checked -> PreparedKernelDischarge location PreparedImplicitObvious (KernelProof.builtProofStatement checked)
            locals [] (KernelProof.builtProofDerivation checked)) <$> proof)
    citedProof fingerprint proposition = do
        proof <- prepareRecursiveKernel location (KernelProof.countedImportedProof proofContext (importIx 0)
            (checkedPropositionTerm proposition))
        pure ((\checked -> PreparedKernelDischarge location (PreparedObviousReferences (fingerprint :| []))
            (KernelProof.builtProofStatement checked) locals [fingerprint] (KernelProof.builtProofDerivation checked)) <$> proof)
    visit current currentLocals currentProofContext sources = do
        request <- currentRecursiveRequest
        case sources of
            [] -> residual current currentLocals goal
            _ | Preparation.preparationExhausted (Preparation.preparationStatistics (requestPreparation request)) ->
                residual current currentLocals goal
            (proposition,originalProof):rest -> do
                heads <- prepareRecursiveCore location (\work ->
                    Bifunctor.first (Bifunctor.first (fmap absurd)) (countedCanonicalGlobals work (scopedCoreTerm proposition)))
                if not (maybe False (any (not . null . requestDefinitions request)) heads)
                    then visit current currentLocals currentProofContext rest
                    else case splitScopedConjunction proposition of
                        Just (left,right) -> visit current currentLocals currentProofContext
                            ((left,project False originalProof):(right,project True originalProof):rest)
                        Nothing -> do
                            evaluated <- evaluateRecursiveExpression location current currentLocals
                                (plainPreparedProofGoal proposition) currentProofContext proposition
                            case evaluated of
                                Nothing -> visit current currentLocals currentProofContext rest
                                Just (description,equality) -> do
                                    original <- originalProof
                                    transported <- case original of
                                        Nothing -> pure Nothing
                                        Just proof -> prepareRecursiveComposition location (equality :| [proof]) \scoped -> do
                                            equation <- KernelProof.countedIndexedHypothesisProof scoped (hypothesisIx 0)
                                            premise <- KernelProof.countedIndexedHypothesisProof scoped (hypothesisIx 1)
                                            KernelProof.countedEqualityModusPonensProof scoped equation premise
                                    case transported of
                                        Nothing -> completeDiscardedRecursiveEvidence equality >> visit current currentLocals currentProofContext rest
                                        Just proof -> do
                                            let derived = preparedProofGoalCore description
                                            local <- allocateLocal ProofDerivedClaim current derived
                                            extended <- extendContextWithSourceLocal local (SourceEvidence.SourceResidual Nothing) [] current
                                            nested <- prepareRecursiveKernel location
                                                (KernelProof.countedExtendProofContextHypothesis currentProofContext derived)
                                            case nested of
                                                Nothing -> completeDiscardedRecursiveEvidence proof >> residual current currentLocals goal
                                                Just nestedProofContext -> do
                                                    closed <- localClosure nestedProofContext (local:currentLocals)
                                                    child <- maybe (visit extended (local:currentLocals) nestedProofContext rest) pure closed
                                                    pure (PreparedEvidenceDischarge location target local proof child)
    project right original = original >>= \case
        Nothing -> pure Nothing
        Just proof -> prepareRecursiveComposition location (proof :| []) \current -> do
            premise <- KernelProof.countedIndexedHypothesisProof current (hypothesisIx 0)
            KernelProof.countedProjectConjunctionProof (not right) current premise
    localClosure current currentLocals = do
        request <- currentRecursiveRequest
        let (answer,balance) = Preparation.prepareLocalEvidence (requestPreparation request) current target
        modifyRecursiveRequest (\remaining -> remaining {requestPreparation = balance})
        plan <- either (throwProof . ProofStructuralCompositionFailed location) pure answer
        pure $ case Preparation.preparationView plan of
            Preparation.PreparationProof proof _ -> Just (PreparedKernelDischarge location PreparedImplicitObvious target
                currentLocals [] (KernelProof.builtProofDerivation proof))
            _ -> Nothing

-- Dependency scanning is only a pruning aid. Authorization independently
-- replays the retained proof and performs the definition-use check there.
pruneRecursiveEvidence :: Location -> PreparedDischarge -> Prepare (PreparedDischarge,Maybe (Set Natural))
pruneRecursiveEvidence location original = do
    request <- currentRecursiveRequest
    if Preparation.preparationExhausted (Preparation.preparationStatistics (requestPreparation request))
        then pure (original,Nothing) else case original of
            PreparedKernelDischarge _ _ _ locals _ derivation -> do
                used <- uses derivation
                pure (original, fmap (\indices -> Set.fromList [preparedLocalOrdinalValue local
                    | (index,local) <- zip [0..] locals, hypothesisIx index `Set.member` indices]) used)
            PreparedEvidenceDischarge site goal local evidence child -> do
                (retained,used) <- prune child
                case used of
                    Just indices | preparedLocalOrdinalValue local `Set.notMember` indices ->
                        completeDiscardedRecursiveEvidence evidence >> pure (retained,used)
                    _ -> do
                        (source,dependencies) <- prune evidence
                        pure (PreparedEvidenceDischarge site goal local source retained,
                            Set.union <$> dependencies <*> (Set.delete (preparedLocalOrdinalValue local) <$> used))
            PreparedEqualityDischarge site goal local equation child -> do
                (e,a) <- prune equation
                (c,b) <- prune child
                pure (PreparedEqualityDischarge site goal local e c,Set.union <$> a <*> b)
            PreparedRecursiveEquation site application child derivation -> do
                (c,used) <- prune child
                pure (PreparedRecursiveEquation site application c derivation,used)
            PreparedUniversalDischarge site goal ty identity child -> do
                (c,used) <- prune child
                pure (PreparedUniversalDischarge site goal ty identity c,used)
            PreparedImplicationDischarge site goal local child -> do
                (c,used) <- prune child
                pure (PreparedImplicationDischarge site goal local c,Set.delete (preparedLocalOrdinalValue local) <$> used)
            PreparedKernelComposition site goal facts children derivation -> do
                scanned <- uses derivation
                results <- traverse prune children
                pure (PreparedKernelComposition site goal facts (fst <$> results) derivation,
                    scanned >>= \indices -> Set.unions <$> traverse snd
                        [result | (index,result) <- zip [0..] (toList results), hypothesisIx index `Set.member` indices])
            PreparedFormationDischarge completion child -> wrap (PreparedFormationDischarge completion) child
            PreparedPreparationLimit statistics child -> wrap (PreparedPreparationLimit statistics) child
            PreparedDefinitionDischarge child -> wrap PreparedDefinitionDischarge child
            PreparedExcludedMiddle{} -> pure (original,Just Set.empty)
            PreparedVampireDischarge{} -> impossible "recursive evidence pruning encountered ATP"
  where
    prune = pruneRecursiveEvidence location
    wrap constructor child = do
        (retained,used) <- prune child
        pure (constructor retained,used)
    uses derivation = prepareRecursiveCore location \work ->
        let (answer,remaining) = countedKernelDerivationSourceUses work derivation
        in (maybe (Left CountedCoreStructuralWorkExhausted) (Right . kernelSourceExternalHypothesisUses) answer,remaining)

-- A candidate may be discarded after its guard has been materialized.
-- Its physical work still belongs to the completed formation query.
completeDiscardedRecursiveEvidence :: PreparedDischarge -> Prepare ()
completeDiscardedRecursiveEvidence = \case
    PreparedFormationDischarge completion child -> do
        recorder <- liftDriver Declaration.formationRecorderLowering
        liftIO (FormationDiagnostics.complete recorder completion)
        completeDiscardedRecursiveEvidence child
    PreparedDefinitionDischarge child -> completeDiscardedRecursiveEvidence child
    PreparedPreparationLimit _ child -> completeDiscardedRecursiveEvidence child
    PreparedRecursiveEquation _ _ child _ -> completeDiscardedRecursiveEvidence child
    PreparedEqualityDischarge _ _ _ a b -> completeDiscardedRecursiveEvidence a >> completeDiscardedRecursiveEvidence b
    PreparedEvidenceDischarge _ _ _ a b -> completeDiscardedRecursiveEvidence a >> completeDiscardedRecursiveEvidence b
    PreparedUniversalDischarge _ _ _ _ child -> completeDiscardedRecursiveEvidence child
    PreparedImplicationDischarge _ _ _ child -> completeDiscardedRecursiveEvidence child
    PreparedKernelComposition _ _ _ children _ -> traverse_ completeDiscardedRecursiveEvidence children
    _ -> pure ()

prepareRecursiveReplacement
    :: Location -> ScopedCheckedCore ObjectId -> PreparedDischarge
    -> Prepare (Maybe (ScopedCheckedCore ObjectId,PreparedDischarge))
prepareRecursiveReplacement location target equation = do
    (left,right) <- case splitScopedEquality (preparedDischargeGoal equation) of
        Just (_,a,b) -> pure (a,b)
        _ -> impossible "a recursive application lost its equality endpoints"
    replacement <- prepareRecursiveCore location (\work ->
        Bifunctor.first (Bifunctor.first (fmap (Text.pack . show)))
            (countedReplaceScopedCoreOccurrence work left right target))
    case join replacement of
        Nothing -> pure Nothing
        Just replaced -> do
            foundation <- liftDriver Declaration.currentFoundationLowering
            typing <- prepareGlobalTyping
            composed <- prepareRecursiveKernel location do
                current <- KernelProof.countedScopedProofContext foundation typing (scopedCoreContext target)
                    [preparedDischargeGoal equation]
                premise <- KernelProof.countedIndexedHypothesisProof current (hypothesisIx 0)
                function <- KernelProof.countedEqualityReflexivityProof current (scopedCoreReplacementAbstraction replaced)
                result <- KernelProof.countedEqualityCongruenceApplicationProof current function premise
                expected <- KernelProof.countedScopedTerm current (CEq (scopedCoreType target)
                    (scopedCoreTerm target) (scopedCoreTerm (scopedCoreReplacementResult replaced)))
                KernelProof.countedConversionProof current result expected
            pure ((\proof -> (scopedCoreReplacementResult replaced,
                PreparedKernelComposition location (KernelProof.builtProofStatement proof) [] (equation :| [])
                    (KernelProof.builtProofDerivation proof))) <$> composed)

prepareRecursiveGuard
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> RecursiveInterface.CheckedRecursiveDefinition -> Recursive.RecursiveApplication
    -> Prepare (Maybe PreparedDischarge)
prepareRecursiveGuard location context locals source definition application = do
    request <- currentRecursiveRequest
    if isJust (requestFormationFailure request) then pure Nothing
        else prepareRecursiveGuardAttempt location context locals source definition application

prepareRecursiveGuardAttempt
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal] -> PreparedProofGoal
    -> RecursiveInterface.CheckedRecursiveDefinition -> Recursive.RecursiveApplication
    -> Prepare (Maybe PreparedDischarge)
prepareRecursiveGuardAttempt location context locals (PreparedProofGoal sourceGoal sourceEvidence) definition application = do
    typing <- prepareGlobalTyping
    template <- maybe (impossible "an admitted recursive guard lost its source description") pure
        (nth (Recursive.applicationCase application) (toList (RecursiveInterface.recursiveGuardSources definition)))
    let witnesses = Recursive.applicationWitnessCount application
        types = scopedCoreContext (Recursive.applicationEquality application)
        witnessTypes = replicate witnesses TySet <> types
    described <- prepareRecursiveSource location do
        written <- RecursiveSource.writtenOperands typing location sourceGoal sourceEvidence
        shifted <- traverse (\term -> expansionCoreWork (\work ->
            SourceTerm.countedShiftCanonicalSourceTermOccurrence work (fromIntegral witnesses) 0 term)) written
        let actuals = [SourceTerm.sourceTermOccurrence term TySet (Elaboration.LocatedSourceTerm location)
                | term <- Recursive.applicationArguments application]
        instantiated <- RecursiveSource.instantiateSource typing witnessTypes location shifted actuals template
        (body,evidence) <- RecursiveSource.sealProposition typing witnessTypes location instantiated
        closed <- foldM (\(goal,view) _ -> do
            chargeExpansion 1
            wrapped <- maybe (Except.throwError (ExpansionInvalid "a recursive guard lost its witness scope")) pure
                (closeScopedExists goal)
            pure (wrapped,SourceEvidence.SourceExists view)) (body,evidence) [1 .. witnesses]
        same <- expansionCoreWork (\work -> countedScopedCoreIdentity work (fst closed) (Recursive.applicationGuard application))
        unless same (Except.throwError (ExpansionInvalid "recursive source substitution changed its joint guard"))
        pure closed
    case described of
        Nothing -> pure Nothing
        Just (goal,evidence) -> do
            request <- currentRecursiveRequest
            -- Citations become privately proved locals of this guard. They do
            -- not become ambient definition evidence in the residual solver.
            (guardContext,guardLocals,citations) <- foldM introduceCitation (context,locals,[])
                (requestSelectedFacts request)
            remaining <- currentRecursiveRequest
            if Preparation.preparationExhausted (Preparation.preparationStatistics (requestPreparation remaining))
                then pure Nothing else do
                modifyRecursiveRequest (\current -> current {requestGuardQueries = requestGuardQueries current + 1})
                (outcome,balance,completion) <- liftDriver (Elaboration.prepareProofNotionGoalAttemptWithBudget
                    (requestFormation request) guardContext location goal evidence)
                    >>= either (throwProof . ProofElaborationFailed) pure
                modifyRecursiveRequest (\current -> current {requestFormation = balance})
                case outcome of
                    Right (Elaboration.NotionQueryFound materialized) -> do
                        (proof,completed) <- continueFormationCompletion completion
                            (materializeNotionDischarge location guardContext guardLocals goal materialized)
                        let guarded = PreparedFormationDischarge completed proof
                        pure (Just (foldr (\(local,citation) child ->
                            PreparedEvidenceDischarge location goal local citation child) guarded citations))
                    result -> do
                        recorder <- liftDriver Declaration.formationRecorderLowering
                        liftIO (FormationDiagnostics.complete recorder completion)
                        case result of
                            Left (Elaboration.ElaborationFormationSearchFailed _ failure) -> do
                                modifyRecursiveRequest (\current -> current {requestFormationFailure = Just failure})
                                pure Nothing
                            Left failure -> throwProof (ProofElaborationFailed failure)
                            Right _ -> pure Nothing
  where
    introduceCitation (current,currentLocals,proofs) (fingerprint,proposition) = do
        request <- currentRecursiveRequest
        if Preparation.preparationExhausted (Preparation.preparationStatistics (requestPreparation request))
            then pure (current,currentLocals,proofs) else do
            let target = embedClosedCore (scopedCoreContext (Recursive.applicationEquality application))
                    (checkedPropositionTerm proposition)
            local <- allocateLocal ProofDerivedClaim current target
            extended <- extendContextWithSourceLocal local (SourceEvidence.SourceResidual Nothing) [] current
            foundation <- liftDriver Declaration.currentFoundationLowering
            typing <- prepareGlobalTyping
            imported <- prepareRecursiveKernel location do
                proofContext <- KernelProof.countedScopedProofContext foundation typing (scopedCoreContext target) []
                KernelProof.countedImportedProof proofContext (importIx 0) (checkedPropositionTerm proposition)
            case imported of
                Nothing -> pure (current,currentLocals,proofs)
                Just proof -> pure (extended,currentLocals <> [local],proofs <>
                    [(local,PreparedKernelDischarge location (PreparedObviousReferences (fingerprint :| []))
                        target [] [fingerprint] (KernelProof.builtProofDerivation proof))])

-- Contradictory premises are an expected success condition throughout an
-- indirect proof, including while discharging its intermediate claims.
data ProofMode
    = DirectProof
    | ContradictionProof

data PrepareEnvironment = PrepareEnvironment
    { prepareProofMode :: !ProofMode
    , prepareFoundationAuxiliaries :: ![FoundationAxiomTag]
    , prepareLocalObject :: !(Maybe AssertedObject)
    , prepareObviousFailureFixture :: !(Maybe (Obvious.ObviousFailureReport ObjectId))
    , prepareAutomaticWork :: !Word
    , prepareRecordObligations :: ![Obligation.RecordObligation]
    }

type Prepare =
    ReaderT
        PrepareEnvironment
        (StateT
            PrepareState
            (ExceptT ProofError (Declaration.LoweringDriver)))

prepareProof
    :: Raw.Block
    -> Maybe Raw.Proof
    -> Declaration.LoweringDriver
        (Either ProofError PreparedProof)
prepareProof =
    prepareProofWithContext []
        Nothing Preparation.defaultPreparationWork [] Nothing Nothing
        (Just ImplicitTheoremClose)
        PreparedImplicitObvious

-- | Failure-only test seam for the real preparation/fallback boundary.  The
-- fixture cannot supply a proof or change the permitted source environment.
prepareProofWithObviousFailureFixture
    :: Obvious.ObviousFailureReport ObjectId
    -> Raw.Block
    -> Maybe Raw.Proof
    -> Declaration.LoweringDriver (Either ProofError PreparedProof)
prepareProofWithObviousFailureFixture failure =
    prepareProofWithContext []
        (Just failure) Preparation.defaultPreparationWork [] Nothing Nothing
        (Just ImplicitTheoremClose)
        PreparedImplicitObvious

-- | Compiler-generated projection claims have no source justification to
-- interpret.  Keep their established internal ATP discharge distinct from a
-- user-authored missing proof, which means obvious inference.
prepareGeneratedProofWithTransparentDefinition
    :: Binding.PreparedBinding
    -> Raw.Block
    -> Declaration.LoweringDriver
        (Either ProofError PreparedProof)
prepareGeneratedProofWithTransparentDefinition definition block =
    prepareProofWithContext []
        Nothing Preparation.defaultPreparationWork [] (Just definition) Nothing Nothing
        PreparedInternalAuto block Nothing

-- | Internal proof preparation with a checked canonical target. Record
-- constructors use their elaborated field view, so spelling collisions cannot
-- change the selector identity of a generated projection equation.
prepareGeneratedProofWithTransparentDefinitionTarget
    :: Binding.PreparedBinding -> ScopedCheckedCore ObjectId -> Raw.Block
    -> Declaration.LoweringDriver (Either ProofError PreparedProof)
prepareGeneratedProofWithTransparentDefinitionTarget definition target block =
    prepareProofWithContext []
        Nothing Preparation.defaultPreparationWork [] (Just definition) (Just target) Nothing
        PreparedInternalAuto block Nothing

-- | Prepare an instance-owned proof against a checked mathematical target
-- while retaining the source claim solely as its lexical and transparent-name
-- context. The checked target is closed and keeps precisely the source
-- envelope's parameters and ordered hypotheses. Only its conclusion changes;
-- the ordinary opening and proof-authority paths remain responsible for it.
prepareProofWithTransparentDefinitionTarget
    :: Binding.PreparedBinding
    -> ScopedCheckedCore ObjectId
    -> [Obligation.RecordObligation]
    -> Raw.Block
    -> Maybe Raw.Proof
    -> Declaration.LoweringDriver
        (Either ProofError PreparedProof)
prepareProofWithTransparentDefinitionTarget definition target obligations =
    prepareProofWithContext obligations
        Nothing Preparation.defaultPreparationWork [] (Just definition) (Just target)
        (Just ImplicitInstanceObligation)
        PreparedImplicitObvious

-- | Configure optional local preparation without changing Obvious or ATP
-- limits. Useful for bounded callers and exhaustion diagnostics.
prepareProofWithPreparationWork
    :: Word -> Raw.Block -> Maybe Raw.Proof
    -> Declaration.LoweringDriver (Either ProofError PreparedProof)
prepareProofWithPreparationWork work =
    prepareProofWithContext [] Nothing work [] Nothing Nothing
        (Just ImplicitTheoremClose) PreparedImplicitObvious

prepareProofWithContext
    :: [Obligation.RecordObligation]
    -> Maybe (Obvious.ObviousFailureReport ObjectId)
    -> Word
    -> [FoundationAxiomTag]
    -> Maybe Binding.PreparedBinding
    -> Maybe (ScopedCheckedCore ObjectId)
    -> Maybe ObviousInvocationSite
    -> PreparedJustification
    -> Raw.Block
    -> Maybe Raw.Proof
    -> Declaration.LoweringDriver
        (Either ProofError PreparedProof)
prepareProofWithContext
        obligations failureFixture automaticWork auxiliaries transparent targetOverride missingSite missingJustification
        block explicitProof =
    Except.runExceptT
        (State.evalStateT
            (Reader.runReaderT prepare
                (PrepareEnvironment
                    DirectProof
                    auxiliaries
                    (transparent >>= Binding.preparedBindingObject)
                    failureFixture
                    automaticWork obligations))
            initialState)
  where
    initialState = PrepareState 0 0 [] Nothing

    prepare =
        case block of
            Raw.BlockClaim
                    kind location _title (Raw.Marker marker)
                    (Raw.Claim assumptions statement) -> do
                rawComposition <-
                    case kind of
                        Raw.Composition ->
                            either
                                (throwProof
                                    . ProofCompositionDeclarationInvalid
                                    location)
                                (pure . Just)
                                (extractRawCompositionSchema
                                    assumptions statement)
                        _ -> pure Nothing
                envelope <-
                    liftDriver
                        (case transparent of
                            Nothing ->
                                Elaboration.elaborateClaimEnvelope
                                    assumptions statement
                            Just definition ->
                                case Binding.preparedBindingTransparentView
                                        definition of
                                    Left failure -> pure (Left failure)
                                    Right transparentView ->
                                        Binding.elaborateClaimEnvelopeWithTransparentBinding
                                            transparentView
                                            assumptions
                                            statement)
                        >>= either
                            (throwProof . ProofElaborationFailed)
                            pure
                let compiledTarget = Elaboration.elaboratedClaimTarget envelope
                    targetCore = fromMaybe compiledTarget targetOverride
                unless (null (scopedCoreContext targetCore))
                    (throwProof
                        (ProofUnsupportedClaim location))
                unless (scopedCoreType targetCore == TyProp)
                    (throwProof
                        (ProofUnsupportedClaim location))
                when
                    ( isJust targetOverride
                      && not (overrideRetainsEnvelope envelope targetCore)
                    )
                    (throwProof
                        (ProofUnsupportedClaim location))
                composition <-
                    traverse
                        (prepareCompositionMetadata location envelope)
                        rawComposition
                (context, openedGoal, identities) <-
                    openEnvelopeVariables
                        targetCore
                        (Elaboration.elaboratedClaimVariables envelope)
                        (Elaboration.elaboratedClaimContext envelope)
                (bodyContext, locals, bodyGoal, antecedents) <-
                    openEnvelopeAntecedents
                        context
                        openedGoal
                        (Elaboration.elaboratedClaimAntecedents envelope)
                notionRegistration <-
                    if kind == Raw.Classification
                    then
                        either
                            (throwProof . ProofClassificationInvalid location)
                            (pure . Just)
                            (prepareClaimNotionRegistration
                                (fromIntegral (length identities))
                                antecedents
                                bodyGoal
                                (Elaboration.elaboratedClaimAntecedents
                                    envelope)
                                (Elaboration.elaboratedClaimConclusionEvidence
                                    envelope))
                    else pure Nothing
                initialInduction <-
                    prepareInitialSetInductionView
                        statement
                        bodyContext
                        (Elaboration.elaboratedClaimVariables envelope)
                        identities
                        antecedents
                        bodyGoal
                let preparedBodyGoal = sourcePreparedProofGoal
                        bodyGoal
                        (Elaboration.elaboratedClaimConclusionEvidence envelope)
                bodyProof <-
                    case explicitProof of
                        Nothing ->
                            PreparedImplicitDischarge
                                <$> preparePreparedDischarge
                                    location
                                    bodyContext
                                    locals
                                    bodyGoal
                                    ((\site ->
                                        obviousInvocationForPrepared
                                            site missingJustification)
                                        <$> missingSite)
                                    missingJustification
                        Just sourceProof ->
                            prepareProofGoalTree
                                location
                                bodyContext
                                locals
                                (InitialClaimInduction initialInduction)
                                preparedBodyGoal
                                sourceProof
                withAssumptions <-
                    prepareEnvelopeAssumptions
                        location
                        antecedents
                        bodyGoal
                        bodyProof
                let proof =
                        case identities of
                            [] -> withAssumptions
                            _ -> PreparedFix identities withAssumptions
                statistics <- reverse <$> State.gets prepareAutomaticStatistics
                pure
                    (PreparedProof
                        location
                        (semanticName marker)
                        targetCore
                        proof
                        (summarizeProofPlanning proof)
                        composition
                        notionRegistration
                        (proofSyntaxId
                            (encodePreparedProof proof))
                        statistics obligations)
            _ ->
                throwProof
                    (ProofUnsupportedClaim (locate block))

-- A compiler-owned target may replace a conclusion, but never silently
-- change the parameters or premises that the source proof opens.
overrideRetainsEnvelope :: Elaboration.ElaboratedClaimEnvelope -> ScopedCheckedCore ObjectId -> Bool
overrideRetainsEnvelope envelope target =
    isJust (dropBinders (length (Elaboration.elaboratedClaimVariables envelope)) (scopedCoreTerm target)
        >>= dropHeaders (Elaboration.elaboratedClaimAntecedents envelope))
  where
    dropBinders 0 term = Just term
    dropBinders count (CForall TySet body) = dropBinders (count - 1) body
    dropBinders _ _ = Nothing
    dropHeaders [] term = Just term
    dropHeaders (header : remaining) (CImp premise conclusion)
        | premise == scopedCoreTerm (Elaboration.compiledHeaderCore header) =
            dropHeaders remaining conclusion
    dropHeaders _ _ = Nothing

data RawCompositionSchema = RawCompositionSchema
    !Raw.VarSymbol !Raw.Sign !Raw.Relation !Raw.VarSymbol !Raw.Sign !Raw.Relation !Raw.VarSymbol !Raw.Sign !Raw.Relation

extractRawCompositionSchema :: [Raw.Asm] -> Raw.Stmt -> Either Text RawCompositionSchema
extractRawCompositionSchema assumptions conclusion = do
    (x,signLeft,left,y,signRight,right,z) <- case reverse assumptions of
        Raw.AsmSuppose (Raw.StmtFormula (Raw.FormulaChain
                (Raw.ChainCons first signA relationA (Raw.ChainBase middle signB relationB final)))) : _ ->
            (,,,,,,) <$> variable first <*> pure signA <*> pure relationA <*> variable middle
                <*> pure signB <*> pure relationB <*> variable final
        _ -> Left "the final assumption of a composition must be one two-link chain"
    (first,signResult,result,final) <- case conclusion of
        Raw.StmtFormula (Raw.FormulaChain (Raw.ChainBase a sign relation b)) ->
            (,,,) <$> variable a <*> pure sign <*> pure relation <*> variable b
        _ -> Left "a composition conclusion must be one relation link"
    unless (first == x && final == z) (Left "the conclusion must reuse the first and third premise variables")
    unless (x /= y && y /= z && x /= z) (Left "the three composition variables must be distinct")
    pure (RawCompositionSchema x signLeft left y signRight right z signResult result)
  where
    variable (Raw.ExprVar symbol@Raw.NamedVarAt{} :| []) = Right symbol
    variable _ = Left "composition endpoints must be bare named variables"

prepareCompositionMetadata
    :: Location -> Elaboration.ElaboratedClaimEnvelope -> RawCompositionSchema -> Prepare SemanticRelationComposition
prepareCompositionMetadata location envelope (RawCompositionSchema x signA a y signB b z signC c) = do
    let variables = Elaboration.elaboratedClaimVariables envelope
        count = length variables
        context = Elaboration.elaboratedClaimContext envelope
        headers = Elaboration.elaboratedClaimAntecedents envelope
        position variable = maybe (throwProof (ProofCompositionDeclarationInvalid location "an endpoint is absent from the theorem telescope"))
            (pure . fromIntegral) (List.elemIndex variable variables)
    positions <- (,,) <$> position x <*> position y <*> position z
    (conditions,_) <- case reverse headers of
        [] -> throwProof (ProofCompositionDeclarationInvalid location "a composition has no chain assumption")
        chain:rest -> pure (reverse rest,chain)
    -- Install only preceding headers while obtaining the relation templates.
    -- The chain being registered never supplies its own formation evidence.
    opened <- foldM (\goal _ -> maybe (impossible "a composition lost its theorem telescope") (pure . snd)
        (openScopedForall goal)) (Elaboration.elaboratedClaimTarget envelope) variables
    (prior,_,_,_) <- openEnvelopeAntecedents context opened conditions
    let link sign relation destination = Raw.CalcRelationLink sign relation (Raw.ExprVar destination) Raw.JustificationImplicit
    (inputs,remaining) <- liftDriver (Elaboration.elaborateRelationCalculation Calculation.defaultCompositionAdmissionWork prior
        (Raw.ExprVar x) (link signA a y :| [link signB b z])) >>= either (throwProof . ProofElaborationFailed) pure
    (output,afterOutput) <- liftDriver (Elaboration.elaborateRelationCalculation remaining prior
        (Raw.ExprVar x) (link signC c z :| [])) >>= either (throwProof . ProofElaborationFailed) pure
    let layout = Vector.fromList ([1,0] <> reverse (take count [2..]))
        conditionLayout = Vector.fromList (reverse (take count [0..]))
        describe header = Elaboration.abstractPropositionSource conditionLayout
            (Elaboration.compiledHeaderEvidence header) (Elaboration.compiledHeaderEqualities header)
        source application = Elaboration.abstractCalculationSource layout application
        prepared = do
            guards <- traverse describe conditions
            case toList inputs of
                [left,right] -> SemanticRelationComposition positions (Vector.fromList guards)
                    <$> source left <*> source right <*> source (NonEmpty.head output)
                _ -> impossible "a composition schema lost a link"
    either (throwProof . ProofCompositionDeclarationInvalid location . renderExpansionFailure) pure
        (fst (runIdentity (runExpansionWork afterOutput prepared)))

prepareFinalPreludeFoundationClaim
    :: CheckedFoundation
    -> Raw.Block
    -> Maybe Raw.Proof
    -> Declaration.LoweringDriver
        (Either ProofError PreparedFinalPreludeFoundationClaim)
prepareFinalPreludeFoundationClaim foundation block explicitProof =
    Except.runExceptT do
        case (block, explicitProof) of
            ( Raw.BlockClaim
                    kind location _title (Raw.Marker marker)
                    (Raw.Claim assumptions statement)
              , Nothing
              ) -> do
                when (kind == Raw.Classification)
                    (Except.throwError (ProofUnsupportedClaim location))
                envelope <-
                    Trans.lift
                        (Elaboration.elaborateClaimEnvelope
                            assumptions
                            statement)
                        >>= either
                            (Except.throwError
                                . ProofElaborationFailed)
                            pure
                unless
                    ( null (Elaboration.elaboratedClaimVariables envelope)
                        && Elaboration.elaboratedClaimAntecedentCount envelope
                            == 0
                    )
                    (Except.throwError
                        (ProofFoundationLeafRequiresImplicitAuto
                            location))
                let target = Elaboration.elaboratedClaimTarget envelope
                    matches =
                        [ tag
                        | tag <- [minBound .. maxBound]
                        , target == foundationTarget tag
                        ]
                tag <- case matches of
                    [] ->
                        Except.throwError
                            (ProofFoundationLeafTargetMismatch location)
                    [only] ->
                        pure only
                    _ ->
                        Except.throwError
                            (ProofFoundationLeafTargetAmbiguous location)
                pure
                    (PreparedFinalPreludeFoundationClaim
                        location
                        (semanticName marker)
                        target
                        tag
                        (implicitProofSyntaxId target))
            (Raw.BlockClaim _kind location _title _marker _claim, Just{}) ->
                Except.throwError
                    (ProofFoundationLeafRequiresImplicitAuto location)
            _ ->
                Except.throwError
                    (ProofUnsupportedClaim (locate block))
  where
    foundationTarget tag =
        embedClosedCore []
            (eliminateFrozenVoid
                (foundationAxiomFrozen foundation tag))

-- | Recognize the closed theorem presentations of guarded kernel rules in the
-- confined final prelude.  The target must be exactly the schema constructed
-- by the checked rule proof; ordinary source modules cannot enter this path.
prepareFinalPreludeGuardedRuleClaim
    :: CheckedFoundation
    -> Raw.Block
    -> Declaration.LoweringDriver
        (Either ProofError PreparedFinalPreludeGuardedRuleClaim)
prepareFinalPreludeGuardedRuleClaim foundation block =
    Except.runExceptT do
        case block of
            Raw.BlockClaim
                    kind location _title (Raw.Marker marker)
                    (Raw.Claim assumptions statement) -> do
                when (kind == Raw.Classification)
                    (Except.throwError (ProofUnsupportedClaim location))
                envelope <-
                    Trans.lift
                        (Elaboration.elaborateClaimEnvelope assumptions statement)
                        >>= either
                            (Except.throwError
                                . ProofElaborationFailed)
                            pure
                unless
                    ( null (Elaboration.elaboratedClaimVariables envelope)
                        && Elaboration.elaboratedClaimAntecedentCount envelope
                            == 0
                    )
                    (Except.throwError
                        (ProofGuardedRuleTargetMismatch location))
                let target = Elaboration.elaboratedClaimTarget envelope
                schemas <-
                    traverse
                        (prepareSchema location)
                        [minBound .. maxBound]
                case
                    [ (tag, derivation)
                    | (tag, expected, derivation) <- schemas
                    , target == expected
                    ] of
                    [] ->
                        Except.throwError
                            (ProofGuardedRuleTargetMismatch location)
                    [(tag, derivation)] ->
                        pure
                            (PreparedFinalPreludeGuardedRuleClaim
                                location
                                (semanticName marker)
                                target
                                tag
                                derivation
                                (implicitProofSyntaxId target))
                    _ ->
                        Except.throwError
                            (ProofGuardedRuleTargetAmbiguous location)
            _ ->
                Except.throwError
                    (ProofUnsupportedClaim (locate block))
  where
    prepareSchema location tag = do
        proof <-
            either
                (Except.throwError
                    . ProofStructuralCompositionFailed location)
                pure
                (KernelProof.setLfpRuleSchemaProof foundation tag)
        pure
            ( tag
            , eliminateScopedVoid
                (KernelProof.builtProofStatement proof)
            , eliminateKernelDerivationVoid
                (KernelProof.builtProofDerivation proof)
            )

openEnvelopeVariables
    :: ScopedCheckedCore ObjectId
    -> [Raw.VarSymbol]
    -> Elaboration.ElaborationContext
    -> Prepare
        ( Elaboration.ElaborationContext
        , ScopedCheckedCore ObjectId
        , [Elaboration.LocalId]
        )
openEnvelopeVariables target variables preparedContext =
    case NonEmpty.nonEmpty variables of
        Nothing ->
            pure (preparedContext, target, [])
        Just nonempty -> do
            (_unannotated, opened, identities) <-
                openFixedVariables
                Nothing
                Elaboration.emptyElaborationContext
                target
                nonempty
            let expected =
                    reverse
                        (fst <$> toList
                            (Elaboration.elaborationContextSupport preparedContext))
            unless
                (identities == expected)
                (impossible
                    "prepared claim annotations do not match opened binders")
            pure (preparedContext, opened, identities)

openEnvelopeAntecedents
    :: Elaboration.ElaborationContext
    -> ScopedCheckedCore ObjectId
    -> [Elaboration.CompiledHeaderAntecedent]
    -> Prepare
        ( Elaboration.ElaborationContext
        , [PreparedLocal]
        , ScopedCheckedCore ObjectId
        , [ScopedCheckedCore ObjectId]
        )
openEnvelopeAntecedents context initialGoal initialAntecedents =
    go context [] [] initialGoal initialAntecedents
  where
    go activeContext locals antecedents goal [] =
        pure (activeContext, locals, goal, antecedents)
    go activeContext locals antecedents goal (compiled : remaining) = do
        (antecedent, conclusion) <-
            maybe
                (impossible
                    "a prepared claim envelope has too few implications")
                pure
                (openScopedImplication goal)
        unless
            (antecedent == Elaboration.compiledHeaderCore compiled)
            (impossible
                "a prepared claim antecedent differs from its checked sidecar")
        local <- allocateLocal ProofAssumption activeContext antecedent
        activeContext' <-
            extendContextWithSourceLocal
                local
                (Elaboration.compiledHeaderEvidence compiled)
                (Elaboration.compiledHeaderEqualities compiled)
                activeContext
        go
            activeContext'
            (locals <> [local])
            (antecedents <> [antecedent])
            conclusion
            remaining

prepareClaimNotionRegistration
    :: Natural
    -> [ScopedCheckedCore ObjectId]
    -> ScopedCheckedCore ObjectId
    -> [Elaboration.CompiledHeaderAntecedent]
    -> SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence
    -> Either Text [(Notion.ConjunctionPath, RegistrationBody)]
prepareClaimNotionRegistration binderArity openedAntecedents conclusion
        compiledAntecedents conclusionEvidence = do
    leaves <- walk conclusion conclusionEvidence
    premises <- concat <$> traverse (uncurry walk)
        [(proposition, Elaboration.compiledHeaderEvidence header)
        | (proposition, header) <- zip openedAntecedents compiledAntecedents]
    let premiseDescriptions = [template | leaf <- premises, Right template <- [describe leaf]]
    branches <- for leaves (\leaf -> (\template -> (leaf,template)) <$> describe leaf)
    traverse prepare [(leaf,template) | (leaf,template) <- branches, template `notElem` premiseDescriptions]
  where
    walk = SourceEvidence.notionLeaves (pure ())
        (\right path -> pure (path . if right then Notion.ConjunctionRight else Notion.ConjunctionLeft)) id
    -- Kind and exact source description decide tautology before parameter
    -- planning. Whole formulas never recover rich atomic operands.
    describe leaf = case SourceEvidence.sourceLeafDescription leaf of
        SourceEvidence.LeafAtom assertion -> AtomicLeaf <$> Premise.compileAtom binderArity assertion
        _ -> WholeLeaf <$> Premise.describeResidual binderArity
            (SourceEvidence.sourceLeafFormula leaf) (SourceEvidence.sourceLeafEvidence leaf)
    prepare (leaf,template) = do
        body <- case (SourceEvidence.sourceLeafDescription leaf,template) of
            (SourceEvidence.LeafAtom assertion,AtomicLeaf{}) ->
                prepareClaimNotionBranch binderArity openedAntecedents compiledAntecedents assertion
            (_,WholeLeaf residual) -> do
                unless (length openedAntecedents == length compiledAntecedents)
                    (Left "a whole classification has mismatched premise sidecars")
                premises <- for (zip openedAntecedents compiledAntecedents) \(proposition,header) -> do
                    unless (proposition == Elaboration.compiledHeaderCore header)
                        (Left "a rule premise sidecar does not match the opened theorem")
                    premise <- Premise.compilePremise binderArity proposition (Elaboration.compiledHeaderEvidence header)
                    pure (premise,scopedCoreTerm proposition)
                planned <- FormationRule.compileDescribedRule (const (pure ())) binderArity premises (WholeLeaf residual)
                void (Bifunctor.first (\case
                    FormationJoin.JoinWholeConclusionUndetermined ->
                        "every theorem parameter must occur in the whole conclusion or be determined by the premises"
                    failure -> Text.pack (show failure)) planned)
                pure (RegisterWholeConclusion (WholeConclusionRule binderArity (fst <$> premises) residual))
            _ -> impossible "a source leaf changed classification kind"
        pure (SourceEvidence.sourceLeafPath leaf Notion.ConjunctionHere,body)

prepareClaimNotionBranch
    :: Natural
    -> [ScopedCheckedCore ObjectId]
    -> [Elaboration.CompiledHeaderAntecedent]
    -> Elaboration.ScopedSourceNotionOccurrence
    -> Either Text RegistrationBody
prepareClaimNotionBranch binderArity openedAntecedents compiledAntecedents selectedAssertion =
    -- Specialized descriptions retain useful provider/subject metadata for
    -- existing consumers. Their applicability never restricts clause admission.
    case specialized of
        Right rule -> Right rule
        Left _ -> prepareFiniteRule selectedAssertion []
  where
    specialized = do
      when (sourceTerminalConclusion selectedAssertion)
        (Left "this predicate has no subject specialization")
      case nullaryProviderCandidate selectedAssertion of
        Just candidate -> prepareNullaryProviderClassification candidate
        Nothing -> case graphDomainCandidate selectedAssertion of
            Just (left, right, graph, provider) ->
                prepareGraphDomainRule
                    left right graph provider selectedAssertion
            Nothing -> do
                focus <- assertionFocus "conclusion" selectedAssertion
                case SourceTerm.sourceTermOccurrenceProvider focus of
                    Just provider ->
                        case prepareProviderResultRule
                                selectedAssertion provider of
                            Right prepared -> Right prepared
                            Left providerReason ->
                                prepareOrdinaryRule
                                    selectedAssertion
                                    [providerReason]
                    Nothing -> prepareOrdinaryRule selectedAssertion []
    expectedVariables =
        if binderArity == 0
        then Set.empty
        else Set.fromList [0 .. binderArity - 1]
    expectedViewVariables = Set.map ViewVariableIx expectedVariables

    nullaryProviderCandidate assertion = case Notion.sourceAssertionAtom assertion of
        GlobalAtomTemplate head' arguments -> do
            [focus] <- pure (toList arguments)
            provider <- SourceTerm.sourceTermOccurrenceProvider focus
            IntrinsicSourceProvider intrinsic <- pure (SourceTerm.sourceTermProviderHead provider)
            guard (Vector.null (SourceTerm.sourceTermProviderArguments provider))
            pure (intrinsic, head')
        _ -> Nothing

    prepareNullaryProviderClassification (provider, conclusionHead) = do
        unless
            ( binderArity == 0
              && null openedAntecedents
              && null compiledAntecedents
            )
            (Left
                "a nullary intrinsic classification must be a completely closed atomic claim")
        unless
            (isJust (intrinsicProviderApplication provider Vector.empty))
            (Left
                "a nullary intrinsic classification must focus on an exact nullary set provider")
        pure
            (RegisterNullaryProvider (NullaryProviderRule provider conclusionHead))

    graphDomainCandidate conclusionAssertion = do
        ([antecedent], [compiled]) <-
            pure (openedAntecedents, compiledAntecedents)
        [antecedentAssertion] <-
            pure (Elaboration.compiledHeaderAssertions compiled)
        guard
            ( Notion.sourceAssertionPath antecedentAssertion
                == Notion.ConjunctionHere
              && Notion.sourceAssertionFormula antecedentAssertion
                == antecedent
            )
        (pair, graph) <- membershipTerms antecedentAssertion
        (left, right) <-
            SourceTerm.sourceTermOccurrenceOrderedPair pair
        (_conclusionElement, conclusionSet) <-
            membershipTerms conclusionAssertion
        provider <- SourceTerm.sourceTermOccurrenceProvider conclusionSet
        pure (left, right, graph, provider)

    membershipTerms assertion = case Notion.sourceAssertionAtom assertion of
        MembershipAtomTemplate element set -> Just (element, set)
        _ -> Nothing

    prepareGraphDomainRule left right graph provider conclusionAssertion = do
        premiseLeft <- compileDirectArgument left
        premiseRight <- compileDirectArgument right
        premiseGraph <- compileDirectArgument graph
        (conclusionLeft, _conclusionSet) <-
            maybe
                (Left
                    "a graph-domain rule conclusion must be a membership statement")
                Right
                (membershipTerms conclusionAssertion)
        conclusionLeftVariable <- compileDirectArgument conclusionLeft
        unless (conclusionLeftVariable == premiseLeft)
            (Left
                "a graph-domain rule conclusion must retain the pair's left component")
        providerArguments <- traverse compileDirectArgument
            (SourceTerm.sourceTermProviderArguments provider)
        providerGraph <- case toList providerArguments of
            [argument] -> Right argument
            _ -> Left
                "a graph-domain rule provider must have exactly one graph argument"
        unless (providerGraph == premiseGraph)
            (Left
                "a graph-domain rule conclusion must apply its provider to the premise graph")
        let variables = Set.fromList
                [premiseLeft, premiseRight, premiseGraph]
        unless (variables == expectedViewVariables)
            (Left
                "the ordered-pair membership premise must determine every theorem variable")
        pure
            (RegisterGraphDomain (GraphDomainRule
                (SourceTerm.sourceTermProviderHead provider)
                premiseLeft premiseRight premiseGraph))

    prepareUnaryView antecedentAssertion conclusionAssertion = do
        premise <- compileUnaryPremiseTemplate antecedentAssertion
        conclusionTemplate <-
            compileRuleAtomTemplate conclusionAssertion
        let premiseVariables = templateVariables premise
            conclusionVariables = atomTemplateVariables conclusionTemplate
        unless
            (premiseVariables == expectedViewVariables)
            (Left
                ("every theorem variable must be determined by the view premise"
                    :: Text))
        unless
            (conclusionVariables `Set.isSubsetOf` premiseVariables)
            (Left
                "the view conclusion contains a variable absent from its premise")
        pure (RegisterNotionView (NotionViewRule premise (AtomicLeaf conclusionTemplate)))

    prepareProviderResultRule conclusionAssertion provider = do
        unless
            (length openedAntecedents == length compiledAntecedents)
            (Left "a provider-result rule has mismatched premise sidecars")
        let sources =
                [ (proposition, Elaboration.compiledHeaderEvidence compiled)
                | (proposition, compiled) <-
                    zip openedAntecedents compiledAntecedents
                ]
        (providerTemplate, premises, conclusionTemplate) <-
            Bifunctor.first ProviderResult.providerResultErrorReason $
                ProviderResult.prepareWrittenProviderResultRuleTemplates
                    binderArity
                    sources
                    conclusionAssertion
                    (ProviderResult.writtenProviderResultSubject provider)
        pure
            (RegisterProviderResult (ProviderResultRule
                providerTemplate premises conclusionTemplate))

    prepareOrdinaryRule conclusionAssertion earlierReasons =
        case unaryCandidate of
            Just antecedentAssertion ->
                case prepareUnaryView antecedentAssertion conclusionAssertion of
                    Right unary -> Right unary
                    Left unaryReason ->
                        prepareFiniteRule conclusionAssertion
                            (earlierReasons <> [unaryReason])
            Nothing -> prepareFiniteRule conclusionAssertion earlierReasons
      where
        unaryCandidate = case (openedAntecedents, compiledAntecedents) of
            ([antecedent], [compiled])
                | [antecedentAssertion] <-
                    Elaboration.compiledHeaderAssertions compiled
                , Notion.sourceAssertionPath antecedentAssertion
                    == Notion.ConjunctionHere
                , Notion.sourceAssertionFormula antecedentAssertion
                    == antecedent -> Just antecedentAssertion
            _ -> Nothing

    prepareFiniteRule conclusionAssertion _earlierReasons = do
        unless (length openedAntecedents == length compiledAntecedents)
            (Left "a notion clause has mismatched premise sidecars")
        premises <- traverse (uncurry compilePremiseBundle)
            (zip openedAntecedents compiledAntecedents)
        conclusion <- compileRuleAtomTemplate conclusionAssertion
        skeleton <- checkedNotionRuleSkeleton binderArity premises conclusion
        pure (RegisterFiniteEvidence (FiniteEvidenceRule skeleton))

    compilePremiseBundle proposition compiled = do
        unless (proposition == Elaboration.compiledHeaderCore compiled)
            (Left "a rule premise sidecar does not match the opened theorem")
        Premise.compilePremise binderArity proposition (Elaboration.compiledHeaderEvidence compiled)

    compileRuleAtomTemplate = Premise.compileAtom binderArity

    compileRuleTermTemplate = RuleTerm.compileSourceRuleTermTemplate binderArity

    ruleAtomVariables = Set.unions
        . fmap RuleTerm.ruleTermTemplateVariables
        . toList

    compileUnaryPremiseTemplate assertion = case Notion.sourceAssertionAtom assertion of
        NegativeAtomTemplate{} -> Left "a signed premise uses the common clause compiler"
        GlobalAtomTemplate head' arguments ->
            GlobalNotionViewPremise head' <$> traverse compileRuleTermTemplate arguments
        StructureAtomTemplate head' arguments ->
            StructureNotionViewPremise head' <$> traverse compileRuleTermTemplate arguments
        MembershipAtomTemplate element set ->
            case SourceTerm.sourceTermOccurrenceProvider set of
                Just provider ->
                    ExactProviderMembershipPremise
                        <$> compileRuleTermTemplate element
                        <*> pure (SourceTerm.sourceTermProviderHead provider)
                        <*> traverse compileRuleTermTemplate (SourceTerm.sourceTermProviderArguments provider)
                Nothing -> Left "a unary membership premise must retain an exact source provider"
        ExactStructureAtomTemplate{} ->
            Left "an exact-shape premise requires a finite-evidence rule"

    compileDirectArgument argument =
        case ( SourceTerm.sourceTermOccurrenceProvider argument
             , scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore argument)
             ) of
            (Nothing, CBound index)
                | index < binderArity ->
                    Right (ViewVariableIx index)
            (Just{}, _) ->
                Left
                    "direct theorem variables must not be provider occurrences"
            _ ->
                Left
                    "view arguments must be direct universally closed variables"

    assertionFocus label assertion = atomFocus label (Notion.sourceAssertionAtom assertion)
    atomFocus label = \case
        NegativeAtomTemplate body -> atomFocus label body
        GlobalAtomTemplate head' arguments -> case globalNotionHeadRole head' of
            HostedGlobalNotion -> firstArgument arguments
            UnhostedGlobalPredicate ->
                Left ("the marked view " <> label <> " is a hostless source-terminal predicate")
        StructureAtomTemplate _head arguments -> firstArgument arguments
        MembershipAtomTemplate element _set -> Right element
        ExactStructureAtomTemplate _shape subject -> Right subject
      where
        firstArgument = maybe
            (Left ("the marked view " <> label <> " has no subject"))
            (Right . fst) . Vector.uncons

    sourceTerminalConclusion assertion = case Notion.sourceAssertionAtom assertion of
        GlobalAtomTemplate head' _arguments -> globalNotionHeadRole head' == UnhostedGlobalPredicate
        _ -> False

    templateVariables = \case
        GlobalNotionViewPremise _head terms ->
            Set.unions
                (RuleTerm.ruleTermTemplateVariables <$> toList terms)
        StructureNotionViewPremise _head terms ->
            Set.unions
                (RuleTerm.ruleTermTemplateVariables <$> toList terms)
        ExactProviderMembershipPremise element _provider arguments ->
            Set.unions
                ( RuleTerm.ruleTermTemplateVariables element
                : ( RuleTerm.ruleTermTemplateVariables
                  <$> toList arguments
                  )
                )

    atomTemplateVariables = ruleAtomVariables

prepareEnvelopeAssumptions
    :: Location
    -> [ScopedCheckedCore ObjectId]
    -> ScopedCheckedCore ObjectId
    -> PreparedProofTree
    -> Prepare PreparedProofTree
prepareEnvelopeAssumptions location antecedents bodyGoal bodyProof =
    go antecedents bodyGoal bodyProof
  where
    go [] _continuationGoal proof =
        pure proof
    go (antecedent : rest) continuationGoal proof = do
        let innerGoal =
                foldr
                    (\premise continuation ->
                        fromMaybe
                            (impossible
                                "prepared envelope antecedents changed context")
                            (implyScopedCore premise continuation))
                    continuationGoal
                    rest
            currentGoal =
                fromMaybe
                    (impossible
                        "prepared envelope antecedent changed context")
                    (implyScopedCore antecedent innerGoal)
        wrapped <-
            go rest continuationGoal proof
        (opening, _detailed) <-
            prepareAssumptionOpening
                location
                currentGoal
                antecedent
        pure (PreparedAssume opening wrapped)

prepareInitialSetInductionView
    :: Raw.Stmt
    -> Elaboration.ElaborationContext
    -> [Raw.VarSymbol]
    -> [Elaboration.LocalId]
    -> [ScopedCheckedCore ObjectId]
    -> ScopedCheckedCore ObjectId
    -> Prepare InitialSetInductionView
prepareInitialSetInductionView
        statement context variables identities antecedents bodyGoal = do
    unless (length variables == length identities)
        (impossible
            "opened claim binders lost their source identity association")
    foci <- traverse checkedFocus (zip variables identities)
    let property = foldr implyChecked bodyGoal antecedents
        support = Elaboration.elaborationContextSupport context
    unless
        ( scopedCoreContext property
            == (snd <$> Vector.toList support)
        )
        (impossible
            "initial set-induction property changed its checked context")
    pure
        (InitialSetInductionView
            foci support property antecedents bodyGoal
            (claimLeadingUniversalName statement))
  where
    checkedFocus (variable, identity) = do
        index <-
            maybe
                (impossible
                    "an opened claim binder is absent from its exact context")
                pure
                (Elaboration.elaborationContextIndex variable context)
        case Elaboration.elaborationContextSupport context
                Vector.!? (fromIntegral index) of
            Just (actualIdentity, TySet)
                | actualIdentity == identity ->
                    pure
                        (InitialSetInductionFocus
                            variable identity index)
            _ ->
                impossible
                    "an initial set-induction focus changed identity or type"

    implyChecked antecedent conclusion =
        fromMaybe
            (impossible
                "an exact claim antecedent changed context")
            (implyScopedCore antecedent conclusion)

claimLeadingUniversalName :: Raw.Stmt -> Maybe Raw.VarSymbol
claimLeadingUniversalName = \case
    Raw.StmtFormula
            (Raw.FormulaQuantified _location Raw.Universally
                (variable :| _rest) _bound _formula) ->
        Just variable
    Raw.SymbolicForall _location (variable :| _rest)
            _bound _suchThat _statement ->
        Just variable
    Raw.StmtQuantPhrase
            _location
            (Raw.QuantPhrase Raw.Universally
                (Raw.NounPhrase _left _noun (Raw.NounBinder variables _bound) _right _suchThat))
            _statement ->
        listToMaybe variables
    Raw.StmtVerbPhrase
            (Raw.TermQuantified Raw.Universally _location
                (Raw.NounPhrase _left _noun (Raw.NounBinder variable _bound) _right _suchThat)
                :| [])
            _verb ->
        variable
    Raw.StmtNoun
            _sign
            (Raw.TermQuantified Raw.Universally _location
                (Raw.NounPhrase _left _noun (Raw.NounBinder variable _bound) _right _suchThat)
                :| [])
            _nounPhrase ->
        variable
    _statement ->
        Nothing

prepareProofTree
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> SetInductionBoundary
    -> ScopedCheckedCore ObjectId
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareProofTree fallback context locals inductionBoundary goal =
    prepareProofGoalTree
        fallback context locals inductionBoundary
        (plainPreparedProofGoal goal)

prepareProofGoalTree
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> SetInductionBoundary
    -> PreparedProofGoal
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareProofGoalTree
        fallback context locals inductionBoundary preparedGoal proof =
    Reader.local
        (\environment ->
            environment
                { prepareProofMode =
                    proofModeForProof goal proof
                        (prepareProofMode environment)
                })
        (prepareProofStep
            fallback context locals inductionBoundary preparedGoal proof)
  where
    goal = preparedProofGoalCore preparedGoal

prepareProofStep
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> SetInductionBoundary
    -> PreparedProofGoal
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareProofStep fallback context locals inductionBoundary preparedGoal = \case
    Raw.Omitted location ->
        pure (PreparedOmitted location goal)
    Raw.Qed maybeLocation justification ->
        PreparedQed
            <$> prepareProofGoalDischarge
                (maybe ImplicitTheoremClose (const FinalFollows) maybeLocation)
                (fromMaybe fallback maybeLocation)
                context
                locals
                preparedGoal
                justification
    Raw.Fix location binders condition continuation ->
        prepareFixBinders
            fallback location context locals goal
            binders condition continuation
    Raw.Assume location _intro statement continuation -> do
        supplied <- prepareStatement context statement
        unless (isAssumptiveGoal goal)
            (throwProof
                (ProofExpectedAssumptiveGoal location (goalShape goal)))
        (opening, detailed) <-
            prepareAssumptionOpening
                location
                goal
                (Elaboration.elaboratedPropositionCore supplied)
        let assumption =
                LooseDeduction.detailedOpeningSupplied detailed
            conclusion =
                LooseDeduction.detailedOpeningResidual detailed
        local <- allocateLocal ProofAssumption context assumption
        context' <-
            extendContextWithSourceLocal
                local
                (Elaboration.elaboratedPropositionEvidence supplied)
                (Elaboration.elaboratedPropositionEqualities supplied)
                context
        prepared <-
            prepareProofTree
                fallback
                context'
                (locals <> [local])
                RecursiveProofInduction
                conclusion
                continuation
        pure (PreparedAssume opening prepared)
    Raw.TakeVar location variables bound statement justification continuation -> do
        prepareSymbolicTake
            fallback location context locals goal variables bound statement
            justification continuation
    Raw.TakeTyped
            location variables concreteType statement justification continuation ->
        prepareTypedTake
            fallback location context locals goal variables
            (Elaboration.concreteTypeCoreType concreteType)
            statement justification continuation
    Raw.TakeNoun location nounPhrase justification continuation ->
        prepareNounTake
            fallback location context locals goal nounPhrase
            justification continuation
    Raw.BySetInduction location variable continuation ->
        prepareSetInduction
            fallback location context locals inductionBoundary goal
            variable continuation
    Raw.ByStructuralInduction location variable cases ->
        prepareStructuralInduction location context locals preparedGoal variable cases
    Raw.ByOrdInduction location continuation ->
        prepareTransfiniteInduction
            fallback location context locals inductionBoundary goal
            continuation
    Raw.Have location _intro
            (Raw.SymbolicExists _existential variables bound statement)
            justification continuation ->
        prepareSymbolicTake
            fallback location context locals goal variables bound statement
            justification continuation
    Raw.Have location _intro statement justification continuation -> do
        elaborated <- prepareStatement context statement
        let claim = Elaboration.elaboratedPropositionCore elaborated
            preparedClaim = sourcePreparedProofGoal
                claim
                (Elaboration.elaboratedPropositionEvidence elaborated)
        discharge <-
            prepareProofGoalDischarge
                InlineObviousInference
                location context locals preparedClaim justification
        local <- allocateLocal ProofDerivedClaim context claim
        context' <-
            extendContextWithSourceLocal
                local
                (Elaboration.elaboratedPropositionEvidence elaborated)
                (Elaboration.elaboratedPropositionEqualities elaborated)
                context
        PreparedHave claim discharge
            <$> prepareProofGoalTree
                fallback
                context'
                (locals <> [local])
                RecursiveProofInduction
                preparedGoal
                continuation
    Raw.Since
            premiseLocation sinceStatement premiseJustification
            claimLocation statement claimJustification
            continuation -> do
        sinceElaborated <- prepareStatement context sinceStatement
        let sinceProposition =
                Elaboration.elaboratedPropositionCore sinceElaborated
            preparedSince = sourcePreparedProofGoal
                sinceProposition
                (Elaboration.elaboratedPropositionEvidence sinceElaborated)
        premiseDischarge <-
            prepareProofGoalDischarge
                InlineObviousInference
                premiseLocation
                context
                locals
                preparedSince
                premiseJustification
        temporaryPremise <-
            allocateLocal ProofDerivedClaim context sinceProposition
        temporaryContext <-
            extendContextWithSourceLocal
                temporaryPremise
                (Elaboration.elaboratedPropositionEvidence sinceElaborated)
                (Elaboration.elaboratedPropositionEqualities sinceElaborated)
                context
        claimElaborated <- prepareStatement temporaryContext statement
        let claim = Elaboration.elaboratedPropositionCore claimElaborated
            preparedClaim = sourcePreparedProofGoal
                claim
                (Elaboration.elaboratedPropositionEvidence claimElaborated)
        claimDischarge <-
            prepareProofGoalDischarge
                InlineObviousInference
                claimLocation
                temporaryContext
                (locals <> [temporaryPremise])
                preparedClaim
                claimJustification
        claimLocal <-
            allocateLocal ProofDerivedClaim context claim
        claimContext <-
            extendContextWithSourceLocal
                claimLocal
                (Elaboration.elaboratedPropositionEvidence claimElaborated)
                (Elaboration.elaboratedPropositionEqualities claimElaborated)
                context
        PreparedSince
            sinceProposition premiseDischarge temporaryPremise
            claim claimDischarge
            <$> prepareProofGoalTree
                fallback
                claimContext
                (locals <> [claimLocal])
                RecursiveProofInduction
                preparedGoal
                continuation
    Raw.Suffices location statement justification continuation -> do
        elaborated <- prepareStatement context statement
        let reduction = Elaboration.elaboratedPropositionCore elaborated
            preparedReduction = sourcePreparedProofGoal
                reduction
                (Elaboration.elaboratedPropositionEvidence elaborated)
        implication <-
            maybe
                (impossible
                    "a checked suffices reduction changed lexical context")
                pure
                (implyScopedCore reduction goal)
        discharge <-
            prepareDischarge
                InlineObviousInference
                location context locals implication justification
        PreparedSuffices goal reduction implication discharge
            <$> prepareProofGoalTree
                fallback
                context
                locals
                (SourceStatementInduction
                    (claimLeadingUniversalName statement))
                preparedReduction
                continuation
    Raw.Calc location quantifier calculation continuation -> do
        (prepared,result) <- prepareCalculation location context locals quantifier calculation
        local <-
            allocateLocal
                ProofDerivedClaim
                context
                (preparedDischargeGoal prepared)
        extended <- extendContextWithSourceLocal local (Elaboration.elaboratedPropositionEvidence result)
            (Elaboration.elaboratedPropositionEqualities result) context
        PreparedCalculate prepared
            <$> prepareProofGoalTree
                fallback
                extended
                (locals <> [local])
                RecursiveProofInduction
                preparedGoal
                continuation
    Raw.Subclaim location statement subproof continuation -> do
        elaborated <- prepareStatement context statement
        let claim = Elaboration.elaboratedPropositionCore elaborated
            preparedClaim = sourcePreparedProofGoal
                claim
                (Elaboration.elaboratedPropositionEvidence elaborated)
        preparedSubproof <-
            prepareProofGoalTree
                location
                context
                locals
                (SourceStatementInduction
                    (claimLeadingUniversalName statement))
                preparedClaim
                subproof
        local <- allocateLocal ProofDerivedClaim context claim
        context' <-
            extendContextWithSourceLocal
                local
                (Elaboration.elaboratedPropositionEvidence elaborated)
                (Elaboration.elaboratedPropositionEqualities elaborated)
                context
        PreparedSubclaim claim preparedSubproof
            <$> prepareProofGoalTree
                fallback
                context'
                (locals <> [local])
                RecursiveProofInduction
                preparedGoal
                continuation
    Raw.Define location variable expression continuation -> do
        preparedBody <-
            liftDriver
                (Elaboration.elaborateSetExpression context expression)
                >>= either
                    (throwProof . ProofElaborationFailed)
                    pure
        let body = Elaboration.elaboratedSetExpressionCore preparedBody
            source = Elaboration.elaboratedSetExpressionSource preparedBody
        identity <- allocateLocalIdentity
        context' <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (Elaboration.extendElaborationContext
                    ((identity, variable) :| [])
                    context)
        case Elaboration.elaboratedSetExpressionConstruction preparedBody of
            Nothing -> do
                separationCharacteristic <-
                    liftDriver
                        (Declaration.currentFoundationAxiomLowering
                            SeparationCharacteristic)
                definition <-
                    maybe
                        (impossible
                            "an exact set expression did not form a local definition")
                        pure
                        (scopedSetDefinition separationCharacteristic body)
                local <-
                    allocateLocal ProofLocalDefinition context' definition
                aliasContext <- extendContextWithLocalAlias
                    location identity source local context'
                PreparedDefine identity body (definition :| [])
                    <$> prepareProofTree
                        fallback aliasContext (locals <> [local])
                        RecursiveProofInduction
                        (weakenCheckedScopedCore TySet goal)
                        continuation
            Just (Elaboration.ElaboratedUnconditionalSetConstruction construction) -> do
                characteristics <- prepareConstructionFoundation
                (extensional, equation) <-
                    maybe
                        (impossible
                            "a checked named construction has no definition views")
                        pure
                        (namedSetConstructionLocalViews
                            characteristics construction)
                extensionalLocal <-
                    allocateLocal
                        ProofLocalConstructionExtensional context' extensional
                equationLocal <-
                    allocateLocal
                        ProofLocalConstructionEquation context' equation
                aliasContext <- extendContextWithLocalAlias
                    location identity source equationLocal context'
                PreparedDefine identity body (extensional :| [equation])
                    <$> prepareProofTree
                        fallback aliasContext
                        (locals <> [extensionalLocal, equationLocal])
                        RecursiveProofInduction
                        (weakenCheckedScopedCore TySet goal)
                        continuation
            Just (Elaboration.ElaboratedRelationalSetConstruction construction) -> do
                characteristics <- prepareConstructionFoundation
                let functionality =
                        relationalSetConstructionFunctionality construction
                discharge <-
                    preparePreparedDischarge
                        location context locals functionality
                        Nothing
                        PreparedInternalAuto
                (extensional, equation) <-
                    maybe
                        (impossible
                            "a checked relational construction has no admitted definition views")
                        pure
                        (relationalSetConstructionLocalViews
                            characteristics construction functionality)
                extensionalLocal <-
                    allocateLocal
                        ProofLocalConstructionExtensional context' extensional
                equationLocal <-
                    allocateLocal
                        ProofLocalConstructionEquation context' equation
                aliasContext <- extendContextWithLocalAlias
                    location identity source equationLocal context'
                PreparedDefineRelational
                    identity body discharge (extensional :| [equation])
                    <$> prepareProofTree
                        fallback aliasContext
                        (locals <> [extensionalLocal, equationLocal])
                        RecursiveProofInduction
                        (weakenCheckedScopedCore TySet goal)
                        continuation
    Raw.DefineTyped
            location variable concreteType expression continuation -> do
        preparedBody <-
            liftDriver
                (Elaboration.elaborateExpression context expression)
                >>= either
                    (throwProof . ProofElaborationFailed)
                    pure
        let body = Elaboration.elaboratedExpressionCore preparedBody
            source = Elaboration.elaboratedExpressionSource preparedBody
            declaredType = Elaboration.concreteTypeCoreType concreteType
        unless (scopedCoreType body == declaredType)
            (throwProof
                (ProofElaborationFailed
                    (Elaboration.ElaborationObjectTypeMismatch
                        location declaredType (scopedCoreType body))))
        identity <- allocateLocalIdentity
        context' <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (Elaboration.extendTypedElaborationContext
                    ((identity, variable, declaredType) :| [])
                    context)
        let definition = scopedDefinition body
        local <-
            allocateLocal ProofLocalDefinition context' definition
        aliasContext <- case source of
            Just setSource | declaredType == TySet ->
                extendContextWithLocalAlias
                    location identity setSource local context'
            _ -> pure context'
        PreparedDefine identity body (definition :| [])
            <$> prepareProofTree
                fallback aliasContext (locals <> [local])
                RecursiveProofInduction
                (weakenCheckedScopedCore declaredType goal)
                continuation
    Raw.DefineFunction
            location function argument value bound domain continuation -> do
        unless (argument == bound)
            (throwProof
                (ProofLocalFunctionBinderMismatch (locate bound)))
        when (function == argument)
            (throwProof
                (ProofLocalFunctionNameConflict (locate function)))
        argumentIdentity <- allocateLocalIdentity
        argumentContext <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (Elaboration.extendElaborationContext
                    ((argumentIdentity, argument) :| [])
                    context)
        graph <-
            liftDriver
                (Elaboration.elaborateLocalFunctionGraph
                    location context argumentContext domain value)
                >>= either
                    (throwProof . ProofElaborationFailed)
                    pure
        functionIdentity <- allocateLocalIdentity
        functionContext <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (Elaboration.extendElaborationContext
                    ((functionIdentity, function) :| [])
                    context)
        replacementCharacteristic <-
            liftDriver
                (Declaration.currentFoundationAxiomLowering
                    ReplacementCharacteristic)
        definition <-
            maybe
                (impossible
                    "a checked replacement graph did not form a local definition")
                pure
                (scopedCharacteristicDefinition
                    replacementCharacteristic
                    (Elaboration.elaboratedLocalFunctionGraphCore graph)
                    ( Elaboration.elaboratedLocalFunctionGraphDomain graph
                        :| [Elaboration.elaboratedLocalFunctionGraphMap graph]
                    ))
        local <-
            allocateLocal ProofLocalDefinition functionContext definition
        PreparedDefineFunction
            functionIdentity
            (Elaboration.elaboratedLocalFunctionGraphCore graph)
            definition
            <$> prepareProofTree
                fallback
                functionContext
                (locals <> [local])
                RecursiveProofInduction
                (weakenCheckedScopedCore TySet goal)
                continuation
    Raw.ByCase location sourceCases ->
        prepareByCase
            location context locals preparedGoal sourceCases
    Raw.ByContradiction location continuation -> do
        let falsum = falsumScopedCore (scopedCoreContext goal)
        negation <-
            maybe
                (structuralFailure
                    location
                    "proof by contradiction requires a proposition goal")
                pure
                (negateScopedCore goal)
        local <- allocateLocal ProofAssumption context negation
        prepared <-
            prepareProofTree
                location
                context
                (locals <> [local])
                RecursiveProofInduction
                falsum
                continuation
        validateStructuralComposition
            location [goal, negation, falsum]
            (\foundation globalType ->
                KernelProof.validateDoubleNegationComposition
                    foundation globalType goal negation falsum)
        pure
            (PreparedByContradiction
                goal negation falsum prepared)
    Raw.Contradiction location justification -> do
        let falsum = falsumScopedCore (scopedCoreContext goal)
        discharge <-
            prepareDischarge
                ContradictionObligation
                location
                context
                locals
                falsum
                justification
        validateStructuralComposition
            location [goal, falsum]
            (\foundation globalType ->
                KernelProof.validateFalsumEliminationComposition
                    foundation globalType goal falsum)
        pure (PreparedContradiction goal falsum discharge)
    proof ->
        throwProof
            (ProofUnsupportedStep
                (proofLocation fallback proof))
  where
    goal = preparedProofGoalCore preparedGoal

prepareSetInduction
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> SetInductionBoundary
    -> ScopedCheckedCore ObjectId
    -> Maybe Raw.Term
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareSetInduction
        fallback location context locals boundary goal sourceFocus
        continuation = do
    selected <-
        selectSetInductionFocus
            location context boundary goal sourceFocus
    case selected of
        SelectedInitialSetInduction
                (InitialSetInductionFocus _variable identity index) -> do
            (foci, expectedSupport, property, antecedents, childTarget) <-
                case boundary of
                    InitialClaimInduction
                            (InitialSetInductionView
                                foundFoci support foundProperty
                                foundAntecedents foundTarget _leadingName) ->
                        pure
                            ( foundFoci
                            , support
                            , foundProperty
                            , foundAntecedents
                            , foundTarget
                            )
                    RecursiveProofInduction ->
                        impossible
                            "an initial induction focus escaped its claim boundary"
                    SourceStatementInduction _leadingName ->
                        impossible
                            "an initial induction focus escaped its claim boundary"
            unless
                ( Elaboration.elaborationContextSupport context == expectedSupport
                    && goal == childTarget
                    && any (sameInitialFocus identity index) foci
                )
                (throwProof
                    (ProofSetInductionGoalMismatch location))
            PreparedSetInduction
                <$> prepareCheckedSetInduction
                    fallback location context locals
                    (PreparedInitialSetInductionFocus identity index)
                    index property antecedents childTarget continuation
        SelectedLeadingSetInduction sourceName -> do
            (binderType, property) <-
                maybe
                    (throwProof
                        (ProofSetInductionGoalMismatch location))
                    pure
                    (openScopedForall goal)
            unless (binderType == TySet)
                (throwProof
                    (ProofSetInductionGoalMismatch location))
            identity <- allocateLocalIdentity
            extendedContext <-
                either
                    (throwProof . ProofElaborationFailed)
                    pure
                    (case sourceName of
                        Just variable ->
                            Elaboration.extendElaborationContext
                                ((identity, variable) :| [])
                                context
                        Nothing ->
                            Elaboration.extendAnonymousElaborationContext
                                identity context)
            let expectedResult = weakenCheckedScopedCore TySet goal
            prepared <- prepareCheckedSetInduction
                fallback location extendedContext locals
                (PreparedLeadingSetInductionFocus identity)
                0 property [] property continuation
            unless
                (preparedSetInductionResult prepared == expectedResult)
                (throwProof
                    (ProofSetInductionGoalMismatch location))
            pure (PreparedSetInduction prepared)
  where
    sameInitialFocus expectedIdentity expectedIndex
            (InitialSetInductionFocus _variable identity index) =
        identity == expectedIdentity && index == expectedIndex

prepareTransfiniteInduction
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> SetInductionBoundary
    -> ScopedCheckedCore ObjectId
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareTransfiniteInduction
        fallback location context locals boundary goal continuation =
    case boundary of
        InitialClaimInduction
                (InitialSetInductionView
                    [] _support _property _antecedents _target leadingName) ->
            prepareLeading leadingName
        InitialClaimInduction
                (InitialSetInductionView
                    foci support property antecedents childTarget
                    _leadingName) ->
            prepareInitial
                foci support property antecedents childTarget
        SourceStatementInduction leadingName ->
            prepareLeading leadingName
        RecursiveProofInduction ->
            throwProof
                (ProofTransfiniteInductionGoalMismatch location)
  where
    prepareInitial foci expectedSupport property antecedents childTarget = do
        unless
            ( Elaboration.elaborationContextSupport context == expectedSupport
                && goal == childTarget
            )
            (throwProof
                (ProofTransfiniteInductionGoalMismatch location))
        let guardCandidates =
                [ (focus, position, predicate)
                | focus@(InitialSetInductionFocus
                        _variable _identity selected) <- foci
                , (position, antecedent) <-
                    zip [0 :: Natural ..] antecedents
                , Just predicate <-
                    [directGuardPredicate selected antecedent]
                ]
        when (null guardCandidates)
            (throwProof
                (ProofTransfiniteInductionGoalMismatch location))
        resolved <-
            traverse
                (\(focus, position, predicate) -> do
                    heredity <- resolveHeredity predicate
                    pure
                        ((\facts -> (focus, position, facts))
                            <$> heredity))
                guardCandidates
        let resolvedFocusName
                (InitialSetInductionFocus variable _identity _index,
                    _position, _facts) = variable
        (focus, guardPosition, heredityFacts) <-
            case catMaybes resolved of
                [] ->
                    throwProof
                        (ProofTransfiniteInductionHeredityUnavailable
                            location)
                [only] -> pure only
                first : second : remaining ->
                    throwProof
                        (ProofTransfiniteInductionFocusAmbiguous
                            location
                            (resolvedFocusName first
                                :| (resolvedFocusName second
                                    : (resolvedFocusName <$> remaining))))
        let InitialSetInductionFocus
                _variable identity index = focus
            remainingAntecedents =
                [ antecedent
                | (position, antecedent) <-
                    zip [0 :: Natural ..] antecedents
                , position /= guardPosition
                ]
            reducedProperty =
                foldr implyChecked childTarget remainingAntecedents
        simplifiedHypothesis <-
            inductionHypothesis index reducedProperty
        prepared <-
            prepareCheckedSetInductionWithChild
                location context
                (PreparedInitialSetInductionFocus identity index)
                index property antecedents childTarget
                (prepareInitialChild
                    childTarget simplifiedHypothesis heredityFacts)
        pure (PreparedSetInduction prepared)

    prepareLeading sourceName = do
        (binderType, property) <-
            maybe
                (throwProof
                    (ProofTransfiniteInductionGoalMismatch location))
                pure
                (openScopedForall goal)
        unless (binderType == TySet)
            (throwProof
                (ProofTransfiniteInductionGoalMismatch location))
        (guardProposition, childTarget) <-
            maybe
                (throwProof
                    (ProofTransfiniteInductionGoalMismatch location))
                pure
                (openScopedImplication property)
        predicate <-
            maybe
                (throwProof
                    (ProofTransfiniteInductionGoalMismatch location))
                pure
                (directGuardPredicate 0 guardProposition)
        heredityFacts <-
            resolveHeredity predicate >>= maybe
                (throwProof
                    (ProofTransfiniteInductionHeredityUnavailable
                        location))
                pure
        identity <- allocateLocalIdentity
        extendedContext <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (case sourceName of
                    Just variable ->
                        Elaboration.extendElaborationContext
                            ((identity, variable) :| [])
                            context
                    Nothing ->
                        Elaboration.extendAnonymousElaborationContext
                            identity context)
        simplifiedHypothesis <-
            inductionHypothesis 0 childTarget
        let expectedResult = weakenCheckedScopedCore TySet goal
        prepared <-
            prepareCheckedSetInductionWithChild
                location extendedContext
                (PreparedLeadingSetInductionFocus identity)
                0 property [] property
                (prepareLeadingChild
                    extendedContext
                    guardProposition
                    childTarget
                    simplifiedHypothesis
                    heredityFacts)
        unless
            (preparedSetInductionResult prepared == expectedResult)
            (throwProof
                (ProofTransfiniteInductionGoalMismatch location))
        pure (PreparedSetInduction prepared)

    implyChecked antecedent conclusion =
        fromMaybe
            (impossible
                "a transfinite-induction guard changed checked context")
            (implyScopedCore antecedent conclusion)

    inductionHypothesis selected property =
        maybe
            (throwProof
                (ProofTransfiniteInductionGoalMismatch location))
            (\(_predicate, hypothesis, _step, _result) -> pure hypothesis)
            (scopedSetInductionInstance selected property)

    directGuardPredicate selected antecedent =
        case scopedCoreTerm antecedent of
            CApp (CGlobal predicate) (CBound index)
                | index == selected -> Just predicate
            _ -> Nothing

    resolveHeredity predicate = do
        globalTyping <- prepareGlobalTyping
        let predicateType = lookupGlobalType globalTyping predicate
        unless
            (predicateType
                == Just (TyArrow TySet TyProp))
            (impossible
                "a checked unary induction guard lost its predicate type")
        let targetTerm = hereditaryPredicateTarget predicate
        target <-
            either
                (const
                    (impossible
                        "a checked hereditary-predicate target is ill-typed"))
                pure
                (checkCanonicalCore globalTyping targetTerm)
        references <-
            liftDriver
                (Declaration.resolveVisibleFactTargetsLowering target)
        pure (NonEmpty.nonEmpty references)

    hereditaryPredicateTarget predicate =
        CForall TySet
            (CForall TySet
                (CImp
                    (CApp (CGlobal predicate) (CBound 1))
                    (CImp
                        (CApp
                            (CApp
                                (CIntrinsic Member)
                                (CBound 0))
                            (CBound 1))
                        (CApp (CGlobal predicate) (CBound 0)))))

    prepareInitialChild childTarget simplifiedHypothesis heredityFacts
            _rawHypothesis rawLocal = do
        bridge <-
            prepareBridge
                context
                (locals <> [rawLocal])
                simplifiedHypothesis
                heredityFacts
        simplifiedLocal <-
            allocateLocal
                ProofDerivedClaim
                context
                simplifiedHypothesis
        child <-
            prepareProofTree
                fallback
                context
                (locals <> [simplifiedLocal])
                RecursiveProofInduction
                childTarget
                continuation
        pure
            (PreparedHave
                simplifiedHypothesis
                bridge
                child)

    prepareLeadingChild extendedContext guardProposition childTarget
            simplifiedHypothesis heredityFacts
            _rawHypothesis rawLocal = do
        guardLocal <-
            allocateLocal
                ProofAssumption
                extendedContext
                guardProposition
        bridge <-
            prepareBridge
                extendedContext
                (locals <> [rawLocal, guardLocal])
                simplifiedHypothesis
                heredityFacts
        simplifiedLocal <-
            allocateLocal
                ProofDerivedClaim
                extendedContext
                simplifiedHypothesis
        child <-
            prepareProofTree
                fallback
                extendedContext
                (locals <> [guardLocal, simplifiedLocal])
                RecursiveProofInduction
                childTarget
                continuation
        pure
            (PreparedGuardAssume guardProposition
                (PreparedHave
                    simplifiedHypothesis
                    bridge
                    child))

    prepareBridge bridgeContext bridgeLocals simplifiedHypothesis
            heredityFacts = do
        environment <- Reader.ask
        preparePreparedDischargeWith
            (proofModeForGoal simplifiedHypothesis
                (prepareProofMode environment))
            (prepareFoundationAuxiliaries environment)
            (Just
                (Declaration.explicitVampirePremisePolicy heredityFacts))
            Nothing
            location
            bridgeContext
            bridgeLocals
            (plainPreparedProofGoal simplifiedHypothesis)
            PreparedInternalAuto

prepareCheckedSetInduction
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedSetInductionFocus
    -> Natural
    -> ScopedCheckedCore ObjectId
    -> [ScopedCheckedCore ObjectId]
    -> ScopedCheckedCore ObjectId
    -> Raw.Proof
    -> Prepare PreparedSetInduction
prepareCheckedSetInduction
        fallback location context locals focus selected property antecedents
        childTarget continuation =
    prepareCheckedSetInductionWithChild
        location context focus selected property antecedents childTarget
        (\_hypothesis local ->
            prepareProofTree
                fallback
                context
                (locals <> [local])
                RecursiveProofInduction
                childTarget
                continuation)

prepareCheckedSetInductionWithChild
    :: Location
    -> Elaboration.ElaborationContext
    -> PreparedSetInductionFocus
    -> Natural
    -> ScopedCheckedCore ObjectId
    -> [ScopedCheckedCore ObjectId]
    -> ScopedCheckedCore ObjectId
    -> ( ScopedCheckedCore ObjectId
         -> PreparedLocal
         -> Prepare PreparedProofTree
       )
    -> Prepare PreparedSetInduction
prepareCheckedSetInductionWithChild
        location context focus selected property antecedents childTarget
        prepareChild = do
    (_predicate, hypothesis, _step, result) <-
        maybe
            (throwProof
                (ProofSetInductionGoalMismatch location))
            pure
            (scopedSetInductionInstance selected property)
    validateStructuralComposition
        location
        (property : hypothesis : result : childTarget : antecedents)
        (\foundation globalType ->
            KernelProof.validateSetInductionComposition
                foundation globalType selected property antecedents
                childTarget hypothesis result)
    local <- allocateLocal ProofAssumption context hypothesis
    child <- prepareChild hypothesis local
    pure
        (PreparedCheckedSetInduction
            focus property antecedents childTarget hypothesis result child)

preparedSetInductionResult
    :: PreparedSetInduction
    -> ScopedCheckedCore ObjectId
preparedSetInductionResult
        (PreparedCheckedSetInduction
            _focus _property _antecedents _target _hypothesis result _child) =
    result

selectSetInductionFocus
    :: Location
    -> Elaboration.ElaborationContext
    -> SetInductionBoundary
    -> ScopedCheckedCore ObjectId
    -> Maybe Raw.Term
    -> Prepare SelectedSetInductionFocus
selectSetInductionFocus location context boundary goal sourceFocus = do
    explicit <- traverse simpleVariable sourceFocus
    let (initialFoci, retainedLeadingName) =
            case boundary of
                InitialClaimInduction
                        (InitialSetInductionView
                            foci _support _property _antecedents _target
                            leadingName) ->
                    (foci, leadingName)
                SourceStatementInduction leadingName ->
                    ([], leadingName)
                RecursiveProofInduction ->
                    ([], Nothing)
        leadingAvailable =
            case openScopedForall goal of
                Just (TySet, _body) -> True
                _ -> False
    case explicit of
        Just variable ->
            case find (initialNamed variable) initialFoci of
                Just focus ->
                    pure (SelectedInitialSetInduction focus)
                Nothing
                    | leadingAvailable
                    , isJust
                        (Elaboration.elaborationContextIndex variable context) ->
                        throwProof
                            (ProofSetInductionBinderConflict
                                location variable)
                    | leadingAvailable ->
                        pure
                            (SelectedLeadingSetInduction
                                (Just variable))
                    | isJust
                        (Elaboration.elaborationContextIndex variable context) ->
                        throwProof
                            (ProofSetInductionActiveBinderIneligible
                                location variable)
                    | otherwise ->
                        throwProof
                            (ProofSetInductionVariableNotActive
                                location variable)
        Nothing ->
            case
                ( (SelectedInitialSetInduction <$> initialFoci)
                    <> [ SelectedLeadingSetInduction retainedLeadingName
                       | leadingAvailable
                       ]
                ) of
                [only] -> pure only
                [] ->
                    throwProof
                        (ProofSetInductionGoalMismatch location)
                candidates ->
                    case NonEmpty.nonEmpty
                            (catMaybes
                                (selectedFocusSourceName <$> candidates)) of
                        Nothing ->
                            throwProof
                                (ProofSetInductionGoalMismatch location)
                        Just names ->
                            throwProof
                                (ProofSetInductionFocusAmbiguous
                                    location names)
  where
    simpleVariable = \case
        Raw.TermExpr (Raw.ExprVar variable) ->
            pure variable
        _term ->
            throwProof
                (ProofSetInductionVariableRequired location)

    initialNamed variable
            (InitialSetInductionFocus candidate _identity _index) =
        candidate == variable

    selectedFocusSourceName = \case
        SelectedInitialSetInduction
                (InitialSetInductionFocus variable _identity _index) ->
            Just variable
        SelectedLeadingSetInduction sourceName ->
            sourceName

-- Cases are ordinary independent subproofs. Their closed obligations become
-- local facts only for the final, kernel-checked application of predicate
-- induction; datatype metadata supplies no evidence of its own.
prepareStructuralInduction
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> Raw.VarSymbol
    -> NonEmpty Raw.NamedCase
    -> Prepare PreparedProofTree
prepareStructuralInduction location context locals (PreparedProofGoal goal evidence) focus sourceCases = do
    typing <- prepareGlobalTyping
    aligned <- alignPreparedLocals context locals
    (reference, parameters, carrier, predicate, selected, caseContext, caseLocals, projections) <-
        case (scopedCoreTerm goal, strip evidence) of
            (CForall TySet (CImp guardTerm body), SourceEvidence.SourceBind inner)
                | SourceEvidence.SourceRequire guardEvidence _ <- strip inner
                , Just (reference, arguments, carrier) <- sourceMembership 0 guardEvidence
                , guardTerm == member (CBound 0) carrier -> do
                    when (isJust (Elaboration.elaborationContextIndex focus context))
                        (invalid "the bounded variable conflicts with an active variable")
                    when (any (depends 0) (carrier : arguments))
                        (invalid "the family parameters must be independent of the induction variable")
                    empty <- either (structuralFailure location . Text.pack . show) pure
                        (checkScopedCanonicalCore typing (scopedCoreContext goal) (CIntrinsic Empty))
                    let lower term = do
                            scoped <- either (structuralFailure location . Text.pack . show) pure
                                (checkScopedCanonicalCore typing (TySet : scopedCoreContext goal) term)
                            scopedCoreTerm <$> either (structuralFailure location . Text.pack . show) pure
                                (instantiateScopedCore empty scoped)
                    arguments' <- traverse lower arguments
                    carrier' <- lower carrier
                    pure (reference, arguments', carrier', CLam TySet body,
                        Nothing, context, aligned, [])
            _ -> do
                index <- maybe (invalid "expected a bounded universal goal or an active datatype membership") pure
                    (Elaboration.elaborationContextIndex focus context)
                (observations, _) <- either
                    (invalid . Text.pack . show) pure
                    (Elaboration.formationObservationsFor Notion.defaultFormationSearchLimits
                        Elaboration.ProofNotionQuery context)
                let candidates = Set.toList (Set.fromList
                        [(reference, arguments, carrier)
                        | observation <- observations
                        , Just (reference, arguments, carrier) <-
                            [sourceMembership index (SourceEvidence.SourceAtom
                                (Elaboration.formationObservationAssertion observation))]])
                available <- fmap catMaybes $ for candidates \candidate@(reference, _, _) -> do
                    binding <- liftDriver (Declaration.resolveVisibleGlobalLowering (globalBindingRefKey reference))
                    pure $ case binding of
                        Just (resolved, _) | resolvedBindingRef resolved == reference
                            , isJust (semanticGlobalBindingDatatype (resolvedBindingDeclaration resolved)) -> Just candidate
                        _ -> Nothing
                (reference, arguments, carrier) <- case available of
                    [only] -> pure only
                    [] -> invalid "no active membership names a checked datatype"
                    _ -> invalid "several datatypes apply; use a bounded universal goal naming the intended carrier"
                when (any (depends index) (carrier : arguments))
                    (invalid "the family parameters must be independent of the induction variable")
                let membership = member (CBound index) carrier
                    remove term | term == membership = CTruth
                    remove (CAnd left right) = CAnd (remove left) (remove right)
                    remove term = term
                retained <- fmap catMaybes $ for aligned \local -> do
                    let original = preparedLocalProposition local
                        residual = remove (scopedCoreTerm original)
                    if scopedCoreTerm original == membership then pure Nothing else do
                        when (depends index residual)
                            (invalid "another active assumption or local definition depends on the induction variable; put it in the quantified or implicational motive")
                        if residual == scopedCoreTerm original then pure (Just (local, Nothing)) else do
                            checked <- either (structuralFailure location . Text.pack . show) pure
                                (checkScopedCanonicalCore typing (scopedCoreContext goal) residual)
                            projected <- allocateLocal ProofDerivedClaim context checked
                            bridge <- prepareCheckedProofEnvironment [original, checked] $ \foundation globalTyping -> do
                                kernel <- KernelProof.scopedProofContext foundation globalTyping
                                    (scopedCoreContext goal) [original]
                                premise <- KernelProof.indexedHypothesisProof kernel (hypothesisIx 0)
                                KernelProof.structuralLogicalProof kernel [premise] checked
                                    >>= maybe (Left KernelProof.ProofHypothesisNotFound) pure
                            built <- either (throwProof . ProofStructuralCompositionFailed location) pure bridge
                            let discharge = PreparedKernelDischarge location PreparedImplicitObvious checked [local] []
                                    (KernelProof.builtProofDerivation built)
                            pure (Just (projected, Just (preparedLocalOrdinalValue local, checked, discharge)))
                (predicate, _, _, _) <- maybe (invalid "the induction motive cannot be abstracted") pure
                    (scopedSetInductionInstance index goal)
                let (identity, _) = Elaboration.elaborationContextSupport context Vector.! fromIntegral index
                    replacements = [(old, preparedLocalOrdinalValue new, residual)
                        | (new, Just (old, residual, _)) <- retained]
                projected <- liftDriver (Elaboration.finishFormationScopePreparation
                    (Elaboration.projectProofElaborationContext identity
                        (Set.fromList [preparedLocalOrdinalValue local | (local, Nothing) <- retained])
                        replacements context))
                    >>= either (throwProof . ProofElaborationFailed . Elaboration.ElaborationFormationScopeFailed location) pure
                pure (reference, arguments, carrier, scopedCoreTerm predicate, Just index, projected, fst <$> retained,
                    [(residual, discharge) | (_, Just (_, residual, discharge)) <- retained])
    resolved <- liftDriver (Declaration.resolveVisibleGlobalLowering (globalBindingRefKey reference))
        >>= maybe (invalid "the carrier binding is no longer visible") (pure . fst)
    unless (resolvedBindingRef resolved == reference)
        (invalid "the carrier source binding is ambiguous")
    descriptor <- maybe (invalid "the named carrier is not a checked datatype") pure
        (semanticGlobalBindingDatatype (resolvedBindingDeclaration resolved))
    let descriptions = datatypeDescriptorCases descriptor
        keys = datatypeCaseName <$> toList descriptions
    names <- for sourceCases \named -> maybe (invalid "invalid induction case name") pure
        (Raw.datatypeCaseKey (Raw.namedCaseName named))
    unless (length names == Set.size (Set.fromList (toList names)))
        (invalid "duplicate induction case")
    unless (Set.fromList keys == Set.fromList (toList names))
        (invalid ("expected exactly these induction cases: " <> Text.intercalate ", " keys))
    let sources = Map.fromList (zip (toList names) (toList sourceCases))
        types = scopedCoreContext goal
        check term = either (structuralFailure location . Text.pack . show) pure
            (checkScopedCanonicalCore typing types term)
        instantiateParameters template = do
            let count = length parameters
            scoped <- either (structuralFailure location . Text.pack . show) pure
                (checkScopedCanonicalCore typing (replicate count TySet <> types) template)
            foldM (\body (argument, remaining) -> do
                checkedArgument <- check argument
                let lifted = iterate (weakenCheckedScopedCore TySet) checkedArgument !! remaining
                either (structuralFailure location . Text.pack . show) pure
                    (instantiateScopedCore lifted body)) scoped
                (zip (reverse parameters) (reverse [0 .. count - 1]))
    clauses <- for descriptions \description -> do
        constructor <- liftDriver (Declaration.resolveVisibleGlobalLowering (datatypeCaseConstructor description))
            >>= maybe (invalid "a datatype constructor is no longer visible") (pure . fst)
        unless (globalBindingRefOwner (resolvedBindingRef constructor) == globalBindingRefOwner reference)
            (invalid "a constructor resolves to a different source declaration")
        object <- case semanticGlobalBindingTarget (resolvedBindingDeclaration constructor) of
            GlobalReference object -> pure object
            _ -> invalid "a datatype constructor is not an ordinary object"
        domains <- for (datatypeCasePremises description) \case
            DatatypeRecursivePremise -> pure Datatype.Recursive
            DatatypeFixedPremise template -> Datatype.FixedDomain <$> instantiateParameters template
        pure (Datatype.Clause object (datatypeCaseFields description) domains)
    targets <- for clauses \clause ->
        either (throwProof . ProofStructuralCompositionFailed location) check
            (Datatype.predicateCaseBoundedTarget (length types) predicate carrier clause)
    children <- for (NonEmpty.zip descriptions targets) \(description, target) -> do
        let named = fromMaybe (impossible "validated induction case disappeared")
                (Map.lookup (datatypeCaseName description) sources)
        child <- prepareProofTree (Raw.namedCaseLocation named) caseContext caseLocals
            RecursiveProofInduction target (Raw.namedCaseProof named)
        pure (target, child)
    caseFacts <- traverse (allocateLocal ProofDerivedClaim context) targets
    let fingerprint = datatypeDescriptorPredicateInductionFact descriptor
    theorem <- liftDriver (Declaration.resolveVisibleFactLowering fingerprint)
        >>= maybe (invalid "the checked predicate-induction theorem is unavailable") pure
    parameterTerms <- traverse check parameters
    predicateTerm <- check predicate
    universal <- case predicate of
        CLam TySet body -> check (CForall TySet (CImp
            (member (CBound 0) (shiftCanonical 1 0 carrier)) body))
        _ -> impossible "structural induction did not abstract a predicate"
    let allLocals = aligned <> toList caseFacts
    proof <- prepareCheckedProofEnvironment (goal : toList targets) $ \foundation globalTyping -> do
        kernel <- KernelProof.scopedProofContext foundation globalTyping types
            (preparedLocalProposition <$> allLocals)
        law <- KernelProof.importedProof kernel (importIx 0) (checkedPropositionTerm theorem)
        specialized <- foldM (KernelProof.forallEliminationProof kernel) law (parameterTerms <> [predicateTerm])
        cases <- for (NonEmpty.zip clauses
                (length aligned :| [length aligned + 1 .. length allLocals - 1])) \(clause, index) ->
            Datatype.provePredicateCaseFromBounded kernel predicate carrier clause (hypothesisIx (fromIntegral index))
        conjunction <- foldM (KernelProof.conjunctionIntroductionProof kernel)
            (NonEmpty.head cases) (NonEmpty.tail cases)
        expected <- maybe (Left (KernelProof.ProofStructuralCompositionMismatch "induction case scope changed")) pure
            (implyScopedCore (KernelProof.builtProofStatement conjunction) universal)
        applicable <- KernelProof.conversionProof kernel specialized expected
        result <- KernelProof.implicationEliminationProof kernel applicable conjunction
        case selected of
            Nothing -> KernelProof.conversionProof kernel result goal
            Just index -> do
                argument <- Bifunctor.first KernelProof.ProofTermIllTyped (checkScopedCanonicalCore globalTyping types (CBound index))
                instanceProof <- KernelProof.forallEliminationProof kernel result argument
                membership <- Bifunctor.first KernelProof.ProofTermIllTyped (checkScopedCanonicalCore globalTyping types (member (CBound index) carrier))
                hypotheses <- traverse (KernelProof.indexedHypothesisProof kernel . hypothesisIx . fromIntegral)
                    [0 .. length aligned - 1]
                premise <- KernelProof.structuralLogicalProof kernel hypotheses membership
                    >>= maybe (Left KernelProof.ProofHypothesisNotFound) pure
                applied <- KernelProof.implicationEliminationProof kernel instanceProof premise
                KernelProof.conversionProof kernel applied goal
    built <- either (throwProof . ProofStructuralCompositionFailed location) pure proof
    let final = PreparedQed (PreparedKernelDischarge location (PreparedObviousReferences (fingerprint :| []))
            goal allLocals [fingerprint] (KernelProof.builtProofDerivation built))
    let cases = foldr (\(target, child) rest -> PreparedSubclaim target child rest) final children
    pure (foldr (\(residual, discharge) rest -> PreparedHave residual discharge rest) cases projections)
  where
    invalid :: Text -> Prepare value
    invalid = throwProof . ProofStructuralInductionInvalid location
    strip (SourceEvidence.SourceWithInputs _ body) = strip body
    strip body = body
    depends index term = index `Set.member` runIdentity (canonicalFreeIndicesWith (pure ()) term)
    member element set = CApp (CApp (CIntrinsic Member) element) set
    sourceMembership index source = do
        SourceEvidence.SourceAtom assertion <- pure (strip source)
        MembershipAtomTemplate element set <- pure (Notion.sourceAssertionAtom assertion)
        guard (scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore element) == CBound index)
        provider <- SourceTerm.sourceTermOccurrenceProvider set
        GlobalSourceProvider reference <- pure (SourceTerm.sourceTermProviderHead provider)
        pure (reference, scopedCoreTerm . SourceTerm.sourceTermOccurrenceCore <$>
            toList (SourceTerm.sourceTermProviderArguments provider),
            scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore set))

prepareByCase
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> [Raw.Case]
    -> Prepare PreparedProofTree
prepareByCase location context locals preparedGoal sourceCases = do
    cases <-
        maybe
            (throwProof (ProofEmptyCaseSplit location))
            (traverse prepareCase)
            (NonEmpty.nonEmpty sourceCases)
    exhaustive <-
        foldM disjoin
            (preparedCaseAssumption (NonEmpty.head cases))
            (preparedCaseAssumption <$> NonEmpty.tail cases)
    discharge <-
        case scopedCoreTerm exhaustive of
            COr proposition (CNot negated)
                | proposition == negated -> do
                    validateStructuralComposition
                        location
                        [exhaustive]
                        (\foundation globalType ->
                            KernelProof.validateExcludedMiddleComposition
                                foundation
                                globalType
                                exhaustive)
                    pure
                        (PreparedExcludedMiddle location exhaustive)
            _ -> do
                alignedLocals <- alignPreparedLocals context locals
                let justification =
                        if any
                            ((== exhaustive) . preparedLocalProposition)
                            alignedLocals
                            then PreparedAssumption
                            else PreparedInternalAuto
                preparePreparedDischarge
                    location context locals exhaustive Nothing justification
    validateStructuralComposition
        location
        (goal : exhaustive : (preparedCaseAssumption <$> toList cases))
        (\foundation globalType ->
            KernelProof.validateCaseAnalysisComposition
                foundation
                globalType
                goal
                (preparedCaseAssumption <$> cases)
                exhaustive)
    pure
        (PreparedByCase
            (PreparedCaseAnalysis goal cases exhaustive discharge))
  where
    prepareCase (Raw.Case statement child) = do
        elaborated <- prepareStatement context statement
        let assumption = Elaboration.elaboratedPropositionCore elaborated
        local <- allocateLocal ProofAssumption context assumption
        caseContext <-
            extendContextWithSourceLocal
                local
                (Elaboration.elaboratedPropositionEvidence elaborated)
                (Elaboration.elaboratedPropositionEqualities elaborated)
                context
        prepared <-
            prepareProofGoalTree
                (locate statement)
                caseContext
                (locals <> [local])
                RecursiveProofInduction
                preparedGoal
                child
        pure (PreparedCase assumption prepared)

    disjoin left right =
        maybe
            (structuralFailure
                location
                "case assumptions changed type or lexical context")
            pure
            (disjoinScopedCore left right)

    goal = preparedProofGoalCore preparedGoal

preparedCaseAssumption
    :: PreparedCase
    -> ScopedCheckedCore ObjectId
preparedCaseAssumption (PreparedCase assumption _proof) =
    assumption

preparedCaseProof :: PreparedCase -> PreparedProofTree
preparedCaseProof (PreparedCase _assumption proof) =
    proof

prepareFixBinders
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> NonEmpty Raw.FixBinder
    -> Maybe Raw.Stmt
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareFixBinders
        fallback location context locals goal binders condition continuation =
    go context locals goal (expandBoundedFixBinders binders)
  where
    expandBoundedFixBinders =
        concatMap \case
            Raw.FixBinderSymbolic variables bound@Raw.Bounded{} ->
                [ Raw.FixBinderSymbolic (variable :| []) bound
                | variable <- NonEmpty.toList variables
                ]
            binder ->
                [binder]

    go currentContext currentLocals currentGoal = \case
        [] ->
            case condition of
                Nothing ->
                    prepareProofTree
                        fallback
                        currentContext
                        currentLocals
                        RecursiveProofInduction
                        currentGoal
                        continuation
                Just statement -> do
                    constraint <- prepareStatement currentContext statement
                    prepareGuardedAssumption
                        location
                        currentContext currentLocals currentGoal constraint
                        (\context' conclusion locals' ->
                            prepareProofTree
                                fallback
                                context'
                                locals'
                                RecursiveProofInduction
                                conclusion
                                continuation)
        Raw.FixBinderSymbolic variables bound : remaining -> do
            (context', goal', identities) <-
                openFixedVariables Nothing currentContext currentGoal variables
            case bound of
                Raw.Unbounded ->
                    PreparedFix identities
                        <$> go context' currentLocals goal' remaining
                _ -> do
                    constraint <-
                        prepareSymbolicBoundConstraints
                            context' variables bound
                    prepareGuardedAssumption
                        location
                        context' currentLocals goal' constraint
                        (\guardedContext conclusion locals' ->
                            PreparedFix identities
                                <$> go guardedContext locals' conclusion remaining)
        Raw.FixBinderTyped variables concreteType : remaining -> do
            let binderType =
                    Elaboration.concreteTypeCoreType concreteType
            (context', goal', identities) <-
                openFixedVariables
                    (Just binderType)
                    currentContext currentGoal variables
            PreparedFix identities
                <$> go context' currentLocals goal' remaining

prepareGuardedAssumption
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Elaboration.ElaboratedProposition
    -> ( Elaboration.ElaborationContext
         -> ScopedCheckedCore ObjectId
         -> [PreparedLocal]
         -> Prepare PreparedProofTree
       )
    -> Prepare PreparedProofTree
prepareGuardedAssumption
        location context locals goal elaborated continue = do
    let constraint = Elaboration.elaboratedPropositionCore elaborated
    (antecedent, conclusion) <-
        maybe
            (throwProof
                (ProofExpectedImplicationGoal location (goalShape goal)))
            pure
            (openScopedImplication goal)
    unless (constraint == antecedent)
        (throwProof (ProofGoalStatementMismatch location))
    local <- allocateLocal ProofAssumption context constraint
    context' <-
        extendContextWithSourceLocal
            local
            (Elaboration.elaboratedPropositionEvidence elaborated)
            (Elaboration.elaboratedPropositionEqualities elaborated)
            context
    continue context' conclusion (locals <> [local])

prepareCalculation
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal]
    -> Maybe Raw.CalcQuantifier -> Raw.Calc
    -> Prepare (PreparedDischarge,Elaboration.ElaboratedProposition)
prepareCalculation location context locals quantifier calculation = do
    (identities,opened,calculationGuard) <- prepareCalculationScope context quantifier
    aligned <- alignPreparedLocals opened locals
    (calculationContext,calculationLocals,guardLocal) <- case calculationGuard of
        Nothing -> pure (opened,aligned,Nothing)
        Just proposition -> do
            local <- allocateLocal ProofAssumption opened (Elaboration.elaboratedPropositionCore proposition)
            guarded <- extendContextWithSourceLocal local (Elaboration.elaboratedPropositionEvidence proposition)
                (Elaboration.elaboratedPropositionEqualities proposition) opened
            pure (guarded,aligned <> [local],Just local)
    (openDischarge,result) <- State.evalStateT (case calculation of
        Raw.RelationCalculation first links -> do
            checked <- calculationElaboration (\work -> Elaboration.elaborateRelationCalculation work calculationContext first links)
            finishCalculation location calculationContext calculationLocals
                (zipCalculationSources checked (relationSource <$> links))
        Raw.Biconditionals first destinations -> do
            initial <- endpoint calculationContext first
            applications <- biconditionals calculationContext initial destinations
            finishCalculation location calculationContext calculationLocals applications) Calculation.defaultCalculationWork
    closed <- closeCalculationDischarge location identities guardLocal openDischarge
    pure (closed,Elaboration.closeCalculationProposition (preparedDischargeGoal closed) (length identities) calculationGuard result)
  where
    endpoint current formula = State.lift (Elaboration.elaboratedPropositionCore <$> prepareStatement current (Raw.StmtFormula formula))
    relationSource (Raw.CalcRelationLink _ relation destination justification) =
        CalculationSource (locate destination) (locate relation) justification
    biconditionals current left ((destination,justification) :| rest) = do
        right <- endpoint current destination
        application <- calculationElaboration (\work -> Elaboration.equalityCalculationApplication work (locate destination) current left right)
        later <- case NonEmpty.nonEmpty rest of
            Nothing -> pure []
            Just remaining -> toList <$> biconditionals current right remaining
        pure ((application,CalculationSource (locate destination) (locate destination) justification) :| later)

data CalculationSource = CalculationSource !Location !Location !Raw.Justification

zipCalculationSources
    :: NonEmpty Elaboration.CheckedCalculationApplication -> NonEmpty CalculationSource
    -> NonEmpty (Elaboration.CheckedCalculationApplication,CalculationSource)
zipCalculationSources applications sources
    | NonEmpty.length applications == NonEmpty.length sources = NonEmpty.zip applications sources
    | otherwise = impossible "calculation lowering changed the number of displayed links"

prepareCalculationScope
    :: Elaboration.ElaborationContext -> Maybe Raw.CalcQuantifier
    -> Prepare ([Elaboration.LocalId],Elaboration.ElaborationContext,Maybe Elaboration.ElaboratedProposition)
prepareCalculationScope context Nothing = pure ([],context,Nothing)
prepareCalculationScope context (Just (Raw.CalcQuantifier variables bound suchThat)) = do
    identities <- traverse (const allocateLocalIdentity) variables
    opened <- either (throwProof . ProofElaborationFailed) pure
        (Elaboration.extendElaborationContext (NonEmpty.zip identities variables) context)
    proposition <- liftDriver (Elaboration.elaborateCalculationGuard opened variables bound suchThat)
        >>= either (throwProof . ProofElaborationFailed) pure
    let condition = if scopedCoreTerm (Elaboration.elaboratedPropositionCore proposition) == CTruth
            then Nothing else Just proposition
    pure (toList identities,opened,condition)

-- One account spans lowering, every candidate scan, and all folds. Notion
-- conditions retain their own existing bounded search account.
type CalculationPrepare = State.StateT Word Prepare

calculationPure :: Location -> Calculation.CalculationWork Identity value -> CalculationPrepare value
calculationPure location action = do
    allowance <- State.get
    let (result,remaining) = runIdentity (Calculation.runCalculationWork allowance action)
    State.put remaining
    either (State.lift . throwProof . ProofCalculationFailed location) pure result

calculationElaboration
    :: (Word -> Declaration.LoweringDriver (Either Elaboration.ElaborationError (value,Word)))
    -> CalculationPrepare value
calculationElaboration operation = do
    allowance <- State.get
    (value,remaining) <- State.lift (liftDriver (operation allowance)
        >>= either (throwProof . ProofElaborationFailed) pure)
    State.put remaining
    pure value

finishCalculation
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal]
    -> NonEmpty (Elaboration.CheckedCalculationApplication,CalculationSource)
    -> CalculationPrepare (PreparedDischarge,Elaboration.ElaboratedProposition)
finishCalculation fallback context locals ((firstApplication,firstSource) :| remaining) = do
    firstDischarge <- link firstApplication firstSource
    (result,discharge) <- foldM compose (firstApplication,firstDischarge) remaining
    pure (discharge,Elaboration.calculationProposition result)
  where
    link application (CalculationSource destinationLocation _ justification) = State.lift $
        prepareProofGoalDischarge InlineObviousInference
            (if destinationLocation == Nowhere then fallback else destinationLocation) context locals
            (sourcePreparedProofGoal (Elaboration.calculationOpenProposition application)
                (Elaboration.elaboratedPropositionEvidence (Elaboration.calculationProposition application))) justification
    compose (previous,previousDischarge) (next,source@(CalculationSource _ location _)) = do
        nextDischarge <- link next source
        aligned <- calculationPure location (Calculation.calculationCoreWork (\work -> countedScopedCoreIdentity work
            (Elaboration.calculationRight previous) (Elaboration.calculationLeft next)))
        unless aligned (impossible "a calculation lost its shared middle endpoint")
        let leftEquality = Calculation.relatorIsEquality (Elaboration.calculationRelator previous)
            rightEquality = Calculation.relatorIsEquality (Elaboration.calculationRelator next)
        (result,facts,conditions,arguments) <- if leftEquality || rightEquality then do
            let template = if leftEquality then next else previous
            transported <- calculationElaboration (\work -> Elaboration.transportCalculationApplication work location context template
                (Elaboration.calculationLeftSource previous) (Elaboration.calculationRightSource next))
            pure (transported,[],[],[])
          else do
            registry <- State.lift (liftDriver Declaration.compositionRegistryLowering)
            found <- calculationPure location (Calculation.selectCompositionLaws registry
                (Elaboration.calculationRelator previous) (Elaboration.calculationRelator next))
            case found of
                [] -> State.lift (throwProof (ProofCalculationCompositionMissing location
                    (Calculation.relatorCore (Elaboration.calculationRelator previous))
                    (Calculation.relatorCore (Elaboration.calculationRelator next))))
                [(fingerprint,law,bindings)] -> do
                    (application,guards,actuals) <- calculationElaboration (\work ->
                        Elaboration.instantiateCompositionApplication work location context law bindings previous next)
                    pure (application,[fingerprint],guards,actuals)
                matches -> State.lift (throwProof (ProofCalculationCompositionAmbiguous location
                    (Calculation.relatorCore (Elaboration.calculationRelator previous))
                    (Calculation.relatorCore (Elaboration.calculationRelator next))
                    (fromMaybe (impossible "ambiguous composition list became empty")
                        (NonEmpty.nonEmpty [fingerprint | (fingerprint,_,_) <- matches]))))
        let (group,paths) = balancedConditions conditions
        conditionDischarge <- traverse (\proposition -> State.lift (Except.catchError
            (prepareNotionDischarge location context locals
                (sourcePreparedProofGoal (Elaboration.elaboratedPropositionCore proposition)
                    (Elaboration.elaboratedPropositionEvidence proposition)))
            (\case
                ProofNotionUnavailable _ failure
                    | Just path <- Elaboration.notionQueryFailurePath failure
                    , Just ordinal <- List.findIndex (`pathPrefix` path) paths
                    , [fingerprint] <- facts
                    , condition:_ <- drop ordinal conditions ->
                        throwProof (ProofCalculationConditionUnavailable location fingerprint (fromIntegral ordinal + 1)
                            (Elaboration.elaboratedPropositionCore condition) failure)
                failure -> throwProof failure))) group
        let children = previousDischarge :| (nextDischarge : maybeToList conditionDischarge)
        derivation <- prepareCalculationComposition location previous next result facts arguments paths
            (preparedDischargeGoal <$> toList children)
        pure (result,PreparedKernelComposition location (Elaboration.calculationOpenProposition result) facts children derivation)

pathPrefix :: ConjunctionPath -> ConjunctionPath -> Bool
pathPrefix ConjunctionHere _ = True
pathPrefix (ConjunctionLeft a) (ConjunctionLeft b) = pathPrefix a b
pathPrefix (ConjunctionRight a) (ConjunctionRight b) = pathPrefix a b
pathPrefix _ _ = False

balancedConditions :: [Elaboration.ElaboratedProposition] -> (Maybe Elaboration.ElaboratedProposition,[ConjunctionPath])
balancedConditions [] = (Nothing,[])
balancedConditions values = let (proposition,paths) = build (Vector.fromList values) in (Just proposition,paths)
  where
    build terms | Vector.length terms == 1 = (Vector.head terms,[ConjunctionHere])
                | otherwise =
        let (left,right) = Vector.splitAt (Vector.length terms `div` 2) terms
            (a,as) = build left
            (b,bs) = build right
        in (Elaboration.conjoinElaboratedPropositions a b, (ConjunctionLeft <$> as) <> (ConjunctionRight <$> bs))

prepareCalculationComposition
    :: Location -> Elaboration.CheckedCalculationApplication -> Elaboration.CheckedCalculationApplication
    -> Elaboration.CheckedCalculationApplication -> [SemanticFactOccurrenceFingerprint]
    -> [ScopedCheckedCore ObjectId] -> [ConjunctionPath] -> [ScopedCheckedCore ObjectId]
    -> CalculationPrepare (KernelDerivation ObjectId)
prepareCalculationComposition location previous next composed directFacts arguments paths children = do
    fact <- case directFacts of
        [] -> pure Nothing
        [fingerprint] -> do
            selected <- State.lift (liftDriver (Declaration.resolveVisibleFactLowering fingerprint))
            Just . checkedPropositionTerm <$> maybe (impossible "a selected composition is not visible") pure selected
        _ -> impossible "a composition selected several laws"
    let target = Elaboration.calculationOpenProposition composed
    foundation <- State.lift (liftDriver Declaration.currentFoundationLowering)
    globalType <- State.lift prepareGlobalTyping
    equalityMotive <- case fact of
        Just _ -> pure Nothing
        Nothing | Calculation.relatorIsEquality (Elaboration.calculationRelator previous) ->
            Just <$> motive (Elaboration.calculationRelator next) True (Elaboration.calculationRight next)
        Nothing -> Just <$> motive (Elaboration.calculationRelator previous) False (Elaboration.calculationLeft previous)
    calculationPure location (Calculation.calculationCoreWork (\work -> KernelProof.runSharedProofWork work do
        context <- KernelProof.countedScopedProofContext foundation globalType (scopedCoreContext target) children
        a <- KernelProof.countedIndexedHypothesisProof context (hypothesisIx 0)
        b <- KernelProof.countedIndexedHypothesisProof context (hypothesisIx 1)
        proof <- case fact of
            Nothing -> equalityComposition equalityMotive context a b
            Just theorem -> do
                imported <- KernelProof.countedImportedProof context (importIx 0) theorem
                specialized <- foldM (KernelProof.countedForallEliminationProof context) imported arguments
                guarded <- if null paths then pure specialized else do
                    group <- KernelProof.countedIndexedHypothesisProof context (hypothesisIx 2)
                    foldM (\current path -> project context path group >>= apply context current) specialized paths
                pair <- KernelProof.countedConjunctionIntroductionProof a b
                apply context guarded pair
        KernelProof.builtProofDerivation <$> KernelProof.countedConversionProof context proof target))
  where
    apply context theorem premise = do
        let (expected,_) = fromMaybe (impossible "a checked composition lost an implication")
                (openScopedImplication (KernelProof.builtProofStatement theorem))
        converted <- KernelProof.countedConversionProof context premise expected
        KernelProof.countedImplicationEliminationProof context theorem converted
    project context path proof = case path of
        ConjunctionHere -> pure proof
        ConjunctionLeft rest -> KernelProof.countedProjectConjunctionProof True context proof >>= project context rest
        ConjunctionRight rest -> KernelProof.countedProjectConjunctionProof False context proof >>= project context rest
    equalityComposition preparedMotive context a b
        | Calculation.relatorIsEquality (Elaboration.calculationRelator previous) = do
            equation <- equality context previous a
            reversed <- KernelProof.countedEqualityReverseProof context equation
            predicate <- KernelProof.countedScopedTerm context (fromMaybe (impossible "equality transport has no motive") preparedMotive)
            KernelProof.countedEqualityTransportProof context reversed predicate b
        | otherwise = do
            equation <- equality context next b
            predicate <- KernelProof.countedScopedTerm context (fromMaybe (impossible "equality transport has no motive") preparedMotive)
            KernelProof.countedEqualityTransportProof context equation predicate a
    equality context application proof = do
        let expected = fromMaybe (impossible "equality endpoint types changed")
                (equalScopedCore (Elaboration.calculationLeft application) (Elaboration.calculationRight application))
        KernelProof.countedConversionProof context proof expected
    motive relation replaceLeft fixed = do
        let (leftType,rightType) = Calculation.relatorEndpointTypes relation
            ty = if replaceLeft then leftType else rightType
        predicate <- scopedCoreTerm <$> calculationPure location (Calculation.calculationCoreWork (\work ->
            countedWeakenCheckedScopedCore work ty (Calculation.relatorCore relation)))
        operand <- scopedCoreTerm <$> calculationPure location (Calculation.calculationCoreWork (\work ->
            countedWeakenCheckedScopedCore work ty fixed))
        let body = if replaceLeft then CApp (CApp predicate (CBound 0)) operand
                else CApp (CApp predicate operand) (CBound 0)
        pure (CLam ty body)

closeCalculationDischarge
    :: Location
    -> [Elaboration.LocalId]
    -> Maybe PreparedLocal
    -> PreparedDischarge
    -> Prepare PreparedDischarge
closeCalculationDischarge location identities calculationGuard discharge = do
    guarded <- case calculationGuard of
        Nothing -> pure discharge
        Just local -> do
            let premise = preparedLocalProposition local
            target <- maybe (impossible "a calculation guard changed context") pure
                (implyScopedCore premise (preparedDischargeGoal discharge))
            pure (PreparedImplicationDischarge location target local discharge)
    foldM closeBinder guarded (reverse identities)
  where
    closeBinder child identity = do
        let body = preparedDischargeGoal child
        target <- maybe (impossible "a calculation lost a quantified binder") pure
            (closeScopedForall body)
        case scopedCoreContext body of
            binderType : _ -> pure (PreparedUniversalDischarge location target binderType identity child)
            [] -> impossible "a calculation binder has an empty context"

-- The two conjunction children are the complete external hypothesis vector.
conjunctionDerivation :: KernelDerivation ObjectId
conjunctionDerivation =
    conjunctionIntroductionDerivation
        (localHypothesisDerivation (hypothesisIx 0))
        (localHypothesisDerivation (hypothesisIx 1))

preparedDischargeGoal
    :: PreparedDischarge
    -> ScopedCheckedCore ObjectId
preparedDischargeGoal = \case
    PreparedDefinitionDischarge child -> preparedDischargeGoal child
    PreparedRecursiveEquation _ application _ _ -> Recursive.applicationEquality application
    PreparedPreparationLimit _statistics discharge -> preparedDischargeGoal discharge
    PreparedFormationDischarge _completion discharge -> preparedDischargeGoal discharge
    PreparedEqualityDischarge _location goal _local _equation _child -> goal
    PreparedEvidenceDischarge _location goal _local _evidence _child -> goal
    PreparedUniversalDischarge _location goal _type _identity _child -> goal
    PreparedImplicationDischarge _location goal _premise _child -> goal
    PreparedVampireDischarge _location _justification goal _obligation ->
        goal
    PreparedExcludedMiddle _location goal ->
        goal
    PreparedKernelDischarge _location _method goal _locals _facts _derivation ->
        goal
    PreparedKernelComposition _location goal _facts _children _derivation ->
        goal

prepareSymbolicBoundConstraints
    :: Elaboration.ElaborationContext
    -> NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Prepare Elaboration.ElaboratedProposition
prepareSymbolicBoundConstraints context variables bound =
    liftDriver
            (Elaboration.elaborateSymbolicBoundConstraints
                context variables bound)
        >>= either
            (throwProof . ProofElaborationFailed)
            pure

prepareSymbolicTake
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> NonEmpty Raw.VarSymbol
    -> Raw.Bound
    -> Raw.Stmt
    -> Raw.Justification
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareSymbolicTake
        fallback location context locals goal variables bound statement
        justification continuation = do
    identities <- traverse (const allocateLocalIdentity) variables
    context' <-
        either
            (throwProof . ProofElaborationFailed)
            pure
            (Elaboration.extendElaborationContext
                (NonEmpty.zip identities variables)
                context)
    elaborated <-
        liftDriver
                (Elaboration.elaborateSymbolicWitnessConstraints
                    context' variables bound statement)
            >>= either
                (throwProof . ProofElaborationFailed)
                pure
    prepareTake
        fallback location context locals goal context'
        (toList identities)
        (replicate (length (toList identities)) TySet)
        (Elaboration.elaboratedPropositionCore elaborated)
        (Elaboration.elaboratedPropositionEvidence elaborated)
        (Elaboration.elaboratedPropositionEqualities elaborated)
        justification continuation

prepareTypedTake
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> NonEmpty Raw.VarSymbol
    -> CoreType
    -> Raw.Stmt
    -> Raw.Justification
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareTypedTake
        fallback location context locals goal variables binderType statement
        justification continuation = do
    identities <- traverse (const allocateLocalIdentity) variables
    context' <-
        either
            (throwProof . ProofElaborationFailed)
            pure
            (Elaboration.extendTypedElaborationContext
                ((\(identity, variable) ->
                    (identity, variable, binderType))
                    <$> NonEmpty.zip identities variables)
                context)
    elaborated <- prepareStatement context' statement
    prepareTake
        fallback location context locals goal context'
        (toList identities)
        (replicate (length (toList identities)) binderType)
        (Elaboration.elaboratedPropositionCore elaborated)
        (Elaboration.elaboratedPropositionEvidence elaborated)
        (Elaboration.elaboratedPropositionEqualities elaborated)
        justification continuation

prepareNounTake
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Raw.NounPhrase []
    -> Raw.Justification
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareNounTake
        fallback location context locals goal nounPhrase
        justification continuation = do
    (identities, context') <-
        case nounPhrase of
            Raw.NounPhrase _left _noun (Raw.NounBinder variables _bound) _right _suchThat ->
                case NonEmpty.nonEmpty variables of
                    Just binders -> do
                        identities <-
                            traverse (const allocateLocalIdentity) binders
                        context' <-
                            either
                                (throwProof . ProofElaborationFailed)
                                pure
                                (Elaboration.extendElaborationContext
                                    (NonEmpty.zip identities binders)
                                    context)
                        pure (toList identities, context')
                    Nothing -> do
                        identity <- allocateLocalIdentity
                        context' <-
                            either
                                (throwProof . ProofElaborationFailed)
                                pure
                                (Elaboration.extendAnonymousElaborationContext
                                    identity context)
                        pure ([identity], context')
    elaborated <-
        liftDriver
                (Elaboration.elaborateNounWitnessConstraints
                    context context' nounPhrase)
            >>= either
                (throwProof . ProofElaborationFailed)
                pure
    prepareTake
        fallback location context locals goal context'
        identities
        (replicate (length identities) TySet)
        (Elaboration.elaboratedPropositionCore elaborated)
        (Elaboration.elaboratedPropositionEvidence elaborated)
        (Elaboration.elaboratedPropositionEqualities elaborated)
        justification continuation

prepareTake
    :: Location
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Elaboration.ElaborationContext
    -> [Elaboration.LocalId]
    -> [CoreType]
    -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence
    -> [Elaboration.ScopedSourceEqualityOccurrence]
    -> Raw.Justification
    -> Raw.Proof
    -> Prepare PreparedProofTree
prepareTake
        fallback location context locals goal witnessContext
        identities witnessTypes witness assertions equalities
        justification continuation = do
    let witnessCount = length identities
        existence = closeTakenWitnesses witnessCount witness
        goal' = weakenForTakenWitnesses witnessTypes goal
    discharge <-
        prepareDischarge
            InlineObviousInference
            location context locals existence justification
    local <- allocateLocal ProofAssumption witnessContext witness
    continuationContext <-
        extendContextWithSourceLocal
            local assertions equalities witnessContext
    PreparedTake identities witness discharge
        <$> prepareProofTree
            fallback
            continuationContext
            (locals <> [local])
            RecursiveProofInduction
            goal'
            continuation

-- The discharged existential and the opened witness premise are the same
-- checked proposition viewed on opposite sides of existential elimination.
closeTakenWitnesses
    :: Int
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
closeTakenWitnesses binderCount = go binderCount
  where
    go 0 proposition = proposition
    go remaining proposition =
        go (remaining - 1)
            (fromMaybe
                (impossible "a taken witness has no checked binder")
                (closeScopedExists proposition))

weakenForTakenWitnesses
    :: [CoreType]
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
weakenForTakenWitnesses binderTypes proposition =
    foldl'
        (flip weakenCheckedScopedCore)
        proposition
        binderTypes

openFixedVariables
    :: Maybe CoreType
    -> Elaboration.ElaborationContext
    -> ScopedCheckedCore ObjectId
    -> NonEmpty Raw.VarSymbol
    -> Prepare
        ( Elaboration.ElaborationContext
        , ScopedCheckedCore ObjectId
        , [Elaboration.LocalId]
        )
openFixedVariables expectedType initialContext initialGoal variables =
    foldM openOne
        (initialContext, initialGoal, [])
        (toList variables)
  where
    openOne (context, goal, identities) variable = do
        (binderType, body) <-
            maybe
                (throwProof
                    (ProofExpectedUniversalGoal
                        (locate variable)
                        (goalShape goal)))
                pure
                (openScopedForall goal)
        traverse_
            (\expected ->
                unless (binderType == expected)
                    (throwProof
                        (ProofExpectedUniversalGoal
                            (locate variable)
                            (goalShape goal))))
            expectedType
        identity <- allocateLocalIdentity
        context' <-
            either
                (throwProof . ProofElaborationFailed)
                pure
                (Elaboration.extendTypedElaborationContext
                    ((identity, variable, binderType) :| [])
                    context)
        pure (context', body, identities <> [identity])

allocateLocalIdentity :: Prepare Elaboration.LocalId
allocateLocalIdentity = do
    state <- State.get
    State.put
        state
            { prepareNextLocal = prepareNextLocal state + 1
            }
    pure (Elaboration.localId (prepareNextLocal state))

allocateLocal
    :: ProofLocalOrigin
    -> Elaboration.ElaborationContext
    -> ScopedCheckedCore ObjectId
    -> Prepare PreparedLocal
allocateLocal origin context proposition = do
    state <- State.get
    State.put
        state
            { prepareNextPremise = prepareNextPremise state + 1
            }
    pure
        (PreparedLocal
            (Backend.localPremiseOrdinal
                (prepareNextPremise state))
            origin
            (Elaboration.elaborationContextSupport context)
            proposition)

extendContextWithSourceLocal
    :: PreparedLocal
    -> SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence
    -> [Elaboration.ScopedSourceEqualityOccurrence]
    -> Elaboration.ElaborationContext
    -> Prepare Elaboration.ElaborationContext
extendContextWithSourceLocal
        (PreparedLocal ordinal origin support proposition)
        assertions
        equalities
        context = do
    rebasedAssertions <-
        either
            (\failure ->
                impossible
                    ("a source local could not retain notion assertions: "
                        <> Text.unpack failure))
            pure
            (Elaboration.rebaseEvidenceOntoLocal proposition assertions)
    rebasedEqualities <-
        either
            (\failure ->
                impossible
                    ("a source local could not retain equalities: "
                        <> Text.unpack failure))
            pure
            (Elaboration.rebaseEqualitiesOntoLocal proposition equalities)
    withNotions <- liftDriver (Elaboration.finishFormationScopePreparation (Elaboration.prepareFormationPremiseSource
        (Elaboration.formationEvidenceSource
            support
            proposition
            rebasedAssertions
            (Backend.localPremiseOrdinalValue ordinal)
            (formationProofLocalKind origin))
        context)) >>= either
            (throwProof . ProofElaborationFailed . Elaboration.ElaborationFormationScopeFailed Nowhere) pure
    case NonEmpty.nonEmpty rebasedEqualities of
        Nothing -> pure withNotions
        Just nonempty ->
            liftDriver (Elaboration.finishFormationScopePreparation (Elaboration.prepareFormationEqualitySource
                (Elaboration.formationEqualitySource
                    support
                    proposition
                    nonempty
                    (Backend.localPremiseOrdinalValue ordinal)
                    (formationProofLocalKind origin))
                withNotions)) >>= either
                    (throwProof . ProofElaborationFailed . Elaboration.ElaborationFormationScopeFailed Nowhere) pure

formationProofLocalKind
    :: ProofLocalOrigin
    -> Elaboration.FormationProofLocalKind
formationProofLocalKind = \case
    ProofAssumption -> Elaboration.FormationProofAssumption
    ProofDerivedClaim -> Elaboration.FormationProofDerivedClaim
    ProofLocalDefinition -> Elaboration.FormationProofLocalDefinition
    ProofLocalConstructionExtensional ->
        Elaboration.FormationProofLocalConstructionExtensional
    ProofLocalConstructionEquation ->
        Elaboration.FormationProofLocalConstructionEquation

extendContextWithLocalAlias
    :: Location
    -> Elaboration.LocalId
    -> Elaboration.ScopedSourceTerm
    -> PreparedLocal
    -> Elaboration.ElaborationContext
    -> Prepare Elaboration.ElaborationContext
extendContextWithLocalAlias location identity source
        (PreparedLocal ordinal _origin _support equality) context = do
    extended <- liftDriver (Elaboration.extendElaborationContextWithFormationAliasLowering
        identity source equality (Backend.localPremiseOrdinalValue ordinal) location context)
        >>= either (impossible . ("a generated local alias is invalid: " <>) . Text.unpack) pure
    pure (fromMaybe context extended)

prepareConstructionFoundation
    :: Prepare SetConstructionFoundation
prepareConstructionFoundation = do
    familyUnion <- foundation FamilyUnionCharacteristic
    separation <- foundation SeparationCharacteristic
    replacement <- foundation ReplacementCharacteristic
    pure
        (setConstructionFoundation
            familyUnion separation replacement)
  where
    foundation tag =
        liftDriver
            (Declaration.currentFoundationAxiomLowering tag)

prepareDischarge
    :: ObviousInvocationSite
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Raw.Justification
    -> Prepare PreparedDischarge
prepareDischarge site location context locals goal justification = do
    prepareProofGoalDischarge
        site location context locals (plainPreparedProofGoal goal) justification

prepareProofGoalDischarge
    :: ObviousInvocationSite
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> Raw.Justification
    -> Prepare PreparedDischarge
prepareProofGoalDischarge
        site location context locals preparedGoal justification =
    case justification of
        Raw.JustificationNotion ->
            prepareNotionDischarge location context locals preparedGoal
        _ -> prepareOrdinary
  where
    goal = preparedProofGoalCore preparedGoal
    prepareOrdinary = do
        environment <- Reader.ask
        prepareDischargeWith
            (proofModeForGoal goal
                (prepareProofMode environment))
            (prepareFoundationAuxiliaries environment)
            Nothing site location context locals preparedGoal justification

prepareNotionDischarge
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> Prepare PreparedDischarge
prepareNotionDischarge location context locals
        (PreparedProofGoal goal evidence) = do
    (outcome, completion) <-
        liftDriver
            (Elaboration.prepareProofNotionEvidence
                context location goal evidence)
            >>= either
                (throwProof . ProofElaborationFailed)
                pure
    (discharge, completed) <- continueFormationCompletion completion do
        materialized <- case outcome of
            Elaboration.NotionQueryFound found -> pure found
            Elaboration.NotionQueryUnsupported -> throwProof (ProofNotionGoalUnsupported location)
            Elaboration.NotionQueryUnavailable failure ->
                throwProof (ProofNotionUnavailable location failure)
        materializeNotionDischarge location context locals goal materialized
    pure (PreparedFormationDischarge completed discharge)

materializeNotionDischarge
    :: Location -> Elaboration.ElaborationContext -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Notion.MaterializedFormationEvidence Elaboration.FormationSourceOrigin
    -> Prepare PreparedDischarge
materializeNotionDischarge location context locals goal materialized = do
    let selectedHypotheses =
            toList (Notion.materializedFormationHypotheses materialized)
        localIndex = Map.fromList
            [ (Backend.localPremiseOrdinalValue ordinal, local)
            | local@(PreparedLocal ordinal _origin _support _proposition) <- locals
            ]
    unless (Map.size localIndex == length locals)
        invalidEvidence
    selectedLocals <- for selectedHypotheses \hypothesis ->
        case Notion.materializedNotionHypothesisOrigin hypothesis of
            Elaboration.FormationFromProofLocal ordinal expectedKind -> do
                local@(PreparedLocal _ordinal origin _support _proposition) <-
                    maybe
                        invalidEvidence
                        pure
                        (Map.lookup ordinal localIndex)
                unless (formationProofLocalKind origin == expectedKind)
                    invalidEvidence
                pure local
            Elaboration.FormationFromDefinitionHeader{} ->
                invalidEvidence
            Elaboration.FormationFromCheckedGuard{} ->
                invalidEvidence
            Elaboration.FormationFromPhraseCore{} ->
                invalidEvidence
            Elaboration.FormationFromGoalAssumption{} ->
                invalidEvidence
    alignedLocals <- alignPreparedLocals context selectedLocals
    let fingerprints = Notion.materializedFormationImports materialized
    imports <- for fingerprints \fingerprint -> do
        proposition <-
            liftDriver (Declaration.resolveVisibleFactLowering fingerprint)
                >>= maybe
                    (throwProof
                        (ProofNotionFormationFailed location
                            (Notion.FormationProofKernelError
                                (KernelProof.ProofStructuralCompositionMismatch
                                    ("selected notion fact is no longer visible: "
                                        <> Text.pack (show fingerprint))))))
                    pure
        either
            (\(DerivationImportIsNotProposition coreType) ->
                throwProof (ProofNotionFormationFailed location
                    (Notion.FormationProofKernelError
                        (KernelProof.ProofSemanticsFailed
                            (KernelSemantics.KernelExpectedProposition coreType)))))
            pure
            (derivationImportJudgement (checkedPropositionTerm proposition))
    foundation <- liftDriver Declaration.currentFoundationLowering
    globalTyping <- prepareGlobalTyping
    proofContext <-
        either
            (throwProof . ProofNotionFormationFailed location
                . Notion.FormationProofKernelError)
            pure
            (KernelProof.scopedProofContext foundation globalTyping
                (scopedCoreContext goal) (preparedLocalProposition <$> alignedLocals))
    built <- liftDriver (Declaration.materializeFormationProofLowering proofContext materialized imports)
        >>= either (throwProof . ProofNotionFormationFailed location) pure
    unless (KernelProof.builtProofStatement built == goal)
        (throwProof (ProofNotionFormationTargetMismatch location))
    pure
        (PreparedKernelDischarge
            location
            PreparedNotion
            goal
            alignedLocals
            (toList fingerprints)
            (KernelProof.builtProofDerivation built))
  where
    invalidEvidence :: Prepare value
    invalidEvidence =
        throwProof (ProofNotionFormationFailed location Notion.FormationProofInvalidRecipe)

-- Scope rollback still belongs to proof preparation. Its physical measurement
-- survives an ordinary preparation error and closes at that failing owner.
continueFormationCompletion
    :: FormationDiagnostics.Completion -> Prepare value
    -> Prepare (value, FormationDiagnostics.Completion)
continueFormationCompletion completion action = Reader.ReaderT $ \environment ->
    State.StateT $ \initial -> Except.ExceptT do
        recorder <- Declaration.formationRecorderLowering
        result <- FormationDiagnostics.continueCompletion recorder completion
            (Except.runExceptT (State.runStateT (Reader.runReaderT action environment) initial))
        pure (fmap (\((value, final), completed) -> ((value, completed), final)) result)

preparePreparedDischarge
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> Maybe ObviousInvocation
    -> PreparedJustification
    -> Prepare PreparedDischarge
preparePreparedDischarge
        location context locals goal invocation justification = do
    environment <- Reader.ask
    preparePreparedDischargeWith
        (proofModeForGoal goal
            (prepareProofMode environment))
        (prepareFoundationAuxiliaries environment)
        Nothing invocation location context locals (plainPreparedProofGoal goal) justification

-- Entering a falsum goal starts an indirect proof scope.  A proof chain whose
-- closing rule is explicit contradiction also starts that scope at the
-- beginning of the chain, so intermediate claims in an impossible case may
-- use its contradictory premises.  Once entered, the scope is inherited by
-- every nested proof and discharge until the prepared subtree returns.
proofModeForGoal
    :: ScopedCheckedCore ObjectId
    -> ProofMode
    -> ProofMode
proofModeForGoal goal = \case
    ContradictionProof ->
        ContradictionProof
    DirectProof
        | scopedCoreType goal == TyProp
        , scopedCoreTerm goal == CFalsum ->
            ContradictionProof
        | otherwise ->
            DirectProof

proofModeForProof
    :: ScopedCheckedCore ObjectId
    -> Raw.Proof
    -> ProofMode
    -> ProofMode
proofModeForProof goal proof mode =
    case proofModeForGoal goal mode of
        ContradictionProof ->
            ContradictionProof
        DirectProof
            | proofChainEndsInContradiction proof ->
                ContradictionProof
            | otherwise ->
                DirectProof

proofChainEndsInContradiction :: Raw.Proof -> Bool
proofChainEndsInContradiction = \case
    Raw.ByStructuralInduction{} -> False
    Raw.Contradiction{} -> True
    Raw.ByContradiction{} -> True
    Raw.BySetInduction _location _focus continuation ->
        proofChainEndsInContradiction continuation
    Raw.ByOrdInduction _location continuation ->
        proofChainEndsInContradiction continuation
    Raw.Assume _location _intro _statement continuation ->
        proofChainEndsInContradiction continuation
    Raw.Fix _location _binders _condition continuation ->
        proofChainEndsInContradiction continuation
    Raw.Calc _location _quantifier _calculation continuation ->
        proofChainEndsInContradiction continuation
    Raw.TakeVar
            _location _variables _bound _statement _justification
            continuation ->
        proofChainEndsInContradiction continuation
    Raw.TakeTyped
            _location _variables _coreType _statement _justification
            continuation ->
        proofChainEndsInContradiction continuation
    Raw.TakeNoun _location _nounPhrase _justification continuation ->
        proofChainEndsInContradiction continuation
    Raw.Have _location _intro _statement _justification continuation ->
        proofChainEndsInContradiction continuation
    Raw.Since
            _premiseLocation _premise _premiseJustification
            _claimLocation _claim _claimJustification continuation ->
        proofChainEndsInContradiction continuation
    Raw.Suffices _location _statement _justification continuation ->
        proofChainEndsInContradiction continuation
    Raw.Subclaim _location _statement _subproof continuation ->
        proofChainEndsInContradiction continuation
    Raw.Define _location _variable _expression continuation ->
        proofChainEndsInContradiction continuation
    Raw.DefineTyped
            _location _variable _coreType _expression continuation ->
        proofChainEndsInContradiction continuation
    Raw.DefineFunction
            _location _function _argument _value _bound _domain
            continuation ->
        proofChainEndsInContradiction continuation
    Raw.DefineFunctionLocal
            _location _function _argument _value _bound _target _rules
            continuation ->
        proofChainEndsInContradiction continuation
    Raw.Omitted{} -> False
    Raw.Qed{} -> False
    Raw.ByCase{} -> False

prepareDischargeWith
    :: ProofMode
    -> [FoundationAxiomTag]
    -> Maybe Declaration.VampirePremisePolicy
    -> ObviousInvocationSite
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> Raw.Justification
    -> Prepare PreparedDischarge
prepareDischargeWith
        proofMode auxiliaries selectionOverride
        site location context locals preparedGoal justification =
    case justification of
        Raw.JustificationSetExt -> do
            alignedLocals <- alignPreparedLocals context locals
            let evidence = buildExactEvidenceView alignedLocals
            prepareSetExtensionality location goal evidence
                >>= either
                    (throwProof . renderSetExtensionalityFailure location)
                    pure
        Raw.JustificationStructureExt -> do
            alignedLocals <- alignPreparedLocals context locals
            let evidence = buildExactEvidenceView alignedLocals
            prepareExactRecordExtensionality
                location context alignedLocals goal evidence
                >>= either
                    (throwProof . renderRecordExtensionalityFailure location)
                    pure
        Raw.JustificationExtensionality -> do
            alignedLocals <- alignPreparedLocals context locals
            let evidence = buildExactEvidenceView alignedLocals
            recordResult <-
                prepareExactRecordExtensionality
                    location context alignedLocals goal evidence
            case recordResult of
                Right discharge -> pure discharge
                Left recordFailure -> do
                    setResult <- prepareSetExtensionality location goal evidence
                    case setResult of
                        Right discharge -> pure discharge
                        Left setFailure ->
                            throwProof
                                (case recordFailure of
                                    RecordExtensionalityFieldUnavailable{} ->
                                        renderRecordExtensionalityFailure
                                            location recordFailure
                                    _ ->
                                        renderSetExtensionalityFailure
                                            location setFailure)
        _ -> do
            (preparedJustification, invocation) <-
                prepareJustification site location justification
            preparePreparedDischargeWith
                proofMode auxiliaries selectionOverride
                invocation location context locals preparedGoal preparedJustification

  where
    goal = preparedProofGoalCore preparedGoal

data SetExtensionalityFailure
    = SetExtensionalityGoalMismatch
    | SetExtensionalityLeftToRightUnavailable
    | SetExtensionalityRightToLeftUnavailable

data SameOrientation
    = SameGoalOrder
    | SameReverseGoalOrder

data SetDirection
    = SetLeftToRight
    | SetRightToLeft

data DefinitionExposureStep = DefinitionExposureStep
    !SemanticFactOccurrenceFingerprint
    ![CanonicalTerm ObjectId]

data SetEvidencePlan = SetEvidencePlan
    !EvidenceRow
    ![DefinitionExposureStep]

data SetObservationMatch
    = SetDirectionMatch !SetDirection
    | SetSameMatch !SameOrientation

data SetObservationPlan
    = SetObservationDirections !SetEvidencePlan !SetEvidencePlan
    | SetObservationSame !SameOrientation !SetEvidencePlan

renderSetExtensionalityFailure
    :: Location
    -> SetExtensionalityFailure
    -> ProofError
renderSetExtensionalityFailure location = \case
    SetExtensionalityGoalMismatch ->
        ProofSetExtensionalityGoalMismatch location
    SetExtensionalityLeftToRightUnavailable ->
        ProofSetExtensionalityLeftToRightUnavailable location
    SetExtensionalityRightToLeftUnavailable ->
        ProofSetExtensionalityRightToLeftUnavailable location

prepareSetExtensionality
    :: Location
    -> ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Prepare (Either SetExtensionalityFailure PreparedDischarge)
prepareSetExtensionality location goal evidence =
    case setEqualityObservations goal of
        Nothing -> pure (Left SetExtensionalityGoalMismatch)
        Just (leftToRight, rightToLeft, same, sameReversed) -> do
            let leftRow = exactEvidenceRow leftToRight evidence
                rightRow = exactEvidenceRow rightToLeft evidence
                exactPlan =
                    SetObservationDirections
                        <$> (literalSetEvidencePlan <$> leftRow)
                        <*> (literalSetEvidencePlan <$> rightRow)
                literalSamePlan =
                    firstLiteralSame same sameReversed evidence
            case exactPlan <|> literalSamePlan of
                Just plan ->
                    Right <$> buildSetExtensionality
                        leftToRight rightToLeft plan
                Nothing -> do
                    exposedSamePlan <-
                        firstExposedSame
                            location same sameReversed evidence
                    case exposedSamePlan of
                        Just plan ->
                            Right <$> buildSetExtensionality
                                leftToRight rightToLeft plan
                        Nothing -> do
                            leftPlan <-
                                case leftRow of
                                    Just row ->
                                        pure
                                            (Just (literalSetEvidencePlan row))
                                    Nothing ->
                                        firstExposedDirection
                                            location SetLeftToRight
                                            leftToRight evidence
                            case leftPlan of
                                Nothing ->
                                    pure
                                        (Left
                                            SetExtensionalityLeftToRightUnavailable)
                                Just selectedLeft -> do
                                    rightPlan <-
                                        case rightRow of
                                            Just row ->
                                                pure
                                                    (Just
                                                        (literalSetEvidencePlan
                                                            row))
                                            Nothing ->
                                                firstExposedDirection
                                                    location SetRightToLeft
                                                    rightToLeft evidence
                                    case rightPlan of
                                        Nothing ->
                                            pure
                                                (Left
                                                    SetExtensionalityRightToLeftUnavailable)
                                        Just selectedRight ->
                                            Right <$> buildSetExtensionality
                                                leftToRight rightToLeft
                                                (SetObservationDirections
                                                    selectedLeft selectedRight)
  where
    buildSetExtensionality leftToRight rightToLeft plan = do
        let selectedEvidencePlans =
                case plan of
                    SetObservationDirections leftPlan rightPlan ->
                        [leftPlan, rightPlan]
                    SetObservationSame _orientation samePlan ->
                        [samePlan]
            selectedRows = setEvidencePlanSeed <$> selectedEvidencePlans
            selectedLocals = compactEvidenceLocals selectedRows
            hypotheses = preparedLocalProposition <$> selectedLocals
            hypothesisIndices = Map.fromList
                [ ( preparedLocalOrdinalValue local
                  , hypothesisIx (fromIntegral index)
                  )
                | (index, local) <- zip [0 :: Int ..] selectedLocals
                ]
            fingerprints =
                stableDefinitionExposureFingerprints selectedEvidencePlans
        importedFacts <-
            traverse resolveDefinitionExposureFact fingerprints
        let importedPropositions =
                embedClosedCore (scopedCoreContext goal)
                    . checkedPropositionTerm . snd
                    <$> importedFacts
            importedFactMap = Map.fromList
                [ (fingerprint, (importIx (fromIntegral index), proposition))
                | (index, (fingerprint, proposition)) <-
                    zip [0 :: Int ..] importedFacts
                ]
        result <-
            prepareCheckedProofEnvironment
                (goal : hypotheses <> importedPropositions)
                (\foundation globalType -> do
                    context <-
                        KernelProof.scopedProofContext
                            foundation
                            globalType
                            (scopedCoreContext goal)
                            hypotheses
                    (left, right) <-
                        case scopedCoreTerm goal of
                            CEq TySet leftTerm rightTerm ->
                                pure (leftTerm, rightTerm)
                            _ ->
                                Left
                                    (KernelProof.ProofStructuralCompositionMismatch
                                        "set extensionality lost its checked equality goal")
                    checkedLeft <- KernelProof.scopedTerm context left
                    checkedRight <- KernelProof.scopedTerm context right
                    (leftProof, rightProof) <-
                        case plan of
                            SetObservationDirections leftPlan rightPlan ->
                                (,)
                                    <$> setEvidenceProof
                                        context hypothesisIndices
                                        importedFactMap [] leftPlan
                                    <*> setEvidenceProof
                                        context hypothesisIndices
                                        importedFactMap [] rightPlan
                            SetObservationSame orientation samePlan ->
                                (,)
                                    <$> pointwiseSameDirectionProof
                                        context hypothesisIndices importedFactMap
                                        orientation SetLeftToRight
                                        leftToRight samePlan
                                    <*> pointwiseSameDirectionProof
                                        context hypothesisIndices importedFactMap
                                        orientation SetRightToLeft
                                        rightToLeft samePlan
                    extensionality <-
                        KernelProof.foundationInstanceProof
                            context SetExtensionality
                            [checkedLeft, checkedRight]
                    afterLeft <-
                        KernelProof.implicationEliminationProof
                            context extensionality leftProof
                    completed <-
                        KernelProof.implicationEliminationProof
                            context afterLeft rightProof
                    unless
                        (KernelProof.builtProofStatement completed == goal)
                        (Left
                            (KernelProof.ProofStructuralCompositionMismatch
                                "set extensionality produced a different goal"))
                    pure completed)
        proof <- either
            (throwProof . ProofStructuralCompositionFailed location)
            pure
            result
        pure
            (PreparedKernelDischarge
                location
                PreparedSetExtensionality
                goal
                selectedLocals
                fingerprints
                (KernelProof.builtProofDerivation proof))

    resolveDefinitionExposureFact fingerprint = do
        proposition <-
            liftDriver (Declaration.resolveVisibleFactLowering fingerprint)
        maybe
            (structuralFailure location
                "a planned pointwise definition view became unavailable")
            (\available -> pure (fingerprint, available))
            proposition

setEqualityObservations
    :: ScopedCheckedCore ObjectId
    -> Maybe
        ( ScopedCheckedCore ObjectId
        , ScopedCheckedCore ObjectId
        , ScopedCheckedCore ObjectId
        , ScopedCheckedCore ObjectId
        )
setEqualityObservations goal = do
    (leftToRight, rightToLeft) <- splitScopedSetEquality goal
    (leftMember, rightMember) <- pointwiseMembers leftToRight
    same <- equalScopedCore leftMember rightMember >>= closeScopedForall
    sameReversed <-
        equalScopedCore rightMember leftMember >>= closeScopedForall
    pure (leftToRight, rightToLeft, same, sameReversed)
  where
    pointwiseMembers direction = do
        (TySet, body) <- openScopedForall direction
        openScopedImplication body

firstLiteralSame
    :: ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Maybe SetObservationPlan
firstLiteralSame same sameReversed (ExactEvidenceView rows _buckets) =
    firstMatch rows
  where
    firstMatch = \case
        [] -> Nothing
        row@(EvidenceRow _local proposition _path) : remaining
            | proposition == same ->
                Just
                    (SetObservationSame
                        SameGoalOrder (literalSetEvidencePlan row))
            | proposition == sameReversed ->
                Just
                    (SetObservationSame
                        SameReverseGoalOrder (literalSetEvidencePlan row))
            | otherwise -> firstMatch remaining

literalSetEvidencePlan :: EvidenceRow -> SetEvidencePlan
literalSetEvidencePlan row = SetEvidencePlan row []

setEvidencePlanSeed :: SetEvidencePlan -> EvidenceRow
setEvidencePlanSeed (SetEvidencePlan seed _steps) = seed

firstExposedSame
    :: Location
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Prepare (Maybe SetObservationPlan)
firstExposedSame location same sameReversed evidence =
    fmap toPlan
        <$> firstExposedObservation
            location
            [ (SetSameMatch SameGoalOrder, same)
            , (SetSameMatch SameReverseGoalOrder, sameReversed)
            ]
            evidence
  where
    toPlan (SetSameMatch orientation, plan) =
        SetObservationSame orientation plan
    toPlan (SetDirectionMatch _direction, _plan) =
        impossible "same set observation matched a membership direction"

firstExposedDirection
    :: Location
    -> SetDirection
    -> ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Prepare (Maybe SetEvidencePlan)
firstExposedDirection location direction expected evidence =
    fmap toPlan
        <$> firstExposedObservation
            location
            [(SetDirectionMatch direction, expected)]
            evidence
  where
    toPlan (SetDirectionMatch matched, plan)
        | sameDirection matched direction = plan
    toPlan _ =
        impossible "set direction observation matched a different target"

    sameDirection SetLeftToRight SetLeftToRight = True
    sameDirection SetRightToLeft SetRightToLeft = True
    sameDirection _ _ = False

firstExposedObservation
    :: Location
    -> [(SetObservationMatch, ScopedCheckedCore ObjectId)]
    -> ExactEvidenceView
    -> Prepare (Maybe (SetObservationMatch, SetEvidencePlan))
firstExposedObservation location expected
        (ExactEvidenceView rows _buckets) =
    firstMatch rows
  where
    firstMatch = \case
        [] -> pure Nothing
        row : remaining -> do
            exposed <- exposeEvidenceRow location expected row
            case exposed of
                Just (_observation, SetEvidencePlan _seed (_step : _steps)) ->
                    pure exposed
                _ -> firstMatch remaining

-- Follow only the declaration-sealed pointwise view of the current atomic
-- proposition.  A missing view is an ordinary non-match; once a view exists,
-- failure to specialize its checked equality is an integrity error.
exposeEvidenceRow
    :: Location
    -> [(SetObservationMatch, ScopedCheckedCore ObjectId)]
    -> EvidenceRow
    -> Prepare (Maybe (SetObservationMatch, SetEvidencePlan))
exposeEvidenceRow location expected seed@(EvidenceRow _local initial _path) =
    go [] initial
  where
    go reversedSteps current =
        case List.find ((== current) . snd) expected of
            Just (observation, _target) ->
                pure
                    (Just
                        ( observation
                        , SetEvidencePlan seed (reverse reversedSteps)
                        ))
            Nothing ->
                case canonicalApplicationSpine (scopedCoreTerm current) of
                    (CGlobal object, arguments) -> do
                        views <-
                            liftDriver
                                (Declaration.resolveVisibleDefinitionViewsLowering
                                    object)
                        case List.find
                                ((== DefinitionPointwiseView)
                                    . Declaration.resolvedDefinitionViewKind)
                                views of
                            Nothing -> pure Nothing
                            Just view -> do
                                next <- specializePointwiseDefinitionView
                                    location current arguments view
                                go
                                    ( DefinitionExposureStep
                                        (Declaration.resolvedDefinitionViewFingerprint
                                            view)
                                        arguments
                                      : reversedSteps
                                    )
                                    next
                    _ -> pure Nothing

specializePointwiseDefinitionView
    :: Location
    -> ScopedCheckedCore ObjectId
    -> [CanonicalTerm ObjectId]
    -> Declaration.ResolvedDefinitionView
    -> Prepare (ScopedCheckedCore ObjectId)
specializePointwiseDefinitionView location current arguments view = do
    let viewInContext =
            embedClosedCore
                (scopedCoreContext current)
                (checkedPropositionTerm
                    (Declaration.resolvedDefinitionViewProposition view))
    result <-
        prepareCheckedProofEnvironment
            [current, viewInContext]
            (\_foundation globalType -> do
                checkedArguments <-
                    traverse
                        (Bifunctor.first KernelProof.ProofTermIllTyped
                            . checkScopedCanonicalCore
                                globalType (scopedCoreContext current))
                        arguments
                specialized <-
                    foldM
                        (\proposition argument ->
                            Bifunctor.first KernelProof.ProofSemanticsFailed
                                (KernelSemantics.forallElimination
                                    proposition argument))
                        viewInContext
                        checkedArguments
                case scopedCoreTerm specialized of
                    CEq TyProp left right
                        | left == scopedCoreTerm current -> do
                            checkedRight <-
                                Bifunctor.first KernelProof.ProofTermIllTyped
                                    (checkScopedCanonicalCore
                                        globalType
                                        (scopedCoreContext current)
                                        right)
                            if scopedCoreType checkedRight == TyProp
                                then pure checkedRight
                                else
                                    Left
                                        (KernelProof.ProofStructuralCompositionMismatch
                                            "a pointwise definition view produced a non-proposition")
                    _ ->
                        Left
                            (KernelProof.ProofStructuralCompositionMismatch
                                "a pointwise definition view did not expose its current proposition"))
    either
        (throwProof . ProofStructuralCompositionFailed location)
        pure
        result

stableDefinitionExposureFingerprints
    :: [SetEvidencePlan]
    -> [SemanticFactOccurrenceFingerprint]
stableDefinitionExposureFingerprints plans =
    reverse reversed
  where
    (_seen, reversed) =
        foldl' add (Set.empty, [])
            [ fingerprint
            | SetEvidencePlan _seed steps <- plans
            , DefinitionExposureStep fingerprint _arguments <- steps
            ]

    add (seen, accumulated) fingerprint
        | fingerprint `Set.member` seen = (seen, accumulated)
        | otherwise =
            (Set.insert fingerprint seen, fingerprint : accumulated)

setEvidenceProof
    :: KernelProof.ProofContext ObjectId
    -> Map Natural HypothesisIx
    -> Map
        SemanticFactOccurrenceFingerprint
        (ImportIx, CheckedPropositionContent)
    -> [CoreType]
    -> SetEvidencePlan
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
setEvidenceProof context hypothesisIndices importedFacts binderTypes
        (SetEvidencePlan seed steps) = do
    initial <-
        exactEvidenceProof
            context hypothesisIndices
            (foldl' (flip weakenEvidenceRow) seed binderTypes)
    foldM expose initial steps
  where
    binderDepth = fromIntegral (length binderTypes)

    expose current (DefinitionExposureStep fingerprint arguments) = do
        (index, proposition) <-
            maybe
                (Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "a planned pointwise definition import was not resolved"))
                pure
                (Map.lookup fingerprint importedFacts)
        theorem <-
            KernelProof.importedProof
                context index (checkedPropositionTerm proposition)
        specialized <-
            KernelProof.specializeForalls context theorem
                (shiftCanonical binderDepth 0 <$> arguments)
        case scopedCoreTerm (KernelProof.builtProofStatement specialized) of
            CEq TyProp left _right
                | left == scopedCoreTerm
                    (KernelProof.builtProofStatement current) ->
                    KernelProof.equalityModusPonensProof
                        context specialized current
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "a pointwise definition replay did not expose its current proposition")

pointwiseSameDirectionProof
    :: KernelProof.ProofContext ObjectId
    -> Map Natural HypothesisIx
    -> Map
        SemanticFactOccurrenceFingerprint
        (ImportIx, CheckedPropositionContent)
    -> SameOrientation
    -> SetDirection
    -> ScopedCheckedCore ObjectId
    -> SetEvidencePlan
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
pointwiseSameDirectionProof
        context hypothesisIndices importedFacts
        orientation direction expected evidencePlan = do
    directionProof <-
        KernelProof.forallIntroductionProof context TySet
            (\elementContext element -> do
                equivalence <-
                    setEvidenceProof
                        elementContext hypothesisIndices importedFacts
                        [TySet] evidencePlan
                specialized <-
                    KernelProof.forallEliminationProof
                        elementContext equivalence element
                oriented <-
                    if reverseEquality orientation direction
                        then KernelProof.equalityReverseProof
                            elementContext specialized
                        else pure specialized
                premise <-
                    case scopedCoreTerm
                            (KernelProof.builtProofStatement oriented) of
                        CEq TyProp premiseTerm _conclusionTerm ->
                            KernelProof.scopedTerm
                                elementContext premiseTerm
                        _ ->
                            Left
                                (KernelProof.ProofStructuralCompositionMismatch
                                    "pointwise set equivalence did not specialize to a propositional equality")
                KernelProof.implicationIntroductionProof
                    elementContext premise
                    (\premiseContext premiseProof ->
                        KernelProof.equalityModusPonensProof
                            premiseContext
                            (KernelProof.weakenProofHypotheses 1 oriented)
                            premiseProof))
    unless
        (KernelProof.builtProofStatement directionProof == expected)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "pointwise set equivalence produced the wrong membership direction"))
    pure directionProof
  where
    reverseEquality sameOrientation setDirection =
        case (sameOrientation, setDirection) of
            (SameGoalOrder, SetLeftToRight) -> False
            (SameGoalOrder, SetRightToLeft) -> True
            (SameReverseGoalOrder, SetLeftToRight) -> True
            (SameReverseGoalOrder, SetRightToLeft) -> False

weakenEvidenceRow :: CoreType -> EvidenceRow -> EvidenceRow
weakenEvidenceRow binderType
        (EvidenceRow local proposition path) =
    EvidenceRow
        local
        (weakenCheckedScopedCore binderType proposition)
        path

data RecordExtensionalityFailure
    = RecordExtensionalityGoalMismatch
    | RecordExtensionalityLeftShapeUnavailable
    | RecordExtensionalityRightShapeUnavailable
    | RecordExtensionalityCommonShapeUnavailable
    | RecordExtensionalityFieldUnavailable !Raw.StructSymbol

renderRecordExtensionalityFailure
    :: Location
    -> RecordExtensionalityFailure
    -> ProofError
renderRecordExtensionalityFailure location = \case
    RecordExtensionalityGoalMismatch ->
        ProofRecordExtensionalityGoalMismatch location
    RecordExtensionalityLeftShapeUnavailable ->
        ProofRecordExtensionalityLeftShapeUnavailable location
    RecordExtensionalityRightShapeUnavailable ->
        ProofRecordExtensionalityRightShapeUnavailable location
    RecordExtensionalityCommonShapeUnavailable ->
        ProofRecordExtensionalityCommonShapeUnavailable location
    RecordExtensionalityFieldUnavailable field ->
        ProofRecordExtensionalityFieldUnavailable location field

data CompleteRecordExtensionality = CompleteRecordExtensionality
    !Declaration.ResolvedRecordShape
    !NormalizedEvidenceRow
    !NormalizedEvidenceRow
    ![( Declaration.ResolvedRecordShapeField
        , ScopedCheckedCore ObjectId
        , NormalizedEvidenceRow
        )]

prepareExactRecordExtensionality
    :: Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Prepare (Either RecordExtensionalityFailure PreparedDischarge)
prepareExactRecordExtensionality
        location elaborationContext activeLocals goal evidence = do
    let aliases = Elaboration.alignFormationAliases elaborationContext
    normalizedGoal <-
        normalizeOrThrow aliases goal
    normalizedEvidence <-
        either
            (throwIntegrity . recordAliasReplacementIntegrity)
            pure
            (normalizeExactEvidenceView aliases evidence)
    case scopedCoreTerm
            (Elaboration.formationAliasNormalizationResult normalizedGoal) of
        CEq TySet left right ->
            prepareForOperands normalizedGoal normalizedEvidence left right
        _ -> pure (Left RecordExtensionalityGoalMismatch)
  where
    prepareForOperands goalNormalization normalizedView left right = do
        let leftShapes = recognizedShapes left normalizedView
            rightShapes = recognizedShapes right normalizedView
        if Map.null leftShapes
            then pure (Left RecordExtensionalityLeftShapeUnavailable)
            else if Map.null rightShapes
                then pure (Left RecordExtensionalityRightShapeUnavailable)
                else do
                    candidates <- fmap concat
                        (for
                            (Map.toAscList
                                (Map.intersectionWith (,)
                                    leftShapes rightShapes))
                            (\(selectors, (leftRow, rightRow)) -> do
                                shapes <- liftDriver
                                    (Declaration.resolveVisibleRecordShapesLowering
                                        selectors)
                                pure
                                    [ (shape, leftRow, rightRow)
                                    | shape <- shapes
                                    ]))
                    selectComplete goalNormalization normalizedView left right
                        (List.sortOn
                            (Declaration.resolvedRecordShapeKey
                                . firstOfThree)
                            candidates)
                        Nothing

    firstOfThree (firstValue, _secondValue, _thirdValue) = firstValue

    selectComplete _goalNormalization _normalizedView
            _left _right [] Nothing =
        pure (Left RecordExtensionalityCommonShapeUnavailable)
    selectComplete _goalNormalization _normalizedView
            _left _right [] (Just failure) =
        pure (Left failure)
    selectComplete goalNormalization normalizedView left right
            ((shape, leftRow, rightRow) : remaining) firstFailure = do
        assessed <-
            assessShape normalizedView left right shape leftRow rightRow
        case assessed of
            Left failure ->
                selectComplete
                    goalNormalization normalizedView left right remaining
                    (firstFailure <|> Just failure)
            Right complete ->
                Right <$>
                    buildRecordExtensionality
                        goalNormalization left right complete

    assessShape normalizedView left right shape leftRow rightRow = do
        let fields = Declaration.resolvedRecordShapeFields shape
            terms = fieldEquality left right <$> fields
        globalTyping <- prepareGlobalTyping
        checked <- traverse
            (checkStructureTerm
                location globalTyping (scopedCoreContext goal))
            terms
        unless (all ((== TyProp) . scopedCoreType) checked)
            (throwProof (ProofStructureMetadataMismatch location))
        let selected =
                zipWith
                    (\field proposition ->
                        (field, proposition,
                            normalizedExactEvidenceRow
                                proposition normalizedView))
                    fields
                    checked
        case
            [ Declaration.resolvedRecordShapeFieldSymbol field
            | (field, _proposition, Nothing) <- toList selected
            ] of
            missing : _ ->
                pure (Left (RecordExtensionalityFieldUnavailable missing))
            [] ->
                pure
                    (Right
                        (CompleteRecordExtensionality
                            shape leftRow rightRow
                            (fmap
                                (\(field, proposition, maybeRow) ->
                                    ( field
                                    , proposition
                                    , fromMaybe
                                        (impossible
                                            "complete record evidence lost a field row")
                                        maybeRow
                                    ))
                                selected)))

    fieldEquality left right field =
        let projection =
                CGlobal
                    (Declaration.resolvedRecordShapeFieldProjection field)
        in CEq TySet
            (CApp projection left)
            (CApp projection right)

    buildRecordExtensionality normalizedGoal left right
            (CompleteRecordExtensionality
                shape leftShapeRow rightShapeRow fieldEvidence) = do
        let fields = Declaration.resolvedRecordShapeFields shape
            theoremTerm =
                Record.recordSchemaProjectionExtensionalityLaw
                    [ ( CGlobal
                            (Declaration.resolvedRecordShapeFieldSelector field)
                      , CGlobal
                            (Declaration.resolvedRecordShapeFieldProjection field)
                      )
                    | field <- toList fields
                    ]
        target <-
            liftDriver
                (Declaration.checkStructureProjectionLawTargetLowering
                    theoremTerm)
                >>= either
                    (throwIntegrity
                        . RecordExtensionalityProjectionLawIntegrity)
                    pure
        fingerprint <-
            liftDriver
                (Declaration.resolveStructureProjectionLawLowering shape target)
                >>= either
                    (throwIntegrity
                        . RecordExtensionalityProjectionLawIntegrity)
                    pure
        selectedProposition <-
            liftDriver (Declaration.resolveVisibleFactLowering fingerprint)
        unless
            ( maybe False
                ((== target) . checkedPropositionTerm)
                selectedProposition
            )
            (throwIntegrity
                (RecordExtensionalityProjectionLawIntegrity
                    (Declaration.StructureProjectionGeneratedLawUnavailable
                        target)))
        let fieldRows =
                (\(_field, _proposition, row) -> row) <$> fieldEvidence
            selectedNormalizedRows =
                leftShapeRow : rightShapeRow : toList fieldRows
            selectedRows =
                normalizedEvidenceRowOriginal <$> selectedNormalizedRows
            usedNormalizations =
                normalizedGoal
                    : (normalizedEvidenceRowNormalization
                        <$> selectedNormalizedRows)
        definitionLocals <-
            either throwIntegrity pure
                (reconcileFormationAliasDefinitions
                    activeLocals usedNormalizations)
        let selectedLocals =
                mergeSelectedLocals
                    (compactEvidenceLocals selectedRows)
                    definitionLocals
            hypotheses = preparedLocalProposition <$> selectedLocals
            hypothesisIndices = Map.fromList
                [ ( preparedLocalOrdinalValue local
                  , hypothesisIx (fromIntegral index)
                  )
                | (index, local) <- zip [0 :: Int ..] selectedLocals
                ]
            targetInContext =
                embedClosedCore (scopedCoreContext goal) target
            normalizedGoalProposition =
                Elaboration.formationAliasNormalizationResult normalizedGoal
            replayPredicates =
                [ Elaboration.formationAliasReplayStepAbstraction step
                | normalization <- usedNormalizations
                , step <-
                    Elaboration.formationAliasNormalizationReplaySteps
                        normalization
                ]
        result <-
            prepareCheckedProofEnvironment
                ( goal
                    : normalizedGoalProposition
                    : targetInContext
                    : replayPredicates <> hypotheses
                )
                (\foundation globalType -> do
                    proofContext <- structural
                        (KernelProof.scopedProofContext
                            foundation globalType
                            (scopedCoreContext goal) hypotheses)
                    checkedLeft <- structural
                        (KernelProof.scopedTerm proofContext left)
                    checkedRight <- structural
                        (KernelProof.scopedTerm proofContext right)
                    theorem <-
                        structural
                            (KernelProof.importedProof
                                proofContext (importIx 0) target)
                    atLeft <-
                        structural
                            (KernelProof.forallEliminationProof
                                proofContext theorem checkedLeft)
                    specialized <-
                        structural
                            (KernelProof.forallEliminationProof
                                proofContext atLeft checkedRight)
                    leftShape <-
                        normalizedEvidenceProof
                            proofContext hypothesisIndices leftShapeRow
                    rightShape <-
                        normalizedEvidenceProof
                            proofContext hypothesisIndices rightShapeRow
                    fieldProofs <- traverse
                        (normalizedEvidenceProof
                            proofContext hypothesisIndices)
                        fieldRows
                    fieldConjunction <-
                        structural
                            (KernelProof.buildLeftAssociatedConjunction
                                proofContext (toList fieldProofs))
                    afterLeft <-
                        structural
                            (KernelProof.implicationEliminationProof
                                proofContext specialized leftShape)
                    afterRight <-
                        structural
                            (KernelProof.implicationEliminationProof
                                proofContext afterLeft rightShape)
                    completed <-
                        structural
                            (KernelProof.implicationEliminationProof
                                proofContext afterRight fieldConjunction)
                    unless
                        (KernelProof.builtProofStatement completed
                            == normalizedGoalProposition)
                        (Left
                            (RecordExtensionalityProofStructural
                                (KernelProof.ProofStructuralCompositionMismatch
                                    "record extensionality produced a different normalized goal")))
                    replayNormalization
                        proofContext hypothesisIndices
                        ReplayFormationAliasesReverse
                        normalizedGoal completed)
        proof <- case result of
            Left (RecordExtensionalityProofStructural failure) ->
                throwProof
                    (ProofStructuralCompositionFailed location failure)
            Left (RecordExtensionalityProofIntegrity failure) ->
                throwIntegrity failure
            Right value -> pure value
        pure
            (PreparedKernelDischarge
                location
                PreparedRecordExtensionality
                goal
                selectedLocals
                [fingerprint]
                (KernelProof.builtProofDerivation proof))

    normalizeOrThrow aliases proposition =
        either
            (throwIntegrity . recordAliasReplacementIntegrity)
            pure
            (Elaboration.normalizeFormationAliases aliases proposition)

    normalizedEvidenceProof proofContext hypothesisIndices row = do
        initial <- structural
            (exactEvidenceProof
                proofContext hypothesisIndices
                (normalizedEvidenceRowOriginal row))
        Bifunctor.first RecordExtensionalityProofIntegrity
            (replayFormationAliasNormalization
                proofContext hypothesisIndices
                ReplayFormationAliasesForward
                (normalizedEvidenceRowNormalization row)
                initial)

    replayNormalization
            proofContext hypothesisIndices direction normalization initial =
        Bifunctor.first RecordExtensionalityProofIntegrity
            (replayFormationAliasNormalization
                proofContext hypothesisIndices direction normalization initial)

    structural =
        Bifunctor.first RecordExtensionalityProofStructural

    throwIntegrity
        :: RecordExtensionalityIntegrityError
        -> Prepare value
    throwIntegrity failure =
        throwProof
            (ProofRecordExtensionalityIntegrityFailure location failure)

recognizedShapes
    :: CanonicalTerm ObjectId
    -> NormalizedExactEvidenceView
    -> Map [ObjectId] NormalizedEvidenceRow
recognizedShapes subject (NormalizedExactEvidenceView rows _buckets) =
    foldl' retain Map.empty rows
  where
    retain found row =
        case Record.recognizeRecordExactGlobalShape
                (normalizedEvidenceRowProposition row) of
            Just (actual, selectors)
                | actual == subject ->
                    Map.insertWith (\_new old -> old) selectors row found
            _ -> found

normalizeExactEvidenceView
    :: Elaboration.AlignedFormationAliases
    -> ExactEvidenceView
    -> Either
        Elaboration.FormationAliasNormalizationError
        NormalizedExactEvidenceView
normalizeExactEvidenceView aliases (ExactEvidenceView rows _buckets) = do
    (reversedRows, buckets) <- foldM retain ([], Map.empty) rows
    pure (NormalizedExactEvidenceView (reverse reversedRows) buckets)
  where
    retain (reversedRows, buckets) row@(EvidenceRow _local proposition _path)
        | relevantOuterForm proposition = do
            normalization <-
                Elaboration.normalizeFormationAliases aliases proposition
            let normalizedRow = NormalizedEvidenceRow row normalization
                normalizedProposition =
                    Elaboration.formationAliasNormalizationResult
                        normalization
            pure
                ( normalizedRow : reversedRows
                , Map.alter
                    (Just
                        . maybe
                            (normalizedRow :| [])
                            (<> (normalizedRow :| [])))
                    normalizedProposition
                    buckets
                )
        | otherwise = pure (reversedRows, buckets)

    relevantOuterForm proposition =
        isJust (Record.recognizeRecordExactGlobalShape proposition)
            || case scopedCoreTerm proposition of
                CEq TySet _left _right -> True
                _ -> False

normalizedExactEvidenceRow
    :: ScopedCheckedCore ObjectId
    -> NormalizedExactEvidenceView
    -> Maybe NormalizedEvidenceRow
normalizedExactEvidenceRow proposition
        (NormalizedExactEvidenceView _rows buckets) =
    NonEmpty.head <$> Map.lookup proposition buckets

normalizedEvidenceRowOriginal
    :: NormalizedEvidenceRow
    -> EvidenceRow
normalizedEvidenceRowOriginal
        (NormalizedEvidenceRow row _normalization) =
    row

normalizedEvidenceRowNormalization
    :: NormalizedEvidenceRow
    -> Elaboration.FormationAliasNormalization
normalizedEvidenceRowNormalization
        (NormalizedEvidenceRow _row normalization) =
    normalization

normalizedEvidenceRowProposition
    :: NormalizedEvidenceRow
    -> ScopedCheckedCore ObjectId
normalizedEvidenceRowProposition =
    Elaboration.formationAliasNormalizationResult
        . normalizedEvidenceRowNormalization

recordAliasReplacementIntegrity
    :: Elaboration.FormationAliasNormalizationError
    -> RecordExtensionalityIntegrityError
recordAliasReplacementIntegrity = \case
    Elaboration.FormationAliasReplacementInvariantFailed
            aliasLocation ordinal failure ->
        RecordExtensionalityAliasNormalizationIntegrity
            aliasLocation ordinal
            (FormationAliasCheckedReplacementFailed failure)

reconcileFormationAliasDefinitions
    :: [PreparedLocal]
    -> [Elaboration.FormationAliasNormalization]
    -> Either RecordExtensionalityIntegrityError [PreparedLocal]
reconcileFormationAliasDefinitions activeLocals normalizations = do
    unless
        (Map.size activeByOrdinal == length activeLocals)
        (impossible "active proof locals have duplicate premise ordinals")
    Map.elems <$> foldM reconcile Map.empty replaySteps
  where
    activeByOrdinal = Map.fromList
        [ (preparedLocalOrdinalValue local, local)
        | local <- activeLocals
        ]
    replaySteps =
        [ step
        | normalization <- normalizations
        , step <-
            Elaboration.formationAliasNormalizationReplaySteps normalization
        ]

    reconcile selected step = do
        let ordinal = Elaboration.formationAliasReplayStepOrdinal step
            aliasLocation =
                Elaboration.formationAliasReplayStepLocation step
            definition =
                Elaboration.formationAliasReplayStepDefinition step
            retainedOrigin =
                Notion.materializedNotionHypothesisOrigin definition
            mismatch =
                RecordExtensionalityActiveDefinitionMismatch
                    aliasLocation ordinal
        case retainedOrigin of
            Elaboration.FormationFromProofLocal
                    retainedOrdinal
                    Elaboration.FormationProofLocalDefinition
                | retainedOrdinal == ordinal -> pure ()
            _ ->
                Left
                    (mismatch
                        (ActiveDefinitionRetainedOriginMismatch
                            retainedOrigin))
        local@(PreparedLocal _localOrdinal origin _support proposition) <-
            maybe
                (Left (mismatch ActiveDefinitionMissing))
                pure
                (Map.lookup ordinal activeByOrdinal)
        unless
            (origin == ProofLocalDefinition)
            (Left
                (mismatch
                    (ActiveDefinitionLocalOriginMismatch origin)))
        unless
            ( proposition
                == Notion.materializedNotionHypothesisProposition definition
            )
            (Left (mismatch ActiveDefinitionPropositionMismatch))
        pure (Map.insert ordinal local selected)

mergeSelectedLocals
    :: [PreparedLocal]
    -> [PreparedLocal]
    -> [PreparedLocal]
mergeSelectedLocals evidenceLocals definitionLocals =
    Map.elems
        (Map.fromList
            [ (preparedLocalOrdinalValue local, local)
            | local <- evidenceLocals <> definitionLocals
            ])

replayFormationAliasNormalization
    :: KernelProof.ProofContext ObjectId
    -> Map Natural HypothesisIx
    -> FormationAliasReplayDirection
    -> Elaboration.FormationAliasNormalization
    -> KernelProof.BuiltProof ObjectId
    -> Either
        RecordExtensionalityIntegrityError
        (KernelProof.BuiltProof ObjectId)
replayFormationAliasNormalization
        proofContext hypothesisIndices direction normalization initial = do
    replayed <- foldM replayStep initial orderedSteps
    case NonEmpty.nonEmpty steps of
        Nothing -> do
            unless
                (KernelProof.builtProofStatement replayed == expectedResult)
                (impossible
                    "identity alias normalization changed its checked proposition")
            pure replayed
        Just nonempty ->
            Bifunctor.first
                (\failure ->
                    aliasReplayIntegrity
                        (case direction of
                            ReplayFormationAliasesForward ->
                                NonEmpty.last nonempty
                            ReplayFormationAliasesReverse ->
                                NonEmpty.head nonempty)
                        (case failure of
                            KernelProof.ProofConversionNotConvertible ->
                                FormationAliasReplayResultMismatch
                            _ -> FormationAliasReplayKernelFailed failure))
                (KernelProof.conversionProof
                    proofContext replayed expectedResult)
  where
    steps =
        Elaboration.formationAliasNormalizationReplaySteps normalization
    orderedSteps = case direction of
        ReplayFormationAliasesForward -> steps
        ReplayFormationAliasesReverse -> reverse steps
    expectedResult = case direction of
        ReplayFormationAliasesForward ->
            Elaboration.formationAliasNormalizationResult normalization
        ReplayFormationAliasesReverse ->
            Elaboration.formationAliasNormalizationOriginal normalization

    replayStep current step = do
        let ordinal = Elaboration.formationAliasReplayStepOrdinal step
            definition =
                Elaboration.formationAliasReplayStepDefinition step
            expectedDefinition =
                Notion.materializedNotionHypothesisProposition definition
        index <-
            maybe
                (replayFailure
                    step FormationAliasReplayHypothesisUnavailable)
                pure
                (Map.lookup ordinal hypothesisIndices)
        definitionProof <-
            Bifunctor.first
                (replayKernelFailure step)
                (KernelProof.indexedHypothesisProof proofContext index)
        unless
            (KernelProof.builtProofStatement definitionProof
                == expectedDefinition)
            (replayFailure step FormationAliasReplayHypothesisMismatch)
        equalityProof <- case direction of
            ReplayFormationAliasesForward -> pure definitionProof
            ReplayFormationAliasesReverse ->
                Bifunctor.first
                    (replayKernelFailure step)
                    (KernelProof.equalityReverseProof
                        proofContext definitionProof)
        Bifunctor.first
            (replayKernelFailure step)
            (KernelProof.equalityTransportProof
                proofContext equalityProof
                (Elaboration.formationAliasReplayStepAbstraction step)
                current)

    replayKernelFailure step =
        aliasReplayIntegrity step . FormationAliasReplayKernelFailed

    replayFailure step =
        Left . aliasReplayIntegrity step

    aliasReplayIntegrity step failure =
        RecordExtensionalityAliasNormalizationIntegrity
            (Elaboration.formationAliasReplayStepLocation step)
            (Elaboration.formationAliasReplayStepOrdinal step)
            failure

preparePreparedDischargeWith
    :: ProofMode
    -> [FoundationAxiomTag]
    -> Maybe Declaration.VampirePremisePolicy
    -> Maybe ObviousInvocation
    -> Location
    -> Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> PreparedProofGoal
    -> PreparedJustification
    -> Prepare PreparedDischarge
preparePreparedDischargeWith
        proofMode auxiliaries selectionOverride invocation
        location context locals preparedGoal method =
    case method of
        PreparedAssumption ->
            prepareLocalDischarge PreparedAssumption
        PreparedDefinition ->
            prepareObvious PreparedDefinition Nothing
        PreparedImplicitObvious ->
            prepareObvious PreparedImplicitObvious Nothing
        PreparedObviousReferences references ->
            prepareObvious method (Just references)
        PreparedNotion ->
            impossible "a notion justification bypassed its source goal"
        PreparedSetExtensionality ->
            impossible "set extensionality bypassed its direct preparer"
        PreparedRecordExtensionality ->
            impossible "record extensionality bypassed its direct preparer"
        _ ->
            prepareOrdinaryDischarge method
  where
    goal = preparedProofGoalCore preparedGoal
    prepareLocalDischarge preparedJustification = do
        alignedLocals <- alignPreparedLocals context locals
        let hypotheses = preparedLocalProposition <$> alignedLocals
        prepared <-
            prepareCheckedProofEnvironment
                (goal : hypotheses)
                (\foundation globalType -> do
                    proofContext <-
                        KernelProof.scopedProofContext
                            foundation
                            globalType
                            (scopedCoreContext goal)
                            hypotheses
                    premiseProofs <-
                        traverse
                            (\(index, _hypothesis) ->
                                KernelProof.indexedHypothesisProof
                                    proofContext
                                    (hypothesisIx (fromIntegral index)))
                            (zip
                                [0 :: Int ..]
                                hypotheses)
                    KernelProof.conjunctionAssumptionProof
                        proofContext premiseProofs goal)
        case prepared of
            Right (Just proof) ->
                pure
                    (PreparedKernelDischarge
                        location
                        preparedJustification
                        goal
                        alignedLocals
                        []
                        (KernelProof.builtProofDerivation proof))
            Right Nothing ->
                throwProof (ProofAssumptionUnavailable location)
            Left failure ->
                throwProof
                    (ProofStructuralCompositionFailed
                        location failure)

    prepareObvious preparedJustification references =
        prepareObviousWith True preparedJustification references >>= maybe
            (impossible "a required obvious inference returned no result") pure

    prepareObviousWith required preparedJustification references = do
        alignedLocals <- alignPreparedLocals context locals
        resolvedFacts <-
            traverse resolvePreparedFact
                (maybe [] toList references)
        structuralViews <- traverse resolveCitedViews references
        let structuralFacts = maybe [] Declaration.citedStructureViewFacts structuralViews
            structuralOrigins = maybe [] Declaration.citedStructureViewOrigins structuralViews
            selectedFacts = stableUniqueFacts (resolvedFacts <> structuralFacts)
        definitions <- liftDriver Declaration.recursiveDefinitionLookupLowering
        (resolvedViews,recursiveRelevant) <-
            resolveCanonicalDefinitionClosure definitions
                ( goal
                    : (preparedLocalProposition <$> alignedLocals)
                    <> [ embedClosedCore
                            (scopedCoreContext goal)
                            (checkedPropositionTerm proposition)
                       | (_fingerprint, proposition) <- selectedFacts
                       ]
                )
        let hypotheses = preparedLocalProposition <$> alignedLocals
            viewFacts =
                [ ( Declaration.resolvedDefinitionViewFingerprint view
                  , Declaration.resolvedDefinitionViewProposition view
                  )
                | view <- resolvedViews
                ]
            allFacts = stableUniqueFacts (selectedFacts <> viewFacts)
            indexedFacts =
                zipWith
                    (\index fact ->
                        (importIx (fromIntegral index), fact))
                    [0 :: Int ..]
                    allFacts
            importByFingerprint =
                Map.fromList
                    [ (fingerprint, (index, proposition))
                    | (index, (fingerprint, proposition)) <- indexedFacts
                    ]
            imports =
                [ Obvious.obviousImport index
                    (checkedPropositionTerm proposition)
                | (fingerprint, _proposition) <- selectedFacts
                , Just (index, proposition) <-
                    [Map.lookup fingerprint importByFingerprint]
                ]
            importedDefinitionRows =
                [ ( Obvious.obviousImportedDefinitionView
                        (Declaration.resolvedDefinitionViewObject view)
                        (Declaration.resolvedDefinitionViewKind view)
                        (Obvious.obviousImport
                            index
                            (checkedPropositionTerm proposition))
                  , ImportedDefinitionOriginSeed
                        index
                        (Declaration.resolvedDefinitionViewFingerprint view)
                        (Declaration.resolvedDefinitionViewObject view)
                  )
                | view <- resolvedViews
                , Just (index, proposition) <-
                    [ Map.lookup
                        (Declaration.resolvedDefinitionViewFingerprint view)
                        importByFingerprint
                    ]
                ]
            definitionRows =
                localDefinitionViews alignedLocals <> importedDefinitionRows
            definitionViews = fst <$> definitionRows
            definitionOrigins = snd <$> definitionRows
            importedPropositions =
                [ embedClosedCore
                    (scopedCoreContext goal)
                    (checkedPropositionTerm proposition)
                | (_index, (_fingerprint, proposition)) <- indexedFacts
                ]
        failureFixture <- Reader.asks prepareObviousFailureFixture
        active <- State.gets prepareRecursiveRequest
        let starting = required && recursiveRelevant && isNothing active
            requirement = case preparedJustification of
                PreparedDefinition -> Obvious.MustUseCanonicalDefinition
                _ -> Obvious.AnyObviousProof
        attempted <- case failureFixture of
            Just failureReport -> pure (Just (Left failureReport),Nothing,[])
            Nothing -> do
              run <- prepareCheckedProofEnvironment
                (goal : hypotheses <> importedPropositions)
                (\foundation globalType ->
                    case active of
                        Just request -> Just (Obvious.obviousProofReportWithin
                            (requestAllowance request) requirement foundation globalType
                            hypotheses imports definitionViews goal)
                        Nothing | starting -> Obvious.obviousInitialProofReportWithin
                            (Obvious.obviousAllowance Obvious.defaultObviousBudget) requirement foundation globalType
                            hypotheses imports definitionViews goal
                        Nothing -> Just (Obvious.obviousProofReportWithin
                            (Obvious.obviousAllowance Obvious.defaultObviousBudget) requirement foundation globalType
                            hypotheses imports definitionViews goal))
              case run of
                Nothing -> pure (Nothing,Just (Obvious.obviousAllowance Obvious.defaultObviousBudget),[])
                Just (report,balance) -> do
                    when (isJust active) (modifyRecursiveRequest (\request -> request
                        {requestAllowance = balance, requestPriorObvious = requestPriorObvious request <> [Obvious.obviousRunStatistics report]}))
                    pure (Just (runResult report),Just balance,[Obvious.obviousRunStatistics report])
        case attempted of
          (result,Just balance,statistics) | starting, shouldPrepare result -> do
            work <- Reader.asks prepareAutomaticWork
            State.modify' (\state -> state {prepareRecursiveRequest = Just (RecursiveRequest balance
                (Preparation.preparationSession work)
                (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits)
                goal definitions statistics selectedFacts Map.empty Nothing 0 0)})
            let residualMethod = case preparedJustification of
                    PreparedDefinition -> PreparedImplicitObvious
                    other -> other
                residual nested nestedLocals nestedGoal = preparePreparedDischargeWith
                    proofMode auxiliaries selectionOverride invocation location nested nestedLocals nestedGoal residualMethod
            preparedTree <- prepareRecursiveScopes location context alignedLocals preparedGoal residual
            (prepared,_) <- pruneRecursiveEvidence location preparedTree
            request <- currentRecursiveRequest
            let preparation = Preparation.preparationStatistics (requestPreparation request)
                authorized = case preparedJustification of
                    PreparedDefinition -> PreparedDefinitionDischarge prepared
                    _ -> prepared
            State.modify' (\state -> state {prepareRecursiveRequest = Nothing
                ,prepareAutomaticStatistics = (location,preparation) : prepareAutomaticStatistics state})
            pure (Just (if Preparation.preparationExhausted preparation
                then PreparedPreparationLimit preparation authorized else authorized))
          (Just result,_,_) -> finishObvious result alignedLocals indexedFacts structuralOrigins definitionOrigins
          _ -> impossible "an ordinary obvious run was skipped"

      where
        shouldPrepare Nothing = True
        shouldPrepare (Just (Right _)) = False
        shouldPrepare (Just (Left report)) =
            obviousFailureDisposition (Obvious.obviousFailureFinal report) /= ProofInfrastructureFailure

        finishObvious result alignedLocals indexedFacts structuralOrigins definitionOrigins = case result of
            Left failureReport
                | not required
                , obviousFailureDisposition (Obvious.obviousFailureFinal failureReport)
                    == ProofSourceRejection -> pure Nothing
            Left failureReport -> do
                let failure = Obvious.obviousFailureFinal failureReport
                obviousInvocation <-
                    maybe
                        (if required
                            then impossible "an Obvious discharge lost its invocation sidecar"
                            else throwProof (ProofObviousInferenceFailed location failure))
                        pure
                        invocation
                diagnostic <-
                    either
                        (throwProof
                            . ProofObviousDiagnosticIntegrityFailure location)
                        pure
                        (assembleProofObviousDiagnostic
                            obviousInvocation
                            failureReport
                            alignedLocals
                            indexedFacts
                            structuralOrigins
                            definitionOrigins)
                request <- State.gets prepareRecursiveRequest
                let described = case (request,diagnostic) of
                        (Just current,ProofObviousDiagnostic a b c d e f g notes) ->
                            ProofObviousDiagnostic a b c d e f g (notes <> recursiveRequestNotes current)
                        _ -> diagnostic
                throwProofForGoal (Just (maybe goal requestOriginalGoal request))
                    (ProofObviousInferenceReported location described)
            Right obvious -> Just <$> do
                let usedImports = Obvious.obviousUsedImports obvious
                    retainedFacts =
                        [ (sourceIndex, fingerprint)
                        | (sourceIndex, (fingerprint, _proposition)) <-
                            indexedFacts
                        , sourceIndex `Set.member` usedImports
                        ]
                    importRemapping =
                        Map.fromList
                            [ (sourceIndex, importIx (fromIntegral retainedIndex))
                            | (retainedIndex, (sourceIndex, _fingerprint)) <-
                                zip [0 :: Int ..] retainedFacts
                            ]
                    sourceDerivation =
                        KernelProof.builtProofDerivation
                            (Obvious.obviousBuiltProof obvious)
                derivation <-
                    maybe
                        (impossible
                            "obvious inference reported an inconsistent import set")
                        pure
                        (remapKernelDerivationImports
                            (`Map.lookup` importRemapping)
                            sourceDerivation)
                pure
                    (PreparedKernelDischarge
                        location
                        preparedJustification
                        goal
                        alignedLocals
                        (snd <$> retainedFacts)
                        derivation)

    runResult report = case Obvious.obviousRunResult report of
        Right proof -> Right proof
        Left _failure -> Left
            (fromMaybe (impossible "a failed Obvious run has no failure report")
                (Obvious.obviousRunFailure report))

    resolvePreparedFact fingerprint = do
        proposition <-
            liftDriver
                (Declaration.resolveVisibleFactLowering fingerprint)
        maybe
            (impossible "a prepared proof reference is no longer visible")
            (\checked -> pure (fingerprint, checked))
            proposition

    resolveCitedViews references =
        liftDriver (Declaration.resolveCitedStructureViewsLowering references)
            >>= either (throwProof . ProofCompositionDeclarationInvalid location) pure

    prepareOrdinaryDischarge preparedJustification = do
        -- Flattened predicates no longer mention parent predicate names.
        -- Try the bounded definition-aware kernel search on the exact cited
        -- premises before asking ATP to recover a structure application.
        obvious <- case (proofMode, selectionOverride, preparedJustification) of
            (DirectProof, Nothing, PreparedAuto (Just references)) -> do
                structure <- liftDriver
                    (Declaration.resolveVisibleStructurePredicateApplicationLowering (scopedCoreTerm goal))
                    >>= either (throwProof . ProofStructurePredicateResolutionFailed location) pure
                case structure of
                    Just _ -> prepareObviousWith False preparedJustification (Just references)
                    Nothing -> pure Nothing
            _ -> pure Nothing
        maybe (prepareOrdinaryFallback preparedJustification) pure obvious

    prepareOrdinaryFallback preparedJustification = do
        selection <- case (selectionOverride, preparedJustification) of
            (Just override, _) -> pure override
            (Nothing, PreparedAuto (Just references)) ->
                Declaration.citedStructureVampirePremisePolicy <$> resolveCitedViews references
            _ -> pure (vampirePremisePolicy preparedJustification)
        case (proofMode, selectionOverride) of
            (DirectProof, Nothing) -> do
                alignedLocals <- alignPreparedLocals context locals
                proofContext <- prepareCheckedProofEnvironment
                    (goal : (preparedLocalProposition <$> alignedLocals))
                    (\foundation globalType -> KernelProof.scopedProofContext
                        foundation globalType (scopedCoreContext goal)
                        (preparedLocalProposition <$> alignedLocals))
                    >>= either (throwProof . ProofStructuralCompositionFailed location) pure
                work <- Reader.asks prepareAutomaticWork
                (prepared, session) <- State.runStateT
                    (prepareLocalFirst context proofContext alignedLocals preparedJustification selection goal)
                    (Preparation.preparationSession work)
                State.modify' (\state -> state
                    {prepareAutomaticStatistics =
                        (location, Preparation.preparationStatistics session)
                            : prepareAutomaticStatistics state})
                result <- either (throwProof . ProofObligationPreparationFailed location) pure prepared
                let statistics = Preparation.preparationStatistics session
                pure (if Preparation.preparationExhausted statistics
                    then PreparedPreparationLimit statistics result else result)
            _ -> requireVampireLeaf (prepareVampireLeaf context locals preparedJustification selection goal)

    prepareLocalFirst currentContext proofContext alignedLocals preparedJustification selection target = do
        (plan, facts) <- localPlan Preparation.prepareLocalEvidenceWithDefinitions proofContext target
        lowerLocalPlan facts currentContext proofContext alignedLocals
            (\childContext childProofContext childLocals ->
                prepareOrdinaryHole childContext childProofContext childLocals preparedJustification selection)
            plan

    localPlan prepare proofContext target = do
        lookupDefinition <- Trans.lift (liftDriver Declaration.pointwiseDefinitionLookupLowering)
        session <- State.get
        let (result, remaining) = prepare
                (fmap (checkedPropositionTerm . Declaration.resolvedDefinitionViewProposition) . lookupDefinition)
                session proofContext target
        State.put remaining
        (plan, imports) <- Trans.lift
            (either (throwProof . ProofStructuralCompositionFailed location) pure result)
        let facts = Map.fromList
                [ (index, maybe (impossible "preparation lost an admitted pointwise association")
                    Declaration.resolvedDefinitionViewFingerprint (lookupDefinition object))
                | (index, object) <- imports
                ]
        pure (plan, facts)

    lowerLocalPlan facts currentContext proofContext alignedLocals prepareHole plan =
        case Preparation.preparationView plan of
            Preparation.PreparationHole target -> prepareHole currentContext proofContext alignedLocals target
            Preparation.PreparationProof proof used ->
                Right <$> lowerKernelEvidence facts alignedLocals proof used
            Preparation.PreparationRewrite target equation child -> do
                evidence <- lowerKernelEvidence facts alignedLocals equation Set.empty
                local <- Trans.lift (allocateLocal ProofDerivedClaim currentContext (KernelProof.builtProofStatement equation))
                prepared <- lowerLocalPlan facts currentContext proofContext alignedLocals prepareHole child
                pure (PreparedEqualityDischarge location target local evidence <$> prepared)
            Preparation.PreparationEvidence proof used nested child -> do
                evidence <- lowerKernelEvidence facts alignedLocals proof used
                local <- Trans.lift (allocateLocal ProofDerivedClaim currentContext (KernelProof.builtProofStatement proof))
                prepared <- lowerLocalPlan facts currentContext nested (local : alignedLocals) prepareHole child
                pure (PreparedEvidenceDischarge location (Preparation.preparationGoal child) local evidence <$> prepared)
            Preparation.PreparationConjunction target left right -> do
                -- The opaque preparation plan owns the exact checked split;
                -- replaying another optional structural proof here would repeat
                -- its already charged construction outside the root account.
                leftChild <- lowerLocalPlan facts currentContext proofContext alignedLocals prepareHole left
                rightChild <- lowerLocalPlan facts currentContext proofContext alignedLocals prepareHole right
                pure ((\l r -> PreparedKernelComposition location target [] (l :| [r]) conjunctionDerivation)
                    <$> leftChild <*> rightChild)

            Preparation.PreparationUniversal target binderType nested child -> do
                Trans.lift (validateUniversalDischarge target binderType (Preparation.preparationGoal child))
                identity <- Trans.lift allocateLocalIdentity
                nestedContext <- Trans.lift (either (throwProof . ProofElaborationFailed) pure
                    (Elaboration.extendTypedAnonymousElaborationContext binderType identity currentContext))
                let support = Elaboration.elaborationContextSupport nestedContext
                    nestedLocals = retainWeakenedLocals support alignedLocals
                        (KernelProof.proofContextHypotheses nested)
                prepared <- lowerLocalPlan facts nestedContext nested nestedLocals prepareHole child
                pure (PreparedUniversalDischarge location target binderType identity <$> prepared)
            Preparation.PreparationImplication target premise nested child -> do
                Trans.lift (validateImplicationDischarge target premise (Preparation.preparationGoal child))
                local <- Trans.lift (allocateLocal ProofAssumption currentContext premise)
                prepared <- lowerLocalPlan facts currentContext nested (local : alignedLocals) prepareHole child
                pure (PreparedImplicationDischarge location target local <$> prepared)

    lowerKernelEvidence facts alignedLocals proof used = do
        let retained = [(index, fromMaybe (impossible "preparation used an unbound definition import")
                (Map.lookup index facts)) | index <- Set.toAscList used]
            remapping = Map.fromList
                [(index, importIx ordinal) | (ordinal, (index, _)) <- zip [0..] retained]
        derivation <- maybe (impossible "preparation reported inconsistent definition dependencies") pure
            (remapKernelDerivationImports (`Map.lookup` remapping) (KernelProof.builtProofDerivation proof))
        pure (PreparedKernelDischarge location PreparedImplicitObvious
            (KernelProof.builtProofStatement proof) alignedLocals (snd <$> retained) derivation)

    -- Binder opening has already weakened and charged the logical hypotheses.
    -- Keep their original ordinals/origins while attaching the fresh support.
    retainWeakenedLocals _support [] [] = []
    retainWeakenedLocals support (PreparedLocal ordinal origin _ _ : remaining) (proposition : rest) =
        PreparedLocal ordinal origin support proposition : retainWeakenedLocals support remaining rest
    retainWeakenedLocals _ _ _ = impossible "preparation changed the binder's hypothesis inventory"

    prepareCitedEvidence proofContext alignedLocals preparedJustification target =
        case preparedJustification of
            PreparedAuto (Just references) -> trySelected (toList references)
            _ -> pure Nothing
      where
        trySelected [] = pure Nothing
        trySelected (fingerprint : rest) = do
            session <- State.get
            if Preparation.preparationExhausted (Preparation.preparationStatistics session)
                then pure Nothing else do
                    (_, proposition) <- Trans.lift (resolvePreparedFact fingerprint)
                    let (result, remaining) = Preparation.prepareSelectedImport session proofContext target
                            (checkedPropositionTerm proposition)
                    State.put remaining
                    proof <- Trans.lift (either (throwProof . ProofStructuralCompositionFailed location) pure result)
                    case proof of
                        Nothing -> trySelected rest
                        Just checked -> pure (Just (PreparedKernelDischarge location preparedJustification
                            target alignedLocals [fingerprint] (KernelProof.builtProofDerivation checked)))

    prepareOrdinaryHole currentContext proofContext alignedLocals preparedJustification selection target = do
        session <- State.get
        let originals = Map.fromList
                [(preparedLocalOrdinalValue local, (index, local))
                | (index, local) <- zip [0..] alignedLocals]
            aliases = mapMaybe eligible (reverse (Elaboration.formationAliasDefinitions
                (Elaboration.alignFormationAliases currentContext)))
            eligible definition = case Notion.materializedNotionHypothesisOrigin definition of
                Elaboration.FormationFromProofLocal ordinal Elaboration.FormationProofLocalDefinition -> do
                    (index, local@(PreparedLocal _ origin _ _)) <- Map.lookup ordinal originals
                    guard (origin == ProofLocalDefinition)
                    if preparedLocalProposition local == Notion.materializedNotionHypothesisProposition definition
                        then Just index
                        else impossible "an eligible compiler alias changed its active definition"
                _ -> impossible "a compiler alias lost its definition origin"
        if Preparation.preparationExhausted (Preparation.preparationStatistics session) || null aliases
            then prepareRepresentationHole currentContext proofContext alignedLocals preparedJustification selection target
            else do
                (plan, facts) <- localPlan (Preparation.prepareAliasEvidence aliases) proofContext target
                lowerLocalPlan facts currentContext proofContext alignedLocals
                    (\childContext childProofContext childLocals ->
                        prepareRepresentationHole childContext childProofContext childLocals preparedJustification selection)
                    plan

    prepareRepresentationHole currentContext proofContext alignedLocals preparedJustification selection target = do
        let original = Trans.lift (prepareVampireLeaf currentContext alignedLocals preparedJustification selection target)
            structureEligible = case preparedJustification of
                PreparedInternalAuto -> True
                PreparedAuto _ -> True
                _ -> False
        exactPair <- if structureEligible
            then Trans.lift (recognizeExactStructurePair location target)
            else pure Nothing
        case exactPair of
            Nothing -> do
                residualized <- if structureEligible
                    then prepareStructureResidualization currentContext proofContext alignedLocals
                        preparedJustification selection target
                    else pure Nothing
                maybe original (pure . Right) residualized
            Just (left, right) -> do
                leftPrepared <- prepareLocalFirst currentContext proofContext alignedLocals
                    preparedJustification selection left
                rightPrepared <- prepareLocalFirst currentContext proofContext alignedLocals
                    preparedJustification selection right
                case (leftPrepared, rightPrepared) of
                    (Right leftChild, Right rightChild) -> pure (Right
                        (PreparedKernelComposition location target [] (leftChild :| [rightChild]) conjunctionDerivation))
                    _ -> original

    prepareStructureResidualization currentContext proofContext alignedLocals preparedJustification selection target = do
        analysis <- Trans.lift (analyseStructureResidualization location selection target)
        case analysis of
            Nothing -> pure Nothing
            Just (definitionFingerprint, definition, componentCount, excluded) -> do
                selected <- prepareCitedEvidence proofContext alignedLocals preparedJustification target
                case selected of
                    Just proof -> pure (Just proof)
                    Nothing -> do
                        session <- State.get
                        let (opening, remaining) = Preparation.preparePredicateEquality session proofContext target definition
                        State.put remaining
                        opened <- Trans.lift (either (throwProof . ProofStructureIntroductionFailed location) pure opening)
                        case opened of
                            Nothing -> pure Nothing
                            Just (equality, body) -> do
                                local <- Trans.lift (allocateLocal ProofDerivedClaim currentContext
                                    (KernelProof.builtProofStatement equality))
                                (plan, facts) <- localPlan (Preparation.prepareStructureRequirements componentCount) proofContext body
                                child <- lowerLocalPlan facts currentContext proofContext alignedLocals
                                    (\childContext _childProofContext childLocals ->
                                        Trans.lift . prepareStructureLeaf childContext childLocals
                                            local excluded preparedJustification selection)
                                    plan
                                prepared <- Trans.lift (either (throwProof . ProofObligationPreparationFailed location) pure child)
                                let equation = PreparedKernelDischarge location PreparedImplicitObvious
                                        (KernelProof.builtProofStatement equality) alignedLocals [definitionFingerprint]
                                        (KernelProof.builtProofDerivation equality)
                                pure (Just (PreparedEqualityDischarge location target local equation prepared))

    -- Consume the representation equation when that exposes a first-order
    -- residual. A higher-order residual keeps the original authorized premise
    -- policy; it must not discard completed siblings to regain abstraction.
    prepareStructureLeaf currentContext currentLocals equationLocal excluded preparedJustification selection leafGoal
      | Set.null excluded = do
        equations <- alignPreparedLocals currentContext [equationLocal]
        prepareVampireLeaf currentContext (equations <> currentLocals) preparedJustification selection leafGoal
      | otherwise = do
        -- An explicitly consumed definition does not acquire an extra local
        -- specialization. Uncited residuals above keep the proved equation.
        reduced <- prepareVampireLeafExcluding currentContext currentLocals excluded preparedJustification selection leafGoal
        case reduced of
            Right child@(PreparedVampireDischarge _ _ _ obligation)
                | Declaration.preparedVampireObligationRoute obligation == Backend.RouteFof -> pure (Right child)
            Right _ -> prepareVampireLeaf currentContext currentLocals preparedJustification selection leafGoal
            Left failure -> pure (Left failure)

    prepareVampireLeaf currentContext currentLocals preparedJustification selection leafGoal = do
        prepared <-
            liftDriver
                (prepareObligation
                    (Elaboration.elaborationContextSupport currentContext)
                    leafGoal
                    (toScopedPremise <$> currentLocals)
                    auxiliaries
                    selection)
        pure
            (PreparedVampireDischarge
                location
                preparedJustification
                leafGoal
                <$> prepared)

    prepareVampireLeafExcluding
            currentContext currentLocals excluded preparedJustification selection leafGoal = do
        prepared <-
            liftDriver
                (Declaration.prepareScopedVampireObligationExcludingLowering
                    excluded
                    (Elaboration.elaborationContextSupport currentContext)
                    leafGoal
                    (toScopedPremise <$> currentLocals)
                    auxiliaries
                    selection)
        pure
            (PreparedVampireDischarge
                location
                preparedJustification
                leafGoal
                <$> prepared)

    requireVampireLeaf prepareLeaf =
        prepareLeaf
            >>= either
                (throwProof
                    . ProofObligationPreparationFailed location)
                pure

    prepareObligation =
        case proofMode of
            DirectProof ->
                Declaration.prepareScopedVampireObligationLowering
            ContradictionProof ->
                Declaration.prepareScopedContradictionObligationLowering

    toScopedPremise
            (PreparedLocal ordinal origin support proposition) =
        Declaration.scopedVampirePremise
            ordinal origin support proposition

-- | Resolve only canonical definitions reachable from the checked proof
-- problem. Following globals in view propositions makes a newly exposed
-- definiens usable without turning the complete imported library into a
-- rewrite environment.
resolveCanonicalDefinitionClosure
    :: (ObjectId -> [RecursiveInterface.CheckedRecursiveDefinition])
    -> [ScopedCheckedCore ObjectId]
    -> Prepare ([Declaration.ResolvedDefinitionView],Bool)
resolveCanonicalDefinitionClosure definitions propositions =
    go Set.empty initial [] False
  where
    initial =
        Set.unions
            (canonicalTermGlobals . scopedCoreTerm <$> propositions)

    go visited pending reversed relevant =
        case Set.minView pending of
            Nothing ->
                pure
                    (List.sortOn
                        (\view ->
                            ( Declaration.resolvedDefinitionViewObject view
                            , Declaration.resolvedDefinitionViewKind view
                            ))
                        (reverse reversed),relevant)
            Just (object, rest)
                | object `Set.member` visited ->
                    go visited rest reversed relevant
                | otherwise -> do
                    views <-
                        liftDriver
                            (Declaration.resolveVisibleDefinitionViewsLowering
                                object)
                    let discovered =
                            Set.unions
                                [ canonicalTermGlobals
                                    (frozenCoreTerm
                                        (checkedPropositionTerm
                                            (Declaration.resolvedDefinitionViewProposition
                                                view)))
                                | view <- views
                                ]
                        visited' = Set.insert object visited
                    go
                        visited'
                        (rest <> Set.difference discovered visited')
                        (reverse views <> reversed)
                        (relevant || not (null (definitions object)))

stableUniqueFacts
    :: [(SemanticFactOccurrenceFingerprint, CheckedPropositionContent)]
    -> [(SemanticFactOccurrenceFingerprint, CheckedPropositionContent)]
stableUniqueFacts =
    reverse . snd
        . foldl'
            (\(seen, reversed) fact@(fingerprint, _proposition) ->
                if fingerprint `Set.member` seen
                    then (seen, reversed)
                    else
                        ( Set.insert fingerprint seen
                        , fact : reversed
                        ))
            (Set.empty, [])

assembleProofObviousDiagnostic
    :: ObviousInvocation
    -> Obvious.ObviousFailureReport ObjectId
    -> [PreparedLocal]
    -> [ ( ImportIx
         , ( SemanticFactOccurrenceFingerprint
           , CheckedPropositionContent
           )
         )
       ]
    -> [(SemanticFactOccurrenceFingerprint, SemanticFactOccurrenceFingerprint)]
    -> [ObviousDefinitionOriginSeed]
    -> Either Text ProofObviousDiagnostic
assembleProofObviousDiagnostic
        invocation@(ObviousInvocation _site _method citationGroups)
        report locals indexedFacts structuralOrigins definitionOrigins = do
    hypothesisOrigins <-
        traverse joinHypothesis (Obvious.obviousFailureHypotheses report)
    importOrigins <-
        traverse joinImport (Obvious.obviousFailureImports report)
    localDefinitionViewOrigins <-
        traverse joinDefinition
            (Obvious.obviousFailureLocalDefinitionViews report)
    importedDefinitionViewOrigins <-
        traverse joinDefinition
            (Obvious.obviousFailureImportedDefinitionViews report)
    candidateOrigins <-
        traverse joinCandidate (Obvious.obviousFailureCandidates report)
    pure
        (ProofObviousDiagnostic
            invocation report hypothesisOrigins importOrigins
            localDefinitionViewOrigins importedDefinitionViewOrigins
            candidateOrigins [])
  where
    factIndex = Map.fromList
        [ (index, fingerprint)
        | (index, (fingerprint, _proposition)) <- indexedFacts
        ]
    citationIndex = Map.fromList
        [ (fingerprint, group)
        | group@(ObviousCitationGroup fingerprint _first _count
                _distinct _additional) <- citationGroups
        ]
    structuralIndex = Map.fromList structuralOrigins

    importCitation fingerprint = case Map.lookup fingerprint citationIndex of
        Just group -> Right (False, group)
        Nothing -> maybe (Left "a diagnostic import has no cited resource origin")
            (\group -> Right (True, group))
            (Map.lookup fingerprint structuralIndex >>= (`Map.lookup` citationIndex))

    joinHypothesis = \case
        Obvious.ObviousHypothesisObservation index _summary -> do
            PreparedLocal _ordinal origin _support _proposition <-
                maybe
                    (Left "a diagnostic hypothesis identifier is out of range")
                    Right
                    (atNaturalProof index locals)
            pure
                (ProofObviousLocalOrigin
                    index (renderProofLocalOrigin origin))
        _observation ->
            Left "a non-hypothesis appeared in the hypothesis observations"

    joinImport = \case
        Obvious.ObviousImportObservation index _summary -> do
            fingerprint <-
                maybe
                    (Left "a diagnostic import identifier is not in the request")
                    Right
                    (Map.lookup index factIndex)
            (structural, group) <- importCitation fingerprint
            pure (if structural then ProofObviousStructuralOrigin index group
                else ProofObviousCitedOrigin index group)
        _observation ->
            Left "a non-import appeared in the import observations"

    joinDefinition = \case
        Obvious.ObviousDefinitionObservation ordinal _kind source _summary -> do
            seed <-
                maybe
                    (Left "a diagnostic definition-view ordinal is out of range")
                    Right
                    (atNaturalProof ordinal definitionOrigins)
            case (source, seed) of
                ( Obvious.ObviousDefinitionFromHypothesis expected
                  , LocalDefinitionOriginSeed actual description
                  ) | expected == actual ->
                        pure
                            (ProofObviousLocalDefinitionOrigin
                                ordinal description)
                ( Obvious.ObviousDefinitionFromImport expected
                  , ImportedDefinitionOriginSeed actual fingerprint object
                  ) | expected == actual ->
                        pure
                            (ProofObviousImportedDefinitionOrigin
                                ordinal fingerprint object)
                _ ->
                    Left "diagnostic definition-view provenance is misaligned"
        _observation ->
            Left "a non-definition appeared in definition-view observations"

    joinCandidate candidate = do
        base <- case Obvious.obviousCandidateSource candidate of
            Obvious.CandidateHypothesis index -> do
                PreparedLocal _ordinal origin _support _proposition <-
                    maybe
                        (Left "a candidate hypothesis identifier is out of range")
                        Right
                        (atNaturalProof index locals)
                pure
                    ("local #" <> Text.pack (show index) <> " ("
                        <> renderProofLocalOrigin origin <> ")")
            Obvious.CandidateImport index -> do
                fingerprint <-
                    maybe
                        (Left "a candidate import identifier is not in the request")
                        Right
                        (Map.lookup index factIndex)
                (structural, group) <- importCitation fingerprint
                pure ((if structural then "direct-parent view of " else "") <> renderCitationGroup group)
        let (factOrdinals, goalOrdinals) =
                candidateDefinitionOrdinals
                    (Obvious.obviousCandidateDefinitionParticipation candidate)
        factDefinitions <- traverse joinDefinitionOrdinal factOrdinals
        goalDefinitions <- traverse joinDefinitionOrdinal goalOrdinals
        pure
            (ProofObviousCandidateOrigin
                base factDefinitions goalDefinitions)

    joinDefinitionOrdinal ordinal = do
        seed <-
            maybe
                (Left "a candidate definition-view ordinal is out of range")
                Right
                (atNaturalProof ordinal definitionOrigins)
        pure
            ("#" <> Text.pack (show ordinal) <> " (" <> case seed of
                LocalDefinitionOriginSeed _index description ->
                    description <> ")"
                ImportedDefinitionOriginSeed _index _fingerprint object ->
                    "imported " <> renderObjectId object <> ")")

candidateDefinitionOrdinals
    :: Obvious.CandidateDefinitionParticipation
    -> ([Natural], [Natural])
candidateDefinitionOrdinals = \case
    Obvious.CandidateNoDefinitionParticipation -> ([], [])
    Obvious.CandidateFactDefinitionParticipation fact _truncated ->
        (fact, [])
    Obvious.CandidateGoalDefinitionParticipation goal _truncated ->
        ([], goal)
    Obvious.CandidateFactAndGoalDefinitionParticipation
            fact _factTruncated goal _goalTruncated ->
        (fact, goal)

atNaturalProof :: Natural -> [value] -> Maybe value
atNaturalProof requested = go requested
  where
    go _remaining [] = Nothing
    go 0 (value : _rest) = Just value
    go remaining (_value : rest) = go (remaining - 1) rest

data ObviousDefinitionOriginSeed
    = LocalDefinitionOriginSeed !Natural !Text
    | ImportedDefinitionOriginSeed
        !ImportIx !SemanticFactOccurrenceFingerprint !ObjectId

localDefinitionViews
    :: [PreparedLocal]
    -> [ ( Obvious.ObviousDefinitionView ObjectId
         , ObviousDefinitionOriginSeed
         )
       ]
localDefinitionViews locals =
    mapMaybe make
        (zip [0 ..] locals)
  where
    make (index, PreparedLocal _ordinal origin _support proposition) = do
        kind <- localViewKind origin (scopedCoreTerm proposition)
        pure
            ( Obvious.obviousLocalDefinitionView index kind
            , LocalDefinitionOriginSeed index (renderProofLocalOrigin origin)
            )

    localViewKind origin proposition =
        case origin of
            ProofLocalConstructionExtensional ->
                Just DefinitionMembershipView
            ProofLocalConstructionEquation ->
                Just DefinitionExactView
            ProofLocalDefinition ->
                let (binderCount, body) = stripForalls 0 proposition
                in case body of
                    CEq _operandType
                            (CApp (CApp (CIntrinsic Member) _element) _set)
                            _right ->
                        Just DefinitionMembershipView
                    CEq{} | binderCount > 0 ->
                        Just DefinitionPointwiseView
                    CEq{} ->
                        Just DefinitionExactView
                    _ -> Nothing
            ProofAssumption -> Nothing
            ProofDerivedClaim -> Nothing

    stripForalls
        :: Natural
        -> CanonicalTerm global
        -> (Natural, CanonicalTerm global)
    stripForalls binderCount = \case
        CForall _binderType body ->
            stripForalls (binderCount + 1) body
        body -> (binderCount, body)

renderProofLocalOrigin :: ProofLocalOrigin -> Text
renderProofLocalOrigin = \case
    ProofAssumption -> "assumption"
    ProofDerivedClaim -> "derived claim"
    ProofLocalDefinition -> "local definition"
    ProofLocalConstructionExtensional ->
        "local construction membership law"
    ProofLocalConstructionEquation ->
        "local construction equation"

recognizeExactStructurePair
    :: Location
    -> ScopedCheckedCore ObjectId
    -> Prepare
        (Maybe
            ( ScopedCheckedCore ObjectId
            , ScopedCheckedCore ObjectId
            ))
recognizeExactStructurePair location goal =
    case splitScopedConjunction goal of
        Nothing -> pure Nothing
        Just pair@(structureGoal, exactShapeGoal) -> do
            resolved <-
                liftDriver
                    (Declaration.resolveVisibleStructurePredicateApplicationLowering
                        (scopedCoreTerm structureGoal))
                >>= either
                    (throwProof
                        . ProofStructurePredicateResolutionFailed
                            location)
                    pure
            case resolved of
                Nothing -> pure Nothing
                Just application -> do
                    let structure =
                            Declaration.resolvedStructurePredicateApplicationStructure
                                application
                        subject =
                            Declaration.resolvedStructurePredicateApplicationSubject
                                application
                    let selectors = [CGlobal (Schema.resolvedFieldSelector field)
                            | field <- Map.elems (Schema.resolvedSchemaFields (Declaration.resolvedStructureSchema structure))]
                    pure
                        ( pair <$ guard
                            (scopedCoreTerm exactShapeGoal
                                == Record.recordExactShape selectors subject)
                        )

-- The canonical registry owns the equation's proof occurrence; the recognized
-- schema owns only its normalized component boundaries and shape metadata.
-- Specialization and residual construction belong to the shared work account.
analyseStructureResidualization
    :: Location
    -> Declaration.VampirePremisePolicy
    -> ScopedCheckedCore ObjectId
    -> Prepare (Maybe (SemanticFactOccurrenceFingerprint, FrozenCheckedCore ObjectId, Natural,
        Set SemanticFactOccurrenceFingerprint))
analyseStructureResidualization location selection goal = do
    resolved <- liftDriver (Declaration.resolveVisibleStructurePredicateApplicationLowering (scopedCoreTerm goal))
        >>= either (throwProof . ProofStructurePredicateResolutionFailed location) pure
    case resolved of
        Nothing -> pure Nothing
        Just application -> do
            let structure = Declaration.resolvedStructurePredicateApplicationStructure application
                registration = Declaration.resolvedStructureRegistration structure
                schema = Declaration.resolvedStructureSchema structure
                predicate = StructurePredicate.pendingStructurePredicate registration
            lookupCanonical <- liftDriver Declaration.pointwiseDefinitionLookupLowering
            view <- maybe (throwProof (ProofStructureMetadataMismatch location)) pure (lookupCanonical predicate)
            let definition = Declaration.resolvedDefinitionViewProposition view
            unless (Declaration.resolvedDefinitionViewObject view == predicate
                && Declaration.resolvedDefinitionViewKind view == DefinitionPointwiseView
                && definition == StructurePredicate.structurePredicateDefinitionProposition registration)
                (throwProof (ProofStructureMetadataMismatch location))
            excluded <- liftDriver (Declaration.selectedStructurePredicateResourcesLowering selection predicate)
                >>= either (throwProof . ProofObligationPreparationFailed location) pure
            pure (Just (Declaration.resolvedDefinitionViewFingerprint view, checkedPropositionTerm definition,
                1 + fromIntegral (Map.size (Schema.resolvedSchemaRequirements schema)),
                excluded))

checkStructureTerm
    :: Location
    -> GlobalTyping ObjectId
    -> [CoreType]
    -> CanonicalTerm ObjectId
    -> Prepare (ScopedCheckedCore ObjectId)
checkStructureTerm location globalTyping context term =
    either
        (const
            (throwProof
                (ProofStructureMetadataMismatch location)))
        pure
        (checkScopedCanonicalCore
            globalTyping
            context
            term)

prepareJustification
    :: ObviousInvocationSite
    -> Location
    -> Raw.Justification
    -> Prepare (PreparedJustification, Maybe ObviousInvocation)
prepareJustification site _location Raw.JustificationImplicit =
    pure
        ( PreparedImplicitObvious
        , Just (ObviousInvocation site ImplicitObvious [])
        )
prepareJustification _site location (Raw.JustificationAuto markers) = do
    prepared <- PreparedAuto <$> traverse (prepareReferences location) markers
    pure (prepared, Nothing)
prepareJustification site location
        (Raw.JustificationObviousReferences markers) = do
    (references, groups) <- prepareObviousReferences location markers
    pure
        ( PreparedObviousReferences references
        , Just (ObviousInvocation site CitedObvious groups)
        )
prepareJustification _site _location Raw.JustificationAssumption =
    pure (PreparedAssumption, Nothing)
prepareJustification site _location Raw.JustificationDefinition =
    pure
        ( PreparedDefinition
        , Just (ObviousInvocation site DefinitionObvious [])
        )
prepareJustification _site _location Raw.JustificationNotion =
    pure (PreparedNotion, Nothing)
prepareJustification _site location Raw.JustificationSetExt =
    throwProof (ProofUnsupportedStep location)
prepareJustification _site location Raw.JustificationStructureExt =
    throwProof (ProofUnsupportedStep location)
prepareJustification _site location Raw.JustificationExtensionality =
    throwProof (ProofUnsupportedStep location)

obviousInvocationForPrepared
    :: ObviousInvocationSite
    -> PreparedJustification
    -> ObviousInvocation
obviousInvocationForPrepared site = \case
    PreparedImplicitObvious -> ObviousInvocation site ImplicitObvious []
    PreparedDefinition -> ObviousInvocation site DefinitionObvious []
    _justification ->
        impossible "a source Obvious invocation lost its method"

data CitationGroupBuilder = CitationGroupBuilder
    !Raw.Marker
    !Natural
    !(Set Raw.Marker)
    ![Raw.Marker]

prepareObviousReferences
    :: Location
    -> NonEmpty Raw.Marker
    -> Prepare
        ( NonEmpty SemanticFactOccurrenceFingerprint
        , [ObviousCitationGroup]
        )
prepareObviousReferences location markers = do
    resolved <- traverse resolve (toList markers)
    let (orderReversed, builders) =
            foldl' retain ([], Map.empty) resolved
        order = reverse orderReversed
        groups = fmap (completeGroup builders) order
    case order of
        [] -> impossible "a nonempty citation list resolved to no facts"
        first : rest -> pure (first :| rest, groups)
  where
    resolve marker = do
        fingerprint <- resolveReference location marker
        pure (fingerprint, marker)

    retain (order, builders) (fingerprint, marker) =
        case Map.lookup fingerprint builders of
            Nothing ->
                ( fingerprint : order
                , Map.insert
                    fingerprint
                    (CitationGroupBuilder marker 1 (Set.singleton marker) [])
                    builders
                )
            Just (CitationGroupBuilder first count spellings additional) ->
                let newSpelling = marker `Set.notMember` spellings
                    additional' =
                        if newSpelling && length additional < 2
                            then additional <> [marker]
                            else additional
                in ( order
                   , Map.insert
                        fingerprint
                        (CitationGroupBuilder
                            first
                            (count + 1)
                            (Set.insert marker spellings)
                            additional')
                        builders
                   )

    completeGroup builders fingerprint =
        case Map.lookup fingerprint builders of
            Just (CitationGroupBuilder first count spellings additional) ->
                ObviousCitationGroup
                    fingerprint first count
                    (fromIntegral (Set.size spellings)) additional
            Nothing -> impossible "a cited fact lost its source group"

prepareReferences
    :: Location
    -> NonEmpty Raw.Marker
    -> Prepare (NonEmpty SemanticFactOccurrenceFingerprint)
prepareReferences location markers = do
    resolved <- traverse (resolveReference location) (toList markers)
    let unique = stableUnique resolved
    case unique of
        [] ->
            impossible "a nonempty citation list resolved to no facts"
        first : rest ->
            pure (first :| rest)

vampirePremisePolicy
    :: PreparedJustification
    -> Declaration.VampirePremisePolicy
vampirePremisePolicy = \case
    PreparedInternalAuto ->
        Declaration.internalVampirePremisePolicy
    PreparedAuto Nothing ->
        Declaration.localVampirePremisePolicy
    PreparedAuto (Just fingerprints) ->
        Declaration.explicitVampirePremisePolicy fingerprints
    PreparedAssumption ->
        impossible "assumption reuse reached Vampire preparation"
    PreparedDefinition ->
        impossible "definition-aware obvious inference reached Vampire preparation"
    PreparedNotion ->
        impossible "notion inference reached Vampire preparation"
    PreparedSetExtensionality ->
        impossible "set extensionality reached Vampire preparation"
    PreparedRecordExtensionality ->
        impossible "record extensionality reached Vampire preparation"
    PreparedImplicitObvious ->
        impossible "obvious inference reached Vampire preparation"
    PreparedObviousReferences{} ->
        impossible "obvious inference reached Vampire preparation"

resolveReference
    :: Location
    -> Raw.Marker
    -> Prepare SemanticFactOccurrenceFingerprint
resolveReference location marker@(Raw.Marker name) = do
    resolved <-
        liftDriver
            (Declaration.resolveVisibleFactAliasLowering
                (semanticName name))
    maybe
        (throwProof
            (ProofUnknownReference location marker))
        pure
        resolved

prepareStatement
    :: Elaboration.ElaborationContext
    -> Raw.Stmt
    -> Prepare Elaboration.ElaboratedProposition
prepareStatement context statement =
    liftDriver
        (Elaboration.elaborateProposition context statement)
        >>= either
            (throwProof . ProofElaborationFailed)
            pure

prepareAssumptionOpening
    :: Location
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> Prepare
        ( LooseDeduction.AssumptionOpening ObjectId
        , LooseDeduction.DetailedAssumptionOpening ObjectId
        )
prepareAssumptionOpening location goal supplied = do
    detailed <-
        case LooseDeduction.findAssumptionOpening supplied goal of
            Left (LooseDeduction.AssumptionOpeningInvalidInput _failure) ->
                impossible "assumption opening received invalid checked input"
            Left
                    (LooseDeduction.AssumptionOpeningDoesNotMatch mismatch) ->
                throwProof
                    (ProofAssumptionOpeningFailed location mismatch)
            Right opening ->
                pure opening
    let opening =
            LooseDeduction.compactAssumptionOpening detailed
    case LooseDeduction.validateAssumptionOpening opening of
        Left _failure ->
            impossible "a newly prepared assumption opening did not replay"
        Right () ->
            pure ()
    validateStructuralComposition
        location
        [ goal
        , LooseDeduction.detailedOpeningSupplied detailed
        , LooseDeduction.detailedOpeningResidual detailed
        ]
        (\foundation globalType ->
            () <$ KernelProof.buildAssumptionOpeningComposition
                foundation
                globalType
                detailed)
    pure (opening, detailed)

validateStructuralComposition
    :: Location
    -> [ScopedCheckedCore ObjectId]
    -> ( CheckedFoundation
         -> GlobalTyping ObjectId
         -> Either KernelProof.KernelProofBuildError ()
       )
    -> Prepare ()
validateStructuralComposition location propositions validate = do
    result <- prepareStructuralComposition propositions validate
    either
        (throwProof
            . ProofStructuralCompositionFailed location)
        pure
        result

prepareStructuralComposition
    :: [ScopedCheckedCore ObjectId]
    -> ( CheckedFoundation
         -> GlobalTyping ObjectId
         -> Either KernelProof.KernelProofBuildError result
       )
    -> Prepare (Either KernelProof.KernelProofBuildError result)
prepareStructuralComposition =
    prepareCheckedProofEnvironment

prepareCheckedProofEnvironment
    :: [ScopedCheckedCore ObjectId]
    -> ( CheckedFoundation
         -> GlobalTyping ObjectId
         -> result
       )
    -> Prepare result
prepareCheckedProofEnvironment propositions use = do
    foundation <-
        liftDriver Declaration.currentFoundationLowering
    globalTyping <- prepareGlobalTyping
    unless
        (all
            (all isJust
                . fmap (lookupGlobalType globalTyping)
                . Set.toList
                . canonicalTermGlobals
                . scopedCoreTerm)
            propositions)
        (impossible "a checked structural proof lost a global object")
    pure (use foundation globalTyping)

-- | Build the proof-preparation view from the committed closure plus the one
-- exact owner-local object carried by the prepared declaration.  Closure
-- extension validates that object before the carrier enters checked proof
-- construction; the carrier is not retained by the prepared result.
prepareGlobalTyping :: Prepare (GlobalTyping ObjectId)
prepareGlobalTyping = do
    baseClosure <- liftDriver Declaration.checkedObjectClosureLowering
    localObject <- Reader.asks prepareLocalObject
    closure <-
        either
            (impossible
                . ("a prepared proof had an invalid owner-local object: " <>)
                . show)
            pure
            (extendObjectClosure baseClosure (maybeToList localObject))
    pure (globalTypingFromClosure closure)

structuralFailure :: Location -> Text -> Prepare value
structuralFailure location message =
    throwProof
        (ProofStructuralCompositionFailed
            location
            (KernelProof.ProofStructuralCompositionMismatch message))

data CheckedProofAuthorization = CheckedProofAuthorization
    !PreparedProofTree
    !ProofPlanningSummary
    ![Obligation.RecordObligation]

lowerPreparedProofCandidate
    :: [AssertedObject]
    -> FactSearchEligibility
    -> [SemanticName]
    -> PreparedProof
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            ( Declaration.CandidateSpec
            , Declaration.CheckedCandidate
            , CheckedProofAuthorization
            ))
lowerPreparedProofCandidate objects eligibility aliases
        (PreparedProof _location _alias target proof summary composition
            _notionRegistration _syntax _statistics obligations) =
    fmap makeParts
        <$> Declaration.prepareCandidateSpecLowering
            objects target eligibility aliases
  where
    makeParts spec =
        let annotated =
                maybe
                    spec
                    (`Declaration.candidateSpecWithRelationComposition` spec)
                    composition
        in ( annotated
        , Declaration.checkedCandidate annotated planning
        , authorization
        )
    authorization =
        CheckedProofAuthorization
            proof
            summary
            obligations
    requests = proofPlanningRequests summary
    facts = proofPlanningFacts summary
    planning
        | isJust (proofPlanningFirstOmission summary) =
            Declaration.checkedOmittedPlanning requests facts []
        | Just nonemptyRequests <- NonEmpty.nonEmpty requests =
            Declaration.checkedExternalSourceProofPlanningWithFacts
                nonemptyRequests facts []
        | otherwise =
            Declaration.checkedNoExternalSourceProofPlanningWithFacts
                facts []

lowerPreparedProof
    :: PreparedProof
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration CheckedProofAuthorization))
lowerPreparedProof
        prepared@(PreparedProof _location alias _target _proof _summary _composition
            notionRegistration syntax _statistics _obligations) =
    fmap checked
        <$> lowerPreparedProofCandidate
            [] SearchEligible [alias] prepared
  where
    checked (_spec, candidate, authorization) =
        Declaration.checkedProofDeclarationWithRegistrations
            syntax [] [] [] Nothing
            [ Registration (Planning.plannedEarlierCandidate 0 0) path body
            | (path, body) <- foldMap toList notionRegistration
            ]
            [candidate :| []]
            authorization

authorizeCheckedProofCandidate
    :: CheckedProofAuthorization
    -> Declaration.ReservedCandidate
    -> Declaration.Declaration ()
authorizeCheckedProofCandidate
        (CheckedProofAuthorization proof summary obligations) candidate
    | isJust (proofPlanningFirstOmission summary) =
        Declaration.authorizeOmittedCandidate
            candidate
            execution
    | null (proofPlanningRequests summary) =
        Declaration.authorizeStructuralSourceProofCandidate
            candidate
            (Authorization.structuralProofAuthorization
                execution)
    | otherwise =
        Declaration.authorizeVampireCandidate
            candidate
            execution
  where
    execution = Declaration.noteRecordObligations obligations (executePreparedProof proof)

authorizeCheckedProof
    :: CheckedProofAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedProof
        authorization = \case
    [candidate :| []]
        -> authorizeCheckedProofCandidate
                authorization
            candidate
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                1 (length stages))

data CheckedFinalPreludeFoundationAuthorization =
    CheckedFinalPreludeFoundationAuthorization !FoundationAxiomTag

lowerPreparedFinalPreludeFoundationClaim
    :: PreparedFinalPreludeFoundationClaim
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration
                CheckedFinalPreludeFoundationAuthorization))
lowerPreparedFinalPreludeFoundationClaim
        (PreparedFinalPreludeFoundationClaim
            _location alias target tag syntax) =
    fmap checked
        <$> Declaration.prepareCandidateSpecLowering
            [] target eligibility [alias]
  where
    eligibility =
        case classifyCanonicalFofStructure (scopedCoreTerm target) of
            FoundationFofProjectable -> SearchEligible
            FoundationRequiresTh0{} -> SearchIneligible

    checked spec =
        Declaration.checkedProofDeclaration
            syntax [] [] [] Nothing
            [ Declaration.checkedCandidate spec
                (Declaration.checkedKernelPlanning
                    (Authority.FoundationLeaf tag) [])
                :| []
            ]
            (CheckedFinalPreludeFoundationAuthorization tag)

authorizeCheckedFinalPreludeFoundationClaim
    :: CheckedFinalPreludeFoundationAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedFinalPreludeFoundationClaim
        (CheckedFinalPreludeFoundationAuthorization tag) = \case
    [candidate :| []] ->
        Declaration.authorizeKernelConstructionCandidate
            (Authority.FoundationLeaf tag)
            candidate
            (pure (foundationFactDerivation tag))
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                1 (length stages))

data CheckedFinalPreludeGuardedRuleAuthorization =
    CheckedFinalPreludeGuardedRuleAuthorization
    !KernelRuleTag
    !(KernelDerivation ObjectId)

lowerPreparedFinalPreludeGuardedRuleClaim
    :: PreparedFinalPreludeGuardedRuleClaim
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration
                CheckedFinalPreludeGuardedRuleAuthorization))
lowerPreparedFinalPreludeGuardedRuleClaim
        (PreparedFinalPreludeGuardedRuleClaim
            _location alias target tag derivation syntax) =
    fmap checked
        <$> Declaration.prepareCandidateSpecLowering
            [] target SearchIneligible [alias]
  where
    descriptor =
        Authority.GuardedFoundationRules
            (Authority.guardedRuleSet (tag :| []))

    checked spec =
        Declaration.checkedProofDeclaration
            syntax [] [] [] Nothing
            [ Declaration.checkedCandidate spec
                (Declaration.checkedKernelPlanning descriptor [])
                :| []
            ]
            (CheckedFinalPreludeGuardedRuleAuthorization
                tag derivation)

authorizeCheckedFinalPreludeGuardedRuleClaim
    :: CheckedFinalPreludeGuardedRuleAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedFinalPreludeGuardedRuleClaim
        (CheckedFinalPreludeGuardedRuleAuthorization tag derivation) = \case
    [candidate :| []] ->
        Declaration.authorizeKernelConstructionCandidate
            (Authority.GuardedFoundationRules
                (Authority.guardedRuleSet (tag :| [])))
            candidate
            (pure derivation)
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                1 (length stages))

-- Each node prepends its local observations to the remaining source sequence.
-- This visits the tree once without appending an accumulated prefix.
summarizeProofPlanning :: PreparedProofTree -> ProofPlanningSummary
summarizeProofPlanning tree = proofSummary tree (ProofPlanningSummary Nothing [] [])
  where
    proofSummary :: PreparedProofTree -> ProofPlanningSummary -> ProofPlanningSummary
    proofSummary proof rest = case proof of
        PreparedImplicitDischarge discharge -> dischargeSummary discharge rest
        PreparedQed discharge -> dischargeSummary discharge rest
        PreparedOmitted location _goal ->
            rest { proofPlanningFirstOmission = Just location }
        PreparedFix _identities continuation -> proofSummary continuation rest
        PreparedAssume _opening continuation -> proofSummary continuation rest
        PreparedGuardAssume _guard continuation -> proofSummary continuation rest
        PreparedTake _identities _witness discharge continuation ->
            dischargeSummary discharge (proofSummary continuation rest)
        PreparedSetInduction
                (PreparedCheckedSetInduction
                    _focus _property _antecedents _target _hypothesis _result child) ->
            proofSummary child rest
        PreparedHave _claim discharge continuation ->
            dischargeSummary discharge (proofSummary continuation rest)
        PreparedSuffices _goal _reduction _implication discharge continuation ->
            dischargeSummary discharge (proofSummary continuation rest)
        PreparedCalculate calculation continuation ->
            dischargeSummary calculation (proofSummary continuation rest)
        PreparedSince
                _since premiseDischarge _temporaryPremise _claim claimDischarge continuation ->
            dischargeSummary premiseDischarge
                (dischargeSummary claimDischarge (proofSummary continuation rest))
        PreparedSubclaim _claim subproof continuation ->
            proofSummary subproof (proofSummary continuation rest)
        PreparedDefine _identity _body _definition continuation -> proofSummary continuation rest
        PreparedDefineRelational _identity _body functionality _definitions continuation ->
            dischargeSummary functionality (proofSummary continuation rest)
        PreparedDefineFunction _identity _graph _definition continuation -> proofSummary continuation rest
        PreparedByCase (PreparedCaseAnalysis _goal cases _exhaustive discharge) ->
            foldr (proofSummary . preparedCaseProof) (dischargeSummary discharge rest) cases
        PreparedByContradiction _goal _negation _falsum child -> proofSummary child rest
        PreparedContradiction _goal _falsum discharge -> dischargeSummary discharge rest

    dischargeSummary :: PreparedDischarge -> ProofPlanningSummary -> ProofPlanningSummary
    dischargeSummary discharge rest = case discharge of
        PreparedDefinitionDischarge child -> dischargeSummary child rest
        PreparedRecursiveEquation _ application child _ ->
            dischargeSummary child rest {proofPlanningFacts = fst (Recursive.applicationEquation application) : proofPlanningFacts rest}
        PreparedPreparationLimit _statistics child -> dischargeSummary child rest
        PreparedFormationDischarge _completion child -> dischargeSummary child rest
        PreparedEqualityDischarge _ _ _ equation child ->
            dischargeSummary equation (dischargeSummary child rest)
        PreparedEvidenceDischarge _ _ _ evidence child ->
            dischargeSummary evidence (dischargeSummary child rest)
        PreparedUniversalDischarge _ _ _ _ child -> dischargeSummary child rest
        PreparedImplicationDischarge _ _ _ child -> dischargeSummary child rest
        PreparedVampireDischarge location _justification _goal obligation ->
            rest { proofPlanningRequests =
                Declaration.checkedPlannedVampireRequest location obligation : proofPlanningRequests rest }
        PreparedExcludedMiddle{} -> rest
        PreparedKernelDischarge _location _method _goal _locals facts _derivation ->
            rest { proofPlanningFacts = facts <> proofPlanningFacts rest }
        PreparedKernelComposition _location _goal facts children _derivation ->
            let childrenSummary = foldr dischargeSummary rest children
            in childrenSummary { proofPlanningFacts = facts <> proofPlanningFacts childrenSummary }

executePreparedProof
    :: PreparedProofTree
    -> Declaration.CandidateProof ()
executePreparedProof = \case
    PreparedImplicitDischarge discharge ->
        executeDischarge discharge
    PreparedQed discharge ->
        executeDischarge discharge
    PreparedOmitted _location _goal ->
        Declaration.recordOmittedUse
    PreparedFix _identities continuation ->
        executePreparedProof continuation
    PreparedAssume opening continuation -> do
        case LooseDeduction.validateAssumptionOpening opening of
            Left _failure ->
                impossible "a prepared assumption opening diverged"
            Right () ->
                executePreparedProof continuation
    PreparedGuardAssume _guard continuation ->
        executePreparedProof continuation
    PreparedTake _identities _witness discharge continuation -> do
        executeDischarge discharge
        executePreparedProof continuation
    PreparedSetInduction
            (PreparedCheckedSetInduction
                _focus _property _antecedents _target
                _hypothesis _result child) ->
        executePreparedProof child
    PreparedHave _claim discharge continuation -> do
        executeDischarge discharge
        executePreparedProof continuation
    PreparedSuffices goal reduction implication discharge continuation -> do
        executeDischarge discharge
        executePreparedProof continuation
        unless
            (implyScopedCore reduction goal == Just implication)
            (impossible "a prepared suffices implication diverged")
    PreparedCalculate calculation continuation -> do
        executeDischarge calculation
        executePreparedProof continuation
    PreparedSince
            sinceProposition premiseDischarge temporaryPremise
            claim claimDischarge continuation -> do
        executeDischarge premiseDischarge
        unless
            ( preparedDischargeGoal premiseDischarge == sinceProposition
                && preparedLocalProposition temporaryPremise
                    == sinceProposition
                && preparedDischargeGoal claimDischarge == claim
            )
            (impossible "a prepared since step diverged")
        executeDischarge claimDischarge
        executePreparedProof continuation
    PreparedSubclaim _claim subproof continuation -> do
        executePreparedProof subproof
        executePreparedProof continuation
    PreparedDefine _identity _body _definition continuation ->
        executePreparedProof continuation
    PreparedDefineRelational
            _identity _body functionality _definitions continuation -> do
        executeDischarge functionality
        executePreparedProof continuation
    PreparedDefineFunction _identity _graph _definition continuation ->
        executePreparedProof continuation
    PreparedByCase
            (PreparedCaseAnalysis _goal cases _exhaustive discharge) -> do
        traverse_ (executePreparedProof . preparedCaseProof) cases
        executeDischarge discharge
    PreparedByContradiction _goal _negation _falsum child ->
        executePreparedProof child
    PreparedContradiction _goal _falsum discharge ->
        executeDischarge discharge

executeDischarge
    :: PreparedDischarge
    -> Declaration.CandidateProof ()
executeDischarge (PreparedDefinitionDischarge child) = do
    (_,used) <- executeDefinitionDischarge child
    unless used (Error.throwError_ Declaration.KernelDefinitionEvidenceMissing)
executeDischarge (PreparedRecursiveEquation location application child derivation) = do
    executeDischarge child
    executeRecursiveEquation location application child derivation
executeDischarge (PreparedEqualityDischarge _location goal local equation child) = do
    unless (preparedLocalProposition local == preparedDischargeGoal equation
            && splitScopedEquality (preparedDischargeGoal equation)
            == Just (TyProp, goal, preparedDischargeGoal child))
        (impossible "a prepared predicate refinement changed its defining equality")
    executeDischarge equation
    executeDischarge child
executeDischarge (PreparedEvidenceDischarge _location goal local evidence child) = do
    unless (preparedLocalProposition local == preparedDischargeGoal evidence
            && goal == preparedDischargeGoal child)
        (impossible "a prepared evidence continuation changed its proved premise or goal")
    executeDischarge evidence
    executeDischarge child
executeDischarge (PreparedUniversalDischarge _location goal binderType _identity child) = do
    validateUniversalDischarge goal binderType (preparedDischargeGoal child)
    executeDischarge child
executeDischarge (PreparedImplicationDischarge _location goal local child) = do
    validateImplicationDischarge goal (preparedLocalProposition local) (preparedDischargeGoal child)
    executeDischarge child
executeDischarge (PreparedFormationDischarge completion discharge) =
    Declaration.completeFormationCandidate completion (executeDischarge discharge)
executeDischarge (PreparedPreparationLimit statistics discharge) =
    Declaration.notePreparationExhaustion statistics (executeDischarge discharge)
executeDischarge
        (PreparedVampireDischarge
            location _justification goal obligation) =
    Declaration.locateProofObligation location
        (Declaration.noteProofObligationGoal goal
            (Declaration.acceptPreparedVampireObligation obligation))
executeDischarge PreparedExcludedMiddle{} =
    pure ()
executeDischarge (PreparedKernelDischarge location method goal locals facts derivation) =
    void (executeKernelDischarge location method goal locals facts derivation)
executeDischarge (PreparedKernelComposition location goal facts children derivation) = do
    traverse_ executeDischarge children
    void (executeKernelComposition location goal facts children derivation)

executeKernelDischarge
    :: Location -> PreparedJustification -> ScopedCheckedCore ObjectId
    -> [PreparedLocal] -> [SemanticFactOccurrenceFingerprint] -> KernelDerivation ObjectId
    -> Declaration.CandidateProof Declaration.ScopedKernelUsage
executeKernelDischarge location method goal locals facts derivation =
    Declaration.locateProofObligation location
        (Declaration.acceptScopedKernelDischarge (kernelMethodPolicy method locals) facts
            (Vector.fromList (preparedLocalProposition <$> locals)) goal derivation)
  where
    kernelMethodPolicy prepared preparedLocals =
        case prepared of
            PreparedAuto (Just references) ->
                Declaration.KernelCitedObvious
                    (Set.fromList (toList references))
            PreparedImplicitObvious ->
                Declaration.KernelImplicitObvious
            PreparedObviousReferences references ->
                Declaration.KernelCitedObvious
                    (Set.fromList (toList references))
            PreparedAssumption ->
                Declaration.KernelAssumption
            PreparedDefinition ->
                Declaration.KernelDefinition
                    (Set.fromList
                        [ hypothesisIx (fromIntegral index)
                        | (index, local) <- zip [0 :: Int ..] preparedLocals
                        , preparedLocalIsDefinition local
                        ])
            PreparedNotion ->
                Declaration.KernelNotion
                    (Set.fromList
                        [ hypothesisIx (fromIntegral index)
                        | (index, _local) <-
                            zip [0 :: Int ..] preparedLocals
                        ])
            PreparedSetExtensionality ->
                Declaration.KernelSetExtensionality
                    (Set.fromList
                        [ hypothesisIx (fromIntegral index)
                        | (index, _local) <-
                            zip [0 :: Int ..] preparedLocals
                        ])
            PreparedRecordExtensionality ->
                Declaration.KernelRecordExtensionality
                    (Set.fromList
                        [ hypothesisIx (fromIntegral index)
                        | (index, _local) <-
                            zip [0 :: Int ..] preparedLocals
                        ])
            _ ->
                impossible
                    "a non-kernel proof method reached scoped kernel replay"

    preparedLocalIsDefinition
            (PreparedLocal _ordinal origin _support _proposition) =
        case origin of
            ProofLocalDefinition -> True
            ProofLocalConstructionExtensional -> True
            ProofLocalConstructionEquation -> True
            ProofAssumption -> False
            ProofDerivedClaim -> False
executeKernelComposition
    :: Location -> ScopedCheckedCore ObjectId -> [SemanticFactOccurrenceFingerprint]
    -> NonEmpty PreparedDischarge -> KernelDerivation ObjectId
    -> Declaration.CandidateProof Declaration.ScopedKernelUsage
executeKernelComposition location goal facts children derivation =
    Declaration.locateProofObligation location
        (Declaration.acceptScopedKernelDischarge Declaration.KernelStructuralComposition facts
            (Vector.fromList (preparedDischargeGoal <$> toList children)) goal derivation)

executeRecursiveEquation
    :: Location -> Recursive.RecursiveApplication -> PreparedDischarge -> KernelDerivation ObjectId
    -> Declaration.CandidateProof ()
executeRecursiveEquation location application child derivation = do
    unless (preparedDischargeGoal child == Recursive.applicationGuard application)
        (impossible "a recursive application changed its proved guard")
    let target = Recursive.applicationEquality application
        call = case splitScopedEquality target of
            Just (_,left,_) -> left
            Nothing -> impossible "an admitted recursive application lost its equality"
    Declaration.locateProofObligation location
        (Declaration.acceptScopedRecursiveEquation (Recursive.applicationBinding application)
            call (preparedDischargeGoal child) target derivation)

-- This transient use check follows independently replayed hypothesis indices.
-- Guard subproofs contribute their local dependencies, never definition credit.
executeDefinitionDischarge :: PreparedDischarge -> Declaration.CandidateProof (Set Natural, Bool)
executeDefinitionDischarge = \case
    PreparedDefinitionDischarge child -> do
        result@(_,used) <- executeDefinitionDischarge child
        unless used (Error.throwError_ Declaration.KernelDefinitionEvidenceMissing)
        pure result
    PreparedRecursiveEquation location application child derivation -> do
        (locals,_) <- executeDefinitionDischarge child
        executeRecursiveEquation location application child derivation
        pure (locals,True)
    PreparedPreparationLimit statistics child ->
        Declaration.notePreparationExhaustion statistics (executeDefinitionDischarge child)
    PreparedFormationDischarge completion child ->
        Declaration.completeFormationCandidate completion (executeDefinitionDischarge child)
    PreparedEqualityDischarge _ goal local equation child -> do
        unless (preparedLocalProposition local == preparedDischargeGoal equation
            && splitScopedEquality (preparedDischargeGoal equation) == Just (TyProp,goal,preparedDischargeGoal child))
            (impossible "an audited goal rewrite changed its checked equality")
        equality <- executeDefinitionDischarge equation
        result <- executeDefinitionDischarge child
        pure (combine equality result)
    PreparedEvidenceDischarge _ goal local evidence child -> do
        unless (preparedLocalProposition local == preparedDischargeGoal evidence && goal == preparedDischargeGoal child)
            (impossible "an audited local continuation changed its proved premise")
        source <- executeDefinitionDischarge evidence
        (locals,used) <- executeDefinitionDischarge child
        let ordinal = preparedLocalOrdinalValue local
        pure (if ordinal `Set.member` locals
            then combine source (Set.delete ordinal locals,used) else (locals,used))
    PreparedUniversalDischarge _ goal ty _ child -> do
        validateUniversalDischarge goal ty (preparedDischargeGoal child)
        executeDefinitionDischarge child
    PreparedImplicationDischarge _ goal local child -> do
        validateImplicationDischarge goal (preparedLocalProposition local) (preparedDischargeGoal child)
        (locals,used) <- executeDefinitionDischarge child
        pure (Set.delete (preparedLocalOrdinalValue local) locals,used)
    PreparedKernelDischarge location method goal locals facts derivation -> do
        usage <- executeKernelDischarge location method goal locals facts derivation
        let usedLocals = Set.fromList [preparedLocalOrdinalValue local
                | (index,local) <- zip [0..] locals
                , hypothesisIx index `Set.member` Declaration.scopedKernelExternalHypothesisUses usage]
            definitions = Set.fromList [hypothesisIx index | (index,PreparedLocal _ origin _ _) <- zip [0..] locals
                , origin `elem` [ProofLocalDefinition,ProofLocalConstructionExtensional,ProofLocalConstructionEquation]]
        used <- Declaration.scopedKernelUsesCanonicalDefinition facts definitions usage
        pure (usedLocals,used)
    PreparedKernelComposition location goal facts children derivation -> do
        results <- traverse executeDefinitionDischarge children
        usage <- executeKernelComposition location goal facts children derivation
        pure (foldl' combine (Set.empty,False) [result | (index,result) <- zip [0..] (toList results)
            , hypothesisIx index `Set.member` Declaration.scopedKernelExternalHypothesisUses usage])
    PreparedExcludedMiddle{} -> pure (Set.empty,False)
    PreparedVampireDischarge{} -> impossible "a composed definition proof invoked ATP"
  where
    combine (left,a) (right,b) = (left <> right,a || b)

-- These are the same exact checked openings used by source Fix and Assume.
-- The private discharge constructors retain them through planning and execution.
validateUniversalDischarge
    :: Monad m => ScopedCheckedCore ObjectId -> CoreType -> ScopedCheckedCore ObjectId -> m ()
validateUniversalDischarge goal binderType body =
    unless (openScopedForall goal == Just (binderType, body))
        (impossible "a prepared universal introduction changed its scoped body")

validateImplicationDischarge
    :: Monad m => ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId -> m ()
validateImplicationDischarge goal premise body =
    unless (openScopedImplication goal == Just (premise, body))
        (impossible "a prepared implication introduction changed its premise or body")

preparedLocalProposition
    :: PreparedLocal
    -> ScopedCheckedCore ObjectId
preparedLocalProposition
        (PreparedLocal _ordinal _origin _support proposition) =
    proposition

-- Active proof locals retain the support at which they were introduced.
-- Kernel replay uses one exact lexical context, so weaken each still-active
-- local across the newer nearest binders while preserving its source ordinal
-- and origin.
alignPreparedLocals
    :: Elaboration.ElaborationContext
    -> [PreparedLocal]
    -> Prepare [PreparedLocal]
alignPreparedLocals context =
    traverse align
  where
    currentSupport = Elaboration.elaborationContextSupport context
    current = Vector.toList currentSupport

    align (PreparedLocal ordinal origin support proposition) = do
        let introduced = Vector.toList support
            addedCount = length current - length introduced
        unless
            ( addedCount >= 0
              && drop addedCount current == introduced
              && scopedCoreContext proposition == (snd <$> introduced)
            )
            (impossible "an active proof local is not a prefix-scope ancestor")
        let addedNearestFirst = take addedCount current
            weakened =
                foldl'
                    (\value (_identity, binderType) ->
                        weakenCheckedScopedCore binderType value)
                    proposition
                    (reverse addedNearestFirst)
        pure
            (PreparedLocal
                ordinal origin currentSupport weakened)

buildExactEvidenceView :: [PreparedLocal] -> ExactEvidenceView
buildExactEvidenceView locals =
    ExactEvidenceView rows buckets
  where
    orderedLocals =
        List.sortOn preparedLocalOrdinalValue locals
    rows = concatMap evidenceRows orderedLocals
    buckets = foldl' insertRow Map.empty rows

    evidenceRows local =
        enumerate [] (preparedLocalProposition local)
      where
        enumerate path proposition =
            EvidenceRow local proposition path
                : case splitScopedConjunction proposition of
                    Nothing -> []
                    Just (left, right) ->
                        enumerate
                            (path <> [EvidenceProjectionLeft])
                            left
                        <> enumerate
                            (path <> [EvidenceProjectionRight])
                            right

    insertRow entries row@(EvidenceRow _local proposition _path) =
        Map.alter
            (Just . maybe (row :| []) (<> (row :| [])))
            proposition
            entries

exactEvidenceRow
    :: ScopedCheckedCore ObjectId
    -> ExactEvidenceView
    -> Maybe EvidenceRow
exactEvidenceRow proposition (ExactEvidenceView _rows buckets) =
    NonEmpty.head <$> Map.lookup proposition buckets

compactEvidenceLocals :: [EvidenceRow] -> [PreparedLocal]
compactEvidenceLocals rows =
    Map.elems
        (Map.fromList
            [ (preparedLocalOrdinalValue local, local)
            | EvidenceRow local _proposition _path <- rows
            ])

preparedLocalOrdinalValue :: PreparedLocal -> Natural
preparedLocalOrdinalValue
        (PreparedLocal ordinal _origin _support _proposition) =
    Backend.localPremiseOrdinalValue ordinal

exactEvidenceProof
    :: KernelProof.ProofContext ObjectId
    -> Map Natural HypothesisIx
    -> EvidenceRow
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
exactEvidenceProof context hypothesisIndices
        (EvidenceRow local expected path) = do
    index <-
        maybe
            (Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "exact evidence lost its selected hypothesis"))
            pure
            (Map.lookup
                (preparedLocalOrdinalValue local)
                hypothesisIndices)
    initial <- KernelProof.indexedHypothesisProof context index
    projected <- foldM project initial path
    unless
        (KernelProof.builtProofStatement projected == expected)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "exact evidence projection produced a different proposition"))
    pure projected
  where
    project proof direction = do
        (_left, _right) <-
            maybe
                (Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "exact evidence projection left conjunction syntax"))
                pure
                (splitScopedConjunction
                    (KernelProof.builtProofStatement proof))
        case direction of
            EvidenceProjectionLeft ->
                KernelProof.conjunctionLeftProof
                    context
                    proof
            EvidenceProjectionRight ->
                KernelProof.conjunctionRightProof
                    context
                    proof

encodePreparedProof :: PreparedProofTree -> ByteString
encodePreparedProof =
    encodeCache . putPreparedProof

putPreparedProof :: PreparedProofTree -> CachePut
putPreparedProof = \case
    PreparedImplicitDischarge discharge -> do
        putCacheTag 0x00
        putPreparedDischarge discharge
    PreparedQed discharge -> do
        putCacheTag 0x01
        putPreparedDischarge discharge
    PreparedOmitted _location goal -> do
        putCacheTag 0x06
        putScopedProposition goal
    PreparedFix identities continuation -> do
        putCacheTag 0x02
        putCacheList
            (putCacheNatural . Elaboration.localIdValue)
            identities
        putPreparedProof continuation
    PreparedAssume opening continuation -> do
        putCacheTag 0x03
        putPreparedAssumptionOpening opening
        putPreparedProof continuation
    PreparedGuardAssume _guard continuation -> do
        putCacheTag 0x12
        putScopedProposition _guard
        putPreparedProof continuation
    PreparedTake identities witness discharge continuation -> do
        putCacheTag 0x08
        putCacheList
            (putCacheNatural . Elaboration.localIdValue)
            identities
        putScopedProposition witness
        putPreparedDischarge discharge
        putPreparedProof continuation
    PreparedSetInduction
            (PreparedCheckedSetInduction
                focus property antecedents target hypothesis result child) -> do
        putCacheTag 0x07
        putPreparedSetInductionFocus focus
        putScopedProposition property
        putCacheList putScopedProposition antecedents
        putScopedProposition target
        putScopedProposition hypothesis
        putScopedProposition result
        putPreparedProof child
    PreparedHave claim discharge continuation -> do
        putCacheTag 0x04
        putScopedProposition claim
        putPreparedDischarge discharge
        putPreparedProof continuation
    PreparedSuffices goal reduction implication discharge continuation -> do
        putCacheTag 0x0c
        putScopedProposition goal
        putScopedProposition reduction
        putScopedProposition implication
        putPreparedDischarge discharge
        putPreparedProof continuation
    PreparedCalculate calculation continuation -> do
        putCacheTag 0x0d
        putPreparedDischarge calculation
        putPreparedProof continuation
    PreparedSince
            sinceProposition premiseDischarge temporaryPremise
            claim claimDischarge continuation -> do
        putCacheTag 0x0e
        putScopedProposition sinceProposition
        putPreparedDischarge premiseDischarge
        putPreparedLocalEvidence temporaryPremise
        putScopedProposition claim
        putPreparedDischarge claimDischarge
        putPreparedProof continuation
    PreparedSubclaim claim subproof continuation -> do
        putCacheTag 0x05
        putScopedProposition claim
        putPreparedProof subproof
        putPreparedProof continuation
    PreparedDefine identity body definitions continuation -> do
        putCacheTag 0x09
        putCacheNatural (Elaboration.localIdValue identity)
        putScopedTerm body
        putCacheList putScopedProposition (toList definitions)
        putPreparedProof continuation
    PreparedDefineRelational
            identity body functionality definitions continuation -> do
        putCacheTag 0x11
        putCacheNatural (Elaboration.localIdValue identity)
        putScopedTerm body
        putPreparedDischarge functionality
        putCacheList putScopedProposition (toList definitions)
        putPreparedProof continuation
    PreparedByCase caseAnalysis -> do
        putCacheTag 0x0f
        putPreparedCaseAnalysis caseAnalysis
    PreparedByContradiction goal negation falsum child -> do
        putCacheTag 0x10
        putScopedProposition goal
        putScopedProposition negation
        putScopedProposition falsum
        putPreparedProof child
    PreparedContradiction goal falsum discharge -> do
        putCacheTag 0x0a
        putScopedProposition goal
        putScopedProposition falsum
        putPreparedDischarge discharge
    PreparedDefineFunction identity graph definition continuation -> do
        putCacheTag 0x0b
        putCacheNatural (Elaboration.localIdValue identity)
        putScopedTerm graph
        putScopedProposition definition
        putPreparedProof continuation

putPreparedAssumptionOpening
    :: LooseDeduction.AssumptionOpening ObjectId
    -> CachePut
putPreparedAssumptionOpening opening = do
    putCacheTag
        (case LooseDeduction.assumptionOpeningKind opening of
            LooseDeduction.DirectImplicationOpening -> 0x00
            LooseDeduction.DirectNegationOpening -> 0x01
            LooseDeduction.ClassicalDisjunctionOpening -> 0x02
            LooseDeduction.ConjunctiveFrontierOpening -> 0x03)
    putScopedProposition
        (LooseDeduction.assumptionOpeningGoal opening)
    putScopedProposition
        (LooseDeduction.assumptionOpeningSupplied opening)
    putScopedProposition
        (LooseDeduction.assumptionOpeningResidual opening)

putPreparedSetInductionFocus
    :: PreparedSetInductionFocus
    -> CachePut
putPreparedSetInductionFocus = \case
    PreparedInitialSetInductionFocus identity index -> do
        putCacheTag 0x00
        putCacheNatural (Elaboration.localIdValue identity)
        putCacheNatural index
    PreparedLeadingSetInductionFocus identity -> do
        putCacheTag 0x01
        putCacheNatural (Elaboration.localIdValue identity)

putPreparedDischarge :: PreparedDischarge -> CachePut
-- Work statistics are an execution sidecar, not proof syntax or authority.
putPreparedDischarge (PreparedDefinitionDischarge child) =
    putCacheTag 0x09 >> putPreparedDischarge child
putPreparedDischarge (PreparedRecursiveEquation _ application child derivation) = do
    putCacheTag 0x0a
    putGlobalBindingRefCache (Recursive.applicationBinding application)
    putScopedProposition (Recursive.applicationEquality application)
    putPreparedDischarge child
    putKernelDerivationCache putObjectIdCache derivation
putPreparedDischarge (PreparedEqualityDischarge _location goal local equation child) = do
    putCacheTag 0x07
    putScopedProposition goal
    putPreparedLocalEvidence local
    putPreparedDischarge equation
    putPreparedDischarge child
putPreparedDischarge (PreparedEvidenceDischarge _location goal local evidence child) = do
    putCacheTag 0x08
    putScopedProposition goal
    putPreparedLocalEvidence local
    putPreparedDischarge evidence
    putPreparedDischarge child
putPreparedDischarge (PreparedUniversalDischarge _location goal binderType identity child) = do
    putCacheTag 0x05
    putScopedProposition goal
    putCoreTypeCache binderType
    putCacheNatural (Elaboration.localIdValue identity)
    putPreparedDischarge child
putPreparedDischarge (PreparedImplicationDischarge _location goal local child) = do
    putCacheTag 0x06
    putScopedProposition goal
    putPreparedLocalEvidence local
    putPreparedDischarge child
putPreparedDischarge (PreparedFormationDischarge _completion discharge) =
    putPreparedDischarge discharge
putPreparedDischarge (PreparedPreparationLimit _statistics discharge) =
    putPreparedDischarge discharge
putPreparedDischarge
        (PreparedVampireDischarge
            _location justification goal _obligation) = do
    putCacheTag 0x00
    putPreparedDischargeSyntax justification goal
putPreparedDischarge
        (PreparedExcludedMiddle _location goal) = do
    putCacheTag 0x02
    putScopedProposition goal
putPreparedDischarge
        (PreparedKernelDischarge
            _location method goal locals facts derivation) = do
    putCacheTag 0x03
    putPreparedJustification method
    putScopedProposition goal
    putCacheList putPreparedLocalEvidence locals
    putCacheList putSemanticFactOccurrenceFingerprintCache facts
    putKernelDerivationCache putObjectIdCache derivation
putPreparedDischarge
        (PreparedKernelComposition _location goal facts children derivation) = do
    putCacheTag 0x04
    putScopedProposition goal
    putCacheList putSemanticFactOccurrenceFingerprintCache facts
    putCacheList putPreparedDischarge (toList children)
    putKernelDerivationCache putObjectIdCache derivation

putPreparedDischargeSyntax
    :: PreparedJustification
    -> ScopedCheckedCore ObjectId
    -> CachePut
putPreparedDischargeSyntax justification goal = do
    putPreparedJustification justification
    putScopedProposition goal

putPreparedCaseAnalysis :: PreparedCaseAnalysis -> CachePut
putPreparedCaseAnalysis
        (PreparedCaseAnalysis goal cases exhaustive discharge) = do
    putScopedProposition goal
    putCacheList putPreparedCase (toList cases)
    putScopedProposition exhaustive
    putPreparedDischarge discharge

putPreparedCase :: PreparedCase -> CachePut
putPreparedCase (PreparedCase assumption proof) = do
    putScopedProposition assumption
    putPreparedProof proof

putPreparedLocalEvidence :: PreparedLocal -> CachePut
putPreparedLocalEvidence
        (PreparedLocal ordinal origin support proposition) = do
    putCacheNatural (Backend.localPremiseOrdinalValue ordinal)
    putProofLocalOrigin origin
    putCacheList
        (\(identity, coreType) -> do
            putCacheNatural (Elaboration.localIdValue identity)
            putCoreTypeCache coreType)
        (Vector.toList support)
    putScopedProposition proposition

putProofLocalOrigin :: ProofLocalOrigin -> CachePut
putProofLocalOrigin = \case
    ProofAssumption ->
        putCacheTag 0x00
    ProofDerivedClaim ->
        putCacheTag 0x01
    ProofLocalDefinition ->
        putCacheTag 0x02
    ProofLocalConstructionExtensional ->
        putCacheTag 0x03
    ProofLocalConstructionEquation ->
        putCacheTag 0x04

implicitProofSyntaxId
    :: ScopedCheckedCore ObjectId
    -> ProofSyntaxId
implicitProofSyntaxId goal =
    proofSyntaxId
        (encodeCache do
            putCacheTag 0x00
            putPreparedDischargeSyntax PreparedImplicitObvious goal)

putPreparedJustification :: PreparedJustification -> CachePut
putPreparedJustification = \case
    PreparedInternalAuto ->
        putCacheTag 0x00
    PreparedAuto Nothing ->
        putCacheTag 0x05
    PreparedAuto fingerprints@(Just _) -> do
        putCacheTag 0x01
        putPreparedReferenceSelection fingerprints
    PreparedImplicitObvious ->
        putCacheTag 0x02
    PreparedObviousReferences fingerprints -> do
        putCacheTag 0x06
        putCacheList
            putSemanticFactOccurrenceFingerprintCache
            (toList fingerprints)
    PreparedAssumption ->
        putCacheTag 0x03
    PreparedDefinition ->
        putCacheTag 0x04
    PreparedNotion ->
        putCacheTag 0x07
    PreparedSetExtensionality ->
        putCacheTag 0x08
    PreparedRecordExtensionality ->
        putCacheTag 0x09

putPreparedReferenceSelection
    :: Maybe (NonEmpty SemanticFactOccurrenceFingerprint)
    -> CachePut
putPreparedReferenceSelection =
    putCacheMaybe
        (putCacheList
            putSemanticFactOccurrenceFingerprintCache
            . toList)

putScopedProposition
    :: ScopedCheckedCore ObjectId
    -> CachePut
putScopedProposition proposition = do
    putCacheList putCoreTypeCache
        (scopedCoreContext proposition)
    putCanonicalTermCache putObjectIdCache
        (scopedCoreTerm proposition)

putScopedTerm
    :: ScopedCheckedCore ObjectId
    -> CachePut
putScopedTerm term = do
    putCacheList putCoreTypeCache
        (scopedCoreContext term)
    putCoreTypeCache (scopedCoreType term)
    putCanonicalTermCache putObjectIdCache
        (scopedCoreTerm term)

proofLocation :: Location -> Raw.Proof -> Location
proofLocation fallback = \case
    Raw.Omitted location -> location
    Raw.Qed maybeLocation _justification ->
        fromMaybe fallback maybeLocation
    Raw.Contradiction location _justification -> location
    Raw.ByCase location _cases -> location
    Raw.ByContradiction location _proof -> location
    Raw.BySetInduction location _term _proof -> location
    Raw.ByStructuralInduction location _variable _cases -> location
    Raw.ByOrdInduction location _proof -> location
    Raw.Assume location _intro _statement _proof -> location
    Raw.Fix location _binders _condition _proof -> location
    Raw.Calc location _quantifier _calculation _proof -> location
    Raw.TakeVar location _variables _bound _statement _justification _proof ->
        location
    Raw.TakeTyped
            location _variables _coreType _statement _justification _proof ->
        location
    Raw.TakeNoun location _noun _justification _proof -> location
    Raw.Have location _intro _statement _justification _proof -> location
    Raw.Since location _premise _premiseJustification
            _claimLocation _claim _claimJustification _proof ->
        location
    Raw.Suffices location _statement _justification _proof -> location
    Raw.Subclaim location _statement _subproof _proof -> location
    Raw.Define location _variable _expression _proof -> location
    Raw.DefineTyped location _variable _coreType _expression _proof -> location
    Raw.DefineFunction location _function _argument _value _bound _domain _proof ->
        location
    Raw.DefineFunctionLocal
            location _function _argument _value _bound _target _rules _proof ->
        location

throwProof :: ProofError -> Prepare value
throwProof = throwProofForGoal Nothing

throwProofForGoal :: Maybe (ScopedCheckedCore ObjectId) -> ProofError -> Prepare value
throwProofForGoal goal failure = do
    obligations <- Reader.asks prepareRecordObligations
    Trans.lift . State.lift . Except.throwError $
        if null obligations then failure
        else ProofRecordObligations (Obligation.obligationContext goal obligations) failure

liftDriver
    :: Declaration.LoweringDriver value
    -> Prepare value
liftDriver =
    Trans.lift . State.lift . Trans.lift

stableUnique :: Ord value => [value] -> [value]
stableUnique =
    reverse . snd
        . foldl'
            (\(seen, reversed) value ->
                if value `Set.member` seen
                    then (seen, reversed)
                    else
                        ( Set.insert value seen
                        , value : reversed
                        ))
            (Set.empty, [])
