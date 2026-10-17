{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}

-- | Small deterministic source-level proof search.  Every success is built
-- from kernel proof combinators and must still pass independent replay.
module Felix.Checking.Obvious.Driver
    ( ObviousImport
    , obviousImport
    , obviousImportIndex
    , obviousImportStatement
    , ObviousDefinitionView
    , obviousImportedDefinitionView
    , obviousLocalDefinitionView
    , ObviousProof
    , obviousBuiltProof
    , obviousUsedImports
    , ProofRequirement(..)
    , ObviousFailure(..)
    , ObviousMalformedRequest(..)
    , ObviousBudget(..)
    , ObviousLimit(..)
    , defaultObviousBudget
    , ObviousAllowance
    , obviousAllowance
    , obviousRemainingBudget
    , debitObviousConversion
    , obviousProofReportWithin
    , obviousInitialProofReportWithin
    , ObviousTierOutcome(..)
    , ObviousStatistics
    , obviousEffectiveBudget
    , ObviousBreadthObservation(..)
    , obviousBreadthObservations
    , obviousFocusedTierOutcome
    , obviousRefutationTierOutcome
    , obviousFocusedWorkConsumed
    , obviousRefutationWorkConsumed
    , obviousConversionWorkConsumed
    , obviousBranchNodesCreated
    , obviousTermsAdmitted
    , obviousSignedFormulasAdmitted
    , obviousEqualityEventsProcessed
    , obviousRuleInstancesAdmitted
    , obviousFactDomainsStarted
    , obviousFactDomainsDeferred
    , ObviousRunReport
    , ObviousFailureReport
    , ObviousFailureClass(..)
    , ObviousFailurePath(..)
    , ObviousRefutationSkipReason(..)
    , ObviousFocusedGoalView(..)
    , ObviousInputObservation(..)
    , ObviousDefinitionSource(..)
    , CandidateCoverage(..)
    , CandidateOutcome(..)
    , MismatchClass(..)
    , IncompleteReason(..)
    , CandidateBaseSource(..)
    , CandidateComparisonView(..)
    , CandidateRootGoalView(..)
    , CandidateDefinitionParticipation(..)
    , CandidateDifferenceStep(..)
    , CandidateStructuralDifference(..)
    , ObviousAuxiliaryObligationKind(..)
    , CandidateAuxiliaryCause(..)
    , ObviousCandidateObservation(..)
    , ObviousCoreSummary(..)
    , ObviousTypeSummary(..)
    , ObviousTermSummary(..)
    , obviousRunStatistics
    , obviousRunResult
    , obviousRunFailure
    , obviousFailureFinal
    , obviousFailureClass
    , obviousFailureStatistics
    , obviousFailurePrimaryClass
    , obviousFailurePath
    , obviousFailureCheckedGoal
    , obviousFailureFocusedGoalView
    , obviousFailureHypotheses
    , obviousFailureHypothesisCount
    , obviousFailureImports
    , obviousFailureImportCount
    , obviousFailureLocalDefinitionViews
    , obviousFailureLocalDefinitionViewCount
    , obviousFailureImportedDefinitionViews
    , obviousFailureImportedDefinitionViewCount
    , obviousFailureCandidateCoverage
    , obviousFailureCandidates
    , obviousFailureRootRequirementRejections
    , obviousFailureAuxiliaryCauses
    , obviousFailureAdditionalAuxiliaryCauseCount
    , obviousProof
    , obviousProofWithRequirement
    , obviousProofDetailed
    , obviousProofReport
    , SearchPolicy(..)
    , productionSearchPolicy
    , disabledSearchPolicy
    , obviousProofReportWithPolicy
    , WitnessPolicy(..)
    , PremiseQueryPolicy(..)
    , UniversalPolicy(..)
    , obviousWitnessAttempts
    , obviousWitnessesDeferred
    , ExistentialPolicy(..)
    , obviousExistentialOpenings
    , obviousExistentialsDeferred
    , ExtensionalityPolicy(..)
    , EndpointPolicy(..)
    , obviousEndpointGuardWaits
    , obviousExtensionalityAttempts
    , obviousExtensionalityDeferred
    , obviousPremiseQueriesStarted
    , obviousPremiseQueriesDeferred
    , obviousUniversalAttempts
    , obviousUniversalHintSteps
    , obviousUniversalsDeferred
    , obviousPendingFactDomainOpportunities
    , obviousScopeInventory
    , ScopeId
    , Evidence
    , evidenceProof
    , evidenceUses
    , Scoped
    , runScoped
    , GroundAllowance(..)
    , scopeContext
    , scopeAssume
    , scopeBind
    , scopeHypothesis
    , scopeImported
    , scopeApplyEquality
    , scopeIntroduceImplication
    , scopeIntroduceForall
    , scopeAt
    , scopeRequireStatement
    , scopeMatchTemplate
    , scopeReconstructFunctionEquality
    , scopeReconstructBooleanEquality
    , scopeDirectionalInventories
    , scopeDirectionalGroundProof
    , scopeBooleanBodyHandoff
    , scopeConsumerDelivery
    , BooleanBodyHandoff(..)
    , TemplateMatchResult(..)
    , scopeRefute
    , GroundQuery
    , GroundDomain
    , GroundQueryProgress(..)
    , scopeStartGround
    , scopeGroundDomain
    , scopeStartGroundInDomain
    , scopeAdvanceGround
    , scopeResumeGround
    , advanceOwnedGround
    , currentGroundLimits
    , FocusedObligationId(..)
    , focusedOwnerDemanded
    , FocusedProducerKey(..)
    , FocusedPhase(..)
    , FocusedConsumerRole(..)
    , countedFocusedDrivingRequirement
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Elimination qualified as Elimination
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.Semantics qualified as KernelSemantics
    (KernelSemanticsError(KernelScopedInstantiationFailed))
import Felix.Checking.Obvious.Conversion qualified as Effort
import Felix.Checking.Obvious.Conversion
    (ObviousConversionLimitOwner(..), ObviousConversionRunError(..), PreparationResult(..), runObviousConversion)
import Felix.Checking.Obvious.Choice qualified as Choice
import Felix.Checking.Obvious.Refutation qualified as Refutation
import Felix.Checking.Obvious.Refutation (UniversalPolicy(..))
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template
import Felix.Checking.Semantic (DefinitionViewKind(..))

import Control.Monad (foldM, unless, when)
import Data.Graph qualified as Graph
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Data.Bifunctor (first, second)
import Data.Map.Strict qualified as Map
import Data.List (filter, partition)
import Data.Maybe (catMaybes, mapMaybe)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word)
import Numeric.Natural (Natural)


data ObviousImport global = ObviousImport
    !ImportIx
    !(FrozenCheckedCore global)

type role ObviousImport nominal

obviousImport
    :: ImportIx
    -> FrozenCheckedCore global
    -> ObviousImport global
obviousImport =
    ObviousImport

obviousImportIndex :: ObviousImport global -> ImportIx
obviousImportIndex (ObviousImport index _statement) =
    index

obviousImportStatement
    :: ObviousImport global
    -> FrozenCheckedCore global
obviousImportStatement (ObviousImport _index statement) =
    statement

-- | One checked canonical definition view.  Imported views name their object
-- directly.  Proof-local views retain the exact external hypothesis position;
-- their bound subject is recovered after each logical or binder introduction.
data ObviousDefinitionView global
    = ObviousImportedDefinitionView
        !global
        !DefinitionViewKind
        !(ObviousImport global)
    | ObviousLocalDefinitionView
        !Natural
        !DefinitionViewKind

type role ObviousDefinitionView nominal

obviousImportedDefinitionView
    :: global
    -> DefinitionViewKind
    -> ObviousImport global
    -> ObviousDefinitionView global
obviousImportedDefinitionView =
    ObviousImportedDefinitionView

obviousLocalDefinitionView
    :: Natural
    -> DefinitionViewKind
    -> ObviousDefinitionView global
obviousLocalDefinitionView =
    ObviousLocalDefinitionView

-- | Search-only evidence used to choose among logically valid candidates.
-- Kernel replay independently reconstructs the authoritative dependency set.
data CandidateDependencies = CandidateDependencies
    { candidateImports :: !(Set ImportIx)
    , candidateCanonicalSource :: !(Maybe CanonicalSource)
    }

-- Sources belong to the original request, not to an introduced branch. A local
-- index therefore survives checked weakening and discharge without acquiring the
-- identity of a new assumption. Imported witnesses retain the registered view's
-- occurrence as well as its immutable import association.
data CanonicalSource
    = CanonicalImportedSource !Natural !ImportIx
    | CanonicalHypothesisSource !Natural

candidateUsesCanonicalDefinition :: CandidateDependencies -> Bool
candidateUsesCanonicalDefinition = isJust . candidateCanonicalSource

emptyCandidateDependencies :: CandidateDependencies
emptyCandidateDependencies =
    CandidateDependencies Set.empty Nothing

importDependencies :: ImportIx -> CandidateDependencies
importDependencies index =
    emptyCandidateDependencies
        {candidateImports = Set.singleton index}

canonicalImportDependencies :: Natural -> ImportIx -> CandidateDependencies
canonicalImportDependencies ordinal index =
    (importDependencies index)
        {candidateCanonicalSource = Just (CanonicalImportedSource ordinal index)}

canonicalHypothesisDependencies :: Natural -> CandidateDependencies
canonicalHypothesisDependencies index =
    emptyCandidateDependencies
        {candidateCanonicalSource = Just (CanonicalHypothesisSource index)}

data FocusedSourceKey
    = FocusedSourceKey !Int !Int
    | FocusedDerivedSourceKey !Int
    deriving stock (Show, Eq, Ord)

data CandidateSourceAnnotation = CandidateSourceAnnotation
    !CandidateBaseSource
    !Natural
    !Natural
    ![Natural]
    !Bool

data ObviousProof global = ObviousProofPayload
    { proofBuilt :: !(KernelProof.BuiltProof global)
    , obviousProofDependencies :: !CandidateDependencies
    , obviousProofSourceKey :: !(Maybe FocusedSourceKey)
    , obviousProofCandidateSource :: !(Maybe CandidateSourceAnnotation)
    , obviousProofCandidateCompletion :: !(Maybe (CandidateCompletion global))
    , obviousProofObligation :: !(Maybe FocusedObligationId)
    , obviousProofCertification :: !(Maybe (FocusedContextId, KernelSourceUses))
    }

type role ObviousProof nominal

pattern ObviousProof
    :: KernelProof.BuiltProof global
    -> CandidateDependencies
    -> ObviousProof global
pattern ObviousProof proof dependencies <-
    ObviousProofPayload {proofBuilt = proof, obviousProofDependencies = dependencies}
  where
    ObviousProof proof dependencies =
        ObviousProofPayload proof dependencies Nothing Nothing Nothing Nothing Nothing

{-# COMPLETE ObviousProof #-}

withFocusedSourceKey :: FocusedSourceKey -> ObviousProof global -> ObviousProof global
withFocusedSourceKey sourceKey proof = proof {obviousProofSourceKey = Just sourceKey}

withCandidateSource :: CandidateSourceAnnotation -> ObviousProof global -> ObviousProof global
withCandidateSource candidateSource proof = proof {obviousProofCandidateSource = Just candidateSource}

withCandidateCompletion :: CandidateCompletion global -> ObviousProof global -> ObviousProof global
withCandidateCompletion completion proof = proof {obviousProofCandidateCompletion = Just completion}

deriveCandidateProof :: KernelProof.BuiltProof global -> ObviousProof global -> ObviousProof global
deriveCandidateProof built source = source
    { proofBuilt = built, obviousProofSourceKey = Nothing
    , obviousProofCandidateCompletion = Nothing, obviousProofObligation = Nothing
    , obviousProofCertification = Nothing }

withoutCandidateEvidence :: ObviousProof global -> ObviousProof global
withoutCandidateEvidence proof = proof
    { obviousProofCandidateSource = Nothing, obviousProofCandidateCompletion = Nothing
    , obviousProofObligation = Nothing, obviousProofCertification = Nothing }

obviousUsedImports :: ObviousProof global -> Set ImportIx
obviousUsedImports = candidateImports . obviousProofDependencies

obviousBuiltProof :: ObviousProof global -> KernelProof.BuiltProof global
obviousBuiltProof = proofBuilt

data ProofRequirement
    = AnyObviousProof
    | MustUseCanonicalDefinition
    deriving stock (Show, Eq, Ord)

data ObviousFailure global
    = ObviousNoMatchingConclusion !(ScopedCheckedCore global)
    | ObviousAntecedentUnavailable !(ScopedCheckedCore global)
    | ObviousUndeterminedParameter !Natural
    | ObviousFalsityPairUnavailable
    | ObviousUnsupportedHigherOrderInstantiation
    | ObviousUnsupportedTermOutsideUniverse
    | ObviousCanonicalDefinitionEvidenceRequired
    | ObviousRefutationSaturated
    | ObviousResourceExhausted !ObviousLimit
    | ObviousMalformedInput !ObviousMalformedRequest
    | ObviousRepeatedState !(ScopedCheckedCore global)
    | ObviousIntegrityFailure !KernelProof.KernelProofBuildError
    | ObviousConversionFailed !Conversion.ConversionFailure
    | ObviousRequiredConversionNotConvertible
    | ObviousConversionAccountingInvariant
        !Conversion.ConversionCost !Conversion.ConversionPool
    deriving stock (Show, Eq)

type role ObviousFailure nominal

data ObviousMalformedRequest
    = ObviousLimitExceedsImplementationCapacity
        !ObviousLimit
        !Word
    | ObviousTargetNotPropositional !CoreType
    | ObviousHypothesisMetadataMismatch
    | ObviousImportNotPropositional !ImportIx !CoreType
    | ObviousDuplicateImportIx !ImportIx
    | ObviousConflictingImportStatement !ImportIx
    | ObviousDefinitionViewNotPropositional !ImportIx !CoreType
    | ObviousLocalDefinitionViewOutOfRange !Natural
    deriving stock (Show, Eq)

data ObviousBudget = ObviousBudget
    { obviousFocusedWorkLimit :: !Word
    , obviousRefutationWorkLimit :: !Word
    , obviousConversionPool :: !Conversion.ConversionPool
    , obviousGroundTermLimit :: !Word
    , obviousBranchNodeLimit :: !Word
    , obviousRuleInstanceLimit :: !Word
    , obviousFactDomainLimit :: !Word -- Optional selected-fact variants, shared request-wide.
    }
    deriving stock (Show, Eq)

-- One automatic proof request shares this conversion pool across candidate
-- and premise alternatives. Failed attempts retain their spent work. See
-- benchmark/readme.md#work-budgets for the other limits and measurement history.
defaultObviousConversionPool :: Conversion.ConversionPool
defaultObviousConversionPool = Conversion.conversionPool 100000000

defaultObviousBudget :: ObviousBudget
defaultObviousBudget =
    ObviousBudget
        { obviousFocusedWorkLimit = 30000000
        , obviousRefutationWorkLimit = 10000000
        , obviousConversionPool = defaultObviousConversionPool
        , obviousGroundTermLimit = 100000
        , obviousBranchNodeLimit = 4096
        , obviousRuleInstanceLimit = 10000
        , obviousFactDomainLimit = 2
        }

-- Private witness policy. Disabled performs no witness discovery; zero
-- limits in an enabled policy still distinguish a prevented real candidate.
data WitnessPolicy
    = WitnessesDisabled
    | ExistingWitnesses !Word !Word -- per-obligation prefix, request attempts
    deriving stock (Show, Eq)

-- Only already-owned domains can service these queries.
data PremiseQueryPolicy
    = PremiseQueriesDisabled
    | ExistingPremiseQueries !Word
    deriving stock (Show, Eq)

data ExistentialPolicy
    = ExistentialsDisabled
    | SuppliedExistentials !Word
    deriving stock (Show, Eq, Ord)

-- One selected application owns both pointwise directions.
data ExtensionalityPolicy
    = ExtensionalityDisabled
    | MembershipExtensionality !Word
    deriving stock (Show, Eq)

data ObviousLimit
    = ObviousFocusedWorkLimit
    | ObviousRefutationWorkLimit
    | ObviousConversionOperationLimit
    | ObviousConversionPoolLimit
    | ObviousGroundTermLimit
    | ObviousBranchNodeLimit
    | ObviousRuleInstanceLimit
    deriving stock (Show, Eq, Ord)

data ObviousTierOutcome
    = ObviousTierNotStarted
    | ObviousTierNotCompleted
    | ObviousTierCandidateBuilt
    | ObviousTierNoProof
    | ObviousTierUnsupported
    | ObviousTierResourceExhausted !ObviousLimit
    | ObviousTierIntegrityFailure
    deriving stock (Show, Eq, Ord)

-- | Read-only request observations. Each search row contains its effective
-- request cap, actual starts/attempts and whether a further candidate was
-- prevented. Witnesses also carry the per-obligation cap first. Disabled
-- producers have no row. Hint effort never removes fallback candidates.
data ObviousBreadthObservation
    = ObviousFactDomainBreadth !Word !Word !Bool
    | ObviousWitnessBreadth !Word !Word !Word !Bool
    | ObviousPremiseQueryBreadth !Word !Word !Bool
    | ObviousUniversalBreadth !Word !Word !Bool
    | ObviousUniversalHintEffort !Word !Word
    | ObviousExistentialBreadth !Word !Word !Bool
    | ObviousExtensionalityBreadth !Word !Word !Bool
    | ObviousEndpointBreadth !Word !Word !Bool
    deriving stock (Show, Eq)

obviousBreadthObservations :: ObviousStatistics -> [ObviousBreadthObservation]
obviousBreadthObservations = statisticsBreadthObservations

data ObviousStatistics = ObviousStatistics
    { statisticsEffectiveBudget :: !ObviousBudget
    , statisticsBreadthObservations :: ![ObviousBreadthObservation]
    , statisticsFocusedTierOutcome :: !ObviousTierOutcome
    , statisticsRefutationTierOutcome :: !ObviousTierOutcome
    , statisticsFocusedWorkConsumed :: !Word
    , statisticsRefutationWorkConsumed :: !Word
    , statisticsConversionWorkConsumed :: !Word
    , statisticsBranchNodesCreated :: !Word
    , statisticsTermsAdmitted :: !Word
    , statisticsSignedFormulasAdmitted :: !Word
    , statisticsEqualityEventsProcessed :: !Word
    , statisticsRuleInstancesAdmitted :: !Word
    , statisticsFactDomainsStarted :: !Word
    , statisticsFactDomainsDeferred :: !Bool
    , statisticsWitnessAttempts :: !Word
    , statisticsWitnessesDeferred :: !Bool
    , statisticsExistentialOpenings :: !Word
    , statisticsExistentialsDeferred :: !Bool
    , statisticsExtensionalityAttempts :: !Word
    , statisticsExtensionalityDeferred :: !Bool
    , statisticsEndpointAttempts :: !Word
    , statisticsEndpointsDeferred :: !Bool
    , statisticsEndpointGuardWaits :: !Word
    , statisticsPremiseQueriesStarted :: !Word
    , statisticsPremiseQueriesDeferred :: !Bool
    , statisticsUniversalAttempts :: !Word
    , statisticsUniversalHintSteps :: !Word
    , statisticsUniversalsDeferred :: !Bool
    , statisticsPendingFactDomainOpportunities :: !Word
    , statisticsScopeInventory :: !(Int, Int)
    }
    deriving stock (Show, Eq)

-- Private bridge observation of already-owned state, not inference counters.
-- The public facade does not expose scheduler ownership details.
obviousScopeInventory :: ObviousStatistics -> (Int, Int)
obviousScopeInventory = statisticsScopeInventory

-- | One bounded, checked-Core snapshot. The context list and syntax tree carry
-- explicit truncation markers and never retain omitted subtrees.
data ObviousCoreSummary global = ObviousCoreSummary
    ![ObviousTypeSummary]
    !Bool
    !ObviousTypeSummary
    !(ObviousTermSummary global)
    deriving stock (Show, Eq)

type role ObviousCoreSummary nominal

data ObviousTypeSummary
    = ObviousTypeProposition
    | ObviousTypeSet
    | ObviousTypeArrow !ObviousTypeSummary !ObviousTypeSummary
    | ObviousTypeTruncated
    deriving stock (Show, Eq)

data ObviousTermSummary global
    = ObviousBoundVariable !Natural
    | ObviousGlobal !global
    | ObviousGlobalTruncated
    | ObviousIntrinsic !CoreIntrinsicTag
    | ObviousLogicalSelection !ObviousTypeSummary
    | ObviousOpaqueInteger !Text !Bool
    | ObviousApplication
        !(ObviousTermSummary global)
        !(ObviousTermSummary global)
    | ObviousLambda !ObviousTypeSummary !(ObviousTermSummary global)
    | ObviousFalsum
    | ObviousTruth
    | ObviousNegation !(ObviousTermSummary global)
    | ObviousConjunction
        !(ObviousTermSummary global)
        !(ObviousTermSummary global)
    | ObviousDisjunction
        !(ObviousTermSummary global)
        !(ObviousTermSummary global)
    | ObviousImplication
        !(ObviousTermSummary global)
        !(ObviousTermSummary global)
    | ObviousEquality
        !ObviousTypeSummary
        !(ObviousTermSummary global)
        !(ObviousTermSummary global)
    | ObviousUniversal !ObviousTypeSummary !(ObviousTermSummary global)
    | ObviousExistential !ObviousTypeSummary !(ObviousTermSummary global)
    | ObviousTermTruncated
    deriving stock (Show, Eq)

type role ObviousTermSummary nominal

data ObviousFailureClass
    = ObviousNoMatchClass
    | ObviousAntecedentUnavailableClass
    | ObviousParameterUndeterminedClass
    | ObviousFalsityPairUnavailableClass
    | ObviousHigherOrderUnsupportedClass
    | ObviousTermOutsideUniverseClass
    | ObviousDefinitionEvidenceRequiredClass
    | ObviousSaturatedClass
    | ObviousResourceExhaustedClass !ObviousLimit
    | ObviousRepeatedStateClass
    | ObviousMalformedClass
    | ObviousIntegrityClass
    deriving stock (Show, Eq, Ord)

data ObviousRefutationSkipReason
    = ObviousRefutationQueryNotStarted
    deriving stock (Show, Eq, Ord)

data ObviousFailurePath global
    = ObviousValidationFailure
    | ObviousFocusedOnlyFailure !ObviousRefutationSkipReason
    | ObviousCoordinatedFailure
    deriving stock (Show, Eq)

type role ObviousFailurePath nominal

data ObviousFocusedGoalView global
    = ObviousFocusedViewUnavailable
    | ObviousFocusedExposureFailed !ObviousFailureClass
    | ObviousFocusedViewRetained
    | ObviousFocusedViewChanged !(ObviousCoreSummary global)
    deriving stock (Show, Eq)

type role ObviousFocusedGoalView nominal

data ObviousDefinitionSource
    = ObviousDefinitionFromHypothesis !Natural
    | ObviousDefinitionFromImport !ImportIx
    deriving stock (Show, Eq, Ord)

data ObviousInputObservation global
    = ObviousHypothesisObservation
        !Natural
        !(ObviousCoreSummary global)
    | ObviousImportObservation
        !ImportIx
        !(ObviousCoreSummary global)
    | ObviousDefinitionObservation
        !Natural
        !DefinitionViewKind
        !ObviousDefinitionSource
        !(Maybe (ObviousCoreSummary global))
    deriving stock (Show, Eq)

type role ObviousInputObservation nominal

data CandidateCoverage
    = CandidateObservationNotStarted
    | CandidateObservationFinished
    | CandidateObservationStoppedEarly
    deriving stock (Show, Eq, Ord)

data MismatchClass
    = SyntacticMismatch
    | ConversionMismatch
    | BinderMismatch
    | MismatchDetailUnavailable
    deriving stock (Show, Eq, Ord)

data IncompleteReason
    = ParameterUndetermined
    | AntecedentUnavailable
    | TransportPremiseUnavailable
    deriving stock (Show, Eq, Ord)

data CandidateOutcome
    = ComparisonRejected !MismatchClass
    | ProofIncomplete !IncompleteReason
    | ProofRejectedByRequirement
    deriving stock (Show, Eq, Ord)

data CandidateBaseSource
    = CandidateHypothesis !Natural
    | CandidateImport !ImportIx
    deriving stock (Show, Eq, Ord)

data CandidateComparisonView
    = CandidateDirectView
    | CandidateProjectedView !Natural
    | CandidatePreparedTheoremView !Natural
    | CandidateEqualityTransportView !Natural
    deriving stock (Show, Eq, Ord)

data CandidateRootGoalView
    = CandidateOriginalGoalView
    | CandidateDefinitionGoalView ![Natural] !Bool
    deriving stock (Show, Eq, Ord)

data CandidateDefinitionParticipation
    = CandidateNoDefinitionParticipation
    | CandidateFactDefinitionParticipation ![Natural] !Bool
    | CandidateGoalDefinitionParticipation ![Natural] !Bool
    | CandidateFactAndGoalDefinitionParticipation
        ![Natural] !Bool ![Natural] !Bool
    deriving stock (Show, Eq, Ord)

data CandidateDifferenceStep
    = CandidateFirstChild
    | CandidateSecondChild
    | CandidateBodyChild
    deriving stock (Show, Eq, Ord)

data CandidateStructuralDifference = CandidateStructuralDifference
    ![CandidateDifferenceStep]
    !Bool
    deriving stock (Show, Eq, Ord)

data ObviousAuxiliaryObligationKind
    = AuxiliaryIntroductionComponent
    | AuxiliaryDisjunctionBranch
    | AuxiliaryImplicationBody
    | AuxiliaryNegationBody
    | AuxiliaryUniversalBody
    | AuxiliaryExistentialBranch
    | AuxiliaryTheoremAntecedent
    | AuxiliaryTransportPremise
    deriving stock (Show, Eq, Ord)

data CandidateAuxiliaryCause
    = CandidateAuxiliaryRequirementRejected
        !ObviousAuxiliaryObligationKind
    deriving stock (Show, Eq, Ord)

data ObviousCandidateObservation global = ObviousCandidateObservation
    { obviousCandidateSource :: !CandidateBaseSource
    , obviousCandidateView :: !CandidateComparisonView
    , obviousCandidateRootView :: !CandidateRootGoalView
    , obviousCandidateDefinitionParticipation ::
        !CandidateDefinitionParticipation
    , obviousCandidateProposition :: !(ObviousCoreSummary global)
    , obviousCandidateOutcome :: !CandidateOutcome
    , obviousCandidateProgress :: !Natural
    , obviousCandidateStructuralDifference ::
        !(Maybe CandidateStructuralDifference)
    , obviousCandidateAuxiliaryCause :: !(Maybe CandidateAuxiliaryCause)
    }
    deriving stock (Show, Eq)

type role ObviousCandidateObservation nominal

data ObviousRunReport global
    = ObviousRunSucceeded
        !ObviousStatistics
        !(ObviousProof global)
    | ObviousRunFailed
        !(ObviousFailureReport global)

type role ObviousRunReport nominal

data ObviousFailureReport global = ObviousFailureReport
    { obviousFailureStatistics :: !ObviousStatistics
    , obviousFailureFinal :: !(ObviousFailure global)
    , obviousFailurePrimaryClass :: !ObviousFailureClass
    , obviousFailurePath :: !(ObviousFailurePath global)
    , obviousFailureCheckedGoal :: !(ObviousCoreSummary global)
    , obviousFailureFocusedGoalView :: !(ObviousFocusedGoalView global)
    , obviousFailureHypothesisCount :: !Natural
    , obviousFailureHypotheses :: ![ObviousInputObservation global]
    , obviousFailureImportCount :: !Natural
    , obviousFailureImports :: ![ObviousInputObservation global]
    , obviousFailureLocalDefinitionViewCount :: !Natural
    , obviousFailureLocalDefinitionViews :: ![ObviousInputObservation global]
    , obviousFailureImportedDefinitionViewCount :: !Natural
    , obviousFailureImportedDefinitionViews :: ![ObviousInputObservation global]
    , obviousFailureCandidateCoverage :: !CandidateCoverage
    , obviousFailureCandidates :: ![ObviousCandidateObservation global]
    , obviousFailureRootRequirementRejections :: ![CandidateRootGoalView]
    , obviousFailureAuxiliaryCauses :: ![CandidateAuxiliaryCause]
    , obviousFailureAdditionalAuxiliaryCauseCount :: !Natural
    }
    deriving stock (Show, Eq)

type role ObviousFailureReport nominal

obviousRunStatistics :: ObviousRunReport global -> ObviousStatistics
obviousRunStatistics = \case
    ObviousRunSucceeded statistics _proof -> statistics
    ObviousRunFailed failure -> obviousFailureStatistics failure

obviousRunResult
    :: ObviousRunReport global
    -> Either (ObviousFailure global) (ObviousProof global)
obviousRunResult = \case
    ObviousRunSucceeded _statistics proof -> Right proof
    ObviousRunFailed failure ->
        Left (obviousFailureFinal failure)

obviousRunFailure
    :: ObviousRunReport global
    -> Maybe (ObviousFailureReport global)
obviousRunFailure = \case
    ObviousRunSucceeded{} -> Nothing
    ObviousRunFailed failure -> Just failure

obviousEffectiveBudget :: ObviousStatistics -> ObviousBudget
obviousEffectiveBudget = statisticsEffectiveBudget

obviousFocusedTierOutcome :: ObviousStatistics -> ObviousTierOutcome
obviousFocusedTierOutcome = statisticsFocusedTierOutcome

obviousRefutationTierOutcome :: ObviousStatistics -> ObviousTierOutcome
obviousRefutationTierOutcome = statisticsRefutationTierOutcome

obviousFocusedWorkConsumed :: ObviousStatistics -> Word
obviousFocusedWorkConsumed = statisticsFocusedWorkConsumed

obviousRefutationWorkConsumed :: ObviousStatistics -> Word
obviousRefutationWorkConsumed = statisticsRefutationWorkConsumed

obviousConversionWorkConsumed :: ObviousStatistics -> Word
obviousConversionWorkConsumed = statisticsConversionWorkConsumed

obviousBranchNodesCreated :: ObviousStatistics -> Word
obviousBranchNodesCreated = statisticsBranchNodesCreated

obviousTermsAdmitted :: ObviousStatistics -> Word
obviousTermsAdmitted = statisticsTermsAdmitted

obviousSignedFormulasAdmitted :: ObviousStatistics -> Word
obviousSignedFormulasAdmitted = statisticsSignedFormulasAdmitted

obviousEqualityEventsProcessed :: ObviousStatistics -> Word
obviousEqualityEventsProcessed = statisticsEqualityEventsProcessed

obviousRuleInstancesAdmitted :: ObviousStatistics -> Word
obviousRuleInstancesAdmitted = statisticsRuleInstancesAdmitted

obviousFactDomainsStarted :: ObviousStatistics -> Word
obviousFactDomainsStarted = statisticsFactDomainsStarted

obviousFactDomainsDeferred :: ObviousStatistics -> Bool
obviousFactDomainsDeferred = statisticsFactDomainsDeferred

obviousWitnessAttempts :: ObviousStatistics -> Word
obviousWitnessAttempts = statisticsWitnessAttempts

obviousWitnessesDeferred :: ObviousStatistics -> Bool
obviousWitnessesDeferred = statisticsWitnessesDeferred

obviousExistentialOpenings :: ObviousStatistics -> Word
obviousExistentialOpenings = statisticsExistentialOpenings

obviousExistentialsDeferred :: ObviousStatistics -> Bool
obviousExistentialsDeferred = statisticsExistentialsDeferred

obviousExtensionalityAttempts :: ObviousStatistics -> Word
obviousExtensionalityAttempts = statisticsExtensionalityAttempts

obviousExtensionalityDeferred :: ObviousStatistics -> Bool
obviousExtensionalityDeferred = statisticsExtensionalityDeferred

obviousEndpointGuardWaits :: ObviousStatistics -> Word
obviousEndpointGuardWaits = statisticsEndpointGuardWaits

obviousPremiseQueriesStarted :: ObviousStatistics -> Word
obviousPremiseQueriesStarted = statisticsPremiseQueriesStarted

obviousPremiseQueriesDeferred :: ObviousStatistics -> Bool
obviousPremiseQueriesDeferred = statisticsPremiseQueriesDeferred

obviousUniversalAttempts :: ObviousStatistics -> Word
obviousUniversalAttempts = statisticsUniversalAttempts

obviousUniversalHintSteps :: ObviousStatistics -> Word
obviousUniversalHintSteps = statisticsUniversalHintSteps

obviousUniversalsDeferred :: ObviousStatistics -> Bool
obviousUniversalsDeferred = statisticsUniversalsDeferred

-- Diagnostic snapshot: an outside-domain package reached its captured source
-- opportunity, but had not started when the request completed or stopped.
obviousPendingFactDomainOpportunities :: ObviousStatistics -> Word
obviousPendingFactDomainOpportunities = statisticsPendingFactDomainOpportunities

newtype ValidatedObviousBudget = ValidatedObviousBudget
    { validatedObviousBudget :: ObviousBudget
    }

newtype FocusedObligationId = FocusedObligationId Int
    deriving stock (Show, Eq, Ord)

newtype FocusedContextId = FocusedContextId Int
    deriving stock (Show, Eq, Ord)

newtype CandidateId = CandidateId Int
    deriving stock (Show, Eq, Ord)

newtype RootGoalViewId = RootGoalViewId Int
    deriving stock (Show, Eq, Ord)

data RootGoalView = RootGoalView
    !RootGoalViewId
    !CandidateRootGoalView

data CandidateObservationScope
    = ObserveRoot !RootGoalView
    | SuppressAuxiliary !ObviousAuxiliaryObligationKind
    -- A producer collects both slots; rejection belongs to its consumer.
    | CollectSharedEvidence

data CandidateIdentity = CandidateIdentity
    !CandidateId
    !RootGoalViewId
    deriving stock (Show, Eq, Ord)

data CandidateSeed global = CandidateSeed
    !CandidateIdentity
    !RootGoalView
    !CandidateSourceAnnotation
    !CandidateComparisonView
    !(ScopedCheckedCore global)

data CandidateRank = CandidateRank
    !CandidateIdentity
    !CandidateOutcome
    !Natural
    !Int
    !Natural

data CandidateCompletion global = CandidateCompletion
    !(CandidateSeed global)
    !Natural
    !(Maybe CandidateStructuralDifference)

data RetainedCandidate global = RetainedCandidate
    !CandidateRank
    !(ObviousCandidateObservation global)

type role CandidateSeed nominal
type role CandidateCompletion nominal
type role RetainedCandidate nominal

data FocusedScopeLineage global
    = FocusedRootScope
    | FocusedAssumptionScope !FocusedContextId !(ScopedCheckedCore global)
    | FocusedBinderScope !FocusedContextId !CoreType

data FocusedContext global = FocusedContext
    !(FocusedScopeLineage global)
    !(KernelProof.ProofContext global)

newtype GroundFamilyId = GroundFamilyId Int
    deriving stock (Show, Eq, Ord)

-- A directional pair is one ordered selection, not two independently selected
-- views. Sharing one operand neither aliases two pairs nor constitutes a cycle.
data GroundViewSelection global
    = SelectedGoalView !(ScopedCheckedCore global)
    | SelectedDirections !(ScopedCheckedCore global) !(ScopedCheckedCore global)

selectionRoots :: GroundViewSelection global -> [ScopedCheckedCore global]
selectionRoots (SelectedGoalView target) = [target]
selectionRoots (SelectedDirections forward backward) = [forward, backward]

traverseSelection
    :: Applicative m
    => (ScopedCheckedCore global -> m (ScopedCheckedCore global))
    -> GroundViewSelection global -> m (GroundViewSelection global)
traverseSelection visit = \case
    SelectedGoalView target -> SelectedGoalView <$> visit target
    SelectedDirections forward backward -> SelectedDirections <$> visit forward <*> visit backward

-- The anchor is syntax, never evidence. Assumption children share it; a term
-- binder starts a new family in its extended checked context.
data GroundFamily global = GroundFamily
    { familyScope :: !FocusedContextId
    , familyContext :: !(KernelProof.ProofContext global)
    , familyAnchor :: !(ScopedCheckedCore global)
    , familyImports :: ![ObviousImport global]
    , familyViewLineage :: !(Seq (GroundViewSelection global))
    , familyViewVariants :: !(Map.Map FocusedContextId [(GroundViewSelection global, GroundFamilyId)])
    , familyDomainQuery :: !(Maybe Int)
    , familyQueries :: !(Map.Map (FocusedContextId, FocusedSourcePolicy)
        [(ScopedCheckedCore global, Int)])
    , familyTypeInventories :: !(Map.Map Search.TypeId Search.CatalogueTypeTerms)
    }

-- Domain and session ownership stay in the driver. In particular, a handle
-- never contains a resumable snapshot which a consumer could replay later.
data GroundOwner global = GroundOwner
    { ownedGroundFamilies :: !(Seq (GroundFamily global))
    , ownedGroundQueries :: !(Seq (OwnedGroundQuery global))
    , ownedGroundFacts :: !(Seq (PublishedGroundFact global))
    , ownedGroundActivations :: !(Map.Map Int (GroundActivation global))
    , ownedGroundVariantLimit :: !Word
    , ownedGroundVariantStarts :: !Word
    , ownedGroundVariantsDeferred :: !Bool
    , ownedDirectionalEntries :: !(Seq (DirectionalEntry global))
    }

newtype DirectionalEntryId = DirectionalEntryId Int

-- Checked syntax belongs to the equality entry, never to a direction's fresh
-- assumption. Each successful preparation step survives a canceled requester.
data DirectionalEntry global = DirectionalEntry
    !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(DirectionalPreparation global)

data DirectionalPreparation global
    = DirectionsUnprepared
    | DirectionLeftPrepared !(Refutation.PreparedSyntax global)
    | DirectionOperandsPrepared !(Refutation.PreparedSyntax global) !(Refutation.PreparedSyntax global)
    | DirectionForwardPrepared !(Refutation.PreparedSyntax global) !(Refutation.PreparedSyntax global)
        !(Refutation.PreparedSyntax global)
    | DirectionsPrepared ![Refutation.PreparedSyntax global] !(Maybe GroundEligibility)
    | DirectionsFailed ![Refutation.PreparedSyntax global] !(ObviousFailure global)

-- The key is the original exact query, including its nominal scope and family.
-- Later domains are execution state, never new obligation/activation identities.
data GroundActivation global = GroundActivation
    { activationQuery :: !Int
    , activationRunning :: !(Seq Int)
    , activationParked :: !(Seq Int)
    , activationCertificates :: !(Maybe (OwnedGroundCertificate global), Maybe (OwnedGroundCertificate global))
    , activationCursor :: !Int
    , activationSnapshot :: !Int
    , activationInputs :: !(Seq (Int, Maybe (ScopedCheckedCore global), Refutation.PreparedCertifiedFact global))
    , activationOutside :: !Bool
    , activationOpportunity :: !Bool
    , activationFailure :: !(Maybe (ObviousFailure global))
    }

-- Nothing marks an initially supplied or known-outside input. A checked pending
-- view is reused at the existing frontier boundary, in this exact query scope.
data GroundInputCursor global = GroundInputCursor
    !Int !(Map.Map Int (Maybe (Refutation.PreparedCertifiedFact global)))

emptyGroundInputCursor :: GroundInputCursor global
emptyGroundInputCursor = GroundInputCursor 0 Map.empty

data OwnedGroundQuery global = OwnedGroundQuery
    !FocusedContextId
    !(GlobalTyping global)
    !FocusedContextId -- nominal owner of the family syntax, possibly an ancestor
    !(Maybe (Refutation.FrozenDomain global))
    !(OwnedGroundStatus global)
    !(Maybe (OwnedGroundSupport global))
    !(GroundInputCursor global)

data OwnedGroundStatus global
    = OwnedGroundRunning !(Refutation.RefutationSession global)
    | OwnedGroundBlocked !Refutation.RefutationStatistics !Refutation.RefutationFailure
        !(Refutation.RefutationSession global)
    | OwnedGroundFinished !Refutation.RefutationStatistics
        !(Either Refutation.RefutationFailure (OwnedGroundCertificate global))
    | OwnedGroundCertificationFailed !Refutation.RefutationStatistics !(ObviousFailure global)

-- Support belongs to this query, not its identity. The source registry maps
-- query-context hypotheses back to original request sources. An ordinary
-- certificate remains available while the sole session seeks canonical use.
data OwnedGroundSupport global = OwnedGroundSupport
    ![(Refutation.RefutationCanonicalSource, CanonicalSource)]
    !(Maybe (OwnedGroundCertificate global))

data OwnedGroundCertificate global = OwnedGroundCertificate
    !(KernelProof.BuiltProof global) !KernelSourceUses !(Maybe CanonicalSource)

-- Discovery retains the immutable checked selection. Its source-use audit is
-- paid once, when a ground consumer needs it, in the original producer scope.
data PublishedGroundFact global = PublishedGroundFact
    !FocusedContextId !(Maybe GroundFamilyId) !(SearchEnvironment global) !(ObviousProof global)
    !(Maybe (Either (ObviousFailure global) (OwnedGroundCertificate global)))

data GroundEligibility
    = SeedEligible !GroundFamilyId
    | ExistingFamily !ReadOnlyGroundUse !GroundFamilyId
    | FocusedOnly
    deriving stock (Show, Eq, Ord)

data ReadOnlyGroundUse = WitnessBody | TheoremPremise | ExistentialBranch | ExtensionalityBranch
    deriving stock (Show, Eq, Ord)

data FocusedSourcePolicy
    = AllPermittedSources
    | CitedPredicateSources
    deriving stock (Show, Eq, Ord)

data FocusedObligation global = FocusedObligation
    !(ScopedCheckedCore global)
    !(FocusedCertificates global)
    !Bool -- an ordinary scheduler producer needs certificate notifications

-- The first certificate may already be canonical. Filling canonical support
-- does not replace that first result or create another obligation identity.
data FocusedCertificates global
    = FocusedSingleCertificate !(Maybe (ObviousProof global))
    | FocusedSupportedCertificates !(Maybe (ObviousProof global)) !(Maybe (ObviousProof global))

data FocusedObligationHead global = FocusedObligationHead
    !Int
    !(FocusedHeadAtom global)
    deriving stock (Show, Eq, Ord)

data FocusedHeadAtom global
    = FocusedHeadGlobal !global
    | FocusedHeadIntrinsic !CoreIntrinsicTag
    | FocusedHeadBound !Natural
    | FocusedHeadOpaqueInteger !Integer
    | FocusedHeadLogicalSelect
    | FocusedHeadLambda
    | FocusedHeadFalsum
    | FocusedHeadTruth
    | FocusedHeadNegation
    | FocusedHeadConjunction
    | FocusedHeadDisjunction
    | FocusedHeadImplication
    | FocusedHeadEquality
    | FocusedHeadUniversal
    | FocusedHeadExistential
    deriving stock (Show, Eq, Ord)

newtype FocusedEqualityTermId = FocusedEqualityTermId Int
    deriving stock (Show, Eq, Ord)

newtype FocusedEqualityEdgeId = FocusedEqualityEdgeId Int
    deriving stock (Show, Eq, Ord)

data PreparedTheoremSource global = PreparedTheoremSource
    !(ObviousProof global)
    !(CompiledTheoremSpine global)

data TheoremWorkItem global
    = RootTheoremWorkItem !(ObviousProof global)
    | ProjectedTheoremWorkItem !(ObviousProof global)
    | SelectedTheoremWorkItem !(ObviousProof global)
        ![TheoremSpineStep global] !(Template.CompiledTemplate global)

data PropositionTransportScan global = PropositionTransportScan
    !(Seq (ObviousProof global)) !Bool !EqualityProducer

data DefinitionViewCatalogue global = DefinitionViewCatalogue
    ![ObviousDefinitionView global]
    !(Map.Map
        (DefinitionViewKind, global)
        (Seq (Natural, ObviousImport global)))
    ![(Natural, Natural, DefinitionViewKind)]
    !(Map.Map
        (DefinitionViewKind, global)
        (Seq (Natural, ObviousImport global)))

data DefinitionViewCandidate global
    = ImportedDefinitionViewCandidate
        !Natural
        !(ObviousImport global)
    | LocalDefinitionViewCandidate
        !Natural
        !Natural

data DefinitionViewSelection
    = AllDefinitionViews
    | ImportedDefinitionViewsOnly
    | LocalDefinitionViewsOnly
    deriving stock (Eq)

data FocusedEqualityDirection
    = FocusedEqualityForward
    | FocusedEqualityReverse
    deriving stock (Show, Eq, Ord)

data FocusedEqualityEdge global = FocusedEqualityEdge
    !FocusedEqualityTermId
    !FocusedEqualityTermId
    !FocusedEqualityDirection
    !(ObviousProof global)

data FocusedEqualityGraph global = FocusedEqualityGraph
    !(Seq (ScopedCheckedCore global))
    !(Seq (FocusedEqualityEdge global))
    !(Map.Map FocusedEqualityTermId (Seq FocusedEqualityEdgeId))
    !(Map.Map
        (CoreType, FocusedObligationHead global)
        (Seq FocusedEqualityTermId))

data FocusedEqualityVisit = FocusedEqualityVisit
    !FocusedEqualityTermId
    !Bool
    deriving stock (Show, Eq, Ord)

-- An assumption keeps its birth identity across hypothesis and term weakening.
-- Opening an ancestor again is distinct from opening a newly exposed nested body.
data ExistentialSourceOrigin
    = ExistentialHypothesis !FocusedContextId !Natural
    | ExistentialImport !ImportIx
    deriving stock (Eq, Ord)

data MembershipDirection = ForwardMembership | ReverseMembership
    deriving stock (Eq, Ord)

data ExtensionalityBranch global = MembershipBranch
    !(FocusedRequest global)
    !(KernelProof.ProofContext global) -- binder scope, before its assumption
    !(ScopedCheckedCore global) -- the membership assumption to discharge

data EndpointPolicy = EndpointsDisabled | EndpointApplications !Word
    deriving stock (Show, Eq)

-- Parameter discovery from premises belongs to ordinary theorem application.
-- The endpoint producer enters reconstruction only after all slots are fixed.
data ApplicationParameterPolicy = PremiseParameters | PrefixParameters | EndpointParameters !FocusedEqualityDirection

data FocusedObligationPurpose = OrdinaryObligation | EndpointObligation
    deriving stock (Eq, Ord)

-- Private to the search driver and its controlled test/benchmark entry point.
-- Disabled features remain distinct from enabled policies with zero allowance.
data SearchPolicy = SearchPolicy
    { policyEndpoints :: !EndpointPolicy
    , policyExtensionality :: !ExtensionalityPolicy
    , policyExistentials :: !ExistentialPolicy
    , policyUniversals :: !UniversalPolicy
    , policyPremiseQueries :: !PremiseQueryPolicy
    , policyWitnesses :: !WitnessPolicy
    }
    deriving stock (Show, Eq)

productionSearchPolicy :: SearchPolicy
productionSearchPolicy = SearchPolicy
    { policyEndpoints = EndpointApplications 16
    , policyExtensionality = MembershipExtensionality 1
    , policyExistentials = SuppliedExistentials 2
    , policyUniversals = HintedUniversals 32 128
    , policyPremiseQueries = ExistingPremiseQueries 2
    , policyWitnesses = ExistingWitnesses 4 32
    }

disabledSearchPolicy :: SearchPolicy
disabledSearchPolicy = SearchPolicy
    { policyEndpoints = EndpointsDisabled
    , policyExtensionality = ExtensionalityDisabled
    , policyExistentials = ExistentialsDisabled
    , policyUniversals = UniversalsDisabled
    , policyPremiseQueries = PremiseQueriesDisabled
    , policyWitnesses = WitnessesDisabled
    }

-- | Consumable resources for a sequence of completed searches. No syntax,
-- evidence, or suspended search state survives a run. Private attempt quotas
-- travel with the public budget so another residual cannot replenish them.
data ObviousAllowance = ObviousAllowance !ObviousBudget !SearchPolicy
    deriving stock (Show, Eq)

obviousAllowance :: ObviousBudget -> ObviousAllowance
obviousAllowance budget = ObviousAllowance budget productionSearchPolicy

obviousRemainingBudget :: ObviousAllowance -> ObviousBudget
obviousRemainingBudget (ObviousAllowance budget _) = budget

-- Preparation shares the request's conversion pool without reopening the
-- solver's private attempt quotas. Debit only work actually consumed.
debitObviousConversion :: Word -> ObviousAllowance -> Maybe ObviousAllowance
debitObviousConversion consumed (ObviousAllowance budget policy)
    | consumed > available = Nothing
    | otherwise = Just (ObviousAllowance budget
        {obviousConversionPool = Conversion.conversionPool (available - consumed)} policy)
  where
    available = Conversion.conversionPoolAmount (obviousConversionPool budget)

-- Per-obligation witness prefixes are caps, not request-wide resources.
portionPolicy :: (Word -> Word) -> SearchPolicy -> SearchPolicy
portionPolicy portion (SearchPolicy endpoints extensionality existentials universals premises witnesses) =
    SearchPolicy
        (case endpoints of
            EndpointsDisabled -> EndpointsDisabled
            EndpointApplications total -> EndpointApplications (portion total))
        (case extensionality of
            ExtensionalityDisabled -> ExtensionalityDisabled
            MembershipExtensionality total -> MembershipExtensionality (portion total))
        (case existentials of
            ExistentialsDisabled -> ExistentialsDisabled
            SuppliedExistentials total -> SuppliedExistentials (portion total))
        (case universals of
            UniversalsDisabled -> UniversalsDisabled
            ExistingUniversals total -> ExistingUniversals (portion total)
            HintedUniversals total hints -> HintedUniversals (portion total) (portion hints))
        (case premises of
            PremiseQueriesDisabled -> PremiseQueriesDisabled
            ExistingPremiseQueries total -> ExistingPremiseQueries (portion total))
        (case witnesses of
            WitnessesDisabled -> WitnessesDisabled
            ExistingWitnesses prefix total -> ExistingWitnesses prefix (portion total))

portionBudget :: (Word -> Word) -> ObviousBudget -> ObviousBudget
portionBudget portion budget = ObviousBudget
    { obviousFocusedWorkLimit = portion (obviousFocusedWorkLimit budget)
    , obviousRefutationWorkLimit = portion (obviousRefutationWorkLimit budget)
    , obviousConversionPool = Conversion.conversionPool (portion (Conversion.conversionPoolAmount (obviousConversionPool budget)))
    , obviousGroundTermLimit = portion (obviousGroundTermLimit budget)
    , obviousBranchNodeLimit = portion (obviousBranchNodeLimit budget)
    , obviousRuleInstanceLimit = portion (obviousRuleInstanceLimit budget)
    , obviousFactDomainLimit = portion (obviousFactDomainLimit budget)
    }

-- Debit actual driver consumption, returning unused credit as well as any
-- untouched reserve. In particular, an exhausted initial slice is not an
-- exhausted enclosing request.
remainingAllowance :: ObviousAllowance -> ObviousBudget -> SearchPolicy
    -> ObviousSearchState global -> ObviousAllowance
remainingAllowance (ObviousAllowance budget policy) granted grantedPolicy state =
    ObviousAllowance budget
        { obviousFocusedWorkLimit = remaining obviousFocusedWorkLimit (searchRemainingFocusedWork state)
        , obviousRefutationWorkLimit = remaining obviousRefutationWorkLimit (groundWork ground)
        , obviousConversionPool = Conversion.conversionPool
            (remaining (Conversion.conversionPoolAmount . obviousConversionPool)
                (Conversion.conversionPoolAmount (searchRemainingConversionPool state)))
        , obviousGroundTermLimit = remaining obviousGroundTermLimit (groundTerms ground)
        , obviousBranchNodeLimit = remaining obviousBranchNodeLimit (groundBranches ground)
        , obviousRuleInstanceLimit = remaining obviousRuleInstanceLimit (groundInstances ground)
        , obviousFactDomainLimit = obviousFactDomainLimit budget - ownedGroundVariantStarts (searchGroundOwner state)
        }
        policy
        { policyEndpoints = case policyEndpoints policy of
            EndpointsDisabled -> EndpointsDisabled
            EndpointApplications total -> EndpointApplications (total - searchEndpointAttempts state)
        , policyExtensionality = case policyExtensionality policy of
            ExtensionalityDisabled -> ExtensionalityDisabled
            MembershipExtensionality total -> MembershipExtensionality (total - searchExtensionalityAttempts state)
        , policyExistentials = case policyExistentials policy of
            ExistentialsDisabled -> ExistentialsDisabled
            SuppliedExistentials total -> SuppliedExistentials (total - searchExistentialOpenings state)
        , policyUniversals = remainingUniversals (policyUniversals policy)
            (policyUniversals grantedPolicy) (groundUniversals ground)
        , policyPremiseQueries = case policyPremiseQueries policy of
            PremiseQueriesDisabled -> PremiseQueriesDisabled
            ExistingPremiseQueries total -> ExistingPremiseQueries (total - searchPremiseQueriesStarted state)
        , policyWitnesses = case policyWitnesses policy of
            WitnessesDisabled -> WitnessesDisabled
            ExistingWitnesses prefix total -> ExistingWitnesses prefix (total - searchWitnessAttempts state)
        }
  where
    ground = searchRemainingGround state
    remaining field balance = field budget - (field granted - balance)
    remainingUniversals UniversalsDisabled UniversalsDisabled UniversalsDisabled = UniversalsDisabled
    remainingUniversals (ExistingUniversals total) (ExistingUniversals slice) (ExistingUniversals balance) =
        ExistingUniversals (total - (slice - balance))
    remainingUniversals (HintedUniversals total hints) (HintedUniversals slice hintSlice) (HintedUniversals balance hintBalance) =
        HintedUniversals (total - (slice - balance)) (hints - (hintSlice - hintBalance))
    remainingUniversals _ _ _ = impossible "an Obvious run changed its universal policy"

data ObviousSearchState global = ObviousSearchState
    { searchPolicy :: !SearchPolicy
    , searchRemainingFocusedWork :: !Word
    , searchEndpointAttempts :: !Word
    , searchEndpointsDeferred :: !Bool
    , searchEndpointGuardWaits :: !Word
    , searchEndpointOwners :: !(Map.Map FocusedObligationId (FocusedObligationId, Bool))
    , searchEndpointSources :: !(Map.Map (FocusedContextId, FocusedSourcePolicy) [ObviousProof global])
    , searchWitnessAttempts :: !Word
    , searchWitnessesDeferred :: !Bool
    , searchExistentialOpenings :: !Word
    , searchExistentialsDeferred :: !Bool
    , searchExistentialBranches :: !(Map.Map (FocusedObligationId, ExistentialSourceOrigin)
        (Either (ObviousFailure global) (FocusedRequest global)))
    , searchExistentialScopes :: !(Map.Map FocusedContextId (Set ExistentialSourceOrigin))
    , searchExtensionalityAttempts :: !Word
    , searchExtensionalityDeferred :: !Bool
    , searchExtensionalityBranches :: !(Map.Map (FocusedObligationId, FocusedSourceKey)
        (Map.Map MembershipDirection
            (Either (ObviousFailure global) (ExtensionalityBranch global))))
    , searchPremiseQueriesStarted :: !Word
    , searchPremiseQueriesDeferred :: !Bool
    , searchRemainingConversionPool :: !Conversion.ConversionPool
    , searchRemainingGround :: !GroundAllowance
    -- Literal reuse does not force the registry for certified source admission.
    , searchPermittedImports :: Map.Map ImportIx (FrozenCheckedCore global)
    , searchRegisteredDefinitionImports :: !(Set Natural)
    , searchCanonicalImportCandidates :: !(Map.Map ImportIx (Natural, ObviousImport global))
    , searchCanonicalRequest :: !Bool
    , searchCertificateEvents :: !(Seq FocusedObligationId)
    , searchRootAnyCertificate :: !(Maybe (ObviousProof global))
    , searchNextFocusedObligationId :: !Int
    , searchFocusedObligations :: !(Seq (FocusedObligation global))
    , searchFocusedObligationBuckets :: !(Map.Map
        (FocusedContextId, FocusedSourcePolicy, FocusedObligationPurpose, FocusedObligationHead global)
        (Map.Map GroundEligibility (Seq FocusedObligationId)))
    , searchFocusedTheoremCache :: !(Map.Map
        FocusedSourceKey
        (CompiledTheoremSpine global))
    , searchFocusedContexts :: !(Seq (FocusedContext global))
    , searchGroundOwner :: !(GroundOwner global)
    , searchAvailableProofCache :: !(Map.Map
        FocusedContextId
        [ObviousProof global])
    , searchFocusedExposureCache :: !(Map.Map
        FocusedSourceKey
        (ObviousProof global))
    , searchNextDerivedSourceId :: !Int
    , searchProjectionCache :: !(Map.Map FocusedSourceKey [ObviousProof global])
    , searchTheoremSelectionKeys :: !(Map.Map FocusedSourceKey (FocusedSourceKey, FocusedSourceKey))
    , searchFactExpansionCache :: !(Map.Map
        (FocusedSourceKey, Natural, DefinitionObservationSlot)
        (ObviousProof global))
    , searchGroundAdmissionFailure :: !(Maybe (ObviousFailure global))
    , searchRootFocusedOutcome :: !(Maybe ObviousTierOutcome)
    , searchRootFocusedGoalView :: !(Maybe (ObviousFocusedGoalView global))
    , searchCandidateObservationStarted :: !Bool
    , searchNextCandidateId :: !Int
    , searchNextRootGoalViewId :: !Int
    , searchRetainedCandidates :: ![RetainedCandidate global]
    , searchRootRequirementRejections :: ![CandidateRootGoalView]
    , searchAuxiliaryRequirementCauses :: ![CandidateAuxiliaryCause]
    , searchAdditionalAuxiliaryRequirementCauses :: !Word
    }

initialSearchState
    :: SearchPolicy
    -> Word
    -> Conversion.ConversionPool
    -> GroundAllowance
    -> Word
    -> Map.Map ImportIx (FrozenCheckedCore global)
    -> ObviousSearchState global
initialSearchState policy work pool ground factDomains imports =
    ObviousSearchState
        { searchPolicy = policy
        , searchRemainingFocusedWork = work
        , searchEndpointAttempts = 0
        , searchEndpointsDeferred = False
        , searchEndpointGuardWaits = 0
        , searchEndpointOwners = Map.empty
        , searchEndpointSources = Map.empty
        , searchWitnessAttempts = 0
        , searchWitnessesDeferred = False
        , searchExistentialOpenings = 0
        , searchExistentialsDeferred = False
        , searchExistentialBranches = Map.empty
        , searchExistentialScopes = Map.empty
        , searchExtensionalityAttempts = 0
        , searchExtensionalityDeferred = False
        , searchExtensionalityBranches = Map.empty
        , searchPremiseQueriesStarted = 0
        , searchPremiseQueriesDeferred = False
        , searchRemainingConversionPool = pool
        , searchRemainingGround = ground
        , searchPermittedImports = imports
        , searchRegisteredDefinitionImports = Set.empty
        , searchCanonicalImportCandidates = Map.empty
        , searchCanonicalRequest = False
        , searchCertificateEvents = Seq.empty
        , searchRootAnyCertificate = Nothing
        , searchNextFocusedObligationId = 0
        , searchFocusedObligations = Seq.empty
        , searchFocusedObligationBuckets = Map.empty
        , searchFocusedTheoremCache = Map.empty
        , searchFocusedContexts = Seq.empty
        , searchGroundOwner = GroundOwner Seq.empty Seq.empty Seq.empty Map.empty factDomains 0 False Seq.empty
        , searchAvailableProofCache = Map.empty
        , searchFocusedExposureCache = Map.empty
        , searchNextDerivedSourceId = 0
        , searchProjectionCache = Map.empty
        , searchTheoremSelectionKeys = Map.empty
        , searchFactExpansionCache = Map.empty
        , searchGroundAdmissionFailure = Nothing
        , searchRootFocusedOutcome = Nothing
        , searchRootFocusedGoalView = Nothing
        , searchCandidateObservationStarted = False
        , searchNextCandidateId = 0
        , searchNextRootGoalViewId = 1
        , searchRetainedCandidates = []
        , searchRootRequirementRejections = []
        , searchAuxiliaryRequirementCauses = []
        , searchAdditionalAuxiliaryRequirementCauses = 0
        }

data SearchEnvironment global = SearchEnvironment
    !(GlobalTyping global)
    ![ObviousImport global]
    !Natural
    !(DefinitionViewCatalogue global)

data ValidatedObviousRequest global = ValidatedObviousRequest
    !ValidatedObviousBudget
    !ProofRequirement
    !(SearchEnvironment global)
    !(KernelProof.ProofContext global)
    !(ScopedCheckedCore global)

data AvailableDefinitionView global = AvailableDefinitionView
    !Natural
    !(CanonicalTerm global)
    !DefinitionViewKind
    !(ObviousProof global)

availableDefinitionViewOrdinal :: AvailableDefinitionView global -> Natural
availableDefinitionViewOrdinal
        (AvailableDefinitionView ordinal _subject _kind _proof) =
    ordinal

data DefinitionObservationSlot
    = PredicateDefinitionSlot
    | PredicateArgumentDefinitionSlot
    | MembershipDefinitionSlot
    | EqualityLeftDefinitionSlot
    | EqualityRightDefinitionSlot
    deriving stock (Eq, Ord)

definitionObservationSlot :: RootObservation global -> DefinitionObservationSlot
definitionObservationSlot = \case
    PredicateObservation{} -> PredicateDefinitionSlot
    PredicateArgumentObservation{} -> PredicateArgumentDefinitionSlot
    MembershipObservation{} -> MembershipDefinitionSlot
    EqualityLeftObservation{} -> EqualityLeftDefinitionSlot
    EqualityRightObservation{} -> EqualityRightDefinitionSlot

data RootObservation global
    = PredicateObservation
        !(CanonicalTerm global)
        ![CanonicalTerm global]
        !(ScopedCheckedCore global)
    | PredicateArgumentObservation
        !(CanonicalTerm global)
        ![CanonicalTerm global]
        !(ScopedCheckedCore global)
        !(CanonicalTerm global)
    | EqualityLeftObservation
        !CoreType
        !(CanonicalTerm global)
        !(ScopedCheckedCore global)
        ![CanonicalTerm global]
        !(CanonicalTerm global)
    | EqualityRightObservation
        !CoreType
        !(CanonicalTerm global)
        !(ScopedCheckedCore global)
        ![CanonicalTerm global]
        !(CanonicalTerm global)
    | MembershipObservation
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        ![CanonicalTerm global]
        !(ScopedCheckedCore global)

data Attempt global
    = AttemptNotApplicable
    | AttemptFailed !(ObviousFailure global)
    | AttemptSucceeded !(ObviousProof global)

data ExactConversionPolicy
    = ConvertExactCandidates
    | DeferExactCandidateConversion
    deriving stock (Eq)

data TemplateMatchResult global
    = TemplateMismatch !TemplateMismatchEvidence
    | TemplateHigherOrderUnsupported !Natural
    | TemplateMatched !(Template.TemplateSubstitution global) !Natural

data TemplateMismatchEvidence = TemplateMismatchEvidence
    !MismatchClass
    !(Maybe CandidateStructuralDifference)
    !Natural

type TheoremSpineStep global =
    Elimination.EliminationStep Template.MatcherSlot (Template.CompiledTemplate global)

data CompiledTheoremSpine global = CompiledTheoremSpine
    ![TheoremSpineStep global]
    !(Template.CompiledTemplate global)
    !Bool -- the checked, paired membership-extensionality schema

spineBinderEnvironment :: CompiledTheoremSpine global -> Template.BinderEnvironment
spineBinderEnvironment (CompiledTheoremSpine _steps result _) =
    Template.compiledTemplateBinderEnvironment result

-- | Search checked inputs under the supplied global typing snapshot.  The
-- target and hypotheses must have been checked in the target lexical context
-- in the same nominal global universe; imported values must have been checked
-- closed in that universe.  The owner which supplies these values preserves
-- their shared provenance; this function cannot reconstruct it independently.
obviousProof
    :: Ord global
    => ObviousBudget
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> Either (ObviousFailure global) (ObviousProof global)
obviousProof workBudget =
    obviousProofWithRequirement workBudget AnyObviousProof

-- | The checked-input global-universe precondition is the same as for
-- 'obviousProof'.
obviousProofWithRequirement
    :: Ord global
    => ObviousBudget
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> Either (ObviousFailure global) (ObviousProof global)
obviousProofWithRequirement
        budget requirement foundation globalType hypotheses imports
        definitionViews target =
    obviousRunResult
        (obviousProofReport
            budget requirement foundation globalType hypotheses imports
            definitionViews target)

-- | Run the same checked search while retaining stable tier outcomes and
-- coarse logical-work statistics.  This has the same global-universe
-- precondition as 'obviousProof'.
obviousProofDetailed
    :: Ord global
    => ObviousBudget
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> ( ObviousStatistics
       , Either (ObviousFailure global) (ObviousProof global)
       )
obviousProofDetailed
        budget requirement foundation globalTyping hypotheses imports
        definitionViews target =
    let report =
            obviousProofReport
                budget requirement foundation globalTyping hypotheses imports
                definitionViews target
    in (obviousRunStatistics report, obviousRunResult report)

-- | Run checked search once and retain a failure-only bounded diagnostic
-- report. Compatibility entry points are projections of this value.
obviousProofReport
    :: Ord global
    => ObviousBudget
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> ObviousRunReport global
obviousProofReport = obviousProofReportWithPolicy productionSearchPolicy

obviousProofReportWithPolicy
    :: Ord global
    => SearchPolicy
    -> ObviousBudget
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> ObviousRunReport global
obviousProofReportWithPolicy policy
        budget requirement foundation globalTyping hypotheses imports
        definitionViews target =
    fst (runObviousAllowance id (ObviousAllowance budget policy)
        requirement foundation globalTyping hypotheses imports definitionViews target)

-- | Run one complete residual search with the remaining request allowance.
obviousProofReportWithin
    :: Ord global
    => ObviousAllowance
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> (ObviousRunReport global, ObviousAllowance)
obviousProofReportWithin = runObviousAllowance id

-- | Reserve three quarters of each consumable for preparation and residuals.
-- Zero focused credit skips the attempt; zero in any other resource stays zero.
obviousInitialProofReportWithin
    :: Ord global
    => ObviousAllowance
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> Maybe (ObviousRunReport global, ObviousAllowance)
obviousInitialProofReportWithin allowance requirement foundation globalTyping hypotheses imports views target
    | obviousFocusedWorkLimit (obviousRemainingBudget allowance) < 4 = Nothing
    | otherwise = Just (runObviousAllowance (`div` 4) allowance
        requirement foundation globalTyping hypotheses imports views target)

runObviousAllowance
    :: Ord global
    => (Word -> Word)
    -> ObviousAllowance
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> (ObviousRunReport global, ObviousAllowance)
runObviousAllowance portion allowance@(ObviousAllowance fullBudget fullPolicy)
        requirement foundation globalTyping hypotheses imports definitionViews target =
    case validateObviousRequest
            fullBudget requirement foundation globalTyping hypotheses imports
            definitionViews target of
        Left malformed ->
            let statistics = observeBreadth (emptyObviousStatistics budget)
                failure = ObviousMalformedInput malformed
                report =
                    makeObviousFailureReport
                        statistics
                        failure
                        (obviousFailureClass failure)
                        ObviousValidationFailure
                        target
                        ObviousFocusedViewUnavailable
                        hypotheses imports definitionViews
                        CandidateObservationNotStarted [] [] [] 0
            in statistics `seq` report `seq`
                (ObviousRunFailed report, allowance)
        Right
                (ValidatedObviousRequest
                    validatedBudget
                    validatedRequirement
                    environment
                    context
                    validatedTarget) ->
            let effectiveBudget =
                    portionBudget portion (validatedObviousBudget validatedBudget)
                initialState = (initialSearchState policy
                    (obviousFocusedWorkLimit effectiveBudget)
                    (obviousConversionPool effectiveBudget)
                    (GroundAllowance
                        (obviousRefutationWorkLimit effectiveBudget)
                        (obviousGroundTermLimit effectiveBudget)
                        (obviousBranchNodeLimit effectiveBudget)
                        (obviousRuleInstanceLimit effectiveBudget) universalPolicy)
                    (obviousFactDomainLimit effectiveBudget)
                    (Map.fromList [(index, statement) | ObviousImport index statement <- imports]))
                    { searchCanonicalRequest = validatedRequirement == MustUseCanonicalDefinition
                    , searchCanonicalImportCandidates = if validatedRequirement == MustUseCanonicalDefinition
                        then Map.fromListWith (\_new existing -> existing)
                            [(obviousImportIndex source, (ordinal, source))
                            | (ordinal, ObviousImportedDefinitionView _subject _kind source) <- zip [0 ..] definitionViews]
                        else Map.empty }
                (result, finalState) = State.runState
                    (startObviousRoot validatedRequirement environment context validatedTarget
                        >>= auditSelectedCanonicalProof validatedRequirement) initialState
                statistics = observeBreadth (completedObviousStatistics effectiveBudget finalState result)
                focusedGoalView = fromMaybe ObviousFocusedViewUnavailable (searchRootFocusedGoalView finalState)
                remaining = remainingAllowance allowance effectiveBudget policy finalState
            in case result of
                Right proof ->
                    let semanticProof = withoutCandidateEvidence proof
                    in statistics `seq` semanticProof `seq` remaining `seq`
                        (ObviousRunSucceeded statistics semanticProof, remaining)
                Left failure ->
                    let path =
                            if Seq.null (ownedGroundQueries (searchGroundOwner finalState))
                                then ObviousFocusedOnlyFailure
                                    ObviousRefutationQueryNotStarted
                                else ObviousCoordinatedFailure
                        primary = obviousFailureClass failure
                        report =
                            makeObviousFailureReport
                                statistics
                                failure primary path target focusedGoalView
                                hypotheses imports definitionViews
                                (candidateCoverage finalState result)
                                (retainedCandidateObservation
                                    <$> searchRetainedCandidates finalState)
                                (searchRootRequirementRejections finalState)
                                (searchAuxiliaryRequirementCauses finalState)
                                (fromIntegral
                                    (searchAdditionalAuxiliaryRequirementCauses
                                        finalState))
                    in statistics `seq` report `seq` remaining `seq`
                        (ObviousRunFailed report, remaining)

  where
    budget = portionBudget portion fullBudget
    policy = portionPolicy portion fullPolicy
    SearchPolicy endpointPolicy extensionalityPolicy existentialPolicy
        universalPolicy premisePolicy witnessPolicy = policy
    observeBreadth statistics = statistics
        { statisticsBreadthObservations =
            [ObviousFactDomainBreadth (obviousFactDomainLimit budget)
                (statisticsFactDomainsStarted statistics) (statisticsFactDomainsDeferred statistics)]
            <> case witnessPolicy of
                WitnessesDisabled -> []
                ExistingWitnesses perObligation total ->
                    [ObviousWitnessBreadth perObligation total
                        (statisticsWitnessAttempts statistics) (statisticsWitnessesDeferred statistics)]
            <> case premisePolicy of
                PremiseQueriesDisabled -> []
                ExistingPremiseQueries total -> [ObviousPremiseQueryBreadth total
                    (statisticsPremiseQueriesStarted statistics) (statisticsPremiseQueriesDeferred statistics)]
            <> case universalPolicy of
                UniversalsDisabled -> []
                ExistingUniversals total -> [universal total]
                HintedUniversals total hints -> [universal total,
                    ObviousUniversalHintEffort hints (statisticsUniversalHintSteps statistics)]
            <> case existentialPolicy of
                ExistentialsDisabled -> []
                SuppliedExistentials total -> [ObviousExistentialBreadth total
                    (statisticsExistentialOpenings statistics) (statisticsExistentialsDeferred statistics)]
            <> case extensionalityPolicy of
                ExtensionalityDisabled -> []
                MembershipExtensionality total -> [ObviousExtensionalityBreadth total
                    (statisticsExtensionalityAttempts statistics) (statisticsExtensionalityDeferred statistics)]
            <> case endpointPolicy of
                EndpointsDisabled -> []
                EndpointApplications total -> [ObviousEndpointBreadth total
                    (statisticsEndpointAttempts statistics) (statisticsEndpointsDeferred statistics)]
        }
      where
        universal total = ObviousUniversalBreadth total
            (statisticsUniversalAttempts statistics) (statisticsUniversalsDeferred statistics)

-- A failed root exposure cannot be treated as a proved propositional head.
-- Later operation exhaustion may leave enough shared credit for the already
-- exposed problem to close under the independent ground structural limit.
allowsGroundAfterPreparation
    :: ObviousFocusedGoalView global -> ObviousFailure global -> Bool
allowsGroundAfterPreparation view failure
    | isFocusedInfrastructureFailure failure = False
    | ObviousResourceExhausted limit <- failure,
        limit == ObviousConversionOperationLimit || limit == ObviousConversionPoolLimit =
            case view of
                ObviousFocusedExposureFailed{} -> False
                ObviousFocusedViewUnavailable -> False
                _ -> True
    | otherwise = True

mapRefutationFailure
    :: Refutation.RefutationFailure
    -> ObviousFailure global
mapRefutationFailure = \case
    Refutation.RefutationSaturated -> ObviousRefutationSaturated
    Refutation.RefutationCanonicalSupportMissing -> ObviousCanonicalDefinitionEvidenceRequired
    Refutation.RefutationWorkExhausted ->
        ObviousResourceExhausted ObviousRefutationWorkLimit
    Refutation.RefutationConversionLimitExhausted owner _limit ->
        ObviousResourceExhausted (conversionOwnerLimit owner)
    Refutation.RefutationConversionFailed failure -> ObviousConversionFailed failure
    Refutation.RefutationRequiredConversionNotConvertible ->
        ObviousRequiredConversionNotConvertible
    Refutation.RefutationConversionAccountingInvariant cost pool ->
        ObviousConversionAccountingInvariant cost pool
    Refutation.RefutationGroundTermsExhausted ->
        ObviousResourceExhausted ObviousGroundTermLimit
    Refutation.RefutationBranchesExhausted ->
        ObviousResourceExhausted ObviousBranchNodeLimit
    Refutation.RefutationRuleInstancesExhausted ->
        ObviousResourceExhausted ObviousRuleInstanceLimit
    Refutation.RefutationUnsupportedTermOutsideUniverse ->
        ObviousUnsupportedTermOutsideUniverse
    Refutation.RefutationUndeterminedParameter parameter ->
        ObviousUndeterminedParameter parameter
    Refutation.RefutationIntegrityFailure failure ->
        ObviousIntegrityFailure failure
    Refutation.RefutationInternalFailure message ->
        ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch message)

candidateCoverage
    :: ObviousSearchState global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> CandidateCoverage
candidateCoverage state focused
    | not (searchCandidateObservationStarted state) =
        CandidateObservationNotStarted
    | otherwise =
        case focused of
            Left failure
                | candidateObservationStoppedBy failure ->
                    CandidateObservationStoppedEarly
            _ -> CandidateObservationFinished

candidateObservationStoppedBy :: ObviousFailure global -> Bool
candidateObservationStoppedBy = \case
    ObviousResourceExhausted{} -> True
    ObviousMalformedInput{} -> True
    ObviousRepeatedState{} -> True
    ObviousIntegrityFailure{} -> True
    ObviousConversionFailed{} -> True
    ObviousRequiredConversionNotConvertible -> True
    ObviousConversionAccountingInvariant{} -> True
    _failure -> False

retainedCandidateObservation
    :: RetainedCandidate global
    -> ObviousCandidateObservation global
retainedCandidateObservation
        (RetainedCandidate _rank observation) =
    observation

obviousFailureClass :: ObviousFailure global -> ObviousFailureClass
obviousFailureClass = \case
    ObviousNoMatchingConclusion{} -> ObviousNoMatchClass
    ObviousAntecedentUnavailable{} -> ObviousAntecedentUnavailableClass
    ObviousUndeterminedParameter{} -> ObviousParameterUndeterminedClass
    ObviousFalsityPairUnavailable -> ObviousFalsityPairUnavailableClass
    ObviousUnsupportedHigherOrderInstantiation ->
        ObviousHigherOrderUnsupportedClass
    ObviousUnsupportedTermOutsideUniverse -> ObviousTermOutsideUniverseClass
    ObviousCanonicalDefinitionEvidenceRequired ->
        ObviousDefinitionEvidenceRequiredClass
    ObviousRefutationSaturated -> ObviousSaturatedClass
    ObviousResourceExhausted limit -> ObviousResourceExhaustedClass limit
    ObviousRepeatedState{} -> ObviousRepeatedStateClass
    ObviousMalformedInput{} -> ObviousMalformedClass
    ObviousIntegrityFailure{} -> ObviousIntegrityClass
    ObviousConversionFailed{} -> ObviousIntegrityClass
    ObviousRequiredConversionNotConvertible -> ObviousIntegrityClass
    ObviousConversionAccountingInvariant{} -> ObviousIntegrityClass

makeObviousFailureReport
    :: Ord global
    => ObviousStatistics
    -> ObviousFailure global
    -> ObviousFailureClass
    -> ObviousFailurePath global
    -> ScopedCheckedCore global
    -> ObviousFocusedGoalView global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> CandidateCoverage
    -> [ObviousCandidateObservation global]
    -> [CandidateRootGoalView]
    -> [CandidateAuxiliaryCause]
    -> Natural
    -> ObviousFailureReport global
makeObviousFailureReport
        statistics failure primary path target focusedView hypotheses imports
        definitionViews coverage candidates rootRejections auxiliaryCauses
        additionalAuxiliaryCauses =
    let ( localDefinitionCount, localDefinitions
          , importedDefinitionCount, importedDefinitions
          ) = boundedDefinitionObservations hypotheses definitionViews
    in ObviousFailureReport
        { obviousFailureStatistics = statistics
        , obviousFailureFinal = failure
        , obviousFailurePrimaryClass = primary
        , obviousFailurePath = path
        , obviousFailureCheckedGoal = summarizeScopedCore target
        , obviousFailureFocusedGoalView = focusedView
        , obviousFailureHypothesisCount =
            fromIntegral (length hypotheses)
        , obviousFailureHypotheses =
            [ ObviousHypothesisObservation
                (fromIntegral index)
                (summarizeScopedCore hypothesis)
            | (index, hypothesis) <- take diagnosticInputLimit
                (zip [0 :: Int ..] hypotheses)
            ]
        , obviousFailureImportCount = fromIntegral (length imports)
        , obviousFailureImports =
            [ ObviousImportObservation index (summarizeFrozenCore statement)
            | ObviousImport index statement <- take diagnosticInputLimit imports
            ]
        , obviousFailureLocalDefinitionViewCount = localDefinitionCount
        , obviousFailureLocalDefinitionViews = localDefinitions
        , obviousFailureImportedDefinitionViewCount = importedDefinitionCount
        , obviousFailureImportedDefinitionViews = importedDefinitions
        , obviousFailureCandidateCoverage = coverage
        , obviousFailureCandidates = candidates
        , obviousFailureRootRequirementRejections = rootRejections
        , obviousFailureAuxiliaryCauses = auxiliaryCauses
        , obviousFailureAdditionalAuxiliaryCauseCount =
            additionalAuxiliaryCauses
        }

boundedDefinitionObservations
    :: Ord global
    => [ScopedCheckedCore global]
    -> [ObviousDefinitionView global]
    -> ( Natural
       , [ObviousInputObservation global]
       , Natural
       , [ObviousInputObservation global]
       )
boundedDefinitionObservations hypotheses =
    finish . foldl' retain (0, [], 0, []) . zip [0 :: Natural ..]
  where
    retain (localCount, locals, importedCount, imported)
            (ordinal, view) =
        case view of
            ObviousLocalDefinitionView index kind ->
                ( localCount + 1
                , retainBounded
                    (ObviousDefinitionObservation
                        ordinal kind (ObviousDefinitionFromHypothesis index)
                        (summarizeScopedCore <$> atNatural index hypotheses))
                    locals
                , importedCount
                , imported
                )
            ObviousImportedDefinitionView
                    _global kind (ObviousImport index statement) ->
                ( localCount
                , locals
                , importedCount + 1
                , retainBounded
                    (ObviousDefinitionObservation
                        ordinal kind (ObviousDefinitionFromImport index)
                        (Just (summarizeFrozenCore statement)))
                    imported
                )

    retainBounded observation reversed
        | length reversed < diagnosticInputLimit = observation : reversed
        | otherwise = reversed

    finish (localCount, locals, importedCount, imported) =
        (localCount, reverse locals, importedCount, reverse imported)

diagnosticInputLimit :: Int
diagnosticInputLimit = 4

diagnosticCoreNodeLimit :: Int
diagnosticCoreNodeLimit = 96

diagnosticCoreDepthLimit :: Int
diagnosticCoreDepthLimit = 12

diagnosticContextRowLimit :: Int
diagnosticContextRowLimit = 8

diagnosticGlobalLimit :: Int
diagnosticGlobalLimit = 16

diagnosticIntegerDigitLimit :: Integer
diagnosticIntegerDigitLimit = 1000000000000000000000000

data CoreSummaryState global = CoreSummaryState
    !Int
    !(Set.Set global)

summarizeScopedCore
    :: Ord global
    => ScopedCheckedCore global
    -> ObviousCoreSummary global
summarizeScopedCore core =
    State.evalState build (CoreSummaryState diagnosticCoreNodeLimit Set.empty)
  where
    (rows, rowsTruncated) =
        boundedPrefix diagnosticContextRowLimit (scopedCoreContext core)
    build = do
        context <- traverse (summarizeCoreType 0) rows
        coreType <- summarizeCoreType 0 (scopedCoreType core)
        term <- summarizeCanonicalTerm 0 (scopedCoreTerm core)
        pure (ObviousCoreSummary context rowsTruncated coreType term)

summarizeFrozenCore
    :: Ord global
    => FrozenCheckedCore global
    -> ObviousCoreSummary global
summarizeFrozenCore core =
    State.evalState build (CoreSummaryState diagnosticCoreNodeLimit Set.empty)
  where
    build = do
        coreType <- summarizeCoreType 0 (frozenCoreType core)
        term <- summarizeCanonicalTerm 0 (frozenCoreTerm core)
        pure (ObviousCoreSummary [] False coreType term)

summarizeCoreType
    :: Int
    -> CoreType
    -> State (CoreSummaryState global) ObviousTypeSummary
summarizeCoreType depth coreType
    | depth >= diagnosticCoreDepthLimit = pure ObviousTypeTruncated
    | otherwise = do
        available <- consumeSummaryNode
        if not available
            then pure ObviousTypeTruncated
            else case coreType of
                TyProp -> pure ObviousTypeProposition
                TySet -> pure ObviousTypeSet
                TyArrow argument result ->
                    ObviousTypeArrow
                        <$> summarizeCoreType (depth + 1) argument
                        <*> summarizeCoreType (depth + 1) result

summarizeCanonicalTerm
    :: Ord global
    => Int
    -> CanonicalTerm global
    -> State (CoreSummaryState global) (ObviousTermSummary global)
summarizeCanonicalTerm depth term
    | depth >= diagnosticCoreDepthLimit = pure ObviousTermTruncated
    | otherwise = do
        available <- consumeSummaryNode
        if not available
            then pure ObviousTermTruncated
            else summarize term
  where
    child = summarizeCanonicalTerm (depth + 1)
    typeChild = summarizeCoreType (depth + 1)

    summarize = \case
        CBound index -> pure (ObviousBoundVariable index)
        CGlobal global -> summarizeGlobal global
        CIntrinsic intrinsic -> pure (ObviousIntrinsic intrinsic)
        CLogicalSelect coreType ->
            ObviousLogicalSelection <$> typeChild coreType
        COpaqueInteger integer ->
            let small = abs integer < diagnosticIntegerDigitLimit
                rendered =
                    if small
                        then Text.pack (show integer)
                        else if integer < 0 then "-<integer>" else "<integer>"
            in pure (ObviousOpaqueInteger rendered (not small))
        CApp function argument ->
            ObviousApplication <$> child function <*> child argument
        CLam binderType body ->
            ObviousLambda <$> typeChild binderType <*> child body
        CFalsum -> pure ObviousFalsum
        CTruth -> pure ObviousTruth
        CNot proposition -> ObviousNegation <$> child proposition
        CAnd left right -> ObviousConjunction <$> child left <*> child right
        COr left right -> ObviousDisjunction <$> child left <*> child right
        CImp premise conclusion ->
            ObviousImplication <$> child premise <*> child conclusion
        CEq operandType left right ->
            ObviousEquality
                <$> typeChild operandType
                <*> child left
                <*> child right
        CForall binderType body ->
            ObviousUniversal <$> typeChild binderType <*> child body
        CExists binderType body ->
            ObviousExistential <$> typeChild binderType <*> child body

summarizeGlobal
    :: Ord global
    => global
    -> State (CoreSummaryState global) (ObviousTermSummary global)
summarizeGlobal global = do
    CoreSummaryState remaining globals <- State.get
    if global `Set.member` globals
        then pure (ObviousGlobal global)
        else if Set.size globals < diagnosticGlobalLimit
            then do
                State.put
                    (CoreSummaryState remaining (Set.insert global globals))
                pure (ObviousGlobal global)
            else pure ObviousGlobalTruncated

consumeSummaryNode :: State (CoreSummaryState global) Bool
consumeSummaryNode = do
    CoreSummaryState remaining globals <- State.get
    if remaining <= 0
        then pure False
        else do
            State.put (CoreSummaryState (remaining - 1) globals)
            pure True

boundedPrefix :: Int -> [value] -> ([value], Bool)
boundedPrefix limit = go limit []
  where
    go 0 reversed remaining = (reverse reversed, not (null remaining))
    go _remaining reversed [] = (reverse reversed, False)
    go remaining reversed (value : rest) =
        go (remaining - 1) (value : reversed) rest

atNatural :: Natural -> [value] -> Maybe value
atNatural requested = go requested
  where
    go _remaining [] = Nothing
    go 0 (value : _rest) = Just value
    go remaining (_value : rest) = go (remaining - 1) rest

validateObviousRequest
    :: Ord global
    => ObviousBudget
    -> ProofRequirement
    -> CheckedFoundation
    -> GlobalTyping global
    -> [ScopedCheckedCore global]
    -> [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> ScopedCheckedCore global
    -> Either ObviousMalformedRequest (ValidatedObviousRequest global)
validateObviousRequest
        budget requirement foundation globalTyping hypotheses imports
        definitionViews target = do
    let hypothesisCount = fromIntegral (length hypotheses)
    validatedBudget <- validateObviousBudget budget
    unless (scopedCoreType target == TyProp)
        (Left (ObviousTargetNotPropositional (scopedCoreType target)))
    context <-
        first (const ObviousHypothesisMetadataMismatch)
            (KernelProof.scopedProofContext
                foundation
                globalTyping
                (scopedCoreContext target)
                hypotheses)
    validateObviousImports imports
    traverse_
        (validateDefinitionView hypothesisCount)
        definitionViews
    pure
        (ValidatedObviousRequest
            validatedBudget
            requirement
            (SearchEnvironment
                globalTyping imports hypothesisCount
                (definitionViewCatalogue imports definitionViews))
            context
            target)

definitionViewCatalogue
    :: Ord global
    => [ObviousImport global]
    -> [ObviousDefinitionView global]
    -> DefinitionViewCatalogue global
definitionViewCatalogue imports views =
    DefinitionViewCatalogue views importedBuckets localViews citedPredicates
  where
    -- This index is request metadata, built once with the ordinary catalogue.
    -- It selects explicitly cited predicate equations for direct elimination.
    cited = Set.fromList (map obviousImportIndex imports)
    citedPredicates = Map.mapMaybe selectCited importedBuckets
    selectCited bucket =
        let selected = Seq.filter
                (\(_ordinal, imported) ->
                    obviousImportIndex imported `Set.member` cited
                        && predicateEquation (frozenCoreTerm
                            (obviousImportStatement imported)))
                bucket
        in if Seq.null selected then Nothing else Just selected
    predicateEquation = \case
        CForall _binder body -> predicateEquation body
        CEq TyProp left _right -> predicateHead left
        _ -> False
    predicateHead = \case
        CApp function _argument -> predicateHead function
        CGlobal{} -> True
        CIntrinsic Member -> True
        _ -> False

    (importedBuckets, localViews) =
        second reverse
            (foldl' insertView (Map.empty, [])
                (zip [0 ..] views))

    insertView (buckets, locals) (ordinal, view) =
        case view of
            ObviousImportedDefinitionView object kind imported ->
                ( Map.insertWith
                    (\new old -> old <> new)
                    (kind, object)
                    (Seq.singleton (ordinal, imported))
                    buckets
                , locals
                )
            ObviousLocalDefinitionView sourceIndex kind ->
                (buckets, (ordinal, sourceIndex, kind) : locals)

validateObviousBudget
    :: ObviousBudget
    -> Either ObviousMalformedRequest ValidatedObviousBudget
validateObviousBudget budget = do
    traverse_
        (uncurry validateImplementationLimit)
        [ (ObviousFocusedWorkLimit, obviousFocusedWorkLimit budget)
        , (ObviousRefutationWorkLimit, obviousRefutationWorkLimit budget)
        , (ObviousGroundTermLimit, obviousGroundTermLimit budget)
        , (ObviousBranchNodeLimit, obviousBranchNodeLimit budget)
        , (ObviousRuleInstanceLimit, obviousRuleInstanceLimit budget)
        ]
    pure (ValidatedObviousBudget budget)

validateImplementationLimit
    :: ObviousLimit
    -> Word
    -> Either ObviousMalformedRequest ()
validateImplementationLimit limit amount =
    unless
        (toInteger amount <= toInteger (maxBound :: Int))
        (Left (ObviousLimitExceedsImplementationCapacity limit amount))

validateObviousImports
    :: [ObviousImport global]
    -> Either ObviousMalformedRequest ()
validateObviousImports =
    go Set.empty
  where
    go _seen [] = pure ()
    go seen (ObviousImport index statement : rest) = do
        unless (frozenCoreType statement == TyProp)
            (Left
                (ObviousImportNotPropositional
                    index (frozenCoreType statement)))
        if index `Set.member` seen
            then Left (ObviousDuplicateImportIx index)
            else go (Set.insert index seen) rest

validateDefinitionView
    :: Natural
    -> ObviousDefinitionView global
    -> Either ObviousMalformedRequest ()
validateDefinitionView hypothesisCount = \case
    ObviousImportedDefinitionView
            _global _kind (ObviousImport index statement) ->
        unless (frozenCoreType statement == TyProp)
            (Left
                (ObviousDefinitionViewNotPropositional
                    index (frozenCoreType statement)))
    ObviousLocalDefinitionView index _kind ->
        unless (index < hypothesisCount)
            (Left (ObviousLocalDefinitionViewOutOfRange index))

emptyObviousStatistics :: ObviousBudget -> ObviousStatistics
emptyObviousStatistics budget =
    ObviousStatistics
        { statisticsEffectiveBudget = budget
        , statisticsBreadthObservations = []
        , statisticsFocusedTierOutcome = ObviousTierNotStarted
        , statisticsRefutationTierOutcome = ObviousTierNotStarted
        , statisticsFocusedWorkConsumed = 0
        , statisticsScopeInventory = (0, 0)
        , statisticsRefutationWorkConsumed = 0
        , statisticsConversionWorkConsumed = 0
        , statisticsBranchNodesCreated = 0
        , statisticsTermsAdmitted = 0
        , statisticsSignedFormulasAdmitted = 0
        , statisticsEqualityEventsProcessed = 0
        , statisticsRuleInstancesAdmitted = 0
        , statisticsFactDomainsStarted = 0
        , statisticsFactDomainsDeferred = False
        , statisticsWitnessAttempts = 0
        , statisticsWitnessesDeferred = False
        , statisticsExistentialOpenings = 0
        , statisticsExistentialsDeferred = False
        , statisticsExtensionalityAttempts = 0
        , statisticsExtensionalityDeferred = False
        , statisticsEndpointAttempts = 0
        , statisticsEndpointsDeferred = False
        , statisticsEndpointGuardWaits = 0
        , statisticsPremiseQueriesStarted = 0
        , statisticsPremiseQueriesDeferred = False
        , statisticsUniversalAttempts = 0
        , statisticsUniversalHintSteps = 0
        , statisticsUniversalsDeferred = False
        , statisticsPendingFactDomainOpportunities = 0
        }

completedObviousStatistics
    :: ObviousBudget -> ObviousSearchState global
    -> Either (ObviousFailure global) (ObviousProof global) -> ObviousStatistics
completedObviousStatistics budget finalState result =
    ObviousStatistics
        { statisticsEffectiveBudget = budget
        , statisticsBreadthObservations = []
        , statisticsFocusedTierOutcome = case result of
            Left failure | isFocusedInfrastructureFailure failure && groundOutcome /= ObviousTierIntegrityFailure ->
                ObviousTierIntegrityFailure
            _ -> fromMaybe (if Seq.null queries then focusedTierOutcome result else ObviousTierNotCompleted)
                (searchRootFocusedOutcome finalState)
        , statisticsRefutationTierOutcome = groundOutcome
        , statisticsFocusedWorkConsumed = obviousFocusedWorkLimit budget - searchRemainingFocusedWork finalState
        , statisticsScopeInventory =
            let binders = length [() | FocusedContext FocusedBinderScope{} _ <- toList (searchFocusedContexts finalState)]
                families = Seq.length (ownedGroundFamilies (searchGroundOwner finalState))
            -- The private observation must not retain the completed search.
            in binders `seq` families `seq` (binders, families)
        , statisticsRefutationWorkConsumed = obviousRefutationWorkLimit budget - groundWork (searchRemainingGround finalState)
        , statisticsConversionWorkConsumed = Conversion.conversionPoolAmount (obviousConversionPool budget)
            - Conversion.conversionPoolAmount (searchRemainingConversionPool finalState)
        , statisticsBranchNodesCreated = sum (Refutation.refutationBranchNodes . fst <$> observations)
        , statisticsTermsAdmitted = sum (Refutation.refutationTerms . fst <$> observations)
        , statisticsSignedFormulasAdmitted = sum (Refutation.refutationSignedFormulas . fst <$> observations)
        , statisticsEqualityEventsProcessed = sum (Refutation.refutationEqualityEvents . fst <$> observations)
        , statisticsRuleInstancesAdmitted = sum (Refutation.refutationRuleInstances . fst <$> observations)
        , statisticsFactDomainsStarted = ownedGroundVariantStarts (searchGroundOwner finalState)
        , statisticsFactDomainsDeferred = ownedGroundVariantsDeferred (searchGroundOwner finalState)
        , statisticsWitnessAttempts = searchWitnessAttempts finalState
        , statisticsWitnessesDeferred = searchWitnessesDeferred finalState
        , statisticsExistentialOpenings = searchExistentialOpenings finalState
        , statisticsExistentialsDeferred = searchExistentialsDeferred finalState
        , statisticsExtensionalityAttempts = searchExtensionalityAttempts finalState
        , statisticsExtensionalityDeferred = searchExtensionalityDeferred finalState
        , statisticsEndpointAttempts = searchEndpointAttempts finalState
        , statisticsEndpointsDeferred = searchEndpointsDeferred finalState
        , statisticsEndpointGuardWaits = searchEndpointGuardWaits finalState
        , statisticsPremiseQueriesStarted = searchPremiseQueriesStarted finalState
        , statisticsPremiseQueriesDeferred = searchPremiseQueriesDeferred finalState
        , statisticsUniversalAttempts = sum (Refutation.refutationUniversalAttempts . fst <$> observations)
        , statisticsUniversalHintSteps = sum (Refutation.refutationUniversalHintSteps . fst <$> observations)
        , statisticsUniversalsDeferred = any (Refutation.refutationUniversalsDeferred . fst) observations
        , statisticsPendingFactDomainOpportunities = foldl' (\count active ->
            if activationOutside active && activationOpportunity active then count + 1 else count)
            0 (ownedGroundActivations (searchGroundOwner finalState))
        }
  where
    queries = ownedGroundQueries (searchGroundOwner finalState)
    observations = groundQueryObservation <$> toList queries
    groundOutcome = foldl' (\earlier (_statistics, current) ->
        if outcomeRank current > outcomeRank earlier then current else earlier)
        (maybe ObviousTierNotStarted (focusedTierOutcome . Left) (searchGroundAdmissionFailure finalState)) observations
    -- Reports summarize attempted components, not a serial tier chronology.
    -- A pending query prevents a claim of saturation, and any infrastructure
    -- failure remains visible even if another query previously built a proof.
    outcomeRank = \case
        ObviousTierNotStarted -> 0 :: Int
        ObviousTierNoProof -> 1
        ObviousTierNotCompleted -> 2
        ObviousTierUnsupported -> 3
        ObviousTierResourceExhausted{} -> 4
        ObviousTierCandidateBuilt -> 5
        ObviousTierIntegrityFailure -> 6

groundQueryObservation :: OwnedGroundQuery global -> (Refutation.RefutationStatistics, ObviousTierOutcome)
groundQueryObservation (OwnedGroundQuery _scope _typing _domainScope _domain status support _inputCursor) = case status of
    OwnedGroundRunning session -> (Refutation.refutationSessionStatistics session,
        if isJust (support >>= \(OwnedGroundSupport _sources ordinary) -> ordinary)
            then ObviousTierCandidateBuilt else ObviousTierNotCompleted)
    OwnedGroundBlocked statistics failure _session -> (statistics, refutationTierOutcome (Left failure))
    OwnedGroundFinished statistics result -> (statistics, refutationTierOutcome result)
    OwnedGroundCertificationFailed statistics failure -> (statistics, focusedTierOutcome (Left failure))

refutationTierOutcome
    :: Either
        Refutation.RefutationFailure
        result
    -> ObviousTierOutcome
refutationTierOutcome = \case
    Right _candidate -> ObviousTierCandidateBuilt
    Left Refutation.RefutationSaturated -> ObviousTierNoProof
    Left Refutation.RefutationCanonicalSupportMissing -> ObviousTierNoProof
    Left Refutation.RefutationWorkExhausted ->
        ObviousTierResourceExhausted ObviousRefutationWorkLimit
    Left (Refutation.RefutationConversionLimitExhausted owner _limit) ->
        ObviousTierResourceExhausted (conversionOwnerLimit owner)
    Left Refutation.RefutationConversionFailed{} -> ObviousTierIntegrityFailure
    Left Refutation.RefutationRequiredConversionNotConvertible -> ObviousTierIntegrityFailure
    Left Refutation.RefutationConversionAccountingInvariant{} -> ObviousTierIntegrityFailure
    Left Refutation.RefutationGroundTermsExhausted ->
        ObviousTierResourceExhausted ObviousGroundTermLimit
    Left Refutation.RefutationBranchesExhausted ->
        ObviousTierResourceExhausted ObviousBranchNodeLimit
    Left Refutation.RefutationRuleInstancesExhausted ->
        ObviousTierResourceExhausted ObviousRuleInstanceLimit
    Left Refutation.RefutationUnsupportedTermOutsideUniverse ->
        ObviousTierUnsupported
    Left Refutation.RefutationUndeterminedParameter{} ->
        ObviousTierNoProof
    Left Refutation.RefutationIntegrityFailure{} ->
        ObviousTierIntegrityFailure
    Left Refutation.RefutationInternalFailure{} ->
        ObviousTierIntegrityFailure

focusedTierOutcome
    :: Either (ObviousFailure global) (ObviousProof global)
    -> ObviousTierOutcome
focusedTierOutcome = \case
    Right _proof -> ObviousTierCandidateBuilt
    Left (ObviousResourceExhausted limit) ->
        ObviousTierResourceExhausted limit
    Left ObviousUnsupportedHigherOrderInstantiation ->
        ObviousTierUnsupported
    Left ObviousIntegrityFailure{} ->
        ObviousTierIntegrityFailure
    Left ObviousConversionFailed{} -> ObviousTierIntegrityFailure
    Left ObviousRequiredConversionNotConvertible -> ObviousTierIntegrityFailure
    Left ObviousConversionAccountingInvariant{} -> ObviousTierIntegrityFailure
    Left ObviousMalformedInput{} ->
        ObviousTierIntegrityFailure
    Left _failure ->
        ObviousTierNoProof

consumeSearchStep :: State (ObviousSearchState global) Bool
consumeSearchStep = do
    remaining <- State.gets searchRemainingFocusedWork
    if remaining == 0
        then pure False
        else do
            State.modify'
                (\state ->
                    state
                        { searchRemainingFocusedWork = remaining - 1
                        })
            pure True

getFocusedWorkBudget :: State (ObviousSearchState global) Word
getFocusedWorkBudget =
    State.gets searchRemainingFocusedWork

putFocusedWorkBudget :: Word -> State (ObviousSearchState global) ()
putFocusedWorkBudget remaining =
    State.modify'
        (\state ->
            state {searchRemainingFocusedWork = remaining})

getConversionPool :: State (ObviousSearchState global) Conversion.ConversionPool
getConversionPool =
    State.gets searchRemainingConversionPool

putConversionPool :: Conversion.ConversionPool -> State (ObviousSearchState global) ()
putConversionPool remaining =
    State.modify'
        (\state ->
            state {searchRemainingConversionPool = remaining})

obviousCountedFailure
    :: (error -> ObviousFailure global)
    -> CountedCoreFailure error
    -> ObviousFailure global
obviousCountedFailure operationFailure = \case
    CountedCoreStructuralWorkExhausted ->
        ObviousResourceExhausted ObviousFocusedWorkLimit
    CountedCoreOperationFailed failure ->
        operationFailure failure

runCountedKernel
    :: KernelProof.CountedProof global value
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) value)
runCountedKernel operation = do
    structural <- getFocusedWorkBudget
    pool <- getConversionPool
    let (result, afterStructural, afterPool) = KernelProof.runCountedProof structural pool operation
    putFocusedWorkBudget afterStructural
    putConversionPool afterPool
    pure (first (obviousCountedFailure kernelFailure) result)

-- Only actual conversion limits are resource results; required-conversion
-- mismatch and every other construction defect remain fatal.
kernelFailure :: KernelProof.KernelProofBuildError -> ObviousFailure global
kernelFailure = \case
    KernelProof.ProofConversionLimitExhausted owner _limit ->
        ObviousResourceExhausted case owner of
            KernelProof.ProofConversionOperationLimit -> ObviousConversionOperationLimit
            KernelProof.ProofConversionAggregatePool -> ObviousConversionPoolLimit
    failure -> ObviousIntegrityFailure failure

-- The protected fixtures' successful preparation/construction operations cost
-- at most 399 units. This fixed slice is the first larger power of two. It is
-- policy only: production ceilings and the request's real pool are unchanged.
preparatoryConversionLimit :: Conversion.ConversionLimit
preparatoryConversionLimit = Conversion.conversionLimit 512

runPreparedKernel
    :: KernelProof.CountedProof global value
    -> State (ObviousSearchState global) (PreparationResult (ObviousFailure global) value)
runPreparedKernel operation = do
    structural <- getFocusedWorkBudget
    pool <- getConversionPool
    let (result, afterStructural, afterPool) =
            Effort.runPreparatoryBuilder preparatoryConversionLimit structural pool (\work conversionPool ->
                KernelProof.runCountedProof work conversionPool operation)
    putFocusedWorkBudget afterStructural
    putConversionPool afterPool
    pure case result of
        NeedsMoreEffort offered -> NeedsMoreEffort offered
        PreparationFinished outcome -> PreparationFinished
            (first (obviousCountedFailure kernelFailure) outcome)

-- Only a blocked operation carries its previous effective allowance. A resumed
-- operation may run once, with a strictly larger allowance from the same owner.
-- Successful neighbouring operations never enter this retry state.
data PreparationEffort = SmallPreparation | FullPreparation !Conversion.ConversionLimit

preparationIsDeferred :: PreparationEffort -> Bool
preparationIsDeferred SmallPreparation = False
preparationIsDeferred FullPreparation{} = True

runKernelPreparation
    :: PreparationEffort
    -> KernelProof.CountedProof global value
    -> State (ObviousSearchState global) (PreparationResult (ObviousFailure global) value)
runKernelPreparation SmallPreparation operation = runPreparedKernel operation
runKernelPreparation (FullPreparation offered) operation = do
    more <- canEscalatePreparation offered
    if more then PreparationFinished <$> runCountedKernel operation
        else pure (PreparationFinished (Left (ObviousResourceExhausted ObviousConversionPoolLimit)))

runConversionPreparation
    :: PreparationEffort
    -> (Conversion.ConversionLimit -> Conversion.ConversionReport value)
    -> State (ObviousSearchState global) (PreparationResult (ObviousFailure global) value)
runConversionPreparation (FullPreparation offered) operation = do
    more <- canEscalatePreparation offered
    if more then PreparationFinished <$> runConversion operation
        else pure (PreparationFinished (Left (ObviousResourceExhausted ObviousConversionPoolLimit)))
runConversionPreparation SmallPreparation operation = do
    pool <- getConversionPool
    case Effort.runPreparatoryConversion preparatoryConversionLimit pool operation of
        Left (ObviousConversionPoolAccountingInvariant cost incoming) ->
            pure (PreparationFinished (Left (ObviousConversionAccountingInvariant cost incoming)))
        Right (owner, remaining, result) -> do
            putConversionPool remaining
            pure case result of
                NeedsMoreEffort offered -> NeedsMoreEffort offered
                PreparationFinished completed -> PreparationFinished
                    (first (conversionFailure owner) completed)

canEscalatePreparation
    :: Conversion.ConversionLimit -> State (ObviousSearchState global) Bool
canEscalatePreparation offered = do
    pool <- getConversionPool
    pure (Conversion.conversionPoolAmount pool > Conversion.conversionLimitAmount offered)

conversionFailure :: ObviousConversionLimitOwner -> Conversion.ConversionFailure -> ObviousFailure global
conversionFailure owner = \case
    Conversion.ConversionLimitExhausted _ -> ObviousResourceExhausted (conversionOwnerLimit owner)
    failure -> ObviousConversionFailed failure

conversionOwnerLimit :: ObviousConversionLimitOwner -> ObviousLimit
conversionOwnerLimit = \case
    ObviousConversionOperationOwner -> ObviousConversionOperationLimit
    ObviousConversionPoolOwner -> ObviousConversionPoolLimit

runConversion
    :: (Conversion.ConversionLimit -> Conversion.ConversionReport value)
    -> State (ObviousSearchState global) (Either (ObviousFailure global) value)
runConversion operation = do
    pool <- getConversionPool
    case runObviousConversion pool operation of
        Left (ObviousConversionPoolAccountingInvariant cost incoming) ->
            pure (Left (ObviousConversionAccountingInvariant cost incoming))
        Right (owner, remaining, result) -> do
            putConversionPool remaining
            pure case result of
                Left (Conversion.ConversionLimitExhausted _limit) ->
                    Left (ObviousResourceExhausted (conversionOwnerLimit owner))
                Left failure -> Left (ObviousConversionFailed failure)
                Right value -> Right value

headNeedsReduction
    :: Bool -> CanonicalTerm global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) Bool)
headNeedsReduction applied term = do
    work <- consumeSearchStep
    if not work then pure focusedWorkExhausted else case term of
        CApp function _argument -> headNeedsReduction True function
        CLam{} -> pure (Right applied)
        _ -> pure (Right False)

conversionProof
    :: Eq global
    => KernelProof.ProofContext global
    -> KernelProof.BuiltProof global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (KernelProof.BuiltProof global))
conversionProof context proof target = do
    runCountedKernel
        (KernelProof.countedConversionProof
                context proof target)


reverseEqualityProof
    :: Eq global
    => KernelProof.ProofContext global
    -> KernelProof.BuiltProof global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (KernelProof.BuiltProof global))
reverseEqualityProof context proof = do
    runCountedKernel
        (KernelProof.countedEqualityReverseProof
                context proof)


convertible
    :: Eq global
    => SearchEnvironment global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) Bool)
convertible (SearchEnvironment globalType _imports _hypotheses _views) left right =
    fmap (fmap (== Conversion.Convertible))
        (runConversion (\limit -> Conversion.convertibleChecked globalType limit left right))

scopedIdentity
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Bool)
scopedIdentity left right = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            countedScopedCoreIdentity structural left right
    putFocusedWorkBudget remaining
    pure (first (obviousCountedFailure absurd) result)

scopedIdentityWithObservation
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (CountedIdentityResult, Natural))
scopedIdentityWithObservation left right = do
    before <- getFocusedWorkBudget
    let (result, remaining) =
            countedScopedCoreIdentityDetailed before left right
    putFocusedWorkBudget remaining
    pure
        ((\identity -> (identity, fromIntegral (before - remaining)))
            <$> first (obviousCountedFailure absurd) result)

candidateDifference
    :: CoreIdentityDifference
    -> (MismatchClass, CandidateStructuralDifference)
candidateDifference
        (CoreIdentityDifference kind path truncated) =
    ( case kind of
        CoreTypeDifference -> BinderMismatch
        CoreConstructorDifference -> SyntacticMismatch
        CoreAtomDifference -> SyntacticMismatch
    , CandidateStructuralDifference
        (map differenceStep path) truncated
    )
  where
    differenceStep = \case
        CoreFirstChild -> CandidateFirstChild
        CoreSecondChild -> CandidateSecondChild
        CoreBodyChild -> CandidateBodyChild

coreTypeIdentity
    :: CoreType
    -> CoreType
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Bool)
coreTypeIdentity left right = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            countedCoreTypeIdentity structural left right
    putFocusedWorkBudget remaining
    pure (first (obviousCountedFailure absurd) result)

canonicalIdentity
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Bool)
canonicalIdentity left right = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            countedCanonicalIdentity structural left right
    putFocusedWorkBudget remaining
    pure (first (obviousCountedFailure absurd) result)

canonicalIdentityWithDifference
    :: Eq global
    => CanonicalTerm global
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            CountedIdentityResult)
canonicalIdentityWithDifference left right = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            countedCanonicalIdentityDetailed structural left right
    putFocusedWorkBudget remaining
    pure (first (obviousCountedFailure absurd) result)

shiftCanonicalCounted
    :: Natural
    -> Natural
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (CanonicalTerm global))
shiftCanonicalCounted amount cutoff term = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            countedShiftCanonical structural amount cutoff term
    putFocusedWorkBudget remaining
    pure (first (obviousCountedFailure absurd) result)

obviousTemplateError
    :: Template.TemplateError
    -> ObviousFailure global
obviousTemplateError = \case
    Template.TemplateContextMismatch expected actual ->
        ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
            ("prepared template context mismatch: " <> fromString (show (expected, actual))))
    Template.TemplateCheckFailed failure ->
        ObviousIntegrityFailure (KernelProof.ProofTermIllTyped failure)
    Template.TemplateInstantiationFailed failure ->
        ObviousIntegrityFailure
            (KernelProof.ProofSemanticsFailed
                (KernelSemantics.KernelScopedInstantiationFailed failure))
    Template.TemplateExpectedProposition _coreType ->
        ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch
                "theorem template is not propositional")

runCountedTemplate
    :: ( Word
         -> ( Either
                (CountedCoreFailure Template.TemplateError)
                value
            , Word
            )
       )
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) value)
runCountedTemplate operation = do
    structural <- getFocusedWorkBudget
    let (result, remaining) = operation structural
    putFocusedWorkBudget remaining
    pure
        (first
            (obviousCountedFailure obviousTemplateError)
            result)

missingFocusedTemplateSlots
    :: Template.BinderEnvironment
    -> Template.TemplateSubstitution global
    -> State (ObviousSearchState other)
        (Either (ObviousFailure other) [Template.MatcherSlot])
missingFocusedTemplateSlots binders substitutions = do
    structural <- getFocusedWorkBudget
    let (result, remaining) =
            Template.missingTemplateSlotsCounted
                structural binders substitutions
    putFocusedWorkBudget remaining
    pure
        (case result of
            Left CountedCoreStructuralWorkExhausted ->
                Left
                    (ObviousResourceExhausted
                        ObviousFocusedWorkLimit)
            Right missing -> Right missing)

closeFocusedTemplate
    :: Template.CompiledTemplate global
    -> Template.TemplateSubstitution global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (Template.TemplateClosure global))
closeFocusedTemplate template substitutions =
    runCountedTemplate
        (\structural ->
            Template.closeTemplate
                structural template substitutions)

-- | Aggregate only the selected authority leaves.  Both input sets are
-- visited in ascending order, so a duplicate occurrence is charged before
-- the shallow ImportIx insertion discovers it.  The accumulator is private
-- until the complete fold succeeds.
combineCandidateDependencies
    :: CandidateDependencies
    -> CandidateDependencies
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) CandidateDependencies)
combineCandidateDependencies left right = do
    entered <- consumeSearchStep
    if not entered
        then pure exhausted
        else
            go
                Set.empty
                (Set.toAscList (candidateImports left))
                (Set.toAscList (candidateImports right))
  where
    go imports [] [] =
        pure
            (Right
                (CandidateDependencies
                    imports
                    (candidateCanonicalSource left <|> candidateCanonicalSource right)))
    go imports (leftIndex : leftRest) [] =
        visit imports leftIndex leftRest []
    go imports [] (rightIndex : rightRest) =
        visit imports rightIndex [] rightRest
    go imports leftRows@(leftIndex : leftRest)
            rightRows@(rightIndex : rightRest)
        | leftIndex < rightIndex =
            visit imports leftIndex leftRest rightRows
        | rightIndex < leftIndex =
            visit imports rightIndex leftRows rightRest
        | otherwise = do
            afterLeft <- consumeOccurrence imports leftIndex
            case afterLeft of
                Left failure -> pure (Left failure)
                Right withLeft ->
                    visit withLeft rightIndex leftRest rightRest

    visit imports index leftRows rightRows = do
        consumed <- consumeOccurrence imports index
        case consumed of
            Left failure -> pure (Left failure)
            Right updated -> go updated leftRows rightRows

    consumeOccurrence imports index = do
        hasWork <- consumeSearchStep
        if not hasWork
            then pure exhausted
            else pure (Right (Set.insert index imports))

    exhausted =
        Left (ObviousResourceExhausted ObviousFocusedWorkLimit)

-- Scope admission is generative: matching printed assumptions or binder types
-- cannot merge distinct assumption lineages. Callers retain the context returned
-- by the corresponding checked introduction operation.
admitFocusedContext
    :: FocusedScopeLineage global
    -> KernelProof.ProofContext global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) FocusedContextId)
admitFocusedContext = admitContextWith FocusedScopeWork

admitContextWith
    :: ScopeWork -> FocusedScopeLineage global -> KernelProof.ProofContext global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) FocusedContextId)
admitContextWith owner lineage context = Except.runExceptT do
    scopeChargeTo owner
    contexts <- State.gets searchFocusedContexts
    let next = Seq.length contexts
    when (next == maxBound) (scopeIntegrity "focused scope identifier overflow")
    State.modify' (\state -> state
        { searchFocusedContexts = contexts Seq.|> FocusedContext lineage context })
    pure (FocusedContextId next)

admitGroundFamily
    :: FocusedContextId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> [ObviousImport global]
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) GroundEligibility)
admitGroundFamily contextId context target imports =
    admitFamilyWith FocusedScopeWork contextId context target imports Seq.empty

admitFamilyWith
    :: ScopeWork -> FocusedContextId -> KernelProof.ProofContext global
    -> ScopedCheckedCore global -> [ObviousImport global] -> Seq (GroundViewSelection global)
    -> State (ObviousSearchState global) (Either (ObviousFailure global) GroundEligibility)
admitFamilyWith owner contextId context target imports views = Except.runExceptT do
    scopeChargeTo owner
    families <- State.gets (ownedGroundFamilies . searchGroundOwner)
    let next = Seq.length families
    when (next == maxBound) (scopeIntegrity "ground family identifier overflow")
    State.modify' (\state -> state
        { searchGroundOwner = (searchGroundOwner state)
            { ownedGroundFamilies = families Seq.|> GroundFamily contextId context target imports views Map.empty Nothing Map.empty Map.empty } })
    pure (SeedEligible (GroundFamilyId next))

-- A selected checked goal view extends this family rather than replacing its
-- anchor. Exact variants are shared, and directed view cycles are rejected
-- before they can create fresh obligation or catalogue identities.
selectedGoalFamily
    :: Eq global => FocusedRequest global -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) GroundEligibility)
selectedGoalFamily request target = selectGoalFamilyWith FocusedScopeWork request (SelectedGoalView target)

selectGoalFamilyWith
    :: Eq global => ScopeWork -> FocusedRequest global -> GroundViewSelection global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) GroundEligibility)
selectGoalFamilyWith owner request selection = case focusedEligibility request of
    FocusedOnly -> pure (Right FocusedOnly)
    retained@ExistingFamily{} -> pure (Right retained)
    SeedEligible (GroundFamilyId parentIndex) -> Except.runExceptT do
        scopeChargeTo owner
        families <- State.gets (ownedGroundFamilies . searchGroundOwner)
        parent <- maybe (scopeIntegrity "a selected goal view lost its family anchor") pure
            (Seq.lookup parentIndex families)
        _ <- scopeAncestorDistance owner (ScopeId (familyScope parent))
            (ScopeId (focusedContextId request))
        let variants = Map.findWithDefault [] (focusedContextId request) (familyViewVariants parent)
        existing <- findVariant variants
        case existing of
            Just identifier -> pure (SeedEligible identifier)
            Nothing -> do
                cyclic <- anyTarget (SelectedGoalView (familyAnchor parent) : toList (familyViewLineage parent))
                when cyclic (Except.throwE (ObviousRepeatedState (case selection of
                    SelectedGoalView target -> target
                    SelectedDirections{} -> focusedTarget request)))
                scopeChargeTo owner
                let index = Seq.length families
                    identifier = GroundFamilyId index
                when (index == maxBound) (scopeIntegrity "selected-view family identifier overflow")
                let child = parent
                        { familyScope = focusedContextId request
                        , familyContext = focusedContext request
                        , familyViewLineage = familyViewLineage parent Seq.|> selection
                        , familyViewVariants = Map.empty
                        , familyDomainQuery = Nothing
                        , familyQueries = Map.empty
                        , familyTypeInventories = Map.empty }
                    updated = parent {familyViewVariants = Map.insert (focusedContextId request)
                        (variants <> [(selection, identifier)]) (familyViewVariants parent)}
                State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                    {ownedGroundFamilies = Seq.update parentIndex updated families Seq.|> child}})
                pure (SeedEligible identifier)
  where
    same previous = sameGroundSelection owner previous selection
    anyTarget [] = pure False
    anyTarget (term : rest) = same term >>= \matches -> if matches then pure True else anyTarget rest
    findVariant [] = pure Nothing
    findVariant ((term, identifier) : rest) = same term >>= \matches ->
        if matches then pure (Just identifier) else findVariant rest

sameGroundSelection
    :: Eq global => ScopeWork -> GroundViewSelection global -> GroundViewSelection global
    -> Scoped request global Bool
sameGroundSelection owner previous selection = case (previous, selection) of
    (SelectedGoalView left, SelectedGoalView right) -> exact left right
    (SelectedDirections leftForward leftBackward, SelectedDirections rightForward rightBackward) ->
        exact leftForward rightForward >>= \matched -> if matched then exact leftBackward rightBackward else pure False
    _ -> scopeChargeTo owner >> pure False
  where
    exact left right = runScopeCore owner absurd (\work -> countedScopedCoreIdentity work left right)

-- Validate the target against its nominal context once per lookup. Every
-- stored target has passed this check, so comparisons within a context bucket
-- need only compare canonical terms; their checked types follow from the same
-- immutable typing environment. Rechecking the binder list per candidate made
-- otherwise small searches cubic in the number of local binders and facts.
checkFocusedTargetScope
    :: FocusedContextId -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) ())
checkFocusedTargetScope contextId target = Except.runExceptT do
    context <- scopeContext (ScopeId contextId)
    same <- runScopedCore (\work -> countedCoreTypeListIdentity work
        (KernelProof.proofContextTypes context) (scopedCoreContext target))
    unless same (scopeIntegrity "a focused target is outside its nominal context")

-- Scope, source policy, and inherited eligibility select a bucket before any
-- counted canonical-term comparison. No source or proof authority is merged.
internFocusedObligation
    :: Ord global
    => FocusedContextId
    -> FocusedSourcePolicy
    -> GroundEligibility
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) FocusedObligationId)
internFocusedObligation = internFocusedObligationFor OrdinaryObligation

internFocusedObligationFor
    :: Ord global
    => FocusedObligationPurpose -> FocusedContextId -> FocusedSourcePolicy
    -> GroundEligibility -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) FocusedObligationId)
internFocusedObligationFor purpose contextId policy eligibility target = do
    checked <- checkFocusedTargetScope contextId target
    case checked of
        Left failure -> pure (Left failure)
        Right () -> findBucket
  where
    findBucket = focusedObligationHead (scopedCoreTerm target) >>= \case
        Left failure -> pure (Left failure)
        Right targetHead -> do
            let discriminator = (contextId, policy, purpose, targetHead)
            candidates <- State.gets
                (Map.findWithDefault Seq.empty eligibility . Map.findWithDefault Map.empty discriminator
                    . searchFocusedObligationBuckets)
            findExisting discriminator (Seq.viewl candidates)

    findExisting discriminator Seq.EmptyL = admit discriminator
    findExisting discriminator (existingId@(FocusedObligationId position) Seq.:< rest) = do
        hasWork <- consumeSearchStep
        if not hasWork then pure focusedWorkExhausted else do
            rows <- State.gets searchFocusedObligations
            case Seq.lookup position rows of
                Nothing -> pure (Left (ObviousIntegrityFailure
                    (KernelProof.ProofStructuralCompositionMismatch
                        "focused-obligation bucket contains an unknown ID")))
                Just (FocusedObligation existingTarget _certificates _subscribed) ->
                    canonicalIdentity (scopedCoreTerm existingTarget) (scopedCoreTerm target) >>= \case
                        Left failure -> pure (Left failure)
                        Right True -> pure (Right existingId)
                        Right False -> findExisting discriminator (Seq.viewl rest)

    admit discriminator = do
        hasWork <- consumeSearchStep
        if not hasWork then pure focusedWorkExhausted else do
            next <- State.gets searchNextFocusedObligationId
            canonical <- State.gets searchCanonicalRequest
            let obligationId = FocusedObligationId next
                certificates = if canonical then FocusedSupportedCertificates Nothing Nothing
                    else FocusedSingleCertificate Nothing
            State.modify' (\state -> state
                { searchNextFocusedObligationId = next + 1
                , searchFocusedObligations = searchFocusedObligations state Seq.|> FocusedObligation target certificates False
                , searchFocusedObligationBuckets = Map.alter
                    (Just . Map.insertWith (\new old -> old <> new) eligibility (Seq.singleton obligationId)
                        . fromMaybe Map.empty) discriminator
                    (searchFocusedObligationBuckets state)
                })
            pure (Right obligationId)

-- Evidence keeps its exact nominal scope and permitted-source policy. A
-- certificate may come from another ground eligibility, without granting that
-- eligibility to its consumer. Endpoint producers are deliberately excluded.
existingFocusedEvidenceOwners
    :: Ord global
    => FocusedRequest global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) [FocusedObligationId])
existingFocusedEvidenceOwners request = Except.runExceptT do
    Except.ExceptT (checkFocusedTargetScope (focusedContextId request) (focusedTarget request))
    headKey <- Except.ExceptT (focusedObligationHead (scopedCoreTerm (focusedTarget request)))
    buckets <- State.gets (Map.findWithDefault Map.empty
        (focusedContextId request, focusedSourcePolicy request, OrdinaryObligation, headKey)
        . searchFocusedObligationBuckets)
    matching <- forM (foldMap toList buckets) \identifier@(FocusedObligationId position) -> do
        scopeCharge
        row <- State.gets (Seq.lookup position . searchFocusedObligations)
        case row of
            Nothing -> scopeIntegrity "an evidence bucket lost its obligation"
            Just (FocusedObligation target _ _) -> do
                same <- Except.ExceptT (canonicalIdentity (scopedCoreTerm target) (scopedCoreTerm (focusedTarget request)))
                pure (if same then Just identifier else Nothing)
    pure (catMaybes matching)

reverseEndpointTarget
    :: FocusedRequest global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ScopedCheckedCore global))
reverseEndpointTarget request = case splitScopedEquality (focusedTarget request) of
    Nothing -> pure (Left (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "endpoint request is not an equality")))
    Just (ty, left, right) -> checkedProposition (focusedContext request)
        (CEq ty (scopedCoreTerm right) (scopedCoreTerm left))

enterEndpointOwner
    :: Ord global
    => FocusedRequest global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedRequest global, FocusedObligationId, Bool))
enterEndpointOwner request = Except.runExceptT do
    let intern = internFocusedObligationFor EndpointObligation (focusedContextId request)
            (focusedSourcePolicy request) FocusedOnly
    identifier <- Except.ExceptT (intern (focusedTarget request))
    known <- State.gets (Map.lookup identifier . searchEndpointOwners)
    (owner@(FocusedObligationId position), reversed) <- case known of
        Just association -> pure association
        Nothing -> do
            opposite <- Except.ExceptT (reverseEndpointTarget request)
            reverseId <- Except.ExceptT (intern opposite)
            State.modify' (\state -> state {searchEndpointOwners =
                Map.insert identifier (identifier, False)
                    (Map.insert reverseId (identifier, True) (searchEndpointOwners state))})
            pure (identifier, False)
    row <- State.gets (Seq.lookup position . searchFocusedObligations)
    statement <- case row of
        Nothing -> scopeIntegrity "an endpoint request lost its retained owner"
        Just (FocusedObligation target _ _) -> pure target
    pure (request {focusedTarget = statement, focusedEligibility = FocusedOnly,
        focusedObligation = Just owner}, owner, reversed)

-- Endpoint application is a demand for a supplied equation. Do not unfold an
-- unrelated predicate to discover whether its representation contains one;
-- ordinary theorem search retains that broader opportunity. Inspect only the
-- elimination spine and conjunction projections, never the guards or operands.
-- A concrete equality needs no application and stays with the existing graph.
endpointTheoremSources
    :: Eq global => FocusedRequest global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) [ObviousProof global])
endpointTheoremSources request = Except.runExceptT do
    let key = (focusedContextId request, focusedSourcePolicy request)
    cached <- State.gets (Map.lookup key . searchEndpointSources)
    case cached of
        Just selected -> pure selected
        Nothing -> do
            sources <- Except.ExceptT (availableProofs (focusedEnvironment request)
                (focusedContextId request) (focusedContext request))
            selected <- fmap catMaybes $ forM sources \source -> do
                eligible <- equationSpine False (scopedCoreTerm (obviousProofStatement source))
                pure (if eligible then Just source else Nothing)
            scopeCharge
            State.modify' (\state -> state {searchEndpointSources =
                Map.insert key selected (searchEndpointSources state)})
            pure selected
  where
    equationSpine hasApplication term = do
        scopeCharge
        case term of
            CEq{} -> pure hasApplication
            CForall _ body -> equationSpine True body
            CImp _ body -> equationSpine True body
            CAnd left right -> equationSpine hasApplication left >>= \case
                True -> pure True
                False -> equationSpine hasApplication right
            _ -> pure False

endpointProducerFor
    :: Eq global => FocusedRequest global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) EqualityProducer)
endpointProducerFor request = do
    policy <- State.gets (policyEndpoints . searchPolicy)
    if policy == EndpointsDisabled then pure (Right EvidenceOnly)
        else fmap (\sources -> if null sources then EvidenceOnly else SuppliedEquations)
            <$> endpointTheoremSources request

lookupFocusedCertificate
    :: ProofRequirement -> FocusedObligationId
    -> State (ObviousSearchState global) (Maybe (ObviousProof global))
lookupFocusedCertificate requirement identifier =
    fmap (>>= selectFocusedCertificate requirement) (lookupFocusedCertificates identifier)

lookupFocusedCertificates
    :: FocusedObligationId -> State (ObviousSearchState global) (Maybe (FocusedCertificates global))
lookupFocusedCertificates (FocusedObligationId index) = do
    row <- State.gets (Seq.lookup index . searchFocusedObligations)
    pure ((\(FocusedObligation _target certificates _subscribed) -> certificates) <$> row)

selectFocusedCertificate :: ProofRequirement -> FocusedCertificates global -> Maybe (ObviousProof global)
selectFocusedCertificate requirement certificates = case (requirement, certificates) of
    (AnyObviousProof, FocusedSingleCertificate proof) -> proof
    (MustUseCanonicalDefinition, FocusedSingleCertificate{}) -> Nothing
    (AnyObviousProof, FocusedSupportedCertificates proof _supported) -> proof
    (MustUseCanonicalDefinition, FocusedSupportedCertificates _proof supported) -> supported

retainFocusedCertificate
    :: FocusedObligationId -> ObviousProof global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) ())
retainFocusedCertificate identifier@(FocusedObligationId index) proof = Except.runExceptT do
    row <- State.gets (Seq.lookup index . searchFocusedObligations)
    FocusedObligation target certificates subscribed <- maybe
        (scopeIntegrity "a focused certificate lost its obligation") pure row
    let canonical = candidateUsesCanonicalDefinition (obviousProofDependencies proof)
        update = case certificates of
            FocusedSingleCertificate Nothing -> Just (FocusedSingleCertificate (Just proof))
            FocusedSingleCertificate (Just _) -> Nothing
            FocusedSupportedCertificates unrestricted supported
                | isNothing unrestricted || (canonical && isNothing supported) -> Just
                    (FocusedSupportedCertificates (unrestricted <|> Just proof)
                        (supported <|> if canonical then Just proof else Nothing))
                | otherwise -> Nothing
    for_ update \updated -> do
        scopeChargeTo (if isJust (obviousProofCertification proof) then GroundScopeWork else FocusedScopeWork)
        State.modify' (\state -> state
            { searchFocusedObligations = Seq.update index (FocusedObligation target updated subscribed)
                (searchFocusedObligations state)
            , searchCertificateEvents = if searchCanonicalRequest state || subscribed
                then searchCertificateEvents state Seq.|> identifier else searchCertificateEvents state })

focusedObligationHead
    :: CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedObligationHead global))
focusedObligationHead = go 0
  where
    go arity term = do
        hasWork <- consumeSearchStep
        if not hasWork
            then
                pure
                    (Left
                        (ObviousResourceExhausted ObviousFocusedWorkLimit))
            else
                case term of
                    CApp function _argument -> go (arity + 1) function
                    _ ->
                        pure
                            (Right
                                (FocusedObligationHead arity (atom term)))

    atom = \case
        CBound index -> FocusedHeadBound index
        CGlobal global -> FocusedHeadGlobal global
        CIntrinsic intrinsic -> FocusedHeadIntrinsic intrinsic
        CLogicalSelect _coreType -> FocusedHeadLogicalSelect
        COpaqueInteger integer -> FocusedHeadOpaqueInteger integer
        CApp{} -> FocusedHeadLambda
        CLam{} -> FocusedHeadLambda
        CFalsum -> FocusedHeadFalsum
        CTruth -> FocusedHeadTruth
        CNot{} -> FocusedHeadNegation
        CAnd{} -> FocusedHeadConjunction
        COr{} -> FocusedHeadDisjunction
        CImp{} -> FocusedHeadImplication
        CEq{} -> FocusedHeadEquality
        CForall{} -> FocusedHeadUniversal
        CExists{} -> FocusedHeadExistential

possiblyConvertibleFocusedHeads
    :: Eq global
    => FocusedObligationHead global
    -> FocusedObligationHead global
    -> Bool
possiblyConvertibleFocusedHeads left right =
    left == right || reducibleFocusedHead left || reducibleFocusedHead right

reducibleFocusedHead :: FocusedObligationHead global -> Bool
reducibleFocusedHead (FocusedObligationHead _arity FocusedHeadLambda) = True
reducibleFocusedHead _discriminator = False

obviousProofStatement :: ObviousProof global -> ScopedCheckedCore global
obviousProofStatement = KernelProof.builtProofStatement . obviousBuiltProof

data SourceExposureStep global
    = SourceExposure !(ObviousProof global) !(HeadProofStep global)
    | SourceExposureFinished !(Either (ObviousFailure global) (ObviousProof global))

startSourceExposure
    :: KernelProof.ProofContext global -> ObviousProof global
    -> State (ObviousSearchState global) (SourceExposureStep global)
startSourceExposure context source = do
    cached <- case obviousProofSourceKey source of
        Nothing -> pure Nothing
        Just key -> State.gets (Map.lookup key . searchFocusedExposureCache)
    case cached of
        Just prepared -> pure (SourceExposureFinished (Right prepared))
        Nothing -> runCountedKernel (KernelProof.countedAdmitScopedTerm
                context (obviousProofStatement source)) >>= \case
            Left failure -> pure (SourceExposureFinished (Left failure))
            Right _ -> pure (SourceExposure source (HeadProofInspect (obviousBuiltProof source)))

advanceSourceExposure
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> SourceExposureStep global
    -> State (ObviousSearchState global) (SourceExposureStep global)
advanceSourceExposure environment context = \case
    finished@SourceExposureFinished{} -> pure finished
    SourceExposure source (HeadProofFinished result) -> case result of
        Left failure -> done (Left failure)
        Right built -> do
            let prepared = inheritCandidateSource source (ObviousProof built (obviousProofDependencies source))
            case obviousProofSourceKey source of
                Nothing -> done (Right prepared)
                Just key -> do
                    work <- consumeSearchStep
                    if not work then done focusedWorkExhausted else do
                        let tagged = withFocusedSourceKey key prepared
                        State.modify' (\state -> state {searchFocusedExposureCache =
                            Map.insert key tagged (searchFocusedExposureCache state)})
                        done (Right tagged)
    SourceExposure source step -> advanceHeadProof environment context step >>= \case
        finished@HeadProofFinished{} -> advanceSourceExposure environment context (SourceExposure source finished)
        pending -> pure (SourceExposure source pending)
  where
    done = pure . SourceExposureFinished

sourceExposureIsDeferred :: SourceExposureStep global -> Bool
sourceExposureIsDeferred (SourceExposure _ step) = headProofIsDeferred step
sourceExposureIsDeferred SourceExposureFinished{} = False

-- Deferred consumers use the same exposure worker, including its charged small
-- probe. Scheduled discovery retains SourceExposureStep instead of draining it.
exposeProof
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> ObviousProof global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ObviousProof global))
exposeProof environment context source = startSourceExposure context source >>= drive
  where
    drive (SourceExposureFinished result) = pure result
    drive step = advanceSourceExposure environment context step >>= drive

inheritCandidateSource
    :: ObviousProof global
    -> ObviousProof global
    -> ObviousProof global
inheritCandidateSource source prepared =
    case obviousProofCandidateSource source of
        Nothing -> prepared
        Just candidateSource -> withCandidateSource candidateSource prepared

-- Head exposure and the proof conversion that justifies it are separate
-- operations. In particular, a successful residual is retained when attaching
-- it to the proof needs more effort.
data HeadProofStep global
    = HeadProofInspect !(KernelProof.BuiltProof global)
    | HeadProofReduce !PreparationEffort !(KernelProof.BuiltProof global)
    | HeadProofConvert !PreparationEffort !(KernelProof.BuiltProof global)
        !(ScopedCheckedCore global)
    | HeadProofFinished !(Either (ObviousFailure global) (KernelProof.BuiltProof global))

headProofIsDeferred :: HeadProofStep global -> Bool
headProofIsDeferred (HeadProofReduce effort _) = preparationIsDeferred effort
headProofIsDeferred (HeadProofConvert effort _ _) = preparationIsDeferred effort
headProofIsDeferred _ = False

advanceHeadProof
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> HeadProofStep global
    -> State (ObviousSearchState global) (HeadProofStep global)
advanceHeadProof environment@(SearchEnvironment typing _ _ _) context = \case
    HeadProofInspect proof -> headNeedsReduction False
            (scopedCoreTerm (KernelProof.builtProofStatement proof)) >>= \case
        Left failure -> done (Left failure)
        Right False -> done (Right proof)
        Right True -> advanceHeadProof environment context (HeadProofReduce SmallPreparation proof)
    HeadProofReduce effort proof -> runConversionPreparation effort (\limit ->
            Conversion.residualizeHeadChecked (Conversion.ConversionRecoveryTyping typing typing)
                limit (KernelProof.builtProofStatement proof)) >>= \case
        NeedsMoreEffort offered -> pure (HeadProofReduce (FullPreparation offered) proof)
        PreparationFinished (Left failure) -> done (Left failure)
        PreparationFinished (Right target) -> scopedIdentity (KernelProof.builtProofStatement proof) target >>= \case
            Left failure -> done (Left failure)
            Right True -> done (Right proof)
            Right False -> pure (HeadProofConvert SmallPreparation proof target)
    HeadProofConvert effort proof target -> runKernelPreparation effort (KernelProof.countedConversionProof context proof target) >>= \case
        NeedsMoreEffort offered -> pure (HeadProofConvert (FullPreparation offered) proof target)
        PreparationFinished result -> done result
    finished@HeadProofFinished{} -> pure finished
  where
    done = pure . HeadProofFinished

-- A selected pointwise prefix owns its exact child and outer targets. Retain
-- each abstraction as it succeeds; a final conversion retry cannot reopen the
-- child, repeat wrappers, or accidentally include an unselected deeper prefix.
data FunctionEqualityProofStep global
    = FunctionEqualityCheckChild !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        ![CoreType] !(KernelProof.BuiltProof global)
    | FunctionEqualityChild !(ScopedCheckedCore global) ![CoreType] !(HeadProofStep global)
    | FunctionEqualityAbstract !(ScopedCheckedCore global) ![CoreType] !(KernelProof.BuiltProof global)
    | FunctionEqualityResult !(HeadProofStep global)
    | FunctionEqualityFinished !(Either (ObviousFailure global) (KernelProof.BuiltProof global))

startFunctionEqualityProof
    :: ScopedCheckedCore global -> ScopedCheckedCore global -> [CoreType]
    -> KernelProof.BuiltProof global -> FunctionEqualityProofStep global
startFunctionEqualityProof outer child nearestFirst proof =
    FunctionEqualityCheckChild outer child nearestFirst proof

advanceFunctionEqualityProof
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global
    -> KernelProof.ProofContext global -> FunctionEqualityProofStep global
    -> State (ObviousSearchState global) (FunctionEqualityProofStep global)
advanceFunctionEqualityProof environment outerContext childContext = \case
    FunctionEqualityCheckChild outer child binders proof ->
        scopedIdentity child (KernelProof.builtProofStatement proof) >>= \case
            Left failure -> pure (FunctionEqualityFinished (Left failure))
            Right True -> pure (FunctionEqualityAbstract outer binders proof)
            Right False -> pure (FunctionEqualityChild outer binders (HeadProofConvert SmallPreparation proof child))
    FunctionEqualityChild outer binders (HeadProofFinished result) -> pure case result of
        Left failure -> FunctionEqualityFinished (Left failure)
        Right proof -> FunctionEqualityAbstract outer binders proof
    FunctionEqualityChild outer binders child -> FunctionEqualityChild outer binders
        <$> advanceHeadProof environment childContext child
    FunctionEqualityAbstract outer [] proof ->
        pure (FunctionEqualityResult (HeadProofConvert SmallPreparation proof outer))
    FunctionEqualityAbstract outer (binder : rest) proof -> do
        result <- runCountedKernel (KernelProof.countedEqualityCongruenceLambdaProof binder proof)
        pure case result of
            Left failure -> FunctionEqualityFinished (Left failure)
            Right abstracted -> FunctionEqualityAbstract outer rest abstracted
    FunctionEqualityResult (HeadProofFinished result) -> pure (FunctionEqualityFinished result)
    FunctionEqualityResult conversion -> FunctionEqualityResult
        <$> advanceHeadProof environment outerContext conversion
    finished@FunctionEqualityFinished{} -> pure finished

-- Only the current node can be retried. In particular neither the foundation
-- instantiation nor the first consumed direction is rebuilt when the final
-- implication elimination needs a larger conversion allowance.
data BooleanEqualityProofStep global
    = BooleanEqualityFoundation !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global)
    | BooleanEqualityInstantiate !PreparationEffort ![ScopedCheckedCore global]
        !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global)
    | BooleanEqualityEliminate !PreparationEffort ![KernelProof.BuiltProof global] !(KernelProof.BuiltProof global)
    | BooleanEqualityFinished !(Either (ObviousFailure global) (KernelProof.BuiltProof global))

advanceBooleanEqualityProof
    :: Eq global
    => KernelProof.ProofContext global -> BooleanEqualityProofStep global
    -> State (ObviousSearchState global) (BooleanEqualityProofStep global)
advanceBooleanEqualityProof context = \case
    BooleanEqualityFoundation left right forward backward -> do
        result <- runCountedKernel (KernelProof.countedFoundationProof context PropositionalExtensionality)
        pure case result of
            Left failure -> BooleanEqualityFinished (Left failure)
            Right axiom -> BooleanEqualityInstantiate SmallPreparation [left, right] forward backward axiom
    BooleanEqualityInstantiate _ [] forward backward axiom ->
        pure (BooleanEqualityEliminate SmallPreparation [forward, backward] axiom)
    BooleanEqualityInstantiate effort (argument : rest) forward backward axiom ->
        runKernelPreparation effort (KernelProof.countedForallEliminationProof context axiom argument) >>= \case
                NeedsMoreEffort offered -> pure
                    (BooleanEqualityInstantiate (FullPreparation offered) (argument : rest) forward backward axiom)
                PreparationFinished (Left failure) -> pure (BooleanEqualityFinished (Left failure))
                PreparationFinished (Right instantiated) -> pure
                    (BooleanEqualityInstantiate SmallPreparation rest forward backward instantiated)
    BooleanEqualityEliminate _ [] proof -> pure (BooleanEqualityFinished (Right proof))
    BooleanEqualityEliminate effort (direction : rest) implication ->
        runKernelPreparation effort (KernelProof.countedImplicationEliminationProof context implication direction) >>= \case
                NeedsMoreEffort offered -> pure
                    (BooleanEqualityEliminate (FullPreparation offered) (direction : rest) implication)
                PreparationFinished (Left failure) -> pure (BooleanEqualityFinished (Left failure))
                PreparationFinished (Right eliminated) -> pure
                    (BooleanEqualityEliminate SmallPreparation rest eliminated)
    finished@BooleanEqualityFinished{} -> pure finished

convertIfDifferent
    :: Eq global
    => KernelProof.ProofContext global
    -> KernelProof.BuiltProof global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (KernelProof.BuiltProof global))
convertIfDifferent context proof target = do
    same <- scopedIdentity (KernelProof.builtProofStatement proof) target
    case same of
        Left failure -> pure (Left failure)
        Right True -> pure (Right proof)
        Right False -> conversionProof context proof target

-- The focused driver owns child requests and their returns. Component cursors
-- describe one proof-search operation; none of them recursively starts a proof.
data DirectEvidenceMode = SuppliedEvidence | EstablishedEvidence
    deriving stock (Eq)

data FocusedRequest global = FocusedRequest
    { focusedObservation :: !CandidateObservationScope
    , focusedRequirement :: !ProofRequirement
    , focusedEnvironment :: !(SearchEnvironment global)
    , focusedActive :: !(Set FocusedObligationId)
    , focusedContextId :: !FocusedContextId
    , focusedContext :: !(KernelProof.ProofContext global)
    , focusedTarget :: !(ScopedCheckedCore global)
    , focusedEligibility :: !GroundEligibility
    , focusedSourcePolicy :: !FocusedSourcePolicy
    , focusedObligation :: !(Maybe FocusedObligationId)
    , focusedDirectEvidence :: !DirectEvidenceMode
    , focusedDirectionalEntry :: !(Maybe DirectionalEntryId)
    , focusedCompletionPermission :: !CompletionPermission
    }

data CompletionPermission = CompletionAllowed | CompletionSuppressed
    deriving stock (Eq)

data FocusedRulesInput global = FocusedRulesInput
    !(FocusedRequest global) ![ObviousProof global] !Bool

data FocusedRule global
    = FocusedExact !ExactConversionPolicy
    | FocusedExactContinuation !(ExactStep global)
    | FocusedIntroduction
    | FocusedDirectIntroduction
    | FocusedWitness
    | FocusedExistentialElimination
    | FocusedProjection !ExactConversionPolicy
    | FocusedEquality !(ScopedCheckedCore global)
    | FocusedStructuralEquality !(ScopedCheckedCore global)
    | FocusedFalsum
    | FocusedTheorem
    | FocusedArgumentTransport
    | FocusedTransportRule
    | FocusedLocalFacts
    | FocusedImportedFacts !Bool
    | FocusedGoalDefinitions
    | FocusedCitedDefinitions
    | FocusedPointwiseRule

data FocusedAction global
    = FocusedStart !(FocusedRequest global)
    | FocusedEqualityEntry !(FocusedRequest global)
    | FocusedArgumentEntry !(FocusedRequest global)
    | FocusedPhaseEntry !FocusedPhase !FocusedConsumerRole !(FocusedRequest global)
    | FocusedPointwiseOpen !(FocusedRequest global) !(FocusedRequest global) ![CoreType]
    | FocusedPointwiseProbe !(FocusedRequest global) !(FocusedRequest global) ![CoreType]
    | FocusedPointwiseLeaf !(FocusedRequest global) !(FocusedRequest global) ![CoreType]
    | FocusedPointwiseSupport !(FocusedRequest global) !(FocusedRequest global) ![CoreType]
    | FocusedPointwiseBuild !(FocusedRequest global) !(FocusedRequest global)
        !CandidateDependencies !(FunctionEqualityProofStep global) !(FocusedAction global)
    | FocusedBooleanBegin !(FocusedRequest global)
    | FocusedBooleanDirection !(FocusedRequest global)
    | FocusedBooleanIntroduce !(FocusedRequest global)
    | FocusedBooleanSecond !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(ObviousProof global) !(FocusedRequest global)
    | FocusedBooleanBuild !(FocusedRequest global) !CandidateDependencies
        !(BooleanEqualityProofStep global) !(FocusedAction global)
    | FocusedBooleanSupport !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(ObviousProof global) !(ObviousProof global)
    | FocusedPrefixBegin !(FocusedRequest global)
    | FocusedPrefixTheorems !(FocusedRequest global)
    | FocusedPublish !(FocusedRequest global) !(ObviousProof global) !(FocusedAction global)
    | FocusedEndpointRequest !(FocusedRequest global)
    | FocusedEndpointBegin !(FocusedRequest global)
    | FocusedEndpointSearch !(FocusedRequest global) !(TheoremStep global)
    | FocusedEndpointSource !(FocusedRequest global) !(PreparedTheoremSource global) !Bool
    | FocusedEndpointSourceWithContinuation !(FocusedRequest global) !(PreparedTheoremSource global)
        !(TheoremContinuation global)
    | FocusedEndpointReverse !(KernelProof.ProofContext global) !PreparationEffort !(ObviousProof global)
    | FocusedEndpointSupport !(FocusedRequest global) !PreparationEffort
        !(ObviousProof global) !(ApplicationStep global)
    | FocusedEndpointGuard !(FocusedRequest global) !(FocusedContinuation global)
    | FocusedExistingEvidence !(FocusedRequest global) !(FocusedContinuation global)
    | FocusedAwaitEvidence !(FocusedRequest global) !FocusedObligationId !FocusedPhase
    | FocusedDirectQuantum !Word !(FocusedAction global)
    | FocusedDirectPremise !(FocusedRequest global)
    | FocusedDirectBody !(FocusedRequest global)
    | FocusedPreparedProbe !(FocusedRequest global)
    | FocusedRetryHead !Bool !(FocusedRequest global) !Conversion.ConversionLimit
    | FocusedPreparedTarget !Bool !(FocusedRequest global) !(ScopedCheckedCore global)
    | FocusedSearch !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | FocusedProduce !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | FocusedGround !(FocusedRequest global) !(Maybe (FocusedGroundQuery () global))
    | FocusedAwaitGround !(FocusedRequest global) !(FocusedGroundQuery () global) !Refutation.RefutationFailure
    | FocusedGroundOpportunity !(FocusedRequest global) !(FocusedGroundQuery () global) ![Natural]
    | FocusedUseFact !(FocusedRulesInput global) !Bool !(ObviousProof global)
    | FocusedRules !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | FocusedDirectRules !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | FocusedRunRule !(FocusedRulesInput global) !(FocusedRule global)
    | FocusedReturn !(Attempt global)
    | FocusedConvertRequest !(FocusedRequest global) !CandidateDependencies !(HeadProofStep global)
    | FocusedExactCandidates !(FocusedRequest global) !(ExactStep global)
    | FocusedProjectionCandidates !(FocusedRequest global) !ExactConversionPolicy !(ProjectionStep global)
    | FocusedFalsumCandidates !(FocusedRequest global) ![ObviousProof global] !(FalsumStep global)
    | FocusedEqualities !(FocusedRequest global) !ExactConversionPolicy !(EqualityStep global)
    | FocusedIntroduce !(FocusedRequest global) !(IntroductionStep global)
    | FocusedWitnesses !(FocusedRequest global) ![ObviousProof global] !(WitnessStep global)
    | FocusedExistentials !(FocusedRequest global) ![ObviousProof global]
    | FocusedExtensionality !(FocusedRequest global) !FocusedSourceKey !MembershipDirection
        !(ScopedCheckedCore global) !ProofRequirement !(Attempt global) !(FocusedContinuation global)
    | FocusedExistentialOffer !(FocusedRequest global) !(FocusedRequest global)
        !(ObviousProof global) !CoreType !(CanonicalTerm global) ![ObviousProof global]
    | FocusedConjoin !(FocusedRequest global) !(ConjunctionStep global)
    | FocusedConjunctionSupport !FocusedPhase !(FocusedRequest global) !(ObviousProof global) !(ObviousProof global)
    | FocusedDemandCertificate !FocusedPhase !(FocusedRequest global) !FocusedObligationId
    | FocusedSupportDependency !(FocusedRequest global) !(ObviousProof global) !(FocusedContinuation global)
    | FocusedTheorems !(FocusedRulesInput global) !Bool !(TheoremStep global)
    | FocusedMatchApplication !(FocusedRequest global) !(Maybe (CandidateSeed global))
        !(ApplicationInput global) !(TheoremMatchStep global)
    | FocusedApply !(FocusedRequest global) !(ApplicationStep global)
    | FocusedApplicationSupport !(FocusedRequest global) !(ApplicationInput global)
        !(Seq (ApplicationSupportRecipe global)) ![ApplicationFrame global]
    | FocusedDeferredPremise !(FocusedRequest global) !(FocusedContinuation global)
        !(Maybe (ObviousFailure global))
    | FocusedTransport !(FocusedRequest global) !(TransportStep global)
    | FocusedGoalViews !(FocusedRequest global) !(GoalDefinitionStep global)
    | FocusedFactViews !(FocusedRulesInput global) !Bool !DefinitionViewSelection
        !(FactDefinitionStep global)

data FocusedContinuation global
    = AfterFocusedRequest !(FocusedRequest global)
    | AfterPointwise !(FocusedRequest global) !(FocusedRequest global) ![CoreType]
    | AfterPrefixDirect !(FocusedRequest global)
    | AfterBooleanFirst !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(FocusedRequest global)
    | AfterBooleanSecond !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(ObviousProof global)
    | AfterBooleanUpgrade !(FocusedRequest global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !Bool !(ObviousProof global)
    | AfterBooleanDirect !(FocusedRequest global)
    | AfterBooleanIntroduction !(FocusedRequest global)
    | AfterBooleanBodyDirect !(FocusedRequest global) !(FocusedRulesInput global)
        ![FocusedRule global] !(Maybe (ObviousFailure global)) !Bool
    | AfterBooleanBodyGround !(FocusedRequest global) !(FocusedRulesInput global)
        ![FocusedRule global] !(Maybe (ObviousFailure global)) !Bool
    | AfterEndpointDirection !(KernelProof.ProofContext global) !Bool
    | AfterEndpointEquality !(FocusedRequest global) !ExactConversionPolicy !(EqualityCursor global)
    | AfterArgumentEquality !(FocusedRequest global) !ExactConversionPolicy !(EqualityCursor global)
    | AfterEndpointTransport !(FocusedRequest global) !(TransportCursor global)
    | AfterArgumentTransport !(FocusedRequest global) !(TransportCursor global)
    | AfterEndpointSource !(FocusedRequest global) !(PreparedTheoremSource global)
        !Bool !(TheoremContinuation global)
    | AfterEndpointGuard !(FocusedRequest global) !(FocusedContinuation global)
    | AfterFocusedProducer !FocusedProducerKey
    | AfterFocusedGeneralEntry !FocusedObligationId
    | AfterFocusedAlias !(FocusedRequest global) !FocusedObligationId
    | AfterFocusedCertificate !FocusedObligationId
    | AfterLeftConjunctionSupport !(ObviousProof global)
    | AfterRightConjunctionSupport !(ObviousProof global)
    | AfterFocusedSearch !(FocusedRequest global)
    | AfterGroundEntryFailure !(ObviousFailure global)
    | AfterDirectPremise !(ScopedCheckedCore global)
    | AfterDirectRule !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | AfterFocusedRule !(FocusedRulesInput global) ![FocusedRule global]
        !(Maybe (ObviousFailure global)) !Bool
    | AfterFocusedIntroduction !(FocusedRequest global) !(FocusedRequest global)
        !(IntroductionContinuation global)
    | AfterFocusedExistential !(FocusedRequest global) !(FocusedRequest global)
        !(ObviousProof global) !CoreType !(CanonicalTerm global)
    | AfterFocusedConjunction !(FocusedRequest global) !(ScopedCheckedCore global)
        !(ConjunctionContinuation global)
    | AfterMatchedTheorem !(Maybe (CandidateSeed global)) !Natural
    | AfterDirectProbe !(FocusedRequest global) !(FocusedContinuation global)
    | AfterApplicationChild !(FocusedRequest global) !(ApplicationInput global)
        !(ScopedCheckedCore global) !(Template.TemplateSubstitution global)
        !(PremiseContinuation global) ![ApplicationFrame global]
    | AfterApplicationUpgrade !(FocusedRequest global) !(ApplicationInput global) !(ApplicationSupportRecipe global)
    | AfterExtensionalityFallback !(FocusedRequest global) !FocusedSourceKey !MembershipDirection
        !(ScopedCheckedCore global) !ProofRequirement !(FocusedContinuation global)
    | AfterExtensionalityDischarge !(FocusedRequest global) !(ExtensionalityBranch global)
        !(FocusedContinuation global)
    | AfterFocusedTransport !(FocusedRequest global) !(ScopedCheckedCore global)
        !(TransportContinuation global)
    | AfterFocusedGoalView !(FocusedRequest global) !(ScopedCheckedCore global)
        !(GoalDefinitionContinuation global)

-- A choice owns its return continuation once. Its independently scheduled
-- alternatives retain only their local reconstruction frames. The ownership
-- forest cancels dependent work without duplicating a source/view fallback.
data FocusedTask global
    = FocusedTask !Choice.Owner !Natural !(FocusedAction global) ![FocusedContinuation global]
    | FocusedSourceTask !Choice.Owner !Natural !(FocusedRulesInput global) !Bool !(TheoremStep global)
    | FocusedFactSourceTask !Choice.Owner !Natural !(FocusedRulesInput global) !Bool
        !DefinitionViewSelection ![ScopedCheckedCore global] !(FactDefinitionStep global)

focusedTaskOwner :: FocusedTask global -> Choice.Owner
focusedTaskOwner = \case
    FocusedTask owner _ordinal _action _frames -> owner
    FocusedSourceTask owner _ordinal _input _recursive _step -> owner
    FocusedFactSourceTask owner _ordinal _input _direct _selection _seen _step -> owner


data FocusedChoice global = FocusedChoice
    !Natural ![FocusedContinuation global] !Natural
    !(Maybe (Natural, ObviousFailure global)) !(FocusedDiscovery global)

data FocusedDiscovery global
    = DiscoveryComplete
    | Discovering !(Set Natural) !(Seq (FocusedTask global))

data FocusedSchedule global = FocusedSchedule
    { scheduledChoices :: !(Choice.Forest FocusedProducerKey (FocusedChoice global))
    , scheduledNextId :: !Natural
    , scheduledCheapTurns :: !Word
    , scheduledReturns :: !(Seq (FocusedTask global))
    , scheduledDirect :: !(Seq (FocusedTask global))
    , scheduledPreparation :: !(Seq (FocusedTask global))
    , scheduledDeferred :: !(Seq (FocusedTask global))
    , scheduledProducers :: !(Map.Map FocusedProducerKey (FocusedProducer global))
    , scheduledDormant :: !(Seq (FocusedTask global))
    , scheduledGroundWaiting :: !(Seq (FocusedTask global))
    , scheduledGroundInputs :: !Int
    }

-- Consumers keep their own scope reconstruction and one choice owner. A producer
-- is owned by an obligation phase, so satisfying one consumer cannot discard another
-- consumer's canonical frontier. With no unmet consumer it retains dormant tasks.
data FocusedConsumer global = FocusedConsumer
    !FocusedConsumerRole !ProofRequirement !Choice.Owner !Natural ![FocusedContinuation global]

data FocusedConsumerRole = SearchDependency | PhaseDelegation | ExistingEvidenceWait
    deriving stock (Eq, Show)

data FocusedProducerKey = FocusedProducerKey !FocusedObligationId !FocusedPhase
    deriving stock (Eq, Ord)

-- Ordinary obligations may enter direct evidence and general search once each.
-- Endpoint obligations have a separate identity and only their restricted phase.
data FocusedPhase = DirectEvidence | GeneralSearch | EndpointSearch | EqualityReasoning | PrefixEvidence | ArgumentCompletion
    deriving stock (Eq, Ord)

focusedPhases :: [FocusedPhase]
focusedPhases = [DirectEvidence, GeneralSearch, EndpointSearch, EqualityReasoning, PrefixEvidence, ArgumentCompletion]

data FocusedPhaseState global
    = RunningPhase !Natural
    | FinishedPhase !(Attempt global)

data FocusedProducer global = FocusedProducer
    !(FocusedPhaseState global) !(Seq (FocusedConsumer global))

data FocusedEffort = PreparatoryEffort | DeferredEffort

equalityEntryAction :: FocusedRequest global -> FocusedAction global
equalityEntryAction request = case splitScopedEquality (focusedTarget request) of
    Just (TyProp, _, _) -> FocusedBooleanBegin request
    _ -> FocusedPointwiseOpen request request []

pointwiseEvidencePhase :: FocusedRequest global -> FocusedPhase
pointwiseEvidencePhase request
    | focusedCompletionPermission request == CompletionSuppressed = PrefixEvidence
    | Just (TyArrow{}, _, _) <- splitScopedEquality (focusedTarget request) = PrefixEvidence
    | otherwise = GeneralSearch

runFocusedMachine
    :: Ord global
    => FocusedAction global
    -> [FocusedContinuation global]
    -> State (ObviousSearchState global) (Attempt global)
runFocusedMachine initial frames = runFocusedSchedule (queueFocused (FocusedTask Choice.RootContinuation 0 initial frames)
    (FocusedSchedule Choice.empty 1 512 Seq.empty Seq.empty Seq.empty Seq.empty Map.empty Seq.empty Seq.empty 0))

runFocusedSchedule :: Ord global => FocusedSchedule global -> State (ObviousSearchState global) (Attempt global)
runFocusedSchedule = run
  where
    run schedule = do
        inputs <- State.gets (Seq.length . ownedGroundFacts . searchGroundOwner)
        let current = if inputs == scheduledGroundInputs schedule then schedule
                else foldl' (flip queueFocused) schedule
                    {scheduledGroundInputs = inputs, scheduledGroundWaiting = Seq.empty}
                    (fmap resumeGroundTask (scheduledGroundWaiting schedule))
        events <- State.gets searchCertificateEvents
        if Seq.null events then runReady current else do
            State.modify' (\state -> state {searchCertificateEvents = Seq.empty})
            notified <- foldM (flip notifyFocusedConsumers) current events
            runReady notified

    runReady schedule = case popFocused schedule of
        Nothing -> case Seq.viewl (scheduledGroundWaiting schedule) of
            Seq.EmptyL -> case settleFocusedObservers schedule of
                Nothing -> blockedFocusedSupport schedule
                Just resumed -> run resumed
            task Seq.:< remaining -> run (queueFocused (finishGroundTask task)
                schedule {scheduledGroundWaiting = remaining})
        Just (task, rest) ->
            let owner = focusedTaskOwner task
            in if not (Choice.live owner (scheduledChoices rest)) then run rest
                else if focusedTaskNeeded task rest then runActive task rest
                else run rest { scheduledDormant = scheduledDormant rest Seq.|> task }

    resumeGroundTask (FocusedTask owner ordinal (FocusedAwaitGround request query _failure) following) =
        FocusedTask owner ordinal (FocusedGround request (Just query)) following
    resumeGroundTask task = task
    finishGroundTask (FocusedTask owner ordinal (FocusedAwaitGround _request _query failure) following) =
        FocusedTask owner ordinal (FocusedReturn (AttemptFailed (mapRefutationFailure failure))) following
    finishGroundTask task = task

    -- Every emitted view already consumes a canonical source. Within one
    -- producer's scope/policy, its first proof supplies the same support slot;
    -- rediscovery of that statement cannot justify another consuming search.
    seenFact _target [] = pure False
    seenFact target (previous : remaining) = do
        same <- Except.ExceptT (scopedIdentity target previous)
        if same then pure True else seenFact target remaining

    enterShared owner ordinal input@(FocusedRulesInput request available continue) rules firstFailure rejected incomingFrames schedule = do
        canonical <- State.gets searchCanonicalRequest
        case (focusedObligation request, incomingFrames) of
            (Just identifier, AfterFocusedRequest original : following)
                -- The general phase of an existing direct owner prepared this
                -- same target. Execute it, rather than subscribing to itself.
                | AfterFocusedGeneralEntry producer : rest <- following, producer == identifier ->
                    runActive (FocusedTask owner ordinal (FocusedProduce input rules firstFailure rejected)
                        (AfterFocusedRequest original : rest)) schedule
                | otherwise -> do
                    let (role, requirement, consumerFrames) = case following of
                            AfterFocusedGeneralEntry producer : rest ->
                                -- Relay the ordinary certificate through its
                                -- spelling first. AfterFocusedAlias retains the
                                -- support subscription; delegation demand is
                                -- always taken from the actual callers.
                                (PhaseDelegation, AnyObviousProof, AfterFocusedRequest original {focusedObligation = Nothing}
                                    : AfterFocusedAlias original {focusedObligation = Just producer} identifier : rest)
                            _ -> (SearchDependency, focusedRequirement original,
                                AfterFocusedRequest original {focusedObligation = Nothing}
                                    : AfterFocusedCertificate identifier : following)
                        consumer = FocusedConsumer role requirement owner ordinal consumerFrames
                        producerRequest = request {focusedRequirement = if canonical then MustUseCanonicalDefinition else AnyObviousProof}
                        producerAction = FocusedProduce (FocusedRulesInput producerRequest available continue) rules firstFailure rejected
                    subscribe identifier GeneralSearch consumer producerAction
                        [AfterFocusedRequest producerRequest] schedule
                        (failedSearchEntry request owner ordinal incomingFrames schedule)
            _ -> pure (AttemptFailed (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch "a shared obligation lost its identity or consumer")))

    -- Focused-only setup has not installed the mixed alternative yet. The
    -- ordinary request still owns its original target, family and continuation;
    -- endpoint/direct evidence consumers do not acquire this recovery path.
    failedSearchEntry request owner ordinal entryFrames schedule failure = case entryFrames of
        AfterFocusedRequest original : following
            | eligibleFocusedGround request, eligibleFocusedGround original,
                ObviousResourceExhausted ObviousFocusedWorkLimit <- failure -> do
                recordRootFocusedOutcome original (Left failure)
                runActive (FocusedTask owner ordinal (FocusedGround original Nothing)
                    (AfterGroundEntryFailure failure : following)) schedule
        _ -> complete owner ordinal (AttemptFailed failure) schedule

    subscribe identifier phase consumer@(FocusedConsumer _ requirement owner ordinal consumerFrames) action following schedule admissionFailure = do
        snapshot <- lookupFocusedCertificates identifier
        case snapshot >>= selectFocusedCertificate requirement of
            Just proof -> runActive (FocusedTask owner ordinal (FocusedReturn (AttemptSucceeded proof)) consumerFrames) schedule
            Nothing -> do
                let key = FocusedProducerKey identifier phase
                    previous = Map.lookup key (scheduledProducers schedule)
                    starting = isNothing previous
                admitted <- Except.runExceptT do
                    scopeCharge
                    when starting do
                        scopeCharge >> scopeCharge >> scopeCharge
                        let FocusedObligationId position = identifier
                        State.modify' (\state -> state
                            {searchFocusedObligations = Seq.adjust'
                                (\(FocusedObligation target certificates _subscribed) -> FocusedObligation target certificates True)
                                position (searchFocusedObligations state)})
                case admitted of
                    Left failure -> admissionFailure failure
                    Right () -> do
                        let choice = scheduledNextId schedule
                            ticket = choice + 1
                            producer = fromMaybe (FocusedProducer (RunningPhase choice) Seq.empty) previous
                            started = if not starting then Right schedule else do
                                choices <- admitFocusedChoice (Choice.insertProducer choice key)
                                    (FocusedChoice ticket [AfterFocusedProducer key] 1 Nothing DiscoveryComplete)
                                    schedule
                                pure (queueFocused (FocusedTask (Choice.OwnedChoice choice) ticket action following)
                                    schedule {scheduledNextId = ticket + 1, scheduledChoices = choices})
                        case started of
                            Left failure -> pure (AttemptFailed failure)
                            Right next -> run (registerFocusedConsumer snapshot key consumer producer next)

    demand phase request identifier@(FocusedObligationId position) owner ordinal continuations schedule = do
        canonical <- State.gets searchCanonicalRequest
        row <- State.gets (Seq.lookup position . searchFocusedObligations)
        case row of
            Nothing -> pure (AttemptFailed (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch "a support demand lost its obligation")))
            Just (FocusedObligation target _certificates _subscribed) -> do
                let consumer = FocusedConsumer SearchDependency (focusedRequirement request) owner ordinal
                        (AfterFocusedRequest request {focusedObligation = Nothing}
                            : AfterFocusedCertificate identifier : continuations)
                    -- The consumer may use another convertible spelling. The
                    -- phase always constructs the statement owned by this row.
                    producerRequest = request {focusedRequirement = if canonical then MustUseCanonicalDefinition else AnyObviousProof
                        , focusedTarget = target, focusedObligation = Just identifier
                        , focusedActive = Set.delete identifier (focusedActive request)}
                    (action, following) = case phase of
                        DirectEvidence -> (FocusedDirectBody producerRequest {focusedObservation = CollectSharedEvidence}, [])
                        GeneralSearch -> (FocusedStart producerRequest, [AfterFocusedGeneralEntry identifier])
                        EndpointSearch -> (FocusedEndpointBegin producerRequest, [])
                        EqualityReasoning -> (equalityEntryAction producerRequest, [])
                        PrefixEvidence -> (FocusedPrefixBegin producerRequest, [])
                        ArgumentCompletion -> (FocusedPointwiseOpen producerRequest producerRequest [], [])
                subscribe identifier phase consumer action following schedule
                    (\failure -> complete owner ordinal (AttemptFailed failure) schedule)

    -- This operation only attaches to work already registered by an ordinary
    -- request. It has no action with which to start a missing producer phase.
    awaitEvidence request identifier phase owner ordinal continuations schedule =
        let key = FocusedProducerKey identifier phase
        in case Map.lookup key (scheduledProducers schedule) of
            Just producer@(FocusedProducer progress _consumers) -> do
                admitted <- consumeSearchStep
                if not admitted then complete owner ordinal
                    (AttemptFailed (ObviousResourceExhausted ObviousFocusedWorkLimit)) schedule
                    else do
                        snapshot <- lookupFocusedCertificates identifier
                        when (isNothing (snapshot >>= selectFocusedCertificate (focusedRequirement request))
                                && case progress of RunningPhase{} -> True; _ -> False)
                            (State.modify' (\state -> state
                                {searchEndpointGuardWaits = searchEndpointGuardWaits state + 1}))
                        let consumer = FocusedConsumer ExistingEvidenceWait (focusedRequirement request) owner ordinal
                                (AfterFocusedRequest request {focusedObligation = Nothing}
                                    : AfterFocusedCertificate identifier : continuations)
                        run (registerFocusedConsumer snapshot key consumer producer schedule)
            _ -> complete owner ordinal AttemptNotApplicable schedule

    -- Returns already have unconditional priority. Keep that administrative
    -- transfer local instead of allocating and immediately draining a queue
    -- entry and rechecking the same live choice owner.
    runActive task rest = do
        events <- State.gets searchCertificateEvents
        if not (Seq.null events) then run (queueFocused task rest) else
            case boundedOwner task rest of
                Nothing -> runAuthorized task rest
                Just key -> do
                    authorized <- Except.runExceptT (runScopeCore (demandWorkOwner task) absurd (\work ->
                        countedFocusedDrivingRequirement work consumerInfo (phaseConsumers rest)
                            (scheduledChoices rest) key))
                    case authorized of
                        Left failure -> runAuthorized (failedTask task failure) rest
                        Right Nothing -> park task rest
                        Right (Just requirement) -> do
                            let FocusedProducerKey identifier _ = key
                            known <- lookupFocusedCertificate requirement identifier
                            prefix <- case task of
                                FocusedTask _ _ (FocusedPointwiseOpen _ request (_ : _)) _ ->
                                    maybe (pure Nothing) (lookupFocusedCertificate requirement) (focusedObligation request)
                                _ -> pure Nothing
                            if isJust known || isJust prefix then park task rest else runAuthorized task rest

    consumerInfo (FocusedConsumer role requirement owner _ _) = (role, requirement, owner)
    phaseConsumers schedule key = case Map.lookup key (scheduledProducers schedule) of
        Just (FocusedProducer _ attached) -> attached
        Nothing -> Seq.empty
    park task schedule = run schedule {scheduledDormant = scheduledDormant schedule Seq.|> task}
    failedTask task failure = case task of
        FocusedTask owner ordinal _ following -> FocusedTask owner ordinal (FocusedReturn (AttemptFailed failure)) following
        FocusedSourceTask owner ordinal _ _ _ -> FocusedTask owner ordinal (FocusedReturn (AttemptFailed failure)) []
        FocusedFactSourceTask owner ordinal _ _ _ _ _ -> FocusedTask owner ordinal (FocusedReturn (AttemptFailed failure)) []
    -- An ordinary body need not enter a shared GeneralSearch producer. Its
    -- native worker can retain the enclosing equality owner, but authorization
    -- still belongs to the account funding that advance. Keep the same charged
    -- live-demand traversal (including the observer barrier) on every resume.
    demandWorkOwner = \case
        FocusedTask _ _ FocusedGround{} _ -> GroundScopeWork
        FocusedTask _ _ FocusedAwaitGround{} _ -> GroundScopeWork
        FocusedTask _ _ FocusedGroundOpportunity{} _ -> GroundScopeWork
        _ -> FocusedScopeWork
    boundedOwner task schedule = case task of
        FocusedTask _ _ FocusedPublish{} _ -> Nothing
        FocusedTask _ _ FocusedReturn{} _ -> Nothing
        FocusedSourceTask _ _ _ _ TheoremFinished{} -> Nothing
        _ -> case Choice.ownerProducer (focusedTaskOwner task) (scheduledChoices schedule) of
            Just (Just key@(FocusedProducerKey _ phase))
                | boundedPhase phase || startsEquality task -> Just key
            _ -> Nothing
    -- A legacy alias forwards live demand at the delegation boundary; it does
    -- not turn all of its existing work (especially ground delivery) into new
    -- focused inference. Prefix source/application continuations retain their
    -- phase owner and therefore pass this check on every advance.
    boundedPhase = \case
        EqualityReasoning -> True
        PrefixEvidence -> True
        ArgumentCompletion -> True
        DirectEvidence -> False
        GeneralSearch -> False
        EndpointSearch -> False
    startsEquality (FocusedTask _ _ FocusedEqualityEntry{} _) = True
    startsEquality (FocusedTask _ _ FocusedArgumentEntry{} _) = True
    startsEquality (FocusedTask _ _ FocusedPhaseEntry{} _) = True
    startsEquality _ = False

    runAuthorized task rest =
        let owner = focusedTaskOwner task
        in case task of
        FocusedSourceTask _owner ordinal input@(FocusedRulesInput request _available _continue) recursive step ->
            case step of
                TheoremFinished result -> complete owner ordinal result rest
                TheoremPending cursor -> do
                    next <- advanceTheoremSearch (focusedEnvironment request) (focusedContext request) cursor
                    run (queueFocused (FocusedSourceTask owner ordinal input recursive next) rest)
                TheoremBlocked blocked following -> do
                    work <- consumeSearchStep
                    if not work then complete owner ordinal (AttemptFailed (ObviousResourceExhausted ObviousFocusedWorkLimit)) rest
                        else case owner of
                            Choice.RootContinuation -> pure (AttemptFailed malformedApplicationSpine)
                            Choice.OwnedChoice choice -> do
                                let ticket = scheduledNextId rest
                                    forked = rest { scheduledNextId = ticket + 1
                                        , scheduledChoices = Choice.adjust
                                            (\(FocusedChoice parentTicket followingFrames pending failure discovery) ->
                                                FocusedChoice parentTicket followingFrames (pending + 1) failure discovery)
                                            choice (scheduledChoices rest) }
                                run (queueFocused (FocusedSourceTask owner ordinal input recursive (TheoremPending following))
                                    (queueFocused (FocusedSourceTask owner ticket input recursive (TheoremPending blocked)) forked))
                TheoremApply prepared continuation -> do
                    started <- startApplicationWithParameters
                        (if recursive then PremiseParameters else PrefixParameters) recursive (focusedObservation request)
                        (focusedRequirement request) (focusedEnvironment request)
                        (focusedContextId request) (focusedContext request) (focusedTarget request) prepared
                    forked <- addFocusedApplication owner input started rest
                    case forked of
                        Left failure -> complete owner ordinal (AttemptFailed failure) rest
                        Right updated -> run (queueFocused
                            (FocusedSourceTask owner ordinal input recursive
                                (resumeTheoremSearch continuation)) updated)
        FocusedFactSourceTask _owner ordinal input@(FocusedRulesInput request _available _continue) direct selection seen step ->
            case step of
                FactDefinitionFinished result -> complete owner ordinal result rest
                FactDefinitionPending cursor -> do
                    following <- advanceFactDefinition selection (focusedEnvironment request) (focusedContext request) cursor
                    let ready = case focusedActionEffort (FocusedFactViews input direct selection following) of
                            DeferredEffort -> releaseFocusedDiscovery owner ordinal rest
                            PreparatoryEffort -> rest
                    run (queueFocused (FocusedFactSourceTask owner ordinal input direct selection seen following) ready)
                FactDefinitionUse proof remaining -> do
                    duplicate <- Except.runExceptT (seenFact (obviousProofStatement proof) seen)
                    forked <- case duplicate of
                        Left failure -> pure (Left failure)
                        Right True -> pure (Right rest)
                        Right False -> do
                            published <- if eligibleFocusedGround request
                                then Except.runExceptT (publishGroundFact request proof) else pure (Right ())
                            case published of
                                Left failure | isFocusedInfrastructureFailure failure -> pure (Left failure)
                                Left failure -> recordGroundAdmissionFailure failure >> addFocusedFact owner input direct proof rest
                                Right () -> addFocusedFact owner input direct proof rest
                    case forked of
                        Left failure -> complete owner ordinal (AttemptFailed failure) rest
                        Right updated -> run (queueFocused
                            (FocusedFactSourceTask owner ordinal input direct selection
                                (case duplicate of Right True -> seen; _ -> obviousProofStatement proof : seen)
                                (FactDefinitionPending remaining)) updated)
        FocusedTask _owner ordinal action continuations -> case action of
            FocusedEqualityEntry request ->
                runActive (FocusedTask owner ordinal
                    (FocusedPhaseEntry EqualityReasoning (case Choice.ownerProducer owner (scheduledChoices rest) of
                        Just (Just _) -> PhaseDelegation
                        _ -> SearchDependency) request) continuations) rest
            FocusedPhaseEntry phase role request -> do
                let purpose = if phase == ArgumentCompletion ||
                        (phase == PrefixEvidence && focusedCompletionPermission request == CompletionSuppressed)
                        then EndpointObligation else OrdinaryObligation
                admitted <- internFocusedObligationFor purpose (focusedContextId request)
                    (focusedSourcePolicy request) (focusedEligibility request) (focusedTarget request)
                case admitted of
                    Left failure -> complete owner ordinal (AttemptFailed failure) rest
                    Right identifier -> do
                        let producer = request {focusedRequirement = MustUseCanonicalDefinition,
                                focusedObligation = Just identifier, focusedObservation = CollectSharedEvidence}
                            action' = case phase of
                                EqualityReasoning -> equalityEntryAction producer
                                PrefixEvidence -> FocusedPrefixBegin producer
                                ArgumentCompletion -> FocusedPointwiseOpen producer producer []
                                GeneralSearch -> FocusedStart producer {focusedActive = Set.delete identifier (focusedActive producer)}
                                _ -> FocusedReturn (AttemptFailed (ObviousIntegrityFailure
                                    (KernelProof.ProofStructuralCompositionMismatch "invalid equality phase delegation")))
                            consumer = FocusedConsumer role (focusedRequirement request) owner ordinal
                                (AfterFocusedRequest request {focusedObligation = Nothing}
                                    : AfterFocusedCertificate identifier : continuations)
                        subscribe identifier phase consumer action'
                            [AfterFocusedGeneralEntry identifier | phase == GeneralSearch] rest
                            (\failure -> complete owner ordinal (AttemptFailed failure) rest)
            FocusedPointwiseProbe outer prefix binders -> do
                admitted <- internFocusedObligationFor
                    (if focusedCompletionPermission outer == CompletionSuppressed then EndpointObligation else OrdinaryObligation)
                    (focusedContextId prefix) (focusedSourcePolicy prefix) (focusedEligibility prefix) (focusedTarget prefix)
                case admitted of
                    Left failure -> complete owner ordinal (AttemptFailed failure) rest
                    Right identifier -> do
                        let child = prefix {focusedObligation = Just identifier}
                        forkFocusedAlternatives owner ordinal continuations Nothing
                            [(FocusedPhaseEntry PrefixEvidence SearchDependency child {focusedRequirement = AnyObviousProof},
                                [AfterPointwise outer child binders]),
                             (FocusedPointwiseOpen outer child binders, [])] rest
                            >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedPointwiseLeaf outer leaf binders ->
                runActive (FocusedTask owner ordinal
                    (FocusedPhaseEntry (pointwiseEvidencePhase leaf) SearchDependency leaf {focusedRequirement = AnyObviousProof})
                    (AfterPointwise outer leaf binders : continuations)) rest
            FocusedBooleanSupport request left right forward backward -> do
                let upgrade forwardSide proof other =
                        (FocusedPhaseEntry GeneralSearch SearchDependency request
                            {focusedTarget = obviousProofStatement proof,
                             focusedEligibility = structuralGroundEligibility (focusedEligibility request),
                             focusedRequirement = MustUseCanonicalDefinition},
                            [AfterBooleanUpgrade request left right forwardSide other])
                forkFocusedAlternatives owner ordinal continuations Nothing
                    [upgrade True forward backward, upgrade False backward forward] rest
                    >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedDirectQuantum _ inner | isJust (boundedOwner task rest) ->
                runActive (FocusedTask owner ordinal inner continuations) rest
            FocusedReturn result@(AttemptFailed failure)
                | isFocusedInfrastructureFailure failure -> pure result
            FocusedReturn result | [AfterFocusedProducer key@(FocusedProducerKey identifier _phase)] <- continuations -> do
                retained <- case result of
                    AttemptSucceeded proof -> retainFocusedCertificate identifier proof
                    _ -> pure (Right ())
                case retained of
                    Left failure -> pure (AttemptFailed failure)
                    Right () -> do
                        let finished = rest { scheduledProducers = Map.adjust
                                (\(FocusedProducer _progress consumers) ->
                                    FocusedProducer (FinishedPhase result) consumers)
                                key (scheduledProducers rest) }
                        notifyFocusedConsumers identifier finished >>= run
            FocusedDirectPremise request -> do
                canonical <- State.gets searchCanonicalRequest
                if not canonical || focusedDirectEvidence request == EstablishedEvidence
                    then advance task rest else do
                    identifier <- internFocusedObligation (focusedContextId request)
                        (focusedSourcePolicy request) (focusedEligibility request) (focusedTarget request)
                    case identifier of
                        Left failure -> complete owner ordinal (AttemptFailed failure) rest
                        Right producer ->
                            let bind (AfterDirectProbe child following) =
                                    AfterDirectProbe child {focusedObligation = Just producer} following
                                bind following = following
                            in demand DirectEvidence request producer owner ordinal (map bind continuations) rest
            FocusedSearch input@(FocusedRulesInput request _available _continue) rules firstFailure rejected -> do
                canonical <- State.gets searchCanonicalRequest
                witnesses <- State.gets (policyWitnesses . searchPolicy)
                endpoints <- endpointProducerFor request
                let existential = witnesses /= WitnessesDisabled && isJust (openScopedExists (focusedTarget request))
                -- Endpoint guards may consume an ordinary request already in
                -- progress. Register that request before any guard can attach;
                -- evidence lookup itself never creates its general phase.
                case endpoints of
                    Left failure -> failedSearchEntry request owner ordinal continuations rest failure
                    Right producer | canonical || existential || producer == SuppliedEquations ->
                        enterShared owner ordinal input rules firstFailure rejected continuations rest
                    Right _ -> do
                        certificate <- maybe (pure Nothing) (lookupFocusedCertificate AnyObviousProof)
                            (focusedObligation request)
                        runActive (FocusedTask owner ordinal (case certificate of
                            Just proof -> FocusedReturn (AttemptSucceeded proof)
                            Nothing -> FocusedProduce input rules firstFailure rejected) continuations) rest
            FocusedConjunctionSupport phase request left right -> do
                let support proof following =
                        let child = request
                                { focusedTarget = obviousProofStatement proof
                                , focusedEligibility = structuralGroundEligibility (focusedEligibility request)
                                , focusedRequirement = MustUseCanonicalDefinition }
                        in case (focusedDirectEvidence request, obviousProofObligation proof) of
                            (EstablishedEvidence, _) -> [(FocusedEndpointGuard child following, [])]
                            (_, Nothing) -> []
                            (_, Just identifier) -> [(FocusedDemandCertificate phase child identifier, [following])]
                    alternatives = support left (AfterLeftConjunctionSupport right)
                        <> support right (AfterRightConjunctionSupport left)
                case alternatives of
                    [] -> complete owner ordinal (AttemptFailed ObviousCanonicalDefinitionEvidenceRequired) rest
                    _ -> forkFocusedAlternatives owner ordinal continuations Nothing alternatives rest
                        >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedEndpointSearch request (TheoremBlocked blocked following) ->
                forkFocusedAlternatives owner ordinal continuations Nothing
                    [(FocusedEndpointSearch request (TheoremPending following), []),
                     (FocusedEndpointSearch request (TheoremPending blocked), [])] rest
                    >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedExistingEvidence request following -> do
                observed <- Except.runExceptT do
                    identifiers <- Except.ExceptT (existingFocusedEvidenceOwners request)
                    certificates <- lift (traverse (lookupFocusedCertificate (focusedRequirement request)) identifiers)
                    waits <- fmap concat $ forM identifiers \identifier -> do
                        scopeCharge
                        pure [(FocusedAwaitEvidence request identifier phase, [])
                            | phase <- [DirectEvidence, GeneralSearch, EqualityReasoning, PrefixEvidence]
                            , Just (FocusedProducer (RunningPhase choice) _consumers) <-
                                [Map.lookup (FocusedProducerKey identifier phase) (scheduledProducers rest)]
                            , Choice.live (Choice.OwnedChoice choice) (scheduledChoices rest)]
                    pure (listToMaybe (catMaybes certificates), waits)
                case observed of
                    Left failure -> complete owner ordinal (AttemptFailed failure) rest
                    Right (Just proof, _) -> runActive
                        (FocusedTask owner ordinal (FocusedReturn (AttemptSucceeded proof))
                            (following : continuations)) rest
                    Right (Nothing, []) -> runActive
                        (FocusedTask owner ordinal (FocusedReturn AttemptNotApplicable)
                            (following : continuations)) rest
                    Right (Nothing, alternatives) ->
                        forkFocusedAlternatives owner ordinal (following : continuations) Nothing alternatives rest
                            >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedAwaitEvidence request identifier phase ->
                awaitEvidence request identifier phase owner ordinal continuations rest
            FocusedDemandCertificate phase request identifier ->
                demand phase request identifier owner ordinal continuations rest
            FocusedApplicationSupport request input@(ApplicationInput parameters recursive _ _ _ _ _ _ _ _) recipes applicationFrames -> do
                premisePolicy <- State.gets (policyPremiseQueries . searchPolicy)
                extensionalityPolicy <- State.gets (policyExtensionality . searchPolicy)
                let upgrade recipe@(ApplicationSupportRecipe premise _ _ _ target _ steps) =
                        let child = request
                                { focusedObservation = SuppressAuxiliary AuxiliaryTheoremAntecedent
                                , focusedEligibility = if recursive then theoremPremiseEligibility premisePolicy request else FocusedOnly
                                , focusedRequirement = MustUseCanonicalDefinition
                                , focusedTarget = obviousProofStatement premise }
                            upgraded = extensionalityFallback extensionalityPolicy recursive request input
                                target steps MustUseCanonicalDefinition (AfterApplicationUpgrade request input recipe)
                        in case (parameters, obviousProofObligation premise) of
                            (EndpointParameters{}, _) -> (FocusedEndpointGuard child upgraded, [])
                            (PrefixParameters, _) -> (FocusedDirectBody child {focusedObligation = Nothing}, [upgraded])
                            (_, Just identifier) -> (FocusedDemandCertificate
                                (if recursive then GeneralSearch else DirectEvidence) child identifier, [upgraded])
                            (_, Nothing) -> (FocusedDirectPremise child,
                                [if recursive then AfterDirectProbe child upgraded else upgraded])
                    -- The completed instance keeps its support recipes while
                    -- the retained matcher may discover another substitution.
                    -- A direct-to-recursive restart is unnecessary once all
                    -- selected premises have already produced a proof.
                    remaining = filter (\case AfterDirectPlan{} -> False; _ -> True) applicationFrames
                    discover = [(FocusedApply request (ApplicationPending input
                        (ApplicationReturn (AttemptFailed ObviousCanonicalDefinitionEvidenceRequired)) remaining), [])
                        | not (null remaining)]
                    alternatives = map upgrade (toList recipes) <> discover
                case alternatives of
                    [] -> complete owner ordinal (AttemptFailed ObviousCanonicalDefinitionEvidenceRequired) rest
                    _ -> forkFocusedAlternatives owner ordinal continuations Nothing alternatives rest
                        >>= either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run
            FocusedProduce input@(FocusedRulesInput request _available _continue) rules firstFailure rejected ->
                case continuations of
                    AfterFocusedRequest original : following -> do
                        ground <- State.gets (groundWork . searchRemainingGround)
                        let focused = FocusedRules input rules firstFailure rejected
                            completed = [AfterFocusedRequest original, AfterFocusedSearch original]
                        -- Both alternatives finish the original checked target
                        -- before returning to their common consumer. A ground
                        -- proof must not pass through a focused final conversion
                        -- after the focused structural allowance is exhausted.
                        if eligibleFocusedGround request && ground > 0
                            then do
                                directional <- Except.runExceptT (isDirectionalBody original)
                                case directional of
                                    Left failure -> do
                                        recordGroundAdmissionFailure failure
                                        if isFocusedInfrastructureFailure failure
                                            then pure (AttemptFailed failure)
                                            else runActive (FocusedTask owner ordinal focused (completed <> following)) rest
                                    -- Do not eagerly duplicate the expensive
                                    -- whole-direction and body frontiers. The
                                    -- native body query releases the retained
                                    -- ordinary rules on a local block or miss.
                                    Right True -> runActive (FocusedTask owner ordinal
                                        (FocusedDirectRules input (directFocusedRules (focusedTarget request)) Nothing False)
                                        (AfterBooleanBodyDirect original input rules firstFailure rejected : following)) rest
                                    Right False -> do
                                        forked <- forkFocusedAlternativesWith GroundScopeWork owner ordinal following Nothing
                                            [(focused, completed), (FocusedGround original Nothing, [])] rest
                                        case forked of
                                            Right schedule ->
                                                let choice = scheduledNextId rest
                                                    captured = schedule {scheduledChoices = Choice.adjust
                                                        (\(FocusedChoice ticket followingFrames pending failure _discovery) ->
                                                            FocusedChoice ticket followingFrames pending failure
                                                                (Discovering (Set.singleton (choice + 1)) Seq.empty))
                                                        choice (scheduledChoices schedule)}
                                                in run captured
                                            Left failure -> do
                                                recordGroundAdmissionFailure failure
                                                if isFocusedInfrastructureFailure failure
                                                    then pure (AttemptFailed failure)
                                                    else runActive (FocusedTask owner ordinal focused (completed <> following)) rest
                            else do
                                when (eligibleFocusedGround request) (recordGroundAdmissionFailure
                                    (ObviousResourceExhausted ObviousRefutationWorkLimit))
                                runActive (FocusedTask owner ordinal focused (completed <> following)) rest
                    _ -> pure (AttemptFailed (ObviousIntegrityFailure
                        (KernelProof.ProofStructuralCompositionMismatch "an obligation lost its target reconstruction")))
            FocusedFactViews input direct selection step -> do
                forked <- forkFocusedFactSources owner ordinal continuations input direct selection step rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedAwaitGround request query failure
                | AfterBooleanBodyGround original input rules firstFailure rejected : following <- continuations ->
                    -- A local blocked frontier releases ordinary search now,
                    -- while retaining this exact query for later fact delivery.
                    -- As at initial ground startup, the ground owner pays for
                    -- this mixed fork. Exhausted focused credit must not retire
                    -- the retained query; the focused branch pays its own work.
                    forkFocusedAlternativesWith GroundScopeWork owner ordinal following Nothing
                        [(FocusedRules input rules firstFailure rejected,
                            [AfterFocusedRequest original, AfterFocusedSearch original]),
                         (FocusedAwaitGround request query failure, [])] rest
                        -- A partially paid fork installs neither child. Send
                        -- failure through the saved body continuation so its
                        -- ordinary fallback survives under its own account;
                        -- that continuation also retains exhaustion on a miss.
                        >>= either (\problem -> runActive (failedTask task problem) rest) run
            FocusedAwaitGround{} -> run rest
                {scheduledGroundWaiting = scheduledGroundWaiting rest Seq.|> task}
            FocusedGroundOpportunity request query@(FocusedGroundQuery (GroundQuery index) _ _) tickets -> case tickets of
                [] -> do
                    end <- State.gets (Seq.length . ownedGroundFacts . searchGroundOwner)
                    State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                        {ownedGroundActivations = Map.adjust (\active -> active {activationSnapshot = end})
                            index (ownedGroundActivations (searchGroundOwner state))}})
                    advance (FocusedTask owner ordinal (FocusedGround request (Just query)) continuations) rest
                choice : remaining -> case Choice.payload <$> Choice.lookup choice (scheduledChoices rest) of
                    Just (FocusedChoice ticket following pending failure (Discovering captured parked)) ->
                        run rest {scheduledChoices = Choice.adjust
                            (const (FocusedChoice ticket following pending failure (Discovering captured (parked Seq.|> task)))) choice
                            (scheduledChoices rest)}
                    _ -> runActive (FocusedTask owner ordinal (FocusedGroundOpportunity request query remaining) continuations) rest
            FocusedGround request (Just _) | not (canSeedFocusedGround request) -> advance task rest
            FocusedGround request (Just query@(FocusedGroundQuery (GroundQuery index) _ _)) -> do
                activation <- State.gets (Map.lookup index . ownedGroundActivations . searchGroundOwner)
                case activation of
                    Just active | activationOutside active && not (activationOpportunity active)
                        , activationCursor active == activationSnapshot active -> do
                            captured <- captureGroundOpportunity owner rest
                            case captured of
                                -- Capture may fail before the native body has
                                -- released its saved focused fallback. Preserve
                                -- that continuation and the spent ground work.
                                Left failure -> runActive (failedTask task failure) rest
                                Right (tickets, ready) -> do
                                    State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                                        {ownedGroundActivations = Map.insert index active {activationOpportunity = True}
                                            (ownedGroundActivations (searchGroundOwner state))}})
                                    runActive (FocusedTask owner ordinal (FocusedGroundOpportunity request query tickets) continuations) ready
                    _ -> advance task rest
            FocusedGround _request Nothing ->
                let released = releaseFocusedDiscovery owner ordinal rest
                in case parkGroundOpportunity task released of
                    Just parked -> run parked
                    Nothing -> advance task released
            FocusedRules input rules@(_ : _ : _) firstFailure rejected -> do
                forked <- forkFocusedRules owner ordinal continuations input rules firstFailure rejected rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedIntroduce request (IntroductionAlternatives requirement left right) -> do
                let branch target following =
                        let child = request
                                { focusedObservation = SuppressAuxiliary AuxiliaryDisjunctionBranch
                                , focusedEligibility = structuralGroundEligibility (focusedEligibility request)
                                , focusedRequirement = AnyObviousProof, focusedTarget = target }
                        in ( FocusedDirectPremise child
                           , [AfterDirectProbe child
                                (AfterFocusedIntroduction request child
                                    {focusedRequirement = requirement} following)]
                           )
                forked <- forkFocusedAlternatives owner ordinal continuations Nothing
                    [ branch left (IntroductionLeftDisjunct (scopedCoreTerm right))
                    , branch right (IntroductionRightDisjunct (scopedCoreTerm left))
                    ] rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedWitnesses request available (WitnessOffer witness body cursor@(WitnessSearch binderType template _ _)) -> do
                let child = request
                        { focusedObservation = SuppressAuxiliary AuxiliaryIntroductionComponent
                        , focusedRequirement = AnyObviousProof
                        , focusedTarget = body
                        , focusedObligation = Nothing
                        , focusedEligibility = case focusedEligibility request of
                            SeedEligible family -> ExistingFamily WitnessBody family
                            ExistingFamily ExistentialBranch family -> ExistingFamily WitnessBody family
                            ExistingFamily ExtensionalityBranch family -> ExistingFamily WitnessBody family
                            existing -> structuralGroundEligibility existing }
                    continuation = IntroductionExistential binderType (Template.compiledTemplateTerm template) witness
                forked <- forkFocusedAlternatives owner ordinal continuations Nothing
                    [(FocusedDirectQuantum 512 (FocusedPreparedProbe child),
                        [AfterDirectProbe child (AfterFocusedIntroduction request child continuation)])
                    ,(FocusedWitnesses request available (WitnessPending cursor), [])] rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedExistentialOffer request child source binderType body remaining -> case focusedObligation child of
                Nothing -> complete owner ordinal (AttemptFailed (ObviousIntegrityFailure
                    (KernelProof.ProofStructuralCompositionMismatch "an existential branch lost its retained obligation"))) rest
                Just identifier -> do
                    forked <- forkFocusedAlternatives owner ordinal continuations Nothing
                        [(FocusedDemandCertificate GeneralSearch child identifier,
                            [AfterFocusedExistential request child source binderType body])
                        ,(FocusedExistentials request remaining, [])] rest
                    either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedTransport request (TransportOffer source left right following) -> do
                forked <- forkFocusedAlternatives owner ordinal continuations Nothing
                    [(FocusedDirectQuantum 512 (FocusedTransport request
                        (TransportPending (TransportRight SmallPreparation source left right))), [])
                    ,(FocusedTransport request (TransportPending following), [])] rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedTheorems input recursive step -> do
                forked <- forkFocusedSources owner ordinal continuations input recursive step rest
                either (\failure -> complete owner ordinal (AttemptFailed failure) rest) run forked
            FocusedDeferredPremise _request _following blocked -> do
                let ready = releaseFocusedDiscovery owner ordinal
                        (recordFocusedBlock owner ordinal blocked rest)
                case parkFocusedPremise task ready of
                    Just parked -> run parked
                    Nothing -> advance task ready
            FocusedMatchApplication _ _ _ step | theoremMatchIsDeferred step ->
                advance task (releaseFocusedDiscovery owner ordinal rest)
            FocusedApply _request (ApplicationPending _input work applicationFrames)
                | probedOpenPremise work applicationFrames ->
                    advance task (releaseFocusedDiscovery owner ordinal rest)
            _ -> advance task rest

    advance (FocusedTask owner ordinal action continuations) schedule =
        advanceFocused action continuations >>= \case
            Right (next, following) ->
                let task = FocusedTask owner ordinal next following
                    ready = if blocksFocusedDiscovery next || deferred action || deferred next
                        then releaseFocusedDiscovery owner ordinal schedule else schedule
                in if finishedFocusedAction next
                    then runActive task ready
                    else run (queueFocused task ready)
            Left result -> complete owner ordinal result schedule
    advance _sourceTask _schedule = pure (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a source cursor entered the scalar worker")))

    deferred action = case focusedActionEffort action of
        DeferredEffort -> True
        PreparatoryEffort -> False

    complete owner ordinal result before
        | AttemptFailed failure <- result, isFocusedInfrastructureFailure failure = pure result
        | otherwise = finish (releaseFocusedDiscovery owner ordinal before)
      where
        finish schedule = case owner of
                Choice.RootContinuation -> pure result
                Choice.OwnedChoice choiceId -> case Choice.lookup choiceId (scheduledChoices schedule) of
                    Nothing -> pure (AttemptFailed (ObviousIntegrityFailure
                        (KernelProof.ProofStructuralCompositionMismatch "focused choice lost its owner")))
                    Just choice ->
                        let FocusedChoice parentOrdinal following pending firstFailure discovery = Choice.payload choice
                            remaining = pending - 1
                            failure = rememberFocusedFailure ordinal firstFailure result
                            resume outcome = queueFocused
                                (FocusedTask (Choice.parent choice) parentOrdinal (FocusedReturn outcome) following)
                                schedule { scheduledChoices = Choice.retire choiceId (scheduledChoices schedule) }
                        in case result of
                            AttemptSucceeded{} -> run (resume result)
                            _ | remaining == 0 -> run (resume
                                    (maybe AttemptNotApplicable (AttemptFailed . snd) failure))
                              | otherwise -> run schedule { scheduledChoices = Choice.adjust (const
                                    (FocusedChoice parentOrdinal following remaining failure discovery)) choiceId
                                    (scheduledChoices schedule) }

blocksFocusedDiscovery :: FocusedAction global -> Bool
blocksFocusedDiscovery = \case
    FocusedDeferredPremise{} -> True
    FocusedMatchApplication _ _ _ step -> theoremMatchIsDeferred step
    FocusedApply _ (ApplicationPending _ task _) -> applicationIsDeferred task
    _ -> False

focusedTaskNeeded :: FocusedTask global -> FocusedSchedule global -> Bool
focusedTaskNeeded task = focusedOwnerNeeded (focusedTaskOwner task)

focusedOwnerNeeded :: Choice.Owner -> FocusedSchedule global -> Bool
focusedOwnerNeeded owner schedule
    | Map.null (scheduledProducers schedule) = True
    | otherwise = focusedOwnerDemanded consumerOwner consumers (scheduledChoices schedule) owner
  where
    consumerOwner (FocusedConsumer _role _requirement parent _ordinal _frames) = parent
    consumers identifier = case Map.lookup identifier (scheduledProducers schedule) of
        Nothing -> Seq.empty
        Just (FocusedProducer _progress attached) -> attached

-- Demand follows consumers, not ownership children. A cycle without an external
-- live consumer has no demand; a shared producer can be woken by a later consumer.
focusedOwnerDemanded
    :: Ord producer
    => (consumer -> Choice.Owner) -> (producer -> Seq consumer)
    -> Choice.Forest producer value -> Choice.Owner -> Bool
focusedOwnerDemanded consumerOwner consumers choices owner = neededOwner Set.empty owner []
  where
    neededOwner _seen Choice.RootContinuation _pending = True
    neededOwner seen (Choice.OwnedChoice choiceId) pending = case Choice.lookup choiceId choices of
        Nothing -> resume seen pending
        Just choice -> case Choice.producer choice of
            Nothing -> True
            Just identifier
                | Set.member identifier seen -> resume seen pending
                | otherwise -> resume (Set.insert identifier seen) (consumers identifier : pending)
    -- Saved consumer cursors preserve left-first short-circuiting without
    -- copying a frontier or revisiting shared subgraphs through another path.
    resume _seen [] = False
    resume seen (attached : pending) = case Seq.viewl attached of
        Seq.EmptyL -> resume seen pending
        consumer Seq.:< remaining -> neededOwner seen (consumerOwner consumer) (remaining : pending)

data FocusedDemandVisit consumer
    = DemandConsumers !(Maybe ProofRequirement) !(Seq consumer)
    | DemandOwner !(Maybe ProofRequirement) !Choice.Owner

-- New equality inference needs an uninterrupted path of driving subscriptions
-- to a live requester. The label is the target consumer's local requirement:
-- an ancestor's canonical demand establishes liveness, not child authority.
-- Notifications must be processed before this atomic check. Do not use this
-- charged traversal for legacy delivery or cleanup. A native worker retaining
-- a bounded phase owner uses its own ground account, not focused credit.
countedFocusedDrivingRequirement
    :: Ord producer
    => Word -> (consumer -> (FocusedConsumerRole, ProofRequirement, Choice.Owner))
    -> (producer -> Seq consumer) -> Choice.Forest producer value -> producer
    -> (Either (CountedCoreFailure Void) (Maybe ProofRequirement), Word)
countedFocusedDrivingRequirement available consumerInfo consumers choices target =
    State.runState (Except.runExceptT (visit Set.empty Nothing
        [DemandConsumers Nothing (consumers target)])) available
  where
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwE CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    visit _seen requirement [] = pure requirement
    visit seen requirement (next : pending) = do
        charge
        case next of
            DemandConsumers inherited attached -> case Seq.viewl attached of
                Seq.EmptyL -> visit seen requirement pending
                consumer Seq.:< rest ->
                    let (role, local, owner) = consumerInfo consumer
                        following = DemandConsumers inherited rest : pending
                    in case role of
                        ExistingEvidenceWait -> visit seen requirement following
                        SearchDependency -> visit seen requirement
                            (DemandOwner (Just (fromMaybe local inherited)) owner : following)
                        -- Same-goal delegation retains capacity, not demand. Its
                        -- live callers select the requirement, including upgrades.
                        PhaseDelegation -> visit seen requirement
                            (DemandOwner inherited owner : following)
            DemandOwner local owner -> case Choice.ownerProducer owner choices of
                Nothing -> visit seen requirement pending
                Just Nothing -> visit seen (maybe requirement (`combine` requirement) local) pending
                Just (Just producer)
                    | Set.member (local, producer) seen -> visit seen requirement pending
                    | otherwise -> visit (Set.insert (local, producer) seen) requirement
                        (DemandConsumers local (consumers producer) : pending)
    combine MustUseCanonicalDefinition _ = Just MustUseCanonicalDefinition
    combine AnyObviousProof Nothing = Just AnyObviousProof
    combine AnyObviousProof previous = previous

-- At the fixed point, a cycle of unfilled support slots is an honest miss.
-- Application source and substitution discovery run independently of these
-- consumers. An acyclic missing return remains an infrastructure failure;
-- this is not a catch-all empty-queue exit.
blockedFocusedSupport
    :: FocusedSchedule global -> State (ObviousSearchState global) (Attempt global)
blockedFocusedSupport schedule = do
    checked <- Except.runExceptT do
        nodes <- traverse producerNode (Map.toAscList (scheduledProducers schedule))
        failures <- foldM collectFailure Nothing (Choice.rows (scheduledChoices schedule))
        pure (mapMaybe cyclic (Graph.stronglyConnComp nodes),
            any (\((_target, canonical), _key, _parents) -> canonical) nodes, failures)
    pure case checked of
        Left failure -> AttemptFailed failure
        Right (target : _, canonical, failure) -> AttemptFailed
            (maybe (if canonical then ObviousCanonicalDefinitionEvidenceRequired
                else ObviousRepeatedState target) snd failure)
        Right ([], _, _) -> AttemptFailed (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch "focused search lost a pending continuation"))
  where
    producerNode (key@(FocusedProducerKey (FocusedObligationId position) _phase), FocusedProducer _progress consumers) = do
        scopeCharge
        parents <- traverse dependency consumers
        row <- State.gets (Seq.lookup position . searchFocusedObligations)
        target <- case row of
            Just (FocusedObligation statement _certificates _subscribed) -> pure statement
            Nothing -> scopeIntegrity "a blocked producer lost its obligation"
        let canonical = any (== Just MustUseCanonicalDefinition) (snd <$> parents)
        pure ((target, canonical), key, foldMap (maybe [] pure . fst) parents)
    dependency (FocusedConsumer _role requirement owner _ordinal _frames) = do
        scopeCharge
        pure (if focusedOwnerNeeded owner schedule
            then (Choice.ownerProducer owner (scheduledChoices schedule) >>= id, Just requirement)
            else (Nothing, Nothing))
    collectFailure previous (identifier, choice) = do
        scopeCharge
        let FocusedChoice _ordinal _frames _pending failure _discovery = Choice.payload choice
        pure case failure of
            Just (ordinal, cause)
                | focusedOwnerNeeded (Choice.OwnedChoice identifier) schedule
                , isTerminalFocusedFailure cause || isConversionLimit cause ->
                    rememberFocusedFailure ordinal previous (AttemptFailed cause)
            _ -> previous
    cyclic (Graph.CyclicSCC ((target, _) : _)) = Just target
    cyclic _ = Nothing

-- A newly registered consumer can make a retained dependency chain runnable.
-- Re-offer dormant tasks in their retained order; the demand check parks tasks
-- with no live consumer again. No source or worker cursor is recreated.
wakeFocusedFrontier :: FocusedSchedule global -> FocusedSchedule global
wakeFocusedFrontier schedule = foldl' offer
    schedule {scheduledDormant = Seq.empty} (scheduledDormant schedule)
  where
    offer current task
        | Choice.live (focusedTaskOwner task) (scheduledChoices current) = queueFocused task current
        | otherwise = current

-- At quiescence observers have no operation that could make progress. Return
-- their local miss without settling the producer: another alternative may now
-- attach a real consumer and resume its paid, dormant frontier in this request.
-- Subscription admission already paid for this administrative retirement.
settleFocusedObservers :: FocusedSchedule global -> Maybe (FocusedSchedule global)
settleFocusedObservers schedule | not (any bounded (scheduledDormant schedule)) = Nothing
  where
    bounded task = case task of
        FocusedTask _ _ FocusedEqualityEntry{} _ -> True
        FocusedTask _ _ FocusedArgumentEntry{} _ -> True
        FocusedTask _ _ FocusedPhaseEntry{} _ -> True
        _ -> case Choice.ownerProducer (focusedTaskOwner task) (scheduledChoices schedule) of
            Just (Just (FocusedProducerKey _ phase)) -> case phase of
                EqualityReasoning -> True
                PrefixEvidence -> True
                ArgumentCompletion -> True
                DirectEvidence -> False
                GeneralSearch -> False
                EndpointSearch -> False
            _ -> False
settleFocusedObservers schedule =
    let (changed, resumed) = Map.foldlWithKey' settle (False, schedule) (scheduledProducers schedule)
    in if changed then Just resumed else Nothing
  where
    settle (changed, current) key (FocusedProducer progress consumers) =
        let (waiting, returns) = foldr select (Seq.empty, []) consumers
            updated = current {scheduledProducers = Map.insert key
                (FocusedProducer progress waiting) (scheduledProducers current)}
        in (changed || not (null returns), foldl' (flip queueFocused) updated returns)
    select consumer@(FocusedConsumer role _ owner ordinal frames) (waiting, returns) = case role of
        ExistingEvidenceWait | Choice.live owner (scheduledChoices schedule) ->
            (waiting, FocusedTask owner ordinal (FocusedReturn AttemptNotApplicable) frames : returns)
        ExistingEvidenceWait -> (waiting, returns)
        SearchDependency -> (consumer Seq.<| waiting, returns)
        PhaseDelegation -> (consumer Seq.<| waiting, returns)

notifyFocusedConsumers
    :: FocusedObligationId -> FocusedSchedule global
    -> State (ObviousSearchState global) (FocusedSchedule global)
notifyFocusedConsumers identifier schedule = do
    snapshot <- lookupFocusedCertificates identifier
    pure (foldl' (notifyPhase snapshot) schedule focusedPhases)
  where
    notifyPhase snapshot current phase =
        let key = FocusedProducerKey identifier phase
        in case Map.lookup key (scheduledProducers current) of
            Nothing -> current
            Just (FocusedProducer progress consumers) ->
                let (waiting, notified) = foldl' (deliverFocusedConsumer snapshot progress) (Seq.empty, current) consumers
                in notified {scheduledProducers = Map.insert key
                    (FocusedProducer progress waiting) (scheduledProducers notified)}

-- Registration wakes the same retained frontier as before, but evaluates only
-- the new waiter. Real publication and phase completion broadcast to all phases.
registerFocusedConsumer
    :: Maybe (FocusedCertificates global) -> FocusedProducerKey -> FocusedConsumer global
    -> FocusedProducer global -> FocusedSchedule global -> FocusedSchedule global
registerFocusedConsumer snapshot key consumer (FocusedProducer progress consumers) schedule =
    let (waiting, notified) = deliverFocusedConsumer snapshot progress
            (consumers, wakeFocusedFrontier schedule) consumer
    in notified {scheduledProducers = Map.insert key (FocusedProducer progress waiting) (scheduledProducers notified)}

deliverFocusedConsumer
    :: Maybe (FocusedCertificates global) -> FocusedPhaseState global
    -> (Seq (FocusedConsumer global), FocusedSchedule global) -> FocusedConsumer global
    -> (Seq (FocusedConsumer global), FocusedSchedule global)
deliverFocusedConsumer snapshot progress (waiting, schedule) consumer@(FocusedConsumer _role requirement owner ordinal frames)
    | not (Choice.live owner (scheduledChoices schedule)) = (waiting, schedule)
    | otherwise = case focusedConsumerOutcome snapshot progress requirement of
        Nothing -> (waiting Seq.|> consumer, schedule)
        Just outcome -> (waiting, queueFocused (FocusedTask owner ordinal (FocusedReturn outcome) frames) schedule)

focusedConsumerOutcome
    :: Maybe (FocusedCertificates global) -> FocusedPhaseState global -> ProofRequirement
    -> Maybe (Attempt global)
focusedConsumerOutcome snapshot progress requirement =
    case snapshot >>= selectFocusedCertificate requirement of
        Just proof -> Just (AttemptSucceeded proof)
        Nothing -> case completed of
            Just (AttemptFailed failure) | isTerminalFocusedFailure failure -> completed
            Just _ | requirement == MustUseCanonicalDefinition
                , isJust (snapshot >>= selectFocusedCertificate AnyObviousProof) ->
                    Just (AttemptFailed ObviousCanonicalDefinitionEvidenceRequired)
            _ -> completed
  where
    completed = case progress of
        FinishedPhase outcome -> Just outcome
        RunningPhase{} -> Nothing

-- Finished native workers merely deliver an already checked result. Returning
-- it is not a new inference opportunity and should not allocate a queue entry
-- or let unrelated source discovery delay its waiting proof continuation.
finishedFocusedAction :: FocusedAction global -> Bool
finishedFocusedAction = \case
    FocusedReturn{} -> True
    FocusedConvertRequest _ _ HeadProofFinished{} -> True
    FocusedRules{} -> True
    FocusedSearch{} -> True
    FocusedProduce{} -> True
    FocusedDirectRules{} -> True
    FocusedExactCandidates _ (ExactFinished _) -> True
    FocusedExactCandidates _ ExactFound{} -> True
    FocusedProjectionCandidates _ _ (ProjectionFinished _) -> True
    FocusedProjectionCandidates _ _ ProjectionFound{} -> True
    FocusedFalsumCandidates _ _ (FalsumFinished _) -> True
    FocusedFalsumCandidates _ _ FalsumFound{} -> True
    FocusedEqualities _ _ (EqualityFinished _) -> True
    FocusedEqualities _ _ EqualityFound{} -> True
    FocusedIntroduce _ (IntroductionFinished _) -> True
    FocusedWitnesses _ _ WitnessFinished{} -> True
    FocusedConjoin _ (ConjunctionFinished _) -> True
    FocusedTheorems _ _ (TheoremFinished _) -> True
    FocusedApply _ (ApplicationFinished _) -> True
    FocusedApply _ ApplicationFound{} -> True
    FocusedTransport _ (TransportFinished _) -> True
    FocusedTransport _ TransportFound{} -> True
    FocusedGoalViews _ (GoalDefinitionFinished _) -> True
    FocusedFactViews _ _ _ (FactDefinitionFinished _) -> True
    _ -> False

-- A fixed substitution can check all of its supplied premises directly. An
-- open template gets one fact probe in the initial round; exhausting all of its
-- substitutions is not a prerequisite for exploration by other candidates.
probedOpenPremise :: ApplicationTask global -> [ApplicationFrame global] -> Bool
probedOpenPremise ApplicationNextFact{} _frames = True
probedOpenPremise _work (AfterMatchedPremise{} : _frames) = True
probedOpenPremise _work _frames = False

recordFocusedBlock
    :: Choice.Owner -> Natural -> Maybe (ObviousFailure global)
    -> FocusedSchedule global -> FocusedSchedule global
recordFocusedBlock (Choice.OwnedChoice choiceId) ordinal (Just failure) schedule = schedule
    { scheduledChoices = Choice.adjust
        (\(FocusedChoice ticket frames pending previous discovery) ->
            FocusedChoice ticket frames pending
                (rememberFocusedFailure ordinal previous (AttemptFailed failure)) discovery)
        choiceId (scheduledChoices schedule)
    }
recordFocusedBlock _owner _ordinal _failure schedule = schedule

releaseFocusedDiscovery :: Choice.Owner -> Natural -> FocusedSchedule global -> FocusedSchedule global
releaseFocusedDiscovery (Choice.OwnedChoice choiceId) ordinal schedule =
    case Choice.lookup choiceId (scheduledChoices schedule) of
        Just choice
            | FocusedChoice ticket frames pending failure (Discovering tickets parked) <- Choice.payload choice
            , Set.member ordinal tickets ->
                let remaining = Set.delete ordinal tickets
                    discovery = if Set.null remaining then DiscoveryComplete else Discovering remaining parked
                    updated = schedule { scheduledChoices = Choice.adjust
                        (const (FocusedChoice ticket frames pending failure discovery)) choiceId (scheduledChoices schedule) }
                in if Set.null remaining
                    then releaseFocusedDiscovery (Choice.parent choice) ticket (foldl' (flip queueFocused) updated parked)
                    else updated
        _ -> schedule
releaseFocusedDiscovery Choice.RootContinuation _ordinal schedule = schedule

-- Ground activation waits on the actual inherited supplied-source tickets,
-- including their emitted direct dependencies. Unrelated completed choices
-- cannot certify this boundary. The task retains its exact query cursor.
parkGroundOpportunity :: FocusedTask global -> FocusedSchedule global -> Maybe (FocusedSchedule global)
parkGroundOpportunity task schedule = visit (focusedTaskOwner task)
  where
    visit Choice.RootContinuation = Nothing
    visit (Choice.OwnedChoice identifier) = case Choice.lookup identifier (scheduledChoices schedule) of
        Nothing -> Nothing
        Just choice -> case Choice.payload choice of
            FocusedChoice ticket frames pending failure (Discovering tickets parked) ->
                Just schedule {scheduledChoices = Choice.adjust
                    (const (FocusedChoice ticket frames pending failure (Discovering tickets (parked Seq.|> task))))
                    identifier (scheduledChoices schedule)}
            _ -> visit (Choice.parent choice)

-- A later epoch captures existing preparatory producers below this goal's
-- choice, plus their outstanding direct dependencies. Full-effort sources have
-- already yielded their bounded opportunity. Newly created producer groups do
-- not join this snapshot. Re-arming a retained source ticket does not restart
-- its scan or reclaim any of its work.
captureGroundOpportunity
    :: Choice.Owner -> FocusedSchedule global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) ([Natural], FocusedSchedule global))
captureGroundOpportunity owner schedule = Except.runExceptT do
    armed <- foldM arm schedule (scheduledPreparation schedule)
    choices <- foldM (collect armed) [] (Choice.rows (scheduledChoices armed))
    pure (reverse choices, armed)
  where
    -- Only this finite activation snapshot walks ancestry. Ordinary task
    -- liveness still uses the forest's direct owner lookup.
    belongs current = case owner of
        Choice.RootContinuation -> const False
        Choice.OwnedChoice target -> visit
          where
            visit Choice.RootContinuation = False
            visit (Choice.OwnedChoice identifier)
                | identifier == target = True
                | otherwise = maybe False (visit . Choice.parent)
                    (Choice.lookup identifier (scheduledChoices current))
    arm current task = do
        scopeChargeTo GroundScopeWork
        let selected = case task of
                FocusedSourceTask parent ordinal _input _recursive _step -> Just (parent, ordinal)
                FocusedFactSourceTask parent ordinal _input _direct _selection _seen _step -> Just (parent, ordinal)
                _ -> Nothing
        pure case selected of
            Just (parent@(Choice.OwnedChoice choice), ordinal)
                | belongs current parent, focusedTaskNeeded task current
                , Choice.live parent (scheduledChoices current) ->
                    current {scheduledChoices = Choice.adjust
                        (\(FocusedChoice ticket frames pending failure discovery) ->
                            FocusedChoice ticket frames pending failure (case discovery of
                                DiscoveryComplete -> Discovering (Set.singleton ordinal) Seq.empty
                                Discovering tickets parked -> Discovering (Set.insert ordinal tickets) parked))
                        choice (scheduledChoices current)}
            _ -> current
    collect current accumulated (identifier, choice) = do
        scopeChargeTo GroundScopeWork
        let FocusedChoice _ticket _frames _pending _failure discovery = Choice.payload choice
        pure case discovery of
            Discovering{} | belongs current (Choice.parent choice)
                , focusedOwnerNeeded (Choice.OwnedChoice identifier) current -> identifier : accumulated
            _ -> accumulated

parkFocusedPremise :: FocusedTask global -> FocusedSchedule global -> Maybe (FocusedSchedule global)
parkFocusedPremise task schedule = case focusedTaskOwner task of
    Choice.OwnedChoice choiceId -> case Choice.payload <$> Choice.lookup choiceId (scheduledChoices schedule) of
        Just (FocusedChoice ticket frames pending failure (Discovering tickets parked)) ->
            Just schedule { scheduledChoices = Choice.adjust
                (const (FocusedChoice ticket frames pending failure (Discovering tickets (parked Seq.|> task))))
                choiceId (scheduledChoices schedule) }
        _ -> Nothing
    Choice.RootContinuation -> Nothing

-- Charge ownership registration at admission, including its eventual retirement.
-- This bounds the iterative cleanup by paid choices without making delivery of
-- an already checked result depend on unused proof-search credit.
admitFocusedChoice
    :: (FocusedChoice global -> Choice.Forest FocusedProducerKey (FocusedChoice global)
        -> Maybe (Choice.Forest FocusedProducerKey (FocusedChoice global)))
    -> FocusedChoice global -> FocusedSchedule global
    -> Either (ObviousFailure global) (Choice.Forest FocusedProducerKey (FocusedChoice global))
admitFocusedChoice insert choice schedule = maybe
    (Left (ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
        "focused choice admission lost its parent or reused an identifier")))
    Right (insert choice (scheduledChoices schedule))

-- The source cursor owns discovery only. A candidate's missing premise cannot
-- consume that cursor or hide the remaining supplied sources from the queue.
forkFocusedSources
    :: Choice.Owner -> Natural -> [FocusedContinuation global]
    -> FocusedRulesInput global -> Bool -> TheoremStep global -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
forkFocusedSources owner ordinal frames input recursive step schedule = Except.runExceptT do
    scopeCharge
    scopeCharge
    scopeCharge
    let choiceId = scheduledNextId schedule
        sourceId = choiceId + 1
    choices <- Except.except (admitFocusedChoice (Choice.insert choiceId owner)
        (FocusedChoice ordinal frames 1 Nothing (Discovering (Set.singleton sourceId) Seq.empty)) schedule)
    pure (queueFocused (FocusedSourceTask (Choice.OwnedChoice choiceId) sourceId input recursive step)
        schedule {scheduledNextId = sourceId + 1, scheduledChoices = choices})

-- Fact discovery shares the existing finite discovery/choice protocol. Emitted
-- candidates own preparation and search; the source keeps only its next cursor.
forkFocusedFactSources
    :: Choice.Owner -> Natural -> [FocusedContinuation global]
    -> FocusedRulesInput global -> Bool -> DefinitionViewSelection -> FactDefinitionStep global
    -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
forkFocusedFactSources owner ordinal frames input direct selection step schedule = Except.runExceptT do
    scopeCharge
    scopeCharge
    scopeCharge
    let choice = scheduledNextId schedule
        source = choice + 1
    choices <- Except.except (admitFocusedChoice (Choice.insert choice owner)
        (FocusedChoice ordinal frames 1 Nothing (Discovering (Set.singleton source) Seq.empty)) schedule)
    pure (queueFocused (FocusedFactSourceTask (Choice.OwnedChoice choice) source input direct selection [] step)
        schedule {scheduledNextId = source + 1, scheduledChoices = choices})

addFocusedFact
    :: Choice.Owner -> FocusedRulesInput global -> Bool -> ObviousProof global -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
addFocusedFact owner input direct proof schedule = Except.runExceptT do
    scopeCharge
    choice <- case owner of
        Choice.OwnedChoice firstChoice -> pure firstChoice
        Choice.RootContinuation -> scopeIntegrity "a fact producer lost its choice"
    FocusedChoice ordinal frames pending failure discovery <- maybe
        (scopeIntegrity "a fact producer lost its continuation") pure
        (Choice.payload <$> Choice.lookup choice (scheduledChoices schedule))
    let candidate = scheduledNextId schedule
        immediate = FocusedDirectQuantum 512 (FocusedUseFact input direct proof)
        tickets = case discovery of
            Discovering current parked -> Discovering (Set.insert candidate current) parked
            DiscoveryComplete -> DiscoveryComplete
    pure (queueFocused (FocusedTask owner candidate immediate [AfterFocusedRule input [] Nothing False])
        schedule {scheduledNextId = candidate + 1
            , scheduledChoices = Choice.adjust
                (const (FocusedChoice ordinal frames (pending + 1) failure tickets)) choice (scheduledChoices schedule)})

addFocusedApplication
    :: Choice.Owner -> FocusedRulesInput global -> ApplicationStart global -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
addFocusedApplication owner input@(FocusedRulesInput request _available _continue) started schedule = do
    hasWork <- consumeSearchStep
    if not hasWork then pure focusedWorkExhausted else pure do
        choiceId <- case owner of
            Choice.RootContinuation -> Left (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch "a focused source has no choice owner"))
            Choice.OwnedChoice choice -> Right choice
        FocusedChoice ordinal frames pending firstFailure discovery <- maybe
            (Left (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch "a focused source lost its choice owner")))
            (Right . Choice.payload) (Choice.lookup choiceId (scheduledChoices schedule))
        let candidateId = scheduledNextId schedule
            required = [AfterFocusedRule input [] Nothing False]
            task = case started of
                ApplicationComplete result -> FocusedTask owner candidateId (FocusedReturn result) required
                ApplicationMatching candidate application step -> FocusedTask owner candidateId
                    (FocusedMatchApplication request candidate application step) required
                ApplicationMatched candidate progress next -> FocusedTask owner candidateId
                    (FocusedDirectQuantum 512 (FocusedApply request next))
                    (AfterMatchedTheorem candidate progress : required)
        pure (queueFocused task schedule
            { scheduledNextId = candidateId + 1
            , scheduledChoices = Choice.adjust
                (const (FocusedChoice ordinal frames (pending + 1) firstFailure (case (started, discovery) of
                    (ApplicationMatched{}, Discovering tickets parked) ->
                        Discovering (Set.insert candidateId tickets) parked
                    (ApplicationMatching{}, Discovering tickets parked) ->
                        Discovering (Set.insert candidateId tickets) parked
                    _ -> discovery))) choiceId (scheduledChoices schedule)
            })

forkFocusedRules
    :: Choice.Owner -> Natural -> [FocusedContinuation global]
    -> FocusedRulesInput global
    -> [FocusedRule global]
    -> Maybe (ObviousFailure global)
    -> Bool
    -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
forkFocusedRules owner ordinal frames input rules firstFailure rejected =
    forkFocusedAlternatives owner ordinal frames
        (rememberFocusedFailure ordinal (fmap (\failure -> (ordinal, failure)) firstFailure)
            (if rejected then AttemptFailed ObviousCanonicalDefinitionEvidenceRequired else AttemptNotApplicable))
        [(FocusedRunRule input rule, [AfterFocusedRule input [] Nothing False]) | rule <- rules]

forkFocusedAlternatives
    :: Choice.Owner -> Natural -> [FocusedContinuation global]
    -> Maybe (Natural, ObviousFailure global)
    -> [(FocusedAction global, [FocusedContinuation global])]
    -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
forkFocusedAlternatives = forkFocusedAlternativesWith FocusedScopeWork

forkFocusedAlternativesWith
    :: ScopeWork -> Choice.Owner -> Natural -> [FocusedContinuation global]
    -> Maybe (Natural, ObviousFailure global)
    -> [(FocusedAction global, [FocusedContinuation global])]
    -> FocusedSchedule global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedSchedule global))
forkFocusedAlternativesWith workOwner owner ordinal frames firstFailure alternatives schedule = Except.runExceptT do
        scopeChargeTo workOwner
        scopeChargeTo workOwner
        let choiceId = scheduledNextId schedule
        choices <- Except.except (admitFocusedChoice (Choice.insert choiceId owner)
            (FocusedChoice ordinal frames (fromIntegral (length alternatives)) firstFailure discovery) schedule)
        admit choiceId alternatives schedule {scheduledNextId = choiceId + 1, scheduledChoices = choices}
  where
    discovery = case owner of
        Choice.OwnedChoice choice -> case Choice.payload <$> Choice.lookup choice (scheduledChoices schedule) of
            Just (FocusedChoice _ _ _ _ (Discovering tickets _)) | Set.member ordinal tickets ->
                Discovering Set.empty Seq.empty
            _ -> DiscoveryComplete
        Choice.RootContinuation -> DiscoveryComplete
    admit _choice [] current = pure current
    admit choice ((action, following) : rest) current = do
        scopeChargeTo workOwner
        let ticket = scheduledNextId current
            task = FocusedTask (Choice.OwnedChoice choice) ticket action following
        admit choice rest (queueFocused task current { scheduledNextId = ticket + 1
            , scheduledChoices = Choice.adjust
                (\(FocusedChoice parentTicket parentFrames pending failure captured) ->
                    FocusedChoice parentTicket parentFrames pending failure (case captured of
                        Discovering tickets parked -> Discovering (Set.insert ticket tickets) parked
                        DiscoveryComplete -> DiscoveryComplete)) choice (scheduledChoices current) })

rememberFocusedFailure
    :: Natural
    -> Maybe (Natural, ObviousFailure global)
    -> Attempt global
    -> Maybe (Natural, ObviousFailure global)
rememberFocusedFailure ordinal previous = \case
    AttemptFailed failure -> case previous of
        Just (earlier, found) | (rank found, earlier) <= (rank failure, ordinal) -> previous
        _ -> Just (ordinal, failure)
    _ -> previous
  where
    rank = \case
        ObviousResourceExhausted ObviousConversionPoolLimit -> 0 :: Int
        ObviousResourceExhausted ObviousConversionOperationLimit -> 0
        ObviousResourceExhausted{} -> 1
        ObviousUnsupportedTermOutsideUniverse -> 2
        ObviousCanonicalDefinitionEvidenceRequired -> 3
        ObviousUnsupportedHigherOrderInstantiation -> 4
        ObviousUndeterminedParameter{} -> 4
        _ -> 5

queueFocused :: FocusedTask global -> FocusedSchedule global -> FocusedSchedule global
queueFocused task@(FocusedSourceTask _ _ _ _ step) schedule = case step of
    TheoremPending (TheoremPreparing _ _ _ preparation) | theoremSourceIsDeferred preparation ->
        schedule { scheduledDeferred = scheduledDeferred schedule Seq.|> task }
    _ -> schedule { scheduledPreparation = scheduledPreparation schedule Seq.|> task }
queueFocused task@(FocusedFactSourceTask _ _ input direct selection _seen step) schedule =
    case focusedActionEffort (FocusedFactViews input direct selection step) of
        PreparatoryEffort -> schedule {scheduledPreparation = scheduledPreparation schedule Seq.|> task}
        DeferredEffort -> schedule {scheduledDeferred = scheduledDeferred schedule Seq.|> task}
queueFocused task@(FocusedTask _path _ordinal action _frames) schedule = case action of
    FocusedDirectQuantum{} -> schedule { scheduledDirect = scheduledDirect schedule Seq.|> task }
    FocusedReturn{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    FocusedSearch{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    FocusedDemandCertificate{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    FocusedProduce{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    FocusedRules{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    FocusedDirectRules{} -> schedule { scheduledReturns = scheduledReturns schedule Seq.|> task }
    _ -> case focusedActionEffort action of
        PreparatoryEffort -> schedule { scheduledPreparation = scheduledPreparation schedule Seq.|> task }
        DeferredEffort -> schedule { scheduledDeferred = scheduledDeferred schedule Seq.|> task }

focusedActionEffort :: FocusedAction global -> FocusedEffort
focusedActionEffort = \case
    FocusedBooleanBuild{} -> PreparatoryEffort
    FocusedPointwiseProbe{} -> PreparatoryEffort
    FocusedPointwiseLeaf{} -> PreparatoryEffort
    FocusedPointwiseBuild{} -> PreparatoryEffort
    FocusedPrefixBegin{} -> PreparatoryEffort
    FocusedPrefixTheorems{} -> PreparatoryEffort
    FocusedPhaseEntry{} -> PreparatoryEffort
    FocusedPublish{} -> PreparatoryEffort
    FocusedDirectQuantum{} -> PreparatoryEffort
    FocusedRules{} -> PreparatoryEffort
    FocusedDirectRules{} -> PreparatoryEffort
    FocusedEndpointRequest{} -> PreparatoryEffort
    FocusedEndpointBegin{} -> PreparatoryEffort
    FocusedEndpointSearch _ (TheoremPending (TheoremPreparing _ _ _ source))
        | theoremSourceIsDeferred source -> DeferredEffort
    FocusedEndpointSearch{} -> PreparatoryEffort
    FocusedEndpointSource{} -> PreparatoryEffort
    FocusedEndpointSourceWithContinuation{} -> PreparatoryEffort
    FocusedEndpointReverse _ effort _ -> if preparationIsDeferred effort then DeferredEffort else PreparatoryEffort
    FocusedEndpointSupport _ effort _ _ -> if preparationIsDeferred effort then DeferredEffort else PreparatoryEffort
    FocusedEndpointGuard{} -> PreparatoryEffort
    FocusedExistingEvidence{} -> PreparatoryEffort
    FocusedAwaitEvidence{} -> PreparatoryEffort
    FocusedStart request -> case focusedObservation request of
        SuppressAuxiliary AuxiliaryTheoremAntecedent -> DeferredEffort
        SuppressAuxiliary AuxiliaryTransportPremise -> DeferredEffort
        _ -> PreparatoryEffort
    FocusedDirectPremise{} -> PreparatoryEffort
    FocusedUseFact{} -> PreparatoryEffort
    FocusedDirectBody{} -> PreparatoryEffort
    FocusedConvertRequest _ _ step | headProofIsDeferred step -> DeferredEffort
    FocusedPreparedProbe{} -> PreparatoryEffort
    FocusedPreparedTarget{} -> PreparatoryEffort
    FocusedRetryHead{} -> DeferredEffort
    FocusedGoalViews _ (GoalDefinitionPending (GoalDefinitionPrepareRoots step))
        | rootObservationIsDeferred step -> DeferredEffort
    FocusedGoalViews _ (GoalDefinitionPending (GoalDefinitionSpecialize _ _ _ step))
        | definitionSpecializationIsDeferred step -> DeferredEffort
    FocusedGoalViews _ (GoalDefinitionPending (GoalDefinitionExpose _ _ _ step))
        | observationExposureIsDeferred step -> DeferredEffort
    FocusedGoalViews _ (GoalDefinitionPending (GoalDefinitionBuild _ step))
        | viewProofIsDeferred step -> DeferredEffort
    FocusedGoalViews{} -> PreparatoryEffort
    FocusedRunRule _input rule -> case rule of
        FocusedExactContinuation (ExactPending ExactRetry{}) -> DeferredEffort
        FocusedExactContinuation{} -> PreparatoryEffort
        FocusedExact ConvertExactCandidates -> PreparatoryEffort
        FocusedCitedDefinitions -> PreparatoryEffort
        FocusedExact DeferExactCandidateConversion -> PreparatoryEffort
        FocusedProjection DeferExactCandidateConversion -> PreparatoryEffort
        FocusedIntroduction -> PreparatoryEffort
        FocusedDirectIntroduction -> PreparatoryEffort
        FocusedWitness -> PreparatoryEffort
        FocusedStructuralEquality{} -> PreparatoryEffort
        FocusedArgumentTransport -> PreparatoryEffort
        FocusedTheorem -> PreparatoryEffort
        FocusedLocalFacts -> PreparatoryEffort
        FocusedGoalDefinitions -> PreparatoryEffort
        _ -> DeferredEffort
    FocusedExactCandidates _request (ExactPending ExactRetry{}) -> DeferredEffort
    FocusedExactCandidates{} -> PreparatoryEffort
    FocusedProjectionCandidates _ _ step | projectionIsDeferred step -> DeferredEffort
    FocusedProjectionCandidates{} -> PreparatoryEffort
    FocusedEqualities _ DeferExactCandidateConversion step ->
        if equalityIsDeferred step then DeferredEffort else PreparatoryEffort
    FocusedIntroduce{} -> PreparatoryEffort
    -- A proposed value is speculative. Supplied proof sources retain their
    -- preparation opportunity before discovery offers another body search.
    FocusedWitnesses{} -> DeferredEffort
    FocusedExistentials{} -> DeferredEffort
    FocusedExistentialOffer{} -> DeferredEffort
    FocusedConjoin{} -> PreparatoryEffort
    FocusedTheorems{} -> PreparatoryEffort
    FocusedMatchApplication _ _ _ step | theoremMatchIsDeferred step -> DeferredEffort
    FocusedMatchApplication{} -> PreparatoryEffort
    FocusedApply _ (ApplicationPending _ task _) | applicationIsDeferred task -> DeferredEffort
    FocusedApply{} -> PreparatoryEffort
    FocusedFactViews _ _ _ (FactDefinitionPending (FactDefinitionExpose _ _ _ step))
        | sourceExposureIsDeferred step -> DeferredEffort
    FocusedFactViews _ _ _ (FactDefinitionPending (FactDefinitionPrepareRoots _ step))
        | rootObservationIsDeferred step -> DeferredEffort
    FocusedFactViews _ _ _ (FactDefinitionPending (FactDefinitionSpecialize _ _ _ _ step))
        | definitionSpecializationIsDeferred step -> DeferredEffort
    FocusedFactViews _ _ _ (FactDefinitionPending (FactDefinitionExpand _ step))
        | factExpansionIsDeferred step -> DeferredEffort
    FocusedTransport _ (TransportPending cursor) | transportIsDeferred cursor -> DeferredEffort
    FocusedTransport _ (TransportPending TransportArguments{}) -> PreparatoryEffort
    FocusedTransport _ (TransportPending (TransportDiscover (PropositionTransportScan _ _ SuppliedEquations) _)) -> PreparatoryEffort
    FocusedTransport _ (TransportPending (TransportDescend (PropositionTransportScan _ _ SuppliedEquations) _ _)) -> PreparatoryEffort
    FocusedTransport _ (TransportPending (TransportEquality _ _ _ _ step))
        | endpointEqualityStep step -> PreparatoryEffort
    FocusedTransport _ (TransportPending TransportReconstruct{}) -> PreparatoryEffort
    FocusedFactViews _input _direct LocalDefinitionViewsOnly _step -> PreparatoryEffort
    FocusedFactViews _input True _selection _step -> PreparatoryEffort
    _ -> DeferredEffort

-- A fixed finite preparation slice, followed by a deferred/recursive turn.
-- Administrative returns finish their already selected recipe. New sources
-- cannot extend the slice; FIFO ordering is stable within each effort class.
popFocused :: FocusedSchedule global -> Maybe (FocusedTask global, FocusedSchedule global)
popFocused schedule = case Seq.viewl (scheduledReturns schedule) of
    task Seq.:< rest -> Just (task, schedule { scheduledReturns = rest })
    Seq.EmptyL -> case Seq.viewl (scheduledDirect schedule) of
        task Seq.:< rest -> Just (task, schedule { scheduledDirect = rest })
        Seq.EmptyL
            | scheduledCheapTurns schedule > 0 -> cheap <|> full
            | otherwise -> full <|> cheap
  where
    cheap = case Seq.viewl (scheduledPreparation schedule) of
        task Seq.:< rest -> Just (task, spent schedule { scheduledPreparation = rest })
        Seq.EmptyL -> Nothing
    full = case Seq.viewl (scheduledDeferred schedule) of
        task Seq.:< rest -> Just (task, schedule
            { scheduledDeferred = rest, scheduledCheapTurns = 512 })
        Seq.EmptyL -> Nothing
    spent current = current { scheduledCheapTurns = if scheduledCheapTurns current == 0
        then 0 else scheduledCheapTurns current - 1 }

-- Run the existing direct-candidate cursor before allocating a family or an
-- obligation. A miss transfers its observations and remaining allowance to
-- the driver at the next rule; neither preparation nor the scan is restarted.
proveRoot
    :: Ord global
    => ProofRequirement
    -> SearchEnvironment global
    -> FocusedContextId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (ObviousProof global))
proveRoot requirement environment contextId context target = do
    prepared <- prepareFocusedTargetSmall observation environment target
    entry <- case prepared of
        PreparationFinished (Left failure) -> failed Nothing failure
        PreparationFinished (Right exposed) -> Except.runExceptT (directRoot exposed) >>= \case
            Left failure -> failed Nothing failure
            Right next -> pure next
        NeedsMoreEffort offered -> admitGroundFamily contextId context target rootImports >>= \case
            Left failure -> failed Nothing failure
            Right eligibility -> pure (RootScheduled
                (FocusedRetryHead False (request eligibility target) offered) [])
    runRootEntry target entry
  where
    directRoot exposed = do
        lift (beginCandidateObservation observation)
        available <- Except.ExceptT (availableProofs environment contextId context)
        direct <- lift (startExactAttempt ConvertExactCandidates exposed available >>= driveExact exposed)
        case direct of
            ExactPending{} -> continue available exposed [FocusedExactContinuation direct] Nothing False
            ExactFound proof@(ObviousProof built dependencies) remaining -> do
                accepted <- Except.ExceptT (checkProofRequirement observation requirement proof)
                if accepted
                    then do
                        converted <- Except.ExceptT (convertIfDifferent context built target)
                        pure (RootComplete (Right (ObviousProof converted dependencies)))
                    else do
                        lift (State.modify' (\state -> state
                            {searchRootAnyCertificate = searchRootAnyCertificate state <|> Just proof}))
                        continue available exposed [FocusedExactContinuation remaining] Nothing True
            ExactFinished Nothing -> continue available exposed [] Nothing False
            ExactFinished (Just failure)
                | isTerminalFocusedFailure failure -> Except.throwE failure
                | otherwise -> continue available exposed [] (Just failure) False
    SearchEnvironment _typing rootImports _hypotheses _views = environment
    observation = ObserveRoot (RootGoalView (RootGoalViewId 0) CandidateOriginalGoalView)
    request eligibility goal = FocusedRequest observation requirement environment Set.empty
        contextId context goal eligibility AllPermittedSources Nothing SuppliedEvidence Nothing CompletionAllowed
    failed = failedRootEntry requirement environment contextId context target
    driveExact exposed = \case
        pending@(ExactPending ExactRetry{}) -> pure pending
        found@ExactFound{} -> pure found
        finished@ExactFinished{} -> pure finished
        ExactPending cursor -> advanceExactAttempt observation context exposed cursor >>= driveExact exposed
    continue available exposed pending firstFailure rejected = do
        eligibility <- Except.ExceptT (admitGroundFamily contextId context target rootImports)
        let original = request eligibility target
        lift (activateFocusedRequest original { focusedTarget = exposed }) >>= \case
            Left failure -> lift (failed (Just eligibility) failure)
            Right activated -> do
                for_ (focusedObligation activated) \identifier -> do
                    unrestricted <- State.gets searchRootAnyCertificate
                    for_ unrestricted (Except.ExceptT . retainFocusedCertificate identifier)
                policy <- State.gets (policyWitnesses . searchPolicy)
                existentialPolicy <- State.gets (policyExistentials . searchPolicy)
                let input = FocusedRulesInput activated available True
                pure (RootScheduled
                    (FocusedSearch input (pending <> afterExactFocusedRules policy existentialPolicy input) firstFailure rejected)
                    [AfterFocusedRequest original])

data RootEntry global
    = RootComplete !(Either (ObviousFailure global) (ObviousProof global))
    | RootScheduled !(FocusedAction global) ![FocusedContinuation global]

runRootEntry
    :: Ord global => ScopedCheckedCore global -> RootEntry global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ObviousProof global))
runRootEntry target = \case
    RootComplete result -> pure result
    RootScheduled action frames -> focusedAttemptResult target <$> runFocusedMachine action frames

-- A failed direct prefix may leave the independent ground allowance available.
-- No obligation, source cursor or query existed yet; schedule that remaining
-- operation under the same request owner, retaining any already admitted family.
failedRootEntry
    :: ProofRequirement -> SearchEnvironment global -> FocusedContextId
    -> KernelProof.ProofContext global -> ScopedCheckedCore global
    -> Maybe GroundEligibility -> ObviousFailure global
    -> State (ObviousSearchState global) (RootEntry global)
failedRootEntry requirement environment contextId context target existing failure = do
    State.modify' (\state -> state {searchRootFocusedOutcome = Just (focusedTierOutcome (Left failure))})
    view <- State.gets (fromMaybe ObviousFocusedViewUnavailable . searchRootFocusedGoalView)
    if not (allowsGroundAfterPreparation view failure)
        then pure (RootComplete (Left failure))
        else do
            let SearchEnvironment _typing imports _hypotheses _views = environment
            admitted <- maybe (admitFamilyWith GroundScopeWork contextId context target imports Seq.empty) (pure . Right) existing
            case admitted of
                Left blocked -> do
                    recordGroundAdmissionFailure blocked
                    pure (RootComplete (Left (preferObviousFailure failure blocked)))
                Right eligibility -> pure (RootScheduled
                    (FocusedGround (FocusedRequest
                        (ObserveRoot (RootGoalView (RootGoalViewId 0) CandidateOriginalGoalView))
                        requirement environment Set.empty contextId context target eligibility AllPermittedSources Nothing SuppliedEvidence Nothing CompletionAllowed) Nothing)
                    [AfterGroundEntryFailure failure])

preferObviousFailure :: ObviousFailure global -> ObviousFailure global -> ObviousFailure global
preferObviousFailure firstFailure following
    | isFocusedInfrastructureFailure following = following
    | otherwise = maybe firstFailure snd
        (rememberFocusedFailure 1 (Just (0, firstFailure)) (AttemptFailed following))

recordGroundAdmissionFailure :: ObviousFailure global -> State (ObviousSearchState global) ()
recordGroundAdmissionFailure failure = State.modify' (\state -> state
    { searchGroundAdmissionFailure = Just (maybe failure (`preferObviousFailure` failure)
        (searchGroundAdmissionFailure state)) })

startObviousRoot
    :: Ord global => ProofRequirement -> SearchEnvironment global
    -> KernelProof.ProofContext global -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ObviousProof global))
startObviousRoot requirement environment context target = do
    work <- getFocusedWorkBudget
    when (work == 0) (State.modify' (\state -> state
        { searchRootFocusedOutcome = Just (ObviousTierResourceExhausted ObviousFocusedWorkLimit) }))
    let owner = if work == 0 then GroundScopeWork else FocusedScopeWork
    admitted <- admitContextWith owner FocusedRootScope context
    case admitted of
        Left failure | work == 0 -> do
            recordGroundAdmissionFailure failure
            pure (Left (preferObviousFailure (ObviousResourceExhausted ObviousFocusedWorkLimit) failure))
        Left failure -> pure (Left failure)
        Right contextId -> do
            root <- runCountedKernel (KernelProof.countedAdmitScopedTerm context target)
            case root of
                Left failure -> failedRootEntry requirement environment contextId context target Nothing failure
                    >>= runRootEntry target
                Right checked -> proveRoot requirement environment contextId context checked

recordRootFocusedOutcome
    :: FocusedRequest global -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) ()
recordRootFocusedOutcome request result = case focusedObservation request of
    ObserveRoot (RootGoalView (RootGoalViewId 0) _view) -> State.modify' (\state -> state
        {searchRootFocusedOutcome = Just (focusedTierOutcome result)})
    _ -> pure ()

focusedAttemptResult
    :: ScopedCheckedCore global
    -> Attempt global
    -> Either (ObviousFailure global) (ObviousProof global)
focusedAttemptResult target = \case
    AttemptSucceeded proof -> Right proof
    AttemptFailed failure -> Left failure
    AttemptNotApplicable -> Left (ObviousAntecedentUnavailable target)

advanceFocused
    :: Ord global
    => FocusedAction global
    -> [FocusedContinuation global]
    -> State (ObviousSearchState global)
        (Either (Attempt global) (FocusedAction global, [FocusedContinuation global]))
advanceFocused action continuations = case action of
    FocusedPointwiseSupport outer child binders -> nextWith
        (FocusedPhaseEntry (pointwiseEvidencePhase child) SearchDependency child {focusedRequirement = MustUseCanonicalDefinition})
        (AfterPointwise outer child binders)
    FocusedArgumentEntry request
        | focusedCompletionPermission request == CompletionSuppressed -> returned AttemptNotApplicable
        | Just (TyArrow{}, _, _) <- splitScopedEquality (focusedTarget request) -> endpointProducerFor request >>= \case
            Left failure -> returned (AttemptFailed failure)
            Right EvidenceOnly -> returned AttemptNotApplicable
            Right SuppliedEquations -> next (FocusedPhaseEntry ArgumentCompletion SearchDependency request
                {focusedCompletionPermission = CompletionSuppressed, focusedDirectEvidence = EstablishedEvidence})
        | otherwise -> returned AttemptNotApplicable
    FocusedBooleanSecond request left right forward backward -> nextWith
        (FocusedBooleanDirection backward)
        (AfterBooleanSecond request left right forward)
    -- Retain supplied directions before opening their assumptions. General
    -- whole-direction search remains a fallback to ordinary introduction,
    -- rather than another eager copy of the body's expensive search.
    FocusedBooleanDirection request -> nextWith (FocusedDirectPremise request) (AfterBooleanDirect request)
    FocusedBooleanIntroduce request -> do
        introduction <- startIntroduction (focusedRequirement request) (focusedContextId request)
            (focusedContext request) (focusedTarget request)
        nextWith (FocusedIntroduce request introduction) (AfterBooleanIntroduction request)
    FocusedBooleanSupport{} -> schedulerOnly
    FocusedBooleanBegin request -> case splitScopedEquality (focusedTarget request) of
        Just (TyProp, left, right) -> do
            prepared <- Except.runExceptT do
                forward <- implication left right
                backward <- implication right left
                entry <- Except.ExceptT (admitDirectionalEntry request left right forward backward)
                let parent = request {focusedDirectionalEntry = entry}
                    child target = parent {focusedTarget = target, focusedObligation = Nothing,
                        focusedEligibility = structuralGroundEligibility (focusedEligibility request),
                        focusedRequirement = AnyObviousProof}
                pure (parent, child forward, child backward)
            case prepared of
                Left failure -> returned (AttemptFailed failure)
                Right (parent, forward, backward) -> nextWith
                    (FocusedBooleanDirection forward)
                    (AfterBooleanFirst parent left right backward)
        _ -> returned AttemptNotApplicable
    FocusedBooleanBuild request dependencies step following -> case step of
        BooleanEqualityFinished (Left failure) -> returned (AttemptFailed failure)
        BooleanEqualityFinished (Right proof) -> next (FocusedPublish request (ObviousProof proof dependencies) following)
        _ -> advanceBooleanEqualityProof (focusedContext request) step
            >>= next . (\progress -> FocusedBooleanBuild request dependencies progress following)
    FocusedEqualityEntry{} -> schedulerOnly
    FocusedPhaseEntry{} -> schedulerOnly
    FocusedPointwiseProbe{} -> schedulerOnly
    FocusedPointwiseLeaf{} -> schedulerOnly
    FocusedPointwiseOpen outer prefix binders -> openPointwisePrefix outer prefix >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right Nothing -> returned AttemptNotApplicable
        Right (Just (child, binder, arrow)) -> next (if arrow
            then FocusedPointwiseProbe outer child (binder : binders)
            else FocusedPointwiseLeaf outer child (binder : binders))
    FocusedPointwiseBuild outer child dependencies step following -> case step of
        FunctionEqualityFinished (Left failure) -> returned (AttemptFailed failure)
        FunctionEqualityFinished (Right proof) -> next (FocusedPublish outer (ObviousProof proof dependencies) following)
        _ -> advanceFunctionEqualityProof (focusedEnvironment outer) (focusedContext outer)
            (focusedContext child) step >>= next . (\progress -> FocusedPointwiseBuild outer child dependencies progress following)
    FocusedPrefixBegin request -> nextWith (FocusedDirectBody request) (AfterPrefixDirect request)
    FocusedPrefixTheorems request | focusedCompletionPermission request == CompletionSuppressed ->
        next (FocusedEndpointBegin request)
    FocusedPrefixTheorems request -> availableFor request >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right sources -> startTheoremSearch (focusedTarget request) sources
            >>= next . FocusedTheorems (FocusedRulesInput request sources False) False
    FocusedPublish request proof following -> foundCandidate request proof following
    -- Only a matched supplied-source application starts this quantum. Its
    -- direct fragment reuses the ordinary worker and retains its proof prefix.
    -- A miss requiring recursion or a blocked probe gives up completion priority;
    -- exhausting the finite quantum returns the same cursor to ordinary preparation.
    FocusedDirectQuantum remaining current -> do
      shared <- case current of
          FocusedDirectPremise request ->
              (&& focusedDirectEvidence request == SuppliedEvidence) <$> State.gets searchCanonicalRequest
          _ -> pure False
      if shared then next current else advanceFocused current continuations >>= \case
        Left result -> pure (Left result)
        Right (following, frames) -> pure (Right
            (case following of
                FocusedDirectQuantum offered nextAction
                    | remaining > 1 -> FocusedDirectQuantum (min (remaining - 1) offered) nextAction
                    | otherwise -> nextAction
                _ | remaining > 1 && continuesDirectQuantum following -> FocusedDirectQuantum (remaining - 1) following
                  | otherwise -> following, frames))
    FocusedEndpointRequest request -> enterEndpointOwner request >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right (owned, identifier, reversed) -> nextWith
            (FocusedDemandCertificate EndpointSearch owned identifier)
            (AfterEndpointDirection (focusedContext request) reversed)
    FocusedEndpointBegin request -> endpointTheoremSources request >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right selected -> startTheoremSearch (focusedTarget request) selected
            >>= next . FocusedEndpointSearch request
    FocusedEndpointSearch request step -> case step of
        TheoremFinished result -> returned result
        TheoremPending cursor -> advanceTheoremSearch (focusedEnvironment request) (focusedContext request) cursor
            >>= next . FocusedEndpointSearch request
        TheoremBlocked{} -> returned (AttemptFailed (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch "endpoint discovery lost its scheduled alternative")))
        TheoremApply prepared continuation -> nextWith
            (FocusedEndpointSource request prepared False)
            (AfterEndpointSource request prepared False continuation)
    FocusedEndpointSource request prepared@(PreparedTheoremSource _ (CompiledTheoremSpine _ result _)) reversed ->
        case scopedCoreTerm (Template.compiledTemplateTerm result) of
            CEq{} -> do
                target <- if reversed then reverseEndpointTarget request else pure (Right (focusedTarget request))
                case target of
                    Left failure -> returned (AttemptFailed failure)
                    Right equation -> do
                        let direction = if reversed then FocusedEqualityReverse else FocusedEqualityForward
                        started <- startApplicationWithParameters (EndpointParameters direction) False (focusedObservation request)
                            (focusedRequirement request) (focusedEnvironment request) (focusedContextId request)
                            (focusedContext request) equation prepared
                        case started of
                            ApplicationComplete attempt -> returned attempt
                            ApplicationMatching candidate input pending -> next (FocusedMatchApplication request candidate input pending)
                            ApplicationMatched candidate progress following -> nextWith
                                (FocusedDirectQuantum 512 (FocusedApply request following))
                                (AfterMatchedTheorem candidate progress)
            _ -> returned AttemptNotApplicable
    FocusedEndpointSourceWithContinuation request source following -> nextWith
        (FocusedEndpointSource request source True) (AfterEndpointSource request source True following)
    FocusedEndpointReverse context effort selected@(ObviousProof proof _) ->
        runKernelPreparation effort (KernelProof.countedEqualityReverseProof context proof) >>= \case
            NeedsMoreEffort offered -> next (FocusedEndpointReverse context (FullPreparation offered) selected)
            PreparationFinished (Left failure) -> returned (AttemptFailed failure)
            PreparationFinished (Right reversed) -> returned (AttemptSucceeded (deriveCandidateProof reversed selected))
    FocusedEndpointSupport request effort selected@(ObviousProof proof _) remaining ->
        runKernelPreparation effort (KernelProof.countedEqualityReverseProof
            (focusedContext request) proof) >>= \case
            NeedsMoreEffort offered -> next (FocusedEndpointSupport request (FullPreparation offered) selected remaining)
            PreparationFinished (Left failure) -> returned (AttemptFailed failure)
            PreparationFinished (Right reversed) -> foundCandidate request
                (deriveCandidateProof reversed selected) (FocusedApply request remaining)
    FocusedEndpointGuard request following ->
        let query = request {focusedDirectEvidence = EstablishedEvidence, focusedObligation = Nothing,
                focusedCompletionPermission = CompletionSuppressed}
        in nextWith (FocusedDirectPremise query) (AfterEndpointGuard query following)
    FocusedExistingEvidence{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "existing evidence lookup entered the scalar worker")))
    FocusedAwaitEvidence{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an evidence subscription entered the scalar worker")))
    FocusedStart request -> prepareRequest False request
    FocusedPreparedProbe request -> prepareRequest True request
    FocusedRetryHead direct request offered -> do
        pool <- getConversionPool
        if Conversion.conversionPoolAmount pool <= Conversion.conversionLimitAmount offered
            then returned (AttemptFailed (ObviousResourceExhausted ObviousConversionPoolLimit))
            else finishPreparedTargetHead (focusedObservation request) (focusedEnvironment request)
                    (focusedTarget request) >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right target -> next (FocusedPreparedTarget direct request target)
    FocusedPreparedTarget direct request target
        | direct -> next (FocusedDirectPremise request { focusedTarget = target })
        | otherwise -> beginPreparedFocusedRequest request target >>= \case
            Left failure -> preparationFailure False request failure
            Right input -> do
                policy <- State.gets (policyWitnesses . searchPolicy)
                existentialPolicy <- State.gets (policyExistentials . searchPolicy)
                nextWith (FocusedSearch input (ordinaryFocusedRules policy existentialPolicy input) Nothing False)
                    (AfterFocusedRequest request)
    FocusedDirectPremise request -> advanceFocused (FocusedDirectBody request {focusedObligation = Nothing}) continuations
    FocusedDirectBody request -> availableFor request >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right available -> nextWith
            (FocusedDirectRules (FocusedRulesInput request available False)
                (directFocusedRules (focusedTarget request)) Nothing False)
            (AfterDirectPremise (focusedTarget request))
    FocusedSearch{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an obligation choice entered the scalar worker")))
    FocusedProduce{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an obligation producer entered the scalar worker")))
    FocusedAwaitGround{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a ground-input waiter entered the scalar worker")))
    FocusedGroundOpportunity{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a fact activation lost its discovery opportunity")))
    FocusedGround request Nothing -> Except.runExceptT (startFocusedGround request) >>= \case
        Left failure -> do
            recordGroundAdmissionFailure failure
            returned (AttemptFailed failure)
        Right GroundStartPending -> next (FocusedGround request Nothing)
        Right GroundStartUnavailable -> returned AttemptNotApplicable
        Right (GroundStarted query) -> next (FocusedGround request (Just query))
    FocusedGround request (Just query) -> Except.runExceptT (advanceFocusedGround request query) >>= \case
        Left failure -> returned (AttemptFailed failure)
        Right GroundQueryPending -> next (FocusedGround request (Just query))
        Right (GroundQueryBlocked _statistics failure) -> next (FocusedAwaitGround request query failure)
        Right (GroundQueryFinished _statistics result) -> case result of
            Left failure -> returned (AttemptFailed (mapRefutationFailure failure))
            Right (OwnedGroundCertificate built uses source) ->
                -- The shared premise's consumer owns its requirement failure.
                -- Publishing another ordinary ground proof adds evidence,
                -- not a second rejected auxiliary candidate.
                let observed = case (focusedObligation request, focusedObservation request) of
                        (Just _, SuppressAuxiliary _) -> request {focusedObservation = CollectSharedEvidence}
                        _ -> request
                in foundCandidate observed ((ObviousProof built (CandidateDependencies (kernelSourceImportUses uses) source))
                    {obviousProofCertification = Just (focusedContextId request, uses)})
                    (FocusedGround request (Just query))
    FocusedRules _input [] firstFailure rejected ->
        returned (if rejected then AttemptFailed ObviousCanonicalDefinitionEvidenceRequired
            else maybe AttemptNotApplicable AttemptFailed firstFailure)
    FocusedRules input (rule : rest) firstFailure rejected ->
        nextWith (FocusedRunRule input rule) (AfterFocusedRule input rest firstFailure rejected)
    FocusedDirectRules input [] firstFailure rejected ->
        next (FocusedRules input [] firstFailure rejected)
    FocusedDirectRules input (rule : rest) firstFailure rejected ->
        nextWith (FocusedRunRule input rule) (AfterDirectRule input rest firstFailure rejected)
    FocusedRunRule input rule -> enterFocusedRule input rule >>= next
    FocusedExactCandidates request step -> case step of
        ExactFinished failure -> returned (maybe AttemptNotApplicable AttemptFailed failure)
        ExactFound proof remaining -> foundCandidate request proof (FocusedExactCandidates request remaining)
        ExactPending cursor -> advanceExactAttempt (focusedObservation request)
            (focusedContext request) (focusedTarget request) cursor
                >>= next . FocusedExactCandidates request
    FocusedProjectionCandidates request policy step -> case step of
        ProjectionFinished result -> returned result
        ProjectionFound proof remaining -> foundCandidate request proof (FocusedProjectionCandidates request policy remaining)
        ProjectionPending cursor -> advanceProjectionAttempt policy (focusedObservation request)
            (focusedEnvironment request) (focusedContext request) (focusedTarget request) cursor
                >>= next . FocusedProjectionCandidates request policy
    FocusedFalsumCandidates request available step -> case step of
        FalsumFinished result -> returned result
        FalsumFound proof remaining -> foundCandidate request proof (FocusedFalsumCandidates request available remaining)
        FalsumPending cursor -> advanceFalsum (focusedEnvironment request)
            (focusedContext request) (focusedTarget request) available cursor
                >>= next . FocusedFalsumCandidates request available
    FocusedEqualities request policy step -> case step of
        EqualityFinished result -> returned result
        EqualityFound proof remaining -> foundCandidate request proof (FocusedEqualities request policy remaining)
        EqualityPending cursor@(EqualityTarget _ _ (EqualityProofDemand _ demanded operands _)) ->
            requestEndpointProof request demanded operands >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right child -> nextWith (FocusedEndpointRequest child) (AfterEndpointEquality request policy cursor)
        EqualityPending cursor@(EqualityTarget _ _ (EqualityCompletionDemand _ demanded operands _)) ->
            requestEndpointProof request demanded operands >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right child -> nextWith (FocusedArgumentEntry child) (AfterArgumentEquality request policy cursor)
        EqualityPending cursor -> endpointProducerFor request >>= \case
            Left failure -> returned (AttemptFailed failure)
            Right producer -> advanceEquality producer policy (focusedRequirement request)
                (focusedEnvironment request) (focusedContext request) cursor
                    >>= next . FocusedEqualities request policy
    FocusedIntroduce request step -> case step of
        IntroductionFinished result -> returned result
        IntroductionNeedsSupport proof left right -> retainConjunction GeneralSearch request proof left right
        IntroductionAlternatives{} -> returned (AttemptFailed (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch "a disjunction choice entered the scalar worker")))
        IntroductionChild observation requirement scope target continuation ->
            structuralChildRequest request scope continuation observation requirement target >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right child -> nextWith (FocusedStart child)
                    (AfterFocusedIntroduction request child continuation)
    FocusedWitnesses request available step -> case step of
        WitnessFinished result -> returned result
        WitnessPending cursor -> advanceWitnessSearch request available cursor
            >>= next . FocusedWitnesses request available
        WitnessOffer{} -> returned (AttemptFailed (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch "a witness choice entered the scalar worker")))
    FocusedExistentials request sources -> case sources of
        [] -> returned AttemptNotApplicable
        source : remaining -> do
            entered <- consumeSearchStep
            if not entered then returned (AttemptFailed (ObviousResourceExhausted ObviousFocusedWorkLimit))
                else case openScopedExists (obviousProofStatement source) of
                    Nothing -> next (FocusedExistentials request remaining)
                    Just (binderType, body) -> openSuppliedExistential request source binderType body >>= \case
                        Left failure -> returned (AttemptFailed failure)
                        Right Nothing -> next (FocusedExistentials request remaining)
                        Right (Just child) -> next (FocusedExistentialOffer request child source binderType
                            (scopedCoreTerm body) remaining)
    FocusedExistentialOffer{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an existential choice entered the scalar worker")))
    FocusedConjoin request step -> case step of
        ConjunctionFinished result -> returned result
        ConjunctionNeedsSupport proof left right -> retainConjunction DirectEvidence request proof left right
        ConjunctionChild requirement target continuation ->
            let child = request { focusedRequirement = requirement, focusedTarget = target
                    , focusedEligibility = structuralGroundEligibility (focusedEligibility request) }
                following = AfterFocusedConjunction request target continuation
            in case focusedDirectEvidence request of
                SuppliedEvidence -> nextWith (FocusedDirectPremise child) following
                EstablishedEvidence -> next (FocusedEndpointGuard child following)
    FocusedConjunctionSupport{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a support choice entered the scalar worker")))
    FocusedDemandCertificate{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a certificate demand entered the scalar worker")))
    FocusedSupportDependency request proof continuation -> case obviousProofObligation proof of
        -- A direct disjunction probe has not entered recursive search yet.
        -- Its ordinary result is published before starting that retained route.
        Nothing -> next (FocusedDeferredPremise request
            {focusedRequirement = MustUseCanonicalDefinition} continuation Nothing)
        Just identifier -> nextWith
            (FocusedDemandCertificate GeneralSearch request {focusedRequirement = MustUseCanonicalDefinition} identifier) continuation
    FocusedTheorems{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a theorem cursor entered the scalar worker")))
    FocusedMatchApplication request candidate input step -> case step of
        TheoremMatchFinished result -> finishApplicationMatch candidate input result >>= \case
            Left rejected -> returned rejected
            Right (progress, following) -> nextWith
                (FocusedDirectQuantum 512 (FocusedApply request following))
                (AfterMatchedTheorem candidate progress)
        _ -> advanceTheoremMatch (focusedEnvironment request) step >>= next
            . FocusedMatchApplication request candidate input
    FocusedApply request step -> case step of
        ApplicationFinished result -> returned result
        ApplicationFound proof remaining
            | ApplicationSupport (ApplicationInput (EndpointParameters FocusedEqualityReverse) _ _ _ _ _ _ _ _ _) _ _ <- remaining ->
                -- The ordinary support slot belongs to the owner's orientation,
                -- even while this source's written equation is reversed.
                next (FocusedEndpointSupport request SmallPreparation proof remaining)
            | otherwise -> foundCandidate request proof (FocusedApply request remaining)
        ApplicationSupport input recipes frames -> next (FocusedApplicationSupport request input recipes frames)
        ApplicationPending input task frames ->
            advanceApplication (focusedEnvironment request) input task frames
                >>= next . FocusedApply request
        ApplicationChild input recursive target substitutions continuation frames -> do
            premisePolicy <- State.gets (policyPremiseQueries . searchPolicy)
            extensionalityPolicy <- State.gets (policyExtensionality . searchPolicy)
            let child = request
                    { focusedObservation = SuppressAuxiliary AuxiliaryTheoremAntecedent
                    , focusedEligibility = if recursive then theoremPremiseEligibility premisePolicy request else FocusedOnly
                    , focusedRequirement = AnyObviousProof
                    , focusedTarget = target
                    }
                ordinary = AfterApplicationChild request input target substitutions continuation frames
                following = case continuation of
                    ContinueTheoremPremises _allowSearch _selected steps ->
                        extensionalityFallback extensionalityPolicy recursive request input target steps
                            AnyObviousProof ordinary
                    _ -> ordinary
            case input of
                ApplicationInput EndpointParameters{} _ _ _ _ _ _ _ _ _ ->
                    next (FocusedEndpointGuard child following)
                ApplicationInput PrefixParameters _ _ _ _ _ _ _ _ _ ->
                    nextWith (FocusedDirectBody child {focusedObligation = Nothing}) following
                _ -> nextWith (FocusedDirectPremise child)
                    (if recursive then AfterDirectProbe child following else following)
    FocusedExtensionality request source direction target requirement earlier following -> do
        opened <- openMembershipBranch request source direction target requirement
        case opened of
            Left failure -> nextWith (FocusedReturn (AttemptFailed failure)) following
            Right Nothing -> nextWith (FocusedReturn earlier) following
            Right (Just branch@(MembershipBranch child _ _)) ->
                case focusedObligation child of
                    Nothing -> nextWith (FocusedReturn (AttemptFailed (ObviousIntegrityFailure
                        (KernelProof.ProofStructuralCompositionMismatch
                            "a membership branch lost its retained obligation")))) following
                    Just identifier -> nextWith (FocusedDemandCertificate GeneralSearch child identifier)
                        (AfterExtensionalityDischarge request branch following)
    FocusedApplicationSupport{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "application support entered the scalar worker")))
    FocusedDeferredPremise request continuation _blocked -> do
        canonical <- State.gets searchCanonicalRequest
        nextWith (case (canonical, focusedObligation request) of
            (True, Just identifier) -> FocusedDemandCertificate GeneralSearch request identifier
            _ -> FocusedStart request) continuation
    FocusedTransport request step -> case step of
        TransportFinished result -> returned result
        TransportPending cursor@(TransportEquality _ _ _ _ (EqualityProofDemand _ demanded operands _)) ->
            requestEndpointProof request demanded operands >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right child -> nextWith (FocusedEndpointRequest child) (AfterEndpointTransport request cursor)
        TransportPending cursor@(TransportEquality _ _ _ _ (EqualityCompletionDemand _ demanded operands _)) ->
            requestEndpointProof request demanded operands >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right child -> nextWith (FocusedArgumentEntry child) (AfterArgumentTransport request cursor)
        TransportPending cursor -> endpointProducerFor request >>= \case
            Left failure -> returned (AttemptFailed failure)
            Right producer -> advanceTransport producer (focusedObservation request)
                (focusedRequirement request) (focusedEnvironment request)
                (focusedContext request) (focusedTarget request) cursor
                    >>= next . FocusedTransport request
        TransportFound proof following -> foundCandidate request proof (FocusedTransport request following)
        TransportOffer{} -> returned (AttemptFailed (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch "a transport source offer entered the scalar worker")))
        TransportChild target continuation ->
            let child = request
                    { focusedObservation = SuppressAuxiliary AuxiliaryTransportPremise
                    , focusedEligibility = FocusedOnly, focusedRequirement = AnyObviousProof
                    , focusedTarget = target }
            in nextWith (FocusedDirectPremise child)
                (AfterDirectProbe child (AfterFocusedTransport request target continuation))
        TransportSupport proof continuation ->
            next (FocusedSupportDependency request
                { focusedObservation = SuppressAuxiliary AuxiliaryTransportPremise
                , focusedEligibility = FocusedOnly, focusedTarget = obviousProofStatement proof }
                proof (AfterFocusedTransport request (obviousProofStatement proof) continuation))
    FocusedGoalViews request step -> case step of
        GoalDefinitionFinished result -> returned result
        GoalDefinitionPending cursor -> advanceGoalDefinition (focusedObservation request)
            (focusedEnvironment request) (focusedActive request)
            (focusedContext request) (focusedTarget request) cursor
                >>= next . FocusedGoalViews request
        GoalDefinitionChild observation target continuation -> selectedGoalFamily request target >>= \case
            Left failure -> readyGoalView request <$> resumeGoalDefinition (focusedActive request) continuation (Left failure) >>= next
            Right eligibility ->
                let child = request
                        { focusedObservation = observation
                        , focusedEligibility = eligibility
                        , focusedRequirement = AnyObviousProof
                        , focusedTarget = target }
                in nextWith (FocusedPreparedProbe child)
                    (AfterDirectProbe child (AfterFocusedGoalView request target continuation))
    FocusedFactViews{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "a fact producer entered the scalar worker")))
    FocusedUseFact (FocusedRulesInput request roots _continue) direct exposed
        -- Keep the selected source, but let its premises use ordinary scoped
        -- evidence (for example, membership transported across a local alias).
        | direct -> next (startRules (FocusedRulesInput request [exposed] False)
            ([FocusedExact DeferExactCandidateConversion, FocusedProjection DeferExactCandidateConversion]
                <> [FocusedStructuralEquality (focusedTarget request)
                    | isJust (splitScopedEquality (focusedTarget request))]
                <> [FocusedTheorem]))
        -- General fact rules are entered only with the prepared request target.
        -- Reuse it: residualizing that same head here repeated preparation before
        -- releasing discovery. Each candidate worker owns any later conversion.
        | otherwise -> next (startRules (FocusedRulesInput request (exposed : roots) False)
            [ FocusedExact ConvertExactCandidates, FocusedProjection ConvertExactCandidates
            , FocusedEquality (focusedTarget request), FocusedFalsum, FocusedTheorem, FocusedTransportRule ])
    FocusedConvertRequest request dependencies step -> case step of
        HeadProofFinished result -> returned (fromObvious dependencies result)
        _ -> advanceHeadProof (focusedEnvironment request) (focusedContext request) step
            >>= next . FocusedConvertRequest request dependencies
    FocusedReturn result
        | AfterBooleanBodyDirect original input rules firstFailure rejected : rest <- continuations ->
            case result of
                AttemptSucceeded{} -> pure (Right (FocusedReturn result,
                    AfterFocusedRequest original : AfterFocusedSearch original : rest))
                AttemptFailed failure | isFocusedInfrastructureFailure failure -> pure (Right (FocusedReturn result, rest))
                _ -> pure (Right (FocusedGround original Nothing,
                    AfterBooleanBodyGround original input rules firstFailure rejected : rest))
        | AfterBooleanBodyGround original input rules firstFailure rejected : rest <- continuations ->
            case result of
                AttemptSucceeded{} -> pure (Right (FocusedReturn result, rest))
                AttemptFailed failure | isFocusedInfrastructureFailure failure -> pure (Right (FocusedReturn result, rest))
                _ -> pure (Right (FocusedRules input rules firstFailure rejected,
                    [AfterFocusedRequest original, AfterFocusedSearch original]
                        <> [AfterGroundEntryFailure failure | AttemptFailed failure <- [result]] <> rest))
    FocusedReturn result -> case continuations of
        [] -> pure (Left result)
        continuation : rest -> resumeFocused continuation result >>= \nextAction ->
            pure (Right (nextAction, rest))
  where
    next nextAction = pure (Right (nextAction, continuations))
    nextWith nextAction continuation = pure (Right (nextAction, continuation : continuations))
    returned = next . FocusedReturn
    schedulerOnly = returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an equality phase entered the scalar worker")))
    implication left right = runScopedCore (\work -> countedImplyScopedCore work left right)
        >>= maybe (scopeIntegrity "Boolean direction operands disagree") pure

    foundCandidate request proof remaining
        | satisfiesRequirement (focusedRequirement request) proof = returned (AttemptSucceeded proof)
        | otherwise = do
            retained <- Except.runExceptT do
                _ <- Except.ExceptT (checkProofRequirement (focusedObservation request)
                    (focusedRequirement request) proof)
                for_ (focusedObligation request) (Except.ExceptT . (`retainFocusedCertificate` proof))
            case retained of
                Left failure -> returned (AttemptFailed failure)
                Right () -> next remaining

    retainConjunction phase request proof left right = do
        retained <- maybe (pure (Right ())) (`retainFocusedCertificate` proof) (focusedObligation request)
        case retained of
            Left failure -> returned (AttemptFailed failure)
            Right () -> next (FocusedConjunctionSupport phase request left right)

    prepareRequest direct request = prepareFocusedTargetSmall (focusedObservation request)
            (focusedEnvironment request) (focusedTarget request) >>= \case
        NeedsMoreEffort offered -> next (FocusedRetryHead direct request offered)
        PreparationFinished (Left failure) -> preparationFailure direct request failure
        PreparationFinished (Right target) -> next (FocusedPreparedTarget direct request target)

    preparationFailure direct request failure
        | not direct, eligibleFocusedGround request,
            ObviousResourceExhausted ObviousFocusedWorkLimit <- failure = do
                recordRootFocusedOutcome request (Left failure)
                nextWith (FocusedGround request Nothing) (AfterGroundEntryFailure failure)
        | otherwise = returned (AttemptFailed failure)

    availableFor request = availableProofs (focusedEnvironment request)
        (focusedContextId request) (focusedContext request)

continuesDirectQuantum :: FocusedAction global -> Bool
continuesDirectQuantum = \case
    FocusedArgumentEntry{} -> False
    FocusedBooleanSupport{} -> False
    FocusedEqualityEntry{} -> False
    FocusedPhaseEntry{} -> False
    FocusedPointwiseProbe{} -> False
    FocusedPointwiseLeaf{} -> False
    FocusedPublish{} -> False
    FocusedEndpointSearch _ TheoremBlocked{} -> False
    FocusedEndpointSearch _ (TheoremPending (TheoremPreparing _ _ _ source)) -> not (theoremSourceIsDeferred source)
    FocusedExistingEvidence{} -> False
    FocusedAwaitEvidence{} -> False
    -- Choices and source producers must return to their scheduler owner.
    FocusedSearch{} -> False
    FocusedConjunctionSupport{} -> False
    FocusedApplicationSupport{} -> False
    FocusedDemandCertificate{} -> False
    FocusedGround{} -> False
    FocusedAwaitGround{} -> False
    FocusedGroundOpportunity{} -> False
    FocusedRules _ (_ : _ : _) _ _ -> False
    FocusedTheorems{} -> False
    FocusedIntroduce _ IntroductionAlternatives{} -> False
    FocusedWitnesses{} -> False
    FocusedExistentials{} -> False
    FocusedExistentialOffer{} -> False
    FocusedStart{} -> False
    FocusedConvertRequest _ _ step -> not (headProofIsDeferred step)
    FocusedDeferredPremise{} -> False
    FocusedRetryHead{} -> False
    FocusedExactCandidates _ (ExactPending ExactRetry{}) -> False
    FocusedGoalViews _ (GoalDefinitionPending (GoalDefinitionBuild _ step)) -> not (viewProofIsDeferred step)
    FocusedTransport _ TransportOffer{} -> False
    FocusedTransport _ (TransportPending cursor) -> not (transportIsDeferred cursor)
    FocusedProjectionCandidates _ _ step -> not (projectionIsDeferred step)
    FocusedEqualities _ _ step -> not (equalityIsDeferred step)
    FocusedApply _ (ApplicationPending _ task _) -> not (applicationIsDeferred task)
    FocusedReturn (AttemptFailed failure) -> not (isTerminalFocusedFailure failure)
    _ -> True

eligibleFocusedGround :: FocusedRequest global -> Bool
eligibleFocusedGround request = focusedSourcePolicy request == AllPermittedSources
    && case focusedEligibility request of
        FocusedOnly -> False
        SeedEligible{} -> True
        ExistingFamily{} -> True

-- Only a recognized final premise can reach the extra scope permission, and
-- only after its ordinary restricted search. A guard with the same syntax
-- does not qualify: its position in the retained spine is authoritative.
extensionalityFallback
    :: ExtensionalityPolicy -> Bool -> FocusedRequest global -> ApplicationInput global
    -> ScopedCheckedCore global -> [TheoremSpineStep global] -> ProofRequirement
    -> FocusedContinuation global -> FocusedContinuation global
extensionalityFallback policy recursive request input target remaining requirement following
    | policy == ExtensionalityDisabled || not recursive || not (permitsSeededScopeOpening request) = following
    | otherwise = case input of
        ApplicationInput _ _ _ _ (CompiledTheoremSpine _ _ True) _ _ _ equality (Just source)
            | CEq TySet _ _ <- scopedCoreTerm equality -> case remaining of
                [Elimination.Apply _] -> offer source ForwardMembership
                [] -> offer source ReverseMembership
                _ -> following
        _ -> following
  where
    offer source direction = AfterExtensionalityFallback request source direction target requirement following

-- The two bare equality parameters are fixed uniquely by the selected goal.
-- Its nominal obligation plus the stable theorem-view key therefore identifies
-- the concrete application without recursive terms as map keys. Directions
-- keep separate scopes but share one request-wide debit, including failed setup.
openMembershipBranch
    :: Ord global
    => FocusedRequest global -> FocusedSourceKey -> MembershipDirection
    -> ScopedCheckedCore global -> ProofRequirement
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (Maybe (ExtensionalityBranch global)))
openMembershipBranch request source direction target requirement = Except.runExceptT do
    obligation <- Except.ExceptT (internFocusedObligation (focusedContextId request)
        (focusedSourcePolicy request) (focusedEligibility request) (focusedTarget request))
    scopeCharge
    let key = (obligation, source)
    application <- State.gets (Map.lookup key . searchExtensionalityBranches)
    allowed <- case application of
        Just _ -> pure True
        Nothing -> do
            policy <- State.gets (policyExtensionality . searchPolicy)
            used <- State.gets searchExtensionalityAttempts
            case policy of
                ExtensionalityDisabled -> scopeIntegrity "disabled extensionality was scheduled"
                MembershipExtensionality cap | used >= cap -> do
                    State.modify' (\state -> state {searchExtensionalityDeferred = True})
                    pure False
                MembershipExtensionality{} -> do
                    scopeCharge
                    State.modify' (\state -> state
                        { searchExtensionalityAttempts = used + 1
                        , searchExtensionalityBranches = Map.insert key Map.empty
                            (searchExtensionalityBranches state) })
                    pure True
    if not allowed then pure Nothing else do
        branch <- case application >>= Map.lookup direction of
            Just result -> either Except.throwE pure result
            Nothing -> do
                -- Pay for recording before setup: even a hard failure is retained.
                scopeCharge
                result <- lift (Except.runExceptT prepare)
                State.modify' (\state -> state {searchExtensionalityBranches =
                    Map.adjust (Map.insert direction result) key (searchExtensionalityBranches state)})
                either Except.throwE pure result
        let MembershipBranch child boundContext assumption = branch
        pure (Just (MembershipBranch child
            { focusedActive = focusedActive request, focusedRequirement = requirement }
            boundContext assumption))
  where
    prepare = do
        GroundFamilyId familyIndex <- case focusedEligibility request of
            SeedEligible family -> pure family
            ExistingFamily ExistentialBranch family -> pure family
            _ -> scopeIntegrity "a membership branch has no seed authority"
        scopeCharge
        parentFamily <- State.gets (Seq.lookup familyIndex . ownedGroundFamilies . searchGroundOwner)
            >>= maybe (scopeIntegrity "a membership branch lost its parent family") pure
        _ <- scopeAncestorDistance FocusedScopeWork (ScopeId (familyScope parentFamily))
            (ScopeId (focusedContextId request))
        (_, body) <- maybe (Except.throwE malformedApplicationSpine) pure (openScopedForall target)
        (assumption, consequent) <- maybe (Except.throwE malformedApplicationSpine) pure
            (openScopedImplication body)
        bound <- scopeBind (ScopeId (focusedContextId request)) TySet
        boundContext <- scopeContext bound
        childScope <- scopeAssume bound assumption
        childContext <- scopeContext childScope
        let weaken term = runScopedCore (\work -> countedWeakenCheckedScopedCore work TySet term)
        anchor <- weaken (familyAnchor parentFamily)
        views <- traverse (traverseSelection weaken) (familyViewLineage parentFamily)
        admitted <- Except.ExceptT (admitFamilyWith FocusedScopeWork (ownedContextId childScope)
            childContext anchor (familyImports parentFamily) (views Seq.|> SelectedGoalView body))
        eligibility <- case admitted of
            SeedEligible family -> pure (ExistingFamily ExtensionalityBranch family)
            _ -> scopeIntegrity "a membership branch did not create its own family"
        identifier <- Except.ExceptT (internFocusedObligation (ownedContextId childScope)
            (focusedSourcePolicy request) eligibility consequent)
        pure (MembershipBranch request
            { focusedObservation = SuppressAuxiliary AuxiliaryTheoremAntecedent
            , focusedRequirement = requirement
            , focusedContextId = ownedContextId childScope
            , focusedContext = childContext
            , focusedTarget = consequent
            , focusedEligibility = eligibility
            , focusedDirectionalEntry = Nothing
            , focusedObligation = Just identifier }
            boundContext assumption)

permitsSeededScopeOpening :: FocusedRequest global -> Bool
permitsSeededScopeOpening request = focusedSourcePolicy request == AllPermittedSources
    && case focusedEligibility request of
        SeedEligible{} -> True
        ExistingFamily ExistentialBranch _ -> True
        _ -> False

-- Opening owns both its nominal branch and its producer. Repeated consumers
-- reuse them even after the soft allowance stops admitting new sources.
openSuppliedExistential
    :: Ord global
    => FocusedRequest global -> ObviousProof global -> CoreType -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (Maybe (FocusedRequest global)))
openSuppliedExistential request source binderType body = Except.runExceptT do
    origin <- case obviousProofCandidateSource source of
        Just (CandidateSourceAnnotation (CandidateHypothesis index) _ _ _ _) ->
            hypothesisOrigin (focusedContextId request) index
        Just (CandidateSourceAnnotation (CandidateImport index) _ _ _ _) ->
            pure (ExistentialImport index)
        _ -> scopeIntegrity "an existential opening lost its supplied source"
    opened <- inheritedOpenings (focusedContextId request)
    if Set.member origin opened then pure Nothing else do
        obligation <- maybe (scopeIntegrity "an existential opening lost its owning obligation")
            pure (focusedObligation request)
        scopeCharge
        let key = (obligation, origin)
        cached <- State.gets (Map.lookup key . searchExistentialBranches)
        case cached of
            Just result -> Just . resume <$> either Except.throwE pure result
            Nothing -> do
                policy <- State.gets (policyExistentials . searchPolicy)
                used <- State.gets searchExistentialOpenings
                case policy of
                    ExistentialsDisabled -> scopeIntegrity "a disabled existential opening was scheduled"
                    SuppliedExistentials cap | used >= cap -> do
                        State.modify' (\state -> state {searchExistentialsDeferred = True})
                        pure Nothing
                    SuppliedExistentials{} -> do
                        -- Prepay recording the result, including failed setup at
                        -- the hard work boundary. Failure cannot restart the debit.
                        scopeCharge
                        State.modify' (\state -> state {searchExistentialOpenings = used + 1})
                        result <- lift (Except.runExceptT (prepare (Set.insert origin opened)))
                        State.modify' (\state -> state {searchExistentialBranches =
                            Map.insert key result (searchExistentialBranches state)})
                        Just <$> either Except.throwE pure result
  where
    resume child = child {focusedActive = focusedActive request}

    hypothesisOrigin scope index = do
        FocusedContext lineage _ <- lookupOwnedScope (ScopeId scope)
        case lineage of
            FocusedRootScope -> pure (ExistentialHypothesis scope index)
            FocusedBinderScope parent _ -> hypothesisOrigin parent index
            FocusedAssumptionScope parent _
                | index == 0 -> pure (ExistentialHypothesis scope 0)
                | otherwise -> hypothesisOrigin parent (index - 1)

    inheritedOpenings scope = do
        scopeCharge
        found <- State.gets (Map.lookup scope . searchExistentialScopes)
        case found of
            Just opened -> pure opened
            Nothing -> do
                FocusedContext lineage _ <- lookupOwnedScope (ScopeId scope)
                case lineage of
                    FocusedRootScope -> pure Set.empty
                    FocusedAssumptionScope parent _ -> inheritedOpenings parent
                    FocusedBinderScope parent _ -> inheritedOpenings parent

    prepare opened = do
        GroundFamilyId familyIndex <- case focusedEligibility request of
            SeedEligible family -> pure family
            ExistingFamily ExistentialBranch family -> pure family
            _ -> scopeIntegrity "an existential opening has no seed authority"
        scopeCharge
        parentFamily <- State.gets (Seq.lookup familyIndex . ownedGroundFamilies . searchGroundOwner)
            >>= maybe (scopeIntegrity "an existential opening lost its parent family") pure
        _ <- scopeAncestorDistance FocusedScopeWork (ScopeId (familyScope parentFamily))
            (ScopeId (focusedContextId request))
        bound <- scopeBind (ScopeId (focusedContextId request)) binderType
        childScope <- scopeAssume bound body
        childContext <- scopeContext childScope
        -- Binder extension preserves the global typing universe. These checked
        -- roots require only capture-avoiding weakening, not another type check.
        let weaken term = runScopedCore (\work -> countedWeakenCheckedScopedCore work binderType term)
        target <- weaken (focusedTarget request)
        anchor <- weaken (familyAnchor parentFamily)
        views <- traverse (traverseSelection weaken) (familyViewLineage parentFamily)
        admitted <- Except.ExceptT (admitFamilyWith FocusedScopeWork (ownedContextId childScope)
            childContext anchor (familyImports parentFamily) (views Seq.|> SelectedGoalView target))
        eligibility <- case admitted of
            SeedEligible family -> pure (ExistingFamily ExistentialBranch family)
            _ -> scopeIntegrity "an existential opening did not create its own family"
        identifier <- Except.ExceptT (internFocusedObligation (ownedContextId childScope)
            (focusedSourcePolicy request) eligibility target)
        scopeCharge
        State.modify' (\state -> state {searchExistentialScopes =
            Map.insert (ownedContextId childScope) opened (searchExistentialScopes state)})
        pure request
            { focusedObservation = SuppressAuxiliary AuxiliaryExistentialBranch
            , focusedRequirement = AnyObviousProof
            , focusedContextId = ownedContextId childScope
            , focusedContext = childContext
            , focusedTarget = target
            , focusedEligibility = eligibility
            , focusedDirectionalEntry = Nothing
            , focusedObligation = Just identifier }

-- Only a matched, fully instantiated application calls this transition. Its
-- direct premise probe retains the same owner for later support demand.
theoremPremiseEligibility :: PremiseQueryPolicy -> FocusedRequest global -> GroundEligibility
theoremPremiseEligibility policy request
    | policy == PremiseQueriesDisabled || not (eligibleFocusedGround request) = FocusedOnly
    | otherwise = case focusedEligibility request of
        SeedEligible family -> ExistingFamily TheoremPremise family
        ExistingFamily _use family -> ExistingFamily TheoremPremise family
        FocusedOnly -> FocusedOnly

canSeedFocusedGround :: FocusedRequest global -> Bool
canSeedFocusedGround request = focusedSourcePolicy request == AllPermittedSources
    && case focusedEligibility request of
        SeedEligible{} -> True
        _ -> False

-- A selected theorem premise owns one whole ground query opportunity. Its
-- structural components keep focused reasoning, without spending new starts.
-- Witness bodies retain their separately authorized existing-domain access.
structuralGroundEligibility :: GroundEligibility -> GroundEligibility
structuralGroundEligibility (ExistingFamily TheoremPremise _) = FocusedOnly
structuralGroundEligibility eligibility = eligibility

structuralChildRequest
    :: FocusedRequest global
    -> IntroductionScope global
    -> IntroductionContinuation global
    -> CandidateObservationScope
    -> ProofRequirement
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedRequest global))
structuralChildRequest parent scope continuation observation requirement target = do
    let (contextId, context) = case scope of
            IntroductionCurrentScope -> (focusedContextId parent, focusedContext parent)
            IntroductionExtendedScope childId childContext -> (childId, childContext)
    eligibility <- case (focusedEligibility parent, continuation) of
        (SeedEligible{}, IntroductionUniversal{}) ->
            let SearchEnvironment _typing imports _hypotheses _views = focusedEnvironment parent
            in admitGroundFamily contextId context target imports
        (ExistingFamily{}, IntroductionUniversal{}) -> pure (Right FocusedOnly)
        _ -> pure (Right (structuralGroundEligibility (focusedEligibility parent)))
    pure (fmap (\inherited -> parent
        { focusedObservation = observation
        , focusedRequirement = requirement
        , focusedContextId = contextId
        , focusedContext = context
        , focusedTarget = target
        , focusedEligibility = inherited
        , focusedDirectionalEntry = case continuation of
            IntroductionUniversal{} -> Nothing
            _ -> focusedDirectionalEntry parent
        }) eligibility)

-- The spine owns each checked binder prefix once. Only its first non-arrow
-- leaf may acquire a seed, and that permission is fixed before interning it.
openPointwisePrefix
    :: FocusedRequest global -> FocusedRequest global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (Maybe (FocusedRequest global, CoreType, Bool)))
openPointwisePrefix outer prefix = Except.runExceptT $
    case splitScopedEquality (focusedTarget prefix) of
        Just (TyArrow binder _, left, right) -> do
            scope <- scopeBind (ScopeId (focusedContextId prefix)) binder
            context <- scopeContext scope
            leftBody <- runScopedCore (\work -> countedPointwiseBodyScopedCore work left)
                >>= maybe (scopeIntegrity "a checked function lost its pointwise body") pure
            rightBody <- runScopedCore (\work -> countedPointwiseBodyScopedCore work right)
                >>= maybe (scopeIntegrity "a checked function lost its pointwise body") pure
            target <- runScopedCore (\work -> countedEqualScopedCore work leftBody rightBody)
                >>= maybe (scopeIntegrity "pointwise equality operands disagree") pure
            let arrow = case scopedCoreType leftBody of TyArrow{} -> True; _ -> False
                SearchEnvironment _ imports _ _ = focusedEnvironment outer
            eligibility <- if not arrow && canSeedFocusedGround outer
                    && focusedCompletionPermission outer == CompletionAllowed
                then Except.ExceptT (admitGroundFamily (ownedContextId scope) context target imports)
                else pure FocusedOnly
            pure (Just (prefix {focusedTarget = target, focusedContextId = ownedContextId scope,
                focusedContext = context, focusedObligation = Nothing, focusedEligibility = eligibility,
                focusedDirectionalEntry = Nothing}, binder, arrow))
        _ -> pure Nothing


startRules :: FocusedRulesInput global -> [FocusedRule global] -> FocusedAction global
startRules input rules = FocusedRules input rules Nothing False

ordinaryFocusedRules :: WitnessPolicy -> ExistentialPolicy -> FocusedRulesInput global -> [FocusedRule global]
ordinaryFocusedRules policy existentialPolicy input =
    FocusedExact ConvertExactCandidates : afterExactFocusedRules policy existentialPolicy input

directFocusedRules :: ScopedCheckedCore global -> [FocusedRule global]
directFocusedRules target =
    [FocusedExact DeferExactCandidateConversion, FocusedProjection DeferExactCandidateConversion]
    <> [FocusedStructuralEquality target | isJust (splitScopedEquality target)]
    <> [FocusedDirectIntroduction]

afterExactFocusedRules :: WitnessPolicy -> ExistentialPolicy -> FocusedRulesInput global -> [FocusedRule global]
afterExactFocusedRules policy existentialPolicy (FocusedRulesInput request available _continue) =
    introduction
    <> [FocusedStructuralEquality target | isJust (splitScopedEquality target)]
    <> [FocusedProjection ConvertExactCandidates | hasFacts]
    <> [FocusedEquality target | isJust (splitScopedEquality target)]
    <> [FocusedFalsum | hasFacts]
    <> [FocusedTheorem | hasFacts]
    <> [FocusedArgumentTransport | hasFacts, CApp _ CBound{} <- [scopedCoreTerm target]]
    <> [FocusedExistentialElimination | hasFacts && existentialPolicy /= ExistentialsDisabled
        && permitsSeededScopeOpening request]
    <> [FocusedCitedDefinitions | hasFacts && not (Map.null cited)]
    <> [FocusedTransportRule | hasFacts]
    <> [FocusedLocalFacts | hasFacts && not (null localViews)]
    <> [FocusedGoalDefinitions | not (null localViews) || not (Map.null importedViews)]
    <> [FocusedImportedFacts False | hasFacts && not (Map.null importedViews)]
    <> [FocusedPointwiseRule | Just (ty, _, _) <- [splitScopedEquality target], case ty of
        TyArrow{} -> True; TyProp -> True; TySet -> False]
  where
    target = focusedTarget request
    hasFacts = not (null available)
    SearchEnvironment _ _ _ (DefinitionViewCatalogue _ importedViews localViews cited) =
        focusedEnvironment request
    -- These workers would return immediately for an absent logical head or
    -- empty input family. Do not allocate choices and queue entries for them.
    -- This inspects the already prepared, checked root, without conversion.
    introduction = case scopedCoreTerm target of
        CTruth -> [FocusedIntroduction]
        CAnd{} -> [FocusedIntroduction]
        COr{} -> [FocusedIntroduction]
        CImp{} -> [FocusedIntroduction]
        CNot{} -> [FocusedIntroduction]
        CForall{} -> [FocusedIntroduction]
        CExists{} | policy /= WitnessesDisabled -> [FocusedWitness]
        _ -> []

beginPreparedFocusedRequest
    :: Ord global
    => FocusedRequest global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedRulesInput global))
beginPreparedFocusedRequest request exposed = Except.runExceptT do
    activated <- Except.ExceptT (activateFocusedRequest request { focusedTarget = exposed })
    lift (beginCandidateObservation (focusedObservation request))
    available <- Except.ExceptT (availableProofs (focusedEnvironment request)
        (focusedContextId request) (focusedContext request))
    pure (FocusedRulesInput activated available (Set.null (focusedActive request)))

prepareFocusedTargetSmall
    :: Ord global
    => CandidateObservationScope
    -> SearchEnvironment global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (PreparationResult (ObviousFailure global) (ScopedCheckedCore global))
prepareFocusedTargetSmall observation environment target = do
    work <- consumeSearchStep
    needs <- if work then headNeedsReduction False (scopedCoreTerm target)
        else pure focusedWorkExhausted
    case needs of
        Left failure -> PreparationFinished <$> observed (Left failure)
        Right False -> do
            case observation of
                ObserveRoot{} -> recordRootFocusedGoalView ObviousFocusedViewRetained
                SuppressAuxiliary{} -> pure ()
                CollectSharedEvidence -> pure ()
            pure (PreparationFinished (Right target))
        Right True -> do
            pool <- getConversionPool
            let SearchEnvironment typing _ _ _ = environment
            case Effort.runPreparatoryConversion preparatoryConversionLimit pool (\limit ->
                    Conversion.residualizeHeadChecked (Conversion.ConversionRecoveryTyping typing typing) limit target) of
                Left (ObviousConversionPoolAccountingInvariant cost incoming) ->
                    pure (PreparationFinished (Left (ObviousConversionAccountingInvariant cost incoming)))
                Right (owner, remaining, result) -> do
                    putConversionPool remaining
                    case result of
                        NeedsMoreEffort offered -> pure (NeedsMoreEffort offered)
                        PreparationFinished completed -> PreparationFinished <$> observed
                            (first (conversionFailure owner) completed)
  where
    observed = observePreparedTarget observation target

-- This cursor has already paid for head inspection. A larger retry runs just
-- the blocked converter; source discovery and the defining proof are retained.
finishPreparedTargetHead
    :: Ord global
    => CandidateObservationScope -> SearchEnvironment global -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ScopedCheckedCore global))
finishPreparedTargetHead observation (SearchEnvironment typing _ _ _) target =
    runConversion (\limit -> Conversion.residualizeHeadChecked
        (Conversion.ConversionRecoveryTyping typing typing) limit target)
        >>= observePreparedTarget observation target

observePreparedTarget
    :: Ord global
    => CandidateObservationScope -> ScopedCheckedCore global
    -> Either (ObviousFailure global) (ScopedCheckedCore global)
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ScopedCheckedCore global))
observePreparedTarget observation original = \case
    Left failure -> do
        observe (ObviousFocusedExposureFailed (obviousFailureClass failure))
        pure (Left failure)
    Right exposed -> scopedIdentity original exposed >>= \case
        Left failure -> pure (Left failure)
        Right same -> do
            observe (if same then ObviousFocusedViewRetained
                else ObviousFocusedViewChanged (summarizeScopedCore exposed))
            pure (Right exposed)
  where
    observe view = case observation of
        ObserveRoot{} -> recordRootFocusedGoalView view
        SuppressAuxiliary{} -> pure ()
        CollectSharedEvidence -> pure ()

activateFocusedRequest
    :: Ord global
    => FocusedRequest global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedRequest global))
activateFocusedRequest request = do
    obligation <- internFocusedObligation (focusedContextId request)
        (focusedSourcePolicy request) (focusedEligibility request)
        (focusedTarget request)
    case obligation of
        Left failure -> pure (Left failure)
        Right obligationId -> do
            certificate <- lookupFocusedCertificate (focusedRequirement request) obligationId
            pure (if Set.member obligationId (focusedActive request) && isNothing certificate
                then Left (ObviousRepeatedState (focusedTarget request))
                else Right request { focusedActive = Set.insert obligationId (focusedActive request)
                    , focusedObligation = Just obligationId })

enterFocusedRule
    :: Ord global => FocusedRulesInput global
    -> FocusedRule global
    -> State (ObviousSearchState global) (FocusedAction global)
enterFocusedRule input@(FocusedRulesInput request available _continue) = \case
    FocusedPointwiseRule -> pure (FocusedEqualityEntry request)
    FocusedExactContinuation pending -> pure (FocusedExactCandidates request pending)
    FocusedExact policy -> FocusedExactCandidates request
        <$> startExactAttempt policy target available
    FocusedIntroduction -> FocusedIntroduce request <$> startIntroduction requirement (focusedContextId request) context target
    FocusedWitness -> pure (FocusedWitnesses request available (startWitnessSearch target))
    FocusedExistentialElimination -> pure (FocusedExistentials request available)
    FocusedDirectIntroduction -> case scopedCoreTerm target of
        CAnd{} -> FocusedConjoin request <$> startConjunction requirement target
        CTruth -> FocusedIntroduce request <$> startIntroduction requirement (focusedContextId request) context target
        _ -> pure (FocusedReturn AttemptNotApplicable)
    FocusedProjection policy -> pure (FocusedProjectionCandidates request policy
        (ProjectionPending (ProjectionCursor Nothing (ProjectionRoots available) Seq.empty)))
    FocusedEquality equalityTarget -> pure (FocusedEqualities request ConvertExactCandidates (startEquality equalityTarget available))
    FocusedStructuralEquality equalityTarget -> pure (FocusedEqualities request DeferExactCandidateConversion (startEquality equalityTarget available))
    FocusedFalsum -> FocusedFalsumCandidates request available
        . FalsumPending . FalsumLookup FalsumDirect
            <$> startTermLookup context CFalsum available
    FocusedTheorem -> ordinaryTheorems True
    FocusedCitedDefinitions
        | Map.null citedPredicates -> pure (FocusedReturn AttemptNotApplicable)
        | otherwise -> pure (FocusedFactViews
            (FocusedRulesInput request { focusedEnvironment =
                SearchEnvironment typing imports hypothesisCount
                    (DefinitionViewCatalogue definitions citedPredicates locals Map.empty)
                , focusedSourcePolicy = CitedPredicateSources }
                available False)
            True ImportedDefinitionViewsOnly (FactDefinitionPending (FactDefinitionSources Nothing available)))
    FocusedArgumentTransport -> pure (FocusedTransport request (TransportPending (TransportArguments available)))
    FocusedTransportRule -> endpointProducerFor request >>= \case
        Left failure -> pure (FocusedReturn (AttemptFailed failure))
        Right producer -> pure (FocusedTransport request
            (TransportPending (TransportDiscover (PropositionTransportScan Seq.empty False producer) available)))
    FocusedLocalFacts
        | null locals -> pure (FocusedReturn AttemptNotApplicable)
        | otherwise -> pure (facts False LocalDefinitionViewsOnly)
    FocusedImportedFacts direct
        | Map.null imported -> pure (FocusedReturn AttemptNotApplicable)
        | otherwise -> pure (facts direct ImportedDefinitionViewsOnly)
    FocusedGoalDefinitions -> FocusedGoalViews request <$> startGoalDefinition (focusedEnvironment request) context target
  where
    requirement = focusedRequirement request
    context = focusedContext request
    target = focusedTarget request
    SearchEnvironment typing imports hypothesisCount
        (DefinitionViewCatalogue definitions imported locals citedPredicates) = focusedEnvironment request
    ordinaryTheorems recursive = FocusedTheorems input recursive <$> startTheoremSearch target available
    facts direct selection = FocusedFactViews input direct selection
        (FactDefinitionPending (FactDefinitionSources Nothing available))

buildBooleanEquality
    :: FocusedRequest global -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> ObviousProof global -> ObviousProof global -> FocusedAction global
    -> State (ObviousSearchState global) (FocusedAction global)
buildBooleanEquality request left right forward backward following =
    combineCandidateDependencies (obviousProofDependencies forward) (obviousProofDependencies backward) >>= \case
        Left failure -> pure (FocusedReturn (AttemptFailed failure))
        Right dependencies -> pure (FocusedBooleanBuild request dependencies
            (BooleanEqualityFoundation left right (obviousBuiltProof forward) (obviousBuiltProof backward)) following)

resumeFocused
    :: Ord global
    => FocusedContinuation global
    -> Attempt global
    -> State (ObviousSearchState global) (FocusedAction global)
resumeFocused continuation result = case continuation of
    AfterBooleanDirect request -> pure case result of
        AttemptSucceeded{} -> FocusedReturn result
        AttemptFailed failure | isTerminalFocusedFailure failure -> FocusedReturn result
        _ -> FocusedBooleanIntroduce request
    AfterBooleanIntroduction request -> pure case result of
        AttemptSucceeded{} -> FocusedReturn result
        AttemptFailed failure | isTerminalFocusedFailure failure -> FocusedReturn result
        _ -> FocusedPhaseEntry GeneralSearch SearchDependency request
    AfterBooleanBodyDirect{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "directional direct continuation escaped its worker")))
    AfterBooleanBodyGround{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "directional ground continuation escaped its worker")))
    AfterBooleanFirst request left right backward -> pure case result of
        AttemptSucceeded forward -> FocusedBooleanSecond request left right forward backward
        _ -> FocusedReturn result
    AfterBooleanSecond request left right forward -> case result of
        AttemptSucceeded backward -> buildBooleanEquality request left right forward backward
            (FocusedBooleanSupport request left right forward backward)
        _ -> returned result
    AfterBooleanUpgrade request left right forwardSide other -> case result of
        AttemptSucceeded proof -> buildBooleanEquality request left right
            (if forwardSide then proof else other) (if forwardSide then other else proof)
            (FocusedReturn (AttemptFailed ObviousCanonicalDefinitionEvidenceRequired))
        _ -> returned result
    AfterPointwise outer child binders -> pure case result of
        AttemptSucceeded proof -> FocusedPointwiseBuild outer child (obviousProofDependencies proof)
            (startFunctionEqualityProof (focusedTarget outer) (focusedTarget child) binders (obviousBuiltProof proof))
            -- Subscribe for support only after ordinary publication. A first
            -- canonical certificate is wrapped once, not delivered to two
            -- concurrent reconstruction continuations.
            (FocusedPointwiseSupport outer child binders)
        _ -> FocusedReturn result
    AfterPrefixDirect request -> case result of
        AttemptSucceeded proof -> pure (FocusedPublish request proof (FocusedPrefixTheorems request))
        AttemptFailed failure | isTerminalFocusedFailure failure -> returned result
        _ -> pure (FocusedPrefixTheorems request)
    AfterEndpointGuard request following -> case result of
        AttemptSucceeded{} -> resumeFocused following result
        AttemptFailed failure | isTerminalFocusedFailure failure -> resumeFocused following result
        _ -> pure (FocusedExistingEvidence request following)
    AfterEndpointEquality request policy (EqualityTarget target following
            (EqualityProofDemand input demanded operands frames)) ->
        pure (FocusedEqualities request policy (EqualityPending
            (EqualityTarget target following (resumeEndpointProof input demanded operands frames result))))
    AfterEndpointEquality{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "endpoint equality lost its demand frame")))
    AfterArgumentEquality request policy (EqualityTarget target following
            (EqualityCompletionDemand input _ operands frames)) ->
        pure (FocusedEqualities request policy (EqualityPending
            (EqualityTarget target following (resumeArgumentProof input operands frames result))))
    AfterArgumentEquality{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "argument equality lost its demand frame")))
    AfterEndpointTransport request (TransportEquality demanded graph source following
            (EqualityProofDemand input requirement operands frames)) ->
        pure (FocusedTransport request (TransportPending
            (TransportEquality demanded graph source following (resumeEndpointProof input requirement operands frames result))))
    AfterEndpointTransport{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "endpoint transport lost its demand frame")))
    AfterArgumentTransport request (TransportEquality demanded graph source following
            (EqualityCompletionDemand input _ operands frames)) ->
        pure (FocusedTransport request (TransportPending
            (TransportEquality demanded graph source following (resumeArgumentProof input operands frames result))))
    AfterArgumentTransport{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "argument transport lost its demand frame")))
    AfterEndpointDirection context reversed -> case result of
        AttemptSucceeded proof | reversed -> pure (FocusedEndpointReverse context SmallPreparation proof)
        _ -> returned result
    AfterEndpointSource request prepared reversed followingSource -> case result of
        AttemptSucceeded proof
            | reversed -> pure (FocusedEndpointReverse (focusedContext request) SmallPreparation proof)
            | otherwise -> returned result
        AttemptFailed failure | isTerminalFocusedFailure failure -> returned result
        _ | not reversed -> pure (FocusedDirectQuantum 512
                (FocusedEndpointSourceWithContinuation request prepared followingSource))
          | otherwise -> pure (FocusedEndpointSearch request (resumeTheoremSearch followingSource))
    AfterFocusedRequest request -> case result of
        AttemptNotApplicable -> returned (AttemptFailed (ObviousNoMatchingConclusion (focusedTarget request)))
        AttemptFailed{} -> returned result
        AttemptSucceeded completed@(ObviousProof proof dependencies) ->
            -- Delivering an already certified ground result must remain
            -- possible after competing focused search exhausts its allowance.
            -- The exact target check is still charged to its producing owner.
            Except.runExceptT (runScopeCore
                (if isJust (obviousProofCertification completed) then GroundScopeWork else FocusedScopeWork)
                absurd (\work -> countedScopedCoreIdentity work
                    (KernelProof.builtProofStatement proof) (focusedTarget request))) >>= \case
                Left failure -> returned (AttemptFailed failure)
                Right True -> returned (AttemptSucceeded completed)
                Right False -> pure (FocusedConvertRequest request dependencies
                    (HeadProofConvert SmallPreparation proof (focusedTarget request)))
    AfterFocusedSearch request -> do
        recordRootFocusedOutcome request (focusedAttemptResult (focusedTarget request) result)
        returned result
    AfterFocusedProducer{} -> returned (AttemptFailed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "an obligation producer returned outside its scheduler")))
    AfterFocusedGeneralEntry _identifier -> returned result
    AfterFocusedAlias request prepared -> case result of
        AttemptSucceeded proof -> do
            retained <- maybe (pure (Right ())) (`retainFocusedCertificate` proof) (focusedObligation request)
            pure case retained of
                Left failure -> FocusedReturn (AttemptFailed failure)
                Right () | satisfiesRequirement MustUseCanonicalDefinition proof -> FocusedReturn result
                Right () -> FocusedDemandCertificate GeneralSearch request
                    {focusedRequirement = MustUseCanonicalDefinition} prepared
        _ -> returned result
    AfterFocusedCertificate identifier -> returned case result of
        AttemptSucceeded proof -> AttemptSucceeded proof {obviousProofObligation = Just identifier}
        _ -> result
    AfterLeftConjunctionSupport right -> case result of
        AttemptSucceeded left -> FocusedReturn <$> buildConjunction left right
        _ -> returned result
    AfterRightConjunctionSupport left -> case result of
        AttemptSucceeded right -> FocusedReturn <$> buildConjunction left right
        _ -> returned result
    AfterGroundEntryFailure earlier -> returned case result of
        AttemptFailed failure -> AttemptFailed (preferObviousFailure earlier failure)
        AttemptNotApplicable -> AttemptFailed earlier
        AttemptSucceeded{} -> result
    AfterDirectPremise target -> returned case result of
        AttemptNotApplicable -> AttemptFailed (ObviousAntecedentUnavailable target)
        _ -> result
    AfterDirectRule input rest firstFailure rejected ->
        resumeFocusedRules input rest firstFailure rejected result >>= \case
            FocusedRules following rules failure wasRejected ->
                pure (FocusedDirectRules following rules failure wasRejected)
            other -> pure other
    AfterFocusedRule input rest firstFailure rejected ->
        resumeFocusedRules input rest firstFailure rejected result
    AfterFocusedIntroduction request child pending -> do
        resumed <- resumeIntroduction (focusedContext request) pending
            (focusedAttemptResult (focusedTarget child) result)
        case (resumed, result) of
            (IntroductionFinished (AttemptSucceeded proof), AttemptSucceeded premise)
                | not (satisfiesRequirement (focusedRequirement request) proof) -> do
                    retained <- maybe (pure (Right ())) (`retainFocusedCertificate` proof) (focusedObligation request)
                    pure case retained of
                        Left failure -> FocusedReturn (AttemptFailed failure)
                        Right () -> FocusedSupportDependency child premise continuation
            _ -> pure (FocusedIntroduce request resumed)
    AfterFocusedExistential request child source binderType body -> case result of
        AttemptSucceeded premise -> do
            rebuilt <- Except.runExceptT do
                dependencies <- Except.ExceptT (combineCandidateDependencies
                    (obviousProofDependencies source) (obviousProofDependencies premise))
                proof <- Except.ExceptT (runCountedKernel (KernelProof.countedPreparedExistentialEliminationProof (focusedContext request) binderType body (obviousBuiltProof source)
                        (focusedTarget request) (obviousBuiltProof premise)))
                pure (ObviousProof proof dependencies)
            case rebuilt of
                Left failure -> returned (AttemptFailed failure)
                Right proof | satisfiesRequirement (focusedRequirement request) proof ->
                    returned (AttemptSucceeded proof)
                Right proof -> do
                    retained <- maybe (pure (Right ())) (`retainFocusedCertificate` proof) (focusedObligation request)
                    pure case retained of
                        Left failure -> FocusedReturn (AttemptFailed failure)
                        Right () -> FocusedSupportDependency child premise continuation
        _ -> returned result
    AfterFocusedConjunction request target pending ->
        FocusedConjoin request <$> resumeConjunction pending (focusedAttemptResult target result)
    AfterMatchedTheorem candidate progress ->
        FocusedReturn <$> observeMatchedTheorem candidate progress result
    AfterDirectProbe child following -> case result of
        AttemptSucceeded proof
            | satisfiesRequirement (focusedRequirement child) proof -> resumeFocused following result
        AttemptFailed failure@(ObviousResourceExhausted ObviousConversionOperationLimit) ->
            pure (FocusedDeferredPremise child following (Just failure))
        AttemptFailed failure
            | isTerminalFocusedFailure failure -> resumeFocused following result
        _ -> pure (FocusedDeferredPremise child following Nothing)
    AfterApplicationChild request input target substitutions pending frames ->
        FocusedApply request <$> resumeApplicationChild input target substitutions pending frames
            (focusedAttemptResult target result)
    AfterExtensionalityFallback request source direction target requirement following -> case result of
        AttemptSucceeded proof | satisfiesRequirement requirement proof -> resumeFocused following result
        AttemptFailed failure | isTerminalFocusedFailure failure -> resumeFocused following result
        _ -> pure (FocusedExtensionality request source direction target requirement result following)
    AfterExtensionalityDischarge request (MembershipBranch _child boundContext assumption) following ->
        case result of
            AttemptSucceeded premise -> do
                rebuilt <- runCountedKernel do
                    implication <- KernelProof.countedImplicationIntroductionProof
                        boundContext assumption (obviousBuiltProof premise)
                    universal <- KernelProof.countedForallIntroductionProof
                        (focusedContext request) TySet implication
                    -- The inner obligation is for a different statement and scope.
                    -- Keep only consumed evidence; application support resumes this
                    -- retained branch rather than aliasing its inner certificate.
                    pure (ObviousProof universal (obviousProofDependencies premise))
                resumeFocused following (either AttemptFailed AttemptSucceeded rebuilt)
            _ -> resumeFocused following result
    AfterApplicationUpgrade request input (ApplicationSupportRecipe _selected substitutions prefix
            dependencies target remaining steps) -> case result of
        AttemptSucceeded premise -> scopedIdentity (obviousProofStatement premise) target >>= \case
            Left failure -> returned (AttemptFailed failure)
            Right same -> pure (FocusedDirectQuantum 512 (FocusedApply request (ApplicationPending input
                (ApplicationConvertPremise substitutions prefix dependencies (obviousProofDependencies premise)
                    remaining steps (if same then HeadProofFinished (Right (obviousBuiltProof premise))
                        else HeadProofConvert SmallPreparation (obviousBuiltProof premise) target)) [])))
        _ -> returned result
    AfterFocusedTransport request target pending ->
        readyTransport request <$> resumeTransport (focusedRequirement request) (focusedTarget request)
            pending (focusedAttemptResult target result)
    AfterFocusedGoalView request target pending ->
        readyGoalView request <$> resumeGoalDefinition (focusedActive request)
            pending (focusedAttemptResult target result)
  where
    returned = pure . FocusedReturn

readyTransport :: FocusedRequest global -> TransportStep global -> FocusedAction global
readyTransport request step = case step of
    TransportPending TransportReconstruct{} -> FocusedDirectQuantum 512 (FocusedTransport request step)
    _ -> FocusedTransport request step

readyGoalView :: FocusedRequest global -> GoalDefinitionStep global -> FocusedAction global
readyGoalView request step = case step of
    GoalDefinitionPending GoalDefinitionBuild{} -> FocusedDirectQuantum 512 (FocusedGoalViews request step)
    _ -> FocusedGoalViews request step

resumeFocusedRules
    :: Ord global
    => FocusedRulesInput global
    -> [FocusedRule global]
    -> Maybe (ObviousFailure global)
    -> Bool
    -> Attempt global
    -> State (ObviousSearchState global) (FocusedAction global)
resumeFocusedRules input@(FocusedRulesInput request _available continue) rest firstFailure rejected = \case
    AttemptSucceeded proof -> do
        retained <- maybe (pure (Right ())) (`retainFocusedCertificate` proof) (focusedObligation request)
        case retained of
            Left failure -> done (AttemptFailed failure)
            Right () -> checkProofRequirement (focusedObservation request)
                (focusedRequirement request) proof >>= \case
                    Left failure -> done (AttemptFailed failure)
                    Right True -> done (AttemptSucceeded proof)
                    Right False -> next firstFailure True
    AttemptNotApplicable -> next firstFailure rejected
    AttemptFailed failure@(ObviousResourceExhausted ObviousConversionOperationLimit)
        | continue -> next (firstFailure <|> Just failure) rejected
    AttemptFailed failure | isTerminalFocusedFailure failure -> done (AttemptFailed failure)
    AttemptFailed ObviousCanonicalDefinitionEvidenceRequired -> next firstFailure True
    AttemptFailed failure -> next (firstFailure <|> Just failure) rejected
  where
    done = pure . FocusedReturn
    next failure wasRejected = pure (FocusedRules input rest failure wasRejected)


recordRootFocusedGoalView
    :: ObviousFocusedGoalView global
    -> State (ObviousSearchState global) ()
recordRootFocusedGoalView view =
    State.modify'
        (\state ->
            state
                { searchRootFocusedGoalView =
                    searchRootFocusedGoalView state <|> Just view
                })

beginCandidateObservation
    :: CandidateObservationScope
    -> State (ObviousSearchState global) ()
beginCandidateObservation = \case
    ObserveRoot{} ->
        State.modify'
            (\state -> state {searchCandidateObservationStarted = True})
    SuppressAuxiliary{} -> pure ()
    CollectSharedEvidence -> pure ()

extendRootGoalView
    :: Natural
    -> CandidateObservationScope
    -> State (ObviousSearchState global) CandidateObservationScope
extendRootGoalView ordinal = \case
    CollectSharedEvidence -> pure CollectSharedEvidence
    suppressed@SuppressAuxiliary{} -> pure suppressed
    ObserveRoot (RootGoalView _previousId publicView) -> do
        next <- State.gets searchNextRootGoalViewId
        State.modify'
            (\state -> state {searchNextRootGoalViewId = next + 1})
        let (lineage, truncated) =
                case publicView of
                    CandidateOriginalGoalView -> ([ordinal], False)
                    CandidateDefinitionGoalView retained alreadyTruncated ->
                        retainCandidateLineage
                            ordinal retained alreadyTruncated
        pure
            (ObserveRoot
                (RootGoalView
                    (RootGoalViewId next)
                    (CandidateDefinitionGoalView lineage truncated)))

beginCandidate
    :: CandidateObservationScope
    -> CandidateComparisonView
    -> ScopedCheckedCore global
    -> ObviousProof global
    -> State (ObviousSearchState global) (Maybe (CandidateSeed global))
beginCandidate scope view proposition proof =
    case (scope, obviousProofCandidateSource proof) of
        (ObserveRoot root@(RootGoalView rootId _publicView),
                Just source) -> do
            next <- State.gets searchNextCandidateId
            State.modify'
                (\state -> state {searchNextCandidateId = next + 1})
            pure
                (Just
                    (CandidateSeed
                        (CandidateIdentity (CandidateId next) rootId)
                        root source view proposition))
        _ -> pure Nothing

candidateSucceeded
    :: Maybe (CandidateSeed global)
    -> Natural
    -> Maybe CandidateStructuralDifference
    -> ObviousProof global
    -> State (ObviousSearchState global) (ObviousProof global)
candidateSucceeded Nothing _progress _difference proof = pure proof
candidateSucceeded (Just seed) progress difference proof =
    pure (withCandidateCompletion (CandidateCompletion seed progress difference) proof)

recordCandidateOutcome
    :: Ord global
    => CandidateSeed global
    -> CandidateOutcome
    -> Natural
    -> Maybe CandidateStructuralDifference
    -> Maybe CandidateAuxiliaryCause
    -> State (ObviousSearchState global) ()
recordCandidateOutcome (CandidateSeed
        identity (RootGoalView _rootId rootView)
        (CandidateSourceAnnotation
            baseSource sourceOrder _projectionDepth
            factDefinitions factDefinitionsTruncated)
        view proposition)
        outcome progress structuralDifference auxiliaryCause = do
    retained <- State.gets searchRetainedCandidates
    let rank = CandidateRank
            identity outcome progress (candidateFamilyRank view)
            sourceOrder
    if not (candidateCanEnter rank retained)
        then
            traverse_
                (\cause -> State.modify' (retainAuxiliaryCauseInState cause))
                auxiliaryCause
        else do
            let observation =
                    ObviousCandidateObservation
                        { obviousCandidateSource = baseSource
                        , obviousCandidateView = view
                        , obviousCandidateRootView = rootView
                        , obviousCandidateDefinitionParticipation =
                            candidateDefinitionParticipation
                                factDefinitions factDefinitionsTruncated rootView
                        , obviousCandidateProposition =
                            summarizeScopedCore proposition
                        , obviousCandidateOutcome = outcome
                        , obviousCandidateProgress = progress
                        , obviousCandidateStructuralDifference =
                            structuralDifference
                        , obviousCandidateAuxiliaryCause = auxiliaryCause
                        }
                candidate = RetainedCandidate rank observation
            State.modify'
                (\state ->
                    let previous = searchRetainedCandidates state
                        updated = insertRetainedCandidate candidate previous
                        displacedCauses =
                            candidateAuxiliaryCausesDisplaced previous updated
                        withCandidates =
                            state {searchRetainedCandidates = updated}
                    in foldl'
                        (flip retainAuxiliaryCauseInState)
                        withCandidates displacedCauses)

candidateCanEnter
    :: CandidateRank
    -> [RetainedCandidate global]
    -> Bool
candidateCanEnter rank retained =
    case findRetainedCandidate rank retained of
        Just existing -> compareCandidateRank rank existing == GT
        Nothing ->
            length retained < candidateObservationLimit
                || case reverse retained of
                    RetainedCandidate worst _observation : _rest ->
                        compareCandidateRank rank worst == GT
                    [] -> True

findRetainedCandidate
    :: CandidateRank
    -> [RetainedCandidate global]
    -> Maybe CandidateRank
findRetainedCandidate (CandidateRank identity _outcome _progress _family
        _sourceOrder) =
    listToMaybe . mapMaybe sameIdentity
  where
    sameIdentity (RetainedCandidate rank@(CandidateRank found _foundOutcome
            _foundProgress _foundFamily _foundSourceOrder)
            _observation)
        | found == identity = Just rank
        | otherwise = Nothing

insertRetainedCandidate
    :: RetainedCandidate global
    -> [RetainedCandidate global]
    -> [RetainedCandidate global]
insertRetainedCandidate candidate@(RetainedCandidate candidateRank _observation) =
    take candidateObservationLimit . insert . removeIdentity
  where
    removeIdentity = filter
        (\(RetainedCandidate rank _row) ->
            candidateRankIdentity rank /= candidateRankIdentity candidateRank)

    insert [] = [candidate]
    insert rows@(row@(RetainedCandidate rank _row) : rest)
        | compareCandidateRank candidateRank rank == GT = candidate : rows
        | otherwise = row : insert rest

candidateRankIdentity :: CandidateRank -> CandidateIdentity
candidateRankIdentity
        (CandidateRank identity _outcome _progress _family _sourceOrder) =
    identity

candidateAuxiliaryCausesDisplaced
    :: [RetainedCandidate global]
    -> [RetainedCandidate global]
    -> [CandidateAuxiliaryCause]
candidateAuxiliaryCausesDisplaced previous updated =
    mapMaybe displaced previous
  where
    displaced (RetainedCandidate rank observation) =
        case obviousCandidateAuxiliaryCause observation of
            Nothing -> Nothing
            Just cause
                | any (retainsCause (candidateRankIdentity rank) cause) updated ->
                    Nothing
                | otherwise -> Just cause

    retainsCause identity cause (RetainedCandidate foundRank foundObservation) =
        candidateRankIdentity foundRank == identity
            && obviousCandidateAuxiliaryCause foundObservation == Just cause

compareCandidateRank :: CandidateRank -> CandidateRank -> Ordering
compareCandidateRank
        (CandidateRank _leftIdentity leftOutcome leftProgress leftFamily
            leftSourceOrder)
        (CandidateRank _rightIdentity rightOutcome rightProgress rightFamily
            rightSourceOrder) =
    compare (candidateOutcomeRank leftOutcome) (candidateOutcomeRank rightOutcome)
        <> compare leftProgress rightProgress
        <> compare rightFamily leftFamily
        <> compare rightSourceOrder leftSourceOrder

candidateOutcomeRank :: CandidateOutcome -> Int
candidateOutcomeRank = \case
    ProofRejectedByRequirement -> 3
    ProofIncomplete{} -> 2
    ComparisonRejected{} -> 1

candidateFamilyRank :: CandidateComparisonView -> Int
candidateFamilyRank = \case
    CandidateDirectView -> 0
    CandidateProjectedView{} -> 1
    CandidatePreparedTheoremView{} -> 2
    CandidateEqualityTransportView{} -> 3

candidateDefinitionParticipation
    :: [Natural]
    -> Bool
    -> CandidateRootGoalView
    -> CandidateDefinitionParticipation
candidateDefinitionParticipation factDefinitions factTruncated = \case
    CandidateOriginalGoalView
        | null factDefinitions -> CandidateNoDefinitionParticipation
        | otherwise ->
            CandidateFactDefinitionParticipation
                factDefinitions factTruncated
    CandidateDefinitionGoalView goalDefinitions goalTruncated
        | null factDefinitions ->
            CandidateGoalDefinitionParticipation
                goalDefinitions goalTruncated
        | otherwise ->
            CandidateFactAndGoalDefinitionParticipation
                factDefinitions factTruncated goalDefinitions goalTruncated

candidateObservationLimit :: Int
candidateObservationLimit = 3

isTerminalFocusedFailure :: ObviousFailure global -> Bool
isTerminalFocusedFailure = \case
    ObviousResourceExhausted{} -> True
    ObviousMalformedInput{} -> True
    ObviousIntegrityFailure{} -> True
    ObviousConversionFailed{} -> True
    ObviousRequiredConversionNotConvertible -> True
    ObviousConversionAccountingInvariant{} -> True
    _failure -> False

-- A recursive goal-definition branch returns exhausted resources to its caller.
-- Only the original goal may inspect later goal-definition views.
stopsGoalDefinitionSearch
    :: Set FocusedObligationId
    -> ObviousFailure global
    -> Bool
stopsGoalDefinitionSearch active
        (ObviousResourceExhausted ObviousConversionOperationLimit) =
    Set.size active > 1
stopsGoalDefinitionSearch _active failure =
    isTerminalFocusedFailure failure

isConversionLimit :: ObviousFailure global -> Bool
isConversionLimit = \case
    ObviousResourceExhausted ObviousConversionOperationLimit -> True
    ObviousResourceExhausted ObviousConversionPoolLimit -> True
    _ -> False

isFocusedInfrastructureFailure :: ObviousFailure global -> Bool
isFocusedInfrastructureFailure = \case
    ObviousMalformedInput{} -> True
    ObviousIntegrityFailure{} -> True
    ObviousConversionFailed{} -> True
    ObviousRequiredConversionNotConvertible -> True
    ObviousConversionAccountingInvariant{} -> True
    _failure -> False

satisfiesRequirement
    :: ProofRequirement
    -> ObviousProof global
    -> Bool
satisfiesRequirement AnyObviousProof _proof =
    True
satisfiesRequirement MustUseCanonicalDefinition
        (ObviousProof _proof dependencies) =
    candidateUsesCanonicalDefinition dependencies

checkProofRequirement
    :: Ord global
    => CandidateObservationScope
    -> ProofRequirement
    -> ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Bool)
checkProofRequirement observationScope requirement proof
    | satisfiesRequirement requirement proof = pure (Right True)
    | otherwise = do
        case obviousProofCandidateCompletion proof of
            Just (CandidateCompletion seed progress difference) ->
                recordCandidateOutcome seed ProofRejectedByRequirement progress difference Nothing
            Nothing -> recordUnattributedRequirementRejection observationScope
        pure (Right False)

-- Audit only the selected completed derivation, never every speculative prefix.
-- The constructors above retain one consumed source in predecessor order; the
-- read-only kernel summary checks that source after all proof binders discharge.
-- Ground publication retains its checked source-use summary with that exact
-- immutable proof. A subsequent construction clears it and is audited anew.
auditSelectedCanonicalProof
    :: ProofRequirement
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ObviousProof global))
auditSelectedCanonicalProof AnyObviousProof result = pure result
auditSelectedCanonicalProof MustUseCanonicalDefinition (Left failure) = pure (Left failure)
auditSelectedCanonicalProof MustUseCanonicalDefinition (Right proof@(ObviousProof built dependencies)) =
    Except.runExceptT do
        source <- maybe (Except.throwE ObviousCanonicalDefinitionEvidenceRequired) pure
            (candidateCanonicalSource dependencies)
        (owner, uses) <- case obviousProofCertification proof of
            Just (context, summary) -> do
                unless (context == FocusedContextId 0)
                    (scopeIntegrity "a selected ground proof belongs to a different scope")
                pure (GroundScopeWork, summary)
            Nothing -> do
                evidence <- recordConstruction (ScopeId (FocusedContextId 0)) built
                pure (FocusedScopeWork, evidenceUses evidence)
        consumed <- case source of
            CanonicalImportedSource ordinal index -> do
                scopeChargeTo owner
                registered <- State.gets (Set.member ordinal . searchRegisteredDefinitionImports)
                pure (registered && Set.member index (kernelSourceImportUses uses))
            CanonicalHypothesisSource index -> do
                scopeChargeTo owner
                pure (Set.member (hypothesisIx index) (kernelSourceExternalHypothesisUses uses))
        unless consumed (scopeIntegrity "a canonical Obvious certificate did not consume its retained source")
        pure proof

recordUnattributedRequirementRejection
    :: CandidateObservationScope
    -> State (ObviousSearchState global) ()
recordUnattributedRequirementRejection = \case
    CollectSharedEvidence -> pure ()
    ObserveRoot (RootGoalView _rootId rootView) ->
        State.modify'
            (\state ->
                state
                    { searchRootRequirementRejections =
                        retainBoundedDistinct
                            candidateRequirementNoteLimit rootView
                            (searchRootRequirementRejections state)
                    })
    SuppressAuxiliary auxiliaryKind ->
        let cause = CandidateAuxiliaryRequirementRejected auxiliaryKind
        in State.modify' (retainAuxiliaryCauseInState cause)

retainAuxiliaryCauseInState
    :: CandidateAuxiliaryCause
    -> ObviousSearchState global
    -> ObviousSearchState global
retainAuxiliaryCauseInState cause state
    | length (searchAuxiliaryRequirementCauses state)
            < candidateRequirementNoteLimit =
        state
            { searchAuxiliaryRequirementCauses =
                searchAuxiliaryRequirementCauses state <> [cause]
            }
    | otherwise =
        state
            { searchAdditionalAuxiliaryRequirementCauses =
                saturatingSuccessor
                    (searchAdditionalAuxiliaryRequirementCauses state)
            }

saturatingSuccessor :: Word -> Word
saturatingSuccessor value
    | value == maxBound = maxBound
    | otherwise = value + 1

claimAuxiliaryRequirementCause
    :: ObviousAuxiliaryObligationKind
    -> State (ObviousSearchState global) CandidateAuxiliaryCause
claimAuxiliaryRequirementCause kind = do
    let cause = CandidateAuxiliaryRequirementRejected kind
    fromMaybe cause <$> claimAuxiliaryRequirementCauseIfPresent kind

claimAuxiliaryRequirementCauseIfPresent
    :: ObviousAuxiliaryObligationKind
    -> State (ObviousSearchState global) (Maybe CandidateAuxiliaryCause)
claimAuxiliaryRequirementCauseIfPresent kind = do
    state <- State.get
    let cause = CandidateAuxiliaryRequirementRejected kind
        additional = searchAdditionalAuxiliaryRequirementCauses state
        retained = searchAuxiliaryRequirementCauses state
    if additional > 0
        then do
            State.put
                state
                    { searchAdditionalAuxiliaryRequirementCauses =
                        additional - 1
                    }
            pure (Just cause)
        else if cause `elem` retained
            then do
                State.put
                    state
                        { searchAuxiliaryRequirementCauses =
                            removeLast cause retained
                        }
                pure (Just cause)
            else pure Nothing
  where
    removeLast requested = reverse . removeFirst requested . reverse
    removeFirst _requested [] = []
    removeFirst requested (value : rest)
        | value == requested = rest
        | otherwise = value : removeFirst requested rest

retainBoundedDistinct :: Eq value => Int -> value -> [value] -> [value]
retainBoundedDistinct limit value values
    | value `elem` values = values
    | length values < limit = values <> [value]
    | otherwise = values

candidateRequirementNoteLimit :: Int
candidateRequirementNoteLimit = 2

availableProofs
    :: Eq global
    => SearchEnvironment global
    -> FocusedContextId
    -> KernelProof.ProofContext global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) [ObviousProof global])
availableProofs
        environment@(SearchEnvironment
            _globalType imports initialHypothesisCount
            (DefinitionViewCatalogue definitionViews
                _importedDefinitionViews localDefinitionRows _citedPredicates))
        contextId context = do
    cached <-
        State.gets (Map.lookup contextId . searchAvailableProofCache)
    case cached of
        Just proofs -> pure (Right proofs)
        Nothing -> build
  where
    build = do
        currentCount <-
            if null localDefinitionRows
                then pure (Right initialHypothesisCount)
                else currentHypothesisCountCounted context
        case currentCount >>= \count ->
                Map.fromList . concat
                    <$> traverse (localDefinitionIndex count) definitionViews of
            Left failure -> pure (Left failure)
            Right canonicalLocalIndices -> do
                localResult <-
                    runCountedKernel
                        (KernelProof.countedHypothesisProofs
                                context)
                case localResult of
                    Left failure -> pure (Left failure)
                    Right localProofs -> do
                        importedResult <- buildImports 0 imports
                        case importedResult of
                            Left failure -> pure (Left failure)
                            Right importedRoots -> do
                                let localRoots =
                                        [ withCandidateSource
                                            (CandidateSourceAnnotation
                                                (CandidateHypothesis index)
                                                index 0 [] False)
                                            (ObviousProof proof
                                                (maybe emptyCandidateDependencies canonicalHypothesisDependencies
                                                    (Map.lookup (hypothesisIx index) canonicalLocalIndices)))
                                        | (index, proof) <-
                                            zip [0 :: Natural ..] localProofs
                                        ]
                                tagged <-
                                    case contextId of
                                        FocusedContextId contextPosition ->
                                            tagProofs contextPosition 0
                                                (localRoots <> importedRoots)
                                case tagged of
                                    Left failure -> pure (Left failure)
                                    Right proofs -> do
                                        State.modify'
                                            (\state ->
                                                state
                                                    { searchAvailableProofCache =
                                                        Map.insert contextId proofs
                                                            (searchAvailableProofCache
                                                                state)
                                                    })
                                        pure (Right proofs)

    tagProofs _contextPosition _sourcePosition [] = pure (Right [])
    tagProofs contextPosition sourcePosition (proof : rest) = do
        hasWork <- consumeSearchStep
        if not hasWork
            then pure focusedWorkExhausted
            else do
                remaining <-
                    tagProofs contextPosition (sourcePosition + 1) rest
                pure
                    ((withFocusedSourceKey
                        (FocusedSourceKey contextPosition sourcePosition)
                        proof :)
                        <$> remaining)

    localDefinitionIndex currentCount = \case
        ObviousImportedDefinitionView{} ->
            pure []
        ObviousLocalDefinitionView sourceIndex _kind ->
            (\current -> [(current, sourceIndex)])
                <$> currentLocalDefinitionHypothesisIx
                    environment currentCount sourceIndex

    buildImports _position [] =
        pure (Right [])
    buildImports position (ObviousImport index statement : rest) = do
        proofResult <-
            runCountedKernel
                (KernelProof.countedImportedProof
                        context index statement)
        case proofResult of
            Left failure -> pure (Left failure)
            Right proof -> Except.runExceptT do
                candidate <- State.gets (Map.lookup index . searchCanonicalImportCandidates)
                dependencies <- case candidate of
                    Nothing -> pure (importDependencies index)
                    Just (ordinal, source) -> do
                        -- Index equality only selects a candidate. Registration
                        -- checks its immutable association with this cited root.
                        Except.ExceptT (registerDefinitionImport ordinal source)
                        pure (canonicalImportDependencies ordinal index)
                remaining <- Except.ExceptT (buildImports (position + 1) rest)
                pure
                    (withCandidateSource
                        (CandidateSourceAnnotation
                            (CandidateImport index)
                            (initialHypothesisCount + position)
                            0 [] False)
                        (ObviousProof proof dependencies) : remaining)

currentLocalDefinitionHypothesisIx
    :: SearchEnvironment global
    -> Natural
    -> Natural
    -> Either (ObviousFailure global) HypothesisIx
currentLocalDefinitionHypothesisIx
        (SearchEnvironment
            _globalType _imports initialHypothesisCount _definitionViews)
        currentHypothesisCount sourceIndex = do
    unless
        (currentHypothesisCount >= initialHypothesisCount)
        (Left
            (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch
                    "obvious inference lost an external local hypothesis")))
    unless
        (sourceIndex < initialHypothesisCount)
        (Left
            (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch
                    "a proof-local canonical view has an invalid hypothesis index")))
    pure
        (hypothesisIx
            (currentHypothesisCount - initialHypothesisCount + sourceIndex))

currentHypothesisCountCounted
    :: KernelProof.ProofContext global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Natural)
currentHypothesisCountCounted context =
    -- ProofContext deliberately exposes a list.  Count its spine through the
    -- focused allowance once per consumer rather than hiding recursive length.
    countRows 0 (KernelProof.proofContextHypotheses context)
  where
    countRows count [] = pure (Right count)
    countRows count (_row : rest) = do
        available <- consumeSearchStep
        if available
            then countRows (count + 1) rest
            else pure focusedWorkExhausted

projectedChildren
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) [ObviousProof global])
projectedChildren environment context source = do
    exposed <- exposeProof environment context source
    case exposed of
        Left failure -> pure (Left failure)
        Right prepared -> projectedChildrenFromExposed context prepared

projectedChildrenFromExposed
    :: Eq global
    => KernelProof.ProofContext global
    -> ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) [ObviousProof global])
projectedChildrenFromExposed context source@(ObviousProof built _imports) =
    case splitScopedConjunction (KernelProof.builtProofStatement built) of
        Nothing -> pure (Right [])
        Just (left, right) -> project (scopedCoreTerm left) (scopedCoreTerm right)
  where
    project left right = case obviousProofSourceKey source of
            Nothing -> build left right
            Just sourceKey -> do
                hasWork <- consumeSearchStep
                if not hasWork
                    then pure focusedWorkExhausted
                    else do
                        cached <- State.gets
                            (Map.lookup sourceKey . searchProjectionCache)
                        case cached of
                            Just children -> pure (Right children)
                            Nothing -> do
                                projected <- build left right
                                case projected of
                                    Left failure -> pure (Left failure)
                                    Right children -> do
                                        tagged <- tagChildren children
                                        case tagged of
                                            Left failure -> pure (Left failure)
                                            Right stable -> do
                                                State.modify' (\state -> state
                                                    { searchProjectionCache =
                                                        Map.insert sourceKey stable
                                                            (searchProjectionCache state)
                                                    })
                                                pure (Right stable)

    tagChildren [] = pure (Right [])
    tagChildren (child : rest) = do
        tagged <- tagDerivedSource child
        case tagged of
            Left failure -> pure (Left failure)
            Right stable -> fmap (fmap (stable :)) (tagChildren rest)

    build left right = runCountedKernel do
        leftBuilt <- KernelProof.countedConjunctionLeftProof context left right built
        rightBuilt <- KernelProof.countedConjunctionRightProof context left right built
        pure [projectCandidateProof leftBuilt source, projectCandidateProof rightBuilt source]

-- Keys describe checked proof operations, independently of diagnostic labels.
-- A fresh derived key cannot collide with an original context/source row.
tagDerivedSource
    :: ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (ObviousProof global))
tagDerivedSource proof = do
    hasWork <- consumeSearchStep
    if not hasWork
        then pure focusedWorkExhausted
        else do
            next <- State.gets searchNextDerivedSourceId
            State.modify' (\state -> state {searchNextDerivedSourceId = next + 1})
            pure (Right (withFocusedSourceKey (FocusedDerivedSourceKey next) proof))

projectCandidateProof
    :: KernelProof.BuiltProof global
    -> ObviousProof global
    -> ObviousProof global
projectCandidateProof built source =
    case obviousProofCandidateSource source of
        Nothing -> deriveCandidateProof built source
        Just (CandidateSourceAnnotation base sourceOrder projectionDepth
                factDefinitions factDefinitionsTruncated) ->
            withCandidateSource
                (CandidateSourceAnnotation
                    base sourceOrder (projectionDepth + 1)
                    factDefinitions factDefinitionsTruncated)
                (deriveCandidateProof built source)

deriveCandidateProofWithDependencies
    :: KernelProof.BuiltProof global
    -> CandidateDependencies
    -> ObviousProof global
    -> ObviousProof global
deriveCandidateProofWithDependencies built dependencies source =
    case obviousProofCandidateSource source of
        Nothing -> ObviousProof built dependencies
        Just candidateSource ->
            withCandidateSource candidateSource (ObviousProof built dependencies)

withFactDefinitionOccurrence
    :: Natural
    -> ObviousProof global
    -> ObviousProof global
withFactDefinitionOccurrence ordinal proof =
    case obviousProofCandidateSource proof of
        Nothing -> proof
        Just (CandidateSourceAnnotation base sourceOrder projectionDepth
                occurrences truncated) ->
            let (retained, nowTruncated) =
                    retainCandidateLineage ordinal occurrences truncated
            in withCandidateSource
                (CandidateSourceAnnotation
                    base sourceOrder projectionDepth retained nowTruncated)
                proof

retainCandidateLineage
    :: Natural
    -> [Natural]
    -> Bool
    -> ([Natural], Bool)
retainCandidateLineage ordinal retained truncated
    | length retained < candidateDefinitionLineageLimit =
        (retained <> [ordinal], truncated)
    | otherwise = (retained, True)

candidateDefinitionLineageLimit :: Int
candidateDefinitionLineageLimit = 4

data AvailableSourceCursor global
    = AvailableNext ![ObviousProof global]
    | AvailableDescend !(ObviousProof global) ![ObviousProof global]

data AvailableSourceStep global
    = AvailableSourceFinished
    | AvailableSourcePending !(AvailableSourceCursor global)
    | AvailableSourceFound !(ObviousProof global) !(AvailableSourceCursor global)

-- Inspect a source before asking to expose its children. A consumer that has
-- found its proof need not construct any further projections.
advanceAvailableSource
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> AvailableSourceCursor global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (AvailableSourceStep global))
advanceAvailableSource environment context = \case
    AvailableNext [] -> pure (Right AvailableSourceFinished)
    AvailableNext (source : rest) ->
        pure (Right (AvailableSourceFound source (AvailableDescend source rest)))
    AvailableDescend source rest -> do
        children <- projectedChildren environment context source
        pure (fmap (AvailableSourcePending . AvailableNext . (<> rest)) children)

data ExactStep global
    = ExactFinished !(Maybe (ObviousFailure global))
    | ExactFound !(ObviousProof global) !(ExactStep global)
    | ExactPending !(ExactCursor global)

data ExactCursor global
    = ExactCursor !ExactConversionPolicy !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) ![ObviousProof global]
        ![(Conversion.ConversionLimit, ExactConversionCandidate global)]
    | ExactConvert !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) ![ObviousProof global]
        ![(Conversion.ConversionLimit, ExactConversionCandidate global)]
        !(ExactConversionCandidate global)
    | ExactRetry !(Maybe (ObviousFailure global))
        ![(Conversion.ConversionLimit, ExactConversionCandidate global)]

-- Retain the checked comparison when conversion becomes schedulable. Resuming
-- this candidate does not repeat source discovery, identity or diagnostics.
data ExactCandidateStep global
    = ExactCandidateDone !(Attempt global)
    | ExactCandidateNeedsConversion !(ExactConversionCandidate global)

data ExactConversionCandidate global = ExactConversionCandidate
    !(KernelProof.BuiltProof global) !CandidateDependencies
    !(Maybe (CandidateSeed global)) !Natural !CandidateStructuralDifference

startExactAttempt
    :: ExactConversionPolicy
    -> ScopedCheckedCore global
    -> [ObviousProof global]
    -> State (ObviousSearchState global) (ExactStep global)
startExactAttempt policy target available =
    focusedObligationHead (scopedCoreTerm target) >>= \case
        Left failure -> pure (ExactFinished (Just failure))
        Right discriminator -> pure (continueExact policy discriminator Nothing available)

continueExact
    :: ExactConversionPolicy
    -> FocusedObligationHead global
    -> Maybe (ObviousFailure global)
    -> [ObviousProof global]
    -> ExactStep global
continueExact policy discriminator failure available =
    pendingExact policy discriminator failure available []

pendingExact
    :: ExactConversionPolicy -> FocusedObligationHead global
    -> Maybe (ObviousFailure global) -> [ObviousProof global]
    -> [(Conversion.ConversionLimit, ExactConversionCandidate global)] -> ExactStep global
pendingExact _policy _discriminator failure [] deferred =
    retryExact failure (reverse deferred)
pendingExact policy discriminator failure available deferred =
    ExactPending (ExactCursor policy discriminator failure available deferred)

retryExact :: Maybe (ObviousFailure global)
    -> [(Conversion.ConversionLimit, ExactConversionCandidate global)] -> ExactStep global
retryExact failure [] = ExactFinished failure
retryExact failure deferred = ExactPending (ExactRetry failure deferred)

advanceExactAttempt
    :: Ord global
    => CandidateObservationScope
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> ExactCursor global
    -> State (ObviousSearchState global) (ExactStep global)
advanceExactAttempt observation context target = \case
    ExactCursor policy discriminator firstFailure available deferred -> case available of
        [] -> pure (pendingExact policy discriminator firstFailure [] deferred)
        proof : rest -> prepareExactCandidate policy observation target discriminator proof >>= \case
            ExactCandidateDone result -> pure
                (following (\failure -> pendingExact policy discriminator failure rest deferred) firstFailure result)
            ExactCandidateNeedsConversion candidate -> pure
                (ExactPending (ExactConvert discriminator firstFailure rest deferred candidate))
    ExactConvert discriminator firstFailure rest deferred candidate@(ExactConversionCandidate built _ _ _ _) -> do
        prepared <- runPreparedKernel (KernelProof.countedConversionProof context built target)
        case prepared of
            NeedsMoreEffort offered -> pure (pendingExact ConvertExactCandidates discriminator firstFailure
                rest ((offered, candidate) : deferred))
            PreparationFinished result -> following
                    (\failure -> pendingExact ConvertExactCandidates discriminator failure rest deferred) firstFailure
                <$> finishExactConversion candidate result
    ExactRetry firstFailure [] -> pure (retryExact firstFailure [])
    ExactRetry firstFailure ((offered, candidate) : rest) -> do
        pool <- getConversionPool
        -- The first slice was below the production ceiling. If other tasks
        -- have spent the remaining difference, retrying cannot make progress.
        if Conversion.conversionPoolAmount pool <= Conversion.conversionLimitAmount offered
            then pure (retryExact (firstFailure <|> Just
                (ObviousResourceExhausted ObviousConversionPoolLimit)) rest)
            else following (\failure -> retryExact failure rest) firstFailure
                <$> convertExactCandidate context target candidate
  where
    following next firstFailure = \case
        AttemptNotApplicable -> next firstFailure
        AttemptFailed failure | isConversionLimit failure -> next (firstFailure <|> Just failure)
        AttemptSucceeded proof -> ExactFound proof (next firstFailure)
        AttemptFailed failure -> ExactFinished (Just failure)

-- Projection and falsity searches select a single source here. They share
-- the candidate operation without draining an additional source collection.
exactCandidateAttempt
    :: Ord global
    => ExactConversionPolicy
    -> CandidateObservationScope
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> ObviousProof global
    -> State (ObviousSearchState global) (Attempt global)
exactCandidateAttempt policy observation context target proof =
    focusedObligationHead (scopedCoreTerm target) >>= \case
        Left failure -> pure (AttemptFailed failure)
        Right discriminator -> inspectExactCandidate policy observation context target discriminator proof

inspectExactCandidate
    :: Ord global
    => ExactConversionPolicy
    -> CandidateObservationScope
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> FocusedObligationHead global
    -> ObviousProof global
    -> State (ObviousSearchState global) (Attempt global)
inspectExactCandidate policy observation context target discriminator proof =
    prepareExactCandidate policy observation target discriminator proof >>= \case
        ExactCandidateDone result -> pure result
        ExactCandidateNeedsConversion candidate -> convertExactCandidate context target candidate

prepareExactCandidate
    :: Ord global
    => ExactConversionPolicy
    -> CandidateObservationScope
    -> ScopedCheckedCore global
    -> FocusedObligationHead global
    -> ObviousProof global
    -> State (ObviousSearchState global) (ExactCandidateStep global)
prepareExactCandidate policy observation target targetDiscriminator
        proof@(ObviousProof built dependencies) = do
    sourceDiscriminator <- focusedObligationHead
        (scopedCoreTerm (KernelProof.builtProofStatement built))
    case sourceDiscriminator of
        Left failure -> done (AttemptFailed failure)
        Right discriminator -> do
            let sourceStatement = KernelProof.builtProofStatement built
            candidate <- beginCandidate observation (exactCandidateView proof) sourceStatement proof
            if not (possiblyConvertibleFocusedHeads discriminator targetDiscriminator)
                then do
                    traverse_ (\seed -> recordCandidateOutcome seed
                        (ComparisonRejected SyntacticMismatch) 0 Nothing Nothing) candidate
                    done AttemptNotApplicable
                else scopedIdentityWithObservation sourceStatement target >>= \case
                    Left failure -> done (AttemptFailed failure)
                    Right (CountedIdentical, progress) ->
                        ExactCandidateDone . AttemptSucceeded <$> candidateSucceeded candidate progress Nothing proof
                    Right (CountedDifferent difference, progress) -> do
                        let (mismatch, structuralDifference) = candidateDifference difference
                        traverse_ (\seed -> recordCandidateOutcome seed
                            (ComparisonRejected mismatch) progress (Just structuralDifference) Nothing) candidate
                        pure (if policy == DeferExactCandidateConversion
                            then ExactCandidateDone AttemptNotApplicable
                            else ExactCandidateNeedsConversion
                                (ExactConversionCandidate built dependencies candidate progress structuralDifference))
  where
    done = pure . ExactCandidateDone

convertExactCandidate
    :: Ord global
    => KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> ExactConversionCandidate global
    -> State (ObviousSearchState global) (Attempt global)
convertExactCandidate context target candidate@(ExactConversionCandidate built _ _ _ _) =
    conversionProof context built target >>= finishExactConversion candidate

finishExactConversion
    :: Ord global
    => ExactConversionCandidate global
    -> Either (ObviousFailure global) (KernelProof.BuiltProof global)
    -> State (ObviousSearchState global) (Attempt global)
finishExactConversion (ExactConversionCandidate _built dependencies candidate progress difference) = \case
    Right result ->
        AttemptSucceeded <$> candidateSucceeded candidate (progress + 1)
            (Just difference) (ObviousProof result dependencies)
    Left (ObviousIntegrityFailure KernelProof.ProofConversionNotConvertible) -> do
        traverse_ (\seed -> recordCandidateOutcome seed
            (ComparisonRejected ConversionMismatch) (progress + 1)
            (Just difference) Nothing) candidate
        pure AttemptNotApplicable
    Left failure -> pure (AttemptFailed failure)

exactCandidateView :: ObviousProof global -> CandidateComparisonView
exactCandidateView proof = case obviousProofCandidateSource proof of
    Just (CandidateSourceAnnotation _base _sourceOrder projectionDepth _factDefinitions _truncated)
        | projectionDepth > 0 -> CandidateProjectedView projectionDepth
    _ -> CandidateDirectView

data ProjectionStep global
    = ProjectionFinished !(Attempt global)
    | ProjectionFound !(ObviousProof global) !(ProjectionStep global)
    | ProjectionPending !(ProjectionCursor global)

data ProjectionCursor global = ProjectionCursor
    !(Maybe (ObviousFailure global)) !(ProjectionScan global) !(Seq (ProjectionScan global))

data ProjectionScan global
    = ProjectionRoots ![ObviousProof global]
    | ProjectionCompare ![ObviousProof global] ![ObviousProof global]
    | ProjectionDescend !(ObviousProof global) ![ObviousProof global] ![ObviousProof global]
    | ProjectionExpose !(SourceExposureStep global) ![ObviousProof global] ![ObviousProof global]
    | ProjectionConvert !(ExactConversionCandidate global) !(ObviousProof global)
        ![ObviousProof global] ![ObviousProof global]
    | ProjectionRetry !Conversion.ConversionLimit !(ExactConversionCandidate global)

projectionIsDeferred :: ProjectionStep global -> Bool
projectionIsDeferred (ProjectionPending (ProjectionCursor _ scan _)) = case scan of
    ProjectionExpose exposure _ _ -> sourceExposureIsDeferred exposure
    ProjectionRetry{} -> True
    _ -> False
projectionIsDeferred _ = False

-- Roots are skipped; projections are compared before descending again. Blocked
-- exposure and conversion retain their exact inputs while this finite supplied
-- source scan continues. A successful cheap projection can finish the request
-- without first paying for an unrelated projection's full conversion.
advanceProjectionAttempt
    :: Ord global
    => ExactConversionPolicy -> CandidateObservationScope -> SearchEnvironment global
    -> KernelProof.ProofContext global -> ScopedCheckedCore global -> ProjectionCursor global
    -> State (ObviousSearchState global) (ProjectionStep global)
advanceProjectionAttempt policy observation environment context target (ProjectionCursor firstFailure scan deferred) = case scan of
    ProjectionRoots [] -> case Seq.viewl deferred of
        Seq.EmptyL -> pure (ProjectionFinished (maybe AttemptNotApplicable AttemptFailed firstFailure))
        pending Seq.:< rest -> pure (ProjectionPending (ProjectionCursor firstFailure pending rest))
    ProjectionRoots (root : roots) -> descend root [] roots
    ProjectionCompare [] roots -> next (ProjectionRoots roots)
    ProjectionCompare (source : rest) roots -> do
        discriminator <- focusedObligationHead (scopedCoreTerm target)
        case discriminator of
            Left failure -> failed failure
            Right headKey -> prepareExactCandidate policy observation target headKey source >>= \case
                ExactCandidateNeedsConversion candidate -> next (ProjectionConvert candidate source rest roots)
                ExactCandidateDone result -> following (ProjectionDescend source rest roots) result
    ProjectionConvert candidate@(ExactConversionCandidate built _ _ _ _) source rest roots ->
        runPreparedKernel (KernelProof.countedConversionProof context built target) >>= \case
            NeedsMoreEffort offered -> park (ProjectionRetry offered candidate) (ProjectionDescend source rest roots)
            PreparationFinished result -> finishExactConversion candidate result >>= following (ProjectionDescend source rest roots)
    ProjectionRetry offered candidate@(ExactConversionCandidate built _ _ _ _) ->
        runKernelPreparation (FullPreparation offered) (KernelProof.countedConversionProof context built target) >>= \case
                PreparationFinished result -> finishExactConversion candidate result >>= following (ProjectionRoots [])
                NeedsMoreEffort{} -> failed malformedApplicationSpine
    ProjectionDescend source rest roots -> descend source rest roots
    ProjectionExpose (SourceExposureFinished result) rest roots -> case result of
        Left failure | isConversionLimit failure -> recover failure (ProjectionCompare rest roots)
        Left failure -> failed failure
        Right exposed -> projectedChildrenFromExposed context exposed >>= \case
            Left failure -> failed failure
            Right children -> next (ProjectionCompare (children <> rest) roots)
    ProjectionExpose exposure rest roots -> advanceSourceExposure environment context exposure >>= \prepared ->
        if sourceExposureIsDeferred prepared && not (null rest && null roots)
            then park (ProjectionExpose prepared [] []) (ProjectionCompare rest roots)
            else finishExposure prepared rest roots
  where
    finishExposure prepared rest roots = case prepared of
        SourceExposureFinished{} -> advanceProjectionAttempt policy observation environment context target
            (ProjectionCursor firstFailure (ProjectionExpose prepared rest roots) deferred)
        _ -> next (ProjectionExpose prepared rest roots)
    next cursor = pure (ProjectionPending (ProjectionCursor firstFailure cursor deferred))
    recover failure cursor = pure (ProjectionPending (ProjectionCursor (firstFailure <|> Just failure) cursor deferred))
    park pending nextScan = pure (ProjectionPending (ProjectionCursor firstFailure nextScan (deferred Seq.|> pending)))
    failed = pure . ProjectionFinished . AttemptFailed
    following cursor = \case
        AttemptNotApplicable -> next cursor
        AttemptFailed failure | isConversionLimit failure -> recover failure cursor
        AttemptSucceeded proof -> ProjectionFound proof <$> next cursor
        result -> pure (ProjectionFinished result)
    descend source rest roots = do
        started <- startSourceExposure context source
        case started of
            SourceExposureFinished{} -> finishExposure started rest roots
            _ -> advanceSourceExposure environment context started >>= \prepared ->
                if sourceExposureIsDeferred prepared && not (null rest && null roots)
                    then park (ProjectionExpose prepared [] []) (ProjectionCompare rest roots)
                    else finishExposure prepared rest roots

data IntroductionScope global
    = IntroductionCurrentScope
    | IntroductionExtendedScope !FocusedContextId !(KernelProof.ProofContext global)

data IntroductionStep global
    = IntroductionFinished !(Attempt global)
    | IntroductionNeedsSupport !(ObviousProof global) !(ObviousProof global) !(ObviousProof global)
    | IntroductionAlternatives !ProofRequirement !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | IntroductionChild
        !CandidateObservationScope
        !ProofRequirement
        !(IntroductionScope global)
        !(ScopedCheckedCore global)
        !(IntroductionContinuation global)

data IntroductionContinuation global
    = IntroductionConjunction !(ConjunctionContinuation global)
    | IntroductionLeftDisjunct !(CanonicalTerm global)
    | IntroductionRightDisjunct !(CanonicalTerm global)
    | IntroductionImplication !(ScopedCheckedCore global)
    | IntroductionNegation !(ScopedCheckedCore global)
    | IntroductionUniversal !CoreType
    | IntroductionExistential !CoreType !(ScopedCheckedCore global) !(ScopedCheckedCore global)

startIntroduction
    :: ProofRequirement
    -> FocusedContextId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (IntroductionStep global)
startIntroduction requirement parentId context target = case scopedCoreTerm target of
    CTruth -> do
        result <- runCountedKernel
            (KernelProof.countedTruthIntroductionProof context)
        pure (IntroductionFinished (fromObvious emptyCandidateDependencies result))
    CAnd{} -> fromConjunctionStep <$> startConjunction requirement target
    COr{} -> do
        hasWork <- consumeSearchStep
        if not hasWork then finishedFailure (ObviousResourceExhausted ObviousFocusedWorkLimit)
            else case splitScopedDisjunction target of
                Just (left, right) -> pure (IntroductionAlternatives requirement left right)
                Nothing -> finishedFailure (ObviousIntegrityFailure
                    (KernelProof.ProofStructuralCompositionMismatch "disjunction introduction received a different head"))
    CImp premise conclusion -> beginAssumption premise conclusion
        AuxiliaryImplicationBody IntroductionImplication
    CNot proposition -> beginAssumption proposition CFalsum
        AuxiliaryNegationBody IntroductionNegation
    CForall binderType body -> do
        extendedResult <- runCountedKernel
            (KernelProof.countedExtendProofContextBinder context binderType)
        case extendedResult of
            Left failure -> finishedFailure failure
            Right (extended, _variable) -> do
                extendedId <- admitFocusedContext (FocusedBinderScope parentId binderType) extended
                bodyTarget <- checkedProposition extended body
                case (extendedId, bodyTarget) of
                    (Left failure, _) -> finishedFailure failure
                    (_, Left failure) -> finishedFailure failure
                    (Right childId, Right childTarget) -> pure (IntroductionChild
                        (SuppressAuxiliary AuxiliaryUniversalBody) AnyObviousProof
                        (IntroductionExtendedScope childId extended) childTarget
                        (IntroductionUniversal binderType))
    _ -> pure (IntroductionFinished AttemptNotApplicable)
  where
    finishedFailure = pure . IntroductionFinished . AttemptFailed

    beginAssumption premise body observation continuation = checkedProposition context premise >>= \case
        Left failure -> finishedFailure failure
        Right assumed -> do
            extendedResult <- runCountedKernel
                (KernelProof.countedExtendProofContextHypothesis context assumed)
            case extendedResult of
                Left failure -> finishedFailure failure
                Right extended -> do
                    extendedId <- admitFocusedContext (FocusedAssumptionScope parentId assumed) extended
                    bodyTarget <- checkedProposition extended body
                    case (extendedId, bodyTarget) of
                        (Left failure, _) -> finishedFailure failure
                        (_, Left failure) -> finishedFailure failure
                        (Right childId, Right childTarget) -> pure (IntroductionChild
                            (SuppressAuxiliary observation) AnyObviousProof
                            (IntroductionExtendedScope childId extended) childTarget
                            (continuation assumed))

resumeIntroduction
    :: Eq global
    => KernelProof.ProofContext global
    -> IntroductionContinuation global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (IntroductionStep global)
resumeIntroduction context continuation result = case continuation of
    IntroductionConjunction pending -> fromConjunctionStep <$> resumeConjunction pending result
    IntroductionLeftDisjunct right -> unary
        (\proof -> KernelProof.countedDisjunctionLeftProof context right proof)
    IntroductionRightDisjunct left -> unary
        (\proof -> KernelProof.countedDisjunctionRightProof context left proof)
    IntroductionImplication premise -> unary
        (\proof -> KernelProof.countedImplicationIntroductionProof context premise proof)
    IntroductionNegation proposition -> unary
        (\proof -> KernelProof.countedNegationIntroductionProof context proposition proof)
    IntroductionUniversal binderType -> unary
        (\proof -> KernelProof.countedForallIntroductionProof context binderType proof)
    IntroductionExistential binderType body witness -> unary
        (\proof -> KernelProof.countedExistentialIntroductionProof context binderType body witness proof)
  where
    failed = pure . IntroductionFinished . AttemptFailed
    finish dependencies operation = IntroductionFinished . fromObvious dependencies <$> operation
    unary construct = case result of
        Left failure -> failed failure
        Right (ObviousProof proof dependencies) -> finish dependencies
            (runCountedKernel (construct proof))

-- Candidate discovery carries no proof authority. Every offered witness owns
-- one retained body search, and ordinary introduction reconstructs its result.
data WitnessSearch global = WitnessSearch
    !CoreType !(Template.CompiledTemplate global)
    !(Seq (ScopedCheckedCore global)) !(WitnessDiscovery global)

data WitnessDiscovery global
    = WitnessEqualities ![Template.CompiledTemplate global] !(Seq (Template.CompiledTemplate global))
    | WitnessEvidence ![Template.CompiledTemplate global] ![ObviousProof global]
    | WitnessMatching !(Template.CompiledTemplate global) ![Template.CompiledTemplate global]
        ![ObviousProof global] !(TheoremMatchStep global)
    | WitnessAwaitInventory
    | WitnessInventory !(Search.Catalogue global) !Search.CatalogueTypeTerms
    | WitnessComplete

data WitnessStep global
    = WitnessPending !(WitnessSearch global)
    | WitnessOffer !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(WitnessSearch global)
    | WitnessFinished !(Attempt global)

startWitnessSearch :: ScopedCheckedCore global -> WitnessStep global
startWitnessSearch target = case Template.retainCheckedPropositionTemplate target of
    Left failure -> WitnessFinished (AttemptFailed (obviousTemplateError failure))
    Right template -> case Template.openCompiledExists template of
        Nothing -> WitnessFinished AttemptNotApplicable
        Just (binderType, body) -> WitnessPending
            (WitnessSearch binderType body Seq.empty (WitnessEqualities [body] Seq.empty))

advanceWitnessSearch
    :: Ord global
    => FocusedRequest global -> [ObviousProof global] -> WitnessSearch global
    -> State (ObviousSearchState global) (WitnessStep global)
advanceWitnessSearch request available (WitnessSearch binderType body seen discovery) = do
    work <- consumeSearchStep
    if not work then failed (ObviousResourceExhausted ObviousFocusedWorkLimit) else case discovery of
        WitnessEqualities [] leaves -> pending (WitnessEvidence (toList leaves) available)
        WitnessEqualities (current : rest) leaves ->
            case Template.splitCompiledConjunction current <|> Template.splitCompiledDisjunction current
                    <|> Template.openCompiledImplication current of
                Just (left, right) -> pending (WitnessEqualities (left : right : rest) leaves)
                Nothing -> case scopedCoreTerm (Template.compiledTemplateTerm current) of
                    CForall{} -> pending (WitnessEqualities rest leaves)
                    CExists{} -> pending (WitnessEqualities rest leaves)
                    _ -> do
                        let following = WitnessEqualities rest (leaves Seq.|> current)
                            hint = do
                                (_type, left, right) <- splitScopedEquality (Template.compiledTemplateTerm current)
                                case (scopedCoreTerm left, scopedCoreTerm right) of
                                    (CBound 0, _) -> Just right
                                    (_, CBound 0) -> Just left
                                    _ -> Nothing
                        case hint of
                            Nothing -> pending following
                            Just term -> do
                                checked <- Except.runExceptT do
                                    row <- Except.ExceptT (analyseTheoremOccurrence (focusedEnvironment request) 1 term)
                                    structural <- lift getFocusedWorkBudget
                                    let (rebased, remaining) = countedRebaseCheckedOccurrence structural row
                                    lift (putFocusedWorkBudget remaining)
                                    Except.except (first (obviousCountedFailure (\_ ->
                                        ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
                                            "existential hint rebasing contradicted its checked scope"))) rebased)
                                case checked of
                                    Left failure -> failed failure
                                    Right Nothing -> pending following
                                    Right (Just witness) -> offer witness following
        WitnessEvidence [] _facts -> pending WitnessAwaitInventory
        WitnessEvidence (_ : rest) [] -> pending (WitnessEvidence rest available)
        WitnessEvidence (leaf : rest) (fact : facts) -> do
            matched <- startTheoremMatch (focusedEnvironment request) (focusedContext request)
                leaf (obviousProofStatement fact) Template.emptyTemplateSubstitution
            pending (WitnessMatching leaf rest facts matched)
        WitnessMatching leaf rest facts step -> case step of
            TheoremMatchFinished result -> case result of
                Left failure -> failed failure
                Right (TemplateMatched substitutions _progress) ->
                    case Template.lookupTemplateSubstitution (Template.MatcherSlot 0) substitutions of
                        Just witness -> offer witness (WitnessEvidence (leaf : rest) facts)
                        Nothing -> pending (WitnessEvidence (leaf : rest) facts)
                Right _ -> pending (WitnessEvidence (leaf : rest) facts)
            _ -> advanceTheoremMatch (focusedEnvironment request) step
                >>= pending . WitnessMatching leaf rest facts
        WitnessAwaitInventory -> beginWitnessInventory request binderType >>= \case
            Left failure -> failed failure
            Right following -> pending following
        WitnessInventory catalogue cursor ->
            runWitnessCatalogue (\work' -> Search.nextCatalogueTypeTermCounted work' cursor) >>= \case
                Left failure -> failed failure
                Right Nothing -> pending WitnessComplete
                Right (Just (termId, following)) -> case Search.catalogueTerm catalogue termId of
                    Nothing -> failed (ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
                        "an existential inventory lost its original term"))
                    Just term -> offer (Search.catalogueTermValue term) (WitnessInventory catalogue following)
        WitnessComplete -> pure (WitnessFinished AttemptNotApplicable)
  where
    failed = pure . WitnessFinished . AttemptFailed
    pending = pure . WitnessPending . WitnessSearch binderType body seen
    duplicate witness = scan (Seq.viewl seen)
      where
        scan Seq.EmptyL = pure (Right False)
        scan (prior Seq.:< rest) = scopedIdentity witness prior >>= \case
            Right False -> scan (Seq.viewl rest)
            other -> pure other
    offer witness following = duplicate witness >>= \case
        Left failure -> failed failure
        Right True -> pending following
        Right False -> do
            policy <- State.gets (policyWitnesses . searchPolicy)
            attempts <- State.gets searchWitnessAttempts
            case policy of
                WitnessesDisabled -> pure (WitnessFinished AttemptNotApplicable)
                ExistingWitnesses prefix total
                    | fromIntegral (Seq.length seen) >= prefix || attempts >= total -> do
                        State.modify' (\state -> state {searchWitnessesDeferred = True})
                        pure (WitnessFinished AttemptNotApplicable)
                    | otherwise -> do
                        State.modify' (\state -> state {searchWitnessAttempts = attempts + 1})
                        instantiated <- closeFocusedTemplate body
                            (Template.insertTemplateSubstitution (Template.MatcherSlot 0) witness Template.emptyTemplateSubstitution)
                        case instantiated of
                            Left failure -> failed failure
                            Right Template.TemplateOpen{} -> failed (ObviousIntegrityFailure
                                (KernelProof.ProofStructuralCompositionMismatch "a complete existential witness left its binder open"))
                            Right (Template.TemplateClosed target) -> pure (WitnessOffer witness target
                                (WitnessSearch binderType body (seen Seq.|> witness) following))

runWitnessCatalogue
    :: (Word -> (Either Search.CatalogueError value, Word))
    -> State (ObviousSearchState global) (Either (ObviousFailure global) value)
runWitnessCatalogue operation = do
    work <- getFocusedWorkBudget
    let (result, remaining) = operation work
    putFocusedWorkBudget remaining
    pure (first (\case
        Search.CatalogueWorkExhausted -> ObviousResourceExhausted ObviousFocusedWorkLimit
        failure -> ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
            ("read-only witness inventory failed: " <> fromString (show failure)))) result)

beginWitnessInventory
    :: Eq global
    => FocusedRequest global -> CoreType
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (WitnessDiscovery global))
beginWitnessInventory request coreType
    | not (eligibleFocusedGround request) = pure (Right WitnessComplete)
    | otherwise = Except.runExceptT do
        possible <- startFocusedGround request
        case possible of
            GroundStartPending -> pure WitnessAwaitInventory
            GroundStartUnavailable -> pure WitnessComplete
            GroundStarted (FocusedGroundQuery query eligibility _views) -> do
                OwnedGroundQuery _scope _typing _domainScope frozen _status _support _inputs <- lookupGroundQuery query
                case frozen of
                    Nothing -> scopeAdvanceGround query >>= \case
                        GroundQueryPending -> pure WitnessAwaitInventory
                        GroundQueryBlocked _statistics failure -> Except.throwE (mapRefutationFailure failure)
                        GroundQueryFinished _statistics (Left failure) -> Except.throwE (mapRefutationFailure failure)
                        GroundQueryFinished _statistics (Right _) -> scopeIntegrity "a witness domain completed without freezing"
                    Just domain -> do
                        let catalogue = Refutation.frozenDomainCatalogue domain
                        typeId <- Except.ExceptT (runWitnessCatalogue (\work -> Search.findCatalogueTypeCounted work catalogue coreType))
                        case typeId of
                            Nothing -> pure WitnessComplete
                            Just identifier -> do
                                familyIndex <- case eligibility of
                                    SeedEligible (GroundFamilyId index) -> pure index
                                    ExistingFamily _use (GroundFamilyId index) -> pure index
                                    FocusedOnly -> scopeIntegrity "a focused-only witness requested an inventory"
                                families <- State.gets (ownedGroundFamilies . searchGroundOwner)
                                family <- maybe (scopeIntegrity "a witness inventory lost its family") pure (Seq.lookup familyIndex families)
                                cursor <- case Map.lookup identifier (familyTypeInventories family) of
                                    Just existing -> pure existing
                                    Nothing -> do
                                        collected <- Except.ExceptT (runWitnessCatalogue (\work ->
                                            Search.catalogueTypeTermsCounted work catalogue identifier))
                                        State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                                            {ownedGroundFamilies = Seq.adjust'
                                                (\current -> current {familyTypeInventories = Map.insert identifier collected
                                                    (familyTypeInventories current)}) familyIndex
                                                (ownedGroundFamilies (searchGroundOwner state))}})
                                        pure collected
                                pure (WitnessInventory catalogue cursor)

data ConjunctionContinuation global
    = ConjunctionLeft !ProofRequirement !(ScopedCheckedCore global) !(Maybe (ConjunctionContinuation global))
    | ConjunctionRight !ProofRequirement !(ObviousProof global) !(Maybe (ConjunctionContinuation global))
    | ConjunctionGroup !(ScopedCheckedCore global) !(ConjunctionContinuation global)

data ConjunctionStep global
    = ConjunctionFinished !(Attempt global)
    | ConjunctionChild !ProofRequirement !(ScopedCheckedCore global) !(ConjunctionContinuation global)
    | ConjunctionNeedsSupport !(ObviousProof global) !(ObviousProof global) !(ObviousProof global)

startConjunction
    :: ProofRequirement -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (ConjunctionStep global)
startConjunction = beginConjunction Nothing

beginConjunction
    :: Maybe (ConjunctionContinuation global) -> ProofRequirement -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (ConjunctionStep global)
beginConjunction parent requirement conjunction = do
    hasWork <- consumeSearchStep
    if not hasWork
        then pure (ConjunctionFinished (AttemptFailed (ObviousResourceExhausted ObviousFocusedWorkLimit)))
        else case splitScopedConjunction conjunction of
            Nothing -> pure (ConjunctionFinished (AttemptFailed (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch
                    "conjunction introduction received a different checked head"))))
            Just (left, right) -> conjunctionComponent left (ConjunctionLeft requirement right parent)

-- Search leaves first, retaining each internal group as a fallback. A supplied
-- theorem may prove a whole group whose individual conjuncts do not match its
-- conclusion. Successful leaf assembly needs no search for those groups.
conjunctionComponent
    :: ScopedCheckedCore global -> ConjunctionContinuation global
    -> State (ObviousSearchState global) (ConjunctionStep global)
conjunctionComponent target continuation = case scopedCoreTerm target of
    CAnd{} -> beginConjunction (Just (ConjunctionGroup target continuation)) AnyObviousProof target
    _ -> pure (ConjunctionChild AnyObviousProof target continuation)

resumeConjunction
    :: ConjunctionContinuation global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (ConjunctionStep global)
resumeConjunction continuation (Left failure)
    | isTerminalFocusedFailure failure = pure (ConjunctionFinished (AttemptFailed failure))
    | otherwise = case continuation of
        ConjunctionGroup target outer -> pure (ConjunctionChild AnyObviousProof target outer)
        ConjunctionLeft _ _ parent -> unwind parent
        ConjunctionRight _ _ parent -> unwind parent
  where
    unwind Nothing = pure (ConjunctionFinished (AttemptFailed failure))
    unwind (Just parent) = resumeConjunction parent (Left failure)
resumeConjunction (ConjunctionGroup _ outer) (Right proof) = resumeConjunction outer (Right proof)
resumeConjunction (ConjunctionLeft requirement right parent) (Right proof) =
    conjunctionComponent right (ConjunctionRight requirement proof parent)
resumeConjunction (ConjunctionRight requirement left parent) (Right right) =
    buildConjunction left right >>= \case
        AttemptSucceeded proof | not (satisfiesRequirement requirement proof) ->
            pure (ConjunctionNeedsSupport proof left right)
        AttemptSucceeded proof | Just continuation <- parent -> resumeConjunction continuation (Right proof)
        result -> pure (ConjunctionFinished result)

buildConjunction
    :: ObviousProof global -> ObviousProof global
    -> State (ObviousSearchState global) (Attempt global)
buildConjunction (ObviousProof left leftDependencies) (ObviousProof right rightDependencies) = do
    combined <- runCountedKernel
        (KernelProof.countedConjunctionIntroductionProof left right)
    case combined of
        Left failure -> pure (AttemptFailed failure)
        Right built -> do
            dependencies <- combineCandidateDependencies leftDependencies rightDependencies
            pure (either AttemptFailed (AttemptSucceeded . ObviousProof built) dependencies)

fromConjunctionStep :: ConjunctionStep global -> IntroductionStep global
fromConjunctionStep = \case
    ConjunctionFinished result -> IntroductionFinished result
    ConjunctionChild requirement target continuation -> IntroductionChild
        (SuppressAuxiliary AuxiliaryIntroductionComponent) requirement IntroductionCurrentScope target
        (IntroductionConjunction continuation)
    ConjunctionNeedsSupport proof left right -> IntroductionNeedsSupport proof left right

data EqualityStep global
    = EqualityFinished !(Attempt global)
    | EqualityFound !(ObviousProof global) !(EqualityStep global)
    | EqualityPending !(EqualityCursor global)

data EqualityCursor global
    = EqualityCompare !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        ![ObviousProof global]
    | EqualityReflexive !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(Maybe (EqualityCursor global))
    | EqualityCollect !ProofRequirement !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(EqualityGraphStep global)
    | EqualityTarget !(ScopedCheckedCore global) !(Maybe (EqualityCursor global)) !(EqualityProofStep global)
    | EqualityConvert !PreparationEffort !(ScopedCheckedCore global) !(ObviousProof global) !(Maybe (EqualityCursor global))

equalityIsDeferred :: EqualityStep global -> Bool
equalityIsDeferred (EqualityPending (EqualityConvert effort _ _ _)) = preparationIsDeferred effort
equalityIsDeferred (EqualityPending (EqualityTarget _ _ step)) = equalityProofIsDeferred step
equalityIsDeferred _ = False

startEquality :: ScopedCheckedCore global -> [ObviousProof global] -> EqualityStep global
startEquality target available = case splitScopedEquality target of
    Nothing -> EqualityFinished AttemptNotApplicable
    Just (_operandType, left, right) -> EqualityPending (EqualityCompare target left right available)

advanceEquality
    :: Ord global
    => EqualityProducer -> ExactConversionPolicy
    -> ProofRequirement
    -> SearchEnvironment global
    -> KernelProof.ProofContext global
    -> EqualityCursor global
    -> State (ObviousSearchState global) (EqualityStep global)
advanceEquality equationProducer policy requirement environment context = \case
    EqualityCompare target left right available -> (case policy of
        ConvertExactCandidates -> convertible environment left right
        DeferExactCandidateConversion -> scopedIdentity left right) >>= \case
        Left failure -> failed failure
        Right True -> next (EqualityReflexive target left
            (if requirement == MustUseCanonicalDefinition
                then Just (collect MustUseCanonicalDefinition target left right available) else Nothing))
        Right False -> next (collect AnyObviousProof target left right available)
    EqualityReflexive target left following -> runCountedKernel
            (KernelProof.countedEqualityReflexivityProof context left) >>= \case
        Left failure -> failed failure
        Right proof -> next (EqualityConvert SmallPreparation target (ObviousProof proof emptyCandidateDependencies) following)
    EqualityCollect demanded target left right (EqualityGraphPending cursor) ->
        advanceEqualityGraph policy environment context cursor >>= \case
            Left failure -> failed failure
            Right step -> next (EqualityCollect demanded target left right step)
    EqualityCollect demanded target left right (EqualityGraphFinished graph) -> do
        let producer = if policy == ConvertExactCandidates then equationProducer else EvidenceOnly
            following = if demanded == AnyObviousProof && requirement == MustUseCanonicalDefinition
                then Just (EqualityTarget target Nothing
                    (startEqualityProof producer policy MustUseCanonicalDefinition graph left right)) else Nothing
        next (EqualityTarget target following (startEqualityProof producer policy demanded graph left right))
    EqualityTarget target following (EqualityProofPending input action continuations) ->
        advanceEqualityProof environment context input action continuations >>= next . EqualityTarget target following
    EqualityTarget _ _ EqualityProofDemand{} -> failed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "equality demand bypassed its focused owner"))
    EqualityTarget _ _ EqualityCompletionDemand{} -> failed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "argument completion bypassed its focused owner"))
    EqualityTarget _target _following (EqualityProofFinished (Left failure)) -> failed failure
    EqualityTarget _target _following (EqualityProofFinished (Right Nothing)) -> pure (EqualityFinished AttemptNotApplicable)
    EqualityTarget target following (EqualityProofFinished (Right (Just proof))) ->
        next (EqualityConvert SmallPreparation target proof following)
    EqualityConvert effort target source@(ObviousProof proof dependencies) following ->
        runKernelPreparation effort (KernelProof.countedConversionProof context proof target) >>= \case
            NeedsMoreEffort offered -> next (EqualityConvert (FullPreparation offered) target source following)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right built) -> pure (EqualityFound (ObviousProof built dependencies)
                (maybe (EqualityFinished AttemptNotApplicable) EqualityPending following))
  where
    failed = pure . EqualityFinished . AttemptFailed
    next = pure . EqualityPending
    collect demanded target left right available = EqualityCollect demanded target left right
        (EqualityGraphPending (EqualityGraphSources emptyFocusedEqualityGraph available))

data EqualityGraphStep global
    = EqualityGraphFinished !(FocusedEqualityGraph global)
    | EqualityGraphPending !(EqualityGraphCursor global)

data EqualityGraphCursor global
    = EqualityGraphSources !(FocusedEqualityGraph global) ![ObviousProof global]
    | EqualityGraphExpose !(FocusedEqualityGraph global) !(ObviousProof global) ![ObviousProof global]
    | EqualityGraphAdmit !(FocusedEqualityGraph global) !(ObviousProof global) ![ObviousProof global]
    | EqualityGraphProject !(FocusedEqualityGraph global) !(ObviousProof global) ![ObviousProof global]

emptyFocusedEqualityGraph :: FocusedEqualityGraph global
emptyFocusedEqualityGraph =
    FocusedEqualityGraph Seq.empty Seq.empty Map.empty Map.empty

advanceEqualityGraph
    :: Ord global
    => ExactConversionPolicy
    -> SearchEnvironment global
    -> KernelProof.ProofContext global
    -> EqualityGraphCursor global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (EqualityGraphStep global))
advanceEqualityGraph policy environment context = \case
    EqualityGraphSources graph [] -> pure (Right (EqualityGraphFinished graph))
    EqualityGraphSources graph (source : rest) -> do
        hasWork <- consumeSearchStep
        pure (if hasWork then Right (EqualityGraphPending (EqualityGraphExpose graph source rest))
            else focusedWorkExhausted)
    EqualityGraphExpose graph source rest -> case policy of
        -- Direct premise composition consumes entered equality/conjunction
        -- evidence only. It does not expose arbitrary source heads or ask for
        -- recursive premises. The general worker retains those opportunities.
        DeferExactCandidateConversion -> pure (Right (EqualityGraphPending (EqualityGraphAdmit graph source rest)))
        ConvertExactCandidates -> do
            exposed <- exposeProof environment context source
            pure (fmap (\proof -> EqualityGraphPending (EqualityGraphAdmit graph proof rest)) exposed)
    EqualityGraphAdmit graph source rest -> do
        admitted <- addFocusedEqualityFromExposed graph source
        pure (fmap (\updated -> EqualityGraphPending (EqualityGraphProject updated source rest)) admitted)
    EqualityGraphProject graph source rest -> do
        children <- projectedChildrenFromExposed context source
        pure (fmap (\projected -> EqualityGraphPending (EqualityGraphSources graph (projected <> rest))) children)

addFocusedEqualityFromExposed
    :: Ord global
    => FocusedEqualityGraph global
    -> ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (FocusedEqualityGraph global))
addFocusedEqualityFromExposed graph proof =
    case splitScopedEquality (obviousProofStatement proof) of
        Nothing -> pure (Right graph)
        Just (_operandType, left, right) -> do
            leftInterned <- internFocusedEqualityTerm graph left
            case leftInterned of
                Left failure -> pure (Left failure)
                Right (withLeft, leftId) -> do
                    rightInterned <- internFocusedEqualityTerm withLeft right
                    case rightInterned of
                        Left failure -> pure (Left failure)
                        Right (withRight, rightId) -> do
                            forward <- admitFocusedEqualityEdge withRight
                                leftId rightId FocusedEqualityForward proof
                            case forward of
                                Left failure -> pure (Left failure)
                                Right withForward -> admitFocusedEqualityEdge withForward
                                    rightId leftId FocusedEqualityReverse proof

internFocusedEqualityTerm
    :: Ord global
    => FocusedEqualityGraph global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (FocusedEqualityGraph global, FocusedEqualityTermId))
internFocusedEqualityTerm
        graph@(FocusedEqualityGraph terms edges outgoing buckets)
        candidate = do
    found <- lookupFocusedEqualityTermWithHead graph candidate
    case found of
        Left failure -> pure (Left failure)
        Right (_headKey, Just termId) -> pure (Right (graph, termId))
        Right (headKey, Nothing) -> do
            admitted <- consumeSearchStep
            if not admitted
                then pure focusedWorkExhausted
                else
                    let termId = FocusedEqualityTermId (Seq.length terms)
                    in pure
                        (Right
                            ( FocusedEqualityGraph
                                (terms Seq.|> candidate)
                                edges outgoing
                                (Map.insertWith
                                    (\new old -> old <> new)
                                    headKey
                                    (Seq.singleton termId)
                                    buckets)
                            , termId
                            ))

lookupFocusedEqualityTerm
    :: Ord global
    => FocusedEqualityGraph global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (Maybe FocusedEqualityTermId))
lookupFocusedEqualityTerm graph candidate =
    fmap (fmap snd) (lookupFocusedEqualityTermWithHead graph candidate)

lookupFocusedEqualityTermWithHead
    :: Ord global
    => FocusedEqualityGraph global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            ( (CoreType, FocusedObligationHead global)
            , Maybe FocusedEqualityTermId
            ))
lookupFocusedEqualityTermWithHead
        (FocusedEqualityGraph terms _edges _outgoing buckets)
        candidate = do
    headResult <- focusedObligationHead (scopedCoreTerm candidate)
    case headResult of
        Left failure -> pure (Left failure)
        Right headKey ->
            scan
                (scopedCoreType candidate, headKey)
                (Map.findWithDefault
                    Seq.empty
                    (scopedCoreType candidate, headKey)
                    buckets)
  where
    scan headKey remaining =
        case Seq.viewl remaining of
            Seq.EmptyL -> pure (Right (headKey, Nothing))
            termId@(FocusedEqualityTermId position) Seq.:< rest -> do
                visited <- consumeSearchStep
                if not visited
                    then pure focusedWorkExhausted
                    else
                        case Seq.lookup position terms of
                            Nothing -> pure (Left corruptGraph)
                            Just existing -> do
                                same <- scopedIdentity existing candidate
                                case same of
                                    Left failure -> pure (Left failure)
                                    Right True ->
                                        pure (Right (headKey, Just termId))
                                    Right False -> scan headKey rest

admitFocusedEqualityEdge
    :: FocusedEqualityGraph global
    -> FocusedEqualityTermId
    -> FocusedEqualityTermId
    -> FocusedEqualityDirection
    -> ObviousProof global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (FocusedEqualityGraph global))
admitFocusedEqualityEdge
        (FocusedEqualityGraph terms edges outgoing buckets)
        source target direction proof = do
    admitted <- consumeSearchStep
    if not admitted
        then pure focusedWorkExhausted
        else
            let edgeId =
                    FocusedEqualityEdgeId (Seq.length edges)
                edge =
                    FocusedEqualityEdge
                        source target direction proof
                updatedOutgoing =
                    Map.alter
                        (Just . maybe
                            (Seq.singleton edgeId)
                            (Seq.|> edgeId))
                        source outgoing
            in pure
                (Right
                    (FocusedEqualityGraph
                        terms (edges Seq.|> edge) updatedOutgoing buckets))

data EqualityProducer = EvidenceOnly | SuppliedEquations
    deriving stock (Eq)

data EqualityProofInput global = EqualityProofInput
    !ExactConversionPolicy !(FocusedEqualityGraph global) !Bool !EqualityProducer

data EqualityOperands global
    = RootEqualityOperands !EqualityDemandSite !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | OccurrenceEqualityOperands !EqualityDemandSite !(CheckedOccurrence global) !(CheckedOccurrence global)

-- Representation is not permission: both root and retained occurrence pairs
-- carry the actual congruence position through endpoints and support retries.
data EqualityDemandSite = ConcreteEndpoint | FunctionArgument
    deriving stock (Eq)

data ApplicationEqualityOperands global = ApplicationEqualityOperands
    !(CheckedOccurrence global) !(CheckedOccurrence global)
    !(CheckedOccurrence global) !(CheckedOccurrence global)
    !(CheckedOccurrence global) !(CheckedOccurrence global)

data EqualityProofStep global
    = EqualityProofFinished !(Either (ObviousFailure global) (Maybe (ObviousProof global)))
    | EqualityProofDemand !(EqualityProofInput global) !ProofRequirement !(EqualityOperands global)
        ![EqualityProofContinuation global]
    | EqualityCompletionDemand !(EqualityProofInput global) !ProofRequirement !(EqualityOperands global)
        ![EqualityProofContinuation global]
    | EqualityProofPending !(EqualityProofInput global) !(EqualityProofAction global)
        ![EqualityProofContinuation global]

data EqualityProofAction global
    = EqualityProofPath !ProofRequirement !(EqualityOperands global)
        !(EqualityPathInput global) !(EqualityPathCursor global)
    | EqualityProofCongruence !ProofRequirement !(EqualityOperands global)
    | EqualityProofSupport !(EqualitySupportRecipe global)
    | EqualityProofJoin !PreparationEffort !(ApplicationEqualityOperands global) !(ObviousProof global) !(ObviousProof global)
        !(Maybe (EqualitySupportRecipe global))
    | EqualityProofExpected !(CheckedOccurrence global) !(CheckedOccurrence global) !(ObviousProof global)
        !(Maybe (EqualitySupportRecipe global))
    | EqualityProofConvert !PreparationEffort !(ScopedCheckedCore global) !(ObviousProof global)
        !(Maybe (EqualitySupportRecipe global))

data EqualityProofContinuation global
    = AfterEqualityFunction !(ApplicationEqualityOperands global) !ProofRequirement
    | AfterEndpointCongruence !ProofRequirement !(EqualityOperands global)
    | AfterEqualityArgument !(ApplicationEqualityOperands global) !ProofRequirement !(ObviousProof global)
        !(Maybe (EqualitySupportRecipe global))
    | AfterSupportedEqualityFunction !(ApplicationEqualityOperands global)
        !(ObviousProof global) !(ObviousProof global) !(EqualitySupportRecipe global)
    | AfterSupportedEqualityArgument !(ApplicationEqualityOperands global) !(ObviousProof global)

-- Retain the selected ordinary derivation's children for a support upgrade.
-- A direct path has no congruence recipe yet; an application reuses its completed
-- descendants rather than recursively proving their ordinary versions again.
data EqualitySupportRecipe global
    = EqualitySupportPath !(EqualityOperands global)
    | EqualitySupportApplication !(ApplicationEqualityOperands global)
        !(ObviousProof global) !(EqualitySupportRecipe global)
        !(ObviousProof global) !(EqualitySupportRecipe global)

startEqualityProof
    :: EqualityProducer -> ExactConversionPolicy -> ProofRequirement
    -> FocusedEqualityGraph global -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> EqualityProofStep global
startEqualityProof producer policy requirement graph left right =
    startEqualityOperands (EqualityProofInput policy graph (requirement == MustUseCanonicalDefinition) producer) requirement
        (RootEqualityOperands ConcreteEndpoint left right) []

startEqualityOperands
    :: EqualityProofInput global
    -> ProofRequirement
    -> EqualityOperands global
    -> [EqualityProofContinuation global]
    -> EqualityProofStep global
startEqualityOperands input@(EqualityProofInput policy graph _retainSupport _producer) requirement operands =
    EqualityProofPending input (EqualityProofPath requirement operands
        (EqualityPathInput policy requirement graph left right) PathCompare)
  where
    (left, right) = case operands of
        RootEqualityOperands _ lhs rhs -> (lhs, rhs)
        OccurrenceEqualityOperands _ lhs rhs -> (checkedOccurrenceScopedCore lhs, checkedOccurrenceScopedCore rhs)

-- Direct graph lookup precedes congruence. Only a failed root lookup prepares
-- occurrence trees; children retain those checked rows throughout descent.
-- Returning a result or selecting a retained component needs no scheduling turn.
advanceEqualityProof
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> EqualityProofInput global
    -> EqualityProofAction global
    -> [EqualityProofContinuation global]
    -> State (ObviousSearchState global) (EqualityProofStep global)
advanceEqualityProof environment context input action continuations = do
    result <- Except.runExceptT case action of
        EqualityProofPath requirement operands pathInput cursor ->
            lift (advanceEqualityPath environment context pathInput cursor) >>= \case
                EqualityPathFinished (Left failure) -> Except.throwE failure
                EqualityPathFinished (Right (Just proof)) ->
                    let EqualityProofInput _ _ retainSupport _producer = input
                        support = if retainSupport && not (satisfiesRequirement MustUseCanonicalDefinition proof)
                            then Just (EqualitySupportPath operands) else Nothing
                    in pure (returned (Just proof) support)
                EqualityPathFinished (Right Nothing) -> pure (case input of
                    EqualityProofInput _ _ _ EvidenceOnly -> next (EqualityProofCongruence requirement operands)
                    EqualityProofInput _ _ _ SuppliedEquations ->
                        EqualityProofDemand input requirement operands continuations)
                EqualityPathPending nextInput nextCursor ->
                    pure (next (EqualityProofPath requirement operands nextInput nextCursor))
        EqualityProofCongruence requirement (RootEqualityOperands site left right) ->
            case (scopedCoreTerm left, scopedCoreTerm right) of
                (CApp{}, CApp{}) -> do
                    -- Keep paired validation and its failure/cost order together.
                    leftResult <- lift (analyseEqualityOperand environment context left)
                    rightResult <- lift (analyseEqualityOperand environment context right)
                    case (leftResult, rightResult) of
                        (Left failure, _) -> Except.throwE failure
                        (_, Left failure) -> Except.throwE failure
                        (Right leftRow, Right rightRow) -> pure (next
                            (EqualityProofCongruence requirement (OccurrenceEqualityOperands site leftRow rightRow)))
                _ -> pure (returned Nothing Nothing)
        EqualityProofCongruence requirement (OccurrenceEqualityOperands _ left right) ->
            case (checkedOccurrenceView left, checkedOccurrenceView right) of
                (OccurrenceApplication leftFunction leftArgument, OccurrenceApplication rightFunction rightArgument) -> do
                    functionsAgree <- lift (coreTypeIdentity (checkedOccurrenceType leftFunction) (checkedOccurrenceType rightFunction))
                    argumentsAgree <- lift (coreTypeIdentity (checkedOccurrenceType leftArgument) (checkedOccurrenceType rightArgument))
                    case (functionsAgree, argumentsAgree) of
                        (Left failure, _) -> Except.throwE failure
                        (_, Left failure) -> Except.throwE failure
                        (Right True, Right True) ->
                            let operands = ApplicationEqualityOperands left right leftFunction rightFunction leftArgument rightArgument
                            in pure (startEqualityOperands input AnyObviousProof
                                (OccurrenceEqualityOperands ConcreteEndpoint leftFunction rightFunction)
                                (AfterEqualityFunction operands requirement : continuations))
                        _ -> pure (returned Nothing Nothing)
                _ -> pure (returned Nothing Nothing)
        EqualityProofSupport (EqualitySupportPath operands) ->
            pure (startEqualityOperands input MustUseCanonicalDefinition operands continuations)
        EqualityProofSupport (EqualitySupportApplication operands function functionSupport argument argumentSupport) ->
            pure (EqualityProofPending input (EqualityProofSupport functionSupport)
                (AfterSupportedEqualityFunction operands function argument argumentSupport : continuations))
        EqualityProofJoin effort operands@(ApplicationEqualityOperands left right _leftFunction _rightFunction _leftArgument _rightArgument)
                functionProof argumentProof support ->
            lift (runKernelPreparation effort (KernelProof.countedEqualityCongruenceApplicationProof context
                    (obviousBuiltProof functionProof) (obviousBuiltProof argumentProof))) >>= \case
                NeedsMoreEffort offered -> pure (next
                    (EqualityProofJoin (FullPreparation offered) operands functionProof argumentProof support))
                PreparationFinished (Left failure) -> Except.throwE failure
                PreparationFinished (Right proof) -> do
                    dependencies <- Except.ExceptT (combineCandidateDependencies
                        (obviousProofDependencies functionProof) (obviousProofDependencies argumentProof))
                    pure (next (EqualityProofExpected left right (ObviousProof proof dependencies) support))
        EqualityProofExpected left right proof support -> do
            let leftTerm = checkedOccurrenceScopedCore left
                rightTerm = checkedOccurrenceScopedCore right
            expected <- Except.ExceptT (checkedProposition context
                (CEq (scopedCoreType leftTerm) (scopedCoreTerm leftTerm) (scopedCoreTerm rightTerm)))
            pure (next (EqualityProofConvert SmallPreparation expected proof support))
        EqualityProofConvert effort expected selected@(ObviousProof proof dependencies) support ->
            lift (runKernelPreparation effort (KernelProof.countedConversionProof context proof expected)) >>= \case
                NeedsMoreEffort offered -> pure (next (EqualityProofConvert (FullPreparation offered) expected selected support))
                PreparationFinished (Left failure) -> Except.throwE failure
                PreparationFinished (Right exact) -> pure (returned (Just (ObviousProof exact dependencies)) support)
    pure (either (EqualityProofFinished . Left) id result)
  where
    next cursor = EqualityProofPending input cursor continuations
    returned proof support = finishEqualityOperands input proof support continuations

endpointOperands :: EqualityOperands global -> (ScopedCheckedCore global, ScopedCheckedCore global)
endpointOperands = \case
    RootEqualityOperands _ left right -> (left, right)
    OccurrenceEqualityOperands _ left right -> (checkedOccurrenceScopedCore left, checkedOccurrenceScopedCore right)

argumentOperands :: EqualityOperands global -> Bool
argumentOperands = \case
    RootEqualityOperands site left _ -> site == FunctionArgument && arrow (scopedCoreType left)
    OccurrenceEqualityOperands site left _ -> site == FunctionArgument && arrow (checkedOccurrenceType left)
  where
    arrow TyArrow{} = True
    arrow _ = False

requestEndpointProof
    :: FocusedRequest global -> ProofRequirement -> EqualityOperands global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (FocusedRequest global))
requestEndpointProof request requirement operands = do
    let (left, right) = endpointOperands operands
    target <- checkedProposition (focusedContext request)
        (CEq (scopedCoreType left) (scopedCoreTerm left) (scopedCoreTerm right))
    pure ((\equation -> request {focusedTarget = equation, focusedRequirement = requirement,
        focusedObservation = SuppressAuxiliary AuxiliaryTransportPremise, focusedEligibility = FocusedOnly, focusedObligation = Nothing}) <$> target)

resumeEndpointProof
    :: EqualityProofInput global -> ProofRequirement -> EqualityOperands global
    -> [EqualityProofContinuation global] -> Attempt global -> EqualityProofStep global
resumeEndpointProof input@(EqualityProofInput _ _ retainSupport _) requirement operands frames = \case
    AttemptSucceeded proof -> finishEqualityOperands input (Just proof)
        (if retainSupport && not (satisfiesRequirement MustUseCanonicalDefinition proof)
            then Just (EqualitySupportPath operands) else Nothing) frames
    AttemptFailed failure | isTerminalFocusedFailure failure -> EqualityProofFinished (Left failure)
    _ -> EqualityProofPending input (EqualityProofCongruence requirement operands)
        (if argumentOperands operands then AfterEndpointCongruence requirement operands : frames else frames)

-- Both ordinary operands are retained before canonical support is requested.
-- Upgrading one never re-proves the other or reanalyses its occurrence tree.
resumeArgumentProof
    :: EqualityProofInput global -> EqualityOperands global -> [EqualityProofContinuation global]
    -> Attempt global -> EqualityProofStep global
resumeArgumentProof input@(EqualityProofInput _ _ retainSupport _) operands frames = \case
    AttemptSucceeded proof -> finishEqualityOperands input (Just proof)
        (if retainSupport && not (satisfiesRequirement MustUseCanonicalDefinition proof)
            then Just (EqualitySupportPath operands) else Nothing) frames
    AttemptFailed failure | isTerminalFocusedFailure failure -> EqualityProofFinished (Left failure)
    _ -> finishEqualityOperands input Nothing Nothing frames

finishEqualityOperands
    :: EqualityProofInput global -> Maybe (ObviousProof global) -> Maybe (EqualitySupportRecipe global)
    -> [EqualityProofContinuation global] -> EqualityProofStep global
finishEqualityOperands input@(EqualityProofInput _ _ retainSupport _producer) proof support = \case
    [] -> EqualityProofFinished (Right proof)
    continuation : rest -> case (continuation, proof) of
        (AfterEndpointCongruence requirement operands, Nothing) ->
            EqualityCompletionDemand input requirement operands rest
        (AfterEndpointCongruence _ _, Just _) -> finishEqualityOperands input proof support rest
        (AfterEqualityFunction _operands _requirement, Nothing) -> finishEqualityOperands input Nothing Nothing rest
        (AfterEqualityArgument _operands _requirement _function _support, Nothing) -> finishEqualityOperands input Nothing Nothing rest
        (AfterEqualityFunction operands@(ApplicationEqualityOperands _ _ _ _ leftArgument rightArgument)
                requirement, Just function) ->
            startEqualityOperands input AnyObviousProof (OccurrenceEqualityOperands FunctionArgument leftArgument rightArgument)
                (AfterEqualityArgument operands requirement function support : rest)
        (AfterEqualityArgument operands requirement function functionSupport, Just argument)
            | satisfiesRequirement MustUseCanonicalDefinition function || satisfiesRequirement MustUseCanonicalDefinition argument ->
                join operands function argument Nothing rest
            | not retainSupport -> join operands function argument Nothing rest
            | otherwise -> case (functionSupport, support) of
                (Just functionRecipe, Just argumentRecipe) ->
                    let recipe = EqualitySupportApplication operands function functionRecipe argument argumentRecipe
                    in case requirement of
                        AnyObviousProof -> join operands function argument (Just recipe) rest
                        MustUseCanonicalDefinition -> EqualityProofPending input (EqualityProofSupport recipe) rest
                _ -> EqualityProofFinished (Left (ObviousIntegrityFailure
                    (KernelProof.ProofStructuralCompositionMismatch "an equality operand lost its support recipe")))
        (AfterSupportedEqualityFunction operands function _argument argumentSupport, Nothing) ->
            EqualityProofPending input (EqualityProofSupport argumentSupport)
                (AfterSupportedEqualityArgument operands function : rest)
        (AfterSupportedEqualityFunction operands _function argument _support, Just supported) ->
            join operands supported argument Nothing rest
        (AfterSupportedEqualityArgument _operands _function, Nothing) -> finishEqualityOperands input Nothing Nothing rest
        (AfterSupportedEqualityArgument operands function, Just supported) -> join operands function supported Nothing rest
  where
    join operands function argument recipe rest =
        EqualityProofPending input (EqualityProofJoin SmallPreparation operands function argument recipe) rest

endpointEqualityStep :: EqualityProofStep global -> Bool
endpointEqualityStep = \case
    EqualityProofDemand{} -> True
    EqualityCompletionDemand{} -> True
    EqualityProofPending (EqualityProofInput _ _ _ SuppliedEquations) _ _ -> True
    _ -> False

equalityProofIsDeferred :: EqualityProofStep global -> Bool
equalityProofIsDeferred = \case
    EqualityProofPending _ (EqualityProofJoin effort _ _ _ _) _ -> preparationIsDeferred effort
    EqualityProofPending _ (EqualityProofConvert effort _ _ _) _ -> preparationIsDeferred effort
    _ -> False

analyseEqualityOperand
    :: SearchEnvironment global
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (CheckedOccurrence global))
analyseEqualityOperand (SearchEnvironment globalType _imports _hypotheses _views) context checked = do
    remaining <- getFocusedWorkBudget
    let (result, after) = countedAnalyseCanonicalOccurrences globalType remaining
            (KernelProof.proofContextTypes context) (scopedCoreTerm checked)
    putFocusedWorkBudget after
    pure (first (obviousCountedFailure (ObviousIntegrityFailure . KernelProof.ProofTermIllTyped)) result)

data EqualityPathInput global = EqualityPathInput
    !ExactConversionPolicy !ProofRequirement !(FocusedEqualityGraph global)
    !(ScopedCheckedCore global) !(ScopedCheckedCore global)

data EqualityPathStep global
    = EqualityPathFinished !(Either (ObviousFailure global) (Maybe (ObviousProof global)))
    | EqualityPathPending !(EqualityPathInput global) !(EqualityPathCursor global)

data EqualityPathCursor global
    = PathCompare
    | PathReflexive
    | PathLookupLeft
    | PathLookupRight !FocusedEqualityTermId
    | PathVisit !FocusedEqualityVisit !FocusedEqualityTermId
        !(Set FocusedEqualityVisit)
        !(Map.Map FocusedEqualityVisit (FocusedEqualityVisit, FocusedEqualityEdgeId))
        !(Seq FocusedEqualityVisit)
    | PathExpand !FocusedEqualityVisit !FocusedEqualityTermId !FocusedEqualityVisit
        !(Set FocusedEqualityVisit)
        !(Map.Map FocusedEqualityVisit (FocusedEqualityVisit, FocusedEqualityEdgeId))
        !(Seq FocusedEqualityVisit) !(Seq FocusedEqualityEdgeId)
    | PathReconstruct !FocusedEqualityVisit
        !(Map.Map FocusedEqualityVisit (FocusedEqualityVisit, FocusedEqualityEdgeId))
        !FocusedEqualityVisit ![FocusedEqualityEdgeId]
    | PathFirstEdge ![FocusedEqualityEdgeId]
    | PathNextEdge !(ObviousProof global) ![FocusedEqualityEdgeId]
    | PathJoin !(ObviousProof global) !(ObviousProof global) ![FocusedEqualityEdgeId]
    | PathExpected !(ObviousProof global)
    | PathConvert !(ScopedCheckedCore global) !(ObviousProof global)

-- The graph is immutable throughout lookup and proof construction. Search
-- visits and materialization prefixes are retained independently of its rows.
advanceEqualityPath
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> EqualityPathInput global
    -> EqualityPathCursor global
    -> State (ObviousSearchState global) (EqualityPathStep global)
advanceEqualityPath environment context input@(EqualityPathInput policy requirement graph left right) cursor = do
    result <- Except.runExceptT case cursor of
        PathCompare -> do
            same <- Except.ExceptT case policy of
                ConvertExactCandidates -> convertible environment left right
                DeferExactCandidateConversion -> canonicalIdentity (scopedCoreTerm left) (scopedCoreTerm right)
            pure (next (if same && requirement == AnyObviousProof then PathReflexive else PathLookupLeft))
        PathReflexive -> do
            proof <- Except.ExceptT (runCountedKernel
                (KernelProof.countedEqualityReflexivityProof context left))
            pure (next (PathExpected (ObviousProof proof emptyCandidateDependencies)))
        PathLookupLeft -> do
            found <- Except.ExceptT (lookupFocusedEqualityTerm graph left)
            pure (maybe (finished Nothing) (next . PathLookupRight) found)
        PathLookupRight source -> do
            found <- Except.ExceptT (lookupFocusedEqualityTerm graph right)
            let initial = FocusedEqualityVisit source False
            pure (maybe (finished Nothing)
                (\target -> next (PathVisit initial target (Set.singleton initial) Map.empty (Seq.singleton initial))) found)
        PathVisit initial target visited predecessors pending -> case Seq.viewl pending of
            Seq.EmptyL -> pure (finished Nothing)
            current Seq.:< rest -> do
                charge
                pure (if isGoal target current
                    then next (PathReconstruct initial predecessors current [])
                    else next (PathExpand initial target current visited predecessors rest
                        (Map.findWithDefault Seq.empty (focusedVisitTerm current) (focusedEqualityOutgoing graph))))
        PathExpand initial target current visited predecessors pending outgoing -> case Seq.viewl outgoing of
            Seq.EmptyL -> pure (next (PathVisit initial target visited predecessors pending))
            edgeId Seq.:< rest -> do
                charge
                edge <- maybe (Except.throwE corruptGraph) pure (lookupFocusedEqualityEdge graph edgeId)
                let FocusedEqualityEdge edgeSource edgeTarget _direction proof = edge
                unless (edgeSource == focusedVisitTerm current) (Except.throwE corruptGraph)
                let carriesCanonical = focusedVisitCanonical current
                        || candidateUsesCanonicalDefinition (obviousProofDependencies proof)
                    reached = FocusedEqualityVisit edgeTarget
                        (requirement /= AnyObviousProof && carriesCanonical)
                if reached `Set.member` visited
                    then pure (next (PathExpand initial target current visited predecessors pending rest))
                    else do
                        charge
                        pure (next (PathExpand initial target current (Set.insert reached visited)
                            (Map.insert reached (current, edgeId) predecessors) (pending Seq.|> reached) rest))
        PathReconstruct initial predecessors current accumulated
            | current == initial -> pure (next (PathFirstEdge accumulated))
            | otherwise -> do
                charge
                (previous, edgeId) <- maybe (Except.throwE corruptGraph) pure (Map.lookup current predecessors)
                pure (next (PathReconstruct initial predecessors previous (edgeId : accumulated)))
        PathFirstEdge [] -> Except.throwE corruptGraph
        PathFirstEdge (edge : rest) -> do
            proof <- Except.ExceptT (materializeFocusedEqualityEdge context graph edge)
            pure (next (PathNextEdge proof rest))
        PathNextEdge proof [] -> pure (next (PathExpected proof))
        PathNextEdge proof (edge : rest) -> do
            following <- Except.ExceptT (materializeFocusedEqualityEdge context graph edge)
            pure (next (PathJoin proof following rest))
        PathJoin (ObviousProof accumulated accumulatedDependencies) (ObviousProof following followingDependencies) rest -> do
            proof <- Except.ExceptT (runCountedKernel
                (KernelProof.countedComposeEqualityProof context accumulated following))
            dependencies <- Except.ExceptT (combineCandidateDependencies accumulatedDependencies followingDependencies)
            pure (next (PathNextEdge (ObviousProof proof dependencies) rest))
        PathExpected proof -> do
            expected <- Except.ExceptT (checkedProposition context
                (CEq (scopedCoreType left) (scopedCoreTerm left) (scopedCoreTerm right)))
            pure (next (PathConvert expected proof))
        PathConvert expected (ObviousProof proof dependencies) -> do
            exact <- Except.ExceptT (conversionProof context proof expected)
            pure (finished (Just (ObviousProof exact dependencies)))
    pure (either (EqualityPathFinished . Left) id result)
  where
    next = EqualityPathPending input
    finished = EqualityPathFinished . Right
    isGoal target visit = focusedVisitTerm visit == target
        && (requirement == AnyObviousProof || focusedVisitCanonical visit)
    charge = do
        hasWork <- lift consumeSearchStep
        unless hasWork (Except.throwE (ObviousResourceExhausted ObviousFocusedWorkLimit))

focusedVisitTerm
    :: FocusedEqualityVisit
    -> FocusedEqualityTermId
focusedVisitTerm (FocusedEqualityVisit termId _canonical) = termId

focusedVisitCanonical :: FocusedEqualityVisit -> Bool
focusedVisitCanonical (FocusedEqualityVisit _termId canonical) = canonical

focusedEqualityOutgoing
    :: FocusedEqualityGraph global
    -> Map.Map FocusedEqualityTermId (Seq FocusedEqualityEdgeId)
focusedEqualityOutgoing
        (FocusedEqualityGraph _terms _edges outgoing _buckets) =
    outgoing

lookupFocusedEqualityEdge
    :: FocusedEqualityGraph global
    -> FocusedEqualityEdgeId
    -> Maybe (FocusedEqualityEdge global)
lookupFocusedEqualityEdge
        (FocusedEqualityGraph _terms edges _outgoing _buckets)
        (FocusedEqualityEdgeId position) =
    Seq.lookup position edges

materializeFocusedEqualityEdge
    :: Eq global
    => KernelProof.ProofContext global
    -> FocusedEqualityGraph global
    -> FocusedEqualityEdgeId
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (ObviousProof global))
materializeFocusedEqualityEdge context graph edgeId = do
    hasWork <- consumeSearchStep
    if not hasWork
        then pure focusedWorkExhausted
        else case lookupFocusedEqualityEdge graph edgeId of
            Nothing -> pure (Left corruptGraph)
            Just (FocusedEqualityEdge _source _target direction proof@(ObviousProof built dependencies)) ->
                case direction of
                    FocusedEqualityForward -> pure (Right proof)
                    FocusedEqualityReverse -> do
                        reversed <- reverseEqualityProof context built
                        pure ((\result -> ObviousProof result dependencies) <$> reversed)

focusedWorkExhausted
    :: Either (ObviousFailure global) value
focusedWorkExhausted =
    Left (ObviousResourceExhausted ObviousFocusedWorkLimit)

corruptGraph :: ObviousFailure global
corruptGraph =
    ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch
            "the focused equality graph is internally inconsistent")

data TermLookupStep global
    = TermLookupFinished !(Maybe (ObviousFailure global))
    | TermLookupFound !(ObviousProof global) !(TermLookupStep global)
    | TermLookupPending !(TermLookupCursor global)

data ReverseLookup global = ReverseLookup
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    !(AvailableSourceCursor global)

data TermLookupCursor global
    = LookupExact !(ScopedCheckedCore global) !(AvailableSourceCursor global)
    | LookupCompareExact !(ScopedCheckedCore global) !(ObviousProof global) !(AvailableSourceCursor global)
    | LookupReverse !(ScopedCheckedCore global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(AvailableSourceCursor global)
    | LookupExposeReverse !(ReverseLookup global) !(ObviousProof global)
    | LookupReverseLeft !(ReverseLookup global) !(ObviousProof global)
        !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | LookupReverseRight !(ReverseLookup global) !(ObviousProof global) !(ScopedCheckedCore global)
    | LookupReverseBuild !(ReverseLookup global) !(ObviousProof global)
    | LookupReverseConvert !(ReverseLookup global) !(ObviousProof global)

startTermLookup
    :: KernelProof.ProofContext global
    -> CanonicalTerm global
    -> [ObviousProof global]
    -> State (ObviousSearchState global) (TermLookupStep global)
startTermLookup context term available = checkedProposition context term >>= \case
    Left failure -> pure (TermLookupFinished (Just failure))
    Right target -> pure (TermLookupPending (LookupExact target (AvailableNext available)))

advanceTermLookup
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> [ObviousProof global]
    -> TermLookupCursor global
    -> State (ObviousSearchState global) (TermLookupStep global)
advanceTermLookup environment context available cursor = do
    result <- Except.runExceptT case cursor of
        LookupExact target sources -> do
            source <- Except.ExceptT (advanceAvailableSource environment context sources)
            pure case source of
                AvailableSourceFinished -> case splitScopedEquality target of
                    Just (_operandType, left, right) ->
                        next (LookupReverse target left right (AvailableNext available))
                    Nothing -> finished Nothing
                AvailableSourcePending pending -> next (LookupExact target pending)
                AvailableSourceFound proof following -> next (LookupCompareExact target proof following)
        LookupCompareExact target source following -> do
            matched <- lift (exactCandidateAttempt ConvertExactCandidates
                (SuppressAuxiliary AuxiliaryIntroductionComponent) context target source)
            case matched of
                AttemptFailed failure -> Except.throwE failure
                AttemptNotApplicable -> pure (next (LookupExact target following))
                AttemptSucceeded proof -> pure (TermLookupFound proof (next (LookupExact target following)))
        LookupReverse target left right sources -> do
            source <- Except.ExceptT (advanceAvailableSource environment context sources)
            pure case source of
                AvailableSourceFinished -> finished Nothing
                AvailableSourcePending pending -> next (LookupReverse target left right pending)
                AvailableSourceFound proof following ->
                    next (LookupExposeReverse (ReverseLookup target left right following) proof)
        LookupExposeReverse lookup@(ReverseLookup _target left _right _following) source -> do
            exposed <- Except.ExceptT (exposeProof environment context source)
            case splitScopedEquality (obviousProofStatement exposed) of
                Nothing -> pure (resumeReverse lookup)
                Just (foundType, foundLeft, foundRight) -> do
                    sameType <- Except.ExceptT (coreTypeIdentity foundType (scopedCoreType left))
                    pure (if sameType then next (LookupReverseLeft lookup exposed foundLeft foundRight)
                        else resumeReverse lookup)
        LookupReverseLeft lookup@(ReverseLookup _target _left right _following) source foundLeft foundRight -> do
            matches <- Except.ExceptT (convertible environment foundLeft right)
            pure (if matches then next (LookupReverseRight lookup source foundRight) else resumeReverse lookup)
        LookupReverseRight lookup@(ReverseLookup _target left _right _following) source foundRight -> do
            matches <- Except.ExceptT (convertible environment foundRight left)
            pure (if matches then next (LookupReverseBuild lookup source) else resumeReverse lookup)
        LookupReverseBuild lookup (ObviousProof proof dependencies) -> do
            reversed <- Except.ExceptT (reverseEqualityProof context proof)
            pure (next (LookupReverseConvert lookup (ObviousProof reversed dependencies)))
        LookupReverseConvert lookup@(ReverseLookup target _ _ _) (ObviousProof proof dependencies) -> do
            converted <- Except.ExceptT (conversionProof context proof target)
            pure (TermLookupFound (ObviousProof converted dependencies) (resumeReverse lookup))
    pure (either (TermLookupFinished . Just) id result)
  where
    next = TermLookupPending
    finished = TermLookupFinished
    resumeReverse (ReverseLookup target left right following) =
        next (LookupReverse target left right following)

data FalsumStep global
    = FalsumFinished !(Attempt global)
    | FalsumFound !(ObviousProof global) !(FalsumStep global)
    | FalsumPending !(FalsumCursor global)

data FalsumCursor global
    = FalsumLookup !(FalsumContinuation global) !(TermLookupStep global)
    | FalsumContradictions !(AvailableSourceCursor global)
    | FalsumExposeContradiction !(ObviousProof global) !(AvailableSourceCursor global)
    | FalsumBuild !PreparationEffort !(FalsumConstruction global) !(FalsumStep global)

data FalsumConstruction global
    = FalsumEliminate !(ObviousProof global)
    | FalsumContradiction !(ObviousProof global) !(ObviousProof global)

data FalsumContinuation global
    = FalsumDirect
    | FalsumNegativeSource !(ObviousProof global) !(AvailableSourceCursor global)
    | FalsumPositiveSource !(ObviousProof global) !(AvailableSourceCursor global)

advanceFalsum
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> [ObviousProof global]
    -> FalsumCursor global
    -> State (ObviousSearchState global) (FalsumStep global)
advanceFalsum environment context target available = \case
    FalsumLookup continuation (TermLookupPending cursor) ->
        FalsumPending . FalsumLookup continuation <$> advanceTermLookup environment context available cursor
    FalsumLookup continuation (TermLookupFound proof remaining) -> do
        let following = FalsumPending (FalsumLookup continuation remaining)
        pure case continuation of
            FalsumDirect
                | scopedCoreTerm target == CFalsum -> FalsumFound proof following
                | otherwise -> FalsumPending (FalsumBuild SmallPreparation (FalsumEliminate proof) following)
            FalsumNegativeSource source _ ->
                FalsumPending (FalsumBuild SmallPreparation (FalsumContradiction proof source) following)
            FalsumPositiveSource source _ ->
                FalsumPending (FalsumBuild SmallPreparation (FalsumContradiction source proof) following)
    FalsumLookup continuation (TermLookupFinished result) -> pure case result of
        Just failure -> FalsumFinished (AttemptFailed failure)
        Nothing -> case continuation of
            FalsumDirect
                | scopedCoreTerm target == CFalsum ->
                    FalsumPending (FalsumContradictions (AvailableNext available))
                | otherwise -> FalsumFinished AttemptNotApplicable
            FalsumNegativeSource _ following -> FalsumPending (FalsumContradictions following)
            FalsumPositiveSource _ following -> FalsumPending (FalsumContradictions following)
    FalsumContradictions cursor -> advanceAvailableSource environment context cursor >>= \case
        Left failure -> pure (FalsumFinished (AttemptFailed failure))
        Right AvailableSourceFinished -> pure (FalsumFinished (AttemptFailed ObviousFalsityPairUnavailable))
        Right (AvailableSourcePending pending) -> pure (FalsumPending (FalsumContradictions pending))
        Right (AvailableSourceFound source following) ->
            pure (FalsumPending (FalsumExposeContradiction source following))
    FalsumExposeContradiction source following -> exposeProof environment context source >>= \case
        Left failure -> pure (FalsumFinished (AttemptFailed failure))
        Right exposed -> case scopedCoreTerm (obviousProofStatement exposed) of
            CNot proposition -> FalsumPending . FalsumLookup (FalsumNegativeSource exposed following)
                <$> startTermLookup context proposition available
            proposition -> FalsumPending . FalsumLookup (FalsumPositiveSource exposed following)
                <$> startTermLookup context (CNot proposition) available
    FalsumBuild effort construction following -> do
        built <- runKernelPreparation effort (case construction of
            FalsumEliminate proof -> KernelProof.countedFalsumEliminationProof
                context (obviousBuiltProof proof) target
            FalsumContradiction positive negative -> KernelProof.countedNegationEliminationProof
                context (obviousBuiltProof positive) (obviousBuiltProof negative))
        case built of
            NeedsMoreEffort offered -> pure
                (FalsumPending (FalsumBuild (FullPreparation offered) construction following))
            PreparationFinished (Left failure) -> pure (FalsumFinished (AttemptFailed failure))
            PreparationFinished (Right proof) -> do
                dependencies <- case construction of
                    FalsumEliminate source -> pure (Right (obviousProofDependencies source))
                    FalsumContradiction positive negative -> combineCandidateDependencies
                        (obviousProofDependencies positive) (obviousProofDependencies negative)
                pure case dependencies of
                    Left failure -> FalsumFinished (AttemptFailed failure)
                    Right consumed -> FalsumFound (ObviousProof proof consumed) following

data TheoremCursor global
    = TheoremDiscover !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) ![TheoremWorkItem global]
    | TheoremPreparing !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) ![TheoremWorkItem global] !(TheoremSourceStep global)
    | TheoremProject !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) !(ObviousProof global) ![TheoremWorkItem global]
    | TheoremSelectResult !(FocusedObligationHead global)
        !(Maybe (ObviousFailure global)) !(PreparedTheoremSource global) ![TheoremWorkItem global]

data TheoremContinuation global = TheoremContinuation
    !(FocusedObligationHead global)
    !(Maybe (ObviousFailure global))
    !(PreparedTheoremSource global)
    ![TheoremWorkItem global]

data TheoremStep global
    = TheoremPending !(TheoremCursor global)
    | TheoremBlocked !(TheoremCursor global) !(TheoremCursor global)
    | TheoremApply !(PreparedTheoremSource global) !(TheoremContinuation global)
    | TheoremFinished !(Attempt global)

startTheoremSearch
    :: ScopedCheckedCore global
    -> [ObviousProof global]
    -> State (ObviousSearchState global) (TheoremStep global)
startTheoremSearch target roots = focusedObligationHead (scopedCoreTerm target) >>= \case
    Left failure -> pure (TheoremFinished (AttemptFailed failure))
    Right targetHead -> pure (TheoremPending
        (TheoremDiscover targetHead Nothing (map RootTheoremWorkItem roots)))

advanceTheoremSearch
    :: Ord global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> TheoremCursor global
    -> State (ObviousSearchState global) (TheoremStep global)
advanceTheoremSearch environment context = \case
    TheoremDiscover _targetHead firstFailure [] ->
        pure (TheoremFinished (maybe AttemptNotApplicable AttemptFailed firstFailure))
    TheoremDiscover targetHead firstFailure (workItem : rest) -> do
        let (hasPrefix, root) = theoremWorkItemRoot workItem
        relevant <- shallowTheoremSourceMayApply hasPrefix targetHead root
        case relevant of
            Left failure -> failed failure
            Right False -> next (TheoremDiscover targetHead firstFailure rest)
            Right True -> do
                started <- startTheoremSource context workItem
                prepared <- advanceTheoremSource environment context started
                continuePrepared targetHead firstFailure rest prepared
    TheoremPreparing targetHead firstFailure rest preparation -> case preparation of
        TheoremSourceFinished (Left failure)
            | isConversionLimit failure -> next (TheoremDiscover targetHead (firstFailure <|> Just failure) rest)
            | otherwise -> failed failure
        TheoremSourceFinished (Right (PreparedTheoremSource exposed (CompiledTheoremSpine [] _ _))) ->
            next (TheoremProject targetHead firstFailure exposed rest)
        TheoremSourceFinished (Right prepared) ->
            pure (TheoremApply prepared (TheoremContinuation targetHead firstFailure prepared rest))
        _ -> advanceTheoremSource environment context preparation >>= continuePrepared targetHead firstFailure rest
    TheoremSelectResult targetHead firstFailure
            (PreparedTheoremSource source (CompiledTheoremSpine steps result _)) rest ->
        case Template.splitCompiledConjunction result of
            Nothing -> next (TheoremDiscover targetHead firstFailure rest)
            Just (left, right) -> reverseTheoremStepsCounted [] steps >>= \case
                Left failure -> failed failure
                Right prefix -> selectedTheoremSources source >>= \case
                    Left failure -> failed failure
                    Right (leftSource, rightSource) ->
                        let children =
                                [ SelectedTheoremWorkItem leftSource (Elimination.ProjectLeft : prefix) left
                                , SelectedTheoremWorkItem rightSource (Elimination.ProjectRight : prefix) right
                                ]
                        in next (TheoremDiscover targetHead firstFailure (children <> rest))
    TheoremProject targetHead firstFailure source rest ->
        projectedChildrenFromExposed context source >>= \case
            Left failure | isConversionLimit failure ->
                next (TheoremDiscover targetHead (firstFailure <|> Just failure) rest)
            Left failure -> failed failure
            Right projected -> next (TheoremDiscover targetHead firstFailure
                (map ProjectedTheoremWorkItem projected <> rest))
  where
    continuePrepared targetHead firstFailure rest prepared = case prepared of
        TheoremSourceFinished{} -> advanceTheoremSearch environment context (TheoremPreparing targetHead firstFailure rest prepared)
        _ | theoremSourceIsDeferred prepared && not (null rest) ->
                pure (TheoremBlocked (TheoremPreparing targetHead Nothing [] prepared) (TheoremDiscover targetHead firstFailure rest))
          | otherwise -> next (TheoremPreparing targetHead firstFailure rest prepared)
    next = pure . TheoremPending
    failed = pure . TheoremFinished . AttemptFailed

resumeTheoremSearch :: TheoremContinuation global -> TheoremStep global
resumeTheoremSearch (TheoremContinuation targetHead firstFailure prepared rest) =
    TheoremPending (TheoremSelectResult targetHead firstFailure prepared rest)

-- Keep the original proof until application can fill every hole. These keys
-- identify its selected programs, not proofs of the open conjuncts. Repeated
-- discovery reuses the same keys for endpoint/cycle tracking; neither child
-- shares the unselected source's spine or proof-projection cache identity.
selectedTheoremSources
    :: ObviousProof global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) (ObviousProof global, ObviousProof global))
selectedTheoremSources source = Except.runExceptT do
    let selected = projectCandidateProof (obviousBuiltProof source) source
    case obviousProofSourceKey source of
        Nothing -> pure (selected, selected)
        Just sourceKey -> do
            scopeCharge
            cached <- lift (State.gets (Map.lookup sourceKey . searchTheoremSelectionKeys))
            (leftKey, rightKey) <- case cached of
                Just keys -> pure keys
                Nothing -> do
                    -- Pay for both identities and publication before changing
                    -- the table; an exhausted lookup publishes no half-pair.
                    scopeCharge
                    scopeCharge
                    scopeCharge
                    next <- lift (State.gets searchNextDerivedSourceId)
                    let keys = (FocusedDerivedSourceKey next, FocusedDerivedSourceKey (next + 1))
                    lift (State.modify' (\state -> state
                        { searchNextDerivedSourceId = next + 2
                        , searchTheoremSelectionKeys = Map.insert sourceKey keys (searchTheoremSelectionKeys state)
                        }))
                    pure keys
            pure (withFocusedSourceKey leftKey selected, withFocusedSourceKey rightKey selected)

theoremWorkItemRoot :: TheoremWorkItem global -> (Bool, CanonicalTerm global)
theoremWorkItemRoot = \case
    RootTheoremWorkItem source -> (False, sourceTerm source)
    ProjectedTheoremWorkItem source -> (False, sourceTerm source)
    SelectedTheoremWorkItem _source _prefix result ->
        (True, scopedCoreTerm (Template.compiledTemplateTerm result))
  where
    sourceTerm =
        scopedCoreTerm
            . KernelProof.builtProofStatement
            . obviousBuiltProof

-- | Reject a syntactically rigid atomic root before theorem exposure.  Direct
-- forall and implication constructors are only a shallow relevance hint; a
-- lambda-headed root remains eligible because head reduction may reveal either
-- a theorem spine or a conjunction.  The filter therefore removes redundant
-- work without changing the supported conversion boundary.
shallowTheoremSourceMayApply
    :: Eq global
    => Bool
    -> FocusedObligationHead global
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either (ObviousFailure global) Bool)
shallowTheoremSourceMayApply hasPrefix targetHead =
    go hasPrefix
  where
    go hasSpine term = do
        hasWork <- consumeSearchStep
        if not hasWork
            then pure focusedWorkExhausted
            else
                case term of
                    CForall _binderType body -> go True body
                    CImp _premise conclusion -> go True conclusion
                    CAnd left right
                        | not hasSpine -> pure (Right True)
                        | otherwise -> focusedObligationHead term >>= \case
                            Left failure -> pure (Left failure)
                            Right sourceHead
                                | theoremHeadMayMatch sourceHead targetHead -> pure (Right True)
                                | otherwise -> go True left >>= \case
                                    Right False -> go True right
                                    result -> pure result
                    _ -> do
                        sourceHeadResult <- focusedObligationHead term
                        pure
                            (fmap
                                (\sourceHead ->
                                    if hasSpine
                                        then theoremHeadMayMatch
                                            sourceHead targetHead
                                        else reducibleFocusedHead sourceHead)
                                sourceHeadResult)

    -- A bound conclusion head may be a theorem parameter, and ambient bound
    -- heads still require rebasing after the peeled forall prefix.  Neither is
    -- a sound shallow rejection key.
    theoremHeadMayMatch
            (FocusedObligationHead _arity FocusedHeadBound{}) _target = True
    theoremHeadMayMatch source target =
        possiblyConvertibleFocusedHeads source target

data ApplicationInput global = ApplicationInput
    !ApplicationParameterPolicy !Bool
    !ProofRequirement
    !FocusedContextId
    !(CompiledTheoremSpine global)
    !(KernelProof.BuiltProof global)
    !CandidateDependencies
    !(KernelProof.ProofContext global)
    !(ScopedCheckedCore global)
    !(Maybe FocusedSourceKey)

data ApplicationTask global
    = ApplicationStartPremises !(Template.TemplateSubstitution global)
    | ApplicationSteps !Bool !(Template.TemplateSubstitution global)
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationPremise !Bool !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
    | ApplicationFacts !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
        !(Maybe (ObviousFailure global)) ![ObviousProof global]
    | ApplicationExposeFact !(ApplicationFact global) !(SourceExposureStep global)
    | ApplicationMatchFact !(ApplicationFact global) !(ObviousProof global) !(TheoremMatchStep global)
    | ApplicationConvertFact !(ApplicationFact global) !(Template.TemplateSubstitution global)
        !CandidateDependencies !(HeadProofStep global)
    | ApplicationNextFact !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
        !(Maybe (ObviousFailure global)) !(ObviousProof global) ![ObviousProof global]
    | ApplicationJoin !(Attempt global)
        !(Template.CompiledTemplate global) !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
    | ApplicationFinish !(Template.TemplateSubstitution global) !(Seq (ObviousProof global))
    | ApplicationReconstruct !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationPrepareHead !(Template.TemplateSubstitution global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global] !(HeadProofStep global)
    | ApplicationPrepared !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationConvertPremise !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !CandidateDependencies !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global] !(HeadProofStep global)
    | ApplicationEliminateForall !PreparationEffort !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !(ScopedCheckedCore global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationEliminateImplication !PreparationEffort !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationProject !PreparationEffort !Bool !(Template.TemplateSubstitution global)
        !(KernelProof.BuiltProof global) !CandidateDependencies
        !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ApplicationConvertResult !CandidateDependencies !(HeadProofStep global)
    | ApplicationContinue !(PremiseContinuation global)
        !(Template.TemplateSubstitution global) !(ObviousProof global)
    | ApplicationReturn !(Attempt global)

applicationAdministrative :: ApplicationTask global -> Bool
applicationAdministrative = \case
    ApplicationReconstruct{} -> True
    ApplicationPrepareHead _ _ _ _ HeadProofFinished{} -> True
    ApplicationPrepared{} -> True
    ApplicationConvertPremise _ _ _ _ _ _ HeadProofFinished{} -> True
    ApplicationConvertResult _ HeadProofFinished{} -> True
    ApplicationExposeFact _ SourceExposureFinished{} -> True
    ApplicationMatchFact _ _ TheoremMatchFinished{} -> True
    ApplicationConvertFact _ _ _ HeadProofFinished{} -> True
    _ -> False

data ApplicationFact global = ApplicationFact
    !(Template.CompiledTemplate global) !(Template.TemplateSubstitution global)
    !(PremiseContinuation global) !(Maybe (ObviousFailure global)) !(ObviousProof global) ![ObviousProof global]

applicationIsDeferred :: ApplicationTask global -> Bool
applicationIsDeferred = \case
    ApplicationExposeFact _ step -> sourceExposureIsDeferred step
    ApplicationMatchFact _ _ step -> theoremMatchIsDeferred step
    ApplicationConvertFact _ _ _ step -> headProofIsDeferred step
    ApplicationPrepareHead _ _ _ _ step -> headProofIsDeferred step
    ApplicationConvertPremise _ _ _ _ _ _ step -> headProofIsDeferred step
    ApplicationConvertResult _ step -> headProofIsDeferred step
    ApplicationEliminateForall effort _ _ _ _ _ _ -> preparationIsDeferred effort
    ApplicationEliminateImplication effort _ _ _ _ _ _ -> preparationIsDeferred effort
    ApplicationProject effort _ _ _ _ _ _ -> preparationIsDeferred effort
    _ -> False

data PremiseContinuation global
    = ContinueTheoremPremises !Bool !(Seq (ObviousProof global)) ![TheoremSpineStep global]
    | ContinueLeftPremise !(Template.CompiledTemplate global)
        !(PremiseContinuation global)
    | ContinueRightPremise !(ObviousProof global) !(PremiseContinuation global)

data ApplicationFrame global
    = AfterApplicationBuild !(Seq (ApplicationSupportRecipe global))
    | AfterDirectPlan !(Template.TemplateSubstitution global)
    | AfterWholePremise !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
    | AfterJoinedPremise !(Attempt global)
    | AfterMatchedPremise !(Template.CompiledTemplate global)
        !(Template.TemplateSubstitution global) !(PremiseContinuation global)
        !(Maybe (ObviousFailure global)) !(ObviousProof global) ![ObviousProof global]

data ApplicationStep global
    = ApplicationPending !(ApplicationInput global) !(ApplicationTask global)
        ![ApplicationFrame global]
    | ApplicationChild !(ApplicationInput global) !Bool
        !(ScopedCheckedCore global) !(Template.TemplateSubstitution global)
        !(PremiseContinuation global) ![ApplicationFrame global]
    | ApplicationFinished !(Attempt global)
    | ApplicationFound !(ObviousProof global) !(ApplicationStep global)
    | ApplicationSupport !(ApplicationInput global) !(Seq (ApplicationSupportRecipe global))
        ![ApplicationFrame global]

-- A support upgrade reuses the checked prefix before this implication. The
-- substitution and later selected premises are fixed; no matcher or source
-- scan is restarted to upgrade an already completed application.
data ApplicationSupportRecipe global = ApplicationSupportRecipe
    !(ObviousProof global)
    !(Template.TemplateSubstitution global)
    !(KernelProof.BuiltProof global) !CandidateDependencies
    !(ScopedCheckedCore global)
    !(Seq (ObviousProof global)) ![TheoremSpineStep global]

-- One transition selects a premise candidate, resumes a dependent alternative,
-- or reconstructs one spine step. No continuation retains a Haskell callback.
advanceApplication
    :: Ord global
    => SearchEnvironment global
    -> ApplicationInput global
    -> ApplicationTask global
    -> [ApplicationFrame global]
    -> State (ObviousSearchState global) (ApplicationStep global)
advanceApplication environment input@(ApplicationInput _ allowRecursive requirement contextId spine
        source sourceDependencies context target _sourceKey) task frames = case task of
    ApplicationStartPremises substitutions -> do
        missing <- missingFocusedTemplateSlots (spineBinderEnvironment spine) substitutions
        case missing of
            Left failure -> failed failure
            Right slots -> pure (ApplicationPending input
                (ApplicationSteps (allowRecursive && null slots) substitutions Seq.empty steps)
                (if allowRecursive && null slots then frames else AfterDirectPlan substitutions : frames))
    ApplicationSteps allowSearch substitutions selected pending -> case pending of
        [] -> next (ApplicationFinish substitutions selected)
        Elimination.Instantiate{} : rest ->
            next (ApplicationSteps allowSearch substitutions selected rest)
        Elimination.ProjectLeft : rest ->
            next (ApplicationSteps allowSearch substitutions selected rest)
        Elimination.ProjectRight : rest ->
            next (ApplicationSteps allowSearch substitutions selected rest)
        Elimination.Apply template : rest ->
            next (ApplicationPremise allowSearch template substitutions
                (ContinueTheoremPremises allowSearch selected rest))
    ApplicationPremise allowSearch template substitutions continuation -> do
        closure <- closeFocusedTemplate template substitutions
        case closure of
            Left failure -> failed failure
            Right (Template.TemplateClosed premiseTarget) ->
                pure (ApplicationChild input allowSearch premiseTarget substitutions
                    continuation frames)
            Right Template.TemplateOpen{} -> do
                available <- availableProofs environment contextId context
                case available of
                    Left failure -> failed failure
                    Right facts -> pure (ApplicationPending input
                        (ApplicationFacts template substitutions continuation Nothing facts)
                        (AfterWholePremise template substitutions continuation : frames))
    ApplicationFacts template substitutions _continuation firstFailure [] -> do
        missing <- missingFocusedTemplateSlots
            (Template.compiledTemplateBinderEnvironment template) substitutions
        failed (case missing of
            Left failure -> failure
            Right slots -> fromMaybe
                (case slots of
                    Template.MatcherSlot position : _rest -> ObviousUndeterminedParameter position
                    [] -> ObviousAntecedentUnavailable (Template.compiledTemplateTerm template))
                firstFailure)
    ApplicationFacts template substitutions continuation firstFailure (fact : rest) -> do
        hasWork <- consumeSearchStep
        if not hasWork then failed (ObviousResourceExhausted ObviousFocusedWorkLimit)
            else startSourceExposure context fact >>= next . ApplicationExposeFact
                (ApplicationFact template substitutions continuation firstFailure fact rest)
    ApplicationExposeFact candidate@(ApplicationFact template substitutions _ _ _ _) step -> case step of
        SourceExposureFinished (Left failure) -> failed failure
        SourceExposureFinished (Right exposed) -> do
            matched <- startTheoremMatch environment context template (obviousProofStatement exposed) substitutions
            next (ApplicationMatchFact candidate exposed matched)
        _ -> advanceSourceExposure environment context step >>= next . ApplicationExposeFact candidate
    ApplicationMatchFact candidate@(ApplicationFact template _ _ firstFailure _ _) exposed step -> case step of
        TheoremMatchFinished (Left failure) -> failed failure
        TheoremMatchFinished (Right TemplateMismatch{}) -> continueFact candidate firstFailure
        TheoremMatchFinished (Right TemplateHigherOrderUnsupported{}) ->
            continueFact candidate (firstFailure <|> Just ObviousUnsupportedHigherOrderInstantiation)
        TheoremMatchFinished (Right (TemplateMatched updated _progress)) ->
            closeFocusedTemplate template updated >>= \case
                Left failure -> failed failure
                Right Template.TemplateOpen{} -> continueFact candidate
                    (firstFailure <|> Just ObviousUnsupportedHigherOrderInstantiation)
                Right (Template.TemplateClosed premiseTarget) -> next
                    (ApplicationConvertFact candidate updated (obviousProofDependencies exposed)
                        (HeadProofConvert SmallPreparation (obviousBuiltProof exposed) premiseTarget))
        _ -> advanceTheoremMatch environment step >>= next . ApplicationMatchFact candidate exposed
    ApplicationConvertFact candidate@(ApplicationFact template substitutions continuation firstFailure fact rest)
            updated dependencies step -> case step of
        HeadProofFinished (Left failure) -> failed failure
        HeadProofFinished (Right proof) -> continueApplication input continuation updated (ObviousProof proof dependencies)
            (AfterMatchedPremise template substitutions continuation firstFailure fact rest : frames)
        _ -> advanceHeadProof environment context step >>= next . ApplicationConvertFact candidate updated dependencies
    ApplicationNextFact template substitutions continuation firstFailure fact rest ->
        projectedChildren environment context fact >>= \case
            Left failure -> failed failure
            Right projected -> next (ApplicationFacts template substitutions
                continuation firstFailure (projected <> rest))
    ApplicationJoin fallback left right substitutions continuation ->
        pure (ApplicationPending input
            (ApplicationPremise False left substitutions (ContinueLeftPremise right continuation))
            (AfterJoinedPremise fallback : frames))
    ApplicationFinish substitutions selected -> do
        missing <- missingFocusedTemplateSlots (spineBinderEnvironment spine) substitutions
        case missing of
            Left failure -> failed failure
            Right (Template.MatcherSlot position : _rest) -> failed (ObviousUndeterminedParameter position)
            Right [] -> pure (ApplicationPending input
                (ApplicationReconstruct substitutions source sourceDependencies selected steps)
                (if requirement == MustUseCanonicalDefinition
                        && not (candidateUsesCanonicalDefinition sourceDependencies)
                    then AfterApplicationBuild Seq.empty : frames else frames))
    ApplicationReconstruct substitutions current dependencies remaining pending ->
        next (ApplicationPrepareHead substitutions dependencies remaining pending (HeadProofInspect current))
    ApplicationPrepareHead substitutions dependencies remaining pending step -> case step of
        HeadProofFinished (Left failure) -> failed failure
        HeadProofFinished (Right prepared) -> next
            (ApplicationPrepared substitutions prepared dependencies remaining pending)
        _ -> advanceHeadProof environment context step >>= next
            . ApplicationPrepareHead substitutions dependencies remaining pending
    ApplicationPrepared substitutions prepared dependencies remaining pending -> do
        result <- Except.runExceptT case pending of
            [] -> case Seq.viewl remaining of
                Seq.EmptyL -> do
                    same <- Except.ExceptT (scopedIdentity (KernelProof.builtProofStatement prepared) target)
                    pure (if same then ApplicationReturn (AttemptSucceeded (ObviousProof prepared dependencies))
                        else ApplicationConvertResult dependencies (HeadProofConvert SmallPreparation prepared target), Nothing)
                _premise Seq.:< _rest -> Except.throwE malformedApplicationSpine
            Elimination.Instantiate binderType slot : rest -> do
                (foundType, _body) <- maybe (Except.throwE malformedApplicationSpine) pure
                    (openScopedForall (KernelProof.builtProofStatement prepared))
                sameType <- Except.ExceptT (coreTypeIdentity binderType foundType)
                unless sameType (Except.throwE malformedApplicationSpine)
                argument <- maybe
                    (Except.throwE (ObviousUndeterminedParameter
                        (case slot of Template.MatcherSlot position -> position)))
                    pure (Template.lookupTemplateSubstitution slot substitutions)
                pure (ApplicationEliminateForall SmallPreparation substitutions prepared argument
                    dependencies remaining rest, Nothing)
            Elimination.ProjectLeft : rest -> pure
                (ApplicationProject SmallPreparation True substitutions prepared dependencies remaining rest, Nothing)
            Elimination.ProjectRight : rest -> pure
                (ApplicationProject SmallPreparation False substitutions prepared dependencies remaining rest, Nothing)
            Elimination.Apply template : rest -> case Seq.viewl remaining of
                Seq.EmptyL -> Except.throwE malformedApplicationSpine
                selected@(ObviousProof premise premiseDependencies) Seq.:< remainingPremises -> do
                    (premiseTarget, _conclusion) <- maybe (Except.throwE malformedApplicationSpine) pure
                        (openScopedImplication (KernelProof.builtProofStatement prepared))
                    closure <- Except.ExceptT (closeFocusedTemplate template substitutions)
                    case closure of
                        Template.TemplateOpen{} -> Except.throwE malformedApplicationSpine
                        Template.TemplateClosed{} -> do
                            same <- Except.ExceptT (scopedIdentity (KernelProof.builtProofStatement premise) premiseTarget)
                            let recipe = case frames of
                                    AfterApplicationBuild{} : _
                                        | not (candidateUsesCanonicalDefinition dependencies)
                                        , not (candidateUsesCanonicalDefinition premiseDependencies) ->
                                            Just (ApplicationSupportRecipe selected substitutions prepared
                                                dependencies premiseTarget remainingPremises rest)
                                    _ -> Nothing
                            pure (ApplicationConvertPremise substitutions prepared dependencies premiseDependencies
                                remainingPremises rest (if same then HeadProofFinished (Right premise)
                                    else HeadProofConvert SmallPreparation premise premiseTarget), recipe)
        case result of
            Left failure -> failed failure
            Right (following, Nothing) -> next following
            Right (following, Just recipe) -> do
                admitted <- consumeSearchStep
                case (admitted, frames) of
                    (False, _) -> failed (ObviousResourceExhausted ObviousFocusedWorkLimit)
                    (True, AfterApplicationBuild recipes : rest) -> pure
                        (ApplicationPending input following (AfterApplicationBuild (recipes Seq.|> recipe) : rest))
                    _ -> failed malformedApplicationSpine
    ApplicationConvertPremise substitutions prepared dependencies premiseDependencies remaining rest step -> case step of
        HeadProofFinished (Left failure) -> failed failure
        HeadProofFinished (Right premise) -> combineCandidateDependencies dependencies premiseDependencies >>= \case
            Left failure -> failed failure
            Right combined -> next (ApplicationEliminateImplication SmallPreparation substitutions
                prepared premise combined remaining rest)
        _ -> advanceHeadProof environment context step >>= next
            . ApplicationConvertPremise substitutions prepared dependencies premiseDependencies remaining rest
    ApplicationEliminateForall effort substitutions prepared argument dependencies remaining rest ->
        runKernelPreparation effort (KernelProof.countedForallEliminationProof
                context prepared argument) >>= \case
            NeedsMoreEffort offered -> next (ApplicationEliminateForall (FullPreparation offered)
                substitutions prepared argument dependencies remaining rest)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right eliminated) -> next
                (ApplicationReconstruct substitutions eliminated dependencies remaining rest)
    ApplicationEliminateImplication effort substitutions prepared premise dependencies remaining rest ->
        runKernelPreparation effort (KernelProof.countedImplicationEliminationProof
                context prepared premise) >>= \case
            NeedsMoreEffort offered -> next (ApplicationEliminateImplication (FullPreparation offered)
                substitutions prepared premise dependencies remaining rest)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right eliminated) -> next
                (ApplicationReconstruct substitutions eliminated dependencies remaining rest)
    ApplicationProject effort selectLeft substitutions prepared dependencies remaining rest ->
        case splitScopedConjunction (KernelProof.builtProofStatement prepared) of
            Nothing -> failed malformedApplicationSpine
            Just (left, right) ->
                runKernelPreparation effort ((if selectLeft then KernelProof.countedConjunctionLeftProof else KernelProof.countedConjunctionRightProof)
                        context (scopedCoreTerm left) (scopedCoreTerm right) prepared) >>= \case
                    NeedsMoreEffort offered -> next (ApplicationProject (FullPreparation offered)
                        selectLeft substitutions prepared dependencies remaining rest)
                    PreparationFinished (Left failure) -> failed failure
                    PreparationFinished (Right projected) -> next
                        (ApplicationReconstruct substitutions projected dependencies remaining rest)
    ApplicationConvertResult dependencies step -> case step of
        HeadProofFinished result -> done (either AttemptFailed (AttemptSucceeded . (`ObviousProof` dependencies)) result)
        _ -> advanceHeadProof environment context step >>= next . ApplicationConvertResult dependencies
    ApplicationContinue continuation substitutions proof ->
        continueApplication input continuation substitutions proof frames
    ApplicationReturn result -> case frames of
        [] -> pure (ApplicationFinished result)
        frame : rest -> resumeApplicationFrame input frame result rest
  where
    CompiledTheoremSpine steps _conclusion _schema = spine
    next nextTask
        | applicationAdministrative nextTask = advanceApplication environment input nextTask frames
        | otherwise = pure (ApplicationPending input nextTask frames)
    done = next . ApplicationReturn
    failed = done . AttemptFailed
    continueFact (ApplicationFact template substitutions continuation _ fact rest) failure =
        next (ApplicationNextFact template substitutions continuation failure fact rest)

continueApplication
    :: ApplicationInput global
    -> PremiseContinuation global
    -> Template.TemplateSubstitution global
    -> ObviousProof global
    -> [ApplicationFrame global]
    -> State (ObviousSearchState global) (ApplicationStep global)
continueApplication input continuation substitutions proof frames = case continuation of
    ContinueTheoremPremises allowSearch selected steps ->
        next (ApplicationSteps allowSearch substitutions (selected Seq.|> proof) steps)
    ContinueLeftPremise right following ->
        next (ApplicationPremise False right substitutions (ContinueRightPremise proof following))
    ContinueRightPremise left following -> do
        built <- runCountedKernel (KernelProof.countedConjunctionIntroductionProof
            (obviousBuiltProof left) (obviousBuiltProof proof))
        case built of
            Left failure -> failed failure
            Right combined -> do
                dependencies <- combineCandidateDependencies
                    (obviousProofDependencies left) (obviousProofDependencies proof)
                case dependencies of
                    Left failure -> failed failure
                    Right used -> next (ApplicationContinue following substitutions (ObviousProof combined used))
  where
    next task = pure (ApplicationPending input task frames)
    failed = next . ApplicationReturn . AttemptFailed

resumeApplicationChild
    :: ApplicationInput global
    -> ScopedCheckedCore global
    -> Template.TemplateSubstitution global
    -> PremiseContinuation global
    -> [ApplicationFrame global]
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (ApplicationStep global)
resumeApplicationChild input target substitutions continuation frames = \case
    Right proof -> continueApplication input continuation substitutions proof frames
    Left failure -> pure (ApplicationPending input
        (ApplicationReturn (AttemptFailed
            (if isTerminalFocusedFailure failure || repeated failure
                then failure else ObviousAntecedentUnavailable target)))
        frames)
  where
    repeated ObviousRepeatedState{} = True
    repeated _failure = False

resumeApplicationFrame
    :: ApplicationInput global
    -> ApplicationFrame global
    -> Attempt global
    -> [ApplicationFrame global]
    -> State (ObviousSearchState global) (ApplicationStep global)
resumeApplicationFrame input@(ApplicationInput _ allowRecursive _requirement _contextId
        (CompiledTheoremSpine steps _conclusion _schema) _source _dependencies _context _target _sourceKey)
        frame result frames = case frame of
    AfterApplicationBuild recipes
        | AttemptSucceeded proof <- result
        , not (candidateUsesCanonicalDefinition (obviousProofDependencies proof)) ->
            pure (ApplicationFound proof (ApplicationSupport input recipes frames))
        | otherwise -> done
    AfterDirectPlan substitutions
        | completed || not allowRecursive -> done
        | otherwise -> next (ApplicationSteps True substitutions Seq.empty steps)
    AfterWholePremise template substitutions continuation
        | completed -> done
        | otherwise -> case Template.splitCompiledConjunction template of
            Nothing -> done
            Just (left, right) -> next (ApplicationJoin result left right substitutions continuation)
    AfterJoinedPremise fallback
        | completed -> done
        | otherwise -> next (ApplicationReturn fallback)
    AfterMatchedPremise template substitutions continuation firstFailure fact rest
        | completed -> done
        | otherwise -> next (ApplicationNextFact template substitutions continuation
            (remember firstFailure) fact rest)
  where
    next task = pure (ApplicationPending input task frames)
    done = next (ApplicationReturn result)
    completed = case result of
        AttemptSucceeded{} -> True
        AttemptFailed failure -> isTerminalFocusedFailure failure
        AttemptNotApplicable -> False
    remember firstFailure = case result of
        AttemptFailed failure -> firstFailure <|> Just failure
        _result -> firstFailure

malformedApplicationSpine :: ObviousFailure global
malformedApplicationSpine = ObviousIntegrityFailure
    (KernelProof.ProofStructuralCompositionMismatch
        "the compiled theorem spine did not replay exactly")

data ApplicationStart global
    = ApplicationComplete !(Attempt global)
    | ApplicationMatched !(Maybe (CandidateSeed global)) !Natural !(ApplicationStep global)
    | ApplicationMatching !(Maybe (CandidateSeed global))
        !(ApplicationInput global) !(TheoremMatchStep global)

startApplicationWithParameters
    :: Ord global
    => ApplicationParameterPolicy -> Bool -> CandidateObservationScope -> ProofRequirement
    -> SearchEnvironment global -> FocusedContextId -> KernelProof.ProofContext global
    -> ScopedCheckedCore global -> PreparedTheoremSource global
    -> State (ObviousSearchState global) (ApplicationStart global)
startApplicationWithParameters parameterPolicy allowRecursivePremises observationScope requirement environment contextId context target
        (PreparedTheoremSource source@(ObviousProof sourceProof sourceImports) preparedSpine) = do
    let CompiledTheoremSpine _steps resultTemplate _schema = preparedSpine
        candidateView = case obviousProofCandidateSource source of
            Just (CandidateSourceAnnotation _base _sourceOrder projectionDepth _definitions _truncated) ->
                CandidatePreparedTheoremView projectionDepth
            Nothing -> CandidatePreparedTheoremView 0
    candidate <- beginCandidate observationScope candidateView
        (Template.compiledTemplateTerm resultTemplate) source
    let input = ApplicationInput parameterPolicy allowRecursivePremises requirement contextId preparedSpine sourceProof sourceImports context target (obviousProofSourceKey source)
    started <- startTheoremMatch environment context resultTemplate target Template.emptyTemplateSubstitution
    matched <- advanceTheoremMatch environment started
    case matched of
        TheoremMatchFinished result -> finishApplicationMatch candidate input result >>= \case
            Left rejected -> pure (ApplicationComplete rejected)
            Right (progress, following) -> pure (ApplicationMatched candidate progress following)
        pending -> pure (ApplicationMatching candidate input pending)

finishApplicationMatch
    :: Ord global
    => Maybe (CandidateSeed global) -> ApplicationInput global
    -> Either (ObviousFailure global) (TemplateMatchResult global)
    -> State (ObviousSearchState global) (Either (Attempt global) (Natural, ApplicationStep global))
finishApplicationMatch candidate input@(ApplicationInput parameterPolicy _ _ _ spine@(CompiledTheoremSpine steps _ _)
        _source _sourceImports _context _target _sourceKey) matched =
    case matched of
        Left failure -> pure (Left (AttemptFailed failure))
        Right (TemplateMismatch (TemplateMismatchEvidence mismatch difference progress)) -> do
            traverse_ (\seed -> recordCandidateOutcome
                seed (ComparisonRejected mismatch) progress difference Nothing) candidate
            pure (Left AttemptNotApplicable)
        Right (TemplateHigherOrderUnsupported progress) -> do
            traverse_ (\seed -> recordCandidateOutcome seed
                (ComparisonRejected MismatchDetailUnavailable) progress Nothing Nothing) candidate
            pure (Left (AttemptFailed ObviousUnsupportedHigherOrderInstantiation))
        Right (TemplateMatched substitutions matchProgress)
            | null steps -> pure (Left AttemptNotApplicable)
            | EndpointParameters{} <- parameterPolicy -> do
                missing <- missingFocusedTemplateSlots (spineBinderEnvironment spine) substitutions
                case missing of
                    Left failure -> pure (Left (AttemptFailed failure))
                    Right (_ : _) -> pure (Left AttemptNotApplicable)
                    Right [] -> do
                        policy <- State.gets (policyEndpoints . searchPolicy)
                        used <- State.gets searchEndpointAttempts
                        case policy of
                            EndpointsDisabled -> pure (Left AttemptNotApplicable)
                            EndpointApplications limit
                                | used >= limit -> do
                                    State.modify' (\state -> state {searchEndpointsDeferred = True})
                                    pure (Left AttemptNotApplicable)
                                | otherwise -> do
                                    State.modify' (\state -> state {searchEndpointAttempts = used + 1})
                                    pure (Right (matchProgress,
                                        ApplicationPending input (ApplicationStartPremises substitutions) []))
            | otherwise -> pure (Right (matchProgress,
                ApplicationPending input (ApplicationStartPremises substitutions) []))

observeMatchedTheorem
    :: Ord global
    => Maybe (CandidateSeed global)
    -> Natural
    -> Attempt global
    -> State (ObviousSearchState global) (Attempt global)
observeMatchedTheorem candidate progress attempt =
    case attempt of
        AttemptSucceeded proof -> do
            owned <- candidateSucceeded candidate progress Nothing proof
            pure (AttemptSucceeded owned)
        AttemptFailed ObviousUndeterminedParameter{} -> do
            traverse_
                (\seed -> recordCandidateOutcome
                    seed (ProofIncomplete ParameterUndetermined)
                    progress Nothing Nothing)
                candidate
            pure attempt
        AttemptFailed ObviousAntecedentUnavailable{} -> do
            cause <- case candidate of
                Nothing -> pure Nothing
                Just _seed ->
                    claimAuxiliaryRequirementCauseIfPresent
                        AuxiliaryTheoremAntecedent
            traverse_
                (\seed -> recordCandidateOutcome
                    seed (ProofIncomplete AntecedentUnavailable)
                    progress Nothing cause)
                candidate
            pure attempt
        AttemptFailed ObviousCanonicalDefinitionEvidenceRequired -> do
            cause <- case candidate of
                Nothing -> pure Nothing
                Just _seed ->
                    Just
                        <$> claimAuxiliaryRequirementCause
                            AuxiliaryTheoremAntecedent
            traverse_
                (\seed -> recordCandidateOutcome
                    seed (ProofIncomplete AntecedentUnavailable)
                    progress Nothing cause)
                candidate
            pure attempt
        AttemptNotApplicable -> do
            traverse_
                (\seed -> recordCandidateOutcome
                    seed
                    (ComparisonRejected MismatchDetailUnavailable)
                    progress Nothing Nothing)
                candidate
            pure attempt
        AttemptFailed _failure -> pure attempt


data TransportCursor global
    = TransportArguments ![ObviousProof global]
    | TransportDiscover !(PropositionTransportScan global) ![ObviousProof global]
    | TransportRight !PreparationEffort !(ObviousProof global)
        !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | TransportLeft !PreparationEffort !(ObviousProof global)
        !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | TransportDescend !(PropositionTransportScan global) !(ObviousProof global) ![ObviousProof global]
    | TransportBuildGraph !(Seq (ObviousProof global))
        !(FocusedEqualityGraph global) ![ObviousProof global]
    | TransportCompose !(FocusedEqualityGraph global) ![ObviousProof global]
    | TransportEquality !ProofRequirement !(FocusedEqualityGraph global)
        !(ObviousProof global) !(TransportCursor global) !(EqualityProofStep global)
    | TransportComposeBuild !PreparationEffort !(Maybe (CandidateSeed global))
        !(ObviousProof global) !(ObviousProof global) !(TransportCursor global)
    | TransportReconstruct !(Maybe (CandidateSeed global)) !CandidateDependencies !(ViewProofStep global)
        !(Maybe (ObviousProof global, TransportContinuation global))

data TransportContinuation global = TransportContinuation
    !(ObviousProof global) !(Maybe (CandidateSeed global)) !FocusedEqualityDirection

data TransportStep global
    = TransportPending !(TransportCursor global)
    | TransportOffer !(ObviousProof global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(TransportCursor global)
    | TransportChild !(ScopedCheckedCore global) !(TransportContinuation global)
    | TransportSupport !(ObviousProof global) !(TransportContinuation global)
    | TransportFound !(ObviousProof global) !(TransportStep global)
    | TransportFinished !(Attempt global)

advanceTransport
    :: Ord global
    => EqualityProducer -> CandidateObservationScope -> ProofRequirement -> SearchEnvironment global
    -> KernelProof.ProofContext global -> ScopedCheckedCore global -> TransportCursor global
    -> State (ObviousSearchState global) (TransportStep global)
advanceTransport equationProducer observationScope requirement environment@(SearchEnvironment typing _ _ _) context target = \case
    TransportArguments [] -> finished AttemptNotApplicable
    -- A concrete equation can expose a named argument needed by a theorem's
    -- conclusion. Lift only an exact immediate argument match to proposition
    -- equality; the existing transport owner handles both directions, cycles,
    -- premise search and reconstruction. No source unfolding is needed here.
    TransportArguments (source : rest) -> do
        result <- Except.runExceptT do
            admitted <- lift consumeSearchStep
            unless admitted (Except.throwE (ObviousResourceExhausted ObviousFocusedWorkLimit))
            projected <- Except.ExceptT (projectedChildrenFromExposed context source)
            let following = TransportArguments (projected <> rest)
            case (scopedCoreTerm target, splitScopedEquality (obviousProofStatement source)) of
                (CApp predicate argument@CBound{}, Just (_operandType, left, right)) -> do
                    checkedArgument <- Except.ExceptT (checkedTerm argument)
                    matchesLeft <- Except.ExceptT (scopedIdentity checkedArgument left)
                    matchesRight <- Except.ExceptT (scopedIdentity checkedArgument right)
                    if matchesLeft == matchesRight then pure (TransportPending following) else do
                        checkedPredicate <- Except.ExceptT (checkedTerm predicate)
                        reflexive <- Except.ExceptT (runCountedKernel (KernelProof.countedEqualityReflexivityProof context checkedPredicate))
                        congruence <- Except.ExceptT (runCountedKernel (KernelProof.countedEqualityCongruenceApplicationProof context
                                reflexive (obviousBuiltProof source)))
                        case splitScopedEquality (KernelProof.builtProofStatement congruence) of
                            Just (TyProp, before, after) -> pure (TransportOffer
                                (deriveCandidateProof congruence source) before after following)
                            _ -> Except.throwE (ObviousIntegrityFailure
                                (KernelProof.ProofStructuralCompositionMismatch "predicate congruence lost its proposition equality"))
                _ -> pure (TransportPending following)
        either failed pure result
    TransportDiscover (PropositionTransportScan retained hasEquality _producer) []
        | hasEquality -> next (TransportBuildGraph retained
            emptyFocusedEqualityGraph (toList retained))
        | otherwise -> finished AttemptNotApplicable
    TransportDiscover (PropositionTransportScan retained hasEquality producer) (source : rest) ->
        exposeProof environment context source >>= \case
            Left failure -> failed failure
            Right prepared -> do
                let statement = obviousProofStatement prepared
                    isEquality = case scopedCoreTerm statement of
                        CEq{} -> True
                        _term -> False
                    scan = PropositionTransportScan
                        (retained Seq.|> prepared) (hasEquality || isEquality) producer
                    following = TransportDescend scan prepared rest
                eligible <- if producer == EvidenceOnly then pure (Right False)
                    else case (scopedCoreTerm statement, scopedCoreTerm target) of
                        (CApp{}, CApp{}) -> do
                            sourceHead <- focusedObligationHead (scopedCoreTerm statement)
                            targetHead <- focusedObligationHead (scopedCoreTerm target)
                            pure ((==) <$> sourceHead <*> targetHead)
                        _ -> pure (Right False)
                case eligible of
                    Left failure -> failed failure
                    Right True -> next (TransportEquality AnyObviousProof emptyFocusedEqualityGraph prepared following
                        (startEqualityProof SuppliedEquations DeferExactCandidateConversion AnyObviousProof
                            emptyFocusedEqualityGraph statement target))
                    Right False -> pure (case splitScopedEquality statement of
                        Just (TyProp, left, right) -> TransportOffer prepared left right following
                        _head -> TransportPending following)
    TransportRight effort source left right -> compareAt effort right >>= \case
        NeedsMoreEffort offered -> next (TransportRight (FullPreparation offered) source left right)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right Conversion.Convertible) -> child source left FocusedEqualityForward
        PreparationFinished (Right Conversion.NotConvertible) -> next (TransportLeft SmallPreparation source left right)
    TransportLeft effort source left right -> compareAt effort left >>= \case
        NeedsMoreEffort offered -> next (TransportLeft (FullPreparation offered) source left right)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right Conversion.Convertible) -> child source right FocusedEqualityReverse
        PreparationFinished (Right Conversion.NotConvertible) -> finished AttemptNotApplicable
    TransportDescend scan source rest -> projectedChildrenFromExposed context source >>= \case
        Left failure -> failed failure
        Right projected -> next (TransportDiscover scan (projected <> rest))
    TransportBuildGraph retained graph [] ->
        next (TransportCompose graph (toList retained))
    TransportBuildGraph retained graph (source : rest) -> do
        hasWork <- consumeSearchStep
        if not hasWork then failed (ObviousResourceExhausted ObviousFocusedWorkLimit)
            else addFocusedEqualityFromExposed graph source >>= \case
                Left failure -> failed failure
                Right updated -> next (TransportBuildGraph retained updated rest)
    TransportReconstruct candidate dependencies (ViewProofFinished result) support -> case result of
        Left failure -> failed failure
        Right proof -> do
            selected <- candidateSucceeded candidate 1 Nothing (ObviousProof proof dependencies)
            pure (case support of
                Nothing -> TransportFinished (AttemptSucceeded selected)
                Just (premise, continuation) -> TransportFound selected (TransportSupport premise continuation))
    TransportReconstruct candidate dependencies step support -> advanceViewProof environment context step
        >>= next . (\following -> TransportReconstruct candidate dependencies following support)
    TransportCompose _graph [] -> finished AttemptNotApplicable
    TransportCompose graph (source : rest) -> do
        proof <- equalityFor AnyObviousProof graph source
        next (TransportEquality AnyObviousProof graph source (TransportCompose graph rest)
            proof)
    TransportEquality demanded graph source rest (EqualityProofPending input action continuations) ->
        advanceEqualityProof environment context input action continuations
            >>= next . TransportEquality demanded graph source rest
    TransportEquality _ _ _ _ EqualityProofDemand{} -> failed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "transport demand bypassed its focused owner"))
    TransportEquality _ _ _ _ EqualityCompletionDemand{} -> failed (ObviousIntegrityFailure
        (KernelProof.ProofStructuralCompositionMismatch "argument transport bypassed its focused owner"))
    TransportEquality _demanded _graph _source _rest (EqualityProofFinished (Left failure)) -> failed failure
    TransportEquality _demanded _graph _source following (EqualityProofFinished (Right Nothing)) ->
        next following
    TransportEquality demanded graph source rest (EqualityProofFinished (Right (Just equality))) -> do
        candidate <- beginCandidate observationScope (transportCandidateView source) (obviousProofStatement source) source
        following <- if requirement == MustUseCanonicalDefinition && demanded == AnyObviousProof
                && not (satisfiesRequirement requirement source || satisfiesRequirement requirement equality)
            then TransportEquality MustUseCanonicalDefinition graph source rest
                <$> equalityFor MustUseCanonicalDefinition graph source
            else pure rest
        next (TransportComposeBuild SmallPreparation candidate source equality following)
    TransportComposeBuild effort candidate source equality following ->
        runKernelPreparation effort (KernelProof.countedEqualityModusPonensProof
            context (obviousBuiltProof equality) (obviousBuiltProof source)) >>= \case
            NeedsMoreEffort offered -> next (TransportComposeBuild (FullPreparation offered) candidate source equality following)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right built) -> combineCandidateDependencies
                    (obviousProofDependencies source) (obviousProofDependencies equality) >>= \case
                Left failure -> failed failure
                Right dependencies -> do
                    proof <- candidateSucceeded candidate 1 Nothing (ObviousProof built dependencies)
                    pure (if satisfiesRequirement requirement proof then TransportFinished (AttemptSucceeded proof)
                        else TransportFound proof (TransportPending following))
  where
    next = pure . TransportPending
    finished = pure . TransportFinished
    failed = finished . AttemptFailed
    checkedTerm term = runCountedKernel (KernelProof.countedScopedTerm context term)
    equalityFor demanded graph source = do
        pure (startEqualityProof equationProducer DeferExactCandidateConversion demanded
            graph (obviousProofStatement source) target)
    compareAt effort right = runConversionPreparation effort
        (\limit -> Conversion.convertibleChecked typing limit target right)
    child source premise direction = do
        candidate <- beginCandidate observationScope (transportCandidateView source) (obviousProofStatement source) source
        pure (TransportChild premise (TransportContinuation source candidate direction))

resumeTransport
    :: Ord global
    => ProofRequirement -> ScopedCheckedCore global -> TransportContinuation global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (TransportStep global)
resumeTransport requirement target continuation@(TransportContinuation source candidate direction) = \case
    Left failure -> do
        unless (isFocusedInfrastructureFailure failure) do
            cause <- case (failure, candidate) of
                (ObviousCanonicalDefinitionEvidenceRequired, Just _seed) ->
                    Just <$> claimAuxiliaryRequirementCause AuxiliaryTransportPremise
                _ -> pure Nothing
            traverse_ (\seed -> recordCandidateOutcome seed
                (ProofIncomplete TransportPremiseUnavailable) 1 Nothing cause) candidate
        pure (TransportFinished (AttemptFailed failure))
    Right selected@(ObviousProof premise premiseDependencies) -> do
        combined <- combineCandidateDependencies (obviousProofDependencies source) premiseDependencies
        pure case combined of
            Left failure -> TransportFinished (AttemptFailed failure)
            Right dependencies ->
                let equation = obviousBuiltProof source
                    reconstruction = GoalViewReconstruction target equation
                        (KernelProof.builtProofStatement premise) GoalPropositionTransport
                    step = case direction of
                        FocusedEqualityForward -> ViewProofTransport SmallPreparation FoldGoalView reconstruction equation premise
                        FocusedEqualityReverse -> ViewProofReverse SmallPreparation reconstruction premise
                    support = if requirement == MustUseCanonicalDefinition && not (candidateUsesCanonicalDefinition dependencies)
                        then Just (selected, continuation) else Nothing
                in TransportPending (TransportReconstruct candidate dependencies step support)

transportIsDeferred :: TransportCursor global -> Bool
transportIsDeferred = \case
    TransportRight effort _ _ _ -> preparationIsDeferred effort
    TransportLeft effort _ _ _ -> preparationIsDeferred effort
    TransportComposeBuild effort _ _ _ _ -> preparationIsDeferred effort
    TransportEquality _ _ _ _ step -> equalityProofIsDeferred step
    TransportReconstruct _ _ step _ -> viewProofIsDeferred step
    _ -> False

transportCandidateView :: ObviousProof global -> CandidateComparisonView
transportCandidateView proof = case obviousProofCandidateSource proof of
    Just (CandidateSourceAnnotation _base _sourceOrder projectionDepth _factDefinitions _truncated) ->
        CandidateEqualityTransportView projectionDepth
    Nothing -> CandidateEqualityTransportView 0

data GoalDefinitionCursor global
    = GoalDefinitionPrepareRoots !(RootObservationStep global)
    | GoalDefinitionObservations
        !(Maybe (ObviousFailure global)) ![RootObservation global]
    | GoalDefinitionResolving
        !(Maybe (ObviousFailure global)) ![RootObservation global]
        !(RootObservation global) !(DefinitionViewCursor global)
        !(Seq (AvailableDefinitionView global))
    | GoalDefinitionSpecialize !(GoalDefinitionCursor global) !(RootObservation global)
        !Natural !(DefinitionSpecializationStep global)
    | GoalDefinitionExpose !(GoalDefinitionCursor global) !Natural !CandidateDependencies !(ObservationExposureStep global)
    | GoalDefinitionBuild !CandidateDependencies !(ViewProofStep global)
    | GoalDefinitionViews
        !(Maybe (ObviousFailure global)) ![RootObservation global]
        !(RootObservation global) !(Maybe (ObviousFailure global))
        ![AvailableDefinitionView global]

data GoalDefinitionContinuation global = GoalDefinitionContinuation
    !(GoalDefinitionCursor global)
    !(GoalViewReconstruction global)
    !CandidateDependencies

data GoalDefinitionStep global
    = GoalDefinitionPending !(GoalDefinitionCursor global)
    | GoalDefinitionChild !CandidateObservationScope !(ScopedCheckedCore global)
        !(GoalDefinitionContinuation global)
    | GoalDefinitionFinished !(Attempt global)

startGoalDefinition
    :: SearchEnvironment global -> KernelProof.ProofContext global -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (GoalDefinitionStep global)
startGoalDefinition (SearchEnvironment _ _ _ (DefinitionViewCatalogue _ _ locals _)) context target = do
    roots <- startRootObservations target
    -- A named local term may hide the head needed by a supplied closure lemma.
    -- Expose that argument through its checked definition before unfolding the
    -- outer predicate. This adds no traversal under binders or imported terms.
    observed <- case (null locals, roots, scopedCoreTerm target) of
        (False, RootObservationFinished (Right existing), CApp predicate argument) -> fmap RootObservationFinished $ Except.runExceptT do
            application <- Except.ExceptT (definedApplicationCounted argument)
            case application of
                Just (subject@CBound{}, arguments) -> do
                    checked <- Except.ExceptT (runCountedKernel (KernelProof.countedScopedTerm context argument))
                    pure (PredicateArgumentObservation subject arguments checked predicate : existing)
                _ -> pure existing
        _ -> pure roots
    pure (GoalDefinitionPending (GoalDefinitionPrepareRoots observed))

advanceGoalDefinition
    :: Ord global
    => CandidateObservationScope
    -> SearchEnvironment global
    -> Set FocusedObligationId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> GoalDefinitionCursor global
    -> State (ObviousSearchState global) (GoalDefinitionStep global)
advanceGoalDefinition observationScope environment active context target cursor = case cursor of
    GoalDefinitionPrepareRoots (RootObservationFinished (Left failure)) ->
        pure (GoalDefinitionFinished (AttemptFailed failure))
    GoalDefinitionPrepareRoots (RootObservationFinished (Right roots)) ->
        -- Observe the explicitly cited side of an equality before expanding
        -- an uncited operand. The same ordering keeps a cited predicate ahead
        -- of an incidental alias in its argument. Local operands come next,
        -- before expanding imported representations; all other views remain.
        let SearchEnvironment _ imports _ (DefinitionViewCatalogue _ buckets locals _) = environment
            cited = Set.fromList (map obviousImportIndex imports)
            explicitlyCited observation = case observationSubject observation of
                CGlobal object -> any
                    (\kind -> any (\(_, imported) -> obviousImportIndex imported `Set.member` cited)
                        (Map.findWithDefault Seq.empty (kind, object) buckets))
                    [DefinitionPointwiseView, DefinitionExactView, DefinitionMembershipView]
                _ -> False
            localOperand observation = not (null locals) && case observationSubject observation of
                CBound{} -> True
                _ -> False
            (selected, remaining) = partition explicitlyCited roots
            (aliases, others) = partition localOperand remaining
        in pure (GoalDefinitionPending (GoalDefinitionObservations Nothing (selected <> aliases <> others)))
    GoalDefinitionPrepareRoots step -> advanceRootObservations environment step
        >>= next . GoalDefinitionPrepareRoots
    GoalDefinitionObservations firstFailure [] ->
        pure (GoalDefinitionFinished (maybe AttemptNotApplicable AttemptFailed firstFailure))
    GoalDefinitionObservations firstFailure (observation : rest) -> do
        views <- startDefinitionViews AllDefinitionViews environment context observation
        case views of
            Left failure -> rejectGoalDefinition active
                (GoalDefinitionObservations firstFailure rest) failure
            Right resolving -> pure (GoalDefinitionPending
                (GoalDefinitionResolving firstFailure rest observation resolving Seq.empty))
    GoalDefinitionResolving firstFailure rest observation resolving completed ->
        advanceDefinitionViews environment context resolving >>= \case
            Left failure -> rejectGoalDefinition active
                (GoalDefinitionObservations firstFailure rest) failure
            Right DefinitionViewsFinished -> pure (GoalDefinitionPending
                (GoalDefinitionViews firstFailure rest observation Nothing (toList completed)))
            Right (DefinitionViewResolved view remaining) -> pure (GoalDefinitionPending
                (GoalDefinitionResolving firstFailure rest observation remaining
                    (maybe completed (completed Seq.|>) view)))
    GoalDefinitionViews firstFailure rest _observation viewFailure [] ->
        pure (GoalDefinitionPending
            (GoalDefinitionObservations (firstFailure <|> viewFailure) rest))
    GoalDefinitionViews firstFailure rest observation viewFailure (view : views) ->
        pure (GoalDefinitionPending (GoalDefinitionSpecialize
            (GoalDefinitionViews firstFailure rest observation viewFailure views) observation
            (availableDefinitionViewOrdinal view) (startDefinitionSpecialization observation view)))
    GoalDefinitionSpecialize remaining observation ordinal (DefinitionSpecialized result) -> case result of
        Left failure -> rejectGoalDefinition active remaining failure
        Right Nothing -> pure (GoalDefinitionPending remaining)
        Right (Just (ObviousProof equation dependencies)) ->
            startObservationExposure target observation equation
                >>= next . GoalDefinitionExpose remaining ordinal dependencies
    GoalDefinitionExpose remaining _ _ (ObservationExposed (Left failure)) -> rejectGoalDefinition active remaining failure
    GoalDefinitionExpose remaining ordinal dependencies (ObservationExposed (Right reconstruction@(GoalViewReconstruction _ _ childTarget _))) -> do
        childObservation <- extendRootGoalView ordinal observationScope
        pure (GoalDefinitionChild childObservation childTarget (GoalDefinitionContinuation remaining reconstruction dependencies))
    GoalDefinitionExpose remaining ordinal dependencies step -> advanceObservationExposure environment context step
        >>= next . GoalDefinitionExpose remaining ordinal dependencies
    GoalDefinitionBuild dependencies (ViewProofFinished result) -> pure (GoalDefinitionFinished
        (either AttemptFailed (AttemptSucceeded . (`ObviousProof` dependencies)) result))
    GoalDefinitionBuild dependencies step -> advanceViewProof environment context step
        >>= next . GoalDefinitionBuild dependencies
    GoalDefinitionSpecialize remaining observation ordinal step ->
        advanceDefinitionSpecialization environment context observation step
            >>= next . GoalDefinitionSpecialize remaining observation ordinal
  where
    next following
        | goalDefinitionAdministrative following = advanceGoalDefinition observationScope environment active context target following
        | otherwise = pure (GoalDefinitionPending following)

goalDefinitionAdministrative :: GoalDefinitionCursor global -> Bool
goalDefinitionAdministrative = \case
    GoalDefinitionPrepareRoots RootObservationFinished{} -> True
    GoalDefinitionSpecialize _ _ _ DefinitionSpecialized{} -> True
    GoalDefinitionExpose _ _ _ ObservationExposed{} -> True
    GoalDefinitionBuild _ ViewProofFinished{} -> True
    _ -> False

rejectGoalDefinition
    :: Set FocusedObligationId
    -> GoalDefinitionCursor global
    -> ObviousFailure global
    -> State (ObviousSearchState global) (GoalDefinitionStep global)
rejectGoalDefinition active cursor failure
    | stopsGoalDefinitionSearch active failure =
        pure (GoalDefinitionFinished (AttemptFailed failure))
    | otherwise = pure (GoalDefinitionPending case cursor of
        GoalDefinitionPrepareRoots{} -> GoalDefinitionObservations (Just failure) []
        GoalDefinitionSpecialize remaining _ _ _ -> remaining
        GoalDefinitionExpose remaining _ _ _ -> remaining
        GoalDefinitionBuild{} -> GoalDefinitionObservations (Just failure) []
        GoalDefinitionObservations firstFailure rest ->
            GoalDefinitionObservations (firstFailure <|> Just failure) rest
        GoalDefinitionResolving firstFailure rest _observation _resolving _completed ->
            GoalDefinitionObservations (firstFailure <|> Just failure) rest
        GoalDefinitionViews firstFailure rest observation viewFailure views ->
            GoalDefinitionViews firstFailure rest observation (viewFailure <|> Just failure) views)

resumeGoalDefinition
    :: Set FocusedObligationId
    -> GoalDefinitionContinuation global
    -> Either (ObviousFailure global) (ObviousProof global)
    -> State (ObviousSearchState global) (GoalDefinitionStep global)
resumeGoalDefinition active
        (GoalDefinitionContinuation remaining reconstruction equationDependencies) = \case
    Left failure -> rejectGoalDefinition active remaining failure
    Right (ObviousProof childProof childDependencies) -> do
        combined <- combineCandidateDependencies equationDependencies childDependencies
        pure case combined of
            Left failure -> GoalDefinitionFinished (AttemptFailed failure)
            Right dependencies -> GoalDefinitionPending (GoalDefinitionBuild dependencies
                (startViewProof FoldGoalView reconstruction childProof))

data FactDefinitionSource global = FactDefinitionSource
    !(ObviousProof global)
    !(ObviousProof global)
    !(Maybe (ObviousFailure global))
    ![ObviousProof global]

data FactDefinitionCursor global
    = FactDefinitionSources !(Maybe (ObviousFailure global)) ![ObviousProof global]
    | FactDefinitionExpose !(ObviousProof global) !(Maybe (ObviousFailure global))
        ![ObviousProof global] !(SourceExposureStep global)
    | FactDefinitionPrepareRoots !(FactDefinitionSource global) !(RootObservationStep global)
    | FactDefinitionDescend !(ObviousProof global)
        !(Maybe (ObviousFailure global)) ![ObviousProof global]
    | FactDefinitionObservations !(FactDefinitionSource global)
        !(Maybe (ObviousFailure global)) ![RootObservation global]
    | FactDefinitionResolving !(FactDefinitionSource global) !(Maybe (ObviousFailure global))
        !(RootObservation global) ![RootObservation global]
        !(DefinitionViewCursor global) !(Seq (AvailableDefinitionView global))
    | FactDefinitionSpecialize !(FactDefinitionCursor global) !(ObviousProof global)
        !(RootObservation global) !Natural !(DefinitionSpecializationStep global)
    | FactDefinitionExpand !(FactDefinitionCursor global) !(FactExpansionStep global)
    | FactDefinitionViews !(FactDefinitionSource global) !(Maybe (ObviousFailure global))
        !(RootObservation global) ![RootObservation global]
        !(Maybe (ObviousFailure global)) ![AvailableDefinitionView global]

data FactDefinitionStep global
    = FactDefinitionPending !(FactDefinitionCursor global)
    | FactDefinitionUse !(ObviousProof global) !(FactDefinitionCursor global)
    | FactDefinitionFinished !(Attempt global)

advanceFactDefinition
    :: Ord global
    => DefinitionViewSelection
    -> SearchEnvironment global
    -> KernelProof.ProofContext global
    -> FactDefinitionCursor global
    -> State (ObviousSearchState global) (FactDefinitionStep global)
advanceFactDefinition selection environment context = \case
    FactDefinitionSources firstFailure [] ->
        finished (maybe AttemptNotApplicable AttemptFailed firstFailure)
    FactDefinitionSources firstFailure (source : rest) ->
        startSourceExposure context source >>= next . FactDefinitionExpose source firstFailure rest
    FactDefinitionExpose _ firstFailure rest (SourceExposureFinished (Left failure)) ->
        pure (rejectFactDefinition (FactDefinitionSources firstFailure rest) failure)
    FactDefinitionExpose source firstFailure rest (SourceExposureFinished (Right prepared)) ->
        startRootObservations (obviousProofStatement prepared) >>= next
            . FactDefinitionPrepareRoots (FactDefinitionSource source prepared firstFailure rest)
    FactDefinitionExpose source firstFailure rest step ->
        advanceSourceExposure environment context step >>= next . FactDefinitionExpose source firstFailure rest
    FactDefinitionPrepareRoots (FactDefinitionSource source _ firstFailure rest)
            (RootObservationFinished (Left failure)) ->
        pure (rejectFactDefinition (FactDefinitionDescend source firstFailure rest) failure)
    FactDefinitionPrepareRoots source (RootObservationFinished (Right observations)) ->
        next (FactDefinitionObservations source Nothing observations)
    FactDefinitionPrepareRoots source step -> advanceRootObservations environment step
        >>= next . FactDefinitionPrepareRoots source
    FactDefinitionDescend source firstFailure rest ->
        projectedChildren environment context source >>= \case
            Left failure -> finished (AttemptFailed failure)
            Right projected -> next (FactDefinitionSources firstFailure (projected <> rest))
    FactDefinitionObservations (FactDefinitionSource source _prepared firstFailure rest) observationFailure [] ->
        next (FactDefinitionDescend source (firstFailure <|> observationFailure) rest)
    FactDefinitionObservations source firstFailure (observation : rest) ->
        startDefinitionViews selection environment context observation >>= \case
            Left failure -> pure (rejectFactDefinition
                (FactDefinitionObservations source firstFailure rest) failure)
            Right resolving -> next (FactDefinitionResolving
                source firstFailure observation rest resolving Seq.empty)
    FactDefinitionResolving source firstFailure observation rest resolving completed ->
        advanceDefinitionViews environment context resolving >>= \case
            Left failure -> pure (rejectFactDefinition
                (FactDefinitionObservations source firstFailure rest) failure)
            Right DefinitionViewsFinished -> next (FactDefinitionViews
                source firstFailure observation rest Nothing (toList completed))
            Right (DefinitionViewResolved view remaining) -> next (FactDefinitionResolving
                source firstFailure observation rest remaining (maybe completed (completed Seq.|>) view))
    FactDefinitionViews source firstFailure _observation rest viewFailure [] ->
        next (FactDefinitionObservations source (firstFailure <|> viewFailure) rest)
    FactDefinitionViews source@(FactDefinitionSource _original prepared _sourceFailure _sources)
            firstFailure observation rest viewFailure (view : views) ->
        next (FactDefinitionSpecialize (FactDefinitionViews source firstFailure observation rest viewFailure views)
            prepared observation (availableDefinitionViewOrdinal view) (startDefinitionSpecialization observation view))
    FactDefinitionSpecialize remaining prepared observation ordinal (DefinitionSpecialized result) -> case result of
        Left failure -> pure (rejectFactDefinition remaining failure)
        Right Nothing -> next remaining
        Right (Just equation) -> startFactExpansion prepared ordinal observation equation
            >>= next . FactDefinitionExpand remaining
    FactDefinitionExpand remaining (FactExpansionFinished result) -> case result of
        Left failure -> pure (rejectFactDefinition remaining failure)
        Right proof -> pure (FactDefinitionUse proof remaining)
    FactDefinitionExpand remaining step -> advanceFactExpansion environment context step
        >>= next . FactDefinitionExpand remaining
    FactDefinitionSpecialize remaining prepared observation ordinal step ->
        advanceDefinitionSpecialization environment context observation step
            >>= next . FactDefinitionSpecialize remaining prepared observation ordinal
  where
    next following
        | factDefinitionAdministrative following = advanceFactDefinition selection environment context following
        | otherwise = pure (FactDefinitionPending following)
    finished = pure . FactDefinitionFinished

factDefinitionAdministrative :: FactDefinitionCursor global -> Bool
factDefinitionAdministrative = \case
    FactDefinitionExpose _ _ _ SourceExposureFinished{} -> True
    FactDefinitionPrepareRoots _ RootObservationFinished{} -> True
    FactDefinitionSpecialize _ _ _ _ DefinitionSpecialized{} -> True
    FactDefinitionExpand _ FactExpansionFinished{} -> True
    _ -> False

rejectFactDefinition :: FactDefinitionCursor global -> ObviousFailure global -> FactDefinitionStep global
rejectFactDefinition cursor failure
    | isFocusedInfrastructureFailure failure = FactDefinitionFinished (AttemptFailed failure)
    | otherwise = FactDefinitionPending case cursor of
        FactDefinitionSpecialize remaining _ _ _ _ -> remaining
        FactDefinitionExpand remaining _ -> remaining
        FactDefinitionExpose _ firstFailure rest _ -> FactDefinitionSources (firstFailure <|> Just failure) rest
        FactDefinitionPrepareRoots (FactDefinitionSource source _ firstFailure rest) _ ->
            FactDefinitionDescend source (firstFailure <|> Just failure) rest
        FactDefinitionSources firstFailure rest ->
            FactDefinitionSources (firstFailure <|> Just failure) rest
        FactDefinitionDescend source firstFailure rest ->
            FactDefinitionDescend source (firstFailure <|> Just failure) rest
        FactDefinitionObservations source firstFailure rest ->
            FactDefinitionObservations source (firstFailure <|> Just failure) rest
        FactDefinitionResolving source firstFailure _observation rest _resolving _completed ->
            FactDefinitionObservations source (firstFailure <|> Just failure) rest
        FactDefinitionViews source firstFailure observation rest viewFailure views ->
            FactDefinitionViews source firstFailure observation rest (viewFailure <|> Just failure) views

-- Reuse only successful expansions of the same checked source, view, and
-- root occurrence. The source key owns its context and authority lineage.
data FactExpansionStep global
    = FactExpansionObserve !(ObviousProof global) !Natural !DefinitionObservationSlot !CandidateDependencies
        !(ObservationExposureStep global)
    | FactExpansionBuild !(ObviousProof global) !Natural !DefinitionObservationSlot !CandidateDependencies !(ViewProofStep global)
    | FactExpansionFinished !(Either (ObviousFailure global) (ObviousProof global))

startFactExpansion
    :: ObviousProof global -> Natural -> RootObservation global -> ObviousProof global
    -> State (ObviousSearchState global) (FactExpansionStep global)
startFactExpansion source ordinal observation equation = do
    cached <- case obviousProofSourceKey source of
        Nothing -> pure (Right Nothing)
        Just key -> do
            work <- consumeSearchStep
            if not work then pure focusedWorkExhausted
                else Right <$> State.gets (Map.lookup (key, ordinal, slot) . searchFactExpansionCache)
    case cached of
        Left failure -> pure (FactExpansionFinished (Left failure))
        Right (Just proof) -> pure (FactExpansionFinished (Right proof))
        Right Nothing -> startObservationExposure (obviousProofStatement source) observation (obviousBuiltProof equation)
            >>= pure . FactExpansionObserve source ordinal slot (obviousProofDependencies equation)
  where
    slot = definitionObservationSlot observation

factExpansionIsDeferred :: FactExpansionStep global -> Bool
factExpansionIsDeferred (FactExpansionObserve _ _ _ _ step) = observationExposureIsDeferred step
factExpansionIsDeferred (FactExpansionBuild _ _ _ _ step) = viewProofIsDeferred step
factExpansionIsDeferred FactExpansionFinished{} = False

advanceFactExpansion
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> FactExpansionStep global
    -> State (ObviousSearchState global) (FactExpansionStep global)
advanceFactExpansion environment context = \case
    finished@FactExpansionFinished{} -> pure finished
    FactExpansionObserve source ordinal slot dependencies (ObservationExposed result) -> case result of
        Left failure -> done (Left failure)
        Right reconstruction -> pure (FactExpansionBuild source ordinal slot dependencies
            (startViewProof UnfoldFactView reconstruction (obviousBuiltProof source)))
    FactExpansionObserve source ordinal slot dependencies step -> advanceObservationExposure environment context step
        >>= pure . FactExpansionObserve source ordinal slot dependencies
    FactExpansionBuild source ordinal slot dependencies (ViewProofFinished result) -> case result of
        Left failure -> done (Left failure)
        Right built -> do
            combined <- combineCandidateDependencies (obviousProofDependencies source) dependencies
            case combined of
                Left failure -> done (Left failure)
                Right imports -> do
                    let proof = withFactDefinitionOccurrence ordinal (deriveCandidateProofWithDependencies built imports source)
                    case obviousProofSourceKey source of
                        Nothing -> done (Right proof)
                        Just key -> tagDerivedSource proof >>= \case
                            Left failure -> done (Left failure)
                            Right stable -> do
                                State.modify' (\state -> state {searchFactExpansionCache =
                                    Map.insert (key, ordinal, slot) stable (searchFactExpansionCache state)})
                                done (Right stable)
    FactExpansionBuild source ordinal slot dependencies step -> advanceViewProof environment context step
        >>= pure . FactExpansionBuild source ordinal slot dependencies
  where
    done = pure . FactExpansionFinished

data DefinitionViewCursor global = DefinitionViewCursor
    !Natural
    !(CanonicalTerm global)
    ![(DefinitionViewKind, [(Natural, ObviousImport global)], [(Natural, Natural, DefinitionViewKind)])]

data DefinitionViewProgress global
    = DefinitionViewsFinished
    | DefinitionViewResolved !(Maybe (AvailableDefinitionView global)) !(DefinitionViewCursor global)

startDefinitionViews
    :: Ord global
    => DefinitionViewSelection
    -> SearchEnvironment global
    -> KernelProof.ProofContext global
    -> RootObservation global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (DefinitionViewCursor global))
startDefinitionViews selection
        (SearchEnvironment _typing _imports initialHypothesisCount
            (DefinitionViewCatalogue _definitions importedBuckets localViews _citedPredicates))
        context observation = do
    currentCount <- if selection == ImportedDefinitionViewsOnly || null localViews
        then pure (Right initialHypothesisCount)
        else currentHypothesisCountCounted context
    pure (fmap (\count -> DefinitionViewCursor count requiredSubject
        [(kind, imported kind, local) | kind <- preferredKinds]) currentCount)
  where
    requiredSubject = observationSubject observation
    preferredKinds = case observation of
        MembershipObservation{} ->
            [DefinitionMembershipView, DefinitionPointwiseView, DefinitionExactView]
        _observation -> [DefinitionPointwiseView, DefinitionExactView]
    imported kind = case (selection, requiredSubject) of
        (LocalDefinitionViewsOnly, _subject) -> []
        (_, CGlobal object) -> toList
            (Map.findWithDefault Seq.empty (kind, object) importedBuckets)
        (_, _notGlobal) -> []
    local = if selection == ImportedDefinitionViewsOnly then [] else localViews

advanceDefinitionViews
    :: Eq global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> DefinitionViewCursor global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (DefinitionViewProgress global))
advanceDefinitionViews environment context (DefinitionViewCursor count subject pending) = case pending of
    [] -> pure (Right DefinitionViewsFinished)
    (_kind, [], []) : rest -> skipped rest
    (kind, imported, (_ordinal, _index, localKind) : locals) : rest
        | kind /= localKind -> skipped ((kind, imported, locals) : rest)
    (kind, imported, locals) : rest -> case (imported, locals) of
        ((ordinal, proof) : remainingImports, [])
            -> resolve kind (ImportedDefinitionViewCandidate ordinal proof)
                ((kind, remainingImports, []) : rest)
        ([], (ordinal, index, _localKind) : remainingLocals)
            -> resolve kind (LocalDefinitionViewCandidate ordinal index)
                ((kind, [], remainingLocals) : rest)
        ((importOrdinal, proof) : remainingImports, (localOrdinal, index, _localKind) : remainingLocals)
            | importOrdinal <= localOrdinal ->
                resolve kind (ImportedDefinitionViewCandidate importOrdinal proof)
                    ((kind, remainingImports, locals) : rest)
            | otherwise ->
                resolve kind (LocalDefinitionViewCandidate localOrdinal index)
                    ((kind, imported, remainingLocals) : rest)
  where
    skipped rest = pure (Right (DefinitionViewResolved Nothing (DefinitionViewCursor count subject rest)))
    resolve kind candidate rest = do
        hasWork <- consumeSearchStep
        if not hasWork
            then pure focusedWorkExhausted
            else do
                selected <- resolveDefinitionView environment context count subject kind candidate
                pure (fmap (\view -> DefinitionViewResolved view (DefinitionViewCursor count subject rest)) selected)

-- Ordinary imports have unique indices after input validation. Admitting a
-- canonical source or a selected view joins that association and may not replace
-- its checked statement. Ordinals retain successful checks across scope rebasing.
registerDefinitionImport
    :: Eq global
    => Natural
    -> ObviousImport global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) ())
registerDefinitionImport = registerDefinitionImportWith FocusedScopeWork

registerDefinitionImportWith
    :: Eq global => ScopeWork -> Natural -> ObviousImport global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) ())
registerDefinitionImportWith owner ordinal (ObviousImport index statement) = Except.runExceptT do
    scopeChargeTo owner
    registered <- State.gets (Set.member ordinal . searchRegisteredDefinitionImports)
    unless registered do
        prior <- State.gets (Map.lookup index . searchPermittedImports)
        for_ prior \previous -> do
            identical <- runScopeCore owner absurd (\work -> countedCanonicalIdentity
                work (frozenCoreTerm previous) (frozenCoreTerm statement))
            unless identical (Except.throwE
                (ObviousMalformedInput (ObviousConflictingImportStatement index)))
        State.modify' (\state -> state
            { searchPermittedImports = Map.insert index statement (searchPermittedImports state)
            , searchRegisteredDefinitionImports = Set.insert ordinal (searchRegisteredDefinitionImports state)
            })

resolveDefinitionView
    :: Eq global
    => SearchEnvironment global
    -> KernelProof.ProofContext global
    -> Natural
    -> CanonicalTerm global
    -> DefinitionViewKind
    -> DefinitionViewCandidate global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (Maybe (AvailableDefinitionView global)))
resolveDefinitionView environment context count requiredSubject wantedKind = \case
    ImportedDefinitionViewCandidate ordinal source@(ObviousImport index statement) -> Except.runExceptT do
        Except.ExceptT (registerDefinitionImport ordinal source)
        proof <- Except.ExceptT (runCountedKernel (KernelProof.countedImportedProof context index statement))
        pure (Just (AvailableDefinitionView ordinal requiredSubject wantedKind
            (ObviousProof proof (canonicalImportDependencies ordinal index))))
    LocalDefinitionViewCandidate ordinal sourceIndex -> Except.runExceptT do
        currentIndex <- Except.ExceptT
            (pure (currentLocalDefinitionHypothesisIx environment count sourceIndex))
        proof <- Except.ExceptT (runCountedKernel
            (KernelProof.countedIndexedHypothesisProof context currentIndex))
        found <- Except.ExceptT (definitionViewSubjectCounted wantedKind
            (scopedCoreTerm (KernelProof.builtProofStatement proof)))
        subject <- maybe
            (Except.throwE (ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
                "a proof-local canonical view has an invalid proposition")))
            pure found
        matches <- Except.ExceptT (canonicalIdentity subject requiredSubject)
        pure (AvailableDefinitionView ordinal subject wantedKind
            (ObviousProof proof (canonicalHypothesisDependencies sourceIndex)) <$ guard matches)

data RootObservationStep global
    = RootObservationMembership !(CanonicalTerm global) !PreparationEffort !(ScopedCheckedCore global)
    | RootObservationLeft !CoreType !PreparationEffort !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | RootObservationRight !CoreType !(ScopedCheckedCore global) !PreparationEffort !(ScopedCheckedCore global)
    | RootObservationFinished !(Either (ObviousFailure global) [RootObservation global])

startRootObservations
    :: ScopedCheckedCore global -> State (ObviousSearchState global) (RootObservationStep global)
startRootObservations checked = case splitScopedMembership checked of
    Just (element, set) -> pure (RootObservationMembership (scopedCoreTerm element) SmallPreparation set)
    Nothing -> case splitScopedEquality checked of
        Just (operandType, left, right) -> pure (RootObservationLeft operandType SmallPreparation left right)
        Nothing -> do
            application <- definedApplicationCounted (scopedCoreTerm checked)
            pure (RootObservationFinished (fmap
                (maybe [] (\(subject, arguments) -> [PredicateObservation subject arguments checked])) application))

rootObservationIsDeferred :: RootObservationStep global -> Bool
rootObservationIsDeferred = \case
    RootObservationMembership _ effort _ -> preparationIsDeferred effort
    RootObservationLeft _ effort _ _ -> preparationIsDeferred effort
    RootObservationRight _ _ effort _ -> preparationIsDeferred effort
    _ -> False

advanceRootObservations
    :: SearchEnvironment global -> RootObservationStep global
    -> State (ObviousSearchState global) (RootObservationStep global)
advanceRootObservations environment@(SearchEnvironment typing _ _ _) = \case
    finished@RootObservationFinished{} -> pure finished
    RootObservationMembership element effort set -> prepare effort set >>= \case
        NeedsMoreEffort offered -> pure (RootObservationMembership element (FullPreparation offered) set)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right prepared) -> do
            application <- definedApplicationCounted (scopedCoreTerm prepared)
            done (fmap (maybe [] (\(subject, arguments) ->
                [MembershipObservation element subject arguments prepared])) application)
    RootObservationLeft operandType effort left right -> prepare effort left >>= \case
        NeedsMoreEffort offered -> pure (RootObservationLeft operandType (FullPreparation offered) left right)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right prepared) ->
            advanceRootObservations environment (RootObservationRight operandType prepared SmallPreparation right)
    RootObservationRight operandType left effort right -> prepare effort right >>= \case
        NeedsMoreEffort offered -> pure (RootObservationRight operandType left (FullPreparation offered) right)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right prepared) -> do
            leftApplication <- definedApplicationCounted (scopedCoreTerm left)
            rightApplication <- definedApplicationCounted (scopedCoreTerm prepared)
            done do
                leftFound <- leftApplication
                rightFound <- rightApplication
                pure (toList ((\(subject, arguments) -> EqualityLeftObservation operandType subject left arguments
                        (scopedCoreTerm prepared)) <$> leftFound)
                    <> toList ((\(subject, arguments) -> EqualityRightObservation operandType subject prepared arguments
                        (scopedCoreTerm left)) <$> rightFound))
  where
    done = pure . RootObservationFinished
    failed = done . Left
    prepare SmallPreparation checked = headNeedsReduction False (scopedCoreTerm checked) >>= \case
        Left failure -> pure (PreparationFinished (Left failure))
        Right False -> pure (PreparationFinished (Right checked))
        Right True -> reduce SmallPreparation checked
    prepare effort checked = reduce effort checked
    reduce effort checked = runConversionPreparation effort (\limit ->
        Conversion.residualizeHeadChecked (Conversion.ConversionRecoveryTyping typing typing) limit checked)

definedApplicationCounted
    :: CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (Maybe (CanonicalTerm global, [CanonicalTerm global])))
definedApplicationCounted =
    go []
  where
    go arguments term = do
        hasWork <- consumeSearchStep
        if not hasWork
            then
                pure
                    (Left
                        (ObviousResourceExhausted
                            ObviousFocusedWorkLimit))
            else
                case term of
                    CApp function argument ->
                        go (argument : arguments) function
                    CGlobal{} ->
                        pure (Right (Just (term, arguments)))
                    CBound{} ->
                        pure (Right (Just (term, arguments)))
                    _ ->
                        pure (Right Nothing)

observationSubject
    :: RootObservation global
    -> CanonicalTerm global
observationSubject = \case
    PredicateObservation subject _arguments _term -> subject
    PredicateArgumentObservation subject _arguments _term _predicate -> subject
    EqualityLeftObservation _type subject _term _arguments _other -> subject
    EqualityRightObservation _type subject _term _arguments _other -> subject
    MembershipObservation _element subject _arguments _set -> subject

observationArguments
    :: RootObservation global
    -> [CanonicalTerm global]
observationArguments observation =
    case observation of
        PredicateObservation _subject arguments _term -> arguments
        PredicateArgumentObservation _subject arguments _term _predicate -> arguments
        EqualityLeftObservation _type _subject _term arguments _other ->
            arguments
        EqualityRightObservation _type _subject _term arguments _other ->
            arguments
        MembershipObservation _element _subject arguments _set -> arguments

observationDefinedTerm
    :: RootObservation global
    -> ScopedCheckedCore global
observationDefinedTerm = \case
    PredicateObservation _subject _arguments term -> term
    PredicateArgumentObservation _subject _arguments term _predicate -> term
    EqualityLeftObservation _type _subject term _arguments _other -> term
    EqualityRightObservation _type _subject term _arguments _other -> term
    MembershipObservation _element _subject _arguments set -> set

definitionViewSubjectCounted
    :: DefinitionViewKind
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (Maybe (CanonicalTerm global)))
definitionViewSubjectCounted kind proposition = do
    stripped <- stripForalls 0 proposition
    case stripped of
        Left failure -> pure (Left failure)
        Right (binderCount, body)
            | CEq _operandType left _right <- body -> do
                rawSubject <-
                    case kind of
                        DefinitionMembershipView ->
                            case left of
                                CApp
                                    (CApp (CIntrinsic Member) _element)
                                    candidate ->
                                        definedApplicationCounted candidate
                                _ -> pure (Right Nothing)
                        DefinitionPointwiseView ->
                            definedApplicationCounted left
                        DefinitionExactView ->
                            definedApplicationCounted left
                case rawSubject of
                    Left failure -> pure (Left failure)
                    Right Nothing -> pure (Right Nothing)
                    Right (Just (subject, _arguments)) ->
                        removeInnerBindersCounted binderCount subject
        Right _notEquality ->
            pure (Right Nothing)
  where
    stripForalls binderCount term = do
        hasWork <- consumeSearchStep
        if not hasWork
            then
                pure
                    (Left
                        (ObviousResourceExhausted
                            ObviousFocusedWorkLimit))
            else
                case term of
                    CForall _binderType body ->
                        stripForalls (binderCount + 1) body
                    body ->
                        pure (Right (binderCount, body))

data DefinitionSpecializationStep global
    = DefinitionApply !DefinitionViewKind !CandidateDependencies !(KernelProof.BuiltProof global) ![CanonicalTerm global]
    | DefinitionApplyForall !PreparationEffort !DefinitionViewKind !CandidateDependencies
        !(KernelProof.BuiltProof global) !(ScopedCheckedCore global) ![CanonicalTerm global]
    | DefinitionApplyCongruence !PreparationEffort !CandidateDependencies
        !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global) ![CanonicalTerm global]
    | DefinitionExpose !DefinitionViewKind !(SourceExposureStep global)
    | DefinitionCompare !PreparationEffort !(ObviousProof global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | DefinitionSpecialized !(Either (ObviousFailure global) (Maybe (ObviousProof global)))

startDefinitionSpecialization :: RootObservation global -> AvailableDefinitionView global -> DefinitionSpecializationStep global
startDefinitionSpecialization observation (AvailableDefinitionView _ _ kind (ObviousProof source imports)) =
    DefinitionApply kind imports source arguments
  where
    arguments = case (kind, observation) of
        (DefinitionMembershipView, MembershipObservation element _ entered _) -> entered <> [element]
        _ -> observationArguments observation

definitionSpecializationIsDeferred :: DefinitionSpecializationStep global -> Bool
definitionSpecializationIsDeferred = \case
    DefinitionApplyForall effort _ _ _ _ _ -> preparationIsDeferred effort
    DefinitionApplyCongruence effort _ _ _ _ -> preparationIsDeferred effort
    DefinitionExpose _ step -> sourceExposureIsDeferred step
    DefinitionCompare effort _ _ _ -> preparationIsDeferred effort
    _ -> False

advanceDefinitionSpecialization
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> RootObservation global
    -> DefinitionSpecializationStep global -> State (ObviousSearchState global) (DefinitionSpecializationStep global)
advanceDefinitionSpecialization environment@(SearchEnvironment typing _ _ _) context observation = \case
    finished@DefinitionSpecialized{} -> pure finished
    DefinitionApply kind dependencies proof [] ->
        startSourceExposure context (ObviousProof proof dependencies) >>= pure . DefinitionExpose kind
    DefinitionApply kind dependencies proof (argument : rest) -> do
        checked <- runCountedKernel (KernelProof.countedScopedTerm context argument)
        case checked of
            Left failure -> failed failure
            Right term -> case kind of
                DefinitionExactView -> do
                    reflexive <- runCountedKernel (KernelProof.countedEqualityReflexivityProof context term)
                    case reflexive of
                        Left failure -> failed failure
                        Right equality -> pure (DefinitionApplyCongruence SmallPreparation dependencies proof equality rest)
                _ -> pure (DefinitionApplyForall SmallPreparation kind dependencies proof term rest)
    DefinitionApplyForall effort kind dependencies proof argument rest ->
        runKernelPreparation effort (KernelProof.countedForallEliminationProof
            context proof argument) >>= \case
                NeedsMoreEffort offered -> pure (DefinitionApplyForall (FullPreparation offered) kind dependencies proof argument rest)
                PreparationFinished (Left failure) -> failed failure
                PreparationFinished (Right prepared) -> pure (DefinitionApply kind dependencies prepared rest)
    DefinitionApplyCongruence effort dependencies proof reflexive rest ->
        runKernelPreparation effort (KernelProof.countedEqualityCongruenceApplicationProof
            context proof reflexive) >>= \case
                NeedsMoreEffort offered -> pure (DefinitionApplyCongruence (FullPreparation offered) dependencies proof reflexive rest)
                PreparationFinished (Left failure) -> failed failure
                PreparationFinished (Right prepared) -> pure (DefinitionApply DefinitionExactView dependencies prepared rest)
    DefinitionExpose kind (SourceExposureFinished result) -> case result of
        Left failure -> failed failure
        Right prepared -> case splitScopedEquality (obviousProofStatement prepared) of
            Nothing -> done (Right Nothing)
            Just (_, left, _) -> do
                expected <- case (observation, kind) of
                    (MembershipObservation element _ _ set, DefinitionMembershipView) ->
                        checkedProposition context (CApp (CApp (CIntrinsic Member) element) (scopedCoreTerm set))
                    _ -> pure (Right (observationDefinedTerm observation))
                case expected of
                    Left failure -> failed failure
                    Right term -> pure (DefinitionCompare SmallPreparation prepared left term)
    DefinitionExpose kind step -> advanceSourceExposure environment context step >>= pure . DefinitionExpose kind
    DefinitionCompare effort prepared left expected ->
        runConversionPreparation effort (\limit -> Conversion.convertibleChecked typing limit left expected) >>= \case
            NeedsMoreEffort offered -> pure (DefinitionCompare (FullPreparation offered) prepared left expected)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right result) -> done (Right (prepared <$ guard (result == Conversion.Convertible)))
  where
    done = pure . DefinitionSpecialized
    failed = done . Left

data GoalViewTransport global
    = GoalPropositionTransport
    | GoalTermTransport !(ScopedCheckedCore global)

data GoalViewReconstruction global = GoalViewReconstruction
    !(ScopedCheckedCore global)
    !(KernelProof.BuiltProof global)
    !(ScopedCheckedCore global)
    !(GoalViewTransport global)

data ObservationExposureStep global
    = ObservationCheckOriginal !PreparationEffort !(ScopedCheckedCore global) !(RootObservation global)
        !(KernelProof.BuiltProof global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | ObservationCheckDefined !PreparationEffort !(ScopedCheckedCore global) !(RootObservation global)
        !(KernelProof.BuiltProof global) !(ScopedCheckedCore global) !(ScopedCheckedCore global)
    | ObservationExposed !(Either (ObviousFailure global) (GoalViewReconstruction global))

startObservationExposure
    :: ScopedCheckedCore global -> RootObservation global -> KernelProof.BuiltProof global
    -> State (ObviousSearchState global) (ObservationExposureStep global)
startObservationExposure original observation equation = case definitionEquality equation of
    Left failure -> pure (ObservationExposed (Left failure))
    Right (operandType, left, right) -> coreTypeIdentity operandType TyProp >>= \case
        Left failure -> pure (ObservationExposed (Left failure))
        Right proposition -> pure ((if proposition then ObservationCheckOriginal else ObservationCheckDefined)
            SmallPreparation original observation equation left right)

observationExposureIsDeferred :: ObservationExposureStep global -> Bool
observationExposureIsDeferred = \case
    ObservationCheckOriginal effort _ _ _ _ _ -> preparationIsDeferred effort
    ObservationCheckDefined effort _ _ _ _ _ -> preparationIsDeferred effort
    _ -> False

advanceObservationExposure
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> ObservationExposureStep global
    -> State (ObviousSearchState global) (ObservationExposureStep global)
advanceObservationExposure (SearchEnvironment typing _ _ _) context = \case
    finished@ObservationExposed{} -> pure finished
    ObservationCheckOriginal effort original observation equation left right -> compareAt effort left original >>= \case
        NeedsMoreEffort offered -> pure (ObservationCheckOriginal (FullPreparation offered) original observation equation left right)
        PreparationFinished (Left failure) -> failed failure
        PreparationFinished (Right Conversion.Convertible) -> done (Right
            (GoalViewReconstruction original equation right GoalPropositionTransport))
        PreparationFinished (Right Conversion.NotConvertible) -> pure
            (ObservationCheckDefined SmallPreparation original observation equation left right)
    ObservationCheckDefined effort original observation equation left right ->
        compareAt effort left (observationDefinedTerm observation) >>= \case
            NeedsMoreEffort offered -> pure (ObservationCheckDefined (FullPreparation offered) original observation equation left right)
            PreparationFinished (Left failure) -> failed failure
            PreparationFinished (Right Conversion.NotConvertible) -> failed (ObviousIntegrityFailure
                (KernelProof.ProofStructuralCompositionMismatch "canonical definition view has the wrong left side"))
            PreparationFinished (Right Conversion.Convertible) -> do
                result <- Except.runExceptT do
                    predicate <- Except.ExceptT (observationPredicate context observation)
                    term <- Except.ExceptT (pure (observationWithDefinedTerm observation (scopedCoreTerm right)))
                    unfolded <- Except.ExceptT (checkedProposition context term)
                    pure (GoalViewReconstruction original equation unfolded (GoalTermTransport predicate))
                done result
  where
    done = pure . ObservationExposed
    failed = done . Left
    compareAt effort left right = runConversionPreparation effort (\limit -> Conversion.convertibleChecked typing limit left right)

-- The same checked transport recipe folds a goal view or unfolds a source.
-- Each stage owns its proof prefix; only the single blocked builder is retried.
data ViewDirection = FoldGoalView | UnfoldFactView

data ViewProofStep global
    = ViewProofBody !ViewDirection !(GoalViewReconstruction global) !(HeadProofStep global)
    | ViewProofReverse !PreparationEffort !(GoalViewReconstruction global) !(KernelProof.BuiltProof global)
    | ViewProofTransport !PreparationEffort !ViewDirection !(GoalViewReconstruction global)
        !(KernelProof.BuiltProof global) !(KernelProof.BuiltProof global)
    | ViewProofResult !(HeadProofStep global)
    | ViewProofFinished !(Either (ObviousFailure global) (KernelProof.BuiltProof global))

startViewProof :: ViewDirection -> GoalViewReconstruction global -> KernelProof.BuiltProof global -> ViewProofStep global
startViewProof direction reconstruction@(GoalViewReconstruction _ equation unfolded transport) source = case direction of
    FoldGoalView -> ViewProofBody direction reconstruction (HeadProofConvert SmallPreparation source unfolded)
    UnfoldFactView -> case transport of
        GoalTermTransport{} -> ViewProofTransport SmallPreparation direction reconstruction equation source
        GoalPropositionTransport -> case definitionEquality equation of
            Left failure -> ViewProofFinished (Left failure)
            Right (_, left, _) -> ViewProofBody direction reconstruction (HeadProofConvert SmallPreparation source left)

viewProofIsDeferred :: ViewProofStep global -> Bool
viewProofIsDeferred = \case
    ViewProofBody _ _ step -> headProofIsDeferred step
    ViewProofReverse effort _ _ -> preparationIsDeferred effort
    ViewProofTransport effort _ _ _ _ -> preparationIsDeferred effort
    ViewProofResult step -> headProofIsDeferred step
    _ -> False

advanceViewProof
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> ViewProofStep global
    -> State (ObviousSearchState global) (ViewProofStep global)
advanceViewProof environment context = \case
    finished@ViewProofFinished{} -> pure finished
    ViewProofBody direction reconstruction@(GoalViewReconstruction _ equation _ _) (HeadProofFinished result) -> case result of
        Left failure -> done (Left failure)
        Right body -> pure case direction of
            FoldGoalView -> ViewProofReverse SmallPreparation reconstruction body
            UnfoldFactView -> ViewProofTransport SmallPreparation direction reconstruction equation body
    ViewProofBody direction reconstruction step -> advanceHeadProof environment context step >>= \following -> case following of
            HeadProofFinished{} -> advanceViewProof environment context (ViewProofBody direction reconstruction following)
            _ -> pure (ViewProofBody direction reconstruction following)
    ViewProofReverse effort reconstruction@(GoalViewReconstruction _ equation _ _) body ->
        runKernelPreparation effort (KernelProof.countedEqualityReverseProof context equation) >>= \case
            NeedsMoreEffort offered -> pure (ViewProofReverse (FullPreparation offered) reconstruction body)
            PreparationFinished (Left failure) -> done (Left failure)
            PreparationFinished (Right reversed) -> pure (ViewProofTransport SmallPreparation FoldGoalView reconstruction reversed body)
    ViewProofTransport effort direction reconstruction@(GoalViewReconstruction original _ unfolded transport) equation body -> do
        result <- runKernelPreparation effort (case transport of
            GoalPropositionTransport -> KernelProof.countedEqualityModusPonensProof context equation body
            GoalTermTransport predicate -> KernelProof.countedEqualityTransportProof context equation predicate body)
        case result of
            NeedsMoreEffort offered -> pure (ViewProofTransport (FullPreparation offered) direction reconstruction equation body)
            PreparationFinished (Left failure) -> done (Left failure)
            PreparationFinished (Right proof) -> case (direction, transport) of
                (UnfoldFactView, GoalPropositionTransport) -> done (Right proof)
                _ -> pure (ViewProofResult (HeadProofConvert SmallPreparation proof (case direction of
                    FoldGoalView -> original
                    UnfoldFactView -> unfolded)))
    ViewProofResult (HeadProofFinished result) -> done result
    ViewProofResult step -> advanceHeadProof environment context step >>= \following -> case following of
        HeadProofFinished result -> done result
        _ -> pure (ViewProofResult following)
  where
    done = pure . ViewProofFinished

definitionEquality
    :: KernelProof.BuiltProof global
    -> Either (ObviousFailure global)
        (CoreType, ScopedCheckedCore global, ScopedCheckedCore global)
definitionEquality proof =
    maybe
        (Left (ObviousIntegrityFailure
            (KernelProof.ProofStructuralCompositionMismatch
                "canonical definition view is not an equality")))
        Right (splitScopedEquality (KernelProof.builtProofStatement proof))

observationPredicate
    :: KernelProof.ProofContext global
    -> RootObservation global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (ScopedCheckedCore global))
observationPredicate context observation = do
    predicateTerm <- case observation of
        PredicateArgumentObservation _subject _arguments _term predicate -> pure (Right predicate)
        EqualityLeftObservation operandType _subject _term _arguments other ->
            fmap
                (fmap
                    (\shifted ->
                        CLam operandType
                            (CEq operandType (CBound 0) shifted)))
                (shiftCanonicalCounted 1 0 other)
        EqualityRightObservation operandType _subject _term _arguments other ->
            fmap
                (fmap
                    (\shifted ->
                        CLam operandType
                            (CEq operandType shifted (CBound 0))))
                (shiftCanonicalCounted 1 0 other)
        MembershipObservation element _subject _arguments _set ->
            fmap
                (fmap
                    (\shifted ->
                        CLam TySet
                            (CApp
                                (CApp (CIntrinsic Member) shifted)
                                (CBound 0))))
                (shiftCanonicalCounted 1 0 element)
        PredicateObservation{} ->
            impossible
                "a proposition-root definition requested term transport"
    case predicateTerm of
        Left failure -> pure (Left failure)
        Right term ->
            runCountedKernel
                (KernelProof.countedScopedTerm
                        context term)

observationWithDefinedTerm
    :: RootObservation global
    -> CanonicalTerm global
    -> Either (ObviousFailure global) (CanonicalTerm global)
observationWithDefinedTerm observation replacement =
    pure case observation of
        PredicateArgumentObservation _subject _arguments _term predicate -> CApp predicate replacement
        EqualityLeftObservation operandType _subject _term _arguments other ->
            CEq operandType replacement other
        EqualityRightObservation operandType _subject _term _arguments other ->
            CEq operandType other replacement
        MembershipObservation element _subject _arguments _set ->
            CApp (CApp (CIntrinsic Member) element) replacement
        PredicateObservation{} ->
            impossible
                "a proposition-root definition requested term replacement"

data TheoremSourceStep global
    = TheoremSourceExpose !Bool !(Maybe (CompiledTheoremSpine global)) !(SourceExposureStep global)
    | TheoremSourceSpine !Bool !(ObviousProof global) !(SpinePreparationStep global)
    | TheoremSourceFinished !(Either (ObviousFailure global) (PreparedTheoremSource global))

startTheoremSource
    :: KernelProof.ProofContext global -> TheoremWorkItem global
    -> State (ObviousSearchState global) (TheoremSourceStep global)
startTheoremSource context = \case
    SelectedTheoremWorkItem source prefix result ->
        pure (TheoremSourceSpine False source (SpinePreparationInspect prefix result))
    RootTheoremWorkItem source -> start True source
    ProjectedTheoremWorkItem source -> start False source
  where
    start cache source = do
        spine <- case (cache, obviousProofSourceKey source) of
            (True, Just key) -> State.gets (Map.lookup key . searchFocusedTheoremCache)
            _ -> pure Nothing
        TheoremSourceExpose cache spine <$> startSourceExposure context source

advanceTheoremSource
    :: Eq global
    => SearchEnvironment global -> KernelProof.ProofContext global -> TheoremSourceStep global
    -> State (ObviousSearchState global) (TheoremSourceStep global)
advanceTheoremSource environment context = \case
    finished@TheoremSourceFinished{} -> pure finished
    TheoremSourceExpose cache cached step -> case step of
        SourceExposureFinished (Left failure) -> done (Left failure)
        SourceExposureFinished (Right source) -> case cached of
            Just spine -> done (Right (PreparedTheoremSource source spine))
            Nothing -> advanceTheoremSource environment context (TheoremSourceSpine cache source (startSpinePreparation (obviousProofStatement source)))
        _ -> advanceSourceExposure environment context step >>= \next ->
            advanceIfFinished (TheoremSourceExpose cache cached next)
    TheoremSourceSpine cache source step -> case step of
        SpinePreparationFinished (Left failure) -> done (Left failure)
        SpinePreparationFinished (Right spine) -> case (cache, obviousProofSourceKey source) of
            (True, Just key) -> do
                work <- consumeSearchStep
                if not work then done focusedWorkExhausted else do
                    State.modify' (\state -> state {searchFocusedTheoremCache =
                        Map.insert key spine (searchFocusedTheoremCache state)})
                    done (Right (PreparedTheoremSource source spine))
            _ -> done (Right (PreparedTheoremSource source spine))
        _ -> advanceSpinePreparation environment step >>= \next ->
            advanceIfFinished (TheoremSourceSpine cache source next)
  where
    done = pure . TheoremSourceFinished
    advanceIfFinished next = case next of
        TheoremSourceExpose _ _ SourceExposureFinished{} -> advanceTheoremSource environment context next
        TheoremSourceSpine _ _ SpinePreparationFinished{} -> advanceTheoremSource environment context next
        _ -> pure next

theoremSourceIsDeferred :: TheoremSourceStep global -> Bool
theoremSourceIsDeferred (TheoremSourceExpose _ _ step) = sourceExposureIsDeferred step
theoremSourceIsDeferred (TheoremSourceSpine _ _ (SpinePreparationReduce effort _ _)) = preparationIsDeferred effort
theoremSourceIsDeferred _ = False

data SpinePreparationStep global
    = SpinePreparationInspect ![TheoremSpineStep global] !(Template.CompiledTemplate global)
    | SpinePreparationReduce !PreparationEffort ![TheoremSpineStep global] !(Template.CompiledTemplate global)
    | SpinePreparationFinished !(Either (ObviousFailure global) (CompiledTheoremSpine global))

startSpinePreparation :: ScopedCheckedCore global -> SpinePreparationStep global
startSpinePreparation checked = case Template.retainCheckedPropositionTemplate checked of
    Left failure -> SpinePreparationFinished (Left (obviousTemplateError failure))
    Right initial -> SpinePreparationInspect [] initial

advanceSpinePreparation
    :: Eq global
    => SearchEnvironment global -> SpinePreparationStep global
    -> State (ObviousSearchState global) (SpinePreparationStep global)
advanceSpinePreparation environment = \case
    SpinePreparationInspect steps current -> go steps current
    SpinePreparationReduce effort steps current -> reduce effort steps current
    finished@SpinePreparationFinished{} -> pure finished
  where
    -- The source proof already owns its exposed head. Only a selected tail
    -- requests a fresh observation, under its existing removable prefix.
    go reverseSteps current = do
        hasWork <- consumeSearchStep
        if not hasWork
            then done focusedWorkExhausted
            else case Template.openCompiledForall current of
                Just (binderType, body) ->
                    let slot = Template.MatcherSlot
                            (Template.binderEnvironmentCount
                                (Template.compiledTemplateBinderEnvironment current))
                    in prepareTail (Elimination.Instantiate binderType slot : reverseSteps) body
                Nothing -> case Template.openCompiledImplication current of
                    Just (premise, conclusion) ->
                        prepareTail (Elimination.Apply premise : reverseSteps) conclusion
                    Nothing -> finish reverseSteps current

    prepareTail reverseSteps tailTemplate = do
        reducible <- Except.runExceptT
            (needsReduction False (scopedCoreTerm (Template.compiledTemplateTerm tailTemplate)))
        case reducible of
            Left failure -> done (Left failure)
            Right False -> go reverseSteps tailTemplate
            Right True -> reduce SmallPreparation reverseSteps tailTemplate

    reduce effort reverseSteps tailTemplate = do
        let SearchEnvironment globalType _ _ _ = environment
        prepared <- runConversionPreparation effort \limit ->
            Conversion.prepareImplicationSpineChecked
                (Conversion.ConversionRecoveryTyping globalType globalType)
                limit (Template.compiledTemplateTerm tailTemplate)
        case prepared of
            NeedsMoreEffort offered -> pure (SpinePreparationReduce (FullPreparation offered) reverseSteps tailTemplate)
            PreparationFinished (Left failure) -> done (Left failure)
            PreparationFinished (Right spine) -> appendPrepared reverseSteps
                (Template.compiledTemplateBinderEnvironment tailTemplate)
                (Conversion.preparedSpineSteps spine)
                (Conversion.preparedSpineTerminal spine)

    needsReduction applied term = do
        available <- lift consumeSearchStep
        unless available
            (Except.throwE (ObviousResourceExhausted ObviousFocusedWorkLimit))
        case term of
            CApp function _argument -> needsReduction True function
            CLam{} -> pure applied
            _ -> pure False

    appendPrepared reverseSteps binders steps terminal = do
        available <- consumeSearchStep
        if not available then done focusedWorkExhausted else case steps of
            Conversion.PreparedUniversal binderType : rest ->
                appendPrepared
                    (Elimination.Instantiate binderType
                        (Template.MatcherSlot (Template.binderEnvironmentCount binders))
                        : reverseSteps)
                    (Template.extendBinderEnvironment binderType binders) rest terminal
            Conversion.PreparedPremise premise : rest -> do
                retained <- runCountedTemplate \remaining ->
                    Template.retainCheckedPropositionTemplateUnder remaining binders premise
                case retained of
                    Left failure -> done (Left failure)
                    Right template -> appendPrepared
                        (Elimination.Apply template : reverseSteps) binders rest terminal
            [] -> do
                retained <- runCountedTemplate \remaining ->
                    Template.retainCheckedPropositionTemplateUnder remaining binders terminal
                case retained of
                    Left failure -> done (Left failure)
                    Right template -> finish reverseSteps template

    finish reverseSteps terminal = do
        result <- Except.runExceptT do
            ordered <- Except.ExceptT (reverseTheoremStepsCounted [] reverseSteps)
            schema <- Except.ExceptT (membershipExtensionalitySchema ordered reverseSteps terminal)
            pure (CompiledTheoremSpine ordered terminal schema)
        done result

    done = pure . SpinePreparationFinished

reverseTheoremStepsCounted
    :: [TheoremSpineStep global] -> [TheoremSpineStep global]
    -> State (ObviousSearchState global) (Either (ObviousFailure global) [TheoremSpineStep global])
reverseTheoremStepsCounted ordered [] = pure (Right ordered)
reverseTheoremStepsCounted ordered (step : rest) = do
    hasWork <- consumeSearchStep
    if hasWork then reverseTheoremStepsCounted (step : ordered) rest
        else pure focusedWorkExhausted

-- Inspect only the already-compiled prefix and final pair. Guards between
-- them remain ordinary premises. The schema grants scope, never evidence.
-- Disabled requests perform no recognition work, including comparisons.
membershipExtensionalitySchema
    :: Eq global
    => [TheoremSpineStep global] -> [TheoremSpineStep global]
    -> Template.CompiledTemplate global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) Bool)
membershipExtensionalitySchema ordered reversed terminal = do
    policy <- State.gets (policyExtensionality . searchPolicy)
    if policy == ExtensionalityDisabled then pure (Right False) else Except.runExceptT do
        scopeCharge
        let binders = Template.compiledTemplateBinderEnvironment terminal
            twoSets = Template.binderEnvironmentCount binders == 2
                && Template.binderEnvironmentSlotType (Template.MatcherSlot 0) binders == Just TySet
                && Template.binderEnvironmentSlotType (Template.MatcherSlot 1) binders == Just TySet
            same template term = Except.ExceptT
                (canonicalIdentity (scopedCoreTerm (Template.compiledTemplateTerm template)) term)
            member x a = CApp (CApp (CIntrinsic Member) (CBound x)) (CBound a)
            pointwise a b = CForall TySet (CImp (member 0 a) (member 0 b))
        case (ordered, reversed) of
            (Elimination.Instantiate TySet (Template.MatcherSlot 0) : Elimination.Instantiate TySet (Template.MatcherSlot 1) : _,
             Elimination.Apply backward : Elimination.Apply forward : _)
                | twoSets -> do
                    equality <- same terminal (CEq TySet (CBound 1) (CBound 0))
                    if not equality then pure False else do
                        firstDirection <- same forward (pointwise 2 1)
                        if not firstDirection then pure False else same backward (pointwise 1 2)
            _ -> pure False

-- The matcher retains checked rows, successful assignments and its pending
-- sibling comparisons. A head/slot probe suspends immediately before only that
-- converter's larger retry; no source, subtree analysis or prefix is replayed.
-- Assignments are bare slots, optionally exposed eta spines, not higher-order
-- unification. Beta heads are recovered at visits; the eta scan itself does not
-- normalize beneath its lambda chain. A later visit may expose another spine.
data TheoremMatchWork global
    = MatchVisit !Natural !(Maybe EtaSpine) !(CheckedOccurrence global) !(CheckedOccurrence global)
    | MatchPatternHead !PreparationEffort !Natural !(Maybe EtaSpine) !(CheckedOccurrence global) !(CheckedOccurrence global)
    | MatchGoalHead !PreparationEffort !Natural !(Maybe EtaSpine) !(CheckedOccurrence global) !(CheckedOccurrence global)
    | MatchHeads !Natural !(Maybe EtaSpine) !(CheckedOccurrence global) !(CheckedOccurrence global)
    | MatchEtaLambdas !Natural !(CheckedOccurrence global) !(CheckedOccurrence global) !Natural !(CheckedOccurrence global)
    | MatchEtaArguments !Natural !(CheckedOccurrence global) !(CheckedOccurrence global) !Natural !Natural !(CheckedOccurrence global)
    | MatchSlotCompare !PreparationEffort !(ScopedCheckedCore global) !(ScopedCheckedCore global)

-- One exposed lambda chain has at most one suffix headed by a bare theorem
-- slot. Keep its bottom depth and any qualifying suffix while descending the
-- unqualified prefix, including through mixed-lambda head recovery.
data EtaSpine = EtaSpine !Natural !(Maybe (Natural, Template.MatcherSlot))

data TheoremMatchStep global
    = TheoremMatchPending !Template.BinderEnvironment !Natural
        !(Template.TemplateSubstitution global) ![TheoremMatchWork global]
    | TheoremMatchFinished !(Either (ObviousFailure global) (TemplateMatchResult global))

theoremMatchIsDeferred :: TheoremMatchStep global -> Bool
theoremMatchIsDeferred (TheoremMatchPending _ _ _ (work : _)) = case work of
    MatchPatternHead effort _ _ _ _ -> preparationIsDeferred effort
    MatchGoalHead effort _ _ _ _ -> preparationIsDeferred effort
    MatchSlotCompare effort _ _ -> preparationIsDeferred effort
    _ -> False
theoremMatchIsDeferred _ = False

startTheoremMatch
    :: SearchEnvironment global -> KernelProof.ProofContext global
    -> Template.CompiledTemplate global -> ScopedCheckedCore global -> Template.TemplateSubstitution global
    -> State (ObviousSearchState global) (TheoremMatchStep global)
startTheoremMatch environment context template target substitutions = do
    result <- Except.runExceptT do
        ambientMatches <- sameContext (Template.binderEnvironmentAmbientContext binders)
            (KernelProof.proofContextTypes context)
        goalMatches <- sameContext (scopedCoreContext target) (KernelProof.proofContextTypes context)
        unless (ambientMatches && goalMatches)
            (Except.throwE (ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch
                "theorem matcher has inconsistent ambient contexts")))
        patternRoot <- Except.ExceptT (analyseTheoremOccurrence environment 0 (Template.compiledTemplateTerm template))
        goalRoot <- Except.ExceptT (analyseTheoremOccurrence environment 0 target)
        pure (TheoremMatchPending binders 0 substitutions [MatchVisit 0 Nothing patternRoot goalRoot])
    pure (either (TheoremMatchFinished . Left) id result)
  where
    binders = Template.compiledTemplateBinderEnvironment template
    charge = do
        available <- lift consumeSearchStep
        unless available (Except.throwE (ObviousResourceExhausted ObviousFocusedWorkLimit))
    sameContext [] [] = pure True
    sameContext (left : lefts) (right : rights) = do
        charge
        same <- Except.ExceptT (coreTypeIdentity left right)
        if same then sameContext lefts rights else pure False
    sameContext _left _right = pure False


analyseTheoremOccurrence
    :: SearchEnvironment global -> Natural -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (CheckedOccurrence global))
analyseTheoremOccurrence (SearchEnvironment globalType _ _ _) depth checked = Except.runExceptT do
    work <- lift getFocusedWorkBudget
    let (result, remaining) =
            countedAnalyseScopedOccurrencesUnderBinders globalType work depth checked
    lift (putFocusedWorkBudget remaining)
    case result of
        Left (CountedCoreOperationFailed (CheckedOccurrenceAnalysisCheckFailed failure)) ->
            Except.throwE (ObviousIntegrityFailure (KernelProof.ProofTermIllTyped failure))
        Left failure -> Except.throwE
            (obviousCountedFailure
                (\cause -> ObviousIntegrityFailure
                    (KernelProof.ProofStructuralCompositionMismatch
                        ("theorem occurrence analysis failed: " <> fromString (show cause))))
                failure)
        Right row -> pure row

-- Private bridge observation: exercise the real matcher without making the
-- driver state or suspended work constructors available to fixtures.
scopeMatchTemplate
    :: Ord global
    => ScopeId request -> Template.CompiledTemplate global -> ScopedCheckedCore global
    -> Scoped request global (TemplateMatchResult global, Natural)
scopeMatchTemplate scope template target = do
    context <- scopeContext scope
    let environment = SearchEnvironment (KernelProof.proofContextGlobalTyping context) [] 0
            (definitionViewCatalogue [] [])
        finish turns = \case
            TheoremMatchFinished result -> (\matched -> (matched, turns)) <$> Except.ExceptT (pure result)
            pending -> lift (advanceTheoremMatch environment pending) >>= finish (turns + 1)
    lift (startTheoremMatch environment context template target Template.emptyTemplateSubstitution) >>= finish 0

-- Private bridge drains of the actual reconstruction cursors. They return
-- ordinary BuiltProof values, not scope-authorized evidence. Replay remains
-- independent; the observations count executed wrappers and final attempts.
scopeReconstructFunctionEquality
    :: Ord global
    => ScopeId request -> ScopeId request -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> [CoreType] -> KernelProof.BuiltProof global
    -> Scoped request global (KernelProof.BuiltProof global, Natural, Natural)
scopeReconstructFunctionEquality outerScope childScope outer child binders proof = do
    outerContext <- scopeContext outerScope
    childContext <- scopeContext childScope
    let environment = SearchEnvironment (KernelProof.proofContextGlobalTyping outerContext) [] 0
            (definitionViewCatalogue [] [])
        finish wrappers attempts = \case
            FunctionEqualityFinished result -> (\built -> (built, wrappers, attempts))
                <$> Except.ExceptT (pure result)
            pending -> do
                let added = case pending of FunctionEqualityAbstract _ (_ : _) _ -> 1; _ -> 0
                    attempted = case pending of FunctionEqualityResult HeadProofConvert{} -> 1; _ -> 0
                lift (advanceFunctionEqualityProof environment outerContext childContext pending)
                    >>= finish (wrappers + added) (attempts + attempted)
    finish 0 0 (startFunctionEqualityProof outer child binders proof)

scopeReconstructBooleanEquality
    :: Eq global
    => ScopeId request -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> KernelProof.BuiltProof global -> KernelProof.BuiltProof global
    -> Scoped request global (KernelProof.BuiltProof global)
scopeReconstructBooleanEquality scope left right forward backward = do
    context <- scopeContext scope
    let finish = \case
            BooleanEqualityFinished result -> Except.ExceptT (pure result)
            pending -> lift (advanceBooleanEqualityProof context pending) >>= finish
    finish (BooleanEqualityFoundation left right forward backward)

-- First-start bridge: the real directional entry prepares its operands and
-- starts a body query under an actual assumption, without a pre-frozen domain.
scopeDirectionalGroundProof
    :: Ord global => ScopeId request -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> Scoped request global (KernelProof.BuiltProof global, Word)
scopeDirectionalGroundProof scope left right = do
    context <- scopeContext scope
    equality <- runScopedCore (\work -> countedEqualScopedCore work left right)
        >>= maybe (scopeIntegrity "invalid directional fixture equality") pure
    eligibility <- Except.ExceptT (admitGroundFamily (ownedContextId scope) context equality [])
    let environment = SearchEnvironment (KernelProof.proofContextGlobalTyping context) [] 0 (definitionViewCatalogue [] [])
        request = FocusedRequest CollectSharedEvidence AnyObviousProof environment Set.empty
            (ownedContextId scope) context equality eligibility AllPermittedSources Nothing SuppliedEvidence Nothing CompletionAllowed
        implication p q = runScopedCore (\work -> countedImplyScopedCore work p q)
            >>= maybe (scopeIntegrity "invalid directional fixture") pure
    forward <- implication left right
    backward <- implication right left
    entry <- Except.ExceptT (admitDirectionalEntry request left right forward backward)
    child <- scopeAssume scope left
    childContext <- scopeContext child
    let body = request {focusedContextId = ownedContextId child, focusedContext = childContext,
            focusedTarget = right, focusedDirectionalEntry = entry}
        start = startFocusedGround body >>= \case
            GroundStartPending -> start
            GroundStartUnavailable -> scopeIntegrity "directional body unavailable"
            GroundStarted (FocusedGroundQuery query _ _) -> do
                before <- lift getConversionPool
                proof <- finish query
                after <- lift getConversionPool
                pure (proof, Conversion.conversionPoolAmount before - Conversion.conversionPoolAmount after)
        finish query = advanceGroundCertificate AnyObviousProof query >>= \case
            GroundQueryPending -> finish query
            GroundQueryFinished _ (Right (OwnedGroundCertificate proof _ _)) -> pure proof
            _ -> scopeIntegrity "directional body did not finish"
    start

-- The private bridge supplies an unevaluated old requirement to detect a
-- registration-only rescan, then observes real publication/completion returns.
scopeConsumerDelivery
    :: Ord global => ProofRequirement -> ScopeId request -> Evidence request global
    -> Scoped request global (Int, [(Natural, Either (ObviousFailure global) (KernelProof.BuiltProof global))])
scopeConsumerDelivery unusedRequirement scope supplied = do
    evidence <- scopeAt scope supplied
    let proof = ObviousProof (evidenceProof evidence)
            (CandidateDependencies (kernelSourceImportUses (evidenceUses evidence)) Nothing)
    State.modify' (\state -> state {searchCanonicalRequest = True})
    identifier <- Except.ExceptT (internFocusedObligation (ownedContextId scope)
        AllPermittedSources FocusedOnly (obviousProofStatement proof))
    let key = FocusedProducerKey identifier GeneralSearch
        progress = RunningPhase 0
        consumer role requirement ordinal = FocusedConsumer role requirement
            (Choice.OwnedChoice ordinal) ordinal [AfterFocusedCertificate identifier]
        producer = FocusedProducer progress Seq.empty
    choices <- maybe (scopeIntegrity "delivery fixture lost its producer") pure
        (Choice.insertProducer 0 key (FocusedChoice 0 [AfterFocusedProducer key] 1 Nothing DiscoveryComplete) Choice.empty)
    branches <- foldM (\forest ordinal -> maybe (scopeIntegrity "delivery fixture lost a consumer") pure
        (Choice.insert ordinal Choice.RootContinuation (FocusedChoice ordinal [] 1 Nothing DiscoveryComplete) forest))
        choices [1 .. 10]
    let initial = FocusedSchedule branches 11 512 Seq.empty Seq.empty Seq.empty Seq.empty
            (Map.singleton key producer) Seq.empty Seq.empty 0
        probe = registerFocusedConsumer Nothing key (consumer SearchDependency AnyObviousProof 2)
            (FocusedProducer progress (Seq.singleton (consumer SearchDependency unusedRequirement 1))) initial
        waiting schedule = case Map.lookup key (scheduledProducers schedule) of
            Just (FocusedProducer _ consumers) -> Just (Seq.length consumers)
            Nothing -> Nothing
        attach snapshot role requirement ordinal schedule = case Map.lookup key (scheduledProducers schedule) of
            Just current -> pure (registerFocusedConsumer snapshot key (consumer role requirement ordinal) current schedule)
            Nothing -> scopeIntegrity "delivery fixture lost its phase"
    -- Force only the retained queue's length, not its old consumer payload.
    untouched <- maybe (scopeIntegrity "delivery probe lost its phase") pure (waiting probe)
    untouched `seq` pure ()
    ordinary <- foldM (\schedule ordinal -> attach Nothing SearchDependency AnyObviousProof ordinal schedule) initial [1 .. 8]
    waitingSupport <- attach Nothing SearchDependency MustUseCanonicalDefinition 9 ordinary
    Except.ExceptT (retainFocusedCertificate identifier proof)
    published <- lift (notifyFocusedConsumers identifier waitingSupport)
    snapshot <- lift (lookupFocusedCertificates identifier)
    late <- attach snapshot ExistingEvidenceWait AnyObviousProof 10 published
    let finished = late {scheduledProducers = Map.adjust
            (\(FocusedProducer _ consumers) -> FocusedProducer (FinishedPhase AttemptNotApplicable) consumers)
            key (scheduledProducers late)}
    completed <- lift (notifyFocusedConsumers identifier finished)
    repeated <- lift (notifyFocusedConsumers identifier completed)
    returns <- traverse (\case
        FocusedTask (Choice.OwnedChoice owner) ordinal (FocusedReturn result) [AfterFocusedCertificate returned]
            | owner == ordinal, returned == identifier -> case result of
                AttemptSucceeded delivered -> pure (ordinal, Right (obviousBuiltProof delivered))
                AttemptFailed failure -> pure (ordinal, Left failure)
                _ -> scopeIntegrity "delivery fixture returned an unexpected miss"
        _ -> scopeIntegrity "delivery changed a consumer owner or continuation") (scheduledReturns repeated)
    unless (waiting repeated == Just 0) (scopeIntegrity "delivery lost its phase or left a completed consumer attached")
    pure (untouched, toList returns)

data BooleanBodyHandoff = BodyGroundExhausted | BodyFocusedExhausted | BodySelectedFactExhausted
    deriving stock (Eq)

-- Owner-state bridge at the retained Boolean-body continuation. Preparation and
-- source construction precede competing expenditure; only the chosen account
-- is depleted. The late source has already been checked but not yet published.
scopeBooleanBodyHandoff
    :: Ord global => BooleanBodyHandoff -> ScopeId request -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> KernelProof.BuiltProof global
    -> Scoped request global (KernelProof.BuiltProof global, Word, Word, Bool)
scopeBooleanBodyHandoff boundary parent left target lateProof = do
    parentContext <- scopeContext parent
    equality <- runScopedCore (\work -> countedEqualScopedCore work left target)
        >>= maybe (scopeIntegrity "invalid handoff fixture equality") pure
    let typing = KernelProof.proofContextGlobalTyping parentContext
        environment = SearchEnvironment typing []
            (fromIntegral (length (KernelProof.proofContextHypotheses parentContext))) (definitionViewCatalogue [] [])
    eligibility <- Except.ExceptT (admitGroundFamily (ownedContextId parent) parentContext equality [])
    scope <- scopeAssume parent left
    context <- scopeContext scope
    let request = FocusedRequest CollectSharedEvidence AnyObviousProof environment Set.empty
            (ownedContextId scope) context target eligibility AllPermittedSources Nothing SuppliedEvidence Nothing CompletionAllowed
    input <- Except.ExceptT (beginPreparedFocusedRequest request target)
    equations <- Except.ExceptT (endpointProducerFor request)
    unless (equations /= SuppliedEquations) (scopeIntegrity "handoff fixture unexpectedly has endpoint equations")
    -- A native body can wait for an independently prepared source in this real
    -- context. Start with seed syntax, then reach its actual blocked cursor.
    query@(GroundQuery queryIndex) <- scopeStartGround typing scope [target] [] target
    let block = scopeAdvanceGround query >>= \case
            GroundQueryPending -> block
            GroundQueryBlocked _ failure -> pure failure
            _ -> scopeIntegrity "handoff fixture did not reach a native block"
    failure <- block
    let native = FocusedGroundQuery (GroundQuery queryIndex) eligibility []
        selectedProof = ObviousProof lateProof (canonicalHypothesisDependencies 0)
    when (boundary == BodySelectedFactExhausted) do
        publishGroundFact request selectedProof
        advanceFocusedGround request native >>= \case
            GroundQueryPending -> pure ()
            _ -> scopeIntegrity "selected fact classification did not yield"
        active <- State.gets (Map.lookup queryIndex . ownedGroundActivations . searchGroundOwner)
        unless (case active of
            Just activation -> activationOutside activation && not (activationOpportunity activation)
                && activationCursor activation == activationSnapshot activation
                && not (Seq.null (activationInputs activation))
            Nothing -> False) (scopeIntegrity "selected fact did not reach the outside-domain opportunity")
    identifier <- Except.ExceptT (internFocusedObligation (ownedContextId parent)
        AllPermittedSources eligibility equality)
    let key = FocusedProducerKey identifier EqualityReasoning
        owner = Choice.OwnedChoice 1
        consumer = FocusedConsumer SearchDependency AnyObviousProof Choice.RootContinuation 0 []
        initial = FocusedSchedule Choice.empty 3 0 Seq.empty Seq.empty Seq.empty Seq.empty
            (Map.singleton key (FocusedProducer (RunningPhase 1) (Seq.singleton consumer))) Seq.empty Seq.empty 0
    choices <- either Except.throwE pure (admitFocusedChoice (Choice.insertProducer 1 key)
        (FocusedChoice 0 [] 1 Nothing DiscoveryComplete) initial)
    -- The independent source choice also owns unfinished ordinary work. Its
    -- focused failure cannot retire the body producer or its native query.
    choicesWithSource <- either Except.throwE pure (admitFocusedChoice (Choice.insert 2 Choice.RootContinuation)
        (FocusedChoice 1 [] 2 Nothing DiscoveryComplete) initial {scheduledChoices = choices})
    let frame = AfterBooleanBodyGround request input [FocusedTheorem] Nothing False
        handoff = FocusedTask owner 0 (case boundary of
            BodySelectedFactExhausted -> FocusedGround request (Just native)
            _ -> FocusedAwaitGround request native failure) [frame]
        source = FocusedFactSourceTask (Choice.OwnedChoice 2) 1 input False AllDefinitionViews []
            (FactDefinitionUse selectedProof (FactDefinitionSources Nothing []))
        schedule = initial {scheduledChoices = choicesWithSource,
            scheduledReturns = Seq.singleton handoff,
            scheduledPreparation = if boundary == BodyFocusedExhausted then Seq.singleton source else Seq.empty}
    before <- State.gets (Seq.length . ownedGroundQueries . searchGroundOwner)
    -- Model sibling expenditure after the native block, never a fresh request
    -- with zero credit. These updates only decrease the existing accounts.
    -- Three units authorize this direct consumer; the remaining three cannot
    -- finish the four-unit fork, including its partially paid child admission.
    case boundary of
        BodyGroundExhausted -> lift (putScopeWork GroundScopeWork 6)
        BodyFocusedExhausted -> lift (putScopeWork FocusedScopeWork 0)
        -- Authorization costs three; opportunity capture can inspect one of
        -- the two choice rows, but must fail before installing its snapshot.
        BodySelectedFactExhausted -> lift (putScopeWork GroundScopeWork 4)
    focusedBefore <- lift (getScopeWork FocusedScopeWork)
    groundBefore <- lift (getScopeWork GroundScopeWork)
    result <- lift (runFocusedSchedule schedule)
    focused <- lift (getScopeWork FocusedScopeWork)
    ground <- lift (getScopeWork GroundScopeWork)
    after <- State.gets (Seq.length . ownedGroundQueries . searchGroundOwner)
    OwnedGroundQuery _ _ _ _ status _ _ <- lookupGroundQuery query
    let retained = before == after && case status of
            OwnedGroundFinished _ (Right _) -> True
            _ -> False
    case result of
        AttemptSucceeded proof -> pure (obviousBuiltProof proof, focusedBefore - focused, groundBefore - ground, retained)
        AttemptFailed problem -> Except.throwE problem
        AttemptNotApplicable -> scopeIntegrity "handoff fixture lost its fallback"

-- Exercise the actual directional startup and witness-cache boundary without
-- manufacturing evidence. The original family is frozen first; both nominal
-- assumption children then request inventories through the same lazy entry.
scopeDirectionalInventories
    :: Ord global => ScopeId request -> ScopedCheckedCore global
    -> ScopedCheckedCore global -> ScopedCheckedCore global -> ScopedCheckedCore global -> CoreType
    -> Scoped request global ([[ScopedCheckedCore global]], Bool)
scopeDirectionalInventories scope anchor left right selectedGoal coreType = do
    context <- scopeContext scope
    eligibility <- Except.ExceptT (admitGroundFamily (ownedContextId scope) context anchor [])
    familyId <- case eligibility of
        SeedEligible identifier -> pure identifier
        _ -> scopeIntegrity "a directional fixture lost its anchor"
    let environment = SearchEnvironment (KernelProof.proofContextGlobalTyping context) [] 0 (definitionViewCatalogue [] [])
        request = FocusedRequest CollectSharedEvidence AnyObviousProof environment Set.empty
            (ownedContextId scope) context anchor eligibility AllPermittedSources Nothing SuppliedEvidence Nothing CompletionAllowed
        implication p q = runScopedCore (\work -> countedImplyScopedCore work p q)
            >>= maybe (scopeIntegrity "invalid directional fixture") pure
    original <- inventory request
    forward <- implication left right
    backward <- implication right left
    equality <- runScopedCore (\work -> countedEqualScopedCore work left right)
        >>= maybe (scopeIntegrity "invalid directional fixture equality") pure
    entry <- Except.ExceptT (admitDirectionalEntry request {focusedTarget = equality} left right forward backward)
    let direction assumed target = do
            child <- scopeAssume scope assumed
            childContext <- scopeContext child
            pure request {focusedContextId = ownedContextId child, focusedContext = childContext,
                focusedTarget = target, focusedDirectionalEntry = entry}
    firstRequest <- direction left right
    secondRequest <- direction right left
    -- Select the descendant before the entry caches its common pair. Its
    -- extra syntax must compose above that base, never disappear into it.
    selectedEligibility <- Except.ExceptT (selectedGoalFamily firstRequest selectedGoal)
    firstTerms <- inventory firstRequest
    selectedTerms <- inventory firstRequest {focusedEligibility = selectedEligibility, focusedTarget = selectedGoal}
    secondTerms <- inventory secondRequest
    outside <- inventory secondRequest {focusedEligibility = ExistingFamily WitnessBody familyId}
    retained <- inventory request
    common <- case entry of
        Nothing -> pure False
        Just (DirectionalEntryId index) -> do
            prepared <- State.gets (Seq.lookup index . ownedDirectionalEntries . searchGroundOwner)
            case prepared of
                Just (DirectionalEntry _ _ _ _ _ (DirectionsPrepared _ (Just (SeedEligible (GroundFamilyId selected))))) -> do
                    family <- State.gets (Seq.lookup selected . ownedGroundFamilies . searchGroundOwner)
                    pure (maybe False ((== ownedContextId scope) . familyScope) family)
                _ -> pure False
    pure ([original, firstTerms, selectedTerms, secondTerms, outside, retained], common)
  where
    inventory request = Except.ExceptT (beginWitnessInventory request coreType) >>= \case
        WitnessAwaitInventory -> inventory request
        WitnessComplete -> pure []
        WitnessInventory catalogue cursor -> collect catalogue cursor
        _ -> scopeIntegrity "a directional witness fixture entered candidate search"
    collect catalogue cursor = Except.ExceptT (runWitnessCatalogue (\work -> Search.nextCatalogueTypeTermCounted work cursor)) >>= \case
        Nothing -> pure []
        Just (identifier, following) -> do
            term <- maybe (scopeIntegrity "a selected inventory crossed catalogue ownership")
                (pure . Search.catalogueTermValue) (Search.catalogueTerm catalogue identifier)
            (term :) <$> collect catalogue following


advanceTheoremMatch
    :: Ord global
    => SearchEnvironment global -> TheoremMatchStep global
    -> State (ObviousSearchState global) (TheoremMatchStep global)
advanceTheoremMatch _ finished@TheoremMatchFinished{} = pure finished
advanceTheoremMatch environment@(SearchEnvironment globalType _ _ _)
        (TheoremMatchPending binders previousProgress initialSubstitutions pending) = do
    before <- getFocusedWorkBudget
    result <- Except.runExceptT (loop (512 :: Word) initialSubstitutions pending)
    after <- getFocusedWorkBudget
    let spent = previousProgress + fromIntegral (before - after)
    pure case result of
        Left failure -> TheoremMatchFinished (Left failure)
        Right (TheoremMatchPending retained _ updated rest) -> TheoremMatchPending retained spent updated rest
        Right (TheoremMatchFinished matched) -> TheoremMatchFinished (attachProgress spent <$> matched)
  where
    parameterCount = Template.binderEnvironmentCount binders
    charge = do
        available <- lift consumeSearchStep
        unless available (Except.throwE (ObviousResourceExhausted ObviousFocusedWorkLimit))
    malformed message = Except.throwE (ObviousIntegrityFailure (KernelProof.ProofStructuralCompositionMismatch message))
    finished = pure . TheoremMatchFinished . Right
    suspend updated rest = pure (TheoremMatchPending binders 0 updated rest)

    needsHead applied row = do
        charge
        case checkedOccurrenceView row of
            OccurrenceApplication function _ -> needsHead True function
            OccurrenceLambda{} -> pure applied
            _ -> pure False

    patternSlot depth row = case checkedOccurrenceView row of
        OccurrenceBound index | index >= depth && index < depth + parameterCount ->
            Just (Template.MatcherSlot (parameterCount - (index - depth) - 1))
        _ -> Nothing

    etaSlot depth (Just (EtaSpine _ (Just (start, slot)))) | start == depth = Just slot
    etaSlot _ _ = Nothing

    retainedSpine depth known@(Just (EtaSpine bottom _)) | depth < bottom = known
    retainedSpine _ _ = Nothing

    preparePattern turns depth known patternRow goalRow updated rest =
        case (known, checkedOccurrenceView patternRow) of
            (Nothing, OccurrenceLambda{}) | parameterCount > 0 -> loop turns updated
                (MatchEtaLambdas depth patternRow goalRow 0 patternRow : rest)
            _ -> prepareGoal turns depth known patternRow goalRow updated rest

    prepareGoal turns depth known patternRow goalRow updated rest = do
        -- The checked occurrence summary rules out escaping locals before any
        -- target beta recovery. A rebasable bare/eta slot keeps the whole target.
        needs <- if isJust (patternSlot depth patternRow <|> etaSlot depth known)
                && not (checkedOccurrenceDependsOnBinderPrefix goalRow)
            then pure False else needsHead False goalRow
        loop turns updated ((if needs then MatchGoalHead SmallPreparation depth known patternRow goalRow
            else MatchHeads depth known patternRow goalRow) : rest)

    loop _turns updated [] = finished (TemplateMatched updated 0)
    loop 0 updated rest = suspend updated rest
    loop turns updated (work : rest) = case work of
        MatchVisit depth known patternRow goalRow -> do
            charge
            needs <- needsHead False patternRow
            if needs then loop (turns - 1) updated (MatchPatternHead SmallPreparation depth known patternRow goalRow : rest)
                else preparePattern (turns - 1) depth known patternRow goalRow updated rest
        MatchPatternHead effort depth known patternRow goalRow -> do
            result <- lift (reduce effort (checkedOccurrenceScopedCore patternRow))
            case result of
                NeedsMoreEffort offered -> suspend updated (MatchPatternHead (FullPreparation offered) depth known patternRow goalRow : rest)
                PreparationFinished outcome -> do
                    residual <- Except.ExceptT (pure outcome)
                    prepared <- Except.ExceptT (analyseTheoremOccurrence environment depth residual)
                    preparePattern (turns - 1) depth known prepared goalRow updated rest
        MatchGoalHead effort depth known patternRow goalRow -> do
            result <- lift (reduce effort (checkedOccurrenceScopedCore goalRow))
            case result of
                NeedsMoreEffort offered -> suspend updated (MatchGoalHead (FullPreparation offered) depth known patternRow goalRow : rest)
                PreparationFinished outcome -> do
                    residual <- Except.ExceptT (pure outcome)
                    prepared <- Except.ExceptT (analyseTheoremOccurrence environment depth residual)
                    loop (turns - 1) updated (MatchHeads depth known patternRow prepared : rest)
        MatchHeads depth known patternRow goalRow -> matchHeads (turns - 1) depth known patternRow goalRow updated rest
        MatchEtaLambdas depth patternRow goalRow count current -> do
            charge
            case checkedOccurrenceView current of
                OccurrenceLambda _ body -> loop (turns - 1) updated
                    (MatchEtaLambdas depth patternRow goalRow (count + 1) body : rest)
                _ -> loop (turns - 1) updated
                    (MatchEtaArguments depth patternRow goalRow count 0 current : rest)
        MatchEtaArguments depth patternRow goalRow count arguments current -> do
            charge
            let finishScan suffix = prepareGoal (turns - 1) depth
                    (Just (EtaSpine (depth + count) suffix)) patternRow goalRow updated rest
            case checkedOccurrenceView current of
                OccurrenceApplication function argument | arguments < count -> do
                    charge
                    case checkedOccurrenceView argument of
                        OccurrenceBound index | index == arguments -> loop (turns - 1) updated
                            (MatchEtaArguments depth patternRow goalRow count (arguments + 1) function : rest)
                        _ -> finishScan Nothing
                _ -> finishScan (if arguments == 0 then Nothing else
                    (\slot -> (depth + count - arguments, slot)) <$> patternSlot (depth + count) current)
        MatchSlotCompare effort existing checked -> do
            result <- lift (runConversionPreparation effort (\limit ->
                Conversion.convertibleChecked globalType limit existing checked))
            case result of
                NeedsMoreEffort offered -> suspend updated (MatchSlotCompare (FullPreparation offered) existing checked : rest)
                PreparationFinished (Left failure) -> Except.throwE failure
                PreparationFinished (Right Conversion.Convertible) -> loop (turns - 1) updated rest
                PreparationFinished (Right Conversion.NotConvertible) ->
                    finished (TemplateMismatch (TemplateMismatchEvidence ConversionMismatch Nothing 0))

    reduce effort checked = runConversionPreparation effort (\limit ->
        Conversion.residualizeHeadChecked (Conversion.ConversionRecoveryTyping globalType globalType) limit checked)

    matchHeads turns depth known patternRow goalRow substitutions rest
        | Just slot <- patternSlot depth patternRow <|> etaSlot depth known = assign slot
        | mixedLambda = do
            sameType <- Except.ExceptT (coreTypeIdentity
                (scopedCoreType (checkedOccurrenceScopedCore patternRow))
                (scopedCoreType (checkedOccurrenceScopedCore goalRow)))
            if not sameType then mismatch else do
                let pointwise row = do
                        body <- runScopedCore (\work -> countedPointwiseBodyScopedCore work
                            (checkedOccurrenceScopedCore row))
                        checked <- maybe (malformed "an arrow matcher operand lost its function type") pure body
                        Except.ExceptT (analyseTheoremOccurrence environment (depth + 1) checked)
                patternBody <- pointwise patternRow
                goalBody <- pointwise goalRow
                loop turns substitutions (MatchVisit (depth + 1) (retainedSpine (depth + 1) known)
                    patternBody goalBody : rest)
        | otherwise = case checkedOccurrenceView patternRow of
            OccurrenceBound index
                | index < depth -> atomic (CBound index)
                | otherwise -> atomic (CBound (index - parameterCount))
            OccurrenceGlobal global -> atomic (CGlobal global)
            OccurrenceIntrinsic intrinsic -> atomic (CIntrinsic intrinsic)
            OccurrenceLogicalSelect coreType -> atomic (CLogicalSelect coreType)
            OccurrenceOpaqueInteger integer -> atomic (COpaqueInteger integer)
            OccurrenceApplication function argument ->
                case goalView of
                    OccurrenceApplication foundFunction foundArgument ->
                        pair function foundFunction argument foundArgument
                    _ -> mismatch
            OccurrenceLambda binderType body ->
                case goalView of
                    OccurrenceLambda foundType foundBody -> binder binderType body foundType foundBody
                    _ -> mismatch
            OccurrenceFalsum -> atomic CFalsum
            OccurrenceTruth -> atomic CTruth
            OccurrenceNegation child ->
                case goalView of
                    OccurrenceNegation found -> loop turns substitutions (MatchVisit depth Nothing child found : rest)
                    _ -> mismatch
            OccurrenceConjunction left right ->
                case goalView of
                    OccurrenceConjunction foundLeft foundRight -> pair left foundLeft right foundRight
                    _ -> mismatch
            OccurrenceDisjunction left right ->
                case goalView of
                    OccurrenceDisjunction foundLeft foundRight -> pair left foundLeft right foundRight
                    _ -> mismatch
            OccurrenceImplication premise conclusion ->
                case goalView of
                    OccurrenceImplication foundPremise foundConclusion ->
                        pair premise foundPremise conclusion foundConclusion
                    _ -> mismatch
            OccurrenceEquality operandType left right ->
                case goalView of
                    OccurrenceEquality foundType foundLeft foundRight -> do
                        sameType <- Except.ExceptT (coreTypeIdentity operandType foundType)
                        if sameType then pair left foundLeft right foundRight else mismatch
                    _ -> mismatch
            OccurrenceUniversal binderType body ->
                case goalView of
                    OccurrenceUniversal foundType foundBody -> binder binderType body foundType foundBody
                    _ -> mismatch
            OccurrenceExistential binderType body ->
                case goalView of
                    OccurrenceExistential foundType foundBody -> binder binderType body foundType foundBody
                    _ -> mismatch
      where
        goalView = checkedOccurrenceView goalRow
        mixedLambda = case
                ( scopedCoreType (checkedOccurrenceScopedCore patternRow)
                , checkedOccurrenceView patternRow, goalView) of
            (TyArrow{}, OccurrenceLambda{}, OccurrenceLambda{}) -> False
            (TyArrow{}, OccurrenceLambda{}, _) -> True
            (TyArrow{}, _, OccurrenceLambda{}) -> True
            _ -> False
        assign slot = do
            work <- lift getFocusedWorkBudget
            let (result, remaining) = countedRebaseCheckedOccurrence work goalRow
            lift (putFocusedWorkBudget remaining)
            case result of
                Left failure -> Except.throwE
                    (obviousCountedFailure
                        (\_cause -> ObviousIntegrityFailure
                            (KernelProof.ProofStructuralCompositionMismatch
                                "theorem slot rebasing contradicted its checked occurrence")) failure)
                Right Nothing -> finished (TemplateHigherOrderUnsupported 0)
                Right (Just candidate) -> bindSlot turns rest slot candidate substitutions
        atomic expected = do
            same <- Except.ExceptT
                (canonicalIdentityWithDifference
                    (scopedCoreTerm (checkedOccurrenceScopedCore goalRow)) expected)
            case same of
                CountedIdentical -> loop turns substitutions rest
                CountedDifferent difference ->
                    let (mismatchClass, structuralDifference) = candidateDifference difference
                    in finished (TemplateMismatch
                        (TemplateMismatchEvidence mismatchClass (Just structuralDifference) 0))

        pair left foundLeft right foundRight = loop turns substitutions
            (MatchVisit depth Nothing left foundLeft : MatchVisit depth Nothing right foundRight : rest)

        binder binderType body foundType foundBody = do
            sameType <- Except.ExceptT (coreTypeIdentity binderType foundType)
            if sameType
                then loop turns substitutions (MatchVisit (depth + 1)
                    (retainedSpine (depth + 1) known) body foundBody : rest)
                else finished (TemplateMismatch (TemplateMismatchEvidence BinderMismatch Nothing 0))

        mismatch = finished (TemplateMismatch (TemplateMismatchEvidence SyntacticMismatch Nothing 0))

    bindSlot turns rest slot checked substitutions =
        case Template.binderEnvironmentSlotType slot binders of
            Nothing -> malformed "theorem matcher referenced an invalid stable slot"
            Just expectedType -> do
                typeMatches <- Except.ExceptT (coreTypeIdentity expectedType (scopedCoreType checked))
                if not typeMatches
                    then finished (TemplateMismatch (TemplateMismatchEvidence BinderMismatch Nothing 0))
                    else case Template.lookupTemplateSubstitution slot substitutions of
                        Nothing -> loop turns
                            (Template.insertTemplateSubstitution slot checked substitutions) rest
                        Just existing -> do
                            identical <- Except.ExceptT (scopedIdentity existing checked)
                            if identical then loop turns substitutions rest
                                else loop turns substitutions (MatchSlotCompare SmallPreparation existing checked : rest)

    attachProgress progress = \case
        TemplateMismatch (TemplateMismatchEvidence mismatch difference _oldProgress) ->
            TemplateMismatch (TemplateMismatchEvidence mismatch difference progress)
        TemplateHigherOrderUnsupported _oldProgress -> TemplateHigherOrderUnsupported progress
        TemplateMatched updated _oldProgress -> TemplateMatched updated progress

removeInnerBindersCounted
    :: Natural
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (Maybe (CanonicalTerm global)))
removeInnerBindersCounted amount =
    go 0
  where
    go localDepth term = do
        hasWork <- consumeSearchStep
        if not hasWork
            then
                pure
                    (Left
                        (ObviousResourceExhausted
                            ObviousFocusedWorkLimit))
            else
                case term of
                    CBound index
                        | index < localDepth ->
                            pure (Right (Just (CBound index)))
                        | index < localDepth + amount ->
                            pure (Right Nothing)
                        | otherwise ->
                            pure (Right (Just (CBound (index - amount))))
                    CGlobal global ->
                        pure (Right (Just (CGlobal global)))
                    CIntrinsic intrinsic ->
                        pure (Right (Just (CIntrinsic intrinsic)))
                    CLogicalSelect coreType ->
                        pure (Right (Just (CLogicalSelect coreType)))
                    COpaqueInteger integer ->
                        pure (Right (Just (COpaqueInteger integer)))
                    CApp function argument ->
                        binary localDepth CApp function argument
                    CLam binderType body ->
                        unary (localDepth + 1) (CLam binderType) body
                    CFalsum -> pure (Right (Just CFalsum))
                    CTruth -> pure (Right (Just CTruth))
                    CNot proposition ->
                        unary localDepth CNot proposition
                    CAnd left right ->
                        binary localDepth CAnd left right
                    COr left right ->
                        binary localDepth COr left right
                    CImp premise conclusion ->
                        binary localDepth CImp premise conclusion
                    CEq operandType left right ->
                        binary localDepth (CEq operandType) left right
                    CForall binderType body ->
                        unary
                            (localDepth + 1)
                            (CForall binderType)
                            body
                    CExists binderType body ->
                        unary
                            (localDepth + 1)
                            (CExists binderType)
                            body

    unary depth constructor term = do
        result <- go depth term
        pure (fmap (fmap constructor) result)

    binary depth constructor left right = do
        leftResult <- go depth left
        case leftResult of
            Left failure -> pure (Left failure)
            Right Nothing -> pure (Right Nothing)
            Right (Just leftTerm) -> do
                rightResult <- go depth right
                pure
                    (fmap
                        (fmap (constructor leftTerm))
                        rightResult)

checkedProposition
    :: KernelProof.ProofContext global
    -> CanonicalTerm global
    -> State (ObviousSearchState global)
        (Either
            (ObviousFailure global)
            (ScopedCheckedCore global))
checkedProposition context term = do
    checkedResult <-
        runCountedKernel
            (KernelProof.countedScopedTerm
                    context term)
    case checkedResult of
        Left failure -> pure (Left failure)
        Right checked -> do
            propositionType <-
                coreTypeIdentity (scopedCoreType checked) TyProp
            pure do
                matches <- propositionType
                if matches
                    then Right checked
                    else
                        Left
                            (ObviousIntegrityFailure
                                (KernelProof.ProofStructuralCompositionMismatch
                                    "obvious inference constructed a non-proposition subgoal"))

fromObvious
    :: CandidateDependencies
    -> Either
        (ObviousFailure global)
        (KernelProof.BuiltProof global)
    -> Attempt global
fromObvious dependencies =
    either
        AttemptFailed
        (AttemptSucceeded . (`ObviousProof` dependencies))


-- Private evidence construction belongs to the focused driver, so its scope
-- association cannot be attached by an external producer of opaque proofs.
newtype ScopeId request = ScopeId FocusedContextId
    deriving stock (Eq, Ord)
type role ScopeId nominal

ownedContextId :: ScopeId request -> FocusedContextId
ownedContextId (ScopeId contextId) = contextId

data Evidence request global = Evidence
    !(ScopeId request)
    !(KernelProof.BuiltProof global)
    !KernelSourceUses
type role Evidence nominal nominal

evidenceProof :: Evidence request global -> KernelProof.BuiltProof global
evidenceProof (Evidence _scope proof _uses) = proof

evidenceUses :: Evidence request global -> KernelSourceUses
evidenceUses (Evidence _scope _proof uses) = uses

data GroundAllowance = GroundAllowance
    { groundWork :: !Word
    , groundTerms :: !Word
    , groundBranches :: !Word
    , groundInstances :: !Word
    , groundUniversals :: !UniversalPolicy
    }
    deriving stock (Show, Eq)

type Scoped request global =
    Except.ExceptT (ObviousFailure global) (State (ObviousSearchState global))

-- The same owner admits production and fixture scopes. The rank-2 request
-- prevents private evidence handles from crossing independent runs.
runScoped
    :: Word
    -> Conversion.ConversionPool
    -> GroundAllowance
    -> KernelProof.ProofContext global
    -> Map.Map ImportIx (FrozenCheckedCore global)
    -> (forall request. ScopeId request -> Scoped request global result)
    -> (Either (ObviousFailure global) result, Word, Conversion.ConversionPool)
runScoped work pool ground context imports action =
    let computation = do
            root <- Except.ExceptT (admitFocusedContext FocusedRootScope context)
            action (ScopeId root)
        (result, final) = State.runState (Except.runExceptT computation)
            (initialSearchState
                disabledSearchPolicy {policyUniversals = groundUniversals ground}
                work pool ground (obviousFactDomainLimit defaultObviousBudget) imports)
    in result `seq` final `seq`
        (result, searchRemainingFocusedWork final, searchRemainingConversionPool final)

scopeCharge :: Scoped request global ()
scopeCharge = scopeChargeTo FocusedScopeWork

-- Scope bookkeeping and selected-proof certification belong to the component
-- requesting them. Ground publication must not depend on unused focused work.
-- Both owners spend the same request conversion pool; only structural work has
-- separate existing limits.
data ScopeWork = FocusedScopeWork | GroundScopeWork

scopeWorkLimit :: ScopeWork -> ObviousLimit
scopeWorkLimit FocusedScopeWork = ObviousFocusedWorkLimit
scopeWorkLimit GroundScopeWork = ObviousRefutationWorkLimit

getScopeWork :: ScopeWork -> State (ObviousSearchState global) Word
getScopeWork FocusedScopeWork = getFocusedWorkBudget
getScopeWork GroundScopeWork = State.gets (groundWork . searchRemainingGround)

putScopeWork :: ScopeWork -> Word -> State (ObviousSearchState global) ()
putScopeWork FocusedScopeWork = putFocusedWorkBudget
putScopeWork GroundScopeWork = \remaining -> State.modify' (\state -> state
    { searchRemainingGround = (searchRemainingGround state) {groundWork = remaining} })

scopeChargeTo :: ScopeWork -> Scoped request global ()
scopeChargeTo owner = do
    available <- lift (getScopeWork owner)
    if available == 0
        then Except.throwE (ObviousResourceExhausted (scopeWorkLimit owner))
        else lift (putScopeWork owner (available - 1))

runScopeCore
    :: ScopeWork
    -> (failure -> ObviousFailure global)
    -> (Word -> (Either (CountedCoreFailure failure) result, Word))
    -> Scoped request global result
runScopeCore owner failure operation = do
    available <- lift (getScopeWork owner)
    let (result, remaining) = operation available
    finishScopeWork owner failure remaining result

finishScopeWork
    :: ScopeWork -> (failure -> ObviousFailure global) -> Word
    -> Either (CountedCoreFailure failure) result -> Scoped request global result
finishScopeWork owner failure remaining result = do
    lift (putScopeWork owner remaining)
    either (Except.throwE . \case
        CountedCoreStructuralWorkExhausted -> ObviousResourceExhausted (scopeWorkLimit owner)
        CountedCoreOperationFailed problem -> failure problem) pure result

runScopeKernel
    :: ScopeWork
    -> KernelProof.CountedProof global result
    -> Scoped request global result
runScopeKernel owner operation = do
    available <- lift (getScopeWork owner)
    pool <- lift getConversionPool
    let (result, remaining, afterPool) = KernelProof.runCountedProof available pool operation
    lift (putConversionPool afterPool)
    finishScopeWork owner kernelFailure remaining result

scopeIntegrity :: Text -> Scoped request global result
scopeIntegrity = Except.throwE . ObviousIntegrityFailure . KernelProof.ProofStructuralCompositionMismatch

lookupOwnedScope :: ScopeId request -> Scoped request global (FocusedContext global)
lookupOwnedScope = lookupOwnedScopeWith FocusedScopeWork

lookupOwnedScopeWith :: ScopeWork -> ScopeId request -> Scoped request global (FocusedContext global)
lookupOwnedScopeWith owner (ScopeId (FocusedContextId index)) = do
    scopeChargeTo owner
    found <- State.gets (Seq.lookup index . searchFocusedContexts)
    maybe (scopeIntegrity "an Obvious scope is outside its request") pure found

scopeContext :: ScopeId request -> Scoped request global (KernelProof.ProofContext global)
scopeContext = scopeContextWith FocusedScopeWork

scopeContextWith :: ScopeWork -> ScopeId request -> Scoped request global (KernelProof.ProofContext global)
scopeContextWith owner scope = do
    FocusedContext _lineage context <- lookupOwnedScopeWith owner scope
    pure context

runScopedKernel
    :: KernelProof.CountedProof global result
    -> Scoped request global result
runScopedKernel = runScopeKernel FocusedScopeWork

currentGroundLimits :: State (ObviousSearchState global) Refutation.RefutationLimits
currentGroundLimits = do
    allowance <- State.gets searchRemainingGround
    pool <- getConversionPool
    pure (Refutation.RefutationLimits (groundWork allowance) pool
        (groundTerms allowance) (groundBranches allowance) (groundInstances allowance) True True (groundUniversals allowance))

-- A sequential quantum holds the current owner allowance exclusively. Yield
-- after 512 structural units, domain publication, a new ordinary certificate,
-- or a stopped query. Each operation retains its own checks and can exceed
-- this scheduling quantum; it cannot exceed its real remaining allowance.
advanceOwnedGround
    :: Eq global
    => Refutation.RefutationSession global
    -> State (ObviousSearchState global) (Refutation.RefutationProgress global)
advanceOwnedGround session = do
    before <- currentGroundLimits
    let threshold = Refutation.refutationWorkLimit before
            - min 512 (Refutation.refutationWorkLimit before)
        advance available current =
            let result@(remainder, outcome) = Refutation.advanceRefutation available current
            in case outcome of
                Refutation.RefutationPending following
                    | Refutation.refutationWorkLimit remainder > threshold
                    , not (isNothing (Refutation.refutationSessionDomain current)
                        && isJust (Refutation.refutationSessionDomain following))
                    , not (isNothing (Refutation.refutationSessionAnyCandidate current)
                        && isJust (Refutation.refutationSessionAnyCandidate following)) ->
                            advance remainder following
                _ -> result
        (remaining, progress) = advance before session
    committed <- commitGroundLimits before remaining
    pure (if committed then progress else Refutation.RefutationFinished (groundProgressStatistics progress)
        (Left (Refutation.RefutationInternalFailure
            "an Obvious ground query replenished or overspent its allowance")))

commitGroundLimits :: Refutation.RefutationLimits -> Refutation.RefutationLimits
    -> State (ObviousSearchState global) Bool
commitGroundLimits before remaining = do
    let monotone =
            Refutation.refutationWorkLimit remaining <= Refutation.refutationWorkLimit before
            && Conversion.conversionPoolAmount (Refutation.refutationConversionPool remaining)
                <= Conversion.conversionPoolAmount (Refutation.refutationConversionPool before)
            && Refutation.refutationGroundTermLimit remaining <= Refutation.refutationGroundTermLimit before
            && Refutation.refutationBranchNodeLimit remaining <= Refutation.refutationBranchNodeLimit before
            && Refutation.refutationRuleInstanceLimit remaining <= Refutation.refutationRuleInstanceLimit before
            && Refutation.permitsUniversalRemainder
                (Refutation.refutationUniversals before) (Refutation.refutationUniversals remaining)
    if not monotone
        then pure False
        else do
            State.modify' (\state -> state
                { searchRemainingConversionPool = Refutation.refutationConversionPool remaining
                , searchRemainingGround = GroundAllowance
                    (Refutation.refutationWorkLimit remaining)
                    (Refutation.refutationGroundTermLimit remaining)
                    (Refutation.refutationBranchNodeLimit remaining)
                    (Refutation.refutationRuleInstanceLimit remaining)
                    (Refutation.refutationUniversals remaining)
                })
            pure True

groundProgressStatistics :: Refutation.RefutationProgress global -> Refutation.RefutationStatistics
groundProgressStatistics = \case
    Refutation.RefutationPending session -> Refutation.refutationSessionStatistics session
    Refutation.RefutationBlocked statistics _failure _session -> statistics
    Refutation.RefutationFinished statistics _result -> statistics


runScopedCore
    :: (Word -> (Either (CountedCoreFailure Void) result, Word))
    -> Scoped request global result
runScopedCore = runScopeCore FocusedScopeWork absurd

scopeAssume
    :: ScopeId request
    -> ScopedCheckedCore global
    -> Scoped request global (ScopeId request)
scopeAssume parent premise = do
    context <- scopeContext parent
    extended <- runScopedKernel (KernelProof.countedExtendProofContextHypothesis context premise)
    ScopeId <$> Except.ExceptT (admitFocusedContext
        (FocusedAssumptionScope (ownedContextId parent) premise) extended)

scopeBind :: ScopeId request -> CoreType -> Scoped request global (ScopeId request)
scopeBind parent binderType = do
    context <- scopeContext parent
    (extended, _variable) <- runScopedKernel
        (KernelProof.countedExtendProofContextBinder context binderType)
    ScopeId <$> Except.ExceptT (admitFocusedContext
        (FocusedBinderScope (ownedContextId parent) binderType) extended)

-- Only the owner of a checked construction may record it.  In particular this
-- does not validate an arbitrary opaque proof under a newly invented context.
-- Producer scopes are retained here; consumers cannot replace that association.
recordConstruction
    :: ScopeId request
    -> KernelProof.BuiltProof global
    -> Scoped request global (Evidence request global)
recordConstruction = recordConstructionWith FocusedScopeWork

recordConstructionWith
    :: ScopeWork -> ScopeId request -> KernelProof.BuiltProof global
    -> Scoped request global (Evidence request global)
recordConstructionWith owner scope proof = do
    context <- scopeContextWith owner scope
    sameContext <- runScopeCore owner absurd (\work -> countedCoreTypeListIdentity work
        (KernelProof.proofContextTypes context) (scopedCoreContext (KernelProof.builtProofStatement proof)))
    unless sameContext
        (scopeIntegrity "an Obvious construction changed its lexical context")
    available <- lift (getScopeWork owner)
    let (result, remaining) = countedKernelDerivationSourceUses available (KernelProof.builtProofDerivation proof)
    lift (putScopeWork owner remaining)
    uses <- maybe (Except.throwE (ObviousResourceExhausted (scopeWorkLimit owner))) pure result
    imports <- State.gets searchPermittedImports
    for_ (Set.toAscList (kernelSourceImportUses uses)) \index -> do
        scopeChargeTo owner
        unless (Map.member index imports) (scopeIntegrity "an Obvious construction used an unpermitted import")
    for_ (Set.toAscList (kernelSourceExternalHypothesisUses uses)) \index -> do
        -- The indexed builder performs the counted lookup in the producer's
        -- actual hypothesis environment, including non-dense external uses.
        _ <- runScopeKernel owner (KernelProof.countedIndexedHypothesisProof context index)
        pure ()
    pure (Evidence scope proof uses)

scopeHypothesis :: ScopeId request -> HypothesisIx -> Scoped request global (Evidence request global)
scopeHypothesis scope index = do
    context <- scopeContext scope
    proof <- runScopedKernel (KernelProof.countedIndexedHypothesisProof context index)
    recordConstruction scope proof

scopeImported :: ScopeId request -> ImportIx -> Scoped request global (Evidence request global)
scopeImported scope index = do
    context <- scopeContext scope
    scopeCharge
    found <- State.gets (Map.lookup index . searchPermittedImports)
    statement <- maybe (scopeIntegrity "an Obvious import is outside its request") pure found
    proof <- runScopedKernel (KernelProof.countedImportedProof context index statement)
    recordConstruction scope proof

scopeAt
    :: ScopeId request
    -> Evidence request global
    -> Scoped request global (Evidence request global)
scopeAt = scopeAtWith FocusedScopeWork

scopeAtWith
    :: ScopeWork -> ScopeId request -> Evidence request global
    -> Scoped request global (Evidence request global)
scopeAtWith owner consumer evidence@(Evidence producer proof _uses)
    | consumer == producer = pure evidence
    | otherwise = do
        distance <- scopeAncestorDistance owner producer consumer
        weakened <- runScopeKernel owner (KernelProof.countedWeakenProofHypotheses distance proof)
        recordConstructionWith owner consumer weakened

scopeAncestorDistance :: ScopeWork -> ScopeId request -> ScopeId request -> Scoped request global Natural
scopeAncestorDistance owner ancestor = go 0
  where
    go distance current
        | ancestor == current = pure (distance :: Natural)
        | otherwise = do
            FocusedContext lineage _context <- lookupOwnedScopeWith owner current
            case lineage of
                FocusedAssumptionScope previous _premise ->
                    let next = distance + 1
                    in next `seq` go next (ScopeId previous)
                FocusedBinderScope{} -> scopeIntegrity "an Obvious derived proof crossed a term binder"
                FocusedRootScope -> scopeIntegrity "an Obvious proof crossed unrelated assumption scopes"

scopeRequireStatement
    :: Eq global
    => ScopedCheckedCore global
    -> Evidence request global
    -> Scoped request global ()
scopeRequireStatement expected evidence = do
    same <- runScopedCore (\work -> countedScopedCoreIdentity work expected
        (KernelProof.builtProofStatement (evidenceProof evidence)))
    unless same (scopeIntegrity "a certified Obvious input has a different statement")

scopeApplyEquality
    :: Eq global
    => ScopeId request -> Evidence request global -> Evidence request global
    -> Scoped request global (Evidence request global)
scopeApplyEquality scope equation source = do
    equality <- scopeAt scope equation
    premise <- scopeAt scope source
    context <- scopeContext scope
    proof <- runScopedKernel (KernelProof.countedEqualityModusPonensProof context (evidenceProof equality) (evidenceProof premise))
    recordConstruction scope proof

scopeIntroduceImplication
    :: ScopeId request -> Evidence request global -> Scoped request global (Evidence request global)
scopeIntroduceImplication parent (Evidence child body _uses) = do
    FocusedContext lineage _context <- lookupOwnedScope child
    case lineage of
        FocusedAssumptionScope actualParent premise | actualParent == ownedContextId parent -> do
            context <- scopeContext parent
            proof <- runScopedKernel (KernelProof.countedImplicationIntroductionProof context premise body)
            recordConstruction parent proof
        _ -> scopeIntegrity "an Obvious implication discharged a different scope"

scopeIntroduceForall
    :: ScopeId request -> Evidence request global -> Scoped request global (Evidence request global)
scopeIntroduceForall parent (Evidence child body _uses) = do
    FocusedContext lineage _context <- lookupOwnedScope child
    case lineage of
        FocusedBinderScope actualParent binderType | actualParent == ownedContextId parent -> do
            context <- scopeContext parent
            proof <- runScopedKernel (KernelProof.countedForallIntroductionProof context binderType body)
            recordConstruction parent proof
        _ -> scopeIntegrity "an Obvious universal discharged a different scope"

-- A domain handle names the query which paid for its immutable initial syntax.
-- A query handle names the sole current cursor in this request. Neither exposes
-- the service's catalogue, typing snapshot or assumption-bearing session.
newtype GroundDomain request global = GroundDomain Int
type role GroundDomain nominal nominal

newtype GroundQuery request global = GroundQuery Int
type role GroundQuery nominal nominal

data GroundQueryProgress certificate
    = GroundQueryPending
    | GroundQueryBlocked !Refutation.RefutationStatistics !Refutation.RefutationFailure
    | GroundQueryFinished !Refutation.RefutationStatistics
        !(Either Refutation.RefutationFailure certificate)
    deriving stock (Functor)

lookupGroundQuery :: GroundQuery request global -> Scoped request global (OwnedGroundQuery global)
lookupGroundQuery (GroundQuery index) = do
    found <- State.gets (Seq.lookup index . ownedGroundQueries . searchGroundOwner)
    maybe (scopeIntegrity "an Obvious ground query is outside its request") pure found

storeGroundQuery :: GroundQuery request global -> OwnedGroundQuery global -> Scoped request global ()
storeGroundQuery (GroundQuery index) query = State.modify' (\state -> state
    { searchGroundOwner = (searchGroundOwner state)
        { ownedGroundQueries = Seq.update index query (ownedGroundQueries (searchGroundOwner state)) } })

admitGroundQuery :: OwnedGroundQuery global -> Scoped request global (GroundQuery request global)
admitGroundQuery query = do
    scopeChargeTo GroundScopeWork
    queries <- State.gets (ownedGroundQueries . searchGroundOwner)
    let index = Seq.length queries
    unless (index < maxBound) (scopeIntegrity "Obvious ground query identifier overflow")
    State.modify' (\state -> state
        { searchGroundOwner = (searchGroundOwner state) { ownedGroundQueries = queries Seq.|> query } })
    pure (GroundQuery index)

scopeStartGround
    :: GlobalTyping global
    -> ScopeId request
    -> [ScopedCheckedCore global]
    -> [Evidence request global]
    -> ScopedCheckedCore global
    -> Scoped request global (GroundQuery request global)
scopeStartGround globalType scope seedSyntax inputs target = do
    context <- scopeContextWith GroundScopeWork scope
    aligned <- traverse (scopeAtWith GroundScopeWork scope) inputs
    limits <- lift currentGroundLimits
    admitGroundQuery (OwnedGroundQuery (ownedContextId scope) globalType (ownedContextId scope) Nothing
        (OwnedGroundRunning (Refutation.startCertifiedRefutation limits globalType context seedSyntax
            [(evidenceProof evidence, evidenceUses evidence) | evidence <- aligned] target)) Nothing emptyGroundInputCursor)

-- A family owns one frozen seed and exact query identities. A second consumer
-- can finish the first query's pending domain preparation even if its original
-- search alternative was canceled; it never resumes that query's branch search
-- merely to obtain the domain. Every handle still names the sole current cursor.
data GroundStart request global
    = GroundStartPending
    | GroundStartUnavailable
    | GroundStarted !(FocusedGroundQuery request global)

-- Execution family and prepared syntax are retained with the query. The
-- unchanged FocusedRequest remains the authority for selecting extra facts.
data FocusedGroundQuery request global = FocusedGroundQuery
    !(GroundQuery request global) !GroundEligibility ![Refutation.PreparedSyntax global]

admitDirectionalEntry
    :: FocusedRequest global -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> ScopedCheckedCore global -> ScopedCheckedCore global
    -> State (ObviousSearchState global) (Either (ObviousFailure global) (Maybe DirectionalEntryId))
admitDirectionalEntry request left right forward backward
    | not (canSeedFocusedGround request) = pure (Right Nothing)
    | otherwise = Except.runExceptT do
        scopeCharge
        entries <- State.gets (ownedDirectionalEntries . searchGroundOwner)
        let index = Seq.length entries
        when (index == maxBound) (scopeIntegrity "directional entry identifier overflow")
        State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
            {ownedDirectionalEntries = entries Seq.|> DirectionalEntry request left right forward backward DirectionsUnprepared}})
        pure (Just (DirectionalEntryId index))

runDirectionalPreparation
    :: (Refutation.RefutationLimits -> (Refutation.RefutationLimits, Either Refutation.RefutationFailure value))
    -> Scoped request global value
runDirectionalPreparation operation = do
    before <- lift currentGroundLimits
    let (remaining, result) = operation before
    committed <- lift (commitGroundLimits before remaining)
    unless committed (scopeIntegrity "directional preparation changed its ground allowance")
    either (Except.throwE . mapRefutationFailure) pure result

-- Each transition retains its successful checked prefix or terminal failure.
-- Preparation is lazy and charged to the ground requester; family selection
-- uses the equality-entry scope, never a directional assumption's scope.
directionalGroundRequest
    :: Eq global => FocusedRequest global
    -> Scoped request global (Maybe (FocusedRequest global, [Refutation.PreparedSyntax global]))
directionalGroundRequest request = case focusedDirectionalEntry request of
    Just (DirectionalEntryId index) | canSeedFocusedGround request -> do
        scopeChargeTo GroundScopeWork
        DirectionalEntry owner left right forward backward preparation <-
            State.gets (Seq.lookup index . ownedDirectionalEntries . searchGroundOwner)
                >>= maybe (scopeIntegrity "a directional query lost its equality entry") pure
        _ <- scopeAncestorDistance GroundScopeWork (ScopeId (focusedContextId owner)) (ScopeId (focusedContextId request))
        let context = focusedContext owner
            typing = KernelProof.proofContextGlobalTyping context
            store status = State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                {ownedDirectionalEntries = Seq.update index
                    (DirectionalEntry owner left right forward backward status)
                    (ownedDirectionalEntries (searchGroundOwner state))}})
            prepared views eligibility = pure (Just (eligibility, views))
            prepare term = runDirectionalPreparation (\budget -> Refutation.prepareGroundSyntax budget typing context term)
            assemble written leftView rightView = runDirectionalPreparation (\budget ->
                Refutation.assembleGroundImplication budget typing context written leftView rightView)
        -- Reserve the state update before an operation can exhaust its account.
        scopeChargeTo GroundScopeWork
        outcome <- lift (Except.runExceptT case preparation of
            DirectionsUnprepared -> do
                view <- prepare left
                store (DirectionLeftPrepared view)
                pure Nothing
            DirectionLeftPrepared leftView -> do
                rightView <- prepare right
                store (DirectionOperandsPrepared leftView rightView)
                pure Nothing
            DirectionOperandsPrepared leftView rightView -> do
                view <- assemble forward leftView rightView
                store (DirectionForwardPrepared leftView rightView view)
                pure Nothing
            DirectionForwardPrepared leftView rightView forwardView -> do
                backwardView <- assemble backward rightView leftView
                store (DirectionsPrepared [forwardView, backwardView] Nothing)
                pure Nothing
            DirectionsPrepared views (Just eligibility) -> prepared views eligibility
            DirectionsPrepared views Nothing -> do
                parentIndex <- case focusedEligibility owner of
                    SeedEligible (GroundFamilyId position) -> pure position
                    _ -> scopeIntegrity "a directional entry lost its seed permission"
                family <- State.gets (Seq.lookup parentIndex . ownedGroundFamilies . searchGroundOwner)
                    >>= maybe (scopeIntegrity "directional setup lost its original family") pure
                compatible <- case familyDomainQuery family of
                    Nothing -> pure False
                    Just queryIndex -> do
                        OwnedGroundQuery _ _ _ domain _ _ _ <- lookupGroundQuery (GroundQuery queryIndex)
                        maybe (pure False) (\frozen -> runDirectionalPreparation (\budget ->
                            Refutation.groundSyntaxFits budget typing context frozen views)) domain
                eligibility <- if compatible then pure (focusedEligibility owner)
                    else Except.ExceptT (selectGoalFamilyWith GroundScopeWork owner (SelectedDirections forward backward))
                store (DirectionsPrepared views (Just eligibility))
                prepared views eligibility
            DirectionsFailed _ failure -> Except.throwE failure)
        case outcome of
            Left failure -> do
                let prefix = case preparation of
                        DirectionsUnprepared -> []
                        DirectionLeftPrepared leftView -> [leftView]
                        DirectionOperandsPrepared leftView rightView -> [leftView, rightView]
                        DirectionForwardPrepared leftView rightView view -> [leftView, rightView, view]
                        DirectionsPrepared views _ -> views
                        DirectionsFailed views _ -> views
                store (DirectionsFailed prefix failure)
                Except.throwE failure
            Right Nothing -> pure Nothing
            Right (Just (base, views)) -> do
                -- Selection failure belongs to this descendant, not the paid
                -- common preparation retained for its siblings.
                eligibility <- composeDirectionalSelection owner request base
                pure (Just (request {focusedEligibility = eligibility}, views))
    _ -> pure (Just (request, []))

-- The entry's common pair is a base. Retain the requesting descendant's
-- authorized suffix above it through the existing exact variant registry.
-- This changes execution selection only; the focused obligation and the
-- original request's selected-fact authority remain untouched.
composeDirectionalSelection
    :: Eq global => FocusedRequest global -> FocusedRequest global -> GroundEligibility
    -> Scoped request global GroundEligibility
composeDirectionalSelection owner request base
    | focusedEligibility owner == focusedEligibility request = pure base
    | otherwise = do
        original <- family (focusedEligibility owner)
        selected <- family (focusedEligibility request)
        _ <- scopeAncestorDistance GroundScopeWork (ScopeId (familyScope selected))
            (ScopeId (focusedContextId request))
        sameAnchor <- runScopeCore GroundScopeWork absurd (\work ->
            countedScopedCoreIdentity work (familyAnchor original) (familyAnchor selected))
        unless sameAnchor (scopeIntegrity "directional selection changed its family anchor")
        suffix <- strip (toList (familyViewLineage original)) (toList (familyViewLineage selected))
        foldM (\eligibility selection -> Except.ExceptT
            (selectGoalFamilyWith GroundScopeWork request {focusedEligibility = eligibility} selection)) base suffix
  where
    family (SeedEligible (GroundFamilyId index)) = do
        scopeChargeTo GroundScopeWork
        State.gets (Seq.lookup index . ownedGroundFamilies . searchGroundOwner)
            >>= maybe (scopeIntegrity "directional selection lost its seed family") pure
    family _ = scopeIntegrity "read-only directional request attempted a selection"
    strip [] suffix = pure suffix
    strip (prior : rest) (selected : following) =
        sameGroundSelection GroundScopeWork prior selected >>= \matches ->
            if matches then strip rest following else scopeIntegrity "directional selection changed its lineage"
    strip _ [] = scopeIntegrity "directional selection shortened its lineage"

startFocusedGround
    :: Eq global
    => FocusedRequest global
    -> Scoped request global (GroundStart request global)
startFocusedGround original = directionalGroundRequest original >>= \case
    Nothing -> pure GroundStartPending
    Just (request, views) -> startFocusedGroundWithViews request views

-- Only the actual operand under a directional assumption gets this local
-- order: direct evidence, native ground execution, then ordinary search at
-- the ground frontier. Descendant goal views keep their normal execution.
-- This selects scheduling, not permissions or a new focused identity.
isDirectionalBody :: Eq global => FocusedRequest global -> Scoped request global Bool
isDirectionalBody request = case focusedDirectionalEntry request of
    Nothing -> pure False
    Just (DirectionalEntryId index) -> do
        scopeChargeTo GroundScopeWork
        entry <- State.gets (Seq.lookup index . ownedDirectionalEntries . searchGroundOwner)
            >>= maybe (scopeIntegrity "directional body lost its entry") pure
        case entry of
            DirectionalEntry owner left right _ _ _
                | focusedContextId request /= focusedContextId owner -> do
                    matched <- exact left
                    if matched then pure True else exact right
                | otherwise -> pure False
  where
    exact operand = runScopeCore GroundScopeWork absurd (\work ->
        countedScopedCoreIdentity work (focusedTarget request) operand)

startFocusedGroundWithViews
    :: Eq global => FocusedRequest global -> [Refutation.PreparedSyntax global]
    -> Scoped request global (GroundStart request global)
startFocusedGroundWithViews request views
    | limited && quantified (scopedCoreTerm (focusedTarget request)) = pure GroundStartUnavailable
    | otherwise = case focusedEligibility request of
        FocusedOnly -> scopeIntegrity "a focused-only premise requested a fresh ground domain"
        SeedEligible family -> startFamily family
        ExistingFamily _use family -> startFamily family
  where
    limited = case focusedEligibility request of
        ExistingFamily TheoremPremise _family -> True
        _ -> False
    quantified CForall{} = True
    quantified CExists{} = True
    quantified _ = False
    startFamily (GroundFamilyId familyIndex) = do
        scopeChargeTo GroundScopeWork
        families <- State.gets (ownedGroundFamilies . searchGroundOwner)
        family <- maybe (scopeIntegrity "a ground request lost its family") pure
            (Seq.lookup familyIndex families)
        let key = (focusedContextId request, focusedSourcePolicy request)
            remember firstQuery query@(GroundQuery index) = do
                let updated = family
                        { familyDomainQuery = if firstQuery then Just index else familyDomainQuery family
                        , familyQueries = Map.insertWith (<>) key [(focusedTarget request, index)] (familyQueries family) }
                State.modify' (\state -> state
                    { searchGroundOwner = (searchGroundOwner state)
                        { ownedGroundFamilies = Seq.update familyIndex updated
                            (ownedGroundFamilies (searchGroundOwner state)) } })
                pure (GroundStarted (FocusedGroundQuery query (focusedEligibility request) views))
            create domain = do
                permitted <- if limited then claimPremiseQuery else pure True
                if permitted then createAdmitted domain else pure GroundStartUnavailable
            createAdmitted domain = do
                _ <- scopeAncestorDistance GroundScopeWork
                    (ScopeId (familyScope family)) (ScopeId (focusedContextId request))
                let SearchEnvironment typing imports _hypotheses _views = focusedEnvironment request
                    context = focusedContext request
                    inputs = contextGroundFacts context imports
                    anchorContext = familyContext family
                    ambient = KernelProof.proofContextTypes anchorContext
                    seeds = familyAnchor family :|
                        (KernelProof.proofContextHypotheses anchorContext <>
                            [embedClosedCore ambient statement | ObviousImport _index statement <- familyImports family]
                            <> concatMap selectionRoots (toList (familyViewLineage family)))
                limits <- lift currentGroundLimits
                session <- case domain of
                    Just frozen -> pure (Refutation.startRefutationInDomainWithViews limits typing context views frozen inputs (focusedTarget request))
                    Nothing -> do
                        sameAnchor <- if null views && Seq.null (familyViewLineage family) && focusedContextId request == familyScope family
                            then runScopeCore GroundScopeWork absurd (\work ->
                                countedScopedCoreIdentity work (familyAnchor family) (focusedTarget request))
                            else pure False
                        -- The original root already has exactly the family seed
                        -- order. Reuse that preparation instead of walking every
                        -- input a second time through frozen proposition admission.
                        pure (if sameAnchor
                            then Refutation.startRefutation limits typing context inputs (focusedTarget request)
                            else Refutation.startRefutationFromSeedWithViews limits typing context views seeds inputs (focusedTarget request))
                canonical <- focusedGroundSources request
                tracked <- case canonical of
                    Nothing -> pure session
                    Just (OwnedGroundSupport sources _ordinary) ->
                        either (Except.throwE . mapRefutationFailure) pure
                            (Refutation.trackRefutationCanonicalSources (map fst sources) session)
                query <- admitGroundQuery (OwnedGroundQuery (focusedContextId request) typing
                    (familyScope family) domain (OwnedGroundRunning tracked) canonical emptyGroundInputCursor)
                remember (isNothing domain) query
        existing <- findQuery (Map.findWithDefault [] key (familyQueries family))
        case existing of
            Just query -> pure (GroundStarted (FocusedGroundQuery query (focusedEligibility request) views))
            Nothing -> case familyDomainQuery family of
                Nothing
                    | limited -> pure GroundStartUnavailable
                    | otherwise -> create Nothing
                Just index -> do
                    OwnedGroundQuery _scope _typing _domainScope domain _status _support _inputCursor <- lookupGroundQuery (GroundQuery index)
                    case domain of
                        Just frozen -> create (Just frozen)
                        Nothing -> scopeAdvanceGround (GroundQuery index) >>= \case
                            GroundQueryPending -> pure GroundStartPending
                            GroundQueryBlocked _statistics failure -> Except.throwE (mapRefutationFailure failure)
                            GroundQueryFinished _statistics (Left failure) -> Except.throwE (mapRefutationFailure failure)
                            GroundQueryFinished _statistics (Right _proof) ->
                                scopeIntegrity "a ground query completed without publishing its frozen domain"
    findQuery [] = pure Nothing
    findQuery ((target, index) : rest) = do
        same <- runScopeCore GroundScopeWork absurd (\work ->
            countedScopedCoreIdentity work target (focusedTarget request))
        if same then pure (Just (GroundQuery index)) else findQuery rest

-- The exact query registry is checked first. Once a new start is admitted,
-- subsequent preparation failures and support upgrades retain that same row.
claimPremiseQuery :: Scoped request global Bool
claimPremiseQuery = do
    scopeChargeTo GroundScopeWork
    policy <- State.gets (policyPremiseQueries . searchPolicy)
    starts <- State.gets searchPremiseQueriesStarted
    case policy of
        PremiseQueriesDisabled -> scopeIntegrity "a disabled theorem premise requested a ground query"
        ExistingPremiseQueries limit
            | starts < limit -> do
                State.modify' (\state -> state {searchPremiseQueriesStarted = starts + 1})
                pure True
            | otherwise -> do
                State.modify' (\state -> state {searchPremiseQueriesDeferred = True})
                pure False

contextGroundFacts
    :: KernelProof.ProofContext global -> [ObviousImport global]
    -> [Refutation.RefutationFact global]
contextGroundFacts context imports =
    zipWith Refutation.RefutationHypothesis [0 ..] (KernelProof.proofContextHypotheses context)
    <> [Refutation.RefutationImport index statement | ObviousImport index statement <- imports]

-- One cursor belongs to the original exact query through every fact-domain
-- epoch. Classification runs before branch work, never by saturating a base
-- query to discover that selected syntax is missing. Compatible input is kept
-- for that query's existing admission boundary. Only selected views from this
-- authorized family can justify a new domain.
advanceFocusedGround
    :: Eq global => FocusedRequest global -> FocusedGroundQuery request global
    -> Scoped request global (GroundQueryProgress (OwnedGroundCertificate global))
advanceFocusedGround request (FocusedGroundQuery query _ _) | not (canSeedFocusedGround request) =
    advanceGroundCertificate (focusedRequirement request) query
advanceFocusedGround request (FocusedGroundQuery (GroundQuery ownerIndex) seedEligibility views) = do
    facts <- State.gets (ownedGroundFacts . searchGroundOwner)
    previous <- State.gets (Map.lookup ownerIndex . ownedGroundActivations . searchGroundOwner)
    let initial = GroundActivation ownerIndex (Seq.singleton ownerIndex) Seq.empty (Nothing, Nothing)
            0 (Seq.length facts) Seq.empty False False Nothing
        current = fromMaybe initial previous
        query = GroundQuery (activationQuery current)
    for_ (activationFailure current) Except.throwE
    OwnedGroundQuery scope typing domainScope frozen status support cursor <- lookupGroundQuery query
    let ordinary = support >>= \(OwnedGroundSupport _sources proof) -> proof
        settled = case status of
            OwnedGroundFinished{} -> True
            OwnedGroundCertificationFailed{} -> True
            _ -> focusedRequirement request == AnyObviousProof && isJust ordinary
        -- A snapshot is a finite prefix. Later publication belongs to another
        -- opportunity; it does not grow an activation already being prepared.
        active = if activationCursor current == activationSnapshot current
                        && not (activationOutside current)
                        && activationSnapshot current < Seq.length facts
            then current {activationSnapshot = Seq.length facts
                , activationRunning = activationRunning current <> activationParked current
                , activationParked = Seq.empty} else current
        certificate = (case focusedRequirement request of
            AnyObviousProof -> fst
            MustUseCanonicalDefinition -> snd) (activationCertificates active)
    case certificate of
        Just proof -> pure (GroundQueryFinished (fst (groundQueryObservation
            (OwnedGroundQuery scope typing domainScope frozen status support cursor))) (Right proof))
        Nothing | (settled && isNothing previous)
            || (activationCursor active == Seq.length facts && not (activationOutside active))
            -> if isNothing previous then advanceGroundCertificate (focusedRequirement request) query else advanceQueries active
        Nothing -> do
            result <- lift (Except.runExceptT (prepare active query scope typing domainScope frozen status support cursor facts))
            case result of
                Right progress -> pure progress
                Left failure -> do
                    saved <- State.gets (Map.findWithDefault active ownerIndex . ownedGroundActivations . searchGroundOwner)
                    store saved {activationFailure = Just failure}
                    Except.throwE failure
  where
    store active = State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
        {ownedGroundActivations = Map.insert ownerIndex active (ownedGroundActivations (searchGroundOwner state))}})
    prepare active query scope typing domainScope frozen status support cursor facts = case frozen of
        Nothing -> store active >> advanceQueries active
        Just domain
            | activationCursor active < activationSnapshot active -> do
                scopeChargeTo GroundScopeWork
                unless (scope == focusedContextId request)
                    (scopeIntegrity "a fact activation changed its nominal query owner")
                _ <- scopeAncestorDistance GroundScopeWork (ScopeId domainScope) (ScopeId scope)
                let index = activationCursor active
                    next = active {activationCursor = index + 1}
                PublishedGroundFact producer family _environment _proof _certificate <- maybe
                    (scopeIntegrity "a fact activation lost its selected snapshot") pure (Seq.lookup index facts)
                visible <- groundFactVisibleFrom producer scope
                if not visible
                    then store next >> pure GroundQueryPending
                    else do
                        OwnedGroundCertificate built uses _source <- certifyPublishedGroundFact index
                        aligned <- scopeAtWith GroundScopeWork (ScopeId scope) (Evidence (ScopeId producer) built uses)
                        before <- lift currentGroundLimits
                        let (remaining, result) = Refutation.prepareFrozenFact before typing (focusedContext request)
                                domain (evidenceProof aligned) (evidenceUses aligned)
                        committed <- lift (commitGroundLimits before remaining)
                        unless committed (scopeIntegrity "a selected input replenished its preparation allowance")
                        (prepared, compatible) <- either (Except.throwE . mapRefutationFailure) pure result
                        let authorized = case family of
                                Just owner -> focusedEligibility request == SeedEligible owner
                                Nothing -> False
                            GroundInputCursor position pending = cursor
                            retained = GroundInputCursor position (if index < position then pending
                                else Map.insert index (if compatible then Just prepared else Nothing) pending)
                        storeGroundQuery query (OwnedGroundQuery scope typing domainScope frozen status support retained)
                        store next
                            { activationInputs = if compatible || authorized then activationInputs active Seq.|>
                                (index, if authorized then Just (KernelProof.builtProofStatement (evidenceProof aligned))
                                    else Nothing, prepared) else activationInputs active
                            , activationOutside = activationOutside active || (authorized && not compatible) }
                        pure GroundQueryPending
            | activationOutside active -> do
                -- Mark the snapshot before charged startup. A failed startup
                -- cannot return to the same selected package with fresh work.
                store active {activationOutside = False}
                scopeChargeTo GroundScopeWork
                owner <- State.gets searchGroundOwner
                if ownedGroundVariantStarts owner >= ownedGroundVariantLimit owner then do
                    State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
                        {ownedGroundVariantsDeferred = True}})
                    advanceQueries active {activationOutside = False}
                  else startVariant active
            | otherwise -> store active >> advanceQueries active
    startVariant active = do
        State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
            {ownedGroundVariantStarts = ownedGroundVariantStarts (searchGroundOwner state) + 1}})
        familyIndex <- case seedEligibility of
            SeedEligible (GroundFamilyId index) -> pure index
            ExistingFamily{} -> scopeIntegrity "a read-only premise requested a selected fact domain"
            FocusedOnly -> scopeIntegrity "a focused-only premise requested a selected fact domain"
        families <- State.gets (ownedGroundFamilies . searchGroundOwner)
        family <- maybe (scopeIntegrity "a selected fact activation lost its family") pure
            (Seq.lookup familyIndex families)
        let SearchEnvironment typing imports _hypotheses _views = focusedEnvironment request
            context = focusedContext request
            ambient = KernelProof.proofContextTypes (familyContext family)
            selected = toList (activationInputs active)
            seeds = familyAnchor family :|
                (KernelProof.proofContextHypotheses (familyContext family)
                <> [embedClosedCore ambient statement | ObviousImport _index statement <- familyImports family]
                <> concatMap selectionRoots (toList (familyViewLineage family)) <> [statement | (_index, Just statement, _prepared) <- selected])
            inputs = contextGroundFacts context imports
                <> [Refutation.RefutationPrepared prepared | (_index, _statement, prepared) <- selected]
            cursor = GroundInputCursor 0 (Map.fromList [(index, Nothing) | (index, _statement, _prepared) <- selected])
        limits <- lift currentGroundLimits
        OwnedGroundQuery _scope _typing _domainScope _domain _status priorSupport _cursor <-
            lookupGroundQuery (GroundQuery (activationQuery active))
        registered <- focusedGroundSources request
        let canonical = fmap (\(OwnedGroundSupport sources _ordinary) ->
                OwnedGroundSupport sources (fst (activationCertificates active) <|>
                    (priorSupport >>= \(OwnedGroundSupport _prior ordinary) -> ordinary))) registered
        let session = Refutation.startRefutationFromSeedWithViews limits typing context views seeds inputs (focusedTarget request)
        tracked <- case canonical of
            Nothing -> pure session
            Just (OwnedGroundSupport sources _ordinary) -> either (Except.throwE . mapRefutationFailure) pure
                (Refutation.trackRefutationCanonicalSources (map fst sources) session)
        GroundQuery index <- admitGroundQuery (OwnedGroundQuery (focusedContextId request) typing
            (focusedContextId request) Nothing (OwnedGroundRunning tracked) canonical cursor)
        store active {activationQuery = index, activationRunning = activationRunning active Seq.|> index
            , activationOutside = False, activationOpportunity = False}
        pure GroundQueryPending

    -- A new domain is an alternative, not a reason to abandon a viable base
    -- query. Each retained cursor receives a sequential service transition;
    -- blocked frontiers park until publication. All use the same real allowance.
    advanceQueries active = case Seq.viewl (activationRunning active) of
        Seq.EmptyL -> parkedQuery active
        index Seq.:< remaining -> do
            result <- lift (Except.runExceptT
                (advanceGroundCertificate (focusedRequirement request) (GroundQuery index)))
            case result of
                Left failure | isFocusedInfrastructureFailure failure -> Except.throwE failure
                _ -> pure ()
            let (running, parked, certificate) = case result of
                    Right GroundQueryPending -> (remaining Seq.|> index, activationParked active, Nothing)
                    Right (GroundQueryBlocked _ _) -> (remaining, activationParked active Seq.|> index, Nothing)
                    Right (GroundQueryFinished _ (Right proof)) ->
                        (remaining Seq.|> index, activationParked active, Just proof)
                    _ -> (remaining, activationParked active, Nothing)
                retained = active {activationRunning = running, activationParked = parked
                    , activationCertificates =
                        (fst (activationCertificates active) <|> certificate,
                         snd (activationCertificates active) <|> case certificate of
                            Just proof@(OwnedGroundCertificate _ _ (Just _)) -> Just proof
                            _ -> Nothing)}
            store retained
            case result of
                Right progress@GroundQueryFinished{} | isJust certificate -> pure progress
                _ | not (Seq.null running) -> pure GroundQueryPending
                _ | not (Seq.null parked) -> parkedQuery retained
                Right progress -> pure progress
                Left failure -> Except.throwE failure

    -- Failure of a new alternative does not destroy an older open or support
    -- frontier. New compatible input may still discharge it without the failed
    -- operation or another domain admission.
    parkedQuery active = case Seq.viewl (activationParked active) of
        Seq.EmptyL -> advanceGroundCertificate (focusedRequirement request) (GroundQuery (activationQuery active))
        index Seq.:< remaining -> do
            result <- advanceGroundCertificate (focusedRequirement request) (GroundQuery index)
            case result of
                GroundQueryPending -> store active
                    {activationRunning = Seq.singleton index, activationParked = remaining}
                _ -> pure ()
            pure result

-- Reading a handle does not advance preparation. The scheduler decides when
-- the owning query gets another turn; a frozen domain remains available after
-- that query closes and releases its search state.
scopeGroundDomain
    :: GroundQuery request global -> Scoped request global (Maybe (GroundDomain request global))
scopeGroundDomain query@(GroundQuery index) = do
    OwnedGroundQuery _scope _typing _domainScope domain _status _support _inputCursor <- lookupGroundQuery query
    pure (GroundDomain index <$ domain)

scopeStartGroundInDomain
    :: GroundDomain request global
    -> ScopeId request
    -> [Evidence request global]
    -> ScopedCheckedCore global
    -> Scoped request global (GroundQuery request global)
scopeStartGroundInDomain (GroundDomain domainIndex) scope inputs target = do
    OwnedGroundQuery _queryScope globalType domainScope frozen _status _support _inputCursor <- lookupGroundQuery (GroundQuery domainIndex)
    domain <- maybe (scopeIntegrity "an Obvious domain was used before freezing") pure frozen
    -- Equal type lists do not establish lexical ownership. Only this exact
    -- family scope and its proof-assumption descendants can reuse its syntax.
    _distance <- scopeAncestorDistance GroundScopeWork (ScopeId domainScope) scope
    context <- scopeContextWith GroundScopeWork scope
    aligned <- traverse (scopeAtWith GroundScopeWork scope) inputs
    limits <- lift currentGroundLimits
    admitGroundQuery (OwnedGroundQuery (ownedContextId scope) globalType domainScope frozen
        (OwnedGroundRunning (Refutation.startCertifiedRefutationInDomain limits globalType context domain
            [(evidenceProof evidence, evidenceUses evidence) | evidence <- aligned] target)) Nothing emptyGroundInputCursor)

scopeAdvanceGround
    :: Eq global
    => GroundQuery request global -> Scoped request global (GroundQueryProgress (Evidence request global))
scopeAdvanceGround query = do
    OwnedGroundQuery contextId _typing _domainScope _domain _status _support _inputCursor <- lookupGroundQuery query
    fmap (\(OwnedGroundCertificate proof uses _source) -> Evidence (ScopeId contextId) proof uses)
        <$> advanceGroundCertificate AnyObviousProof query

advanceGroundCertificate
    :: Eq global
    => ProofRequirement -> GroundQuery request global
    -> Scoped request global (GroundQueryProgress (OwnedGroundCertificate global))
advanceGroundCertificate requirement query = do
    OwnedGroundQuery contextId typing domainScope domain status support inputCursor <- lookupGroundQuery query
    -- A saved ordinary proof survives unsuccessful support search, but cannot
    -- mask infrastructure failure observed by this same query owner.
    case status of
        OwnedGroundCertificationFailed _statistics failure -> Except.throwE failure
        OwnedGroundFinished _statistics (Left failure)
            | isFocusedInfrastructureFailure (mapRefutationFailure failure) ->
                Except.throwE (mapRefutationFailure failure)
        _ -> pure ()
    let scope = ScopeId contextId
        store frozen following tracking = storeGroundQuery query
            (OwnedGroundQuery contextId typing domainScope frozen following tracking inputCursor)
        retain session = domain <|> Refutation.refutationSessionDomain session
        ordinary = support >>= \(OwnedGroundSupport _sources candidate) -> candidate
        remember certificate = fmap (\(OwnedGroundSupport sources prior) ->
            OwnedGroundSupport sources (prior <|> Just certificate)) support
        finish statistics result = pure (GroundQueryFinished statistics result)
        certify statistics candidate = do
            certified <- lift (Except.runExceptT do
                evidence <- recordConstructionWith GroundScopeWork scope (Refutation.refutationCandidateProof candidate)
                source <- case Refutation.refutationCandidateCanonicalSource candidate of
                    Nothing -> pure Nothing
                    Just selected -> do
                        scopeChargeTo GroundScopeWork
                        let registry = maybe [] (\(OwnedGroundSupport sources _ordinary) -> sources) support
                        source <- findSource selected registry
                        let uses = evidenceUses evidence
                            consumed = case selected of
                                Refutation.RefutationCanonicalHypothesis index ->
                                    Set.member (hypothesisIx index) (kernelSourceExternalHypothesisUses uses)
                                Refutation.RefutationCanonicalImport index -> Set.member index (kernelSourceImportUses uses)
                        unless consumed (scopeIntegrity "a ground certificate did not consume its canonical source")
                        pure (Just source)
                pure (OwnedGroundCertificate (evidenceProof evidence) (evidenceUses evidence) source))
            case certified of
                Left failure -> do
                    store domain (OwnedGroundCertificationFailed statistics failure) support
                    Except.throwE failure
                Right certificate -> pure certificate
        findSource _selected [] = scopeIntegrity "a ground certificate named an unregistered canonical source"
        findSource selected ((registered, source) : rest) = do
            scopeChargeTo GroundScopeWork
            admitted <- case source of
                CanonicalImportedSource ordinal _index -> State.gets (Set.member ordinal . searchRegisteredDefinitionImports)
                CanonicalHypothesisSource{} -> pure True
            if selected == registered && admitted then pure source else findSource selected rest
        currentStatistics statistics = do
            remaining <- lift currentGroundLimits
            pure statistics
                { Refutation.refutationRemainingWork = Refutation.refutationWorkLimit remaining
                , Refutation.refutationRemainingConversionPool = Refutation.refutationConversionPool remaining }
        statusStatistics = case status of
            OwnedGroundRunning session -> Refutation.refutationSessionStatistics session
            OwnedGroundBlocked statistics _failure _session -> statistics
            OwnedGroundFinished statistics _result -> statistics
            OwnedGroundCertificationFailed statistics _failure -> statistics
    case (requirement, ordinary) of
        (AnyObviousProof, Just certificate) -> do
            statistics <- currentStatistics statusStatistics
            finish statistics (Right certificate)
        _ -> case status of
            OwnedGroundBlocked statistics failure _session -> resumePublishedGroundFact query >>= \resumed ->
                pure (if resumed then GroundQueryPending else GroundQueryBlocked statistics failure)
            OwnedGroundFinished statistics result -> finish statistics result
            OwnedGroundCertificationFailed _statistics failure -> Except.throwE failure
            OwnedGroundRunning session -> lift (advanceOwnedGround session) >>= \case
                Refutation.RefutationPending next -> case (ordinary, Refutation.refutationSessionAnyCandidate next) of
                    (Nothing, Just candidate) -> do
                        certificate <- certify (Refutation.refutationSessionStatistics next) candidate
                        statistics <- currentStatistics (Refutation.refutationSessionStatistics next)
                        store (retain next) (OwnedGroundRunning next) (remember certificate)
                        finish statistics (Right certificate)
                    _ -> do
                        store (retain next) (OwnedGroundRunning next) support
                        pure GroundQueryPending
                Refutation.RefutationBlocked statistics failure current -> do
                    store (retain current) (OwnedGroundBlocked statistics failure current) support
                    resumed <- resumePublishedGroundFact query
                    pure (if resumed then GroundQueryPending else GroundQueryBlocked statistics failure)
                Refutation.RefutationFinished statistics (Left failure) -> do
                    store domain (OwnedGroundFinished statistics (Left failure)) support
                    finish statistics (Left failure)
                Refutation.RefutationFinished statistics (Right candidate) -> do
                    certificate@(OwnedGroundCertificate _built _uses source) <- certify statistics candidate
                    published <- currentStatistics statistics
                    let final = if isJust support && isNothing source
                            then Left Refutation.RefutationCanonicalSupportMissing else Right certificate
                    store domain (OwnedGroundFinished published final) (remember certificate)
                    finish published (Right certificate)

-- The registry names possible sources, not asserted facts. Ordinary imported
-- roots validate their canonical association now; a later selected view must
-- register its exact association before it can publish certified evidence.
focusedGroundSources
    :: Eq global => FocusedRequest global -> Scoped request global (Maybe (OwnedGroundSupport global))
focusedGroundSources request = do
    tracking <- State.gets searchCanonicalRequest
    if not tracking then pure Nothing else do
        count <- foldM (\n _ -> scopeChargeTo GroundScopeWork >> pure (n + 1))
            0 (KernelProof.proofContextHypotheses (focusedContext request))
        let environment@(SearchEnvironment _typing imports _initial (DefinitionViewCatalogue definitions _ locals _)) =
                focusedEnvironment request
        local <- forM locals $ \(_ordinal, index, _kind) -> do
            scopeChargeTo GroundScopeWork
            current <- either Except.throwE pure (currentLocalDefinitionHypothesisIx environment count index)
            pure (Refutation.RefutationCanonicalHypothesis (hypothesisIxValue current), CanonicalHypothesisSource index)
        forM_ imports $ \(ObviousImport index _statement) -> do
            scopeChargeTo GroundScopeWork
            candidate <- State.gets (Map.lookup index . searchCanonicalImportCandidates)
            forM_ candidate $ \(ordinal, source) ->
                Except.ExceptT (registerDefinitionImportWith GroundScopeWork ordinal source)
        imported <- fmap catMaybes $ forM (zip [0 ..] definitions) $ \(ordinal, definition) -> do
            scopeChargeTo GroundScopeWork
            pure case definition of
                ObviousImportedDefinitionView _subject _kind (ObviousImport index _statement) ->
                    Just (Refutation.RefutationCanonicalImport index, CanonicalImportedSource ordinal index)
                ObviousLocalDefinitionView{} -> Nothing
        pure (Just (OwnedGroundSupport (local <> imported) Nothing))

-- Only completed selected fact views cross this publication boundary. The first
-- supported proof of the same statement in the same scope supplies its slot;
-- repeated discovery cannot keep extending the input round.
publishGroundFact
    :: Eq global => FocusedRequest global -> ObviousProof global -> Scoped request global ()
publishGroundFact request proof = do
    family <- case focusedEligibility request of
        SeedEligible owner -> pure (Just owner)
        ExistingFamily{} -> pure Nothing
        FocusedOnly -> scopeIntegrity "a focused-only source requested ground publication"
    facts <- State.gets (ownedGroundFacts . searchGroundOwner)
    duplicate <- findFact family (Seq.viewl facts)
    unless duplicate do
        scopeChargeTo GroundScopeWork
        when (Seq.length facts == maxBound) (scopeIntegrity "published ground fact identifier overflow")
        let selected = PublishedGroundFact (focusedContextId request) family
                (focusedEnvironment request) proof Nothing
        State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
            {ownedGroundFacts = facts Seq.|> selected}})
  where
    findFact _family Seq.EmptyL = pure False
    findFact family (PublishedGroundFact context origin _environment previous _certificate Seq.:< rest) = do
        scopeChargeTo GroundScopeWork
        same <- if context /= focusedContextId request || family /= origin then pure False else
            runScopeCore GroundScopeWork absurd (\work -> countedScopedCoreIdentity work
                (obviousProofStatement previous) (obviousProofStatement proof))
        if same then pure True else findFact family (Seq.viewl rest)

certifyPublishedGroundFact :: Int -> Scoped request global (OwnedGroundCertificate global)
certifyPublishedGroundFact factIndex = do
    facts <- State.gets (ownedGroundFacts . searchGroundOwner)
    PublishedGroundFact producer family environment proof prior <- maybe
        (scopeIntegrity "a selected ground input lost its producer") pure (Seq.lookup factIndex facts)
    result <- case prior of
      Just certificate -> pure certificate
      Nothing -> lift (Except.runExceptT do
        source <- maybe (scopeIntegrity "a selected fact view lost its canonical source") pure
            (candidateCanonicalSource (obviousProofDependencies proof))
        evidence <- recordConstructionWith GroundScopeWork (ScopeId producer) (obviousBuiltProof proof)
        let uses = evidenceUses evidence
        consumed <- case source of
            CanonicalImportedSource ordinal index -> do
                scopeChargeTo GroundScopeWork
                registered <- State.gets (Set.member ordinal . searchRegisteredDefinitionImports)
                pure (registered && Set.member index (kernelSourceImportUses uses))
            CanonicalHypothesisSource index -> do
                context <- scopeContextWith GroundScopeWork (ScopeId producer)
                count <- foldM (\n _ -> scopeChargeTo GroundScopeWork >> pure (n + 1))
                    0 (KernelProof.proofContextHypotheses context)
                current <- either Except.throwE pure
                    (currentLocalDefinitionHypothesisIx environment count index)
                pure (Set.member current (kernelSourceExternalHypothesisUses uses))
        unless consumed (scopeIntegrity "a selected fact view did not consume its canonical source")
        pure (OwnedGroundCertificate (evidenceProof evidence) uses (Just source)))
    when (isNothing prior) (State.modify' (\state -> state {searchGroundOwner = (searchGroundOwner state)
        {ownedGroundFacts = Seq.update factIndex
            (PublishedGroundFact producer family environment proof (Just result))
            (ownedGroundFacts (searchGroundOwner state))}}))
    either Except.throwE pure result

-- Offer one new source at a retained frontier. The refuter performs its existing
-- frozen-domain admission and propagates accepted input through the same branch
-- tree. An unsuccessful input is still charged and its cursor is not rewound.
resumePublishedGroundFact :: GroundQuery request global -> Scoped request global Bool
resumePublishedGroundFact query = do
    OwnedGroundQuery context typing domainScope domain status support (GroundInputCursor cursor prepared) <- lookupGroundQuery query
    case status of
        OwnedGroundBlocked _statistics _failure session -> do
            facts <- State.gets (ownedGroundFacts . searchGroundOwner)
            case Seq.lookup cursor facts of
                Nothing -> pure False
                Just (PublishedGroundFact producer _family _environment _proof _certificate) -> do
                    scopeChargeTo GroundScopeWork
                    following <- case Map.lookup cursor prepared of
                        Just Nothing -> pure status
                        Just (Just input) -> OwnedGroundRunning <$> either (Except.throwE . mapRefutationFailure) pure
                            (Refutation.resumeRefutationWithPreparedInput input session)
                        Nothing -> do
                            permitted <- groundFactVisibleFrom producer context
                            if not permitted then pure status else do
                                OwnedGroundCertificate built uses _source <- certifyPublishedGroundFact cursor
                                aligned <- scopeAtWith GroundScopeWork (ScopeId context) (Evidence (ScopeId producer) built uses)
                                resumed <- either (Except.throwE . mapRefutationFailure) pure
                                    (Refutation.resumeRefutationWithInput (evidenceProof aligned) (evidenceUses aligned) session)
                                pure (OwnedGroundRunning resumed)
                    storeGroundQuery query (OwnedGroundQuery context typing domainScope domain following support
                        (GroundInputCursor (cursor + 1) (Map.delete cursor prepared)))
                    pure True
        _ -> scopeIntegrity "published input lost its retained ground frontier"

groundFactVisibleFrom :: FocusedContextId -> FocusedContextId -> Scoped request global Bool
groundFactVisibleFrom producer consumer
    | producer == consumer = pure True
    | otherwise = do
        FocusedContext lineage _context <- lookupOwnedScopeWith GroundScopeWork (ScopeId consumer)
        case lineage of
            FocusedAssumptionScope parent _premise -> groundFactVisibleFrom producer parent
            FocusedBinderScope{} -> pure False
            FocusedRootScope -> pure False


scopeResumeGround
    :: GroundQuery request global -> Evidence request global -> Scoped request global ()
scopeResumeGround query evidence = do
    OwnedGroundQuery contextId typing domainScope domain status support inputCursor <- lookupGroundQuery query
    aligned <- scopeAtWith GroundScopeWork (ScopeId contextId) evidence
    case status of
        OwnedGroundBlocked _statistics _failure current -> do
            resumed <- either (Except.throwE . mapRefutationFailure) pure
                (Refutation.resumeRefutationWithInput (evidenceProof aligned) (evidenceUses aligned) current)
            storeGroundQuery query (OwnedGroundQuery contextId typing domainScope domain (OwnedGroundRunning resumed) support inputCursor)
        _ -> scopeIntegrity "certified evidence can resume only the current open Obvious query"

-- The scope owner supplies the real context and aligned source proofs, then
-- certifies the result in that same context. No caller can attach a scope to
-- an arbitrary BuiltProof, whose hypothesis environment is otherwise opaque.
scopeRefute
    :: Ord global
    => GlobalTyping global
    -> ScopeId request
    -> [ScopedCheckedCore global]
    -> [Evidence request global]
    -> ScopedCheckedCore global
    -> Scoped request global
        (Refutation.RefutationStatistics, Either Refutation.RefutationFailure (Evidence request global))
scopeRefute globalType scope seedSyntax inputs target = do
    query <- scopeStartGround globalType scope seedSyntax inputs target
    drain query
  where
    drain query = scopeAdvanceGround query >>= \case
        GroundQueryPending -> drain query
        GroundQueryBlocked statistics failure -> pure (statistics, Left failure)
        GroundQueryFinished statistics result -> pure (statistics, result)
