{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Deterministic bounded propositional refutation.  Search retains shallow
-- request IDs and compact proof reasons; only the selected closed tree is
-- materialized through counted kernel proof combinators.
module Felix.Checking.Obvious.Refutation
    ( RefutationLimits(..)
    , UniversalPolicy(..)
    , permitsUniversalRemainder
    , RefutationFact(..)
    , RefutationFailure(..)
    , RefutationCandidate
    , refutationCandidateProof
    , refutationCandidateImports
    , RefutationCanonicalSource(..)
    , trackRefutationCanonicalSources
    , refutationCandidateCanonicalSource
    , RefutationStatistics(..)
    , RefutationSession
    , FrozenDomain
    , frozenDomainCatalogue
    , refutationSessionDomain
    , startCertifiedRefutationInDomain
    , resumeRefutationWithInput
    , resumeRefutationWithPreparedInput
    , RefutationProgress(..)
    , startRefutation
    , startRefutationFromSeed
    , startRefutationFromSeedWithViews
    , startRefutationInDomain
    , startRefutationInDomainWithViews
    , PreparedSyntax
    , prepareGroundSyntax
    , assembleGroundImplication
    , groundSyntaxFits
    , PreparedCertifiedFact
    , prepareFrozenFact
    , advanceRefutation
    , refutationSessionStatistics
    , refutationSessionAnyCandidate
    , runRefutation
    , startCertifiedRefutation
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Elimination qualified as Elimination
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.Semantics qualified as KernelSemantics
    (KernelSemanticsError(KernelScopedInstantiationFailed))
import Felix.Checking.Obvious.Conversion
    (ObviousConversionLimitOwner(..), ObviousConversionRunError(..), runObviousConversion)
import Felix.Checking.Obvious.Equality qualified as Equality
import Felix.Checking.Obvious.LogicalView qualified as LogicalView
import Felix.Checking.Obvious.Match qualified as Match
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template

import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Word (Word)
import Numeric.Natural (Natural)


-- Disabled does no discovery; an enabled zero allowance can still report a
-- real prevented candidate. The payload is a remainder, never a session cap.
data UniversalPolicy
    = UniversalsDisabled
    | ExistingUniversals !Word
    | HintedUniversals !Word !Word -- Remaining candidate attempts and hint turns.
    deriving stock (Show, Eq)

permitsUniversalRemainder :: UniversalPolicy -> UniversalPolicy -> Bool
permitsUniversalRemainder UniversalsDisabled UniversalsDisabled = True
permitsUniversalRemainder (ExistingUniversals before) (ExistingUniversals after) = after <= before
permitsUniversalRemainder (HintedUniversals before hintsBefore) (HintedUniversals after hintsAfter) =
    after <= before && hintsAfter <= hintsBefore
permitsUniversalRemainder _ _ = False

data RefutationLimits = RefutationLimits
    { refutationWorkLimit :: !Word
    , refutationConversionPool :: !Conversion.ConversionPool
    , refutationGroundTermLimit :: !Word
    , refutationBranchNodeLimit :: !Word
    , refutationRuleInstanceLimit :: !Word
    , refutationBooleanPropagation :: !Bool
    , refutationExtendedRules :: !Bool
    , refutationUniversals :: !UniversalPolicy
    }
    deriving stock (Eq)

data RefutationFact global
    = RefutationHypothesis !Natural !(ScopedCheckedCore global)
    | RefutationImport !ImportIx !(FrozenCheckedCore global)
    | RefutationCertified !(KernelProof.BuiltProof global) !KernelSourceUses
    | RefutationPrepared !(PreparedCertifiedFact global)

data RefutationFailure
    = RefutationSaturated
    | RefutationCanonicalSupportMissing
    | RefutationWorkExhausted
    | RefutationConversionLimitExhausted
        !ObviousConversionLimitOwner !Conversion.ConversionLimit
    | RefutationConversionFailed !Conversion.ConversionFailure
    | RefutationRequiredConversionNotConvertible
    | RefutationConversionAccountingInvariant
        !Conversion.ConversionCost !Conversion.ConversionPool
    | RefutationGroundTermsExhausted
    | RefutationBranchesExhausted
    | RefutationRuleInstancesExhausted
    | RefutationUnsupportedTermOutsideUniverse
    | RefutationUndeterminedParameter !Natural
    | RefutationIntegrityFailure !KernelProof.KernelProofBuildError
    | RefutationInternalFailure !Text
    deriving stock (Show, Eq)

data RefutationCandidate global = RefutationCandidate
    !(KernelProof.BuiltProof global)
    !(Set ImportIx)
    !(Maybe RefutationCanonicalSource)

-- The driver validates these exact source associations before enabling support.
-- They describe source use, not additional proof authority.
data RefutationCanonicalSource
    = RefutationCanonicalHypothesis !Natural
    | RefutationCanonicalImport !ImportIx
    deriving stock (Show, Eq, Ord)

refutationCandidateCanonicalSource :: RefutationCandidate global -> Maybe RefutationCanonicalSource
refutationCandidateCanonicalSource (RefutationCandidate _ _ source) = source

refutationCandidateProof
    :: RefutationCandidate global
    -> KernelProof.BuiltProof global
refutationCandidateProof (RefutationCandidate proof _imports _source) = proof

refutationCandidateImports
    :: RefutationCandidate global
    -> Set ImportIx
refutationCandidateImports (RefutationCandidate _proof imports _source) = imports

data RefutationStatistics = RefutationStatistics
    { refutationRemainingWork :: !Word
    , refutationRemainingConversionPool :: !Conversion.ConversionPool
    , refutationBranchNodes :: !Word
    , refutationTerms :: !Word -- Cumulative admissions, including discarded staging.
    , refutationSignedFormulas :: !Word
    , refutationEqualityEvents :: !Word
    , refutationRuleInstances :: !Word
    , refutationUniversalAttempts :: !Word
    , refutationUniversalHintSteps :: !Word
    , refutationUniversalsDeferred :: !Bool
    }

newtype BranchId = BranchId Int
    deriving stock (Show, Eq, Ord)

newtype ProofReasonId = ProofReasonId Int
    deriving stock (Show, Eq, Ord)

newtype RuleId = RuleId Int
    deriving stock (Show, Eq, Ord)

newtype MatcherSubstitutionId = MatcherSubstitutionId Int
    deriving stock (Show, Eq, Ord)

data Sign = SignTrue | SignFalse
    deriving stock (Show, Eq, Ord)

newtype PreparedFormula global = PreparedFormula
    (Search.CataloguedFormulaView global)

preparedFormulaValue
    :: PreparedFormula global
    -> ScopedCheckedCore global
preparedFormulaValue (PreparedFormula formulaView) =
    Template.compiledTemplateTerm
        (LogicalView.logicalViewResidualTemplate
            (Search.cataloguedFormulaLogicalView formulaView))

preparedFormulaRoot :: PreparedFormula global -> Search.TermId
preparedFormulaRoot (PreparedFormula formulaView) =
    Search.cataloguedRootTermId
        (Search.cataloguedFormulaRootReferences formulaView)

preparedFormulaNode
    :: PreparedFormula global
    -> LogicalView.LogicalNode global Search.CataloguedNodeRefs
preparedFormulaNode =
    LogicalView.logicalViewNode . preparedFormulaView

preparedFormulaHeadRefs
    :: PreparedFormula global
    -> Search.HeadRefs Search.TermId
preparedFormulaHeadRefs (PreparedFormula formulaView) =
    Search.cataloguedRootHeadRefs
        (Search.cataloguedFormulaRootReferences formulaView)

preparedFormulaView
    :: PreparedFormula global
    -> Search.CataloguedLogicalView global
preparedFormulaView (PreparedFormula formulaView) =
    Search.cataloguedFormulaLogicalView formulaView

data SignedMembership = SignedMembership
    { membershipTrueReason :: !(Maybe ProofReasonId)
    , membershipFalseReason :: !(Maybe ProofReasonId)
    }

emptySignedMembership :: SignedMembership
emptySignedMembership = SignedMembership Nothing Nothing

data AgendaItem = AgendaItem !Sign !Search.FormulaId

data PremiseIx = PremiseIx Int
    deriving stock (Show, Eq, Ord)

data ActiveRuleWitness = ActiveRuleWitness
    !Search.FormulaId
    !ProofReasonId

data InstanceKey = InstanceKey
    !BranchId
    !RuleId
    !MatcherSubstitutionId
    deriving stock (Show, Eq, Ord)

data PartialMatchKey = PartialMatchKey
    !BranchId
    !RuleId
    !PremiseIx
    !MatcherSubstitutionId
    deriving stock (Show, Eq, Ord)

data DemandSource
    = DemandFromFormula !Search.FormulaId
    | DemandFromPartial !PartialMatchKey
    deriving stock (Show, Eq, Ord)

data DemandKey = DemandKey
    !BranchId
    !DemandSource
    !Search.FormulaId
    deriving stock (Show, Eq, Ord)

data RuleMatchState
    = RuleStart
    | RulePartial !PartialMatchKey
    deriving stock (Show, Eq, Ord)

data RuleTrigger
    = FormulaTrigger !Search.FormulaId
    | DemandTrigger !DemandKey
    deriving stock (Show, Eq, Ord)

newtype EqualityMergeId = EqualityMergeId Int
    deriving stock (Show, Eq, Ord)

data RuleTriggerGeneration
    = BaseTrigger
    | EqualityRetry !EqualityMergeId
    deriving stock (Show, Eq, Ord)

data RuleTriggerKey = RuleTriggerKey
    !BranchId
    !RuleTriggerGeneration
    !RuleId
    !RuleMatchState
    !RuleTrigger
    deriving stock (Show, Eq, Ord)

data RuleRejectionSite
    = RejectedPremise !PremiseIx
    | RejectedConclusion
    deriving stock (Show, Eq, Ord)

data TerminalRuleRejectionKey = TerminalRuleRejectionKey
    !BranchId
    !RuleId
    !RuleRejectionSite
    !MatcherSubstitutionId
    deriving stock (Show, Eq, Ord)

data RuleProjectionSource
    = SourceProjection !Search.FormulaId
    | RuleContinuation !RuleId
    deriving stock (Show, Eq, Ord)

data RuleQueueKey
    = RuleActivationKey !BranchId !RuleId
    | RuleTriggerQueueKey !RuleTriggerKey
    | RuleProjectionKey !BranchId !RuleProjectionSource !Int
    deriving stock (Show, Eq, Ord)

data RuleQueueItem
    = RuleActivationItem !BranchId !RuleId
    | RuleTriggerItem !RuleTriggerKey
    | RuleProjectionItem !BranchId !RuleProjectionSource !Int

data AtomicComponent = AtomicComponent
    !Search.TermId
    !Search.TermId
    !(Equality.EqualityPath ProofReasonId)

data PremiseWitness
    = WitnessExact
        !Search.FormulaId
        !ProofReasonId
    | WitnessPropositionTransport
        !Search.FormulaId
        !ProofReasonId
        !(Equality.EqualityPath ProofReasonId)
    | WitnessAtomic
        !Search.FormulaId
        !ProofReasonId
        ![AtomicComponent]
    | WitnessOpenEquality
        !Search.FormulaId
        !ProofReasonId
        !Equality.EqualityDirection
        !(Equality.EqualityPath ProofReasonId)
        !(Equality.EqualityPath ProofReasonId)
    | WitnessDerivedEquality
        !(Equality.EqualityPath ProofReasonId)

data ReverseWitnessSpine
    = EmptyWitnessSpine
    | WitnessSpineCons
        !PremiseIx
        !PremiseWitness
        !ReverseWitnessSpine

data RetainedPartialMatch = RetainedPartialMatch
    !ActiveRuleWitness
    !ReverseWitnessSpine

data MatcherSubstitution = MatcherSubstitution
    !RuleId
    ![Maybe Search.TermId]

-- Each edge is one shallow term ID (or an unresolved slot). Lookup work
-- depends on binder arity, not on the number of earlier substitutions. IDs
-- still come from the append-only row sequence, preserving discovery order.
data MatcherSubstitutionTrie = MatcherSubstitutionTrie
    !(Maybe MatcherSubstitutionId)
    !(Map.Map (Maybe Search.TermId) MatcherSubstitutionTrie)

emptyMatcherSubstitutionTrie :: MatcherSubstitutionTrie
emptyMatcherSubstitutionTrie = MatcherSubstitutionTrie Nothing Map.empty

data ProspectiveMatcherSubstitution
    = ExistingMatcherSubstitution !MatcherSubstitutionId
    | FreshMatcherSubstitution
        !MatcherSubstitutionId
        !RuleId
        ![Maybe Search.TermId]

data RuleCacheEntry
    = CachedNotARule
    | CachedRule !RuleId
    | CachedProjections

data ProjectionCompilation global
    = ProjectionCompiling !(Match.RuleProjectionCursor global)
    | ProjectionComplete !Match.RuleCoverage

data CompiledRule global = CompiledRule
    !RuleId
    !Search.FormulaId
    !(Match.CompiledRule global)

type PartialSubstitution =
    Map.Map Template.MatcherSlot Search.TermId

data PremiseCandidate global
    = PremiseMatched !PartialSubstitution !PremiseWitness
    | PremiseOutsideUniverse
        !PartialSubstitution
        !(ScopedCheckedCore global)

data CandidateControl state
    = ContinueCandidates !state
    | StopCandidates !state

data BranchClosureDemand
    = UntrackedClosure
    | RetainOrdinaryClosure
    | SeekCanonicalClosure !ProofReasonId

-- Syntax is shared within a query; matching progress and signed events belong
-- to one branch. Each leaf remembers its next event, including when new events
-- arrive after it has reached the current end of the stream.
data UniversalHintSchema global = UniversalHintSchema
    !(Maybe (Match.UniversalHintCursor global)) !(Seq (Match.UniversalHint global))

data UniversalHintProgress = UniversalHintProgress !Int !(Seq Int)

data BranchState = BranchState
    { branchStateId :: !BranchId
    , branchMembership :: !(Map.Map Search.FormulaId SignedMembership)
    , branchAgenda :: !(Seq AgendaItem)
    , branchSplits :: !(Seq AgendaItem)
    , branchSupportSplits :: !(Seq AgendaItem)
    , branchClosure :: !(Maybe ProofReasonId)
    , branchClosureDemand :: !BranchClosureDemand
    , branchEquality :: !(Equality.EqualityState ProofReasonId)
    , branchActiveRules :: !(Map.Map RuleId ActiveRuleWitness)
    , branchRuleContinuations :: !(Set.Set RuleId)
    , branchRuleInstances :: !(Map.Map InstanceKey ProofReasonId)
    , branchPartialMatches :: !(Map.Map
        PartialMatchKey RetainedPartialMatch)
    , branchPartialOrder :: !(Seq PartialMatchKey)
    , branchDemands :: !(Set.Set DemandKey)
    , branchDemandOrder :: !(Seq DemandKey)
    , branchTerminalRejections :: !(Set.Set TerminalRuleRejectionKey)
    , branchRuleActivations :: !(Set.Set RuleQueueKey)
    , branchRuleTriggers :: !(Set.Set RuleTriggerKey)
    , branchRuleQueue :: !(Map.Map (Int, RuleQueueKey) RuleQueueItem)
    , branchNextEqualityMerge :: !Int
    , branchUniversalSources :: !(Map.Map Search.FormulaId Search.CatalogueTypeTerms)
    , branchUniversalQueue :: !(Seq Search.FormulaId)
    , branchUniversalAttempts :: !(Set.Set (Search.FormulaId, Search.TermId))
    -- An actual instance has run since the last split opportunity. Its ordinary
    -- consequences may enqueue the split after the instance itself returns.
    , branchUniversalSinceSplit :: !Bool
    , branchUniversalHintProgress :: !(Map.Map Search.FormulaId UniversalHintProgress)
    , branchUniversalHintEvents :: !(Seq AgendaItem)
    , branchUniversalHintStreak :: !Word
    , branchUniversalHintQueue :: !(Seq Search.FormulaId)
    }

data BranchInfo global = BranchInfo
    { branchParent :: !(Maybe BranchId)
    , branchDepth :: !Natural
    , branchContext :: !(KernelProof.ProofContext global)
    }

data BooleanPropagation
    = DisjunctionUnit !Bool -- Eliminate the left disjunct when True.
    | NegatedConjunctionUnit !Bool -- The left conjunct is known when True.
    | ImplicationUnit
    | ImplicationContrapositive

data ProofReason global
    = ReasonGoalNegation
    | ReasonExternalHypothesis !Natural
    | ReasonImport !ImportIx !(FrozenCheckedCore global)
    | ReasonCertifiedInput !(KernelProof.BuiltProof global) !KernelSourceUses
    | ReasonBranchHypothesis
    | ReasonTrueResidualization
        !(LogicalView.HeadResidualization global)
        !ProofReasonId
    | ReasonFalseResidualization
        !(LogicalView.HeadResidualization global)
        !ProofReasonId
    | ReasonDoubleNegation
        !(ScopedCheckedCore global)
        !ProofReasonId
    | ReasonConjunctionLeft
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
    | ReasonConjunctionRight
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
    | ReasonFalseDisjunction
        !Bool
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
    | ReasonFalseImplicationLeft
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
    | ReasonFalseImplicationRight
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
    | ReasonFalseConjunctionRight
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
        !ProofReasonId
    | ReasonTrueImplicationRight
        !(ScopedCheckedCore global)
        !ProofReasonId
        !ProofReasonId
    | ReasonBooleanPropagation !BooleanPropagation !ProofReasonId !ProofReasonId
    | ReasonContradiction !ProofReasonId !ProofReasonId
    | ReasonFalseTruth !ProofReasonId
    | ReasonTrueDisjunctionSplit
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !ProofReasonId
        !BranchId
        !ProofReasonId
        !BranchId
        !ProofReasonId
    | ReasonClassicalSplit
        !(ScopedCheckedCore global)
        !BranchId
        !ProofReasonId
        !BranchId
        !ProofReasonId
    | ReasonEqualityPath !(ScopedCheckedCore global) !(Equality.EqualityPath ProofReasonId)
    | ReasonSignedTransport !Sign !ProofReasonId !(Equality.EqualityPath ProofReasonId)
    | ReasonEqualityCongruence
        !ProofReasonId
        !ProofReasonId
    | ReasonEqualityContradiction
        !ProofReasonId
        !ProofReasonId
    | ReasonPropositionEqualityContradiction
        !ProofReasonId
        !ProofReasonId
        !ProofReasonId
    | ReasonUniversalInstance !Search.TermId !ProofReasonId
    | ReasonRuleInstance
        !RuleId
        !Search.FormulaId
        !ProofReasonId
        !MatcherSubstitutionId
        !(Seq PremiseWitness)

data ReasonEntry global = ReasonEntry
    !BranchId
    !(ScopedCheckedCore global)
    !(Seq ProofReasonId)
    !(ProofReason global)

-- | A materialized fragment is valid only at one branch-lineage proof depth.
-- The depth counts introduced proof hypotheses (the root negated goal and
-- case assumptions), independently of lexical Core binders.
data ProofAtDepth global = ProofAtDepth
    !BranchId
    !Natural
    !(KernelProof.BuiltProof global)

-- A support slot belongs to a branch, including when its ordinary reason was
-- inherited. Cloning a recipe in a child never changes an ancestor's slot.
data SupportConsumer
    = SupportRecipe !ProofReasonId
    | SupportAlias !ProofReasonId !ProofReasonId
    | SupportEquivalentFact !ProofReasonId
    | SupportEqualityRecipe !ProofReasonId

data BranchSupport = BranchSupport
    { supportedReasons :: !(Map.Map ProofReasonId ProofReasonId)
    , supportConsumers :: !(Map.Map ProofReasonId (Seq SupportConsumer))
    , supportFacts :: !(Seq (ProofReasonId, Sign, Search.TermId))
    , supportFactViews :: !(Map.Map ProofReasonId (Seq (Sign, Search.TermId)))
    , supportDemandedFacts :: !(Set.Set ProofReasonId)
    , supportEqualityConsumers :: !(Set.Set ProofReasonId)
    , supportEqualityLabels :: !(Set.Set ProofReasonId)
    , supportEqualityState :: !(Maybe (Equality.EqualityState ProofReasonId))
    , supportEqualityPaths :: !(Map.Map (Search.TermId, Search.TermId) (Equality.EqualityPath ProofReasonId))
    }

data RefutationSupport global = RefutationSupport
    { supportSources :: ![RefutationCanonicalSource]
    , supportBranches :: !(Map.Map BranchId BranchSupport)
    , supportWitnesses :: !(Map.Map ProofReasonId RefutationCanonicalSource)
    , supportPending :: !(Seq (BranchId, SupportConsumer))
    , supportAnyCandidate :: !(Maybe (RefutationCandidate global))
    }

data RefutationState global = RefutationState
    { stateGlobalTyping :: !(GlobalTyping global)
    , stateAmbientContext :: ![CoreType]
    , stateRemainingWork :: !Word
    , stateRemainingConversionPool :: !Conversion.ConversionPool
    , stateGroundTermLimit :: !Word
    , stateBranchNodeLimit :: !Word
    , stateRuleInstanceLimit :: !Word
    , stateBooleanPropagation :: !Bool
    , stateExtendedRules :: !Bool
    , stateUniversals :: !UniversalPolicy
    , stateUniversalAttempts :: !Word
    , stateUniversalHintSteps :: !Word
    , stateUniversalHintSchemas :: !(Map.Map Search.FormulaId (UniversalHintSchema global))
    , stateUniversalsDeferred :: !Bool
    , stateUniversalInventory :: !(Maybe Search.CatalogueTypeTerms)
    , stateBranchNodes :: !Word
    , stateTermCount :: !Word
    , statePrepaidTermCount :: !Word
    , stateTermAdmissions :: !Word
    , stateSignedCount :: !Word
    , stateEqualityEventCount :: !Word
    , stateRuleInstanceCount :: !Word
    , stateUnsupportedTerm :: !Bool
    , stateUndeterminedParameter :: !(Maybe Natural)
    , stateCatalogue :: !(Maybe (Search.Catalogue global))
    , stateFrozenDomain :: !(Maybe (FrozenDomain global))
    , stateFormulas :: !(Seq (PreparedFormula global))
    , stateFormulaByTerm :: !(Map.Map Search.TermId Search.FormulaId)
    , stateBranches :: !(Seq (BranchInfo global))
    , stateReasons :: !(Seq (ReasonEntry global))
    , stateSupport :: !(Maybe (RefutationSupport global))
    , stateRuleCache :: !(Map.Map Search.FormulaId RuleCacheEntry)
    , stateRuleProjections :: !(Map.Map RuleProjectionSource (Seq RuleId, ProjectionCompilation global))
    , stateRules :: !(Seq (CompiledRule global))
    , stateSubstitutions :: !(Seq MatcherSubstitution)
    , stateSubstitutionIndex :: !(Map.Map
        RuleId MatcherSubstitutionTrie)
    , stateTerminalRejectionPayloads :: !(Map.Map
        TerminalRuleRejectionKey (ScopedCheckedCore global))
    , stateMaterialized :: !(Map.Map
        (ProofReasonId, BranchId)
        (ProofAtDepth global))
    }

type Refute global value =
    Except.ExceptT RefutationFailure (State (RefutationState global)) value

initialState
    :: GlobalTyping global
    -> [CoreType]
    -> RefutationLimits
    -> RefutationState global
initialState globalTyping ambient limits =
    RefutationState
        { stateGlobalTyping = globalTyping
        , stateAmbientContext = ambient
        , stateRemainingWork = refutationWorkLimit limits
        , stateRemainingConversionPool = refutationConversionPool limits
        , stateGroundTermLimit = refutationGroundTermLimit limits
        , stateBranchNodeLimit = refutationBranchNodeLimit limits
        , stateRuleInstanceLimit = refutationRuleInstanceLimit limits
        , stateBooleanPropagation = refutationBooleanPropagation limits
        , stateExtendedRules = refutationExtendedRules limits
        , stateUniversals = refutationUniversals limits
        , stateUniversalAttempts = 0
        , stateUniversalHintSteps = 0
        , stateUniversalHintSchemas = Map.empty
        , stateUniversalsDeferred = False
        , stateUniversalInventory = Nothing
        , stateBranchNodes = 0
        , stateTermCount = 0
        , statePrepaidTermCount = 0
        , stateTermAdmissions = 0
        , stateSignedCount = 0
        , stateEqualityEventCount = 0
        , stateRuleInstanceCount = 0
        , stateUnsupportedTerm = False
        , stateUndeterminedParameter = Nothing
        , stateCatalogue = Nothing
        , stateFrozenDomain = Nothing
        , stateFormulas = Seq.empty
        , stateFormulaByTerm = Map.empty
        , stateBranches = Seq.empty
        , stateReasons = Seq.empty
        , stateSupport = Nothing
        , stateRuleCache = Map.empty
        , stateRuleProjections = Map.empty
        , stateRules = Seq.empty
        , stateSubstitutions = Seq.empty
        , stateSubstitutionIndex = Map.empty
        , stateTerminalRejectionPayloads = Map.empty
        , stateMaterialized = Map.empty
        }

statisticsFromState :: RefutationState global -> RefutationStatistics
statisticsFromState state =
    RefutationStatistics
        { refutationRemainingWork = stateRemainingWork state
        , refutationRemainingConversionPool = stateRemainingConversionPool state
        , refutationBranchNodes = stateBranchNodes state
        , refutationTerms = stateTermAdmissions state
        , refutationSignedFormulas = stateSignedCount state
        , refutationEqualityEvents = stateEqualityEventCount state
        , refutationRuleInstances = stateRuleInstanceCount state
        , refutationUniversalAttempts = stateUniversalAttempts state
        , refutationUniversalHintSteps = stateUniversalHintSteps state
        , refutationUniversalsDeferred = stateUniversalsDeferred state
        }

consumeWork :: Refute global ()
consumeWork = do
    remaining <- State.gets stateRemainingWork
    if remaining == 0
        then Except.throwE RefutationWorkExhausted
        else
            State.modify'
                (\state ->
                    state {stateRemainingWork = remaining - 1})

applicationSpine
    :: CanonicalTerm global
    -> Refute other (CanonicalTerm global, [CanonicalTerm global])
applicationSpine = collect []
  where
    collect reverseArguments term = do
        consumeWork
        case term of
            CApp function argument ->
                collect (argument : reverseArguments) function
            headTerm -> do
                arguments <- copyCounted reverseArguments
                pure (headTerm, arguments)

    copyCounted [] = pure []
    copyCounted (argument : rest) = do
        consumeWork
        (argument :) <$> copyCounted rest

runKernel
    :: KernelProof.CountedProof global value
    -> Refute global value
runKernel operation = do
    structural <- State.gets stateRemainingWork
    pool <- State.gets stateRemainingConversionPool
    let (result, afterStructural, afterPool) = KernelProof.runCountedProof structural pool operation
    State.modify'
        (\state ->
            state
                { stateRemainingWork = afterStructural
                , stateRemainingConversionPool = afterPool
                })
    case result of
        Left CountedCoreStructuralWorkExhausted ->
            Except.throwE RefutationWorkExhausted
        Left (CountedCoreOperationFailed (KernelProof.ProofConversionLimitExhausted owner limit)) ->
            Except.throwE (RefutationConversionLimitExhausted
                (case owner of
                    KernelProof.ProofConversionOperationLimit -> ObviousConversionOperationOwner
                    KernelProof.ProofConversionAggregatePool -> ObviousConversionPoolOwner)
                limit)
        Left (CountedCoreOperationFailed failure) ->
            Except.throwE (RefutationIntegrityFailure failure)
        Right value -> pure value

runConversion
    :: (Conversion.ConversionLimit -> Conversion.ConversionReport value)
    -> Refute global value
runConversion operation = do
    pool <- State.gets stateRemainingConversionPool
    case runObviousConversion pool operation of
        Left (ObviousConversionPoolAccountingInvariant cost incoming) ->
            Except.throwE (RefutationConversionAccountingInvariant cost incoming)
        Right (owner, remaining, result) -> do
            State.modify'
                (\state -> state {stateRemainingConversionPool = remaining})
            case result of
                Left (Conversion.ConversionLimitExhausted limit) ->
                    Except.throwE (RefutationConversionLimitExhausted owner limit)
                Left failure -> Except.throwE (RefutationConversionFailed failure)
                Right value -> pure value

-- Every root entered this Refutation owner before any recursive projection.
-- Reinspect applications after instantiation, since it can create a beta head.
prepareHead
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> Refute global (Maybe (ScopedCheckedCore global))
prepareHead globalType checked = do
    reducible <- needsReduction False (scopedCoreTerm checked)
    if not reducible
        then pure Nothing
        else do
            residual <- runConversion
                (\limit -> Conversion.residualizeHeadChecked
                    (Conversion.ConversionRecoveryTyping globalType globalType)
                    limit checked)
            unchanged <- scopedIdentity checked residual
            pure (if unchanged then Nothing else Just residual)
  where
    needsReduction applied term = do
        consumeWork
        case term of
            CApp function _argument -> needsReduction True function
            CLam{} -> pure applied
            _ -> pure False

runEqualityOperation
    :: (Word -> (Either Equality.EqualityFailure value, Word))
    -> Refute global value
runEqualityOperation operation = do
    work <- State.gets stateRemainingWork
    let (result, remaining) = operation work
    State.modify'
        (\state -> state {stateRemainingWork = remaining})
    case result of
        Left Equality.EqualityWorkExhausted ->
            Except.throwE RefutationWorkExhausted
        Left failure ->
            Except.throwE
                (RefutationInternalFailure
                    ("equality engine invariant failed: "
                        <> showText failure))
        Right value -> pure value

runMatchOperation
    :: (Word -> (Either Match.MatchFailure value, Word))
    -> Refute global value
runMatchOperation operation = do
    work <- State.gets stateRemainingWork
    let (result, remaining) = operation work
    State.modify' (\state -> state {stateRemainingWork = remaining})
    case result of
        Left Match.MatchWorkExhausted ->
            Except.throwE RefutationWorkExhausted
        Left (Match.MatchIntegrityFailure message) ->
            Except.throwE (RefutationInternalFailure message)
        Right value -> pure value

runTemplateOperation
    :: ( Word
         -> ( Either
                (CountedCoreFailure Template.TemplateError)
                value
            , Word
            )
       )
    -> Refute global value
runTemplateOperation operation = do
    work <- State.gets stateRemainingWork
    let (result, remaining) = operation work
    State.modify'
        (\state -> state {stateRemainingWork = remaining})
    case result of
        Left CountedCoreStructuralWorkExhausted ->
            Except.throwE RefutationWorkExhausted
        Left (CountedCoreOperationFailed failure) ->
            Except.throwE (refutationTemplateFailure failure)
        Right value -> pure value

refutationTemplateFailure :: Template.TemplateError -> RefutationFailure
refutationTemplateFailure = \case
    Template.TemplateContextMismatch expected actual ->
        RefutationInternalFailure ("prepared template context mismatch: " <> showText (expected, actual))
    Template.TemplateCheckFailed failure ->
        RefutationIntegrityFailure (KernelProof.ProofTermIllTyped failure)
    Template.TemplateInstantiationFailed failure ->
        RefutationIntegrityFailure (KernelProof.ProofSemanticsFailed
            (KernelSemantics.KernelScopedInstantiationFailed failure))
    Template.TemplateExpectedProposition coreType ->
        RefutationInternalFailure
            ("rule template is not propositional: " <> showText coreType)

prepareLogicalView
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> Refute global (LogicalView.LogicalView global ())
prepareLogicalView globalType checked = do
    template <-
        either
            (Except.throwE . refutationTemplateFailure)
            pure
            (Template.retainCheckedPropositionTemplate checked)
    result <-
        LogicalView.prepareCompiledLogicalViewCounted
            (prepareHead globalType) consumeWork template
    case result of
        Left (LogicalView.LogicalViewIntegrityFailure message) ->
            Except.throwE (RefutationInternalFailure message)
        Right view -> pure view

scopedIdentity
    :: Eq global
    => ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Refute other Bool
scopedIdentity left right = do
    work <- State.gets stateRemainingWork
    let (result, remaining) = countedScopedCoreIdentity work left right
    State.modify' (\state -> state {stateRemainingWork = remaining})
    case result of
        Left _failure -> Except.throwE RefutationWorkExhausted
        Right same -> pure same

showText :: Show value => value -> Text
showText = fromString . show

preparedFromView
    :: Search.CataloguedLogicalView global
    -> Refute other (PreparedFormula global)
preparedFromView view =
    case Search.cataloguedFormulaView view of
        Nothing ->
            Except.throwE
                (RefutationInternalFailure
                    "closed formula view has no catalogue root")
        Just formulaView ->
            case ( LogicalView.logicalViewNode view
                 , Search.cataloguedRootHeadRefs
                    (Search.cataloguedFormulaRootReferences formulaView)
                 ) of
                (LogicalView.LogicalEquality{}, Search.NonEqualityRefs) ->
                    Except.throwE
                        (RefutationInternalFailure
                            "catalogue evidence omitted an exposed equality payload")
                (LogicalView.LogicalEquality{}, Search.EqualityRefs{}) ->
                    pure (PreparedFormula formulaView)
                (_, Search.EqualityRefs{}) ->
                    Except.throwE
                        (RefutationInternalFailure
                            "catalogue equality evidence disagrees with the exposed head")
                (_, Search.NonEqualityRefs) ->
                    pure (PreparedFormula formulaView)

internFormula
    :: PreparedFormula global
    -> Refute global Search.FormulaId
internFormula candidate = do
    let root = preparedFormulaRoot candidate
    existing <- State.gets (Map.lookup root . stateFormulaByTerm)
    case existing of
        Just formulaId -> pure formulaId
        Nothing -> do
            consumeWork
            formulas <- State.gets stateFormulas
            let position = Seq.length formulas
                formulaId = Search.FormulaId position
            State.modify'
                (\state ->
                    state
                        { stateFormulas = stateFormulas state Seq.|> candidate
                        , stateFormulaByTerm =
                            Map.insert root formulaId (stateFormulaByTerm state)
                        })
            pure formulaId

lookupFormula
    :: Search.FormulaId
    -> Refute global (PreparedFormula global)
lookupFormula (Search.FormulaId position) = do
    consumeWork
    formulas <- State.gets stateFormulas
    maybe
        (Except.throwE
            (RefutationInternalFailure "unknown FormulaId"))
        pure
        (Seq.lookup position formulas)

lookupBranch
    :: BranchId
    -> Refute global (BranchInfo global)
lookupBranch (BranchId position) = do
    consumeWork
    branches <- State.gets stateBranches
    maybe
        (Except.throwE
            (RefutationInternalFailure "unknown BranchId"))
        pure
        (Seq.lookup position branches)

stageReasonPredecessor
    :: Int
    -> Seq ProofReasonId
    -> ProofReasonId
    -> Refute global (Seq ProofReasonId)
stageReasonPredecessor next predecessors
        predecessor@(ProofReasonId position) = do
    consumeWork
    unless (position >= 0 && position < next)
        (Except.throwE
            (RefutationInternalFailure
                "proof reason predecessor is not strictly older"))
    pure (predecessors Seq.|> predecessor)

stageEqualityPathPredecessors
    :: Int
    -> Seq ProofReasonId
    -> Equality.EqualityPath ProofReasonId
    -> Refute global (Seq ProofReasonId)
stageEqualityPathPredecessors next predecessors path =
    stageEqualityStepsPredecessors
        next predecessors (Equality.equalityPathSteps path)

stageEqualityStepsPredecessors
    :: Int
    -> Seq ProofReasonId
    -> [Equality.EqualityStep ProofReasonId]
    -> Refute global (Seq ProofReasonId)
stageEqualityStepsPredecessors _next predecessors [] = pure predecessors
stageEqualityStepsPredecessors next predecessors
        (Equality.EqualityStep reason _direction : rest) = do
    consumeWork
    withStep <- stageReasonPredecessor next predecessors reason
    stageEqualityStepsPredecessors next withStep rest

stagePremiseWitnessPredecessors
    :: Int
    -> Seq ProofReasonId
    -> PremiseWitness
    -> Refute global (Seq ProofReasonId)
stagePremiseWitnessPredecessors next predecessors witness = do
    consumeWork
    case witness of
        WitnessExact _formulaId reason ->
            stageReasonPredecessor next predecessors reason
        WitnessPropositionTransport _formulaId reason path -> do
            withReason <- stageReasonPredecessor next predecessors reason
            stageEqualityPathPredecessors next withReason path
        WitnessAtomic _formulaId reason components -> do
            withReason <- stageReasonPredecessor next predecessors reason
            stageComponents withReason components
        WitnessOpenEquality _formulaId reason _direction left right -> do
            withReason <- stageReasonPredecessor next predecessors reason
            withLeft <-
                stageEqualityPathPredecessors next withReason left
            stageEqualityPathPredecessors next withLeft right
        WitnessDerivedEquality path ->
            stageEqualityPathPredecessors next predecessors path
  where
    stageComponents current [] = pure current
    stageComponents current
            (AtomicComponent _left _right path : rest) = do
        consumeWork
        withComponent <-
            stageEqualityPathPredecessors next current path
        stageComponents withComponent rest

stagePremiseWitnessSequence
    :: Int
    -> Seq ProofReasonId
    -> Seq PremiseWitness
    -> Refute global (Seq ProofReasonId)
stagePremiseWitnessSequence next predecessors witnesses =
    case Seq.viewl witnesses of
        Seq.EmptyL -> pure predecessors
        witness Seq.:< rest -> do
            withWitness <-
                stagePremiseWitnessPredecessors next predecessors witness
            stagePremiseWitnessSequence next withWitness rest

stageReasonPredecessors
    :: Int
    -> ProofReason global
    -> Refute global (Seq ProofReasonId)
stageReasonPredecessors next = \case
    ReasonGoalNegation -> pure Seq.empty
    ReasonExternalHypothesis{} -> pure Seq.empty
    ReasonImport{} -> pure Seq.empty
    ReasonCertifiedInput{} -> pure Seq.empty
    ReasonBranchHypothesis -> pure Seq.empty
    ReasonTrueResidualization _ predecessor -> one predecessor
    ReasonFalseResidualization _ predecessor -> one predecessor
    ReasonDoubleNegation _ predecessor -> one predecessor
    ReasonConjunctionLeft _ _ predecessor -> one predecessor
    ReasonConjunctionRight _ _ predecessor -> one predecessor
    ReasonFalseDisjunction _ _ _ predecessor -> one predecessor
    ReasonFalseImplicationLeft _ _ predecessor -> one predecessor
    ReasonFalseImplicationRight _ _ predecessor -> one predecessor
    ReasonFalseConjunctionRight _ _ source assumption -> do
        withSource <- stageReasonPredecessor next Seq.empty source
        stageReasonPredecessor next withSource assumption
    ReasonTrueImplicationRight _ source assumption -> do
        withSource <- stageReasonPredecessor next Seq.empty source
        stageReasonPredecessor next withSource assumption
    ReasonBooleanPropagation _ source witness -> do
        withSource <- stageReasonPredecessor next Seq.empty source
        stageReasonPredecessor next withSource witness
    ReasonContradiction positive negative -> do
        withPositive <- stageReasonPredecessor next Seq.empty positive
        stageReasonPredecessor next withPositive negative
    ReasonFalseTruth predecessor -> one predecessor
    ReasonTrueDisjunctionSplit _ _ source _ left _ right -> do
        withSource <- stageReasonPredecessor next Seq.empty source
        withLeft <- stageReasonPredecessor next withSource left
        stageReasonPredecessor next withLeft right
    ReasonClassicalSplit _ _ left _ right -> do
        withLeft <- stageReasonPredecessor next Seq.empty left
        stageReasonPredecessor next withLeft right
    ReasonEqualityPath _ path -> stageEqualityPathPredecessors next Seq.empty path
    ReasonSignedTransport _ source path -> do
        withSource <- stageReasonPredecessor next Seq.empty source
        stageEqualityPathPredecessors next withSource path
    ReasonEqualityCongruence function argument -> do
        withFunction <- stageReasonPredecessor next Seq.empty function
        stageReasonPredecessor next withFunction argument
    ReasonEqualityContradiction equality disequality -> do
        withEquality <- stageReasonPredecessor next Seq.empty equality
        stageReasonPredecessor next withEquality disequality
    ReasonPropositionEqualityContradiction
            positive negative equality -> do
        withPositive <- stageReasonPredecessor next Seq.empty positive
        withNegative <- stageReasonPredecessor next withPositive negative
        stageReasonPredecessor next withNegative equality
    ReasonUniversalInstance _argument source -> one source
    ReasonRuleInstance
            _rule _sourceFormula source _substitution witnesses -> do
        initial <- stageReasonPredecessor next Seq.empty source
        stagePremiseWitnessSequence next initial witnesses
  where
    one predecessor = stageReasonPredecessor next Seq.empty predecessor

appendReason
    :: BranchId
    -> ScopedCheckedCore global
    -> ProofReason global
    -> Refute global ProofReasonId
appendReason branch statement reason = do
    consumeWork
    reasons <- State.gets stateReasons
    let next = Seq.length reasons
    predecessors <- stageReasonPredecessors next reason
    let reasonId = ProofReasonId next
    State.modify'
        (\state ->
            state
                { stateReasons =
                    stateReasons state
                        Seq.|> ReasonEntry
                            branch statement predecessors reason
                })
    registerSupportReason branch reasonId predecessors reason
    pure reasonId

-- Support bookkeeping is absent from ordinary requests. The source list and
-- every retained dependency are traversed under the same structural allowance.
modifySupport :: (RefutationSupport global -> RefutationSupport global) -> Refute global ()
modifySupport change = State.modify' (\state -> state {stateSupport = change <$> stateSupport state})

inheritBranchSupport :: BranchId -> Maybe BranchId -> Refute global ()
inheritBranchSupport branch parent = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        consumeWork
        inherited <- case parent of
            Nothing -> pure (BranchSupport Map.empty Map.empty Seq.empty Map.empty Set.empty Set.empty Set.empty Nothing Map.empty)
            Just ancestor -> maybe (Except.throwE (RefutationInternalFailure "a branch lost its support owner")) pure
                (Map.lookup ancestor (supportBranches support))
        modifySupport (\current -> current {supportBranches = Map.insert branch inherited (supportBranches current)})

branchSupport :: RefutationSupport global -> BranchId -> Refute global BranchSupport
branchSupport support branch = do
    consumeWork
    maybe (Except.throwE (RefutationInternalFailure "unknown branch support owner")) pure
        (Map.lookup branch (supportBranches support))

canonicalReason :: BranchId -> ProofReasonId -> Refute global (Maybe ProofReasonId)
canonicalReason branch reason = State.gets stateSupport >>= \case
    Nothing -> pure Nothing
    Just support -> do
        owned <- branchSupport support branch
        pure (Map.lookup reason (supportedReasons owned)
            <|> if Map.member reason (supportWitnesses support) then Just reason else Nothing)

supportSource :: ProofReason global -> Refute global (Maybe RefutationCanonicalSource)
supportSource reason = case reason of
    ReasonExternalHypothesis{} -> registered
    ReasonImport{} -> registered
    ReasonCertifiedInput{} -> registered
    _ -> pure Nothing
  where
    registered = State.gets stateSupport >>= \case
        Nothing -> pure Nothing
        Just support -> findSource (supportSources support)
    findSource [] = pure Nothing
    findSource (source : rest) = do
        consumeWork
        if consumed source then pure (Just source) else findSource rest
    consumed = \case
        RefutationCanonicalHypothesis index -> case reason of
            ReasonExternalHypothesis actual -> actual == index
            ReasonCertifiedInput _ uses -> Set.member (hypothesisIx index) (kernelSourceExternalHypothesisUses uses)
            _ -> False
        RefutationCanonicalImport index -> case reason of
            ReasonImport actual _ -> actual == index
            ReasonCertifiedInput _ uses -> Set.member index (kernelSourceImportUses uses)
            _ -> False

-- The global witness table describes actual immutable derivations. Alternatives
-- are recorded separately in their branch's slot, never by relabelling a reason.
registerSupportReason
    :: BranchId -> ProofReasonId -> Seq ProofReasonId -> ProofReason global -> Refute global ()
registerSupportReason branch identifier predecessors reason = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just _ -> do
        source <- supportSource reason
        witness <- maybe (consumedPredecessor (Seq.viewl predecessors)) (pure . Just) source
        case witness of
            Just used -> do
                modifySupport (\support -> support
                    {supportWitnesses = Map.insert identifier used (supportWitnesses support)})
                publishSupport branch identifier identifier
            Nothing -> do
                forM_ predecessors $ \predecessor -> subscribeSupport branch predecessor (SupportRecipe identifier)
                registerEqualityConsumer branch identifier reason
  where
    consumedPredecessor Seq.EmptyL = pure Nothing
    consumedPredecessor (predecessor Seq.:< rest) = do
        consumeWork
        witness <- State.gets (\state -> stateSupport state >>= Map.lookup predecessor . supportWitnesses)
        maybe (consumedPredecessor (Seq.viewl rest)) (pure . Just) witness

subscribeSupport :: BranchId -> ProofReasonId -> SupportConsumer -> Refute global ()
subscribeSupport branch predecessor consumer = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        let waiting = Map.findWithDefault Seq.empty predecessor (supportConsumers owned) Seq.|> consumer
        modifySupport (\current -> current {supportBranches = Map.insert branch
            owned {supportConsumers = Map.insert predecessor waiting (supportConsumers owned)}
            (supportBranches current)})
        known <- canonicalReason branch predecessor
        if isJust known then queueSupport branch consumer else demandSupportFact branch predecessor

queueSupport :: BranchId -> SupportConsumer -> Refute global ()
queueSupport branch consumer = do
    consumeWork
    modifySupport (\support -> support {supportPending = supportPending support Seq.|> (branch, consumer)})

publishSupport :: BranchId -> ProofReasonId -> ProofReasonId -> Refute global ()
publishSupport branch original canonical = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        unless (Map.member original (supportedReasons owned)) do
            unless (Map.member canonical (supportWitnesses support))
                (Except.throwE (RefutationInternalFailure "a support slot named an unsupported derivation"))
            let consumers = Map.findWithDefault Seq.empty original (supportConsumers owned)
            modifySupport (\current -> current {supportBranches = Map.insert branch
                owned {supportedReasons = Map.insert original canonical (supportedReasons owned)
                      , supportConsumers = Map.delete original (supportConsumers owned)
                      , supportDemandedFacts = Set.delete original (supportDemandedFacts owned)
                      , supportEqualityConsumers = Set.delete original (supportEqualityConsumers owned)}
                (supportBranches current)})
            forM_ consumers (queueSupport branch)
            when (Map.member original (supportFactViews owned)) (notifyFactSupport branch)
            when (Set.member original (supportEqualityLabels owned)) (notifyEqualitySupport branch)

-- Duplicate signed facts can support the existing reason, including after its
-- logical/rule consumers have fired. The duplicate is not a new formula event.
aliasSupport :: BranchId -> ProofReasonId -> ProofReasonId -> Refute global ()
aliasSupport branch original alternative = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just _ -> do
        known <- canonicalReason branch original
        unless (isJust known) (subscribeSupport branch alternative (SupportAlias original alternative))

advanceSupport :: Refute global Bool
advanceSupport = State.gets stateSupport >>= \case
    Nothing -> pure False
    Just support -> case Seq.viewl (supportPending support) of
        Seq.EmptyL -> pure False
        (branch, consumer) Seq.:< rest -> do
            consumeWork
            modifySupport (\current -> current {supportPending = rest})
            let original = case consumer of
                    SupportRecipe reason -> reason
                    SupportAlias reason _ -> reason
                    SupportEquivalentFact reason -> reason
                    SupportEqualityRecipe reason -> reason
            known <- canonicalReason branch original
            unless (isJust known) case consumer of
                SupportEquivalentFact _ -> upgradeEquivalentFact branch original
                SupportEqualityRecipe _ -> upgradeEqualityRecipe branch original
                SupportAlias _ alternative -> canonicalReason branch alternative >>= \case
                    Just canonical -> publishSupport branch original canonical
                    Nothing -> Except.throwE (RefutationInternalFailure "a support notification preceded its certificate")
                SupportRecipe _ -> do
                    ReasonEntry owner statement predecessors reason <- lookupReason original
                    -- A child may re-instantiate an inherited rule recipe with
                    -- its own inputs. A split recipe instead owns actual case
                    -- scopes; those cannot move below a different branch.
                    unless (owner /= branch && ownsCaseScopes reason) do
                        selected <- firstSupported branch (Seq.viewl predecessors)
                        case selected of
                            Nothing -> Except.throwE (RefutationInternalFailure "a support recipe lost its completed predecessor")
                            Just (ordinary, canonical) -> do
                                upgraded <- replaceReasonPredecessor ordinary canonical reason
                                completed <- appendReason branch statement upgraded
                                publishSupport branch original completed
            pure True
  where
    firstSupported _branch Seq.EmptyL = pure Nothing
    firstSupported branch (predecessor Seq.:< rest) = canonicalReason branch predecessor >>= \case
        Just canonical -> pure (Just (predecessor, canonical))
        Nothing -> firstSupported branch (Seq.viewl rest)
    ownsCaseScopes ReasonTrueDisjunctionSplit{} = True
    ownsCaseScopes ReasonClassicalSplit{} = True
    ownsCaseScopes _ = False

storeSupportEquality :: BranchState -> Refute global ()
storeSupportEquality branch = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support (branchStateId branch)
        modifySupport (\current -> current {supportBranches = Map.insert (branchStateId branch)
            owned {supportEqualityState = Just (branchEquality branch)} (supportBranches current)})

noteSupportEqualityEdge :: BranchId -> ProofReasonId -> Refute global ()
noteSupportEqualityEdge branch reason = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        modifySupport (\current -> current {supportBranches = Map.insert branch
            owned {supportEqualityLabels = Set.insert reason (supportEqualityLabels owned)} (supportBranches current)})
        notifyEqualitySupport branch

-- Admission order selects equivalent source facts. The reverse index permits
-- one reason to denote both positive not-P and negative P without losing either
-- legitimate view of the very same checked statement.
registerSupportFact :: BranchId -> ProofReasonId -> Sign -> Search.TermId -> Refute global ()
registerSupportFact branch reason sign term = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        let views = Map.findWithDefault Seq.empty reason (supportFactViews owned) Seq.|> (sign, term)
        modifySupport (\current -> current {supportBranches = Map.insert branch
            owned {supportFacts = supportFacts owned Seq.|> (reason, sign, term)
                  , supportFactViews = Map.insert reason views (supportFactViews owned)} (supportBranches current)})
        when (Map.member reason (supportConsumers owned)) (demandSupportFact branch reason)
        notifyFactSupport branch

demandSupportFact :: BranchId -> ProofReasonId -> Refute global ()
demandSupportFact branch reason = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        when (Map.member reason (supportFactViews owned) && Set.notMember reason (supportDemandedFacts owned)) do
            modifySupport (\current -> current {supportBranches = Map.insert branch
                owned {supportDemandedFacts = Set.insert reason (supportDemandedFacts owned)} (supportBranches current)})
            queueSupport branch (SupportEquivalentFact reason)

notifyFactSupport :: BranchId -> Refute global ()
notifyFactSupport branch = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        -- Reason IDs are admission ordinals, the explicit order of consumers.
        forM_ (supportDemandedFacts owned) (queueSupport branch . SupportEquivalentFact)

notifyEqualitySupport :: BranchId -> Refute global ()
notifyEqualitySupport branch = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        forM_ (supportEqualityConsumers owned) (queueSupport branch . SupportEqualityRecipe)
        notifyFactSupport branch

registerEqualityConsumer :: BranchId -> ProofReasonId -> ProofReason global -> Refute global ()
registerEqualityConsumer branch identifier reason = do
    hasPaths <- case reason of
        ReasonEqualityPath{} -> pure True
        ReasonSignedTransport{} -> pure True
        ReasonRuleInstance _ _ _ _ witnesses -> inspect (Seq.viewl witnesses)
        _ -> pure False
    when hasPaths do
        support <- State.gets stateSupport
        case support of
            Nothing -> pure ()
            Just current -> do
                owned <- branchSupport current branch
                modifySupport (\updated -> updated {supportBranches = Map.insert branch
                    owned {supportEqualityConsumers = Set.insert identifier (supportEqualityConsumers owned)}
                    (supportBranches updated)})
                queueSupport branch (SupportEqualityRecipe identifier)
  where
    inspect Seq.EmptyL = pure False
    inspect (witness Seq.:< rest) = do
        consumeWork
        case witness of
            WitnessExact{} -> inspect (Seq.viewl rest)
            WitnessAtomic _ _ [] -> inspect (Seq.viewl rest)
            _ -> pure True

-- Completed supported paths are immutable, branch-owned certificates. A miss
-- is not cached: later edges or predecessor upgrades can make it succeed.
-- Congruence descends only existing catalogue children and never changes the
-- evidence graph or reports a new equality merge.
supportEqualityPath
    :: BranchId -> Bool -> Search.TermId -> Search.TermId
    -> Refute global (Maybe (Equality.EqualityPath ProofReasonId))
supportEqualityPath branch requireCanonical left right = State.gets stateSupport >>= \case
    Nothing -> pure Nothing
    Just support -> do
        owned <- branchSupport support branch
        consumeWork
        case if requireCanonical then Map.lookup (left, right) (supportEqualityPaths owned) else Nothing of
            Just completed -> pure (Just completed)
            Nothing -> case supportEqualityState owned of
                Nothing -> pure Nothing
                Just graph -> do
                    catalogue <- currentCatalogue
                    let supported reason = Map.lookup reason (supportedReasons owned)
                            <|> if Map.member reason (supportWitnesses support) then Just reason else Nothing
                    direct <- runEqualityOperation (\work -> if requireCanonical
                        then Equality.equalitySupportedPath work catalogue supported graph left right
                        else Equality.equalityPath work catalogue graph left right)
                    selected <- case direct of
                        Nothing | requireCanonical -> congruence catalogue
                        _ -> pure direct
                    when requireCanonical $ forM_ selected $ \completed -> do
                        consumeWork
                        current <- State.gets stateSupport
                        forM_ current $ \latest -> do
                            currentBranch <- branchSupport latest branch
                            modifySupport (\updated -> updated {supportBranches = Map.insert branch
                                currentBranch {supportEqualityPaths = Map.insert (left, right) completed
                                    (supportEqualityPaths currentBranch)} (supportBranches updated)})
                    pure selected
  where
    row catalogue identifier = do
        consumeWork
        maybe (Except.throwE (RefutationInternalFailure "support path references an unknown catalogue term"))
            pure (Search.catalogueTerm catalogue identifier)
    congruence catalogue = do
        leftRow <- row catalogue left
        rightRow <- row catalogue right
        case (Search.catalogueTermApplication leftRow, Search.catalogueTermApplication rightRow) of
            (Just (leftFunction, leftArgument), Just (rightFunction, rightArgument)) -> do
                leftFunctionRow <- row catalogue leftFunction
                rightFunctionRow <- row catalogue rightFunction
                if Search.catalogueTermTypeId leftFunctionRow /= Search.catalogueTermTypeId rightFunctionRow
                    then pure Nothing
                    else do
                        ordinaryFunction <- supportEqualityPath branch False leftFunction rightFunction
                        ordinaryArgument <- supportEqualityPath branch False leftArgument rightArgument
                        case (ordinaryFunction, ordinaryArgument) of
                            (Just function, Just argument) -> do
                                supportedFunction <- supportEqualityPath branch True leftFunction rightFunction
                                operands <- case supportedFunction of
                                    Just upgraded -> pure (Just (upgraded, argument))
                                    Nothing -> fmap (\argumentPath -> (function, argumentPath)) <$> supportEqualityPath branch True leftArgument rightArgument
                                traverse (complete leftRow rightRow) operands
                            _ -> pure Nothing
            _ -> pure Nothing
    complete leftRow rightRow (function, argument) = do
        functionReason <- appendEqualityPathReasonInBranch function branch
        argumentReason <- appendEqualityPathReasonInBranch argument branch
        let leftValue = Search.catalogueTermValue leftRow
            rightValue = Search.catalogueTermValue rightRow
        statement <- scopedInBranch branch (CEq (scopedCoreType leftValue)
            (scopedCoreTerm leftValue) (scopedCoreTerm rightValue))
        reason <- appendReason branch statement (ReasonEqualityCongruence functionReason argumentReason)
        pure (Equality.EqualityPath left right [Equality.EqualityStep reason Equality.EqualityForward])

upgradeEquivalentFact :: BranchId -> ProofReasonId -> Refute global ()
upgradeEquivalentFact branch original = State.gets stateSupport >>= \case
    Nothing -> pure ()
    Just support -> do
        owned <- branchSupport support branch
        let views = Map.findWithDefault Seq.empty original (supportFactViews owned)
        selected <- targets (Seq.viewl views) (supportFacts owned)
        case selected of
            Nothing -> pure ()
            Just (sign, source, path) -> do
                ReasonEntry _owner statement _predecessors _recipe <- lookupReason original
                upgraded <- appendReason branch statement (ReasonSignedTransport sign source path)
                publishSupport branch original upgraded
  where
    targets Seq.EmptyL _sources = pure Nothing
    targets ((sign, target) Seq.:< rest) sources = do
        selected <- findSource sign target (Seq.viewl sources)
        maybe (targets (Seq.viewl rest) sources) (pure . Just) selected
    findSource _sign _target Seq.EmptyL = pure Nothing
    findSource sign target ((source, sourceSign, term) Seq.:< rest) = do
        consumeWork
        if sourceSign /= sign then findSource sign target (Seq.viewl rest) else do
            canonical <- canonicalReason branch source
            path <- supportEqualityPath branch (isNothing canonical) term target
            case path of
                Just explanation -> pure (Just (sign, fromMaybe source canonical, explanation))
                Nothing -> findSource sign target (Seq.viewl rest)

upgradeEqualityRecipe :: BranchId -> ProofReasonId -> Refute global ()
upgradeEqualityRecipe branch original = do
    ReasonEntry _owner statement _predecessors reason <- lookupReason original
    selected <- case reason of
        ReasonEqualityPath left explanation -> fmap (ReasonEqualityPath left) <$> path explanation
        ReasonSignedTransport sign source explanation -> fmap (ReasonSignedTransport sign source) <$> path explanation
        ReasonRuleInstance rule formula source substitution witnesses ->
            fmap (ReasonRuleInstance rule formula source substitution) <$> witnessSequence witnesses
        _ -> Except.throwE (RefutationInternalFailure "an equality consumer lost its path payload")
    forM_ selected $ \recipe -> do
        completed <- appendReason branch statement recipe
        publishSupport branch original completed
  where
    path explanation = supportEqualityPath branch True
        (Equality.equalityPathSource explanation) (Equality.equalityPathTarget explanation)
    witnessSequence witnesses = case Seq.viewl witnesses of
        Seq.EmptyL -> pure Nothing
        witness Seq.:< rest -> upgradeWitness witness >>= \case
            Just upgraded -> pure (Just (upgraded Seq.<| rest))
            Nothing -> fmap (witness Seq.<|) <$> witnessSequence rest
    upgradeWitness = \case
        WitnessExact{} -> pure Nothing
        WitnessPropositionTransport formula source explanation ->
            fmap (WitnessPropositionTransport formula source) <$> path explanation
        WitnessAtomic formula source components -> fmap (WitnessAtomic formula source) <$> upgradeComponents components
        WitnessOpenEquality formula source direction left right -> path left >>= \case
            Just upgraded -> pure (Just (WitnessOpenEquality formula source direction upgraded right))
            Nothing -> fmap (WitnessOpenEquality formula source direction left) <$> path right
        WitnessDerivedEquality explanation -> fmap WitnessDerivedEquality <$> path explanation
    upgradeComponents [] = pure Nothing
    upgradeComponents (component@(AtomicComponent left right explanation) : rest) = do
        consumeWork
        path explanation >>= \case
            Just upgraded -> pure (Just (AtomicComponent left right upgraded : rest))
            Nothing -> fmap (component :) <$> upgradeComponents rest

-- Replace the actual consumed input, including equality paths and rule witness
-- payloads. Updating only ReasonEntry's parallel predecessor list is unsound.
replaceReasonPredecessor
    :: ProofReasonId -> ProofReasonId -> ProofReason global -> Refute global (ProofReason global)
replaceReasonPredecessor original canonical reason = do
    consumeWork
    case reason of
        ReasonGoalNegation -> pure reason
        ReasonExternalHypothesis{} -> pure reason
        ReasonImport{} -> pure reason
        ReasonCertifiedInput{} -> pure reason
        ReasonBranchHypothesis -> pure reason
        ReasonTrueResidualization view predecessor -> ReasonTrueResidualization view <$> replace predecessor
        ReasonFalseResidualization view predecessor -> ReasonFalseResidualization view <$> replace predecessor
        ReasonDoubleNegation proposition predecessor -> ReasonDoubleNegation proposition <$> replace predecessor
        ReasonConjunctionLeft left right predecessor -> ReasonConjunctionLeft left right <$> replace predecessor
        ReasonConjunctionRight left right predecessor -> ReasonConjunctionRight left right <$> replace predecessor
        ReasonFalseDisjunction side left right predecessor -> ReasonFalseDisjunction side left right <$> replace predecessor
        ReasonFalseImplicationLeft left right predecessor -> ReasonFalseImplicationLeft left right <$> replace predecessor
        ReasonFalseImplicationRight left right predecessor -> ReasonFalseImplicationRight left right <$> replace predecessor
        ReasonFalseConjunctionRight left right source assumption ->
            ReasonFalseConjunctionRight left right <$> replace source <*> replace assumption
        ReasonTrueImplicationRight proposition source assumption ->
            ReasonTrueImplicationRight proposition <$> replace source <*> replace assumption
        ReasonBooleanPropagation operation source premise ->
            ReasonBooleanPropagation operation <$> replace source <*> replace premise
        ReasonContradiction positive negative -> ReasonContradiction <$> replace positive <*> replace negative
        ReasonFalseTruth predecessor -> ReasonFalseTruth <$> replace predecessor
        ReasonTrueDisjunctionSplit left right source leftBranch leftProof rightBranch rightProof ->
            ReasonTrueDisjunctionSplit left right <$> replace source <*> pure leftBranch <*> replace leftProof
                <*> pure rightBranch <*> replace rightProof
        ReasonClassicalSplit proposition leftBranch left rightBranch right ->
            ReasonClassicalSplit proposition leftBranch <$> replace left <*> pure rightBranch <*> replace right
        ReasonEqualityPath left explanation -> ReasonEqualityPath left <$> path explanation
        ReasonSignedTransport sign source explanation -> ReasonSignedTransport sign <$> replace source <*> path explanation
        ReasonEqualityCongruence function argument -> ReasonEqualityCongruence <$> replace function <*> replace argument
        ReasonEqualityContradiction equality disequality -> ReasonEqualityContradiction <$> replace equality <*> replace disequality
        ReasonPropositionEqualityContradiction positive negative equality ->
            ReasonPropositionEqualityContradiction <$> replace positive <*> replace negative <*> replace equality
        ReasonRuleInstance rule formula source substitution witnesses ->
            ReasonRuleInstance rule formula <$> replace source <*> pure substitution <*> traverse witness witnesses
        ReasonUniversalInstance argument source -> ReasonUniversalInstance argument <$> replace source
  where
    replace predecessor = consumeWork >> pure (if predecessor == original then canonical else predecessor)
    step (Equality.EqualityStep predecessor direction) = Equality.EqualityStep <$> replace predecessor <*> pure direction
    path (Equality.EqualityPath left right steps) = Equality.EqualityPath left right <$> traverse step steps
    component (AtomicComponent left right explanation) = consumeWork >> AtomicComponent left right <$> path explanation
    witness value = do
        consumeWork
        case value of
            WitnessExact formula predecessor -> WitnessExact formula <$> replace predecessor
            WitnessPropositionTransport formula predecessor explanation ->
                WitnessPropositionTransport formula <$> replace predecessor <*> path explanation
            WitnessAtomic formula predecessor components ->
                WitnessAtomic formula <$> replace predecessor <*> traverse component components
            WitnessOpenEquality formula predecessor direction left right ->
                WitnessOpenEquality formula <$> replace predecessor <*> pure direction <*> path left <*> path right
            WitnessDerivedEquality explanation -> WitnessDerivedEquality <$> path explanation

lookupReason
    :: ProofReasonId
    -> Refute global (ReasonEntry global)
lookupReason (ProofReasonId position) = do
    consumeWork
    reasons <- State.gets stateReasons
    maybe
        (Except.throwE
            (RefutationInternalFailure "unknown ProofReasonId"))
        pure
        (Seq.lookup position reasons)

newRootBranch
    :: KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> Refute global (BranchState, BranchId)
newRootBranch context assumption = do
    checkBranchCapacity
    catalogue <- currentCatalogue
    equalityState <-
        runEqualityOperation
            (\available ->
                Equality.initializeEqualityState available catalogue)
    rootContext <-
        runKernel
            (KernelProof.countedExtendProofContextHypothesis
                    context assumption)
    branchId <- appendBranchUnchecked Nothing 1 rootContext
    tracking <- State.gets (isJust . stateSupport)
    storeSupportEquality (emptyBranch branchId equalityState)
    pure ((emptyBranch branchId equalityState)
        {branchClosureDemand = if tracking then RetainOrdinaryClosure else UntrackedClosure}, branchId)

newChildBranch
    :: BranchState
    -> ScopedCheckedCore global
    -> Refute global (BranchState, ProofReasonId)
newChildBranch parent assumption = do
    parentInfo <- lookupBranch (branchStateId parent)
    checkBranchCapacity
    context <-
        runKernel
            (KernelProof.countedExtendProofContextHypothesis
                    (branchContext parentInfo)
                    assumption)
    childId <-
        appendBranchUnchecked
            (Just (branchStateId parent))
            (branchDepth parentInfo + 1)
            context
    reason <-
        appendReason
            childId assumption ReasonBranchHypothesis
    pure
        ( (emptyBranch childId (branchEquality parent))
            { branchClosure = branchAnyClosure parent
            , branchClosureDemand = case branchClosureDemand parent of
                UntrackedClosure -> UntrackedClosure
                _ -> RetainOrdinaryClosure
            , branchMembership = branchMembership parent
            , branchAgenda = branchAgenda parent
            , branchSplits = branchSplits parent
            , branchSupportSplits = branchSupportSplits parent
            , branchActiveRules = branchActiveRules parent
            , branchRuleContinuations = branchRuleContinuations parent
            , branchRuleInstances = branchRuleInstances parent
            , branchPartialMatches = branchPartialMatches parent
            , branchPartialOrder = branchPartialOrder parent
            , branchDemands = branchDemands parent
            , branchDemandOrder = branchDemandOrder parent
            , branchTerminalRejections =
                branchTerminalRejections parent
            , branchUniversalSources = branchUniversalSources parent
            , branchUniversalQueue = branchUniversalQueue parent
            , branchUniversalAttempts = branchUniversalAttempts parent
            , branchUniversalHintProgress = branchUniversalHintProgress parent
            , branchUniversalHintEvents = branchUniversalHintEvents parent
            , branchUniversalHintStreak = branchUniversalHintStreak parent
            , branchUniversalHintQueue = branchUniversalHintQueue parent
            }
        , reason
        )

emptyBranch
    :: BranchId
    -> Equality.EqualityState ProofReasonId
    -> BranchState
emptyBranch branchId equalityState =
    BranchState
        { branchStateId = branchId
        , branchMembership = Map.empty
        , branchAgenda = Seq.empty
        , branchSplits = Seq.empty
        , branchSupportSplits = Seq.empty
        , branchClosure = Nothing
        , branchClosureDemand = UntrackedClosure
        , branchEquality = equalityState
        , branchActiveRules = Map.empty
        , branchRuleContinuations = Set.empty
        , branchRuleInstances = Map.empty
        , branchPartialMatches = Map.empty
        , branchPartialOrder = Seq.empty
        , branchDemands = Set.empty
        , branchDemandOrder = Seq.empty
        , branchTerminalRejections = Set.empty
        , branchRuleActivations = Set.empty
        , branchRuleTriggers = Set.empty
        , branchRuleQueue = Map.empty
        , branchNextEqualityMerge = 0
        , branchUniversalSources = Map.empty
        , branchUniversalQueue = Seq.empty
        , branchUniversalAttempts = Set.empty
        , branchUniversalSinceSplit = False
        , branchUniversalHintProgress = Map.empty
        , branchUniversalHintEvents = Seq.empty
        , branchUniversalHintStreak = 0
        , branchUniversalHintQueue = Seq.empty
        }

checkBranchCapacity :: Refute global ()
checkBranchCapacity = do
    created <- State.gets stateBranchNodes
    limit <- State.gets stateBranchNodeLimit
    when (created >= limit)
        (Except.throwE RefutationBranchesExhausted)

appendBranchUnchecked
    :: Maybe BranchId
    -> Natural
    -> KernelProof.ProofContext global
    -> Refute global BranchId
appendBranchUnchecked parent depth context = do
    consumeWork
    branches <- State.gets stateBranches
    let branchId = BranchId (Seq.length branches)
    State.modify'
        (\state ->
            state
                { stateBranches =
                    stateBranches state
                        Seq.|> BranchInfo parent depth context
                , stateBranchNodes = stateBranchNodes state + 1
                })
    inheritBranchSupport branchId parent
    pure branchId

scopedInBranch
    :: BranchId
    -> CanonicalTerm global
    -> Refute global (ScopedCheckedCore global)
scopedInBranch branch term = do
    info <- lookupBranch branch
    runKernel
        (KernelProof.countedScopedTerm
                (branchContext info) term)

signedStatement
    :: BranchId
    -> Sign
    -> ScopedCheckedCore global
    -> Refute global (ScopedCheckedCore global)
signedStatement _branch SignTrue proposition = pure proposition
signedStatement branch SignFalse proposition =
    scopedInBranch branch (CNot (scopedCoreTerm proposition))

-- | Logical-view preparation and formula interning finish before a reason
-- or membership row is published. Duplicate admission retains the first stable
-- reason and schedules no work.
admitSignedFormula
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Sign
    -> ScopedCheckedCore global
    -> ProofReasonId
    -> Refute global BranchState
admitSignedFormula globalType branch sign source sourceReason
        | stopsBranchWork branch = pure branch
        | otherwise = do
            view <- prepareLogicalView globalType source
            prepareRequiredResolvedProposition globalType view >>= \case
                Nothing -> Except.throwE RefutationUnsupportedTermOutsideUniverse
                Just resolved ->
                    admitPreparedDerivedSignedFormula
                        globalType branch sign resolved sourceReason

admitPreparedDerivedSignedFormula
    :: GlobalTyping global
    -> BranchState
    -> Sign
    -> Search.ResolvedDerivedProposition global
    -> ProofReasonId
    -> Refute global BranchState
admitPreparedDerivedSignedFormula globalType branch sign resolved sourceReason
        | stopsBranchWork branch = pure branch
        | otherwise = do
            (prepared, formulaId) <- finishResolvedFormula resolved
            admitPreparedSignedFormula
                globalType branch sign prepared formulaId sourceReason

admitCataloguedViewSignedFormula
    :: GlobalTyping global
    -> BranchState
    -> Sign
    -> Search.CataloguedLogicalView global
    -> ProofReasonId
    -> Refute global BranchState
admitCataloguedViewSignedFormula globalType branch sign view sourceReason
        | stopsBranchWork branch = pure branch
        | otherwise = do
            prepared <- preparedFromView view
            formulaId <- internFormula prepared
            admitPreparedSignedFormula
                globalType branch sign prepared formulaId sourceReason

logicalViewOriginalValue
    :: LogicalView.LogicalView global payload
    -> ScopedCheckedCore global
logicalViewOriginalValue =
    Template.compiledTemplateTerm
        . LogicalView.logicalViewOriginalTemplate

admitPreparedSignedFormula
    :: GlobalTyping global
    -> BranchState
    -> Sign
    -> PreparedFormula global
    -> Search.FormulaId
    -> ProofReasonId
    -> Refute global BranchState
admitPreparedSignedFormula globalType branch sign prepared formulaId sourceReason
        | stopsBranchWork branch = pure branch
        | otherwise = do
            let membership =
                    Map.findWithDefault
                        emptySignedMembership formulaId
                        (branchMembership branch)
                existing = reasonFor sign membership
            case existing of
                Just existingReason -> State.gets stateSupport >>= \case
                    Nothing -> pure branch
                    Just _ -> do
                        alternative <- prepareReason
                        aliasSupport (branchStateId branch) existingReason alternative
                        pure branch
                Nothing -> do
                    residualReason <- prepareReason
                    registerSupportFact (branchStateId branch) residualReason sign (preparedFormulaRoot prepared)
                    let updatedMembership =
                            setReason sign residualReason membership
                        updated =
                            branch
                                { branchMembership =
                                    Map.insert
                                        formulaId updatedMembership
                                        (branchMembership branch)
                                }
                    State.modify'
                        (\state ->
                            state
                                { stateSignedCount =
                                    stateSignedCount state + 1
                                })
                    withHintEvent <- retainUniversalHintEvent sign formulaId prepared updated
                    closeOrQueue
                        formulaId prepared sign residualReason
                        updatedMembership withHintEvent
  where
    prepareReason = do
        statement <- signedStatement (branchStateId branch) sign (preparedFormulaValue prepared)
        case LogicalView.logicalViewHeadResidualization (preparedFormulaView prepared) of
            Just residualization -> appendReason (branchStateId branch) statement
                (case sign of
                    SignTrue -> ReasonTrueResidualization residualization sourceReason
                    SignFalse -> ReasonFalseResidualization residualization sourceReason)
            Nothing -> pure sourceReason

    reasonFor SignTrue = membershipTrueReason
    reasonFor SignFalse = membershipFalseReason

    setReason SignTrue reason membership =
        membership {membershipTrueReason = Just reason}
    setReason SignFalse reason membership =
        membership {membershipFalseReason = Just reason}

    closeOrQueue selectedFormulaId selectedPrepared admittedSign reason
            membership updated =
        case (membershipTrueReason membership,
                membershipFalseReason membership) of
            (Just positive, Just negative) -> do
                falsum <- scopedInBranch (branchStateId updated) CFalsum
                closure <-
                    appendReason
                        (branchStateId updated)
                        falsum
                        (ReasonContradiction positive negative)
                closed <- recordBranchClosure updated closure
                continueClosed selectedFormulaId selectedPrepared admittedSign reason closed
            _ ->
                case (admittedSign, preparedFormulaNode selectedPrepared) of
                    (SignTrue, LogicalView.LogicalFalsum) -> do
                        closed <- recordBranchClosure updated reason
                        continueClosed selectedFormulaId selectedPrepared admittedSign reason closed
                    (SignFalse, LogicalView.LogicalTruth) -> do
                        falsum <-
                            scopedInBranch (branchStateId updated) CFalsum
                        closure <-
                            appendReason
                                (branchStateId updated)
                                falsum
                                (ReasonFalseTruth reason)
                        closed <- recordBranchClosure updated closure
                        continueClosed selectedFormulaId selectedPrepared admittedSign reason closed
                    _ -> queueFormula selectedFormulaId selectedPrepared admittedSign reason updated

    continueClosed formula preparedFormula admittedSign reason closed
        | stopsBranchWork closed = pure closed
        | otherwise = queueFormula formula preparedFormula admittedSign reason closed

    queueFormula formula preparedFormula admittedSign reason updated = do
        withEquality <- applyEqualityAdmission globalType formula preparedFormula admittedSign reason updated
        if stopsBranchWork withEquality then pure withEquality else do
            withRules <- applyRuleAdmission globalType formula preparedFormula admittedSign reason withEquality
            pure (if stopsBranchWork withRules then withRules else withRules
                {branchAgenda = branchAgenda withRules Seq.|> AgendaItem admittedSign formula})

currentCatalogue :: Refute global (Search.Catalogue global)
currentCatalogue = do
    consumeWork
    maybe
        (Except.throwE
            (RefutationInternalFailure
                "refutation catalogue was not initialized"))
        pure
        =<< State.gets stateCatalogue

catalogueTermValue
    :: Search.TermId
    -> Refute global (ScopedCheckedCore global)
catalogueTermValue termId = do
    consumeWork
    catalogue <- currentCatalogue
    maybe
        (Except.throwE
            (RefutationInternalFailure
                "equality reason references an unknown TermId"))
        (pure . Search.catalogueTermValue)
        (Search.catalogueTerm catalogue termId)

applySearchResult
    :: (Either Search.CatalogueError value, Word)
    -> Refute global value
applySearchResult (result, remaining) = do
    State.modify' (\state -> state {stateRemainingWork = remaining})
    case result of
        Left Search.CatalogueWorkExhausted ->
            Except.throwE RefutationWorkExhausted
        Left Search.CatalogueGroundTermLimitExhausted ->
            Except.throwE RefutationGroundTermsExhausted
        Left Search.CatalogueOutsideFrozenUniverse ->
            Except.throwE RefutationUnsupportedTermOutsideUniverse
        Left (Search.CatalogueIntegrityFailure message) ->
            Except.throwE (RefutationInternalFailure message)
        Right value -> pure value

data DerivedPreparation global
    = DerivedPrepared !(Search.ResolvedDerivedProposition global)
    | DerivedOutsideFrozenDomain

-- Preparation describes the frozen-domain boundary without selecting a failure
-- policy. In particular, rejecting a speculative proved fact must not poison
-- a query's eventual diagnostic. Required rule callers select that policy below.
prepareResolvedProposition
    :: Eq global
    => GlobalTyping global
    -> LogicalView.LogicalView global ()
    -> Refute global (DerivedPreparation global)
prepareResolvedProposition globalType view = do
    catalogue <- currentCatalogue
    ambient <- State.gets stateAmbientContext
    work <- State.gets stateRemainingWork
    let (result, remaining) = Search.prepareResolvedDerivedPropositionCounted
            globalType work ambient catalogue view
    State.modify' (\state -> state {stateRemainingWork = remaining})
    case result of
        Left Search.CatalogueWorkExhausted -> Except.throwE RefutationWorkExhausted
        Left Search.CatalogueGroundTermLimitExhausted -> Except.throwE RefutationGroundTermsExhausted
        Left Search.CatalogueOutsideFrozenUniverse -> pure DerivedOutsideFrozenDomain
        Left (Search.CatalogueIntegrityFailure message) -> Except.throwE (RefutationInternalFailure message)
        Right resolved -> pure (DerivedPrepared resolved)

prepareRequiredResolvedProposition
    :: Eq global
    => GlobalTyping global
    -> LogicalView.LogicalView global ()
    -> Refute global (Maybe (Search.ResolvedDerivedProposition global))
prepareRequiredResolvedProposition globalType view =
    prepareResolvedProposition globalType view >>= \case
        DerivedOutsideFrozenDomain -> do
            State.modify' (\state -> state {stateUnsupportedTerm = True})
            pure Nothing
        DerivedPrepared resolved -> pure (Just resolved)

resolvedRootExisting
    :: Search.ResolvedDerivedProposition global
    -> Maybe Search.TermId
resolvedRootExisting resolved =
    Search.resolvedDerivedRootRef resolved
        >>= Search.resolvedTermExistingId

requireResolvedRootRef
    :: Search.ResolvedDerivedProposition global
    -> Refute other Search.ResolvedTermRef
requireResolvedRootRef resolved =
    maybe
        (Except.throwE
            (RefutationInternalFailure
                "resolved closed formula view has no root reference"))
        pure
        (Search.resolvedDerivedRootRef resolved)

-- Closing a residual template may create a new head redex. Prepare the
-- resulting checked proposition under the current operation typing.
prepareRequiredDerivedProposition
    :: Eq global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> Refute global (Maybe (Search.ResolvedDerivedProposition global))
prepareRequiredDerivedProposition globalType value = do
    view <- prepareLogicalView globalType value
    prepareRequiredResolvedProposition globalType view

finishResolvedFormula
    :: Search.ResolvedDerivedProposition global
    -> Refute global (PreparedFormula global, Search.FormulaId)
finishResolvedFormula resolved = do
    view <- finishResolvedView resolved
    prepared <- preparedFromView view
    formulaId <- internFormula prepared
    -- Use retained exposure evidence; the resulting formula already owns its
    -- stable catalogue ID.
    pure (prepared, formulaId)

finishResolvedView
    :: Search.ResolvedDerivedProposition global
    -> Refute global (Search.CataloguedLogicalView global)
finishResolvedView resolved = do
    catalogue <- currentCatalogue
    work <- State.gets stateRemainingWork
    termLimit <- effectiveCatalogueLimit
    let (result, remaining, admissions) = Search.finishDerivedPropositionCounted
            work termLimit catalogue resolved
    retainTermAdmissions admissions
    staged <-
        applySearchResult (result, remaining)
    let updatedCatalogue = Search.stagedCatalogue staged
    State.modify'
        (\state -> state
            { stateCatalogue = Just updatedCatalogue
            , stateTermCount = Search.catalogueTermCount updatedCatalogue
            })
    pure (Search.stagedLogicalView staged)

-- Failed staging can discard rows, but cannot refund their request allowance.
-- The catalogue's live size still owns term IDs; admissions own the resource.
effectiveCatalogueLimit :: Refute global Word
effectiveCatalogueLimit = do
    live <- State.gets stateTermCount
    prepaid <- State.gets statePrepaidTermCount
    admitted <- State.gets stateTermAdmissions
    limit <- State.gets stateGroundTermLimit
    unless (prepaid <= live && live - prepaid <= admitted
            && admitted <= limit && live <= maxBound - (limit - admitted))
        (Except.throwE (RefutationInternalFailure "catalogue admission accounting disagrees with live rows"))
    -- An inherited immutable domain was paid by its family. Only additions to
    -- this query consume its remaining admission allowance.
    pure (live + (limit - admitted))

retainTermAdmissions :: Word -> Refute global ()
retainTermAdmissions added = do
    admitted <- State.gets stateTermAdmissions
    limit <- State.gets stateGroundTermLimit
    unless (admitted <= limit && added <= limit - admitted)
        (Except.throwE (RefutationInternalFailure "catalogue admission accounting exceeds its allowance"))
    State.modify' (\state -> state {stateTermAdmissions = admitted + added})

updateEqualityEvents :: Bool -> Refute global ()
updateEqualityEvents False = pure ()
updateEqualityEvents True =
    State.modify'
        (\state ->
            state
                { stateEqualityEventCount =
                    stateEqualityEventCount state + 1
                })

applyEqualityAdmission
    :: GlobalTyping global
    -> Search.FormulaId
    -> PreparedFormula global
    -> Sign
    -> ProofReasonId
    -> BranchState
    -> Refute global BranchState
applyEqualityAdmission
        _globalType formulaId prepared sign reason branch = do
    let propositionId = preparedFormulaRoot prepared
    catalogue <- currentCatalogue
    visible <-
        runEqualityOperation
            (\available ->
                Equality.makeTermVisible
                    available catalogue propositionId
                    (branchEquality branch))
    let withVisible = branch {branchEquality = visible}
    (withPolarity, polarityClash, _polarityAdded) <-
        runEqualityOperation
            (\available ->
                Equality.recordPolarity
                    available catalogue (sign == SignTrue)
                    propositionId formulaId reason visible)
    let afterPolarity = withVisible {branchEquality = withPolarity}
    withClash <- maybe (pure afterPolarity) (closeEqualityClash afterPolarity) polarityClash
    result <- if stopsBranchWork withClash then pure withClash else
        case (preparedFormulaNode prepared, preparedFormulaHeadRefs prepared) of
            (LogicalView.LogicalEquality{}, Search.EqualityRefs _operandType leftId rightId) -> do
                withLeft <- runEqualityOperation (\work ->
                    Equality.makeTermVisible work catalogue leftId (branchEquality withClash))
                withRight <- runEqualityOperation (\work -> Equality.makeTermVisible work catalogue rightId withLeft)
                tracking <- State.gets (isJust . stateSupport)
                (updated, clash, added) <- runEqualityOperation (\work -> case sign of
                    SignTrue -> (if tracking then Equality.recordEqualityWithSupport else Equality.recordEquality)
                        work catalogue leftId rightId reason withRight
                    SignFalse -> Equality.recordDisequality work catalogue leftId rightId reason withRight)
                updateEqualityEvents added
                when (sign == SignTrue) (noteSupportEqualityEdge (branchStateId branch) reason)
                let afterEquality = withClash {branchEquality = updated}
                case clash of
                    Just equalityClash -> closeEqualityClash afterEquality equalityClash
                    Nothing | sign == SignTrue && added -> enqueueEqualityRetry afterEquality
                    _ -> pure afterEquality
            _ -> pure withClash
    storeSupportEquality result
    pure result

applyRuleAdmission
    :: GlobalTyping global
    -> Search.FormulaId
    -> PreparedFormula global
    -> Sign
    -> ProofReasonId
    -> BranchState
    -> Refute global BranchState
applyRuleAdmission globalType formulaId prepared sign reason branch =
    case sign of
        SignFalse ->
            if demandable (preparedFormulaNode prepared)
                then retainFormulaDemand branch formulaId
                else pure branch
        SignTrue -> do
            recognition <- classifyRule globalType formulaId prepared
            withActivation <-
                case recognition of
                    CachedNotARule -> enrollUniversal formulaId prepared branch
                    CachedRule ruleId ->
                        installActiveRule
                            branch ruleId
                            (ActiveRuleWitness formulaId reason)
                    CachedProjections -> enqueueRuleProjection branch (SourceProjection formulaId) 0
            notifyFormulaVisibility withActivation formulaId
  where
    demandable = \case
        LogicalView.LogicalEquality{} -> True
        LogicalView.LogicalNeutral -> True
        _ -> False

classifyRule
    :: GlobalTyping global
    -> Search.FormulaId
    -> PreparedFormula global
    -> Refute global RuleCacheEntry
classifyRule globalType formulaId prepared = do
    consumeWork
    cached <- State.gets (Map.lookup formulaId . stateRuleCache)
    case cached of
        Just entry -> pure entry
        Nothing -> do
            catalogue <- currentCatalogue
            extended <- State.gets stateExtendedRules
            recognition <-
                runMatchOperation
                    (\work ->
                        Match.recognizeRule
                            extended globalType work catalogue
                            (preparedFormulaView prepared))
            case recognition of
                Match.NotARule -> do
                    consumeWork
                    State.modify'
                        (\state ->
                            state
                                { stateRuleCache =
                                    Map.insert formulaId CachedNotARule
                                        (stateRuleCache state)
                                })
                    pure CachedNotARule
                Match.RecognizedRule compiled -> do
                    consumeWork
                    rules <- State.gets stateRules
                    let ruleId = RuleId (Seq.length rules)
                    State.modify'
                        (\state ->
                            state
                                { stateRules =
                                    stateRules state
                                        Seq.|> CompiledRule
                                            ruleId formulaId compiled
                                , stateRuleCache =
                                    Map.insert formulaId (CachedRule ruleId)
                                        (stateRuleCache state)
                                })
                    pure (CachedRule ruleId)
                Match.ProjectedRules cursor -> do
                    consumeWork
                    State.modify' (\state -> state
                        { stateRuleCache = Map.insert formulaId CachedProjections (stateRuleCache state)
                        , stateRuleProjections = Map.insert (SourceProjection formulaId)
                            (Seq.empty, ProjectionCompiling cursor) (stateRuleProjections state) })
                    pure CachedProjections

lookupCompiledRule
    :: RuleId
    -> Refute global
        (Search.FormulaId, Match.CompiledRule global)
lookupCompiledRule (RuleId position) = do
    consumeWork
    rules <- State.gets stateRules
    case Seq.lookup position rules of
        Just (CompiledRule foundRule sourceFormula compiled)
            | foundRule == RuleId position ->
                pure (sourceFormula, compiled)
        Just CompiledRule{} ->
            Except.throwE
                (RefutationInternalFailure
                    "compiled rule has a different stable ID")
        Nothing ->
            Except.throwE
                (RefutationInternalFailure "unknown RuleId")

appendEqualityPathReason
    :: Equality.EqualityPath ProofReasonId
    -> BranchState
    -> Refute global ProofReasonId
appendEqualityPathReason path branch = appendEqualityPathReasonInBranch path (branchStateId branch)

appendEqualityPathReasonInBranch
    :: Equality.EqualityPath ProofReasonId -> BranchId -> Refute global ProofReasonId
appendEqualityPathReasonInBranch path branch = do
    left <- catalogueTermValue (Equality.equalityPathSource path)
    right <- catalogueTermValue (Equality.equalityPathTarget path)
    statement <-
        scopedInBranch
            branch
            (CEq
                (scopedCoreType left)
                (scopedCoreTerm left)
                (scopedCoreTerm right))
    appendReason
        branch
        statement
        (ReasonEqualityPath left path)

closeEqualityClash
    :: BranchState
    -> Equality.EqualityClash ProofReasonId
    -> Refute global BranchState
closeEqualityClash branch clash = do
    falsum <- scopedInBranch (branchStateId branch) CFalsum
    closure <-
        case clash of
            Equality.EqualityDisequalityClash path disequality -> do
                equality <- appendEqualityPathReason path branch
                appendReason
                    (branchStateId branch)
                    falsum
                    (ReasonEqualityContradiction
                        equality disequality)
            Equality.EqualityPropositionClash
                    positive negative path -> do
                equality <- appendEqualityPathReason path branch
                appendReason
                    (branchStateId branch)
                    falsum
                    (ReasonPropositionEqualityContradiction
                        positive negative equality)
    recordBranchClosure branch closure

processAgendaItem
    :: GlobalTyping global
    -> BranchState
    -> AgendaItem
    -> Refute global BranchState
processAgendaItem globalType branch item@(AgendaItem sign formulaId) = do
    prepared <- lookupFormula formulaId
    membership <-
        maybe
            (Except.throwE
                (RefutationInternalFailure
                    "agenda formula lacks signed membership"))
            pure
            (Map.lookup formulaId (branchMembership branch))
    sourceReason <-
        maybe
            (Except.throwE
                (RefutationInternalFailure
                    "agenda sign lacks a proof reason"))
            pure
            (case sign of
                SignTrue -> membershipTrueReason membership
                SignFalse -> membershipFalseReason membership)
    let branchId = branchStateId branch
        addDerived derivedSign childView reason =
            admitCataloguedViewSignedFormula
                globalType branch derivedSign childView reason
    case (sign, preparedFormulaNode prepared) of
        (_, LogicalView.LogicalTruth) -> pure branch
        (_, LogicalView.LogicalFalsum) -> pure branch
        (SignTrue, LogicalView.LogicalNegation childView) ->
            addDerived SignFalse childView sourceReason
        (SignFalse, LogicalView.LogicalNegation childView) -> do
            let child = logicalViewOriginalValue childView
            reason <-
                appendReason
                    branchId child
                    (ReasonDoubleNegation child sourceReason)
            addDerived SignTrue childView reason
        (SignTrue, LogicalView.LogicalConjunction leftView rightView) -> do
            let left = logicalViewOriginalValue leftView
                leftTerm = scopedCoreTerm left
                rightTerm = scopedCoreTerm (logicalViewOriginalValue rightView)
            leftReason <-
                appendReason
                    branchId left
                    (ReasonConjunctionLeft
                        leftTerm rightTerm sourceReason)
            afterLeft <-
                admitCataloguedViewSignedFormula
                    globalType branch SignTrue leftView leftReason
            if stopsBranchWork afterLeft
                then pure afterLeft
                else do
                    let right = logicalViewOriginalValue rightView
                    rightReason <-
                        appendReason
                            branchId right
                            (ReasonConjunctionRight
                                leftTerm rightTerm sourceReason)
                    admitCataloguedViewSignedFormula
                        globalType afterLeft SignTrue rightView rightReason
        (SignFalse, LogicalView.LogicalConjunction{}) ->
            pure
                branch
                    { branchSplits = branchSplits branch Seq.|> item }
        (SignTrue, LogicalView.LogicalDisjunction{}) ->
            pure
                branch
                    { branchSplits = branchSplits branch Seq.|> item }
        (SignFalse, LogicalView.LogicalDisjunction leftView rightView) -> do
            let left = logicalViewOriginalValue leftView
                leftTerm = scopedCoreTerm left
                rightTerm = scopedCoreTerm (logicalViewOriginalValue rightView)
            leftStatement <-
                signedStatement branchId SignFalse left
            leftReason <-
                appendReason
                    branchId leftStatement
                    (ReasonFalseDisjunction
                        True leftTerm rightTerm sourceReason)
            afterLeft <-
                admitCataloguedViewSignedFormula
                    globalType branch SignFalse leftView leftReason
            if stopsBranchWork afterLeft
                then pure afterLeft
                else do
                    let right = logicalViewOriginalValue rightView
                    rightStatement <-
                        signedStatement branchId SignFalse right
                    rightReason <-
                        appendReason
                            branchId rightStatement
                            (ReasonFalseDisjunction
                                False leftTerm rightTerm sourceReason)
                    admitCataloguedViewSignedFormula
                        globalType afterLeft SignFalse rightView rightReason
        (SignTrue, LogicalView.LogicalImplication{}) ->
            pure
                branch
                    { branchSplits = branchSplits branch Seq.|> item }
        (SignFalse, LogicalView.LogicalImplication premiseView conclusionView) -> do
            let premise = logicalViewOriginalValue premiseView
                premiseTerm = scopedCoreTerm premise
                conclusionTerm =
                    scopedCoreTerm (logicalViewOriginalValue conclusionView)
            premiseReason <-
                appendReason
                    branchId premise
                    (ReasonFalseImplicationLeft
                        premiseTerm conclusionTerm sourceReason)
            afterPremise <-
                admitCataloguedViewSignedFormula
                    globalType branch SignTrue premiseView premiseReason
            if stopsBranchWork afterPremise
                then pure afterPremise
                else do
                    let conclusion = logicalViewOriginalValue conclusionView
                    conclusionStatement <-
                        signedStatement branchId SignFalse conclusion
                    conclusionReason <-
                        appendReason
                            branchId conclusionStatement
                            (ReasonFalseImplicationRight
                                premiseTerm conclusionTerm sourceReason)
                    admitCataloguedViewSignedFormula
                        globalType afterPremise SignFalse
                        conclusionView conclusionReason
        (_, LogicalView.LogicalEquality{}) -> pure branch
        (_, LogicalView.LogicalUniversal{}) -> pure branch
        (_, LogicalView.LogicalExistential{}) -> pure branch
        (_, LogicalView.LogicalNeutral) -> pure branch

-- Branch search yields after one agenda, equality, rule, or split transition.
-- Cursor-only returns run locally to that boundary; they cannot repeatedly
-- reconcile the request allowance without doing inference work. The continuation
-- retains successful children without capturing a recursive computation or
-- materializing either proof prematurely.
data BranchSearch global
    = SearchBranch !BranchState ![BranchContinuation global]
    | ResumeBranch !(BranchResult global) ![BranchContinuation global]
    | RefreshSplitParent !(SplitPlan global) !(BranchResult global) !(Maybe (BranchResult global))
        ![BranchContinuation global]
    | RefreshSplitRule !(SplitPlan global) !(BranchResult global) !(Maybe (BranchResult global))
        !(RuleSearch global) ![BranchContinuation global]
    | SearchRuleBranch !(RuleSearch global) ![BranchContinuation global]
    | SupportSplit !(SplitPlan global) !(BranchResult global) !(BranchResult global) ![BranchContinuation global]
    | SupportChildren !(SplitPlan global) !SupportSide !(ChildSupport global) !(ChildSupport global)
        ![BranchContinuation global]
    | ReturnBranch !(BranchResult global) ![BranchContinuation global]
    | FinishedBranch !(BranchResult global)

-- Retain the actual frontier and split history, including a closed sibling.
-- Reasons remain the only proof recipes; this tree owns resumable search state.
data BranchTree global
    = BranchLeaf !BranchState
    | BranchSplit !(SplitPlan global) !(BranchResult global) !(Maybe (BranchResult global))
    | BranchRule !(RuleSearch global) !(BranchTree global)

data BranchResult global
    = BranchClosed !ProofReasonId !(BranchTree global)
    | BranchOpen !(BranchTree global)

branchTreeId :: BranchTree global -> BranchId
branchTreeId = \case
    BranchLeaf branch -> branchStateId branch
    BranchRule pending _ -> branchStateId (ruleSearchBranch pending)
    BranchSplit (SplitPlan parent _source _kind _left _right) _leftResult _rightResult ->
        branchStateId parent

data SplitKind global
    = TrueDisjunction
    | FalseConjunction !(ScopedCheckedCore global)
    | TrueImplication !(ScopedCheckedCore global)

data SplitPlan global = SplitPlan
    !BranchState
    !ProofReasonId
    !(SplitKind global)
    !(Search.CataloguedLogicalView global)
    !(Search.CataloguedLogicalView global)

-- An ordinary closure is retained while either child can supply support. Each
-- advance runs one quantum of the same branch worker. A true limit stops that
-- child's route permanently; its ordinary certificate can still close the AND
-- if the sibling supplies canonical support. Infrastructure errors stay fatal.
data ChildSupport global
    = RunningChildSupport !(BranchResult global) !(BranchSearch global)
    | CompletedChildSupport !(BranchResult global)
    | StoppedChildSupport !(BranchResult global) !RefutationFailure

data SupportSide = SupportLeft | SupportRight

childSupportResult :: ChildSupport global -> BranchResult global
childSupportResult (RunningChildSupport result _) = result
childSupportResult (CompletedChildSupport result) = result
childSupportResult (StoppedChildSupport result _) = result

childSupportRunning :: ChildSupport global -> Bool
childSupportRunning RunningChildSupport{} = True
childSupportRunning _ = False

childSupportFailure :: ChildSupport global -> Maybe RefutationFailure
childSupportFailure (StoppedChildSupport _ failure) = Just failure
childSupportFailure _ = Nothing

advanceChildSupport
    :: Eq global => GlobalTyping global -> ChildSupport global -> Refute global (ChildSupport global)
advanceChildSupport typing current = case current of
    RunningChildSupport ordinary pending -> Except.catchE
        (advanceBranchSearch typing pending >>= \case
            FinishedBranch result@BranchClosed{} -> pure (CompletedChildSupport result)
            FinishedBranch BranchOpen{} -> Except.throwE
                (RefutationInternalFailure "a support worker lost its ordinary closure")
            next -> pure (RunningChildSupport ordinary next))
        (\failure -> if supportInfrastructureFailure failure then Except.throwE failure
            else pure (StoppedChildSupport ordinary failure))
    _ -> pure current

supportInfrastructureFailure :: RefutationFailure -> Bool
supportInfrastructureFailure = \case
    RefutationConversionFailed{} -> True
    RefutationRequiredConversionNotConvertible -> True
    RefutationConversionAccountingInvariant{} -> True
    RefutationIntegrityFailure{} -> True
    RefutationInternalFailure{} -> True
    _ -> False

data BranchContinuation global
    = AwaitLeft !(SplitPlan global) !(Maybe (BranchResult global))
    | AwaitRight !(SplitPlan global) !(BranchTree global) !ProofReasonId

splitParent :: SplitPlan global -> BranchState
splitParent (SplitPlan parent _source _kind _left _right) = parent

replaceSplitParent :: BranchState -> SplitPlan global -> SplitPlan global
replaceSplitParent parent (SplitPlan _old source kind left right) =
    SplitPlan parent source kind left right

branchTreeRoot :: BranchTree global -> BranchState
branchTreeRoot = \case
    BranchLeaf branch -> branch
    BranchRule pending _ -> ruleSearchBranch pending
    BranchSplit plan _left _right -> splitParent plan

-- Tracking requests retain the current bounded operation through its next
-- boundary after an ordinary closure. Only the demanded certificate can stop
-- it; a continuation holding later rule matches is not silently discarded.
branchAnyClosure :: BranchState -> Maybe ProofReasonId
branchAnyClosure branch = case branchClosureDemand branch of
    SeekCanonicalClosure ordinary -> Just ordinary
    _ -> Nothing

stopsBranchWork :: BranchState -> Bool
stopsBranchWork branch = case branchClosureDemand branch of
    RetainOrdinaryClosure -> False
    _ -> isJust (branchClosure branch)

retainsOrdinaryClosure :: BranchState -> Bool
retainsOrdinaryClosure branch = case branchClosureDemand branch of
    RetainOrdinaryClosure -> isJust (branchClosure branch)
    _ -> False

recordBranchClosure :: BranchState -> ProofReasonId -> Refute global BranchState
recordBranchClosure branch reason = case branchClosureDemand branch of
    UntrackedClosure -> pure branch {branchClosure = Just reason}
    RetainOrdinaryClosure -> case branchClosure branch of
        Nothing -> pure branch {branchClosure = Just reason}
        Just ordinary -> do
            when (ordinary /= reason) (aliasSupport (branchStateId branch) ordinary reason)
            pure branch
    SeekCanonicalClosure ordinary -> do
        when (ordinary /= reason) (aliasSupport (branchStateId branch) ordinary reason)
        supported <- canonicalReason (branchStateId branch) reason
        case supported of
            Just canonical -> do
                publishSupport (branchStateId branch) ordinary canonical
                pure branch {branchClosure = Just canonical}
            Nothing -> refreshBranchSupport branch

refreshBranchSupport :: BranchState -> Refute global BranchState
refreshBranchSupport branch = case branchAnyClosure branch of
    Nothing -> pure branch
    Just ordinary -> do
        supported <- canonicalReason (branchStateId branch) ordinary
        unless (isJust supported) (demandSupportFact (branchStateId branch) ordinary)
        pure branch {branchClosure = supported}

seekBranchSupport :: ProofReasonId -> BranchState -> BranchState
seekBranchSupport ordinary branch = branch
    { branchClosureDemand = SeekCanonicalClosure (fromMaybe ordinary (branchAnyClosure branch))
    , branchClosure = Nothing
    }

mapBranchRoot :: (BranchState -> BranchState) -> BranchTree global -> BranchTree global
mapBranchRoot change = \case
    BranchLeaf branch -> BranchLeaf (change branch)
    BranchRule pending tree -> BranchRule (mapRuleBranch change pending) (mapBranchRoot change tree)
    BranchSplit plan left right -> BranchSplit (replaceSplitParent (change (splitParent plan)) plan) left right

seekResultSupport :: BranchResult global -> BranchResult global
seekResultSupport = \case
    BranchClosed ordinary tree -> BranchClosed ordinary (mapBranchRoot (seekBranchSupport ordinary) tree)
    open@BranchOpen{} -> open

retainedBranch :: BranchTree global -> BranchResult global
retainedBranch tree = case branchClosure branch <|> branchAnyClosure branch of
    Nothing -> BranchOpen tree
    Just closure -> BranchClosed closure tree
  where
    branch = branchTreeRoot tree

-- A parent closure is valid in either child by proof-hypothesis weakening. It
-- supplies an ordinary child certificate without rebuilding the parent's proof.
inheritChildClosure :: BranchState -> BranchResult global -> BranchResult global
inheritChildClosure parent result = case (branchAnyClosure parent, result) of
    (Just ordinary, BranchOpen tree) -> BranchClosed ordinary
        (mapBranchRoot (\branch -> branch {branchClosure = Just ordinary}) tree)
    _ -> result

data BranchWork global
    = BranchWorkIdle !BranchState
    | BranchWorkAdvanced !BranchState
    | BranchWorkRule !(RuleSearch global)

-- Refreshing an existing split uses the same agenda/equality/rule transitions
-- as first entry, but never allocates a replacement for that split.
advanceBranchWork
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Refute global (BranchWork global)
advanceBranchWork globalType branch = case Seq.viewl (branchAgenda branch) of
    item Seq.:< rest ->
        BranchWorkAdvanced <$> processAgendaItem globalType branch {branchAgenda = rest} item
    Seq.EmptyL
        | Equality.equalityRefreshPending (branchEquality branch) ->
            BranchWorkAdvanced <$> processEqualityRefresh globalType branch
        | otherwise -> popRuleQueue branch >>= \case
            Just (item, withoutItem) -> pure (BranchWorkRule (startRuleSearch withoutItem item))
            Nothing -> pure (BranchWorkIdle branch)

advanceBranchSearch
    :: Eq global
    => GlobalTyping global
    -> BranchSearch global
    -> Refute global (BranchSearch global)
advanceBranchSearch globalType = \case
    complete@FinishedBranch{} -> pure complete
    ResumeBranch result continuations -> case result of
        BranchClosed _ tree | isJust (branchAnyClosure (branchTreeRoot tree)) -> resumeTree tree continuations
        BranchClosed{} -> advanceBranchSearch globalType (ReturnBranch result continuations)
        BranchOpen tree -> resumeTree tree continuations
    RefreshSplitRule plan left right pending continuations
        | retainsOrdinaryClosure (ruleSearchBranch pending)
        , Just closure <- branchClosure (ruleSearchBranch pending) ->
            pure (ReturnBranch (BranchClosed closure (BranchRule pending (BranchSplit plan left right))) continuations)
        | Just parent <- completedRuleState pending ->
            advanceBranchSearch globalType (RefreshSplitParent (replaceSplitParent parent plan) left right continuations)
    RefreshSplitRule plan left right pending continuations -> do
        advanced <- advanceRuleSearch globalType pending
        pure (RefreshSplitRule plan left right advanced continuations)
    RefreshSplitParent original left right continuations -> do
        parent <- refreshBranchSupport (splitParent original)
        let plan = replaceSplitParent parent original
        case branchClosure parent of
            Just closure -> advanceBranchSearch globalType
                (ReturnBranch (BranchClosed closure (BranchSplit plan left right)) continuations)
            Nothing -> advanceBranchWork globalType parent >>= \case
                BranchWorkAdvanced updated -> pure (RefreshSplitParent (replaceSplitParent updated plan) left right continuations)
                BranchWorkRule pending -> pure (RefreshSplitRule plan left right pending continuations)
                BranchWorkIdle idle -> do
                    let updated = replaceSplitParent idle plan
                        selectedLeft = inheritChildClosure idle left
                        selectedRight = inheritChildClosure idle <$> right
                    case (branchAnyClosure idle, selectedLeft, selectedRight) of
                        (Just _, BranchClosed{}, Just closed@BranchClosed{}) ->
                            pure (SupportSplit updated selectedLeft closed continuations)
                        _ -> case selectedLeft of
                            BranchOpen{} -> pure (ResumeBranch selectedLeft (AwaitLeft updated selectedRight : continuations))
                            BranchClosed closed leftTree -> do
                                let after = AwaitRight updated leftTree closed : continuations
                                case selectedRight of
                                    Just retained -> pure (ResumeBranch retained after)
                                    Nothing -> do
                                        fresh <- startRightBranch globalType updated
                                        pure (SearchBranch fresh after)
    SupportSplit original left right continuations -> do
        parent <- refreshBranchSupport (splitParent original)
        let plan = replaceSplitParent parent original
        case branchClosure parent of
            Just closure -> pure (ReturnBranch (BranchClosed closure (BranchSplit plan left (Just right))) continuations)
            Nothing -> pure (SupportChildren plan SupportLeft
                (RunningChildSupport left (ResumeBranch (seekResultSupport left) []))
                (RunningChildSupport right (ResumeBranch (seekResultSupport right) [])) continuations)
    SupportChildren plan side left right continuations -> do
        consumeWork
        let leftResult = childSupportResult left
            rightResult = childSupportResult right
        leftSupported <- supportedResult leftResult
        rightSupported <- if leftSupported then pure False else supportedResult rightResult
        sourceSupported <- case plan of
            SplitPlan parent source TrueDisjunction _ _ -> isJust <$> canonicalReason (branchStateId parent) source
            _ -> pure False
        if leftSupported || rightSupported || sourceSupported
            then completeSplit plan leftResult rightResult continuations
            else if not (childSupportRunning left || childSupportRunning right)
                then case childSupportFailure left <|> childSupportFailure right of
                    Just failure -> Except.throwE failure
                    Nothing -> completeSplit plan leftResult rightResult continuations
                else case side of
                    SupportLeft | childSupportRunning left -> do
                        next <- advanceChildSupport globalType left
                        pure (SupportChildren plan SupportRight next right continuations)
                    _ | childSupportRunning right -> do
                        next <- advanceChildSupport globalType right
                        pure (SupportChildren plan SupportLeft left next continuations)
                    _ -> do
                        next <- advanceChildSupport globalType left
                        pure (SupportChildren plan SupportRight next right continuations)
    SearchRuleBranch pending continuations
        | retainsOrdinaryClosure (ruleSearchBranch pending)
        , Just closure <- branchClosure (ruleSearchBranch pending) ->
            pure (ReturnBranch (BranchClosed closure (BranchRule pending (BranchLeaf (ruleSearchBranch pending)))) continuations)
        | Just branch <- completedRuleState pending ->
            advanceBranchSearch globalType (SearchBranch branch continuations)
    SearchRuleBranch pending continuations -> do
        advanced <- advanceRuleSearch globalType pending
        pure (SearchRuleBranch advanced continuations)
    ReturnBranch result [] -> pure (FinishedBranch result)
    ReturnBranch result (frame : rest) -> case (frame, result) of
        (AwaitLeft plan retainedRight, BranchClosed closed left) ->
            case retainedRight of
                Just right -> advanceBranchSearch globalType (ResumeBranch right (AwaitRight plan left closed : rest))
                Nothing -> do
                    right <- startRightBranch globalType plan
                    pure (SearchBranch right (AwaitRight plan left closed : rest))
        (AwaitLeft plan right, BranchOpen{}) ->
            advanceBranchSearch globalType (ReturnBranch (retainedBranch (BranchSplit plan result right)) rest)
        (AwaitRight plan left closedLeft, BranchClosed _closedRight _right) -> do
            let leftResult = BranchClosed closedLeft left
            if isJust (branchAnyClosure (splitParent plan))
                then pure (SupportSplit plan leftResult result rest)
                else completeSplit plan leftResult result rest
        (AwaitRight plan left closedLeft, BranchOpen{}) ->
            advanceBranchSearch globalType (ReturnBranch (retainedBranch
                (BranchSplit plan (BranchClosed closedLeft left) (Just result))) rest)
    SearchBranch initial continuations -> do
        branch <- refreshBranchSupport initial
        case branchClosure branch of
            Just closure -> advanceBranchSearch globalType (ReturnBranch (BranchClosed closure (BranchLeaf branch)) continuations)
            Nothing -> advanceBranchWork globalType branch >>= \case
                BranchWorkAdvanced next -> pure (SearchBranch next continuations)
                BranchWorkRule pending -> pure (SearchRuleBranch pending continuations)
                BranchWorkIdle idle -> advanceUniversal globalType idle >>= \case
                    Just updated -> pure (SearchBranch updated continuations)
                    Nothing -> finishIdle continuations idle
  where
    finishIdle continuations idle = case Seq.viewl (branchSplits idle) of
        Seq.EmptyL -> case Seq.viewl (branchSupportSplits idle) of
            Seq.EmptyL -> pure (ReturnBranch (retainedBranch (BranchLeaf idle)) continuations)
            split Seq.:< rest -> splitNow continuations
                idle {branchSupportSplits = rest, branchUniversalSinceSplit = False} split
        split Seq.:< rest -> do
            enabled <- State.gets stateBooleanPropagation
            let popped = idle {branchSplits = rest, branchUniversalSinceSplit = False}
            simplified <- if enabled then simplifySplit globalType popped split else pure Nothing
            case simplified of
                Nothing -> splitNow continuations popped split
                Just updated -> do
                    -- Logical redundancy alone cannot retire a live
                    -- canonical demand. Keep the original split as
                    -- a fallback, without repeating simplification.
                    let retained = case branchClosureDemand updated of
                            UntrackedClosure -> updated
                            _ -> updated {branchSupportSplits = branchSupportSplits updated Seq.|> split}
                    pure (SearchBranch retained continuations)
    splitNow continuations branch item = do
        (plan, left) <- startSplit globalType branch item
        pure (SearchBranch left (AwaitLeft plan Nothing : continuations))
    resumeTree (BranchRule pending tree) continuations = case tree of
        BranchLeaf{} -> pure (SearchRuleBranch pending continuations)
        BranchSplit plan left right -> pure (RefreshSplitRule plan left right pending continuations)
        BranchRule{} -> Except.throwE (RefutationInternalFailure "a retained rule frontier was wrapped twice")
    resumeTree (BranchLeaf branch) continuations = advanceBranchSearch globalType (SearchBranch branch continuations)
    resumeTree (BranchSplit plan left right) continuations =
        advanceBranchSearch globalType (RefreshSplitParent plan left right continuations)
    completeSplit plan left@(BranchClosed closedLeft leftTree) right@(BranchClosed closedRight rightTree) continuations = do
        combined <- finishSplit plan (branchTreeId leftTree) closedLeft (branchTreeId rightTree) closedRight
        parent <- recordBranchClosure (splitParent plan) combined
        pure (ReturnBranch (retainedBranch (BranchSplit (replaceSplitParent parent plan) left (Just right))) continuations)
    completeSplit _ _ _ _ = lostClosure
    supportedResult (BranchClosed reason tree) = isJust <$> canonicalReason (branchTreeId tree) reason
    supportedResult BranchOpen{} = pure False
    lostClosure = Except.throwE (RefutationInternalFailure "a support continuation lost a completed sibling")

-- One transition admits the same query-root reason in one retained branch.
-- A child consumes that reason only through the existing ancestry-aware proof
-- reconstruction; it never creates a new certified root in its own scope.
data InputPropagation global
    = VisitInputBranch !(BranchResult global) ![InputPropagationFrame global]
    | ReturnInputBranch !(BranchResult global) ![InputPropagationFrame global]
    | FinishedInputPropagation !(BranchResult global)

data InputPropagationFrame global
    = InputLeft !(Maybe ProofReasonId) !(SplitPlan global) !(Maybe (BranchResult global))
    | InputRight !(Maybe ProofReasonId) !(SplitPlan global) !(BranchResult global)
    | InputRule !(Maybe ProofReasonId) !(RuleSearch global)

advanceInputPropagation
    :: GlobalTyping global
    -> Search.CataloguedLogicalView global
    -> ProofReasonId
    -> InputPropagation global
    -> Refute global (InputPropagation global)
advanceInputPropagation globalType view reason = \case
    finished@FinishedInputPropagation{} -> pure finished
    VisitInputBranch result frames -> do
        consumeWork
        let (closure, tree) = case result of
                BranchClosed closed retained -> (Just closed, retained)
                BranchOpen retained -> (Nothing, retained)
        case tree of
            BranchRule pending retained -> pure (VisitInputBranch
                (retain closure (mapBranchRoot (const (ruleSearchBranch pending)) retained))
                (InputRule closure pending : frames))
            BranchLeaf branch -> do
                updated <- admit branch
                pure (ReturnInputBranch (retain (closure <|> branchClosure updated) (BranchLeaf updated)) frames)
            BranchSplit plan left right -> do
                updated <- admit (splitParent plan)
                pure (VisitInputBranch left
                    (InputLeft (closure <|> branchClosure updated) (replaceSplitParent updated plan) right : frames))
    ReturnInputBranch result [] -> pure (FinishedInputPropagation result)
    ReturnInputBranch result (frame : rest) -> case frame of
        InputRule closure pending -> do
            let tree = case result of
                    BranchClosed _ retained -> retained
                    BranchOpen retained -> retained
                updated = mapRuleBranch (const (branchTreeRoot tree)) pending
            pure (ReturnInputBranch (retain closure (BranchRule updated tree)) rest)
        InputLeft closure plan Nothing ->
            pure (ReturnInputBranch (retain closure (BranchSplit plan result Nothing)) rest)
        InputLeft closure plan (Just right) ->
            pure (VisitInputBranch right (InputRight closure plan result : rest))
        InputRight closure plan left ->
            pure (ReturnInputBranch (retain closure (BranchSplit plan left (Just result))) rest)
  where
    admit branch = admitCataloguedViewSignedFormula globalType branch SignTrue view reason
    retain Nothing = BranchOpen
    retain (Just closed) = BranchClosed closed

inputAlreadyVisible
    :: BranchTree global
    -> Search.ResolvedDerivedProposition global
    -> Refute global Bool
inputAlreadyVisible tree resolved = do
    consumeWork
    case resolvedRootExisting resolved of
        Nothing -> pure False
        Just root -> do
            formula <- State.gets (Map.lookup root . stateFormulaByTerm)
            pure (isJust (formula >>= \formulaId ->
                Map.lookup formulaId (branchMembership (branchTreeRoot tree))
                    >>= membershipTrueReason))

processEqualityRefresh
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Refute global BranchState
processEqualityRefresh globalType branch = do
    catalogue <- currentCatalogue
    (refreshed, requests) <-
        runEqualityOperation
            (\available ->
                Equality.refreshCongruence
                    available catalogue (branchEquality branch))
    updated <- processRequests (branch {branchEquality = refreshed}) (Seq.viewl requests)
    storeSupportEquality updated
    pure updated
  where
    processRequests current Seq.EmptyL = pure current
    processRequests current _requests
        | stopsBranchWork current = pure current
    processRequests current
            (Equality.CongruenceRequest
                leftId rightId functionPath argumentPath Seq.:< rest) = do
        functionReason <- appendEqualityPathReason functionPath current
        argumentReason <- appendEqualityPathReason argumentPath current
        left <- catalogueTermValue leftId
        right <- catalogueTermValue rightId
        equality <-
            scopedInBranch
                (branchStateId current)
                (CEq
                    (scopedCoreType left)
                    (scopedCoreTerm left)
                    (scopedCoreTerm right))
        reason <-
            appendReason
                (branchStateId current)
                equality
                (ReasonEqualityCongruence
                    functionReason argumentReason)
        admitted <-
            admitSignedFormula
                globalType current SignTrue equality reason
        processRequests admitted (Seq.viewl rest)

closeRuleTemplateWith
    :: Template.CompiledTemplate global
    -> PartialSubstitution
    -> Refute global (Template.TemplateClosure global)
closeRuleTemplateWith template substitutions = do
    prepared <-
        foldM addReplacement
            Template.emptyTemplateSubstitution
            (Map.toAscList (fst (Map.split
                (Template.MatcherSlot (Template.binderEnvironmentCount
                    (Template.compiledTemplateBinderEnvironment template)))
                substitutions)))
    runTemplateOperation
        (\work ->
            Template.closeTemplate work template prepared)
  where
    addReplacement current (slot, termId) = do
        value <- catalogueTermValue termId
        pure (Template.insertTemplateSubstitution slot value current)

closedTemplate
    :: Template.CompiledTemplate global
    -> PartialSubstitution
    -> Refute global (Maybe (ScopedCheckedCore global))
closedTemplate template substitutions =
    closeRuleTemplateWith template substitutions >>= \case
        Template.TemplateClosed closed -> pure (Just closed)
        Template.TemplateOpen{} -> pure Nothing

findCatalogueTermMaybe
    :: Eq global
    => ScopedCheckedCore global
    -> Refute global (Maybe Search.TermId)
findCatalogueTermMaybe candidate = do
    catalogue <- currentCatalogue
    work <- State.gets stateRemainingWork
    typeId <-
        applySearchResult
            (Search.findCatalogueTypeCounted
                work catalogue (scopedCoreType candidate)) >>= \case
            Nothing ->
                Except.throwE
                    (RefutationInternalFailure
                        "checked term type is absent from the frozen catalogue")
            Just found -> pure found
    afterType <- State.gets stateRemainingWork
    applySearchResult
        (Search.findCatalogueTermCounted afterType catalogue typeId
            (scopedCoreTerm candidate))

queryEquality
    :: BranchState
    -> Search.TermId
    -> Search.TermId
    -> Refute global (Maybe (Equality.EqualityPath ProofReasonId))
queryEquality branch left right = do
    catalogue <- currentCatalogue
    runEqualityOperation
        (\work ->
            Equality.equalityPath
                work catalogue (branchEquality branch) left right)

visibleTrueFacts
    :: BranchState
    -> Refute global
        [(Search.FormulaId, PreparedFormula global, ProofReasonId)]
visibleTrueFacts branch =
    fmap catMaybes
        (traverse prepare (Map.toAscList (branchMembership branch)))
  where
    prepare (formulaId, membership) =
        case membershipTrueReason membership of
            Nothing -> pure Nothing
            Just reason -> do
                formula <- lookupFormula formulaId
                pure (Just (formulaId, formula, reason))

matchTermPattern
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> PartialSubstitution
    -> Match.TermPattern global
    -> CanonicalTerm global
    -> Refute global (Maybe PartialSubstitution)
matchTermPattern globalType branch substitutions patternTerm candidate = do
    resolved <- patternSlotsResolved patternTerm substitutions
    direct <-
        if resolved
            then matchClosedPattern
            else pure Nothing
    case direct of
        Just matched -> pure (Just matched)
        Nothing -> matchStructurally resolved
  where
    matchClosedPattern = do
        target <-
            closedTemplate (Match.termPatternTemplate patternTerm)
                substitutions
        case target of
            Nothing ->
                Except.throwE
                    (RefutationInternalFailure
                        "resolved term pattern remained open")
            Just closed -> do
                targetId <- findCatalogueTermMaybe closed
                candidateScoped <-
                    scopedInBranch (branchStateId branch) candidate
                candidateId <- findCatalogueTermMaybe candidateScoped
                case (targetId, candidateId) of
                    (Just expected, Just actual) ->
                        queryEquality branch expected actual >>= \case
                            Just _path -> pure (Just substitutions)
                            Nothing -> pure Nothing
                    _ -> pure Nothing

    matchStructurally resolved =
        case Match.termPatternNode patternTerm of
            Match.PatternVariable slot -> do
                candidateScoped <-
                    scopedInBranch (branchStateId branch) candidate
                candidateId <- findCatalogueTermMaybe candidateScoped
                case candidateId of
                    Nothing -> pure Nothing
                    Just termId ->
                        case Map.lookup slot substitutions of
                            Nothing ->
                                pure
                                    (Just
                                        (Map.insert slot termId substitutions))
                            Just previous ->
                                queryEquality branch previous termId >>= \case
                                    Just _path -> pure (Just substitutions)
                                    Nothing -> pure Nothing
            Match.PatternRigid expectedHead arguments -> do
                (candidateHead, candidateArguments) <-
                    applicationSpine candidate
                sameHead <- rigidHeadMatches expectedHead candidateHead
                if not sameHead
                    then pure Nothing
                    else
                        matchTermArguments
                            globalType branch substitutions
                            arguments candidateArguments
            Match.PatternOpaqueGround
                | resolved -> pure Nothing
                | otherwise ->
                    Except.throwE
                        (RefutationInternalFailure
                            "opaque ground pattern retained matcher slots")

patternSlotsResolved
    :: Match.TermPattern global
    -> PartialSubstitution
    -> Refute other Bool
patternSlotsResolved patternTerm substitutions =
    allResolved (Set.toAscList (Match.termPatternSlots patternTerm))
  where
    allResolved [] = pure True
    allResolved (slot : rest) = do
        consumeWork
        if Map.member slot substitutions
            then allResolved rest
            else pure False

rigidHeadMatches
    :: Eq global
    => Match.RigidHead global
    -> CanonicalTerm global
    -> Refute other Bool
rigidHeadMatches expected candidate = do
    consumeWork
    pure
        (case (expected, candidate) of
            (Match.RigidGlobal left, CGlobal right) -> left == right
            (Match.RigidIntrinsic left, CIntrinsic right) -> left == right
            (Match.RigidOpaqueInteger left, COpaqueInteger right) ->
                left == right
            (Match.RigidAmbient left, CBound right) -> left == right
            _ -> False)

matchTermArguments
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> PartialSubstitution
    -> [Match.TermPattern global]
    -> [CanonicalTerm global]
    -> Refute global (Maybe PartialSubstitution)
matchTermArguments _globalType _branch substitutions [] [] =
    pure (Just substitutions)
matchTermArguments globalType branch substitutions
        (patternTerm : patterns) (candidate : candidates) =
    matchTermPattern
        globalType branch substitutions patternTerm candidate >>= \case
            Nothing -> pure Nothing
            Just updated ->
                matchTermArguments
                    globalType branch updated patterns candidates
matchTermArguments _globalType _branch _substitutions _patterns _candidates =
    pure Nothing

data PremiseMatchInput global = PremiseMatchInput
    !BranchId
    !(Match.CompiledPremise global)
    !PartialSubstitution
    !(Maybe (Search.ResolvedDerivedProposition global))
    !Search.FormulaId
    !(PreparedFormula global)
    !ProofReasonId

data PremiseMatchCursor global
    = BeginPremiseMatch !(PremiseMatchInput global)
    | ReversePremiseMatch !(PremiseMatchInput global)
        !(Match.TermPattern global) !(Match.TermPattern global)
        !(CanonicalTerm global) !(CanonicalTerm global)

data PremiseMatchStep global = PremiseMatchStep
    !(Maybe (PremiseCandidate global))
    !(Maybe (PremiseMatchCursor global))

-- A written equality candidate is returned before any reversed matching work.
-- The cursor retains the checked catalogue operands, so resumption performs no
-- duplicate lookup and cannot quietly switch to a different source occurrence.
advancePremiseMatch
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> PremiseMatchCursor global
    -> Refute global (PremiseMatchStep global)
advancePremiseMatch globalType branch cursor = do
    let input = case cursor of
            BeginPremiseMatch source -> source
            ReversePremiseMatch source _leftPattern _rightPattern _left _right -> source
        PremiseMatchInput owner premise substitutions preparedTarget formulaId fact reason = input
    unless (owner == branchStateId branch)
        (Except.throwE (RefutationInternalFailure "premise matching crossed a branch boundary"))
    case cursor of
        ReversePremiseMatch _source leftPattern rightPattern writtenLeft writtenRight -> do
            consumeWork
            reversed <- matchEqualityOrientation globalType branch premise substitutions preparedTarget
                formulaId fact reason Equality.EqualityReverse leftPattern rightPattern writtenRight writtenLeft
            pure (PremiseMatchStep reversed Nothing)
        BeginPremiseMatch{} -> case Match.compiledPremisePattern premise of
            Match.AtomicPremise expectedHead patterns -> case preparedFormulaNode fact of
                LogicalView.LogicalNeutral -> do
                    let candidateTerm = scopedCoreTerm (preparedFormulaValue fact)
                    (candidateHead, candidateArguments) <- applicationSpine candidateTerm
                    sameHead <- rigidHeadMatches expectedHead candidateHead
                    if not sameHead
                        then pure exhausted
                        else matchTermArguments globalType branch substitutions patterns candidateArguments >>= \case
                            Nothing -> pure exhausted
                            Just updated -> do
                                candidate <- finishAtomicCandidate globalType branch premise updated preparedTarget
                                    formulaId fact reason candidateArguments
                                pure (PremiseMatchStep candidate Nothing)
                _ -> pure exhausted
            Match.EqualityPremise operandTypeId leftPattern rightPattern ->
                case (preparedFormulaNode fact, preparedFormulaHeadRefs fact) of
                    (LogicalView.LogicalEquality{}, Search.EqualityRefs candidateTypeId writtenLeftId writtenRightId)
                        | candidateTypeId == operandTypeId -> do
                            writtenLeft <- scopedCoreTerm <$> catalogueTermValue writtenLeftId
                            writtenRight <- scopedCoreTerm <$> catalogueTermValue writtenRightId
                            consumeWork
                            written <- matchEqualityOrientation globalType branch premise substitutions preparedTarget
                                formulaId fact reason Equality.EqualityForward leftPattern rightPattern writtenLeft writtenRight
                            let remaining = if writtenLeftId == writtenRightId then Nothing else
                                    Just (ReversePremiseMatch input leftPattern rightPattern writtenLeft writtenRight)
                            pure (PremiseMatchStep written remaining)
                    _ -> pure exhausted
  where
    exhausted = PremiseMatchStep Nothing Nothing

-- Serial adapter for existing callers. The rule driver can retain the cursor
-- between consuming a candidate and attempting its remaining orientation.
matchPremiseAgainstFact
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Match.CompiledPremise global
    -> PartialSubstitution
    -> Maybe (Search.ResolvedDerivedProposition global)
    -> Search.FormulaId
    -> PreparedFormula global
    -> ProofReasonId
    -> (PremiseCandidate global -> state -> Refute global (CandidateControl state))
    -> state
    -> Refute global (CandidateControl state)
matchPremiseAgainstFact globalType branch premise substitutions preparedTarget
        formulaId fact reason consumeCandidate initial =
    drain initial (BeginPremiseMatch (PremiseMatchInput (branchStateId branch)
        premise substitutions preparedTarget formulaId fact reason))
  where
    drain current cursor = do
        PremiseMatchStep candidate remaining <- advancePremiseMatch globalType branch cursor
        consumed <- maybe (pure (ContinueCandidates current)) (`consumeCandidate` current) candidate
        case consumed of
            stopped@StopCandidates{} -> pure stopped
            ContinueCandidates updated -> maybe (pure (ContinueCandidates updated)) (drain updated) remaining

data DemandMatchCursor global
    = BeginDemandMatch !BranchId !(Match.PremisePattern global) !(PreparedFormula global)
    | ReverseDemandMatch !BranchId
        !(Match.TermPattern global) !(Match.TermPattern global)
        !(CanonicalTerm global) !(CanonicalTerm global)

advanceDemandMatch
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> DemandMatchCursor global
    -> Refute global (Maybe PartialSubstitution, Maybe (DemandMatchCursor global))
advanceDemandMatch globalType branch cursor = do
    let owner = case cursor of
            BeginDemandMatch source _pattern _demand -> source
            ReverseDemandMatch source _leftPattern _rightPattern _left _right -> source
    unless (owner == branchStateId branch)
        (Except.throwE (RefutationInternalFailure "demand matching crossed a branch boundary"))
    case cursor of
        ReverseDemandMatch _owner leftPattern rightPattern writtenLeft writtenRight -> do
            consumeWork
            reversed <- matchOrientation leftPattern rightPattern writtenRight writtenLeft
            pure (reversed, Nothing)
        BeginDemandMatch _owner premisePattern demand -> case premisePattern of
            Match.AtomicPremise expectedHead patterns -> case preparedFormulaNode demand of
                LogicalView.LogicalNeutral -> do
                    (candidateHead, candidateArguments) <- applicationSpine
                        (scopedCoreTerm (preparedFormulaValue demand))
                    sameHead <- rigidHeadMatches expectedHead candidateHead
                    if not sameHead then pure (Nothing, Nothing) else do
                        substitutions <- matchTermArguments globalType branch Map.empty patterns candidateArguments
                        pure (substitutions, Nothing)
                _ -> pure (Nothing, Nothing)
            Match.EqualityPremise operandTypeId leftPattern rightPattern ->
                case (preparedFormulaNode demand, preparedFormulaHeadRefs demand) of
                    (LogicalView.LogicalEquality{}, Search.EqualityRefs candidateTypeId writtenLeftId writtenRightId)
                        | candidateTypeId == operandTypeId -> do
                            writtenLeft <- scopedCoreTerm <$> catalogueTermValue writtenLeftId
                            writtenRight <- scopedCoreTerm <$> catalogueTermValue writtenRightId
                            consumeWork
                            written <- matchOrientation leftPattern rightPattern writtenLeft writtenRight
                            let remaining = if writtenLeftId == writtenRightId then Nothing else
                                    Just (ReverseDemandMatch owner leftPattern rightPattern writtenLeft writtenRight)
                            pure (written, remaining)
                    _ -> pure (Nothing, Nothing)
  where
    matchOrientation leftPattern rightPattern candidateLeft candidateRight =
        matchTermPattern globalType branch Map.empty leftPattern candidateLeft >>= \case
            Nothing -> pure Nothing
            Just afterLeft -> matchTermPattern globalType branch afterLeft rightPattern candidateRight

finishAtomicCandidate
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Match.CompiledPremise global
    -> PartialSubstitution
    -> Maybe (Search.ResolvedDerivedProposition global)
    -> Search.FormulaId
    -> PreparedFormula global
    -> ProofReasonId
    -> [CanonicalTerm global]
    -> Refute global (Maybe (PremiseCandidate global))
finishAtomicCandidate globalType branch premise substitutions preparedTarget
        formulaId fact reason candidateArguments = do
    selectedTarget <-
        case preparedTarget of
            Just prepared -> pure (Right prepared)
            Nothing ->
                closedTemplate (Match.compiledPremiseTemplate premise) substitutions
                    >>= \case
                        Nothing ->
                            Except.throwE
                                (RefutationInternalFailure
                                    "matched atomic premise remained open")
                        Just closed ->
                            prepareRequiredDerivedProposition
                                globalType closed
                                >>= \case
                                    Nothing -> pure (Left closed)
                                    Just prepared -> pure (Right prepared)
    case selectedTarget of
        Left outside ->
            pure
                (Just
                    (PremiseOutsideUniverse substitutions outside))
        Right target -> do
            let targetRoot = resolvedRootExisting target
                exact = targetRoot == Just (preparedFormulaRoot fact)
            if exact
                then
                    pure
                        (Just
                            (PremiseMatched substitutions
                                (WitnessExact formulaId reason)))
                else do
                    targetArguments <- resolvedApplicationArguments target
                    components <-
                        buildAtomicComponents
                            branch candidateArguments targetArguments
                    case components of
                        Nothing ->
                            Except.throwE
                                (RefutationInternalFailure
                                    "atomic witness changed arity after closure")
                        Just selected ->
                            pure
                                (Just
                                    (PremiseMatched substitutions
                                        (WitnessAtomic formulaId reason selected)))

resolvedApplicationArguments
    :: Search.ResolvedDerivedProposition global
    -> Refute global [Search.ResolvedTermRef]
resolvedApplicationArguments resolved = do
    catalogue <- currentCatalogue
    root <- requireResolvedRootRef resolved
    collect catalogue [] root
  where
    collect catalogue arguments reference = do
        consumeWork
        view <-
            maybe
                (Except.throwE
                    (RefutationInternalFailure
                        "resolved proposition references an unknown term row"))
                pure
                (Search.resolvedTermView catalogue resolved reference)
        case Search.resolvedTermViewApplication view of
            Nothing -> pure arguments
            Just (function, argument) ->
                collect catalogue (argument : arguments) function

buildAtomicComponents
    :: Eq global
    => BranchState
    -> [CanonicalTerm global]
    -> [Search.ResolvedTermRef]
    -> Refute global (Maybe [AtomicComponent])
buildAtomicComponents _branch [] [] = pure (Just [])
buildAtomicComponents branch (candidate : candidates) (target : targets) = do
    candidateScoped <- scopedInBranch (branchStateId branch) candidate
    candidateId <- findCatalogueTermMaybe candidateScoped
    let targetId = Search.resolvedTermExistingId target
    case (candidateId, targetId) of
        (Just actual, Just expected) ->
            queryEquality branch actual expected >>= \case
                Nothing -> pure Nothing
                Just path ->
                    buildAtomicComponents branch candidates targets >>= \case
                        Nothing -> pure Nothing
                        Just remaining ->
                            pure
                                (Just
                                    (AtomicComponent actual expected path
                                        : remaining))
        _ -> pure Nothing
buildAtomicComponents _branch _candidates _targets = pure Nothing

matchEqualityOrientation
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Match.CompiledPremise global
    -> PartialSubstitution
    -> Maybe (Search.ResolvedDerivedProposition global)
    -> Search.FormulaId
    -> PreparedFormula global
    -> ProofReasonId
    -> Equality.EqualityDirection
    -> Match.TermPattern global
    -> Match.TermPattern global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Refute global (Maybe (PremiseCandidate global))
matchEqualityOrientation globalType branch premise substitutions preparedTarget
        formulaId fact reason direction leftPattern rightPattern
        candidateLeft candidateRight =
    matchTermPattern
        globalType branch substitutions leftPattern candidateLeft >>= \case
            Nothing -> pure Nothing
            Just afterLeft ->
                matchTermPattern
                    globalType branch afterLeft rightPattern
                    candidateRight >>= \case
                        Nothing -> pure Nothing
                        Just updated -> do
                            closed <-
                                closedTemplate (Match.compiledPremiseTemplate premise)
                                    updated
                            case closed of
                                Nothing ->
                                    Except.throwE
                                        (RefutationInternalFailure
                                            "matched equality premise remained open")
                                Just target -> do
                                    selected <-
                                        case preparedTarget of
                                            Just prepared -> pure (Just prepared)
                                            Nothing ->
                                                prepareRequiredDerivedProposition
                                                    globalType target
                                    case selected of
                                        Nothing ->
                                            pure
                                                (Just
                                                    (PremiseOutsideUniverse
                                                        updated target))
                                        Just prepared ->
                                            let exact =
                                                    resolvedRootExisting
                                                        prepared
                                                        == Just
                                                            (preparedFormulaRoot fact)
                                            in if exact
                                                then
                                                    -- Equality premises have
                                                    -- the same exact-root fast
                                                    -- path as atomic premises;
                                                    -- do not rebuild an
                                                    -- identity endpoint path.
                                                    pure
                                                        (Just
                                                            (PremiseMatched updated
                                                                (WitnessExact
                                                                    formulaId reason)))
                                                else
                                                    buildEqualityWitness
                                                        branch updated prepared
                                                        formulaId reason direction
                                                        candidateLeft candidateRight

buildEqualityWitness
    :: Eq global
    => BranchState
    -> PartialSubstitution
    -> Search.ResolvedDerivedProposition global
    -> Search.FormulaId
    -> ProofReasonId
    -> Equality.EqualityDirection
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Refute global (Maybe (PremiseCandidate global))
buildEqualityWitness branch substitutions resolved
        formulaId reason direction candidateLeft candidateRight =
    case Search.resolvedDerivedHeadRefs resolved of
        Search.EqualityRefs _operandType targetLeftRef targetRightRef -> do
            candidateLeftScoped <-
                scopedInBranch (branchStateId branch) candidateLeft
            candidateRightScoped <-
                scopedInBranch (branchStateId branch) candidateRight
            let targetLeftId = Search.resolvedTermExistingId targetLeftRef
                targetRightId = Search.resolvedTermExistingId targetRightRef
            candidateLeftId <- findCatalogueTermMaybe candidateLeftScoped
            candidateRightId <- findCatalogueTermMaybe candidateRightScoped
            case (targetLeftId, targetRightId,
                    candidateLeftId, candidateRightId) of
                (Just desiredLeft, Just desiredRight,
                        Just selectedLeft, Just selectedRight) -> do
                    leftPath <-
                        queryEquality branch desiredLeft selectedLeft
                    rightPath <-
                        queryEquality branch selectedRight desiredRight
                    pure do
                        selectedLeftPath <- leftPath
                        selectedRightPath <- rightPath
                        pure
                            (PremiseMatched substitutions
                                (WitnessOpenEquality
                                    formulaId reason direction
                                    selectedLeftPath selectedRightPath))
                _ -> pure Nothing
        _ ->
            Except.throwE
                (RefutationInternalFailure
                    "equality premise closure lost its equality head")

queryClosedPremise
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> Match.CompiledPremise global
    -> PartialSubstitution
    -> Search.ResolvedDerivedProposition global
    -> Refute global (Maybe (PremiseCandidate global))
queryClosedPremise globalType branch premise substitutions resolved = do
    exactFormula <-
        case resolvedRootExisting resolved of
            Nothing -> pure Nothing
            Just termId ->
                State.gets (Map.lookup termId . stateFormulaByTerm)
    let exactWitness = do
            formulaId <- exactFormula
            membership <- Map.lookup formulaId (branchMembership branch)
            reason <- membershipTrueReason membership
            pure (formulaId, reason)
    case exactWitness of
        Just (formulaId, reason) ->
            pure
                (Just
                    (PremiseMatched substitutions
                        (WitnessExact formulaId reason)))
        Nothing ->
            case Match.compiledPremisePattern premise of
                Match.EqualityPremise{} ->
                    queryClosedEquality
                Match.AtomicPremise{} -> do
                    transported <- queryPropositionTransport
                    case transported of
                        Just witness ->
                            pure
                                (Just
                                    (PremiseMatched substitutions witness))
                        Nothing -> queryAtomicFacts
  where
    queryClosedEquality =
        case Search.resolvedDerivedHeadRefs resolved of
            Search.EqualityRefs _operandType leftRef rightRef -> do
                let leftId = Search.resolvedTermExistingId leftRef
                    rightId = Search.resolvedTermExistingId rightRef
                case (leftId, rightId) of
                    (Just source, Just destination) ->
                        queryEquality branch source destination >>= \case
                            Just path ->
                                pure
                                    (Just
                                        (PremiseMatched substitutions
                                            (WitnessDerivedEquality path)))
                            Nothing -> pure Nothing
                    _ -> pure Nothing
            _ ->
                Except.throwE
                    (RefutationInternalFailure
                        "closed equality query lost its equality head")

    queryPropositionTransport = do
        let targetId =
                resolvedRootExisting resolved
        case targetId of
            Nothing -> pure Nothing
            Just destination -> do
                facts <- visibleTrueFacts branch
                scanTransport destination facts

    scanTransport _destination [] = pure Nothing
    scanTransport destination ((formulaId, fact, reason) : rest) = do
        let source = preparedFormulaRoot fact
        queryEquality branch source destination >>= \case
            Just path ->
                pure
                    (Just
                        (WitnessPropositionTransport
                            formulaId reason path))
            Nothing -> scanTransport destination rest

    queryAtomicFacts = do
        facts <- visibleTrueFacts branch
        scanFacts Nothing facts

    scanFacts firstOutside [] = pure firstOutside
    scanFacts firstOutside
            ((formulaId, fact, reason) : rest) = do
        result <-
            matchPremiseAgainstFact
                globalType branch premise substitutions
                (Just resolved) formulaId fact reason
                selectCandidate
                firstOutside
        case result of
            StopCandidates selected -> pure selected
            ContinueCandidates selected -> scanFacts selected rest

    selectCandidate matched@PremiseMatched{} _current =
        pure (StopCandidates (Just matched))
    selectCandidate outside@PremiseOutsideUniverse{} current =
        pure (ContinueCandidates (current <|> Just outside))

ruleQueueKey :: RuleQueueItem -> RuleQueueKey
ruleQueueKey = \case
    RuleActivationItem branch ruleId ->
        RuleActivationKey branch ruleId
    RuleTriggerItem triggerKey ->
        RuleTriggerQueueKey triggerKey
    RuleProjectionItem branch source position -> RuleProjectionKey branch source position

-- This complete priority intentionally selects the next rule. The ordered map
-- preserves the former sorted sequence's order and also supplies queue membership;
-- insertion no longer walks or charges a reconstructed linear prefix.
ruleQueuePriority :: RuleQueueItem -> (Int, RuleQueueKey)
ruleQueuePriority item =
    (kind, ruleQueueKey item)
  where
    kind =
        case item of
            RuleActivationItem{} -> 0
            RuleTriggerItem
                    (RuleTriggerKey
                        _branch _generation _rule RuleStart
                        FormulaTrigger{}) -> 1
            RuleTriggerItem
                    (RuleTriggerKey
                        _branch _generation _rule RuleStart
                        DemandTrigger{}) -> 2
            RuleTriggerItem{} -> 3
            RuleProjectionItem{} -> 4

foldSeqMCounted
    :: (value -> item -> Refute global value)
    -> value
    -> Seq item
    -> Refute global value
foldSeqMCounted step initial items = go initial items
  where
    go current pending =
        case Seq.viewl pending of
            Seq.EmptyL -> pure current
            item Seq.:< rest -> do
                consumeWork
                updated <- step current item
                go updated rest

enqueueRuleActivation
    :: BranchState
    -> RuleId
    -> Refute global BranchState
enqueueRuleActivation branch ruleId = do
    let branchId = branchStateId branch
        item = RuleActivationItem branchId ruleId
        key = ruleQueueKey item
    if key `Set.member` branchRuleActivations branch
        then pure branch
        else do
            consumeWork
            pure
                branch
                    { branchRuleActivations =
                        Set.insert key (branchRuleActivations branch)
                    , branchRuleQueue = Map.insert (ruleQueuePriority item) item (branchRuleQueue branch)
                    }

enqueueRuleTrigger
    :: BranchState
    -> RuleTriggerKey
    -> Refute global BranchState
enqueueRuleTrigger branch triggerKey = do
    let item = RuleTriggerItem triggerKey
        priority = ruleQueuePriority item
    if triggerKey `Set.member` branchRuleTriggers branch
            || Map.member priority (branchRuleQueue branch)
        then pure branch
        else do
            consumeWork
            pure
                branch
                    { branchRuleTriggers =
                        Set.insert triggerKey (branchRuleTriggers branch)
                    , branchRuleQueue = Map.insert priority item (branchRuleQueue branch)
                    }

enqueueRuleProjection :: BranchState -> RuleProjectionSource -> Int -> Refute global BranchState
enqueueRuleProjection branch source position = do
    consumeWork
    let item = RuleProjectionItem (branchStateId branch) source position
    pure branch {branchRuleQueue = Map.insert (ruleQueuePriority item) item (branchRuleQueue branch)}

popRuleQueue
    :: BranchState
    -> Refute global (Maybe (RuleQueueItem, BranchState))
popRuleQueue branch =
    case Map.minView (branchRuleQueue branch) of
        Nothing -> pure Nothing
        Just (item, rest) -> do
            consumeWork
            pure
                (Just
                    ( item
                    , branch { branchRuleQueue = rest }
                    ))

installActiveRule
    :: BranchState
    -> RuleId
    -> ActiveRuleWitness
    -> Refute global BranchState
installActiveRule branch ruleId witness =
    case Map.lookup ruleId (branchActiveRules branch) of
        Just _firstWitness -> pure branch
        Nothing -> do
            consumeWork
            enqueueRuleActivation
                branch
                    { branchActiveRules =
                        Map.insert ruleId witness
                            (branchActiveRules branch)
                    }
                ruleId

enqueueBaseTrigger
    :: BranchState
    -> RuleId
    -> RuleMatchState
    -> RuleTrigger
    -> Refute global BranchState
enqueueBaseTrigger branch ruleId matchState trigger =
    enqueueRuleTrigger branch
        (RuleTriggerKey
            (branchStateId branch) BaseTrigger
            ruleId matchState trigger)

enqueueRetryTrigger
    :: EqualityMergeId
    -> BranchState
    -> RuleId
    -> RuleMatchState
    -> RuleTrigger
    -> Refute global BranchState
enqueueRetryTrigger mergeId branch ruleId matchState trigger =
    enqueueRuleTrigger branch
        (RuleTriggerKey
            (branchStateId branch) (EqualityRetry mergeId)
            ruleId matchState trigger)

notifyFormulaVisibility
    :: BranchState
    -> Search.FormulaId
    -> Refute global BranchState
notifyFormulaVisibility branch formulaId = do
    afterStarts <-
        foldM notifyStart branch
            (Map.toAscList (branchActiveRules branch))
    foldSeqMCounted notifyPartial afterStarts
        (branchPartialOrder branch)
  where
    notifyStart current (ruleId, _witness) = do
        (_sourceFormula, rule) <- lookupCompiledRule ruleId
        if Seq.null (Match.compiledRulePremises rule)
            then pure current
            else
                enqueueBaseTrigger current ruleId RuleStart
                    (FormulaTrigger formulaId)

    notifyPartial current partialKey =
        if partialKey `Map.member` branchPartialMatches current
            then
                case partialKey of
                    PartialMatchKey _origin ruleId _premise _substitution ->
                        enqueueBaseTrigger current ruleId
                            (RulePartial partialKey)
                            (FormulaTrigger formulaId)
            else pure current

notifyDemandVisibility
    :: BranchState
    -> DemandKey
    -> Refute global BranchState
notifyDemandVisibility branch demandKey =
    foldM notify branch (Map.toAscList (branchActiveRules branch))
  where
    notify current (ruleId, _witness) = do
        (_sourceFormula, rule) <- lookupCompiledRule ruleId
        if Seq.null (Match.compiledRulePremises rule)
            then
                enqueueBaseTrigger current ruleId RuleStart
                    (DemandTrigger demandKey)
            else pure current

visibleTrueFormulaIds
    :: BranchState
    -> Refute global [Search.FormulaId]
visibleTrueFormulaIds branch =
    collect (Map.toAscList (branchMembership branch))
  where
    collect [] = pure []
    collect ((formulaId, membership) : rest) = do
        consumeWork
        remaining <- collect rest
        pure
            (case membershipTrueReason membership of
                Nothing -> remaining
                Just _reason -> formulaId : remaining)

enqueueEqualityRetry
    :: BranchState
    -> Refute global BranchState
enqueueEqualityRetry branch = do
    let mergeId = EqualityMergeId (branchNextEqualityMerge branch)
        withMerge =
            branch
                { branchNextEqualityMerge =
                    branchNextEqualityMerge branch + 1
                }
    formulas <- visibleTrueFormulaIds withMerge
    afterStarts <-
        foldM (retryStart mergeId formulas) withMerge
            (Map.toAscList (branchActiveRules withMerge))
    afterPartials <-
        foldSeqMCounted (retryPartial mergeId formulas) afterStarts
            (branchPartialOrder afterStarts)
    foldSeqMCounted (retryDemand mergeId) afterPartials
        (branchDemandOrder afterPartials)
  where
    retryStart mergeId formulas current (ruleId, _witness) = do
        (_sourceFormula, rule) <- lookupCompiledRule ruleId
        if Seq.null (Match.compiledRulePremises rule)
            then pure current
            else
                foldM
                    (\next formulaId ->
                        enqueueRetryTrigger mergeId next ruleId RuleStart
                            (FormulaTrigger formulaId))
                    current formulas

    retryPartial mergeId formulas current partialKey =
        case Map.lookup partialKey (branchPartialMatches current) of
            Nothing -> pure current
            Just _partial ->
                case partialKey of
                    PartialMatchKey _origin ruleId _premise _substitution ->
                        do
                            afterFacts <-
                                foldM
                                    (\next formulaId ->
                                        enqueueRetryTrigger
                                            mergeId next ruleId
                                            (RulePartial partialKey)
                                            (FormulaTrigger formulaId))
                                    current formulas
                            foldSeqMCounted
                                (retryPartialDemand
                                    mergeId ruleId partialKey)
                                afterFacts
                                (branchDemandOrder afterFacts)

    retryPartialDemand mergeId ruleId partialKey current demandKey =
        case demandKey of
            DemandKey _origin
                    (DemandFromPartial sourcePartial) _formulaId
                | sourcePartial == partialKey ->
                    enqueueRetryTrigger mergeId current ruleId
                        (RulePartial partialKey)
                        (DemandTrigger demandKey)
            _ -> pure current

    retryDemand mergeId current demandKey =
        foldM (retryZeroRule mergeId demandKey) current
            (Map.toAscList (branchActiveRules current))

    retryZeroRule mergeId demandKey current (ruleId, _witness) = do
        (_sourceFormula, rule) <- lookupCompiledRule ruleId
        if Seq.null (Match.compiledRulePremises rule)
            then
                enqueueRetryTrigger mergeId current ruleId RuleStart
                    (DemandTrigger demandKey)
            else pure current

findDemand
    :: DemandSource
    -> Search.FormulaId
    -> BranchState
    -> Refute global (Maybe DemandKey)
findDemand source formulaId branch =
    scan (Seq.viewl (branchDemandOrder branch))
  where
    scan Seq.EmptyL = pure Nothing
    scan (key@(DemandKey _origin foundSource foundFormula) Seq.:< rest) = do
        consumeWork
        if foundSource == source && foundFormula == formulaId
                && key `Set.member` branchDemands branch
            then pure (Just key)
            else scan (Seq.viewl rest)

retainDemand
    :: BranchState
    -> DemandSource
    -> Search.FormulaId
    -> Refute global BranchState
retainDemand branch source formulaId =
    findDemand source formulaId branch >>= \case
        Just _existing -> pure branch
        Nothing -> do
            consumeWork
            let key = DemandKey (branchStateId branch) source formulaId
                retained =
                    branch
                        { branchDemands =
                            Set.insert key (branchDemands branch)
                        , branchDemandOrder =
                            branchDemandOrder branch Seq.|> key
                        }
            notifyDemandVisibility retained key

retainFormulaDemand
    :: BranchState
    -> Search.FormulaId
    -> Refute global BranchState
retainFormulaDemand branch formulaId =
    retainDemand branch (DemandFromFormula formulaId) formulaId

preparePartialDemand
    :: GlobalTyping global
    -> BranchState
    -> PartialMatchKey
    -> Search.ResolvedDerivedProposition global
    -> Refute global BranchState
preparePartialDemand _globalType branch partialKey resolved = do
    originalFormulas <- State.gets stateFormulas
    originalFormulaByTerm <- State.gets stateFormulaByTerm
    originalCatalogue <- State.gets stateCatalogue
    originalTermCount <- State.gets stateTermCount
    Except.catchE prepare
        (\failure -> do
            -- Fuel remains consumed, but no unsigned demand preparation is
            -- published unless its FormulaId, proposition root, demand, and
            -- notifications all succeed.
            State.modify'
                (\state ->
                    state
                        { stateFormulas = originalFormulas
                        , stateFormulaByTerm = originalFormulaByTerm
                        , stateCatalogue = originalCatalogue
                        , stateTermCount = originalTermCount
                        })
            Except.throwE failure)
  where
    prepare = do
        (_prepared, formulaId) <- finishResolvedFormula resolved
        retainDemand branch (DemandFromPartial partialKey) formulaId

substitutionPayload
    :: Match.CompiledRule global
    -> PartialSubstitution
    -> Refute other [Maybe Search.TermId]
substitutionPayload rule substitutions =
    go (0 :: Int)
        (Seq.viewl
            (Template.binderEnvironmentSourceTypes
                (Match.compiledRuleBinderEnvironment rule)))
  where
    go _position Seq.EmptyL = pure []
    go position (_binderType Seq.:< rest) = do
        consumeWork
        remaining <- go (position + 1) (Seq.viewl rest)
        pure
            (Map.lookup
                (Template.MatcherSlot (fromIntegral position))
                substitutions
                : remaining)

findMatcherSubstitution
    :: RuleId
    -> [Maybe Search.TermId]
    -> Refute global (Maybe MatcherSubstitutionId)
findMatcherSubstitution ruleId candidate = do
    consumeWork
    index <- State.gets (Map.lookup ruleId . stateSubstitutionIndex)
    maybe (pure Nothing) (walk candidate) index
  where
    walk payload (MatcherSubstitutionTrie terminal children) = do
        consumeWork
        case payload of
            [] -> pure terminal
            term : rest -> maybe (pure Nothing) (walk rest) (Map.lookup term children)

insertMatcherSubstitution
    :: MatcherSubstitutionId
    -> [Maybe Search.TermId]
    -> MatcherSubstitutionTrie
    -> Refute global MatcherSubstitutionTrie
insertMatcherSubstitution substitutionId = walk
  where
    walk payload (MatcherSubstitutionTrie terminal children) = do
        consumeWork
        case payload of
            [] -> do
                when (isJust terminal)
                    (Except.throwE (RefutationInternalFailure
                        "fresh matcher substitution already has an ID"))
                pure (MatcherSubstitutionTrie (Just substitutionId) children)
            term : rest -> do
                child <- walk rest (Map.findWithDefault emptyMatcherSubstitutionTrie term children)
                pure (MatcherSubstitutionTrie terminal (Map.insert term child children))

prepareMatcherSubstitution
    :: RuleId
    -> [Maybe Search.TermId]
    -> Refute global ProspectiveMatcherSubstitution
prepareMatcherSubstitution ruleId payload =
    findMatcherSubstitution ruleId payload >>= \case
        Just substitutionId ->
            pure (ExistingMatcherSubstitution substitutionId)
        Nothing -> do
            rows <- State.gets stateSubstitutions
            pure
                (FreshMatcherSubstitution
                    (MatcherSubstitutionId (Seq.length rows))
                    ruleId payload)

prospectiveSubstitutionId
    :: ProspectiveMatcherSubstitution
    -> MatcherSubstitutionId
prospectiveSubstitutionId = \case
    ExistingMatcherSubstitution substitutionId -> substitutionId
    FreshMatcherSubstitution substitutionId _ruleId _payload ->
        substitutionId

commitMatcherSubstitution
    :: ProspectiveMatcherSubstitution
    -> Refute global MatcherSubstitutionId
commitMatcherSubstitution prospective =
    case prospective of
        ExistingMatcherSubstitution substitutionId -> pure substitutionId
        FreshMatcherSubstitution substitutionId@(MatcherSubstitutionId position)
                ruleId payload -> do
            consumeWork
            rows <- State.gets stateSubstitutions
            unless (position == Seq.length rows)
                (Except.throwE
                    (RefutationInternalFailure
                        "prospective matcher-substitution ID became stale"))
            index <- State.gets (Map.findWithDefault emptyMatcherSubstitutionTrie ruleId . stateSubstitutionIndex)
            updatedIndex <- insertMatcherSubstitution substitutionId payload index
            State.modify'
                (\state ->
                    state
                        { stateSubstitutions =
                            stateSubstitutions state
                                Seq.|> MatcherSubstitution ruleId payload
                        , stateSubstitutionIndex =
                            Map.insert ruleId updatedIndex (stateSubstitutionIndex state)
                        })
            pure substitutionId

lookupMatcherSubstitution
    :: RuleId
    -> MatcherSubstitutionId
    -> Refute global [Maybe Search.TermId]
lookupMatcherSubstitution expectedRule (MatcherSubstitutionId position) = do
    consumeWork
    rows <- State.gets stateSubstitutions
    case Seq.lookup position rows of
        Just (MatcherSubstitution foundRule payload)
            | foundRule == expectedRule -> pure payload
        _ ->
            Except.throwE
                (RefutationInternalFailure
                    "matcher substitution belongs to another rule")

restorePartialSubstitution
    :: Match.CompiledRule global
    -> [Maybe Search.TermId]
    -> Refute other PartialSubstitution
restorePartialSubstitution rule payload =
    go (0 :: Int) payload
        (Seq.viewl
            (Template.binderEnvironmentSourceTypes
                (Match.compiledRuleBinderEnvironment rule)))
        Map.empty
  where
    go _position [] Seq.EmptyL substitutions = pure substitutions
    go position (maybeTerm : rest) (_binderType Seq.:< binderRest)
            substitutions = do
        consumeWork
        let updated =
                case maybeTerm of
                    Nothing -> substitutions
                    Just termId ->
                        Map.insert
                            (Template.MatcherSlot (fromIntegral position))
                            termId substitutions
        go (position + 1) rest (Seq.viewl binderRest) updated
    go _position _payload _binders _substitutions =
        Except.throwE
            (RefutationInternalFailure
                "rule substitution has the wrong arity")

findVisibleInstance
    :: RuleId
    -> MatcherSubstitutionId
    -> BranchState
    -> Refute global (Maybe InstanceKey)
findVisibleInstance ruleId substitutionId branch =
    findInheritedKey (branchStateId branch)
        (\origin -> InstanceKey origin ruleId substitutionId)
        (`Map.member` branchRuleInstances branch)

findVisiblePartial
    :: RuleId
    -> PremiseIx
    -> MatcherSubstitutionId
    -> BranchState
    -> Refute global (Maybe PartialMatchKey)
findVisiblePartial ruleId premiseIx substitutionId branch =
    findInheritedKey (branchStateId branch)
        (\origin -> PartialMatchKey origin ruleId premiseIx substitutionId)
        (`Map.member` branchPartialMatches branch)

findTerminalRuleRejection
    :: RuleId
    -> RuleRejectionSite
    -> MatcherSubstitutionId
    -> BranchState
    -> Refute global (Maybe TerminalRuleRejectionKey)
findTerminalRuleRejection ruleId site substitutionId branch =
    findInheritedKey (branchStateId branch)
        (\origin -> TerminalRuleRejectionKey origin ruleId site substitutionId)
        (`Set.member` branchTerminalRejections branch)

-- Visible rule state belongs to this branch or its ancestors. Query the
-- branch's retained snapshot, never a parent's subsequently extended state.
-- Oldest-first lookup preserves the previous scans' choice of inherited keys.
findInheritedKey
    :: BranchId
    -> (BranchId -> key)
    -> (key -> Bool)
    -> Refute global (Maybe key)
findInheritedKey owner makeKey contains = do
    info <- lookupBranch owner
    inherited <- maybe (pure Nothing)
        (\parent -> findInheritedKey parent makeKey contains) (branchParent info)
    case inherited of
        Just key -> pure (Just key)
        Nothing -> do
            consumeWork
            let key = makeKey owner
            pure (if contains key then Just key else Nothing)

terminalRejectionPresent
    :: Match.CompiledRule global
    -> RuleId
    -> RuleRejectionSite
    -> PartialSubstitution
    -> BranchState
    -> Refute global Bool
terminalRejectionPresent rule ruleId site substitutions branch = do
    payload <- substitutionPayload rule substitutions
    prospective <- prepareMatcherSubstitution ruleId payload
    isJust <$>
        findTerminalRuleRejection
            ruleId site (prospectiveSubstitutionId prospective) branch

-- Queued partial matches already name their interned substitution. Do not
-- reconstruct and re-intern it just to query the terminal rejection set.
terminalMatchRejectionPresent
    :: Match.CompiledRule global
    -> RuleId
    -> RuleRejectionSite
    -> RuleMatchState
    -> BranchState
    -> Refute global Bool
terminalMatchRejectionPresent rule ruleId site matchState branch =
    case matchState of
        RuleStart -> terminalRejectionPresent rule ruleId site Map.empty branch
        RulePartial (PartialMatchKey _origin _rule _premise substitutionId) ->
            isJust <$> findTerminalRuleRejection ruleId site substitutionId branch

retainTerminalRejection
    :: Match.CompiledRule global
    -> RuleId
    -> RuleRejectionSite
    -> PartialSubstitution
    -> ScopedCheckedCore global
    -> BranchState
    -> Refute global BranchState
retainTerminalRejection rule ruleId site substitutions rejected branch = do
    payload <- substitutionPayload rule substitutions
    prospective <- prepareMatcherSubstitution ruleId payload
    let substitutionId = prospectiveSubstitutionId prospective
    findTerminalRuleRejection ruleId site substitutionId branch >>= \case
        Just _existing -> pure branch
        Nothing -> do
            consumeWork
            committed <- commitMatcherSubstitution prospective
            unless (committed == substitutionId)
                (Except.throwE
                    (RefutationInternalFailure
                        "terminal rejection changed substitution identity"))
            let key =
                    TerminalRuleRejectionKey
                        (branchStateId branch) ruleId site substitutionId
            State.modify'
                (\state ->
                    state
                        { stateTerminalRejectionPayloads =
                            Map.insertWith
                                (\_new first -> first)
                                key rejected
                                (stateTerminalRejectionPayloads state)
                        })
            pure
                branch
                    { branchTerminalRejections =
                        Set.insert key (branchTerminalRejections branch)
                    }

chargePremiseWitnessPayload
    :: PremiseWitness
    -> Refute global ()
chargePremiseWitnessPayload witness = do
    consumeWork
    case witness of
        WitnessExact{} -> pure ()
        WitnessPropositionTransport _formula _reason path ->
            chargePath path
        WitnessAtomic _formula _reason components ->
            chargeComponents components
        WitnessOpenEquality
                _formula _reason _direction left right -> do
            chargePath left
            chargePath right
        WitnessDerivedEquality path -> chargePath path
  where
    chargeComponents [] = pure ()
    chargeComponents (AtomicComponent _source _target path : rest) = do
        consumeWork
        chargePath path
        chargeComponents rest

    chargePath path = chargeSteps (Equality.equalityPathSteps path)

    chargeSteps [] = pure ()
    chargeSteps (_step : rest) = do
        consumeWork
        chargeSteps rest

retainPartialMatch
    :: Match.CompiledRule global
    -> RuleId
    -> PremiseIx
    -> ActiveRuleWitness
    -> PartialSubstitution
    -> ReverseWitnessSpine
    -> Maybe PremiseWitness
    -> BranchState
    -> Refute global (BranchState, Maybe PartialMatchKey)
retainPartialMatch rule ruleId premiseIx active substitutions spine
        newWitness branch = do
    payload <- substitutionPayload rule substitutions
    prospective <- prepareMatcherSubstitution ruleId payload
    let substitutionId = prospectiveSubstitutionId prospective
    findVisiblePartial ruleId premiseIx substitutionId branch >>= \case
        Just _existing -> pure (branch, Nothing)
        Nothing -> do
            traverse_ chargePremiseWitnessPayload newWitness
            consumeWork
            committed <- commitMatcherSubstitution prospective
            unless (committed == substitutionId)
                (Except.throwE
                    (RefutationInternalFailure
                        "partial match changed substitution identity"))
            let key =
                    PartialMatchKey
                        (branchStateId branch) ruleId premiseIx substitutionId
                retained = RetainedPartialMatch active spine
            pure
                ( branch
                    { branchPartialMatches =
                        Map.insert key retained
                            (branchPartialMatches branch)
                    , branchPartialOrder =
                        branchPartialOrder branch Seq.|> key
                    }
                , Just key
                )

rulePremiseAt
    :: Int
    -> Seq (Match.CompiledPremise global)
    -> Refute other (Maybe (Match.CompiledPremise global))
rulePremiseAt wanted steps = scan wanted (Seq.viewl steps)
  where
    scan _wanted Seq.EmptyL = pure Nothing
    scan remaining
            (premise Seq.:< rest) = do
        consumeWork
        if remaining == 0
            then pure (Just premise)
            else scan (remaining - 1) (Seq.viewl rest)

loadRuleMatchState
    :: RuleId
    -> RuleMatchState
    -> BranchState
    -> Refute global
        ( ActiveRuleWitness
        , Int
        , PartialSubstitution
        , ReverseWitnessSpine
        )
loadRuleMatchState ruleId matchState branch =
    case matchState of
        RuleStart -> do
            active <-
                maybe
                    (Except.throwE
                        (RefutationInternalFailure
                            "rule-start event has no active witness"))
                    pure
                    (Map.lookup ruleId (branchActiveRules branch))
            pure (active, 0, Map.empty, EmptyWitnessSpine)
        RulePartial key@(PartialMatchKey
                _origin foundRule (PremiseIx position) substitutionId) -> do
            unless (foundRule == ruleId)
                (Except.throwE
                    (RefutationInternalFailure
                        "partial-match event names another rule"))
            RetainedPartialMatch active spine <-
                maybe
                    (Except.throwE
                        (RefutationInternalFailure
                            "rule event names an unknown partial match"))
                    pure
                    (Map.lookup key (branchPartialMatches branch))
            (_sourceFormula, rule) <- lookupCompiledRule ruleId
            payload <- lookupMatcherSubstitution ruleId substitutionId
            substitutions <- restorePartialSubstitution rule payload
            pure (active, position, substitutions, spine)

witnessFormulaId :: PremiseWitness -> Maybe Search.FormulaId
witnessFormulaId = \case
    WitnessExact formulaId _reason -> Just formulaId
    WitnessPropositionTransport formulaId _reason _path -> Just formulaId
    WitnessAtomic formulaId _reason _components -> Just formulaId
    WitnessOpenEquality formulaId _reason _direction _left _right ->
        Just formulaId
    WitnessDerivedEquality{} -> Nothing

retainConsumedBaseTrigger
    :: BranchState
    -> RuleId
    -> RuleMatchState
    -> Search.FormulaId
    -> Refute global BranchState
retainConsumedBaseTrigger branch ruleId matchState formulaId = do
    let key =
            RuleTriggerKey
                (branchStateId branch) BaseTrigger ruleId matchState
                (FormulaTrigger formulaId)
    if key `Set.member` branchRuleTriggers branch
        then pure branch
        else do
            consumeWork
            pure
                branch
                    { branchRuleTriggers =
                        Set.insert key (branchRuleTriggers branch)
                    }

enqueueVisibleFormulaTriggers
    :: BranchState
    -> RuleId
    -> RuleMatchState
    -> Maybe Search.FormulaId
    -> Refute global BranchState
enqueueVisibleFormulaTriggers branch ruleId matchState selected = do
    formulas <- visibleTrueFormulaIds branch
    foldM enqueue branch formulas
  where
    enqueue current formulaId
        | Just formulaId == selected =
            retainConsumedBaseTrigger
                current ruleId matchState formulaId
        | otherwise =
            enqueueBaseTrigger current ruleId matchState
                (FormulaTrigger formulaId)


ensureDemandState
    :: Match.CompiledRule global
    -> RuleId
    -> RuleMatchState
    -> ActiveRuleWitness
    -> Int
    -> PartialSubstitution
    -> ReverseWitnessSpine
    -> BranchState
    -> Refute global (BranchState, PartialMatchKey)
ensureDemandState rule ruleId matchState active position substitutions spine
        branch =
    case matchState of
        RulePartial key -> pure (branch, key)
        RuleStart -> do
            (retained, fresh) <-
                retainPartialMatch
                    rule ruleId (PremiseIx position) active
                    substitutions spine Nothing branch
            key <-
                case fresh of
                    Just created -> pure created
                    Nothing -> do
                        payload <- substitutionPayload rule substitutions
                        prospective <- prepareMatcherSubstitution ruleId payload
                        findVisiblePartial
                            ruleId (PremiseIx position)
                            (prospectiveSubstitutionId prospective) retained
                            >>= maybe
                                (Except.throwE
                                    (RefutationInternalFailure
                                        "duplicate demand state disappeared"))
                                pure
            pure (retained, key)

beginRuleMatch
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> RuleId
    -> RuleMatchState
    -> Refute global (BranchState, [RuleTask global])
beginRuleMatch globalType branch ruleId matchState = do
    (sourceFormula, rule) <- lookupCompiledRule ruleId
    (active, position, substitutions, spine) <- loadRuleMatchState ruleId matchState branch
    let site = RejectedPremise (PremiseIx position)
        application = RuleApplication ruleId sourceFormula rule active position spine
    rejected <- terminalMatchRejectionPresent rule ruleId site matchState branch
    if rejected then pure (branch, []) else do
        premise <- rulePremiseAt position (Match.compiledRulePremises rule) >>= maybe
            (Except.throwE (RefutationInternalFailure "nonzero rule state has no next premise")) pure
        closeRuleTemplateWith (Match.compiledPremiseTemplate premise) substitutions >>= \case
            Template.TemplateOpen{} -> done
                (enqueueVisibleFormulaTriggers branch ruleId matchState Nothing)
            Template.TemplateClosed target -> prepareRequiredDerivedProposition globalType target >>= \case
                Nothing -> done (retainTerminalRejection rule ruleId site substitutions target branch)
                Just targetEvidence -> queryClosedPremise globalType branch premise substitutions targetEvidence >>= \case
                    Nothing -> do
                        (retained, partialKey) <- ensureDemandState rule ruleId matchState active
                            position substitutions spine branch
                        done (preparePartialDemand globalType retained partialKey targetEvidence)
                    Just (PremiseOutsideUniverse rejectedSubstitution rejectedTarget) -> done
                        (retainTerminalRejection rule ruleId site rejectedSubstitution rejectedTarget branch)
                    Just (PremiseMatched updated witness) -> do
                        withSelection <- maybe (pure branch)
                            (retainConsumedBaseTrigger branch ruleId matchState) (witnessFormulaId witness)
                        pure (withSelection,
                            [ SelectRuleWitness application updated witness
                            , EnqueueFollowingFormulas ruleId matchState (witnessFormulaId witness)
                            ])
  where
    done operation = (\updated -> (updated, [])) <$> operation

beginRuleFormula
    :: BranchState
    -> RuleId
    -> RuleMatchState
    -> Search.FormulaId
    -> Refute global (BranchState, [RuleTask global])
beginRuleFormula branch ruleId matchState formulaId = do
    (sourceFormula, rule) <- lookupCompiledRule ruleId
    (active, position, substitutions, spine) <- loadRuleMatchState ruleId matchState branch
    rejected <- terminalMatchRejectionPresent rule ruleId (RejectedPremise (PremiseIx position)) matchState branch
    if rejected then pure (branch, []) else do
        premise <- rulePremiseAt position (Match.compiledRulePremises rule) >>= maybe
            (Except.throwE (RefutationInternalFailure "formula trigger reached a complete rule state")) pure
        membership <- maybe
            (Except.throwE (RefutationInternalFailure "formula trigger names an unknown branch formula")) pure
            (Map.lookup formulaId (branchMembership branch))
        reason <- maybe
            (Except.throwE (RefutationInternalFailure "formula trigger names a non-true formula")) pure
            (membershipTrueReason membership)
        fact <- lookupFormula formulaId
        let application = RuleApplication ruleId sourceFormula rule active position spine
            input = PremiseMatchInput (branchStateId branch) premise substitutions Nothing formulaId fact reason
        pure (branch, [ContinueRulePremises branch application (BeginPremiseMatch input)])

appendRuleInstanceReason
    :: BranchId
    -> ScopedCheckedCore global
    -> RuleId
    -> Search.FormulaId
    -> ProofReasonId
    -> MatcherSubstitutionId
    -> Int
    -> ReverseWitnessSpine
    -> Refute global ProofReasonId
appendRuleInstanceReason branch statement ruleId sourceFormula sourceReason
        substitutionId premiseCount spine = do
    consumeWork
    reasons <- State.gets stateReasons
    let next = Seq.length reasons
    initial <- stageReasonPredecessor next Seq.empty sourceReason
    (witnesses, predecessors) <-
        stageSpine next (premiseCount - 1) spine Seq.empty initial
    let reason =
            ReasonRuleInstance
                ruleId sourceFormula sourceReason substitutionId witnesses
        reasonId = ProofReasonId next
    State.modify'
        (\state ->
            state
                { stateReasons =
                    stateReasons state
                        Seq.|> ReasonEntry
                            branch statement predecessors reason
                })
    registerSupportReason branch reasonId predecessors reason
    pure reasonId
  where
    stageSpine _next expected EmptyWitnessSpine witnesses predecessors
        | expected == -1 = pure (witnesses, predecessors)
        | otherwise =
            Except.throwE
                (RefutationInternalFailure
                    "completed rule witness spine is too short")
    stageSpine next expected
            (WitnessSpineCons (PremiseIx actual) witness rest)
            witnesses predecessors = do
        unless (actual == expected)
            (Except.throwE
                (RefutationInternalFailure
                    "completed rule witness positions are not decreasing"))
        withWitness <-
            stagePremiseWitnessPredecessors next predecessors witness
        stageSpine next (expected - 1) rest
            (witness Seq.<| witnesses) withWitness

completeRuleInstance
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> RuleId
    -> Search.FormulaId
    -> Match.CompiledRule global
    -> ActiveRuleWitness
    -> PartialSubstitution
    -> ReverseWitnessSpine
    -> Int
    -> Refute global (CandidateControl BranchState)
completeRuleInstance globalType branch ruleId sourceFormula rule
        (ActiveRuleWitness activeFormula sourceReason)
        substitutions witnessSpine premiseCount = do
    unless (activeFormula == sourceFormula)
        (Except.throwE
            (RefutationInternalFailure
                "active rule witness cites another source formula"))
    payload <- substitutionPayload rule substitutions
    firstMissing 0 payload >>= \case
        Just missing -> do
            State.modify'
                (\state ->
                    state
                        { stateUndeterminedParameter =
                            stateUndeterminedParameter state
                                <|> Just missing
                        })
            StopCandidates <$> startRuleContinuation branch ruleId rule
        Nothing -> continue payload
  where
    firstMissing _position [] = pure Nothing
    firstMissing position (term : rest) = do
        consumeWork
        if isNothing term
            then pure (Just position)
            else firstMissing (position + 1) rest

    continue payload = do
        prospective <- prepareMatcherSubstitution ruleId payload
        let substitutionId = prospectiveSubstitutionId prospective
        findVisibleInstance ruleId substitutionId branch >>= \case
            Just _existing -> pure (ContinueCandidates branch)
            Nothing -> do
                rejected <-
                    findTerminalRuleRejection
                        ruleId RejectedConclusion substitutionId branch
                case rejected of
                    Just _terminal -> pure (ContinueCandidates branch)
                    Nothing -> do
                        created <- State.gets stateRuleInstanceCount
                        limit <- State.gets stateRuleInstanceLimit
                        when (created >= limit)
                            (Except.throwE RefutationRuleInstancesExhausted)
                        committed <- commitMatcherSubstitution prospective
                        unless (committed == substitutionId)
                            (Except.throwE
                                (RefutationInternalFailure
                                    "completed instance changed substitution identity"))
                        conclusion <-
                            closedTemplate (Match.compiledRuleResultTemplate rule)
                                substitutions >>= \case
                                    Just closed -> pure closed
                                    Nothing ->
                                        Except.throwE
                                            (RefutationInternalFailure
                                                "complete rule conclusion remained open")
                        preparedConclusion <-
                            prepareRequiredDerivedProposition
                                globalType conclusion
                        case preparedConclusion of
                            Nothing -> do
                                retained <- retainTerminalRejection
                                    rule ruleId RejectedConclusion
                                    substitutions conclusion branch
                                ContinueCandidates <$> startRuleContinuation retained ruleId rule
                            Just conclusionEvidence -> do
                                reason <-
                                    appendRuleInstanceReason
                                        (branchStateId branch) conclusion
                                        ruleId sourceFormula sourceReason
                                        substitutionId premiseCount
                                        witnessSpine
                                admitted <-
                                    admitPreparedDerivedSignedFormula
                                        globalType branch SignTrue
                                        conclusionEvidence reason
                                State.modify'
                                    (\state ->
                                        state
                                            { stateRuleInstanceCount =
                                                stateRuleInstanceCount state + 1
                                            })
                                let key =
                                        InstanceKey
                                            (branchStateId branch)
                                            ruleId substitutionId
                                    published =
                                        admitted
                                            { branchRuleInstances =
                                                Map.insert key reason
                                                    (branchRuleInstances admitted)
                                            }
                                pure
                                    (if stopsBranchWork published
                                        then StopCandidates published
                                        else ContinueCandidates published)

-- A rule continuation retains the actual source and consumed witness spine.
-- Returning a new task never recursively advances another premise or instance.
data RuleApplication global = RuleApplication
    !RuleId !Search.FormulaId !(Match.CompiledRule global)
    !ActiveRuleWitness !Int !ReverseWitnessSpine

data RuleTask global
    = ActivateRuleTask !BranchId !RuleId
    | DiscoverRuleProjection !BranchId !RuleProjectionSource !Int
    | TriggerRuleTask !RuleTriggerKey
    | AdvanceRuleMatch !RuleId !RuleMatchState
    | ContinueRulePremises !BranchState !(RuleApplication global) !(PremiseMatchCursor global)
    | ContinueRuleDemands !BranchState !(RuleApplication global) !(DemandMatchCursor global)
    | SelectRuleWitness !(RuleApplication global) !PartialSubstitution !PremiseWitness
    | CompleteRuleTask !(RuleApplication global) !PartialSubstitution !ReverseWitnessSpine !Int
    | EnqueueFollowingFormulas !RuleId !RuleMatchState !(Maybe Search.FormulaId)

data RuleSearch global
    = SearchRule !BranchState ![RuleTask global]
    | FinishedRule !BranchState

ruleSearchBranch :: RuleSearch global -> BranchState
ruleSearchBranch (SearchRule branch _) = branch
ruleSearchBranch (FinishedRule branch) = branch

mapRuleBranch :: (BranchState -> BranchState) -> RuleSearch global -> RuleSearch global
mapRuleBranch change (SearchRule branch tasks) = SearchRule (change branch) tasks
mapRuleBranch change (FinishedRule branch) = FinishedRule (change branch)

completedRuleState :: RuleSearch global -> Maybe BranchState
completedRuleState = \case
    FinishedRule branch -> Just branch
    SearchRule branch tasks
        | null tasks || stopsBranchWork branch -> Just branch
        | otherwise -> Nothing

startRuleSearch :: BranchState -> RuleQueueItem -> RuleSearch global
startRuleSearch branch item = SearchRule branch [case item of
    RuleActivationItem owner ruleId -> ActivateRuleTask owner ruleId
    RuleTriggerItem key -> TriggerRuleTask key
    RuleProjectionItem owner source position -> DiscoverRuleProjection owner source position]

advanceRuleSearch
    :: Eq global
    => GlobalTyping global
    -> RuleSearch global
    -> Refute global (RuleSearch global)
advanceRuleSearch globalType = \case
    finished@FinishedRule{} -> pure finished
    SearchRule branch tasks -> do
        refreshed <- refreshBranchSupport branch
        if stopsBranchWork refreshed then pure (FinishedRule refreshed) else case tasks of
            [] -> pure (FinishedRule refreshed)
            task : rest -> advanceRuleTask globalType refreshed task >>= \case
                finished@FinishedRule{} -> pure finished
                SearchRule updated following -> pure (SearchRule updated (following <> rest))

advanceRuleTask
    :: Eq global
    => GlobalTyping global
    -> BranchState
    -> RuleTask global
    -> Refute global (RuleSearch global)
advanceRuleTask globalType branch = \case
    DiscoverRuleProjection owner source position -> do
        unless (owner == branchStateId branch)
            (Except.throwE (RefutationInternalFailure "rule projection discovery crossed a branch boundary"))
        done (advanceRuleProjection globalType branch source position)
    ActivateRuleTask owner ruleId -> do
        unless (owner == branchStateId branch)
            (Except.throwE (RefutationInternalFailure "rule activation crossed a branch boundary"))
        (_sourceFormula, rule) <- lookupCompiledRule ruleId
        if Seq.null (Match.compiledRulePremises rule)
            then done (foldSeqMCounted
                (\current demandKey -> enqueueBaseTrigger current ruleId RuleStart (DemandTrigger demandKey))
                branch (branchDemandOrder branch))
            else continue (branch, [AdvanceRuleMatch ruleId RuleStart])
    TriggerRuleTask (RuleTriggerKey owner _generation ruleId matchState trigger) -> do
        unless (owner == branchStateId branch)
            (Except.throwE (RefutationInternalFailure "rule trigger crossed a branch boundary"))
        case (matchState, trigger) of
            (RuleStart, DemandTrigger demandKey)
                | Set.notMember demandKey (branchDemands branch) -> continue (branch, [])
                | otherwise -> do
                    (sourceFormula, rule) <- lookupCompiledRule ruleId
                    active <- maybe
                        (Except.throwE (RefutationInternalFailure "demand trigger has no active rule")) pure
                        (Map.lookup ruleId (branchActiveRules branch))
                    demandPattern <- maybe
                        (Except.throwE (RefutationInternalFailure "zero-premise rule lacks a demand pattern")) pure
                        (Match.compiledRuleDemandPattern rule)
                    let DemandKey _origin _source formulaId = demandKey
                    demand <- lookupFormula formulaId
                    let application = RuleApplication ruleId sourceFormula rule active 0 EmptyWitnessSpine
                    continue (branch, [ContinueRuleDemands branch application
                        (BeginDemandMatch owner demandPattern demand)])
            (RulePartial partialKey, DemandTrigger demandKey) -> case demandKey of
                DemandKey _origin (DemandFromPartial source) _formulaId
                    | source == partialKey -> continue (branch, [AdvanceRuleMatch ruleId matchState])
                _ -> continue (branch, [])
            (_, FormulaTrigger formulaId) ->
                uncurry SearchRule <$> beginRuleFormula branch ruleId matchState formulaId
    AdvanceRuleMatch ruleId matchState ->
        uncurry SearchRule <$> beginRuleMatch globalType branch ruleId matchState
    ContinueRulePremises snapshot application@(RuleApplication ruleId _source rule _active position _spine) cursor -> do
        PremiseMatchStep candidate remaining <- advancePremiseMatch globalType snapshot cursor
        let following = maybe [] (\next -> [ContinueRulePremises snapshot application next]) remaining
            site = RejectedPremise (PremiseIx position)
        case candidate of
            Nothing -> continue (branch, following)
            Just (PremiseOutsideUniverse substitutions rejected) -> do
                retained <- retainTerminalRejection rule ruleId site substitutions rejected branch
                continue (retained, following)
            Just (PremiseMatched substitutions witness) -> do
                rejected <- terminalRejectionPresent rule ruleId site substitutions branch
                continue (branch, if rejected then following else SelectRuleWitness application substitutions witness : following)
    ContinueRuleDemands snapshot application cursor -> do
        (substitutions, remaining) <- advanceDemandMatch globalType snapshot cursor
        let following = maybe [] (\next -> [ContinueRuleDemands snapshot application next]) remaining
        continue (branch, maybe following (\selected -> CompleteRuleTask application selected EmptyWitnessSpine 0 : following) substitutions)
    SelectRuleWitness application@(RuleApplication ruleId _source rule active position spine) substitutions witness -> do
        let nextPosition = position + 1
            extended = WitnessSpineCons (PremiseIx position) witness spine
        rulePremiseAt nextPosition (Match.compiledRulePremises rule) >>= \case
            Nothing -> continue (branch, [CompleteRuleTask application substitutions extended nextPosition])
            Just _nextPremise -> do
                (retained, fresh) <- retainPartialMatch rule ruleId (PremiseIx nextPosition) active
                    substitutions extended (Just witness) branch
                continue (retained, maybe [] (\key -> [AdvanceRuleMatch ruleId (RulePartial key)]) fresh)
    CompleteRuleTask (RuleApplication ruleId source rule active _position _spine) substitutions selected count -> do
        completed <- completeRuleInstance globalType branch ruleId source rule active substitutions selected count
        pure case completed of
            StopCandidates updated -> FinishedRule updated
            ContinueCandidates updated -> SearchRule updated []
    EnqueueFollowingFormulas ruleId matchState selected -> done
        (enqueueVisibleFormulaTriggers branch ruleId matchState selected)
  where
    continue = pure . uncurry SearchRule
    done operation = (\updated -> SearchRule updated []) <$> operation

advanceRuleProjection
    :: GlobalTyping global
    -> BranchState
    -> RuleProjectionSource
    -> Int
    -> Refute global BranchState
advanceRuleProjection globalType branch source position = do
    consumeWork
    cached <- State.gets (Map.lookup source . stateRuleProjections)
    case cached of
        Just (rules, compilation) -> case Seq.lookup position rules of
            Just ruleId -> activate ruleId
            Nothing | position /= Seq.length rules -> malformed "rule projection cursor skipped a view"
            Nothing -> case compilation of
                ProjectionComplete coverage -> finishCoverage coverage
                ProjectionCompiling cursor -> do
                    catalogue <- currentCatalogue
                    progress <- runMatchOperation (\work ->
                        Match.advanceRuleProjections globalType work catalogue cursor)
                    case progress of
                        Match.RuleProjectionPending following -> do
                            retain rules (ProjectionCompiling following)
                            enqueueRuleProjection branch source position
                        Match.RuleProjectionFinished coverage -> do
                            retain rules (ProjectionComplete coverage)
                            finishCoverage coverage
                        Match.RuleProjectionFound compiled following -> do
                            consumeWork
                            formulaId <- sourceFormula
                            allRules <- State.gets stateRules
                            let ruleId = RuleId (Seq.length allRules)
                            State.modify' (\state -> state
                                {stateRules = allRules Seq.|> CompiledRule ruleId formulaId compiled})
                            retain (rules Seq.|> ruleId) (ProjectionCompiling following)
                            activate ruleId
        _ -> malformed "rule projection discovery lost its source schema"
  where
    retain rules compilation = do
        consumeWork
        State.modify' (\state -> state
            {stateRuleProjections = Map.insert source (rules, compilation) (stateRuleProjections state)})
    finishCoverage Match.FullRuleCoverage = pure branch
    finishCoverage Match.PartialRuleCoverage = State.gets stateUniversals >>= \case
        UniversalsDisabled -> pure branch
        _ -> do
            formulaId <- sourceFormula
            prepared <- lookupFormula formulaId
            enrollUniversal formulaId prepared branch
    sourceFormula = case source of
        SourceProjection formulaId -> pure formulaId
        RuleContinuation parent -> fst <$> lookupCompiledRule parent
    activate ruleId = do
        formulaId <- sourceFormula
        sourceReason <- maybe (malformed "rule projection lost its positive source") pure
            (Map.lookup formulaId (branchMembership branch) >>= membershipTrueReason)
        active <- installActiveRule branch ruleId (ActiveRuleWitness formulaId sourceReason)
        enqueueRuleProjection active source (position + 1)
    malformed = Except.throwE . RefutationInternalFailure

-- A successfully admitted structured result is classified as an ordinary
-- source and shares its subsequent work. A rejected intermediate must still
-- permit a deeper selected result, whose replay may contain out-of-domain
-- intermediate syntax. Discovery is shared; activation remains branch-local.
startRuleContinuation
    :: BranchState
    -> RuleId
    -> Match.CompiledRule global
    -> Refute global BranchState
startRuleContinuation branch ruleId rule = case Match.compiledRuleContinuation rule of
    Nothing -> pure branch
    Just cursor -> do
        consumeWork
        if Set.member ruleId (branchRuleContinuations branch) then pure branch else do
            let source = RuleContinuation ruleId
            State.modify' (\state -> state
                { stateRuleProjections = Map.insertWith (\_new existing -> existing)
                    source (Seq.empty, ProjectionCompiling cursor) (stateRuleProjections state) })
            enqueueRuleProjection
                branch {branchRuleContinuations = Set.insert ruleId (branchRuleContinuations branch)} source 0

-- Enroll only after exact grammar coverage is known. Retaining exhausted
-- cursors also prevents a later source/support event from restarting a scan.
enrollUniversal
    :: Search.FormulaId -> PreparedFormula global -> BranchState
    -> Refute global BranchState
enrollUniversal source prepared branch = State.gets stateUniversals >>= \case
    UniversalsDisabled -> pure branch
    policy -> case preparedFormulaNode prepared of
        LogicalView.LogicalUniversal TySet _ -> do
            consumeWork
            if Map.member source (branchUniversalSources branch) then pure branch else do
                inventory <- universalInventory
                pure branch
                    { branchUniversalSources = Map.insert source inventory (branchUniversalSources branch)
                    , branchUniversalQueue = branchUniversalQueue branch Seq.|> source
                    , branchUniversalHintQueue = case policy of
                        HintedUniversals attempts turns | attempts > 0 && turns > 0 ->
                            branchUniversalHintQueue branch Seq.|> source
                        _ -> branchUniversalHintQueue branch
                    }
        _ -> pure branch

-- One immutable starting cursor per query. The original frozen catalogue,
-- rather than its later proposition rows, owns every argument in this stream.
universalInventory :: Refute global Search.CatalogueTypeTerms
universalInventory = State.gets stateUniversalInventory >>= \case
    Just inventory -> pure inventory
    Nothing -> do
        domain <- State.gets stateFrozenDomain >>= maybe
            (Except.throwE (RefutationInternalFailure "universal enumeration has no frozen domain")) pure
        let catalogue = frozenDomainCatalogue domain
        work <- State.gets stateRemainingWork
        typeId <- applySearchResult (Search.findCatalogueTypeCounted work catalogue TySet) >>= maybe
            (Except.throwE (RefutationInternalFailure "a universal's binder type is absent from its catalogue")) pure
        afterType <- State.gets stateRemainingWork
        inventory <- applySearchResult (Search.catalogueTypeTermsCounted afterType catalogue typeId)
        State.modify' (\state -> state {stateUniversalInventory = Just inventory})
        pure inventory

-- Disabled and depleted policies retain no extra event history. A signed
-- truth is appended once; reason replacement and canonical upgrades are not
-- new events. Child branches inherit the existing prefix and append privately.
retainUniversalHintEvent
    :: Sign -> Search.FormulaId -> PreparedFormula global -> BranchState
    -> Refute global BranchState
retainUniversalHintEvent sign formula prepared branch = State.gets stateUniversals >>= \case
    HintedUniversals attempts turns | attempts > 0 && turns > 0 -> case preparedFormulaNode prepared of
        LogicalView.LogicalNeutral -> retain
        LogicalView.LogicalEquality{} -> retain
        _ -> pure branch
    _ -> pure branch
  where
    retain = do
        consumeWork
        pure branch {branchUniversalHintEvents = branchUniversalHintEvents branch Seq.|> AgendaItem sign formula}

-- Ordinary work and the existing pre-split turn still surround every actual
-- instance. At most four hint turns precede a fallback turn, even across yields
-- or source arrivals. Hint selection has its own round-robin queue, so its
-- streak cannot bias fallback and new sources join behind waiting sources.
advanceUniversal
    :: Eq global
    => GlobalTyping global -> BranchState -> Refute global (Maybe BranchState)
advanceUniversal globalType branch
    | branchUniversalSinceSplit branch
    , not (Seq.null (branchSplits branch) && Seq.null (branchSupportSplits branch)) = pure Nothing
    | otherwise = case Seq.viewl (branchUniversalQueue branch) of
        Seq.EmptyL -> pure Nothing
        source Seq.:< rest -> do
            policy <- State.gets stateUniversals
            case policy of
                HintedUniversals attempts turns
                    | attempts > 0 && turns > 0 && branchUniversalHintStreak branch < 4 -> do
                        (hintSource, hintRest) <- case Seq.viewl (branchUniversalHintQueue branch) of
                            Seq.EmptyL -> Except.throwE (RefutationInternalFailure "universal hints lost their eligible sources")
                            selected Seq.:< following -> pure (selected, following)
                        (advanced, candidate) <- advanceUniversalHint globalType hintSource branch
                        let hinted = advanced
                                { branchUniversalHintQueue = hintRest Seq.|> hintSource
                                , branchUniversalHintStreak = branchUniversalHintStreak branch + 1 }
                        maybe (pure (Just hinted)) (attemptUniversal globalType hinted hintSource) candidate
                _ -> fallback source rest
  where
    fallback source rest = do
        consumeWork
        cursor <- maybe (Except.throwE (RefutationInternalFailure "universal queue lost its cursor")) pure
            (Map.lookup source (branchUniversalSources branch))
        work <- State.gets stateRemainingWork
        next <- applySearchResult (Search.nextCatalogueTypeTermCounted work cursor)
        case next of
            Nothing -> pure (Just branch {branchUniversalQueue = rest, branchUniversalHintStreak = 0})
            Just (argument, following) -> do
                let advanced = branch
                        { branchUniversalSources = Map.insert source following (branchUniversalSources branch)
                        , branchUniversalQueue = rest Seq.|> source
                        , branchUniversalHintStreak = 0 }
                attemptUniversal globalType advanced source argument

-- Both candidate producers pass through this one pair/allowance owner. Hints
-- cannot duplicate an instance debit or turn a signed match into proof support.
attemptUniversal
    :: Eq global
    => GlobalTyping global -> BranchState -> Search.FormulaId -> Search.TermId
    -> Refute global (Maybe BranchState)
attemptUniversal globalType branch source argument = do
    consumeWork
    let pair = (source, argument)
    if Set.member pair (branchUniversalAttempts branch) then pure (Just branch) else do
        policy <- State.gets stateUniversals
        case policy of
            UniversalsDisabled -> Except.throwE
                (RefutationInternalFailure "disabled universal enumeration retained work")
            ExistingUniversals 0 -> stopped
            HintedUniversals 0 _ -> stopped
            ExistingUniversals remaining -> instantiate (ExistingUniversals (remaining - 1))
            HintedUniversals remaining turns -> instantiate (HintedUniversals (remaining - 1) turns)
  where
    stopped = do
        State.modify' (\state -> state {stateUniversalsDeferred = True})
        pure Nothing
    instantiate following = do
        State.modify' (\state -> state
            { stateUniversals = following
            , stateUniversalAttempts = stateUniversalAttempts state + 1 })
        let attempted = branch
                { branchUniversalAttempts = Set.insert (source, argument) (branchUniversalAttempts branch)
                , branchUniversalSinceSplit = True }
        Just <$> instantiateUniversal globalType attempted source argument

-- A turn compiles one syntax node/leaf or examines one leaf/event pair. The
-- small breadth allowance includes stale and unsuitable events, while the
-- compiler and matcher charge their full structural work independently.
advanceUniversalHint
    :: Eq global
    => GlobalTyping global -> Search.FormulaId -> BranchState
    -> Refute global (BranchState, Maybe Search.TermId)
advanceUniversalHint globalType source branch = do
    consumeWork
    State.gets stateUniversals >>= \case
        HintedUniversals attempts turns | attempts > 0 && turns > 0 ->
            State.modify' (\state -> state
                { stateUniversals = HintedUniversals attempts (turns - 1)
                , stateUniversalHintSteps = stateUniversalHintSteps state + 1 })
        _ -> Except.throwE (RefutationInternalFailure "a hint turn ran without its allowance")
    schemas <- State.gets stateUniversalHintSchemas
    UniversalHintSchema compilation hints <- case Map.lookup source schemas of
        Just retained -> pure retained
        Nothing -> do
            prepared <- lookupFormula source
            pure (UniversalHintSchema (Match.startUniversalHints (preparedFormulaView prepared)) Seq.empty)
    let UniversalHintProgress next events = Map.findWithDefault (UniversalHintProgress 0 Seq.empty)
            source (branchUniversalHintProgress branch)
        index = if next >= Seq.length hints && isNothing compilation then 0 else next
        retainSchema remaining compiled = State.modify' (\state -> state
            {stateUniversalHintSchemas = Map.insert source (UniversalHintSchema remaining compiled)
                (stateUniversalHintSchemas state)})
        retainProgress eventIndex = branch
            {branchUniversalHintProgress = Map.insert source
                (UniversalHintProgress (index + 1) (if index == Seq.length events
                    then events Seq.|> eventIndex else Seq.update index eventIndex events))
                (branchUniversalHintProgress branch)}
    case Seq.lookup index hints of
        Nothing -> case compilation of
            Nothing -> do
                retainSchema Nothing hints
                pure (branch, Nothing)
            Just cursor -> do
                catalogue <- currentCatalogue
                progress <- runMatchOperation (\work -> Match.advanceUniversalHints globalType work catalogue cursor)
                case progress of
                    Match.UniversalHintsFinished -> retainSchema Nothing hints
                    Match.UniversalHintsPending following -> retainSchema (Just following) hints
                    Match.UniversalHintFound hint following -> retainSchema (Just following) (hints Seq.|> hint)
                pure (branch, Nothing)
        Just hint -> do
            let eventIndex = fromMaybe 0 (Seq.lookup index events)
            case Seq.lookup eventIndex (branchUniversalHintEvents branch) of
                Nothing -> pure (retainProgress eventIndex, Nothing)
                Just (AgendaItem sign formula) -> do
                    let advanced = retainProgress (eventIndex + 1)
                        complementary = if Match.universalHintPositive hint then SignFalse else SignTrue
                    if sign /= complementary then pure (advanced, Nothing) else do
                        prepared <- lookupFormula formula
                        -- The first version uses written equality orientation;
                        -- reverse/equality-frontier hints remain optional ordering.
                        (substitution, _reverse) <- advanceDemandMatch globalType branch
                            (BeginDemandMatch (branchStateId branch) (Match.universalHintPattern hint) prepared)
                        case substitution >>= Map.lookup (Template.MatcherSlot 0) of
                            Nothing -> pure (advanced, Nothing)
                            Just argument -> do
                                -- Only original set arguments are eligible, even
                                -- if a later proposition row supplied this event.
                                consumeWork
                                domain <- State.gets stateFrozenDomain >>= maybe
                                    (Except.throwE (RefutationInternalFailure "universal hint lost its domain")) pure
                                let original = Search.catalogueTerm (frozenDomainCatalogue domain) argument
                                pure (advanced, case original of
                                    Just row | scopedCoreType (Search.catalogueTermValue row) == TySet -> Just argument
                                    _ -> Nothing)

instantiateUniversal
    :: Eq global
    => GlobalTyping global -> BranchState -> Search.FormulaId -> Search.TermId
    -> Refute global BranchState
instantiateUniversal globalType branch source argument = do
    prepared <- lookupFormula source
    sourceReason <- maybe (Except.throwE (RefutationInternalFailure "universal instance lost its positive source")) pure
        (Map.lookup source (branchMembership branch) >>= membershipTrueReason)
    template <- either (Except.throwE . refutationTemplateFailure) pure
        (Template.retainCheckedPropositionTemplate (preparedFormulaValue prepared))
    body <- case Template.openCompiledForall template of
        Just (TySet, opened) -> pure opened
        _ -> Except.throwE (RefutationInternalFailure "generic instance source is not a set universal")
    value <- catalogueTermValue argument
    closed <- runTemplateOperation (\work -> Template.closeTemplate work body
        (Template.insertTemplateSubstitution (Template.MatcherSlot 0) value Template.emptyTemplateSubstitution))
    raw <- case closed of
        Template.TemplateClosed result -> pure result
        Template.TemplateOpen{} -> Except.throwE (RefutationInternalFailure "one-binder instantiation left an open slot")
    view <- prepareLogicalView globalType raw
    prepareResolvedProposition globalType view >>= \case
        DerivedOutsideFrozenDomain -> pure branch
        DerivedPrepared resolved -> do
            -- Finish speculative staging before publishing any proof or truth.
            (instanceView, formula) <- finishResolvedFormula resolved
            reason <- appendReason (branchStateId branch) raw (ReasonUniversalInstance argument sourceReason)
            admitPreparedSignedFormula globalType branch SignTrue instanceView formula reason

-- A split is considered only after ordinary agenda, equality and exact-rule
-- work. Inspect existing signed proofs; absence never supplies a negation.
simplifySplit
    :: GlobalTyping global
    -> BranchState
    -> AgendaItem
    -> Refute global (Maybe BranchState)
simplifySplit globalType branch (AgendaItem sign formulaId) = do
    prepared <- lookupFormula formulaId
    source <- maybe
        (Except.throwE (RefutationInternalFailure "a split lost its signed source")) pure
        (Map.lookup formulaId (branchMembership branch) >>= signedReason sign)
    let satisfied known view = (known, view, Nothing)
        propagate known view operation resultSign resultView =
            (known, view, Just (operation, resultSign, resultView))
        choices = case (sign, preparedFormulaNode prepared) of
            (SignTrue, LogicalView.LogicalDisjunction left right) ->
                [ satisfied SignTrue left, satisfied SignTrue right
                , propagate SignFalse left (DisjunctionUnit True) SignTrue right
                , propagate SignFalse right (DisjunctionUnit False) SignTrue left ]
            (SignFalse, LogicalView.LogicalConjunction left right) ->
                [ satisfied SignFalse left, satisfied SignFalse right
                , propagate SignTrue left (NegatedConjunctionUnit True) SignFalse right
                , propagate SignTrue right (NegatedConjunctionUnit False) SignFalse left ]
            (SignTrue, LogicalView.LogicalImplication left right) ->
                [ satisfied SignFalse left, satisfied SignTrue right
                , propagate SignTrue left ImplicationUnit SignTrue right
                , propagate SignFalse right ImplicationContrapositive SignFalse left ]
            _ -> []
        select [] = pure Nothing
        select ((known, view, consequence) : rest) = signedEvidence known view >>= \case
            Nothing -> select rest
            Just (witness, transport) -> case consequence of
                Nothing -> pure (Just branch)
                Just (operation, resultSign, resultView) -> do
                    premise <- case transport of
                        Nothing -> pure witness
                        Just path -> do
                            statement <- signedStatement (branchStateId branch) known
                                (Template.compiledTemplateTerm (LogicalView.logicalViewResidualTemplate view))
                            appendReason (branchStateId branch) statement
                                (ReasonSignedTransport known witness path)
                    statement <- signedStatement (branchStateId branch) resultSign
                        (logicalViewOriginalValue resultView)
                    reason <- appendReason (branchStateId branch) statement
                        (ReasonBooleanPropagation operation source premise)
                    Just <$> admitCataloguedViewSignedFormula globalType branch
                        resultSign resultView reason
    select choices
  where
    signedReason SignTrue = membershipTrueReason
    signedReason SignFalse = membershipFalseReason
    signedEvidence wanted view = do
        consumeWork
        references <- maybe
            (Except.throwE (RefutationInternalFailure "a split child has no closed catalogue root")) pure
            (Search.cataloguedFormulaRootReferences <$> Search.cataloguedFormulaView view)
        let root = Search.cataloguedRootTermId references
        formula <- State.gets (Map.lookup root . stateFormulaByTerm)
        case formula >>= (`Map.lookup` branchMembership branch) >>= signedReason wanted of
            Just reason -> pure (Just (reason, Nothing))
            Nothing -> do
                hasEquality <- State.gets ((> 0) . stateEqualityEventCount)
                if hasEquality then equivalent root (Map.toAscList (branchMembership branch))
                    else pure Nothing
      where
        equivalent _root [] = pure Nothing
        equivalent root ((candidateId, membership) : rest) = do
            consumeWork
            case signedReason wanted membership of
                Nothing -> equivalent root rest
                Just reason -> do
                    candidate <- lookupFormula candidateId
                    catalogue <- currentCatalogue
                    path <- runEqualityOperation (\work -> Equality.equalityPath work catalogue
                        (branchEquality branch) (preparedFormulaRoot candidate) root)
                    case path of
                        Nothing -> equivalent root rest
                        Just explanation -> pure (Just (reason, Just explanation))

startSplit
    :: GlobalTyping global
    -> BranchState
    -> AgendaItem
    -> Refute global (SplitPlan global, BranchState)
startSplit globalType parent (AgendaItem sign formulaId) = do
    prepared <- lookupFormula formulaId
    membership <- maybe
        (Except.throwE (RefutationInternalFailure "split formula lacks membership")) pure
        (Map.lookup formulaId (branchMembership parent))
    sourceReason <- maybe
        (Except.throwE (RefutationInternalFailure "split sign lacks a proof reason")) pure
        (case sign of
            SignTrue -> membershipTrueReason membership
            SignFalse -> membershipFalseReason membership)
    case (sign, preparedFormulaNode prepared) of
        (SignTrue, LogicalView.LogicalDisjunction leftView rightView) ->
            start TrueDisjunction SignTrue (logicalViewOriginalValue leftView) leftView rightView sourceReason
        (SignFalse, LogicalView.LogicalConjunction leftView rightView) -> do
            negatedLeft <- scopedInBranch (branchStateId parent)
                (CNot (scopedCoreTerm (logicalViewOriginalValue leftView)))
            start (FalseConjunction negatedLeft) SignFalse negatedLeft leftView rightView sourceReason
        (SignTrue, LogicalView.LogicalImplication premiseView conclusionView) -> do
            negatedPremise <- scopedInBranch (branchStateId parent)
                (CNot (scopedCoreTerm (logicalViewOriginalValue premiseView)))
            start (TrueImplication negatedPremise) SignFalse negatedPremise premiseView conclusionView sourceReason
        _ -> Except.throwE (RefutationInternalFailure "non-branching formula entered split queue")
  where
    start kind leftSign assumption leftView rightView sourceReason = do
        (leftBranch, leftHypothesis) <- newChildBranch parent assumption
        seeded <- admitCataloguedViewSignedFormula globalType leftBranch leftSign leftView leftHypothesis
        pure (SplitPlan parent sourceReason kind leftView rightView, seeded)

startRightBranch
    :: GlobalTyping global
    -> SplitPlan global
    -> Refute global BranchState
startRightBranch globalType (SplitPlan parent sourceReason kind leftView rightView) =
    case kind of
        TrueDisjunction -> do
            (rightBranch, rightHypothesis) <- newChildBranch parent right
            admitCataloguedViewSignedFormula globalType rightBranch SignTrue rightView rightHypothesis
        FalseConjunction negatedLeft -> classicalRight negatedLeft SignFalse
            (ReasonFalseConjunctionRight leftTerm rightTerm sourceReason)
        TrueImplication negatedPremise -> classicalRight negatedPremise SignTrue
            (ReasonTrueImplicationRight left sourceReason)
  where
    left = logicalViewOriginalValue leftView
    right = logicalViewOriginalValue rightView
    leftTerm = scopedCoreTerm left
    rightTerm = scopedCoreTerm right
    classicalRight negatedLeft sign reason = do
        doubleNegatedLeft <- scopedInBranch (branchStateId parent) (CNot (scopedCoreTerm negatedLeft))
        (rightBranch, rightHypothesis) <- newChildBranch parent doubleNegatedLeft
        statement <- signedStatement (branchStateId rightBranch) sign right
        rightReason <- appendReason (branchStateId rightBranch) statement (reason rightHypothesis)
        admitCataloguedViewSignedFormula globalType rightBranch sign rightView rightReason

finishSplit
    :: SplitPlan global
    -> BranchId -> ProofReasonId
    -> BranchId -> ProofReasonId
    -> Refute global ProofReasonId
finishSplit (SplitPlan parent sourceReason kind leftView rightView) left closedLeft right closedRight = do
    let parentId = branchStateId parent
    falsum <- scopedInBranch parentId CFalsum
    -- A supported child proof is usable here through its explicit discharge;
    -- it never upgrades the same inherited reason in the other child's scope.
    supportedLeft <- canonicalReason left closedLeft
    supportedRight <- if isJust supportedLeft then pure Nothing else canonicalReason right closedRight
    let selectedLeft = fromMaybe closedLeft supportedLeft
        selectedRight = fromMaybe closedRight supportedRight
    appendReason parentId falsum case kind of
        TrueDisjunction -> ReasonTrueDisjunctionSplit
            (scopedCoreTerm (logicalViewOriginalValue leftView))
            (scopedCoreTerm (logicalViewOriginalValue rightView))
            sourceReason left selectedLeft right selectedRight
        FalseConjunction splitProposition ->
            ReasonClassicalSplit splitProposition left selectedLeft right selectedRight
        TrueImplication splitProposition ->
            ReasonClassicalSplit splitProposition left selectedLeft right selectedRight

contextFor
    :: BranchId
    -> Refute global (KernelProof.ProofContext global)
contextFor branch = branchContext <$> lookupBranch branch

weakenCounted
    :: Natural
    -> KernelProof.BuiltProof global
    -> Refute global (KernelProof.BuiltProof global)
weakenCounted amount proof =
    runKernel
        (KernelProof.countedWeakenProofHypotheses amount proof)

ancestorDistance
    :: BranchId
    -> BranchId
    -> Refute global Natural
ancestorDistance ancestor descendant = go 0 descendant
  where
    go distance current
        | current == ancestor = pure distance
        | otherwise = do
            info <- lookupBranch current
            case branchParent info of
                Nothing ->
                    Except.throwE
                        (RefutationInternalFailure
                            "proof reason crossed unrelated branches")
                Just parent -> go (distance + 1) parent

materializeReason
    :: Eq global
    => ProofReasonId
    -> BranchId
    -> Refute global (KernelProof.BuiltProof global)
materializeReason reasonId consumer = do
    consumeWork
    cached <- State.gets (Map.lookup (reasonId, consumer) . stateMaterialized)
    case cached of
        Just proofAtDepth -> proofAtConsumer consumer proofAtDepth
        Nothing -> do
            entry@(ReasonEntry producer _statement _predecessors _reason) <-
                lookupReason reasonId
            distance <- ancestorDistance producer consumer
            producerInfo <- lookupBranch producer
            consumerInfo <- lookupBranch consumer
            unless
                (branchDepth producerInfo + distance
                    == branchDepth consumerInfo)
                (Except.throwE
                    (RefutationInternalFailure
                        "branch lineage and proof-hypothesis depth disagree"))
            exact <- materializeExact reasonId entry
            proof <- weakenCounted distance exact
            memoizeProof reasonId consumer proof
            pure proof

proofAtConsumer
    :: BranchId
    -> ProofAtDepth global
    -> Refute global (KernelProof.BuiltProof global)
proofAtConsumer expectedBranch
        (ProofAtDepth actualBranch storedDepth proof) = do
    info <- lookupBranch expectedBranch
    if actualBranch == expectedBranch
            && storedDepth == branchDepth info
        then pure proof
        else
            Except.throwE
                (RefutationInternalFailure
                    "materialized proof cache crossed a branch scope")

memoizeProof
    :: ProofReasonId
    -> BranchId
    -> KernelProof.BuiltProof global
    -> Refute global ()
memoizeProof reasonId branch proof = do
    consumeWork
    info <- lookupBranch branch
    let proofAtDepth = ProofAtDepth branch (branchDepth info) proof
    State.modify'
        (\state ->
            state
                { stateMaterialized =
                    Map.insert
                        (reasonId, branch) proofAtDepth
                        (stateMaterialized state)
                })

materializeExact
    :: Eq global
    => ProofReasonId
    -> ReasonEntry global
    -> Refute global (KernelProof.BuiltProof global)
materializeExact reasonId
        (ReasonEntry branch expected _predecessors reason) = do
    consumeWork
    cached <- State.gets (Map.lookup (reasonId, branch) . stateMaterialized)
    case cached of
        Just proofAtDepth -> proofAtConsumer branch proofAtDepth
        Nothing -> do
            context <- contextFor branch
            proof <-
                case reason of
                    ReasonGoalNegation ->
                        runKernel
                            (KernelProof.countedIndexedHypothesisProof
                                    context (hypothesisIx 0))
                    ReasonExternalHypothesis sourceIndex ->
                        runKernel
                            (KernelProof.countedIndexedHypothesisProof
                                    context
                                    (hypothesisIx (sourceIndex + 1)))
                    ReasonImport index statement ->
                        runKernel
                            (KernelProof.countedImportedProof
                                    context index statement)
                    ReasonCertifiedInput supplied _uses -> do
                        info <- lookupBranch branch
                        unless (isNothing (branchParent info))
                            (Except.throwE (RefutationInternalFailure
                                "a certified root was associated with an internal branch"))
                        weakenCounted 1 supplied
                    ReasonBranchHypothesis ->
                        runKernel
                            (KernelProof.countedIndexedHypothesisProof
                                    context (hypothesisIx 0))
                    ReasonTrueResidualization residualization predecessor -> do
                        source <- materializeReason predecessor branch
                        ensureExpected
                            (LogicalView.headResidualizationOriginal residualization)
                            source
                        runKernel
                            (KernelProof.countedConversionProof
                                    context source
                                    (LogicalView.headResidualizationResidual
                                        residualization))
                    ReasonFalseResidualization residualization predecessor ->
                        materializeFalseResidualization
                            branch context residualization predecessor
                    ReasonDoubleNegation target predecessor -> do
                        source <- materializeReason predecessor branch
                        runKernel
                            (KernelProof.countedDoubleNegationEliminationProof
                                    context target source)
                    ReasonConjunctionLeft left right predecessor -> do
                        source <- materializeReason predecessor branch
                        runKernel
                            (KernelProof.countedConjunctionLeftProof
                                    context left right source)
                    ReasonConjunctionRight left right predecessor -> do
                        source <- materializeReason predecessor branch
                        runKernel
                            (KernelProof.countedConjunctionRightProof
                                    context left right source)
                    ReasonFalseDisjunction selectLeft left right predecessor ->
                        materializeFalseDisjunction
                            branch context selectLeft left right predecessor
                    ReasonFalseImplicationLeft premise conclusion predecessor ->
                        materializeFalseImplicationLeft
                            branch context premise conclusion predecessor
                    ReasonFalseImplicationRight premise conclusion predecessor ->
                        materializeFalseImplicationRight
                            branch context premise conclusion predecessor
                    ReasonFalseConjunctionRight
                            left right source assumption ->
                        materializeFalseConjunctionRight
                            branch context left right source assumption
                    ReasonTrueImplicationRight
                            premise source assumption -> do
                        implication <- materializeReason source branch
                        doubleNegation <- materializeReason assumption branch
                        premiseProof <-
                            runKernel
                                (KernelProof.countedDoubleNegationEliminationProof
                                        context premise
                                        doubleNegation)
                        runKernel
                            (KernelProof.countedImplicationEliminationProof
                                    context implication
                                    premiseProof)
                    ReasonBooleanPropagation operation source witness ->
                        materializeBooleanPropagation branch context operation source witness
                    ReasonContradiction positive negative -> do
                        proposition <- materializeReason positive branch
                        negation <- materializeReason negative branch
                        runKernel
                            (KernelProof.countedNegationEliminationProof
                                    context proposition negation)
                    ReasonFalseTruth predecessor -> do
                        negation <- materializeReason predecessor branch
                        truth <-
                            runKernel
                                (KernelProof.countedTruthIntroductionProof
                                        context)
                        runKernel
                            (KernelProof.countedNegationEliminationProof
                                    context truth negation)
                    ReasonTrueDisjunctionSplit
                            left right source
                            leftBranch leftClosure
                            rightBranch rightClosure -> do
                        disjunction <- materializeReason source branch
                        closedLeft <-
                            materializeReason leftClosure leftBranch
                        closedRight <-
                            materializeReason rightClosure rightBranch
                        runKernel
                            (KernelProof.countedPreparedDisjunctionEliminationProof
                                    context left right
                                    disjunction expected
                                    closedLeft closedRight)
                    ReasonClassicalSplit
                            splitProposition
                            leftBranch leftClosure
                            rightBranch rightClosure -> do
                        excludedMiddle <-
                            runKernel
                                (KernelProof.countedExcludedMiddleProof
                                        context splitProposition)
                        closedLeft <-
                            materializeReason leftClosure leftBranch
                        closedRight <-
                            materializeReason rightClosure rightBranch
                        runKernel
                            (KernelProof.countedPreparedDisjunctionEliminationProof
                                    context
                                    (scopedCoreTerm splitProposition)
                                    (CNot (scopedCoreTerm splitProposition))
                                    excludedMiddle expected
                                    closedLeft closedRight)
                    ReasonEqualityPath left path ->
                        materializeEqualityPath branch context left (Equality.equalityPathSteps path)
                    ReasonSignedTransport sign source path -> do
                        supplied <- materializeReason source branch
                        equation <- materializeStoredEqualityPath branch context path
                        transported <- case sign of
                            SignTrue -> runKernel (KernelProof.countedEqualityModusPonensProof
                                context equation supplied)
                            SignFalse -> do
                                predicate <- scopedInBranch branch (CLam TyProp (CNot (CBound 0)))
                                runKernel (KernelProof.countedEqualityTransportProof
                                    context equation predicate supplied)
                        runKernel (KernelProof.countedConversionProof context transported expected)
                    ReasonEqualityCongruence
                            functionReason argumentReason -> do
                        functionEquality <-
                            materializeReason functionReason branch
                        argumentEquality <-
                            materializeReason argumentReason branch
                        runKernel
                            (KernelProof.countedEqualityCongruenceApplicationProof
                                    context
                                    functionEquality argumentEquality)
                    ReasonEqualityContradiction
                            equalityReason disequalityReason -> do
                        equality <-
                            materializeReason equalityReason branch
                        disequality <-
                            materializeReason disequalityReason branch
                        runKernel
                            (KernelProof.countedNegationEliminationProof
                                    context
                                    equality disequality)
                    ReasonPropositionEqualityContradiction
                            positiveReason negativeReason equalityReason -> do
                        positive <-
                            materializeReason positiveReason branch
                        negative <-
                            materializeReason negativeReason branch
                        equality <-
                            materializeReason equalityReason branch
                        transported <-
                            runKernel
                                (KernelProof.countedEqualityModusPonensProof
                                        context
                                        equality positive)
                        runKernel
                            (KernelProof.countedNegationEliminationProof
                                    context
                                    transported negative)
                    ReasonUniversalInstance argumentId sourceReason -> do
                        source <- materializeReason sourceReason branch
                        argument <- catalogueTermValue argumentId
                        runKernel (KernelProof.countedForallEliminationProof
                                context source argument)
                    ReasonRuleInstance
                            ruleId sourceFormula sourceReason
                            substitutionId witnesses ->
                        do
                            globalTyping <- State.gets stateGlobalTyping
                            materializeRuleInstance
                                globalTyping branch context ruleId sourceFormula
                                sourceReason substitutionId witnesses
            ensureExpected expected proof
            memoizeProof reasonId branch proof
            pure proof

attachResidualHead
    :: Eq global
    => GlobalTyping global
    -> KernelProof.ProofContext global
    -> KernelProof.BuiltProof global
    -> Refute global (KernelProof.BuiltProof global)
attachResidualHead globalType context proof = do
    residual <- prepareHead globalType (KernelProof.builtProofStatement proof)
    case residual of
        Nothing -> pure proof
        Just target -> runKernel
            (KernelProof.countedConversionProof context proof target)

convertIfDifferent
    :: Eq global
    => KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> KernelProof.BuiltProof global
    -> Refute global (KernelProof.BuiltProof global)
convertIfDifferent context target proof = do
    same <- scopedIdentity (KernelProof.builtProofStatement proof) target
    if same
        then pure proof
        else runKernel
            (KernelProof.countedConversionProof context proof target)

materializeRuleInstance
    :: Eq global
    => GlobalTyping global
    -> BranchId
    -> KernelProof.ProofContext global
    -> RuleId
    -> Search.FormulaId
    -> ProofReasonId
    -> MatcherSubstitutionId
    -> Seq PremiseWitness
    -> Refute global (KernelProof.BuiltProof global)
materializeRuleInstance globalType branch context ruleId sourceFormula
        sourceReason substitutionId witnesses = do
    (compiledSource, rule) <- lookupCompiledRule ruleId
    unless (sourceFormula == compiledSource)
        (malformed "rule reason cites a different source formula")
    payload <- lookupMatcherSubstitution ruleId substitutionId
    source <- materializeReason sourceReason branch
    (afterEliminations, substitutions) <- eliminateSteps source
        (Seq.viewl (Match.compiledRuleEliminations rule)) (0 :: Natural)
        payload witnesses Map.empty
    attached <- attachResidualHead globalType context afterEliminations
    target <- closeRequired (Match.compiledRuleResultTemplate rule) substitutions
    runKernel
        (KernelProof.countedConversionProof context attached target)
  where
    -- Replay the selected path in source order. Intermediate proof statements
    -- need not enter the search catalogue: only matched arguments and the
    -- selected result are subject to its frozen-universe admission.
    eliminateSteps current Seq.EmptyL _position [] remainingWitnesses substitutions =
        case Seq.viewl remainingWitnesses of
            Seq.EmptyL -> pure (current, substitutions)
            _ -> malformed "rule reason has too many premise witnesses"
    eliminateSteps _current Seq.EmptyL _position _payload _witnesses _substitutions =
        malformed "rule substitution has the wrong arity"
    eliminateSteps current (step Seq.:< steps) position payload remainingWitnesses substitutions = do
        consumeWork
        attached <- attachResidualHead globalType context current
        case step of
            Elimination.Instantiate binderType slot -> case payload of
                [] -> malformed "rule substitution has the wrong arity"
                maybeTerm : rest -> do
                    unless (slot == Template.MatcherSlot position)
                        (malformed "compiled binder is out of source order")
                    case openScopedForall (KernelProof.builtProofStatement attached) of
                        Just (openedType, _) | openedType == binderType -> pure ()
                        _ -> malformed "compiled forall step has a different source binder"
                    termId <- maybe (malformed "materialized rule has an open binder") pure maybeTerm
                    argument <- catalogueTermValue termId
                    eliminated <- runKernel (KernelProof.countedForallEliminationProof context attached argument)
                    eliminateSteps eliminated (Seq.viewl steps) (position + 1) rest
                        remainingWitnesses (Map.insert slot termId substitutions)
            Elimination.Apply recipe ->
                case openScopedImplication (KernelProof.builtProofStatement attached) of
                    Nothing -> malformed "compiled implication step has a non-implication proof"
                    Just (rawPremise, _) -> do
                        (premiseProof, rest) <- materializePremise recipe remainingWitnesses substitutions
                        rawPremiseProof <- convertIfDifferent context rawPremise premiseProof
                        eliminated <- runKernel (KernelProof.countedImplicationEliminationProof context attached rawPremiseProof)
                        eliminateSteps eliminated (Seq.viewl steps) position payload rest substitutions
            Elimination.ProjectLeft -> project True attached
            Elimination.ProjectRight -> project False attached
      where
        project selectLeft attached = do
            case splitScopedConjunction (KernelProof.builtProofStatement attached) of
                Nothing -> malformed "compiled projection step has a non-conjunction proof"
                Just (left, right) -> do
                    projected <- runKernel ((if selectLeft then KernelProof.countedConjunctionLeftProof else KernelProof.countedConjunctionRightProof)
                            context (scopedCoreTerm left) (scopedCoreTerm right) attached)
                    eliminateSteps projected (Seq.viewl steps) position payload remainingWitnesses substitutions

    materializePremise recipe remainingWitnesses substitutions = case recipe of
        Match.PremiseTruth -> do
            consumeWork
            proof <- runKernel (KernelProof.countedTruthIntroductionProof context)
            pure (proof, remainingWitnesses)
        Match.PremiseLeaf premise -> case Seq.viewl remainingWitnesses of
            Seq.EmptyL -> malformed "rule reason has too few premise witnesses"
            witness Seq.:< rest -> do
                chargePremiseWitnessPayload witness
                closedPremise <- closeRequired (Match.compiledPremiseTemplate premise) substitutions
                proof <- materializePremiseWitness branch context closedPremise witness
                pure (proof, rest)
        Match.PremiseConjunction left right -> do
            consumeWork
            (leftProof, afterLeft) <- materializePremise left remainingWitnesses substitutions
            (rightProof, afterRight) <- materializePremise right afterLeft substitutions
            proof <- runKernel (KernelProof.countedConjunctionIntroductionProof leftProof rightProof)
            pure (proof, afterRight)

    closeRequired template substitutions =
        closedTemplate template substitutions >>= \case
            Just closed -> pure closed
            Nothing -> malformed "complete rule template remained open"

    malformed message = Except.throwE (RefutationInternalFailure message)

materializeBooleanPropagation
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> BooleanPropagation
    -> ProofReasonId
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeBooleanPropagation branch context operation sourceId witnessId = do
    source <- materializeReason sourceId branch
    witness <- materializeReason witnessId branch
    consumeWork
    case operation of
        ImplicationUnit -> do
            (premise, _) <- require "implication" (openScopedImplication (KernelProof.builtProofStatement source))
            argument <- convertIfDifferent context premise witness
            apply context source argument
        ImplicationContrapositive -> do
            (premise, conclusion) <- require "implication" (openScopedImplication (KernelProof.builtProofStatement source))
            negativeConclusion <- signedStatement branch SignFalse conclusion
            argument <- convertIfDifferent context negativeConclusion witness
            negateTarget premise $ \extended assumed -> do
                implication <- weakenCounted 1 source
                negative <- weakenCounted 1 argument
                positive <- apply extended implication assumed
                contradict extended positive negative
        NegatedConjunctionUnit leftKnown -> do
            conjunction <- require "negation" (splitScopedNegation (KernelProof.builtProofStatement source))
            (left, right) <- require "conjunction" (splitScopedConjunction conjunction)
            argument <- convertIfDifferent context (if leftKnown then left else right) witness
            negateTarget (if leftKnown then right else left) $ \extended assumed -> do
                known <- weakenCounted 1 argument
                negative <- weakenCounted 1 source
                positive <- runKernel (KernelProof.countedConjunctionIntroductionProof
                    (if leftKnown then known else assumed)
                        (if leftKnown then assumed else known))
                contradict extended positive negative
        DisjunctionUnit eliminateLeft -> do
            (left, right) <- require "disjunction" (splitScopedDisjunction (KernelProof.builtProofStatement source))
            negativeDisjunct <- signedStatement branch SignFalse (if eliminateLeft then left else right)
            argument <- convertIfDifferent context negativeDisjunct witness
            let target = if eliminateLeft then right else left
                alternative eliminate proposition = do
                    (extended, assumed) <- assumption proposition
                    if not eliminate then pure assumed else do
                        negative <- weakenCounted 1 argument
                        falsum <- contradict extended assumed negative
                        runKernel (KernelProof.countedFalsumEliminationProof
                            extended falsum target)
            leftProof <- alternative eliminateLeft left
            rightProof <- alternative (not eliminateLeft) right
            runKernel (KernelProof.countedPreparedDisjunctionEliminationProof
                context (scopedCoreTerm left) (scopedCoreTerm right)
                    source target leftProof rightProof)
  where
    require shape = maybe
        (Except.throwE (RefutationInternalFailure ("Boolean propagation lost its " <> shape))) pure
    apply current implication premise = runKernel (KernelProof.countedImplicationEliminationProof current implication premise)
    contradict current positive negative = runKernel (KernelProof.countedNegationEliminationProof current positive negative)
    assumption proposition = runKernel do
        extended <- KernelProof.countedExtendProofContextHypothesis context proposition
        assumed <- KernelProof.countedIndexedHypothesisProof extended (hypothesisIx 0)
        pure (extended, assumed)
    negateTarget proposition contradiction = do
        (extended, assumed) <- assumption proposition
        falsum <- contradiction extended assumed
        runKernel (KernelProof.countedNegationIntroductionProof
            context proposition falsum)

materializePremiseWitness
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> PremiseWitness
    -> Refute global (KernelProof.BuiltProof global)
materializePremiseWitness branch context target = \case
    WitnessExact formulaId reason -> do
        proof <- materializeFormulaWitness
            branch context formulaId reason
        runKernel
            (KernelProof.countedConversionProof
                    context proof target)
    WitnessPropositionTransport formulaId reason path -> do
        proof <- materializeFormulaWitness
            branch context formulaId reason
        equality <- materializeStoredEqualityPath branch context path
        runKernel do
            transported <- KernelProof.countedEqualityModusPonensProof context equality proof
            KernelProof.countedConversionProof context transported target
    WitnessAtomic formulaId reason components -> do
        proof <- materializeFormulaWitness
            branch context formulaId reason
        candidateEquality <-
            materializeAtomicEquality
                branch context
                (KernelProof.builtProofStatement proof)
                target components
        runKernel do
            transported <- KernelProof.countedEqualityModusPonensProof context candidateEquality proof
            KernelProof.countedConversionProof context transported target
    WitnessOpenEquality formulaId reason direction leftPath rightPath -> do
        written <- materializeFormulaWitness
            branch context formulaId reason
        oriented <-
            case direction of
                Equality.EqualityReverse ->
                    runKernel
                        (KernelProof.countedEqualityReverseProof
                                context written)
                Equality.EqualityForward -> pure written
        left <- materializeStoredEqualityPath branch context leftPath
        right <- materializeStoredEqualityPath branch context rightPath
        withFact <- composeEquality left oriented
        complete <- composeEquality withFact right
        runKernel
            (KernelProof.countedConversionProof
                    context complete target)
    WitnessDerivedEquality path -> do
        proof <- materializeStoredEqualityPath branch context path
        runKernel
            (KernelProof.countedConversionProof
                    context proof target)
  where
    composeEquality left right =
        runKernel
            (KernelProof.countedComposeEqualityProof
                    context left right)

materializeFormulaWitness
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> Search.FormulaId
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFormulaWitness branch context formulaId reason = do
    prepared <- lookupFormula formulaId
    proof <- materializeReason reason branch
    runKernel
        (KernelProof.countedConversionProof
                context proof
                (preparedFormulaValue prepared))

materializeStoredEqualityPath
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> Equality.EqualityPath ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeStoredEqualityPath branch context path = do
    left <- catalogueTermValue (Equality.equalityPathSource path)
    materializeEqualityPath
        branch context left (Equality.equalityPathSteps path)

materializeAtomicEquality
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> [AtomicComponent]
    -> Refute global (KernelProof.BuiltProof global)
materializeAtomicEquality branch context candidate target components =
    do
        (candidateHead, candidateArguments) <-
            applicationSpine (scopedCoreTerm candidate)
        (targetHead, targetArguments) <-
            applicationSpine (scopedCoreTerm target)
        consumeWork
        sameArity <- sameLength candidateArguments targetArguments
        completeComponents <- sameLength candidateArguments components
        unless
            (candidateHead == targetHead
                && sameArity
                && completeComponents)
            (Except.throwE
                (RefutationInternalFailure
                    "atomic witness head or arity changed during replay"))
        headTerm <- scopedInBranch branch candidateHead
        reflexivity <-
            runKernel
                (KernelProof.countedEqualityReflexivityProof
                        context headTerm)
        foldM addArgument reflexivity components
  where
    sameLength [] [] = pure True
    sameLength (_ : left) (_ : right) = do
        consumeWork
        sameLength left right
    sameLength _left _right = pure False

    addArgument current (AtomicComponent source targetId path) = do
        consumeWork
        unless
            (source == Equality.equalityPathSource path
                && targetId == Equality.equalityPathTarget path)
            (Except.throwE
                (RefutationInternalFailure
                    "atomic component path has different endpoints"))
        argument <- materializeStoredEqualityPath branch context path
        runKernel
            (KernelProof.countedEqualityCongruenceApplicationProof
                    context current argument)

materializeEqualityPath
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> [Equality.EqualityStep ProofReasonId]
    -> Refute global (KernelProof.BuiltProof global)
materializeEqualityPath branch context left = \case
    [] ->
        runKernel
            (KernelProof.countedEqualityReflexivityProof
                    context left)
    steps -> do
        oriented <- traverse materializeStep steps
        case oriented of
            [] ->
                Except.throwE
                    (RefutationInternalFailure
                        "nonempty equality path lost all steps")
            firstStep : rest -> foldM compose firstStep rest
  where
    materializeStep
            (Equality.EqualityStep reason direction) = do
        proof <- materializeReason reason branch
        case direction of
            Equality.EqualityForward -> pure proof
            Equality.EqualityReverse ->
                runKernel
                    (KernelProof.countedEqualityReverseProof
                            context proof)

    compose firstProof secondProof =
        runKernel
            (KernelProof.countedComposeEqualityProof
                    context firstProof secondProof)

ensureExpected
    :: Eq global
    => ScopedCheckedCore global
    -> KernelProof.BuiltProof global
    -> Refute global ()
ensureExpected expected proof = do
    same <- scopedIdentity expected (KernelProof.builtProofStatement proof)
    unless same
        (Except.throwE
            (RefutationInternalFailure
                "materialized proof has a different statement"))

materializeFalseResidualization
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> LogicalView.HeadResidualization global
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFalseResidualization branch context residualization predecessor = do
    let residual = LogicalView.headResidualizationResidual residualization
        original = LogicalView.headResidualizationOriginal residualization
    sourceNegation <- materializeReason predecessor branch
    runKernel do
        withResidual <- KernelProof.countedExtendProofContextHypothesis context residual
        residualProof <- KernelProof.countedIndexedHypothesisProof withResidual (hypothesisIx 0)
        originalProof <- KernelProof.countedConversionProof withResidual residualProof original
        nestedNegation <- KernelProof.countedWeakenProofHypotheses 1 sourceNegation
        falsum <- KernelProof.countedNegationEliminationProof withResidual originalProof nestedNegation
        KernelProof.countedNegationIntroductionProof context residual falsum

materializeFalseDisjunction
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> Bool
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFalseDisjunction
        branch context selectLeft leftTerm rightTerm predecessor = do
    sourceNegation <- materializeReason predecessor branch
    selected <-
        scopedInBranch branch
            (if selectLeft then leftTerm else rightTerm)
    runKernel do
        withSelected <- KernelProof.countedExtendProofContextHypothesis context selected
        selectedProof <- KernelProof.countedIndexedHypothesisProof withSelected (hypothesisIx 0)
        disjunction <- if selectLeft
            then KernelProof.countedDisjunctionLeftProof withSelected rightTerm selectedProof
            else KernelProof.countedDisjunctionRightProof withSelected leftTerm selectedProof
        nestedNegation <- KernelProof.countedWeakenProofHypotheses 1 sourceNegation
        falsum <- KernelProof.countedNegationEliminationProof withSelected disjunction nestedNegation
        KernelProof.countedNegationIntroductionProof context selected falsum

materializeFalseImplicationLeft
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFalseImplicationLeft
        branch context premiseTerm conclusionTerm predecessor = do
    sourceNegation <- materializeReason predecessor branch
    premise <- scopedInBranch branch premiseTerm
    negatedPremise <- scopedInBranch branch (CNot premiseTerm)
    conclusion <- scopedInBranch branch conclusionTerm
    runKernel do
        withNegatedPremise <- KernelProof.countedExtendProofContextHypothesis context negatedPremise
        negatedPremiseProof <- KernelProof.countedIndexedHypothesisProof withNegatedPremise (hypothesisIx 0)
        withPremise <- KernelProof.countedExtendProofContextHypothesis withNegatedPremise premise
        premiseProof <- KernelProof.countedIndexedHypothesisProof withPremise (hypothesisIx 0)
        nestedNegation <- KernelProof.countedWeakenProofHypotheses 1 negatedPremiseProof
        firstFalsum <- KernelProof.countedNegationEliminationProof withPremise premiseProof nestedNegation
        conclusionProof <- KernelProof.countedFalsumEliminationProof withPremise firstFalsum conclusion
        implication <- KernelProof.countedImplicationIntroductionProof withNegatedPremise premise conclusionProof
        nestedSourceNegation <- KernelProof.countedWeakenProofHypotheses 1 sourceNegation
        secondFalsum <- KernelProof.countedNegationEliminationProof withNegatedPremise implication nestedSourceNegation
        doubleNegation <- KernelProof.countedNegationIntroductionProof context negatedPremise secondFalsum
        KernelProof.countedDoubleNegationEliminationProof context premise doubleNegation

materializeFalseImplicationRight
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFalseImplicationRight
        branch context premiseTerm conclusionTerm predecessor = do
    sourceNegation <- materializeReason predecessor branch
    premise <- scopedInBranch branch premiseTerm
    conclusion <- scopedInBranch branch conclusionTerm
    runKernel do
        withConclusion <- KernelProof.countedExtendProofContextHypothesis context conclusion
        conclusionProof <- KernelProof.countedIndexedHypothesisProof withConclusion (hypothesisIx 0)
        nestedConclusion <- KernelProof.countedWeakenProofHypotheses 1 conclusionProof
        implication <- KernelProof.countedImplicationIntroductionProof withConclusion premise nestedConclusion
        nestedSourceNegation <- KernelProof.countedWeakenProofHypotheses 1 sourceNegation
        falsum <- KernelProof.countedNegationEliminationProof withConclusion implication nestedSourceNegation
        KernelProof.countedNegationIntroductionProof context conclusion falsum

materializeFalseConjunctionRight
    :: Eq global
    => BranchId
    -> KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> ProofReasonId
    -> ProofReasonId
    -> Refute global (KernelProof.BuiltProof global)
materializeFalseConjunctionRight
        branch context leftTerm rightTerm source assumption = do
    sourceNegation <- materializeReason source branch
    doubleNegation <- materializeReason assumption branch
    left <- scopedInBranch branch leftTerm
    right <- scopedInBranch branch rightTerm
    runKernel do
        leftProof <- KernelProof.countedDoubleNegationEliminationProof context left doubleNegation
        withRight <- KernelProof.countedExtendProofContextHypothesis context right
        rightProof <- KernelProof.countedIndexedHypothesisProof withRight (hypothesisIx 0)
        nestedLeft <- KernelProof.countedWeakenProofHypotheses 1 leftProof
        conjunction <- KernelProof.countedConjunctionIntroductionProof nestedLeft rightProof
        nestedSourceNegation <- KernelProof.countedWeakenProofHypotheses 1 sourceNegation
        falsum <- KernelProof.countedNegationEliminationProof withRight conjunction nestedSourceNegation
        KernelProof.countedNegationIntroductionProof context right falsum

collectAuthority
    :: ProofReasonId
    -> Refute global (Set ImportIx)
collectAuthority root =
    go Set.empty Set.empty (Seq.singleton root)
  where
    go visited imports pending =
        case Seq.viewl pending of
            Seq.EmptyL -> pure imports
            reasonId Seq.:< rest
                | reasonId `Set.member` visited ->
                    go visited imports rest
                | otherwise -> do
                    consumeWork
                    ReasonEntry
                        _branch _statement predecessors reason <-
                            lookupReason reasonId
                    chargePredecessors predecessors
                    updatedImports <-
                        case reason of
                            ReasonImport index _statement -> do
                                consumeWork
                                pure (Set.insert index imports)
                            ReasonCertifiedInput _proof uses ->
                                foldM (\retained index -> do
                                    consumeWork
                                    pure (Set.insert index retained))
                                    imports (Set.toAscList (kernelSourceImportUses uses))
                            _ -> pure imports
                    go
                        (Set.insert reasonId visited)
                        updatedImports
                        (predecessors Seq.>< rest)

    chargePredecessors predecessors =
        case Seq.viewl predecessors of
            Seq.EmptyL -> pure ()
            _predecessor Seq.:< rest -> do
                consumeWork
                chargePredecessors rest

data PreparedRoot global
    = PreparedRoot !(ScopedCheckedCore global) !(RootReason global)
    | PreparedCertifiedRoot !(PreparedCertifiedFact global)
    | PreparedSyntaxRoot !(ScopedCheckedCore global) !(RootReason global) ![PreparedSyntax global]

-- LogicalView already provides the abstract syntax handle: no new wrapper or
-- second preparation walker is needed. Its immutable syntax is not evidence.
type PreparedSyntax global = LogicalView.LogicalView global ()

-- This is a checked logical view and its original certified proof, not a
-- catalogue reference. The driver retains the exact scope/typing owner when
-- reusing it in another authorized domain. Resolution still belongs to each
-- query's catalogue; no branch state or query-local IDs cross this boundary.
data PreparedCertifiedFact global = PreparedCertifiedFact
    !(KernelProof.BuiltProof global) !KernelSourceUses !(PreparedSyntax global)

data ViewedPreparedRoot global = ViewedPreparedRoot
    !(RootReason global)
    !(LogicalView.LogicalView global ())

type CataloguedPreparedRoot global =
    (RootReason global, Search.CataloguedLogicalView global)

data RootReason global
    = RootGoal
    | RootHypothesis !Natural
    | RootImport !ImportIx !(FrozenCheckedCore global)
    | RootCertified !(KernelProof.BuiltProof global) !KernelSourceUses
    | RootSeedSyntax

completeRootView
    :: Eq global
    => GlobalTyping global
    -> KernelProof.ProofContext global
    -> PreparedRoot global
    -> Refute global (ViewedPreparedRoot global)
completeRootView _globalType _context (PreparedCertifiedRoot (PreparedCertifiedFact proof uses view)) =
    pure (ViewedPreparedRoot (RootCertified proof uses) view)
completeRootView globalType context (PreparedSyntaxRoot source reason views) = findView views
  where
    findView [] = completeRootView globalType context (PreparedRoot source reason)
    findView (view : rest) = scopedIdentity source
        (Template.compiledTemplateTerm (LogicalView.logicalViewOriginalTemplate view)) >>= \case
            True -> pure (ViewedPreparedRoot reason view)
            False -> findView (case LogicalView.logicalViewNode view of
                LogicalView.LogicalNegation child -> child : rest
                LogicalView.LogicalConjunction left right -> left : right : rest
                LogicalView.LogicalDisjunction left right -> left : right : rest
                LogicalView.LogicalImplication left right -> left : right : rest
                -- A term binder changes the template environment. This syntax
                -- reference grants neither alignment nor fresh-scope authority.
                LogicalView.LogicalUniversal{} -> rest
                LogicalView.LogicalExistential{} -> rest
                LogicalView.LogicalTruth -> rest
                LogicalView.LogicalFalsum -> rest
                LogicalView.LogicalEquality{} -> rest
                LogicalView.LogicalNeutral -> rest)
completeRootView globalType context (PreparedRoot source reason) = do
    admitted <- runKernel
        (KernelProof.countedAdmitScopedTerm
            context source)
    view <- prepareLogicalView globalType admitted
    pure (ViewedPreparedRoot reason view)

rootReason
    :: BranchId
    -> ScopedCheckedCore global
    -> RootReason global
    -> Refute global ProofReasonId
rootReason branch source reason = do
    statement <-
        case reason of
            RootGoal -> signedStatement branch SignFalse source
            RootHypothesis{} -> pure source
            RootImport{} -> pure source
            RootCertified{} -> pure source
            RootSeedSyntax -> Except.throwE (RefutationInternalFailure
                "domain seed syntax cannot supply proof evidence")
    appendReason branch statement
        (case reason of
            RootGoal -> ReasonGoalNegation
            RootHypothesis index -> ReasonExternalHypothesis index
            RootImport index imported -> ReasonImport index imported
            RootCertified proof uses -> ReasonCertifiedInput proof uses
            RootSeedSyntax -> impossible "domain seed syntax passed root reason validation")

seedRoot
    :: GlobalTyping global
    -> BranchState
    -> CataloguedPreparedRoot global
    -> Refute global BranchState
seedRoot _globalType current (RootSeedSyntax, _cataloguedView) = pure current
seedRoot globalType current (reasonKind, cataloguedView) = do
    primitive <- rootReason (branchStateId current)
        (logicalViewOriginalValue cataloguedView) reasonKind
    admitCataloguedViewSignedFormula globalType current
        (case reasonKind of
            RootGoal -> SignFalse
            RootHypothesis{} -> SignTrue
            RootImport{} -> SignTrue
            RootCertified{} -> SignTrue)
        cataloguedView primitive

advanceInitialTerms
    :: Eq global
    => GlobalTyping global
    -> [CoreType]
    -> Search.InitialCatalogueCursor global (RootReason global)
    -> Refute global (Search.InitialCatalogueStep global (RootReason global))
advanceInitialTerms globalType ambient cursor = do
    work <- State.gets stateRemainingWork
    termLimit <- State.gets stateGroundTermLimit
    let (result, remaining, admissions) =
            Search.advanceInitialCatalogue globalType work termLimit ambient cursor
    State.modify' (\state -> state {stateRemainingWork = remaining})
    retainTermAdmissions admissions
    case result of
        Left Search.CatalogueWorkExhausted -> Except.throwE RefutationWorkExhausted
        Left Search.CatalogueGroundTermLimitExhausted -> Except.throwE RefutationGroundTermsExhausted
        Left Search.CatalogueOutsideFrozenUniverse -> Except.throwE
            (RefutationInternalFailure "initial catalogue unexpectedly rejected its own roots")
        Left (Search.CatalogueIntegrityFailure message) -> Except.throwE (RefutationInternalFailure message)
        Right step -> pure step

finishCandidate
    :: Eq global
    => KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BranchId
    -> ProofReasonId
    -> Refute global (RefutationCandidate global)
finishCandidate context target negatedTarget rootBranch closure = do
    -- Authority collection deliberately precedes proof construction.  A
    -- failure in either pass publishes no partial candidate.
    imports <- collectAuthority closure
    falsum <- materializeReason closure rootBranch
    doubleNegation <-
        runKernel
            (KernelProof.countedNegationIntroductionProof
                    context negatedTarget falsum)
    proof <-
        runKernel
            (KernelProof.countedDoubleNegationEliminationProof
                    context target doubleNegation)
    ensureExpected target proof
    witness <- State.gets (\state -> stateSupport state >>= Map.lookup closure . supportWitnesses)
    pure (RefutationCandidate proof imports witness)

-- | Run the complete propositional refutation tier.  The returned statistics
-- are strict observations of the finished search, including failed search or
-- materialization; demanding them cannot resume work.
runRefutation
    :: Ord global
    => RefutationLimits
    -> GlobalTyping global
    -> KernelProof.ProofContext global
    -> [RefutationFact global]
    -> ScopedCheckedCore global
    -> (RefutationStatistics, Either RefutationFailure (RefutationCandidate global))
runRefutation limits globalType context facts target =
    drainRefutation limits (startRefutation limits globalType context facts target)

-- Startup retains checked inputs; it does not traverse roots or enter search.
startRefutation
    :: RefutationLimits
    -> GlobalTyping global
    -> KernelProof.ProofContext global
    -> [RefutationFact global]
    -> ScopedCheckedCore global
    -> RefutationSession global
startRefutation limits globalType context =
    startRefutationWithSeeds limits globalType context []

-- A seed is checked syntax only. Raw initial facts retain the exact associated
-- source indices; the selected source proof is built by the existing materializer.
startRefutationWithSeeds
    :: RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> [ScopedCheckedCore global] -> [RefutationFact global] -> ScopedCheckedCore global
    -> RefutationSession global
startRefutationWithSeeds limits globalType context seedSyntax facts target =
    startPreparedRefutation limits globalType context
        ([PreparedRoot syntax RootSeedSyntax | syntax <- seedSyntax]
            <> map (factRoot (KernelProof.proofContextTypes context)) facts) target

-- Freeze exactly the authorized family syntax before preparing this query's
-- target and asserted roots. Neither an out-of-domain target nor a derived fact
-- can enlarge the domain merely by becoming the first residual to run.
startRefutationFromSeed
    :: RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> NonEmpty (ScopedCheckedCore global) -> [RefutationFact global] -> ScopedCheckedCore global
    -> RefutationSession global
startRefutationFromSeed limits globalType context seedSyntax facts target =
    startRefutationFromSeedWithViews limits globalType context [] seedSyntax facts target

-- Retained views are associated by the driver with this exact immutable typing
-- and lexical owner. Matching is charged at each real seed, goal and fact root;
-- only syntax preparation is shared. Original source indices are untouched.
startRefutationFromSeedWithViews
    :: RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> [PreparedSyntax global] -> NonEmpty (ScopedCheckedCore global)
    -> [RefutationFact global] -> ScopedCheckedCore global -> RefutationSession global
startRefutationFromSeedWithViews limits globalType context views seedSyntax facts target =
    RefutationSession globalType context target
        (initialState globalType (KernelProof.proofContextTypes context) limits)
        (PrepareSeedNegation (reuseSyntax views <$> [PreparedRoot syntax RootSeedSyntax | syntax <- toList seedSyntax])
            (reuseSyntax views <$> (PreparedRoot target RootGoal : map (factRoot (KernelProof.proofContextTypes context)) facts)))

reuseSyntax :: [PreparedSyntax global] -> PreparedRoot global -> PreparedRoot global
reuseSyntax [] root = root
reuseSyntax views (PreparedRoot source reason) = PreparedSyntaxRoot source reason views
reuseSyntax _ root = root

factRoot :: [CoreType] -> RefutationFact global -> PreparedRoot global
factRoot ambient = \case
    RefutationHypothesis index statement -> PreparedRoot statement (RootHypothesis index)
    RefutationImport index statement -> PreparedRoot (embedClosedCore ambient statement)
        (RootImport index statement)
    RefutationCertified proof uses ->
        PreparedRoot (KernelProof.builtProofStatement proof) (RootCertified proof uses)
    RefutationPrepared prepared -> PreparedCertifiedRoot prepared

-- | Internal service for the scope owner, which establishes each producer's
-- exact hypothesis/import association before entry. Seed syntax is not evidence.
startCertifiedRefutation
    :: RefutationLimits
    -> GlobalTyping global
    -> KernelProof.ProofContext global
    -> [ScopedCheckedCore global]
    -> [(KernelProof.BuiltProof global, KernelSourceUses)]
    -> ScopedCheckedCore global
    -> RefutationSession global
startCertifiedRefutation limits globalType context seedSyntax inputs =
    startRefutationWithSeeds limits globalType context seedSyntax
        [RefutationCertified proof uses | (proof, uses) <- inputs]

-- A family exports only its immutable initial catalogue. Later query-local
-- proposition rows, equalities, reasons and negated targets are never shared.
data FrozenDomain global = FrozenDomain ![CoreType] !(Search.Catalogue global)

-- The scope owner may enumerate existing checked terms; the catalogue's
-- constructors and all query-local evidence remain private.
frozenDomainCatalogue :: FrozenDomain global -> Search.Catalogue global
frozenDomainCatalogue (FrozenDomain _ambient catalogue) = catalogue

prepareGroundSyntax
    :: Eq global
    => RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global -> ScopedCheckedCore global
    -> (RefutationLimits, Either RefutationFailure (PreparedSyntax global))
prepareGroundSyntax limits typing context source =
    let (result, final) = State.runState (Except.runExceptT do
            ViewedPreparedRoot _ view <- completeRootView typing context (PreparedRoot source RootSeedSyntax)
            pure view) (initialState typing (KernelProof.proofContextTypes context) limits)
    in (remainingLimits final, result)

assembleGroundImplication
    :: Eq global
    => RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> ScopedCheckedCore global -> PreparedSyntax global -> PreparedSyntax global
    -> (RefutationLimits, Either RefutationFailure (PreparedSyntax global))
assembleGroundImplication limits typing context written left right =
    let (result, final) = State.runState (Except.runExceptT do
            assembled <- LogicalView.assembleImplicationViewCounted scopedIdentity consumeWork written left right
            either (\(LogicalView.LogicalViewIntegrityFailure message) -> Except.throwE (RefutationInternalFailure message))
                pure assembled) (initialState typing (KernelProof.proofContextTypes context) limits)
    in (remainingLimits final, result)

groundSyntaxFits
    :: Eq global
    => RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> FrozenDomain global -> [PreparedSyntax global]
    -> (RefutationLimits, Either RefutationFailure Bool)
groundSyntaxFits limits typing context (FrozenDomain ambient catalogue) views =
    let initial = (initialState typing (KernelProof.proofContextTypes context) limits)
            {stateCatalogue = Just catalogue, stateTermCount = Search.catalogueTermCount catalogue
            , statePrepaidTermCount = Search.catalogueTermCount catalogue}
        fits [] = pure True
        fits (view : rest) = prepareResolvedProposition typing view >>= \case
            DerivedPrepared{} -> fits rest
            DerivedOutsideFrozenDomain -> pure False
        (result, final) = State.runState (Except.runExceptT (requireFrozenContext context ambient >> fits views)) initial
    in (remainingLimits final, result)

-- A neutral compatibility check for the nominal owner. Both an outside result
-- and a later selected-domain startup reuse the paid checked view. The probe
-- asserts nothing, admits no rows, and returns actual remaining resources even
-- when preparation fails. Canonical seed authorization remains driver-owned.
prepareFrozenFact
    :: Eq global
    => RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> FrozenDomain global -> KernelProof.BuiltProof global -> KernelSourceUses
    -> (RefutationLimits, Either RefutationFailure (PreparedCertifiedFact global, Bool))
prepareFrozenFact limits typing context (FrozenDomain ambient catalogue) proof uses =
    let initial = (initialState typing (KernelProof.proofContextTypes context) limits)
            {stateCatalogue = Just catalogue, stateTermCount = Search.catalogueTermCount catalogue
            , statePrepaidTermCount = Search.catalogueTermCount catalogue}
        (result, final) = State.runState (Except.runExceptT do
            requireFrozenContext context ambient
            ViewedPreparedRoot _reason view <- completeRootView typing context
                (PreparedRoot (KernelProof.builtProofStatement proof) (RootCertified proof uses))
            prepared <- prepareResolvedProposition typing view
            pure (PreparedCertifiedFact proof uses view, case prepared of
                DerivedPrepared{} -> True
                DerivedOutsideFrozenDomain -> False)) initial
    in (remainingLimits final, result)

requireFrozenContext :: KernelProof.ProofContext global -> [CoreType] -> Refute global ()
requireFrozenContext context ambient = do
    work <- State.gets stateRemainingWork
    let (sameContext, remaining) = countedCoreTypeListIdentity work ambient
            (KernelProof.proofContextTypes context)
    State.modify' (\state -> state {stateRemainingWork = remaining})
    case sameContext of
        Left _failure -> Except.throwE RefutationWorkExhausted
        Right False -> Except.throwE (RefutationInternalFailure "a frozen domain belongs to a different term context")
        Right True -> pure ()

refutationSessionDomain :: RefutationSession global -> Maybe (FrozenDomain global)
refutationSessionDomain (RefutationSession _typing _context _target state _phase) =
    stateFrozenDomain state

-- The scope owner supplies associated proofs and an already paid family domain.
-- The residual target and every asserted root are prepared against that domain;
-- neither is allowed to introduce a non-propositional term.
startCertifiedRefutationInDomain
    :: RefutationLimits
    -> GlobalTyping global
    -> KernelProof.ProofContext global
    -> FrozenDomain global
    -> [(KernelProof.BuiltProof global, KernelSourceUses)]
    -> ScopedCheckedCore global
    -> RefutationSession global
startCertifiedRefutationInDomain limits globalType context domain inputs =
    startRefutationInDomain limits globalType context domain
        [RefutationCertified proof uses | (proof, uses) <- inputs]

startRefutationInDomain
    :: RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> FrozenDomain global -> [RefutationFact global] -> ScopedCheckedCore global
    -> RefutationSession global
startRefutationInDomain limits globalType context domain inputs target =
    startRefutationInDomainWithViews limits globalType context [] domain inputs target

startRefutationInDomainWithViews
    :: RefutationLimits -> GlobalTyping global -> KernelProof.ProofContext global
    -> [PreparedSyntax global] -> FrozenDomain global -> [RefutationFact global] -> ScopedCheckedCore global
    -> RefutationSession global
startRefutationInDomainWithViews limits globalType context views domain@(FrozenDomain ambient catalogue) inputs target =
    RefutationSession globalType context target
        (initialState globalType (KernelProof.proofContextTypes context) limits)
            { stateCatalogue = Just catalogue
            , stateFrozenDomain = Just domain
            , stateTermCount = Search.catalogueTermCount catalogue
            , statePrepaidTermCount = Search.catalogueTermCount catalogue
            }
        (PrepareFrozenNegation ambient
            (reuseSyntax views <$> (PreparedRoot target RootGoal : map (factRoot ambient) inputs)))

data CataloguePurpose global
    = CatalogueInitialQuery
    | CatalogueSeedForQuery ![PreparedRoot global]

-- Each phase has one owner and a finite next transition. The term catalogue is
-- unavailable to logical search until every initial root has been prepared.
data RefutationPhase global
    = PrepareNegation ![PreparedRoot global]
    | PrepareSeedNegation ![PreparedRoot global] ![PreparedRoot global]
    | PrepareFrozenNegation ![CoreType] ![PreparedRoot global]
    | PrepareFrozenRoots !(ScopedCheckedCore global) ![PreparedRoot global]
        !(Seq (CataloguedPreparedRoot global))
    | PrepareRootViews !(CataloguePurpose global) !(ScopedCheckedCore global) ![PreparedRoot global]
        !(Seq (RootReason global, LogicalView.LogicalView global ()))
    | PrepareCatalogue !(CataloguePurpose global) !(ScopedCheckedCore global)
        !(Search.InitialCatalogueCursor global (RootReason global))
    | CreateRootBranch !(ScopedCheckedCore global) !(NonEmpty (CataloguedPreparedRoot global))
    | SeedRootBranch !(ScopedCheckedCore global) !BranchId !BranchState
        ![CataloguedPreparedRoot global]
    | SearchRootBranch !(ScopedCheckedCore global) !BranchId !(BranchSearch global)
    | MaterializeRoot !(ScopedCheckedCore global) !BranchId !ProofReasonId
    | PublishOrdinaryRoot !(ScopedCheckedCore global) !BranchId !ProofReasonId !(RefutationPhase global)
    | SeedSupportingRoots !(ScopedCheckedCore global) !BranchId !BranchState ![CataloguedPreparedRoot global]
    | SearchSupportingRoot !(ScopedCheckedCore global) !BranchId !(BranchSearch global)
    | PrepareResumingInput !Bool !(ScopedCheckedCore global) !BranchId !(BranchTree global)
        !(PreparedRoot global)
    | PropagateResumingInput !Bool !(ScopedCheckedCore global) !BranchId
        !(Search.CataloguedLogicalView global) !ProofReasonId !(InputPropagation global)

data RefutationSession global = RefutationSession
    !(GlobalTyping global)
    !(KernelProof.ProofContext global)
    !(ScopedCheckedCore global)
    !(RefutationState global)
    !(RefutationPhase global)

-- Enable tracking before any query preparation. Later support demand uses this
-- same state; an already running ordinary query cannot retroactively recover
-- discarded consumers by attaching a source label.
trackRefutationCanonicalSources
    :: [RefutationCanonicalSource] -> RefutationSession global
    -> Either RefutationFailure (RefutationSession global)
trackRefutationCanonicalSources sources (RefutationSession typing context target state phase) = case phase of
    PrepareNegation{} -> enable
    PrepareSeedNegation{} -> enable
    PrepareFrozenNegation{} -> enable
    _ -> Left (RefutationInternalFailure "canonical tracking started after ground preparation")
  where
    enable = case stateSupport state of
        Just _ -> Left (RefutationInternalFailure "ground canonical tracking was registered twice")
        Nothing -> Right (RefutationSession typing context target
            state {stateSupport = Just (RefutationSupport sources Map.empty Map.empty Seq.empty Nothing)} phase)

data RefutationProgress global
    = RefutationPending !(RefutationSession global)
    | RefutationBlocked !RefutationStatistics !RefutationFailure !(RefutationSession global)
    | RefutationFinished !RefutationStatistics
        !(Either RefutationFailure (RefutationCandidate global))

-- The retained open session owns all spent work, branches and rule instances.
-- This operation cannot supply a fresh allowance or rebuild a frozen domain.
-- As at the certified entry, the caller has associated this proof with the
-- query's original hypothesis/import scope.
resumeRefutationWithInput
    :: KernelProof.BuiltProof global
    -> KernelSourceUses
    -> RefutationSession global
    -> Either RefutationFailure (RefutationSession global)
resumeRefutationWithInput proof uses = resumePreparedRoot
    (PreparedRoot (KernelProof.builtProofStatement proof) (RootCertified proof uses))

resumeRefutationWithPreparedInput
    :: PreparedCertifiedFact global -> RefutationSession global
    -> Either RefutationFailure (RefutationSession global)
resumeRefutationWithPreparedInput = resumePreparedRoot . PreparedCertifiedRoot

resumePreparedRoot :: PreparedRoot global -> RefutationSession global
    -> Either RefutationFailure (RefutationSession global)
resumePreparedRoot input
        (RefutationSession typing context target state phase) = case phase of
    SearchRootBranch negated rootId (FinishedBranch (BranchOpen tree)) ->
        Right (RefutationSession typing context target state
            (PrepareResumingInput False negated rootId tree input))
    SearchSupportingRoot negated rootId (FinishedBranch (BranchClosed _ tree)) ->
        Right (RefutationSession typing context target state
            (PrepareResumingInput True negated rootId tree input))
    _ -> Left (RefutationInternalFailure "certified evidence can resume only a retained ground frontier")

refutationSessionAnyCandidate :: RefutationSession global -> Maybe (RefutationCandidate global)
refutationSessionAnyCandidate (RefutationSession _ _ _ state _) = stateSupport state >>= supportAnyCandidate

refutationSessionStatistics :: RefutationSession global -> RefutationStatistics
refutationSessionStatistics (RefutationSession _typing _context _target state _phase) =
    statisticsFromState state

startPreparedRefutation
    :: RefutationLimits
    -> GlobalTyping global
    -> KernelProof.ProofContext global
    -> [PreparedRoot global]
    -> ScopedCheckedCore global
    -> RefutationSession global
startPreparedRefutation limits globalType context roots target =
    RefutationSession globalType context target
        (initialState globalType (KernelProof.proofContextTypes context) limits)
        (PrepareNegation (PreparedRoot target RootGoal : roots))

remainingLimits :: RefutationState global -> RefutationLimits
remainingLimits state = RefutationLimits
    (stateRemainingWork state)
    (stateRemainingConversionPool state)
    (stateGroundTermLimit state - stateTermAdmissions state)
    (stateBranchNodeLimit state - stateBranchNodes state)
    (stateRuleInstanceLimit state - stateRuleInstanceCount state)
    (stateBooleanPropagation state)
    (stateExtendedRules state)
    (stateUniversals state)

-- Other tasks may have spent part of the request allowance while this session
-- was suspended. Accept only a reduction; consumed counters and all query state
-- remain attached to the session. Decreasing these bounds cannot overflow.
restrictRemainingLimits :: RefutationLimits -> Refute global ()
restrictRemainingLimits limits = do
    previous <- remainingLimits <$> State.get
    -- A sequential continuation normally returns exactly its current allowance.
    -- Equality establishes monotonicity without rebuilding the wide search state.
    -- A reduction still checks every owner before installing cumulative limits.
    when (limits /= previous) do
        unless
          (refutationWorkLimit limits <= refutationWorkLimit previous
              && Conversion.conversionPoolAmount (refutationConversionPool limits)
                  <= Conversion.conversionPoolAmount (refutationConversionPool previous)
              && refutationGroundTermLimit limits <= refutationGroundTermLimit previous
              && refutationBranchNodeLimit limits <= refutationBranchNodeLimit previous
              && refutationRuleInstanceLimit limits <= refutationRuleInstanceLimit previous
              && refutationBooleanPropagation limits == refutationBooleanPropagation previous
              && refutationExtendedRules limits == refutationExtendedRules previous
              && permitsUniversalRemainder (refutationUniversals previous) (refutationUniversals limits))
          (Except.throwE (RefutationInternalFailure "a resumed ground session changed its policy or replenished its allowance"))
        State.modify' (\state -> state
          { stateRemainingWork = refutationWorkLimit limits
          , stateRemainingConversionPool = refutationConversionPool limits
          , stateGroundTermLimit = stateTermAdmissions state + refutationGroundTermLimit limits
          , stateBranchNodeLimit = stateBranchNodes state + refutationBranchNodeLimit limits
          , stateRuleInstanceLimit = stateRuleInstanceCount state + refutationRuleInstanceLimit limits
          , stateUniversals = refutationUniversals limits
          })

advanceRefutation
    :: Eq global
    => RefutationLimits
    -> RefutationSession global
    -> (RefutationLimits, RefutationProgress global)
advanceRefutation limits (RefutationSession globalType context target state phase) =
    let (result, updated) = State.runState
            (Except.runExceptT do
                restrictRemainingLimits limits
                advanced <- advanceSupport
                if advanced then pure (NextRefutationPhase phase)
                    else advancePhase globalType context target phase) state
        available = remainingLimits updated
        statistics = statisticsFromState updated
        progress = case result of
            Left failure -> RefutationFinished statistics (Left failure)
            Right (NextRefutationPhase next) ->
                RefutationPending (RefutationSession globalType context target updated next)
            Right (BlockedRefutation failure) ->
                RefutationBlocked statistics failure (RefutationSession globalType context target updated phase)
            Right (CompletedRefutation candidate) -> RefutationFinished statistics (Right candidate)
    in available `seq` progress `seq` (available, progress)

data RefutationTransition global
    = NextRefutationPhase !(RefutationPhase global)
    | BlockedRefutation !RefutationFailure
    | CompletedRefutation !(RefutationCandidate global)

advancePhase
    :: Eq global
    => GlobalTyping global
    -> KernelProof.ProofContext global
    -> ScopedCheckedCore global
    -> RefutationPhase global
    -> Refute global (RefutationTransition global)
advancePhase globalType context target = \case
    PrepareNegation roots -> do
        negated <- runKernel (KernelProof.countedScopedTerm context
            (CNot (scopedCoreTerm target)))
        pure (NextRefutationPhase (PrepareRootViews CatalogueInitialQuery negated roots Seq.empty))
    PrepareSeedNegation seeds roots -> do
        negated <- runKernel (KernelProof.countedScopedTerm context
            (CNot (scopedCoreTerm target)))
        pure (NextRefutationPhase (PrepareRootViews (CatalogueSeedForQuery roots) negated seeds Seq.empty))
    PrepareFrozenNegation ambient roots -> do
        requireFrozenContext context ambient
        negated <- runKernel (KernelProof.countedScopedTerm context
            (CNot (scopedCoreTerm target)))
        pure (NextRefutationPhase (PrepareFrozenRoots negated roots Seq.empty))
    PrepareFrozenRoots negated (root : rest) completed -> do
        ViewedPreparedRoot reason view <- completeRootView globalType context root
        prepareResolvedProposition globalType view >>= \case
            DerivedOutsideFrozenDomain -> Except.throwE RefutationUnsupportedTermOutsideUniverse
            DerivedPrepared resolved -> do
                catalogued <- finishResolvedView resolved
                pure (NextRefutationPhase (PrepareFrozenRoots negated rest (completed Seq.|> (reason, catalogued))))
    PrepareFrozenRoots negated [] completed -> case Seq.viewl completed of
        Seq.EmptyL -> Except.throwE (RefutationInternalFailure "ground query has no target root")
        first Seq.:< rest -> advancePhase globalType context target
            (CreateRootBranch negated (first :| toList rest))
    PrepareRootViews purpose negated (root : rest) completed -> do
        ViewedPreparedRoot reason view <- completeRootView globalType context root
        pure (NextRefutationPhase (PrepareRootViews purpose negated rest (completed Seq.|> (reason, view))))
    PrepareRootViews purpose negated [] completed -> case Seq.viewl completed of
        Seq.EmptyL -> Except.throwE (RefutationInternalFailure "ground query has no target root")
        first Seq.:< rest -> advancePhase globalType context target (PrepareCatalogue purpose negated
            (Search.startInitialCatalogue (first :| toList rest)))
    PrepareCatalogue purpose negated cursor ->
        advanceInitialTerms globalType (KernelProof.proofContextTypes context) cursor >>= \case
            Search.InitialCatalogueMore next -> pure (NextRefutationPhase (PrepareCatalogue purpose negated next))
            Search.InitialCatalogueDone initial -> do
                let catalogue = Search.initialCatalogue initial
                State.modify' (\state -> state
                    { stateTermCount = Search.catalogueTermCount catalogue
                    , stateCatalogue = Just catalogue
                    , stateFrozenDomain = Just (FrozenDomain
                        (KernelProof.proofContextTypes context) catalogue)
                    })
                pure (NextRefutationPhase case purpose of
                    CatalogueInitialQuery -> CreateRootBranch negated (Search.initialRootViews initial)
                    CatalogueSeedForQuery roots -> PrepareFrozenRoots negated roots Seq.empty)
    CreateRootBranch negated roots -> do
        (root, rootId) <- newRootBranch context negated
        pure (NextRefutationPhase (SeedRootBranch negated rootId root (toList roots)))
    SeedRootBranch negated rootId branch pending
        | Just closure <- branchClosure branch -> completeOrdinary negated rootId closure
            (SeedSupportingRoots negated rootId (seekBranchSupport closure branch) pending)
        | otherwise -> case pending of
            [] -> advancePhase globalType context target (SearchRootBranch negated rootId (SearchBranch branch []))
            root : rest -> do
                seeded <- seedRoot globalType branch root
                pure (NextRefutationPhase (SeedRootBranch negated rootId seeded rest))
    SearchRootBranch negated rootId (FinishedBranch result@(BranchClosed closure _tree)) ->
        completeOrdinary negated rootId closure
            (SearchSupportingRoot negated rootId (ResumeBranch (seekResultSupport result) []))
    SearchRootBranch _negated _rootId (FinishedBranch BranchOpen{}) -> blockedRoot RefutationSaturated
    SearchRootBranch negated rootId pending -> do
        advanced <- advanceBranchSearch globalType pending
        pure (NextRefutationPhase (SearchRootBranch negated rootId advanced))
    PrepareResumingInput supporting negated rootId tree input -> do
        consumeWork
        ViewedPreparedRoot source view <- completeRootView globalType context input
        let root = retainedBranch tree
            resume = if supporting then SearchSupportingRoot else SearchRootBranch
            unchanged = NextRefutationPhase (resume negated rootId (FinishedBranch root))
        prepareResolvedProposition globalType view >>= \case
            DerivedOutsideFrozenDomain -> pure unchanged
            DerivedPrepared resolved -> do
                visible <- inputAlreadyVisible tree resolved
                tracking <- State.gets (isJust . stateSupport)
                if visible && not tracking then pure unchanged else do
                    catalogued <- finishResolvedView resolved
                    reason <- rootReason rootId (logicalViewOriginalValue catalogued) source
                    pure (NextRefutationPhase (PropagateResumingInput supporting negated rootId catalogued reason
                        (VisitInputBranch root [])))
    PropagateResumingInput supporting negated rootId _view _reason (FinishedInputPropagation result) ->
        advancePhase globalType context target
            ((if supporting then SearchSupportingRoot else SearchRootBranch) negated rootId (ResumeBranch result []))
    PropagateResumingInput supporting negated rootId view reason pending -> do
        advanced <- advanceInputPropagation globalType view reason pending
        pure (NextRefutationPhase (PropagateResumingInput supporting negated rootId view reason advanced))
    MaterializeRoot negated rootId closure -> do
        selected <- fromMaybe closure <$> canonicalReason rootId closure
        CompletedRefutation <$> finishCandidate context target negated rootId selected
    PublishOrdinaryRoot negated rootId closure continuation -> do
        supported <- canonicalReason rootId closure
        candidate <- finishCandidate context target negated rootId (fromMaybe closure supported)
        if isJust (refutationCandidateCanonicalSource candidate)
            then pure (CompletedRefutation candidate)
            else do
                modifySupport (\support -> support {supportAnyCandidate = Just candidate})
                pure (NextRefutationPhase continuation)
    SeedSupportingRoots negated rootId branch pending -> do
        refreshed <- refreshBranchSupport branch
        case branchClosure refreshed of
            Just closure -> advancePhase globalType context target (MaterializeRoot negated rootId closure)
            Nothing -> case pending of
                [] -> pure (NextRefutationPhase (SearchSupportingRoot negated rootId (SearchBranch refreshed [])))
                root : rest -> do
                    seeded <- seedRoot globalType refreshed root
                    pure (NextRefutationPhase (SeedSupportingRoots negated rootId seeded rest))
    SearchSupportingRoot negated rootId (FinishedBranch (BranchClosed closure _)) -> do
        supported <- canonicalReason rootId closure
        case supported of
            Just selected -> advancePhase globalType context target (MaterializeRoot negated rootId selected)
            Nothing -> blockedRoot RefutationCanonicalSupportMissing
    SearchSupportingRoot _ _ (FinishedBranch BranchOpen{}) ->
        Except.throwE (RefutationInternalFailure "canonical search lost its ordinary root certificate")
    SearchSupportingRoot negated rootId pending -> do
        advanced <- advanceBranchSearch globalType pending
        pure (NextRefutationPhase (SearchSupportingRoot negated rootId advanced))
  where
    blockedRoot fallback = do
        unsupported <- State.gets stateUnsupportedTerm
        undetermined <- State.gets stateUndeterminedParameter
        pure (BlockedRefutation case (unsupported, undetermined) of
            (True, _) -> RefutationUnsupportedTermOutsideUniverse
            (False, Just parameter) -> RefutationUndeterminedParameter parameter
            (False, Nothing) -> fallback)
    completeOrdinary negated rootId closure continuation = do
        tracking <- State.gets (isJust . stateSupport)
        advancePhase globalType context target
            (if tracking then PublishOrdinaryRoot negated rootId closure continuation
                else MaterializeRoot negated rootId closure)

drainRefutation
    :: Eq global
    => RefutationLimits
    -> RefutationSession global
    -> (RefutationStatistics, Either RefutationFailure (RefutationCandidate global))
drainRefutation limits session = case advanceRefutation limits session of
    (remaining, RefutationPending next) -> drainRefutation remaining next
    (_remaining, RefutationBlocked statistics failure _suspended) -> (statistics, Left failure)
    (_remaining, RefutationFinished statistics result) -> (statistics, result)
