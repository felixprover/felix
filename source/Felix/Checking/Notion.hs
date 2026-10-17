{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Source-preserved formation atoms and checked rule applications. Assertions
-- retain exact conjunction projections; transient witnesses replay through
-- the ordinary kernel. Search scheduling belongs to Notion.Evaluation.
module Felix.Checking.Notion
    ( sourceNotionWrittenOrigin
    , withSourceNotionOrigin
    , SourceNotionOccurrence
    , SourceNotionAssertion
    , sourceAssertionAtom
    , sourceAssertionHead
    , sourceAssertionFormula
    , sourceAssertionPath
    , sourceAssertionLocation
    , RuleTerm.compileSourceRuleTermTemplate
    , globalSourceNotionAssertion
    , structureSourceNotionAssertion
    , exactStructureSourceNotionAssertion
    , membershipSourceNotionAssertion
    , sourceNotionAssertionFromTemplate
    , mapSourceNotionAssertion
    , traverseSourceNotionAssertion
    , traverseSourceNotionAssertionParts
    , mapSourceNotionAssertionPath
    , SourceEqualityOccurrence
    , SourceEqualityAssertion
    , sourceEqualityLeft
    , sourceEqualityRight
    , sourceEqualityFormula
    , sourceEqualityPath
    , sourceEqualityLocation
    , setSourceEqualityOccurrence
    , traverseSourceEqualityOccurrenceParts
    , mapSourceEqualityOccurrencePath
    , ConjunctionPath(..)
    , ConjunctionProjection
    , rootConjunctionProjection
    , ConjunctionProjections
    , emptyConjunctionProjections
    , extendConjunctionProjection
    , prepareConjunctionProjection
    , conjunctionProjectionPath
    , leftConjunctionPath
    , rightConjunctionPath
    , projectConjunctionPath
    , NotionHeadKey(..), templateHead
    , GroundNotionKey
    , groundNotionHeadKey
    , groundNotionKeyFromAssertion
    , groundNotionKeyTemplate
    , groundNotionKeyFromFormula
    , groundNotionKeyFromTemplate
    , instantiateDirectNotionTemplate
    , UnaryPremiseKey(..)
    , UnarySourceIndex
    , emptyUnarySourceIndex
    , insertUnarySource
    , lookupDirectUnarySource
    , findDirectFormationEvidenceWithLimits
    , unarySourcesForPremise
    , DirectFormationSource(..)
    , VisibleNotionView
    , visibleNotionView
    , visibleNotionViewSource
    , visibleNotionViewPayload
    , VisibleNullaryProviderClassification
    , visibleNullaryProviderClassification
    , visibleNullaryProviderClassificationSource
    , visibleNullaryProviderClassificationPayload
    , visibleNullaryProviderClassificationConclusionKey
    , VisibleProviderResultRule
    , MaterializedProviderResultPremises(..)
    , visibleProviderResultRule
    , visibleProviderResultRuleSource
    , visibleProviderResultRulePayload
    , visibleProviderResultRuleBinderArity
    , visibleProviderResultRuleConclusionHead
    , VisibleBackwardNotionRule
    , visibleBackwardNotionRule
    , visibleBackwardNotionRuleSource
    , visibleBackwardNotionRulePayload
    , visibleBackwardNotionRuleBinderArity
    , visibleBackwardNotionRuleConclusionHead
    , VisibleFiniteEvidenceRule
    , visibleFiniteEvidenceRule
    , visibleFiniteEvidenceRuleSource
    , visibleFiniteEvidenceRulePayload
    , visibleFiniteEvidenceRuleBinderArity
    , visibleFiniteEvidenceRuleConclusionHead
    , VisibleGraphDomainRule
    , visibleGraphDomainRule
    , visibleGraphDomainRuleSource
    , visibleGraphDomainRulePayload
    , visibleGraphDomainRuleBinderArity
    , VisibleWholeConclusionRule, visibleWholeConclusionRule
    , visibleWholeConclusionRuleSource, visibleWholeConclusionRulePayload
    , FormationSearchLimits
    , formationSearchLimits
    , formationSearchLimitsWithEqualityChain
    , defaultFormationSearchLimits
    , FormationSearchError(..)
    , renderFormationSearchError
    , FormationSearchStatistics(..)
    , emptyFormationSearchStatistics
    , FormationSearchBudget
    , initialFormationSearchBudget
    , formationSearchBudgetLimits
    , formationInferenceWorkRemaining
    , formationInferenceWorkUsed
    , remainingFormationSearchLimits
    , formationSearchBudgetStatistics
    , consumeFormationSearchStatistics
    , formationSearchBudgetDiagnostics
    , formationSearchBudgetMeasurement
    , recordFormationOperation
    , recordFormationCoreWork
    , recordFormationOutcome
    , formationSearchBudgetPhase
    , setFormationSearchPhase
    , formationSearchRejectedDebit
    , recordFormationRejectedDebit
    , formationSearchInferenceInspections
    , setFormationRegistrationFamily
    , formationRuleFamily
    , FormationEvidence
    , FormationWitness
    , FormationWitnessArena
    , FormationConstruction
    , withFormationWitnessArena
    , runFormationConstruction
    , FormationHypothesisReference
    , prepareFormationHypothesis
    , formationHypothesisProposition
    , formationWitnessGroundKey
    , formationWitnessDerivationNodes
    , formationWitnessEqualitySteps
    , preferDirectFormationWitness
    , selectFormationEvidence
    , ProvedRichGoal
    , provedRichGoal
    , provedRichGoalShape
    , provedRichGoalEvidence
    , formationEvidenceGroundKey
    , formationEvidenceImports
    , formationEvidenceBranch
    , formationEvidenceDerivationNodes
    , formationEvidenceDerivationDepth
    , formationEvidenceProviderRuleSteps
    , formationEvidenceCompositeLevel
    , formationEvidenceUsesEquality
    , formationEvidenceEqualityTransportSteps
    , preferDirectFormationEvidence
    , MaterializedNotionHypothesis
    , materializedNotionHypothesis
    , materializedNotionHypothesisProposition
    , materializedNotionHypothesisOrigin
    , MaterializedFormationEvidence
    , FormationProofError(..)
    , materializedFormationHypotheses
    , materializedFormationHypothesisPropositions
    , materializedFormationImports
    , materializeFormationPremiseEvidence
    , materializeFormationEvidence
    , FormationSearchOutcome(..)
    , FormationFailureFrontier(..)
    , FormationFailureExplanation(..)
    , directFormationEvidence
    , directPreparedFormationEvidence
    , FormationRuleSource(..)
    , applyFormationRule, formationRuleSourceBranch
    , applyIntroductionRule
    , FormationSourceEvidence
    , directFormationSourceEvidence
    , countedAlignFormationSourceEvidence
    , countedAlignFormationEqualityTransport
    , formationSourceEvidenceOrdinal
    , formationSourceEvidenceAliasOrdinals
    , transportFormationSourceWithLimits
    , applyUniversalSource, applyProjectedSource, applyProjectedEvidence
    , suppliedFormationEvidence
    , composeFormationEvidence
    , FormationIntroduction(..), introduceFormationEvidence
    , FormationPremiseEvidence(..)
    , FormationEqualityDirection(..)
    , FormationEqualityTransport
    , formationEqualityTransport
    , convertFormationEvidence
    , applyEqualitySubstitutionsWithLimits
    , applyEqualityTransportWithLimits
    , applyWholeEqualitySubstitutionsWithLimits
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation (HypothesisIx)
import Felix.Checking.Kernel.Proof (KernelProofBuildError)
import Felix.Checking.Notion.Formation
import Felix.Checking.Notion.Projection
import Felix.Checking.Notion.Introduction (Introduction(..))
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.SuppliedUniversal (UniversalAdapter, adapterCost)
import Felix.Checking.Notion.SourceEvidence (UniversalElimination(..), WrittenOrigin)
import Felix.Checking.Notion.RuleTerm qualified as RuleTerm
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Semantic
import Felix.Report.Location

import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Reader qualified as Reader
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word)
import Numeric.Natural (Natural)


-- | Written origin does not contribute to equality or ordering: search keys
-- and semantic deduplication observe the canonical atom and source metadata.
data SourceNotionOccurrence presentation argument formula = SourceNotionOccurrence
    !(AtomTemplate argument)
    !formula
    -- Scope indexes use the shared selector. Keep this legacy source-facing
    -- projection lazy so retaining a wide spine does not expand every prefix.
    ConjunctionPath
    !Location
    !(Maybe WrittenOrigin)
    deriving stock (Show, Generic)

sourceAssertionIdentity
    :: SourceNotionOccurrence presentation argument formula
    -> (AtomTemplate argument, formula, ConjunctionPath, Location)
sourceAssertionIdentity (SourceNotionOccurrence atom formula path location _origin) =
    (atom, formula, path, location)

instance (Eq argument, Eq formula)
        => Eq (SourceNotionOccurrence presentation argument formula) where
    left == right = sourceAssertionIdentity left == sourceAssertionIdentity right

instance (Ord argument, Ord formula)
        => Ord (SourceNotionOccurrence presentation argument formula) where
    compare left right = compare (sourceAssertionIdentity left) (sourceAssertionIdentity right)

type SourceNotionAssertion term = SourceNotionOccurrence () term term

sourceNotionWrittenOrigin
    :: SourceNotionOccurrence presentation argument formula
    -> Maybe WrittenOrigin
sourceNotionWrittenOrigin (SourceNotionOccurrence _atom _formula _path _location origin) = origin

withSourceNotionOrigin
    :: WrittenOrigin
    -> SourceNotionOccurrence presentation argument formula
    -> SourceNotionOccurrence presentation argument formula
withSourceNotionOrigin origin (SourceNotionOccurrence atom formula path location _oldOrigin) =
    SourceNotionOccurrence atom formula path location (Just origin)

-- | One positive source equality whose formula is obtainable from the
-- surrounding proposition by the retained conjunction path.  Equality
-- occurrences deliberately retain their two source-aware operands separately
-- from the checked formula: later notion transport may change the logical
-- notion subject without changing a provider-sensitive source identity.
data SourceEqualityOccurrence argument formula = SourceEqualityOccurrence
    !argument
    !argument
    !formula
    !ConjunctionPath
    !Location
    deriving stock (Show, Eq, Ord, Generic)

type SourceEqualityAssertion term = SourceEqualityOccurrence term term

sourceEqualityLeft
    :: SourceEqualityOccurrence argument formula
    -> argument
sourceEqualityLeft (SourceEqualityOccurrence left _right _formula _path _location) =
    left

sourceEqualityRight
    :: SourceEqualityOccurrence argument formula
    -> argument
sourceEqualityRight (SourceEqualityOccurrence _left right _formula _path _location) =
    right

sourceEqualityFormula
    :: SourceEqualityOccurrence argument formula
    -> formula
sourceEqualityFormula
        (SourceEqualityOccurrence _left _right formula _path _location) =
    formula

sourceEqualityPath
    :: SourceEqualityOccurrence argument formula
    -> ConjunctionPath
sourceEqualityPath
        (SourceEqualityOccurrence _left _right _formula path _location) =
    path

sourceEqualityLocation
    :: SourceEqualityOccurrence argument formula
    -> Location
sourceEqualityLocation
        (SourceEqualityOccurrence _left _right _formula _path location) =
    location

setSourceEqualityOccurrence
    :: argument
    -> argument
    -> formula
    -> ConjunctionPath
    -> Location
    -> SourceEqualityOccurrence argument formula
setSourceEqualityOccurrence = SourceEqualityOccurrence

traverseSourceEqualityOccurrenceParts
    :: Applicative effect
    => (leftArgument -> effect rightArgument)
    -> (leftFormula -> effect rightFormula)
    -> SourceEqualityOccurrence leftArgument leftFormula
    -> effect (SourceEqualityOccurrence rightArgument rightFormula)
traverseSourceEqualityOccurrenceParts transformArgument transformFormula
        (SourceEqualityOccurrence left right formula path location) =
    SourceEqualityOccurrence
        <$> transformArgument left
        <*> transformArgument right
        <*> transformFormula formula
        <*> pure path
        <*> pure location

mapSourceEqualityOccurrencePath
    :: (ConjunctionPath -> ConjunctionPath)
    -> SourceEqualityOccurrence argument formula
    -> SourceEqualityOccurrence argument formula
mapSourceEqualityOccurrencePath transform
        (SourceEqualityOccurrence left right formula path location) =
    SourceEqualityOccurrence left right formula (transform path) location

sourceAssertionAtom
    :: SourceNotionOccurrence presentation argument formula
    -> AtomTemplate argument
sourceAssertionAtom (SourceNotionOccurrence atom _formula _path _location _origin) = atom

sourceAssertionHead
    :: SourceNotionOccurrence presentation argument formula
    -> NotionHeadKey
sourceAssertionHead = templateHead . sourceAssertionAtom

sourceAssertionFormula
    :: SourceNotionOccurrence presentation argument formula
    -> formula
sourceAssertionFormula (SourceNotionOccurrence _atom formula _path _location _origin) = formula

sourceAssertionPath
    :: SourceNotionOccurrence presentation argument formula
    -> ConjunctionPath
sourceAssertionPath (SourceNotionOccurrence _atom _formula path _location _origin) = path

sourceAssertionLocation
    :: SourceNotionOccurrence presentation argument formula
    -> Location
sourceAssertionLocation (SourceNotionOccurrence _atom _formula _path location _origin) = location

globalSourceNotionAssertion
    :: GlobalNotionHead
    -> Vector argument
    -> formula
    -> ConjunctionPath
    -> Location
    -> SourceNotionOccurrence presentation argument formula
globalSourceNotionAssertion head' arguments =
    sourceNotionAssertionFromTemplate (GlobalAtomTemplate head' arguments)

structureSourceNotionAssertion
    :: SemanticStructureNotionHead
    -> Vector argument
    -> formula
    -> ConjunctionPath
    -> Location
    -> SourceNotionOccurrence presentation argument formula
structureSourceNotionAssertion head' arguments =
    sourceNotionAssertionFromTemplate (StructureAtomTemplate head' arguments)

exactStructureSourceNotionAssertion
    :: SemanticRecordShapeKey -> argument -> formula -> ConjunctionPath -> Location
    -> SourceNotionOccurrence presentation argument formula
exactStructureSourceNotionAssertion shape subject =
    sourceNotionAssertionFromTemplate (ExactStructureAtomTemplate shape subject)

membershipSourceNotionAssertion
    :: argument
    -> argument
    -> formula
    -> ConjunctionPath
    -> Location
    -> SourceNotionOccurrence presentation argument formula
membershipSourceNotionAssertion element set =
    sourceNotionAssertionFromTemplate (MembershipAtomTemplate element set)

sourceNotionAssertionFromTemplate
    :: AtomTemplate argument
    -> formula
    -> ConjunctionPath
    -> Location
    -> SourceNotionOccurrence presentation argument formula
sourceNotionAssertionFromTemplate atom formula path location =
    SourceNotionOccurrence atom formula path location Nothing

mapSourceNotionAssertion
    :: (left -> right)
    -> SourceNotionAssertion left
    -> SourceNotionAssertion right
mapSourceNotionAssertion transform (SourceNotionOccurrence atom formula path location origin) =
    SourceNotionOccurrence (fmap transform atom) (transform formula) path location origin

traverseSourceNotionAssertion
    :: Applicative effect
    => (left -> effect right)
    -> SourceNotionAssertion left
    -> effect (SourceNotionAssertion right)
traverseSourceNotionAssertion transform =
    traverseSourceNotionAssertionParts transform transform

-- | Traverse atom arguments in their family order, then the asserted formula.
traverseSourceNotionAssertionParts
    :: Applicative effect
    => (leftArgument -> effect rightArgument)
    -> (leftFormula -> effect rightFormula)
    -> SourceNotionOccurrence presentation leftArgument leftFormula
    -> effect (SourceNotionOccurrence presentation rightArgument rightFormula)
traverseSourceNotionAssertionParts transformArgument transformFormula
        (SourceNotionOccurrence atom formula path location origin) =
    SourceNotionOccurrence <$> traverse transformArgument atom <*> transformFormula formula
        <*> pure path <*> pure location <*> pure origin

mapSourceNotionAssertionPath
    :: (ConjunctionPath -> ConjunctionPath)
    -> SourceNotionOccurrence presentation argument formula
    -> SourceNotionOccurrence presentation argument formula
mapSourceNotionAssertionPath transform (SourceNotionOccurrence atom formula path location origin) =
    SourceNotionOccurrence atom formula (transform path) location origin

leftConjunctionPath :: ConjunctionPath -> ConjunctionPath
leftConjunctionPath = ConjunctionLeft

rightConjunctionPath :: ConjunctionPath -> ConjunctionPath
rightConjunctionPath = ConjunctionRight

-- | Follow one checked source-assertion path through a proposition.
projectConjunctionPath
    :: ConjunctionPath
    -> CanonicalTerm global
    -> Maybe (CanonicalTerm global)
projectConjunctionPath path proposition =
    case path of
        ConjunctionHere -> Just proposition
        ConjunctionLeft remaining -> case proposition of
            CAnd left _right -> projectConjunctionPath remaining left
            _ -> Nothing
        ConjunctionRight remaining -> case proposition of
            CAnd _left right -> projectConjunctionPath remaining right
            _ -> Nothing

data NotionHeadKey
    = GlobalNotionHeadKey !GlobalNotionHead
    | StructureNotionHeadKey !SemanticStructureNotionHead
    | MembershipNotionHeadKey
    | ExactStructureNotionHeadKey !SemanticRecordShapeKey
    | NegativeGlobalNotionHeadKey !GlobalNotionHead
    | NegativeStructureNotionHeadKey !SemanticStructureNotionHead
    | NegativeMembershipNotionHeadKey
    | NegativeExactStructureNotionHeadKey !SemanticRecordShapeKey
    deriving stock (Show, Eq, Ord)

newtype GroundNotionKey = GroundNotionKey
    (NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId))
    deriving stock (Show, Eq, Ord)

groundNotionKeyFromAssertion
    :: SourceNotionOccurrence
        presentation
        (ScopedCheckedCore ObjectId)
        (ScopedCheckedCore ObjectId)
    -> GroundNotionKey
groundNotionKeyFromAssertion = groundNotionKeyFromTemplate . fmap scopedCoreTerm . sourceAssertionAtom

-- | Instantiate the notion-0 direct-argument fragment.  Rich provider terms
-- require exact binding resolution and are instantiated by elaboration after
-- contract materialization.
instantiateDirectNotionTemplate
    :: Vector term
    -> NotionTemplate
    -> Maybe (AtomTemplate term)
instantiateDirectNotionTemplate occurrenceArguments =
    traverseAtomTemplateArguments instantiateTerm
  where
    instantiateTerm = \case
        TemplateClosed{} -> Nothing
        TemplateVariable index -> select index
        TemplateProvider{} -> Nothing
        TemplateOrderedPair{} -> Nothing

    select (OccurrenceArgumentIx index) =
        occurrenceArguments Vector.!? fromIntegral index

groundNotionKeyFromTemplate
    :: AtomTemplate (CanonicalTerm ObjectId)
    -> GroundNotionKey
groundNotionKeyFromTemplate = GroundNotionKey . AtomicLeaf

groundNotionKeyFromFormula :: ScopedCheckedCore ObjectId -> GroundNotionKey
groundNotionKeyFromFormula = GroundNotionKey . WholeLeaf

groundNotionKeyTemplate :: GroundNotionKey -> Maybe (AtomTemplate (CanonicalTerm ObjectId))
groundNotionKeyTemplate (GroundNotionKey (AtomicLeaf atom)) = Just atom
groundNotionKeyTemplate (GroundNotionKey WholeLeaf{}) = Nothing

groundNotionHeadKey :: GroundNotionKey -> Maybe NotionHeadKey
groundNotionHeadKey = fmap templateHead . groundNotionKeyTemplate


formationConclusionIsOperational :: AtomTemplate term -> Bool
formationConclusionIsOperational = \case
    NegativeAtomTemplate body -> formationConclusionIsOperational body
    GlobalAtomTemplate head' _arguments ->
        globalNotionHeadRole head' == HostedGlobalNotion
    StructureAtomTemplate{} -> True
    MembershipAtomTemplate{} -> True
    ExactStructureAtomTemplate{} -> True

data UnaryPremiseKey
    = UnaryGlobalPremise !GlobalNotionHead
    | UnaryStructurePremise !SemanticStructureNotionHead
    | UnaryMembershipPremise
    | UnaryExactStructurePremise !SemanticRecordShapeKey
    | UnaryExactMembershipPremise !SourceProviderHead
    deriving stock (Show, Eq, Ord)

data UnarySourceBucket richKey rich origin = UnarySourceBucket
    !(Set richKey)
    !(Seq.Seq (ProvedRichGoal (AtomTemplate rich) origin))

data UnarySourceIndex richKey rich origin = UnarySourceIndex
    !(Map
        GroundNotionKey
        (ProvedRichGoal (AtomTemplate rich) origin))
    !(Map UnaryPremiseKey (UnarySourceBucket richKey rich origin))

emptyUnarySourceIndex :: UnarySourceIndex richKey rich origin
emptyUnarySourceIndex = UnarySourceIndex Map.empty Map.empty

insertUnarySource
    :: Ord richKey
    => richKey
    -> Maybe UnaryPremiseKey
    -> ProvedRichGoal (AtomTemplate rich) origin
    -> UnarySourceIndex richKey rich origin
    -> UnarySourceIndex richKey rich origin
insertUnarySource richKey premiseKey proved
        (UnarySourceIndex byGround byPremise) =
    UnarySourceIndex
        (Map.insertWith preferDirect groundKey proved byGround)
        (case premiseKey of
            Nothing -> byPremise
            Just key -> Map.alter (Just . insertBucket) key byPremise)
  where
    groundKey = formationEvidenceGroundKey (provedRichGoalEvidence proved)

    preferDirect new old =
        case preferDirectCandidate (provedRichGoalEvidence old) (provedRichGoalEvidence new) of
            True -> new
            False -> old

    insertBucket Nothing =
        UnarySourceBucket (Set.singleton richKey) (Seq.singleton proved)
    insertBucket (Just bucket@(UnarySourceBucket keys rows))
        | richKey `Set.member` keys = bucket
        | otherwise =
            UnarySourceBucket
                (Set.insert richKey keys)
                (rows Seq.|> proved)

lookupDirectUnarySource
    :: GroundNotionKey
    -> UnarySourceIndex richKey rich origin
    -> Maybe (ProvedRichGoal (AtomTemplate rich) origin)
lookupDirectUnarySource key (UnarySourceIndex byGround _byPremise) =
    Map.lookup key byGround

unarySourcesForPremise
    :: UnaryPremiseKey
    -> UnarySourceIndex richKey rich origin
    -> [ProvedRichGoal (AtomTemplate rich) origin]
unarySourcesForPremise key (UnarySourceIndex _byGround byPremise) =
    case Map.lookup key byPremise of
        Nothing -> []
        Just (UnarySourceBucket _keys rows) -> toList rows

data DirectFormationSource origin = DirectFormationSource
    { directSourceProposition :: !(ScopedCheckedCore ObjectId)
    , directSourcePath :: !ConjunctionPath
    , directSourceOrigin :: !origin
    , directSourceOrdinal :: !Natural
    } deriving stock (Show, Eq)

data VisibleNotionView = VisibleNotionView
    !SemanticFactBranch
    !NotionViewRule
    !Natural
    deriving stock (Show, Eq)

-- | Materialize the non-serialized runtime shape once.  Exact source
-- registration guarantees the atom formulas; this check independently
-- enforces the finite direct-variable fragment and the theorem's binder
-- skeleton before query evaluation.
visibleNotionView
    :: SemanticFactBranch
    -> NotionViewRule
    -> CheckedPropositionContent
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either Text VisibleNotionView
visibleNotionView branch view proposition expectedPremise expectedConclusion = do
    let premiseVariables = premiseTemplateVariables
            (notionViewPremise view)
        conclusionVariables = templateVariables
            (notionViewConclusion view)
        binderArity = fromIntegral (Set.size premiseVariables)
        densePremiseContext = case ( Set.lookupMin premiseVariables
                                   , Set.lookupMax premiseVariables
                                   ) of
            (Nothing, Nothing) -> True
            (Just minimumIndex, Just maximumIndex) ->
                minimumIndex == 0 && maximumIndex + 1 == binderArity
            _ -> False
    unless
        ( densePremiseContext
          && conclusionVariables `Set.isSubsetOf` premiseVariables
        )
        (Left "notion view variables are not a dense premise-determined context")
    body <- stripSetForalls binderArity
        (frozenCoreTerm (checkedPropositionTerm proposition))
    case body of
        CImp premise conclusion
                | premise == expectedPremise
                  && projectConjunctionPath (semanticFactBranchPath branch) conclusion == Just expectedConclusion ->
            pure (VisibleNotionView branch view binderArity)
        CImp{} ->
            Left "notion view theorem does not match its registered atoms"
        _ -> Left "notion view theorem is not a unary implication"
  where
    stripSetForalls 0 term = Right term
    stripSetForalls remaining term =
        case term of
            CForall TySet body -> stripSetForalls (remaining - 1) body
            _ -> Left "notion view theorem has the wrong universal binder prefix"

visibleNotionViewSource :: VisibleNotionView -> SemanticFactBranch
visibleNotionViewSource (VisibleNotionView source _payload _metadata) = source

visibleNotionViewPayload :: VisibleNotionView -> NotionViewRule
visibleNotionViewPayload (VisibleNotionView _source declaration _binderArity) =
    declaration

data VisibleNullaryProviderClassification =
    VisibleNullaryProviderClassification
        !SemanticFactBranch
        !NullaryProviderRule
        !GroundNotionKey
    deriving stock (Show, Eq)

-- | Materialize one closed intrinsic classification against the exact checked
-- theorem proposition reconstructed by declaration assembly.
visibleNullaryProviderClassification
    :: SemanticFactBranch
    -> NullaryProviderRule
    -> CheckedPropositionContent
    -> CanonicalTerm ObjectId
    -> Either Text VisibleNullaryProviderClassification
visibleNullaryProviderClassification branch classification proposition expected = do
    unless
        ( globalNotionHeadRole
            (nullaryConclusion classification)
          == HostedGlobalNotion
        )
        (Left
            "a source-terminal global predicate cannot be a nullary-classification conclusion")
    unless
        (projectConjunctionPath (semanticFactBranchPath branch)
            (frozenCoreTerm (checkedPropositionTerm proposition)) == Just expected)
        (Left "a nullary classification theorem has the wrong proposition")
    let provider = nullaryProvider classification
        conclusion = nullaryConclusion classification
    providerTerm <- maybe
        (Left "a nullary classification has a non-nullary provider")
        Right
        (intrinsicProviderApplication provider Vector.empty)
    let key = groundNotionKeyFromTemplate
            (GlobalAtomTemplate conclusion (Vector.singleton providerTerm))
    pure (VisibleNullaryProviderClassification branch classification key)

visibleNullaryProviderClassificationSource :: VisibleNullaryProviderClassification -> SemanticFactBranch
visibleNullaryProviderClassificationSource (VisibleNullaryProviderClassification source _payload _metadata) = source

visibleNullaryProviderClassificationPayload
    :: VisibleNullaryProviderClassification
    -> NullaryProviderRule
visibleNullaryProviderClassificationPayload
        (VisibleNullaryProviderClassification _source declaration _key) =
    declaration

visibleNullaryProviderClassificationConclusionKey
    :: VisibleNullaryProviderClassification
    -> GroundNotionKey
visibleNullaryProviderClassificationConclusionKey
        (VisibleNullaryProviderClassification _source _declaration key) =
    key

data VisibleProviderResultRule = VisibleProviderResultRule
    !SemanticFactBranch
    !ProviderResultRule
    !Natural
    deriving stock (Show, Eq)

-- | Premise mode after declaration materialization has reconstructed each
-- guarded header proposition in the visible environment.
data MaterializedProviderResultPremises
    = MaterializedProviderResultUnconditional
    | MaterializedProviderResultGuarded
        !(NonEmpty (CanonicalTerm ObjectId))
    deriving stock (Show, Eq)

visibleProviderResultRule
    :: SemanticFactBranch
    -> ProviderResultRule
    -> CheckedPropositionContent
    -> MaterializedProviderResultPremises
    -> CanonicalTerm ObjectId
    -> Either Text VisibleProviderResultRule
visibleProviderResultRule branch rule proposition expectedPremises expectedConclusion = do
    let scope = RuleTerm.providerResultPremiseScope
            (providerResultProvider rule)
            (providerResultConclusion rule)
        determiningVariables = RuleTerm.providerResultDeterminingVariables scope
        binderArity = fromIntegral (Set.size determiningVariables)
        denseVariables = if binderArity == 0
            then Set.empty
            else Set.fromList [ViewVariableIx index | index <- [0 .. binderArity - 1]]
    unless (determiningVariables == denseVariables)
        (Left
            "a provider-result occurrence and conclusion must determine a dense theorem context")
    unless
        (formationConclusionIsOperational
            (providerResultConclusion rule))
        (Left
            "a source-terminal global predicate cannot be a provider-result conclusion")
    first snd (RuleTerm.validateProviderResultPremises scope
        (providerResultPremises rule))
    unless
        (validResultFocus (providerResultConclusion rule))
        (Left
            "provider-result conclusion must contain the provider exactly once at notion focus")
    body <- stripSetForalls binderArity
        (frozenCoreTerm (checkedPropositionTerm proposition))
    case (providerResultPremises rule, expectedPremises) of
        ( ProviderResultUnconditional
          , MaterializedProviderResultUnconditional
          ) ->
            requireConclusion body
        ( ProviderResultGuarded{}
          , MaterializedProviderResultGuarded premises
          ) ->
            requireImplications (toList premises) body
        _ ->
            Left "provider-result premise mode differs from its semantic declaration"
    pure (VisibleProviderResultRule branch rule binderArity)
  where
    requireConclusion body =
        unless (projectConjunctionPath (semanticFactBranchPath branch) body == Just expectedConclusion)
            (Left "provider-result theorem has the wrong conclusion")
    requireImplications [] body = requireConclusion body
    requireImplications (expected : remaining) body =
        case body of
            CImp premise continuation
                | premise == expected ->
                    requireImplications remaining continuation
            CImp{} ->
                Left "provider-result theorem has the wrong premise grouping"
            _ -> Left "provider-result theorem has too few curried premises"

    stripSetForalls 0 term = Right term
    stripSetForalls remaining term =
        case term of
            CForall TySet body -> stripSetForalls (remaining - 1) body
            _ ->
                Left
                    "provider-result theorem has the wrong universal binder prefix"

    validResultFocus template =
        case template of
            NegativeAtomTemplate body -> validResultFocus body
            GlobalAtomTemplate _head arguments -> focused arguments
            StructureAtomTemplate _head arguments -> focused arguments
            MembershipAtomTemplate element set ->
                element == ResultRuleProviderValue
                    && set /= ResultRuleProviderValue
            ExactStructureAtomTemplate _ subject -> subject == ResultRuleProviderValue

    focused arguments =
        case Vector.uncons arguments of
            Nothing -> False
            Just (focus, remaining) ->
                focus == ResultRuleProviderValue
                    && ResultRuleProviderValue `notElem` toList remaining

visibleProviderResultRuleSource :: VisibleProviderResultRule -> SemanticFactBranch
visibleProviderResultRuleSource (VisibleProviderResultRule source _payload _metadata) = source

visibleProviderResultRulePayload
    :: VisibleProviderResultRule
    -> ProviderResultRule
visibleProviderResultRulePayload
        (VisibleProviderResultRule _source declaration _binderArity) =
    declaration

visibleProviderResultRuleBinderArity
    :: VisibleProviderResultRule
    -> Natural
visibleProviderResultRuleBinderArity
        (VisibleProviderResultRule _source _declaration binderArity) =
    binderArity

visibleProviderResultRuleConclusionHead
    :: VisibleProviderResultRule
    -> NotionHeadKey
visibleProviderResultRuleConclusionHead =
    templateHead
        . providerResultConclusion
        . visibleProviderResultRulePayload

data VisibleBackwardNotionRule = VisibleBackwardNotionRule
    !SemanticFactBranch
    !BackwardNotionRule
    !Natural
    deriving stock (Show, Eq)

visibleBackwardNotionRule
    :: SemanticFactBranch
    -> BackwardNotionRule
    -> CheckedPropositionContent
    -> NonEmpty (CanonicalTerm ObjectId)
    -> CanonicalTerm ObjectId
    -> Either Text VisibleBackwardNotionRule
visibleBackwardNotionRule branch rule proposition expectedPremises expectedConclusion = do
    unless
        (formationConclusionIsOperational
            (backwardNotionConclusion rule))
        (Left
            "a source-terminal global predicate cannot be a backward-rule conclusion")
    let variables = atomRuleVariables
            (backwardNotionConclusion rule)
        binderArity = fromIntegral (Set.size variables)
        denseVariables = if binderArity == 0
            then Set.empty
            else Set.fromList [0 .. binderArity - 1]
    unless (variables == denseVariables)
        (Left
            "a backward notion rule conclusion does not determine a dense theorem context")
    unless
        (all
            (`Set.member` conclusionSubterms)
            (premiseTerms
                (backwardNotionPremises rule)))
        (Left
            "a backward notion rule premise contains a term absent from its conclusion")
    body <- stripSetForalls binderArity
        (frozenCoreTerm (checkedPropositionTerm proposition))
    requireImplications (toList expectedPremises) body
    pure (VisibleBackwardNotionRule branch rule binderArity)
  where
    conclusionSubterms = Set.fromList
        (concatMap recursiveRuleTermTemplates
            (toList (backwardNotionConclusion rule)))

    requireImplications [] body =
        unless (projectConjunctionPath (semanticFactBranchPath branch) body == Just expectedConclusion)
            (Left
                "a backward notion rule theorem has the wrong conclusion")
    requireImplications (expected : remaining) body =
        case body of
            CImp premise continuation
                | premise == expected ->
                    requireImplications remaining continuation
            CImp{} ->
                Left
                    "a backward notion rule theorem has the wrong premise grouping"
            _ ->
                Left
                    "a backward notion rule theorem has too few curried premises"

    stripSetForalls 0 term = Right term
    stripSetForalls remaining term =
        case term of
            CForall TySet body -> stripSetForalls (remaining - 1) body
            _ ->
                Left
                    "a backward notion rule theorem has the wrong universal binder prefix"

visibleBackwardNotionRuleSource :: VisibleBackwardNotionRule -> SemanticFactBranch
visibleBackwardNotionRuleSource (VisibleBackwardNotionRule source _payload _metadata) = source

visibleBackwardNotionRulePayload
    :: VisibleBackwardNotionRule
    -> BackwardNotionRule
visibleBackwardNotionRulePayload
        (VisibleBackwardNotionRule _source declaration _binderArity) =
    declaration

visibleBackwardNotionRuleBinderArity
    :: VisibleBackwardNotionRule
    -> Natural
visibleBackwardNotionRuleBinderArity
        (VisibleBackwardNotionRule _source _declaration binderArity) =
    binderArity

visibleBackwardNotionRuleConclusionHead
    :: VisibleBackwardNotionRule
    -> NotionHeadKey
visibleBackwardNotionRuleConclusionHead =
    templateHead
        . backwardNotionConclusion
        . visibleBackwardNotionRulePayload

data VisibleFiniteEvidenceRule = VisibleFiniteEvidenceRule
    !SemanticFactBranch
    !FiniteEvidenceRule
    deriving stock (Show, Eq)

visibleFiniteEvidenceRule
    :: SemanticFactBranch
    -> FiniteEvidenceRule
    -> CheckedPropositionContent
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> Either Text VisibleFiniteEvidenceRule
visibleFiniteEvidenceRule branch rule proposition expectedPremises expectedConclusion = do
    body <- stripSetForalls binderArity
        (frozenCoreTerm (checkedPropositionTerm proposition))
    requireImplications (toList expectedPremises) body
    pure (VisibleFiniteEvidenceRule branch rule)
  where
    skeleton = finiteEvidenceSkeleton rule
    binderArity = checkedNotionRuleBinderArity skeleton

    requireImplications [] body =
        unless (projectConjunctionPath (semanticFactBranchPath branch) body == Just expectedConclusion)
            (Left "a finite-evidence theorem has the wrong conclusion")
    requireImplications (expected : remaining) body =
        case body of
            CImp premise continuation
                | premise == expected ->
                    requireImplications remaining continuation
            CImp{} ->
                Left
                    "a finite-evidence theorem has the wrong premise grouping"
            _ ->
                Left "a finite-evidence theorem has too few curried premises"

    stripSetForalls 0 term = Right term
    stripSetForalls remaining term =
        case term of
            CForall TySet body -> stripSetForalls (remaining - 1) body
            _ ->
                Left
                    "a finite-evidence theorem has the wrong universal binder prefix"

visibleFiniteEvidenceRuleSource :: VisibleFiniteEvidenceRule -> SemanticFactBranch
visibleFiniteEvidenceRuleSource (VisibleFiniteEvidenceRule source _payload) = source

visibleFiniteEvidenceRulePayload
    :: VisibleFiniteEvidenceRule
    -> FiniteEvidenceRule
visibleFiniteEvidenceRulePayload (VisibleFiniteEvidenceRule _source declaration) =
    declaration

visibleFiniteEvidenceRuleBinderArity
    :: VisibleFiniteEvidenceRule
    -> Natural
visibleFiniteEvidenceRuleBinderArity =
    checkedNotionRuleBinderArity
        . finiteEvidenceSkeleton
        . visibleFiniteEvidenceRulePayload

visibleFiniteEvidenceRuleConclusionHead
    :: VisibleFiniteEvidenceRule
    -> NotionHeadKey
visibleFiniteEvidenceRuleConclusionHead =
    templateHead
        . checkedNotionRuleConclusion
        . finiteEvidenceSkeleton
        . visibleFiniteEvidenceRulePayload

data VisibleWholeConclusionRule = VisibleWholeConclusionRule
    !SemanticFactBranch !WholeConclusionRule
    deriving stock (Show, Eq)

visibleWholeConclusionRule
    :: SemanticFactBranch -> WholeConclusionRule -> CheckedPropositionContent
    -> [CanonicalTerm ObjectId] -> Either Text VisibleWholeConclusionRule
visibleWholeConclusionRule branch rule proposition expectedPremises = do
    body <- open (wholeConclusionArity rule) (frozenCoreTerm (checkedPropositionTerm proposition))
    conclusion <- foldM consume body expectedPremises
    unless (projectConjunctionPath (semanticFactBranchPath branch) conclusion
        == Just (residualTemplateFormula (wholeConclusionTemplate rule)))
        (Left "a whole-conclusion theorem has the wrong conclusion")
    pure (VisibleWholeConclusionRule branch rule)
  where
    open 0 body = Right body
    open remaining (CForall TySet body) = open (remaining - 1) body
    open _ _ = Left "a whole-conclusion theorem has the wrong universal binder prefix"
    consume (CImp actual body) expected | actual == expected = Right body
    consume _ _ = Left "a whole-conclusion theorem has the wrong premise grouping"

visibleWholeConclusionRuleSource :: VisibleWholeConclusionRule -> SemanticFactBranch
visibleWholeConclusionRuleSource (VisibleWholeConclusionRule source _) = source

visibleWholeConclusionRulePayload :: VisibleWholeConclusionRule -> WholeConclusionRule
visibleWholeConclusionRulePayload (VisibleWholeConclusionRule _ rule) = rule

data VisibleGraphDomainRule = VisibleGraphDomainRule
    !SemanticFactBranch
    !GraphDomainRule
    !Natural
    deriving stock (Show, Eq)

visibleGraphDomainRule
    :: SemanticFactBranch
    -> GraphDomainRule
    -> CheckedPropositionContent
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either Text VisibleGraphDomainRule
visibleGraphDomainRule branch rule proposition expectedPremise expectedConclusion = do
    let variables = Set.fromList
            [ variableIndex (graphDomainLeft rule)
            , variableIndex (graphDomainRight rule)
            , variableIndex (graphDomainGraph rule)
            ]
        binderArity = fromIntegral (Set.size variables)
        denseVariables = if binderArity == 0
            then Set.empty
            else Set.fromList [0 .. binderArity - 1]
    unless (variables == denseVariables)
        (Left
            "a graph-domain rule must have a dense premise-determined context")
    body <- stripSetForalls binderArity
        (frozenCoreTerm (checkedPropositionTerm proposition))
    case body of
        CImp premise conclusion
            | premise == expectedPremise
              && projectConjunctionPath (semanticFactBranchPath branch) conclusion == Just expectedConclusion ->
                pure (VisibleGraphDomainRule branch rule binderArity)
        CImp{} ->
            Left "a graph-domain theorem does not match its registered schema"
        _ -> Left "a graph-domain theorem is not a unary implication"
  where
    variableIndex (ViewVariableIx index) = index

    stripSetForalls 0 term = Right term
    stripSetForalls remaining term =
        case term of
            CForall TySet body -> stripSetForalls (remaining - 1) body
            _ ->
                Left
                    "a graph-domain theorem has the wrong universal binder prefix"

visibleGraphDomainRuleSource :: VisibleGraphDomainRule -> SemanticFactBranch
visibleGraphDomainRuleSource (VisibleGraphDomainRule source _payload _metadata) = source

visibleGraphDomainRulePayload
    :: VisibleGraphDomainRule
    -> GraphDomainRule
visibleGraphDomainRulePayload
        (VisibleGraphDomainRule _source declaration _binderArity) = declaration

visibleGraphDomainRuleBinderArity :: VisibleGraphDomainRule -> Natural
visibleGraphDomainRuleBinderArity
        (VisibleGraphDomainRule _source _declaration binderArity) = binderArity

atomRuleVariables
    :: AtomTemplate RuleTermTemplate
    -> Set Natural
atomRuleVariables = Set.fromList
    . concatMap ruleTermVariableIndices
    . toList

ruleTermVariableIndices :: RuleTermTemplate -> [Natural]
ruleTermVariableIndices =
    fmap (\(ViewVariableIx index) -> index)
        . Set.toList
        . RuleTerm.ruleTermTemplateVariables

recursiveRuleTermTemplates :: RuleTermTemplate -> [RuleTermTemplate]
recursiveRuleTermTemplates =
    toList . RuleTerm.recursiveRuleTermTemplates

premiseTerms
    :: RulePremiseBundles RuleTermTemplate
    -> [RuleTermTemplate]
premiseTerms (RulePremiseBundles bundles) =
    concatMap treeTerms (toList bundles)
  where
    treeTerms = \case
        RulePremiseAtom atom -> toList atom
        RulePremiseAnd left right -> treeTerms left <> treeTerms right
        RulePremiseUniversal universal -> foldMap (foldMap (foldMap toList)) universal
        RulePremiseResidual _ -> []

-- | Query-facing buckets built from an already deterministic visible view
-- inventory.  Reverse reachability keeps search expected-directed, while the
-- premise buckets prevent saturation from scanning unrelated registrations.
data FormationSearchLimits = FormationSearchLimits
    { formationMaximumRelevantHeadEdges :: !Natural
    , formationMaximumRelevantViews :: !Natural
    , formationMaximumGroundAtoms :: !Natural
    , formationMaximumInferenceInspections :: !Natural
    , formationMaximumDerivationNodes :: !Natural
    , formationMaximumDerivationDepth :: !Natural
    , formationMaximumEqualityChainLength :: !Natural
    }
    deriving stock (Show, Eq)

formationSearchLimits
    :: Natural
    -> Natural
    -> Natural
    -> Natural
    -> Natural
    -> Natural
    -> Maybe FormationSearchLimits
formationSearchLimits relevantHeadEdges relevantViews groundAtoms inferenceInspections
        derivationNodes derivationDepth
    = formationSearchLimitsWithEqualityChain
        relevantHeadEdges relevantViews groundAtoms inferenceInspections
        derivationNodes derivationDepth groundAtoms

formationSearchLimitsWithEqualityChain
    :: Natural
    -> Natural
    -> Natural
    -> Natural
    -> Natural
    -> Natural
    -> Natural
    -> Maybe FormationSearchLimits
formationSearchLimitsWithEqualityChain
        relevantHeadEdges relevantViews groundAtoms inferenceInspections
        derivationNodes derivationDepth equalityChainLength
    | relevantHeadEdges == 0 = Nothing
    | relevantViews == 0 = Nothing
    | groundAtoms == 0 = Nothing
    | inferenceInspections == 0 = Nothing
    | derivationNodes == 0 = Nothing
    | equalityChainLength == 0 = Nothing
    | otherwise =
        Just
            (FormationSearchLimits
                relevantHeadEdges
                relevantViews
                groundAtoms
                inferenceInspections
                derivationNodes
                derivationDepth
                equalityChainLength)

-- The derivation bounds remain strictly below the ordinary replay limits
-- (200000 nodes and depth 2048).  Search bounds stop hostile or accidental
-- closure growth before a derivation is allocated.
-- The shared group inspection allowance is calibrated against completed
-- library groups; declaration and scope preparation keep independent caps.
defaultFormationSearchLimits :: FormationSearchLimits
defaultFormationSearchLimits =
    FormationSearchLimits 65536 131072 65536 524288 100000 1024 1024

data FormationSearchError
    = FormationRelevantHeadEdgeLimitExceeded !Natural !Natural
    | FormationRelevantViewLimitExceeded !Natural !Natural
    | FormationGroundAtomLimitExceeded !Natural !Natural
    | FormationInferenceInspectionLimitExceeded !Natural !Natural
    | FormationDerivationNodeLimitExceeded !Natural !Natural
    | FormationDerivationDepthLimitExceeded !Natural !Natural
    | FormationEqualityChainLimitExceeded !Natural !Natural
    deriving stock (Show, Eq)

renderFormationSearchError :: FormationSearchError -> Text
renderFormationSearchError = \case
    FormationRelevantHeadEdgeLimitExceeded limit actual ->
        exceeded "relevant notion-head edges" limit actual
    FormationRelevantViewLimitExceeded limit actual ->
        exceeded "relevant notion views" limit actual
    FormationGroundAtomLimitExceeded limit actual ->
        exceeded "ground notion atoms" limit actual
    FormationInferenceInspectionLimitExceeded limit actual ->
        exceeded "inference inspections" limit actual
    FormationDerivationNodeLimitExceeded limit actual ->
        exceeded "derivation nodes" limit actual
    FormationDerivationDepthLimitExceeded limit actual ->
        exceeded "derivation depth" limit actual
    FormationEqualityChainLimitExceeded limit actual ->
        exceeded "equality-transport chain length" limit actual
  where
    exceeded resource limit actual =
        "notion checking observed " <> Text.pack (show actual) <> " " <> resource
            <> ", exceeding the configured limit " <> Text.pack (show limit)

-- | Transient work performed by one top-level formation query.  Unary-view,
-- provider-rule, and composite-rule inspections remain separate diagnostics.
-- Every newly demanded composite goal is also recorded as a composite premise
-- request.  View, provider, composite, and source-index inspections consume
-- the shared inference-inspection limit; indexed rows consume the shared
-- ground-atom limit.
-- Provider depth composes by maximum; every other field is additive across
-- recursive requests.
data FormationSearchStatistics = FormationSearchStatistics
    { formationSearchRelevantHeadEdges :: !Natural
    , formationSearchRelevantViews :: !Natural
    , formationSearchDirectGroundAtoms :: !Natural
    , formationSearchViewInspections :: !Natural
    , formationSearchDerivedGroundAtoms :: !Natural
    , formationSearchProviderOccurrences :: !Natural
    , formationSearchProviderRuleInspections :: !Natural
    , formationSearchProviderPremiseRequests :: !Natural
    , formationSearchCompositeRuleInspections :: !Natural
    , formationSearchCompositePremiseRequests :: !Natural
    , formationSearchEqualitySourceInspections :: !Natural
    , formationSearchEqualityEdgeInspections :: !Natural
    , formationSearchEqualityTransportSteps :: !Natural
    , formationSearchSourceIndexInspections :: !Natural
    , formationSearchIndexedRows :: !Natural
    , formationSearchMaximumProviderDepth :: !Natural
    } deriving stock (Show, Eq)

-- | One requirement group shares structural work across its leaf searches,
-- including arena construction. The emitted kernel proof has separate node
-- and depth limits; reusing a founded witness does not unfold its proof tree.
data FormationSearchBudget = FormationSearchBudget
    { budgetLimits :: !FormationSearchLimits
    , budgetStatistics :: !FormationSearchStatistics
    , budgetDiagnostics :: !Diagnostics.Diagnostics
    , budgetFamily :: !(Maybe Diagnostics.RegistrationFamily)
    , budgetPhase :: !Diagnostics.Phase
    , budgetRejectedDebit :: !(Maybe FormationSearchStatistics)
    } deriving stock (Show, Eq)

initialFormationSearchBudget :: FormationSearchLimits -> FormationSearchBudget
initialFormationSearchBudget limits = FormationSearchBudget limits
    emptyFormationSearchStatistics Diagnostics.emptyDiagnostics Nothing Diagnostics.Query Nothing

formationSearchBudgetStatistics :: FormationSearchBudget -> FormationSearchStatistics
formationSearchBudgetStatistics = budgetStatistics

formationSearchBudgetLimits :: FormationSearchBudget -> FormationSearchLimits
formationSearchBudgetLimits = budgetLimits

formationSearchBudgetDiagnostics :: FormationSearchBudget -> Diagnostics.Diagnostics
formationSearchBudgetDiagnostics = budgetDiagnostics

formationSearchBudgetMeasurement :: FormationSearchBudget -> Diagnostics.Measurement
formationSearchBudgetMeasurement budget = Diagnostics.emptyMeasurement
    { Diagnostics.measuredDiagnostics = budgetDiagnostics budget
    , Diagnostics.limitHighWater = Map.fromList
        [ ("inference.used", formationSearchInferenceInspections statistics)
        , ("inference.cap", formationMaximumInferenceInspections limits)
        , ("heads.used", formationSearchRelevantHeadEdges statistics)
        , ("heads.cap", formationMaximumRelevantHeadEdges limits)
        , ("views.used", formationSearchRelevantViews statistics)
        , ("views.cap", formationMaximumRelevantViews limits)
        , ("rows.used", formationSearchIndexedRows statistics
            + formationSearchDirectGroundAtoms statistics + formationSearchDerivedGroundAtoms statistics)
        , ("rows.cap", formationMaximumGroundAtoms limits)
        ] <> maybe Map.empty (Map.singleton "inference.rejected" . formationSearchInferenceInspections)
            (formationSearchRejectedDebit budget) }
  where
    statistics = budgetStatistics budget
    limits = budgetLimits budget

recordFormationOperation :: Diagnostics.Operation -> Natural -> FormationSearchBudget -> FormationSearchBudget
recordFormationOperation operation amount budget = budget
    {budgetDiagnostics = Diagnostics.countOperation operation amount (budgetDiagnostics budget)}

recordFormationCoreWork :: Natural -> FormationSearchBudget -> FormationSearchBudget
recordFormationCoreWork amount budget = budget
    {budgetDiagnostics = Diagnostics.countCoreWork (budgetPhase budget) amount (budgetDiagnostics budget)}

recordFormationOutcome :: Diagnostics.Outcome -> FormationSearchBudget -> FormationSearchBudget
recordFormationOutcome outcome budget = budget
    {budgetDiagnostics = Diagnostics.countOutcome outcome (budgetDiagnostics budget)}

setFormationRegistrationFamily :: Maybe Diagnostics.RegistrationFamily -> FormationSearchBudget -> FormationSearchBudget
setFormationRegistrationFamily family budget = budget {budgetFamily = family}

formationSearchBudgetPhase :: FormationSearchBudget -> Diagnostics.Phase
formationSearchBudgetPhase = budgetPhase

setFormationSearchPhase :: Diagnostics.Phase -> FormationSearchBudget -> FormationSearchBudget
setFormationSearchPhase phase budget = budget {budgetPhase = phase}

formationSearchRejectedDebit :: FormationSearchBudget -> Maybe FormationSearchStatistics
formationSearchRejectedDebit = budgetRejectedDebit

-- Retain the attempted debit separately: precharging a rejected operation did
-- not perform that operation. Error finalization still owns the accepted work.
recordFormationRejectedDebit :: FormationSearchStatistics -> FormationSearchBudget -> FormationSearchBudget
recordFormationRejectedDebit debit budget = budget {budgetRejectedDebit = Just debit}

formationInferenceWorkRemaining :: FormationSearchBudget -> Natural
formationInferenceWorkRemaining = formationMaximumInferenceInspections . remainingFormationSearchLimits

formationInferenceWorkUsed :: FormationSearchBudget -> Natural
formationInferenceWorkUsed budget = formationMaximumInferenceInspections (formationSearchBudgetLimits budget)
    - formationInferenceWorkRemaining budget

remainingFormationSearchLimits
    :: FormationSearchBudget
    -> FormationSearchLimits
remainingFormationSearchLimits budget =
    limits
        { formationMaximumRelevantHeadEdges = remaining
            formationMaximumRelevantHeadEdges
            formationSearchRelevantHeadEdges
        , formationMaximumRelevantViews = remaining
            formationMaximumRelevantViews
            formationSearchRelevantViews
        , formationMaximumGroundAtoms = remainingGroundAtoms
        , formationMaximumInferenceInspections = remaining
            formationMaximumInferenceInspections
            formationSearchInferenceInspections
        }
  where
    limits = budgetLimits budget
    consumed = budgetStatistics budget
    remaining maximumField usedField =
        maximumField limits - min (maximumField limits) (usedField consumed)
    usedGroundAtoms =
        formationSearchDirectGroundAtoms consumed
            + formationSearchDerivedGroundAtoms consumed
            + formationSearchIndexedRows consumed
    remainingGroundAtoms =
        formationMaximumGroundAtoms limits
            - min (formationMaximumGroundAtoms limits) usedGroundAtoms

consumeFormationSearchStatistics
    :: FormationSearchStatistics
    -> FormationSearchBudget
    -> Either FormationSearchError FormationSearchBudget
consumeFormationSearchStatistics added budget = do
    checkRelevantHeadEdgeLimit limits
        (formationSearchRelevantHeadEdges combined)
    checkRelevantViewLimit limits
        (formationSearchRelevantViews combined)
    checkGroundAtomLimit limits
        ( formationSearchDirectGroundAtoms combined
            + formationSearchDerivedGroundAtoms combined
            + formationSearchIndexedRows combined
        )
    checkInferenceInspectionLimit limits
        (formationSearchInferenceInspections combined)
    checkFormationSearchDepth limits
        (formationSearchMaximumProviderDepth combined)
    pure budget {budgetStatistics = combined, budgetDiagnostics = attributed}
  where
    limits = budgetLimits budget
    combined = addFormationSearchStatistics (budgetStatistics budget) added
    work = formationSearchInferenceInspections added
    counted = Diagnostics.countPhaseWork (budgetPhase budget) work (budgetDiagnostics budget)
    attributed = maybe counted (\owner -> Diagnostics.countFamilyWork owner work counted) (budgetFamily budget)

formationSearchInferenceInspections :: FormationSearchStatistics -> Natural
formationSearchInferenceInspections statistics =
    formationSearchViewInspections statistics
        + formationSearchProviderRuleInspections statistics
        + formationSearchCompositeRuleInspections statistics
        + formationSearchCompositePremiseRequests statistics
        + formationSearchEqualitySourceInspections statistics
        + formationSearchEqualityEdgeInspections statistics
        + formationSearchEqualityTransportSteps statistics
        + formationSearchSourceIndexInspections statistics

checkFormationSearchDepth
    :: FormationSearchLimits
    -> Natural
    -> Either FormationSearchError ()
checkFormationSearchDepth limits depth
    | depth > formationMaximumDerivationDepth limits =
        Left
            (FormationDerivationDepthLimitExceeded
                (formationMaximumDerivationDepth limits)
                depth)
    | otherwise = Right ()

emptyFormationSearchStatistics :: FormationSearchStatistics
emptyFormationSearchStatistics =
    FormationSearchStatistics
        { formationSearchRelevantHeadEdges = 0
        , formationSearchRelevantViews = 0
        , formationSearchDirectGroundAtoms = 0
        , formationSearchViewInspections = 0
        , formationSearchDerivedGroundAtoms = 0
        , formationSearchProviderOccurrences = 0
        , formationSearchProviderRuleInspections = 0
        , formationSearchProviderPremiseRequests = 0
        , formationSearchCompositeRuleInspections = 0
        , formationSearchCompositePremiseRequests = 0
        , formationSearchEqualitySourceInspections = 0
        , formationSearchEqualityEdgeInspections = 0
        , formationSearchEqualityTransportSteps = 0
        , formationSearchSourceIndexInspections = 0
        , formationSearchIndexedRows = 0
        , formationSearchMaximumProviderDepth = 0
        }

addFormationSearchStatistics
    :: FormationSearchStatistics
    -> FormationSearchStatistics
    -> FormationSearchStatistics
addFormationSearchStatistics left right =
    FormationSearchStatistics
        { formationSearchRelevantHeadEdges =
            formationSearchRelevantHeadEdges left
                + formationSearchRelevantHeadEdges right
        , formationSearchRelevantViews =
            formationSearchRelevantViews left
                + formationSearchRelevantViews right
        , formationSearchDirectGroundAtoms =
            formationSearchDirectGroundAtoms left
                + formationSearchDirectGroundAtoms right
        , formationSearchViewInspections =
            formationSearchViewInspections left
                + formationSearchViewInspections right
        , formationSearchDerivedGroundAtoms =
            formationSearchDerivedGroundAtoms left
                + formationSearchDerivedGroundAtoms right
        , formationSearchProviderOccurrences =
            formationSearchProviderOccurrences left
                + formationSearchProviderOccurrences right
        , formationSearchProviderRuleInspections =
            formationSearchProviderRuleInspections left
                + formationSearchProviderRuleInspections right
        , formationSearchProviderPremiseRequests =
            formationSearchProviderPremiseRequests left
                + formationSearchProviderPremiseRequests right
        , formationSearchCompositeRuleInspections =
            formationSearchCompositeRuleInspections left
                + formationSearchCompositeRuleInspections right
        , formationSearchCompositePremiseRequests =
            formationSearchCompositePremiseRequests left
                + formationSearchCompositePremiseRequests right
        , formationSearchEqualitySourceInspections =
            formationSearchEqualitySourceInspections left
                + formationSearchEqualitySourceInspections right
        , formationSearchEqualityEdgeInspections =
            formationSearchEqualityEdgeInspections left
                + formationSearchEqualityEdgeInspections right
        , formationSearchEqualityTransportSteps =
            formationSearchEqualityTransportSteps left
                + formationSearchEqualityTransportSteps right
        , formationSearchSourceIndexInspections =
            formationSearchSourceIndexInspections left
                + formationSearchSourceIndexInspections right
        , formationSearchIndexedRows =
            formationSearchIndexedRows left
                + formationSearchIndexedRows right
        , formationSearchMaximumProviderDepth =
            max
                (formationSearchMaximumProviderDepth left)
                (formationSearchMaximumProviderDepth right)
        }

-- A search answer owns a reference into its requirement's recipe arena.
-- Selected evidence owns only its compact graph and used sources.
data FormationMetadata = FormationMetadata
    { metadataGroundKey :: !GroundNotionKey
    , metadataCost :: !FormationDerivationCost
    , metadataSummary :: !FormationSummary
    , metadataDirectOrdinal :: !(Maybe Natural)
    }

data FormationEvidence origin = FormationEvidence
    !FormationMetadata !(MaterializedFormationEvidence origin)

type role FormationWitness nominal representational
data FormationWitness scope origin = FormationWitness
    !FormationMetadata !FormationRecipeId

type role FormationWitnessArena nominal nominal
newtype FormationWitnessArena scope origin = FormationWitnessArena (FormationArena origin)

type FormationConstruction scope origin m =
    Reader.ReaderT (Bool -> m ())
        (Except.ExceptT FormationSearchError (State.StateT (FormationWitnessArena scope origin) m))

withFormationWitnessArena
    :: (forall scope. FormationWitnessArena scope origin -> m result) -> m result
withFormationWitnessArena action = action (FormationWitnessArena emptyFormationArena)

runFormationConstruction
    :: (Bool -> m ()) -> FormationConstruction scope origin m value -> FormationWitnessArena scope origin
    -> m (Either FormationSearchError value, FormationWitnessArena scope origin)
runFormationConstruction observe action = State.runStateT (Except.runExceptT (Reader.runReaderT action observe))

inFormationArena
    :: Monad m => ((Bool -> m ()) -> State.StateT (FormationArena origin) m value)
    -> FormationConstruction scope origin m value
-- The callback records each actual allocation outside the arena's rollback.
-- Merely comparing arena sizes after success would lose work on exhaustion.
inFormationArena action = do
    observe <- Reader.ask
    lift (lift (State.StateT (\(FormationWitnessArena arena) -> do
        (result, next) <- State.runStateT (action observe) arena
        pure (result, FormationWitnessArena next))))

type role FormationHypothesisReference nominal representational
data FormationHypothesisReference scope origin = FormationHypothesisReference
    !(ScopedCheckedCore ObjectId) !origin !FormationRecipeId

prepareFormationHypothesis
    :: (Monad m, Ord origin) => (Natural -> m ()) -> ScopedCheckedCore ObjectId -> origin
    -> FormationConstruction scope origin m (FormationHypothesisReference scope origin)
prepareFormationHypothesis charge proposition origin = do
    reference <- inFormationArena (\observe -> arenaHypothesis charge observe (MaterializedNotionHypothesis proposition origin))
    pure (FormationHypothesisReference proposition origin reference)

formationHypothesisProposition :: FormationHypothesisReference scope origin -> ScopedCheckedCore ObjectId
formationHypothesisProposition (FormationHypothesisReference proposition _ _) = proposition

formationWitnessGroundKey :: FormationWitness scope origin -> GroundNotionKey
formationWitnessGroundKey (FormationWitness metadata _) = metadataGroundKey metadata

formationWitnessDerivationNodes :: FormationWitness scope origin -> Natural
formationWitnessDerivationNodes (FormationWitness metadata _) = let FormationDerivationCost nodes _ = metadataCost metadata in nodes

formationWitnessEqualitySteps :: FormationWitness scope origin -> Natural
formationWitnessEqualitySteps (FormationWitness metadata _) = summaryEqualitySteps (metadataSummary metadata)

preferDirectFormationWitness
    :: FormationWitness scope origin -> FormationWitness scope origin -> FormationWitness scope origin
preferDirectFormationWitness current@(FormationWitness old _) candidate@(FormationWitness new _)
    | preferDirectMetadata old new = candidate
    | otherwise = current

selectFormationEvidence
    :: Monad m => (Natural -> m ()) -> FormationSearchLimits -> FormationWitness scope origin
    -> FormationConstruction scope origin m (FormationEvidence origin)
selectFormationEvidence charge limits (FormationWitness metadata reference) = do
    selected <- inFormationArena (\_ -> arenaSelect charge
        (formationMaximumDerivationNodes limits, formationMaximumDerivationDepth limits) reference)
    pure (FormationEvidence metadata selected)

-- | One operational rich shape coupled to evidence for exactly its erased
-- logical atom.  The constructor is private: clients may retain source shape
-- only after checking this equality at the query boundary.
data ProvedRichGoal rich origin = ProvedRichGoal
    !rich
    !(FormationEvidence origin)

provedRichGoal
    :: (rich -> GroundNotionKey)
    -> rich
    -> FormationEvidence origin
    -> Maybe (ProvedRichGoal rich origin)
provedRichGoal erase shape evidence
    | erase shape == formationEvidenceGroundKey evidence =
        Just (ProvedRichGoal shape evidence)
    | otherwise = Nothing

provedRichGoalShape :: ProvedRichGoal rich origin -> rich
provedRichGoalShape (ProvedRichGoal shape _evidence) = shape

provedRichGoalEvidence
    :: ProvedRichGoal rich origin
    -> FormationEvidence origin
provedRichGoalEvidence (ProvedRichGoal _shape evidence) = evidence

formationEvidenceGroundKey :: FormationEvidence origin -> GroundNotionKey
formationEvidenceGroundKey (FormationEvidence metadata _) = metadataGroundKey metadata

formationEvidenceImports
    :: FormationEvidence origin
    -> Vector SemanticFactOccurrenceFingerprint
formationEvidenceImports (FormationEvidence _ selected) = materializedFormationImports selected

-- The theorem step establishing the requested atom, after conversions. This
-- observes the selected witness; it does not infer a branch from a catalog.
formationEvidenceBranch :: FormationEvidence origin -> Maybe SemanticFactBranch
formationEvidenceBranch (FormationEvidence metadata _) = summaryBranch (metadataSummary metadata)

formationEvidenceDerivationNodes :: FormationEvidence origin -> Natural
formationEvidenceDerivationNodes (FormationEvidence metadata _) =
    let FormationDerivationCost nodes _depth = metadataCost metadata
    in nodes

formationEvidenceDerivationDepth :: FormationEvidence origin -> Natural
formationEvidenceDerivationDepth (FormationEvidence metadata _) =
    let FormationDerivationCost _nodes depth = metadataCost metadata
    in depth

formationEvidenceProviderRuleSteps :: FormationEvidence origin -> Natural
formationEvidenceProviderRuleSteps (FormationEvidence metadata _) = summaryProviderSteps (metadataSummary metadata)

-- A scalar description of the selected proof, never a witness preference.
formationEvidenceCompositeLevel :: FormationEvidence origin -> Natural
formationEvidenceCompositeLevel (FormationEvidence metadata _) = summaryCompositeLevel (metadataSummary metadata)

formationEvidenceUsesEquality :: FormationEvidence origin -> Bool
formationEvidenceUsesEquality = (> 0) . formationEvidenceEqualityTransportSteps

formationEvidenceEqualityTransportSteps :: FormationEvidence origin -> Natural
formationEvidenceEqualityTransportSteps (FormationEvidence metadata _) = summaryEqualitySteps (metadataSummary metadata)

-- Exact direct lookup retains source/view ordinal order and its cost tie-break.
-- Once search has started, founded composite witnesses are never reranked.
preferDirectFormationEvidence
    :: FormationEvidence origin -> FormationEvidence origin -> FormationEvidence origin
preferDirectFormationEvidence current candidate
    | preferDirectCandidate current candidate = candidate
    | otherwise = current

preferDirectCandidate :: FormationEvidence origin -> FormationEvidence origin -> Bool
preferDirectCandidate (FormationEvidence old _) (FormationEvidence new _) = preferDirectMetadata old new

preferDirectMetadata :: FormationMetadata -> FormationMetadata -> Bool
preferDirectMetadata current candidate = case (metadataDirectOrdinal current, metadataDirectOrdinal candidate) of
    (Just old, Just new) -> preference new candidate < preference old current
    (Nothing, Just _) -> True
    _ -> False
  where
    preference ordinal metadata = let FormationDerivationCost nodes depth = metadataCost metadata
        in (ordinal,nodes,depth)

materializedNotionHypothesis
    :: ScopedCheckedCore ObjectId
    -> origin
    -> MaterializedNotionHypothesis origin
materializedNotionHypothesis = MaterializedNotionHypothesis

materializedNotionHypothesisProposition
    :: MaterializedNotionHypothesis origin
    -> ScopedCheckedCore ObjectId
materializedNotionHypothesisProposition
        (MaterializedNotionHypothesis proposition _origin) =
    proposition

materializedNotionHypothesisOrigin
    :: MaterializedNotionHypothesis origin
    -> origin
materializedNotionHypothesisOrigin
        (MaterializedNotionHypothesis _proposition origin) =
    origin

data FormationProofError
    = FormationProofHypothesisCountMismatch !Natural !Natural
    | FormationProofHypothesisMismatch !HypothesisIx
    | FormationProofImportCountMismatch !Natural !Natural
    | FormationProofInvalidRecipe
    | FormationProofKernelError !KernelProofBuildError
    | FormationProofDerivationLimitExceeded !FormationSearchError
    deriving stock (Show, Eq)

materializedFormationHypotheses
    :: MaterializedFormationEvidence origin
    -> Vector (MaterializedNotionHypothesis origin)
materializedFormationHypotheses
        (MaterializedFormationEvidence hypotheses _imports _recipe _limits) =
    hypotheses

materializedFormationHypothesisPropositions
    :: MaterializedFormationEvidence origin
    -> Vector (ScopedCheckedCore ObjectId)
materializedFormationHypothesisPropositions =
    fmap materializedNotionHypothesisProposition
        . materializedFormationHypotheses

materializedFormationImports
    :: MaterializedFormationEvidence origin
    -> Vector SemanticFactOccurrenceFingerprint
materializedFormationImports
        (MaterializedFormationEvidence _hypotheses imports _recipe _limits) =
    imports


data FormationSearchOutcome origin
    = FormationFound
        !(FormationEvidence origin)
        !FormationSearchStatistics
    | FormationNotFound !(FormationFailureExplanation origin)

-- | A source-backed answer retained by a failed expected-directed search.
-- Greater derivation-node counts rank first; stable order breaks ties.
-- Ground arguments stay private to the search:
-- parameter-erasing views do not determine them, and canonical terms are not
-- suitable source diagnostics.
data FormationFailureFrontier origin = FormationFailureFrontier
    { formationFailureFrontierHead :: !NotionHeadKey
    , formationFailureFrontierOrigin :: !origin
    } deriving stock (Show, Eq)

-- | Bounded data retained from the actual failed search. It is
-- deliberately structural: elaboration decides how to explain the selected
-- source occurrence without reconstructing search in the reporting layer.
data FormationFailureExplanation origin = FormationFailureExplanation
    { formationFailureStatistics :: !FormationSearchStatistics
    , formationFailureFrontier :: !(Maybe (FormationFailureFrontier origin))
    , formationFailureConsideredParameterErasure :: !Bool
    } deriving stock (Show, Eq)

-- | One checked local equality edge.  Its source proposition and conjunction
-- path are inseparable from the exact equality judgement used during replay.
-- The constructor is private so transport evidence cannot cite a formula
-- which the retained source does not project.
data FormationEqualityTransport origin = FormationEqualityTransport
    !(DirectFormationSource origin)
    !(ScopedCheckedCore ObjectId)
    !FormationEqualityDirection

formationEqualityTransport
    :: DirectFormationSource origin
    -> ScopedCheckedCore ObjectId
    -> FormationEqualityDirection
    -> Maybe (FormationEqualityTransport origin)
formationEqualityTransport source equality direction = do
    guard (scopedCoreType equality == TyProp)
    guard (scopedCoreContext equality
        == scopedCoreContext (directSourceProposition source))
    projected <- projectConjunctionPath
        (directSourcePath source)
        (scopedCoreTerm (directSourceProposition source))
    guard (projected == scopedCoreTerm equality)
    case scopedCoreTerm equality of
        CEq TySet _left _right ->
            Just (FormationEqualityTransport source equality direction)
        _ -> Nothing

transportSourceOrdinal :: FormationEqualityTransport origin -> Natural
transportSourceOrdinal
        (FormationEqualityTransport source _equality _direction) =
    directSourceOrdinal source

-- A selected source may be viewed through compiler-owned local equalities.
-- This is a proof of the whole source, never an atomic observation or rule.
data FormationSourceEvidence origin = FormationSourceEvidence
    !(DirectFormationSource origin)
    !(Maybe (NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId),
        ScopedCheckedCore ObjectId, ScopedCheckedCore ObjectId))
    !FormationDerivationCost

directFormationSourceEvidence :: DirectFormationSource origin -> FormationSourceEvidence origin
directFormationSourceEvidence source = FormationSourceEvidence source Nothing (directFormationCost source)

-- A scope owner has already checked nominal descent. Align only the selected
-- source and its alias evidence, preserving all source identities and paths.
countedAlignFormationSourceEvidence
    :: Word -> [CoreType] -> FormationSourceEvidence origin
    -> (Either (CountedCoreFailure Text) (FormationSourceEvidence origin), Word)
countedAlignFormationSourceEvidence allowance context (FormationSourceEvidence source transport cost) =
    State.runState (Except.runExceptT do
        source' <- alignFormationDirect context source
        transport' <- for transport \(steps, premise, target) ->
            (,,) <$> traverse alignStep steps <*> align premise <*> align target
        pure (FormationSourceEvidence source' transport' cost)) allowance
  where
    align = alignFormationChecked context
    alignStep (edge, predicate) = do
        edge' <- alignFormationEquality context edge
        predicate' <- align predicate
        pure (edge', predicate')

countedAlignFormationEqualityTransport
    :: Word -> [CoreType] -> FormationEqualityTransport origin
    -> (Either (CountedCoreFailure Text) (FormationEqualityTransport origin), Word)
countedAlignFormationEqualityTransport allowance context edge =
    State.runState (Except.runExceptT (alignFormationEquality context edge)) allowance

type FormationAlignment = Except.ExceptT (CountedCoreFailure Text) (State.State Word)

alignFormationChecked :: [CoreType] -> ScopedCheckedCore ObjectId -> FormationAlignment (ScopedCheckedCore ObjectId)
alignFormationChecked context scoped = do
    available <- State.get
    let (result, remaining) = countedAlignScopedCore available context scoped
    State.put remaining
    case result of
        Left CountedCoreStructuralWorkExhausted -> Except.throwE CountedCoreStructuralWorkExhausted
        Right Nothing -> Except.throwE (CountedCoreOperationFailed "formation evidence escaped its scope")
        Right (Just value) -> pure value

alignFormationDirect :: [CoreType] -> DirectFormationSource origin -> FormationAlignment (DirectFormationSource origin)
alignFormationDirect context source = do
    proposition <- alignFormationChecked context (directSourceProposition source)
    pure source {directSourceProposition = proposition}

alignFormationEquality :: [CoreType] -> FormationEqualityTransport origin -> FormationAlignment (FormationEqualityTransport origin)
alignFormationEquality context (FormationEqualityTransport source equality direction) =
    FormationEqualityTransport <$> alignFormationDirect context source
        <*> alignFormationChecked context equality <*> pure direction

formationSourceEvidenceOrdinal :: FormationSourceEvidence origin -> Natural
formationSourceEvidenceOrdinal (FormationSourceEvidence source _ _) = directSourceOrdinal source

formationSourceEvidenceAliasOrdinals :: FormationSourceEvidence origin -> [Natural]
formationSourceEvidenceAliasOrdinals = snd . sourceEvidenceEqualitySummary

sourceEvidenceCost :: FormationSourceEvidence origin -> FormationDerivationCost
sourceEvidenceCost (FormationSourceEvidence _ _ cost) = cost

sourceEvidenceEqualitySummary :: FormationSourceEvidence origin -> (Natural, [Natural])
sourceEvidenceEqualitySummary (FormationSourceEvidence _ transport _) =
    maybe (0, []) (\(steps, _, _) -> (fromIntegral (length steps), transportSourceOrdinal . fst <$> toList steps)) transport

transportFormationSourceWithLimits
    :: FormationSearchLimits -> DirectFormationSource origin
    -> NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> Either FormationSearchError (FormationSourceEvidence origin)
transportFormationSourceWithLimits limits source steps premise target = do
    validateSubstitutionScopes steps premise target
    unless (projectConjunctionPath (directSourcePath source) (scopedCoreTerm (directSourceProposition source))
            == Just (scopedCoreTerm premise)
            && scopedCoreContext (directSourceProposition source) == scopedCoreContext premise)
        (impossible "source transport does not select its original proposition")
    let count = fromIntegral (length steps)
        cost = finishTransportCost (foldl' (\current (transport, _) -> extendTransportCost current transport)
            (finishTransportCost (directFormationCost source)) steps)
    when (count > formationMaximumEqualityChainLength limits)
        (Left (FormationEqualityChainLimitExceeded (formationMaximumEqualityChainLength limits) count))
    pure (FormationSourceEvidence source (Just (steps, premise, target)) cost)

data ImportedApplicationKind = ViewApplication | RuleApplication

data FormationPremiseEvidence scope origin
    = FormationPremiseEvidenceTruth
    | FormationPremiseEvidenceLeaf !(FormationWitness scope origin)
    | FormationPremiseEvidenceSupplied !(FormationSourceEvidence origin) !UniversalAdapter
    | FormationPremiseEvidenceAnd
        !(FormationPremiseEvidence scope origin)
        !(FormationPremiseEvidence scope origin)
    | FormationPremiseEvidenceOr !Bool !(ScopedCheckedCore ObjectId)
        !(FormationPremiseEvidence scope origin)
    | FormationPremiseEvidenceIff !(ScopedCheckedCore ObjectId)
        !(FormationPremiseEvidence scope origin) !(FormationPremiseEvidence scope origin)
    | FormationPremiseEvidenceExists !(ScopedCheckedCore ObjectId) !(CanonicalTerm ObjectId)
        !(FormationPremiseEvidence scope origin)
    | FormationPremiseEvidenceReflexivity !(CanonicalTerm ObjectId)

data FormationDerivationCost = FormationDerivationCost !Natural !Natural
    deriving stock (Show, Eq)

data FormationSummary = FormationSummary
    { summaryProviderSteps :: !Natural
    , summaryCompositeLevel :: !Natural
    , summaryEqualitySteps :: !Natural
    , summaryBranch :: !(Maybe SemanticFactBranch)
    }

emptyFormationSummary :: FormationSummary
emptyFormationSummary = FormationSummary 0 0 0 Nothing

summaryAdd :: Natural -> Natural -> Natural
summaryAdd left right = min (fromIntegral (maxBound :: Word)) (left + right)

combineFormationSummary :: FormationSummary -> FormationSummary -> FormationSummary
combineFormationSummary left right = FormationSummary
    (summaryAdd (summaryProviderSteps left) (summaryProviderSteps right))
    (max (summaryCompositeLevel left) (summaryCompositeLevel right))
    (summaryAdd (summaryEqualitySteps left) (summaryEqualitySteps right)) Nothing

premiseSummary :: FormationPremiseEvidence scope origin -> FormationSummary
premiseSummary = \case
    FormationPremiseEvidenceTruth -> emptyFormationSummary
    FormationPremiseEvidenceLeaf (FormationWitness metadata _) -> metadataSummary metadata
    FormationPremiseEvidenceSupplied source _ -> emptyFormationSummary
        {summaryEqualitySteps = fst (sourceEvidenceEqualitySummary source)}
    FormationPremiseEvidenceAnd left right -> combineFormationSummary (premiseSummary left) (premiseSummary right)
    FormationPremiseEvidenceOr _ _ child -> premiseSummary child
    FormationPremiseEvidenceIff _ left right -> combineFormationSummary (premiseSummary left) (premiseSummary right)
    FormationPremiseEvidenceExists _ _ child -> premiseSummary child
    FormationPremiseEvidenceReflexivity{} -> emptyFormationSummary

witnessCost :: FormationWitness scope origin -> FormationDerivationCost
witnessCost (FormationWitness metadata _) = metadataCost metadata

witnessReference :: FormationWitness scope origin -> FormationRecipeId
witnessReference (FormationWitness _ reference) = reference

formationMetadata :: GroundNotionKey -> FormationDerivationCost -> FormationSummary -> Maybe Natural -> FormationMetadata
formationMetadata key (FormationDerivationCost nodes depth) =
    FormationMetadata key (FormationDerivationCost (summaryAdd nodes 0) (summaryAdd depth 0))

materializeFormationEvidence
    :: FormationSearchLimits -> FormationEvidence origin -> MaterializedFormationEvidence origin
materializeFormationEvidence limits (FormationEvidence _ (MaterializedFormationEvidence hypotheses imports recipe _)) =
    MaterializedFormationEvidence hypotheses imports recipe
        (formationMaximumDerivationNodes limits, formationMaximumDerivationDepth limits)

materializeFormationPremiseEvidence
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSearchLimits -> FormationPremiseEvidence scope origin
    -> FormationConstruction scope origin m (MaterializedFormationEvidence origin)
materializeFormationPremiseEvidence charge limits evidence = do
    reference <- buildFormationPremiseRecipe charge evidence
    inFormationArena (\_ -> arenaSelect charge
        (formationMaximumDerivationNodes limits, formationMaximumDerivationDepth limits) reference)

appendFormationRecipe
    :: Monad m => (Natural -> m ()) -> FormationRecipeNode
    -> FormationConstruction scope origin m FormationRecipeId
appendFormationRecipe charge node = inFormationArena (\observe -> arenaInsert charge observe node)

buildRawDirectRecipe
    :: (Monad m, Ord origin) => (Natural -> m ()) -> DirectFormationSource origin
    -> FormationConstruction scope origin m FormationRecipeId
buildRawDirectRecipe charge source = do
    root <- inFormationArena (\observe -> arenaHypothesis charge observe
        (MaterializedNotionHypothesis (directSourceProposition source) (directSourceOrigin source)))
    projectFormationRecipe charge (directSourcePath source) root

buildEqualityTransportRecipe
    :: (Monad m, Ord origin) => (Natural -> m ())
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> FormationRecipeId -> FormationConstruction scope origin m FormationRecipeId
buildEqualityTransportRecipe charge premise target steps parent = do
    edges <- for steps \(FormationEqualityTransport source _ direction, predicate) -> do
        reference <- buildRawDirectRecipe charge source
        pure (predicate, FormationTransportEdge reference direction)
    appendFormationRecipe charge (FormationTransport parent premise target edges)

buildSourceEvidenceRecipe
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSourceEvidence origin
    -> FormationConstruction scope origin m FormationRecipeId
buildSourceEvidenceRecipe charge (FormationSourceEvidence source transport _) = do
    original <- buildRawDirectRecipe charge source
    maybe (pure original) (\(steps, premise, target) ->
        buildEqualityTransportRecipe charge premise target steps original) transport

buildFormationPremiseRecipe
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationPremiseEvidence scope origin
    -> FormationConstruction scope origin m FormationRecipeId
buildFormationPremiseRecipe charge = \case
    FormationPremiseEvidenceTruth -> appendFormationRecipe charge FormationTruthIntroduction
    FormationPremiseEvidenceLeaf witness -> pure (witnessReference witness)
    FormationPremiseEvidenceSupplied source adapter -> do
        parent <- buildSourceEvidenceRecipe charge source
        appendFormationRecipe charge (FormationSuppliedUniversal parent adapter)
    FormationPremiseEvidenceAnd left right -> do
        a <- buildFormationPremiseRecipe charge left
        b <- buildFormationPremiseRecipe charge right
        appendFormationRecipe charge (FormationConjunctionIntroduction a b)
    FormationPremiseEvidenceOr right target child -> do
        parent <- buildFormationPremiseRecipe charge child
        appendFormationRecipe charge (FormationDisjunctionIntroduction right target parent)
    FormationPremiseEvidenceIff target left right -> do
        a <- buildFormationPremiseRecipe charge left
        b <- buildFormationPremiseRecipe charge right
        appendFormationRecipe charge (FormationBiconditionalIntroduction target a b)
    FormationPremiseEvidenceExists target witness child -> do
        parent <- buildFormationPremiseRecipe charge child
        appendFormationRecipe charge (FormationExistentialIntroduction target witness parent)
    FormationPremiseEvidenceReflexivity operand -> appendFormationRecipe charge (FormationEqualityReflexivity operand)

-- Logical composition shares the same proof arena and exact whole identity
-- as clause applications. The kernel checks the selected target at replay.
composeFormationEvidence
    :: (Monad m, Ord origin) => (Natural -> m ()) -> ScopedCheckedCore ObjectId
    -> FormationPremiseEvidence scope origin
    -> FormationConstruction scope origin m (FormationWitness scope origin)
composeFormationEvidence charge target premises = do
    reference <- buildFormationPremiseRecipe charge premises
    pure (FormationWitness (formationMetadata (groundNotionKeyFromFormula target)
        (premiseWitnessCost premises) (premiseSummary premises) Nothing) reference)

data FormationIntroduction origin = FormationSetIntroduction | FormationAssumptionIntroduction !origin

introduceFormationEvidence
    :: (Monad m, Ord origin) => (Natural -> m ())
    -> (ScopedCheckedCore ObjectId -> m (ScopedCheckedCore ObjectId))
    -> FormationIntroduction origin -> ScopedCheckedCore ObjectId -> FormationEvidence origin
    -> FormationConstruction scope origin m (FormationWitness scope origin)
introduceFormationEvidence charge alignParent introduction target
        (FormationEvidence metadata (MaterializedFormationEvidence hypotheses imports recipe _)) = do
    binding <- case introduction of
        FormationSetIntroduction -> pure Nothing
        FormationAssumptionIntroduction origin -> (\reference -> Just (origin,reference)) <$> appendFormationRecipe charge FormationBoundHypothesis
    sources <- for hypotheses \(MaterializedNotionHypothesis formula origin) -> case binding of
        Just (introduced,reference) | origin == introduced -> pure reference
        _ -> inFormationArena (\observe -> do
            parent <- lift (alignParent formula)
            arenaHypothesis charge observe (MaterializedNotionHypothesis parent origin))
    body <- inFormationArena (\observe -> arenaGraft charge observe sources imports recipe)
    result <- case (introduction,scopedCoreTerm target,binding) of
        (FormationSetIntroduction,CForall TySet _,Nothing) -> appendFormationRecipe charge (FormationForallIntroduction TySet body)
        (FormationAssumptionIntroduction{},CImp{},Just (_,reference)) -> do
            let (premise,_) = fromMaybe (impossible "an implication introduction lost its checked premise") (openScopedImplication target)
            appendFormationRecipe charge (FormationImplicationIntroduction premise reference body)
        _ -> impossible "a scoped formation introduction changed its connective"
    let FormationDerivationCost nodes depth = metadataCost metadata
    pure (FormationWitness (formationMetadata (groundNotionKeyFromFormula target)
        (FormationDerivationCost (nodes+1) (depth+1)) (metadataSummary metadata) Nothing) result)

-- A supplied-universal adapter proves a whole formula. It grants neither a
-- rich atomic occurrence nor the capability to instantiate a derived result.
suppliedFormationEvidence
    :: (Monad m, Ord origin) => (Natural -> m ()) -> ScopedCheckedCore ObjectId
    -> FormationSourceEvidence origin -> UniversalAdapter
    -> FormationConstruction scope origin m (FormationWitness scope origin)
suppliedFormationEvidence charge target source adapter = do
    let evidence = FormationPremiseEvidenceSupplied source adapter
    reference <- buildFormationPremiseRecipe charge evidence
    pure (FormationWitness (formationMetadata (groundNotionKeyFromFormula target)
        (premiseWitnessCost evidence) (premiseSummary evidence) Nothing) reference)

-- | Query an exact direct source without preparing or traversing the unary
-- formation graph.  Source-terminal global predicates use this boundary so
-- their evidence can be consumed but never synthesized.
findDirectFormationEvidenceWithLimits
    :: FormationSearchLimits
    -> UnarySourceIndex richKey rich origin
    -> GroundNotionKey
    -> Either FormationSearchError (FormationSearchOutcome origin)
findDirectFormationEvidenceWithLimits limits index goal =
    case lookupDirectUnarySource goal index of
        Nothing ->
            Right
                (FormationNotFound
                    (FormationFailureExplanation
                        emptyFormationSearchStatistics Nothing False))
        Just proved -> do
            let evidence = provedRichGoalEvidence proved
                statistics = emptyFormationSearchStatistics
                    { formationSearchDirectGroundAtoms = 1 }
            checkGroundAtomLimit limits 1
            pure (FormationFound evidence statistics)

-- A common application interface over the existing checked registrations.
-- Constructors retain those registrations, not caller-supplied fingerprints.
-- The original source telescope and premise grouping still determine replay.
data FormationRuleSource
    = FormationViewRule !VisibleNotionView
    | FormationNullaryRule !VisibleNullaryProviderClassification
    | FormationProviderRule !VisibleProviderResultRule
    | FormationBackwardRule !VisibleBackwardNotionRule
    | FormationFiniteRule !VisibleFiniteEvidenceRule
    | FormationGraphRule !VisibleGraphDomainRule
    | FormationWholeRule !VisibleWholeConclusionRule
    | FormationProjectionRule !FormationRuleSource !ProjectionPlan
    | FormationEliminationRule !FormationRuleSource !ResidualTemplate !ProjectionPlan
    | FormationIntroductionRule !FormationRuleSource !Introduction

formationRuleFamily :: FormationRuleSource -> Diagnostics.RegistrationFamily
formationRuleFamily = \case
    FormationViewRule{} -> Diagnostics.ViewFamily
    FormationNullaryRule{} -> Diagnostics.NullaryFamily
    FormationProviderRule{} -> Diagnostics.ProviderFamily
    FormationBackwardRule{} -> Diagnostics.BackwardFamily
    FormationFiniteRule{} -> Diagnostics.FiniteFamily
    FormationGraphRule{} -> Diagnostics.GraphFamily
    FormationWholeRule{} -> Diagnostics.WholeFamily
    FormationProjectionRule source _ -> formationRuleFamily source
    FormationEliminationRule source _ _ -> formationRuleFamily source
    FormationIntroductionRule source _ -> formationRuleFamily source

formationRuleSourceBranch :: FormationRuleSource -> SemanticFactBranch
formationRuleSourceBranch = \case
    FormationViewRule value -> visibleNotionViewSource value
    FormationNullaryRule value -> visibleNullaryProviderClassificationSource value
    FormationProviderRule value -> visibleProviderResultRuleSource value
    FormationBackwardRule value -> visibleBackwardNotionRuleSource value
    FormationFiniteRule value -> visibleFiniteEvidenceRuleSource value
    FormationGraphRule value -> visibleGraphDomainRuleSource value
    FormationWholeRule value -> visibleWholeConclusionRuleSource value
    FormationProjectionRule source _ -> formationRuleSourceBranch source
    FormationEliminationRule source _ _ -> formationRuleSourceBranch source
    FormationIntroductionRule source _ -> formationRuleSourceBranch source

applyFormationRule
    :: (Monad m, Ord origin) => (Natural -> m ())
    -> FormationRuleSource
    -> Map Natural (CanonicalTerm ObjectId)
    -> [FormationPremiseEvidence scope origin]
    -> NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyFormationRule charge source substitution premises conclusion = case source of
    FormationIntroductionRule _ operation -> applyIntroductionRule charge operation substitution premises conclusion
    FormationEliminationRule _ _ plan -> applyProjectedEvidence charge plan substitution premises conclusion
    FormationProjectionRule original plan ->
        admit (formationRuleSourceBranch original) (projectionSourceArity plan) RuleApplication 0
    FormationViewRule view -> do
        unaryPremise
        admit (visibleNotionViewSource view) (visibleNotionViewBinderArity view)
            ViewApplication 0
    FormationNullaryRule classification -> do
        noPremises
        unless (Map.null substitution)
            (impossible "a nullary formation rule received bound arguments")
        unless (visibleNullaryProviderClassificationConclusionKey classification == key)
            (impossible "a nullary formation rule changed its conclusion")
        admit (visibleNullaryProviderClassificationSource classification) 0 RuleApplication 0
    FormationProviderRule rule -> do
        let arity = visibleProviderResultRuleBinderArity rule
        kind <- case providerResultPremises (visibleProviderResultRulePayload rule) of
            ProviderResultUnconditional -> do
                noPremises
                let domain = if arity == 0 then Set.empty else Set.fromList [0 .. arity - 1]
                unless (Map.keysSet substitution == domain)
                    (impossible "an unconditional provider-result substitution has the wrong dense domain")
                pure RuleApplication
            ProviderResultGuarded{} -> groupedPremises >> pure RuleApplication
        admit (visibleProviderResultRuleSource rule) arity kind 1
    FormationBackwardRule rule -> do
        groupedPremises
        admit (visibleBackwardNotionRuleSource rule) (visibleBackwardNotionRuleBinderArity rule)
            RuleApplication 0
    FormationFiniteRule rule -> do
        admit (visibleFiniteEvidenceRuleSource rule) (visibleFiniteEvidenceRuleBinderArity rule)
            RuleApplication 0
    FormationGraphRule rule -> do
        unaryPremise
        admit (visibleGraphDomainRuleSource rule) (visibleGraphDomainRuleBinderArity rule)
            RuleApplication 0
    FormationWholeRule rule ->
        admit (visibleWholeConclusionRuleSource rule)
            (wholeConclusionArity (visibleWholeConclusionRulePayload rule)) RuleApplication 0
  where
    key = case conclusion of
        AtomicLeaf atom -> groundNotionKeyFromTemplate atom
        WholeLeaf formula -> groundNotionKeyFromFormula formula
    noPremises = unless (null premises)
        (impossible "a closed formation rule received premises")
    groupedPremises = when (null premises)
        (impossible "a guarded formation rule lost its premises")
    unaryPremise = case premises of
        [FormationPremiseEvidenceLeaf{}] -> pure ()
        _ -> impossible "a unary formation rule lost its atomic premise"
    admit branch arity kind providerSteps = do
        let unprojected = case (kind, premises) of
                -- Unary views retain their established depth convention.
                (ViewApplication, [FormationPremiseEvidenceLeaf parent]) ->
                    let FormationDerivationCost nodes depth = witnessCost parent
                    in FormationDerivationCost (nodes + arity + 2) (max (depth + 1) (arity + 1))
                _ -> importedApplicationCost arity premises
            projectedCost = projectFormationCost branch unprojected
            cost = case source of
                FormationProjectionRule _ plan -> let FormationDerivationCost nodes depth = projectedCost
                    in FormationDerivationCost (nodes + fromIntegral (length (projectionReverseSteps plan)))
                        (depth + fromIntegral (length (projectionReverseSteps plan)))
                _ -> projectedCost
            summary = foldl' combineFormationSummary emptyFormationSummary (premiseSummary <$> premises)
            increment = case kind of ViewApplication -> 0; RuleApplication -> 1
            combined = summary
                { summaryProviderSteps = summaryAdd providerSteps (summaryProviderSteps summary)
                , summaryCompositeLevel = summaryAdd increment (summaryCompositeLevel summary)
                , summaryBranch = Just branch }
        initial <- instantiateImportedRecipe charge (semanticFactBranchFact branch) arity substitution
        let sourcePremises = case source of
                FormationProjectionRule _ plan -> take (fromIntegral (projectionSourcePremises plan)) premises
                _ -> premises
        applied <- foldM (\parent premise -> do
            child <- buildFormationPremiseRecipe charge premise
            appendFormationRecipe charge (FormationImplicationElimination parent child)) initial sourcePremises
        projected <- projectFormationRecipe charge (semanticFactBranchPath branch) applied
        result <- case source of
            FormationProjectionRule _ plan -> do
                let indexed = Map.fromList (zip [0..] premises)
                foldM (\parent -> \case
                    ProjectionBinder slot -> do
                        lift (lift (lift (charge (indexWork (Map.size substitution) 1))))
                        argument <- maybe (impossible "a projection lost its quantified parameter") pure (Map.lookup slot substitution)
                        appendFormationRecipe charge (FormationForallElimination parent argument)
                    ProjectionGuard slot -> do
                        lift (lift (lift (charge (indexWork (Map.size indexed) 1))))
                        premise <- maybe (impossible "a projection lost its original guard") pure (Map.lookup slot indexed)
                        child <- buildFormationPremiseRecipe charge premise
                        appendFormationRecipe charge (FormationImplicationElimination parent child)
                    ProjectionConjunct right -> appendFormationRecipe charge
                        (if right then FormationConjunctionRightElimination parent else FormationConjunctionLeftElimination parent)
                    ProjectionBiconditionalGuard right slot -> do
                        lift (lift (lift (charge (indexWork (Map.size indexed) 1))))
                        premise <- maybe (impossible "a biconditional projection lost its guard") pure (Map.lookup slot indexed)
                        child <- buildFormationPremiseRecipe charge premise
                        appendFormationRecipe charge (FormationBiconditionalElimination right parent child))
                    projected (reverse (projectionReverseSteps plan))
            _ -> pure projected
        pure (FormationWitness (formationMetadata key cost combined Nothing) result)

-- The source registration supplies only an admitted query description here.
-- A logical introduction uses its actual premises, never the registration's
-- theorem import. The target and witness are retained for independent replay.
applyIntroductionRule
    :: (Monad m, Ord origin) => (Natural -> m ()) -> Introduction
    -> Map Natural (CanonicalTerm ObjectId) -> [FormationPremiseEvidence scope origin]
    -> NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyIntroductionRule charge operation substitution premises conclusion = do
    target <- case conclusion of WholeLeaf formula -> pure formula; _ -> impossible "an introduction acquired an atomic conclusion"
    evidence <- case (operation,premises) of
        (IntroduceConjunction,[left,right]) -> pure (FormationPremiseEvidenceAnd left right)
        (IntroduceDisjunction right,[child]) -> pure (FormationPremiseEvidenceOr right target child)
        (IntroduceExistential (ViewVariableIx slot),[child]) -> do
            lift (lift (lift (charge (indexWork (Map.size substitution) 1))))
            witness <- maybe (impossible "an existential introduction lost its witness") pure (Map.lookup slot substitution)
            pure (FormationPremiseEvidenceExists target witness child)
        _ -> impossible "a logical introduction changed its premise grouping"
    composeFormationEvidence charge target evidence

applyProjectedSource
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSourceEvidence origin
    -> ProjectionPlan -> Map Natural (CanonicalTerm ObjectId) -> [FormationPremiseEvidence scope origin]
    -> NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyProjectedSource charge source plan substitution premises conclusion = do
    initial <- buildSourceEvidenceRecipe charge source
    projectEvidence charge initial (sourceEvidenceCost source) (fst (sourceEvidenceEqualitySummary source))
        plan substitution premises conclusion

applyProjectedEvidence
    :: (Monad m, Ord origin) => (Natural -> m ())
    -> ProjectionPlan -> Map Natural (CanonicalTerm ObjectId) -> [FormationPremiseEvidence scope origin]
    -> NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyProjectedEvidence charge plan substitution premises conclusion = case premises of
    first:_ -> do
        initial <- buildFormationPremiseRecipe charge first
        projectEvidence charge initial (premiseWitnessCost first) 0 plan substitution premises conclusion
    [] -> impossible "a whole elimination lost its source witness"

projectEvidence
    :: (Monad m, Ord origin) => (Natural -> m ())
    -> FormationRecipeId -> FormationDerivationCost -> Natural
    -> ProjectionPlan -> Map Natural (CanonicalTerm ObjectId) -> [FormationPremiseEvidence scope origin]
    -> NotionLeaf (AtomTemplate (CanonicalTerm ObjectId)) (ScopedCheckedCore ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
projectEvidence charge initial initialCost equalitySteps plan substitution premises conclusion = do
    let indexed = Map.fromList (zip [0..] premises)
        steps = reverse (projectionReverseSteps plan)
        argument slot = do
            lift (lift (lift (charge (indexWork (Map.size substitution) 1))))
            maybe (impossible "a local projection lost its quantified argument") pure (Map.lookup slot substitution)
        guardEvidence slot = do
            lift (lift (lift (charge (indexWork (Map.size indexed) 1))))
            maybe (impossible "a local projection lost its guard") pure (Map.lookup slot indexed)
    (result,cost) <- foldM (\(parent,FormationDerivationCost nodes depth) -> \case
        ProjectionBinder slot -> do
            value <- argument slot
            next <- appendFormationRecipe charge (FormationForallElimination parent value)
            pure (next,FormationDerivationCost (nodes+1) (depth+1))
        ProjectionConjunct right -> do
            next <- appendFormationRecipe charge
                (if right then FormationConjunctionRightElimination parent else FormationConjunctionLeftElimination parent)
            pure (next,FormationDerivationCost (nodes+1) (depth+1))
        ProjectionGuard slot -> do
            premise <- guardEvidence slot
            child <- buildFormationPremiseRecipe charge premise
            next <- appendFormationRecipe charge (FormationImplicationElimination parent child)
            let FormationDerivationCost childNodes childDepth = premiseWitnessCost premise
            pure (next,FormationDerivationCost (nodes+childNodes+1) (max depth childDepth+1))
        ProjectionBiconditionalGuard right slot -> do
            premise <- guardEvidence slot
            child <- buildFormationPremiseRecipe charge premise
            next <- appendFormationRecipe charge (FormationBiconditionalElimination right parent child)
            let FormationDerivationCost childNodes childDepth = premiseWitnessCost premise
                overhead = if right then 6 else 1
            pure (next,FormationDerivationCost (nodes+childNodes+overhead) (max depth childDepth+overhead)))
        (initial,initialCost) steps
    let key = case conclusion of
            AtomicLeaf atom -> groundNotionKeyFromTemplate atom
            WholeLeaf formula -> groundNotionKeyFromFormula formula
        summary = foldl' combineFormationSummary emptyFormationSummary (premiseSummary <$> premises)
        combined = summary
            { summaryCompositeLevel = summaryAdd 1 (summaryCompositeLevel summary)
            , summaryEqualitySteps = summaryAdd equalitySteps (summaryEqualitySteps summary) }
    pure (FormationWitness (formationMetadata key cost combined Nothing) result)

applyUniversalSource
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSourceEvidence origin
    -> [UniversalElimination (CanonicalTerm ObjectId) (FormationPremiseEvidence scope origin)]
    -> ConjunctionPath -> AtomTemplate (CanonicalTerm ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyUniversalSource charge source steps path conclusion = do
    initial <- buildSourceEvidenceRecipe charge source
    applied <- foldM (\parent -> \case
        EliminateBinder argument -> appendFormationRecipe charge (FormationForallElimination parent argument)
        EliminateGuard premise -> do
            child <- buildFormationPremiseRecipe charge premise
            appendFormationRecipe charge (FormationImplicationElimination parent child)) initial steps
    projected <- projectFormationRecipe charge path applied
    let FormationDerivationCost nodes depth = foldl' stepCost (sourceEvidenceCost source) steps
        projections = conjunctionPathLength path
        cost = FormationDerivationCost (nodes + projections) (depth + projections)
        summary = foldl' combineFormationSummary emptyFormationSummary
            [premiseSummary premise | EliminateGuard premise <- steps]
        combined = summary
            { summaryCompositeLevel = summaryAdd 1 (summaryCompositeLevel summary)
            , summaryEqualitySteps = summaryAdd (fst (sourceEvidenceEqualitySummary source)) (summaryEqualitySteps summary) }
    pure (FormationWitness (formationMetadata (groundNotionKeyFromTemplate conclusion) cost combined Nothing) projected)
  where
    stepCost (FormationDerivationCost nodes depth) = \case
        EliminateBinder _ -> FormationDerivationCost (nodes + 1) (depth + 1)
        EliminateGuard premise -> let FormationDerivationCost childNodes childDepth = premiseWitnessCost premise
            in FormationDerivationCost (nodes + childNodes + 1) (max depth childDepth + 1)

-- | Retain evidence for an exact denotation answer. Conversion grants no
-- source shape or additional premise authority; the caller must retain that
-- distinction in its answer key. The consumer admits the target in its own
-- scope and checks conversion under the shared kernel conversion pool.
convertFormationEvidence
    :: Monad m => (Natural -> m ()) -> ScopedCheckedCore ObjectId
    -> FormationWitness scope origin -> AtomTemplate (CanonicalTerm ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
convertFormationEvidence charge target (FormationWitness metadata parent) conclusion = do
    reference <- appendFormationRecipe charge (FormationConversion parent target)
    let FormationDerivationCost nodes depth = metadataCost metadata
        cost = FormationDerivationCost (nodes + 1) (depth + 1)
    pure (FormationWitness (formationMetadata (groundNotionKeyFromTemplate conclusion)
        cost (metadataSummary metadata) Nothing) reference)

-- | Transport one already selected logical atom along an exact checked
-- equality chain.  The predicate abstracts only the distinguished notion
-- focus.  Rich provider identity remains a concern of the elaboration-side
-- premise and conclusion shapes; this witness records only logical evidence.
applyEqualityTransportWithLimits
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSearchLimits
    -> NonEmpty (FormationEqualityTransport origin)
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> FormationWitness scope origin
    -> AtomTemplate (CanonicalTerm ObjectId)
    -> AtomTemplate (CanonicalTerm ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyEqualityTransportWithLimits charge limits transports predicate premise target parent premiseAtom conclusionAtom = do
    unless (compatibleTransportChain predicate premise target transports)
        (impossible "an equality-transport chain has incompatible scope or adjacent endpoints")
    applyEqualitySubstitutionsWithLimits charge limits
        ((\transport -> (transport, predicate)) <$> transports)
        premise target parent premiseAtom conclusionAtom

-- Each substitution may address a different position in the proposition.
-- The checked replay attaches every step to the preceding result; a sequence
-- cannot acquire authority merely by supplying well-typed predicates.
applyEqualitySubstitutionsWithLimits
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSearchLimits
    -> NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> FormationWitness scope origin
    -> AtomTemplate (CanonicalTerm ObjectId)
    -> AtomTemplate (CanonicalTerm ObjectId)
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyEqualitySubstitutionsWithLimits charge limits steps premise target
        witness premiseAtom conclusionAtom =
    substituteFormationEquality charge limits steps premise target witness
        (groundNotionKeyFromTemplate premiseAtom) (groundNotionKeyFromTemplate conclusionAtom)

applyWholeEqualitySubstitutionsWithLimits
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSearchLimits
    -> NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId -> FormationWitness scope origin
    -> FormationConstruction scope origin m (FormationWitness scope origin)
applyWholeEqualitySubstitutionsWithLimits charge limits steps premise target witness =
    substituteFormationEquality charge limits steps premise target witness
        (groundNotionKeyFromFormula premise) (groundNotionKeyFromFormula target)

substituteFormationEquality
    :: (Monad m, Ord origin) => (Natural -> m ()) -> FormationSearchLimits
    -> NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId -> FormationWitness scope origin
    -> GroundNotionKey -> GroundNotionKey
    -> FormationConstruction scope origin m (FormationWitness scope origin)
substituteFormationEquality charge limits steps premise target
        witness@(FormationWitness metadata parent) premiseKey targetKey = do
    unless (metadataGroundKey metadata == premiseKey)
        (impossible "equality substitution received evidence for a different premise")
    lift (Except.ExceptT (pure (validateSubstitutionScopes steps premise target)))
    let equalityCount = formationWitnessEqualitySteps witness
                + fromIntegral (length steps)
        cost = finishTransportCost (foldl' (\current (transport, _) -> extendTransportCost current transport)
            (finishTransportCost (metadataCost metadata)) steps)
    when (equalityCount > formationMaximumEqualityChainLength limits)
        (lift (Except.throwE (FormationEqualityChainLimitExceeded (formationMaximumEqualityChainLength limits) equalityCount)))
    reference <- buildEqualityTransportRecipe charge premise target steps parent
    let summary = (metadataSummary metadata) {summaryEqualitySteps = equalityCount}
    pure (FormationWitness (formationMetadata targetKey cost summary Nothing) reference)

validateSubstitutionScopes
    :: NonEmpty (FormationEqualityTransport origin, ScopedCheckedCore ObjectId)
    -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> Either FormationSearchError ()
validateSubstitutionScopes steps premise target = do
    let context = scopedCoreContext premise
        validStep (FormationEqualityTransport _ equality _, predicate) =
            scopedCoreContext equality == context
                && scopedCoreContext predicate == context
                && scopedCoreType predicate == TyArrow TySet TyProp
    unless (scopedCoreType premise == TyProp && scopedCoreType target == TyProp
            && scopedCoreContext target == context && all validStep steps)
        (impossible "equality substitutions have incompatible scopes or predicates")

compatibleTransportChain
    :: ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> NonEmpty (FormationEqualityTransport origin)
    -> Bool
compatibleTransportChain predicate premise target transports =
    scopedCoreType predicate == TyArrow TySet TyProp
        && scopedCoreType premise == TyProp
        && scopedCoreType target == TyProp
        && all ((== context) . transportContext) transportList
        && scopedCoreContext premise == context
        && scopedCoreContext target == context
        && and
            [ firstTarget == laterSource
            | (firstTarget, laterSource) <- zip targets (drop 1 sources)
            ]
  where
    transportList = toList transports
    firstEndpoint :| remainingEndpoints = transportEndpoints <$> transports
    endpointChain = firstEndpoint : remainingEndpoints
    context = scopedCoreContext predicate
    sources = fst <$> endpointChain
    targets = snd <$> endpointChain

transportContext :: FormationEqualityTransport origin -> [CoreType]
transportContext
        (FormationEqualityTransport _source equality _direction) =
    scopedCoreContext equality

transportEndpoints
    :: FormationEqualityTransport origin
    -> (CanonicalTerm ObjectId, CanonicalTerm ObjectId)
transportEndpoints
        (FormationEqualityTransport _source equality direction) =
    case scopedCoreTerm equality of
        CEq TySet left right -> case direction of
            FormationEqualityLeftToRight -> (left, right)
            FormationEqualityRightToLeft -> (right, left)
        _ -> impossible "a checked notion transport ceased to be a set equality"

extendTransportCost
    :: FormationDerivationCost
    -> FormationEqualityTransport origin
    -> FormationDerivationCost
extendTransportCost (FormationDerivationCost parentNodes parentDepth) transport =
    let FormationEqualityTransport source _equality direction = transport
        FormationDerivationCost equalityNodes equalityDepth =
            directFormationCost source
        overhead = case direction of
            FormationEqualityLeftToRight -> 4
            FormationEqualityRightToLeft -> 10
    in FormationDerivationCost
        (parentNodes + equalityNodes + overhead)
        (max (parentDepth + 2) (equalityDepth + overhead))

finishTransportCost :: FormationDerivationCost -> FormationDerivationCost
finishTransportCost (FormationDerivationCost nodes depth) =
    FormationDerivationCost (nodes + 1) (depth + 1)

suppliedCost :: FormationSourceEvidence origin -> UniversalAdapter -> FormationDerivationCost
suppliedCost source adapter =
    let FormationDerivationCost sourceNodes sourceDepth = sourceEvidenceCost source
        (nodes,depth) = adapterCost sourceNodes sourceDepth adapter
    in FormationDerivationCost nodes depth

importedApplicationCost
    :: Natural
    -> [FormationPremiseEvidence scope origin]
    -> FormationDerivationCost
importedApplicationCost binderArity bundles =
    foldl' applyBundle theoremCost (premiseWitnessCost <$> bundles)
  where
    theoremCost = importedTheoremCost binderArity

    applyBundle (FormationDerivationCost theoremNodes theoremDepth)
            (FormationDerivationCost premiseNodes premiseDepth) =
        FormationDerivationCost
            (theoremNodes + premiseNodes + 1)
            (max theoremDepth premiseDepth + 1)


premiseWitnessCost :: FormationPremiseEvidence scope origin -> FormationDerivationCost
premiseWitnessCost = \case
    FormationPremiseEvidenceTruth -> FormationDerivationCost 1 0
    FormationPremiseEvidenceLeaf witness -> witnessCost witness
    FormationPremiseEvidenceSupplied source adapter -> suppliedCost source adapter
    FormationPremiseEvidenceAnd left right ->
        let FormationDerivationCost leftNodes leftDepth = premiseWitnessCost left
            FormationDerivationCost rightNodes rightDepth = premiseWitnessCost right
        in FormationDerivationCost
            (leftNodes + rightNodes + 1)
            (max leftDepth rightDepth + 1)
    FormationPremiseEvidenceOr _ _ child -> grow 1 (premiseWitnessCost child)
    FormationPremiseEvidenceIff _ left right ->
        let FormationDerivationCost a x = premiseWitnessCost left
            FormationDerivationCost b y = premiseWitnessCost right
        in FormationDerivationCost (a+b+5) (max (x+2) (y+1) + 3)
    FormationPremiseEvidenceExists _ _ child -> grow 1 (premiseWitnessCost child)
    FormationPremiseEvidenceReflexivity{} -> FormationDerivationCost 1 0
  where
    grow amount (FormationDerivationCost nodes depth) = FormationDerivationCost (nodes+amount) (depth+amount)

importedTheoremCost :: Natural -> FormationDerivationCost
importedTheoremCost binderArity =
    FormationDerivationCost
        (binderArity + 1)
        (binderArity + 1)


visibleNotionViewBinderArity :: VisibleNotionView -> Natural
visibleNotionViewBinderArity (VisibleNotionView _source _declaration binderArity) =
    binderArity

instantiateImportedRecipe
    :: Monad m => (Natural -> m ()) -> SemanticFactOccurrenceFingerprint -> Natural
    -> Map Natural (CanonicalTerm ObjectId)
    -> FormationConstruction scope origin m FormationRecipeId
instantiateImportedRecipe charge fingerprint binderArity substitution = do
    lift (lift (lift (charge binderArity)))
    initial <- inFormationArena (\observe -> arenaImport charge observe fingerprint)
    foldM (\parent index -> do
        lift (lift (lift (charge (indexWork (Map.size substitution) 1))))
        let term = fromMaybe (impossible "a determined theorem lacks a dense variable") (Map.lookup index substitution)
        appendFormationRecipe charge (FormationForallElimination parent term)) initial
        (if binderArity == 0 then [] else reverse [0 .. binderArity - 1])

directFormationEvidence
    :: Monad m => (Natural -> m ()) -> GroundNotionKey -> FormationHypothesisReference scope origin
    -> ConjunctionPath -> Natural -> FormationConstruction scope origin m (FormationWitness scope origin)
directFormationEvidence charge key (FormationHypothesisReference _ _ parent) path ordinal = do
    reference <- projectFormationRecipe charge path parent
    let projections = conjunctionPathLength path
        cost = FormationDerivationCost (projections + 1) projections
    pure (FormationWitness (formationMetadata key cost emptyFormationSummary (Just ordinal)) reference)

directPreparedFormationEvidence
    :: Monad m => (Natural -> m ()) -> GroundNotionKey -> FormationHypothesisReference scope origin
    -> ConjunctionProjection -> Natural -> FormationConstruction scope origin m (FormationWitness scope origin)
directPreparedFormationEvidence charge key (FormationHypothesisReference _ _ parent) path ordinal = do
    reference <- inFormationArena (\observe -> arenaProject charge observe parent path)
    let projections = conjunctionProjectionDepth path
        cost = FormationDerivationCost (projections + 1) projections
    pure (FormationWitness (formationMetadata key cost emptyFormationSummary (Just ordinal)) reference)

directFormationCost
    :: DirectFormationSource origin
    -> FormationDerivationCost
directFormationCost source =
    let projections = conjunctionPathLength (directSourcePath source)
    in FormationDerivationCost (projections + 1) projections

projectFormationCost :: SemanticFactBranch -> FormationDerivationCost -> FormationDerivationCost
projectFormationCost branch (FormationDerivationCost nodes depth) =
    let projections = conjunctionPathLength (semanticFactBranchPath branch)
    in FormationDerivationCost (nodes + projections) (depth + projections)

conjunctionPathLength :: ConjunctionPath -> Natural
conjunctionPathLength = \case
    ConjunctionHere -> 0
    ConjunctionLeft remaining -> 1 + conjunctionPathLength remaining
    ConjunctionRight remaining -> 1 + conjunctionPathLength remaining

checkGroundAtomLimit
    :: FormationSearchLimits
    -> Natural
    -> Either FormationSearchError ()
checkGroundAtomLimit limits actual
    | actual > maximumAtoms =
        Left (FormationGroundAtomLimitExceeded maximumAtoms actual)
    | otherwise = Right ()
  where
    maximumAtoms = formationMaximumGroundAtoms limits

checkInferenceInspectionLimit
    :: FormationSearchLimits
    -> Natural
    -> Either FormationSearchError ()
checkInferenceInspectionLimit limits actual
    | actual > maximumInspections =
        Left
            (FormationInferenceInspectionLimitExceeded
                maximumInspections actual)
    | otherwise = Right ()
  where
    maximumInspections = formationMaximumInferenceInspections limits

checkRelevantHeadEdgeLimit
    :: FormationSearchLimits
    -> Natural
    -> Either FormationSearchError ()
checkRelevantHeadEdgeLimit limits actual
    | actual > maximumEdges =
        Left (FormationRelevantHeadEdgeLimitExceeded maximumEdges actual)
    | otherwise = Right ()
  where
    maximumEdges = formationMaximumRelevantHeadEdges limits

checkRelevantViewLimit
    :: FormationSearchLimits
    -> Natural
    -> Either FormationSearchError ()
checkRelevantViewLimit limits actual
    | actual > maximumViews =
        Left (FormationRelevantViewLimitExceeded maximumViews actual)
    | otherwise = Right ()
  where
    maximumViews = formationMaximumRelevantViews limits

templateHead :: AtomTemplate variable -> NotionHeadKey
templateHead = \case
    GlobalAtomTemplate head' _arguments -> GlobalNotionHeadKey head'
    StructureAtomTemplate head' _arguments -> StructureNotionHeadKey head'
    ExactStructureAtomTemplate shape _ -> ExactStructureNotionHeadKey shape
    MembershipAtomTemplate{} -> MembershipNotionHeadKey
    NegativeGlobalAtomTemplate head' _ -> NegativeGlobalNotionHeadKey head'
    NegativeStructureAtomTemplate head' _ -> NegativeStructureNotionHeadKey head'
    NegativeMembershipAtomTemplate{} -> NegativeMembershipNotionHeadKey
    NegativeExactStructureAtomTemplate shape _ -> NegativeExactStructureNotionHeadKey shape

premiseTemplateVariables
    :: NotionViewPremiseTemplate
    -> Set Natural
premiseTemplateVariables = \case
    GlobalNotionViewPremise _head variables -> ruleTermVectorVariableSet variables
    StructureNotionViewPremise _head variables -> ruleTermVectorVariableSet variables
    ExactProviderMembershipPremise element _provider arguments ->
        Set.unions
            (ruleTermVariableSet element
                : (ruleTermVariableSet <$> toList arguments))

templateVariables :: NotionViewTemplate -> Set Natural
templateVariables = \case
    AtomicLeaf atom -> foldMap ruleTermVariableSet atom
    WholeLeaf template -> Set.map (\(ViewVariableIx index) -> index) (residualTemplateVariables template)

ruleTermVectorVariableSet :: Vector RuleTermTemplate -> Set Natural
ruleTermVectorVariableSet = Set.unions . fmap ruleTermVariableSet . toList

ruleTermVariableSet :: RuleTermTemplate -> Set Natural
ruleTermVariableSet = Set.fromList . ruleTermVariableIndices

projectFormationRecipe
    :: Monad m => (Natural -> m ()) -> ConjunctionPath -> FormationRecipeId
    -> FormationConstruction scope origin m FormationRecipeId
projectFormationRecipe _ ConjunctionHere parent = pure parent
projectFormationRecipe charge (ConjunctionLeft remaining) parent =
    appendFormationRecipe charge (FormationConjunctionLeftElimination parent) >>= projectFormationRecipe charge remaining
projectFormationRecipe charge (ConjunctionRight remaining) parent =
    appendFormationRecipe charge (FormationConjunctionRightElimination parent) >>= projectFormationRecipe charge remaining
