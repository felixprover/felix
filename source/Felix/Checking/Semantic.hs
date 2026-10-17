{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Canonical semantic declaration, prefix, interface, and validation keys.
module Felix.Checking.Semantic
    ( DeclarationSlot
    , declarationSlot
    , declarationSlotModule
    , declarationSlotOrdinal
    , FactSlot
    , factSlot
    , factSlotModule
    , factSlotOrdinal
    , SemanticName
    , semanticName
    , semanticNameText
    , FactSearchEligibility(..)
    , SemanticFactOccurrence
    , FactPurpose(..)
    , structureLawPurpose
    , semanticFactPurpose
    , semanticFactOccurrence
    , semanticFactOccurrenceWithRelationComposition
    , semanticFactSlot
    , semanticFactProposition
    , semanticFactAuthority
    , semanticFactSearchEligibility
    , semanticFactRelationComposition
    , semanticFactFingerprint
    , SemanticFactOccurrenceFingerprint
    , semanticFactOccurrenceFingerprint
    , semanticFactFingerprintDigest
    , SemanticAlias
    , semanticAlias
    , semanticAliasName
    , semanticAliasTarget
    , DefinitionViewKind(..)
    , SemanticDefinitionView
    , semanticDefinitionViewObject
    , semanticDefinitionViewKind
    , semanticDefinitionViewTarget
    , AdjectiveReadingKind(..)
    , SemanticGlobalKey(..)
    , semanticAdjectiveKey
    , concreteTypeCoreType
    , semanticGlobalKeyFromLexicalEntry
    , semanticGlobalKeyType
    , SemanticRelationComposition(..), SemanticRelationSource(..)
    , SemanticGlobalTarget(..)
    , semanticGlobalTargetObject
    , semanticGlobalTargetRequirements
    , SemanticBindingLabel
    , semanticBindingLabel
    , semanticBindingLabelText
    , SemanticGlobalBinding
    , semanticGlobalBinding
    , semanticGlobalBindingKey
    , semanticGlobalBindingLabel
    , semanticGlobalBindingTarget
    , semanticGlobalBindingContract
    , semanticGlobalBindingWithContract
    , AbbreviationExpansion(..)
    , ExpansionTerm(..)
    , ExpansionEquality(..)
    , ExpansionFailure(..), atExpansionPath, expansionRejectedDebit, renderExpansionFailure
    , ExpansionWork
    , formationMaximumExpansionWork
    , runExpansionWork
    , chargeExpansion
    , expansionCoreWork
    , putAbbreviationExpansionCache, putAbbreviationExpansionCacheWith
    , getAbbreviationExpansionCache
    , semanticGlobalBindingWithMetadata
    , DatatypeDescriptor(..), DatatypeCase(..), DatatypePremise(..)
    , semanticGlobalBindingDatatype, withSemanticDatatype
    , BindingConstruction(..), RecursiveDefinitionDescriptor(..)
    , semanticGlobalBindingConstruction, withSemanticConstruction
    , semanticGlobalBindingRecursion
    , putDatatypeDescriptorCache
    , semanticGlobalBindingExpansion
    , GlobalBindingRef
    , globalBindingRef
    , globalBindingRefOwner
    , globalBindingRefKey
    , IntrinsicProviderId(..)
    , intrinsicProviderCoreTag
    , intrinsicProviderApplication
    , finiteSetLiteralProviderApplication
    , SourceProviderHead(..)
    , putSourceProviderHeadCache
    , getSourceProviderHeadCache
    , GlobalNotionHead(..)
    , GlobalNotionRole(..)
    , globalNotionHeadRole
    , globalNotionHeadReference
    , globalNotionHeadMatchesKey
    , globalNotionHostFocus
    , globalNotionBindingArguments
    , globalNotionOccurrenceArguments
    , SemanticStructureNotionHead
    , pendingStructureNotionHead
    , structureNotionHeadId
    , SemanticRecordShapeKey
    , semanticRecordShapeKey
    , semanticRecordShapeSelectors
    , SemanticFactBranch(..)
    , semanticFactBranchFact
    , semanticFactBranchPath
    , OccurrenceArgumentIx(..)
    , SetTermTemplate(..)
    , ClosedSetValue
    , closedSetValue
    , closedSetValueWith
    , closedSetValueTerm
    , materializeClosedSetValue
    , FormationTermTemplate
    , RuleTermTemplate
    , traverseSetTermTemplateVariables
    , AtomTemplate(..)
    , AtomPolarity(..), atomPolarity, withAtomPolarity, atomArity
    , pattern NegativeAtomTemplate
    , traverseAtomTemplateArguments
    , NotionTemplate
    , NotionLeaf(..)
    , ResidualTemplate(ResidualTemplate)
    , residualTemplateFormula, residualTemplateEvidence, describedResidualTemplate
    , SupportTermTemplate, instantiateSupportPrefixWith
    , residualTemplateVariables, putResidualTemplateCache
    , residualTemplateParametersWith, positiveResidualParametersWith
    , WholeTemplate(..)
    , ViewVariableIx(..)
    , NotionViewPremiseTemplate(..)
    , NotionViewTemplate
    , RuleConclusion
    , UniversalTemplate
    , RulePremiseTree(..)
    , RulePremiseBundles(..)
    , ProviderResultPremises(..)
    , putProviderResultPremisesCache
    , getProviderResultPremisesCache
    , CheckedNotionRuleSkeleton
    , checkedNotionRuleSkeleton
    , checkedNotionRuleBinderArity
    , checkedNotionRulePremises
    , checkedNotionRuleConclusion
    , BackwardNotionRuleTemplate
    , ResultRuleTerm(..)
    , ResultNotionRuleTemplate
    , putResultNotionRuleTemplateCache
    , ResultProviderTemplate
    , resultProviderTemplate
    , resultProviderTemplateHead
    , resultProviderTemplateArguments
    , NotionViewRule(..)
    , NullaryProviderRule(..)
    , ProviderResultRule(..)
    , BackwardNotionRule(..)
    , FiniteEvidenceRule(..)
    , GraphDomainRule(..)
    , RegistrationBody(..)
    , WholeConclusionRule(..)
    , Registration(..)
    , registrationBranch
    , registrationFamily
    , registrationBodyCacheDigest
    , normalizeRegistrations
    , FormationContract
    , FormationRequirement
    , formationContract
    , formationContractRequirements
    , ResolvedFormationContract
    , resolvedFormationContractRequirements
    , FormationContractMaterializationError(..)
    , ResolvedGlobalBinding
    , materializeResolvedGlobalBinding
    , materializeResolvedGlobalBindingWithFields
    , SemanticEnvironmentMaterializationError(..)
    , materializeSemanticEnvironmentDelta
    , materializeSemanticEnvironmentDeltaMeasured
    , resolvedBindingRef
    , resolvedBindingDeclaration
    , resolvedBindingContract
    , resolvedBindingExpansion
    , resolvedBindingSourceProviderHead
    , SemanticGlobalTargetError(..)
    , validateSemanticGlobalBindingTarget
    , SemanticEnvironmentDelta
    , emptySemanticEnvironmentDelta
    , semanticEnvironmentDelta
    , semanticEnvironmentWithStructures
    , semanticEnvironmentBindings
    , semanticEnvironmentStructures
    , StructureInterfaceWire
    , structureInterfaceWire
    , structureBatchSyntaxId
    , structureWireSlot
    , structureWireLocalInput
    , structureWirePredicate
    , structureWireLawIndex
    , structureWireResourceIndex
    , materializeStructureWirePresentation
    , structureWirePresentationMatches
    , putStructureInterfaceWireCache
    , getStructureInterfaceWireCache
    , SemanticEnvironmentError(..)
    , DeclarationInterfaceDelta
    , declarationInterfaceDelta
    , declarationDeltaSlot
    , declarationDeltaFacts
    , declarationDeltaAliases
    , declarationDeltaObjects
    , declarationDeltaPropositions
    , declarationDeltaDefinitionViews
    , declarationDeltaRegistrations
    , declarationDeltaEnvironment
    , DeclarationInterfaceError(..)
    , SemanticInterfaceId
    , semanticInterfaceIdDigest
    , SemanticInterface
    , semanticInterface
    , semanticInterfaceOwner
    , semanticInterfaceDirectInputs
    , semanticInterfaceDeclarations
    , semanticInterfaceAssertedId
    , SemanticInterfaceError(..)
    , validateSemanticInterface
    , renderSemanticInterfaceError
    , PrefixContextId
    , initialPrefixContextId
    , PrefixContextError(..)
    , nextPrefixContextId
    , prefixContextIdDigest
    , ProofSyntaxId
    , proofSyntaxId
    , proofSyntaxIdDigest
    , DeclarationSyntaxId
    , declarationSyntaxId
    , ProofValidationKey
    , proofValidationKey
    , proofValidationKeyDigest
    , ProofValidationRecord
    , proofValidationRecord
    , proofValidationRecordKey
    , proofValidationRecordCertificate
    , DeclarationValidationKey
    , declarationValidationKey
    , declarationValidationKeyDigest
    , DeclarationValidationRecord
    , declarationValidationRecord
    , declarationValidationRecordKey
    , declarationValidationRecordCertificates
    , ModuleArtefactKey
    , moduleArtefactKey
    , moduleArtefactKeyOwner
    , moduleArtefactKeyDirectSemanticInputs
    , moduleArtefactKeyTheory
    , ModuleArtefactKeyError(..)
    , ModuleArtefactId
    , moduleArtefactId
    , moduleArtefactIdDigest
    , ModuleArtefactResult
    , moduleArtefactResult
    , moduleArtefactResultId
    , moduleArtefactResultSyntax
    , moduleArtefactResultSemantic
    , moduleArtefactResultCertificates
    , putModuleArtefactKeyCache
    , getModuleArtefactKeyCache
    , putModuleArtefactIdCache
    , getModuleArtefactIdCache
    , putModuleArtefactResultCache
    , getModuleArtefactResultCache
    , putSemanticFactOccurrenceFingerprintCache
    , getSemanticFactOccurrenceFingerprintCache
    , putSemanticFactOccurrenceCache
    , getSemanticFactOccurrenceCache
    , putSemanticEnvironmentDeltaCache
    , getSemanticEnvironmentDeltaCache
    , putSemanticGlobalKeyCache
    , getSemanticGlobalKeyCache
    , putGlobalBindingRefCache
    , putGlobalNotionHeadCache
    , getGlobalNotionHeadCache
    , putDeclarationInterfaceDeltaCache
    , getDeclarationInterfaceDeltaCache
    , putSemanticInterfaceCache
    , getSemanticInterfaceCache
    , putSemanticInterfaceIdCache
    , getSemanticInterfaceIdCache
    , putPrefixContextIdCache
    , getPrefixContextIdCache
    , putProofValidationRecordCache
    , getProofValidationRecordCache
    , putDeclarationValidationRecordCache
    , getDeclarationValidationRecordCache
    ) where

import Base hiding (Empty)
import Data.Word (Word)
import Felix.Checking.Notion.SourceEvidence (UniversalBody(..), AtomTree(..), UniversalOperand(..))
import Felix.Checking.Notion.SourceEvidence qualified as Source
import Felix.Checking.Notion.Goal qualified as Goal
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Record qualified as Record
import Felix.Checking.Authority
import Felix.Checking.Core
import Felix.Checking.DefinitionView
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Checking.Identity
import Felix.Checking.Structure.Predicate qualified as StructurePredicate
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Module
import Felix.Parsed.Identity
import Felix.Source
import Felix.Syntax.Interface
import Felix.Syntax.Abstract
import Felix.Report.Location qualified as Location

import Control.DeepSeq (NFData(..))
import Control.Monad (unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.Functor.Identity (runIdentity)
import Data.ByteString (ByteString)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector


data DeclarationSlot = DeclarationSlot
    !ModuleName
    !LocalDeclarationOrdinal
    deriving stock (Show, Eq, Ord)

declarationSlot
    :: ModuleName
    -> LocalDeclarationOrdinal
    -> DeclarationSlot
declarationSlot =
    DeclarationSlot

declarationSlotModule :: DeclarationSlot -> ModuleName
declarationSlotModule (DeclarationSlot owner _) =
    owner

declarationSlotOrdinal
    :: DeclarationSlot
    -> LocalDeclarationOrdinal
declarationSlotOrdinal (DeclarationSlot _ ordinal) =
    ordinal

data FactSlot = FactSlot
    !ModuleName
    !LocalFactOrdinal
    deriving stock (Show, Eq, Ord)

factSlot :: ModuleName -> LocalFactOrdinal -> FactSlot
factSlot =
    FactSlot

factSlotModule :: FactSlot -> ModuleName
factSlotModule (FactSlot owner _) =
    owner

factSlotOrdinal :: FactSlot -> LocalFactOrdinal
factSlotOrdinal (FactSlot _ ordinal) =
    ordinal

newtype SemanticName =
    SemanticName Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

semanticName :: Text -> SemanticName
semanticName =
    SemanticName

semanticNameText :: SemanticName -> Text
semanticNameText (SemanticName name) =
    name

data FactSearchEligibility
    = SearchEligible
    | SearchIneligible
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

newtype SemanticFactOccurrenceFingerprint =
    SemanticFactOccurrenceFingerprint CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

semanticFactOccurrenceFingerprint
    :: FactPurpose
    -> FactSlot
    -> FactAuthority
    -> SemanticFactOccurrenceFingerprint
semanticFactOccurrenceFingerprint purpose slot authority =
    SemanticFactOccurrenceFingerprint
        (hashCacheFields
            "felix-semantic-fact-occurrence-v2"
            [ encodeCache (putFactSlotCache slot)
            , encodeCache (putFactAuthorityCache authority)
            , encodeCache (putFactPurposeCache purpose)
            ])

semanticFactFingerprintDigest
    :: SemanticFactOccurrenceFingerprint
    -> CacheDigest
semanticFactFingerprintDigest (SemanticFactOccurrenceFingerprint digest) = digest

data FactPurpose
    = GeneralFactPurpose
    | StructureFactPurpose !Schema.StructureLawId
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord FactPurpose where
    compare GeneralFactPurpose GeneralFactPurpose = EQ
    compare GeneralFactPurpose StructureFactPurpose{} = LT
    compare StructureFactPurpose{} GeneralFactPurpose = GT
    compare (StructureFactPurpose left) (StructureFactPurpose right) = compare left right

structureLawPurpose :: Schema.StructureLawId -> FactPurpose
structureLawPurpose = StructureFactPurpose

data SemanticFactOccurrence = SemanticFactOccurrence
    !FactSlot
    !FactAuthority
    !FactPurpose
    !FactSearchEligibility
    !(Maybe SemanticRelationComposition)
    deriving stock (Show, Eq, Ord, Generic)

semanticFactOccurrence
    :: FactPurpose -> FactSlot -> FactAuthority -> FactSearchEligibility
    -> SemanticFactOccurrence
semanticFactOccurrence purpose slot authority eligibility =
    SemanticFactOccurrence slot authority purpose eligibility Nothing

semanticFactOccurrenceWithRelationComposition
    :: FactPurpose -> FactSlot -> FactAuthority -> FactSearchEligibility
    -> SemanticRelationComposition -> SemanticFactOccurrence
semanticFactOccurrenceWithRelationComposition purpose slot authority eligibility composition =
    SemanticFactOccurrence slot authority purpose eligibility (Just composition)

semanticFactSlot :: SemanticFactOccurrence -> FactSlot
semanticFactSlot (SemanticFactOccurrence slot _ _ _ _) = slot

semanticFactProposition :: SemanticFactOccurrence -> PropositionId
semanticFactProposition = theoremRefProposition . factAuthorityTheorem . semanticFactAuthority

semanticFactAuthority :: SemanticFactOccurrence -> FactAuthority
semanticFactAuthority (SemanticFactOccurrence _ authority _ _ _) = authority

semanticFactPurpose :: SemanticFactOccurrence -> FactPurpose
semanticFactPurpose (SemanticFactOccurrence _ _ purpose _ _) = purpose

semanticFactSearchEligibility :: SemanticFactOccurrence -> FactSearchEligibility
semanticFactSearchEligibility (SemanticFactOccurrence _ _ _ eligibility _) = eligibility

semanticFactRelationComposition :: SemanticFactOccurrence -> Maybe SemanticRelationComposition
semanticFactRelationComposition (SemanticFactOccurrence _ _ _ _ composition) = composition

semanticFactFingerprint :: SemanticFactOccurrence -> SemanticFactOccurrenceFingerprint
semanticFactFingerprint (SemanticFactOccurrence slot authority purpose _ composition) =
    case composition of
        Nothing -> ordinary
        Just metadata -> SemanticFactOccurrenceFingerprint
            (hashCacheFields "felix-composition-fact-occurrence-v1"
                [encodeCache (putSemanticFactOccurrenceFingerprintCache ordinary),
                 encodeCache (putSemanticRelationCompositionCache metadata)])
  where
    ordinary = semanticFactOccurrenceFingerprint purpose slot authority

data SemanticAlias = SemanticAlias
    !SemanticName
    !SemanticFactOccurrenceFingerprint
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticAlias
    :: SemanticName
    -> SemanticFactOccurrenceFingerprint
    -> SemanticAlias
semanticAlias =
    SemanticAlias

semanticAliasName :: SemanticAlias -> SemanticName
semanticAliasName (SemanticAlias name _) =
    name

semanticAliasTarget
    :: SemanticAlias
    -> SemanticFactOccurrenceFingerprint
semanticAliasTarget (SemanticAlias _ target) =
    target

type SemanticDefinitionView =
    DefinitionView ObjectId SemanticFactOccurrenceFingerprint

semanticDefinitionViewObject :: SemanticDefinitionView -> ObjectId
semanticDefinitionViewObject =
    definitionViewObject

semanticDefinitionViewKind
    :: SemanticDefinitionView
    -> DefinitionViewKind
semanticDefinitionViewKind =
    definitionViewKind

semanticDefinitionViewTarget
    :: SemanticDefinitionView
    -> SemanticFactOccurrenceFingerprint
semanticDefinitionViewTarget =
    definitionViewTarget


-- | Exact source-level name used to resolve a declared monomorphic object.
-- Presentation markers and expression fixity are deliberately absent.
data AdjectiveReadingKind
    = OrdinaryAdjectiveReading
    | StructureAdjectiveReading
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data SemanticGlobalKey
    = SemanticLeftAdjective !AdjectiveReadingKind !Pattern
    | SemanticRightAdjective !AdjectiveReadingKind !Pattern
    | SemanticFunctionPhrase !Pattern !Pattern
    | SemanticNoun !Pattern !Pattern
    | SemanticVerb !VerbSurfaces
    | SemanticRelation !Token !ParameterArity
    | SemanticExpressionFunction !Pattern
    | SemanticTypedConstant !Token !CoreType
    | SemanticPrefixPredicate !Text !Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticGlobalKeyType :: SemanticGlobalKey -> Maybe CoreType
semanticGlobalKeyType = \case
    SemanticLeftAdjective _reading pat ->
        Just (setArguments (1 + patternArity pat) TyProp)
    SemanticRightAdjective _reading pat ->
        Just (setArguments (1 + patternArity pat) TyProp)
    SemanticFunctionPhrase singular plural
        | patternArity singular == patternArity plural ->
            Just (setArguments (patternArity singular) TySet)
        | otherwise -> Nothing
    SemanticNoun singular plural
        | patternArity singular == patternArity plural ->
            Just (setArguments (1 + patternArity singular) TyProp)
        | otherwise -> Nothing
    SemanticVerb surfaces ->
        Just
            (setArguments
                (1 + patternArity
                    (patternFromHoley
                        (verbSurfaceSingular surfaces)))
                TyProp)
    SemanticRelation _token arity ->
        Just
            (setArguments
                (2 + parameterArityValue arity)
                TyProp)
    SemanticExpressionFunction pat ->
        Just (setArguments (patternArity pat) TySet)
    SemanticTypedConstant _token coreType ->
        Just coreType
    SemanticPrefixPredicate _command arity ->
        Just (setArguments arity TyProp)
  where
    patternArity :: Pattern -> Natural
    patternArity = \case
        End -> 0
        HoleCons rest -> 1 + patternArity rest
        TokenCons _token rest -> patternArity rest

    setArguments :: Natural -> CoreType -> CoreType
    setArguments argumentCount result =
        foldr
            (const (TyArrow TySet))
            result
            [1 .. argumentCount]

semanticGlobalKeyFromLexicalEntry
    :: CanonicalLexicalEntry
    -> Maybe SemanticGlobalKey
semanticGlobalKeyFromLexicalEntry = \case
    CanonicalUserAdjective side (AdjectiveSurfaceKey pat) ->
        Just (semanticAdjectiveKey OrdinaryAdjectiveReading side pat)
    CanonicalIntrinsicAdjective side pat _marker ->
        Just (semanticAdjectiveKey OrdinaryAdjectiveReading side pat)
    CanonicalFunctionPhrase singular plural _marker ->
        Just (SemanticFunctionPhrase singular plural)
    CanonicalNoun singular plural _marker ->
        Just (SemanticNoun singular plural)
    CanonicalVerb surfaces _marker ->
        Just (SemanticVerb surfaces)
    CanonicalRelation token arity _marker ->
        Just (SemanticRelation token arity)
    CanonicalExpressionFunction pat _marker _fixity ->
        Just (SemanticExpressionFunction pat)
    CanonicalTypedConstant token concreteType _marker ->
        Just
            (SemanticTypedConstant
                token
                (concreteTypeCoreType concreteType))
    CanonicalPrefixPredicate command arity _marker ->
        Just (SemanticPrefixPredicate command arity)
    CanonicalStructureNoun{} ->
        Nothing
    CanonicalStructureOperation{} ->
        Nothing

semanticAdjectiveKey
    :: AdjectiveReadingKind
    -> AdjectiveSide
    -> Pattern
    -> SemanticGlobalKey
semanticAdjectiveKey reading side pat =
    case side of
        LeftAdjectiveSide -> SemanticLeftAdjective reading pat
        RightAdjectiveSide -> SemanticRightAdjective reading pat

concreteTypeCoreType :: ConcreteType -> CoreType
concreteTypeCoreType = \case
    ConcreteProp -> TyProp
    ConcreteSet -> TySet
    ConcreteArrow domain codomain ->
        TyArrow
            (concreteTypeCoreType domain)
            (concreteTypeCoreType codomain)

data SemanticGlobalTarget
    = GlobalReference !ObjectId
    | TransparentExpansion !ObjectId
    | ContextualTransparentExpansion
        !ObjectId
        !(Map.Map StructSymbol (FieldId, ObjectId))
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticGlobalTargetObject :: SemanticGlobalTarget -> ObjectId
semanticGlobalTargetObject = \case
    GlobalReference identity -> identity
    TransparentExpansion identity -> identity
    ContextualTransparentExpansion identity _requirements -> identity

semanticGlobalTargetRequirements
    :: SemanticGlobalTarget
    -> Map.Map StructSymbol (FieldId, ObjectId)
semanticGlobalTargetRequirements = \case
    GlobalReference{} -> Map.empty
    TransparentExpansion{} -> Map.empty
    ContextualTransparentExpansion _identity requirements -> requirements

-- Positions are outermost-first in the checked theorem telescope. Relator
-- source slots 0 and 1 are endpoints; remaining slots name theorem binders.
-- Logical relators and patterns are reconstructed from the checked theorem.
data SemanticRelationComposition = SemanticRelationComposition
    { compositionEndpointPositions :: !(Natural, Natural, Natural)
    , compositionConditions :: !(Vector AbbreviationExpansion)
    , compositionLeftSource :: !SemanticRelationSource
    , compositionRightSource :: !SemanticRelationSource
    , compositionResultSource :: !SemanticRelationSource
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- Captures remain explicit even when a transparent expansion erases them.
-- They use the body's slot layout, but cannot refer to either endpoint slot.
data SemanticRelationSource = SemanticRelationSource
    { relationSourceBody :: !AbbreviationExpansion
    , relationSourceCaptures :: !(Vector ExpansionTerm)
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

newtype SemanticBindingLabel = SemanticBindingLabel Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

semanticBindingLabel :: Text -> SemanticBindingLabel
semanticBindingLabel =
    SemanticBindingLabel

semanticBindingLabelText :: SemanticBindingLabel -> Text
semanticBindingLabelText (SemanticBindingLabel label) =
    label

-- Source-order formals include the contextual receiver last. Locals count
-- nearest-first beneath body binders. Opaque subterms use the body's ordinary
-- de Bruijn context; only admission and bounded instantiation interpret them.
data ExpansionTerm
    = ExpansionFormal !Natural
    | ExpansionLocal !Natural
    | ExpansionProvider !SourceProviderHead !(Vector ExpansionTerm)
    | ExpansionPair !ExpansionTerm !ExpansionTerm
    | ExpansionOpaque !(CanonicalTerm ObjectId)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data ExpansionEquality = ExpansionEquality
    !ExpansionTerm !ExpansionTerm !ConjunctionPath
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- Residual positions refer to the stored checked body. Their written origin
-- belongs to each use site, so payload construction retains no source location.
data AbbreviationExpansion
    = TermExpansion !ExpansionTerm
    | PropositionExpansion
        !(Source.SourceEvidence ExpansionTerm (AtomTemplate ExpansionTerm)) ![ExpansionEquality]
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data ExpansionFailure
    = ExpansionWorkExhausted !Natural
    | ExpansionInvalid !Text
    | ExpansionAtPath !Text !ExpansionFailure
    deriving stock (Show, Eq)

atExpansionPath :: Monad m => Text -> ExpansionWork m value -> ExpansionWork m value
atExpansionPath path action = Except.catchE action (Except.throwE . ExpansionAtPath path)

expansionRejectedDebit :: ExpansionFailure -> Maybe Natural
expansionRejectedDebit = \case
    ExpansionWorkExhausted amount -> Just amount
    ExpansionInvalid{} -> Nothing
    ExpansionAtPath _ failure -> expansionRejectedDebit failure

renderExpansionFailure :: ExpansionFailure -> Text
renderExpansionFailure = \case
    ExpansionWorkExhausted _ -> "expansion work allowance exhausted"
    ExpansionInvalid reason -> reason
    ExpansionAtPath path failure -> path <> ": " <> renderExpansionFailure failure

-- The declaration or written application owns this allowance. Running an
-- inner operation never replenishes it; failure retains all accepted debits.
type ExpansionWork m = Except.ExceptT ExpansionFailure (State.StateT Word m)

formationMaximumExpansionWork :: Word
formationMaximumExpansionWork = 131072

runExpansionWork :: Word -> ExpansionWork m value -> m (Either ExpansionFailure value, Word)
runExpansionWork allowance action = State.runStateT (Except.runExceptT action) allowance

chargeExpansion :: Monad m => Natural -> ExpansionWork m ()
chargeExpansion amount = do
    remaining <- State.get
    if amount <= fromIntegral remaining then State.put (remaining - fromIntegral amount)
    else Except.throwE (ExpansionWorkExhausted amount)

expansionCoreWork
    :: (Monad m, Show failure)
    => (Word -> (Either (CountedCoreFailure failure) value, Word))
    -> ExpansionWork m value
expansionCoreWork operation = do
    allowance <- State.get
    let (result, remaining) = operation allowance
    State.put remaining
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> Except.throwE (ExpansionWorkExhausted 1)
        Left (CountedCoreOperationFailed failure) -> Except.throwE (ExpansionInvalid (Text.pack (show failure)))

data SemanticGlobalBinding = SemanticGlobalBinding
    !SemanticGlobalKey
    !SemanticBindingLabel
    !SemanticGlobalTarget
    !(Maybe FormationContract)
    !(Maybe AbbreviationExpansion)
    !(Maybe (BindingConstruction SemanticFactOccurrenceFingerprint))
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticGlobalBinding
    :: SemanticGlobalKey
    -> SemanticBindingLabel
    -> SemanticGlobalTarget
    -> SemanticGlobalBinding
semanticGlobalBinding =
    \key label target -> SemanticGlobalBinding key label target Nothing Nothing Nothing

semanticGlobalBindingWithContract
    :: SemanticGlobalKey
    -> SemanticBindingLabel
    -> SemanticGlobalTarget
    -> Maybe FormationContract
    -> SemanticGlobalBinding
semanticGlobalBindingWithContract =
    \key label target contract ->
        SemanticGlobalBinding key label target contract Nothing Nothing

semanticGlobalBindingWithMetadata
    :: SemanticGlobalKey
    -> SemanticBindingLabel
    -> SemanticGlobalTarget
    -> Maybe FormationContract
    -> Maybe AbbreviationExpansion
    -> SemanticGlobalBinding
semanticGlobalBindingWithMetadata key label target contract expansion =
    SemanticGlobalBinding key label target contract expansion Nothing

data BindingConstruction fact
    = DatatypeConstruction !(DatatypeDescriptor fact)
    | RecursiveConstruction !(RecursiveDefinitionDescriptor fact)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- The body supplies the recursor and branch lambdas. This descriptor retains
-- source ownership and formation-only information that a transparent object
-- cannot distinguish (in particular, Set headers).
data RecursiveDefinitionDescriptor fact = RecursiveDefinitionDescriptor
    { recursiveDefinitionDatatype :: !GlobalBindingRef
    , recursiveDefinitionArguments :: ![Natural]
    , recursiveDefinitionHeaders :: ![ResidualTemplate]
    , recursiveDefinitionBranches :: !(NonEmpty AbbreviationExpansion)
    , recursiveDefinitionEquations :: !(NonEmpty (SemanticGlobalKey, fact))
    }
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Attached to the carrier's source binding. Parameter and constructor arities
-- come from ordinary object types; premise domains use the parameter context.
data DatatypeDescriptor fact = DatatypeDescriptor
    { datatypeDescriptorCases :: !(NonEmpty (DatatypeCase fact))
    , datatypeDescriptorCasesFact :: !fact
    , datatypeDescriptorInductionFact :: !fact
    , datatypeDescriptorPredicateInductionFact :: !fact
    }
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data DatatypeCase fact = DatatypeCase
    { datatypeCaseName :: !Text
    , datatypeCaseConstructor :: !SemanticGlobalKey
    , datatypeCasePremises :: ![DatatypePremise]
    , datatypeCaseFields :: ![Natural]
    , datatypeCaseIntroductionFact :: !fact
    , datatypeCaseInjectivityFact :: !(Maybe fact)
    -- Each pair occurs once, in declaration order, with the later constructor.
    , datatypeCaseDistinctnessFacts :: ![(SemanticGlobalKey, fact)]
    }
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data DatatypePremise
    = DatatypeRecursivePremise
    | DatatypeFixedPremise !(CanonicalTerm ObjectId)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticGlobalBindingDatatype :: SemanticGlobalBinding -> Maybe (DatatypeDescriptor SemanticFactOccurrenceFingerprint)
semanticGlobalBindingDatatype binding = case semanticGlobalBindingConstruction binding of
    Just (DatatypeConstruction descriptor) -> Just descriptor
    _ -> Nothing

semanticGlobalBindingRecursion :: SemanticGlobalBinding -> Maybe (RecursiveDefinitionDescriptor SemanticFactOccurrenceFingerprint)
semanticGlobalBindingRecursion binding = case semanticGlobalBindingConstruction binding of
    Just (RecursiveConstruction descriptor) -> Just descriptor
    _ -> Nothing

semanticGlobalBindingConstruction :: SemanticGlobalBinding -> Maybe (BindingConstruction SemanticFactOccurrenceFingerprint)
semanticGlobalBindingConstruction (SemanticGlobalBinding _ _ _ _ _ descriptor) = descriptor

withSemanticConstruction :: BindingConstruction SemanticFactOccurrenceFingerprint -> SemanticGlobalBinding -> SemanticGlobalBinding
withSemanticConstruction descriptor (SemanticGlobalBinding key label target contract expansion _) =
    SemanticGlobalBinding key label target contract expansion (Just descriptor)

withSemanticDatatype :: DatatypeDescriptor SemanticFactOccurrenceFingerprint -> SemanticGlobalBinding -> SemanticGlobalBinding
withSemanticDatatype = withSemanticConstruction . DatatypeConstruction

semanticGlobalBindingKey
    :: SemanticGlobalBinding
    -> SemanticGlobalKey
semanticGlobalBindingKey
        (SemanticGlobalBinding key _label _target _contract _expansion _datatype) =
    key

semanticGlobalBindingLabel
    :: SemanticGlobalBinding
    -> SemanticBindingLabel
semanticGlobalBindingLabel
        (SemanticGlobalBinding _key label _target _contract _expansion _datatype) =
    label

semanticGlobalBindingTarget
    :: SemanticGlobalBinding
    -> SemanticGlobalTarget
semanticGlobalBindingTarget
        (SemanticGlobalBinding _key _label target _contract _expansion _datatype) =
    target

semanticGlobalBindingContract
    :: SemanticGlobalBinding
    -> Maybe FormationContract
semanticGlobalBindingContract
        (SemanticGlobalBinding _key _label _target contract _expansion _datatype) =
    contract

semanticGlobalBindingExpansion
    :: SemanticGlobalBinding
    -> Maybe AbbreviationExpansion
semanticGlobalBindingExpansion
        (SemanticGlobalBinding _key _label _target _contract expansion _datatype) =
    expansion

data GlobalBindingRef = GlobalBindingRef
    !DeclarationSlot
    !SemanticGlobalKey
    deriving stock (Show, Eq, Ord)

instance NFData GlobalBindingRef where
    rnf reference = reference `seq` ()

globalBindingRef
    :: DeclarationSlot
    -> SemanticGlobalKey
    -> GlobalBindingRef
globalBindingRef =
    GlobalBindingRef

globalBindingRefOwner :: GlobalBindingRef -> DeclarationSlot
globalBindingRefOwner (GlobalBindingRef owner _key) =
    owner

globalBindingRefKey :: GlobalBindingRef -> SemanticGlobalKey
globalBindingRefKey (GlobalBindingRef _owner key) =
    key

-- | Stable semantic identity of one eligible written set-valued provider.
-- Global providers retain their owning declaration.  Explicit structure-field
-- providers retain both the canonical field identity and the checked unary
-- projection object; the receiver remains an ordinary provider argument.
data IntrinsicProviderId
    = PowerSetProvider
    | GlobalChoiceProvider
    | EmptySetProvider
    | FirstProjectionProvider
    | SecondProjectionProvider
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

intrinsicProviderCoreTag :: IntrinsicProviderId -> CoreIntrinsicTag
intrinsicProviderCoreTag = \case
    PowerSetProvider -> PowerSet
    GlobalChoiceProvider -> GlobalChoice
    EmptySetProvider -> Empty
    FirstProjectionProvider -> FirstProjection
    SecondProjectionProvider -> SecondProjection

-- | Construct exactly one admitted fixed provider application.  The closed
-- whitelist is checked against the authoritative Core signature rather than
-- carrying a second arity table.
intrinsicProviderApplication
    :: IntrinsicProviderId
    -> Vector (CanonicalTerm global)
    -> Maybe (CanonicalTerm global)
intrinsicProviderApplication provider arguments =
    case firstOrderSymbolShape
            (coreIntrinsicType (intrinsicProviderCoreTag provider)) of
        Just (arity, TySet)
            | arity == Vector.length arguments ->
                Just
                    (foldl'
                        CApp
                        (CIntrinsic (intrinsicProviderCoreTag provider))
                        (toList arguments))
        _ -> Nothing

-- | Reconstruct one written nonempty finite-set literal from its exact
-- positional source spine.  The empty set has its own nullary intrinsic
-- provider and is deliberately not represented by this variadic head.
finiteSetLiteralProviderApplication
    :: NonEmpty (CanonicalTerm global)
    -> CanonicalTerm global
finiteSetLiteralProviderApplication arguments =
    foldr
        canonicalSetInsert
        (CIntrinsic Empty)
        (toList arguments)

data SourceProviderHead
    = GlobalSourceProvider !GlobalBindingRef
    | StructureFieldSourceProvider !FieldId !ObjectId
    | IntrinsicSourceProvider !IntrinsicProviderId
    | FiniteSetLiteralSourceProvider
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Stable identities for the exact predicate families admitted as reusable
-- notion atoms.
data GlobalNotionHead
    = NounNotionHead !GlobalBindingRef
    | AdjectiveNotionHead !GlobalBindingRef
    | RelationNotionHead !GlobalBindingRef
    | VerbNotionHead !GlobalBindingRef
    | PrefixPredicateNotionHead !GlobalBindingRef
    deriving stock (Show, Eq, Ord)

instance NFData GlobalNotionHead where
    rnf head' = head' `seq` ()

globalNotionHeadReference :: GlobalNotionHead -> GlobalBindingRef
globalNotionHeadReference = \case
    NounNotionHead reference -> reference
    AdjectiveNotionHead reference -> reference
    RelationNotionHead reference -> reference
    VerbNotionHead reference -> reference
    PrefixPredicateNotionHead reference -> reference

data GlobalNotionRole
    = HostedGlobalNotion
    | UnhostedGlobalPredicate
    deriving stock (Show, Eq, Ord)

-- | Whether source syntax gives a predicate a distinguished host. This does
-- not determine which checked forward definition views may produce it.
globalNotionHeadRole :: GlobalNotionHead -> GlobalNotionRole
globalNotionHeadRole = \case
    NounNotionHead{} -> HostedGlobalNotion
    AdjectiveNotionHead{} -> HostedGlobalNotion
    RelationNotionHead{} -> HostedGlobalNotion
    VerbNotionHead{} -> HostedGlobalNotion
    PrefixPredicateNotionHead{} -> UnhostedGlobalPredicate

globalNotionHeadMatchesKey :: GlobalNotionHead -> SemanticGlobalKey -> Bool
globalNotionHeadMatchesKey head' = case head' of
    NounNotionHead{} -> \case
        SemanticNoun{} -> True
        _ -> False
    AdjectiveNotionHead{} -> \case
        SemanticLeftAdjective{} -> True
        SemanticRightAdjective{} -> True
        _ -> False
    RelationNotionHead{} -> \case
        SemanticRelation{} -> True
        _ -> False
    VerbNotionHead{} -> \case
        SemanticVerb{} -> True
        _ -> False
    PrefixPredicateNotionHead{} -> \case
        SemanticPrefixPredicate{} -> True
        _ -> False

-- | The distinguished subject's position in a binding-order application.
-- Atomic expansion templates use this order because they abstract the
-- checked transparent body of the binding itself.
globalNotionHostFocus :: SemanticGlobalKey -> Maybe OccurrenceArgumentIx
globalNotionHostFocus = \case
    SemanticNoun{} -> Just (OccurrenceArgumentIx 0)
    SemanticLeftAdjective{} -> Just (OccurrenceArgumentIx 0)
    SemanticRightAdjective{} -> Just (OccurrenceArgumentIx 0)
    SemanticVerb{} -> Just (OccurrenceArgumentIx 0)
    SemanticRelation _token arity ->
        Just (OccurrenceArgumentIx (parameterArityValue arity))
    _ -> Nothing

-- | Convert notion arguments to the checked binding's application order.
-- Hosted families arrive in focus-first occurrence order; relation bindings
-- place notation parameters before the left and right operands.  Hostless
-- prefix predicates already use binding order and retain it unchanged.
globalNotionBindingArguments
    :: SemanticGlobalKey
    -> Vector argument
    -> Maybe (Vector argument)
globalNotionBindingArguments key arguments = case key of
    SemanticNoun{} -> Just arguments
    SemanticLeftAdjective{} -> Just arguments
    SemanticRightAdjective{} -> Just arguments
    SemanticVerb{} -> Just arguments
    SemanticRelation _token arity -> do
        (left, trailing) <- Vector.uncons arguments
        let parameterCount = fromIntegral (parameterArityValue arity)
            (parameters, operands) = Vector.splitAt parameterCount trailing
        guard (Vector.length operands == 1)
        right <- Vector.headM operands
        pure (parameters <> Vector.fromList [left, right])
    SemanticPrefixPredicate _command arity -> do
        guard (Vector.length arguments == fromIntegral arity)
        pure arguments
    _ -> Nothing

-- | Invert the same binding permutation when describing a checked predicate
-- application as a source notion. Relation parameters are not the host.
globalNotionOccurrenceArguments
    :: SemanticGlobalKey
    -> Vector argument
    -> Maybe (Vector argument)
globalNotionOccurrenceArguments key arguments = do
    order <- globalNotionBindingArguments key
        (Vector.enumFromN 0 (Vector.length arguments))
    pure (Vector.update arguments (Vector.zip order arguments))

newtype SemanticStructureNotionHead = SemanticStructureNotionHead StructureId
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

-- A fresh head is backed by a checked pending registration. Declaration
-- materializes it against the complete candidate environment before admission.
pendingStructureNotionHead :: StructurePredicate.PendingStructureRegistration -> SemanticStructureNotionHead
pendingStructureNotionHead = SemanticStructureNotionHead
    . Schema.resolvedSchemaId . StructurePredicate.pendingStructureSchema

structureNotionHeadId :: SemanticStructureNotionHead -> StructureId
structureNotionHeadId (SemanticStructureNotionHead identity) = identity

-- Shape identity follows the checked schema catalogue, independently of laws.
newtype SemanticRecordShapeKey = SemanticRecordShapeKey [(FieldId, ObjectId, ObjectId)]
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticRecordShapeKey :: Schema.ResolvedStructureSchema -> SemanticRecordShapeKey
semanticRecordShapeKey schema = SemanticRecordShapeKey
    [(Schema.resolvedFieldIdentity field, Schema.resolvedFieldSelector field, Schema.resolvedFieldProjection field)
    | field <- Map.elems (Schema.resolvedSchemaFields schema)]

semanticRecordShapeSelectors :: SemanticRecordShapeKey -> [ObjectId]
semanticRecordShapeSelectors (SemanticRecordShapeKey fields) = [selector | (_,selector,_) <- fields]

-- The selector applies to the result after the original telescope and premises.
data SemanticFactBranch = SemanticFactBranch
    !SemanticFactOccurrenceFingerprint !ConjunctionPath
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

semanticFactBranchFact :: SemanticFactBranch -> SemanticFactOccurrenceFingerprint
semanticFactBranchFact (SemanticFactBranch fact _) = fact

semanticFactBranchPath :: SemanticFactBranch -> ConjunctionPath
semanticFactBranchPath (SemanticFactBranch _ path) = path

newtype OccurrenceArgumentIx = OccurrenceArgumentIx Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

-- A semantic description of a checked, closed set, not a source provider or
-- proof. Cache admission rechecks its exact objects and type. Search interns
-- this payload separately; recursive Core never becomes a shallow Ord key.
newtype ClosedSetValue = ClosedSetValue {closedSetValueTerm :: CanonicalTerm ObjectId}
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

closedSetValue :: ScopedCheckedCore ObjectId -> Maybe ClosedSetValue
closedSetValue = runIdentity . closedSetValueWith (pure ())

closedSetValueWith :: Monad m => m () -> ScopedCheckedCore ObjectId -> m (Maybe ClosedSetValue)
closedSetValueWith charge checked
    | scopedCoreType checked /= TySet = pure Nothing
    | otherwise = do
        closed <- canonicalClosedWith charge (scopedCoreTerm checked)
        pure (if closed then Just (ClosedSetValue (scopedCoreTerm checked)) else Nothing)

materializeClosedSetValue :: CheckedObjectClosure -> ClosedSetValue -> Either Text (CanonicalTerm ObjectId)
materializeClosedSetValue closure value = do
    checked <- first (Text.pack . show)
        (checkScopedCanonicalCore (globalTypingFromClosure closure) [] (closedSetValueTerm value))
    unless (scopedCoreType checked == TySet) (Left "a closed formation value is not a set")
    pure (scopedCoreTerm checked)

-- | The deliberately small set-term language shared by formation contracts
-- and theorem-backed notion rules. Every constructor denotes a set; provider
-- ownership is retained rather than reconstructed from expanded Core.
data SetTermTemplate variable
    = TemplateVariable !variable
    | TemplateClosed !ClosedSetValue
    | TemplateProvider
        !SourceProviderHead
        !(Vector (SetTermTemplate variable))
    | TemplateOrderedPair
        !(SetTermTemplate variable)
        !(SetTermTemplate variable)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

type FormationTermTemplate = SetTermTemplate OccurrenceArgumentIx

type RuleTermTemplate = SetTermTemplate ViewVariableIx

-- Opaque leaves retain their checked set expressions, including clause slots.
-- Only the written provider/pair nodes supply a structural argument view.
type SupportTermTemplate = SetTermTemplate (CanonicalTerm ObjectId)

-- Substitute a complete written view at a parameter boundary. Inside an
-- opaque operand only Core is substituted; its interior stays opaque.
instantiateSupportPrefixWith
    :: Monad m => m () -> Natural
    -> (Natural -> Natural -> m (SupportTermTemplate, CanonicalTerm ObjectId))
    -> Natural -> SupportTermTemplate -> m SupportTermTemplate
instantiateSupportPrefixWith visit arity actual depth = go
  where
    go term = visit >> case term of
        TemplateVariable (CBound index) | index >= depth && index-depth < arity -> fst <$> actual depth (index-depth)
        TemplateVariable value -> TemplateVariable <$> instantiateCanonicalPrefixWith visit arity
            (\nested slot -> snd <$> actual nested slot) depth value
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateProvider provider children -> TemplateProvider provider <$> traverse go children
        TemplateOrderedPair a b -> TemplateOrderedPair <$> go a <*> go b

traverseSetTermTemplateVariables
    :: Applicative f
    => (left -> f right)
    -> SetTermTemplate left
    -> f (SetTermTemplate right)
traverseSetTermTemplateVariables = traverse

data AtomTemplate variable
    = GlobalAtomTemplate !GlobalNotionHead !(Vector variable)
    | StructureAtomTemplate
        !SemanticStructureNotionHead !(Vector variable)
    | MembershipAtomTemplate !variable !variable
    | ExactStructureAtomTemplate !SemanticRecordShapeKey !variable
    | NegativeGlobalAtomTemplate !GlobalNotionHead !(Vector variable)
    | NegativeStructureAtomTemplate !SemanticStructureNotionHead !(Vector variable)
    | NegativeMembershipAtomTemplate !variable !variable
    | NegativeExactStructureAtomTemplate !SemanticRecordShapeKey !variable
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data AtomPolarity = PositivePolarity | NegativePolarity
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- Polarity is nonrecursive data. Positive atoms retain their compact existing
-- representation; a negative atom cannot contain another signed atom.
atomPolarity :: AtomTemplate variable -> AtomPolarity
atomPolarity atom = case negativeAtomBody atom of
    Just{} -> NegativePolarity
    Nothing -> PositivePolarity

pattern NegativeAtomTemplate :: AtomTemplate variable -> AtomTemplate variable
pattern NegativeAtomTemplate body <- (negativeAtomBody -> Just body)
{-# COMPLETE GlobalAtomTemplate, StructureAtomTemplate, MembershipAtomTemplate, ExactStructureAtomTemplate, NegativeAtomTemplate #-}

negativeAtomBody :: AtomTemplate variable -> Maybe (AtomTemplate variable)
negativeAtomBody = \case
    NegativeGlobalAtomTemplate head' arguments -> Just (GlobalAtomTemplate head' arguments)
    NegativeStructureAtomTemplate head' arguments -> Just (StructureAtomTemplate head' arguments)
    NegativeMembershipAtomTemplate element set -> Just (MembershipAtomTemplate element set)
    NegativeExactStructureAtomTemplate shape subject -> Just (ExactStructureAtomTemplate shape subject)
    _ -> Nothing

withAtomPolarity :: AtomPolarity -> AtomTemplate variable -> AtomTemplate variable
withAtomPolarity polarity atom = case (polarity,atom) of
    (PositivePolarity,NegativeAtomTemplate body) -> body
    (NegativePolarity,GlobalAtomTemplate head' arguments) -> NegativeGlobalAtomTemplate head' arguments
    (NegativePolarity,StructureAtomTemplate head' arguments) -> NegativeStructureAtomTemplate head' arguments
    (NegativePolarity,MembershipAtomTemplate element set) -> NegativeMembershipAtomTemplate element set
    (NegativePolarity,ExactStructureAtomTemplate shape subject) -> NegativeExactStructureAtomTemplate shape subject
    _ -> atom

atomArity :: AtomTemplate variable -> Int
atomArity = \case
    GlobalAtomTemplate _ arguments -> Vector.length arguments
    StructureAtomTemplate _ arguments -> Vector.length arguments
    MembershipAtomTemplate{} -> 2
    ExactStructureAtomTemplate{} -> 1
    NegativeGlobalAtomTemplate _ arguments -> Vector.length arguments
    NegativeStructureAtomTemplate _ arguments -> Vector.length arguments
    NegativeMembershipAtomTemplate{} -> 2
    NegativeExactStructureAtomTemplate{} -> 1

-- | Traverse an atomic template without erasing its family.  Vector arguments
-- are visited left to right; membership visits the element before the set.
traverseAtomTemplateArguments
    :: Applicative f
    => (left -> f right)
    -> AtomTemplate left
    -> f (AtomTemplate right)
traverseAtomTemplateArguments = traverse

type NotionTemplate = AtomTemplate FormationTermTemplate

-- Atomic leaves retain written term construction. Whole leaves have exact
-- proposition identity and never supply terms for parameter determination.
data NotionLeaf atom whole = AtomicLeaf !atom | WholeLeaf !whole
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Free indices belong to the enclosing nearest-first set parameter context.
-- Internal binders retain their own types and are never parameter positions.
data ResidualTemplate = DescribedResidualTemplate
    { residualTemplateFormula :: !(CanonicalTerm ObjectId)
    , residualTemplateEvidence :: !(Maybe (Source.SourceEvidence SupportTermTemplate (AtomTemplate RuleTermTemplate)))
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- Exact whole formulas do not require an elimination description. Where one
-- exists, inspecting the formula must preserve its checked source association.
pattern ResidualTemplate :: CanonicalTerm ObjectId -> ResidualTemplate
pattern ResidualTemplate formula <- DescribedResidualTemplate formula _ where
    ResidualTemplate formula = DescribedResidualTemplate formula Nothing
{-# COMPLETE ResidualTemplate #-}

describedResidualTemplate
    :: CanonicalTerm ObjectId -> Source.SourceEvidence SupportTermTemplate (AtomTemplate RuleTermTemplate) -> ResidualTemplate
describedResidualTemplate formula evidence = case evidence of
    Source.SourceResidual{} -> ResidualTemplate formula
    _ -> DescribedResidualTemplate formula (Just evidence)

residualTemplateVariables :: ResidualTemplate -> Set ViewVariableIx
residualTemplateVariables = Set.map ViewVariableIx
    . runIdentity . canonicalFreeIndicesWith (pure ()) . residualTemplateFormula

-- Rich operands may retain parameters erased from their Core denotation.
-- Formula-local binders are removed before returning source parameters.
residualTemplateParametersWith
    :: Monad m => m () -> ResidualTemplate -> m (Set ViewVariableIx)
residualTemplateParametersWith charge template = do
    exact <- canonicalFreeIndicesWith charge (residualTemplateFormula template)
    let evidence = fromMaybe (Source.SourceResidual Nothing) (residualTemplateEvidence template)
        operands = Source.sourceInputsAtDepth
            (fmap (fmap (\(ViewVariableIx index) -> CBound index)) . toList) evidence
    described <- for operands \(Source.SourceInput binders term) -> do
        indices <- traverse (canonicalFreeIndicesWith charge) term
        let depth = fromIntegral (length binders)
        pure (Set.fromList [index-depth | values <- toList indices, index <- Set.toAscList values, index >= depth])
    pure (Set.map ViewVariableIx (exact <> Set.unions described))

positiveResidualParametersWith
    :: Monad m => m () -> ResidualTemplate -> m (Maybe (Set ViewVariableIx))
positiveResidualParametersWith charge template = do
    plan <- Goal.compileGoal charge (residualTemplateFormula template)
        (fromMaybe (Source.SourceResidual Nothing) (residualTemplateEvidence template))
    if Goal.goalPositive plan then Just <$> residualTemplateParametersWith charge template else pure Nothing

data WholeTemplate term
    = WholeUniversal !(UniversalTemplate term)
    | WholeResidual !ResidualTemplate
    deriving stock (Show, Eq, Ord, Functor, Generic)
    deriving anyclass (NFData)

-- | A variable in the universally closed theorem backing a notion view.
-- Index zero denotes the nearest (innermost) open theorem binder.
newtype ViewVariableIx = ViewVariableIx Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

-- | Unary view premises intentionally exclude membership.  Membership has one
-- coarse static head, so allowing it here would make every direct membership
-- in a scope relevant to an expected-directed query.
data NotionViewPremiseTemplate
    = GlobalNotionViewPremise
        !GlobalNotionHead !(Vector RuleTermTemplate)
    | StructureNotionViewPremise
        !SemanticStructureNotionHead !(Vector RuleTermTemplate)
    | ExactProviderMembershipPremise
        !RuleTermTemplate
        !SourceProviderHead
        !(Vector RuleTermTemplate)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

type RuleConclusion = NotionLeaf (AtomTemplate RuleTermTemplate) ResidualTemplate

type NotionViewTemplate = RuleConclusion

-- | The source-independent premise and conclusion of a unary theorem rule.
data NotionViewRule = NotionViewRule
    { notionViewPremise :: !NotionViewPremiseTemplate
    , notionViewConclusion :: !NotionViewTemplate
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | A closed classification shape: one hosted global notion at an exact
-- nullary intrinsic, with no theorem variables or premises.
data NullaryProviderRule = NullaryProviderRule
    { nullaryProvider :: !IntrinsicProviderId
    , nullaryConclusion :: !GlobalNotionHead
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Exact source grouping of the notion premises contributed by one checked
-- claim header.  This tree is logical data: replay rebuilds precisely this
-- conjunction before eliminating the corresponding curried implication.
type UniversalTemplate term = UniversalBody (AtomTemplate (SetTermTemplate (UniversalOperand term)))

data RulePremiseTree term
    = RulePremiseAtom !(AtomTemplate term)
    | RulePremiseUniversal !(UniversalTemplate term)
    | RulePremiseResidual !ResidualTemplate
    | RulePremiseAnd
        !(RulePremiseTree term)
        !(RulePremiseTree term)
    deriving stock (Show, Eq, Ord, Functor, Generic)
    deriving anyclass (NFData)

newtype RulePremiseBundles term = RulePremiseBundles
    (NonEmpty (RulePremiseTree term))
    deriving stock (Show, Eq, Ord, Functor, Generic)
    deriving newtype (NFData)

-- | Provider-result classifications either apply without implication
-- premises or retain the exact nonempty forest of their checked headers.
-- Other notion-rule families continue to use 'RulePremiseBundles' directly.
data ProviderResultPremises term
    = ProviderResultUnconditional
    | ProviderResultGuarded !(RulePremiseBundles term)
    deriving stock (Show, Eq, Ord, Functor, Generic)
    deriving anyclass (NFData)

-- | The rich, theorem-independent part of one positive notion rule.  The
-- source fact fingerprint is attached only after declaration planning has
-- selected the clean supporting candidate.  Construction checks all closed
-- template invariants; exact theorem reconstruction is checked again when the
-- declaration is materialized in its visible environment.
data CheckedNotionRuleSkeleton = CheckedNotionRuleSkeleton
    !Natural
    ![RulePremiseTree RuleTermTemplate]
    !(AtomTemplate RuleTermTemplate)
    deriving stock (Show, Eq, Ord)

instance NFData CheckedNotionRuleSkeleton where
    rnf (CheckedNotionRuleSkeleton arity premises conclusion) =
        rnf arity `seq` rnf premises `seq` rnf conclusion

checkedNotionRuleSkeleton
    :: Natural
    -> [RulePremiseTree RuleTermTemplate]
    -> AtomTemplate RuleTermTemplate
    -> Either Text CheckedNotionRuleSkeleton
checkedNotionRuleSkeleton binderArity premises conclusion = do
    traverse_ validateAtom allAtoms
    traverse_ validateRuleTerm allTerms
    traverse_ (\body -> case body of
        UniversalBind{} -> validateUniversal 0 body
        _ -> Left "a supplied premise must start with a set binder") (universalPremises premises)
    unless (variables == expectedVariables)
        (Left
            "a notion rule must use exactly its dense nearest-first theorem context")
    unless (Set.fromList (concatMap termVariables (concatMap toList allAtoms)) <> positiveVariables == expectedVariables)
        (Left "a notion clause must determine every parameter from its positive premises and conclusion")
    pure (CheckedNotionRuleSkeleton binderArity premises conclusion)
  where
    allAtoms = premiseAtoms premises <> [conclusion]
    allTerms = concatMap toList allAtoms <> concatMap (foldMap (foldMap (foldMap toList))) (universalPremises premises)
    variables = Set.fromList (concatMap termVariables allTerms)
        <> Set.map (\(ViewVariableIx index) -> index) (residualVariables premises)
        <> positiveVariables
    positiveVariables = Set.map (\(ViewVariableIx index) -> index) (foldMap positive premises)
    positive = \case
        RulePremiseResidual residual -> fromMaybe Set.empty (runIdentity (positiveResidualParametersWith (pure ()) residual))
        RulePremiseAnd left right -> positive left <> positive right
        _ -> Set.empty
    expectedVariables
        | binderArity == 0 = Set.empty
        | otherwise = Set.fromList [0 .. binderArity - 1]

    validateAtom = \case
        NegativeAtomTemplate body -> validateAtom body
        GlobalAtomTemplate head' arguments ->
            case semanticGlobalKeyType
                    (globalBindingRefKey (globalNotionHeadReference head'))
                    >>= firstOrderSymbolShape of
                Just (arity, TyProp)
                    | arity == Vector.length arguments
                      && globalNotionHeadMatchesKey head'
                            (globalBindingRefKey
                                (globalNotionHeadReference head')) -> pure ()
                _ -> Left
                    "a global notion-rule atom has the wrong predicate application shape"
        StructureAtomTemplate{} -> pure ()
        ExactStructureAtomTemplate{} -> pure ()
        MembershipAtomTemplate{} -> pure ()

    validateRuleTerm = \case
        TemplateClosed value -> unless (runIdentity (canonicalClosedWith (pure ()) (closedSetValueTerm value)))
            (Left "a closed notion-rule value captures a theorem variable")
        TemplateVariable (ViewVariableIx index) ->
            unless (index < binderArity)
                (Left "a notion-rule variable is outside its binder context")
        TemplateOrderedPair left right ->
            validateRuleTerm left >> validateRuleTerm right
        TemplateProvider provider arguments -> do
            traverse_ validateRuleTerm arguments
            validateProviderApplication provider arguments

    validateProviderApplication provider arguments = case provider of
        GlobalSourceProvider reference ->
            case semanticGlobalKeyType (globalBindingRefKey reference)
                    >>= firstOrderSymbolShape of
                Just (arity, TySet)
                    | arity == Vector.length arguments -> pure ()
                _ -> Left
                    "a global notion-rule provider has the wrong set-valued application shape"
        StructureFieldSourceProvider{} ->
            unless (Vector.length arguments == 1)
                (Left
                    "a structure-field notion-rule provider must have one receiver")
        IntrinsicSourceProvider providerId ->
            case firstOrderSymbolShape
                    (coreIntrinsicType (intrinsicProviderCoreTag providerId)) of
                Just (arity, TySet)
                    | arity == Vector.length arguments -> pure ()
                _ -> Left
                    "an intrinsic notion-rule provider has the wrong set-valued application shape"
        FiniteSetLiteralSourceProvider ->
            when (Vector.null arguments)
                (Left
                    "a finite-set literal notion-rule provider has an empty spine")

    premiseAtoms = concatMap treeAtoms

    treeAtoms = \case
        RulePremiseAtom atom -> [atom]
        RulePremiseUniversal _ -> []
        RulePremiseResidual _ -> []
        RulePremiseAnd left right -> treeAtoms left <> treeAtoms right

    universalPremises = concatMap whole
      where
        whole (RulePremiseAtom _) = []
        whole (RulePremiseUniversal body) = [body]
        whole (RulePremiseResidual _) = []
        whole (RulePremiseAnd left right) = whole left <> whole right

    residualVariables = foldMap collect
      where
        collect (RulePremiseResidual residual) = residualTemplateVariables residual
        collect (RulePremiseAnd left right) = collect left <> collect right
        collect _ = Set.empty

    validateUniversal depth = \case
        UniversalBind nested -> validateUniversal (depth + 1) nested
        UniversalRequire guard nested -> validateUniversalAtoms depth guard >> validateUniversal depth nested
        UniversalReturn result -> do
            unless (depth > 0) (Left "a supplied premise must bind a set variable")
            validateUniversalAtoms depth result
    validateUniversalAtoms depth = traverse_ $ \atom -> do
        validateAtom atom
        traverse_ (universalTerm depth) atom
    universalTerm depth = \case
        TemplateClosed value -> validateRuleTerm (TemplateClosed value)
        TemplateVariable (UniversalBound index) -> unless (index < depth)
            (Left "a supplied-premise variable is outside its binder telescope")
        TemplateVariable (UniversalOuter term) -> validateRuleTerm term
        TemplateOrderedPair left right -> universalTerm depth left >> universalTerm depth right
        TemplateProvider provider arguments -> do
            validateProviderApplication provider arguments
            traverse_ (universalTerm depth) arguments

    termVariables = \case
        TemplateClosed{} -> []
        TemplateVariable (ViewVariableIx index) -> [index]
        TemplateProvider _provider arguments ->
            concatMap termVariables (toList arguments)
        TemplateOrderedPair left right ->
            termVariables left <> termVariables right

checkedNotionRuleBinderArity :: CheckedNotionRuleSkeleton -> Natural
checkedNotionRuleBinderArity
        (CheckedNotionRuleSkeleton binderArity _premises _conclusion) =
    binderArity

checkedNotionRulePremises
    :: CheckedNotionRuleSkeleton
    -> [RulePremiseTree RuleTermTemplate]
checkedNotionRulePremises
        (CheckedNotionRuleSkeleton _binderArity premises _conclusion) =
    premises

checkedNotionRuleConclusion
    :: CheckedNotionRuleSkeleton
    -> AtomTemplate RuleTermTemplate
checkedNotionRuleConclusion
        (CheckedNotionRuleSkeleton _binderArity _premises conclusion) =
    conclusion

type BackwardNotionRuleTemplate = AtomTemplate RuleTermTemplate

-- | A rule shape whose requested rich conclusion determines
-- every theorem variable.  Premise grouping is retained exactly so that one
-- ordinary kernel derivation can reconstruct the source theorem application.
data BackwardNotionRule = BackwardNotionRule
    { backwardNotionPremises :: !(RulePremiseBundles RuleTermTemplate)
    , backwardNotionConclusion :: !BackwardNotionRuleTemplate
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Checked clause meaning. Execution plans are derived at catalogue admission
-- and do not participate in the persisted declaration's identity.
newtype FiniteEvidenceRule = FiniteEvidenceRule
    { finiteEvidenceSkeleton :: CheckedNotionRuleSkeleton }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data ResultRuleTerm
    = ResultRuleTerm !RuleTermTemplate
    | ResultRuleProviderValue
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

type ResultNotionRuleTemplate = AtomTemplate ResultRuleTerm

data ResultProviderTemplate = ResultProviderTemplate
    !SourceProviderHead
    !(Vector RuleTermTemplate)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

resultProviderTemplate
    :: SourceProviderHead
    -> Vector RuleTermTemplate
    -> ResultProviderTemplate
resultProviderTemplate = ResultProviderTemplate

resultProviderTemplateHead
    :: ResultProviderTemplate
    -> SourceProviderHead
resultProviderTemplateHead (ResultProviderTemplate head' _arguments) =
    head'

resultProviderTemplateArguments
    :: ResultProviderTemplate
    -> Vector RuleTermTemplate
resultProviderTemplateArguments
        (ResultProviderTemplate _head arguments) =
    arguments

data ProviderResultRule = ProviderResultRule
    { providerResultProvider :: !ResultProviderTemplate
    , providerResultPremises :: !(ProviderResultPremises RuleTermTemplate)
    , providerResultConclusion :: !ResultNotionRuleTemplate
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | The sole premise-determined forward schema admitted by notion-2:
-- @(a,b) in f -> a in domain(f)@.  The owner-bearing provider fixes the
-- meaning of @domain@; the three indexes name the theorem's dense set-binder
-- context and are validated again against its checked proposition when the
-- declaration is materialized.
data GraphDomainRule = GraphDomainRule
    { graphDomainProvider :: !SourceProviderHead
    , graphDomainLeft :: !ViewVariableIx
    , graphDomainRight :: !ViewVariableIx
    , graphDomainGraph :: !ViewVariableIx
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | A source-independent rule payload. Family-specific checking consumes the
-- narrow payload; this sum determines registration grouping and installation.
data WholeConclusionRule = WholeConclusionRule
    { wholeConclusionArity :: !Natural
    , wholeConclusionPremises :: ![RulePremiseTree RuleTermTemplate]
    , wholeConclusionTemplate :: !ResidualTemplate
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data RegistrationBody
    = RegisterNotionView !NotionViewRule
    | RegisterNullaryProvider !NullaryProviderRule
    | RegisterProviderResult !ProviderResultRule
    | RegisterBackwardNotion !BackwardNotionRule
    | RegisterFiniteEvidence !FiniteEvidenceRule
    | RegisterGraphDomain !GraphDomainRule
    | RegisterWholeConclusion !WholeConclusionRule
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Source addresses vary across preparation and installation; they carry no
-- proof authority. Only the registration owns the conclusion's source path.
data Registration source = Registration
    { registrationSource :: !source
    , registrationPath :: !ConjunctionPath
    , registrationBody :: !RegistrationBody
    }
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

registrationBranch :: Registration SemanticFactOccurrenceFingerprint -> SemanticFactBranch
registrationBranch (Registration source path _body) = SemanticFactBranch source path

-- Canonical family order is shared by runtime expansion and owned indexes.
registrationFamily :: RegistrationBody -> Int
registrationFamily = \case
    RegisterNotionView{} -> 0
    RegisterNullaryProvider{} -> 1
    RegisterProviderResult{} -> 2
    RegisterBackwardNotion{} -> 3
    RegisterFiniteEvidence{} -> 4
    RegisterGraphDomain{} -> 5
    RegisterWholeConclusion{} -> 6

normalizeRegistrations :: [Registration source] -> [Registration source]
normalizeRegistrations = List.sortOn (registrationFamily . registrationBody)

type FormationRequirement = NotionLeaf NotionTemplate (WholeTemplate FormationTermTemplate)

newtype FormationContract = FormationContract
    (NonEmpty FormationRequirement)
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

formationContract :: NonEmpty FormationRequirement -> FormationContract
formationContract = FormationContract

formationContractRequirements
    :: FormationContract
    -> NonEmpty FormationRequirement
formationContractRequirements (FormationContract requirements) =
    requirements

-- | A persisted contract whose host spine and every referenced notion head
-- have been checked against one complete visible semantic environment.
-- Persisted bytes retain 'FormationContract'; this runtime witness is rebuilt
-- transactionally and deliberately has no independent cache identity.
newtype ResolvedFormationContract = ResolvedFormationContract
    (NonEmpty FormationRequirement)
    deriving stock (Show, Eq, Ord)

resolvedFormationContractRequirements
    :: ResolvedFormationContract
    -> NonEmpty FormationRequirement
resolvedFormationContractRequirements
        (ResolvedFormationContract requirements) =
    requirements

-- Admission failures for the source interface of a visible binding.
data FormationContractMaterializationError
    = FormationContractHostSignatureUnsupported
        !SemanticGlobalKey !(Maybe CoreType)
    | FormationContractDuplicateRequirement !FormationRequirement
    | FormationContractWholeRequirementInvalid !Text
    | FormationContractArgumentOutOfRange
        !OccurrenceArgumentIx !Natural
    | FormationContractGlobalFamilyMismatch
        !GlobalNotionHead !SemanticGlobalKey
    | FormationContractGlobalBindingMissing !GlobalBindingRef
    | FormationContractGlobalSignatureUnsupported
        !GlobalBindingRef !(Maybe CoreType)
    | FormationContractGlobalArityMismatch
        !GlobalBindingRef !Natural !Natural
    | FormationContractGlobalNotDirect
        !GlobalBindingRef !SemanticGlobalTarget
    | FormationContractProviderBindingMissing !GlobalBindingRef
    | FormationContractProviderFamilyMismatch
        !GlobalBindingRef !SemanticGlobalKey
    | FormationContractProviderSignatureUnsupported
        !GlobalBindingRef !(Maybe CoreType)
    | FormationContractProviderArityMismatch
        !GlobalBindingRef !Natural !Natural
    | FormationContractProviderContextual
        !GlobalBindingRef !SemanticGlobalTarget
    | FormationContractProviderContracted !GlobalBindingRef
    | FormationContractStructureFieldProviderMissing !FieldId
    | FormationContractStructureFieldProviderMismatch
        !FieldId !ObjectId !ObjectId
    | FormationContractStructureFieldProviderArityMismatch
        !FieldId !Natural
    | FormationContractIntrinsicProviderSignatureUnsupported
        !IntrinsicProviderId !CoreType
    | FormationContractIntrinsicProviderArityMismatch
        !IntrinsicProviderId !Natural !Natural
    | FormationContractFiniteSetLiteralProviderEmpty
    | FormationContractOrderedPairUnsupported
    | FormationContractClosedValueInvalid !Text
    | FormationContractStructureMissing !StructureId
    | FormationContractRecordShapeMissing !SemanticRecordShapeKey
    | FormationContractStructureArityMismatch
        !SemanticStructureNotionHead !Natural !Natural
    | AbbreviationExpansionInvalid !Text
    | AbbreviationExpansionLimitExceeded !Natural
    deriving stock (Show, Eq)

data ResolvedGlobalBinding = ResolvedGlobalBinding
    !GlobalBindingRef
    !SemanticGlobalBinding
    !(Maybe ResolvedFormationContract)
    !(Maybe AbbreviationExpansion)
    deriving stock (Show, Eq, Ord)

data SemanticEnvironmentMaterializationError
    = SemanticEnvironmentBindingMaterializationFailed
        !GlobalBindingRef
        !FormationContractMaterializationError
    deriving stock (Show, Eq)

-- | The first-order symbol shapes relevant to formation contracts.  The
-- distinction between predicate and set-valued hosts is deliberately a
-- materialization policy, not persisted semantic data: notion-0 admitted only
-- predicates, while later phases extend the policy to total set-valued terms
-- without changing the underlying Core classifier.
data FormationContractSymbolShape
    = FormationPredicateSymbol !Natural
    | FormationSetTermSymbol !Natural
    | FormationUnsupportedSymbol

formationContractSymbolShape :: CoreType -> FormationContractSymbolShape
formationContractSymbolShape coreType =
    case firstOrderSymbolShape coreType of
        Just (arity, TyProp) ->
            FormationPredicateSymbol (fromIntegral arity)
        Just (arity, TySet) ->
            FormationSetTermSymbol (fromIntegral arity)
        _ ->
            FormationUnsupportedSymbol

materializeResolvedGlobalBinding
    :: (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (StructureId -> Maybe StructurePredicate.PendingStructureRegistration)
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> SemanticGlobalBinding
    -> Either FormationContractMaterializationError ResolvedGlobalBinding
materializeResolvedGlobalBinding lookupBinding lookupStructure closure owner binding =
    materializeResolvedGlobalBindingWithFields
        lookupBinding lookupStructure (const Nothing) Set.empty closure owner binding

materializeResolvedGlobalBindingWithFields
    :: (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (StructureId -> Maybe StructurePredicate.PendingStructureRegistration)
    -> (FieldId -> Maybe ObjectId)
    -> Set SemanticRecordShapeKey
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> SemanticGlobalBinding
    -> Either FormationContractMaterializationError ResolvedGlobalBinding
materializeResolvedGlobalBindingWithFields lookupBinding lookupStructure lookupField shapes closure owner binding =
    fst (materializeResolvedGlobalBindingWithFieldsMeasured
        lookupBinding lookupStructure lookupField shapes closure owner binding)

materializeResolvedGlobalBindingWithFieldsMeasured
    :: (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (StructureId -> Maybe StructurePredicate.PendingStructureRegistration)
    -> (FieldId -> Maybe ObjectId)
    -> Set SemanticRecordShapeKey
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> SemanticGlobalBinding
    -> (Either FormationContractMaterializationError ResolvedGlobalBinding, Natural)
materializeResolvedGlobalBindingWithFieldsMeasured
        lookupBinding lookupStructure lookupField shapes closure owner binding = State.runState (Except.runExceptT do
    resolvedContract <- Except.except (traverse resolveContract contract)
    resolvedExpansion <- case (semanticGlobalBindingTarget binding, expansion) of
        (GlobalReference{}, Nothing) -> pure Nothing
        (_, Just persisted) -> Just <$> resolveExpansion persisted
        _ -> Except.throwE (AbbreviationExpansionInvalid "a transparent binding has no expansion payload")
    pure (ResolvedGlobalBinding reference binding resolvedContract resolvedExpansion)) 0
  where
    key = semanticGlobalBindingKey binding
    reference = globalBindingRef owner key
    contract = semanticGlobalBindingContract binding
    expansion = semanticGlobalBindingExpansion binding

    resolveExpansion persisted = do
        (arity, resultType) <- Except.except $ maybe
            (Left (AbbreviationExpansionInvalid "an abbreviation must have a set-valued parameter telescope"))
            (Right . first fromIntegral)
            (semanticGlobalKeyType key >>= firstOrderSymbolShape)
        let target = semanticGlobalBindingTarget binding
            contextual = case target of ContextualTransparentExpansion{} -> True; _ -> False
            count = arity + if contextual then 1 else 0
        content <- Except.except $ maybe
            (Left (AbbreviationExpansionInvalid "the expansion body is not visible")) Right
            (lookupCheckedObjectContent (semanticGlobalTargetObject target) closure)
        body <- Except.except $ case (target, content) of
            (TransparentExpansion{}, TransparentObjectContent _ _ term) -> Right term
            (ContextualTransparentExpansion{}, TransparentObjectContent _ _ term) -> Right term
            _ -> Left (AbbreviationExpansionInvalid "expansion metadata belongs to a transparent abbreviation")
        let (validated, remaining) = runIdentity (runExpansionWork formationMaximumExpansionWork do
                for_ (Map.elems (semanticGlobalTargetRequirements target)) \(field, projection) -> do
                    chargeExpansion 1
                    require (lookupField field == Just projection)
                        "a contextual expansion requires an unassociated field projection"
                chargeExpansion count
                opened <- open count body
                case persisted of
                    TermExpansion term -> do
                        require (resultType == TySet) "a term expansion has the wrong result type"
                        materialized <- expandTerm arity contextual [] term
                        same opened materialized
                    PropositionExpansion evidence equalities -> do
                        require (resultType == TyProp) "a proposition expansion has the wrong result type"
                        validateEvidence arity contextual 0 opened evidence
                        for_ equalities \(ExpansionEquality left right selector) -> do
                            chargeExpansion 1
                            selected <- select selector opened
                            a <- expandTerm arity contextual [] left
                            rightCore <- expandTerm arity contextual [] right
                            same selected (CEq TySet a rightCore))
        State.modify' (+ fromIntegral (formationMaximumExpansionWork - remaining))
        case validated of
            Right () -> pure persisted
            Left failure -> Except.throwE $ case expansionRejectedDebit failure of
                Just debit -> AbbreviationExpansionLimitExceeded debit
                Nothing -> AbbreviationExpansionInvalid (renderExpansionFailure failure)

    invalid = Except.throwE . ExpansionInvalid
    require valid reason = unless valid (invalid reason)
    checked result = either (invalid . Text.pack . show) pure result
    same expected actual = do
        identical <- expansionCoreWork (\work -> countedCanonicalIdentity work expected actual)
        require identical "expansion metadata disagrees with the checked transparent body"
    open 0 body = pure body
    open count body = chargeExpansion 1 >> case body of
        CLam TySet rest -> open (count - 1) rest
        _ -> invalid "the expansion has the wrong parameter telescope"
    select path body = chargeExpansion 1 >> case (path, body) of
        (ConjunctionHere, _) -> pure body
        (ConjunctionLeft rest, CAnd left _) -> select rest left
        (ConjunctionRight rest, CAnd _ right) -> select rest right
        _ -> invalid "an expansion equality is not a conjunction-eliminable body fact"

    expandTerm arity contextual locals expression = chargeExpansion 1 >> case expression of
        ExpansionFormal index
            | index < arity -> pure (CBound (depth + arity - index - 1))
            | contextual && index == arity -> pure (CBound (depth + arity))
            | otherwise -> invalid "an expansion formal is out of range"
        ExpansionLocal index -> do
            require (index < depth) "an expansion local is out of range"
            pure (CBound index)
        ExpansionOpaque term -> do
            chargeExpansion (depth + arity + if contextual then 1 else 0)
            let context = locals <> replicate (fromIntegral (arity + if contextual then 1 else 0)) TySet
            admitted <- expansionCoreWork (\work -> countedCheckScopedCanonicalCore
                (globalTypingFromClosure closure) work context term)
            require (scopedCoreType admitted == TySet) "an opaque expansion term is not set-valued"
            pure term
        ExpansionPair left right -> do
            a <- expandTerm arity contextual locals left
            rightCore <- expandTerm arity contextual locals right
            chargeExpansion 3
            pure (CApp (CApp (CIntrinsic OrderedPair) a) rightCore)
        ExpansionProvider provider arguments -> do
            checked (validateProviderShape provider (fromIntegral (Vector.length arguments)))
            case (provider, toList arguments) of
                (StructureFieldSourceProvider field projection, [ExpansionFormal receiver])
                    | contextual && receiver == arity -> do
                        matches <- for (Map.elems (semanticGlobalTargetRequirements
                            (semanticGlobalBindingTarget binding))) \required ->
                                chargeExpansion 1 >> pure (required == (field, projection))
                        require (or matches) "a contextual provider disagrees with its required field identity"
                _ -> pure ()
            actual <- traverse (expandTerm arity contextual locals) arguments
            chargeExpansion (fromIntegral (Vector.length actual) + 1)
            case provider of
                GlobalSourceProvider providerReference -> do
                    object <- terminal providerReference
                    pure (foldl' CApp (CGlobal object) (toList actual))
                StructureFieldSourceProvider _ projection ->
                    pure (foldl' CApp (CGlobal projection) (toList actual))
                IntrinsicSourceProvider identity -> maybe
                    (invalid "an intrinsic expansion provider has the wrong arity") pure
                    (intrinsicProviderApplication identity actual)
                FiniteSetLiteralSourceProvider -> maybe
                    (invalid "an expansion finite-set literal has no elements")
                    (pure . finiteSetLiteralProviderApplication) (NonEmpty.nonEmpty (toList actual))
      where
        depth = fromIntegral (length locals)

    terminal providerReference = do
        chargeExpansion 1
        required <- maybe (invalid "an expansion reference is not visible") pure (lookupBinding providerReference)
        case semanticGlobalBindingTarget required of
            GlobalReference identity -> pure identity
            _ -> invalid "an expansion retains a transparent head or provider"

    validateEvidence arity contextual depth expected expression = chargeExpansion 1 >> case expression of
        Source.SourceResidual origin -> require (isNothing origin) "an expansion payload retains a written origin"
        Source.SourceInputs origin terms -> do
            require (isNothing origin) "an expansion payload retains a written origin"
            for_ terms \(Source.SourceInput binders term) -> do
                actual <- expandTerm arity contextual (binders <> replicate (fromIntegral depth) TySet) term
                present <- Source.sourceInputOccursWith (chargeExpansion 1) binders actual expected
                require present "an expansion support operand does not occur in its source telescope"
        Source.SourceWithInputs terms body -> do
            validateEvidence arity contextual depth expected (Source.SourceInputs Nothing terms)
            validateEvidence arity contextual depth expected body
        Source.SourceAnd left right -> case expected of
            CAnd a rightCore -> validateEvidence arity contextual depth a left >> validateEvidence arity contextual depth rightCore right
            _ -> invalid "an expansion conjunction disagrees with its body"
        Source.SourceBind body -> case expected of
            CForall TySet nested -> validateEvidence arity contextual (depth + 1) nested body
            _ -> invalid "an expansion binder disagrees with its body"
        Source.SourceExists body -> case expected of
            CExists TySet nested -> validateEvidence arity contextual (depth + 1) nested body
            _ -> invalid "an expansion existential disagrees with its body"
        Source.SourceOr left right -> case expected of
            COr leftCore rightCore -> validateEvidence arity contextual depth leftCore left >> validateEvidence arity contextual depth rightCore right
            _ -> invalid "an expansion disjunction disagrees with its body"
        Source.SourceIff left right -> case expected of
            CEq TyProp leftCore rightCore -> validateEvidence arity contextual depth leftCore left >> validateEvidence arity contextual depth rightCore right
            _ -> invalid "an expansion biconditional disagrees with its body"
        Source.SourceRequire premise body -> case expected of
            CImp a rightCore -> validateEvidence arity contextual depth a premise >> validateEvidence arity contextual depth rightCore body
            _ -> invalid "an expansion guard disagrees with its body"
        Source.SourceAtom atom -> do
            actual <- traverseAtomTemplateArguments (expandTerm arity contextual (replicate (fromIntegral depth) TySet)) atom
            proposition <- expandAtom actual
            same expected proposition

    expandAtom = \case
        NegativeAtomTemplate body -> chargeExpansion 1 >> (CNot <$> expandAtom body)
        GlobalAtomTemplate head' terms -> do
            checked (validateGlobal head' (fromIntegral (Vector.length terms)))
            object <- terminal (globalNotionHeadReference head')
            arguments <- maybe (invalid "an expansion atom has malformed source arguments") pure
                (globalNotionBindingArguments (globalBindingRefKey (globalNotionHeadReference head')) terms)
            chargeExpansion (fromIntegral (Vector.length arguments) + 1)
            pure (foldl' CApp (CGlobal object) (toList arguments))
        StructureAtomTemplate head'@(SemanticStructureNotionHead identity) terms -> do
            checked (validateStructure head' (fromIntegral (Vector.length terms)))
            registration <- maybe (invalid "an expansion structure is not visible") pure (lookupStructure identity)
            chargeExpansion (fromIntegral (Vector.length terms) + 1)
            pure (foldl' CApp (CGlobal (StructurePredicate.pendingStructurePredicate registration)) (toList terms))
        MembershipAtomTemplate element set -> do
            chargeExpansion 3
            pure (CApp (CApp (CIntrinsic Member) element) set)
        ExactStructureAtomTemplate shape subject -> do
            checked (validateShape shape)
            chargeExpansion (fromIntegral (length (semanticRecordShapeSelectors shape)))
            pure (Record.recordExactShape (CGlobal <$> semanticRecordShapeSelectors shape) subject)

    resolveContract persisted = do
        hostType <- maybe
            (Left
                (FormationContractHostSignatureUnsupported
                    key Nothing))
            Right
            (semanticGlobalKeyType key)
        hostArity <-
            case formationContractSymbolShape hostType of
                FormationPredicateSymbol arity -> pure arity
                FormationSetTermSymbol arity
                    | isSupportedSetTermHost key
                        (semanticGlobalBindingTarget binding) ->
                            pure arity
                    | otherwise -> unsupportedHost hostType
                FormationUnsupportedSymbol -> unsupportedHost hostType
        let requirements = formationContractRequirements persisted
        case firstDuplicate (toList requirements) of
            Just duplicate ->
                Left (FormationContractDuplicateRequirement duplicate)
            Nothing -> pure ()
        traverse_ (validateRequirement hostArity) requirements
        pure (ResolvedFormationContract requirements)

    validateRequirement hostArity = \case
        AtomicLeaf atom -> validateAtom (validateTerm hostArity) atom
        WholeLeaf (WholeResidual residual) -> do
            admitted <- first (FormationContractWholeRequirementInvalid . Text.pack . show)
                (checkScopedCanonicalCore (globalTypingFromClosure closure)
                    (replicate (fromIntegral hostArity) TySet) (residualTemplateFormula residual))
            unless (scopedCoreType admitted == TyProp)
                (Left (FormationContractWholeRequirementInvalid "a whole requirement is not a proposition"))
        WholeLeaf (WholeUniversal body) -> universal 0 body
          where
            universal depth = \case
                UniversalBind nested -> universal (depth + 1) nested
                UniversalRequire condition nested -> traverse_ (atom depth) condition >> universal depth nested
                UniversalReturn result -> traverse_ (atom depth) result
            atom depth = validateAtom (term depth)
            term depth = \case
                TemplateVariable (UniversalBound index) -> unless (index < depth)
                    (Left (FormationContractWholeRequirementInvalid "a universal requirement escapes its telescope"))
                TemplateVariable (UniversalOuter value) -> validateTerm hostArity value
                TemplateClosed value -> validateTerm hostArity (TemplateClosed value)
                TemplateProvider provider arguments -> do
                    validateProvider provider (fromIntegral (Vector.length arguments))
                    traverse_ (term depth) arguments
                TemplateOrderedPair{} -> Left FormationContractOrderedPairUnsupported

    validateAtom :: (term -> Either FormationContractMaterializationError ())
        -> AtomTemplate term -> Either FormationContractMaterializationError ()
    validateAtom validate template = do
        traverse_ validate template
        validateHead template
      where
        validateHead = \case
            NegativeAtomTemplate body -> validateHead body
            GlobalAtomTemplate head' indexes ->
                validateGlobal head' (fromIntegral (Vector.length indexes))
            StructureAtomTemplate head' indexes ->
                validateStructure head' (fromIntegral (Vector.length indexes))
            ExactStructureAtomTemplate shape _ -> validateShape shape
            MembershipAtomTemplate{} -> pure ()

    validateIndex hostArity index@(OccurrenceArgumentIx ordinal) =
        unless
            (ordinal < hostArity)
            (Left (FormationContractArgumentOutOfRange index hostArity))

    validateGlobal head' actualArity = do
        let requiredReference = globalNotionHeadReference head'
            requiredKey = globalBindingRefKey requiredReference
        unless
            (globalNotionHeadMatchesKey head' requiredKey)
            (Left
                (FormationContractGlobalFamilyMismatch head' requiredKey))
        requiredBinding <- maybe
            (Left
                (FormationContractGlobalBindingMissing requiredReference))
            Right
            (lookupBinding requiredReference)
        requiredType <- maybe
            (Left
                (FormationContractGlobalSignatureUnsupported
                    requiredReference Nothing))
            Right
            (semanticGlobalKeyType
                (semanticGlobalBindingKey requiredBinding))
        requiredArity <-
            case formationContractSymbolShape requiredType of
                FormationPredicateSymbol arity -> pure arity
                FormationSetTermSymbol{} ->
                    unsupportedRequirement requiredReference requiredType
                FormationUnsupportedSymbol ->
                    unsupportedRequirement requiredReference requiredType
        unless
            (requiredArity == actualArity)
            (Left
                (FormationContractGlobalArityMismatch
                    requiredReference requiredArity actualArity))
        case semanticGlobalBindingTarget requiredBinding of
            GlobalReference{} -> pure ()
            target ->
                Left
                    (FormationContractGlobalNotDirect
                        requiredReference target)

    validateShape shape = unless (Set.member shape shapes)
        (Left (FormationContractRecordShapeMissing shape))

    validateStructure head'@(SemanticStructureNotionHead identity) actualArity = do
        registration <- maybe (Left (FormationContractStructureMissing identity)) Right (lookupStructure identity)
        let expectedArity = 1 + Schema.resolvedSchemaParameterCount (StructurePredicate.pendingStructureSchema registration)
        unless (expectedArity == actualArity)
            (Left (FormationContractStructureArityMismatch head' expectedArity actualArity))

    validateTerm hostArity = \case
        TemplateClosed value -> void (first FormationContractClosedValueInvalid (materializeClosedSetValue closure value))
        TemplateVariable index -> validateIndex hostArity index
        TemplateProvider provider arguments -> do
            validateProvider provider (fromIntegral (Vector.length arguments))
            traverse_ (validateTerm hostArity) arguments
        TemplateOrderedPair{} ->
            Left FormationContractOrderedPairUnsupported

    validateProvider provider actualArity = do
        validateProviderShape provider actualArity
        case provider of
            GlobalSourceProvider providerReference -> case lookupBinding providerReference of
                Just required | isJust (semanticGlobalBindingContract required) ->
                    Left (FormationContractProviderContracted providerReference)
                _ -> pure ()
            _ -> pure ()

    validateProviderShape (GlobalSourceProvider providerReference) actualArity = do
        let providerKey = globalBindingRefKey providerReference
        providerBinding <- maybe
            (Left (FormationContractProviderBindingMissing providerReference))
            Right
            (lookupBinding providerReference)
        unless
            (semanticGlobalBindingKey providerBinding == providerKey)
            (Left
                (FormationContractProviderFamilyMismatch
                    providerReference
                    (semanticGlobalBindingKey providerBinding)))
        providerType <- maybe
            (Left
                (FormationContractProviderSignatureUnsupported
                    providerReference Nothing))
            Right
            (semanticGlobalKeyType providerKey)
        providerArity <-
            case formationContractSymbolShape providerType of
                FormationSetTermSymbol arity -> pure arity
                _ ->
                    Left
                        (FormationContractProviderSignatureUnsupported
                            providerReference (Just providerType))
        unless
            (providerArity == actualArity)
            (Left
                (FormationContractProviderArityMismatch
                    providerReference providerArity actualArity))
        unless
            (isJust (sourceProviderArity providerKey))
            (Left
                (FormationContractProviderFamilyMismatch
                    providerReference providerKey))
        unless (noncontextualSourceProviderTarget (semanticGlobalBindingTarget providerBinding))
            (Left
                (FormationContractProviderContextual
                    providerReference
                    (semanticGlobalBindingTarget providerBinding)))
    validateProviderShape
            (StructureFieldSourceProvider identity projection)
            actualArity = do
        expected <- maybe
            (Left (FormationContractStructureFieldProviderMissing identity))
            Right
            (lookupField identity)
        unless
            (expected == projection)
            (Left
                (FormationContractStructureFieldProviderMismatch
                    identity expected projection))
        unless
            (actualArity == 1)
            (Left
                (FormationContractStructureFieldProviderArityMismatch
                    identity actualArity))
    validateProviderShape (IntrinsicSourceProvider provider) actualArity = do
        let providerType = coreIntrinsicType (intrinsicProviderCoreTag provider)
        providerArity <-
            case formationContractSymbolShape providerType of
                FormationSetTermSymbol arity -> pure arity
                _ ->
                    Left
                        (FormationContractIntrinsicProviderSignatureUnsupported
                            provider providerType)
        unless
            (providerArity == actualArity)
            (Left
                (FormationContractIntrinsicProviderArityMismatch
                    provider providerArity actualArity))
    validateProviderShape FiniteSetLiteralSourceProvider actualArity =
        unless
            (actualArity > 0)
            (Left FormationContractFiniteSetLiteralProviderEmpty)

    unsupportedHost hostType =
        Left
            (FormationContractHostSignatureUnsupported
                key (Just hostType))

    unsupportedRequirement requiredReference requiredType =
        Left
            (FormationContractGlobalSignatureUnsupported
                requiredReference (Just requiredType))

    isSupportedSetTermHost hostKey hostTarget =
        case (hostKey, hostTarget) of
            (SemanticFunctionPhrase{}, GlobalReference identity) ->
                objectIdFamily identity == TransparentObject
            (SemanticExpressionFunction{}, GlobalReference identity) ->
                objectIdFamily identity == TransparentObject
            _ -> False

-- | Materialize one declaration environment against the exact semantic
-- prefix preceding that declaration.  Bindings and structures owned by this
-- delta are staged together, so same-declaration references are visible;
-- entities from later declarations cannot enter through this API.
materializeSemanticEnvironmentDelta
    :: (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (StructureId -> Maybe StructurePredicate.PendingStructureRegistration)
    -> (FieldId -> Maybe ObjectId)
    -> Set SemanticRecordShapeKey
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> SemanticEnvironmentDelta
    -> Either
        SemanticEnvironmentMaterializationError
        [ResolvedGlobalBinding]
materializeSemanticEnvironmentDelta priorBinding priorStructure priorField shapes closure owner environment =
    fst (materializeSemanticEnvironmentDeltaMeasured priorBinding priorStructure priorField shapes closure owner environment)

materializeSemanticEnvironmentDeltaMeasured
    :: (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (StructureId -> Maybe StructurePredicate.PendingStructureRegistration)
    -> (FieldId -> Maybe ObjectId)
    -> Set SemanticRecordShapeKey
    -> CheckedObjectClosure
    -> DeclarationSlot
    -> SemanticEnvironmentDelta
    -> (Either SemanticEnvironmentMaterializationError [ResolvedGlobalBinding], Natural)
materializeSemanticEnvironmentDeltaMeasured priorBinding priorStructure priorField
        shapes closure owner environment =
    State.runState (Except.runExceptT (traverse materialize bindings)) 0
  where
    bindings = semanticEnvironmentBindings environment
    currentBindings = Map.fromList
        [ (globalBindingRef owner (semanticGlobalBindingKey binding), binding)
        | binding <- bindings
        ]
    materialize binding = do
        let reference = globalBindingRef owner (semanticGlobalBindingKey binding)
            (result, used) = materializeResolvedGlobalBindingWithFieldsMeasured
                (\key -> Map.lookup key currentBindings <|> priorBinding key)
                priorStructure priorField shapes closure owner binding
        State.modify' (+ used)
        Except.except (first (SemanticEnvironmentBindingMaterializationFailed reference) result)

resolvedBindingRef :: ResolvedGlobalBinding -> GlobalBindingRef
resolvedBindingRef
        (ResolvedGlobalBinding reference _binding _contract _expansion) =
    reference

resolvedBindingDeclaration
    :: ResolvedGlobalBinding
    -> SemanticGlobalBinding
resolvedBindingDeclaration
        (ResolvedGlobalBinding _reference binding _contract _expansion) =
    binding

resolvedBindingContract
    :: ResolvedGlobalBinding
    -> Maybe ResolvedFormationContract
resolvedBindingContract
        (ResolvedGlobalBinding _reference _binding contract _expansion) =
    contract

resolvedBindingExpansion
    :: ResolvedGlobalBinding
    -> Maybe AbbreviationExpansion
resolvedBindingExpansion
        (ResolvedGlobalBinding _reference _binding _contract expansion) =
    expansion

-- | Classify the exact owner-bearing source-provider identity admitted by the
-- current term-notion phase. Application checks belong to the consumers;
-- eligibility does not establish any mathematical property of the result.
resolvedBindingSourceProviderHead
    :: ResolvedGlobalBinding
    -> Maybe SourceProviderHead
resolvedBindingSourceProviderHead resolved
    | isJust (sourceProviderArity key)
    , noncontextualSourceProviderTarget target =
        Just (GlobalSourceProvider (resolvedBindingRef resolved))
    | otherwise = Nothing
  where
    declaration = resolvedBindingDeclaration resolved
    key = semanticGlobalBindingKey declaration
    target = semanticGlobalBindingTarget declaration

-- Shared by written applications and formation templates. Templates impose
-- their additional total/uncontracted restriction at materialization; guarded
-- written applications instead discharge their contracts during elaboration.
sourceProviderArity :: SemanticGlobalKey -> Maybe Natural
sourceProviderArity key = case key of
    SemanticFunctionPhrase{} -> setArity
    SemanticExpressionFunction{} -> setArity
    SemanticTypedConstant _ TySet -> Just 0
    _ -> Nothing
  where
    setArity = case formationContractSymbolShape <$> semanticGlobalKeyType key of
        Just (FormationSetTermSymbol arity) -> Just arity
        _ -> Nothing

noncontextualSourceProviderTarget :: SemanticGlobalTarget -> Bool
noncontextualSourceProviderTarget = \case
    GlobalReference{} -> True
    _ -> False

data SemanticGlobalTargetError
    = SemanticGlobalKeyHasInconsistentArity !SemanticGlobalKey
    | SemanticGlobalTargetMissing !ObjectId
    | SemanticGlobalTargetIsIntrinsic !ObjectId
    | SemanticGlobalTargetTypeMismatch !ObjectId !CoreType !CoreType
    | SemanticGlobalExpansionNotTransparent !ObjectId
    | SemanticGlobalContextualRequirementsEmpty !ObjectId
    | SemanticGlobalContextualRequirementMissing !StructSymbol !ObjectId
    | SemanticGlobalContextualRequirementIsIntrinsic !StructSymbol !ObjectId
    | SemanticGlobalContextualRequirementTypeMismatch
        !StructSymbol !ObjectId !CoreType !CoreType
    | SemanticGlobalContextualRequirementNotProvided
        !StructSymbol !ObjectId
    | SemanticGlobalContextualRequirementNotReferenced !StructSymbol !ObjectId
    | SemanticGlobalExpansionIncompatible
        !SemanticGlobalKey !SemanticGlobalTarget
    deriving stock (Show, Eq)

validateSemanticGlobalBindingTarget
    :: Set.Set (StructSymbol, ObjectId)
    -> CheckedObjectClosure
    -> SemanticGlobalBinding
    -> Either SemanticGlobalTargetError ()
validateSemanticGlobalBindingTarget operationBindings closure binding = do
    when
        (isJust (semanticGlobalBindingExpansion binding)
          && not (expansionCompatible key target))
        (Left (SemanticGlobalExpansionIncompatible key target))
    expected <-
        maybe
            (Left (SemanticGlobalKeyHasInconsistentArity key))
            Right
            (semanticGlobalKeyType key)
    content <-
        maybe
            (Left (SemanticGlobalTargetMissing identity))
            Right
            (lookupCheckedObjectContent identity closure)
    when
        (objectIdFamily identity == IntrinsicObject)
        (Left (SemanticGlobalTargetIsIntrinsic identity))
    let targetExpected =
            case target of
                ContextualTransparentExpansion{} ->
                    TyArrow TySet expected
                _ -> expected
        actual = objectContentType content
    unless
        (actual == targetExpected)
        (Left
            (SemanticGlobalTargetTypeMismatch
                identity targetExpected actual))
    case target of
        GlobalReference{} -> pure ()
        TransparentExpansion{} ->
            validateTransparent content
        ContextualTransparentExpansion _ requirements -> do
            validateTransparent content
            when
                (Map.null requirements)
                (Left (SemanticGlobalContextualRequirementsEmpty identity))
            traverse_ (validateRequirement content) (Map.toAscList requirements)
  where
    key = semanticGlobalBindingKey binding
    target = semanticGlobalBindingTarget binding
    identity = semanticGlobalTargetObject target

    expansionCompatible _candidateKey = \case
        GlobalReference{} -> False
        TransparentExpansion{} -> True
        ContextualTransparentExpansion{} -> True

    validateTransparent = \case
        TransparentObjectContent{} -> pure ()
        _ -> Left (SemanticGlobalExpansionNotTransparent identity)

    validateRequirement content (symbol, (_field, object)) = do
        operationContent <-
            maybe
                (Left
                    (SemanticGlobalContextualRequirementMissing
                        symbol object))
                Right
                (lookupCheckedObjectContent object closure)
        when
            (objectIdFamily object == IntrinsicObject)
            (Left
                (SemanticGlobalContextualRequirementIsIntrinsic
                    symbol object))
        let expectedOperation = TyArrow TySet TySet
            actualOperation = objectContentType operationContent
        unless
            (actualOperation == expectedOperation)
            (Left
                (SemanticGlobalContextualRequirementTypeMismatch
                    symbol object expectedOperation actualOperation))
        unless
            ((symbol, object) `Set.member` operationBindings)
            (Left
                (SemanticGlobalContextualRequirementNotProvided
                    symbol object))
        case content of
            TransparentObjectContent _theory _coreType body ->
                unless
                    (object `Set.member` canonicalTermGlobals body)
                    (Left
                        (SemanticGlobalContextualRequirementNotReferenced
                            symbol object))
            _ -> impossible "a contextual expansion was not transparent"

data SemanticEnvironmentDelta = SemanticEnvironmentDelta
    ![SemanticGlobalBinding]
    ![StructureInterfaceWire]
    deriving stock (Show, Eq, Ord)

instance NFData SemanticEnvironmentDelta where
    rnf (SemanticEnvironmentDelta bindings structures) =
        rnf bindings `seq` rnf structures

data SemanticEnvironmentError
    = DuplicateSemanticGlobalKey !SemanticGlobalKey
    | NonCanonicalSemanticGlobalBindingOrder
    | DuplicateSemanticStructureSlot !StructureSlot
    | NonCanonicalSemanticStructureOrder
    deriving stock (Show, Eq)

emptySemanticEnvironmentDelta :: SemanticEnvironmentDelta
emptySemanticEnvironmentDelta =
    SemanticEnvironmentDelta [] []

semanticEnvironmentDelta
    :: [SemanticGlobalBinding]
    -> Either SemanticEnvironmentError SemanticEnvironmentDelta
semanticEnvironmentDelta bindings =
    semanticEnvironmentWithStructures bindings []

semanticEnvironmentWithStructures
    :: [SemanticGlobalBinding]
    -> [StructureInterfaceWire]
    -> Either SemanticEnvironmentError SemanticEnvironmentDelta
semanticEnvironmentWithStructures bindings structures = do
    case firstDuplicate (semanticGlobalBindingKey <$> bindings) of
        Just duplicate ->
            Left (DuplicateSemanticGlobalKey duplicate)
        Nothing ->
            pure ()
    unless
        (bindings == List.sortOn semanticGlobalBindingKey bindings)
        (Left NonCanonicalSemanticGlobalBindingOrder)
    case firstDuplicate (structureWireSlot <$> structures) of
        Just duplicate ->
            Left (DuplicateSemanticStructureSlot duplicate)
        Nothing -> pure ()
    unless
        ( structures
            == List.sortOn structureWireSlot structures
        )
        (Left NonCanonicalSemanticStructureOrder)
    pure (SemanticEnvironmentDelta bindings structures)

semanticEnvironmentBindings
    :: SemanticEnvironmentDelta
    -> [SemanticGlobalBinding]
semanticEnvironmentBindings
        (SemanticEnvironmentDelta bindings _structures) =
    bindings

semanticEnvironmentStructures
    :: SemanticEnvironmentDelta
    -> [StructureInterfaceWire]
semanticEnvironmentStructures
        (SemanticEnvironmentDelta _bindings structures) =
    structures


data DeclarationInterfaceDelta = DeclarationInterfaceDelta
    !DeclarationSlot
    ![SemanticFactOccurrence]
    ![SemanticAlias]
    ![ObjectId]
    ![PropositionId]
    ![SemanticDefinitionView]
    ![Registration SemanticFactOccurrenceFingerprint]
    !SemanticEnvironmentDelta
    deriving stock (Show, Eq)

instance Ord DeclarationInterfaceDelta where
    compare (DeclarationInterfaceDelta slot facts aliases objects propositions views registrations environment)
            (DeclarationInterfaceDelta slot' facts' aliases' objects' propositions' views' registrations' environment') =
        compare (slot, facts, aliases, objects, propositions, views)
            (slot', facts', aliases', objects', propositions', views')
            <> compareRegistrations registrations registrations'
            <> compare environment environment'
      where
        -- At a family boundary, an exhausted earlier segment sorts first,
        -- just as it did when the six segments were stored separately.
        compareRegistrations [] [] = EQ
        compareRegistrations [] (_:_) = LT
        compareRegistrations (_:_) [] = GT
        compareRegistrations (left:rest) (right:rest') =
            compare (registrationFamily (registrationBody right)) (registrationFamily (registrationBody left))
                <> compare left right <> compareRegistrations rest rest'

data DeclarationInterfaceError
    = DeclarationFactOwnerMismatch !FactSlot
    | DuplicateDeclarationFactSlot !FactSlot
    | DuplicateDeclarationFactFingerprint
        !SemanticFactOccurrenceFingerprint
    | DuplicateDeclarationAlias !SemanticName
    | DuplicateDeclarationObject !ObjectId
    | DuplicateDeclarationProposition !PropositionId
    | DeclarationFactPropositionMissing !PropositionId
    | DuplicateDeclarationDefinitionView
        !ObjectId !DefinitionViewKind
    | DeclarationDefinitionViewFactMissing
        !SemanticFactOccurrenceFingerprint
    | DuplicateDeclarationRegistration !(Registration SemanticFactOccurrenceFingerprint)
    | DeclarationRegistrationFactMissing !(Registration SemanticFactOccurrenceFingerprint)
    | DeclarationDatatypeFactMissing !SemanticFactOccurrenceFingerprint
    | DeclarationRecursiveFactMissing !SemanticFactOccurrenceFingerprint
    deriving stock (Show, Eq)

declarationInterfaceDelta
    :: DeclarationSlot
    -> [SemanticFactOccurrence]
    -> [SemanticAlias]
    -> [ObjectId]
    -> [PropositionId]
    -> [SemanticDefinitionView]
    -> [Registration SemanticFactOccurrenceFingerprint]
    -> SemanticEnvironmentDelta
    -> Either DeclarationInterfaceError DeclarationInterfaceDelta
declarationInterfaceDelta slot facts aliases objects propositions views supplied environment = do
    traverse_ validateFact facts
    rejectDuplicate
        DuplicateDeclarationFactSlot
        (semanticFactSlot <$> facts)
    rejectDuplicate
        DuplicateDeclarationFactFingerprint
        (semanticFactFingerprint <$> facts)
    rejectDuplicate
        DuplicateDeclarationAlias
        (semanticAliasName <$> aliases)
    rejectDuplicate DuplicateDeclarationObject objects
    rejectDuplicate DuplicateDeclarationProposition propositions
    rejectDuplicate
        (uncurry DuplicateDeclarationDefinitionView)
        [ ( semanticDefinitionViewObject view
          , semanticDefinitionViewKind view
          )
        | view <- views
        ]
    traverse_ validateView views
    for_ (semanticEnvironmentBindings environment) \binding ->
        for_ (semanticGlobalBindingConstruction binding) \descriptor ->
            for_ descriptor \fingerprint -> unless (fingerprint `Set.member` factSet)
                (Left (case descriptor of
                    DatatypeConstruction{} -> DeclarationDatatypeFactMissing fingerprint
                    RecursiveConstruction{} -> DeclarationRecursiveFactMissing fingerprint))
    traverse_ validateRegistrations
        (List.groupBy (\left right -> registrationFamily (registrationBody left)
            == registrationFamily (registrationBody right)) registrations)
    pure (DeclarationInterfaceDelta slot facts aliases objects propositions views registrations environment)
  where
    registrations = normalizeRegistrations supplied
    owner = declarationSlotModule slot
    propositionSet = Set.fromList propositions
    factSet = Set.fromList (semanticFactFingerprint <$> facts)

    validateFact occurrence = do
        unless
            (factSlotModule (semanticFactSlot occurrence) == owner)
            (Left
                (DeclarationFactOwnerMismatch
                    (semanticFactSlot occurrence)))
        let proposition =
                semanticFactProposition occurrence
        unless
            (proposition `Set.member` propositionSet)
            (Left (DeclarationFactPropositionMissing proposition))

    validateView view = do
        let target = semanticDefinitionViewTarget view
        unless (target `Set.member` factSet)
            (Left (DeclarationDefinitionViewFactMissing target))

    validateRegistrations family = do
        rejectDuplicate DuplicateDeclarationRegistration family
        for_ family \registration ->
            unless (registrationSource registration `Set.member` factSet)
                (Left (DeclarationRegistrationFactMissing registration))

declarationDeltaSlot :: DeclarationInterfaceDelta -> DeclarationSlot
declarationDeltaSlot (DeclarationInterfaceDelta value _ _ _ _ _ _ _) = value

declarationDeltaFacts :: DeclarationInterfaceDelta -> [SemanticFactOccurrence]
declarationDeltaFacts (DeclarationInterfaceDelta _ value _ _ _ _ _ _) = value

declarationDeltaAliases :: DeclarationInterfaceDelta -> [SemanticAlias]
declarationDeltaAliases (DeclarationInterfaceDelta _ _ value _ _ _ _ _) = value

declarationDeltaObjects :: DeclarationInterfaceDelta -> [ObjectId]
declarationDeltaObjects (DeclarationInterfaceDelta _ _ _ value _ _ _ _) = value

declarationDeltaPropositions :: DeclarationInterfaceDelta -> [PropositionId]
declarationDeltaPropositions (DeclarationInterfaceDelta _ _ _ _ value _ _ _) = value

declarationDeltaDefinitionViews :: DeclarationInterfaceDelta -> [SemanticDefinitionView]
declarationDeltaDefinitionViews (DeclarationInterfaceDelta _ _ _ _ _ value _ _) = value

declarationDeltaRegistrations :: DeclarationInterfaceDelta -> [Registration SemanticFactOccurrenceFingerprint]
declarationDeltaRegistrations (DeclarationInterfaceDelta _ _ _ _ _ _ value _) = value

declarationDeltaEnvironment :: DeclarationInterfaceDelta -> SemanticEnvironmentDelta
declarationDeltaEnvironment (DeclarationInterfaceDelta _ _ _ _ _ _ _ value) = value



newtype SemanticInterfaceId =
    SemanticInterfaceId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

semanticInterfaceIdDigest
    :: SemanticInterfaceId
    -> CacheDigest
semanticInterfaceIdDigest (SemanticInterfaceId digest) =
    digest

data SemanticInterface = SemanticInterface
    !ModuleName
    ![SemanticInterfaceId]
    ![DeclarationInterfaceDelta]
    !SemanticInterfaceId
    deriving stock (Show, Eq, Ord)

data SemanticInterfaceError
    = DuplicateDirectSemanticInterface !SemanticInterfaceId
    | SemanticDeclarationOwnerMismatch !DeclarationSlot
    | NonIncreasingDeclarationSlots
    | NonIncreasingFactSlots
    | DuplicateSemanticDefinitionView !ObjectId !DefinitionViewKind
    | SemanticInterfaceIdMismatch
        !SemanticInterfaceId
        !SemanticInterfaceId
    deriving stock (Show, Eq)

renderSemanticInterfaceError :: SemanticInterfaceError -> Text
renderSemanticInterfaceError = \case
    DuplicateDirectSemanticInterface interface ->
        "direct semantic interface occurs more than once: "
            <> Text.pack (show interface)
    SemanticDeclarationOwnerMismatch slot ->
        "declaration belongs to a different module: "
            <> Text.pack (show slot)
    NonIncreasingDeclarationSlots ->
        "declaration slots are not in increasing order"
    NonIncreasingFactSlots ->
        "fact slots are not in increasing order"
    DuplicateSemanticDefinitionView object kind ->
        "canonical definition view occurs more than once: "
            <> Text.pack (show (object, kind))
    SemanticInterfaceIdMismatch expected actual ->
        "semantic interface identity mismatch: expected "
            <> Text.pack (show expected)
            <> ", found " <> Text.pack (show actual)

semanticInterface
    :: ModuleName
    -> [SemanticInterfaceId]
    -> [DeclarationInterfaceDelta]
    -> Either SemanticInterfaceError SemanticInterface
semanticInterface owner direct declarations = do
    validateSemanticInterfaceStructure owner direct declarations
    let identity =
            computeSemanticInterfaceId owner direct declarations
    pure (SemanticInterface owner direct declarations identity)

validateSemanticInterface
    :: ModuleName
    -> [SemanticInterfaceId]
    -> [DeclarationInterfaceDelta]
    -> SemanticInterfaceId
    -> Either SemanticInterfaceError SemanticInterface
validateSemanticInterface owner direct declarations asserted = do
    validateSemanticInterfaceStructure owner direct declarations
    let computed =
            computeSemanticInterfaceId
                owner direct declarations
    unless
        (asserted == computed)
        (Left
            (SemanticInterfaceIdMismatch asserted computed))
    pure
        (SemanticInterface
            owner direct declarations asserted)

validateSemanticInterfaceStructure
    :: ModuleName
    -> [SemanticInterfaceId]
    -> [DeclarationInterfaceDelta]
    -> Either SemanticInterfaceError ()
validateSemanticInterfaceStructure owner direct declarations = do
    rejectDuplicate
        DuplicateDirectSemanticInterface
        direct
    traverse_
        (\delta ->
            unless
                (declarationSlotModule
                    (declarationDeltaSlot delta)
                    == owner)
                (Left
                    (SemanticDeclarationOwnerMismatch
                        (declarationDeltaSlot delta))))
        declarations
    unless
        (strictlyIncreasing
            ( localDeclarationOrdinalValue
                . declarationSlotOrdinal
                . declarationDeltaSlot
                <$> declarations))
        (Left NonIncreasingDeclarationSlots)
    unless
        (strictlyIncreasing
            ( localFactOrdinalValue
                . factSlotOrdinal
                . semanticFactSlot
                <$> concatMap
                    declarationDeltaFacts
                    declarations))
        (Left NonIncreasingFactSlots)
    rejectDuplicate
        (uncurry DuplicateSemanticDefinitionView)
        [ ( semanticDefinitionViewObject view
          , semanticDefinitionViewKind view
          )
        | delta <- declarations
        , view <- declarationDeltaDefinitionViews delta
        ]

semanticInterfaceOwner :: SemanticInterface -> ModuleName
semanticInterfaceOwner
        (SemanticInterface owner _ _ _) =
    owner

semanticInterfaceDirectInputs
    :: SemanticInterface
    -> [SemanticInterfaceId]
semanticInterfaceDirectInputs
        (SemanticInterface _ direct _ _) =
    direct

semanticInterfaceDeclarations
    :: SemanticInterface
    -> [DeclarationInterfaceDelta]
semanticInterfaceDeclarations
        (SemanticInterface _ _ declarations _) =
    declarations

semanticInterfaceAssertedId
    :: SemanticInterface
    -> SemanticInterfaceId
semanticInterfaceAssertedId
        (SemanticInterface _ _ _ asserted) =
    asserted

computeSemanticInterfaceId
    :: ModuleName
    -> [SemanticInterfaceId]
    -> [DeclarationInterfaceDelta]
    -> SemanticInterfaceId
computeSemanticInterfaceId owner direct declarations =
    SemanticInterfaceId
        (hashCacheFields
            "felix-semantic-interface-v2"
            [ encodeCache (putModuleNameCache owner)
            , encodeCache
                (putCacheList
                    putSemanticInterfaceIdCache
                    direct)
            , encodeCache
                (putCacheList
                    putDeclarationInterfaceDeltaCache
                    declarations)
            ])


newtype PrefixContextId =
    PrefixContextId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

data PrefixContextError
    = DuplicateInitialPrefixSemanticInput !SemanticInterfaceId
    deriving stock (Show, Eq)

initialPrefixContextId
    :: TheoryId
    -> ModuleName
    -> [SemanticInterfaceId]
    -> Either PrefixContextError PrefixContextId
initialPrefixContextId theory owner direct = do
    rejectDuplicate
        DuplicateInitialPrefixSemanticInput
        direct
    pure
        (PrefixContextId
            (hashCacheFields
                "felix-prefix-initial-v1"
                [ encodeCache (putTheoryIdCache theory)
                , encodeCache (putModuleNameCache owner)
                , encodeCache
                    (putCacheList
                        putSemanticInterfaceIdCache
                        direct)
                ]))

nextPrefixContextId
    :: PrefixContextId
    -> DeclarationInterfaceDelta
    -> PrefixContextId
nextPrefixContextId previous delta =
    PrefixContextId
        (hashCacheFields
            "felix-prefix-step-v1"
            [ encodeCache (putPrefixContextIdCache previous)
            , encodeCache
                (putDeclarationInterfaceDeltaCache delta)
            ])

prefixContextIdDigest :: PrefixContextId -> CacheDigest
prefixContextIdDigest (PrefixContextId digest) =
    digest


newtype ProofSyntaxId =
    ProofSyntaxId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

proofSyntaxId :: ByteString -> ProofSyntaxId
proofSyntaxId bytes =
    ProofSyntaxId
        (hashCacheFields "felix-proof-syntax-v1" [bytes])

proofSyntaxIdDigest :: ProofSyntaxId -> CacheDigest
proofSyntaxIdDigest (ProofSyntaxId digest) =
    digest

newtype DeclarationSyntaxId =
    DeclarationSyntaxId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

declarationSyntaxId :: ByteString -> DeclarationSyntaxId
declarationSyntaxId bytes =
    DeclarationSyntaxId
        (hashCacheFields "felix-declaration-syntax-v1" [bytes])

newtype ProofValidationKey =
    ProofValidationKey CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

proofValidationKey
    :: TheoremId
    -> ProofSyntaxId
    -> PrefixContextId
    -> ProofValidationKey
proofValidationKey theorem (ProofSyntaxId syntax) prefix =
    ProofValidationKey
        (hashCacheFields
            "felix-proof-validation"
            [ mathematicalDigestBytes
                (theoremIdDigest theorem)
            , cacheDigestBytes syntax
            , encodeCache (putPrefixContextIdCache prefix)
            ])

proofValidationKeyDigest
    :: ProofValidationKey
    -> CacheDigest
proofValidationKeyDigest (ProofValidationKey digest) =
    digest

data ProofValidationRecord = ProofValidationRecord
    !ProofValidationKey
    !ValidationCertificate
    deriving stock (Show, Eq, Ord, Generic)

proofValidationRecord
    :: ProofValidationKey
    -> ValidationCertificate
    -> ProofValidationRecord
proofValidationRecord =
    ProofValidationRecord

proofValidationRecordKey
    :: ProofValidationRecord
    -> ProofValidationKey
proofValidationRecordKey
        (ProofValidationRecord key _) =
    key

proofValidationRecordCertificate
    :: ProofValidationRecord
    -> ValidationCertificate
proofValidationRecordCertificate
        (ProofValidationRecord _ certificate) =
    certificate

newtype DeclarationValidationKey =
    DeclarationValidationKey CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

declarationValidationKey
    :: DeclarationSyntaxId
    -> PrefixContextId
    -> [ObjectId]
    -> [TheoremId]
    -> DeclarationValidationKey
declarationValidationKey
        (DeclarationSyntaxId syntax)
        prefix objects theorems =
    DeclarationValidationKey
        (hashCacheFields
            "felix-declaration-validation"
            [ cacheDigestBytes syntax
            , encodeCache (putPrefixContextIdCache prefix)
            , encodeCache (putCacheList putObjectIdCache objects)
            , encodeCache
                (putCacheList
                    (putMathematicalDigestCache . theoremIdDigest)
                    theorems)
            ])

declarationValidationKeyDigest
    :: DeclarationValidationKey
    -> CacheDigest
declarationValidationKeyDigest
        (DeclarationValidationKey digest) =
    digest

data DeclarationValidationRecord = DeclarationValidationRecord
    !DeclarationValidationKey
    ![ValidationCertificate]
    deriving stock (Show, Eq, Ord, Generic)

declarationValidationRecord
    :: DeclarationValidationKey
    -> [ValidationCertificate]
    -> DeclarationValidationRecord
declarationValidationRecord =
    DeclarationValidationRecord

declarationValidationRecordKey
    :: DeclarationValidationRecord
    -> DeclarationValidationKey
declarationValidationRecordKey
        (DeclarationValidationRecord key _) =
    key

declarationValidationRecordCertificates
    :: DeclarationValidationRecord
    -> [ValidationCertificate]
declarationValidationRecordCertificates
        (DeclarationValidationRecord _ certificates) =
    certificates


data ModuleArtefactKey = ModuleArtefactKey
    !ModuleName
    !ParsedModuleId
    ![SemanticInterfaceId]
    !TheoryId
    deriving stock (Show, Eq, Ord)

data ModuleArtefactKeyError
    = DuplicateModuleArtefactSemanticInput
        !SemanticInterfaceId
    deriving stock (Show, Eq)

moduleArtefactKey
    :: ModuleName
    -> ParsedModuleId
    -> [SemanticInterfaceId]
    -> TheoryId
    -> Either ModuleArtefactKeyError ModuleArtefactKey
moduleArtefactKey owner parsed direct theory = do
    rejectDuplicate
        DuplicateModuleArtefactSemanticInput
        direct
    pure (ModuleArtefactKey owner parsed direct theory)

moduleArtefactKeyOwner :: ModuleArtefactKey -> ModuleName
moduleArtefactKeyOwner (ModuleArtefactKey owner _parsed _direct _theory) =
    owner

moduleArtefactKeyDirectSemanticInputs
    :: ModuleArtefactKey
    -> [SemanticInterfaceId]
moduleArtefactKeyDirectSemanticInputs
        (ModuleArtefactKey _owner _parsed direct _theory) =
    direct

moduleArtefactKeyTheory :: ModuleArtefactKey -> TheoryId
moduleArtefactKeyTheory
        (ModuleArtefactKey _owner _parsed _direct theory) =
    theory

newtype ModuleArtefactId =
    ModuleArtefactId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

moduleArtefactId :: ModuleArtefactKey -> ModuleArtefactId
moduleArtefactId key =
    ModuleArtefactId
        (hashCacheFields
            "felix-module-artefact-v4"
            [encodeCache (putModuleArtefactKeyCache key)])

moduleArtefactIdDigest :: ModuleArtefactId -> CacheDigest
moduleArtefactIdDigest (ModuleArtefactId digest) =
    digest

data ModuleArtefactResult = ModuleArtefactResult
    !ModuleArtefactId
    !SyntaxInterfaceId
    !SemanticInterfaceId
    ![ValidationCertificate]
    deriving stock (Show, Eq, Ord, Generic)

moduleArtefactResult
    :: ModuleArtefactKey
    -> SyntaxInterfaceId
    -> SemanticInterfaceId
    -> [ValidationCertificate]
    -> ModuleArtefactResult
moduleArtefactResult key =
    ModuleArtefactResult (moduleArtefactId key)

moduleArtefactResultId
    :: ModuleArtefactResult
    -> ModuleArtefactId
moduleArtefactResultId
        (ModuleArtefactResult identity _ _ _) =
    identity

moduleArtefactResultSyntax
    :: ModuleArtefactResult
    -> SyntaxInterfaceId
moduleArtefactResultSyntax
        (ModuleArtefactResult _ syntax _ _) =
    syntax

moduleArtefactResultSemantic
    :: ModuleArtefactResult
    -> SemanticInterfaceId
moduleArtefactResultSemantic
        (ModuleArtefactResult _ _ semantic _) =
    semantic

moduleArtefactResultCertificates
    :: ModuleArtefactResult
    -> [ValidationCertificate]
moduleArtefactResultCertificates
        (ModuleArtefactResult _ _ _ certificates) =
    certificates


putSemanticFactOccurrenceFingerprintCache
    :: SemanticFactOccurrenceFingerprint
    -> CachePut
putSemanticFactOccurrenceFingerprintCache
        (SemanticFactOccurrenceFingerprint digest) =
    putCacheDigest digest

getSemanticFactOccurrenceFingerprintCache
    :: CacheGet SemanticFactOccurrenceFingerprint
getSemanticFactOccurrenceFingerprintCache =
    SemanticFactOccurrenceFingerprint <$> getCacheDigest

putSemanticFactOccurrenceCache
    :: SemanticFactOccurrence
    -> CachePut
putSemanticFactOccurrenceCache
        (SemanticFactOccurrence slot authority purpose eligibility composition) = do
    putFactSlotCache slot
    putFactAuthorityCache authority
    putFactPurposeCache purpose
    putEligibility eligibility
    putCacheMaybe putSemanticRelationCompositionCache composition

getSemanticFactOccurrenceCache
    :: CacheGet SemanticFactOccurrence
getSemanticFactOccurrenceCache =
    SemanticFactOccurrence
        <$> getFactSlotCache
        <*> getFactAuthorityCache
        <*> getFactPurposeCache
        <*> getEligibility
        <*> getCacheMaybe getSemanticRelationCompositionCache

putSemanticEnvironmentDeltaCache
    :: SemanticEnvironmentDelta
    -> CachePut
putSemanticEnvironmentDeltaCache
        (SemanticEnvironmentDelta bindings structures) = do
    putCacheList putSemanticGlobalBindingCache bindings
    putCacheList putStructureInterfaceWireCache structures

getSemanticEnvironmentDeltaCache
    :: CacheGet SemanticEnvironmentDelta
getSemanticEnvironmentDeltaCache = do
    bindings <- getCacheList getSemanticGlobalBindingCache
    structures <- getCacheList getStructureInterfaceWireCache
    either
        (fail . ("invalid semantic environment delta: " <>) . show)
        pure
        (semanticEnvironmentWithStructures bindings structures)

putSemanticGlobalKeyCache :: SemanticGlobalKey -> CachePut
putSemanticGlobalKeyCache = \case
    SemanticLeftAdjective reading pat -> do
        putCacheTag 0x00
        putAdjectiveReadingKindCache reading
        putPatternCache pat
    SemanticRightAdjective reading pat -> do
        putCacheTag 0x01
        putAdjectiveReadingKindCache reading
        putPatternCache pat
    SemanticFunctionPhrase singular plural -> do
        putCacheTag 0x02
        putPatternCache singular
        putPatternCache plural
    SemanticNoun singular plural -> do
        putCacheTag 0x03
        putPatternCache singular
        putPatternCache plural
    SemanticVerb surfaces -> do
        putCacheTag 0x04
        putSemanticVerbSurfacesCache surfaces
    SemanticRelation token arity -> do
        putCacheTag 0x05
        putTokenCache token
        putCacheNatural (parameterArityValue arity)
    SemanticExpressionFunction pat -> do
        putCacheTag 0x06
        putPatternCache pat
    SemanticTypedConstant token coreType -> do
        putCacheTag 0x08
        putTokenCache token
        putCoreTypeCache coreType
    SemanticPrefixPredicate command arity -> do
        putCacheTag 0x07
        putCacheText command
        putCacheNatural arity

getSemanticGlobalKeyCache :: CacheGet SemanticGlobalKey
getSemanticGlobalKeyCache =
    getCacheTag >>= \case
        0x00 ->
            SemanticLeftAdjective
                <$> getAdjectiveReadingKindCache
                <*> getPatternCache
        0x01 ->
            SemanticRightAdjective
                <$> getAdjectiveReadingKindCache
                <*> getPatternCache
        0x02 ->
            SemanticFunctionPhrase
                <$> getPatternCache
                <*> getPatternCache
        0x03 ->
            SemanticNoun
                <$> getPatternCache
                <*> getPatternCache
        0x04 ->
            SemanticVerb
                <$> getSemanticVerbSurfacesCache
        0x05 ->
            SemanticRelation
                <$> getTokenCache
                <*> (ParameterArity <$> getCacheNatural)
        0x06 -> SemanticExpressionFunction <$> getPatternCache
        0x08 ->
            SemanticTypedConstant
                <$> getTokenCache
                <*> getCoreTypeCache
        0x07 ->
            SemanticPrefixPredicate
                <$> getCacheText
                <*> getCacheNatural
        tag ->
            fail ("unknown semantic global key tag " <> show tag)

putSemanticVerbSurfacesCache :: VerbSurfaces -> CachePut
putSemanticVerbSurfacesCache surfaces = do
    putPatternCache
        (patternFromHoley (verbSurfaceSingular surfaces))
    putPatternCache
        (patternFromHoley (verbSurfaceBase surfaces))

getSemanticVerbSurfacesCache :: CacheGet VerbSurfaces
getSemanticVerbSurfacesCache = do
    singular <- patternToHoley <$> getPatternCache
    base <- patternToHoley <$> getPatternCache
    either (fail . show) pure (checkVerbSurfaces singular base)

putAdjectiveReadingKindCache :: AdjectiveReadingKind -> CachePut
putAdjectiveReadingKindCache = \case
    OrdinaryAdjectiveReading -> putCacheTag 0x00
    StructureAdjectiveReading -> putCacheTag 0x01

getAdjectiveReadingKindCache :: CacheGet AdjectiveReadingKind
getAdjectiveReadingKindCache =
    getCacheTag >>= \case
        0x00 -> pure OrdinaryAdjectiveReading
        0x01 -> pure StructureAdjectiveReading
        tag -> fail ("unknown adjective reading tag " <> show tag)

putSemanticRelationCompositionCache :: SemanticRelationComposition -> CachePut
putSemanticRelationCompositionCache (SemanticRelationComposition (x,y,z) conditions left right result) = do
    putCacheNatural x
    putCacheNatural y
    putCacheNatural z
    putCacheList putAbbreviationExpansionCache (toList conditions)
    putSemanticRelationSourceCache left
    putSemanticRelationSourceCache right
    putSemanticRelationSourceCache result

getSemanticRelationCompositionCache :: CacheGet SemanticRelationComposition
getSemanticRelationCompositionCache = SemanticRelationComposition
    <$> ((,,) <$> getCacheNatural <*> getCacheNatural <*> getCacheNatural)
    <*> (Vector.fromList <$> getCacheList getAbbreviationExpansionCache)
    <*> getSemanticRelationSourceCache
    <*> getSemanticRelationSourceCache
    <*> getSemanticRelationSourceCache

putSemanticRelationSourceCache :: SemanticRelationSource -> CachePut
putSemanticRelationSourceCache (SemanticRelationSource body captures) = do
    putAbbreviationExpansionCache body
    putCacheList (runIdentity . putExpansionTermCacheWith (pure ())) (toList captures)

getSemanticRelationSourceCache :: CacheGet SemanticRelationSource
getSemanticRelationSourceCache = SemanticRelationSource
    <$> getAbbreviationExpansionCache
    <*> (Vector.fromList <$> getCacheList getExpansionTermCache)

putSemanticGlobalBindingCache :: SemanticGlobalBinding -> CachePut
putSemanticGlobalBindingCache
        (SemanticGlobalBinding key label target contract expansion datatype) = do
    putSemanticGlobalKeyCache key
    putCacheText (semanticBindingLabelText label)
    case target of
        GlobalReference identity -> do
            putCacheTag 0x00
            putObjectIdCache identity
        TransparentExpansion identity -> do
            putCacheTag 0x01
            putObjectIdCache identity
        ContextualTransparentExpansion identity requirements -> do
            putCacheTag 0x02
            putObjectIdCache identity
            putCanonicalCacheMap
                (\(StructSymbol symbol) -> putCacheText symbol)
                (\(field, projection) -> putFieldIdCache field >> putObjectIdCache projection)
                requirements
    putCacheMaybe putFormationContractCache contract
    putCacheMaybe
        putAbbreviationExpansionCache
        expansion
    putCacheMaybe putBindingConstructionCache datatype

getSemanticGlobalBindingCache :: CacheGet SemanticGlobalBinding
getSemanticGlobalBindingCache =
    SemanticGlobalBinding
        <$> getSemanticGlobalKeyCache
        <*> (semanticBindingLabel <$> getCacheText)
        <*> (getCacheTag >>= \case
                0x00 -> GlobalReference <$> getObjectIdCache
                0x01 -> TransparentExpansion <$> getObjectIdCache
                0x02 ->
                    ContextualTransparentExpansion
                        <$> getObjectIdCache
                        <*> getCanonicalCacheMap
                            (StructSymbol <$> getCacheText)
                            ((,) <$> getFieldIdCache <*> getObjectIdCache)
                tag ->
                    fail
                        ("unknown semantic global target tag "
                            <> show tag))
        <*> getCacheMaybe getFormationContractCache
        <*> getCacheMaybe
            getAbbreviationExpansionCache
        <*> getCacheMaybe getBindingConstructionCache

putBindingConstructionCache :: BindingConstruction SemanticFactOccurrenceFingerprint -> CachePut
putBindingConstructionCache = \case
    DatatypeConstruction descriptor -> putCacheTag 0 >>
        putDatatypeDescriptorCache putSemanticFactOccurrenceFingerprintCache descriptor
    RecursiveConstruction descriptor -> do
        putCacheTag 1
        putGlobalBindingRefCache (recursiveDefinitionDatatype descriptor)
        putCacheList putCacheNatural (recursiveDefinitionArguments descriptor)
        putCacheList putResidualTemplateCache (recursiveDefinitionHeaders descriptor)
        putCacheList putAbbreviationExpansionCache (toList (recursiveDefinitionBranches descriptor))
        putCacheList (\(key,fact) -> putSemanticGlobalKeyCache key >> putSemanticFactOccurrenceFingerprintCache fact)
            (toList (recursiveDefinitionEquations descriptor))

getBindingConstructionCache :: CacheGet (BindingConstruction SemanticFactOccurrenceFingerprint)
getBindingConstructionCache = getCacheTag >>= \case
    0 -> DatatypeConstruction <$> getDatatypeDescriptorCache
    1 -> do
        datatype <- getGlobalBindingRefCache
        arguments <- getCacheList getCacheNatural
        headers <- getCacheList getResidualTemplateCache
        branches <- getCacheList getAbbreviationExpansionCache >>= maybe
            (fail "a recursive definition has no source branches") pure . NonEmpty.nonEmpty
        equations <- getCacheList ((,) <$> getSemanticGlobalKeyCache <*> getSemanticFactOccurrenceFingerprintCache)
        case NonEmpty.nonEmpty equations of
            Nothing -> fail "a recursive definition has no constructor equations"
            Just nonempty -> pure (RecursiveConstruction (RecursiveDefinitionDescriptor datatype arguments headers branches nonempty))
    tag -> fail ("unknown binding construction tag " <> show tag)

putDatatypeDescriptorCache :: (fact -> CachePut) -> DatatypeDescriptor fact -> CachePut
putDatatypeDescriptorCache putFact descriptor = do
    putCacheList putCase (toList (datatypeDescriptorCases descriptor))
    putFact (datatypeDescriptorCasesFact descriptor)
    putFact (datatypeDescriptorInductionFact descriptor)
    putFact (datatypeDescriptorPredicateInductionFact descriptor)
  where
    putCase clause = do
        putCacheText (datatypeCaseName clause)
        putSemanticGlobalKeyCache (datatypeCaseConstructor clause)
        putCacheList (\case
            DatatypeRecursivePremise -> putCacheTag 0
            DatatypeFixedPremise domain -> putCacheTag 1 >> putCanonicalTermCache putObjectIdCache domain)
            (datatypeCasePremises clause)
        putCacheList putCacheNatural (datatypeCaseFields clause)
        putFact (datatypeCaseIntroductionFact clause)
        putCacheMaybe putFact (datatypeCaseInjectivityFact clause)
        putCacheList (\(constructor, fact) -> putSemanticGlobalKeyCache constructor >> putFact fact)
            (datatypeCaseDistinctnessFacts clause)

getDatatypeDescriptorCache :: CacheGet (DatatypeDescriptor SemanticFactOccurrenceFingerprint)
getDatatypeDescriptorCache = do
    cases <- getCacheList (DatatypeCase <$> getCacheText <*> getSemanticGlobalKeyCache
        <*> getCacheList (getCacheTag >>= \case
            0 -> pure DatatypeRecursivePremise
            1 -> DatatypeFixedPremise <$> getCanonicalTermCache getObjectIdCache
            tag -> fail ("unknown datatype premise tag " <> show tag))
        <*> getCacheList getCacheNatural
        <*> getSemanticFactOccurrenceFingerprintCache
        <*> getCacheMaybe getSemanticFactOccurrenceFingerprintCache
        <*> getCacheList ((,) <$> getSemanticGlobalKeyCache <*> getSemanticFactOccurrenceFingerprintCache))
    nonempty <- maybe (fail "a datatype descriptor needs at least one case") pure (NonEmpty.nonEmpty cases)
    DatatypeDescriptor nonempty <$> getSemanticFactOccurrenceFingerprintCache
        <*> getSemanticFactOccurrenceFingerprintCache <*> getSemanticFactOccurrenceFingerprintCache

putAbbreviationExpansionCache :: AbbreviationExpansion -> CachePut
putAbbreviationExpansionCache = runIdentity . putAbbreviationExpansionCacheWith (pure ())

putAbbreviationExpansionCacheWith :: Monad m => m () -> AbbreviationExpansion -> m CachePut
putAbbreviationExpansionCacheWith visit expansion = visit >> case expansion of
    TermExpansion term -> (putCacheTag 0 >>) <$> putExpansionTermCacheWith visit term
    PropositionExpansion evidence equalities -> do
        body <- putEvidence evidence
        encoded <- for equalities \(ExpansionEquality left right path) -> do
            visit
            a <- putExpansionTermCacheWith visit left
            encodedRight <- putExpansionTermCacheWith visit right
            selector <- putPath path
            pure (a >> encodedRight >> selector)
        pure (putCacheTag 1 >> body >> putCacheList id encoded)
  where
    putEvidence value = visit >> case value of
        Source.SourceResidual _ -> pure (putCacheTag 0)
        Source.SourceInputs _ terms -> do
            encoded <- for terms \(Source.SourceInput binders term) -> do
                traverse_ (const visit) binders
                value <- putExpansionTermCacheWith visit term
                pure (putCacheList putCoreTypeCache binders >> value)
            pure (putCacheTag 5 >> putCacheList id encoded)
        Source.SourceWithInputs terms body -> do
            encoded <- for terms \(Source.SourceInput binders term) -> do
                traverse_ (const visit) binders
                value <- putExpansionTermCacheWith visit term
                pure (putCacheList putCoreTypeCache binders >> value)
            nested <- putEvidence body
            pure (putCacheTag 6 >> putCacheList id encoded >> nested)
        Source.SourceAtom atom -> do
            encoded <- traverseAtomTemplateArguments (putExpansionTermCacheWith visit) atom
            pure (putCacheTag 1 >> putAtomTemplateWith id encoded)
        Source.SourceAnd left right -> binary 2 left right
        Source.SourceBind body -> (putCacheTag 3 >>) <$> putEvidence body
        Source.SourceRequire premise body -> binary 4 premise body
        Source.SourceOr left right -> binary 7 left right
        Source.SourceIff left right -> binary 8 left right
        Source.SourceExists body -> (putCacheTag 9 >>) <$> putEvidence body
    binary tag left right = do
        a <- putEvidence left
        encodedRight <- putEvidence right
        pure (putCacheTag tag >> a >> encodedRight)
    putPath path = visit >> case path of
        ConjunctionHere -> pure (putCacheTag 0)
        ConjunctionLeft rest -> (putCacheTag 1 >>) <$> putPath rest
        ConjunctionRight rest -> (putCacheTag 2 >>) <$> putPath rest

getAbbreviationExpansionCache :: CacheGet AbbreviationExpansion
getAbbreviationExpansionCache = getCacheNode $ getCacheTag >>= \case
    0 -> TermExpansion <$> getExpansionTermCache
    1 -> PropositionExpansion <$> getEvidence <*> getCacheList
        (getCacheNode (ExpansionEquality <$> getExpansionTermCache <*> getExpansionTermCache <*> getConjunctionPathCache))
    tag -> fail ("unknown abbreviation expansion tag " <> show tag)
  where
    getEvidence = getCacheNode $ getCacheTag >>= \case
        0 -> pure (Source.SourceResidual Nothing)
        5 -> Source.SourceInputs Nothing <$> getCacheList
            (Source.SourceInput <$> getCacheList getCoreTypeCache <*> getExpansionTermCache)
        6 -> Source.SourceWithInputs <$> getCacheList
            (Source.SourceInput <$> getCacheList getCoreTypeCache <*> getExpansionTermCache) <*> getEvidence
        1 -> Source.SourceAtom <$> getAtomTemplateWith "expansion atom" getExpansionTermCache
        2 -> Source.SourceAnd <$> getEvidence <*> getEvidence
        3 -> Source.SourceBind <$> getEvidence
        4 -> Source.SourceRequire <$> getEvidence <*> getEvidence
        7 -> Source.SourceOr <$> getEvidence <*> getEvidence
        8 -> Source.SourceIff <$> getEvidence <*> getEvidence
        9 -> Source.SourceExists <$> getEvidence
        tag -> fail ("unknown expansion evidence tag " <> show tag)

putExpansionTermCacheWith :: Monad m => m () -> ExpansionTerm -> m CachePut
putExpansionTermCacheWith visit value = visit >> case value of
    ExpansionFormal index -> pure (putCacheTag 0 >> putCacheNatural index)
    ExpansionLocal index -> pure (putCacheTag 1 >> putCacheNatural index)
    ExpansionProvider provider arguments -> do
        encoded <- traverse (putExpansionTermCacheWith visit) arguments
        pure (putCacheTag 2 >> putSourceProviderHeadCache provider >> putCacheList id (toList encoded))
    ExpansionPair left right -> do
        a <- putExpansionTermCacheWith visit left
        encodedRight <- putExpansionTermCacheWith visit right
        pure (putCacheTag 3 >> a >> encodedRight)
    ExpansionOpaque term -> (putCacheTag 4 >>) <$> putCanonicalTermCacheWith visit putObjectIdCache term

getExpansionTermCache :: CacheGet ExpansionTerm
getExpansionTermCache = getCacheNode $ getCacheTag >>= \case
    0 -> ExpansionFormal <$> getCacheNatural
    1 -> ExpansionLocal <$> getCacheNatural
    2 -> ExpansionProvider <$> getSourceProviderHeadCache <*> (Vector.fromList <$> getCacheList getExpansionTermCache)
    3 -> ExpansionPair <$> getExpansionTermCache <*> getExpansionTermCache
    4 -> ExpansionOpaque <$> getCanonicalTermCache getObjectIdCache
    tag -> fail ("unknown expansion term tag " <> show tag)

putFormationContractCache :: FormationContract -> CachePut
putFormationContractCache contract = do
    putCacheTag 0x02
    putCacheList putRequirement
        (NonEmpty.toList (formationContractRequirements contract))
  where
    putRequirement = \case
        AtomicLeaf atom -> putCacheTag 0x00 >> putNotionTemplateCache atom
        WholeLeaf (WholeUniversal body) -> putCacheTag 0x01 >> putUniversalBodyWith putFormationTermTemplateCache body
        WholeLeaf (WholeResidual residual) -> putCacheTag 0x02 >> putResidualTemplateCache residual

getFormationContractCache :: CacheGet FormationContract
getFormationContractCache = do
    getCacheTag >>= \case
        0x02 -> pure ()
        tag -> fail ("unknown formation contract version " <> show tag)
    requirements <- getCacheList getRequirement
    maybe
        (fail "an encoded formation contract is empty")
        (pure . formationContract)
        (NonEmpty.nonEmpty requirements)
  where
    getRequirement = getCacheNode $ getCacheTag >>= \case
        0x00 -> AtomicLeaf <$> getNotionTemplateCache
        0x01 -> WholeLeaf . WholeUniversal <$> getUniversalBodyWith getFormationTermTemplateCache
        0x02 -> WholeLeaf . WholeResidual <$> getResidualTemplateCache
        tag -> fail ("unknown formation requirement tag " <> show tag)

putSemanticFactBranchCache :: SemanticFactBranch -> CachePut
putSemanticFactBranchCache (SemanticFactBranch fact path) = do
    putSemanticFactOccurrenceFingerprintCache fact
    putConjunctionPathCache path

getSemanticFactBranchCache :: CacheGet SemanticFactBranch
getSemanticFactBranchCache = SemanticFactBranch
    <$> getSemanticFactOccurrenceFingerprintCache <*> getConjunctionPathCache

putConjunctionPathCache :: ConjunctionPath -> CachePut
putConjunctionPathCache = \case
    ConjunctionHere -> putCacheTag 0x00
    ConjunctionLeft rest -> putCacheTag 0x01 >> putConjunctionPathCache rest
    ConjunctionRight rest -> putCacheTag 0x02 >> putConjunctionPathCache rest

getConjunctionPathCache :: CacheGet ConjunctionPath
getConjunctionPathCache = getCacheNode $ getCacheTag >>= \case
    0x00 -> pure ConjunctionHere
    0x01 -> ConjunctionLeft <$> getConjunctionPathCache
    0x02 -> ConjunctionRight <$> getConjunctionPathCache
    tag -> fail ("unknown fact-branch path tag " <> show tag)

putSemanticRecordShapeKeyCache :: SemanticRecordShapeKey -> CachePut
putSemanticRecordShapeKeyCache (SemanticRecordShapeKey fields) =
    putCacheList (\(field,selector,projection) ->
        putFieldIdCache field >> putObjectIdCache selector >> putObjectIdCache projection) fields

getSemanticRecordShapeKeyCache :: CacheGet SemanticRecordShapeKey
getSemanticRecordShapeKeyCache = do
    fields <- getCacheList ((,,) <$> getFieldIdCache <*> getObjectIdCache <*> getObjectIdCache)
    let identities = [field | (field,_,_) <- fields]
    unless (and (zipWith (<) identities (drop 1 identities)))
        (fail "record-shape fields are not in canonical identity order")
    pure (SemanticRecordShapeKey fields)

putNotionTemplateCache :: NotionTemplate -> CachePut
putNotionTemplateCache = putAtomTemplateWith putFormationTermTemplateCache

getNotionTemplateCache :: CacheGet NotionTemplate
getNotionTemplateCache = getAtomTemplateWith "notion template" getFormationTermTemplateCache

putFormationTermTemplateCache :: FormationTermTemplate -> CachePut
putFormationTermTemplateCache = putSetTermTemplateWith putOccurrenceArgumentIxCache

getFormationTermTemplateCache :: CacheGet FormationTermTemplate
getFormationTermTemplateCache =
    getSetTermTemplateWith "formation term template" getOccurrenceArgumentIxCache

putAtomTemplateWith :: (term -> CachePut) -> AtomTemplate term -> CachePut
putAtomTemplateWith putTerm = \case
    GlobalAtomTemplate head' arguments -> do
        putCacheTag 0x00
        putGlobalNotionHeadCache head'
        putCacheList putTerm (toList arguments)
    StructureAtomTemplate head' arguments -> do
        putCacheTag 0x01
        putSemanticStructureNotionHeadCache head'
        putCacheList putTerm (toList arguments)
    MembershipAtomTemplate element set -> do
        putCacheTag 0x02
        putTerm element
        putTerm set
    ExactStructureAtomTemplate shape subject -> do
        putCacheTag 0x03
        putSemanticRecordShapeKeyCache shape
        putTerm subject
    NegativeGlobalAtomTemplate head' arguments -> do
        putCacheTag 0x04
        putGlobalNotionHeadCache head'
        putCacheList putTerm (toList arguments)
    NegativeStructureAtomTemplate head' arguments -> do
        putCacheTag 0x05
        putSemanticStructureNotionHeadCache head'
        putCacheList putTerm (toList arguments)
    NegativeMembershipAtomTemplate element set -> putCacheTag 0x06 >> putTerm element >> putTerm set
    NegativeExactStructureAtomTemplate shape subject ->
        putCacheTag 0x07 >> putSemanticRecordShapeKeyCache shape >> putTerm subject

getAtomTemplateWith :: String -> CacheGet term -> CacheGet (AtomTemplate term)
getAtomTemplateWith family getTerm =
    getCacheTag >>= \case
        0x00 ->
            GlobalAtomTemplate
                <$> getGlobalNotionHeadCache
                <*> (Vector.fromList
                    <$> getCacheList getTerm)
        0x01 ->
            StructureAtomTemplate
                <$> getSemanticStructureNotionHeadCache
                <*> (Vector.fromList
                    <$> getCacheList getTerm)
        0x02 ->
            MembershipAtomTemplate
                <$> getTerm
                <*> getTerm
        0x03 -> ExactStructureAtomTemplate <$> getSemanticRecordShapeKeyCache <*> getTerm
        0x04 -> NegativeGlobalAtomTemplate <$> getGlobalNotionHeadCache <*> (Vector.fromList <$> getCacheList getTerm)
        0x05 -> NegativeStructureAtomTemplate <$> getSemanticStructureNotionHeadCache <*> (Vector.fromList <$> getCacheList getTerm)
        0x06 -> NegativeMembershipAtomTemplate <$> getTerm <*> getTerm
        0x07 -> NegativeExactStructureAtomTemplate <$> getSemanticRecordShapeKeyCache <*> getTerm
        tag -> fail ("unknown " <> family <> " tag " <> show tag)

putSetTermTemplateWith :: (variable -> CachePut) -> SetTermTemplate variable -> CachePut
putSetTermTemplateWith putVariable = \case
    TemplateClosed value -> putCacheTag 0x03 >> putClosedSetValueCache value
    TemplateVariable variable -> do
        putCacheTag 0x00
        putVariable variable
    TemplateProvider head' arguments -> do
        putCacheTag 0x01
        putSourceProviderHeadCache head'
        putCacheList (putSetTermTemplateWith putVariable) (toList arguments)
    TemplateOrderedPair left right -> do
        putCacheTag 0x02
        putSetTermTemplateWith putVariable left
        putSetTermTemplateWith putVariable right

getSetTermTemplateWith :: String -> CacheGet variable -> CacheGet (SetTermTemplate variable)
getSetTermTemplateWith family getVariable = getCacheNode $
    getCacheTag >>= \case
        0x03 -> TemplateClosed <$> getClosedSetValueCache
        0x00 -> TemplateVariable <$> getVariable
        0x01 ->
            TemplateProvider
                <$> getSourceProviderHeadCache
                <*> (Vector.fromList
                    <$> getCacheList (getSetTermTemplateWith family getVariable))
        0x02 ->
            TemplateOrderedPair
                <$> getSetTermTemplateWith family getVariable
                <*> getSetTermTemplateWith family getVariable
        tag -> fail ("unknown " <> family <> " tag " <> show tag)

putProviderResultPremisesCache
    :: ProviderResultPremises RuleTermTemplate
    -> CachePut
putProviderResultPremisesCache = \case
    ProviderResultUnconditional ->
        putCacheTag 0x00
    ProviderResultGuarded premises -> do
        putCacheTag 0x01
        putRulePremiseBundlesCache premises

getProviderResultPremisesCache
    :: CacheGet (ProviderResultPremises RuleTermTemplate)
getProviderResultPremisesCache =
    getCacheTag >>= \case
        0x00 -> pure ProviderResultUnconditional
        0x01 -> ProviderResultGuarded <$> getRulePremiseBundlesCache
        tag -> fail ("unknown provider-result premise-mode tag " <> show tag)

putCheckedNotionRuleSkeletonCache
    :: CheckedNotionRuleSkeleton
    -> CachePut
putCheckedNotionRuleSkeletonCache skeleton = do
    putCacheNatural (checkedNotionRuleBinderArity skeleton)
    putCacheList putRulePremiseTreeCache (checkedNotionRulePremises skeleton)
    putRuleAtomTemplateCache (checkedNotionRuleConclusion skeleton)

getCheckedNotionRuleSkeletonCache :: CacheGet CheckedNotionRuleSkeleton
getCheckedNotionRuleSkeletonCache = do
    binderArity <- getCacheNatural
    premises <- getCacheList getRulePremiseTreeCache
    conclusion <- getRuleAtomTemplateCache
    either
        (fail . ("invalid checked notion-rule skeleton: " <>) . Text.unpack)
        pure
        (checkedNotionRuleSkeleton binderArity premises conclusion)

putRulePremiseBundlesCache
    :: RulePremiseBundles RuleTermTemplate
    -> CachePut
putRulePremiseBundlesCache (RulePremiseBundles bundles) =
    putCacheList putRulePremiseTreeCache (toList bundles)

getRulePremiseBundlesCache
    :: CacheGet (RulePremiseBundles RuleTermTemplate)
getRulePremiseBundlesCache = do
    bundles <- getCacheList getRulePremiseTreeCache
    case NonEmpty.nonEmpty bundles of
        Nothing -> fail "a backward notion rule has no premise bundles"
        Just present -> pure (RulePremiseBundles present)

putResidualTemplateCache :: ResidualTemplate -> CachePut
putResidualTemplateCache template = do
    putCanonicalTermCache putObjectIdCache (residualTemplateFormula template)
    putCacheMaybe putEvidence (residualTemplateEvidence template)
  where
    putEvidence = \case
        Source.SourceResidual _ -> putCacheTag 0
        Source.SourceInputs _ terms -> putCacheTag 5 >> putCacheList
            (\(Source.SourceInput binders term) -> putCacheList putCoreTypeCache binders >>
                putSetTermTemplateWith (putCanonicalTermCache putObjectIdCache) term) terms
        Source.SourceWithInputs terms body -> putCacheTag 6 >> putCacheList
            (\(Source.SourceInput binders term) -> putCacheList putCoreTypeCache binders >>
                putSetTermTemplateWith (putCanonicalTermCache putObjectIdCache) term) terms >> putEvidence body
        Source.SourceAtom atom -> putCacheTag 1 >> putRuleAtomTemplateCache atom
        Source.SourceAnd a b -> putCacheTag 2 >> putEvidence a >> putEvidence b
        Source.SourceBind body -> putCacheTag 3 >> putEvidence body
        Source.SourceRequire a b -> putCacheTag 4 >> putEvidence a >> putEvidence b
        Source.SourceOr left right -> putCacheTag 7 >> putEvidence left >> putEvidence right
        Source.SourceIff left right -> putCacheTag 8 >> putEvidence left >> putEvidence right
        Source.SourceExists body -> putCacheTag 9 >> putEvidence body

getResidualTemplateCache :: CacheGet ResidualTemplate
getResidualTemplateCache = DescribedResidualTemplate
    <$> getCanonicalTermCache getObjectIdCache <*> getCacheMaybe getEvidence
  where
    getEvidence = getCacheNode $ getCacheTag >>= \case
        0 -> pure (Source.SourceResidual Nothing)
        5 -> Source.SourceInputs Nothing <$> getCacheList
            (Source.SourceInput <$> getCacheList getCoreTypeCache <*>
                getSetTermTemplateWith "whole support operand" (getCanonicalTermCache getObjectIdCache))
        6 -> Source.SourceWithInputs <$> getCacheList
            (Source.SourceInput <$> getCacheList getCoreTypeCache <*>
                getSetTermTemplateWith "additional support operand" (getCanonicalTermCache getObjectIdCache)) <*> getEvidence
        1 -> Source.SourceAtom <$> getRuleAtomTemplateCache
        2 -> Source.SourceAnd <$> getEvidence <*> getEvidence
        3 -> Source.SourceBind <$> getEvidence
        4 -> Source.SourceRequire <$> getEvidence <*> getEvidence
        7 -> Source.SourceOr <$> getEvidence <*> getEvidence
        8 -> Source.SourceIff <$> getEvidence <*> getEvidence
        9 -> Source.SourceExists <$> getEvidence
        tag -> fail ("unknown whole source description tag " <> show tag)

putRulePremiseTreeCache
    :: RulePremiseTree RuleTermTemplate
    -> CachePut
putRulePremiseTreeCache = \case
    RulePremiseAtom atom -> do
        putCacheTag 0x00
        putRuleAtomTemplateCache atom
    RulePremiseUniversal body -> putCacheTag 0x02 >> putUniversalBodyWith putRuleTermTemplateCache body
    RulePremiseResidual residual -> putCacheTag 0x03 >> putResidualTemplateCache residual
    RulePremiseAnd left right -> do
        putCacheTag 0x01
        putRulePremiseTreeCache left
        putRulePremiseTreeCache right

getRulePremiseTreeCache
    :: CacheGet (RulePremiseTree RuleTermTemplate)
getRulePremiseTreeCache = getCacheNode $
    getCacheTag >>= \case
        0x00 -> RulePremiseAtom <$> getRuleAtomTemplateCache
        0x01 ->
            RulePremiseAnd
                <$> getRulePremiseTreeCache
                <*> getRulePremiseTreeCache
        0x02 -> RulePremiseUniversal <$> getUniversalBodyWith getRuleTermTemplateCache
        0x03 -> RulePremiseResidual <$> getResidualTemplateCache
        tag -> fail ("unknown rule-premise tree tag " <> show tag)

putUniversalBodyWith :: (term -> CachePut) -> UniversalTemplate term -> CachePut
putUniversalBodyWith putTerm = \case
    UniversalReturn atoms -> putCacheTag 0x00 >> putAtoms atoms
    UniversalBind nested -> putCacheTag 0x01 >> putUniversalBodyWith putTerm nested
    UniversalRequire atoms nested -> putCacheTag 0x02 >> putAtoms atoms >> putUniversalBodyWith putTerm nested
  where
    putAtoms (AtomLeaf atom) = putCacheTag 0x00 >> putAtomTemplateWith
        (putSetTermTemplateWith putOperand) atom
    putAtoms (AtomAnd left right) = putCacheTag 0x01 >> putAtoms left >> putAtoms right
    putOperand (UniversalBound index) = putCacheTag 0x00 >> putCacheNatural index
    putOperand (UniversalOuter term) = putCacheTag 0x01 >> putTerm term

getUniversalBodyWith :: CacheGet term -> CacheGet (UniversalTemplate term)
getUniversalBodyWith getTerm = getCacheNode $ getCacheTag >>= \case
    0x00 -> UniversalReturn <$> getAtoms
    0x01 -> UniversalBind <$> getUniversalBodyWith getTerm
    0x02 -> UniversalRequire <$> getAtoms <*> getUniversalBodyWith getTerm
    tag -> fail ("unknown supplied universal tag " <> show tag)
  where
    getAtoms = getCacheNode $ getCacheTag >>= \case
        0x00 -> AtomLeaf <$> getAtomTemplateWith "supplied universal atom"
            (getSetTermTemplateWith "universal term" getOperand)
        0x01 -> AtomAnd <$> getAtoms <*> getAtoms
        tag -> fail ("unknown supplied conjunction tag " <> show tag)
    getOperand = getCacheNode $ getCacheTag >>= \case
        0x00 -> UniversalBound <$> getCacheNatural
        0x01 -> UniversalOuter <$> getTerm
        tag -> fail ("unknown supplied operand tag " <> show tag)

putRuleAtomTemplateCache :: AtomTemplate RuleTermTemplate -> CachePut
putRuleAtomTemplateCache = putAtomTemplateWith putRuleTermTemplateCache

getRuleAtomTemplateCache :: CacheGet (AtomTemplate RuleTermTemplate)
getRuleAtomTemplateCache = getAtomTemplateWith "rule-atom template" getRuleTermTemplateCache

putRuleTermTemplateCache :: RuleTermTemplate -> CachePut
putRuleTermTemplateCache = putSetTermTemplateWith putViewVariableIxCache

getRuleTermTemplateCache :: CacheGet RuleTermTemplate
getRuleTermTemplateCache = getSetTermTemplateWith "rule-term template" getViewVariableIxCache

putClosedSetValueCache :: ClosedSetValue -> CachePut
putClosedSetValueCache = putCanonicalTermCache putObjectIdCache . closedSetValueTerm

getClosedSetValueCache :: CacheGet ClosedSetValue
getClosedSetValueCache = do
    term <- getCanonicalTermCache getObjectIdCache
    unless (runIdentity (canonicalClosedWith (pure ()) term))
        (fail "a closed set value captures a binder")
    pure (ClosedSetValue term)

putResultProviderTemplateCache :: ResultProviderTemplate -> CachePut
putResultProviderTemplateCache provider = do
    putSourceProviderHeadCache (resultProviderTemplateHead provider)
    putCacheList putRuleTermTemplateCache
        (toList (resultProviderTemplateArguments provider))

getResultProviderTemplateCache :: CacheGet ResultProviderTemplate
getResultProviderTemplateCache =
    resultProviderTemplate
        <$> getSourceProviderHeadCache
        <*> (Vector.fromList <$> getCacheList getRuleTermTemplateCache)

putSourceProviderHeadCache :: SourceProviderHead -> CachePut
putSourceProviderHeadCache = \case
    GlobalSourceProvider reference -> do
        putCacheTag 0x00
        putGlobalBindingRefCache reference
    StructureFieldSourceProvider identity projection -> do
        putCacheTag 0x01
        putFieldIdCache identity
        putObjectIdCache projection
    IntrinsicSourceProvider provider -> do
        putCacheTag 0x02
        putIntrinsicProviderIdCache provider
    FiniteSetLiteralSourceProvider ->
        putCacheTag 0x03

getSourceProviderHeadCache :: CacheGet SourceProviderHead
getSourceProviderHeadCache =
    getCacheTag >>= \case
        0x00 -> GlobalSourceProvider <$> getGlobalBindingRefCache
        0x01 ->
            StructureFieldSourceProvider
                <$> getFieldIdCache
                <*> getObjectIdCache
        0x02 -> IntrinsicSourceProvider <$> getIntrinsicProviderIdCache
        0x03 -> pure FiniteSetLiteralSourceProvider
        tag -> fail ("unknown source-provider head tag " <> show tag)

putIntrinsicProviderIdCache :: IntrinsicProviderId -> CachePut
putIntrinsicProviderIdCache = \case
    PowerSetProvider -> putCacheTag 0x00
    GlobalChoiceProvider -> putCacheTag 0x01
    EmptySetProvider -> putCacheTag 0x02
    FirstProjectionProvider -> putCacheTag 0x03
    SecondProjectionProvider -> putCacheTag 0x04

getIntrinsicProviderIdCache :: CacheGet IntrinsicProviderId
getIntrinsicProviderIdCache =
    getCacheTag >>= \case
        0x00 -> pure PowerSetProvider
        0x01 -> pure GlobalChoiceProvider
        0x02 -> pure EmptySetProvider
        0x03 -> pure FirstProjectionProvider
        0x04 -> pure SecondProjectionProvider
        tag -> fail ("unknown intrinsic-provider id tag " <> show tag)

putResultNotionRuleTemplateCache :: ResultNotionRuleTemplate -> CachePut
putResultNotionRuleTemplateCache = putAtomTemplateWith putResultRuleTermCache

getResultNotionRuleTemplateCache :: CacheGet ResultNotionRuleTemplate
getResultNotionRuleTemplateCache = getAtomTemplateWith "result-notion template" getResultRuleTermCache

putResultRuleTermCache :: ResultRuleTerm -> CachePut
putResultRuleTermCache = \case
    ResultRuleTerm term -> do
        putCacheTag 0x00
        putRuleTermTemplateCache term
    ResultRuleProviderValue ->
        putCacheTag 0x01

getResultRuleTermCache :: CacheGet ResultRuleTerm
getResultRuleTermCache =
    getCacheTag >>= \case
        0x00 -> ResultRuleTerm <$> getRuleTermTemplateCache
        0x01 -> pure ResultRuleProviderValue
        tag -> fail ("unknown result-rule term tag " <> show tag)

putNotionViewPremiseTemplateCache
    :: NotionViewPremiseTemplate
    -> CachePut
putNotionViewPremiseTemplateCache = \case
    GlobalNotionViewPremise head' arguments -> do
        putCacheTag 0x00
        putGlobalNotionHeadCache head'
        putCacheList putRuleTermTemplateCache (toList arguments)
    StructureNotionViewPremise head' arguments -> do
        putCacheTag 0x01
        putSemanticStructureNotionHeadCache head'
        putCacheList putRuleTermTemplateCache (toList arguments)
    ExactProviderMembershipPremise element provider arguments -> do
        putCacheTag 0x02
        putRuleTermTemplateCache element
        putSourceProviderHeadCache provider
        putCacheList putRuleTermTemplateCache (toList arguments)

getNotionViewPremiseTemplateCache
    :: CacheGet NotionViewPremiseTemplate
getNotionViewPremiseTemplateCache =
    getCacheTag >>= \case
        0x00 ->
            GlobalNotionViewPremise
                <$> getGlobalNotionHeadCache
                <*> (Vector.fromList
                    <$> getCacheList getRuleTermTemplateCache)
        0x01 ->
            StructureNotionViewPremise
                <$> getSemanticStructureNotionHeadCache
                <*> (Vector.fromList
                    <$> getCacheList getRuleTermTemplateCache)
        0x02 ->
            ExactProviderMembershipPremise
                <$> getRuleTermTemplateCache
                <*> getSourceProviderHeadCache
                <*> (Vector.fromList
                    <$> getCacheList getRuleTermTemplateCache)
        tag -> fail ("unknown notion-view premise tag " <> show tag)

putNotionViewTemplateCache :: NotionViewTemplate -> CachePut
putNotionViewTemplateCache = \case
    AtomicLeaf atom -> putCacheTag 0 >> putRuleAtomTemplateCache atom
    WholeLeaf residual -> putCacheTag 1 >> putResidualTemplateCache residual

getNotionViewTemplateCache :: CacheGet NotionViewTemplate
getNotionViewTemplateCache = getCacheTag >>= \case
    0 -> AtomicLeaf <$> getRuleAtomTemplateCache
    1 -> WholeLeaf <$> getResidualTemplateCache
    tag -> fail ("unknown rule conclusion tag " <> show tag)

putViewVariableIxCache :: ViewVariableIx -> CachePut
putViewVariableIxCache (ViewVariableIx index) =
    putCacheNatural index

getViewVariableIxCache :: CacheGet ViewVariableIx
getViewVariableIxCache =
    ViewVariableIx <$> getCacheNatural

putOccurrenceArgumentIxCache :: OccurrenceArgumentIx -> CachePut
putOccurrenceArgumentIxCache (OccurrenceArgumentIx index) =
    putCacheNatural index

getOccurrenceArgumentIxCache :: CacheGet OccurrenceArgumentIx
getOccurrenceArgumentIxCache =
    OccurrenceArgumentIx <$> getCacheNatural

putGlobalNotionHeadCache :: GlobalNotionHead -> CachePut
putGlobalNotionHeadCache = \case
    NounNotionHead reference -> do
        putCacheTag 0x00
        putGlobalBindingRefCache reference
    AdjectiveNotionHead reference -> do
        putCacheTag 0x01
        putGlobalBindingRefCache reference
    RelationNotionHead reference -> do
        putCacheTag 0x02
        putGlobalBindingRefCache reference
    VerbNotionHead reference -> do
        putCacheTag 0x03
        putGlobalBindingRefCache reference
    PrefixPredicateNotionHead reference -> do
        putCacheTag 0x04
        putGlobalBindingRefCache reference

getGlobalNotionHeadCache :: CacheGet GlobalNotionHead
getGlobalNotionHeadCache =
    getCacheTag >>= \case
        0x00 -> NounNotionHead <$> getGlobalBindingRefCache
        0x01 -> AdjectiveNotionHead <$> getGlobalBindingRefCache
        0x02 -> RelationNotionHead <$> getGlobalBindingRefCache
        0x03 -> VerbNotionHead <$> getGlobalBindingRefCache
        0x04 -> PrefixPredicateNotionHead <$> getGlobalBindingRefCache
        tag -> fail ("unknown global notion head tag " <> show tag)

putGlobalBindingRefCache :: GlobalBindingRef -> CachePut
putGlobalBindingRefCache (GlobalBindingRef owner key) = do
    putDeclarationSlotCache owner
    putSemanticGlobalKeyCache key

getGlobalBindingRefCache :: CacheGet GlobalBindingRef
getGlobalBindingRefCache =
    GlobalBindingRef
        <$> getDeclarationSlotCache
        <*> getSemanticGlobalKeyCache

putSemanticStructureNotionHeadCache :: SemanticStructureNotionHead -> CachePut
putSemanticStructureNotionHeadCache (SemanticStructureNotionHead identity) = putStructureIdCache identity

getSemanticStructureNotionHeadCache :: CacheGet SemanticStructureNotionHead
getSemanticStructureNotionHeadCache = SemanticStructureNotionHead <$> getStructureIdCache

putStructurePhraseCache
    :: Schema.StructurePhrase
    -> CachePut
putStructurePhraseCache structurePhrase = do
    putPatternCache (Schema.structurePhraseSingular structurePhrase)
    putPatternCache (Schema.structurePhrasePlural structurePhrase)
    let Marker marker = Schema.structurePhraseMarker structurePhrase
    putCacheText marker

getStructurePhraseCache
    :: CacheGet Schema.StructurePhrase
getStructurePhraseCache = do
    singular <- getPatternCache
    plural <- getPatternCache
    marker <- Marker <$> getCacheText
    pure (Schema.structurePhrase (LexicalItemSgPl (SgPl singular plural) marker))

putRegistrationCache :: Registration SemanticFactOccurrenceFingerprint -> CachePut
putRegistrationCache registration = do
    putSemanticFactBranchCache (registrationBranch registration)
    putRegistrationBodyCache (registrationBody registration)

-- A disposable index key, never proof authority. Equal descriptions have
-- equal keys; callers must still compare complete bodies on a collision.
registrationBodyCacheDigest :: RegistrationBody -> CacheDigest
registrationBodyCacheDigest body = hashCacheFields "formation-description"
    [encodeCache (putCacheNatural (fromIntegral (registrationFamily body)) >> putRegistrationBodyCache body)]

putRegistrationBodyCache :: RegistrationBody -> CachePut
putRegistrationBodyCache body =
    case body of
        RegisterNotionView (NotionViewRule premise conclusion) -> do
            putNotionViewPremiseTemplateCache premise
            putNotionViewTemplateCache conclusion
        RegisterNullaryProvider (NullaryProviderRule provider conclusion) -> do
            putIntrinsicProviderIdCache provider
            putGlobalNotionHeadCache conclusion
        RegisterProviderResult (ProviderResultRule provider premises conclusion) -> do
            putResultProviderTemplateCache provider
            putProviderResultPremisesCache premises
            putResultNotionRuleTemplateCache conclusion
        RegisterBackwardNotion (BackwardNotionRule premises conclusion) -> do
            putRulePremiseBundlesCache premises
            putRuleAtomTemplateCache conclusion
        RegisterFiniteEvidence (FiniteEvidenceRule skeleton) -> do
            putCheckedNotionRuleSkeletonCache skeleton
        RegisterGraphDomain (GraphDomainRule provider left right graph) -> do
            putSourceProviderHeadCache provider
            putViewVariableIxCache left
            putViewVariableIxCache right
            putViewVariableIxCache graph
        RegisterWholeConclusion (WholeConclusionRule arity premises conclusion) -> do
            putCacheNatural arity
            putCacheList putRulePremiseTreeCache premises
            putResidualTemplateCache conclusion

getRegistrationCache
    :: CacheGet RegistrationBody
    -> CacheGet (Registration SemanticFactOccurrenceFingerprint)
getRegistrationCache body = do
    SemanticFactBranch source path <- getSemanticFactBranchCache
    Registration source path <$> body

putDeclarationInterfaceDeltaCache :: DeclarationInterfaceDelta -> CachePut
putDeclarationInterfaceDeltaCache
        (DeclarationInterfaceDelta slot facts aliases objects propositions views registrations environment) = do
    putDeclarationSlotCache slot
    putCacheList putSemanticFactOccurrenceCache facts
    putCacheList putSemanticAliasCache aliases
    putCacheList putObjectIdCache objects
    putCacheList putPropositionIdCache propositions
    putCacheList putSemanticDefinitionViewCache views
    for_ [0..6] \family ->
        putCacheList putRegistrationCache
            (List.filter ((== family) . registrationFamily . registrationBody) registrations)
    putSemanticEnvironmentDeltaCache environment

getDeclarationInterfaceDeltaCache :: CacheGet DeclarationInterfaceDelta
getDeclarationInterfaceDeltaCache = do
    slot <- getDeclarationSlotCache
    facts <- getCacheList getSemanticFactOccurrenceCache
    aliases <- getCacheList getSemanticAliasCache
    objects <- getCacheList getObjectIdCache
    propositions <- getCacheList getPropositionIdCache
    views <- getCacheList getSemanticDefinitionViewCache
    registrations <- concat <$> sequence
        [ getCacheList (getRegistrationCache (RegisterNotionView <$> (NotionViewRule
            <$> getNotionViewPremiseTemplateCache
            <*> getNotionViewTemplateCache)))
        , getCacheList (getRegistrationCache (RegisterNullaryProvider <$> (NullaryProviderRule
            <$> getIntrinsicProviderIdCache
            <*> getGlobalNotionHeadCache)))
        , getCacheList (getRegistrationCache (RegisterProviderResult <$> (ProviderResultRule
            <$> getResultProviderTemplateCache
            <*> getProviderResultPremisesCache
            <*> getResultNotionRuleTemplateCache)))
        , getCacheList (getRegistrationCache (RegisterBackwardNotion <$> (BackwardNotionRule
            <$> getRulePremiseBundlesCache
            <*> getRuleAtomTemplateCache)))
        , getCacheList (getRegistrationCache (RegisterFiniteEvidence <$> (FiniteEvidenceRule
            <$> getCheckedNotionRuleSkeletonCache)))
        , getCacheList (getRegistrationCache (RegisterGraphDomain <$> (GraphDomainRule
            <$> getSourceProviderHeadCache
            <*> getViewVariableIxCache
            <*> getViewVariableIxCache
            <*> getViewVariableIxCache)))
        , getCacheList (getRegistrationCache (RegisterWholeConclusion <$> (WholeConclusionRule
            <$> getCacheNatural
            <*> getCacheList getRulePremiseTreeCache
            <*> getResidualTemplateCache)))
        ]
    environment <- getSemanticEnvironmentDeltaCache
    either (fail . ("invalid declaration interface delta: " <>) . show) pure
        (declarationInterfaceDelta slot facts aliases objects propositions views registrations environment)

putSemanticInterfaceCache :: SemanticInterface -> CachePut
putSemanticInterfaceCache
        (SemanticInterface owner direct declarations asserted) = do
    putModuleNameCache owner
    putCacheList putSemanticInterfaceIdCache direct
    putCacheList putDeclarationInterfaceDeltaCache declarations
    putSemanticInterfaceIdCache asserted

getSemanticInterfaceCache :: CacheGet SemanticInterface
getSemanticInterfaceCache = do
    owner <- getModuleNameCache
    direct <- getCacheList getSemanticInterfaceIdCache
    declarations <- getCacheList getDeclarationInterfaceDeltaCache
    asserted <- getSemanticInterfaceIdCache
    either
        (fail . ("invalid semantic interface: " <>) . show)
        pure
        (validateSemanticInterface
            owner direct declarations asserted)

putSemanticInterfaceIdCache :: SemanticInterfaceId -> CachePut
putSemanticInterfaceIdCache (SemanticInterfaceId digest) =
    putCacheDigest digest

getSemanticInterfaceIdCache :: CacheGet SemanticInterfaceId
getSemanticInterfaceIdCache =
    SemanticInterfaceId <$> getCacheDigest

putPrefixContextIdCache :: PrefixContextId -> CachePut
putPrefixContextIdCache (PrefixContextId digest) =
    putCacheDigest digest

getPrefixContextIdCache :: CacheGet PrefixContextId
getPrefixContextIdCache =
    PrefixContextId <$> getCacheDigest

putModuleArtefactKeyCache :: ModuleArtefactKey -> CachePut
putModuleArtefactKeyCache =
    putModuleArtefactKeyFields

getModuleArtefactKeyCache :: CacheGet ModuleArtefactKey
getModuleArtefactKeyCache = do
    owner <- getModuleNameCache
    parsed <- getParsedModuleIdCache
    direct <- getCacheList getSemanticInterfaceIdCache
    theory <- getTheoryIdCache
    either
        (fail . ("invalid module artefact key: " <>) . show)
        pure
        (moduleArtefactKey owner parsed direct theory)

putModuleArtefactIdCache :: ModuleArtefactId -> CachePut
putModuleArtefactIdCache (ModuleArtefactId digest) =
    putCacheDigest digest

getModuleArtefactIdCache :: CacheGet ModuleArtefactId
getModuleArtefactIdCache =
    ModuleArtefactId <$> getCacheDigest

putModuleArtefactResultCache
    :: ModuleArtefactResult
    -> CachePut
putModuleArtefactResultCache
        (ModuleArtefactResult identity syntax semantic certificates) = do
    putModuleArtefactIdCache identity
    putSyntaxInterfaceIdCache syntax
    putSemanticInterfaceIdCache semantic
    putCacheList putValidationCertificateCache certificates

getModuleArtefactResultCache
    :: ModuleArtefactId
    -> CacheGet ModuleArtefactResult
getModuleArtefactResultCache expected = do
    asserted <- getModuleArtefactIdCache
    unless
        (asserted == expected)
        (fail "module artefact result ID mismatch")
    ModuleArtefactResult asserted
        <$> getSyntaxInterfaceIdCache
        <*> getSemanticInterfaceIdCache
        <*> getCacheList getValidationCertificateCache

putProofValidationRecordCache
    :: ProofValidationRecord
    -> CachePut
putProofValidationRecordCache
        (ProofValidationRecord key certificate) = do
    putProofValidationKeyCache key
    putValidationCertificateCache certificate

getProofValidationRecordCache
    :: CacheGet ProofValidationRecord
getProofValidationRecordCache =
    ProofValidationRecord
        <$> getProofValidationKeyCache
        <*> getValidationCertificateCache

putDeclarationValidationRecordCache
    :: DeclarationValidationRecord
    -> CachePut
putDeclarationValidationRecordCache
        (DeclarationValidationRecord key certificates) = do
    putDeclarationValidationKeyCache key
    putCacheList putValidationCertificateCache certificates

getDeclarationValidationRecordCache
    :: CacheGet DeclarationValidationRecord
getDeclarationValidationRecordCache =
    DeclarationValidationRecord
        <$> getDeclarationValidationKeyCache
        <*> getCacheList getValidationCertificateCache


putDeclarationSlotCache :: DeclarationSlot -> CachePut
putDeclarationSlotCache (DeclarationSlot owner ordinal) = do
    putModuleNameCache owner
    putCacheNatural (localDeclarationOrdinalValue ordinal)

getDeclarationSlotCache :: CacheGet DeclarationSlot
getDeclarationSlotCache =
    DeclarationSlot
        <$> getModuleNameCache
        <*> (localDeclarationOrdinal <$> getCacheNatural)

putFactSlotCache :: FactSlot -> CachePut
putFactSlotCache (FactSlot owner ordinal) = do
    putModuleNameCache owner
    putCacheNatural (localFactOrdinalValue ordinal)

getFactSlotCache :: CacheGet FactSlot
getFactSlotCache =
    FactSlot
        <$> getModuleNameCache
        <*> (localFactOrdinal <$> getCacheNatural)

putModuleNameCache :: ModuleName -> CachePut
putModuleNameCache owner = do
    putMathematicalDigestCache
        (sourceNamespaceDigest
            (moduleNameNamespace owner))
    putCacheText
        (Text.pack
            (safeRelativePathFilePath
                (moduleNameRelativePath owner)))

getModuleNameCache :: CacheGet ModuleName
getModuleNameCache = do
    namespace <-
        sourceNamespaceIdFromDigest
            <$> getMathematicalDigestCache
    rawPath <- Text.unpack <$> getCacheText
    relative <-
        either
            (fail . ("invalid cache module path: " <>) . show)
            pure
            (safeRelativePath rawPath)
    pure (moduleNameFromParts namespace relative)

putSemanticAliasCache :: SemanticAlias -> CachePut
putSemanticAliasCache (SemanticAlias name target) = do
    putSemanticNameCache name
    putSemanticFactOccurrenceFingerprintCache target

getSemanticAliasCache :: CacheGet SemanticAlias
getSemanticAliasCache =
    SemanticAlias
        <$> getSemanticNameCache
        <*> getSemanticFactOccurrenceFingerprintCache

putSemanticDefinitionViewCache
    :: SemanticDefinitionView
    -> CachePut
putSemanticDefinitionViewCache view = do
    putObjectIdCache (definitionViewObject view)
    putDefinitionViewKindCache (definitionViewKind view)
    putSemanticFactOccurrenceFingerprintCache (definitionViewTarget view)

getSemanticDefinitionViewCache :: CacheGet SemanticDefinitionView
getSemanticDefinitionViewCache =
    definitionView
        <$> getObjectIdCache
        <*> getDefinitionViewKindCache
        <*> getSemanticFactOccurrenceFingerprintCache

putDefinitionViewKindCache :: DefinitionViewKind -> CachePut
putDefinitionViewKindCache = \case
    DefinitionPointwiseView -> putCacheTag 0x00
    DefinitionExactView -> putCacheTag 0x01
    DefinitionMembershipView -> putCacheTag 0x02

getDefinitionViewKindCache :: CacheGet DefinitionViewKind
getDefinitionViewKindCache =
    getCacheTag >>= \case
        0x00 -> pure DefinitionPointwiseView
        0x01 -> pure DefinitionExactView
        0x02 -> pure DefinitionMembershipView
        tag -> fail ("unknown definition-view kind tag " <> show tag)

putSemanticNameCache :: SemanticName -> CachePut
putSemanticNameCache (SemanticName name) =
    putCacheText name

getSemanticNameCache :: CacheGet SemanticName
getSemanticNameCache =
    SemanticName <$> getCacheText

putEligibility :: FactSearchEligibility -> CachePut
putEligibility = \case
    SearchEligible -> putCacheTag 0x00
    SearchIneligible -> putCacheTag 0x01

getEligibility :: CacheGet FactSearchEligibility
getEligibility =
    getCacheTag >>= \case
        0x00 -> pure SearchEligible
        0x01 -> pure SearchIneligible
        tag ->
            fail ("unknown fact-search eligibility tag " <> show tag)

putModuleArtefactKeyFields :: ModuleArtefactKey -> CachePut
putModuleArtefactKeyFields
        (ModuleArtefactKey owner parsed direct theory) = do
    putModuleNameCache owner
    putParsedModuleIdCache parsed
    putCacheList putSemanticInterfaceIdCache direct
    putTheoryIdCache theory

putProofValidationKeyCache :: ProofValidationKey -> CachePut
putProofValidationKeyCache (ProofValidationKey digest) =
    putCacheDigest digest

getProofValidationKeyCache :: CacheGet ProofValidationKey
getProofValidationKeyCache =
    ProofValidationKey <$> getCacheDigest

putDeclarationValidationKeyCache
    :: DeclarationValidationKey
    -> CachePut
putDeclarationValidationKeyCache
        (DeclarationValidationKey digest) =
    putCacheDigest digest

getDeclarationValidationKeyCache
    :: CacheGet DeclarationValidationKey
getDeclarationValidationKeyCache =
    DeclarationValidationKey <$> getCacheDigest

rejectDuplicate
    :: Ord value
    => (value -> error)
    -> [value]
    -> Either error ()
rejectDuplicate makeError values =
    maybe
        (Right ())
        (Left . makeError)
        (firstDuplicate values)

strictlyIncreasing :: Ord value => [value] -> Bool
strictlyIncreasing values =
    and
        (zipWith (<) values (drop 1 values))

-- Structure purpose and key tags are explicit wire contracts. These decode
-- claims only; local declaration admission reconstructs and checks ownership.
putFactPurposeCache :: FactPurpose -> CachePut
putFactPurposeCache = \case
    GeneralFactPurpose -> putCacheTag 0
    StructureFactPurpose law -> putCacheTag 1 >> putStructureLawIdCache law

getFactPurposeCache :: CacheGet FactPurpose
getFactPurposeCache = getCacheTag >>= \case
    0 -> pure GeneralFactPurpose
    1 -> StructureFactPurpose <$> getStructureLawIdCache
    tag -> fail ("unknown fact purpose tag " <> show tag)

putStructureLawIdCache :: Schema.StructureLawId -> CachePut
putStructureLawIdCache (Schema.StructureLawId owner key) = do
    putStructureIdCache owner
    putStructureLawKeyCache key

getStructureLawIdCache :: CacheGet Schema.StructureLawId
getStructureLawIdCache = Schema.StructureLawId <$> getStructureIdCache <*> getStructureLawKeyCache

putStructureLawKeyCache :: Schema.GeneratedStructureLawKey -> CachePut
putStructureLawKeyCache = \case
    Schema.PredicateComponentLaw component -> do
        putCacheTag 0
        case component of
            Schema.PredicateShapeComponent -> putCacheTag 0
            Schema.PredicateRequirementComponent provenance ->
                putCacheTag 1 >> putRequirementProvenanceKeyCache provenance
    Schema.ParentInheritanceLaw application ->
        putCacheTag 1 >> putStructureApplicationKeyCache application
    Schema.RecordSchemaLaw law -> do
        putCacheTag 2
        let (tag, fields) = Record.recordSchemaLawCode law
        putCacheTag tag
        putCacheList putFieldIdCache fields

getStructureLawKeyCache :: CacheGet Schema.GeneratedStructureLawKey
getStructureLawKeyCache = getCacheTag >>= \case
    0 -> Schema.PredicateComponentLaw <$> (getCacheTag >>= \case
        0 -> pure Schema.PredicateShapeComponent
        1 -> Schema.PredicateRequirementComponent <$> getRequirementProvenanceKeyCache
        tag -> fail ("unknown predicate component tag " <> show tag))
    1 -> Schema.ParentInheritanceLaw <$> getStructureApplicationKeyCache
    2 -> do
        tag <- getCacheTag
        fields <- getCacheList getFieldIdCache
        maybe (fail ("invalid record law code " <> show tag)) (pure . Schema.RecordSchemaLaw)
            (Record.recordSchemaLawFromCode tag fields)
    tag -> fail ("unknown structure law tag " <> show tag)

putStructureResourceKeyCache :: Schema.StructureResourceKey -> CachePut
putStructureResourceKeyCache = \case
    Schema.PredicateDefinitionResource -> putCacheTag 0
    Schema.SelectorDefinitionResource field -> putCacheTag 1 >> putFieldIdCache field
    Schema.ProjectionMembershipResource field -> putCacheTag 2 >> putFieldIdCache field

getStructureResourceKeyCache :: CacheGet Schema.StructureResourceKey
getStructureResourceKeyCache = getCacheTag >>= \case
    0 -> pure Schema.PredicateDefinitionResource
    1 -> Schema.SelectorDefinitionResource <$> getFieldIdCache
    2 -> Schema.ProjectionMembershipResource <$> getFieldIdCache
    tag -> fail ("unknown structure resource tag " <> show tag)

putStructureApplicationKeyCache :: Schema.StructureApplicationKey -> CachePut
putStructureApplicationKeyCache application = do
    putStructureIdCache (Schema.structureApplicationId application)
    putCacheList (putCanonicalTermCache putObjectIdCache) (Schema.structureApplicationArguments application)

getStructureApplicationKeyCache :: CacheGet Schema.StructureApplicationKey
getStructureApplicationKeyCache = Schema.structureApplicationKey
    <$> getStructureIdCache <*> getCacheList (getCanonicalTermCache getObjectIdCache)

putRequirementProvenanceKeyCache :: Schema.RequirementProvenanceKey -> CachePut
putRequirementProvenanceKeyCache (Schema.RequirementProvenanceKey origin owner) = do
    putRequirementOriginCache origin
    putStructureApplicationKeyCache owner

getRequirementProvenanceKeyCache :: CacheGet Schema.RequirementProvenanceKey
getRequirementProvenanceKeyCache = Schema.RequirementProvenanceKey
    <$> getRequirementOriginCache <*> getStructureApplicationKeyCache

putRequirementOriginCache :: Schema.RequirementOrigin -> CachePut
putRequirementOriginCache = \case
    Schema.PreambleOrigin owner (Schema.LocalPreambleClauseKey item row) -> do
        putCacheTag 0
        putStructureIdCache owner
        putCacheNatural item
        putCacheNatural row
    Schema.FieldSpecificationOrigin owner field -> do
        putCacheTag 1
        putStructureIdCache owner
        putFieldIdCache field
    Schema.LawOrigin owner (Schema.LocalLawOrdinal ordinal) -> do
        putCacheTag 2
        putStructureIdCache owner
        putCacheNatural ordinal

getRequirementOriginCache :: CacheGet Schema.RequirementOrigin
getRequirementOriginCache = getCacheTag >>= \case
    0 -> Schema.PreambleOrigin <$> getStructureIdCache
        <*> (Schema.LocalPreambleClauseKey <$> getCacheNatural <*> getCacheNatural)
    1 -> Schema.FieldSpecificationOrigin <$> getStructureIdCache <*> getFieldIdCache
    2 -> Schema.LawOrigin <$> getStructureIdCache <*> (Schema.LocalLawOrdinal <$> getCacheNatural)
    tag -> fail ("unknown requirement origin tag " <> show tag)

-- Only local replay inputs and exact occurrence associations cross the cache
-- boundary. No resolved ancestor closure or process-local evidence is encoded.
data StructureInterfaceWire = StructureInterfaceWire
    !Schema.LocalStructureSchemaWire
    !ObjectId
    !(Map Schema.GeneratedStructureLawKey SemanticFactOccurrenceFingerprint)
    !(Map Schema.StructureResourceKey SemanticFactOccurrenceFingerprint)
    !StructurePresentationWire
    ![Schema.StructureApplicationKey]
    ![FieldId]
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord StructureInterfaceWire where
    compare left right = compare
        (encodeCache (putStructureInterfaceWireCache left))
        (encodeCache (putStructureInterfaceWireCache right))

data StructurePresentationWire = StructurePresentationWire
    !Schema.StructurePhrase !StructureSourcePosition ![VarSymbol]
    ![(Maybe Marker, StructureSourcePosition)]
    !(Map Schema.LocalPreambleClauseKey StructureSourcePosition)
    !(Map StructureFieldSlot (Maybe Marker, StructureSourcePosition))
    !(Map Schema.LocalLawOrdinal (Marker, StructureSourcePosition))
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data StructureSourcePosition
    = StructurePositionUnknown
    | StructurePosition !Text !Text !Natural !Natural
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

-- Local mathematical inputs and their source presentation determine the
-- declaration recipe; occurrence fingerprints are assigned by planning.
structureBatchSyntaxId :: NonEmpty Schema.LocalStructureSchema -> DeclarationSyntaxId
structureBatchSyntaxId inputs = declarationSyntaxId (encodeCache do
    putCacheText "normalized-structure-batch-v1"
    putCacheList putInput (List.sortOn (Schema.localWireSlot . Schema.localSchemaWire) (toList inputs)))
  where
    putInput input = do
        putLocalStructureSchemaWireCache (Schema.localSchemaWire input)
        putStructurePresentationWireCache (freezeStructurePresentation (Schema.localPresentation input))

structureInterfaceWire
    :: Schema.LocalStructureSchema
    -> StructurePredicate.PendingStructureRegistration
    -> Map Schema.GeneratedStructureLawKey SemanticFactOccurrenceFingerprint
    -> Map Schema.StructureResourceKey SemanticFactOccurrenceFingerprint
    -> Either Text StructureInterfaceWire
structureInterfaceWire local registration laws resources = do
    let schema = StructurePredicate.pendingStructureSchema registration
        input = Schema.localSchemaWire local
        presentation = Schema.resolvedSchemaPresentation schema
    unless (Schema.localSchemaId local == Schema.resolvedSchemaId schema
            && Schema.localPresentation local == Schema.resolvedPresentationLocal presentation)
        (Left "structure wire input and registration belong to different local schemas")
    pure (StructureInterfaceWire
        input{Schema.localWireParents = List.sort (Schema.localWireParents input)}
        (StructurePredicate.pendingStructurePredicate registration) laws resources
        (freezeStructurePresentation (Schema.localPresentation local))
        (Schema.resolvedPresentationParentOrder presentation)
        (Schema.resolvedPresentationFieldOrder presentation))

structureWireSlot :: StructureInterfaceWire -> StructureSlot
structureWireSlot (StructureInterfaceWire input _ _ _ _ _ _) = Schema.localWireSlot input

-- Presentation supplies the written order; the canonical input supplies the
-- exact parent applications. Neither can silently drop or invent an edge.
structureWireLocalInput :: StructureInterfaceWire -> Either Text Schema.LocalStructureSchemaWire
structureWireLocalInput (StructureInterfaceWire input _ _ _ _ parentOrder _) = do
    unless (Schema.localWireParents input == List.sort parentOrder)
        (Left "structure wire parent presentation is not a permutation of its canonical input")
    pure input{Schema.localWireParents = parentOrder}

structureWirePredicate :: StructureInterfaceWire -> ObjectId
structureWirePredicate (StructureInterfaceWire _ predicate _ _ _ _ _) = predicate

structureWireLawIndex :: StructureInterfaceWire -> Map Schema.GeneratedStructureLawKey SemanticFactOccurrenceFingerprint
structureWireLawIndex (StructureInterfaceWire _ _ laws _ _ _ _) = laws

structureWireResourceIndex :: StructureInterfaceWire -> Map Schema.StructureResourceKey SemanticFactOccurrenceFingerprint
structureWireResourceIndex (StructureInterfaceWire _ _ _ resources _ _ _) = resources

structureWirePresentationMatches :: StructureInterfaceWire -> Schema.ResolvedStructureSchema -> Bool
structureWirePresentationMatches (StructureInterfaceWire _ _ _ _ local parents fields) schema =
    local == freezeStructurePresentation (Schema.resolvedPresentationLocal presentation)
        && parents == Schema.resolvedPresentationParentOrder presentation
        && fields == Schema.resolvedPresentationFieldOrder presentation
  where
    presentation = Schema.resolvedSchemaPresentation schema

freezeStructurePresentation :: Schema.StructurePresentation -> StructurePresentationWire
freezeStructurePresentation presentation = StructurePresentationWire
    (Schema.structurePresentationPhrase presentation)
    (freezeStructurePosition (Schema.structurePresentationLocation presentation))
    (Schema.structurePresentationParameters presentation)
    (fmap (fmap freezeStructurePosition) (Schema.structurePresentationParents presentation))
    (freezeStructurePosition <$> Schema.structurePresentationPreamble presentation)
    (fmap (fmap freezeStructurePosition) (Schema.structurePresentationFields presentation))
    (fmap (fmap freezeStructurePosition) (Schema.structurePresentationLaws presentation))

freezeStructurePosition :: Location.Location -> StructureSourcePosition
freezeStructurePosition location = case Location.locSourceDescriptor location of
    Nothing -> StructurePositionUnknown
    Just file -> StructurePosition
        (Text.pack (fromMaybe (Location.locFile location) (Location.sourceDescriptorIdentityPath file)))
        (Text.pack (Location.locFile location))
        (fromIntegral (Location.locLine location)) (fromIntegral (Location.locColumn location))

-- Runtime descriptors are never serialized. Restoring diagnostic provenance
-- performs no filesystem access and grants no object or proof authority.
materializeStructureWirePresentation :: StructureInterfaceWire -> Either Text Schema.StructurePresentation
materializeStructureWirePresentation (StructureInterfaceWire _ _ _ _
        (StructurePresentationWire structurePhrase location parameters parents preamble fields laws) _ _) = flip State.evalStateT Map.empty do
    Schema.StructurePresentation structurePhrase <$> restore location <*> pure parameters
        <*> traverse (traverse restore) parents <*> traverse restore preamble
        <*> traverse (traverse restore) fields <*> traverse (traverse restore) laws
  where
    restore StructurePositionUnknown = pure Location.Nowhere
    restore (StructurePosition identity display line column) = do
        State.lift do
            unless (line <= 0xffffff && column <= 0xffffff)
                (Left "structure source position exceeds the supported coordinate range")
        -- This restoration owns sharing; locations retain only their descriptor.
        existing <- State.gets (Map.lookup (identity, display))
        file <- case existing of
            Just descriptor -> pure descriptor
            Nothing -> do
                let descriptor = Location.sourceDescriptor (Text.unpack identity) (Text.unpack display)
                State.modify' (Map.insert (identity, display) descriptor)
                pure descriptor
        State.lift
            (first (Text.pack . show)
                (Location.mkLocationChecked file (fromIntegral line) (fromIntegral column)))

putStructureInterfaceWireCache :: StructureInterfaceWire -> CachePut
putStructureInterfaceWireCache (StructureInterfaceWire input predicate laws resources presentation parents fields) = do
    putLocalStructureSchemaWireCache input
    putObjectIdCache predicate
    putCanonicalCacheMap putStructureLawKeyCache putSemanticFactOccurrenceFingerprintCache laws
    putCanonicalCacheMap putStructureResourceKeyCache putSemanticFactOccurrenceFingerprintCache resources
    putStructurePresentationWireCache presentation
    putCacheList putStructureApplicationKeyCache parents
    putCacheList putFieldIdCache fields

getStructureInterfaceWireCache :: CacheGet StructureInterfaceWire
getStructureInterfaceWireCache = StructureInterfaceWire
    <$> getLocalStructureSchemaWireCache <*> getObjectIdCache
    <*> getCanonicalCacheMap getStructureLawKeyCache getSemanticFactOccurrenceFingerprintCache
    <*> getCanonicalCacheMap getStructureResourceKeyCache getSemanticFactOccurrenceFingerprintCache
    <*> getStructurePresentationWireCache <*> getCacheList getStructureApplicationKeyCache
    <*> getCacheList getFieldIdCache

putLocalStructureSchemaWireCache :: Schema.LocalStructureSchemaWire -> CachePut
putLocalStructureSchemaWireCache input = do
    putCacheNatural (structureSlotValue (Schema.localWireSlot input))
    putCacheList (\(Schema.LocalParameterOrdinal ordinal) -> putCacheNatural ordinal) (Schema.localWireParameters input)
    putCacheList (\(Schema.LocalPreambleWire key prefix body) ->
        putPreambleKey key >> putCacheNatural prefix >> putCanonicalTermCache putObjectIdCache body)
        (Schema.localWirePreamble input)
    putCacheList putStructureApplicationKeyCache (Schema.localWireParents input)
    putCacheList (\(Schema.LocalStructureFieldWire slot (StructSymbol symbol) specification) -> do
        putCacheNatural (structureFieldSlotValue slot)
        putCacheText symbol
        putCacheMaybe (putCanonicalTermCache putObjectIdCache) specification) (Schema.localWireFields input)
    putCacheList (\(Schema.LocalLawOrdinal ordinal, body) ->
        putCacheNatural ordinal >> putCanonicalTermCache putObjectIdCache body) (Schema.localWireLaws input)

getLocalStructureSchemaWireCache :: CacheGet Schema.LocalStructureSchemaWire
getLocalStructureSchemaWireCache = Schema.LocalStructureSchemaWire
    <$> (structureSlot <$> getCacheNatural)
    <*> getCacheList (Schema.LocalParameterOrdinal <$> getCacheNatural)
    <*> getCacheList (Schema.LocalPreambleWire <$> getPreambleKey <*> getCacheNatural <*> getCanonicalTermCache getObjectIdCache)
    <*> getCacheList getStructureApplicationKeyCache
    <*> getCacheList (Schema.LocalStructureFieldWire <$> (structureFieldSlot <$> getCacheNatural)
        <*> (StructSymbol <$> getCacheText) <*> getCacheMaybe (getCanonicalTermCache getObjectIdCache))
    <*> getCacheList ((,) <$> (Schema.LocalLawOrdinal <$> getCacheNatural) <*> getCanonicalTermCache getObjectIdCache)

putPreambleKey :: Schema.LocalPreambleClauseKey -> CachePut
putPreambleKey (Schema.LocalPreambleClauseKey item row) = putCacheNatural item >> putCacheNatural row

getPreambleKey :: CacheGet Schema.LocalPreambleClauseKey
getPreambleKey = Schema.LocalPreambleClauseKey <$> getCacheNatural <*> getCacheNatural

putStructurePresentationWireCache :: StructurePresentationWire -> CachePut
putStructurePresentationWireCache (StructurePresentationWire structurePhrase location parameters parents preamble fields laws) = do
    putStructurePhraseCache structurePhrase
    putStructurePositionCache location
    putCacheList putParameter parameters
    putCacheList (\(marker, position) -> putCacheMaybe putMarker marker >> putStructurePositionCache position) parents
    putCanonicalCacheMap putPreambleKey putStructurePositionCache preamble
    putCanonicalCacheMap (putCacheNatural . structureFieldSlotValue)
        (\(marker, position) -> putCacheMaybe putMarker marker >> putStructurePositionCache position) fields
    putCanonicalCacheMap (\(Schema.LocalLawOrdinal ordinal) -> putCacheNatural ordinal)
        (\(marker, position) -> putMarker marker >> putStructurePositionCache position) laws
  where
    putMarker (Marker marker) = putCacheText marker
    putParameter = \case
        NamedVar name -> putCacheTag 0 >> putCacheText name
        FreshVar index -> putCacheTag 1 >> putCacheInteger (fromIntegral index)

getStructurePresentationWireCache :: CacheGet StructurePresentationWire
getStructurePresentationWireCache = StructurePresentationWire
    <$> getStructurePhraseCache <*> getStructurePositionCache <*> getCacheList getParameter
    <*> getCacheList ((,) <$> getCacheMaybe getMarker <*> getStructurePositionCache)
    <*> getCanonicalCacheMap getPreambleKey getStructurePositionCache
    <*> getCanonicalCacheMap (structureFieldSlot <$> getCacheNatural)
        ((,) <$> getCacheMaybe getMarker <*> getStructurePositionCache)
    <*> getCanonicalCacheMap (Schema.LocalLawOrdinal <$> getCacheNatural)
        ((,) <$> getMarker <*> getStructurePositionCache)
  where
    getMarker = Marker <$> getCacheText
    getParameter = getCacheTag >>= \case
        0 -> NamedVar <$> getCacheText
        1 -> do
            index <- getCacheInteger
            unless (index >= fromIntegral (minBound :: Int) && index <= fromIntegral (maxBound :: Int))
                (fail "structure parameter index exceeds Int range")
            pure (FreshVar (fromIntegral index))
        tag -> fail ("unknown structure parameter tag " <> show tag)

putStructurePositionCache :: StructureSourcePosition -> CachePut
putStructurePositionCache = \case
    StructurePositionUnknown -> putCacheTag 0
    StructurePosition identity display line column -> do
        putCacheTag 1
        putCacheText identity
        putCacheText display
        putCacheNatural line
        putCacheNatural column

getStructurePositionCache :: CacheGet StructureSourcePosition
getStructurePositionCache = getCacheTag >>= \case
    0 -> pure StructurePositionUnknown
    1 -> StructurePosition <$> getCacheText <*> getCacheText <*> getCacheNatural <*> getCacheNatural
    tag -> fail ("unknown structure source-position tag " <> show tag)
