{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Structure vocabulary shared by semantic metadata and schema checking.
module Felix.Checking.Structure.Schema
    ( StructurePhrase
    , structurePhrase
    , structurePhraseSingular
    , structurePhrasePlural
    , structurePhraseMarker
    , LocalPreambleClauseKey(..)
    , LocalParameterOrdinal(..)
    , LocalLawOrdinal(..)
    , StructureRole(..)
    , StructureApplicationKey
    , structureApplicationKey
    , structureApplicationId
    , structureApplicationArguments
    , RequirementBodyKey
    , requirementBodyKey
    , requirementBodyTerm
    , RequirementOrigin(..)
    , RequirementRole(..)
    , requirementRole
    , RequirementProvenanceKey(..)
    , PredicateComponentKey(..)
    , GeneratedStructureLawKey(..)
    , StructureLawId(..)
    , StructureResourceKey(..)
    , StructureFactKey(..)
    , generatedLawKeyBuilder
    , resourceKeyBuilder
    , requirementOriginBuilder
    , applicationKeyBuilder
    , LocalStructureSchemaWire(..)
    , LocalPreambleWire(..)
    , LocalStructureFieldWire(..)
    , StructurePresentation(..)
    , LocalStructureSchema
    , checkLocalStructureSchema
    , checkManifestLocalStructureSchema
    , LocalStructureSchemaError(..)
    , checkLocalSchemaVisibility
    , localSchemaId
    , localSchemaOrigin
    , localSchemaTheory
    , localSchemaObjectDependencies
    , localSchemaRole
    , localSchemaParameters
    , localSchemaPreambleRequirements
    , localSchemaParents
    , localSchemaFields
    , localSchemaLaws
    , localSchemaPhrase
    , localPresentation
    , localSchemaWire
    , LocalPreambleRequirement
    , localPreambleClauseKey
    , localPreambleAvailablePrefix
    , localPreambleBody
    , LocalStructureField
    , localFieldSlot
    , localFieldIdentity
    , localFieldSymbol
    , localFieldSelector
    , localFieldProjection
    , localFieldSpecification
    , LocalParentApplication
    , ResolvedStructureSchema
    , StructureResolutionError(..)
    , resolveStructureBatch
    , resolvedSchemaOrigin
    , resolvedSchemaId
    , resolvedSchemaContentDigest
    , resolvedSchemaTheory
    , resolvedSchemaRole
    , resolvedSchemaRoot
    , resolvedSchemaParameters
    , resolvedSchemaParameterCount
    , resolvedSchemaDirectParents
    , resolvedSchemaAncestors
    , resolvedSchemaFields
    , resolvedSchemaFieldRoles
    , resolvedSchemaRequirements
    , resolvedSchemaPresentation
    , resolvedSchemaPhrase
    , resolvedSchemaSemanticFieldOrder
    , resolvedSchemaSemanticRequirementOrder
    , resolvedSchemaSemanticDirectParentOrder
    , resolvedSchemaSemanticAncestorOrder
    , ResolvedField
    , resolvedFieldIdentity
    , resolvedFieldOwner
    , resolvedFieldSlot
    , resolvedFieldSymbol
    , resolvedFieldSelector
    , resolvedFieldProjection
    , ResolvedPresentation
    , resolvedPresentationLocal
    , resolvedPresentationParentOrder
    , resolvedPresentationParentAliases
    , resolvedPresentationFieldOrder
    , ResolvedRequirement
    , resolvedRequirementBody
    , resolvedRequirementOccurrences
    , RequirementOccurrence
    , requirementOccurrenceLocation
    , requirementOccurrenceMarker
    , requirementIsAdmissibility
    , schemaSubject
    , schemaParameterArguments
    , selfApplicationKey
    , specializeStructureBody
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Math.Codec
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract
    ( LexicalItemSgPl(..), SgPl(..), Pattern(..), Marker(..), StructSymbol
    , pattern CarrierSymbol, VarSymbol
    )

import Control.DeepSeq (NFData(..))
import Control.Monad (foldM, unless, when)
import Data.List qualified as List
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set qualified as Set
import Data.ByteString (ByteString)
import Data.ByteString.Builder qualified as Builder
import Data.Word (Word8)
import Numeric.Natural (Natural)

data StructurePhrase = StructurePhrase
    !Pattern
    !Pattern
    !Marker
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

structurePhrase :: LexicalItemSgPl -> StructurePhrase
structurePhrase (LexicalItemSgPl forms marker) =
    StructurePhrase (sg forms) (pl forms) marker

structurePhraseSingular :: StructurePhrase -> Pattern
structurePhraseSingular (StructurePhrase singular _ _) =
    singular

structurePhrasePlural :: StructurePhrase -> Pattern
structurePhrasePlural (StructurePhrase _ plural _) =
    plural

structurePhraseMarker :: StructurePhrase -> Marker
structurePhraseMarker (StructurePhrase _ _ marker) =
    marker

-- Canonical coordinates are semantic provenance, not display metadata.
data LocalPreambleClauseKey = LocalPreambleClauseKey !Natural !Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

newtype LocalParameterOrdinal = LocalParameterOrdinal Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

newtype LocalLawOrdinal = LocalLawOrdinal Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data StructureRole = GeneralRecordRoot | OrdinaryStructure
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data StructureApplicationKey = StructureApplicationKey
    !StructureId ![CanonicalTerm ObjectId]
    Int [ByteString]

-- Count and encodings are shared, but remain lazy: an unequal structure ID
-- does not inspect argument tails, and an unequal count does not encode terms.
-- Only this constructor function pairs the logical key with its sort material.
-- Generic construction would let a caller provide inconsistent cached fields.

structureApplicationKey :: StructureId -> [CanonicalTerm ObjectId] -> StructureApplicationKey
structureApplicationKey identity arguments =
    StructureApplicationKey identity arguments (length arguments) (encodedTerm <$> arguments)

structureApplicationId :: StructureApplicationKey -> StructureId
structureApplicationId (StructureApplicationKey identity _ _ _) = identity

structureApplicationArguments :: StructureApplicationKey -> [CanonicalTerm ObjectId]
structureApplicationArguments (StructureApplicationKey _ arguments _ _) = arguments

instance Eq StructureApplicationKey where
    StructureApplicationKey leftId leftArgs _ _ == StructureApplicationKey rightId rightArgs _ _ =
        leftId == rightId && leftArgs == rightArgs

instance Ord StructureApplicationKey where
    compare (StructureApplicationKey leftId _ leftCount leftBytes)
            (StructureApplicationKey rightId _ rightCount rightBytes) =
        compare leftId rightId <> compare leftCount rightCount <> compare leftBytes rightBytes

instance Show StructureApplicationKey where
    showsPrec precedence (StructureApplicationKey identity arguments _ _) =
        showParen (precedence > 10)
            (showString "StructureApplicationKey " . showsPrec 11 identity
                . showChar ' ' . showsPrec 11 arguments)

-- Forcing a key retains its logical forcing contract, without turning an
-- unused comparison cache into an eager encoding pass.
instance NFData StructureApplicationKey where
    rnf (StructureApplicationKey identity arguments _ _) = rnf identity `seq` rnf arguments

data RequirementBodyKey = RequirementBodyKey !(CanonicalTerm ObjectId) ByteString

requirementBodyKey :: CanonicalTerm ObjectId -> RequirementBodyKey
requirementBodyKey body = RequirementBodyKey body (encodedTerm body)

requirementBodyTerm :: RequirementBodyKey -> CanonicalTerm ObjectId
requirementBodyTerm (RequirementBodyKey body _) = body

instance Eq RequirementBodyKey where
    RequirementBodyKey left _ == RequirementBodyKey right _ = left == right

instance Ord RequirementBodyKey where
    compare (RequirementBodyKey _ leftBytes) (RequirementBodyKey _ rightBytes) =
        compare leftBytes rightBytes

instance Show RequirementBodyKey where
    showsPrec precedence (RequirementBodyKey body _) =
        showParen (precedence > 10) (showString "RequirementBodyKey " . showsPrec 11 body)

instance NFData RequirementBodyKey where
    rnf (RequirementBodyKey body _) = rnf body

data RequirementOrigin
    = PreambleOrigin !StructureId !LocalPreambleClauseKey
    | FieldSpecificationOrigin !StructureId !FieldId
    | LawOrigin !StructureId !LocalLawOrdinal
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data RequirementRole = PreambleRequirement | FieldRequirement !FieldId | LawRequirement
    deriving stock (Show, Eq)

requirementRole :: RequirementOrigin -> RequirementRole
requirementRole = \case
    PreambleOrigin{} -> PreambleRequirement
    FieldSpecificationOrigin _ field -> FieldRequirement field
    LawOrigin{} -> LawRequirement

instance Ord RequirementOrigin where
    compare left right = compare (originTag left) (originTag right) <>
        case (left, right) of
            (PreambleOrigin a i, PreambleOrigin b j) -> compare (a, i) (b, j)
            (FieldSpecificationOrigin a i, FieldSpecificationOrigin b j) -> compare (a, i) (b, j)
            (LawOrigin a i, LawOrigin b j) -> compare (a, i) (b, j)
            _ -> EQ

originTag :: RequirementOrigin -> Word8
originTag = \case
    PreambleOrigin{} -> 0
    FieldSpecificationOrigin{} -> 1
    LawOrigin{} -> 2

requirementOriginBuilder :: RequirementOrigin -> Builder.Builder
requirementOriginBuilder = \case
    PreambleOrigin owner (LocalPreambleClauseKey item row) ->
        Builder.word8 0 <> structureIdentityBuilder owner
            <> compactNaturalBuilder item <> compactNaturalBuilder row
    FieldSpecificationOrigin owner field ->
        Builder.word8 1 <> structureIdentityBuilder owner <> fieldIdentityBuilder field
    LawOrigin owner (LocalLawOrdinal ordinal) ->
        Builder.word8 2 <> structureIdentityBuilder owner <> compactNaturalBuilder ordinal

data RequirementProvenanceKey = RequirementProvenanceKey
    { requirementOrigin :: !RequirementOrigin
    , requirementOwnerAtSite :: !StructureApplicationKey
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data PredicateComponentKey
    = PredicateShapeComponent
    | PredicateRequirementComponent !RequirementProvenanceKey
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord PredicateComponentKey where
    compare PredicateShapeComponent PredicateShapeComponent = EQ
    compare PredicateShapeComponent PredicateRequirementComponent{} = LT
    compare PredicateRequirementComponent{} PredicateShapeComponent = GT
    compare (PredicateRequirementComponent left) (PredicateRequirementComponent right) = compare left right

data GeneratedStructureLawKey
    = PredicateComponentLaw !PredicateComponentKey
    | ParentInheritanceLaw !StructureApplicationKey
    | RecordSchemaLaw !Record.RecordSchemaLaw
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord GeneratedStructureLawKey where
    compare left right = compare (lawKeyTag left) (lawKeyTag right) <>
        case (left, right) of
            (PredicateComponentLaw a, PredicateComponentLaw b) -> compare a b
            (ParentInheritanceLaw a, ParentInheritanceLaw b) -> compare a b
            (RecordSchemaLaw a, RecordSchemaLaw b) -> compare a b
            _ -> EQ

lawKeyTag :: GeneratedStructureLawKey -> Word8
lawKeyTag = \case
    PredicateComponentLaw{} -> 0
    ParentInheritanceLaw{} -> 1
    RecordSchemaLaw{} -> 2

data StructureLawId = StructureLawId !StructureId !GeneratedStructureLawKey
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data StructureResourceKey
    = PredicateDefinitionResource
    | SelectorDefinitionResource !FieldId
    | ProjectionMembershipResource !FieldId
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord StructureResourceKey where
    -- The wire order is tag 0/1/2, then the existing digest order for a field.
    compare PredicateDefinitionResource PredicateDefinitionResource = EQ
    compare PredicateDefinitionResource _ = LT
    compare _ PredicateDefinitionResource = GT
    compare (SelectorDefinitionResource left) (SelectorDefinitionResource right) = compare left right
    compare SelectorDefinitionResource{} ProjectionMembershipResource{} = LT
    compare ProjectionMembershipResource{} SelectorDefinitionResource{} = GT
    compare (ProjectionMembershipResource left) (ProjectionMembershipResource right) = compare left right

data StructureFactKey
    = StructureLawFact !GeneratedStructureLawKey
    | StructureResourceFact !StructureResourceKey
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord StructureFactKey where
    compare (StructureLawFact left) (StructureLawFact right) = compare left right
    compare StructureLawFact{} StructureResourceFact{} = LT
    compare StructureResourceFact{} StructureLawFact{} = GT
    compare (StructureResourceFact left) (StructureResourceFact right) = compare left right

generatedLawKeyBuilder :: GeneratedStructureLawKey -> Builder.Builder
generatedLawKeyBuilder = \case
    PredicateComponentLaw PredicateShapeComponent -> Builder.word8 0 <> Builder.word8 0
    PredicateComponentLaw (PredicateRequirementComponent (RequirementProvenanceKey origin owner)) ->
        Builder.word8 0 <> Builder.word8 1 <> requirementOriginBuilder origin <> applicationKeyBuilder owner
    ParentInheritanceLaw application -> Builder.word8 1 <> applicationKeyBuilder application
    RecordSchemaLaw law -> Builder.word8 2 <> Record.recordSchemaLawBuilder law

resourceKeyBuilder :: StructureResourceKey -> Builder.Builder
resourceKeyBuilder = \case
    PredicateDefinitionResource -> Builder.word8 0
    SelectorDefinitionResource field -> Builder.word8 1 <> fieldIdentityBuilder field
    ProjectionMembershipResource field -> Builder.word8 2 <> fieldIdentityBuilder field

applicationKeyBuilder :: StructureApplicationKey -> Builder.Builder
applicationKeyBuilder (StructureApplicationKey identity arguments _ _) =
    structureIdentityBuilder identity <> compactSequenceBuilder (canonicalTermBuilder objectIdBuilder) arguments

structureIdentityBuilder :: StructureId -> Builder.Builder
structureIdentityBuilder = Builder.byteString . mathematicalDigestBytes . structureIdDigest

fieldIdentityBuilder :: FieldId -> Builder.Builder
fieldIdentityBuilder = Builder.byteString . mathematicalDigestBytes . fieldIdDigest

encodedTerm :: CanonicalTerm ObjectId -> ByteString
encodedTerm = encodeCanonicalTerm objectIdBuilder

-- | Raw declaration-local input. Checked schemas retain scoped evidence;
-- persistence stores these claims and reconstructs it at local admission.
data LocalStructureSchemaWire = LocalStructureSchemaWire
    { localWireSlot :: !StructureSlot
    , localWireParameters :: ![LocalParameterOrdinal]
    , localWirePreamble :: ![LocalPreambleWire]
    , localWireParents :: ![StructureApplicationKey]
    , localWireFields :: ![LocalStructureFieldWire]
    , localWireLaws :: ![(LocalLawOrdinal, CanonicalTerm ObjectId)]
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data LocalPreambleWire = LocalPreambleWire
    !LocalPreambleClauseKey !Natural !(CanonicalTerm ObjectId)
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data LocalStructureFieldWire = LocalStructureFieldWire
    !StructureFieldSlot !StructSymbol !(Maybe (CanonicalTerm ObjectId))
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

-- Locations and names never participate in normalized mathematical keys.
data StructurePresentation = StructurePresentation
    { structurePresentationPhrase :: !StructurePhrase
    , structurePresentationLocation :: !Location
    , structurePresentationParameters :: ![VarSymbol]
    , structurePresentationParents :: ![(Maybe Marker, Location)]
    , structurePresentationPreamble :: !(Map LocalPreambleClauseKey Location)
    , structurePresentationFields :: !(Map StructureFieldSlot (Maybe Marker, Location))
    , structurePresentationLaws :: !(Map LocalLawOrdinal (Marker, Location))
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data LocalPreambleRequirement = LocalPreambleRequirement
    { internalLocalPreambleClauseKey :: !LocalPreambleClauseKey
    , internalLocalPreambleAvailablePrefix :: !Natural
    , internalLocalPreambleBody :: !(ScopedCheckedCore ObjectId)
    }
    deriving stock (Show, Eq)

data LocalStructureField = LocalStructureField
    { internalLocalFieldSlot :: !StructureFieldSlot
    , internalLocalFieldIdentity :: !FieldId
    , internalLocalFieldSymbol :: !StructSymbol
    , internalLocalFieldSelector :: !ObjectId
    , internalLocalFieldProjection :: !ObjectId
    , internalLocalFieldSpecification :: !(Maybe (ScopedCheckedCore ObjectId))
    }
    deriving stock (Show, Eq)

data LocalParentApplication = LocalParentApplication
    !StructureId ![ScopedCheckedCore ObjectId]
    deriving stock (Show, Eq)

data LocalStructureSchema = LocalStructureSchema
    { internalLocalSchemaOrigin :: !StructureOrigin
    , internalLocalSchemaTheory :: !TheoryId
    , internalLocalSchemaObjectDependencies :: !(Set ObjectId)
    , internalLocalSchemaRole :: !StructureRole
    , internalLocalSchemaParameters :: ![LocalParameterOrdinal]
    , internalLocalSchemaPreambleRequirements :: ![LocalPreambleRequirement]
    , internalLocalSchemaParents :: ![LocalParentApplication]
    , internalLocalSchemaFields :: ![LocalStructureField]
    , internalLocalSchemaLaws :: ![(LocalLawOrdinal, ScopedCheckedCore ObjectId)]
    , internalLocalPresentation :: !StructurePresentation
    }
    deriving stock (Show, Eq)

localSchemaId :: LocalStructureSchema -> StructureId
localSchemaId = structureId . internalLocalSchemaOrigin

localSchemaPhrase :: LocalStructureSchema -> StructurePhrase
localSchemaPhrase = structurePresentationPhrase . internalLocalPresentation

localSchemaWire :: LocalStructureSchema -> LocalStructureSchemaWire
localSchemaWire schema = LocalStructureSchemaWire
    { localWireSlot = structureOriginSlot (internalLocalSchemaOrigin schema)
    , localWireParameters = internalLocalSchemaParameters schema
    , localWirePreamble =
        [ LocalPreambleWire key prefix (scopedCoreTerm body)
        | LocalPreambleRequirement key prefix body <- internalLocalSchemaPreambleRequirements schema
        ]
    , localWireParents =
        [ structureApplicationKey parent (scopedCoreTerm <$> arguments)
        | LocalParentApplication parent arguments <- internalLocalSchemaParents schema
        ]
    , localWireFields =
        [ LocalStructureFieldWire (internalLocalFieldSlot field) (internalLocalFieldSymbol field)
            (scopedCoreTerm <$> internalLocalFieldSpecification field)
        | field <- internalLocalSchemaFields schema
        ]
    , localWireLaws = fmap scopedCoreTerm <$> internalLocalSchemaLaws schema
    }

data LocalStructureSchemaError
    = LocalStructureSlotMismatch !StructureSlot !StructureSlot
    | LocalStructureCoordinatesInvalid !Text
    | LocalStructurePhraseArityMismatch !Natural !Natural
    | LocalStructurePreamblePrefixInvalid !LocalPreambleClauseKey !Natural !Natural
    | LocalStructureTermInvalid !Text !CoreCheckError
    | LocalStructureTermTypeMismatch !Text !CoreType !CoreType
    | LocalStructureResourceMissing !ObjectId
    | LocalStructureReservedCarrier !StructureFieldSlot
    | LocalStructureManifestInvalid !Text
    | LocalStructureTheoryMismatch !TheoryId !TheoryId
    deriving stock (Show, Eq)

checkLocalStructureSchema
    :: CheckedObjectClosure -> StructureOrigin -> LocalStructureSchemaWire
    -> StructurePresentation -> Either LocalStructureSchemaError LocalStructureSchema
checkLocalStructureSchema = checkLocalSchema OrdinarySchemaPolicy

-- | The reserved manifest's construction seam. Only the reserved prelude's
-- two canonical local shapes can pass it; declaration admission additionally
-- checks that this is the compiler-owned manifest declaration.
checkManifestLocalStructureSchema
    :: CheckedObjectClosure -> StructureOrigin -> StructureRole
    -> LocalStructureSchemaWire -> StructurePresentation
    -> Either LocalStructureSchemaError LocalStructureSchema
checkManifestLocalStructureSchema closure origin role wire presentation = do
    unless (structureOriginModule origin == preludeModuleName)
        (Left (LocalStructureManifestInvalid "the manifest belongs to the reserved prelude"))
    let rootOrigin = origin { structureOriginSlot = structureSlot 0 }
        parent = structureApplicationKey (structureId rootOrigin) []
        emptyClauses = null (localWireParameters wire)
            && null (localWirePreamble wire) && null (localWireLaws wire)
        valid = emptyClauses && case role of
            GeneralRecordRoot -> structureOriginSlot origin == structureSlot 0
                && null (localWireParents wire) && null (localWireFields wire)
            OrdinaryStructure -> structureOriginSlot origin == structureSlot 1
                && localWireParents wire == [parent]
                && localWireFields wire == [LocalStructureFieldWire (structureFieldSlot 0) CarrierSymbol Nothing]
    unless valid (Left (LocalStructureManifestInvalid "the manifest local shape differs from its specification"))
    checkLocalSchema (ManifestSchemaPolicy role) closure origin wire presentation

data LocalSchemaPolicy = OrdinarySchemaPolicy | ManifestSchemaPolicy StructureRole

checkLocalSchema
    :: LocalSchemaPolicy -> CheckedObjectClosure -> StructureOrigin
    -> LocalStructureSchemaWire -> StructurePresentation
    -> Either LocalStructureSchemaError LocalStructureSchema
checkLocalSchema policy closure origin wire presentation = do
    unless (structureOriginSlot origin == localWireSlot wire)
        (Left (LocalStructureSlotMismatch (structureOriginSlot origin) (localWireSlot wire)))
    requireCoordinates "parameter telescope"
        (localWireParameters wire == [LocalParameterOrdinal i | i <- ordinals parameterCount])
    let phraseArity = patternArity (structurePhraseSingular (structurePresentationPhrase presentation))
    unless (phraseArity == parameterCount)
        (Left (LocalStructurePhraseArityMismatch parameterCount phraseArity))
    requireCoordinates "plural phrase arity"
        (patternArity (structurePhrasePlural (structurePresentationPhrase presentation)) == parameterCount)
    requireCoordinates "parameter presentation"
        (length (structurePresentationParameters presentation) == length (localWireParameters wire))
    requireCoordinates "parent presentation"
        (length (structurePresentationParents presentation) == length (localWireParents wire))
    requireCoordinates "preamble order" (strictlyIncreasing preambleKeys)
    requireCoordinates "preamble row ordinals"
        (all validPreambleItem
            (List.groupBy ((==) `on` preambleItem) (localWirePreamble wire)))
    requireCoordinates "preamble prefix order"
        (and (zipWith (<=) preamblePrefixes (drop 1 preamblePrefixes)))
    requireCoordinates "preamble presentation"
        (Map.keysSet (structurePresentationPreamble presentation) == Set.fromList preambleKeys)
    requireCoordinates "field order" (strictlyIncreasing fieldSlots)
    requireCoordinates "field presentation"
        (Map.keysSet (structurePresentationFields presentation) == Set.fromList fieldSlots)
    requireCoordinates "field roles" (isNothing (firstDuplicate fieldSymbols))
    requireCoordinates "law ordinals"
        (lawOrdinals == [LocalLawOrdinal i | i <- ordinals (fromIntegral (length lawOrdinals))])
    requireCoordinates "law presentation"
        (Map.keysSet (structurePresentationLaws presentation) == Set.fromList lawOrdinals)
    preamble <- traverse checkPreamble (localWirePreamble wire)
    parents <- traverse checkParent (localWireParents wire)
    fields <- traverse checkField (localWireFields wire)
    laws <- traverse (\(ordinal, body) -> (,) ordinal <$> checkTerm "local law" fullContext TyProp body)
        (localWireLaws wire)
    let terms = (internalLocalPreambleBody <$> preamble)
            <> [argument | LocalParentApplication _ arguments <- parents, argument <- arguments]
            <> mapMaybe internalLocalFieldSpecification fields <> (snd <$> laws)
        resources = concatMap (\field -> [internalLocalFieldSelector field, internalLocalFieldProjection field]) fields
        dependencies = Set.fromList resources <> foldMap (canonicalTermGlobals . scopedCoreTerm) terms
    pure LocalStructureSchema
        { internalLocalSchemaOrigin = origin
        , internalLocalSchemaTheory = theory
        , internalLocalSchemaObjectDependencies = dependencies
        , internalLocalSchemaRole = role
        , internalLocalSchemaParameters = localWireParameters wire
        , internalLocalSchemaPreambleRequirements = preamble
        , internalLocalSchemaParents = parents
        , internalLocalSchemaFields = fields
        , internalLocalSchemaLaws = laws
        , internalLocalPresentation = presentation
        }
  where
    role = case policy of
        OrdinarySchemaPolicy -> OrdinaryStructure
        ManifestSchemaPolicy manifestRole -> manifestRole
    theory = checkedObjectClosureTheory closure
    parameterCount = fromIntegral (length (localWireParameters wire))
    fullContext = replicate (length (localWireParameters wire) + 1) TySet
    preambleKeys = [key | LocalPreambleWire key _ _ <- localWirePreamble wire]
    preamblePrefixes = [prefix | LocalPreambleWire _ prefix _ <- localWirePreamble wire]
    preambleItem (LocalPreambleWire (LocalPreambleClauseKey item _) _ _) = item
    validPreambleItem rows =
        [row | LocalPreambleWire (LocalPreambleClauseKey _ row) _ _ <- rows]
            == ordinals (fromIntegral (length rows))
        && length (nubOrd [prefix | LocalPreambleWire _ prefix _ <- rows]) == 1
    fieldSlots = [slot | LocalStructureFieldWire slot _ _ <- localWireFields wire]
    fieldSymbols = [symbol | LocalStructureFieldWire _ symbol _ <- localWireFields wire]
    lawOrdinals = fst <$> localWireLaws wire
    requireCoordinates label valid = unless valid (Left (LocalStructureCoordinatesInvalid label))
    checkTerm label context expected body = do
        checked <- first (LocalStructureTermInvalid label)
            (checkScopedCanonicalCore (globalTypingFromClosure closure) context body)
        unless (scopedCoreType checked == expected)
            (Left (LocalStructureTermTypeMismatch label expected (scopedCoreType checked)))
        pure checked
    checkPreamble (LocalPreambleWire key available body) = do
        unless (available <= parameterCount)
            (Left (LocalStructurePreamblePrefixInvalid key available parameterCount))
        checked <- checkTerm "preamble requirement" (replicate (fromIntegral available) TySet) TyProp body
        pure (LocalPreambleRequirement key available checked)
    checkParent (StructureApplicationKey parent arguments _ _) =
        LocalParentApplication parent <$> traverse (checkTerm "parent argument" fullContext TySet) arguments
    checkField (LocalStructureFieldWire slot symbol specification) = do
        case policy of
            OrdinarySchemaPolicy -> when (symbol == CarrierSymbol)
                (Left (LocalStructureReservedCarrier slot))
            ManifestSchemaPolicy _ -> pure ()
        let identity = fieldId (structureOriginModule origin) (structureOriginDeclaration origin) slot
            selector = Record.fieldSelectorObjectId theory identity
            projection = Record.fieldProjectionObjectId theory identity
        traverse_ (\object -> unless (checkedObjectMember object closure)
            (Left (LocalStructureResourceMissing object))) [selector, projection]
        checked <- traverse (checkTerm "field specification" fullContext TyProp) specification
        pure (LocalStructureField slot identity symbol selector projection checked)

-- | Typing is stable for content-addressed objects in one theory. Visibility
-- is checked again against the exact declaration closure at each admission.
checkLocalSchemaVisibility
    :: CheckedObjectClosure -> LocalStructureSchema -> Either LocalStructureSchemaError ()
checkLocalSchemaVisibility closure schema = do
    unless (checkedObjectClosureTheory closure == internalLocalSchemaTheory schema)
        (Left (LocalStructureTheoryMismatch (internalLocalSchemaTheory schema) (checkedObjectClosureTheory closure)))
    traverse_ (\object -> unless (checkedObjectMember object closure)
        (Left (LocalStructureResourceMissing object))) (internalLocalSchemaObjectDependencies schema)

patternArity :: Pattern -> Natural
patternArity = \case
    End -> 0
    HoleCons rest -> 1 + patternArity rest
    TokenCons _ rest -> patternArity rest

ordinals :: Natural -> [Natural]
ordinals 0 = []
ordinals count = [0 .. count - 1]

strictlyIncreasing :: Ord value => [value] -> Bool
strictlyIncreasing values = and (zipWith (<) values (drop 1 values))

-- The private constructors certify normalization. Parent and provenance keys
-- are shallow applications; no schema retains an environment or parent schema.
data ResolvedField = ResolvedField
    { internalResolvedFieldIdentity :: !FieldId
    , internalResolvedFieldOwner :: !StructureId
    , internalResolvedFieldSlot :: !StructureFieldSlot
    , internalResolvedFieldSymbol :: !StructSymbol
    , internalResolvedFieldSelector :: !ObjectId
    , internalResolvedFieldProjection :: !ObjectId
    }
    deriving stock (Show, Eq)

data RequirementOccurrence = RequirementOccurrence
    { internalRequirementOccurrenceLocation :: !Location
    , internalRequirementOccurrenceMarker :: !(Maybe Marker)
    }
    deriving stock (Show, Eq)

data ResolvedRequirement = ResolvedRequirement
    { internalResolvedRequirementBody :: !(CanonicalTerm ObjectId)
    , internalResolvedRequirementOccurrences :: !(Map RequirementProvenanceKey RequirementOccurrence)
    }
    deriving stock (Show, Eq)

data ResolvedPresentation = ResolvedPresentation
    { internalResolvedPresentationLocal :: !StructurePresentation
    , internalResolvedPresentationParentOrder :: ![StructureApplicationKey]
    , internalResolvedPresentationFieldOrder :: ![FieldId]
    , internalResolvedPresentationAncestorMarkers :: !(Map StructureId Marker)
    , internalResolvedPresentationParentAliases :: !(Map StructureApplicationKey [Marker])
    }
    deriving stock (Show, Eq)

data ResolvedStructureSchema = ResolvedStructureSchema
    { internalResolvedSchemaOrigin :: !StructureOrigin
    , internalResolvedSchemaTheory :: !TheoryId
    , internalResolvedSchemaRole :: !StructureRole
    , internalResolvedSchemaRoot :: !StructureId
    , internalResolvedSchemaParameters :: ![LocalParameterOrdinal]
    , internalResolvedSchemaDirectParents :: !(Set StructureApplicationKey)
    , internalResolvedSchemaAncestors :: !(Set StructureApplicationKey)
    , internalResolvedSchemaFields :: !(Map FieldId ResolvedField)
    , internalResolvedSchemaFieldRoles :: !(Map StructSymbol FieldId)
    , internalResolvedSchemaRequirements :: !(Map RequirementBodyKey ResolvedRequirement)
    , internalResolvedSchemaPresentation :: !ResolvedPresentation
    }
    deriving stock (Show, Eq)

resolvedSchemaId :: ResolvedStructureSchema -> StructureId
resolvedSchemaId = structureId . internalResolvedSchemaOrigin

-- Mathematical content excludes lexical labels and written parent order.
-- Provenance remains semantic: distinct reasons for a coalesced requirement
-- retain their own component-law identities.
resolvedSchemaContentDigest :: ResolvedStructureSchema -> MathematicalDigest
resolvedSchemaContentDigest schema = hashIdentityBuilder StructureSchemaContentIdentity
    (Builder.byteString (mathematicalDigestBytes (theoryIdDigest (resolvedSchemaTheory schema)))
        <> structureIdentityBuilder (resolvedSchemaId schema)
        <> structureIdentityBuilder (resolvedSchemaRoot schema)
        <> Builder.word8 (case resolvedSchemaRole schema of GeneralRecordRoot -> 0; OrdinaryStructure -> 1)
        <> compactSequenceBuilder (\(LocalParameterOrdinal ordinal) -> compactNaturalBuilder ordinal) (resolvedSchemaParameters schema)
        <> compactSequenceBuilder applicationKeyBuilder (resolvedSchemaSemanticDirectParentOrder schema)
        <> compactSequenceBuilder applicationKeyBuilder (resolvedSchemaSemanticAncestorOrder schema)
        <> compactSequenceBuilder fieldBuilder (Map.elems (resolvedSchemaFields schema))
        <> compactSequenceBuilder requirementBuilder (Map.elems (resolvedSchemaRequirements schema)))
  where
    fieldBuilder field = fieldIdentityBuilder (resolvedFieldIdentity field)
        <> structureIdentityBuilder (resolvedFieldOwner field)
        <> objectIdBuilder (resolvedFieldSelector field) <> objectIdBuilder (resolvedFieldProjection field)
    requirementBuilder requirement = canonicalTermBuilder objectIdBuilder (resolvedRequirementBody requirement)
        <> compactSequenceBuilder (\(RequirementProvenanceKey origin owner) ->
            requirementOriginBuilder origin <> applicationKeyBuilder owner)
            (Map.keys (resolvedRequirementOccurrences requirement))

resolvedSchemaPhrase :: ResolvedStructureSchema -> StructurePhrase
resolvedSchemaPhrase = structurePresentationPhrase . internalResolvedPresentationLocal . internalResolvedSchemaPresentation

resolvedSchemaParameterCount :: ResolvedStructureSchema -> Natural
resolvedSchemaParameterCount = fromIntegral . length . internalResolvedSchemaParameters

-- The subject is the first binder in declared order and the outermost bound
-- index. Parameter ordinals run in declared telescope order after it.
schemaSubject :: Natural -> CanonicalTerm ObjectId
schemaSubject = CBound

schemaParameterArguments :: Natural -> [CanonicalTerm ObjectId]
schemaParameterArguments count = [CBound (count - ordinal - 1) | ordinal <- ordinals count]

selfApplicationKey :: ResolvedStructureSchema -> StructureApplicationKey
selfApplicationKey schema = structureApplicationKey (resolvedSchemaId schema)
    (schemaParameterArguments (resolvedSchemaParameterCount schema))

resolvedSchemaSemanticFieldOrder :: ResolvedStructureSchema -> [FieldId]
resolvedSchemaSemanticFieldOrder = Map.keys . internalResolvedSchemaFields

resolvedSchemaSemanticRequirementOrder :: ResolvedStructureSchema -> [RequirementBodyKey]
resolvedSchemaSemanticRequirementOrder schema =
    [key | (key, requirement) <- rows, requirementIsAdmissibility requirement]
        <> [key | (key, requirement) <- rows, not (requirementIsAdmissibility requirement)]
  where
    rows = Map.toAscList (internalResolvedSchemaRequirements schema)

resolvedSchemaSemanticDirectParentOrder :: ResolvedStructureSchema -> [StructureApplicationKey]
resolvedSchemaSemanticDirectParentOrder = Set.toAscList . internalResolvedSchemaDirectParents

resolvedSchemaSemanticAncestorOrder :: ResolvedStructureSchema -> [StructureApplicationKey]
resolvedSchemaSemanticAncestorOrder = Set.toAscList . internalResolvedSchemaAncestors

requirementIsAdmissibility :: ResolvedRequirement -> Bool
requirementIsAdmissibility = any isPreamble . Map.keys . internalResolvedRequirementOccurrences
  where
    isPreamble key = case requirementOrigin key of
        PreambleOrigin{} -> True
        FieldSpecificationOrigin{} -> False
        LawOrigin{} -> False

-- | Capture-avoiding specialization of a checked parent's complete context.
-- Lambda instantiation supplies the shared child subject followed by parent
-- arguments in declared order, including arguments with their own binders.
specializeStructureBody
    :: Natural -> [CanonicalTerm ObjectId] -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
specializeStructureBody childParameters arguments body =
    foldl' apply template (schemaSubject childParameters : arguments)
  where
    template = foldr (const (CLam TySet)) body (() : map (const ()) arguments)
    apply (CLam TySet inner) argument = instantiateCanonical argument inner
    apply _ _ = impossible "checked structure substitution lost a telescope binder"

data StructureResolutionError
    = StructureParentLabelRequired !Marker !Marker !StructureApplicationKey
    | StructureParentAliasConflict !Marker !StructureApplicationKey !StructureApplicationKey
    | StructureBatchOwnerMismatch !StructureOrigin !StructureOrigin
    | StructureBatchTheoryMismatch !TheoryId !TheoryId
    | StructureBatchDuplicateIdentity !StructureId
    | StructureBatchIdentityAlreadyVisible !StructureId
    | StructureBatchFieldSlotsInvalid ![StructureFieldSlot]
    | StructureParentMissing !StructureId !StructureId
    | StructureParentArityMismatch !StructureId !StructureId !Natural !Natural
    | StructureDuplicateParent !StructureId !StructureApplicationKey
    | StructureCycle ![StructureId]
    | StructureRootMissing !StructureId
    | StructureRootConflict !StructureId !(Set StructureId)
    | StructureFieldRoleConflict !StructSymbol !FieldId !FieldId
    | StructureFieldIdentityConflict !FieldId
    | StructureRequirementConflict !RequirementProvenanceKey
    deriving stock (Show, Eq)

resolveStructureBatch
    :: (StructureId -> Maybe ResolvedStructureSchema)
    -> NonEmpty LocalStructureSchema
    -> Either StructureResolutionError (NonEmpty ResolvedStructureSchema)
resolveStructureBatch incoming inputs@(initial :| _) = do
    traverse_ checkBatchMember members
    case firstDuplicate (localSchemaId <$> members) of
        Just duplicate -> Left (StructureBatchDuplicateIdentity duplicate)
        Nothing -> pure ()
    traverse_ (\local -> when (isJust (incoming (localSchemaId local)))
        (Left (StructureBatchIdentityAlreadyVisible (localSchemaId local)))) members
    unless (fieldSlots == [structureFieldSlot i | i <- ordinals (fromIntegral (length fieldSlots))])
        (Left (StructureBatchFieldSlotsInvalid fieldSlots))
    let pending = Map.fromList [(localSchemaId local, local) | local <- members]
    traverse_ (checkParents pending) members
    resolved <- go Map.empty pending []
    case reverse resolved of
        firstSchema : rest -> pure (firstSchema :| rest)
        [] -> impossible "a nonempty structure batch resolved to no schemas"
  where
    members = toList inputs
    initialOrigin = internalLocalSchemaOrigin initial
    initialTheory = internalLocalSchemaTheory initial
    fieldSlots = concatMap (map internalLocalFieldSlot . internalLocalSchemaFields)
        (List.sortOn (structureOriginSlot . internalLocalSchemaOrigin) members)
    checkBatchMember local = do
        let origin = internalLocalSchemaOrigin local
        unless (structureOriginModule origin == structureOriginModule initialOrigin
                && structureOriginDeclaration origin == structureOriginDeclaration initialOrigin)
            (Left (StructureBatchOwnerMismatch initialOrigin origin))
        unless (internalLocalSchemaTheory local == initialTheory)
            (Left (StructureBatchTheoryMismatch initialTheory (internalLocalSchemaTheory local)))
    checkParents pending local = do
        let applications = localWireParents (localSchemaWire local)
        case firstDuplicate applications of
            Just duplicate -> Left (StructureDuplicateParent (localSchemaId local) duplicate)
            Nothing -> pure ()
        traverse_ (\application ->
            let parent = structureApplicationId application
            in unless (Map.member parent pending || isJust (incoming parent))
                (Left (StructureParentMissing (localSchemaId local) parent))) applications
    go completed pending result
        | Map.null pending = pure result
        | otherwise = case
            [ (identity, local)
            | (identity, local) <- Map.toAscList pending
            , all (\(LocalParentApplication parent _) -> not (Map.member parent pending))
                (internalLocalSchemaParents local)
            ] of
            [] -> Left (StructureCycle (Map.keys pending))
            (identity, local) : _ -> do
                let lookupParent parent = Map.lookup parent completed <|> incoming parent
                schema <- resolveLocalSchema lookupParent local
                go (Map.insert identity schema completed) (Map.delete identity pending) (schema : result)

resolveLocalSchema
    :: (StructureId -> Maybe ResolvedStructureSchema) -> LocalStructureSchema
    -> Either StructureResolutionError ResolvedStructureSchema
resolveLocalSchema lookupParent local = do
    parents <- traverse resolveParent applications
    let roots = Set.fromList (internalResolvedSchemaRoot . snd <$> parents)
        canonicalParents = List.sortOn fst parents
    root <- case internalLocalSchemaRole local of
        GeneralRecordRoot -> pure identity
        OrdinaryStructure -> case Set.toList roots of
            [rootIdentity] -> pure rootIdentity
            [] -> Left (StructureRootMissing identity)
            _ -> Left (StructureRootConflict identity roots)
    let ancestors = Set.fromList
            (applications <> concatMap inheritedAncestors parents)
    when (any ((== identity) . structureApplicationId) ancestors)
        (Left (StructureCycle [identity]))
    (fields, roles) <- foldM insertField (Map.empty, Map.empty)
        (concatMap (Map.elems . internalResolvedSchemaFields . snd) canonicalParents <> ownFields)
    let inheritedRequirements = concatMap parentRequirements canonicalParents
    requirements <- foldM insertRequirement Map.empty (inheritedRequirements <> localRequirements)
    _ <- foldM checkProvenance Map.empty (Map.toAscList requirements)
    let fieldOrder = nubOrd
            (concatMap (internalResolvedPresentationFieldOrder . internalResolvedSchemaPresentation . snd) parents
                <> (internalResolvedFieldIdentity <$> ownFields))
    let ancestorMarkers = Map.unions
            [Map.insert (resolvedSchemaId parent) (structurePhraseMarker (resolvedSchemaPhrase parent))
                (internalResolvedPresentationAncestorMarkers (resolvedSchemaPresentation parent))
            | (_, parent) <- parents]
        markerFor application = fromMaybe (impossible "a resolved ancestor lost its source marker")
            (Map.lookup (structureApplicationId application) ancestorMarkers)
        byMarker = Map.fromListWith Set.union
            [(markerFor application, Set.singleton application) | application <- Set.toAscList ancestors]
        explicit = Map.fromListWith Set.union
            [(application, Set.singleton marker)
            | (application, (Just marker, _)) <- zip applications (structurePresentationParents presentation)]
        Marker ownerName = structurePhraseMarker (structurePresentationPhrase presentation)
        namesFor application = case Map.lookup application explicit of
            Just names -> Set.toAscList names
            Nothing -> case markerFor application of
                marker@(Marker name) | maybe False ((== 1) . Set.size) (Map.lookup marker byMarker) ->
                    [Marker (ownerName <> "inherit_" <> name)]
                _ -> []
        parentAliases = Map.fromList [(application, namesFor application) | application <- Set.toAscList ancestors]
    for_ applications \application ->
        when (null (namesFor application)) (Left (StructureParentLabelRequired (Marker ownerName) (markerFor application) application))
    _ <- foldM checkParentAlias Map.empty
        [(name, application) | (application, names) <- Map.toAscList parentAliases, name <- names]
    pure ResolvedStructureSchema
        { internalResolvedSchemaOrigin = internalLocalSchemaOrigin local
        , internalResolvedSchemaTheory = theory
        , internalResolvedSchemaRole = internalLocalSchemaRole local
        , internalResolvedSchemaRoot = root
        , internalResolvedSchemaParameters = internalLocalSchemaParameters local
        , internalResolvedSchemaDirectParents = Set.fromList applications
        , internalResolvedSchemaAncestors = ancestors
        , internalResolvedSchemaFields = fields
        , internalResolvedSchemaFieldRoles = roles
        , internalResolvedSchemaRequirements = requirements
        , internalResolvedSchemaPresentation = ResolvedPresentation presentation applications fieldOrder ancestorMarkers parentAliases
        }
  where
    checkParentAlias names (name, application) = case Map.lookup name names of
        Just previous | previous /= application -> Left (StructureParentAliasConflict name previous application)
        _ -> Right (Map.insert name application names)
    identity = localSchemaId local
    theory = internalLocalSchemaTheory local
    parameterCount = fromIntegral (length (internalLocalSchemaParameters local))
    self = structureApplicationKey identity (schemaParameterArguments parameterCount)
    presentation = internalLocalPresentation local
    applications = localWireParents (localSchemaWire local)
    resolveParent application = do
        let parentId = structureApplicationId application
        parent <- maybe (Left (StructureParentMissing identity parentId)) Right (lookupParent parentId)
        unless (internalResolvedSchemaTheory parent == theory)
            (Left (StructureBatchTheoryMismatch theory (internalResolvedSchemaTheory parent)))
        let expected = resolvedSchemaParameterCount parent
            actual = fromIntegral (length (structureApplicationArguments application))
        unless (expected == actual)
            (Left (StructureParentArityMismatch identity parentId expected actual))
        pure (application, parent)
    inheritedAncestors (application, parent) =
        specializeKey application <$> resolvedSchemaSemanticAncestorOrder parent
    specializeKey application (StructureApplicationKey parent arguments _ _) =
        structureApplicationKey parent (specialize application <$> arguments)
    specialize application = specializeStructureBody parameterCount (structureApplicationArguments application)
    ownFields =
        [ ResolvedField (internalLocalFieldIdentity field) identity (internalLocalFieldSlot field)
            (internalLocalFieldSymbol field) (internalLocalFieldSelector field) (internalLocalFieldProjection field)
        | field <- internalLocalSchemaFields local
        ]
    parentRequirements (application, parent) =
        [ ResolvedRequirement (specialize application (internalResolvedRequirementBody requirement))
            (Map.fromList
                [ (key { requirementOwnerAtSite = specializeKey application (requirementOwnerAtSite key) }, occurrence)
                | (key, occurrence) <- Map.toAscList (internalResolvedRequirementOccurrences requirement)
                ])
        | requirement <- Map.elems (internalResolvedSchemaRequirements parent)
        ]
    localRequirements =
        [ singletonRequirement (PreambleOrigin identity key)
            (shiftCanonical (parameterCount - available) 0 (scopedCoreTerm body))
            (RequirementOccurrence (requiredPresentation key (structurePresentationPreamble presentation)) Nothing)
        | LocalPreambleRequirement key available body <- internalLocalSchemaPreambleRequirements local
        ] <>
        [ let (marker, location) = requiredPresentation (internalLocalFieldSlot field) (structurePresentationFields presentation)
          in singletonRequirement (FieldSpecificationOrigin identity (internalLocalFieldIdentity field))
                (scopedCoreTerm body) (RequirementOccurrence location marker)
        | field <- internalLocalSchemaFields local
        , body <- maybeToList (internalLocalFieldSpecification field)
        ] <>
        [ let (marker, location) = requiredPresentation ordinal (structurePresentationLaws presentation)
          in singletonRequirement (LawOrigin identity ordinal) (scopedCoreTerm body)
                (RequirementOccurrence location (Just marker))
        | (ordinal, body) <- internalLocalSchemaLaws local
        ]
    singletonRequirement origin body occurrence = ResolvedRequirement body
        (Map.singleton (RequirementProvenanceKey origin self) occurrence)
    requiredPresentation key metadata = fromMaybe
        (impossible "checked local schema lost presentation metadata") (Map.lookup key metadata)
    insertField (fields, roles) field = do
        let fieldId' = internalResolvedFieldIdentity field
            symbol = internalResolvedFieldSymbol field
        case Map.lookup fieldId' fields of
            Just existing | existing /= field -> Left (StructureFieldIdentityConflict fieldId')
            _ -> pure ()
        case Map.lookup symbol roles of
            Just existing | existing /= fieldId' -> Left (StructureFieldRoleConflict symbol existing fieldId')
            _ -> pure ()
        pure (Map.insert fieldId' field fields, Map.insert symbol fieldId' roles)
    insertRequirement requirements requirement =
        let key = requirementBodyKey (internalResolvedRequirementBody requirement)
        in pure (Map.insertWith mergeRequirement key requirement requirements)
    mergeRequirement new old = old
        { internalResolvedRequirementOccurrences = Map.union
            (internalResolvedRequirementOccurrences old) (internalResolvedRequirementOccurrences new) }
    checkProvenance known (body, requirement) =
        foldM (\index provenance -> case Map.lookup provenance index of
            Just previous | previous /= body -> Left (StructureRequirementConflict provenance)
            _ -> pure (Map.insert provenance body index)) known
            (Map.keys (internalResolvedRequirementOccurrences requirement))

localSchemaOrigin :: LocalStructureSchema -> StructureOrigin
localSchemaOrigin = internalLocalSchemaOrigin

localSchemaTheory :: LocalStructureSchema -> TheoryId
localSchemaTheory = internalLocalSchemaTheory

localSchemaObjectDependencies :: LocalStructureSchema -> (Set ObjectId)
localSchemaObjectDependencies = internalLocalSchemaObjectDependencies

localSchemaRole :: LocalStructureSchema -> StructureRole
localSchemaRole = internalLocalSchemaRole

localSchemaParameters :: LocalStructureSchema -> [LocalParameterOrdinal]
localSchemaParameters = internalLocalSchemaParameters

localSchemaPreambleRequirements :: LocalStructureSchema -> [LocalPreambleRequirement]
localSchemaPreambleRequirements = internalLocalSchemaPreambleRequirements

localSchemaParents :: LocalStructureSchema -> [LocalParentApplication]
localSchemaParents = internalLocalSchemaParents

localSchemaFields :: LocalStructureSchema -> [LocalStructureField]
localSchemaFields = internalLocalSchemaFields

localSchemaLaws :: LocalStructureSchema -> [(LocalLawOrdinal, ScopedCheckedCore ObjectId)]
localSchemaLaws = internalLocalSchemaLaws

localPresentation :: LocalStructureSchema -> StructurePresentation
localPresentation = internalLocalPresentation

localPreambleClauseKey :: LocalPreambleRequirement -> LocalPreambleClauseKey
localPreambleClauseKey = internalLocalPreambleClauseKey

localPreambleAvailablePrefix :: LocalPreambleRequirement -> Natural
localPreambleAvailablePrefix = internalLocalPreambleAvailablePrefix

localPreambleBody :: LocalPreambleRequirement -> (ScopedCheckedCore ObjectId)
localPreambleBody = internalLocalPreambleBody

localFieldSlot :: LocalStructureField -> StructureFieldSlot
localFieldSlot = internalLocalFieldSlot

localFieldIdentity :: LocalStructureField -> FieldId
localFieldIdentity = internalLocalFieldIdentity

localFieldSymbol :: LocalStructureField -> StructSymbol
localFieldSymbol = internalLocalFieldSymbol

localFieldSelector :: LocalStructureField -> ObjectId
localFieldSelector = internalLocalFieldSelector

localFieldProjection :: LocalStructureField -> ObjectId
localFieldProjection = internalLocalFieldProjection

localFieldSpecification :: LocalStructureField -> (Maybe (ScopedCheckedCore ObjectId))
localFieldSpecification = internalLocalFieldSpecification

resolvedSchemaOrigin :: ResolvedStructureSchema -> StructureOrigin
resolvedSchemaOrigin = internalResolvedSchemaOrigin

resolvedSchemaTheory :: ResolvedStructureSchema -> TheoryId
resolvedSchemaTheory = internalResolvedSchemaTheory

resolvedSchemaRole :: ResolvedStructureSchema -> StructureRole
resolvedSchemaRole = internalResolvedSchemaRole

resolvedSchemaRoot :: ResolvedStructureSchema -> StructureId
resolvedSchemaRoot = internalResolvedSchemaRoot

resolvedSchemaParameters :: ResolvedStructureSchema -> [LocalParameterOrdinal]
resolvedSchemaParameters = internalResolvedSchemaParameters

resolvedSchemaDirectParents :: ResolvedStructureSchema -> (Set StructureApplicationKey)
resolvedSchemaDirectParents = internalResolvedSchemaDirectParents

resolvedSchemaAncestors :: ResolvedStructureSchema -> (Set StructureApplicationKey)
resolvedSchemaAncestors = internalResolvedSchemaAncestors

resolvedSchemaFields :: ResolvedStructureSchema -> (Map FieldId ResolvedField)
resolvedSchemaFields = internalResolvedSchemaFields

resolvedSchemaFieldRoles :: ResolvedStructureSchema -> (Map StructSymbol FieldId)
resolvedSchemaFieldRoles = internalResolvedSchemaFieldRoles

resolvedSchemaRequirements :: ResolvedStructureSchema -> (Map RequirementBodyKey ResolvedRequirement)
resolvedSchemaRequirements = internalResolvedSchemaRequirements

resolvedSchemaPresentation :: ResolvedStructureSchema -> ResolvedPresentation
resolvedSchemaPresentation = internalResolvedSchemaPresentation

resolvedFieldIdentity :: ResolvedField -> FieldId
resolvedFieldIdentity = internalResolvedFieldIdentity

resolvedFieldOwner :: ResolvedField -> StructureId
resolvedFieldOwner = internalResolvedFieldOwner

resolvedFieldSlot :: ResolvedField -> StructureFieldSlot
resolvedFieldSlot = internalResolvedFieldSlot

resolvedFieldSymbol :: ResolvedField -> StructSymbol
resolvedFieldSymbol = internalResolvedFieldSymbol

resolvedFieldSelector :: ResolvedField -> ObjectId
resolvedFieldSelector = internalResolvedFieldSelector

resolvedFieldProjection :: ResolvedField -> ObjectId
resolvedFieldProjection = internalResolvedFieldProjection

resolvedPresentationLocal :: ResolvedPresentation -> StructurePresentation
resolvedPresentationLocal = internalResolvedPresentationLocal

resolvedPresentationParentOrder :: ResolvedPresentation -> [StructureApplicationKey]
resolvedPresentationParentOrder = internalResolvedPresentationParentOrder

resolvedPresentationParentAliases :: ResolvedPresentation -> Map StructureApplicationKey [Marker]
resolvedPresentationParentAliases = internalResolvedPresentationParentAliases

resolvedPresentationFieldOrder :: ResolvedPresentation -> [FieldId]
resolvedPresentationFieldOrder = internalResolvedPresentationFieldOrder

resolvedRequirementBody :: ResolvedRequirement -> (CanonicalTerm ObjectId)
resolvedRequirementBody = internalResolvedRequirementBody

resolvedRequirementOccurrences :: ResolvedRequirement -> (Map RequirementProvenanceKey RequirementOccurrence)
resolvedRequirementOccurrences = internalResolvedRequirementOccurrences

requirementOccurrenceLocation :: RequirementOccurrence -> Location
requirementOccurrenceLocation = internalRequirementOccurrenceLocation

requirementOccurrenceMarker :: RequirementOccurrence -> (Maybe Marker)
requirementOccurrenceMarker = internalRequirementOccurrenceMarker
