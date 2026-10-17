{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Content-addressed identities for checked mathematical content.
module Felix.Checking.Identity
    ( TheoryId
    , theoryId
    , theoryIdDigest
    , encodeFoundationManifest
    , foundationManifestTags
    , encodeKernelRuleTag
    , ObjectFamily(..)
    , ObjectId
    , objectId
    , objectIdFamily
    , objectIdDigest
    , encodeObjectId
    , objectIdBuilder
    , getObjectIdMathematical
    , OpaqueDeclarationSeed
    , opaqueDeclarationSeed
    , opaqueDeclarationSeedDigest
    , FieldId
    , fieldId
    , fieldIdDigest
    , StructureOrigin(..)
    , StructureId
    , structureId
    , structureIdDigest
    , ObjectContent(..)
    , objectContentTheory
    , objectContentType
    , intrinsicObjectId
    , transparentObjectId
    , opaqueObjectId
    , AssertedObject
    , intrinsicObject
    , transparentObject, transparentObjectWith
    , opaqueObject
    , reenterIntrinsicObject
    , reenterTransparentObject
    , verifyTransparentObjectRoot
    , reenterOpaqueObject
    , ObjectReentryError(..)
    , assertedObjectId
    , assertedObjectContent
    , CheckedObjectClosure
    , checkedObjectClosureTheory
    , checkedObjectIds
    , checkedObjectMember
    , checkedObjectCount
    , CheckedObjectContribution
    , checkedObjectContribution
    , checkedObjectContributionIds
    , checkedObjectContributionAssertions
    , insertCheckedObjectContribution
    , lookupCheckedObjectType
    , lookupCheckedObjectContent
    , globalTypingFromClosure
    , validateObjectClosure
    , extendObjectClosure
    , ObjectValidationError(..)
    , PropositionId
    , propositionIdDigest
    , CheckedPropositionContent
    , checkedPropositionId
    , checkedPropositionTerm
    , validatePropositionContent
    , validateAssertedPropositionContent
    , revalidatePropositionContent
    , ReenteredTerm
    , ReenteredCanonicalTerm
    , reenteredCanonicalTermRoot
    , reenteredCanonicalTermBody
    , identifyAndReenterCanonicalTerm
    , getReenteredCanonicalTermCache
    , reenterCanonicalTerm
    , verifyCanonicalTermRoot
    , TermReentryError(..)
    , StoredPropositionCandidate
    , storedPropositionCandidate
    , storedPropositionCandidateId
    , storedPropositionCandidateTerm
    , validateStoredPropositionCandidate
    , PropositionReentryError(..)
    , propositionIdOf
    , PropositionValidationError(..)
    , TheoremRef
    , theoremRef
    , theoremRefTheory
    , theoremRefProposition
    , encodeTheoremRef
    , TheoremId
    , theoremId
    , theoremIdDigest
    , putTheoryIdCache
    , getTheoryIdCache
    , putObjectIdCache
    , getObjectIdCache
    , putFieldIdCache
    , getFieldIdCache
    , putStructureIdCache
    , getStructureIdCache
    , putOpaqueDeclarationSeedCache
    , getOpaqueDeclarationSeedCache
    , putPropositionIdCache
    , getPropositionIdCache
    , putTheoremRefCache
    , getTheoremRefCache
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Core.StableCode
    ( allCoreIntrinsicTags
    , coreIntrinsicTagCode
    )
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping.Internal (GlobalTyping(..))
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Math.Codec.Internal qualified as Mathematical
import Felix.Module

import Control.DeepSeq (NFData(..))
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word8)




newtype TheoryId =
    TheoryId MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

theoryId :: CheckedFoundation -> TheoryId
theoryId foundation =
    TheoryId
        (hashIdentityBytes TheoryIdentity
            (encodeFoundationManifest foundation))

theoryIdDigest :: TheoryId -> MathematicalDigest
theoryIdDigest (TheoryId digest) =
    digest

-- | Versioned compiled calculus followed by the ordered intrinsic/rule/axiom
-- manifest. The calculus code covers ordinary rules and beta-eta conversion;
-- backend classification is intentionally absent.
encodeFoundationManifest :: CheckedFoundation -> ByteString
encodeFoundationManifest foundation =
    builderBytes
        ( Builder.word8 1 -- manifest format
            <> Builder.word8 1 -- ordinary kernel rules with beta-eta conversion
            <> compactSequenceBuilder putIntrinsicRow intrinsicTags
            <> compactSequenceBuilder putRuleRow ruleTags
            <> compactSequenceBuilder putAxiomRow axiomTags
        )
  where
    (intrinsicTags, ruleTags, axiomTags) =
        foundationManifestTags

    putIntrinsicRow tag =
        Builder.word8 (coreIntrinsicTagCode tag)
            <> compactCoreTypeBuilder (coreIntrinsicType tag)

    putRuleRow tag =
        let KernelRuleSignature inputTypes binderCount =
                foundationRuleSignature foundation tag
        in Builder.word8 (kernelRuleTagCode tag)
            <> compactSequenceBuilder compactCoreTypeBuilder inputTypes
            <> compactNaturalBuilder binderCount

    putAxiomRow tag =
        Builder.word8 (foundationAxiomTagCode tag)
            <> Builder.byteString
                (closedCanonicalTermDigestBytes
                    (frozenCoreTerm
                        (foundationAxiomFrozen foundation tag)))

-- | Exhaustive foundation inventories in their stable encoded-tag order.
foundationManifestTags
    :: ( [CoreIntrinsicTag]
       , [KernelRuleTag]
       , [FoundationAxiomTag]
       )
foundationManifestTags =
    ( stableTagOrder
        "core intrinsic"
        encodeSelectedCoreIntrinsicTag
        allCoreIntrinsicTags
    , stableTagOrder
        "kernel rule"
        encodeKernelRuleTag
        allKernelRuleTags
    , stableTagOrder
        "foundation axiom"
        encodeFoundationAxiomTag
        allFoundationAxiomTags
    )


data ObjectFamily
    = IntrinsicObject
    | TransparentObject
    | OpaqueObject
    deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
    deriving anyclass (Hashable, NFData)

data ObjectId = ObjectId
    !ObjectFamily
    !MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Hashable, NFData)

objectId
    :: ObjectFamily
    -> MathematicalDigest
    -> ObjectId
objectId =
    ObjectId

objectIdFamily :: ObjectId -> ObjectFamily
objectIdFamily (ObjectId family _digest) =
    family

objectIdDigest :: ObjectId -> MathematicalDigest
objectIdDigest (ObjectId _family digest) =
    digest

encodeObjectId :: ObjectId -> ByteString
encodeObjectId (ObjectId family digest) =
    ByteString.singleton (objectFamilyTag family)
        <> mathematicalDigestBytes digest

objectIdBuilder :: ObjectId -> Builder.Builder
objectIdBuilder (ObjectId family digest) =
    Builder.word8 (objectFamilyTag family)
        <> Builder.byteString (mathematicalDigestBytes digest)

getObjectIdMathematical :: MathematicalGet ObjectId
getObjectIdMathematical = do
    familyTag <- getMathematicalWord8
    family <- case familyTag of
        0x00 -> pure IntrinsicObject
        0x01 -> pure TransparentObject
        0x02 -> pure OpaqueObject
        _ -> failMathematicalGet
            (MathematicalInvalidGlobal
                ("unknown object-family tag "
                    <> Text.pack (show familyTag)))
    digestBytes <- getMathematicalBytes 32
    digest <-
        maybe
            (failMathematicalGet
                (MathematicalInvalidGlobal
                    "object digest is not 32 bytes"))
            pure
            (mathematicalDigestFromBytes digestBytes)
    pure (ObjectId family digest)


newtype OpaqueDeclarationSeed =
    OpaqueDeclarationSeed MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

opaqueDeclarationSeed
    :: ModuleName
    -> LocalDeclarationOrdinal
    -> DeclarationFamilyTag
    -> GeneratedObjectSlot
    -> OpaqueDeclarationSeed
opaqueDeclarationSeed
        owner
        declarationOrdinal
        family
        generatedSlot =
    OpaqueDeclarationSeed
        (hashIdentityBuilder
            OpaqueDeclarationSeedIdentity
            ( Builder.byteString (encodeModuleName owner)
                <> compactNaturalBuilder
                    (localDeclarationOrdinalValue declarationOrdinal)
                <> Builder.byteString
                    (encodeDeclarationFamilyTag family)
                <> compactNaturalBuilder
                    (generatedObjectSlotValue generatedSlot)
            ))

opaqueDeclarationSeedDigest
    :: OpaqueDeclarationSeed
    -> MathematicalDigest
opaqueDeclarationSeedDigest
        (OpaqueDeclarationSeed digest) =
    digest


-- | Stable identity of one field declared by a structure schema.  It is
-- source-provenance based, like an opaque declaration seed, but deliberately
-- independent of the object currently used to realize the field projection.
newtype FieldId =
    FieldId MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

fieldId
    :: ModuleName
    -> LocalDeclarationOrdinal
    -> StructureFieldSlot
    -> FieldId
fieldId owner declarationOrdinal fieldSlot =
    FieldId
        (hashIdentityBuilder
            StructureFieldIdentity
            ( Builder.byteString (encodeModuleName owner)
                <> compactNaturalBuilder
                    (localDeclarationOrdinalValue declarationOrdinal)
                <> compactNaturalBuilder
                    (structureFieldSlotValue fieldSlot)
            ))

fieldIdDigest :: FieldId -> MathematicalDigest
fieldIdDigest (FieldId digest) =
    digest


data StructureOrigin = StructureOrigin
    { structureOriginModule :: !ModuleName
    , structureOriginDeclaration :: !LocalDeclarationOrdinal
    , structureOriginSlot :: !StructureSlot
    }
    deriving stock (Show, Eq, Ord, Generic)

newtype StructureId = StructureId MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

structureId :: StructureOrigin -> StructureId
structureId (StructureOrigin owner declarationOrdinal slot) =
    StructureId
        (hashIdentityBuilder StructureIdentity
            ( Builder.byteString (encodeModuleName owner)
                <> compactNaturalBuilder
                    (localDeclarationOrdinalValue declarationOrdinal)
                <> compactNaturalBuilder (structureSlotValue slot)
            ))

structureIdDigest :: StructureId -> MathematicalDigest
structureIdDigest (StructureId digest) = digest

putStructureIdCache :: StructureId -> CachePut
putStructureIdCache = putMathematicalDigestCache . structureIdDigest

getStructureIdCache :: CacheGet StructureId
getStructureIdCache = StructureId <$> getMathematicalDigestCache

data ObjectContent
    = IntrinsicObjectContent
        !TheoryId
        !CoreIntrinsicTag
    | TransparentObjectContent
        !TheoryId
        !CoreType
        !(CanonicalTerm ObjectId)
    | OpaqueObjectContent
        !TheoryId
        !OpaqueDeclarationSeed
        !CoreType
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

objectContentTheory :: ObjectContent -> TheoryId
objectContentTheory = \case
    IntrinsicObjectContent identity _tag ->
        identity
    TransparentObjectContent identity _coreType _body ->
        identity
    OpaqueObjectContent identity _seed _coreType ->
        identity

objectContentType :: ObjectContent -> CoreType
objectContentType = \case
    IntrinsicObjectContent _identity tag ->
        coreIntrinsicType tag
    TransparentObjectContent _identity coreType _body ->
        coreType
    OpaqueObjectContent _identity _seed coreType ->
        coreType

intrinsicObjectId
    :: TheoryId
    -> CoreIntrinsicTag
    -> ObjectId
intrinsicObjectId identity tag =
    ObjectId
            IntrinsicObject
            (hashIdentityBuilder
                IntrinsicObjectIdentity
                ( Builder.byteString
                    (mathematicalDigestBytes
                        (theoryIdDigest identity))
                    <> Builder.word8 (coreIntrinsicTagCode tag)
                ))

transparentObjectId
    :: TheoryId
    -> CoreType
    -> CanonicalTerm ObjectId
    -> ObjectId
transparentObjectId identity coreType body =
    transparentObjectIdFromRoot
        identity
        coreType
        (identifyCanonicalTerm objectIdBuilder body)

transparentObjectIdFromRoot
    :: TheoryId
    -> CoreType
    -> TermDigest
    -> ObjectId
transparentObjectIdFromRoot identity coreType root =
    ObjectId
        TransparentObject
        (hashIdentityBuilder
            TransparentObjectIdentity
            ( Builder.byteString
                (mathematicalDigestBytes (theoryIdDigest identity))
                <> compactCoreTypeBuilder coreType
                <> Builder.byteString (termDigestBytes root)
            ))

opaqueObjectId
    :: TheoryId
    -> OpaqueDeclarationSeed
    -> CoreType
    -> ObjectId
opaqueObjectId identity seed coreType =
    ObjectId
        OpaqueObject
        (hashIdentityBuilder
            OpaqueObjectIdentity
            ( Builder.byteString
                (mathematicalDigestBytes (theoryIdDigest identity))
                <> Builder.byteString
                    (mathematicalDigestBytes
                        (opaqueDeclarationSeedDigest seed))
                <> compactCoreTypeBuilder coreType
            ))


data AssertedObject = AssertedObject
    !ObjectId
    !ObjectContent
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

intrinsicObject :: TheoryId -> CoreIntrinsicTag -> AssertedObject
intrinsicObject theory tag =
    AssertedObject
        (intrinsicObjectId theory tag)
        (IntrinsicObjectContent theory tag)

transparentObject
    :: TheoryId -> CoreType -> CanonicalTerm ObjectId -> AssertedObject
transparentObject theory coreType body = AssertedObject
    (transparentObjectId theory coreType body) (TransparentObjectContent theory coreType body)

transparentObjectWith
    :: Monad m => m () -> TheoryId -> CoreType -> CanonicalTerm ObjectId -> m AssertedObject
transparentObjectWith visit theory coreType body = do
    root <- identifyCanonicalTermWith visit objectIdBuilder body
    encodedType <- compactCoreTypeBuilderWith visit coreType
    let identity = ObjectId TransparentObject (hashIdentityBuilder TransparentObjectIdentity
            (Builder.byteString (mathematicalDigestBytes (theoryIdDigest theory))
                <> encodedType <> Builder.byteString (termDigestBytes root)))
    identity `seq` pure (AssertedObject identity (TransparentObjectContent theory coreType body))

opaqueObject
    :: TheoryId
    -> OpaqueDeclarationSeed
    -> CoreType
    -> AssertedObject
opaqueObject theory seed coreType =
    AssertedObject
        (opaqueObjectId theory seed coreType)
        (OpaqueObjectContent theory seed coreType)

data ObjectReentryError
    = ObjectReentryFamilyMismatch
        !ObjectId
        !ObjectFamily
        !ObjectFamily
    | ObjectReentryIdMismatch
        !ObjectId
        !ObjectId
    deriving stock (Show, Eq)


-- | Re-enter an intrinsic row from its minimal stored content.
reenterIntrinsicObject
    :: TheoryId
    -> ObjectId
    -> CoreIntrinsicTag
    -> Either ObjectReentryError AssertedObject
reenterIntrinsicObject theory supplied tag = do
    verifyReentryFamily IntrinsicObject supplied
    let computed = ObjectId IntrinsicObject
            (hashIdentityBuilder
                IntrinsicObjectIdentity
                ( Builder.byteString
                    (mathematicalDigestBytes (theoryIdDigest theory))
                    <> Builder.word8 (coreIntrinsicTagCode tag)
                ))
        object = AssertedObject computed
            (IntrinsicObjectContent theory tag)
    verifyReenteredObject supplied object

-- | Re-enter a transparent row. The checked term root is used
-- directly; the reconstructed body is never re-encoded or rehashed here.
reenterTransparentObject
    :: TheoryId
    -> ObjectId
    -> CoreType
    -> ReenteredCanonicalTerm
    -> Either ObjectReentryError AssertedObject
reenterTransparentObject theory supplied coreType reentered = do
    verifyTransparentObjectRoot
        theory supplied coreType (reenteredCanonicalTermRoot reentered)
    pure
        (AssertedObject supplied
            (TransparentObjectContent
                theory coreType
                (reenteredCanonicalTermBody reentered)))

-- | Check a transparent row key from the root of its exact canonical body.
verifyTransparentObjectRoot
    :: TheoryId
    -> ObjectId
    -> CoreType
    -> TermDigest
    -> Either ObjectReentryError ()
verifyTransparentObjectRoot theory supplied coreType root = do
    verifyReentryFamily TransparentObject supplied
    let computed = transparentObjectIdFromRoot theory coreType root
    unless
        (supplied == computed)
        (Left (ObjectReentryIdMismatch supplied computed))

-- | Re-enter an opaque row from its minimal stored content.
reenterOpaqueObject
    :: TheoryId
    -> ObjectId
    -> OpaqueDeclarationSeed
    -> CoreType
    -> Either ObjectReentryError AssertedObject
reenterOpaqueObject theory supplied seed coreType = do
    verifyReentryFamily OpaqueObject supplied
    let computed = ObjectId OpaqueObject
            (hashIdentityBuilder
                OpaqueObjectIdentity
                ( Builder.byteString
                    (mathematicalDigestBytes (theoryIdDigest theory))
                    <> Builder.byteString
                        (mathematicalDigestBytes
                            (opaqueDeclarationSeedDigest seed))
                    <> compactCoreTypeBuilder coreType
                ))
        object = AssertedObject computed
            (OpaqueObjectContent theory seed coreType)
    verifyReenteredObject supplied object

verifyReentryFamily
    :: ObjectFamily
    -> ObjectId
    -> Either ObjectReentryError ()
verifyReentryFamily expectedFamily identity =
    let suppliedFamily = objectIdFamily identity
    in unless
        (suppliedFamily == expectedFamily)
        (Left
            (ObjectReentryFamilyMismatch
                identity expectedFamily suppliedFamily))

verifyReenteredObject
    :: ObjectId
    -> AssertedObject
    -> Either ObjectReentryError AssertedObject
verifyReenteredObject supplied object =
    let computed = assertedObjectId object
    in if supplied == computed
        then Right object
        else Left (ObjectReentryIdMismatch supplied computed)

assertedObjectId :: AssertedObject -> ObjectId
assertedObjectId (AssertedObject identity _content) =
    identity

assertedObjectContent :: AssertedObject -> ObjectContent
assertedObjectContent (AssertedObject _identity content) =
    content

data CheckedObject = CheckedObject
    !ObjectContent
    !CoreType

data CheckedObjectClosure = CheckedObjectClosure
    !TheoryId
    !(Map ObjectId CheckedObject)

checkedObjectClosureTheory :: CheckedObjectClosure -> TheoryId
checkedObjectClosureTheory (CheckedObjectClosure identity _objects) =
    identity

checkedObjectIds :: CheckedObjectClosure -> Set ObjectId
checkedObjectIds (CheckedObjectClosure _identity objects) =
    Map.keysSet objects

checkedObjectMember :: ObjectId -> CheckedObjectClosure -> Bool
checkedObjectMember identity (CheckedObjectClosure _theory objects) =
    Map.member identity objects

checkedObjectCount :: CheckedObjectClosure -> Int
checkedObjectCount (CheckedObjectClosure _theory objects) =
    Map.size objects

-- | Only the selected checked objects and their external dependencies are
-- retained. The enclosing closure is not part of a producer's contribution.
data CheckedObjectContribution = CheckedObjectContribution
    !TheoryId
    !(Map ObjectId CheckedObject)
    !(Set ObjectId)

checkedObjectContribution
    :: CheckedObjectClosure
    -> [ObjectId]
    -> Either ObjectValidationError CheckedObjectContribution
checkedObjectContribution (CheckedObjectClosure theory objects) identities = do
    local <- foldM select Map.empty identities
    let dependencies = Set.unions
            [ case checkedObjectContent checked of
                TransparentObjectContent _theory _type body ->
                    canonicalTermGlobals body
                _ -> Set.empty
            | checked <- Map.elems local
            ]
        external = Set.filter (`Map.notMember` local) dependencies
    pure (CheckedObjectContribution theory local external)
  where
    select local identity =
        case Map.lookup identity objects of
            Nothing -> Left (CheckedContributionObjectMissing identity)
            Just checked -> Right (Map.insert identity checked local)

checkedObjectContributionIds :: CheckedObjectContribution -> Set ObjectId
checkedObjectContributionIds (CheckedObjectContribution _ objects _) = Map.keysSet objects

-- | Observe the exact assertions whose objects have already been checked.
-- Admission inserts the contribution itself to retain that evidence.
checkedObjectContributionAssertions :: CheckedObjectContribution -> [AssertedObject]
checkedObjectContributionAssertions (CheckedObjectContribution _ objects _) =
    [AssertedObject identity (checkedObjectContent object) | (identity, object) <- Map.toAscList objects]

-- | Content-addressed objects have immutable types and bodies. Membership of
-- the required external objects therefore preserves the original checking
-- context; compatible insertion does not inspect or validate their bodies.
insertCheckedObjectContribution
    :: CheckedObjectClosure
    -> CheckedObjectContribution
    -> Either ObjectValidationError CheckedObjectClosure
insertCheckedObjectContribution (CheckedObjectClosure theory existing)
        (CheckedObjectContribution actual local external) = do
    unless (theory == actual)
        (Left (CheckedContributionTheoryMismatch theory actual))
    traverse_
        (\identity -> unless (Map.member identity existing)
            (Left (CheckedContributionDependencyMissing identity)))
        external
    pure (CheckedObjectClosure theory
        (Map.foldlWithKey'
            (\objects identity checked ->
                Map.insertWith (\_ old -> old) identity checked objects)
            existing local))

lookupCheckedObjectType
    :: ObjectId
    -> CheckedObjectClosure
    -> Maybe CoreType
lookupCheckedObjectType identity
        (CheckedObjectClosure _theory objects) =
    checkedObjectType
        <$> Map.lookup identity objects

lookupCheckedObjectContent
    :: ObjectId
    -> CheckedObjectClosure
    -> Maybe ObjectContent
lookupCheckedObjectContent identity
        (CheckedObjectClosure _theory objects) =
    checkedObjectContent
        <$> Map.lookup identity objects

-- | Share the immutable checked closure as its global typing snapshot.  This
-- is the production carrier factory: it neither copies nor walks the object
-- map, and retains exactly that map for as long as the view is reachable.
globalTypingFromClosure
    :: CheckedObjectClosure
    -> GlobalTyping ObjectId
globalTypingFromClosure
        (CheckedObjectClosure _theory objects) =
    globalTypingFromCheckedObjects objects

globalTypingFromCheckedObjects
    :: Map ObjectId CheckedObject
    -> GlobalTyping ObjectId
globalTypingFromCheckedObjects objects =
    GlobalTyping \identity ->
        checkedObjectType <$> Map.lookup identity objects

checkedObjectType :: CheckedObject -> CoreType
checkedObjectType (CheckedObject _content coreType) =
    coreType

checkedObjectContent :: CheckedObject -> ObjectContent
checkedObjectContent (CheckedObject content _coreType) =
    content


data ObjectValidationError
    = DuplicateAssertedObjectId !ObjectId
    | CheckedContributionObjectMissing !ObjectId
    | CheckedContributionDependencyMissing !ObjectId
    | CheckedContributionTheoryMismatch !TheoryId !TheoryId
    | ObjectContentTheoryMismatch
        !ObjectId
        !TheoryId
        !TheoryId
    | ObjectContentFamilyMismatch
        !ObjectId
        !ObjectFamily
        !ObjectFamily
    | TransparentObjectReferenceMissing
        !ObjectId
        !ObjectId
    | TransparentObjectCycle !(NonEmpty ObjectId)
    | TransparentObjectCoreCheckError
        !ObjectId
        !CoreCheckError
    | TransparentObjectTypeMismatch
        !ObjectId
        !CoreType
        !CoreType
    | ObjectIdPayloadMismatch
        !ObjectId
        !ObjectId
    deriving stock (Show, Eq)

data ObjectValidationState = ObjectValidationState
    { validationStack :: ![ObjectId]
    , validatedObjects :: !(Map ObjectId CheckedObject)
    }

validateObjectClosure
    :: TheoryId
    -> [AssertedObject]
    -> Either ObjectValidationError CheckedObjectClosure
validateObjectClosure expectedTheory asserted = do
    inventory <- buildObjectInventory asserted
    finalState <-
        execStateT
            (traverse_ (validateOneObject expectedTheory inventory)
                (Map.keys inventory))
            (ObjectValidationState [] Map.empty)
    pure
        (CheckedObjectClosure
            expectedTheory
            (validatedObjects finalState))

-- | Validate one declaration's new objects against an already checked
-- closure. The existing closure is returned unchanged for an empty batch.
extendObjectClosure
    :: CheckedObjectClosure
    -> [AssertedObject]
    -> Either ObjectValidationError CheckedObjectClosure
extendObjectClosure closure [] =
    Right closure
extendObjectClosure
        (CheckedObjectClosure expectedTheory existing)
        asserted = do
    additions <- buildObjectInventory asserted
    traverse_
        (\identity ->
            when
                (Map.member identity existing)
                (Left (DuplicateAssertedObjectId identity)))
        (Map.keys additions)
    finalState <-
        execStateT
            (traverse_
                (validateOneObject expectedTheory additions)
                (Map.keys additions))
            (ObjectValidationState [] existing)
    pure
        (CheckedObjectClosure
            expectedTheory
            (validatedObjects finalState))

buildObjectInventory
    :: [AssertedObject]
    -> Either ObjectValidationError (Map ObjectId ObjectContent)
buildObjectInventory =
    foldM insertOne Map.empty
  where
    insertOne inventory (AssertedObject identity content)
        | Map.member identity inventory =
            Left (DuplicateAssertedObjectId identity)
        | otherwise =
            Right (Map.insert identity content inventory)

validateOneObject
    :: TheoryId
    -> Map ObjectId ObjectContent
    -> ObjectId
    -> StateT
        ObjectValidationState
        (Either ObjectValidationError)
        ()
validateOneObject expectedTheory inventory identity = do
    alreadyValidated <-
        gets (Map.member identity . validatedObjects)
    unless alreadyValidated do
        stack <- gets validationStack
        when (identity `elem` stack) do
            lift
                (Left
                    (TransparentObjectCycle
                        (cyclePath identity stack)))
        content <-
            case Map.lookup identity inventory of
                Nothing ->
                    impossible
                        "object validation root is absent from its inventory"
                Just found ->
                    pure found
        unless
            (objectContentTheory content == expectedTheory)
            (lift
                (Left
                    (ObjectContentTheoryMismatch
                        identity
                        expectedTheory
                        (objectContentTheory content))))
        let expectedFamily =
                objectContentFamily content
            suppliedFamily =
                objectIdFamily identity
        unless
            (suppliedFamily == expectedFamily)
            (lift
                (Left
                    (ObjectContentFamilyMismatch
                        identity
                        expectedFamily
                        suppliedFamily)))
        modify'
            (\validationState ->
                validationState
                    { validationStack =
                        identity
                            : validationStack validationState
                    })
        checked <- case content of
            IntrinsicObjectContent
                    theory
                    tag -> do
                let intrinsicType = coreIntrinsicType tag
                verifyObjectId
                    identity
                    (intrinsicObjectId theory tag)
                pure
                    (CheckedObject content intrinsicType)
            TransparentObjectContent
                    _theory
                    suppliedType
                    body -> do
                traverse_
                    (validateDependency expectedTheory inventory identity)
                    (Set.toAscList (canonicalTermGlobals body))
                resolvedObjects <-
                    gets validatedObjects
                checkedBody <-
                    lift
                        (first
                            (TransparentObjectCoreCheckError
                                identity)
                            (checkCanonicalCore
                                (globalTypingFromCheckedObjects
                                    resolvedObjects)
                                body))
                let inferredType =
                        frozenCoreType checkedBody
                unless
                    (inferredType == suppliedType)
                    (lift
                        (Left
                            (TransparentObjectTypeMismatch
                                identity
                                suppliedType
                                inferredType)))
                pure
                    (CheckedObject content suppliedType)
            OpaqueObjectContent
                    theory
                    seed
                    suppliedType -> do
                verifyObjectId
                    identity
                    (opaqueObjectId
                        theory
                        seed
                        suppliedType)
                pure
                    (CheckedObject content suppliedType)
        modify'
            (\validationState ->
                validationState
                    { validationStack =
                        dropCurrent
                            identity
                            (validationStack validationState)
                    , validatedObjects =
                        Map.insert
                            identity
                            checked
                            (validatedObjects validationState)
                    })
  where
    verifyObjectId supplied computed =
        unless
            (supplied == computed)
            (lift
                (Left
                    (ObjectIdPayloadMismatch
                        supplied
                        computed)))

validateDependency
    :: TheoryId
    -> Map ObjectId ObjectContent
    -> ObjectId
    -> ObjectId
    -> StateT
        ObjectValidationState
        (Either ObjectValidationError)
        ()
validateDependency expectedTheory inventory parent dependency = do
    checked <- gets (Map.member dependency . validatedObjects)
    unless checked do
        case Map.lookup dependency inventory of
            Nothing ->
                lift
                    (Left
                        (TransparentObjectReferenceMissing
                            parent
                            dependency))
            Just _ ->
                validateOneObject
                    expectedTheory
                    inventory
                    dependency

cyclePath :: ObjectId -> [ObjectId] -> NonEmpty ObjectId
cyclePath repeated stack =
    case break (== repeated) stack of
        (between, _repeated : _outer) ->
            repeated :| (reverse between <> [repeated])
        _ ->
            impossible "repeated object is absent from validation stack"

dropCurrent :: ObjectId -> [ObjectId] -> [ObjectId]
dropCurrent expected = \case
    current : rest
        | current == expected ->
            rest
    _ ->
        impossible "object validation stack is inconsistent"

objectContentFamily :: ObjectContent -> ObjectFamily
objectContentFamily = \case
    IntrinsicObjectContent{} ->
        IntrinsicObject
    TransparentObjectContent{} ->
        TransparentObject
    OpaqueObjectContent{} ->
        OpaqueObject

newtype PropositionId =
    PropositionId MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

propositionIdDigest :: PropositionId -> MathematicalDigest
propositionIdDigest (PropositionId digest) =
    digest

data CheckedPropositionContent = CheckedPropositionContent
    !PropositionId
    !(FrozenCheckedCore ObjectId)
    deriving stock (Show, Eq)

-- Keep generic reconstruction unavailable for this checked boundary.
instance NFData CheckedPropositionContent where
    rnf (CheckedPropositionContent identity term) = rnf identity `seq` rnf term

checkedPropositionId
    :: CheckedPropositionContent
    -> PropositionId
checkedPropositionId
        (CheckedPropositionContent identity _term) =
    identity

checkedPropositionTerm
    :: CheckedPropositionContent
    -> FrozenCheckedCore ObjectId
checkedPropositionTerm
        (CheckedPropositionContent _identity term) =
    term

-- | A decoded canonical term paired with the root of the exact bytes from
-- which its body was reconstructed. This phase value grants no dependency or
-- typing authority.
data ReenteredTerm digest = ReenteredTerm
    !digest
    !(CanonicalTerm ObjectId)
    deriving stock (Show, Eq)

type ReenteredCanonicalTerm = ReenteredTerm TermDigest

reenteredCanonicalTermRoot :: ReenteredTerm digest -> digest
reenteredCanonicalTermRoot (ReenteredTerm root _body) =
    root

reenteredCanonicalTermBody
    :: ReenteredTerm digest
    -> CanonicalTerm ObjectId
reenteredCanonicalTermBody (ReenteredTerm _root body) =
    body

data TermReentryError
    = TermRootMismatch
        !TermDigest !TermDigest
    | TermCodecFailure !MathematicalCodecError
    deriving stock (Show, Eq)

-- | Identify and decode an untrusted canonical term payload once.
identifyAndReenterCanonicalTerm
    :: ByteString
    -> Either
        TermReentryError
        ReenteredCanonicalTerm
identifyAndReenterCanonicalTerm bytes = do
    let computed = identifyCanonicalTermBytes bytes
    term <- first TermCodecFailure
        (decodeCanonicalTerm getObjectIdMathematical bytes)
    pure (ReenteredTerm computed term)

-- | Reenter a mathematical byte field using its enclosing row's allowance.
-- Like standalone reentry, this grants no dependency or typing authority.
getReenteredCanonicalTermCache :: CacheGet ReenteredCanonicalTerm
getReenteredCanonicalTermCache = do
    (bytes, term) <- getMathematicalCache
        (Mathematical.getTerm getObjectIdMathematical)
    pure (ReenteredTerm (identifyCanonicalTermBytes bytes) term)

reenterCanonicalTerm
    :: TermDigest
    -> ByteString
    -> Either
        TermReentryError
        ReenteredCanonicalTerm
reenterCanonicalTerm supplied bytes = do
    verifyCanonicalTermRoot supplied bytes
    term <- first TermCodecFailure
        (decodeCanonicalTerm getObjectIdMathematical bytes)
    pure (ReenteredTerm supplied term)

-- | Check that exact canonical bytes have the expected term root.
verifyCanonicalTermRoot
    :: TermDigest
    -> ByteString
    -> Either TermReentryError ()
verifyCanonicalTermRoot supplied bytes =
    let computed = identifyCanonicalTermBytes bytes
    in unless
        (supplied == computed)
        (Left (TermRootMismatch supplied computed))


data StoredPropositionCandidate = StoredPropositionCandidate
    !PropositionId
    !(CanonicalTerm ObjectId)

data PropositionReentryError
    = PropositionReentryRootMismatch
        !PropositionId
        !ByteString
    deriving stock (Show, Eq)

-- | Promote root/body re-entry evidence to an abstract proposition-row
-- candidate. This still grants neither dependency nor proposition typing.
storedPropositionCandidate
    :: PropositionId
    -> ReenteredCanonicalTerm
    -> Either PropositionReentryError StoredPropositionCandidate
storedPropositionCandidate identity reentered =
    let suppliedRoot = termDigestBytes (reenteredCanonicalTermRoot reentered)
    in if mathematicalDigestBytes (propositionIdDigest identity)
            == suppliedRoot
        then Right
            (StoredPropositionCandidate
                identity
                (reenteredCanonicalTermBody reentered))
        else Left
            (PropositionReentryRootMismatch identity suppliedRoot)

storedPropositionCandidateTerm
    :: StoredPropositionCandidate
    -> CanonicalTerm ObjectId
storedPropositionCandidateTerm
        (StoredPropositionCandidate _identity term) =
    term

storedPropositionCandidateId :: StoredPropositionCandidate -> PropositionId
storedPropositionCandidateId (StoredPropositionCandidate identity _term) = identity

data PropositionValidationError
    = PropositionObjectMissing !ObjectId
    | PropositionCoreCheckError !CoreCheckError
    | PropositionIsNotProp !CoreType
    | PropositionIdPayloadMismatch
        !PropositionId
        !PropositionId
    deriving stock (Show, Eq)

validatePropositionContent
    :: CheckedObjectClosure
    -> CanonicalTerm ObjectId
    -> Either
        PropositionValidationError
        CheckedPropositionContent
validatePropositionContent closure term = do
    checked <- validatePropositionTerm closure term
    let identity = propositionIdOf term
    pure
        (CheckedPropositionContent
            identity
            checked)

validatePropositionTerm
    :: CheckedObjectClosure
    -> CanonicalTerm ObjectId
    -> Either PropositionValidationError (FrozenCheckedCore ObjectId)
validatePropositionTerm closure term = do
    traverse_
        (\identity ->
            unless
                (isJust
                    (lookupCheckedObjectType identity closure))
                (Left (PropositionObjectMissing identity)))
        (Set.toAscList (canonicalTermGlobals term))
    checked <-
        first PropositionCoreCheckError
            (checkCanonicalCore
                (globalTypingFromClosure closure)
                term)
    unless
        (frozenCoreType checked == TyProp)
        (Left
            (PropositionIsNotProp
                (frozenCoreType checked)))
    pure checked

validateStoredPropositionCandidate
    :: CheckedObjectClosure
    -> StoredPropositionCandidate
    -> Either PropositionValidationError CheckedPropositionContent
validateStoredPropositionCandidate
        closure (StoredPropositionCandidate identity term) = do
    checked <- validatePropositionTerm closure term
    pure (CheckedPropositionContent identity checked)

validateAssertedPropositionContent
    :: CheckedObjectClosure
    -> PropositionId
    -> CanonicalTerm ObjectId
    -> Either
        PropositionValidationError
        CheckedPropositionContent
validateAssertedPropositionContent closure supplied term = do
    checked <-
        validatePropositionContent closure term
    let computed =
            checkedPropositionId checked
    unless
        (supplied == computed)
        (Left
            (PropositionIdPayloadMismatch
                supplied
                computed))
    pure checked

-- | Recheck dependencies and proposition type while retaining the identity
-- already established by trusted construction or store re-entry.
revalidatePropositionContent
    :: CheckedObjectClosure
    -> CheckedPropositionContent
    -> Either PropositionValidationError CheckedPropositionContent
revalidatePropositionContent closure proposition = do
    let term = frozenCoreTerm (checkedPropositionTerm proposition)
    checked <- validatePropositionTerm closure term
    pure
        (CheckedPropositionContent
            (checkedPropositionId proposition)
            checked)

propositionIdOf
    :: CanonicalTerm ObjectId
    -> PropositionId
propositionIdOf term =
    PropositionId
        (canonicalTermDigest term)


data TheoremRef = TheoremRef
    !TheoryId
    !PropositionId
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

theoremRef :: TheoryId -> PropositionId -> TheoremRef
theoremRef =
    TheoremRef

theoremRefTheory :: TheoremRef -> TheoryId
theoremRefTheory (TheoremRef identity _proposition) =
    identity

theoremRefProposition :: TheoremRef -> PropositionId
theoremRefProposition (TheoremRef _identity proposition) =
    proposition

encodeTheoremRef :: TheoremRef -> ByteString
encodeTheoremRef (TheoremRef identity proposition) =
    mathematicalDigestBytes (theoryIdDigest identity)
        <> mathematicalDigestBytes (propositionIdDigest proposition)

newtype TheoremId =
    TheoremId MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

theoremId :: TheoremRef -> TheoremId
theoremId reference =
    TheoremId
        (hashIdentityBytes
            TheoremIdentity
            (encodeTheoremRef reference))

theoremIdDigest :: TheoremId -> MathematicalDigest
theoremIdDigest (TheoremId digest) =
    digest


putTheoryIdCache :: TheoryId -> CachePut
putTheoryIdCache =
    putMathematicalDigestCache . theoryIdDigest

getTheoryIdCache :: CacheGet TheoryId
getTheoryIdCache =
    TheoryId <$> getMathematicalDigestCache

putObjectIdCache :: ObjectId -> CachePut
putObjectIdCache (ObjectId family digest) = do
    putCacheTag (objectFamilyTag family)
    putMathematicalDigestCache digest

getObjectIdCache :: CacheGet ObjectId
getObjectIdCache = do
    family <- getCacheTag >>= \case
        0x00 ->
            pure IntrinsicObject
        0x01 ->
            pure TransparentObject
        0x02 ->
            pure OpaqueObject
        tag ->
            fail ("unknown cache object-family tag " <> show tag)
    ObjectId family <$> getMathematicalDigestCache

putFieldIdCache :: FieldId -> CachePut
putFieldIdCache =
    putMathematicalDigestCache . fieldIdDigest

getFieldIdCache :: CacheGet FieldId
getFieldIdCache =
    FieldId <$> getMathematicalDigestCache

putOpaqueDeclarationSeedCache
    :: OpaqueDeclarationSeed
    -> CachePut
putOpaqueDeclarationSeedCache =
    putMathematicalDigestCache
        . opaqueDeclarationSeedDigest

getOpaqueDeclarationSeedCache
    :: CacheGet OpaqueDeclarationSeed
getOpaqueDeclarationSeedCache =
    OpaqueDeclarationSeed
        <$> getMathematicalDigestCache

putPropositionIdCache :: PropositionId -> CachePut
putPropositionIdCache =
    putMathematicalDigestCache . propositionIdDigest

getPropositionIdCache :: CacheGet PropositionId
getPropositionIdCache =
    PropositionId <$> getMathematicalDigestCache

putTheoremRefCache :: TheoremRef -> CachePut
putTheoremRefCache (TheoremRef identity proposition) = do
    putTheoryIdCache identity
    putPropositionIdCache proposition

getTheoremRefCache :: CacheGet TheoremRef
getTheoremRefCache =
    TheoremRef
        <$> getTheoryIdCache
        <*> getPropositionIdCache


objectFamilyTag :: ObjectFamily -> Word8
objectFamilyTag = \case
    IntrinsicObject ->
        0x00
    TransparentObject ->
        0x01
    OpaqueObject ->
        0x02

encodeKernelRuleTag :: KernelRuleTag -> ByteString
encodeKernelRuleTag =
    ByteString.singleton . kernelRuleTagCode

encodeFoundationAxiomTag :: FoundationAxiomTag -> ByteString
encodeFoundationAxiomTag =
    ByteString.singleton . foundationAxiomTagCode

encodeSelectedCoreIntrinsicTag :: CoreIntrinsicTag -> ByteString
encodeSelectedCoreIntrinsicTag =
    ByteString.singleton . coreIntrinsicTagCode

stableTagOrder
    :: Show tag
    => String
    -> (tag -> ByteString)
    -> [tag]
    -> [tag]
stableTagOrder description encodeTag tags
    | Set.size encodedTags == length tags =
        List.sortOn encodeTag tags
    | otherwise =
        impossible
            ("duplicate stable "
                <> description
                <> " tag in "
                <> show tags)
  where
    encodedTags =
        Set.fromList (encodeTag <$> tags)

builderBytes :: Builder.Builder -> ByteString
builderBytes =
    LazyByteString.toStrict . Builder.toLazyByteString

canonicalTermDigest
    :: CanonicalTerm ObjectId
    -> MathematicalDigest
canonicalTermDigest term =
    digestFromTermBytes (canonicalTermDigestBytes term)

canonicalTermDigestBytes
    :: CanonicalTerm ObjectId
    -> ByteString
canonicalTermDigestBytes =
    termDigestBytes
        . identifyCanonicalTerm
            objectIdBuilder

closedCanonicalTermDigestBytes
    :: CanonicalTerm Void
    -> ByteString
closedCanonicalTermDigestBytes =
    termDigestBytes
        . identifyCanonicalTerm absurd

digestFromTermBytes :: ByteString -> MathematicalDigest
digestFromTermBytes bytes =
    maybe
        (impossible "term digest is not 32 bytes")
        id
        (mathematicalDigestFromBytes bytes)
