{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Identity (unitTests) where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Core.StableCode qualified as StableCode
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping qualified as GlobalTyping
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Notion (ConjunctionPath(..))
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Module
import Felix.Source
import Felix.Test.Temp (withTemporaryDirectory)

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Binary.Put qualified as Put
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word8)
import Hedgehog
    ( Property
    , evalMaybe
    , forAll
    , property
    , withTests
    , (===)
    )
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Numeric.Natural (Natural)
import System.FilePath.Posix qualified as Posix
import Test.Tasty
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit hiding (assert)




unitTests :: TestTree
unitTests =
    testGroup "Content identities"
        [ testCase "orders exhaustive foundation rows by stable tags"
            ordersFoundationManifestTags
        , testCase "separates durable namespaces from mount labels"
            separatesModuleOwnership
        , testCase "matches every current mathematical identity vector"
            matchesMathematicalIdentityVectors
        , testPropertyNamed "object builders preserve canonical bytes"
            "prop_objectIdBuilderBytes"
            prop_objectIdBuilderBytes
        , testCase "encodes native logical terms with stable distinct tags"
            encodesNativeLogicalTerms
        , testCase "validates recursive transparent object content"
            validatesTransparentObjectClosure
        , testCase "shares immutable global typing snapshots"
            sharesGlobalTypingSnapshots
        , testCase "extends checked objects through inherited dependencies"
            extendsThroughInheritedDependencies
        , testCase "composes local checked object contributions"
            composesCheckedObjectContributions
        , testCase "rejects mismatched object re-entry"
            rejectsMismatchedObjectReentry
        , testCase "validates proposition content and theorem closure"
            validatesPropositionAndTheorem
        , testCase "preserves nested checked evidence through reentry and forcing"
            preservesCheckedEvidence
        , testCase "round-trips deterministic epoch cache values"
            roundTripsEpochCacheValues
        , testCase "streams byte-identical cache digests across chunk boundaries"
            preservesStreamingCacheDigests
        , testCase "bounds decoder-directed cache allocations"
            boundsCacheDecoderAllocations
        , testCase "round-trips every core intrinsic cache code"
            roundTripsCoreIntrinsicCacheCodes
        , testCase "round-trips every foundation stable cache code"
            roundTripsFoundationStableCacheCodes
        , testCase "validates compact fact authority"
            validatesCompactFactAuthority
        , testCase "propagates candidate safety through local claims"
            propagatesCandidateSafety
        , testCase "rejects invalid integer list indices"
            rejectsInvalidListIndices
        ]

prop_objectIdBuilderBytes :: Property
prop_objectIdBuilderBytes = withTests 100 . property $ do
    family <- forAll Gen.enumBounded
    digestBytes <- forAll
        (ByteString.pack
            <$> Gen.list
                (Range.singleton 32)
                (Gen.word8 Range.constantBounded))
    digest <- evalMaybe (mathematicalDigestFromBytes digestBytes)
    let identity = Identity.objectId family digest
        builderBytes =
            LazyByteString.toStrict
                (Builder.toLazyByteString
                    (Identity.objectIdBuilder identity))
    builderBytes === Identity.encodeObjectId identity

sharesGlobalTypingSnapshots :: Assertion
sharesGlobalTypingSnapshots = do
    fixture <- makeIdentityFixture
    let closure = fixtureClosure fixture
        stale = Identity.globalTypingFromClosure closure
        transparentObject =
            Identity.transparentObject
                (fixtureTheory fixture)
                Core.TySet
                (Core.CIntrinsic Core.Empty)
        transparent = Identity.assertedObjectId transparentObject
    assertEqual
        "owner snapshot resolves checked object"
        (Just Core.TySet)
        (GlobalTyping.lookupGlobalType stale (fixtureIntrinsic fixture))
    assertEqual
        "owner snapshot rejects absent object"
        Nothing
        (GlobalTyping.lookupGlobalType stale transparent)
    extended <- expectRight
        (Identity.extendObjectClosure closure [transparentObject])
    let current = Identity.globalTypingFromClosure extended
    assertEqual
        "extended owner snapshot resolves new object"
        (Just Core.TySet)
        (GlobalTyping.lookupGlobalType current transparent)
    assertEqual
        "old snapshot keeps stale visibility"
        Nothing
        (GlobalTyping.lookupGlobalType stale transparent)
    case Identity.extendObjectClosure
            closure
            [ Identity.intrinsicObject
                (fixtureTheory fixture)
                Core.Empty
            ] of
        Left err ->
            assertEqual
                "duplicate extension remains rejected"
                (Identity.DuplicateAssertedObjectId
                    (fixtureIntrinsic fixture))
                err
        Right _extended ->
            assertFailure "duplicate extension was accepted"

extendsThroughInheritedDependencies :: Assertion
extendsThroughInheritedDependencies = do
    fixture <- makeIdentityFixture
    let inherited = fixtureClosure fixture
        parent = Identity.transparentObject (fixtureTheory fixture)
            Core.TySet (Core.CGlobal (fixtureIntrinsic fixture))
        child = Identity.transparentObject (fixtureTheory fixture)
            Core.TySet (Core.CGlobal (Identity.assertedObjectId parent))
    extended <- expectRight
        (Identity.extendObjectClosure inherited [child, parent])
    assertEqual "new dependency chain uses inherited checked objects"
        (Just Core.TySet)
        (Identity.lookupCheckedObjectType (Identity.assertedObjectId child) extended)
    assertEqual "only local objects were added"
        (Identity.checkedObjectCount inherited + 2)
        (Identity.checkedObjectCount extended)
    assertBool "prior closure remains unchanged"
        (not (Identity.checkedObjectMember (Identity.assertedObjectId child) inherited))
    case Identity.extendObjectClosure inherited [child] of
        Left failure -> assertEqual "missing local dependency"
            (Identity.TransparentObjectReferenceMissing
                (Identity.assertedObjectId child) (Identity.assertedObjectId parent))
            failure
        Right _ -> assertFailure "missing dependency was accepted"
    case Identity.extendObjectClosure inherited [parent, parent] of
        Left failure -> assertEqual "duplicate local declarations"
            (Identity.DuplicateAssertedObjectId (Identity.assertedObjectId parent))
            failure
        Right _ -> assertFailure "duplicate local declarations were coalesced"

composesCheckedObjectContributions :: Assertion
composesCheckedObjectContributions = do
    fixture <- makeIdentityFixture
    let theory = fixtureTheory fixture
        inherited = fixtureClosure fixture
        parent = Identity.transparentObject theory Core.TySet
            (Core.CGlobal (fixtureIntrinsic fixture))
        child = Identity.transparentObject theory Core.TySet
            (Core.CGlobal (Identity.assertedObjectId parent))
        localIds = Identity.assertedObjectId <$> [parent, child]
    producer <- expectRight
        (Identity.extendObjectClosure inherited [parent, child])
    contribution <- expectRight
        (Identity.checkedObjectContribution producer localIds)
    emptyClosure <- expectRight (Identity.validateObjectClosure theory [])
    case Identity.insertCheckedObjectContribution emptyClosure contribution of
        Left failure -> assertEqual "external dependency must be supplied"
            (Identity.CheckedContributionDependencyMissing (fixtureIntrinsic fixture))
            failure
        Right _ -> assertFailure "contribution captured its producer's ancestors"
    joined <- expectRight
        (Identity.insertCheckedObjectContribution inherited contribution)
    overlapping <- expectRight
        (Identity.insertCheckedObjectContribution joined contribution)
    assertEqual "compatible repeated contribution coalesces"
        (Identity.checkedObjectIds producer) (Identity.checkedObjectIds overlapping)
    for_ localIds \identity -> assertEqual "checked payload is preserved"
        (Identity.lookupCheckedObjectContent identity producer)
        (Identity.lookupCheckedObjectContent identity overlapping)
    case Identity.checkedObjectContribution inherited localIds of
        Left failure -> assertEqual "selection cannot invent a checked object"
            (Identity.CheckedContributionObjectMissing (Identity.assertedObjectId parent))
            failure
        Right _ -> assertFailure "absent local object was selected"

rejectsInvalidListIndices :: Assertion
rejectsInvalidListIndices = do
    assertEqual
        "negative zero-based index"
        (Nothing :: Maybe Natural)
        (zeroBasedIndex (-1))
    assertEqual
        "nonpositive one-based index"
        (Nothing :: Maybe Natural)
        (oneBasedIndex 0)
    assertEqual "valid one-based index" (Just 1) (oneBasedIndex 2)
    assertEqual
        "out-of-bounds natural index"
        (Nothing :: Maybe Text)
        (nth 2 ["only"])

roundTripsCoreIntrinsicCacheCodes :: Assertion
roundTripsCoreIntrinsicCacheCodes =
    for_ StableCode.allCoreIntrinsicTags \tag ->
        assertEqual
            ("cache round trip for " <> show tag)
            (Right tag)
            (decodeCache
                getCoreIntrinsicTagCache
                (encodeCache (putCoreIntrinsicTagCache tag)))

roundTripsFoundationStableCacheCodes :: Assertion
roundTripsFoundationStableCacheCodes = do
    for_ Foundation.allFoundationAxiomTags \tag -> do
        assertEqual
            ("foundation owner inverse for " <> show tag)
            (Right tag)
            (Foundation.foundationAxiomTagFromCode
                (Foundation.foundationAxiomTagCode tag))
        assertEqual
            ("foundation cache round trip for " <> show tag)
            (Right tag)
            (decodeCache
                getFoundationAxiomTagCache
                (encodeCache (putFoundationAxiomTagCache tag)))
    for_ Foundation.allKernelRuleTags \tag -> do
        assertEqual
            ("kernel-rule owner inverse for " <> show tag)
            (Right tag)
            (Foundation.kernelRuleTagFromCode
                (Foundation.kernelRuleTagCode tag))
        assertEqual
            ("kernel-rule cache round trip for " <> show tag)
            (Right tag)
            (decodeCache
                getKernelRuleTagCache
                (encodeCache (putKernelRuleTagCache tag)))

ordersFoundationManifestTags :: Assertion
ordersFoundationManifestTags = do
    foundation <- expectRight Foundation.checkedFoundation
    assertEqual "manifest format and compiled beta-eta calculus codes"
        (ByteString.pack [1, 1])
        (ByteString.take 2 (Identity.encodeFoundationManifest foundation))
    let (intrinsics, rules, axioms) =
            Identity.foundationManifestTags
    assertEqual
        "intrinsic stable-tag order"
        [ Core.Member
        , Core.Empty
        , Core.PairSet
        , Core.FamilyUnion
        , Core.PowerSet
        , Core.Sep
        , Core.Repl
        , Core.UnivOf
        , Core.ISetLfp
        , Core.GlobalChoice
        , Core.OrderedPair
        , Core.FirstProjection
        , Core.SecondProjection
        ]
        intrinsics
    assertEqual
        "kernel-rule stable-tag order"
        [ Foundation.SetLfpBound
        , Foundation.SetLfpLeast
        , Foundation.SetLfpFixed
        , Foundation.SetLfpInduct
        ]
        rules
    assertEqual
        "foundation-axiom stable-tag order"
        [ Foundation.EmptyCharacteristic
        , Foundation.PairSetCharacteristic
        , Foundation.FamilyUnionCharacteristic
        , Foundation.PowerSetCharacteristic
        , Foundation.SeparationCharacteristic
        , Foundation.ReplacementCharacteristic
        , Foundation.SetExtensionality
        , Foundation.SetInduction
        , Foundation.PropositionalExtensionality
        , Foundation.DoubleNegationElim
        , Foundation.UnivOfContains
        , Foundation.UnivOfTransitive
        , Foundation.UnivOfFamilyUnionClosed
        , Foundation.UnivOfPowerSetClosed
        , Foundation.UnivOfReplacementClosed
        , Foundation.UnivOfMinimal
        , Foundation.GlobalChoiceMember
        , Foundation.OrderedPairInjective
        , Foundation.OrderedPairFirst
        , Foundation.OrderedPairSecond
        ]
        axioms

separatesModuleOwnership :: Assertion
separatesModuleOwnership =
    withTemporaryDirectory "felix-module-owner" \root -> do
        writeFile (root Posix.</> "b.tex") ""
        mounts <- expectRight
            =<< prepareSourceMounts
                [(sourceMountId "display-only", root)]
        request <- expectRight (searchedRoot "b.tex")
        source <- expectRight =<< resolveRoot mounts request
        mount <- case sourceMountList mounts of
            [only] ->
                pure only
            _ ->
                assertFailure "expected one prepared mount"
                    >> fail "unreachable"
        relative <- expectRight (safeRelativePath "b.tex")
        let owner =
                moduleName (resolvedSourceAddress source)
        assertEqual
            "relative owner"
            relative
            (moduleNameRelativePath owner)
        assertEqual
            "namespace derives from the canonical root"
            (sourceNamespaceId (sourceMountRoot mount))
            (moduleNameNamespace owner)

matchesMathematicalIdentityVectors :: Assertion
matchesMathematicalIdentityVectors = do
    fixture <- makeIdentityFixture
    let vectors :: [(String, MathematicalDigest, Text)]
        vectors =
            [ ( "theory"
              , Identity.theoryIdDigest
                    (fixtureTheory fixture)
              , "b05c73812cec80934156b0dd4f04b7f929be6415881a06800d7372309aade65e"
              )
            , ( "intrinsic Empty"
              , Identity.objectIdDigest
                    (fixtureIntrinsic fixture)
              , "78502623b518ef8617f67a1d08aee4bf94b9a1b4b61727d4de6f357a84a34956"
              )
            , ( "transparent Empty"
              , Identity.objectIdDigest
                    (fixtureTransparent fixture)
              , "8bc12933e84288e59cefe382f9b5f4facb69e3bbccfb5720ffccfbd74dc6b3eb"
              )
            , ( "opaque signature"
              , Identity.objectIdDigest
                    (fixtureOpaque fixture)
              , "ed1a6fd55c84d411da7c8c21fb114201bb0ce6a1cbe9e91fbcb885e8eb1a9bb0"
              )
            , ( "proposition"
              , Identity.propositionIdDigest
                    (Identity.checkedPropositionId
                        (fixtureProposition fixture))
              , "688b2566b505a2f124717d9e3a072bfe99c6b6ca089ac3ff1ddccf25094607cb"
              )
            , ( "theorem"
              , Identity.theoremIdDigest
                    (fixtureTheorem fixture)
              , "5cb5f35ec54ab6b7347e1a71bb5374b545463404421cdbdf0508c983d86ffbf5"
              )
            , ( "structure field"
              , Identity.fieldIdDigest
                    (Identity.fieldId
                        (fixtureOwner fixture)
                        (localDeclarationOrdinal 2)
                        (structureFieldSlot 0))
              , "70c24ad0e41e23ef96a61d8bee3adbd12ef47c017886f0b3fe8116ea435c35dc"
              )
            ]
    assertEqual
        "current mathematical identity vectors"
        [ (description, expected)
        | (description, _digest, expected) <- vectors
        ]
        [ (description, mathematicalDigestHex digest)
        | (description, digest, _expected) <- vectors
        ]
    assertEqual
        "opaque declaration seed"
        "0802daf9e7fe0df36cbcd63973027880660f50f84796e4a86990695388ed5dea"
        (mathematicalDigestHex
            (Identity.opaqueDeclarationSeedDigest
                (fixtureOpaqueSeed fixture)))
    mounts <- prepareSourceMounts [(sourceMountId "vector", "/")]
        >>= expectRight
    root <- case sourceMountList mounts of
        [mount] -> pure (sourceMountRoot mount)
        _ -> assertFailure "unexpected vector mount count"
            >> fail "unreachable"
    relative <- expectRight (safeRelativePath "a/b.tex")
    let ordinaryNamespace = sourceNamespaceId root
        ordinaryModule = moduleNameFromParts ordinaryNamespace relative
        reservedNamespace = moduleNameNamespace preludeModuleName
        sourceVectors :: [(String, Text, Text)]
        sourceVectors =
            [ ( "ordinary source namespace"
              , "e15c6697cdb22d3210dc4e8f311ca4f89b43877fa60a17fd0e73de7fdae2a1f1"
              , mathematicalDigestHex
                    (sourceNamespaceDigest ordinaryNamespace)
              )
            , ( "reserved prelude namespace"
              , "a2b3055ca4364d18b0fb2c998f6289b09dce24145a6a85569724c92adb3f6d3c"
              , mathematicalDigestHex
                    (sourceNamespaceDigest reservedNamespace)
              )
            , ( "ordinary module input record"
              , "e15c6697cdb22d3210dc4e8f311ca4f89b43877fa60a17fd0e73de7fdae2a1f102016105622e746578"
              , hex (encodeModuleName ordinaryModule)
              )
            , ( "prelude module input record"
              , "a2b3055ca4364d18b0fb2c998f6289b09dce24145a6a85569724c92adb3f6d3c01077072656c756465"
              , hex (encodeModuleName preludeModuleName)
              )
            ]
    assertEqual "source and module vectors"
        [ (description, expected)
        | (description, expected, _actual) <- sourceVectors
        ]
        [ (description, actual)
        | (description, _expected, actual) <- sourceVectors
        ]
    assertEqual
        "family domains remain distinct"
        (length vectors)
        (Set.size
            (Set.fromList
                [ digest
                | (_description, digest, _expected) <- vectors
                ]))

encodesNativeLogicalTerms :: Assertion
encodesNativeLogicalTerms = do
    let terms :: [(Word8, Core.CanonicalTerm Void)]
        terms =
            [ (0x08, Core.CTruth)
            , (0x09, Core.CNot Core.CTruth)
            , (0x0a, Core.CAnd Core.CTruth Core.CFalsum)
            , (0x0b, Core.COr Core.CTruth Core.CFalsum)
            , (0x0f,
                Core.CExists Core.TySet
                    (Core.CAnd
                        (Core.CNot Core.CTruth)
                        (Core.COr Core.CTruth Core.CFalsum)))
            ]
        nested :: Core.CanonicalTerm Void
        nested =
            Core.CExists Core.TySet
                (Core.CAnd
                    (Core.CNot Core.CTruth)
                    (Core.COr Core.CTruth Core.CFalsum))
    traverse_
        (\(expectedTag, term) ->
            assertEqual
                ("mathematical tag for " <> show term)
                (Just expectedTag)
                (fst <$> ByteString.uncons
                    (encodeCanonicalTerm absurd term)))
        terms
    assertEqual
        "native canonical cache round trip"
        (Right nested)
        (decodeCache
            (getCanonicalTermCache
                (fail "closed native term requested a global"))
            (encodeCache
                (putCanonicalTermCache absurd nested)))

validatesTransparentObjectClosure :: Assertion
validatesTransparentObjectClosure = do
    fixture <- makeIdentityFixture
    let theory = fixtureTheory fixture
        child = fixtureTransparent fixture
        parentBody = Core.CGlobal child
        parentObject =
            Identity.transparentObject theory Core.TySet parentBody
        parent = Identity.assertedObjectId parentObject
        assertions =
            [ parentObject
            , Identity.transparentObject
                theory Core.TySet (Core.CIntrinsic Core.Empty)
            , Identity.intrinsicObject theory Core.Empty
            ]
    closure <- expectRight
        (Identity.validateObjectClosure theory assertions)
    assertEqual
        "all recursively checked objects"
        (Set.fromList
            [ fixtureIntrinsic fixture
            , child
            , parent
            ])
        (Identity.checkedObjectIds closure)
    assertEqual
        "parent type"
        (Just Core.TySet)
        (Identity.lookupCheckedObjectType parent closure)

rejectsMismatchedObjectReentry :: Assertion
rejectsMismatchedObjectReentry = do
    fixture <- makeIdentityFixture
    let theory = fixtureTheory fixture
        body = Core.CIntrinsic Core.Empty
        expected = Identity.transparentObject theory Core.TySet body
        supplied = Identity.transparentObjectId
            theory Core.TySet (Core.CIntrinsic Core.PairSet)
        expectedId = Identity.assertedObjectId expected
        bodyBytes = encodeCanonicalTerm Identity.objectIdBuilder body
    reentered <- expectRight
        (Identity.reenterCanonicalTerm
            (identifyCanonicalTermBytes bodyBytes)
            bodyBytes)
    assertEqual
        "payload mismatch"
        (Left (Identity.ObjectReentryIdMismatch supplied expectedId))
        (Identity.reenterTransparentObject
            theory supplied Core.TySet reentered)
    let intrinsic = Identity.assertedObjectId
            (Identity.intrinsicObject theory Core.Empty)
    assertEqual
        "family mismatch"
        (Left
            (Identity.ObjectReentryFamilyMismatch
                intrinsic
                Identity.TransparentObject
                Identity.IntrinsicObject))
        (Identity.reenterTransparentObject
            theory intrinsic Core.TySet reentered)

validatesPropositionAndTheorem :: Assertion
validatesPropositionAndTheorem = do
    fixture <- makeIdentityFixture
    let proposition =
            fixtureProposition fixture
        reference =
            fixtureTheoremRef fixture
    assertEqual
        "theorem retains its theory"
        (fixtureTheory fixture)
        (Identity.theoremRefTheory reference)
    assertEqual
        "theorem retains its proposition"
        (Identity.checkedPropositionId proposition)
        (Identity.theoremRefProposition reference)
    falsum <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            Core.CFalsum)
    case
        Identity.validateAssertedPropositionContent
            (fixtureClosure fixture)
            (Identity.checkedPropositionId falsum)
            (Core.frozenCoreTerm
                (Identity.checkedPropositionTerm proposition)) of
        Left
            (Identity.PropositionIdPayloadMismatch
                supplied
                computed) -> do
                    assertEqual
                        "supplied proposition ID"
                        (Identity.checkedPropositionId falsum)
                        supplied
                    assertEqual
                        "computed proposition ID"
                        (Identity.checkedPropositionId proposition)
                        computed
        Left other ->
            assertFailure
                ("expected proposition ID disagreement, got "
                    <> show other)
        Right _ ->
            assertFailure
                "expected proposition ID disagreement, got Right"

preservesCheckedEvidence :: Assertion
preservesCheckedEvidence = do
    fixture <- makeIdentityFixture
    let closure = fixtureClosure fixture
        term = Core.CForall Core.TySet
            (Core.CAnd Core.CTruth
                (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)))
        bytes = encodeCanonicalTerm Identity.objectIdBuilder term
    proposition <- expectRight
        (Identity.validatePropositionContent closure term)
    forced <- evaluate (force proposition)
    let frozen = Identity.checkedPropositionTerm forced
        context = [Core.TyArrow Core.TySet Core.TyProp, Core.TySet]
    embedded <- evaluate (force (Core.embedClosedCore context frozen))
    separatelyChecked <- expectRight
        (Core.checkScopedCanonicalCore
            (Identity.globalTypingFromClosure closure) context term)
    assertEqual "embedding preserves checked context, type, and body"
        separatelyChecked embedded
    assertEqual "checked proposition identity agrees with its body"
        (Identity.propositionIdOf (Core.frozenCoreTerm frozen))
        (Identity.checkedPropositionId forced)
    reentered <- expectRight (Identity.identifyAndReenterCanonicalTerm bytes)
    assertEqual "reentered root is the exact canonical byte root"
        (identifyCanonicalTermBytes bytes)
        (Identity.reenteredCanonicalTermRoot reentered)
    candidate <- expectRight
        (Identity.storedPropositionCandidate
            (Identity.checkedPropositionId forced) reentered)
    checkedAgain <- expectRight
        (Identity.validateStoredPropositionCandidate closure candidate)
    assertEqual "stored candidate preserves checked body"
        frozen (Identity.checkedPropositionTerm checkedAgain)
    assertEqual "stored candidate preserves checked identity"
        (Identity.checkedPropositionId forced)
        (Identity.checkedPropositionId checkedAgain)

roundTripsEpochCacheValues :: Assertion
roundTripsEpochCacheValues = do
    fixture <- makeIdentityFixture
    let field =
            Identity.fieldId
                (fixtureOwner fixture)
                (localDeclarationOrdinal 2)
                (structureFieldSlot 0)
    assertEqual
        "field identity cache round trip"
        (Right field)
        (decodeCache
            Identity.getFieldIdCache
            (encodeCache (Identity.putFieldIdCache field)))
    assertEqual
        "constructive theorem reference cache round trip"
        (Right (fixtureTheoremRef fixture))
        (decodeCache
            Identity.getTheoremRefCache
            (encodeCache
                (Identity.putTheoremRefCache
                    (fixtureTheoremRef fixture))))
    let theoremCacheBytes = encodeCache
            (Identity.putTheoremRefCache
                (fixtureTheoremRef fixture))
        theoremIdentityBytes = Identity.encodeTheoremRef
            (fixtureTheoremRef fixture)
    assertEqual
        "current cache and identity theorem-reference records agree"
        theoremIdentityBytes theoremCacheBytes
    let ascending =
            Map.fromList [("a", 1 :: Natural), ("b", 2)]
        putMap =
            putCanonicalCacheMap
                putCacheText
                putCacheNatural
    assertEqual
        "canonical cache map round trip"
        (Right ascending)
        (decodeCache
            (getCanonicalCacheMap
                getCacheText
                getCacheNatural)
            (encodeCache (putMap ascending)))

preservesStreamingCacheDigests :: Assertion
preservesStreamingCacheDigests = do
    let sizes = [0, 1, 4095, 4096, 4097, 32767, 32768, 32769, 65535, 65536, 65537, 1048576]
        cases = [[], [""], ["", ""], ["a", "bc"], ["ab", "c"]]
            <> [["prefix", ByteString.replicate size 0xa5, "suffix"] | size <- sizes]
        reference domain fields = mathematicalDigestBytes
            (hashBlake2b256 ("FELIX\NULCACHE\NUL" <> encodeCache do
                putCacheText domain
                putCacheList putCacheBytes fields))
    for_ ["", "cache-test", "\955\8594\960"] \domain ->
        for_ cases \fields ->
            cacheDigestBytes (hashCacheFields domain fields) @?= reference domain fields
    assertBool "domain lengths separate fields"
        (hashCacheFields "ab" ["c"] /= hashCacheFields "a" ["bc"])
    assertBool "field lengths separate concatenations"
        (hashCacheFields "test" ["a", "bc"] /= hashCacheFields "test" ["ab", "c"])
    assertBool "field order remains significant"
        (hashCacheFields "test" ["a", "b"] /= hashCacheFields "test" ["b", "a"])
    assertBool "an empty field differs from no fields"
        (hashCacheFields "test" [] /= hashCacheFields "test" [""])
    cacheEpochValue currentCacheEpoch @?= 180

boundsCacheDecoderAllocations :: Assertion
boundsCacheDecoderAllocations = do
    expectResource DecoderByteFieldBytes
        (decodeCache getCacheBytes (countOnly (maximumCacheByteStringBytes + 1)))
    expectResource DecoderIntegerBytes
        (decodeCache getCacheNatural (countOnly (maximumCacheMagnitudeBytes + 1)))
    expectResource DecoderListElements
        (decodeCache (getCacheList getCacheTag) (countOnly (maximumCacheListElements + 1)))
    expectResource DecoderByteFieldBytes
        (decodeCache getCacheBytes (countOnly (maxBound :: Word64)))
    case decodeCache getCacheBytes (countOnly 1) of
        Left CacheBinaryDecodeError{} ->
            pure ()
        other ->
            assertFailure
                ("expected truncated cache byte string, got " <> show other)
  where
    countOnly count =
        encodeCache (Put.putWord64be count)

expectResource :: Show value => DecoderResource -> Either CacheDecodeError value -> Assertion
expectResource resource = \case
    Left (CacheResourceLimitExceeded failure) -> decoderLimitedResource failure @?= resource
    other -> assertFailure ("expected resource limit, got " <> show other)

validatesCompactFactAuthority :: Assertion
validatesCompactFactAuthority = do
    fixture <- makeIdentityFixture
    let reference = fixtureTheoremRef fixture
        sourceKinds =
            Authority.singletonEscapeKind Authority.SourceAxiom
        bothKinds =
            Authority.escapeKinds
                [Authority.Omitted, Authority.SourceAxiom]
        sourceTarget =
            Authority.factAuthority
                reference
                (Authority.authoritySafety sourceKinds)
        bothTarget =
            Authority.factAuthority
                reference
                (Authority.authoritySafety bothKinds)
        proofUse =
            Authority.UsesExternalProof
            ( Authority.preparedRequestId
                Authority.PreparedRequestFof
                Authority.PreparedRequestDirect
                "first"
            :| [ Authority.preparedRequestId
                Authority.PreparedRequestFof
                Authority.PreparedRequestDirect
                "first"
            , Authority.preparedRequestId
                Authority.PreparedRequestFof
                Authority.PreparedRequestDirect
                "second"
               ]
            )
        directRequest =
            Authority.preparedRequestId
                Authority.PreparedRequestFof
                Authority.PreparedRequestDirect
                "same bytes"
        indirectRequest =
            Authority.preparedRequestId
                Authority.PreparedRequestFof
                Authority.PreparedRequestIndirect
                "same bytes"
        directAuthorizations =
            [ Authority.CheckedKernelConstruction
                (Authority.FoundationLeaf
                    Foundation.EmptyCharacteristic)
            , Authority.CheckedKernelConstruction
                (Authority.GuardedFoundationRules
                    (Authority.guardedRuleSet
                        (Foundation.SetLfpBound :| [])))
            , Authority.CheckedKernelConstruction
                (Authority.CheckedDefinitionEquation
                    (fixtureIntrinsic fixture))
            , Authority.CheckedKernelConstruction
                (Authority.CheckedDefinitionProjection
                    (fixtureIntrinsic fixture)
                    (ConjunctionLeft (ConjunctionRight ConjunctionHere)))
            , Authority.CheckedKernelConstruction
                (Authority.CheckedSetConstructionExtensionality
                    (fixtureIntrinsic fixture)
                    (hashCacheFields
                        "test-named-construction" ["checked"]))
            , Authority.CheckedKernelConstruction
                (Authority.CheckedStructureLaw
                    Authority.StructureAggregateProjection)
            , Authority.CheckedSourceProof proofUse
            , Authority.CheckedKernelConstruction Authority.CheckedDerivedConstruction
            , Authority.CheckedKernelConstruction
                (Authority.CheckedImplementationDefinition (fixtureIntrinsic fixture))
            , Authority.SourceAxiomAuthorization
            , Authority.OmittedAuthorization
            ]
    sourceCertificate <- expectRight
        (Authority.validationCertificate
            sourceTarget
            Authority.SourceAxiomAuthorization)
    proofCertificate <- expectRight
        (Authority.validationCertificate
            bothTarget
            (Authority.CheckedSourceProof proofUse))
    assertEqual
        "escape bits have canonical order"
        [Authority.SourceAxiom, Authority.Omitted]
        (Authority.escapeKindsToList bothKinds)
    forM_
        [ Authority.cleanAuthoritySafety
        , Authority.authoritySafety sourceKinds
        , Authority.authoritySafety bothKinds
        ] \safety -> do
            forced <- evaluate (force safety)
            assertEqual "forced authority retains canonical encoding"
                (Right safety)
                (decodeCache Authority.getAuthoritySafetyCache
                    (encodeCache (Authority.putAuthoritySafetyCache forced)))
    traverse_
        (\direct ->
            assertEqual
                ("direct authorization round trip: " <> show direct)
                (Right direct)
                (decodeCache
                    Authority.getDirectAuthorizationCache
                    (encodeCache
                        (Authority.putDirectAuthorizationCache
                            direct))))
        directAuthorizations
    assertBool "retired trusted-compilation authority is not decodable"
        (isLeft (decodeCache Authority.getDirectAuthorizationCache
            (encodeCache do
                putCacheTag 0x02 -- former TrustedCompilation
                putCacheTag 0x00 -- former DatatypeCompilation
                Identity.putObjectIdCache (fixtureIntrinsic fixture)
                putCacheList Identity.putObjectIdCache [fixtureIntrinsic fixture]
                putCacheList Identity.putTheoremRefCache [reference])))
    let deepProjection = Authority.CheckedKernelConstruction
            (Authority.CheckedDefinitionProjection (fixtureIntrinsic fixture)
                (foldr (const ConjunctionLeft) ConjunctionHere [1 .. 300 :: Int]))
    expectResource DecoderDepth
        (decodeCache Authority.getDirectAuthorizationCache
            (encodeCache (Authority.putDirectAuthorizationCache deepProjection)))
    assertEqual
        "certificate cache retains repeated ordered requests"
        (Right proofCertificate)
        (decodeCache
            Authority.getValidationCertificateCache
            (encodeCache
                (Authority.putValidationCertificateCache
                    proofCertificate)))
    assertBool
        "cache rejects external proof use without a request"
        (isLeft
            (decodeCache
                Authority.getDirectAuthorizationCache
                (encodeCache do
                    putCacheTag 0x01
                    putCacheTag 0x01
                    putCacheList Authority.putPreparedRequestIdCache [])))
    assertBool
        "request mode participates in exact request identity"
        (directRequest /= indirectRequest)
    assertEqual
        "prepared-request cache identity vector"
        ("a15d3e1cb9e4ab34f4a5fb3399d0e5e3252eb9ad79e17d4a107d26187a51aaf6")
        (hex
            (encodeCache
                (Authority.putPreparedRequestIdCache
                    directRequest)))
    assertEqual
        "source certificate round trip"
        (Right sourceCertificate)
        (decodeCache
            Authority.getValidationCertificateCache
            (encodeCache
                (Authority.putValidationCertificateCache
                    sourceCertificate)))
    assertBool
        "source axiom requires its exact singleton safety"
        (isLeft
            (Authority.validationCertificate
                bothTarget
                Authority.SourceAxiomAuthorization))
    assertBool
        "omitted authorization requires its distinct bit"
        (isLeft
            (Authority.validationCertificate
                sourceTarget
                Authority.OmittedAuthorization))
    assertBool
        "cache rejects an empty escape-backed value"
        (isLeft
            (decodeCache
                Authority.getAuthoritySafetyCache
                (encodeCache do
                    putCacheTag 0x01
                    putCacheTag 0x00)))
    let taintedCandidate =
            Authority.addCandidateEscape
                Authority.SourceAxiom
                Authority.initialCandidateSafety
    assertEqual
        "candidate completion freezes accumulated safety"
        sourceTarget
        (Authority.candidateFactAuthority
            reference
            taintedCandidate)

propagatesCandidateSafety :: Assertion
propagatesCandidateSafety = do
    fixture <- makeIdentityFixture
    let reference = fixtureTheoremRef fixture
        imported =
            Authority.factAuthority
                reference
                (Authority.authoritySafety
                    (Authority.singletonEscapeKind
                        Authority.SourceAxiom))
    afterImported <- expectRight
        (Authority.accumulateFactSafety
            reference
            imported
            Authority.initialCandidateSafety)
    -- A local claim shares the enclosing candidate value; citing that claim
    -- does not create a second support representation.
    afterLocalClaim <- expectRight
        (Authority.accumulateFactSafety
            reference
            (Authority.factAuthority
                reference
                Authority.cleanAuthoritySafety)
            afterImported)
    let finalSafety =
            Authority.addCandidateEscape
                Authority.Omitted
                afterLocalClaim
    assertEqual
        "local claim retains prior safety and direct omission"
        [Authority.SourceAxiom, Authority.Omitted]
        (Authority.escapeKindsToList
            (Authority.authoritySafetyEscapeKinds
                (Authority.candidateSafetyAuthority finalSafety)))

data IdentityFixture = IdentityFixture
    { fixtureTheory :: !Identity.TheoryId
    , fixtureOwner :: !ModuleName
    , fixtureIntrinsic :: !Identity.ObjectId
    , fixtureTransparent :: !Identity.ObjectId
    , fixtureOpaqueSeed :: !Identity.OpaqueDeclarationSeed
    , fixtureOpaque :: !Identity.ObjectId
    , fixtureClosure :: !Identity.CheckedObjectClosure
    , fixtureProposition :: !Identity.CheckedPropositionContent
    , fixtureTheoremRef :: !Identity.TheoremRef
    , fixtureTheorem :: !Identity.TheoremId
    }

makeIdentityFixture :: IO IdentityFixture
makeIdentityFixture = do
    foundation <- expectRight Foundation.checkedFoundation
    let namespaceDigest =
            hashBlake2b256 "identity-fixture-source-namespace"
    relative <- expectRight (safeRelativePath "b.tex")
    let theory =
            Identity.theoryId foundation
        intrinsicObject = Identity.intrinsicObject theory Core.Empty
        intrinsic = Identity.assertedObjectId intrinsicObject
        transparentObject = Identity.transparentObject
            theory Core.TySet (Core.CIntrinsic Core.Empty)
        transparent = Identity.assertedObjectId transparentObject
        owner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest
                    namespaceDigest)
                relative
        seed =
            Identity.opaqueDeclarationSeed
                owner
                (localDeclarationOrdinal 2)
                SignatureDeclaration
                (generatedObjectSlot 0)
        opaque =
            Identity.opaqueObjectId
                theory
                seed
                Core.TySet
    closure <- expectRight
        (Identity.validateObjectClosure
            theory
            [intrinsicObject])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure
            (Core.CEq
                Core.TySet
                (Core.CGlobal intrinsic)
                (Core.CGlobal intrinsic)))
    let reference =
            Identity.theoremRef
                theory
                (Identity.checkedPropositionId proposition)
    pure
        IdentityFixture
            { fixtureTheory = theory
            , fixtureOwner = owner
            , fixtureIntrinsic = intrinsic
            , fixtureTransparent = transparent
            , fixtureOpaqueSeed = seed
            , fixtureOpaque = opaque
            , fixtureClosure = closure
            , fixtureProposition = proposition
            , fixtureTheoremRef = reference
            , fixtureTheorem =
                Identity.theoremId reference
            }

hex :: ByteString.ByteString -> Text
hex =
    Text.pack
        . concatMap byteHex
        . ByteString.unpack
  where
    byteHex byte =
        let digits = "0123456789abcdef"
            high = fromIntegral (byte `div` 16)
            low = fromIntegral (byte `mod` 16)
        in [digits `at` high, digits `at` low]

    at characters index =
        fromMaybe
            (impossible "hex digit index")
            (nth index characters)

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err ->
        assertFailure (show err) >> fail "unreachable"
    Right value ->
        pure value
