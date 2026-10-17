{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.MathCodec (unitTests) where

import Base
import Felix.Checking.Core qualified as Core
import Felix.Checking.Core.StableCode qualified as StableCode
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Cache.Codec qualified as Cache
import Felix.Math.Codec

import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List qualified as List
import Data.Word (Word8)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)



unitTests :: TestTree
unitTests =
    testGroup "mathematical codec"
        [ testCase "matches published BLAKE2b-256 vectors"
            matchesBlake2b256Vectors
        , testCase "round-trips compact scalar primitives"
            roundTripsCompactScalars
        , testCase "owns complete compact stable-code tables"
            checksStableCodes
        , testCase "round-trips every canonical term constructor"
            roundTripsCanonicalTerms
        , testCase "rejects noncanonical term inputs"
            rejectsNoncanonicalTermInputs
        , testCase "agrees across strict and lazy hash sinks"
            agreesAcrossHashSinks
        , testCase "preserves checked term re-entry evidence"
            preservesTermReentryEvidence
        , testPropertyNamed "generated terms round-trip canonically"
            "prop_canonicalTermRoundTrip"
            prop_canonicalTermRoundTrip
        ]

matchesBlake2b256Vectors :: Assertion
matchesBlake2b256Vectors = do
    assertEqual "empty"
        "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"
        (mathematicalDigestHex (hashBlake2b256 ByteString.empty))
    assertEqual "abc"
        "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319"
        (mathematicalDigestHex (hashBlake2b256 "abc"))

roundTripsCompactScalars :: Assertion
roundTripsCompactScalars = do
    let naturals = [0, 1, 127, 128, 255, 624485, 2 ^ (80 :: Int)]
        integers = [0, -1, 1, -2, 2, -(2 ^ (80 :: Int)), 2 ^ (80 :: Int)]
        coreTypes =
            [ Core.TyProp
            , Core.TySet
            , Core.TySet `Core.TyArrow` Core.TyProp
            , Core.TyProp `Core.TyArrow`
                (Core.TySet `Core.TyArrow` Core.TySet)
            ]
    traverse_
        (\value -> assertEqual ("natural " <> show value) (Right value)
            (decodeCompactNatural
                (builderBytes (compactNaturalBuilder value))))
        naturals
    traverse_
        (\value -> assertEqual ("integer " <> show value) (Right value)
            (decodeCompactInteger
                (builderBytes (compactIntegerBuilder value))))
        integers
    traverse_
        (\value -> assertEqual ("type " <> show value) (Right value)
            (decodeCompactCoreType
                (builderBytes (compactCoreTypeBuilder value))))
        coreTypes
    assertEqual "ULEB reference"
        (ByteString.pack [0xe5, 0x8e, 0x26])
        (builderBytes (compactNaturalBuilder 624485))
    assertEqual "ZigZag sequence"
        (ByteString.pack [0x00, 0x01, 0x02, 0x03, 0x04])
        (ByteString.concat
            (builderBytes . compactIntegerBuilder <$> [0, -1, 1, -2, 2]))
    assertEqual "overlong ULEB"
        (Left MathematicalOverlongUleb)
        (decodeCompactNatural (ByteString.pack [0x80, 0x00]))
    assertEqual "unterminated ULEB"
        (Left (MathematicalUnexpectedEnd 1 0))
        (decodeCompactNatural (ByteString.singleton 0x80))

checksStableCodes :: Assertion
checksStableCodes = do
    assertUnique "identity kinds"
        (mathematicalIdentityKindCode <$> allMathematicalIdentityKinds)
    assertEqual "intrinsic compaction" (Right Core.UnivOf)
        (StableCode.coreIntrinsicTagFromCode 0x07)
    assertEqual "axiom compaction"
        (Right Foundation.SetExtensionality)
        (Foundation.foundationAxiomTagFromCode 0x06)
    assertUnique "intrinsic"
        (StableCode.coreIntrinsicTagCode
            <$> StableCode.allCoreIntrinsicTags)
    assertUnique "axiom"
        (Foundation.foundationAxiomTagCode
            <$> Foundation.allFoundationAxiomTags)
    traverse_
        (\tag -> assertEqual ("intrinsic " <> show tag) (Right tag)
            (StableCode.coreIntrinsicTagFromCode
                (StableCode.coreIntrinsicTagCode tag)))
        StableCode.allCoreIntrinsicTags
    traverse_
        (\tag -> assertEqual ("axiom " <> show tag) (Right tag)
            (Foundation.foundationAxiomTagFromCode
                (Foundation.foundationAxiomTagCode tag)))
        Foundation.allFoundationAxiomTags
    traverse_
        (\tag -> assertEqual ("rule " <> show tag) (Right tag)
            (Foundation.kernelRuleTagFromCode
                (Foundation.kernelRuleTagCode tag)))
        Foundation.allKernelRuleTags
  where
    assertUnique caseName codes =
        assertEqual caseName codes (List.nub codes)

roundTripsCanonicalTerms :: Assertion
roundTripsCanonicalTerms =
    traverse_
        (\term -> assertEqual (show term) (Right term)
            (decodeCanonicalTerm getMathematicalWord8
                (encodeCanonicalTerm Builder.word8 term)))
        canonicalTermFixtures

rejectsNoncanonicalTermInputs :: Assertion
rejectsNoncanonicalTermInputs = do
    assertEqual "unknown term tag"
        (Left (MathematicalUnknownTermTag 0xff))
        (decodeCanonicalTerm getMathematicalWord8
            (ByteString.singleton 0xff))
    assertEqual "truncated application"
        (Left (MathematicalUnexpectedEnd 1 0))
        (decodeCanonicalTerm getMathematicalWord8
            (ByteString.pack [0x05, 0x08]))
    assertEqual "overlong bound index"
        (Left MathematicalOverlongUleb)
        (decodeCanonicalTerm getMathematicalWord8
            (ByteString.pack [0x00, 0x80, 0x00]))
    assertEqual "trailing term bytes"
        (Left (MathematicalTrailingBytes 1))
        (decodeCanonicalTerm getMathematicalWord8
            (ByteString.pack [0x08, 0x08]))
    assertEqual "unknown intrinsic"
        (Left (MathematicalUnknownIntrinsicTag 0xff))
        (decodeCanonicalTerm getMathematicalWord8
            (ByteString.pack [0x02, 0xff]))

agreesAcrossHashSinks :: Assertion
agreesAcrossHashSinks =
    traverse_
        (\term ->
            let bytes = encodeCanonicalTerm Builder.word8 term
            in assertEqual (show term)
                (identifyCanonicalTerm Builder.word8 term)
                (identifyCanonicalTermBytes bytes))
        canonicalTermFixtures

preservesTermReentryEvidence :: Assertion
preservesTermReentryEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        object = Identity.intrinsicObject theory Core.Empty
        objectId = Identity.assertedObjectId object
        term = Core.CEq Core.TySet
            (Core.CGlobal objectId)
            (Core.CGlobal objectId)
    closure <- expectRight
        (Identity.validateObjectClosure theory [object])
    _ <- expectRight
        (Identity.validatePropositionContent closure term)

    let termBytes = encodeCanonicalTerm
            Identity.objectIdBuilder term
        termRoot = identifyCanonicalTermBytes termBytes
    reentered <- expectRight
        (Identity.reenterCanonicalTerm termRoot termBytes)
    assertEqual "term re-entry body" term
        (Identity.reenteredCanonicalTermBody reentered)
    identified <- expectRight
        (Identity.identifyAndReenterCanonicalTerm termBytes)
    assertEqual "identified term re-entry" reentered identified
    assertEqual "verified term root"
        (Right ())
        (Identity.verifyCanonicalTermRoot termRoot termBytes)
    let wrongTermRoot = identifyCanonicalTermBytes
            (encodeCanonicalTerm
                Identity.objectIdBuilder Core.CTruth)
    assertEqual "term root mismatch"
        (Left (Identity.TermRootMismatch wrongTermRoot termRoot))
        (Identity.reenterCanonicalTerm wrongTermRoot termBytes)
    assertEqual "verified term root mismatch"
        (Left (Identity.TermRootMismatch wrongTermRoot termRoot))
        (Identity.verifyCanonicalTermRoot wrongTermRoot termBytes)

    termMathematicalDigest <-
        maybe
            (assertFailure "term digest length invariant"
                >> fail "unreachable")
            pure
            (mathematicalDigestFromBytes
                (termDigestBytes termRoot))
    let propositionIdentity =
            either
                (error . show)
                id
                (Cache.decodeCache Identity.getPropositionIdCache
                    (Cache.encodeCache
                        (Cache.putMathematicalDigestCache termMathematicalDigest)))
    stored <- expectRight
        (Identity.storedPropositionCandidate
            propositionIdentity
            reentered)
    assertEqual "stored phase body" term
        (Identity.storedPropositionCandidateTerm stored)

prop_canonicalTermRoundTrip :: Property
prop_canonicalTermRoundTrip = withTests 100 . property $ do
    term <- forAll generatedCanonicalTerm
    let bytes = encodeCanonicalTerm Builder.word8 term
    decodeCanonicalTerm getMathematicalWord8 bytes === Right term
    identifyCanonicalTerm Builder.word8 term
        === identifyCanonicalTermBytes bytes

generatedCanonicalTerm :: Gen (Core.CanonicalTerm Word8)
generatedCanonicalTerm =
    Gen.sized generate
  where
    generate size
        | size <= 1 = leaf
        | otherwise =
            Gen.frequency
                [ (5, leaf)
                , (2, unary size Core.CNot)
                , (2, unary size (Core.CLam Core.TySet))
                , (2, unary size (Core.CForall Core.TyProp))
                , (2, unary size (Core.CExists Core.TySet))
                , (2, binary size Core.CApp)
                , (2, binary size Core.CAnd)
                , (2, binary size Core.COr)
                , (2, binary size Core.CImp)
                , (2, binary size (Core.CEq Core.TySet))
                ]

    leaf =
        Gen.choice
            [ Core.CBound <$> Gen.integral (Range.linear 0 100000)
            , Core.CGlobal <$> Gen.word8 Range.constantBounded
            , Core.CIntrinsic <$> Gen.element StableCode.allCoreIntrinsicTags
            , Core.CLogicalSelect <$> coreType
            , Core.COpaqueInteger
                <$> Gen.integral (Range.linear (-1000000) 1000000)
            , pure Core.CFalsum
            , pure Core.CTruth
            ]

    unary size constructor =
        constructor <$> Gen.resize (size `div` 2) generatedCanonicalTerm

    binary size constructor =
        constructor
            <$> Gen.resize (size `div` 2) generatedCanonicalTerm
            <*> Gen.resize (size `div` 2) generatedCanonicalTerm

    coreType =
        Gen.element
            [ Core.TyProp
            , Core.TySet
            , Core.TySet `Core.TyArrow` Core.TyProp
            ]

canonicalTermFixtures :: [Core.CanonicalTerm Word8]
canonicalTermFixtures =
    [ Core.CBound 0
    , Core.CGlobal 23
    , Core.CIntrinsic Core.UnivOf
    , Core.CLogicalSelect (Core.TySet `Core.TyArrow` Core.TyProp)
    , Core.COpaqueInteger (-624485)
    , Core.CApp Core.CTruth Core.CFalsum
    , Core.CLam Core.TySet (Core.CBound 0)
    , Core.CFalsum
    , Core.CTruth
    , Core.CNot Core.CFalsum
    , Core.CAnd Core.CTruth Core.CFalsum
    , Core.COr Core.CFalsum Core.CTruth
    , Core.CImp Core.CTruth Core.CFalsum
    , Core.CEq Core.TySet (Core.CGlobal 1) (Core.CGlobal 2)
    , Core.CForall Core.TySet
        (Core.CImp Core.CTruth (Core.CNot Core.CFalsum))
    , Core.CExists Core.TyProp
        (Core.CAnd (Core.CBound 0) Core.CTruth)
    ]

builderBytes :: Builder.Builder -> ByteString.ByteString
builderBytes =
    LazyByteString.toStrict . Builder.toLazyByteString

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err ->
        assertFailure ("expected Right, got " <> show err)
            >> fail "unreachable"
    Right value ->
        pure value
