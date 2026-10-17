{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.CodecAdmission (unitTests) where

import Base
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Checking.Core qualified as Core
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Foundation qualified as Foundation
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Binary.Put qualified as Put
import Data.Bits (shiftL)
import Data.ByteString qualified as Bytes
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as Lazy
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Decoder admission"
    [ testCase "preserves arbitrary-precision canonical magnitudes" magnitudeRoundTrips
    , testCase "distinguishes malformed input from magnitude admission" magnitudeBoundaries
    , testCase "checks admitted term and type depth boundaries" depthBoundaries
    , testCase "shares nodes across cache and mathematical fields" embeddedBudget
    , testCase "shares nested map nodes, elements and depth" mapBudgets
    , testCase "bounds cumulative elements before constructing a wide list" elementBoundaries
    , testCase "bounds input and byte fields before reading rejected bytes" byteBoundaries
    , testCase "accounts for text characters before downstream list reconstruction" textElements
    , testCase "checks the standard cumulative node boundary" nodeBoundaries
    ]

expectRight :: Show failure => Either failure value -> IO value
expectRight = either (fail . show) pure

cacheLimit :: Show value => DecoderResource -> Either CacheDecodeError value -> Assertion
cacheLimit resource = \case
    Left (CacheResourceLimitExceeded failure) -> decoderLimitedResource failure @?= resource
    other -> assertFailure ("expected " <> show resource <> ", got " <> show other)

mathLimit :: Show value => DecoderResource -> Either MathematicalCodecError value -> Assertion
mathLimit resource = \case
    Left (MathematicalResourceLimitExceeded failure) -> decoderLimitedResource failure @?= resource
    other -> assertFailure ("expected " <> show resource <> ", got " <> show other)

builderBytes :: Builder.Builder -> Bytes.ByteString
builderBytes = Lazy.toStrict . Builder.toLazyByteString

magnitudeRoundTrips :: Assertion
magnitudeRoundTrips = do
    -- ULEB chunks span nine bytes; cache chunks span eight bytes. Exercise
    -- both boundaries, the highest partial chunk, zero and signed zigzag.
    for_ ([0 .. 140] <> [255, 256, 511, 512, 4095, 28665]) \bits -> do
        let base = (1 :: Natural) `shiftL` bits
        for_ [base - 1, base, base + 1] \number -> do
            let compact = builderBytes (compactNaturalBuilder number)
                cached = encodeCache (putCacheNatural number)
            decodeCompactNatural compact @?= Right number
            decodeCache getCacheNatural cached @?= Right number
            for_ [toInteger number, negate (toInteger number)] \integer -> do
                decodeCompactInteger (builderBytes (compactIntegerBuilder integer)) @?= Right integer
                decodeCache getCacheInteger (encodeCache (putCacheInteger integer)) @?= Right integer

magnitudeBoundaries :: Assertion
magnitudeBoundaries = do
    let limit = fromIntegral (maximumDecoderIntegerBytes standardDecoderLimits)
    for_ [limit - 1, limit] \count -> do
        let compact = Bytes.replicate (count - 1) 0xff <> Bytes.singleton 0x7f
            cached = encodeCache (putCacheBytes (Bytes.replicate count 0xff))
        compactValue <- expectRight (decodeCompactNatural compact)
        builderBytes (compactNaturalBuilder compactValue) @?= compact
        cacheValue <- expectRight (decodeCache getCacheNatural cached)
        encodeCache (putCacheNatural cacheValue) @?= cached
    mathLimit DecoderIntegerBytes
        (decodeCompactNatural (Bytes.replicate (limit + 1) 0xff))
    -- At the limit, continuation alone establishes inadmissibility. No
    -- assertion about termination/minimality of the unconsumed tail is made.
    mathLimit DecoderIntegerBytes (decodeCompactNatural (Bytes.replicate limit 0x80))
    decodeCompactNatural (Bytes.pack [0x80, 0]) @?= Left MathematicalOverlongUleb
    decodeCompactNatural (Bytes.singleton 0x80) @?= Left (MathematicalUnexpectedEnd 1 0)
    cacheLimit DecoderIntegerBytes
        (decodeCache getCacheNatural (encodeCache (Put.putWord64be (fromIntegral limit + 1))))
    case decodeCache getCacheNatural (encodeCache (putCacheBytes (Bytes.singleton 0))) of
        Left CacheBinaryDecodeError{} -> pure ()
        other -> assertFailure (show other)

depthBoundaries :: Assertion
depthBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    let globals = Identity.globalTypingFromClosure closure
    let limit = fromIntegral (maximumDecoderDepth standardDecoderLimits)
        term depth = iterate Core.CNot Core.CTruth !! (depth - 1)
            :: Core.CanonicalTerm Identity.ObjectId
        coreType depth = iterate (Core.TyArrow Core.TySet) Core.TyProp !! (depth - 1)
    for_ [limit - 1, limit] \depth -> do
        let original = term depth
            bytes = encodeCanonicalTerm Identity.objectIdBuilder original
        (decoded, usage) <- expectRight
            (decodeCanonicalTermWithLimits standardDecoderLimits Identity.getObjectIdMathematical bytes)
        decoderPeakDepth usage @?= fromIntegral depth
        checked <- expectRight (Core.checkCanonicalCore globals decoded)
        _ <- evaluate (force checked)
        encodeCanonicalTerm Identity.objectIdBuilder decoded @?= bytes
        cached <- expectRight (decodeCache (getCanonicalTermCache Identity.getObjectIdCache)
            (encodeCache (putCanonicalTermCache Identity.putObjectIdCache original)))
        checkedCache <- expectRight (Core.checkCanonicalCore globals cached)
        _ <- evaluate (force checkedCache)
        let ty = coreType depth
        decodedType <- expectRight (decodeCompactCoreType (builderBytes (compactCoreTypeBuilder ty)))
        decodedType @?= ty
        -- The decoded type survives the checker's recursive type consumer.
        _ <- evaluate . force =<< expectRight
            (Core.checkCanonicalCore globals
                (Core.CLogicalSelect decodedType :: Core.CanonicalTerm Identity.ObjectId))
        decodeCache getCoreTypeCache (encodeCache (putCoreTypeCache ty)) @?= Right ty
    mathLimit DecoderDepth (decodeCanonicalTerm Identity.getObjectIdMathematical
        (encodeCanonicalTerm Identity.objectIdBuilder (term (limit + 1))))
    cacheLimit DecoderDepth (decodeCache getCoreTypeCache
        (encodeCache (putCoreTypeCache (coreType (limit + 1)))))
    mathLimit DecoderDepth (decodeCompactCoreType
        (builderBytes (compactCoreTypeBuilder (coreType (limit + 1)))))

embeddedBudget :: Assertion
embeddedBudget = do
    let ty = Core.TyArrow Core.TyProp Core.TyProp
        term = Core.CLam Core.TyProp (Core.CBound 0)
        termBytes = encodeCanonicalTerm Identity.objectIdBuilder term
        bytes = encodeCache (putCoreTypeCache ty >> putCacheBytes termBytes)
        decoder = (,) <$> getCoreTypeCache <*> Identity.getReenteredCanonicalTermCache
    ((decodedType, reentered), usage) <- expectRight (decodeCacheWithLimits standardDecoderLimits decoder bytes)
    decodedType @?= ty
    Identity.reenteredCanonicalTermBody reentered @?= term
    (_, typeUsage) <- expectRight (decodeCacheWithLimits standardDecoderLimits getCoreTypeCache
        (encodeCache (putCoreTypeCache ty)))
    (_, termUsage) <- expectRight (decodeCanonicalTermWithLimits standardDecoderLimits
        Identity.getObjectIdMathematical termBytes)
    decoderUsedNodes usage @?= decoderUsedNodes typeUsage + decoderUsedNodes termUsage + 1
    for_ [decoderUsedNodes usage, decoderUsedNodes usage + 1] \nodes -> do
        _ <- expectRight (decodeCacheWithLimits standardDecoderLimits
            { maximumDecoderNodes = nodes } decoder bytes)
        pure ()
    cacheLimit DecoderNodes (decodeCacheWithLimits standardDecoderLimits
        { maximumDecoderNodes = decoderUsedNodes usage - 1 } decoder bytes)

mapBudgets :: Assertion
mapBudgets = do
    let values = Map.fromList [(1, Map.singleton 3 [1 .. 12]), (2, Map.singleton 4 [13 .. 24])]
        putInner = putCanonicalCacheMap putCacheNatural (putCacheList putCacheNatural)
        getInner = getCanonicalCacheMap getCacheNatural (getCacheList getCacheNatural)
        bytes = encodeCache (putCanonicalCacheMap putCacheNatural putInner values)
        decoder = getCanonicalCacheMap getCacheNatural getInner
    (decoded, usage) <- expectRight (decodeCacheWithLimits standardDecoderLimits decoder bytes)
    decoded @?= values
    for_ [ (DecoderNodes, decoderUsedNodes usage, \n -> standardDecoderLimits { maximumDecoderNodes = n })
         , (DecoderElements, decoderUsedElements usage, \n -> standardDecoderLimits { maximumDecoderElements = n })
         , (DecoderDepth, decoderPeakDepth usage, \n -> standardDecoderLimits { maximumDecoderDepth = n })
         ] \(resource, used, limits) -> do
        cacheLimit resource (decodeCacheWithLimits (limits (used - 1)) decoder bytes)
        for_ [used, used + 1] \bound -> do
            (actual, _) <- expectRight (decodeCacheWithLimits (limits bound) decoder bytes)
            actual @?= values

elementBoundaries :: Assertion
elementBoundaries = do
    let limit = maximumDecoderElements standardDecoderLimits
        -- Eight individually admissible lists share the outer allowance.
        bytes count = encodeCache do
            Put.putWord64be 8
            traverse_ Put.putWord64be (replicate 7 65535 <> [count - 8 - 7 * 65535])
        decoder = getCacheList (getCacheList (pure ()))
    for_ [limit - 1, limit] \count -> do
        (lists, usage) <- expectRight (decodeCacheWithLimits standardDecoderLimits decoder (bytes count))
        _ <- evaluate (force lists)
        decoderUsedElements usage @?= count
    cacheLimit DecoderElements (decodeCache decoder (bytes (limit + 1)))
    let wide = encodeCache (Put.putWord64be 65536 >> Put.putByteString (Bytes.replicate 65536 7))
    tags <- expectRight (decodeCache (getCacheList getCacheTag) wide)
    length tags @?= 65536

byteBoundaries :: Assertion
byteBoundaries = do
    let limits = standardDecoderLimits { maximumDecoderInputBytes = 3, maximumDecoderByteFieldBytes = 2 }
    for_ [1, 2] \count -> do
        let bytes = Bytes.replicate count 1
        (value, _) <- expectRight (runMathematicalGetWithLimits limits getCompactBytes
            (builderBytes (compactBytesBuilder bytes)))
        value @?= bytes
    mathLimit DecoderByteFieldBytes (runMathematicalGetWithLimits limits getCompactBytes (Bytes.singleton 3))
    mathLimit DecoderInputBytes (runMathematicalGetWithLimits limits getCompactBytes (Bytes.replicate 4 0))
    cacheLimit DecoderInputBytes (decodeCacheWithLimits limits getCacheTag (Bytes.replicate 4 0))
    runMathematicalGet (getMathematicalBytes (-1)) Bytes.empty @?= Left (MathematicalInvalidByteCount (-1))

textElements :: Assertion
textElements = do
    let values = ["aλ🙂", "bcδ🙂"]
        cached = encodeCache (putCacheList putCacheText values)
        compact = builderBytes (compactSequenceBuilder compactTextBuilder values)
        limits amount = standardDecoderLimits { maximumDecoderElements = amount }
    -- Two list elements plus seven Unicode characters, independent of UTF-8
    -- byte lengths. The first field cannot reset the second field's allowance.
    cacheLimit DecoderElements (decodeCacheWithLimits (limits 8) (getCacheList getCacheText) cached)
    mathLimit DecoderElements (runMathematicalGetWithLimits (limits 8) (getCompactSequence getCompactText) compact)
    for_ [9, 10] \amount -> do
        (decoded, usage) <- expectRight (decodeCacheWithLimits (limits amount) (getCacheList getCacheText) cached)
        (mathematical, _) <- expectRight (runMathematicalGetWithLimits (limits amount) (getCompactSequence getCompactText) compact)
        decoderUsedElements usage @?= 9
        _ <- evaluate (force (Text.unpack <$> decoded))
        decoded @?= values
        mathematical @?= values

nodeBoundaries :: Assertion
nodeBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    closure <- expectRight (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    let limit = fromIntegral (maximumDecoderNodes standardDecoderLimits) :: Int
        term :: Int -> Core.CanonicalTerm Identity.ObjectId
        term 1 = Core.CTruth
        term nodes
            | even nodes = Core.CNot (term (nodes - 1))
            | otherwise = Core.CAnd (term (nodes `div` 2)) (term (nodes `div` 2))
    for_ [limit - 1, limit, limit + 1] \nodes -> do
        let original = term nodes
            mathematical = decodeCanonicalTermWithLimits standardDecoderLimits
                Identity.getObjectIdMathematical (encodeCanonicalTerm Identity.objectIdBuilder original)
            cached = decodeCacheWithLimits standardDecoderLimits
                (getCanonicalTermCache Identity.getObjectIdCache)
                (encodeCache (putCanonicalTermCache Identity.putObjectIdCache original))
        if nodes > limit then do
            mathLimit DecoderNodes mathematical
            cacheLimit DecoderNodes cached
        else do
            (decoded, usage) <- expectRight mathematical
            decoderUsedNodes usage @?= fromIntegral nodes
            checked <- expectRight (Core.checkCanonicalCore (Identity.globalTypingFromClosure closure) decoded)
            _ <- evaluate (force checked)
            (cacheDecoded, cacheUsage) <- expectRight cached
            decoderUsedNodes cacheUsage @?= fromIntegral nodes
            checkedCache <- expectRight (Core.checkCanonicalCore (Identity.globalTypingFromClosure closure) cacheDecoded)
            _ <- evaluate (force checkedCache)
            pure ()
