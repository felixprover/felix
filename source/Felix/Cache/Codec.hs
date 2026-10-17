{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Deterministic, checked serialization scoped only by 'CacheEpoch'.
--
-- These bytes are disposable implementation data. They are never input to a
-- durable mathematical identity.
module Felix.Cache.Codec
    ( CacheEpoch
    , currentCacheEpoch
    , cacheEpochValue
    , cacheEpochFromValue
    , CacheDigest
    , cacheDigestBytes
    , cacheDigestFromBytes
    , cacheDigestHex
    , hashCacheFields
    , CachePut
    , CacheGet
    , CacheDecodeError(..)
    , DecoderLimits(..)
    , standardDecoderLimits
    , DecoderResource(..)
    , DecoderLimitFailure(..)
    , DecoderUsage(..)
    , maximumCacheByteStringBytes
    , maximumCacheMagnitudeBytes
    , maximumCacheListElements
    , encodeCache
    , decodeCache
    , decodeCacheWithLimits
    , getCacheNode
    , getNestedCache
    , getMathematicalCache
    , putCacheTag
    , getCacheTag
    , putCacheBytes
    , getCacheBytes
    , putCacheText
    , getCacheText
    , putCacheNatural
    , getCacheNatural
    , putCacheInteger
    , getCacheInteger
    , putMathematicalDigestCache
    , getMathematicalDigestCache
    , putCacheDigest
    , getCacheDigest
    , putCacheList
    , getCacheList
    , putCacheMaybe
    , getCacheMaybe
    , putCanonicalCacheMap
    , getCanonicalCacheMap
    , putCoreTypeCache, putCoreTypeCacheWith
    , getCoreTypeCache
    , putCoreIntrinsicTagCache
    , getCoreIntrinsicTagCache
    , putFoundationAxiomTagCache
    , getFoundationAxiomTagCache
    , putKernelRuleTagCache
    , getKernelRuleTagCache
    , putCanonicalTermCache, putCanonicalTermCacheWith
    , getCanonicalTermCache
    ) where

import Data.Functor.Identity (runIdentity)
import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.StableCode
import Felix.Checking.Foundation
import Felix.Math.Codec
import Felix.Math.Codec.Internal qualified as Mathematical
import Felix.Codec.Admission
import Felix.Text.Hex (lowerHexText)

import Control.DeepSeq (NFData)
import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.Trans.State.Strict qualified as State
import Crypto.Hash qualified as Crypto
import Data.Binary.Get qualified as Get
import Data.Binary.Put qualified as Put
import Data.Bits ((.|.), shiftL)
import Data.ByteArray qualified as ByteArray
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Text qualified as StrictText
import Data.Text.Encoding qualified as Text
import Data.Word (Word8, Word32)
import Numeric.Natural (Natural)




newtype CacheEpoch = CacheEpoch Word32
    deriving stock (Show, Eq, Ord)

currentCacheEpoch :: CacheEpoch
currentCacheEpoch =
    -- Recursive definitions extend the formal block grammar and parsed layout.
    -- The kernel calculus and its independently checked TheoryId are unchanged.
    CacheEpoch 180

cacheEpochValue :: CacheEpoch -> Word32
cacheEpochValue (CacheEpoch value) =
    value

cacheEpochFromValue :: Word32 -> CacheEpoch
cacheEpochFromValue =
    CacheEpoch

-- | A digest whose meaning is scoped by the store-wide cache epoch.
-- Its input encoding is deliberately separate from mathematical identity.
newtype CacheDigest =
    CacheDigest ByteString
    deriving stock (Eq, Ord)
    deriving newtype (Hashable, NFData)

instance Show CacheDigest where
    show =
        StrictText.unpack . cacheDigestHex

cacheDigestBytes :: CacheDigest -> ByteString
cacheDigestBytes (CacheDigest bytes) =
    bytes

cacheDigestFromBytes :: ByteString -> Maybe CacheDigest
cacheDigestFromBytes bytes
    | ByteString.length bytes == 32 =
        Just (CacheDigest bytes)
    | otherwise =
        Nothing

cacheDigestHex :: CacheDigest -> Text
cacheDigestHex =
    lowerHexText . cacheDigestBytes

-- | Hash deterministic cache fields under a cache-only domain. These bytes
-- may change only together with 'currentCacheEpoch'.
hashCacheFields :: Text -> [ByteString] -> CacheDigest
hashCacheFields domain fields =
    CacheDigest
        (ByteArray.convert
            (Crypto.hashlazy input
                :: Crypto.Digest Crypto.Blake2b_256))
  where
    -- The digest consumer keeps Put's chunks; byte-output callers still use
    -- encodeCache when they need a single strict payload.
    input =
        Put.runPut do
            Put.putByteString "FELIX\NULCACHE\NUL"
            putCacheText domain
            putCacheList putCacheBytes fields

type CachePut = Put.Put
newtype CacheGet value = CacheGet
    { unCacheGet :: State.StateT DecoderBudget (Except.ExceptT CacheDecodeError Get.Get) value }
    deriving newtype (Functor, Applicative, Monad, MonadFail)

data CacheDecodeError
    = CacheBinaryDecodeError !String
    | CacheTrailingBytes !Word64
    | CacheResourceLimitExceeded !DecoderLimitFailure
    | CacheMathematicalDecodeError !MathematicalCodecError
    deriving stock (Show, Eq)

-- Compatibility names for the per-value bounds. Cumulative limits and their
-- measurement history are described in benchmark/readme.md#work-budgets.
maximumCacheByteStringBytes :: Word64
maximumCacheByteStringBytes =
    maximumDecoderByteFieldBytes standardDecoderLimits

maximumCacheMagnitudeBytes :: Word64
maximumCacheMagnitudeBytes =
    maximumDecoderIntegerBytes standardDecoderLimits

maximumCacheListElements :: Word64
maximumCacheListElements =
    maximumDecoderListElements standardDecoderLimits

encodeCache :: CachePut -> ByteString
encodeCache =
    LazyByteString.toStrict . Put.runPut

decodeCache
    :: CacheGet value
    -> ByteString
    -> Either CacheDecodeError value
decodeCache decoder bytes =
    fst <$> decodeCacheWithLimits standardDecoderLimits decoder bytes

decodeCacheWithLimits
    :: DecoderLimits -> CacheGet value -> ByteString
    -> Either CacheDecodeError (value, DecoderUsage)
decodeCacheWithLimits limits decoder bytes = do
    (value, final) <- runCacheWithBudget (newDecoderBudget limits) decoder bytes
    pure (value, decoderUsage final)

runCacheWithBudget
    :: DecoderBudget -> CacheGet value -> ByteString
    -> Either CacheDecodeError (value, DecoderBudget)
runCacheWithBudget budget decoder bytes = do
    admitted <- either (Left . CacheResourceLimitExceeded) Right
        (admitDecoderInput (fromIntegral (ByteString.length bytes)) budget)
    case Get.runGetOrFail
            (Except.runExceptT (State.runStateT (unCacheGet decoder) admitted))
            (LazyByteString.fromStrict bytes) of
        Left (_remaining, _offset, message) ->
            Left (CacheBinaryDecodeError message)
        Right (_remaining, _offset, Left failure) -> Left failure
        Right (remaining, _offset, Right result)
            | LazyByteString.null remaining ->
                Right result
            | otherwise ->
                Left
                    (CacheTrailingBytes
                        (fromIntegral
                            (LazyByteString.length remaining)))

binaryGet :: Get.Get value -> CacheGet value
binaryGet = CacheGet . lift . lift

raiseCacheError :: CacheDecodeError -> CacheGet value
raiseCacheError = CacheGet . lift . Except.throwE

changeCacheBudget
    :: (DecoderBudget -> Either DecoderLimitFailure DecoderBudget)
    -> CacheGet ()
changeCacheBudget update = CacheGet do
    before <- State.get
    case update before of
        Left failure -> lift (Except.throwE (CacheResourceLimitExceeded failure))
        Right after -> State.put after

withCacheNesting :: CacheGet value -> CacheGet value
withCacheNesting decoder = CacheGet do
    enclosing <- State.get
    unCacheGet (changeCacheBudget enterDecoderNesting)
    value <- unCacheGet decoder
    State.modify' (restoreDecoderNesting enclosing)
    pure value

-- | One recursive reconstruction node, with a shared allowance for its fields.
getCacheNode :: CacheGet value -> CacheGet value
getCacheNode decoder = withCacheNesting do
    changeCacheBudget (chargeDecoderNodes 1)
    decoder

-- | Decode embedded bytes without restarting nodes, elements or nesting depth.
-- The input is already contained in the outer value; byte limits still apply
-- to the embedded encoding, while the largest input observation is retained.
getNestedCache :: String -> CacheGet value -> ByteString -> CacheGet value
getNestedCache description decoder bytes = do
    budget <- CacheGet State.get
    case runCacheWithBudget budget decoder bytes of
        Left failure@CacheResourceLimitExceeded{} -> raiseCacheError failure
        Left failure@CacheMathematicalDecodeError{} -> raiseCacheError failure
        Left failure -> fail (description <> ": " <> show failure)
        Right (value, after) -> CacheGet (State.put after) >> pure value

-- | A mathematical byte field inside the current cache value. The bytes and
-- decoded term share one admission owner, including the enclosing field depth.
getMathematicalCache :: MathematicalGet value -> CacheGet (ByteString, value)
getMathematicalCache decoder = withCacheNesting do
    bytes <- getCacheBytes
    budget <- CacheGet State.get
    case Mathematical.runMathematicalGetWithBudget budget decoder bytes of
        Left (MathematicalResourceLimitExceeded failure) ->
            raiseCacheError (CacheResourceLimitExceeded failure)
        Left failure -> raiseCacheError (CacheMathematicalDecodeError failure)
        Right (value, after) -> CacheGet (State.put after) >> pure (bytes, value)

putCacheTag :: Word8 -> CachePut
putCacheTag =
    Put.putWord8

getCacheTag :: CacheGet Word8
getCacheTag = do
    changeCacheBudget (chargeDecoderNodes 1)
    binaryGet Get.getWord8

putCacheBytes :: ByteString -> CachePut
putCacheBytes bytes = do
    Put.putWord64be
        (fromIntegral (ByteString.length bytes))
    Put.putByteString bytes

getCacheBytes :: CacheGet ByteString
getCacheBytes = do
    changeCacheBudget (chargeDecoderNodes 1)
    byteCount <- binaryGet Get.getWord64be
    checkedByteCount <-
        checkedCacheByteCount byteCount
    binaryGet (Get.getByteString checkedByteCount)

putCacheText :: Text -> CachePut
putCacheText =
    putCacheBytes . Text.encodeUtf8

getCacheText :: CacheGet Text
getCacheText = do
    bytes <- getCacheBytes
    case Text.decodeUtf8' bytes of
        Left err ->
            fail ("invalid cache UTF-8: " <> show err)
        Right text ->
            -- Several admitted paths later become linked character lists.
            -- Account for those elements before exposing the text to its
            -- consumer, including text nested inside other byte fields.
            changeCacheBudget (chargeDecoderElements (fromIntegral (StrictText.length text)))
                >> pure text

putCacheNatural :: Natural -> CachePut
putCacheNatural number =
    putCacheBytes (naturalMagnitude number)

getCacheNatural :: CacheGet Natural
getCacheNatural = do
    changeCacheBudget (chargeDecoderNodes 1)
    byteCount <- binaryGet Get.getWord64be
    checkedByteCount <-
        checkedCacheMagnitudeByteCount byteCount
    magnitude <- binaryGet (Get.getByteString checkedByteCount)
    case ByteString.uncons magnitude of
        Just (0, _) ->
            fail "non-minimal cache natural"
        _ ->
            pure
                (Mathematical.assembleLittleEndianChunks 64 (magnitudeChunks magnitude))
  where
    magnitudeChunks bytes
        | ByteString.null bytes = []
        | otherwise =
            let (higher, lower) = ByteString.splitAt (max 0 (ByteString.length bytes - 8)) bytes
                chunk = ByteString.foldl' (\value byte -> (value `shiftL` 8) .|. fromIntegral byte) 0 lower
            in chunk : magnitudeChunks higher

putCacheInteger :: Integer -> CachePut
putCacheInteger integer
    | integer < 0 = do
        putCacheTag 0x01
        putCacheNatural (fromInteger (negate integer))
    | otherwise = do
        putCacheTag 0x00
        putCacheNatural (fromInteger integer)

getCacheInteger :: CacheGet Integer
getCacheInteger = do
    sign <- getCacheTag
    magnitude <- getCacheNatural
    case sign of
        0x00 ->
            pure (toInteger magnitude)
        0x01
            | magnitude == 0 ->
                fail "negative zero in cache integer"
            | otherwise ->
                pure (negate (toInteger magnitude))
        _ ->
            fail ("unknown cache integer sign " <> show sign)

putMathematicalDigestCache
    :: MathematicalDigest
    -> CachePut
putMathematicalDigestCache =
    Put.putByteString . mathematicalDigestBytes

getMathematicalDigestCache :: CacheGet MathematicalDigest
getMathematicalDigestCache = do
    changeCacheBudget (chargeDecoderNodes 1)
    bytes <- binaryGet (Get.getByteString 32)
    case mathematicalDigestFromBytes bytes of
        Just digest ->
            pure digest
        Nothing ->
            fail "cache mathematical digest is not 32 bytes"

putCacheDigest :: CacheDigest -> CachePut
putCacheDigest =
    Put.putByteString . cacheDigestBytes

getCacheDigest :: CacheGet CacheDigest
getCacheDigest = do
    changeCacheBudget (chargeDecoderNodes 1)
    bytes <- binaryGet (Get.getByteString 32)
    case cacheDigestFromBytes bytes of
        Just digest ->
            pure digest
        Nothing ->
            fail "cache digest is not 32 bytes"

putCacheList
    :: (value -> CachePut)
    -> [value]
    -> CachePut
putCacheList putValue values = do
    Put.putWord64be (fromIntegral (length values))
    traverse_ putValue values

getCacheList
    :: forall value. CacheGet value
    -> CacheGet [value]
getCacheList getValue = getCacheNode do
    rawCount <- binaryGet Get.getWord64be
    valueCount <- checkedCacheListElementCount rawCount
    collect valueCount []
  where
    collect :: Int -> [value] -> CacheGet [value]
    collect 0 reversed = pure (reverse reversed)
    collect n reversed = do
        value <- getValue
        collect (n - 1) (value : reversed)

putCacheMaybe
    :: (value -> CachePut)
    -> Maybe value
    -> CachePut
putCacheMaybe putValue = \case
    Nothing ->
        putCacheTag 0x00
    Just value -> do
        putCacheTag 0x01
        putValue value

getCacheMaybe
    :: CacheGet value
    -> CacheGet (Maybe value)
getCacheMaybe getValue = withCacheNesting $
    getCacheTag >>= \case
        0x00 ->
            pure Nothing
        0x01 ->
            Just <$> getValue
        tag ->
            fail ("unknown cache maybe tag " <> show tag)

-- | Maps are ordered by encoded semantic key, independently of runtime-map
-- traversal.
putCanonicalCacheMap
    :: (key -> CachePut)
    -> (value -> CachePut)
    -> Map key value
    -> CachePut
putCanonicalCacheMap putKey putValue entries =
    putCacheList putEntry ordered
  where
    ordered =
        List.sortOn fst
            [ (encodeCache (putKey key), value)
            | (key, value) <- Map.toList entries
            ]

    putEntry (keyBytes, value) = do
        putCacheBytes keyBytes
        putCacheBytes (encodeCache (putValue value))

getCanonicalCacheMap
    :: Ord key
    => CacheGet key
    -> CacheGet value
    -> CacheGet (Map key value)
getCanonicalCacheMap getKey getValue = getCacheNode do
    encodedEntries <-
        getCacheList
            ((,) <$> getCacheBytes <*> getCacheBytes)
    verifyStrictlyAscending (fst <$> encodedEntries)
    entries <- decodeEntries encodedEntries []
    let result =
            Map.fromList entries
    unless
        (Map.size result == length entries)
        (fail "duplicate decoded cache map key")
    pure result
  where
    decodeEntries [] reversed = pure (reverse reversed)
    decodeEntries (entry : rest) reversed = do
        decoded <- decodeEntry entry
        decodeEntries rest (decoded : reversed)

    decodeEntry (keyBytes, valueBytes) =
        (,) <$> getNestedCache "invalid cache map key" getKey keyBytes
            <*> getNestedCache "invalid cache map value" getValue valueBytes

verifyStrictlyAscending :: [ByteString] -> CacheGet ()
verifyStrictlyAscending = \case
    left : right : rest
        | left < right ->
            verifyStrictlyAscending (right : rest)
        | otherwise ->
            fail "cache map keys are not in canonical order"
    _ ->
        pure ()


putCoreTypeCache :: CoreType -> CachePut
putCoreTypeCache = runIdentity . putCoreTypeCacheWith (pure ())

putCoreTypeCacheWith :: Monad m => m () -> CoreType -> m CachePut
putCoreTypeCacheWith visit ty = visit >> case ty of
    TyProp -> pure (putCacheTag 0x00)
    TySet -> pure (putCacheTag 0x01)
    TyArrow domain codomain -> do
        left <- putCoreTypeCacheWith visit domain
        right <- putCoreTypeCacheWith visit codomain
        pure (putCacheTag 0x02 >> left >> right)

getCoreTypeCache :: CacheGet CoreType
getCoreTypeCache = withCacheNesting $
    getCacheTag >>= \case
        0x00 ->
            pure TyProp
        0x01 ->
            pure TySet
        0x02 ->
            TyArrow
                <$> getCoreTypeCache
                <*> getCoreTypeCache
        tag ->
            fail ("unknown cache core-type tag " <> show tag)

putCoreIntrinsicTagCache :: CoreIntrinsicTag -> CachePut
putCoreIntrinsicTagCache =
    putCacheTag . coreIntrinsicTagCode

getCoreIntrinsicTagCache :: CacheGet CoreIntrinsicTag
getCoreIntrinsicTagCache = do
    code <- getCacheTag
    case coreIntrinsicTagFromCode code of
        Right tag ->
            pure tag
        Left (UnknownCoreIntrinsicCode unknown) ->
            fail ("unknown cache intrinsic tag " <> show unknown)

putFoundationAxiomTagCache :: FoundationAxiomTag -> CachePut
putFoundationAxiomTagCache =
    putCacheTag . foundationAxiomTagCode

getFoundationAxiomTagCache :: CacheGet FoundationAxiomTag
getFoundationAxiomTagCache = do
    code <- getCacheTag
    case foundationAxiomTagFromCode code of
        Right tag ->
            pure tag
        Left (UnknownFoundationAxiomCode unknown) ->
            fail ("unknown cache foundation-axiom tag " <> show unknown)

putKernelRuleTagCache :: KernelRuleTag -> CachePut
putKernelRuleTagCache =
    putCacheTag . kernelRuleTagCode

getKernelRuleTagCache :: CacheGet KernelRuleTag
getKernelRuleTagCache = do
    code <- getCacheTag
    case kernelRuleTagFromCode code of
        Right tag ->
            pure tag
        Left (UnknownKernelRuleCode unknown) ->
            fail ("unknown cache kernel-rule tag " <> show unknown)

putCanonicalTermCache
    :: (global -> CachePut) -> CanonicalTerm global -> CachePut
putCanonicalTermCache putGlobal = runIdentity . putCanonicalTermCacheWith (pure ()) putGlobal

putCanonicalTermCacheWith
    :: Monad m => m () -> (global -> CachePut) -> CanonicalTerm global -> m CachePut
putCanonicalTermCacheWith visit putGlobal = go
  where
    go term = visit >> case term of
        CBound index -> pure (putCacheTag 0x00 >> putCacheNatural index)
        CGlobal global -> pure (putCacheTag 0x01 >> putGlobal global)
        CIntrinsic intrinsic -> pure (putCacheTag 0x02 >> putCoreIntrinsicTagCache intrinsic)
        CLogicalSelect ty -> (putCacheTag 0x0a >>) <$> putCoreTypeCacheWith visit ty
        COpaqueInteger integer -> pure (putCacheTag 0x03 >> putCacheInteger integer)
        CApp f x -> binary 0x04 f x
        CLam ty body -> binder 0x05 ty body
        CFalsum -> pure (putCacheTag 0x06)
        CTruth -> pure (putCacheTag 0x0b)
        CNot body -> (putCacheTag 0x0c >>) <$> go body
        CAnd left right -> binary 0x0d left right
        COr left right -> binary 0x0e left right
        CImp left right -> binary 0x07 left right
        CEq ty left right -> do
            encodedType <- putCoreTypeCacheWith visit ty
            a <- go left
            b <- go right
            pure (putCacheTag 0x08 >> encodedType >> a >> b)
        CForall ty body -> binder 0x09 ty body
        CExists ty body -> binder 0x0f ty body
    binary tag left right = do
        a <- go left
        b <- go right
        pure (putCacheTag tag >> a >> b)
    binder tag ty body = do
        encodedType <- putCoreTypeCacheWith visit ty
        encodedBody <- go body
        pure (putCacheTag tag >> encodedType >> encodedBody)

getCanonicalTermCache
    :: CacheGet global
    -> CacheGet (CanonicalTerm global)
getCanonicalTermCache getGlobal = withCacheNesting $
    getCacheTag >>= \case
        0x00 ->
            CBound <$> getCacheNatural
        0x01 ->
            CGlobal <$> getGlobal
        0x02 ->
            CIntrinsic <$> getCoreIntrinsicTagCache
        0x0a ->
            CLogicalSelect <$> getCoreTypeCache
        0x03 ->
            COpaqueInteger <$> getCacheInteger
        0x04 ->
            CApp
                <$> getCanonicalTermCache getGlobal
                <*> getCanonicalTermCache getGlobal
        0x05 ->
            CLam
                <$> getCoreTypeCache
                <*> getCanonicalTermCache getGlobal
        0x06 ->
            pure CFalsum
        0x0b ->
            pure CTruth
        0x0c ->
            CNot <$> getCanonicalTermCache getGlobal
        0x0d ->
            CAnd
                <$> getCanonicalTermCache getGlobal
                <*> getCanonicalTermCache getGlobal
        0x0e ->
            COr
                <$> getCanonicalTermCache getGlobal
                <*> getCanonicalTermCache getGlobal
        0x07 ->
            CImp
                <$> getCanonicalTermCache getGlobal
                <*> getCanonicalTermCache getGlobal
        0x08 ->
            CEq
                <$> getCoreTypeCache
                <*> getCanonicalTermCache getGlobal
                <*> getCanonicalTermCache getGlobal
        0x09 ->
            CForall
                <$> getCoreTypeCache
                <*> getCanonicalTermCache getGlobal
        0x0f ->
            CExists
                <$> getCoreTypeCache
                <*> getCanonicalTermCache getGlobal
        tag ->
            fail ("unknown cache canonical-term tag " <> show tag)


naturalMagnitude :: Natural -> ByteString
naturalMagnitude number
    | number == 0 =
        ByteString.empty
    | otherwise =
        ByteString.reverse
            (ByteString.unfoldr step number)
  where
    step 0 =
        Nothing
    step remaining =
        Just
            ( fromIntegral (remaining `mod` 256)
            , remaining `div` 256
            )

checkedCacheByteCount :: Word64 -> CacheGet Int
checkedCacheByteCount count = do
    changeCacheBudget (admitDecoderByteField (fromIntegral count))
    pure (fromIntegral count)

checkedCacheMagnitudeByteCount :: Word64 -> CacheGet Int
checkedCacheMagnitudeByteCount count = do
    changeCacheBudget (admitDecoderMagnitude (fromIntegral count))
    pure (fromIntegral count)

checkedCacheListElementCount :: Word64 -> CacheGet Int
checkedCacheListElementCount count = do
    changeCacheBudget (admitDecoderListWidth (fromIntegral count))
    changeCacheBudget (chargeDecoderElements (fromIntegral count))
    pure (fromIntegral count)
