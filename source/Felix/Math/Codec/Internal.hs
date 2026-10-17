{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Decoder implementation shared by standalone and embedded admissions.
-- The budget-threading entry is package-private so nested readers cannot
-- accidentally create a new allowance through the public codec API.
module Felix.Math.Codec.Internal
    ( MathematicalGet
    , MathematicalCodecError(..)
    , runMathematicalGet
    , runMathematicalGetWithLimits
    , runMathematicalGetWithBudget
    , failMathematicalGet
    , getMathematicalWord8
    , getMathematicalBytes
    , getCompactNatural
    , getCompactInteger
    , getCompactBytes
    , getCompactText
    , getCompactSequence
    , getCompactCoreType
    , getCompactCoreIntrinsicTag
    , decodeCompactNatural
    , decodeCompactInteger
    , decodeCompactBytes
    , decodeCompactText
    , decodeCompactCoreType
    , decodeCanonicalTerm
    , decodeCanonicalTermWithLimits
    , getTerm
    , assembleLittleEndianChunks
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.StableCode (coreIntrinsicTagFromCode)
import Felix.Codec.Admission
import Control.Monad (unless)
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word8)
import Numeric.Natural (Natural)

data MathematicalCodecError
    = MathematicalUnexpectedEnd !Int !Int
    | MathematicalInvalidByteCount !Int
    | MathematicalTrailingBytes !Int
    | MathematicalOverlongUleb
    | MathematicalSequenceCountTooLarge !Natural
    | MathematicalInvalidUtf8 !Text
    | MathematicalUnknownTypeTag !Word8
    | MathematicalUnknownIntrinsicTag !Word8
    | MathematicalUnknownTermTag !Word8
    | MathematicalInvalidGlobal !Text
    | MathematicalResourceLimitExceeded !DecoderLimitFailure
    deriving stock (Show, Eq)

newtype MathematicalGet value = MathematicalGet
    { unMathematicalGet
        :: DecoderBudget
        -> ByteString
        -> Either
            MathematicalCodecError
            (value, ByteString, DecoderBudget)
    }

instance Functor MathematicalGet where
    fmap function (MathematicalGet action) =
        MathematicalGet \budget bytes -> do
            (value, rest, after) <- action budget bytes
            pure (function value, rest, after)

instance Applicative MathematicalGet where
    pure value =
        MathematicalGet \budget bytes -> Right (value, bytes, budget)
    MathematicalGet getFunction <*> MathematicalGet getValue =
        MathematicalGet \budget bytes -> do
            (function, afterFunction, functionBudget) <- getFunction budget bytes
            (value, afterValue, valueBudget) <- getValue functionBudget afterFunction
            pure (function value, afterValue, valueBudget)

instance Monad MathematicalGet where
    MathematicalGet action >>= next =
        MathematicalGet \budget bytes -> do
            (value, rest, after) <- action budget bytes
            unMathematicalGet (next value) after rest

runMathematicalGet
    :: MathematicalGet value
    -> ByteString
    -> Either MathematicalCodecError value
runMathematicalGet decoder bytes =
    fst <$> runMathematicalGetWithLimits standardDecoderLimits decoder bytes

runMathematicalGetWithLimits
    :: DecoderLimits -> MathematicalGet value -> ByteString
    -> Either MathematicalCodecError (value, DecoderUsage)
runMathematicalGetWithLimits limits decoder bytes = do
    (value, final) <- runMathematicalGetWithBudget (newDecoderBudget limits) decoder bytes
    pure (value, decoderUsage final)

runMathematicalGetWithBudget
    :: DecoderBudget -> MathematicalGet value -> ByteString
    -> Either MathematicalCodecError (value, DecoderBudget)
runMathematicalGetWithBudget budget decoder bytes = do
    admitted <- first MathematicalResourceLimitExceeded
        (admitDecoderInput (fromIntegral (ByteString.length bytes)) budget)
    (value, rest, final) <- unMathematicalGet decoder admitted bytes
    unless
        (ByteString.null rest)
        (Left (MathematicalTrailingBytes (ByteString.length rest)))
    pure (value, final)

changeBudget
    :: (DecoderBudget -> Either DecoderLimitFailure DecoderBudget)
    -> MathematicalGet ()
changeBudget update = MathematicalGet \budget bytes -> do
    after <- first MathematicalResourceLimitExceeded (update budget)
    pure ((), bytes, after)

mathematicalNode :: MathematicalGet value -> MathematicalGet value
mathematicalNode decoder = MathematicalGet \budget bytes -> do
    nested <- first MathematicalResourceLimitExceeded
        (chargeDecoderNodes 1 budget >>= enterDecoderNesting)
    (value, rest, final) <- unMathematicalGet decoder nested bytes
    pure (value, rest, restoreDecoderNesting budget final)

failMathematicalGet
    :: MathematicalCodecError
    -> MathematicalGet value
failMathematicalGet failure =
    MathematicalGet \_budget _bytes -> Left failure

getMathematicalWord8 :: MathematicalGet Word8
getMathematicalWord8 =
    MathematicalGet \budget bytes ->
        case ByteString.uncons bytes of
            Nothing -> Left (MathematicalUnexpectedEnd 1 0)
            Just (byte, rest) -> Right (byte, rest, budget)

getMathematicalBytes :: Int -> MathematicalGet ByteString
getMathematicalBytes byteCount =
    MathematicalGet \budget bytes ->
        if byteCount < 0
            then Left (MathematicalInvalidByteCount byteCount)
        else if ByteString.length bytes < byteCount
            then Left
                (MathematicalUnexpectedEnd
                    byteCount
                    (ByteString.length bytes))
            else let (value, rest) = ByteString.splitAt byteCount bytes
                 in Right (value, rest, budget)

getCompactNatural :: MathematicalGet Natural
getCompactNatural = do
    changeBudget (chargeDecoderNodes 1)
    limit <- MathematicalGet \budget bytes -> Right (decoderMagnitudeLimit budget, bytes, budget)
    (byteCount, chunks) <- go limit 0 0 0 []
    changeBudget (admitDecoderMagnitude (fromIntegral byteCount))
    pure (assembleLittleEndianChunks 63 chunks)
  where
    go :: Word64 -> Word64 -> Int -> Word64 -> [Word64]
        -> MathematicalGet (Word64, [Word64])
    go limit !byteCount !inChunk !chunk reversed
        | byteCount >= limit = failMathematicalGet
            (MathematicalResourceLimitExceeded
                (DecoderLimitFailure DecoderIntegerBytes (fromIntegral byteCount + 1) limit))
        | otherwise = do
            byte <- getMathematicalWord8
            let payload = fromIntegral (byte .&. 0x7f)
                combined = chunk .|. (payload `shiftL` (7 * inChunk))
                nextCount = byteCount + 1
            if byte .&. 0x80 /= 0
                then if inChunk == 8
                    then go limit nextCount 0 0 (combined : reversed)
                    else go limit nextCount (inChunk + 1) combined reversed
                else if byteCount > 0 && payload == 0
                    then failMathematicalGet MathematicalOverlongUleb
                    else pure (nextCount, reverse (combined : reversed))

-- All but the highest chunk have the supplied width. Pair adjacent chunks
-- in balanced levels, so large values do not copy a growing magnitude on
-- every input byte. Both callers admit the byte count before assembly.
assembleLittleEndianChunks :: Int -> [Word64] -> Natural
assembleLittleEndianChunks width = levels width . fmap fromIntegral
  where
    levels !_ [] = 0
    levels !_ [value] = value
    levels !bits values = levels (bits * 2) (pairs bits values)
    pairs bits (low : high : rest) =
        let !combined = low .|. (high `shiftL` bits)
        in combined : pairs bits rest
    pairs _ rest = rest

getCompactInteger :: MathematicalGet Integer
getCompactInteger = do
    zigzag <- getCompactNatural
    let magnitude = toInteger (zigzag `shiftR` 1)
    pure
        (if even zigzag
            then magnitude
            else negate magnitude - 1)

getCompactBytes :: MathematicalGet ByteString
getCompactBytes = do
    changeBudget (chargeDecoderNodes 1)
    byteCount <- getCompactNatural
    changeBudget (admitDecoderByteField byteCount)
    getMathematicalBytes (fromIntegral byteCount)

getCompactText :: MathematicalGet Text
getCompactText = do
    bytes <- getCompactBytes
    case Text.decodeUtf8' bytes of
        Left failure ->
            failMathematicalGet
                (MathematicalInvalidUtf8 (Text.pack (show failure)))
        Right value ->
            changeBudget (chargeDecoderElements (fromIntegral (Text.length value)))
                >> pure value

getCompactSequence
    :: forall value. MathematicalGet value
    -> MathematicalGet [value]
getCompactSequence getValue = mathematicalNode do
    elementCount <- getCompactNatural
    changeBudget (admitDecoderListWidth elementCount)
    changeBudget (chargeDecoderElements elementCount)
    collect (fromIntegral elementCount) []
  where
    collect :: Int -> [value] -> MathematicalGet [value]
    collect 0 reversed = pure (reverse reversed)
    collect n reversed = do
        value <- getValue
        collect (n - 1) (value : reversed)

getCompactCoreType :: MathematicalGet CoreType
getCompactCoreType = mathematicalNode do
    tag <- getMathematicalWord8
    case tag of
        0x00 -> pure TyProp
        0x01 -> pure TySet
        0x02 -> TyArrow <$> getCompactCoreType <*> getCompactCoreType
        _ -> failMathematicalGet (MathematicalUnknownTypeTag tag)

getCompactCoreIntrinsicTag :: MathematicalGet CoreIntrinsicTag
getCompactCoreIntrinsicTag = do
    changeBudget (chargeDecoderNodes 1)
    code <- getMathematicalWord8
    case coreIntrinsicTagFromCode code of
        Left _ ->
            failMathematicalGet
                (MathematicalUnknownIntrinsicTag code)
        Right tag ->
            pure tag

decodeCompactNatural
    :: ByteString
    -> Either MathematicalCodecError Natural
decodeCompactNatural =
    runMathematicalGet getCompactNatural

decodeCompactInteger
    :: ByteString
    -> Either MathematicalCodecError Integer
decodeCompactInteger =
    runMathematicalGet getCompactInteger

decodeCompactBytes
    :: ByteString
    -> Either MathematicalCodecError ByteString
decodeCompactBytes =
    runMathematicalGet getCompactBytes

decodeCompactText
    :: ByteString
    -> Either MathematicalCodecError Text
decodeCompactText =
    runMathematicalGet getCompactText

decodeCompactCoreType
    :: ByteString
    -> Either MathematicalCodecError CoreType
decodeCompactCoreType =
    runMathematicalGet getCompactCoreType

decodeCanonicalTerm
    :: MathematicalGet global
    -> ByteString
    -> Either MathematicalCodecError (CanonicalTerm global)
decodeCanonicalTerm getGlobal =
    runMathematicalGet (getTerm getGlobal)

decodeCanonicalTermWithLimits
    :: DecoderLimits -> MathematicalGet global -> ByteString
    -> Either MathematicalCodecError (CanonicalTerm global, DecoderUsage)
decodeCanonicalTermWithLimits limits getGlobal =
    runMathematicalGetWithLimits limits (getTerm getGlobal)

getTerm :: MathematicalGet global -> MathematicalGet (CanonicalTerm global)
getTerm getGlobal = mathematicalNode do
    tag <- getMathematicalWord8
    case tag of
        0x00 -> CBound <$> getCompactNatural
        0x01 -> CGlobal <$> getGlobal
        0x02 -> CIntrinsic <$> getCompactCoreIntrinsicTag
        0x03 -> CLogicalSelect <$> getCompactCoreType
        0x04 -> COpaqueInteger <$> getCompactInteger
        0x05 -> CApp <$> getTerm getGlobal <*> getTerm getGlobal
        0x06 -> CLam <$> getCompactCoreType <*> getTerm getGlobal
        0x07 -> pure CFalsum
        0x08 -> pure CTruth
        0x09 -> CNot <$> getTerm getGlobal
        0x0a -> CAnd <$> getTerm getGlobal <*> getTerm getGlobal
        0x0b -> COr <$> getTerm getGlobal <*> getTerm getGlobal
        0x0c -> CImp <$> getTerm getGlobal <*> getTerm getGlobal
        0x0d -> CEq <$> getCompactCoreType
            <*> getTerm getGlobal <*> getTerm getGlobal
        0x0e -> CForall <$> getCompactCoreType <*> getTerm getGlobal
        0x0f -> CExists <$> getCompactCoreType <*> getTerm getGlobal
        _ -> failMathematicalGet (MathematicalUnknownTermTag tag)
