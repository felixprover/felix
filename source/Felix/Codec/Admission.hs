{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Accounting shared by the deterministic untrusted-value decoders. One
-- top-level admission owns this budget, including embedded encodings.
module Felix.Codec.Admission
    ( DecoderLimits(..)
    , standardDecoderLimits
    , DecoderResource(..)
    , DecoderLimitFailure(..)
    , DecoderUsage(..)
    , DecoderBudget
    , newDecoderBudget
    , decoderLimits
    , decoderUsage
    , decoderMagnitudeLimit
    , admitDecoderInput
    , admitDecoderMagnitude
    , admitDecoderByteField
    , admitDecoderListWidth
    , chargeDecoderNodes
    , chargeDecoderElements
    , enterDecoderNesting
    , restoreDecoderNesting
    ) where

import Base
import Numeric.Natural (Natural)

data DecoderLimits = DecoderLimits
    { maximumDecoderInputBytes :: !Word64
    , maximumDecoderNodes :: !Word64
    , maximumDecoderElements :: !Word64
    , maximumDecoderDepth :: !Word64
    , maximumDecoderIntegerBytes :: !Word64
    , maximumDecoderByteFieldBytes :: !Word64
    , maximumDecoderListElements :: !Word64
    }
    deriving stock (Show, Eq)

standardDecoderLimits :: DecoderLimits
-- These limits bound reconstruction of stored data. They do not change
-- mathematical encodings or proof/search budgets. For accounting and historical
-- corpus measurements, see benchmark/readme.md#work-budgets.
standardDecoderLimits = DecoderLimits
    { maximumDecoderInputBytes = 16 * 1024 * 1024
    , maximumDecoderNodes = 1024 * 1024
    , maximumDecoderElements = 512 * 1024
    , maximumDecoderDepth = 256
    , maximumDecoderIntegerBytes = 4 * 1024
    , maximumDecoderByteFieldBytes = 8 * 1024 * 1024
    , maximumDecoderListElements = 64 * 1024
    }

data DecoderResource
    = DecoderInputBytes
    | DecoderNodes
    | DecoderElements
    | DecoderDepth
    | DecoderIntegerBytes
    | DecoderByteFieldBytes
    | DecoderListElements
    deriving stock (Show, Eq)

-- A limit failure describes the admission decision. It says nothing about
-- validity of the bytes beyond the rejected boundary.
data DecoderLimitFailure = DecoderLimitFailure
    { decoderLimitedResource :: !DecoderResource
    , decoderRequestedAmount :: !Natural
    , decoderResourceLimit :: !Word64
    }
    deriving stock (Show, Eq)

data DecoderUsage = DecoderUsage
    { decoderUsedNodes :: !Word64
    , decoderUsedElements :: !Word64
    , decoderPeakDepth :: !Word64
    , decoderLargestInputBytes :: !Word64
    , decoderLargestIntegerBytes :: !Word64
    , decoderLargestByteFieldBytes :: !Word64
    , decoderLargestListElements :: !Word64
    }
    deriving stock (Show, Eq)

data DecoderBudget = DecoderBudget
    { decoderLimits :: !DecoderLimits
    , remainingNodes :: !Word64
    , remainingElements :: !Word64
    , currentDepth :: !Word64
    , peakDepth :: !Word64
    , largestInput :: !Word64
    , largestMagnitude :: !Word64
    , largestByteField :: !Word64
    , largestList :: !Word64
    }

newDecoderBudget :: DecoderLimits -> DecoderBudget
newDecoderBudget limits = DecoderBudget limits
    (maximumDecoderNodes limits) (maximumDecoderElements limits) 0 0 0 0 0 0

decoderUsage :: DecoderBudget -> DecoderUsage
decoderUsage budget = DecoderUsage
    { decoderUsedNodes = maximumDecoderNodes (decoderLimits budget) - remainingNodes budget
    , decoderUsedElements = maximumDecoderElements (decoderLimits budget) - remainingElements budget
    , decoderPeakDepth = peakDepth budget
    , decoderLargestInputBytes = largestInput budget
    , decoderLargestIntegerBytes = largestMagnitude budget
    , decoderLargestByteFieldBytes = largestByteField budget
    , decoderLargestListElements = largestList budget
    }

boundedCount :: DecoderResource -> Word64 -> Natural -> Either DecoderLimitFailure Word64
boundedCount resource limit amount
    | amount > fromIntegral limit = Left (DecoderLimitFailure resource amount limit)
    | otherwise = Right (fromIntegral amount)

-- Chunk assembly doubles bit widths. This host bound keeps even the final
-- unused doubled width representable, including with a caller-selected policy.
decoderMagnitudeLimit :: DecoderBudget -> Word64
decoderMagnitudeLimit budget =
    min (maximumDecoderIntegerBytes (decoderLimits budget))
        (fromIntegral (maxBound :: Int) `div` 16)

admitDecoderInput, admitDecoderMagnitude, admitDecoderByteField, admitDecoderListWidth
    :: Natural -> DecoderBudget -> Either DecoderLimitFailure DecoderBudget
admitDecoderInput amount budget = do
    count <- boundedCount DecoderInputBytes
        (maximumDecoderInputBytes (decoderLimits budget)) amount
    pure budget { largestInput = max count (largestInput budget) }
admitDecoderMagnitude amount budget = do
    count <- boundedCount DecoderIntegerBytes (decoderMagnitudeLimit budget) amount
    pure budget { largestMagnitude = max count (largestMagnitude budget) }
admitDecoderByteField amount budget = do
    count <- boundedCount DecoderByteFieldBytes
        (min (maximumDecoderByteFieldBytes (decoderLimits budget)) (fromIntegral (maxBound :: Int))) amount
    pure budget { largestByteField = max count (largestByteField budget) }
admitDecoderListWidth amount budget = do
    count <- boundedCount DecoderListElements
        (min (maximumDecoderListElements (decoderLimits budget)) (fromIntegral (maxBound :: Int))) amount
    pure budget { largestList = max count (largestList budget) }

chargeDecoderNodes :: Word64 -> DecoderBudget -> Either DecoderLimitFailure DecoderBudget
chargeDecoderNodes amount budget
    | amount > remainingNodes budget = Left (DecoderLimitFailure DecoderNodes
        (fromIntegral (maximumDecoderNodes limits - remainingNodes budget) + fromIntegral amount)
        (maximumDecoderNodes limits))
    | otherwise = Right budget { remainingNodes = remainingNodes budget - amount }
  where
    limits = decoderLimits budget

chargeDecoderElements :: Natural -> DecoderBudget -> Either DecoderLimitFailure DecoderBudget
chargeDecoderElements amount budget
    | amount > fromIntegral (remainingElements budget) = Left (DecoderLimitFailure DecoderElements
        (fromIntegral (maximumDecoderElements limits - remainingElements budget) + amount)
        (maximumDecoderElements limits))
    | otherwise = Right budget { remainingElements = remainingElements budget - fromIntegral amount }
  where
    limits = decoderLimits budget

enterDecoderNesting :: DecoderBudget -> Either DecoderLimitFailure DecoderBudget
enterDecoderNesting budget
    | currentDepth budget >= maximumDecoderDepth (decoderLimits budget) =
        Left (DecoderLimitFailure DecoderDepth (fromIntegral (currentDepth budget) + 1)
            (maximumDecoderDepth (decoderLimits budget)))
    | otherwise = Right budget
        { currentDepth = currentDepth budget + 1
        , peakDepth = max (peakDepth budget) (currentDepth budget + 1)
        }

-- Restore only the enclosing depth. Nodes, elements and high-water marks
-- remain spent/observed after returning from a nested value.
restoreDecoderNesting :: DecoderBudget -> DecoderBudget -> DecoderBudget
restoreDecoderNesting enclosing nested = nested { currentDepth = currentDepth enclosing }
