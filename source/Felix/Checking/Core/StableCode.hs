{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Stable byte codes and exhaustive inventory for core intrinsics.
module Felix.Checking.Core.StableCode
    ( coreIntrinsicTagCode
    , coreIntrinsicTagFromCode
    , CoreIntrinsicCodeError(..)
    , allCoreIntrinsicTags
    ) where

import Base hiding (Empty)
import Felix.Checking.Core

import Data.List qualified as List
import Data.Word (Word8)


-- | The only forward mapping from a core intrinsic to a durable byte.
-- Constructor order is deliberately irrelevant.
coreIntrinsicTagCode :: CoreIntrinsicTag -> Word8
coreIntrinsicTagCode = \case
    Member -> 0x00
    Empty -> 0x01
    PairSet -> 0x02
    FamilyUnion -> 0x03
    PowerSet -> 0x04
    Sep -> 0x05
    Repl -> 0x06
    UnivOf -> 0x07
    ISetLfp -> 0x08
    GlobalChoice -> 0x09
    OrderedPair -> 0x0a
    FirstProjection -> 0x0b
    SecondProjection -> 0x0c

data CoreIntrinsicCodeError
    = UnknownCoreIntrinsicCode !Word8
    deriving stock (Show, Eq)

coreIntrinsicTagFromCode
    :: Word8
    -> Either CoreIntrinsicCodeError CoreIntrinsicTag
coreIntrinsicTagFromCode code =
    maybe
        (Left (UnknownCoreIntrinsicCode code))
        Right
        (List.find ((== code) . coreIntrinsicTagCode)
            allCoreIntrinsicTags)

-- | The complete intrinsic inventory. Its order follows the stable codes.
allCoreIntrinsicTags :: [CoreIntrinsicTag]
allCoreIntrinsicTags =
    [ Member
    , Empty
    , PairSet
    , FamilyUnion
    , PowerSet
    , Sep
    , Repl
    , UnivOf
    , ISetLfp
    , GlobalChoice
    , OrderedPair
    , FirstProjection
    , SecondProjection
    ]
