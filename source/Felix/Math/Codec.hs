{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Stable byte primitives used only by durable mathematical identities.
module Felix.Math.Codec
    ( MathematicalDigest
    , mathematicalDigestBytes
    , mathematicalDigestFromBytes
    , mathematicalDigestHex
    , MathematicalIdentityKind(..)
    , mathematicalIdentityKindCode
    , allMathematicalIdentityKinds
    , hashBlake2b256
    , hashIdentityBytes
    , hashIdentityBuilder
    , compactNaturalBuilder
    , compactIntegerBuilder
    , compactBytesBuilder
    , compactTextBuilder
    , compactSequenceBuilder
    , compactCoreTypeBuilder, compactCoreTypeBuilderWith
    , compactCoreIntrinsicTagBuilder
    , decodeCompactNatural
    , decodeCompactInteger
    , decodeCompactBytes
    , decodeCompactText
    , decodeCompactCoreType
    , MathematicalGet
    , runMathematicalGet
    , runMathematicalGetWithLimits
    , DecoderLimits(..)
    , standardDecoderLimits
    , DecoderResource(..)
    , DecoderLimitFailure(..)
    , DecoderUsage(..)
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
    , TermDigest
    , termDigestBytes
    , termDigestFromBytes
    , canonicalTermBuilder
    , encodeCanonicalTerm
    , identifyCanonicalTerm, identifyCanonicalTermWith
    , identifyCanonicalTermBytes
    , decodeCanonicalTerm
    , decodeCanonicalTermWithLimits
    , MathematicalCodecError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.StableCode
    ( coreIntrinsicTagCode
    )
import Felix.Text.Hex (lowerHexText)
import Felix.Math.Codec.Internal
import Felix.Codec.Admission
    ( DecoderLimits(..), standardDecoderLimits, DecoderResource(..)
    , DecoderLimitFailure(..), DecoderUsage(..)
    )

import Control.DeepSeq (NFData)
import Data.Functor.Identity (runIdentity)
import Crypto.Hash qualified as Crypto
import Data.Bits ((.&.), (.|.), shiftR)
import Data.ByteArray qualified as ByteArray
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word8)
import Numeric.Natural (Natural)


-- | One raw BLAKE2b-256 digest. Hexadecimal is presentation only.
newtype MathematicalDigest =
    MathematicalDigest ByteString
    deriving stock (Eq, Ord)
    deriving newtype (Hashable, NFData)

instance Show MathematicalDigest where
    show =
        Text.unpack . mathematicalDigestHex

mathematicalDigestBytes :: MathematicalDigest -> ByteString
mathematicalDigestBytes (MathematicalDigest bytes) =
    bytes

mathematicalDigestFromBytes :: ByteString -> Maybe MathematicalDigest
mathematicalDigestFromBytes bytes
    | ByteString.length bytes == 32 =
        Just (MathematicalDigest bytes)
    | otherwise =
        Nothing

mathematicalDigestHex :: MathematicalDigest -> Text
mathematicalDigestHex =
    lowerHexText . mathematicalDigestBytes


-- Production mathematical codec -------------------------------------------------------

-- | Mathematical hash domains. The byte mapping is deliberately explicit
-- and exhaustive rather than derived from constructor order.
data MathematicalIdentityKind
    = CanonicalTermIdentity
    | TheoryIdentity
    | IntrinsicObjectIdentity
    | TransparentObjectIdentity
    | OpaqueObjectIdentity
    | TheoremIdentity
    | OpaqueDeclarationSeedIdentity
    | StructureFieldIdentity
    | SourceNamespaceIdentity
    | StructureIdentity
    | StructureSchemaContentIdentity
    deriving stock (Show, Eq, Ord, Enum, Bounded)

mathematicalIdentityKindCode :: MathematicalIdentityKind -> Word8
mathematicalIdentityKindCode = \case
    CanonicalTermIdentity -> 0x00
    TheoryIdentity -> 0x01
    IntrinsicObjectIdentity -> 0x02
    TransparentObjectIdentity -> 0x03
    OpaqueObjectIdentity -> 0x04
    TheoremIdentity -> 0x05
    OpaqueDeclarationSeedIdentity -> 0x06
    StructureFieldIdentity -> 0x07
    SourceNamespaceIdentity -> 0x08
    StructureIdentity -> 0x09
    StructureSchemaContentIdentity -> 0x0a

allMathematicalIdentityKinds :: [MathematicalIdentityKind]
allMathematicalIdentityKinds =
    [minBound .. maxBound]

mathematicalPrefix :: ByteString
mathematicalPrefix =
    "FELIX\NULMATH\NUL"

hashBlake2b256 :: ByteString -> MathematicalDigest
hashBlake2b256 bytes =
    MathematicalDigest
        (ByteArray.convert
            (Crypto.hash bytes
                :: Crypto.Digest Crypto.Blake2b_256))

hashIdentityBytes
    :: MathematicalIdentityKind
    -> ByteString
    -> MathematicalDigest
hashIdentityBytes kind payload =
    hashBlake2b256
        (identityPrefix kind <> payload)

hashIdentityBuilder
    :: MathematicalIdentityKind
    -> Builder.Builder
    -> MathematicalDigest
hashIdentityBuilder kind payload =
    MathematicalDigest
        (ByteArray.convert
            (Crypto.hashlazy
                (Builder.toLazyByteString
                    (Builder.byteString (identityPrefix kind)
                        <> payload))
                :: Crypto.Digest Crypto.Blake2b_256))

identityPrefix :: MathematicalIdentityKind -> ByteString
identityPrefix kind =
    mathematicalPrefix
        <> ByteString.pack
            [ 0x02
            , mathematicalIdentityKindCode kind
            ]

strictBuilder :: Builder.Builder -> ByteString
strictBuilder =
    LazyByteString.toStrict . Builder.toLazyByteString

compactNaturalBuilder :: Natural -> Builder.Builder
compactNaturalBuilder number =
    go number
  where
    go remaining =
        let payload = fromIntegral (remaining .&. 0x7f)
            rest = remaining `shiftR` 7
        in if rest == 0
            then Builder.word8 payload
            else Builder.word8 (payload .|. 0x80) <> go rest

compactIntegerBuilder :: Integer -> Builder.Builder
compactIntegerBuilder integer =
    compactNaturalBuilder
        (fromInteger
            (if integer >= 0
                then 2 * integer
                else (-2 * integer) - 1))

compactBytesBuilder :: ByteString -> Builder.Builder
compactBytesBuilder bytes =
    compactNaturalBuilder (fromIntegral (ByteString.length bytes))
        <> Builder.byteString bytes

compactTextBuilder :: Text -> Builder.Builder
compactTextBuilder =
    compactBytesBuilder . Text.encodeUtf8

compactSequenceBuilder
    :: (value -> Builder.Builder)
    -> [value]
    -> Builder.Builder
compactSequenceBuilder putValue values =
    compactNaturalBuilder (fromIntegral (length values))
        <> foldMap putValue values

compactCoreTypeBuilder :: CoreType -> Builder.Builder
compactCoreTypeBuilder = runIdentity . compactCoreTypeBuilderWith (pure ())

compactCoreTypeBuilderWith :: Monad m => m () -> CoreType -> m Builder.Builder
compactCoreTypeBuilderWith visit ty = visit >> case ty of
    TyProp -> pure (Builder.word8 0x00)
    TySet -> pure (Builder.word8 0x01)
    TyArrow domain codomain -> do
        left <- compactCoreTypeBuilderWith visit domain
        right <- compactCoreTypeBuilderWith visit codomain
        pure (Builder.word8 0x02 <> left <> right)

compactCoreIntrinsicTagBuilder
    :: CoreIntrinsicTag
    -> Builder.Builder
compactCoreIntrinsicTagBuilder =
    Builder.word8 . coreIntrinsicTagCode

newtype TermDigest = TermDigest MathematicalDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

termDigestBytes :: TermDigest -> ByteString
termDigestBytes (TermDigest digest) =
    mathematicalDigestBytes digest

termDigestFromBytes :: ByteString -> Maybe TermDigest
termDigestFromBytes bytes =
    TermDigest <$> mathematicalDigestFromBytes bytes

canonicalTermBuilder
    :: (global -> Builder.Builder) -> CanonicalTerm global -> Builder.Builder
canonicalTermBuilder putGlobal = runIdentity . canonicalTermBuilderWith (pure ()) putGlobal

-- Debit before constructing each encoding node. The returned builder contains
-- the already traversed fields; hashing it never traverses the Core tree again.
canonicalTermBuilderWith
    :: Monad m => m () -> (global -> Builder.Builder) -> CanonicalTerm global -> m Builder.Builder
canonicalTermBuilderWith visit putGlobal = go
  where
    go term = visit >> case term of
        CBound index -> pure (Builder.word8 0x00 <> compactNaturalBuilder index)
        CGlobal global -> pure (Builder.word8 0x01 <> putGlobal global)
        CIntrinsic intrinsic -> pure (Builder.word8 0x02 <> compactCoreIntrinsicTagBuilder intrinsic)
        CLogicalSelect ty -> (Builder.word8 0x03 <>) <$> compactCoreTypeBuilderWith visit ty
        COpaqueInteger integer -> pure (Builder.word8 0x04 <> compactIntegerBuilder integer)
        CApp f x -> binary 0x05 f x
        CLam ty body -> binder 0x06 ty body
        CFalsum -> pure (Builder.word8 0x07)
        CTruth -> pure (Builder.word8 0x08)
        CNot body -> (Builder.word8 0x09 <>) <$> go body
        CAnd left right -> binary 0x0a left right
        COr left right -> binary 0x0b left right
        CImp left right -> binary 0x0c left right
        CEq ty left right -> do
            encodedType <- compactCoreTypeBuilderWith visit ty
            a <- go left
            b <- go right
            pure (Builder.word8 0x0d <> encodedType <> a <> b)
        CForall ty body -> binder 0x0e ty body
        CExists ty body -> binder 0x0f ty body
    binary tag left right = do
        a <- go left
        b <- go right
        pure (Builder.word8 tag <> a <> b)
    binder tag ty body = do
        encodedType <- compactCoreTypeBuilderWith visit ty
        encodedBody <- go body
        pure (Builder.word8 tag <> encodedType <> encodedBody)

encodeCanonicalTerm
    :: (global -> Builder.Builder)
    -> CanonicalTerm global
    -> ByteString
encodeCanonicalTerm putGlobal =
    strictBuilder . canonicalTermBuilder putGlobal

identifyCanonicalTerm
    :: (global -> Builder.Builder) -> CanonicalTerm global -> TermDigest
identifyCanonicalTerm putGlobal = runIdentity . identifyCanonicalTermWith (pure ()) putGlobal

identifyCanonicalTermWith
    :: Monad m => m () -> (global -> Builder.Builder) -> CanonicalTerm global -> m TermDigest
identifyCanonicalTermWith visit putGlobal term =
    TermDigest . hashIdentityBuilder CanonicalTermIdentity <$> canonicalTermBuilderWith visit putGlobal term

identifyCanonicalTermBytes :: ByteString -> TermDigest
identifyCanonicalTermBytes =
    TermDigest
        . hashIdentityBytes CanonicalTermIdentity
