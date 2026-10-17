{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Durable logical module owners, independent of invocation-local mount IDs.
module Felix.Module
    ( SourceNamespaceId
    , sourceNamespaceId
    , sourceNamespaceIdFromDigest
    , sourceNamespaceDigest
    , ModuleName
    , moduleName
    , moduleNameFromParts
    , moduleNameNamespace
    , moduleNameRelativePath
    , preludeModuleName
    , encodeAbsoluteSourceRoot
    , encodeSafeRelativePath
    , encodeModuleName
    , LocalDeclarationOrdinal
    , localDeclarationOrdinal
    , localDeclarationOrdinalValue
    , LocalFactOrdinal
    , localFactOrdinal
    , localFactOrdinalValue
    , GeneratedObjectSlot
    , generatedObjectSlot
    , generatedObjectSlotValue
    , StructureFieldSlot
    , structureFieldSlot
    , structureFieldSlotValue
    , StructureSlot
    , structureSlot
    , structureSlotValue
    , DeclarationFamilyTag(..)
    , encodeDeclarationFamilyTag
    ) where

import Base
import Felix.Math.Codec
import Felix.Source

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import System.FilePath.Posix qualified as Posix




newtype SourceNamespaceId =
    SourceNamespaceId MathematicalDigest
    deriving stock (Show, Eq, Ord)

sourceNamespaceId :: CanonicalPath -> SourceNamespaceId
sourceNamespaceId root =
    SourceNamespaceId
        (hashIdentityBytes
            SourceNamespaceIdentity
            (ByteString.cons 0x00 (encodeAbsoluteSourceRoot root)))

sourceNamespaceIdFromDigest
    :: MathematicalDigest
    -> SourceNamespaceId
sourceNamespaceIdFromDigest =
    SourceNamespaceId

sourceNamespaceDigest :: SourceNamespaceId -> MathematicalDigest
sourceNamespaceDigest (SourceNamespaceId digest) =
    digest

data ModuleName = ModuleName
    !SourceNamespaceId
    !SafeRelativePath
    deriving stock (Show, Eq, Ord)

moduleName :: ResolvedSourceAddress -> ModuleName
moduleName address =
    ModuleName
        (sourceNamespaceId (sourceAddressRoot address))
        (sourceAddressRelativePath address)

moduleNameFromParts
    :: SourceNamespaceId
    -> SafeRelativePath
    -> ModuleName
moduleNameFromParts =
    ModuleName

moduleNameNamespace :: ModuleName -> SourceNamespaceId
moduleNameNamespace (ModuleName namespace _relativePath) =
    namespace

moduleNameRelativePath :: ModuleName -> SafeRelativePath
moduleNameRelativePath (ModuleName _namespace relativePath) =
    relativePath

preludeModuleName :: ModuleName
preludeModuleName =
    ModuleName
        reservedPreludeNamespace
        (case safeRelativePath "prelude" of
            Right relative -> relative
            Left err ->
                impossible
                    ("invalid reserved prelude path: " <> show err))
  where
    reservedPreludeNamespace =
        SourceNamespaceId
            (hashIdentityBytes
                SourceNamespaceIdentity
                (ByteString.singleton 0x01))

encodeAbsoluteSourceRoot :: CanonicalPath -> ByteString
encodeAbsoluteSourceRoot root =
    compactPathBytes components
  where
    path =
        Posix.dropTrailingPathSeparator
            (canonicalPathFilePath root)
    components =
        case Posix.splitDirectories path of
            [] ->
                []
            rootComponent : rest
                | endsInPathSeparator rootComponent ->
                        rest
                | otherwise ->
                    impossible
                        "canonical source root is not absolute"

    endsInPathSeparator component =
        case reverse component of
            character : _ ->
                Posix.isPathSeparator character
            [] ->
                False

encodeSafeRelativePath :: SafeRelativePath -> ByteString
encodeSafeRelativePath relative =
    compactPathBytes
        (splitComponents (safeRelativePathFilePath relative))

encodeModuleName :: ModuleName -> ByteString
encodeModuleName (ModuleName namespace relative) =
    mathematicalDigestBytes (sourceNamespaceDigest namespace)
        <> encodeSafeRelativePath relative

compactPathBytes :: [FilePath] -> ByteString
compactPathBytes =
    LazyByteString.toStrict
        . Builder.toLazyByteString
        . compactSequenceBuilder (compactTextBuilder . Text.pack)

splitComponents :: FilePath -> [FilePath]
splitComponents path =
    case break (== '/') path of
        (component, []) ->
            [component]
        (component, _slash : rest) ->
            component : splitComponents rest


newtype LocalDeclarationOrdinal =
    LocalDeclarationOrdinal Natural
    deriving stock (Show, Eq, Ord)

localDeclarationOrdinal
    :: Natural
    -> LocalDeclarationOrdinal
localDeclarationOrdinal =
    LocalDeclarationOrdinal

localDeclarationOrdinalValue
    :: LocalDeclarationOrdinal
    -> Natural
localDeclarationOrdinalValue
        (LocalDeclarationOrdinal ordinal) =
    ordinal

newtype LocalFactOrdinal =
    LocalFactOrdinal Natural
    deriving stock (Show, Eq, Ord)

localFactOrdinal :: Natural -> LocalFactOrdinal
localFactOrdinal =
    LocalFactOrdinal

localFactOrdinalValue :: LocalFactOrdinal -> Natural
localFactOrdinalValue (LocalFactOrdinal ordinal) =
    ordinal

newtype GeneratedObjectSlot =
    GeneratedObjectSlot Natural
    deriving stock (Show, Eq, Ord)

generatedObjectSlot :: Natural -> GeneratedObjectSlot
generatedObjectSlot =
    GeneratedObjectSlot

generatedObjectSlotValue :: GeneratedObjectSlot -> Natural
generatedObjectSlotValue (GeneratedObjectSlot slot) =
    slot

-- | Declaration-local identity slot for a structure field.  This is
-- deliberately distinct from 'GeneratedObjectSlot': a field keeps its own
-- identity when its projection representation changes.
newtype StructureFieldSlot =
    StructureFieldSlot Natural
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

structureFieldSlot :: Natural -> StructureFieldSlot
structureFieldSlot =
    StructureFieldSlot

structureFieldSlotValue :: StructureFieldSlot -> Natural
structureFieldSlotValue (StructureFieldSlot slot) =
    slot

-- | A structure's position within one declaration, independent of the
-- declaration-wide namespace of field slots.
newtype StructureSlot = StructureSlot Natural
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

structureSlot :: Natural -> StructureSlot
structureSlot = StructureSlot

structureSlotValue :: StructureSlot -> Natural
structureSlotValue (StructureSlot slot) = slot

data DeclarationFamilyTag
    = SignatureDeclaration
    | StructureDeclaration
    | DatatypeDeclaration
    | InductiveDeclaration
    deriving stock (Show, Eq, Ord, Enum, Bounded)

encodeDeclarationFamilyTag :: DeclarationFamilyTag -> ByteString
encodeDeclarationFamilyTag =
    ByteString.singleton . \case
        SignatureDeclaration ->
            0x00
        StructureDeclaration ->
            0x01
        DatatypeDeclaration ->
            0x02
        InductiveDeclaration ->
            0x03
