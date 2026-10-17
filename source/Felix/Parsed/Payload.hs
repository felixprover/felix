{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Canonical owner-independent raw parsed modules.
module Felix.Parsed.Payload
    ( CanonicalParsedPayload
    , canonicalParsedPayload
    , canonicalParsedPayloadFromBytes
    , canonicalParsedPayloadBytes
    , putCanonicalParsedPayloadCache
    , getCanonicalParsedPayloadCache
    , getParsedVerbSurfacesCache
    , ParsedArtefact
    , parsedArtefact
    , parsedArtefactKey
    , parsedArtefactId
    , parsedArtefactPayload
    , ParsedSyntaxOccurrence
    , parsedSyntaxOccurrence
    , parsedSyntaxOccurrenceBlockIndex
    , parsedSyntaxOccurrenceLocation
    , parsedSyntaxOccurrenceMarker
    , parsedSyntaxOccurrenceEntry
    , DecodedParsedArtefact
    , freshParsedArtefact
    , decodeParsedArtefact
    , decodedParsedArtefactFromBytes
    , decodedParsedArtefactFromBytesWithLimits
    , decodedParsedArtefact
    , decodedParsedImports
    , decodedParsedBlocks
    , decodedParsedOccurrences
    , decodedParsedSyntaxInterface
    ) where

import Base
import Felix.Cache.Codec
import Felix.Parsed.Identity qualified as Identity
import Felix.Source
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface
import Felix.Syntax.LexicalPhrase qualified as Phrase
import Felix.Syntax.Token qualified as Token

import Control.DeepSeq (NFData(..))
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import GHC.Generics qualified as Generic
import Numeric.Natural (Natural)


newtype CanonicalParsedPayload =
    CanonicalParsedPayload ByteString
    deriving stock (Eq, Ord)
    deriving newtype (NFData)

instance Show CanonicalParsedPayload where
    show payload =
        "CanonicalParsedPayload <"
            <> show
                (ByteString.length
                    (canonicalParsedPayloadBytes payload))
            <> " bytes>"

canonicalParsedPayloadBytes
    :: CanonicalParsedPayload
    -> ByteString
canonicalParsedPayloadBytes
        (CanonicalParsedPayload bytes) =
    bytes

canonicalParsedPayloadFromBytes
    :: ByteString
    -> Either CacheDecodeError CanonicalParsedPayload
canonicalParsedPayloadFromBytes bytes =
    payload <$ decodeCanonicalParsedSyntax anonymousSourceDescriptor payload
  where
    payload = CanonicalParsedPayload bytes

-- | The key, payload, and derived identity are inseparable. Store publication
-- uses this retained key rather than accepting a second lookup context.
data ParsedArtefact = ParsedArtefact
    !Identity.ParsedModuleKey
    !CanonicalParsedPayload
    !Identity.ParsedModuleId
    deriving stock (Show, Eq)

instance NFData ParsedArtefact where
    rnf (ParsedArtefact key payload identity) =
        rnf key `seq` rnf payload `seq` rnf identity

parsedArtefact
    :: Identity.ParsedModuleKey
    -> CanonicalParsedPayload
    -> ParsedArtefact
parsedArtefact key payload =
    ParsedArtefact key payload
        (Identity.parsedModuleId key (canonicalParsedPayloadBytes payload))

parsedArtefactKey :: ParsedArtefact -> Identity.ParsedModuleKey
parsedArtefactKey (ParsedArtefact key _payload _identity) = key

parsedArtefactId :: ParsedArtefact -> Identity.ParsedModuleId
parsedArtefactId (ParsedArtefact _key _payload identity) = identity

parsedArtefactPayload :: ParsedArtefact -> CanonicalParsedPayload
parsedArtefactPayload (ParsedArtefact _key payload _identity) = payload

-- | Raw source syntax. The parser separately validates occurrence association.
data ParsedSyntaxOccurrence = ParsedSyntaxOccurrence
    !Int
    !Location
    !Raw.Marker
    !CanonicalLexicalEntry
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

parsedSyntaxOccurrence
    :: Int -> Location -> Raw.Marker -> CanonicalLexicalEntry
    -> ParsedSyntaxOccurrence
parsedSyntaxOccurrence = ParsedSyntaxOccurrence

parsedSyntaxOccurrenceBlockIndex :: ParsedSyntaxOccurrence -> Int
parsedSyntaxOccurrenceBlockIndex (ParsedSyntaxOccurrence index _ _ _) = index

parsedSyntaxOccurrenceLocation :: ParsedSyntaxOccurrence -> Location
parsedSyntaxOccurrenceLocation (ParsedSyntaxOccurrence _ location _ _) = location

parsedSyntaxOccurrenceMarker :: ParsedSyntaxOccurrence -> Raw.Marker
parsedSyntaxOccurrenceMarker (ParsedSyntaxOccurrence _ _ marker _) = marker

parsedSyntaxOccurrenceEntry :: ParsedSyntaxOccurrence -> CanonicalLexicalEntry
parsedSyntaxOccurrenceEntry (ParsedSyntaxOccurrence _ _ _ entry) = entry

-- Raw decoder state is private: callers receive it only paired with the
-- artifact it decodes. Canonical-byte validation also uses this representation.
data ParsedSyntax = ParsedSyntax
    ![ImportRef]
    ![Raw.Block]
    ![ParsedSyntaxOccurrence]
    !SyntaxInterfaceId
    deriving stock (Show, Generic)
    deriving anyclass (NFData)

-- | Syntax retained from fresh encoding or decoded from this exact artifact.
-- Neither route claims that arbitrary syntax was parsed from source bytes.
data DecodedParsedArtefact = DecodedParsedArtefact
    !ParsedArtefact
    !ParsedSyntax
    deriving stock (Show)

instance NFData DecodedParsedArtefact where
    rnf (DecodedParsedArtefact artefact syntax) =
        rnf artefact `seq` rnf syntax

decodedParsedArtefact :: DecodedParsedArtefact -> ParsedArtefact
decodedParsedArtefact (DecodedParsedArtefact artefact _syntax) = artefact

decodedParsedImports :: DecodedParsedArtefact -> [ImportRef]
decodedParsedImports (DecodedParsedArtefact _ (ParsedSyntax imports _ _ _)) =
    imports

decodedParsedBlocks :: DecodedParsedArtefact -> [Raw.Block]
decodedParsedBlocks (DecodedParsedArtefact _ (ParsedSyntax _ blocks _ _)) =
    blocks

decodedParsedOccurrences :: DecodedParsedArtefact -> [ParsedSyntaxOccurrence]
decodedParsedOccurrences
        (DecodedParsedArtefact _ (ParsedSyntax _ _ occurrences _)) =
    occurrences

decodedParsedSyntaxInterface :: DecodedParsedArtefact -> SyntaxInterfaceId
decodedParsedSyntaxInterface
        (DecodedParsedArtefact _ (ParsedSyntax _ _ _ syntax)) =
    syntax

freshParsedArtefact
    :: Identity.ParsedModuleKey
    -> [ImportRef]
    -> [Raw.Block]
    -> [ParsedSyntaxOccurrence]
    -> SyntaxInterfaceId
    -> DecodedParsedArtefact
freshParsedArtefact key imports blocks occurrences syntax =
    DecodedParsedArtefact
        (parsedArtefact key (encodeParsedSyntax parsed))
        parsed
  where
    parsed = ParsedSyntax imports blocks occurrences syntax

canonicalParsedPayload
    :: [ImportRef]
    -> [Raw.Block]
    -> [ParsedSyntaxOccurrence]
    -> SyntaxInterfaceId
    -> CanonicalParsedPayload
canonicalParsedPayload imports blocks occurrences syntax =
    encodeParsedSyntax (ParsedSyntax imports blocks occurrences syntax)

encodeParsedSyntax :: ParsedSyntax -> CanonicalParsedPayload
encodeParsedSyntax (ParsedSyntax imports blocks occurrences syntax) =
    CanonicalParsedPayload
        (encodeCache do
            putCacheTag 0x01
            putCacheList putParsedImport imports
            putCacheList putParsed blocks
            putCacheList putOccurrence occurrences
            putSyntaxInterfaceIdCache syntax)
  where
    putOccurrence (ParsedSyntaxOccurrence blockIndex location marker entry) = do
        putCacheInteger (toInteger blockIndex)
        putParsed location
        putParsed marker
        putCanonicalLexicalEntryCache entry

decodeParsedArtefact
    :: SourceDescriptor
    -> ParsedArtefact
    -> Either CacheDecodeError DecodedParsedArtefact
decodeParsedArtefact descriptor artefact =
    DecodedParsedArtefact artefact
        <$> decodeCanonicalParsedSyntax descriptor (parsedArtefactPayload artefact)

-- | Validate external canonical bytes and retain their decoded syntax with
-- locations bound to the current file. The field readers enforce minimal
-- encoding as they decode; no second traversal through the encoder is needed.
decodedParsedArtefactFromBytes
    :: SourceDescriptor
    -> Identity.ParsedModuleKey
    -> ByteString
    -> Either CacheDecodeError DecodedParsedArtefact
decodedParsedArtefactFromBytes descriptor key bytes =
    fst <$> decodedParsedArtefactFromBytesWithLimits standardDecoderLimits descriptor key bytes

decodedParsedArtefactFromBytesWithLimits
    :: DecoderLimits -> SourceDescriptor -> Identity.ParsedModuleKey -> ByteString
    -> Either CacheDecodeError (DecodedParsedArtefact, DecoderUsage)
decodedParsedArtefactFromBytesWithLimits limits descriptor key bytes = do
    let payload = CanonicalParsedPayload bytes
    (syntax, usage) <- decodeCacheWithLimits limits (getParsedSyntax descriptor) bytes
    pure (DecodedParsedArtefact (parsedArtefact key payload) syntax, usage)

putCanonicalParsedPayloadCache
    :: CanonicalParsedPayload
    -> CachePut
putCanonicalParsedPayloadCache =
    putCacheBytes . canonicalParsedPayloadBytes

getCanonicalParsedPayloadCache
    :: CacheGet CanonicalParsedPayload
getCanonicalParsedPayloadCache = getCacheNode do
    bytes <- getCacheBytes
    _ <- getNestedCache "invalid canonical parsed payload" (getParsedSyntax anonymousSourceDescriptor) bytes
    pure (CanonicalParsedPayload bytes)

decodeCanonicalParsedSyntax
    :: SourceDescriptor
    -> CanonicalParsedPayload
    -> Either CacheDecodeError ParsedSyntax
decodeCanonicalParsedSyntax descriptor payload =
    decodeCache (getParsedSyntax descriptor)
        (canonicalParsedPayloadBytes payload)

getParsedSyntax
    :: SourceDescriptor
    -> CacheGet ParsedSyntax
getParsedSyntax descriptor = do
    getCacheTag >>= \case
        0x01 -> pure ()
        tag ->
            fail
                ("unknown canonical parsed payload tag "
                    <> show tag)
    imports <- getCacheList (getParsedImport descriptor)
    blocks <- getCacheList (getParsed descriptor)
    occurrences <- getCacheList (getOccurrence descriptor)
    syntax <- getSyntaxInterfaceIdCache
    pure
        (ParsedSyntax
            imports
            blocks
            occurrences
            syntax)
  where
    getOccurrence currentSourceDescriptor = do
        blockIndex <- getCacheInteger >>= checkedInt "block index"
        location <- getParsed currentSourceDescriptor
        marker <- getParsed currentSourceDescriptor
        entry <- getCanonicalLexicalEntryCache
        pure (ParsedSyntaxOccurrence blockIndex location marker entry)

putParsedImport :: ImportRef -> CachePut
putParsedImport reference = do
    putCacheText
        (Text.pack
            (safeRelativePathFilePath
                (importPath reference)))
    putParsed (importLocation reference)

getParsedImport :: SourceDescriptor -> CacheGet ImportRef
getParsedImport descriptor = do
    path <- Text.unpack <$> getCacheText
    location <- getParsed descriptor
    case importRef location path of
        Left err ->
            fail ("invalid parsed import path: " <> show err)
        Right reference ->
            pure reference


-- | Epoch-scoped encoding for disposable parsed artefacts. The generic
-- representation follows the current constructor and field layout; changing
-- that layout requires advancing 'currentCacheEpoch'.
--
-- Every successful reader must consume exactly the bytes its writer emits for
-- the decoded value. Generic sums check each tag; products preserve field
-- order. Cache primitives check UTF-8, lengths, minimal magnitudes and integer
-- signs. Specialized readers validate without normalizing paths, locations,
-- verb surfaces or lexical entries. This law composes through the lists and
-- records in 'getParsedSyntax'; 'decodeCache' also rejects trailing bytes.
-- Keep it when adding an instance or changing an imported syntax codec. The
-- parsed-payload tests use re-encoding as the independent canonicality oracle.
class ParsedCodec value where
    putParsed :: value -> CachePut
    default putParsed
        :: (Generic value, GenericPut (Generic.Rep value))
        => value
        -> CachePut
    putParsed = genericPut . Generic.from

    getParsed :: SourceDescriptor -> CacheGet value
    default getParsed
        :: (Generic value, GenericGet (Generic.Rep value))
        => SourceDescriptor
        -> CacheGet value
    getParsed descriptor = getCacheNode (Generic.to <$> genericGet descriptor)

class GenericPut representation where
    genericPut :: representation parameter -> CachePut

class GenericGet representation where
    genericGet
        :: SourceDescriptor
        -> CacheGet (representation parameter)

instance GenericPut Generic.U1 where
    genericPut Generic.U1 = pure ()

instance GenericGet Generic.U1 where
    genericGet _descriptor = pure Generic.U1

instance ParsedCodec value => GenericPut (Generic.K1 index value) where
    genericPut (Generic.K1 value) = putParsed value

instance ParsedCodec value => GenericGet (Generic.K1 index value) where
    genericGet descriptor = Generic.K1 <$> getParsed descriptor

instance GenericPut value => GenericPut (Generic.M1 index meta value) where
    genericPut (Generic.M1 value) = genericPut value

instance GenericGet value => GenericGet (Generic.M1 index meta value) where
    genericGet descriptor = Generic.M1 <$> genericGet descriptor

instance
    (GenericPut left, GenericPut right)
    => GenericPut (left Generic.:*: right) where
    genericPut (left Generic.:*: right) = do
        genericPut left
        genericPut right

instance
    (GenericGet left, GenericGet right)
    => GenericGet (left Generic.:*: right) where
    genericGet descriptor =
        (Generic.:*:)
            <$> genericGet descriptor
            <*> genericGet descriptor

instance
    (GenericPut left, GenericPut right)
    => GenericPut (left Generic.:+: right) where
    genericPut = \case
        Generic.L1 left -> do
            putCacheTag 0x00
            genericPut left
        Generic.R1 right -> do
            putCacheTag 0x01
            genericPut right

instance
    (GenericGet left, GenericGet right)
    => GenericGet (left Generic.:+: right) where
    genericGet descriptor =
        getCacheTag >>= \case
            0x00 -> Generic.L1 <$> genericGet descriptor
            0x01 -> Generic.R1 <$> genericGet descriptor
            tag ->
                fail ("unknown parsed generic sum tag " <> show tag)


instance ParsedCodec Text where
    putParsed = putCacheText
    getParsed _descriptor = getCacheText

instance ParsedCodec Integer where
    putParsed = putCacheInteger
    getParsed _descriptor = getCacheInteger

instance ParsedCodec Int where
    putParsed = putCacheInteger . toInteger
    getParsed _descriptor = getCacheInteger >>= checkedInt "integer"

instance ParsedCodec Natural where
    putParsed = putCacheNatural
    getParsed _descriptor = getCacheNatural

instance ParsedCodec Bool where
    putParsed False = putCacheTag 0x00
    putParsed True = putCacheTag 0x01
    getParsed _descriptor =
        getCacheTag >>= \case
            0x00 -> pure False
            0x01 -> pure True
            tag -> fail ("unknown parsed Boolean tag " <> show tag)

instance ParsedCodec value => ParsedCodec [value] where
    putParsed = putCacheList putParsed
    getParsed descriptor = getCacheList (getParsed descriptor)

instance ParsedCodec value => ParsedCodec (Maybe value) where
    putParsed = putCacheMaybe putParsed
    getParsed descriptor = getCacheMaybe (getParsed descriptor)

instance ParsedCodec value => ParsedCodec (NonEmpty value) where
    putParsed = putCacheList putParsed . toList
    getParsed descriptor = do
        values <- getCacheList (getParsed descriptor)
        case NonEmpty.nonEmpty values of
            Nothing -> fail "empty parsed nonempty sequence"
            Just nonempty -> pure nonempty

instance
    (ParsedCodec left, ParsedCodec right)
    => ParsedCodec (left, right)

instance (ParsedCodec a, ParsedCodec b) => ParsedCodec (Either a b)

instance ParsedCodec Location where
    putParsed location =
        case locSourceDescriptor location of
            Nothing ->
                putCacheTag 0x00
            Just _descriptor -> do
                putCacheTag 0x01
                putCacheNatural (fromIntegral (locLine location))
                putCacheNatural (fromIntegral (locColumn location))
    getParsed descriptor =
        getCacheTag >>= \case
            0x00 ->
                pure Nowhere
            0x01 -> do
                line <- getCacheNatural
                    >>= checkedInt "source line" . toInteger
                column <- getCacheNatural
                    >>= checkedInt "source column" . toInteger
                case mkLocationChecked descriptor line column of
                    Left err ->
                        fail ("invalid parsed source location: " <> show err)
                    Right location ->
                        pure location
            tag ->
                fail ("unknown parsed source location tag " <> show tag)

checkedInt :: String -> Integer -> CacheGet Int
checkedInt label supplied
    | supplied < toInteger (minBound :: Int)
        || supplied > toInteger (maxBound :: Int) =
        fail (label <> " is outside the Int range")
    | otherwise =
        pure (fromInteger supplied)

getParsedVerbSurfacesCache :: CacheGet Raw.VerbSurfaces
getParsedVerbSurfacesCache = do
    singular <- Raw.patternToHoley <$> getPatternCache
    base <- Raw.patternToHoley <$> getPatternCache
    either (fail . show) pure (Raw.checkVerbSurfaces singular base)


instance ParsedCodec Token.Token
instance ParsedCodec value => ParsedCodec (Phrase.SgPl value)

instance ParsedCodec Raw.VarSymbol
instance ParsedCodec Raw.Expr
instance ParsedCodec Raw.StructAggregateEntry
instance ParsedCodec Raw.TypedExpression
instance ParsedCodec Raw.ConcreteType
instance ParsedCodec Raw.LexicalItem
instance ParsedCodec Raw.AdjectiveSide
instance ParsedCodec Raw.AdjectiveSurfaceKey
instance ParsedCodec Raw.AdjectiveLexicalIdentity
instance ParsedCodec Raw.AdjectiveLexicalItem
instance ParsedCodec Raw.LexicalItemSgPl
instance ParsedCodec Raw.VerbSurfaces where
    putParsed surfaces = do
        putPatternCache
            (Raw.patternFromHoley
                (Raw.verbSurfaceSingular surfaces))
        putPatternCache
            (Raw.patternFromHoley
                (Raw.verbSurfaceBase surfaces))
    getParsed _descriptor = getParsedVerbSurfacesCache
instance ParsedCodec Raw.VerbLexicalItem
instance ParsedCodec Raw.Associativity
instance ParsedCodec Raw.MixfixItem
instance ParsedCodec Raw.Pattern
instance ParsedCodec Raw.ParameterArity
instance ParsedCodec Raw.RelationSymbol
instance ParsedCodec Raw.StructSymbol where
    putParsed = putCacheText . Raw.unStructSymbol
    getParsed _descriptor = Raw.StructSymbol <$> getCacheText
instance ParsedCodec Raw.Chain
instance ParsedCodec Raw.Relation
instance ParsedCodec Raw.Sign
instance ParsedCodec Raw.Formula
instance ParsedCodec Raw.PropositionalConstant
instance ParsedCodec Raw.PrefixPredicate
instance ParsedCodec Raw.Connective
instance ParsedCodec value => ParsedCodec (Raw.NounOf value)
instance ParsedCodec names => ParsedCodec (Raw.NounBinder names)
instance
    (ParsedCodec value, ParsedCodec (term Raw.VarSymbol))
    => ParsedCodec (Raw.NounPhraseOf term value)
instance ParsedCodec (Raw.Nameless value)
instance ParsedCodec value => ParsedCodec (Raw.AdjLOf value)
instance ParsedCodec value => ParsedCodec (Raw.AdjROf value)
instance ParsedCodec value => ParsedCodec (Raw.AdjOf value)
instance ParsedCodec value => ParsedCodec (Raw.VerbOf value)
instance ParsedCodec value => ParsedCodec (Raw.FunOf value)
instance ParsedCodec value => ParsedCodec (Raw.VerbPhraseOf value)
instance ParsedCodec Raw.Quantifier
instance ParsedCodec Raw.QuantPhrase
instance ParsedCodec Raw.Term
instance ParsedCodec Raw.Stmt
instance ParsedCodec Raw.Bound
instance ParsedCodec Raw.Asm
instance ParsedCodec Raw.Axiom
instance ParsedCodec Raw.Claim
instance ParsedCodec Raw.DefnHead
instance ParsedCodec Raw.Defn
instance ParsedCodec Raw.CalcQuantifier
instance ParsedCodec Raw.CalcRelationLink
instance ParsedCodec Raw.HaveIntro
instance ParsedCodec Raw.AssumeIntro
instance ParsedCodec Raw.FixBinder
instance ParsedCodec Raw.Proof
instance ParsedCodec Raw.Justification
instance ParsedCodec Raw.Case
instance ParsedCodec Raw.Calc
instance ParsedCodec Raw.Abbreviation
instance ParsedCodec Raw.Datatype
instance ParsedCodec Raw.DatatypeClause
instance ParsedCodec Raw.RecursiveDefinition
instance ParsedCodec Raw.RecursiveClause
instance ParsedCodec Raw.NamedCase
instance ParsedCodec Raw.Inductive
instance ParsedCodec Raw.IntroRule
instance ParsedCodec Raw.SymbolPattern
instance ParsedCodec Raw.Signature
instance ParsedCodec Raw.StructField
instance ParsedCodec Raw.StructParent
instance ParsedCodec Raw.StructDefn
instance ParsedCodec Raw.Instance
instance ParsedCodec Raw.Construction
instance ParsedCodec a => ParsedCodec (Raw.StructApplication a)
instance ParsedCodec a => ParsedCodec (Raw.StructNounPhraseOf a)
instance ParsedCodec Raw.Marker
instance ParsedCodec Raw.ClaimKind
instance ParsedCodec Raw.Block
