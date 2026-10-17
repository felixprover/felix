{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Versioned, path-independent observations shared by the source-scanner
-- benchmark and its differential tests. This module is deliberately outside
-- the production library.
module Felix.Test.SourceScan.Observation
    ( LogicalSourceAddress(..)
    , ManifestSourceInput(..)
    , ManifestSource(..)
    , CorpusManifest
    , makeCorpusManifest
    , corpusManifestDigest
    , corpusManifestSourceCount
    , renderCorpusManifest
    , ObservationCase(..)
    , observationCaseName
    , parseObservationCase
    , comparativeObservationCases
    , NormalizedLocation(..)
    , NormalizedWhitespace(..)
    , NormalizedLocated(..)
    , NormalizedToken(..)
    , NormalizedAssociativity(..)
    , NormalizedPragma(..)
    , NormalizedHeadingLevel(..)
    , NormalizedDocumentSegment(..)
    , NormalizedFailure(..)
    , NormalizedSourceOutcome(..)
    , normalizeOwnedLocation
    , normalizeAnonymousLocation
    , normalizeWhitespace
    , normalizeLocatedText
    , normalizeLocatedToken
    , normalizePragma
    , normalizeSyntaxPragmaFailure
    , normalizedSourceOutcomeLeafCount
    , CompactSourceObservation(..)
    , CompactCaseRecord(..)
    , compactCaseRecord
    , renderCompactCaseRecord
    ) where

import Base

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Word (Word8)
import Felix.Math.Codec
    ( MathematicalDigest
    , hashBlake2b256
    , mathematicalDigestHex
    )
import Felix.Report.Location
    ( SourceDescriptor
    , Location
    , anonymousSourceDescriptor
    , locColumn
    , locSourceDescriptor
    , locLine
    )
import Felix.Syntax.Abstract (Associativity(..))
import Felix.Syntax.Pragma
    ( SyntaxPragma(..)
    , SyntaxPragmaError(..)
    , SyntaxPragmaProblem(..)
    , sourceMixfixLevelValue
    )
import Felix.Syntax.Token
    ( Located(..)
    , Token(..)
    , Whitespace(..)
    )


data LogicalSourceAddress = LogicalSourceAddress
    { logicalSourceMount :: !Text
    , logicalSourceRelativePath :: !Text
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | The physical path is replay metadata only. It is retained in this input
-- type to make the fact that corpus identity ignores it directly testable.
data ManifestSourceInput = ManifestSourceInput
    { manifestInputAddress :: !LogicalSourceAddress
    , manifestInputReadPath :: !FilePath
    , manifestInputBytes :: !ByteString
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data ManifestSource = ManifestSource
    { manifestSourceAddress :: !LogicalSourceAddress
    , manifestSourceByteDigest :: !MathematicalDigest
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data CorpusManifest = CorpusManifest
    { manifestRootAddress :: !LogicalSourceAddress
    , manifestMountSearchOrder :: ![Text]
    , manifestSources :: ![ManifestSource]
    , manifestDigest :: !MathematicalDigest
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

makeCorpusManifest
    :: LogicalSourceAddress
    -> [Text]
    -> [ManifestSourceInput]
    -> CorpusManifest
makeCorpusManifest root mountOrder inputs =
    CorpusManifest
        { manifestRootAddress = root
        , manifestMountSearchOrder = mountOrder
        , manifestSources = sources
        , manifestDigest = hashBlake2b256
            (strictBuilder
                (Builder.byteString "FELIX\NULSOURCE-SCAN-CORPUS\NUL"
                    <> Builder.word8 corpusManifestVersion
                    <> encodeLogicalSourceAddress root
                    <> encodeList encodeText mountOrder
                    <> encodeList encodeManifestSource sources))
        }
  where
    sources =
        [ ManifestSource
            address
            (hashBlake2b256 bytes)
        | ManifestSourceInput address _readPath bytes <- inputs
        ]

corpusManifestVersion :: Word8
corpusManifestVersion = 1

corpusManifestDigest :: CorpusManifest -> MathematicalDigest
corpusManifestDigest = manifestDigest

corpusManifestSourceCount :: CorpusManifest -> Int
corpusManifestSourceCount = length . manifestSources

renderCorpusManifest :: CorpusManifest -> Text
renderCorpusManifest manifest =
    Text.unlines
        ( [ "source-scan-manifest-v1"
          , "root " <> renderLogicalSourceAddress
                (manifestRootAddress manifest)
          ]
        <> [ "mount " <> mount
           | mount <- manifestMountSearchOrder manifest
           ]
        <> [ "source "
                <> Text.pack (show ordinal)
                <> " "
                <> renderLogicalSourceAddress address
                <> " "
                <> mathematicalDigestHex digest
           | (ordinal, ManifestSource address digest) <-
                zip [0 :: Int ..] (manifestSources manifest)
           ]
        <> [ "corpus-digest "
                <> mathematicalDigestHex (manifestDigest manifest)
           , "root-result success"
           , "source-count "
                <> Text.pack (show (length (manifestSources manifest)))
           ]
        )

renderLogicalSourceAddress :: LogicalSourceAddress -> Text
renderLogicalSourceAddress (LogicalSourceAddress mount relative) =
    mount <> ":" <> relative


data ObservationCase
    = PrefixCase
    | VerificationCompletionCase
    | PresentationSpansCase
    | PresentationDecodedCase
    deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
    deriving anyclass (NFData)

observationCaseName :: ObservationCase -> Text
observationCaseName = \case
    PrefixCase -> "prefix"
    VerificationCompletionCase -> "verification-completion"
    PresentationSpansCase -> "presentation-spans"
    PresentationDecodedCase -> "presentation-decoded"

parseObservationCase :: String -> Maybe ObservationCase
parseObservationCase raw =
    find ((== Text.pack raw) . observationCaseName) [minBound .. maxBound]

comparativeObservationCases :: [ObservationCase]
comparativeObservationCases =
    [ PrefixCase
    , VerificationCompletionCase
    , PresentationDecodedCase
    ]


data NormalizedLocation
    = NormalizedNowhere
    | NormalizedAnonymousLocation !Int !Int
    | NormalizedSourceLocation !Int !Int !Int
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedWhitespace
    = NormalizedNoSpace
    | NormalizedSpace
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedLocated value = NormalizedLocated
    { normalizedLocatedStart :: !NormalizedLocation
    , normalizedLocatedValue :: !value
    , normalizedLocatedPostWhitespace :: !NormalizedWhitespace
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedToken
    = NormalizedWord !Text
    | NormalizedVariable !Text
    | NormalizedSymbol !Text
    | NormalizedInteger !Integer
    | NormalizedCommand !Text
    | NormalizedNamedItem !Text
    | NormalizedCaseHeading !Text
    | NormalizedCommandReference !Text !(NonEmpty Text)
    | NormalizedLabel !Text
    | NormalizedReference !(NonEmpty Text)
    | NormalizedBeginEnvironment !Text
    | NormalizedEndEnvironment !Text
    | NormalizedParenLeft
    | NormalizedParenRight
    | NormalizedBracketLeft
    | NormalizedBracketRight
    | NormalizedVisibleBraceLeft
    | NormalizedVisibleBraceRight
    | NormalizedInvisibleBraceLeft
    | NormalizedInvisibleBraceRight
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedAssociativity
    = NormalizedLeftAssociative
    | NormalizedNonAssociative
    | NormalizedRightAssociative
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedPragma = NormalizedPragma
    { normalizedPragmaLocation :: !NormalizedLocation
    , normalizedPragmaAssociativity :: !NormalizedAssociativity
    , normalizedPragmaLevel :: !Word8
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedHeadingLevel
    = NormalizedSection
    | NormalizedSubsection
    | NormalizedSubsubsection
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedDocumentSegment
    = NormalizedDocumentHeading
        !NormalizedHeadingLevel
        !NormalizedLocation
        !Text
        !(Maybe Text)
    | NormalizedDocumentProse !NormalizedLocation !Text
    | NormalizedDocumentFormal !NormalizedLocation !Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedFailure = NormalizedFailure
    { normalizedFailurePhase :: !Text
    , normalizedFailureKind :: !Text
    , normalizedFailureLocation :: !(Maybe NormalizedLocation)
    , normalizedFailureDetails :: ![Text]
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data NormalizedSourceOutcome
    = NormalizedPrefixSuccess ![NormalizedLocated Text]
    | NormalizedVerificationSuccess
        ![NormalizedLocated Text]
        ![Text]
        ![NormalizedPragma]
        ![[NormalizedLocated NormalizedToken]]
    | NormalizedPresentationSuccess ![NormalizedDocumentSegment]
    | NormalizedSourceFailure !NormalizedFailure
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

normalizeOwnedLocation
    :: Int
    -> SourceDescriptor
    -> Location
    -> Either Text NormalizedLocation
normalizeOwnedLocation sourceOrdinal expected location =
    case locSourceDescriptor location of
        Nothing ->
            Right NormalizedNowhere
        Just actual
            | actual == expected ->
                Right
                    (NormalizedSourceLocation
                        sourceOrdinal
                        (locLine location)
                        (locColumn location))
            | otherwise ->
                Left
                    ("location belongs to a different registered source: "
                        <> Text.pack (show actual)
                        <> " /= "
                        <> Text.pack (show expected))

normalizeAnonymousLocation :: Location -> Either Text NormalizedLocation
normalizeAnonymousLocation location =
    case locSourceDescriptor location of
        Nothing ->
            Right NormalizedNowhere
        Just actual
            | actual == anonymousSourceDescriptor ->
                Right
                    (NormalizedAnonymousLocation
                        (locLine location)
                        (locColumn location))
            | otherwise ->
                Left
                    ("fragment location is not anonymous: "
                        <> Text.pack (show actual))

normalizeWhitespace :: Whitespace -> NormalizedWhitespace
normalizeWhitespace = \case
    NoSpace -> NormalizedNoSpace
    Space -> NormalizedSpace

normalizeLocatedText
    :: Int
    -> SourceDescriptor
    -> Located FilePath
    -> Either Text (NormalizedLocated Text)
normalizeLocatedText sourceOrdinal descriptor located = do
    location <- normalizeOwnedLocation sourceOrdinal descriptor (startPos located)
    pure
        NormalizedLocated
            { normalizedLocatedStart = location
            , normalizedLocatedValue = Text.pack (unLocated located)
            , normalizedLocatedPostWhitespace =
                normalizeWhitespace (postWhitespace located)
            }

normalizeLocatedToken
    :: Int
    -> SourceDescriptor
    -> Located Token
    -> Either Text (NormalizedLocated NormalizedToken)
normalizeLocatedToken sourceOrdinal descriptor located = do
    location <- normalizeOwnedLocation sourceOrdinal descriptor (startPos located)
    pure
        NormalizedLocated
            { normalizedLocatedStart = location
            , normalizedLocatedValue = normalizeToken (unLocated located)
            , normalizedLocatedPostWhitespace =
                normalizeWhitespace (postWhitespace located)
            }

normalizeToken :: Token -> NormalizedToken
normalizeToken = \case
    Word value -> NormalizedWord value
    Variable value -> NormalizedVariable value
    Symbol value -> NormalizedSymbol value
    Integer value -> NormalizedInteger value
    Command value -> NormalizedCommand value
    NamedItem value -> NormalizedNamedItem value
    CaseHeading value -> NormalizedCaseHeading value
    CommandReference command markers ->
        NormalizedCommandReference command markers
    Label marker -> NormalizedLabel marker
    Ref markers -> NormalizedReference markers
    BeginEnv environment -> NormalizedBeginEnvironment environment
    EndEnv environment -> NormalizedEndEnvironment environment
    ParenL -> NormalizedParenLeft
    ParenR -> NormalizedParenRight
    BracketL -> NormalizedBracketLeft
    BracketR -> NormalizedBracketRight
    VisibleBraceL -> NormalizedVisibleBraceLeft
    VisibleBraceR -> NormalizedVisibleBraceRight
    InvisibleBraceL -> NormalizedInvisibleBraceLeft
    InvisibleBraceR -> NormalizedInvisibleBraceRight

normalizePragma
    :: Int
    -> SourceDescriptor
    -> SyntaxPragma
    -> Either Text NormalizedPragma
normalizePragma sourceOrdinal descriptor pragma = do
    location <- normalizeOwnedLocation
        sourceOrdinal
        descriptor
        (syntaxPragmaLocation pragma)
    pure
        NormalizedPragma
            { normalizedPragmaLocation = location
            , normalizedPragmaAssociativity =
                normalizeAssociativity (syntaxPragmaAssociativity pragma)
            , normalizedPragmaLevel =
                sourceMixfixLevelValue (syntaxPragmaLevel pragma)
            }

normalizeAssociativity :: Associativity -> NormalizedAssociativity
normalizeAssociativity = \case
    LeftAssoc -> NormalizedLeftAssociative
    NonAssoc -> NormalizedNonAssociative
    RightAssoc -> NormalizedRightAssociative

normalizeSyntaxPragmaFailure
    :: Int
    -> SourceDescriptor
    -> SyntaxPragmaError
    -> Either Text NormalizedFailure
normalizeSyntaxPragmaFailure sourceOrdinal descriptor = \case
    InvalidSyntaxPragma location problem -> do
        normalizedLocation <- normalizeOwnedLocation
            sourceOrdinal
            descriptor
            location
        pure
            NormalizedFailure
                { normalizedFailurePhase = "pragma"
                , normalizedFailureKind = syntaxPragmaProblemTag problem
                , normalizedFailureLocation = Just normalizedLocation
                , normalizedFailureDetails =
                    syntaxPragmaProblemDetails problem
                }
    SyntaxPragmaLocationOutOfRange _file line column ->
        pure
            NormalizedFailure
                { normalizedFailurePhase = "pragma"
                , normalizedFailureKind = "location-out-of-range"
                , normalizedFailureLocation = Nothing
                , normalizedFailureDetails =
                    [ Text.pack (show line)
                    , Text.pack (show column)
                    ]
                }

syntaxPragmaProblemTag :: SyntaxPragmaProblem -> Text
syntaxPragmaProblemTag = \case
    SyntaxPragmaMissingSpaceAfterPrefix -> "missing-space-after-prefix"
    SyntaxPragmaMissingKeyword -> "missing-keyword"
    SyntaxPragmaUnknownKeyword{} -> "unknown-keyword"
    SyntaxPragmaMissingLevel -> "missing-level"
    SyntaxPragmaInvalidLevel -> "invalid-level"
    SyntaxPragmaLevelOutOfRange -> "level-out-of-range"
    SyntaxPragmaTrailingContent -> "trailing-content"
    SyntaxPragmaLoneCarriageReturn -> "lone-carriage-return"

syntaxPragmaProblemDetails :: SyntaxPragmaProblem -> [Text]
syntaxPragmaProblemDetails = \case
    SyntaxPragmaUnknownKeyword keyword -> [keyword]
    SyntaxPragmaMissingSpaceAfterPrefix -> []
    SyntaxPragmaMissingKeyword -> []
    SyntaxPragmaMissingLevel -> []
    SyntaxPragmaInvalidLevel -> []
    SyntaxPragmaLevelOutOfRange -> []
    SyntaxPragmaTrailingContent -> []
    SyntaxPragmaLoneCarriageReturn -> []

normalizedSourceOutcomeLeafCount :: NormalizedSourceOutcome -> Int
normalizedSourceOutcomeLeafCount = \case
    NormalizedPrefixSuccess imports ->
        length imports
    NormalizedVerificationSuccess imports lexerImports pragmas chunks ->
        length imports
            + length lexerImports
            + length pragmas
            + sum (length <$> chunks)
    NormalizedPresentationSuccess segments ->
        length segments
    NormalizedSourceFailure _failure ->
        1


data CompactSourceObservation = CompactSourceObservation
    { compactSourceAddress :: !LogicalSourceAddress
    , compactSourceOutcomeTag :: !Text
    , compactSourceLeafCount :: !Int
    , compactSourceDigest :: !MathematicalDigest
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

data CompactCaseRecord = CompactCaseRecord
    { compactCase :: !ObservationCase
    , compactCorpusDigest :: !MathematicalDigest
    , compactSources :: ![CompactSourceObservation]
    , compactAggregateLeafCount :: !Int
    , compactAggregateDigest :: !MathematicalDigest
    }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

compactCaseRecord
    :: ObservationCase
    -> MathematicalDigest
    -> [(LogicalSourceAddress, NormalizedSourceOutcome)]
    -> CompactCaseRecord
compactCaseRecord selectedCase corpusDigest outcomes =
    CompactCaseRecord
        { compactCase = selectedCase
        , compactCorpusDigest = corpusDigest
        , compactSources = sources
        , compactAggregateLeafCount =
            sum (compactSourceLeafCount <$> sources)
        , compactAggregateDigest =
            hashBlake2b256
                (strictBuilder
                    (Builder.byteString "FELIX\NULSOURCE-SCAN-OBSERVATION\NUL"
                        <> Builder.word8 observationVersion
                        <> encodeObservationCase selectedCase
                        <> encodeList encodeAddressedOutcome outcomes))
        }
  where
    sources =
        [ CompactSourceObservation
            { compactSourceAddress = address
            , compactSourceOutcomeTag = outcomeTag outcome
            , compactSourceLeafCount = normalizedSourceOutcomeLeafCount outcome
            , compactSourceDigest =
                hashBlake2b256
                    (strictBuilder (encodeNormalizedSourceOutcome outcome))
            }
        | (address, outcome) <- outcomes
        ]

observationVersion :: Word8
observationVersion = 1

renderCompactCaseRecord :: CompactCaseRecord -> Text
renderCompactCaseRecord record =
    Text.unlines
        ( [ "source-scan-observation-v1"
          , "case " <> observationCaseName (compactCase record)
          , "corpus-digest "
                <> mathematicalDigestHex (compactCorpusDigest record)
          ]
        <> [ "outcome "
                <> Text.pack (show ordinal)
                <> " "
                <> renderLogicalSourceAddress address
                <> " "
                <> tag
                <> " "
                <> Text.pack (show leafCount)
                <> " "
                <> mathematicalDigestHex digest
           | (ordinal, CompactSourceObservation address tag leafCount digest) <-
                zip [0 :: Int ..] (compactSources record)
           ]
        <> [ "source-count "
                <> Text.pack (show (length (compactSources record)))
           , "leaf-count "
                <> Text.pack (show (compactAggregateLeafCount record))
           , "observation-digest "
                <> mathematicalDigestHex (compactAggregateDigest record)
           ]
        )

outcomeTag :: NormalizedSourceOutcome -> Text
outcomeTag = \case
    NormalizedPrefixSuccess{} -> "prefix-success"
    NormalizedVerificationSuccess{} -> "verification-success"
    NormalizedPresentationSuccess{} -> "presentation-success"
    NormalizedSourceFailure failure ->
        "failure:"
            <> normalizedFailurePhase failure
            <> ":"
            <> normalizedFailureKind failure


encodeManifestSource :: ManifestSource -> Builder.Builder
encodeManifestSource (ManifestSource address digest) =
    encodeLogicalSourceAddress address
        <> encodeText (mathematicalDigestHex digest)

encodeLogicalSourceAddress :: LogicalSourceAddress -> Builder.Builder
encodeLogicalSourceAddress (LogicalSourceAddress mount relative) =
    encodeText mount <> encodeText relative

encodeAddressedOutcome
    :: (LogicalSourceAddress, NormalizedSourceOutcome)
    -> Builder.Builder
encodeAddressedOutcome (address, outcome) =
    encodeLogicalSourceAddress address
        <> encodeNormalizedSourceOutcome outcome

encodeNormalizedSourceOutcome :: NormalizedSourceOutcome -> Builder.Builder
encodeNormalizedSourceOutcome = \case
    NormalizedPrefixSuccess imports ->
        Builder.word8 0x01 <> encodeList encodeLocatedText imports
    NormalizedVerificationSuccess imports lexerImports pragmas chunks ->
        Builder.word8 0x02
            <> encodeList encodeLocatedText imports
            <> encodeList encodeText lexerImports
            <> encodeList encodeNormalizedPragma pragmas
            <> encodeList (encodeList encodeLocatedToken) chunks
    NormalizedPresentationSuccess segments ->
        Builder.word8 0x03
            <> encodeList encodeNormalizedDocumentSegment segments
    NormalizedSourceFailure failure ->
        Builder.word8 0x04 <> encodeNormalizedFailure failure

encodeNormalizedFailure :: NormalizedFailure -> Builder.Builder
encodeNormalizedFailure failure =
    encodeText (normalizedFailurePhase failure)
        <> encodeText (normalizedFailureKind failure)
        <> encodeMaybe encodeNormalizedLocation
            (normalizedFailureLocation failure)
        <> encodeList encodeText (normalizedFailureDetails failure)

encodeNormalizedDocumentSegment
    :: NormalizedDocumentSegment
    -> Builder.Builder
encodeNormalizedDocumentSegment = \case
    NormalizedDocumentHeading level location title marker ->
        Builder.word8 0x01
            <> encodeHeadingLevel level
            <> encodeNormalizedLocation location
            <> encodeText title
            <> encodeMaybe encodeText marker
    NormalizedDocumentProse location source ->
        Builder.word8 0x02
            <> encodeNormalizedLocation location
            <> encodeText source
    NormalizedDocumentFormal location environment ->
        Builder.word8 0x03
            <> encodeNormalizedLocation location
            <> encodeText environment

encodeHeadingLevel :: NormalizedHeadingLevel -> Builder.Builder
encodeHeadingLevel = Builder.word8 . \case
    NormalizedSection -> 0x01
    NormalizedSubsection -> 0x02
    NormalizedSubsubsection -> 0x03

encodeNormalizedPragma :: NormalizedPragma -> Builder.Builder
encodeNormalizedPragma pragma =
    encodeNormalizedLocation (normalizedPragmaLocation pragma)
        <> encodeAssociativity (normalizedPragmaAssociativity pragma)
        <> Builder.word8 (normalizedPragmaLevel pragma)

encodeAssociativity :: NormalizedAssociativity -> Builder.Builder
encodeAssociativity = Builder.word8 . \case
    NormalizedLeftAssociative -> 0x01
    NormalizedNonAssociative -> 0x02
    NormalizedRightAssociative -> 0x03

encodeLocatedText :: NormalizedLocated Text -> Builder.Builder
encodeLocatedText = encodeLocated encodeText

encodeLocatedToken :: NormalizedLocated NormalizedToken -> Builder.Builder
encodeLocatedToken = encodeLocated encodeNormalizedToken

encodeLocated
    :: (value -> Builder.Builder)
    -> NormalizedLocated value
    -> Builder.Builder
encodeLocated encodeValue located =
    encodeNormalizedLocation (normalizedLocatedStart located)
        <> encodeValue (normalizedLocatedValue located)
        <> encodeWhitespace (normalizedLocatedPostWhitespace located)

encodeWhitespace :: NormalizedWhitespace -> Builder.Builder
encodeWhitespace = Builder.word8 . \case
    NormalizedNoSpace -> 0x00
    NormalizedSpace -> 0x01

encodeNormalizedToken :: NormalizedToken -> Builder.Builder
encodeNormalizedToken = \case
    NormalizedWord value -> taggedText 0x01 value
    NormalizedVariable value -> taggedText 0x02 value
    NormalizedSymbol value -> taggedText 0x03 value
    NormalizedInteger value -> taggedText 0x04 (Text.pack (show value))
    NormalizedCommand value -> taggedText 0x05 value
    NormalizedNamedItem value -> taggedText 0x13 value
    NormalizedCaseHeading value -> taggedText 0x14 value
    NormalizedCommandReference command markers ->
        Builder.word8 0x06
            <> encodeText command
            <> encodeNonEmpty encodeText markers
    NormalizedLabel value -> taggedText 0x07 value
    NormalizedReference markers ->
        Builder.word8 0x08 <> encodeNonEmpty encodeText markers
    NormalizedBeginEnvironment value -> taggedText 0x09 value
    NormalizedEndEnvironment value -> taggedText 0x0a value
    NormalizedParenLeft -> Builder.word8 0x0b
    NormalizedParenRight -> Builder.word8 0x0c
    NormalizedBracketLeft -> Builder.word8 0x0d
    NormalizedBracketRight -> Builder.word8 0x0e
    NormalizedVisibleBraceLeft -> Builder.word8 0x0f
    NormalizedVisibleBraceRight -> Builder.word8 0x10
    NormalizedInvisibleBraceLeft -> Builder.word8 0x11
    NormalizedInvisibleBraceRight -> Builder.word8 0x12
  where
    taggedText tag value = Builder.word8 tag <> encodeText value

encodeNormalizedLocation :: NormalizedLocation -> Builder.Builder
encodeNormalizedLocation = \case
    NormalizedNowhere -> Builder.word8 0x00
    NormalizedAnonymousLocation line column ->
        Builder.word8 0x01
            <> encodeInt line
            <> encodeInt column
    NormalizedSourceLocation sourceOrdinal line column ->
        Builder.word8 0x02
            <> encodeInt sourceOrdinal
            <> encodeInt line
            <> encodeInt column

encodeObservationCase :: ObservationCase -> Builder.Builder
encodeObservationCase = Builder.word8 . \case
    PrefixCase -> 0x01
    VerificationCompletionCase -> 0x02
    PresentationSpansCase -> 0x03
    PresentationDecodedCase -> 0x04

encodeInt :: Int -> Builder.Builder
encodeInt = encodeText . Text.pack . show

encodeText :: Text -> Builder.Builder
encodeText value =
    let bytes = Text.encodeUtf8 value
    in Builder.word64BE (fromIntegral (ByteString.length bytes))
        <> Builder.byteString bytes

encodeMaybe :: (value -> Builder.Builder) -> Maybe value -> Builder.Builder
encodeMaybe encodeValue = \case
    Nothing -> Builder.word8 0x00
    Just value -> Builder.word8 0x01 <> encodeValue value

encodeList :: (value -> Builder.Builder) -> [value] -> Builder.Builder
encodeList encodeValue values =
    Builder.word64BE (fromIntegral (length values))
        <> foldMap encodeValue values

encodeNonEmpty
    :: (value -> Builder.Builder)
    -> NonEmpty value
    -> Builder.Builder
encodeNonEmpty encodeValue = encodeList encodeValue . NonEmpty.toList

strictBuilder :: Builder.Builder -> ByteString
strictBuilder = LazyByteString.toStrict . Builder.toLazyByteString
