{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Candidate source-scanner adapters used only by benchmarks and
-- differential tests. Production scanner products remain abstract.
module Felix.Test.SourceScan.Candidate
    ( CandidateSourceInput(..)
    , CandidatePrefixResult
    , runCandidatePrefixCase
    , forceCandidateSourceInputs
    , forceCandidatePrefixResult
    , normalizeCandidatePrefixResult
    , CandidateCaseResult
    , runCandidateCase
    , forceCandidateCaseResult
    , normalizeCandidateCaseResult
    ) where

import Base

import Control.DeepSeq (NFData)
import Data.ByteString qualified as ByteString
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Felix.Report.Location
    ( Location
    , locColumn
    , locSourceDescriptor
    , locLine
    )
import Felix.Source (loadedBytes, loadedText)
import Felix.Source.Content
    ( IdentifiedLoadedSource
    , identifiedSourceDescriptor
    , identifiedSourceLoaded
    )
import Felix.Source.Scan
    ( DecodedPresentationSegment(..)
    , DocumentHeadingLevel(..)
    , PresentationScanError(..)
    , ProjectedSourcePresentation(..)
    , SourcePrefixError(..)
    , SourcePresentationEntry
    , SourceScanFailure(..)
    , SourceScanPrefix
    , SourceScanRejection(..)
    , VerificationScan(..)
    , VerificationScanError(..)
    , forceSourcePresentationEntryHandoff
    , forceSourceScanPrefixHandoff
    , forceVerificationScanHandoff
    , projectSourcePresentationEntry
    , renderPresentationScanError
    , renderSourceScanInvariantError
    , renderSourcePresentationBindingError
    , renderVerificationScanError
    , resumePresentationScan
    , resumeVerificationScan
    , scanSourcePrefix
    , SourcePresentationProjectionError(..)
    , sourcePrefixImports
    )
import Felix.Syntax.Token (Located(..))
import Felix.Test.SourceScan.Observation


data CandidateSourceInput = CandidateSourceInput
    { candidateSourceAddress :: !LogicalSourceAddress
    , candidateSourceIdentified :: !IdentifiedLoadedSource
    }
    deriving stock (Generic)
    deriving anyclass (NFData)

data CandidatePrefixOutcome
    = CandidatePrefixFailure !SourcePrefixError
    | CandidatePrefixSuccess !SourceScanPrefix

newtype CandidatePrefixResult =
    CandidatePrefixResult [CandidatePrefixOutcome]

data CandidateVerificationOutcome
    = CandidateVerificationFailure !VerificationScanError
    | CandidateVerificationSuccess
        !VerificationScan
        !SourcePresentationEntry

data CandidatePresentationSpanOutcome
    = CandidatePresentationSpanFailure !PresentationScanError
    | CandidatePresentationSpanSuccess !SourcePresentationEntry

data CandidatePresentationOutcome
    = CandidatePresentationFailure !PresentationScanError
    | CandidatePresentationSuccess
        !(Vector DecodedPresentationSegment)

data CandidateCaseResult
    = CandidatePrefixCaseResult !CandidatePrefixResult
    | CandidateVerificationResults ![CandidateVerificationOutcome]
    | CandidatePresentationSpanResults ![CandidatePresentationSpanOutcome]
    | CandidatePresentationResults ![CandidatePresentationOutcome]

runCandidatePrefixCase
    :: [CandidateSourceInput]
    -> Either Text CandidatePrefixResult
runCandidatePrefixCase sources =
    CandidatePrefixResult <$> traverse runSource sources
  where
    runSource source =
        case scanSourcePrefix (candidateSourceIdentified source) of
            Left (SourceInputFailure failure) ->
                Right (CandidatePrefixFailure failure)
            Left (SourceScannerInvariantFailure failure) ->
                Left (renderSourceScanInvariantError failure)
            Right prefix ->
                Right (CandidatePrefixSuccess prefix)

forceCandidateSourceInputs :: [CandidateSourceInput] -> ()
forceCandidateSourceInputs =
    forceList forceSource
  where
    forceSource source =
        forceLogicalSourceAddress (candidateSourceAddress source)
            `seq` let identified = candidateSourceIdentified source
                      loaded = identifiedSourceLoaded identified
                  in identifiedSourceDescriptor identified
                         `seq` ByteString.length (loadedBytes loaded)
                         `seq` Text.length (loadedText loaded)
                         `seq` ()

    forceLogicalSourceAddress address =
        Text.length (logicalSourceMount address)
            `seq` Text.length (logicalSourceRelativePath address)
            `seq` ()

forceCandidatePrefixResult :: CandidatePrefixResult -> ()
forceCandidatePrefixResult (CandidatePrefixResult outcomes) =
    forceList forceOutcome outcomes
  where
    forceOutcome = \case
        CandidatePrefixFailure failure ->
            forcePrefixFailure failure
        CandidatePrefixSuccess prefix ->
            forceSourceScanPrefixHandoff prefix

normalizeCandidatePrefixResult
    :: [CandidateSourceInput]
    -> CandidatePrefixResult
    -> Either Text [(LogicalSourceAddress, NormalizedSourceOutcome)]
normalizeCandidatePrefixResult sources (CandidatePrefixResult outcomes)
    | length sources /= length outcomes =
        Left "candidate source and prefix outcome counts disagree"
    | otherwise =
        traverse normalizeOne (zip3 [0 :: Int ..] sources outcomes)
  where
    normalizeOne (sourceOrdinal, source, outcome) = do
        normalized <- case outcome of
            CandidatePrefixFailure failure ->
                NormalizedSourceFailure
                    <$> normalizePrefixFailure sourceOrdinal source failure
            CandidatePrefixSuccess prefix ->
                NormalizedPrefixSuccess
                    <$> traverse
                        (normalizeLocatedText
                            sourceOrdinal
                            (identifiedSourceDescriptor
                                (candidateSourceIdentified source)))
                        (sourcePrefixImports prefix)
        pure (candidateSourceAddress source, normalized)

runCandidateCase
    :: ObservationCase
    -> [CandidateSourceInput]
    -> Either Text CandidateCaseResult
runCandidateCase selectedCase sources =
    case selectedCase of
        PrefixCase ->
            CandidatePrefixCaseResult <$> runCandidatePrefixCase sources
        VerificationCompletionCase ->
            CandidateVerificationResults <$> traverse runVerification sources
        PresentationSpansCase ->
            CandidatePresentationSpanResults <$>
                traverse runPresentationSpans sources
        PresentationDecodedCase ->
            CandidatePresentationResults <$>
                traverse runPresentationDecoded sources
  where
    runVerification source =
        case scanSourcePrefix (candidateSourceIdentified source) of
            Left (SourceInputFailure failure) ->
                Right
                    (CandidateVerificationFailure
                        (VerificationPrefixFailure failure))
            Left (SourceScannerInvariantFailure failure) ->
                Left (renderSourceScanInvariantError failure)
            Right prefix ->
                case resumeVerificationScan prefix of
                    Left (SourceInputFailure failure) ->
                        Right (CandidateVerificationFailure failure)
                    Left (SourceScannerInvariantFailure failure) ->
                        Left (renderSourceScanInvariantError failure)
                    Right (verification, entry) ->
                        Right
                            (CandidateVerificationSuccess
                                verification
                                entry)

    runPresentationSpans source =
        case scanSourcePrefix (candidateSourceIdentified source) of
            Left (SourceInputFailure (SourcePrefixRejected rejection)) ->
                Right
                    (CandidatePresentationSpanFailure
                        (PresentationScanRejected rejection))
            Left (SourceScannerInvariantFailure failure) ->
                Left (renderSourceScanInvariantError failure)
            Right prefix ->
                case resumePresentationScan prefix of
                    Left failure -> Left (renderSourceScanInvariantError failure)
                    Right entry ->
                        Right (CandidatePresentationSpanSuccess entry)

    runPresentationDecoded source =
        case scanSourcePrefix (candidateSourceIdentified source) of
            Left (SourceInputFailure (SourcePrefixRejected rejection)) ->
                Right
                    (CandidatePresentationFailure
                        (PresentationScanRejected rejection))
            Left (SourceScannerInvariantFailure failure) ->
                Left (renderSourceScanInvariantError failure)
            Right prefix ->
                case resumePresentationScan prefix of
                    Left failure -> Left (renderSourceScanInvariantError failure)
                    Right entry ->
                        case projectSourcePresentationEntry
                                (candidateSourceIdentified source)
                                entry of
                            Left (SourcePresentationBindingFailure failure) ->
                                Left
                                    (renderSourcePresentationBindingError
                                        failure)
                            Left (SourcePresentationDecodeInvariant failure) ->
                                Left (renderSourceScanInvariantError failure)
                            Right (SourcePresentationUnavailable failure) ->
                                Right (CandidatePresentationFailure failure)
                            Right (SourcePresentationDecoded segments) ->
                                Right (CandidatePresentationSuccess segments)

forceCandidateCaseResult :: CandidateCaseResult -> ()
forceCandidateCaseResult = \case
    CandidatePrefixCaseResult result ->
        forceCandidatePrefixResult result
    CandidateVerificationResults outcomes ->
        forceList forceVerificationOutcome outcomes
    CandidatePresentationSpanResults outcomes ->
        forceList forcePresentationSpanOutcome outcomes
    CandidatePresentationResults outcomes ->
        forceList forcePresentationOutcome outcomes
  where
    forceVerificationOutcome = \case
        CandidateVerificationFailure failure ->
            Text.length (renderVerificationScanError failure) `seq` ()
        CandidateVerificationSuccess verification entry ->
            forceVerificationScanHandoff verification
                `seq` forceSourcePresentationEntryHandoff entry

    forcePresentationSpanOutcome = \case
        CandidatePresentationSpanFailure failure ->
            Text.length (renderPresentationScanError failure) `seq` ()
        CandidatePresentationSpanSuccess entry ->
            forceSourcePresentationEntryHandoff entry

    forcePresentationOutcome = \case
        CandidatePresentationFailure failure ->
            Text.length (renderPresentationScanError failure) `seq` ()
        CandidatePresentationSuccess segments ->
            Vector.foldl'
                (\forced segment -> forced `seq` forceDecodedSegment segment)
                ()
                segments

    forceDecodedSegment = \case
        DecodedPresentationHeading level location title marker ->
            level
                `seq` forceLocation location
                `seq` Text.length title
                `seq` forceMaybe (\value -> Text.length value `seq` ()) marker
        DecodedPresentationProse location prose ->
            forceLocation location `seq` Text.length prose `seq` ()
        DecodedPresentationFormal location environment ->
            forceLocation location `seq` Text.length environment `seq` ()

normalizeCandidateCaseResult
    :: [CandidateSourceInput]
    -> CandidateCaseResult
    -> Either Text [(LogicalSourceAddress, NormalizedSourceOutcome)]
normalizeCandidateCaseResult sources = \case
    CandidatePrefixCaseResult result ->
        normalizeCandidatePrefixResult sources result
    CandidateVerificationResults outcomes ->
        zipCandidateOutcomes sources outcomes normalizeVerificationOutcome
    CandidatePresentationSpanResults outcomes ->
        zipCandidateOutcomes sources outcomes normalizePresentationSpanOutcome
    CandidatePresentationResults outcomes ->
        zipCandidateOutcomes sources outcomes normalizePresentationOutcome

zipCandidateOutcomes
    :: [CandidateSourceInput]
    -> [outcome]
    -> (Int -> CandidateSourceInput -> outcome
        -> Either Text NormalizedSourceOutcome)
    -> Either Text [(LogicalSourceAddress, NormalizedSourceOutcome)]
zipCandidateOutcomes sources outcomes normalize
    | length sources /= length outcomes =
        Left "candidate source and outcome counts disagree"
    | otherwise =
        traverse normalizeOne (zip3 [0 :: Int ..] sources outcomes)
  where
    normalizeOne (sourceOrdinal, source, outcome) = do
        normalized <- normalize sourceOrdinal source outcome
        pure (candidateSourceAddress source, normalized)

normalizeVerificationOutcome
    :: Int
    -> CandidateSourceInput
    -> CandidateVerificationOutcome
    -> Either Text NormalizedSourceOutcome
normalizeVerificationOutcome sourceOrdinal source = \case
    CandidateVerificationFailure failure ->
        NormalizedSourceFailure <$>
            normalizeVerificationFailure sourceOrdinal source failure
    CandidateVerificationSuccess verification _entry -> do
        let descriptor = identifiedSourceDescriptor
                (candidateSourceIdentified source)
            imports = verificationImports verification
        normalizedImports <- traverse
            (normalizeLocatedText sourceOrdinal descriptor)
            imports
        normalizedPragmas <- traverse
            (normalizePragma sourceOrdinal descriptor)
            (verificationPragmas verification)
        normalizedChunks <- traverse
            (traverse (normalizeLocatedToken sourceOrdinal descriptor))
            (verificationChunks verification)
        pure
            (NormalizedVerificationSuccess
                normalizedImports
                (Text.pack . unLocated <$> imports)
                normalizedPragmas
                normalizedChunks)

normalizeVerificationFailure
    :: Int
    -> CandidateSourceInput
    -> VerificationScanError
    -> Either Text NormalizedFailure
normalizeVerificationFailure sourceOrdinal source = \case
    VerificationPrefixFailure failure ->
        normalizePrefixFailure sourceOrdinal source failure
    VerificationPragmaFailure failure ->
        normalizeSyntaxPragmaFailure
            sourceOrdinal
            (identifiedSourceDescriptor (candidateSourceIdentified source))
            failure
    VerificationBodyFailure rejection ->
        normalizeRejection
            "verification-tokenization"
            sourceOrdinal
            source
            rejection

normalizePresentationSpanOutcome
    :: Int
    -> CandidateSourceInput
    -> CandidatePresentationSpanOutcome
    -> Either Text NormalizedSourceOutcome
normalizePresentationSpanOutcome sourceOrdinal source = \case
    CandidatePresentationSpanFailure (PresentationScanRejected rejection) ->
        NormalizedSourceFailure <$>
            normalizeRejection
                "presentation-document"
                sourceOrdinal
                source
                rejection
    CandidatePresentationSpanSuccess _entry ->
        pure (NormalizedPresentationSuccess [])

normalizePresentationOutcome
    :: Int
    -> CandidateSourceInput
    -> CandidatePresentationOutcome
    -> Either Text NormalizedSourceOutcome
normalizePresentationOutcome sourceOrdinal source = \case
    CandidatePresentationFailure (PresentationScanRejected rejection) ->
        NormalizedSourceFailure <$>
            normalizeRejection
                "presentation-document"
                sourceOrdinal
                source
                rejection
    CandidatePresentationSuccess segments ->
        NormalizedPresentationSuccess <$>
            traverse normalizeSegment (Vector.toList segments)
  where
    normalizeSegment = \case
        DecodedPresentationHeading level location title marker ->
            NormalizedDocumentHeading
                (normalizeHeadingLevel level)
                <$> normalizeLocation location
                <*> pure title
                <*> pure marker
        DecodedPresentationProse location prose ->
            NormalizedDocumentProse
                <$> normalizeLocation location
                <*> pure prose
        DecodedPresentationFormal location environment ->
            NormalizedDocumentFormal
                <$> normalizeLocation location
                <*> pure environment

    normalizeLocation =
        normalizeOwnedLocation
            sourceOrdinal
            (identifiedSourceDescriptor (candidateSourceIdentified source))

normalizeHeadingLevel :: DocumentHeadingLevel -> NormalizedHeadingLevel
normalizeHeadingLevel = \case
    DocumentSection -> NormalizedSection
    DocumentSubsection -> NormalizedSubsection
    DocumentSubsubsection -> NormalizedSubsubsection

normalizePrefixFailure
    :: Int
    -> CandidateSourceInput
    -> SourcePrefixError
    -> Either Text NormalizedFailure
normalizePrefixFailure sourceOrdinal source
        (SourcePrefixRejected rejection) =
    normalizeRejection "prefix" sourceOrdinal source rejection

normalizeRejection
    :: Text
    -> Int
    -> CandidateSourceInput
    -> SourceScanRejection
    -> Either Text NormalizedFailure
normalizeRejection phase sourceOrdinal source rejection =
    case rejection of
        SourceScanUnexpectedInput location input ->
            locatedFailure "unexpected-input" location [input]
        SourceScanUnexpectedEndOfInput location ->
            locatedFailure "unexpected-end-of-input" location []
        SourceScanExplicitFailure location message ->
            locatedFailure "explicit-failure" location [message]
        SourceScanLocationOutOfRange _file line column ->
            pure
                NormalizedFailure
                    { normalizedFailurePhase = phase
                    , normalizedFailureKind = "location-out-of-range"
                    , normalizedFailureLocation = Nothing
                    , normalizedFailureDetails =
                        [ Text.pack (show line)
                        , Text.pack (show column)
                        ]
                    }
  where
    locatedFailure kind location details = do
        normalizedLocation <- normalizeOwnedLocation
            sourceOrdinal
            (identifiedSourceDescriptor (candidateSourceIdentified source))
            location
        pure
            NormalizedFailure
                { normalizedFailurePhase = phase
                , normalizedFailureKind = kind
                , normalizedFailureLocation = Just normalizedLocation
                , normalizedFailureDetails = details
                }

forcePrefixFailure :: SourcePrefixError -> ()
forcePrefixFailure (SourcePrefixRejected rejection) =
    case rejection of
        SourceScanUnexpectedInput location input ->
            forceLocation location `seq` Text.length input `seq` ()
        SourceScanUnexpectedEndOfInput location ->
            forceLocation location
        SourceScanExplicitFailure location message ->
            forceLocation location `seq` Text.length message `seq` ()
        SourceScanLocationOutOfRange file line column ->
            forceString file `seq` line `seq` column `seq` ()

forceLocation :: Location -> ()
forceLocation location =
    locSourceDescriptor location
        `seq` locLine location
        `seq` locColumn location
        `seq` ()

forceString :: String -> ()
forceString = foldr (\character rest -> character `seq` rest) ()

forceList :: (value -> ()) -> [value] -> ()
forceList forceValue = \case
    [] -> ()
    value : rest -> forceValue value `seq` forceList forceValue rest

forceMaybe :: (value -> ()) -> Maybe value -> ()
forceMaybe forceValue = \case
    Nothing -> ()
    Just value -> forceValue value
