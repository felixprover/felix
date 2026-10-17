{-# LANGUAGE NoImplicitPrelude #-}

-- | Small in-memory adapters for parser and extraction tests. Production
-- source loading uses registered physical sources instead.
module Felix.Test.SourceScan.Adapter
    ( scanTestSource
    , scanTestImports
    , scanTestVerification
    , scanTestPresentation
    ) where

import Base

import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Felix.Report.Location (SourceDescriptor)
import Felix.Source.Scan qualified as SourceScan
import Felix.Syntax.Token (Located(..), Token)


scanTestSource
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either String ([FilePath], [[Located Token]])
scanTestSource descriptor file source = do
    verification <- scanTestVerification descriptor file source
    pure
        ( unLocated <$> SourceScan.verificationImports verification
        , SourceScan.verificationChunks verification
        )

scanTestImports
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either String [Located FilePath]
scanTestImports descriptor file source = do
    verification <- scanTestVerification descriptor file source
    pure (SourceScan.verificationImports verification)

scanTestVerification
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either String SourceScan.VerificationScan
scanTestVerification descriptor file source =
    case SourceScan.scanCompleteVerificationText descriptor file source of
        Left (SourceScan.SourceInputFailure failure) ->
            Left
                (Text.unpack
                    (SourceScan.renderVerificationScanError failure))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            Left
                (Text.unpack
                    (SourceScan.renderSourceScanInvariantError failure))
        Right result -> Right result

scanTestPresentation
    :: SourceDescriptor
    -> FilePath
    -> Text
    -> Either String [SourceScan.DecodedPresentationSegment]
scanTestPresentation descriptor file source =
    case SourceScan.scanCompletePresentationText descriptor file source of
        Left (SourceScan.SourceInputFailure failure) ->
            Left
                (Text.unpack
                    (SourceScan.renderPresentationScanError failure))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            Left
                (Text.unpack
                    (SourceScan.renderSourceScanInvariantError failure))
        Right result -> Right (Vector.toList result)
