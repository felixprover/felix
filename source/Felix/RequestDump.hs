{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact prepared-request dump publication.
module Felix.RequestDump
    ( DumpObservationError(..)
    , prepareRequestObserver
    , captureDumpFailure
    , renderDumpObservationError
    ) where

import Base
import Felix.Output.Atomic (writeBytesAtomically)
import Felix.OutputPlan qualified as Output
import Felix.Verification
    ( VerificationRequestObserver
    , verificationRequestObserver
    )
import Felix.Provers

import Control.Exception (displayException)
import Control.Exception qualified as Exception
import Data.Text qualified as Text
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix

data DumpObservationError
    = DumpDirectoryCreationFailed !FilePath !Text
    | DumpRequestWriteFailed !WorkPosition !FilePath !Text
    deriving stock (Show, Eq)

instance Exception.Exception DumpObservationError

prepareRequestObserver
    :: Maybe Output.DumpOutputPlan
    -> IO (Either DumpObservationError VerificationRequestObserver)
prepareRequestObserver = \case
    Nothing ->
        pure
            (Right
                (verificationRequestObserver
                    (\_position _request -> pure ())))
    Just dumpPlan -> do
        let root = Output.dumpOutputPath dumpPlan
        created <- tryIOError
            (Directory.createDirectoryIfMissing True root)
        pure case created of
            Left failure ->
                Left
                    (DumpDirectoryCreationFailed
                        root
                        (Text.pack (displayException failure)))
            Right () ->
                Right (verificationRequestObserver (writeDumpRequest root))

writeDumpRequest
    :: FilePath
    -> WorkPosition
    -> PreparedVerificationRequest
    -> IO ()
writeDumpRequest root position request = do
    let destination =
            root
                Posix.</> ( show (workPositionModuleOrdinal position)
                            <> "-"
                            <> show (workPositionLocalRequestOrdinal position)
                         )
                Posix.<.> "p"
    tryIOError
        (writeBytesAtomically
            destination
            (preparedVerificationBytes request)) >>= \case
                Left failure ->
                    Exception.throwIO
                        (DumpRequestWriteFailed
                            position
                            destination
                            (Text.pack (displayException failure)))
                Right () -> pure ()

captureDumpFailure
    :: IO value
    -> IO (Either DumpObservationError value)
captureDumpFailure = Exception.try

renderDumpObservationError :: DumpObservationError -> Text
renderDumpObservationError = \case
    DumpDirectoryCreationFailed path message ->
        "Could not create dump directory "
            <> Text.pack (show path)
            <> ": "
            <> message
    DumpRequestWriteFailed _position path message ->
        "Could not write request dump "
            <> Text.pack (show path)
            <> ": "
            <> message
