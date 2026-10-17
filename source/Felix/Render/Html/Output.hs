{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Confined whole-snapshot publication for generated HTML.
--
-- The exact output directory is user-owned and may be replaced in full. The
-- parent directory is assumed not to be changed by a hostile actor during one
-- publication. The target itself is inspected without following a final
-- symlink immediately before destructive replacement.
module Felix.Render.Html.Output
    ( PreparedHtmlArtefact
    , preparedHtmlArtefact
    , preparedHtmlArtefactDestination
    , HtmlRoutePlan
    , htmlRoutePlanOutputRoot
    , htmlRoutePlanPublicationWorkspace
    , htmlRoutePlanDestinations
    , planHtmlRoutes
    , HtmlOutputPlan
    , HtmlOutputError(..)
    , renderHtmlOutputError
    , planHtmlOutput
    , planHtmlOutputAgainst
    , HtmlPublicationError(..)
    , renderHtmlPublicationError
    , HtmlSnapshotOperations(..)
    , defaultHtmlSnapshotOperations
    , replaceHtmlSnapshotWith
    , writeHtmlOutput
    ) where

import Base
import Felix.Source
    ( SafeRelativePath
    , safeRelativePathFilePath
    )

import Control.Exception (Exception, IOException, displayException, evaluate)
import Control.Exception qualified as Exception
import Control.Monad (unless, when)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import System.FileLock qualified as FileLock
import System.Posix.Files qualified as PosixFiles


-- | One lazily rendered artefact. Its trusted relative destination is
-- available before the rendering result is demanded.
data PreparedHtmlArtefact = PreparedHtmlArtefact
    !SafeRelativePath
    (Either Text ByteString)

preparedHtmlArtefact
    :: SafeRelativePath
    -> Either Text ByteString
    -> PreparedHtmlArtefact
preparedHtmlArtefact =
    PreparedHtmlArtefact

preparedHtmlArtefactDestination
    :: PreparedHtmlArtefact
    -> SafeRelativePath
preparedHtmlArtefactDestination
        (PreparedHtmlArtefact destination _rendered) =
    destination


-- | Authority-free evidence for the exact output root and reserved artefact
-- namespace. Constructors and absolute paths stay private to this module.
data HtmlRoutePlan = HtmlRoutePlan
    !FilePath
    ![SafeRelativePath]

htmlRoutePlanOutputRoot :: HtmlRoutePlan -> FilePath
htmlRoutePlanOutputRoot (HtmlRoutePlan outputRoot _destinations) =
    outputRoot

htmlRoutePlanPublicationWorkspace :: HtmlRoutePlan -> FilePath
htmlRoutePlanPublicationWorkspace = publicationWorkspace . publicationPaths . htmlRoutePlanOutputRoot

htmlRoutePlanDestinations :: HtmlRoutePlan -> [SafeRelativePath]
htmlRoutePlanDestinations (HtmlRoutePlan _outputRoot destinations) =
    destinations

data HtmlOutputPlan = HtmlOutputPlan
    !FilePath
    ![PreparedHtmlArtefact]

data HtmlOutputError
    = EmptyPreparedHtmlOutput
    | DuplicatePreparedHtmlDestination !SafeRelativePath
    | HtmlOutputRouteMismatch
        ![SafeRelativePath]
        ![SafeRelativePath]
    | EmptyHtmlOutputRoot
    | UnsafeHtmlOutputRoot !FilePath
    | HtmlOutputPathInspectionFailed !FilePath !Text
    | HtmlOutputRootIsSymbolicLink !FilePath
    | HtmlOutputRootNotDirectory !FilePath
    | HtmlOutputParentNotDirectory !FilePath
    deriving stock (Show, Eq)

renderHtmlOutputError :: HtmlOutputError -> Text
renderHtmlOutputError = \case
    EmptyPreparedHtmlOutput ->
        "HTML output contains no artefacts"
    DuplicatePreparedHtmlDestination relative ->
        "HTML output contains destination more than once: "
            <> quoteRelative relative
    HtmlOutputRouteMismatch planned prepared ->
        "prepared HTML destinations do not match the reserved routes; planned "
            <> renderRelatives planned <> ", prepared "
            <> renderRelatives prepared
    EmptyHtmlOutputRoot ->
        "HTML output root is empty"
    UnsafeHtmlOutputRoot path ->
        "refusing to replace unsafe HTML output root " <> quotePath path
    HtmlOutputPathInspectionFailed path reason ->
        "could not inspect HTML output path " <> quotePath path <> ": " <> reason
    HtmlOutputRootIsSymbolicLink path ->
        "HTML output root is a symbolic link: " <> quotePath path
    HtmlOutputRootNotDirectory path ->
        "HTML output root is not a directory: " <> quotePath path
    HtmlOutputParentNotDirectory path ->
        "HTML output parent is not a directory: " <> quotePath path
  where
    renderRelatives = Text.intercalate ", " . fmap quoteRelative

quoteRelative :: SafeRelativePath -> Text
quoteRelative = quotePath . safeRelativePathFilePath

quotePath :: FilePath -> Text
quotePath = Text.pack . show

instance Exception HtmlOutputError

-- | Validate the output root and reserved relative destinations without
-- changing the filesystem.
planHtmlRoutes
    :: FilePath
    -> [SafeRelativePath]
    -> IO (Either HtmlOutputError HtmlRoutePlan)
planHtmlRoutes requestedRoot destinations =
    runExceptT do
        when (null destinations) (throwE EmptyPreparedHtmlOutput)
        case duplicateDestinations destinations of
            duplicate : _ ->
                throwE (DuplicatePreparedHtmlDestination duplicate)
            [] -> pure ()
        outputRoot <- planOutputRoot requestedRoot
        let paths = publicationPaths outputRoot
        _ <- inspectPath (publicationWorkspace paths) (inspectPublicationWorkspace paths)
        pure (HtmlRoutePlan outputRoot (List.sort destinations))

planOutputRoot :: FilePath -> ExceptT HtmlOutputError IO FilePath
planOutputRoot requestedRoot = do
    when (null requestedRoot) (throwE EmptyHtmlOutputRoot)
    absoluteRequested <-
        inspectPath requestedRoot
            (Posix.normalise <$> Directory.makeAbsolute requestedRoot)
    let withoutTrailing = Posix.dropTrailingPathSeparator absoluteRequested
        parent = Posix.takeDirectory withoutTrailing
        name = Posix.takeFileName withoutTrailing
    when (null name || name == "." || name == ".." || parent == withoutTrailing)
        (throwE (UnsafeHtmlOutputRoot withoutTrailing))
    parentExists <- inspectPath parent (Directory.doesDirectoryExist parent)
    when (not parentExists) (throwE (HtmlOutputParentNotDirectory parent))
    canonicalParent <- inspectPath parent (Directory.canonicalizePath parent)
    let outputRoot = canonicalParent Posix.</> name
    inspectOutputRoot outputRoot
    pure outputRoot

-- | Plan directly from prepared artefacts. Most callers reserve routes before
-- verification and use 'planHtmlOutputAgainst' afterward.
planHtmlOutput
    :: FilePath
    -> [PreparedHtmlArtefact]
    -> IO (Either HtmlOutputError HtmlOutputPlan)
planHtmlOutput outputRoot artefacts = do
    routes <-
        planHtmlRoutes
            outputRoot
            (preparedHtmlArtefactDestination <$> artefacts)
    pure (routes >>= (`planHtmlOutputAgainst` artefacts))

planHtmlOutputAgainst
    :: HtmlRoutePlan
    -> [PreparedHtmlArtefact]
    -> Either HtmlOutputError HtmlOutputPlan
planHtmlOutputAgainst
        (HtmlRoutePlan outputRoot plannedDestinations)
        artefacts
    | null artefacts =
        Left EmptyPreparedHtmlOutput
    | duplicate : _ <- duplicateDestinations preparedDestinations =
        Left (DuplicatePreparedHtmlDestination duplicate)
    | Set.fromList plannedDestinations
        /= Set.fromList preparedDestinations =
            Left
                (HtmlOutputRouteMismatch
                    plannedDestinations
                    preparedDestinations)
    | otherwise =
        Right (HtmlOutputPlan outputRoot artefacts)
  where
    preparedDestinations =
        preparedHtmlArtefactDestination <$> artefacts

duplicateDestinations :: [SafeRelativePath] -> [SafeRelativePath]
duplicateDestinations destinations =
    [ destination
    | (destination, multiplicity) <-
        Map.toAscList
            (Map.fromListWith (+)
                [(destination, 1 :: Int) | destination <- destinations])
    , multiplicity > 1
    ]


data HtmlPublicationError
    = HtmlArtefactRenderingFailed !SafeRelativePath !Text
    | HtmlPublicationWorkspaceFailed !FilePath !Text
    | HtmlPublicationBusy !FilePath
    | HtmlStagingDirectoryFailed !FilePath !Text
    | HtmlArtefactStagingFailed
        !FilePath
        !SafeRelativePath
        !Text
    | HtmlSnapshotReplacementFailed
        !FilePath
        !FilePath
        !Text
    | HtmlSnapshotInstallationFailedRestored
        !FilePath
        !FilePath
        !FilePath
        !Text
    | HtmlSnapshotRollbackFailed
        !FilePath
        !FilePath
        !FilePath
        !Text
        !Text
    | HtmlSnapshotCleanupFailed
        !FilePath
        !FilePath
        !Text
    | HtmlSnapshotRecoveryFailed
        !FilePath
        !FilePath
        !Text
    deriving stock (Show, Eq)

instance Exception HtmlPublicationError

renderHtmlPublicationError :: HtmlPublicationError -> [Text]
renderHtmlPublicationError = \case
    HtmlPublicationWorkspaceFailed workspace reason ->
        [ "could not use HTML publication workspace " <> quotePath workspace
            <> ": " <> reason
        , "inspect the retained workspace before retrying; unowned paths are not adopted"
        ]
    HtmlPublicationBusy workspace ->
        [ "another HTML publisher holds workspace " <> quotePath workspace ]
    HtmlArtefactRenderingFailed relative reason ->
        [ "HTML rendering failed for " <> quoteRelative relative
            <> ": " <> reason
        ]
    HtmlStagingDirectoryFailed outputRoot reason ->
        [ "could not create a staging directory beside "
            <> quotePath outputRoot <> ": " <> reason
        ]
    HtmlArtefactStagingFailed staging relative reason ->
        [ "could not stage HTML artefact " <> quoteRelative relative
            <> " below " <> quotePath staging <> ": " <> reason
        ]
    HtmlSnapshotReplacementFailed outputRoot staging reason ->
        [ "could not replace HTML snapshot " <> quotePath outputRoot
            <> ": " <> reason
        , "the completed staging snapshot was retained at "
            <> quotePath staging
        ]
    HtmlSnapshotInstallationFailedRestored
            outputRoot staging backup reason ->
        [ "could not install HTML snapshot " <> quotePath outputRoot
            <> ": " <> reason
        , "the previous snapshot was restored from " <> quotePath backup
        , "the completed staging snapshot was retained at "
            <> quotePath staging
        ]
    HtmlSnapshotRollbackFailed
            outputRoot staging backup installationReason rollbackReason ->
        [ "could not install HTML snapshot " <> quotePath outputRoot
            <> ": " <> installationReason
        , "could not restore the previous snapshot from " <> quotePath backup
            <> ": " <> rollbackReason
        , "the completed staging snapshot was retained at "
            <> quotePath staging
        ]
    HtmlSnapshotCleanupFailed outputRoot artefact reason ->
        [ "could not clean publication workspace for " <> quotePath outputRoot
            <> "; retained artefact "
            <> quotePath artefact <> ": " <> reason
        ]
    HtmlSnapshotRecoveryFailed outputRoot backup reason ->
        [ "could not recover missing HTML snapshot " <> quotePath outputRoot
            <> " from " <> quotePath backup <> ": " <> reason
        ]

-- | The only filesystem operations injected into snapshot replacement.
-- Keeping this seam narrow makes the rollback failure windows testable
-- without introducing a general filesystem abstraction.
data HtmlSnapshotOperations = HtmlSnapshotOperations
    { htmlSnapshotRenameDirectory :: FilePath -> FilePath -> IO ()
    , htmlSnapshotRemovePath :: FilePath -> IO ()
    }

defaultHtmlSnapshotOperations :: HtmlSnapshotOperations
defaultHtmlSnapshotOperations =
    HtmlSnapshotOperations
        { htmlSnapshotRenameDirectory = Directory.renameDirectory
        , htmlSnapshotRemovePath = Directory.removePathForcibly
        }

-- | Demand every renderer result, write a complete owned staging tree, and
-- replace the old snapshot only after staging succeeds.
writeHtmlOutput
    :: HtmlOutputPlan
    -> IO (Either HtmlPublicationError ())
writeHtmlOutput (HtmlOutputPlan outputRoot artefacts) = do
    materialized <- materializeArtefacts artefacts
    case materialized of
        Left failure -> pure (Left failure)
        Right rendered -> withPublication defaultHtmlSnapshotOperations paths do
            let staging = publicationStaging paths
            stagingResult <- tryIOException (Directory.createDirectory staging)
            case stagingResult of
                Left failure ->
                    pure
                        (Left
                            (HtmlStagingDirectoryFailed
                                outputRoot
                                (Text.pack (displayException failure))))
                Right () -> do
                    staged <- stageArtefacts staging rendered
                    case staged of
                        Left failure -> do
                            cleanupStaging staging
                            pure (Left failure)
                        Right () ->
                            installSnapshot
                                defaultHtmlSnapshotOperations
                                paths
  where
    paths = publicationPaths outputRoot

materializeArtefacts
    :: [PreparedHtmlArtefact]
    -> IO
        (Either
            HtmlPublicationError
            [(SafeRelativePath, ByteString)])
materializeArtefacts = go
  where
    go [] = pure (Right [])
    go (PreparedHtmlArtefact relative rendered : remaining) =
        case rendered of
            Left failure ->
                pure (Left (HtmlArtefactRenderingFailed relative failure))
            Right bytes -> do
                _length <- evaluate (ByteString.length bytes)
                go remaining >>= \case
                    Left failure -> pure (Left failure)
                    Right rest -> pure (Right ((relative, bytes) : rest))

stageArtefacts
    :: FilePath
    -> [(SafeRelativePath, ByteString)]
    -> IO (Either HtmlPublicationError ())
stageArtefacts staging = go
  where
    go [] = pure (Right ())
    go ((relative, bytes) : remaining) = do
        let destination =
                foldl'
                    (Posix.</>)
                    staging
                    (Posix.splitDirectories
                        (safeRelativePathFilePath relative))
        result <- tryIOException do
            Directory.createDirectoryIfMissing
                True
                (Posix.takeDirectory destination)
            ByteString.writeFile destination bytes
        case result of
            Left failure ->
                pure
                    (Left
                        (HtmlArtefactStagingFailed
                            staging
                            relative
                            (Text.pack (displayException failure))))
            Right () -> go remaining

replaceHtmlSnapshotWith
    :: HtmlSnapshotOperations
    -> FilePath
    -> FilePath
    -> IO (Either HtmlPublicationError ())
replaceHtmlSnapshotWith operations outputRoot staging = do
    planned <- runExceptT (planOutputRoot outputRoot)
    case planned of
        Left failure -> pure (Left (HtmlPublicationWorkspaceFailed outputRoot (renderHtmlOutputError failure)))
        Right root -> do
            let paths = publicationPaths root
            validated <- tryIOException do
                present <- inspectReplacementTarget staging
                unless present (ioError (userError "the supplied staging directory is absent"))
                canonical <- Directory.canonicalizePath staging
                when (any (pathsOverlap canonical) [root, publicationWorkspace paths])
                    (ioError (userError "the supplied staging directory overlaps the output or publication workspace"))
                pure canonical
            case validated of
                Left failure -> pure (Left (HtmlSnapshotReplacementFailed root staging (exceptionText failure)))
                Right supplied -> withPublication operations paths do
                    adopted <- tryRename operations supplied (publicationStaging paths)
                    case adopted of
                        Left failure -> pure (Left (HtmlSnapshotReplacementFailed root supplied (exceptionText failure)))
                        Right () -> installSnapshot operations paths

-- The lease protects fixed slots, not a collection of prefix-named transactions.
-- The marker is matched against derived paths; it never supplies deletion paths.
data PublicationPaths = PublicationPaths
    { publicationRoot :: !FilePath
    , publicationWorkspace :: !FilePath
    , publicationStaging :: !FilePath
    , publicationBackup :: !FilePath
    }

publicationPaths :: FilePath -> PublicationPaths
publicationPaths root =
    let workspace = root <> ".felix-publication"
    in PublicationPaths root workspace (workspace Posix.</> "staging") (workspace Posix.</> "backup")

publicationMarker :: PublicationPaths -> ByteString
publicationMarker paths = "felix-html-publication-v1\n" <> TextEncoding.encodeUtf8 (Text.pack (publicationRoot paths))

entryStatus :: FilePath -> IO (Maybe PosixFiles.FileStatus)
entryStatus path = tryIOException (PosixFiles.getSymbolicLinkStatus path) >>= \case
    Left failure | isDoesNotExistError failure -> pure Nothing
                 | otherwise -> Exception.throwIO failure
    Right status -> pure (Just status)

requireEntryKind :: (PosixFiles.FileStatus -> Bool) -> FilePath -> IO Bool
requireEntryKind kind path = entryStatus path >>= \case
    Nothing -> pure False
    Just status
        | not (PosixFiles.isSymbolicLink status) && kind status -> pure True
        | otherwise -> ioError (userError ("unsafe publication entry: " <> show path))

inspectPublicationWorkspace :: PublicationPaths -> IO Bool
inspectPublicationWorkspace paths = do
    exists <- requireEntryKind PosixFiles.isDirectory workspace
    when exists do
        let marker = workspace Posix.</> "owner"
            expected = publicationMarker paths
        valid <- entryStatus marker >>= \case
            Just status | PosixFiles.isRegularFile status
                && PosixFiles.fileSize status == fromIntegral (ByteString.length expected) ->
                    (== expected) <$> ByteString.readFile marker
            _ -> pure False
        unless valid (ioError (userError "missing, malformed, or wrong-root ownership marker"))
        _ <- requireEntryKind PosixFiles.isRegularFile (workspace Posix.</> "lock")
        pure ()
    pure exists
  where
    workspace = publicationWorkspace paths

withPublication
    :: HtmlSnapshotOperations -> PublicationPaths
    -> IO (Either HtmlPublicationError ()) -> IO (Either HtmlPublicationError ())
withPublication operations paths action = do
    result <- tryIOException $ Exception.mask \restore -> do
        exists <- inspectPublicationWorkspace paths
        unless exists do
            -- An unsuccessful mkdir never grants ownership, even if a concurrent
            -- initializer has created an empty directory in the meantime.
            Directory.createDirectory workspace
            ByteString.writeFile (workspace Posix.</> "owner") (publicationMarker paths)
        acquired <- FileLock.tryLockFile (workspace Posix.</> "lock") FileLock.Exclusive
        case acquired of
            Nothing -> pure (Left (HtmlPublicationBusy workspace))
            Just lease -> Exception.finally (restore do
                _ <- inspectPublicationWorkspace paths
                entries <- Directory.listDirectory workspace
                unless (all (`elem` ["owner", "lock", "staging", "backup"]) entries)
                    (ioError (userError "unexpected entries in publication workspace"))
                recovered <- recoverInterruptedSnapshot operations paths
                case recovered of
                    Left failure -> pure (Left failure)
                    Right () -> action)
                (FileLock.unlockFile lease)
    pure (either (Left . HtmlPublicationWorkspaceFailed workspace . exceptionText) id result)
  where
    workspace = publicationWorkspace paths

pathsOverlap :: FilePath -> FilePath -> Bool
pathsOverlap left right =
    components left `List.isPrefixOf` components right || components right `List.isPrefixOf` components left
  where
    components = Posix.splitDirectories . Posix.dropTrailingPathSeparator . Posix.normalise

installSnapshot
    :: HtmlSnapshotOperations
    -> PublicationPaths
    -> IO (Either HtmlPublicationError ())
installSnapshot operations paths = Exception.mask_ do
    inspected <- tryIOException (inspectReplacementTarget outputRoot)
    case inspected of
        Left failure -> replacementFailed failure
        Right False -> do
            installed <- tryRename operations staging outputRoot
            case installed of
                Left failure -> replacementFailed failure
                Right () -> pure (Right ())
        Right True -> do
            backedUp <- tryRename operations outputRoot backup
            case backedUp of
                Left failure -> replacementFailed failure
                Right () -> do
                    installed <- tryRename operations staging outputRoot
                    case installed of
                        Right () ->
                            cleanupPublicationArtefacts operations outputRoot [backup]
                        Left installationFailure -> do
                            rolledBack <-
                                tryRename operations backup outputRoot
                            case rolledBack of
                                Right () ->
                                    pure
                                        (Left
                                            (HtmlSnapshotInstallationFailedRestored
                                                outputRoot
                                                staging
                                                backup
                                                (exceptionText
                                                    installationFailure)))
                                Left rollbackFailure ->
                                    pure
                                        (Left
                                            (HtmlSnapshotRollbackFailed
                                                outputRoot
                                                staging
                                                backup
                                                (exceptionText
                                                    installationFailure)
                                                (exceptionText
                                                    rollbackFailure)))
  where
    outputRoot = publicationRoot paths
    staging = publicationStaging paths
    backup = publicationBackup paths
    replacementFailed failure =
        pure
            (Left
                (HtmlSnapshotReplacementFailed
                    outputRoot
                    staging
                    (exceptionText failure)))

recoverInterruptedSnapshot
    :: HtmlSnapshotOperations
    -> PublicationPaths
    -> IO (Either HtmlPublicationError ())
recoverInterruptedSnapshot operations paths = do
    rootPresent <- inspectReplacementTarget root
    staged <- requireEntryKind PosixFiles.isDirectory staging
    backedUp <- requireEntryKind PosixFiles.isDirectory backup
    if rootPresent && staged && backedUp then
        pure (Left (HtmlPublicationWorkspaceFailed (publicationWorkspace paths)
            "root, staging, and backup all exist; retained all copies"))
    else if not rootPresent && backedUp then do
        restored <- tryRename operations backup root
        case restored of
            Left failure -> pure (Left (HtmlSnapshotRecoveryFailed root backup (exceptionText failure)))
            Right () -> cleanupPublicationArtefacts operations root [staging | staged]
    else cleanupPublicationArtefacts operations root
        ([backup | backedUp] <> [staging | staged])
  where
    root = publicationRoot paths
    staging = publicationStaging paths
    backup = publicationBackup paths

cleanupPublicationArtefacts
    :: HtmlSnapshotOperations
    -> FilePath
    -> [FilePath]
    -> IO (Either HtmlPublicationError ())
cleanupPublicationArtefacts operations outputRoot = cleanup
  where
    cleanup [] = pure (Right ())
    cleanup (artefact : remaining) = do
        removed <-
            tryIOException
                (htmlSnapshotRemovePath operations artefact)
        case removed of
            Right () -> cleanup remaining
            Left failure ->
                pure
                    (Left
                        (HtmlSnapshotCleanupFailed
                            outputRoot
                            artefact
                            (exceptionText failure)))

tryRename
    :: HtmlSnapshotOperations
    -> FilePath
    -> FilePath
    -> IO (Either IOException ())
tryRename operations source destination =
    tryIOException
        (htmlSnapshotRenameDirectory operations source destination)

exceptionText :: IOException -> Text
exceptionText = Text.pack . displayException

-- This check is deliberately repeated immediately before replacement because
-- the target is mutable external state; the route plan cannot preserve
-- evidence about its later filesystem kind.
inspectReplacementTarget :: FilePath -> IO Bool
inspectReplacementTarget target = do
    status <- tryIOException (PosixFiles.getSymbolicLinkStatus target)
    case status of
        Left failure
            | isDoesNotExistError failure -> pure False
            | otherwise -> Exception.throwIO failure
        Right targetStatus
            | PosixFiles.isSymbolicLink targetStatus ->
                Exception.throwIO
                    (userError
                        (Text.unpack
                            (renderHtmlOutputError
                                (HtmlOutputRootIsSymbolicLink target))))
            | PosixFiles.isDirectory targetStatus -> pure True
            | otherwise ->
                Exception.throwIO
                    (userError
                        (Text.unpack
                            (renderHtmlOutputError
                                (HtmlOutputRootNotDirectory target))))

inspectOutputRoot :: FilePath -> ExceptT HtmlOutputError IO ()
inspectOutputRoot target = do
    status <-
        liftIO (tryIOException (PosixFiles.getSymbolicLinkStatus target))
    case status of
        Left failure
            | isDoesNotExistError failure -> pure ()
            | otherwise ->
                throwE
                    (HtmlOutputPathInspectionFailed
                        target
                        (Text.pack (displayException failure)))
        Right targetStatus
            | PosixFiles.isSymbolicLink targetStatus ->
                throwE (HtmlOutputRootIsSymbolicLink target)
            | PosixFiles.isDirectory targetStatus -> pure ()
            | otherwise ->
                throwE (HtmlOutputRootNotDirectory target)

cleanupStaging :: FilePath -> IO ()
cleanupStaging staging = do
    _ignored <- tryIOException (Directory.removePathForcibly staging)
    pure ()

inspectPath
    :: FilePath
    -> IO a
    -> ExceptT HtmlOutputError IO a
inspectPath path action = do
    result <- liftIO (tryIOException action)
    case result of
        Right value -> pure value
        Left failure ->
            throwE
                (HtmlOutputPathInspectionFailed
                    path
                    (Text.pack (displayException failure)))

tryIOException :: IO a -> IO (Either IOException a)
tryIOException =
    Exception.try
