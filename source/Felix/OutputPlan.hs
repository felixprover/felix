{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Authority-free reservation of verification output namespaces.
module Felix.OutputPlan
    ( DumpOutputPlan
    , dumpOutputPath
    , VerificationOutputPlan
    , verificationDumpOutput
    , verificationHtmlRoutes
    , OutputNamespaceOwner(..)
    , OutputNamespaceCollision(..)
    , OutputPlanError(..)
    , renderOutputPlanError
    , planVerificationOutputs
    ) where

import Base
import Felix.Source
import Felix.Store
import Felix.Render.Html.Output qualified as Html

import Control.Exception (displayException)
import Control.Monad (foldM, when)
import Control.Monad.Trans.Except (ExceptT(..), runExceptT, throwE)
import Data.List qualified as List
import Data.Set qualified as Set
import Data.Text qualified as Text
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import System.Posix.Files qualified as PosixFiles


newtype DumpOutputPlan = DumpOutputPlan FilePath
    deriving stock (Show, Eq)

dumpOutputPath :: DumpOutputPlan -> FilePath
dumpOutputPath (DumpOutputPlan path) =
    path

data VerificationOutputPlan = VerificationOutputPlan
    !(Maybe DumpOutputPlan)
    !(Maybe Html.HtmlRoutePlan)

verificationDumpOutput
    :: VerificationOutputPlan
    -> Maybe DumpOutputPlan
verificationDumpOutput
        (VerificationOutputPlan dump _html) =
    dump

verificationHtmlRoutes
    :: VerificationOutputPlan
    -> Maybe Html.HtmlRoutePlan
verificationHtmlRoutes
        (VerificationOutputPlan _dump html) =
    html

data OutputNamespaceOwner
    = StoreOutputNamespace
    | StoreLockOutputNamespace
    | StoreJournalOutputNamespace
    | StoreWriteAheadLogOutputNamespace
    | StoreSharedMemoryOutputNamespace
    | DumpOutputNamespace
    | HtmlOutputRoot
    | HtmlPublicationWorkspace
    deriving stock (Show, Eq, Ord)

data OutputNamespaceCollision = OutputNamespaceCollision
    !OutputNamespaceOwner
    !FilePath
    !OutputNamespaceOwner
    !FilePath
    deriving stock (Show, Eq)

data OutputPlanError
    = EmptyDumpDestination
    | OutputPathInspectionFailed !FilePath !Text
    | DumpDestinationNotDirectory !FilePath
    | DumpDestinationNotEmpty !FilePath ![FilePath]
    | HtmlRoutePlanFailed !Html.HtmlOutputError
    | CollidingOutputNamespaces
        !(NonEmpty OutputNamespaceCollision)
    deriving stock (Show, Eq)

renderOutputPlanError :: OutputPlanError -> Text
renderOutputPlanError = \case
    EmptyDumpDestination ->
        "--dump requires a nonempty destination"
    OutputPathInspectionFailed path reason ->
        "could not inspect output path " <> quotePath path <> ": " <> reason
    DumpDestinationNotDirectory path ->
        "dump destination is not a directory: " <> quotePath path
    DumpDestinationNotEmpty path contents ->
        "dump destination " <> quotePath path
            <> " is not empty; choose an absent or empty directory"
            <> case contents of
                [] -> ""
                _ -> "; found "
                    <> Text.intercalate ", " (quotePath <$> contents)
    HtmlRoutePlanFailed failure ->
        Html.renderHtmlOutputError failure
    CollidingOutputNamespaces collisions ->
        "verification output namespaces collide: "
            <> Text.intercalate "; "
                (renderCollision <$> toList collisions)
  where
    renderCollision
        (OutputNamespaceCollision leftOwner leftPath rightOwner rightPath) =
            renderOwner leftOwner <> " " <> quotePath leftPath
                <> " conflicts with " <> renderOwner rightOwner
                <> " " <> quotePath rightPath

    renderOwner = \case
        StoreOutputNamespace -> "store"
        StoreLockOutputNamespace -> "store lock"
        StoreJournalOutputNamespace -> "store rollback journal"
        StoreWriteAheadLogOutputNamespace -> "store write-ahead log"
        StoreSharedMemoryOutputNamespace -> "store shared-memory file"
        DumpOutputNamespace -> "dump directory"
        HtmlOutputRoot -> "HTML output directory"
        HtmlPublicationWorkspace -> "HTML publication workspace"

quotePath :: FilePath -> Text
quotePath = Text.pack . show

planVerificationOutputs
    :: StorePath
    -> Bool
    -> Maybe FilePath
    -> Maybe (FilePath, [SafeRelativePath])
    -> IO (Either OutputPlanError VerificationOutputPlan)
planVerificationOutputs storePath refresh requestedDump requestedHtml = do
    dumpResult <- traverse planDumpOutput requestedDump
    case sequence dumpResult of
        Left failure ->
            pure (Left failure)
        Right dump -> do
            htmlResult <- traverse
                (uncurry Html.planHtmlRoutes)
                requestedHtml
            case sequence htmlResult of
                Left failure ->
                    pure (Left (HtmlRoutePlanFailed failure))
                Right html -> do
                    checked <- rejectCollisions storePath refresh dump html
                    pure (VerificationOutputPlan dump html <$ checked)

planDumpOutput
    :: FilePath
    -> IO (Either OutputPlanError DumpOutputPlan)
planDumpOutput requested
    | null requested =
        pure (Left EmptyDumpDestination)
    | otherwise = do
        absoluteResult <- inspectPath requested
            (Posix.normalise
                <$> Directory.makeAbsolute requested)
        case absoluteResult of
            Left failure ->
                pure (Left failure)
            Right absolute -> do
                existsResult <- inspectPath absolute
                    (pathEntryStatus absolute)
                case existsResult of
                    Left failure ->
                        pure (Left failure)
                    Right Nothing ->
                        pure (Right (DumpOutputPlan absolute))
                    Right (Just _) -> do
                        directoryResult <- inspectPath absolute
                            (PosixFiles.isDirectory <$> PosixFiles.getFileStatus absolute)
                        case directoryResult of
                            Left failure ->
                                pure (Left failure)
                            Right False ->
                                pure
                                    (Left
                                        (DumpDestinationNotDirectory
                                            absolute))
                            Right True -> do
                                contentsResult <- inspectPath absolute
                                    (List.sort
                                        <$> Directory.listDirectory
                                            absolute)
                                pure
                                    (case contentsResult of
                                        Left failure ->
                                            Left failure
                                        Right [] ->
                                            Right
                                                (DumpOutputPlan absolute)
                                        Right contents ->
                                            Left
                                                (DumpDestinationNotEmpty
                                                    absolute
                                                    contents))

rejectCollisions
    :: StorePath
    -> Bool
    -> Maybe DumpOutputPlan
    -> Maybe Html.HtmlRoutePlan
    -> IO (Either OutputPlanError ())
rejectCollisions _ _ Nothing Nothing = pure (Right ())
rejectCollisions storePath refresh dump html = runExceptT do
    -- Refresh removes sidecars only when the selected primary entry exists.
    -- Otherwise SQLite can still encounter an existing sidecar's referent.
    removesPrimary <- if refresh then
        isJust <$> ExceptT (inspectPath (storePathFilePath storePath)
            (pathEntryStatus (storePathFilePath storePath)))
        else pure False
    protectedStores <- traverse (protect removesPrimary) stores
    protectedDump <- traverse (protect removesPrimary) (toList dumpNamespace)
    protectedHtml <- traverse (protect removesPrimary) htmlNamespaces
    let pairs =
            [(store, destination) | store <- protectedStores, destination <- protectedDump]
                <> [(store, destination) | store <- protectedStores, destination <- protectedHtml]
                <> [(dumpOwner, htmlOwner) | dumpOwner <- protectedDump, htmlOwner <- protectedHtml]
        collisions =
            [ OutputNamespaceCollision leftOwner leftPath rightOwner rightPath
            | (((leftOwner, leftPath), leftIdentities), ((rightOwner, rightPath), rightIdentities)) <- pairs
            , or [namespacesOverlap left right | left <- leftIdentities, right <- rightIdentities]
            ]
    case collisions of
        [] -> pure ()
        firstCollision : remaining -> throwE (CollidingOutputNamespaces (firstCollision :| remaining))
  where
    protect removesPrimary namespace@(owner, path) = do
        identities <- ExceptT (inspectPath path do
            parent <- resolveIdentity (Posix.takeDirectory path)
            let entry = parent Posix.</> Posix.takeFileName path
                follows = case owner of
                    StoreOutputNamespace -> not refresh
                    StoreLockOutputNamespace -> True
                    StoreJournalOutputNamespace -> not removesPrimary
                    StoreWriteAheadLogOutputNamespace -> not removesPrimary
                    StoreSharedMemoryOutputNamespace -> not removesPrimary
                    DumpOutputNamespace -> True
                    HtmlOutputRoot -> False
                    HtmlPublicationWorkspace -> False
            if follows then do
                referent <- resolveIdentity path
                pure (if referent == entry then [entry] else [entry, referent])
            else pure [entry])
        pure (namespace, identities)
    stores =
        [ ( StoreOutputNamespace
          , storePathFilePath storePath
          )
        , ( StoreLockOutputNamespace
          , storeLockPath storePath
          )
        , ( StoreJournalOutputNamespace
          , storeRollbackJournalPath storePath
          )
        ]
        <> if refresh
            then
                [ ( StoreWriteAheadLogOutputNamespace
                  , storeWriteAheadLogPath storePath
                  )
                , ( StoreSharedMemoryOutputNamespace
                  , storeSharedMemoryPath storePath
                  )
                ]
            else []
    dumpNamespace =
        (\planned ->
            ( DumpOutputNamespace
            , dumpOutputPath planned
            ))
            <$> dump
    htmlNamespaces =
        case html of
            Nothing -> []
            Just routes ->
                [ (HtmlOutputRoot, Html.htmlRoutePlanOutputRoot routes)
                , (HtmlPublicationWorkspace, Html.htmlRoutePlanPublicationWorkspace routes)
                ]

-- Resolve aliases without changing operational paths or mistaking a dangling
-- final symlink for an absent entry. Missing suffixes remain part of the name;
-- inspection failures and cycles are errors, not evidence of non-overlap.
resolveIdentity :: FilePath -> IO FilePath
resolveIdentity = resolve Set.empty
  where
    resolve active path = foldM (step active) "/" (Posix.splitDirectories path)
    step _ _ "/" = pure "/"
    step _ parent "." = pathEntryStatus (parent Posix.</> ".") >> pure parent
    step _ parent ".." = pathEntryStatus (parent Posix.</> "..") >> pure (Posix.takeDirectory parent)
    step active parent component = do
        let path = parent Posix.</> component
        pathEntryStatus path >>= \case
            Just status | PosixFiles.isSymbolicLink status -> do
                when (Set.member path active)
                    (ioError (userError ("symbolic-link cycle while inspecting " <> show path)))
                target <- PosixFiles.readSymbolicLink path
                resolve (Set.insert path active)
                    (if Posix.isAbsolute target then target else parent Posix.</> target)
            _ -> pure path

pathEntryStatus :: FilePath -> IO (Maybe PosixFiles.FileStatus)
pathEntryStatus path = tryIOError (PosixFiles.getSymbolicLinkStatus path) >>= \case
    Left failure | isDoesNotExistError failure -> pure Nothing
                 | otherwise -> ioError failure
    Right status -> pure (Just status)

namespacesOverlap :: FilePath -> FilePath -> Bool
namespacesOverlap left right =
    components left `List.isPrefixOf` components right
        || components right `List.isPrefixOf` components left
  where
    components =
        Posix.splitDirectories
            . Posix.dropTrailingPathSeparator
            . Posix.normalise

inspectPath
    :: FilePath
    -> IO value
    -> IO (Either OutputPlanError value)
inspectPath path action = do
    result <- tryIOError action
    pure
        (case result of
            Left failure ->
                Left
                    (OutputPathInspectionFailed
                        path
                        (Text.pack
                            (displayException failure)))
            Right value ->
                Right value)
