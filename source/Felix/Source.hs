{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Physical source names and mount policy.
--
-- A 'SafeRelativePath' is interpreted from a source mount, never from the
-- importing file.  A 'CanonicalPath' is an absolute host path used only to
-- identify the physical file selected during this invocation.
module Felix.Source
    ( SourceMountId
    , sourceMountId
    , sourceMountIdText
    , CanonicalPath
    , canonicalPathFilePath
    , SafeRelativePath
    , safeRelativePath
    , safeRelativePathFilePath
    , SourceMount
    , sourceMountIdentifier
    , sourceMountRoot
    , SourceMounts
    , prepareSourceMounts
    , sourceMountList
    , RootRequest
    , searchedRoot
    , existingRoot
    , canonicalizeExistingSourcePath
    , rootRequestSpelling
    , ResolvedSource
    , resolvedSourceCanonicalPath
    , resolvedSourceMount
    , resolvedSourceMountRoot
    , resolvedSourceRelativePath
    , resolvedSourceLocationPath
    , ResolvedSourceAddress
    , resolvedSourceAddress
    , sourceAddressMount
    , sourceAddressRoot
    , sourceAddressRelativePath
    , LoadedSource
    , loadedSource
    , loadedBytes
    , loadedText
    , loadedByteCount
    , ImportRef
    , importRef
    , importPath
    , importLocation
    , SourceCandidate
    , sourceCandidateMount
    , sourceCandidatePath
    , sourceCandidates
    , attributeCanonicalSource
    , resolveRoot
    , resolveImport
    , loadResolvedSource
    , resolveAndLoadRoot
    , resolveAndLoadImport
    , SourceLookup(..)
    , SourceCycleStep
    , sourceCycleStep
    , cycleImporter
    , cycleImport
    , cycleImported
    , RelativePathError(..)
    , SourceError(..)
    , renderSourceError
    ) where

import Base

import Control.DeepSeq (NFData(..))
import Control.Exception (Exception, IOException, displayException, try)
import Data.Bifunctor (first)
import Data.ByteString qualified as ByteString
import Data.Char (ord)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Encoding
import Felix.Report.Location
    ( Location
    , locationToText
    )
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import System.Posix.Files qualified as PosixFiles


-- | Invocation-local name of a configured source mount.
newtype SourceMountId = SourceMountId Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

sourceMountId :: Text -> SourceMountId
sourceMountId = SourceMountId

sourceMountIdText :: SourceMountId -> Text
sourceMountIdText (SourceMountId ident) = ident


-- | Absolute canonical host path.
newtype CanonicalPath = CanonicalPath FilePath
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

canonicalPathFilePath :: CanonicalPath -> FilePath
canonicalPathFilePath (CanonicalPath path) = path


-- | Nonempty mount-root-relative POSIX path without @.@, @..@, or empty
-- components.  A backslash is an ordinary filename character.
newtype SafeRelativePath = SafeRelativePath FilePath
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

safeRelativePathFilePath :: SafeRelativePath -> FilePath
safeRelativePathFilePath (SafeRelativePath path) = path

data RelativePathError
    = EmptyRelativePath
    | AbsoluteRelativePath
    | EmptyPathComponent
    | CurrentDirectoryComponent
    | ParentDirectoryComponent
    | NullPathCharacter
    | NonUnicodeScalarPathCharacter
    deriving stock (Show, Eq)

safeRelativePath :: FilePath -> Either RelativePathError SafeRelativePath
safeRelativePath path
    | null path =
        Left EmptyRelativePath
    | Posix.isAbsolute path =
        Left AbsoluteRelativePath
    | '\0' `elem` path =
        Left NullPathCharacter
    | any (not . isUnicodeScalar) path =
        Left NonUnicodeScalarPathCharacter
    | any null components =
        Left EmptyPathComponent
    | "." `elem` components =
        Left CurrentDirectoryComponent
    | ".." `elem` components =
        Left ParentDirectoryComponent
    | otherwise =
        Right (SafeRelativePath path)
  where
    components = splitPathComponents path

splitPathComponents :: FilePath -> [FilePath]
splitPathComponents path =
    case break (== '/') path of
        (component, []) ->
            [component]
        (component, _slash : rest) ->
            component : splitPathComponents rest


data SourceMount = SourceMount
    !SourceMountId
    !CanonicalPath
    deriving stock (Show, Eq)

sourceMountIdentifier :: SourceMount -> SourceMountId
sourceMountIdentifier (SourceMount ident _root) = ident

sourceMountRoot :: SourceMount -> CanonicalPath
sourceMountRoot (SourceMount _ident root) = root

-- | Validated ordered source mounts.  Order controls candidate search only;
-- canonical ownership is determined independently.
newtype SourceMounts = SourceMounts (NonEmpty SourceMount)
    deriving stock (Show, Eq)

sourceMountList :: SourceMounts -> [SourceMount]
sourceMountList (SourceMounts mounts) = toList mounts


data RootRequest
    = SearchedRoot !SafeRelativePath
    | ExistingRoot !CanonicalPath !FilePath
    deriving stock (Show)

-- The exact-root spelling is diagnostic trivia and does not participate in
-- request equality.
instance Eq RootRequest where
    SearchedRoot left == SearchedRoot right =
        left == right
    ExistingRoot left _leftSpelling == ExistingRoot right _rightSpelling =
        left == right
    _ == _ =
        False

searchedRoot :: FilePath -> Either SourceError RootRequest
searchedRoot path =
    SearchedRoot <$> first (InvalidSearchedRoot path) (safeRelativePath path)

-- | Validate and canonicalize an absolute spelling of an existing source.
existingRoot :: FilePath -> IO (Either SourceError RootRequest)
existingRoot path
    | not (Posix.isAbsolute path) =
        pure (Left (ExistingRootNotAbsolute path))
    | otherwise = do
        statusResult <- try (PosixFiles.getFileStatus path)
            :: IO (Either IOException PosixFiles.FileStatus)
        case statusResult of
            Left err
                | isDoesNotExistError err ->
                    pure (Left (ExistingRootUnavailable path))
                | otherwise ->
                    pure
                        (Left
                            (ExistingRootInspectionFailed
                                path
                                (Text.pack (displayException err))))
            Right status
                | not (PosixFiles.isRegularFile status) -> do
                    canonicalized <-
                        canonicalize ExistingRootCanonicalizationFailed path
                    pure
                        (canonicalized >>= \canonical ->
                            Left (ExistingRootNotRegular path canonical))
                | otherwise ->
                    fmap (\canonical -> ExistingRoot canonical path) <$>
                        canonicalize ExistingRootCanonicalizationFailed path

-- | Validate and canonicalize an existing source path without assigning it
-- to a source mount.
canonicalizeExistingSourcePath
    :: FilePath
    -> IO (Either SourceError CanonicalPath)
canonicalizeExistingSourcePath path =
    fmap extract <$> existingRoot path
  where
    extract = \case
        ExistingRoot canonical _spelling ->
            canonical
        SearchedRoot{} ->
            impossible
                "canonicalizeExistingSourcePath produced a searched root"

-- | The user-facing spelling retained only for diagnostics.
rootRequestSpelling :: RootRequest -> FilePath
rootRequestSpelling = \case
    SearchedRoot path ->
        safeRelativePathFilePath path
    ExistingRoot _canonical spelling ->
        spelling


data ResolvedSource = ResolvedSource
    !CanonicalPath
    !SourceMountId
    !CanonicalPath
    !SafeRelativePath
    deriving stock (Show, Eq, Ord)

instance NFData ResolvedSource where
    rnf (ResolvedSource path mount root relative) =
        rnf path `seq` rnf mount `seq` rnf root `seq` rnf relative

resolvedSourceCanonicalPath :: ResolvedSource -> CanonicalPath
resolvedSourceCanonicalPath
        (ResolvedSource path _mount _mountRoot _relative) =
    path

resolvedSourceMount :: ResolvedSource -> SourceMountId
resolvedSourceMount
        (ResolvedSource _path mount _mountRoot _relative) =
    mount

-- | Canonical root selected for the source's durable namespace.
resolvedSourceMountRoot :: ResolvedSource -> CanonicalPath
resolvedSourceMountRoot
        (ResolvedSource _path _mount mountRoot _relative) =
    mountRoot

resolvedSourceRelativePath :: ResolvedSource -> SafeRelativePath
resolvedSourceRelativePath
        (ResolvedSource _path _mount _mountRoot relative) =
    relative

-- | Stable mount-relative spelling for locations in one resolved workspace.
-- This is derived from the selected source rather than its request or import
-- spelling.
resolvedSourceLocationPath :: ResolvedSource -> FilePath
resolvedSourceLocationPath =
    safeRelativePathFilePath . resolvedSourceRelativePath


-- | The selected mount-relative address retained by the logical source graph.
--
-- This is an invocation-local physical address, not a module or theorem
-- identity.
data ResolvedSourceAddress = ResolvedSourceAddress
    !SourceMountId
    !CanonicalPath
    !SafeRelativePath
    deriving stock (Show, Eq, Ord)

instance NFData ResolvedSourceAddress where
    rnf (ResolvedSourceAddress mount root relative) =
        rnf mount `seq` rnf root `seq` rnf relative

resolvedSourceAddress :: ResolvedSource -> ResolvedSourceAddress
resolvedSourceAddress source =
    ResolvedSourceAddress
        (resolvedSourceMount source)
        (resolvedSourceMountRoot source)
        (resolvedSourceRelativePath source)

sourceAddressMount :: ResolvedSourceAddress -> SourceMountId
sourceAddressMount
        (ResolvedSourceAddress mount _mountRoot _relative) =
    mount

-- | Canonical root carried from source selection.
sourceAddressRoot :: ResolvedSourceAddress -> CanonicalPath
sourceAddressRoot
        (ResolvedSourceAddress _mount mountRoot _relative) =
    mountRoot

sourceAddressRelativePath :: ResolvedSourceAddress -> SafeRelativePath
sourceAddressRelativePath
        (ResolvedSourceAddress _mount _mountRoot relative) =
    relative


data LoadedSource = LoadedSource
    !ResolvedSource
    !ByteString.ByteString
    !Text
    deriving stock (Show, Eq)

instance NFData LoadedSource where
    rnf (LoadedSource source bytes text) =
        rnf source `seq` rnf bytes `seq` rnf text

loadedSource :: LoadedSource -> ResolvedSource
loadedSource (LoadedSource source _bytes _text) = source

loadedBytes :: LoadedSource -> ByteString.ByteString
loadedBytes (LoadedSource _source bytes _text) = bytes

loadedText :: LoadedSource -> Text
loadedText (LoadedSource _source _bytes text) = text

loadedByteCount :: LoadedSource -> Word64
loadedByteCount =
    fromIntegral . ByteString.length . loadedBytes


data ImportRef = ImportRef
    !SafeRelativePath
    !Location
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

importRef :: Location -> FilePath -> Either RelativePathError ImportRef
importRef location path =
    flip ImportRef location <$> safeRelativePath path

importPath :: ImportRef -> SafeRelativePath
importPath (ImportRef path _location) = path

importLocation :: ImportRef -> Location
importLocation (ImportRef _path location) = location


data SourceCandidate = SourceCandidate
    !SourceMountId
    !FilePath
    deriving stock (Show, Eq)

sourceCandidateMount :: SourceCandidate -> SourceMountId
sourceCandidateMount (SourceCandidate ident _path) = ident

sourceCandidatePath :: SourceCandidate -> FilePath
sourceCandidatePath (SourceCandidate _ident path) = path

-- | Candidate paths in configured precedence order.
sourceCandidates :: SourceMounts -> SafeRelativePath -> [SourceCandidate]
sourceCandidates mounts relative =
    [ SourceCandidate
        (sourceMountIdentifier mount)
        (canonicalPathFilePath (sourceMountRoot mount)
            Posix.</> safeRelativePathFilePath relative)
    | mount <- sourceMountList mounts
    ]


data SourceLookup
    = SearchedRootLookup !SafeRelativePath
    | ImportedSourceLookup !ResolvedSource !ImportRef
    deriving stock (Show, Eq)

data SourceCycleStep = SourceCycleStep
    !ResolvedSource
    !ImportRef
    !ResolvedSource
    deriving stock (Show, Eq)

sourceCycleStep
    :: ResolvedSource
    -> ImportRef
    -> ResolvedSource
    -> SourceCycleStep
sourceCycleStep = SourceCycleStep

cycleImporter :: SourceCycleStep -> ResolvedSource
cycleImporter (SourceCycleStep importer _reference _imported) = importer

cycleImport :: SourceCycleStep -> ImportRef
cycleImport (SourceCycleStep _importer reference _imported) = reference

cycleImported :: SourceCycleStep -> ResolvedSource
cycleImported (SourceCycleStep _importer _reference imported) = imported


data SourceError
    = EmptySourceMountTable
    | DuplicateSourceMountId !SourceMountId
    | SourceMountCanonicalizationFailed !SourceMountId !FilePath !Text
    | SourceMountInspectionFailed !SourceMountId !FilePath !Text
    | CanonicalPathContainsNonUnicodeScalar !FilePath
    | SourceMountNotDirectory
        !SourceMountId
        !FilePath
        !CanonicalPath
    | DuplicateCanonicalMountRoot
        !CanonicalPath
        !SourceMountId
        !SourceMountId
    | InvalidSearchedRoot !FilePath !RelativePathError
    | ExistingRootNotAbsolute !FilePath
    | ExistingRootUnavailable !FilePath
    | ExistingRootCanonicalizationFailed !FilePath !Text
    | ExistingRootInspectionFailed !FilePath !Text
    | ExistingRootNotRegular !FilePath !CanonicalPath
    | RootOutsideConfiguredMount !FilePath !CanonicalPath
    | InvalidAttributedRelativePath
        !CanonicalPath
        !CanonicalPath
        !RelativePathError
    | SourceNotFound !SourceLookup ![SourceCandidate]
    | SelectedSourceCanonicalizationFailed
        !SourceLookup
        !FilePath
        !Text
    | SelectedSourceInspectionFailed
        !SourceLookup
        !FilePath
        !Text
    | SelectedSourceNotRegular
        !SourceLookup
        !FilePath
        !CanonicalPath
    | InvalidImportPath
        !ResolvedSource
        !Location
        !FilePath
        !RelativePathError
    | SourceReadFailed !ResolvedSource !Text
    | SourceReadTargetNotRegular !ResolvedSource
    | SourceDecodeError !ResolvedSource !Int
    | SourceImportDiscoveryFailed !ResolvedSource !Text
    | SourceGraphScanningInvariantViolation
        !ResolvedSource
        !Text
    | SourceImportCycle !(NonEmpty SourceCycleStep)
    | ReservedPreludeSelectedAsOrdinarySource !ResolvedSource
    | SourceGraphInvariantViolation !Text
    deriving stock (Show, Eq)

instance Exception SourceError

renderSourceError :: SourceError -> Text
renderSourceError = \case
    EmptySourceMountTable ->
        "no source mounts are configured"
    DuplicateSourceMountId mount ->
        "source mount " <> quoteText (sourceMountIdText mount)
            <> " is configured more than once"
    SourceMountCanonicalizationFailed mount path reason ->
        "could not resolve source mount "
            <> quoteText (sourceMountIdText mount)
            <> " at " <> quotePath path <> ": " <> reason
    SourceMountInspectionFailed mount path reason ->
        "could not inspect source mount "
            <> quoteText (sourceMountIdText mount)
            <> " at " <> quotePath path <> ": " <> reason
    CanonicalPathContainsNonUnicodeScalar path ->
        "canonical source path contains a non-Unicode scalar: "
            <> quotePath path
    SourceMountNotDirectory mount spelling canonical ->
        "source mount " <> quoteText (sourceMountIdText mount)
            <> " is not a directory: " <> quotePath spelling
            <> " (resolved to "
            <> quotePath (canonicalPathFilePath canonical) <> ")"
    DuplicateCanonicalMountRoot canonical firstMount secondMount ->
        "source mounts " <> quoteText (sourceMountIdText firstMount)
            <> " and " <> quoteText (sourceMountIdText secondMount)
            <> " resolve to the same directory "
            <> quotePath (canonicalPathFilePath canonical)
    InvalidSearchedRoot path problem ->
        "invalid searched source " <> quotePath path <> ": "
            <> renderRelativePathError problem
    ExistingRootNotAbsolute path ->
        "exact source path must be absolute: " <> quotePath path
    ExistingRootUnavailable path ->
        "exact source does not exist: " <> quotePath path
    ExistingRootCanonicalizationFailed path reason ->
        "could not resolve exact source " <> quotePath path
            <> ": " <> reason
    ExistingRootInspectionFailed path reason ->
        "could not inspect exact source " <> quotePath path
            <> ": " <> reason
    ExistingRootNotRegular spelling canonical ->
        "exact source is not a regular file: " <> quotePath spelling
            <> " (resolved to "
            <> quotePath (canonicalPathFilePath canonical) <> ")"
    RootOutsideConfiguredMount spelling canonical ->
        "exact source " <> quotePath spelling
            <> " resolves outside every configured mount: "
            <> quotePath (canonicalPathFilePath canonical)
    InvalidAttributedRelativePath canonical root problem ->
        "source " <> quotePath (canonicalPathFilePath canonical)
            <> " cannot be represented relative to mount "
            <> quotePath (canonicalPathFilePath root) <> ": "
            <> renderRelativePathError problem
    SourceNotFound lookup candidates ->
        "source not found for " <> renderSourceLookup lookup
            <> renderCandidates candidates
    SelectedSourceCanonicalizationFailed lookup path reason ->
        "could not resolve selected source " <> quotePath path
            <> " for " <> renderSourceLookup lookup <> ": " <> reason
    SelectedSourceInspectionFailed lookup path reason ->
        "could not inspect selected source " <> quotePath path
            <> " for " <> renderSourceLookup lookup <> ": " <> reason
    SelectedSourceNotRegular lookup path canonical ->
        "selected source for " <> renderSourceLookup lookup
            <> " is not a regular file: " <> quotePath path
            <> " (resolved to "
            <> quotePath (canonicalPathFilePath canonical) <> ")"
    InvalidImportPath importer location path problem ->
        sourceLabel importer <> " at " <> locationToText location
            <> " imports invalid path " <> quotePath path <> ": "
            <> renderRelativePathError problem
    SourceReadFailed source reason ->
        "could not read " <> sourceLabel source <> ": " <> reason
    SourceReadTargetNotRegular source ->
        sourceLabel source <> " is no longer a regular file"
    SourceDecodeError source offset ->
        sourceLabel source <> " contains malformed UTF-8 at byte offset "
            <> Text.pack (show offset)
    SourceImportDiscoveryFailed source reason ->
        "could not discover imports in " <> sourceLabel source
            <> ": " <> reason
    SourceGraphScanningInvariantViolation source reason ->
        "source scanning invariant failed in "
            <> sourceLabel source <> ": " <> reason
    SourceImportCycle steps ->
        "source import cycle: "
            <> Text.intercalate " -> "
                [ sourceLabel (cycleImporter step)
                    <> " at "
                    <> locationToText
                        (importLocation (cycleImport step))
                    <> " imports "
                    <> sourceLabel (cycleImported step)
                | step <- toList steps
                ]
    ReservedPreludeSelectedAsOrdinarySource source ->
        "the prelude is loaded implicitly and cannot be used "
            <> "as ordinary source "
            <> quotePath (resolvedSourceLocationPath source)
    SourceGraphInvariantViolation reason ->
        "source graph invariant failed: " <> reason

renderSourceLookup :: SourceLookup -> Text
renderSourceLookup = \case
    SearchedRootLookup relative ->
        "root " <> quotePath (safeRelativePathFilePath relative)
    ImportedSourceLookup importer reference ->
        "import " <> quotePath
            (safeRelativePathFilePath (importPath reference))
            <> " from " <> sourceLabel importer
            <> " at " <> locationToText (importLocation reference)

renderCandidates :: [SourceCandidate] -> Text
renderCandidates = \case
    [] ->
        " (no candidate paths)"
    candidates ->
        "; searched "
            <> Text.intercalate ", "
                [ quoteText (sourceMountIdText (sourceCandidateMount candidate))
                    <> ":" <> quotePath (sourceCandidatePath candidate)
                | candidate <- candidates
                ]

renderRelativePathError :: RelativePathError -> Text
renderRelativePathError = \case
    EmptyRelativePath -> "the path is empty"
    AbsoluteRelativePath -> "the path is absolute"
    EmptyPathComponent -> "the path contains an empty component"
    CurrentDirectoryComponent -> "the path contains a current-directory component"
    ParentDirectoryComponent -> "the path contains a parent-directory component"
    NullPathCharacter -> "the path contains a null character"
    NonUnicodeScalarPathCharacter ->
        "the path contains a non-Unicode scalar"

sourceLabel :: ResolvedSource -> Text
sourceLabel source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack
            (safeRelativePathFilePath
                (resolvedSourceRelativePath source))

quotePath :: FilePath -> Text
quotePath = Text.pack . show

quoteText :: Text -> Text
quoteText = Text.pack . show


-- | Canonicalize and validate the complete mount table before source
-- resolution.  Missing mount directories are permitted: they simply cannot
-- supply a candidate in this invocation.
prepareSourceMounts
    :: [(SourceMountId, FilePath)]
    -> IO (Either SourceError SourceMounts)
prepareSourceMounts specifications =
    case specifications of
        [] ->
            pure (Left EmptySourceMountTable)
        _ ->
            case firstDuplicate (fst <$> specifications) of
                Just duplicateId ->
                    pure (Left (DuplicateSourceMountId duplicateId))
                Nothing -> do
                    canonicalized <- traverse canonicalizeMount specifications
                    pure do
                        mounts <- sequence canonicalized
                        rejectDuplicateRoots mounts
                        case mounts of
                            [] ->
                                Left EmptySourceMountTable
                            firstMount : rest ->
                                Right (SourceMounts (firstMount :| rest))

canonicalizeMount
    :: (SourceMountId, FilePath)
    -> IO (Either SourceError SourceMount)
canonicalizeMount (ident, path) = do
    canonicalized <- canonicalize
        (\raw message -> SourceMountCanonicalizationFailed ident raw message)
        path
    case canonicalized of
        Left err ->
            pure (Left err)
        Right root ->
            inspectMount ident path root

inspectMount
    :: SourceMountId
    -> FilePath
    -> CanonicalPath
    -> IO (Either SourceError SourceMount)
inspectMount ident spelling root = do
    result <- try (PosixFiles.getFileStatus (canonicalPathFilePath root))
        :: IO (Either IOException PosixFiles.FileStatus)
    pure case result of
        Left err
            | isDoesNotExistError err ->
                Right (SourceMount ident root)
            | otherwise ->
                Left
                    (SourceMountInspectionFailed
                        ident
                        spelling
                        (Text.pack (displayException err)))
        Right status
            | PosixFiles.isDirectory status ->
                Right (SourceMount ident root)
            | otherwise ->
                Left (SourceMountNotDirectory ident spelling root)

canonicalize
    :: (FilePath -> Text -> SourceError)
    -> FilePath
    -> IO (Either SourceError CanonicalPath)
canonicalize makeError path = do
    result <- try (Directory.canonicalizePath path)
        :: IO (Either IOException FilePath)
    pure case result of
        Left err ->
            Left (makeError path (Text.pack (displayException err)))
        Right canonical ->
            if all isUnicodeScalar canonical
                then Right (CanonicalPath canonical)
                else Left
                    (CanonicalPathContainsNonUnicodeScalar canonical)

isUnicodeScalar :: Char -> Bool
isUnicodeScalar character =
    let codePoint = ord character
    in codePoint < 0xd800
        || codePoint > 0xdfff

rejectDuplicateRoots :: [SourceMount] -> Either SourceError ()
rejectDuplicateRoots = go Map.empty
  where
    go _seen [] =
        Right ()
    go seen (mount : mounts) =
        case Map.lookup root seen of
            Just earlierId ->
                Left (DuplicateCanonicalMountRoot root earlierId ident)
            Nothing ->
                go (Map.insert root ident seen) mounts
      where
        root = sourceMountRoot mount
        ident = sourceMountIdentifier mount


-- This policy is kept here, beside the types that establish its invariants.
-- Loading uses it after canonicalizing an actual selected source.
attributeCanonicalSource
    :: SourceMounts
    -> CanonicalPath
    -> Either SourceError ResolvedSource
attributeCanonicalSource mounts sourcePath =
    case containingMounts of
        [] ->
            Left
                (RootOutsideConfiguredMount
                    (canonicalPathFilePath sourcePath)
                    sourcePath)
        firstMount : otherMounts -> do
            let owner = foldl' chooseMoreSpecific firstMount otherMounts
                ownerRoot = sourceMountRoot owner
                ownerId = sourceMountIdentifier owner
            relative <- first
                (InvalidAttributedRelativePath ownerRoot sourcePath)
                (safeRelativePath
                    (Posix.makeRelative
                        (canonicalPathFilePath ownerRoot)
                        (canonicalPathFilePath sourcePath)))
            Right
                (ResolvedSource
                    sourcePath
                    ownerId
                    ownerRoot
                    relative)
  where
    containingMounts =
        List.filter
            (\mount ->
                pathComponents (sourceMountRoot mount)
                    `List.isPrefixOf` pathComponents sourcePath)
            (sourceMountList mounts)

    chooseMoreSpecific left right
        | pathDepth (sourceMountRoot right) > pathDepth (sourceMountRoot left) =
            right
        | otherwise =
            left

pathComponents :: CanonicalPath -> [FilePath]
pathComponents =
    Posix.splitDirectories
        . Posix.dropTrailingPathSeparator
        . canonicalPathFilePath

pathDepth :: CanonicalPath -> Int
pathDepth = length . pathComponents


resolveAndLoadRoot
    :: SourceMounts
    -> RootRequest
    -> IO (Either SourceError LoadedSource)
resolveAndLoadRoot mounts request =
    resolveAndLoad (resolveRoot mounts request)

resolveAndLoadImport
    :: SourceMounts
    -> ResolvedSource
    -> ImportRef
    -> IO (Either SourceError LoadedSource)
resolveAndLoadImport mounts importer reference =
    resolveAndLoad (resolveImport mounts importer reference)

resolveAndLoad
    :: IO (Either SourceError ResolvedSource)
    -> IO (Either SourceError LoadedSource)
resolveAndLoad resolve = do
    resolved <- resolve
    case resolved of
        Left err ->
            pure (Left err)
        Right source ->
            loadResolvedSource source

resolveRoot
    :: SourceMounts
    -> RootRequest
    -> IO (Either SourceError ResolvedSource)
resolveRoot mounts = \case
    SearchedRoot path ->
        resolveSearched mounts (SearchedRootLookup path) path
    ExistingRoot canonical spelling ->
        pure (attributeSelectedSource spelling mounts canonical)

resolveImport
    :: SourceMounts
    -> ResolvedSource
    -> ImportRef
    -> IO (Either SourceError ResolvedSource)
resolveImport mounts importer reference =
    resolveSearched
        mounts
        (ImportedSourceLookup importer reference)
        (importPath reference)

resolveSearched
    :: SourceMounts
    -> SourceLookup
    -> SafeRelativePath
    -> IO (Either SourceError ResolvedSource)
resolveSearched mounts lookupKind relative =
    choose (sourceCandidates mounts relative)
  where
    candidates = sourceCandidates mounts relative

    choose [] =
        pure (Left (SourceNotFound lookupKind candidates))
    choose (candidate : rest) = do
        let path = sourceCandidatePath candidate
        statusResult <- try (PosixFiles.getSymbolicLinkStatus path)
            :: IO (Either IOException PosixFiles.FileStatus)
        case statusResult of
            Left err
                | isDoesNotExistError err ->
                    choose rest
                | otherwise ->
                    pure
                        (Left
                            (SelectedSourceInspectionFailed
                                lookupKind
                                path
                                (Text.pack (displayException err))))
            Right _status ->
                resolveCandidate mounts lookupKind candidate

resolveCandidate
    :: SourceMounts
    -> SourceLookup
    -> SourceCandidate
    -> IO (Either SourceError ResolvedSource)
resolveCandidate mounts lookupKind candidate = do
    canonicalized <- canonicalize
        (\path message ->
            SelectedSourceCanonicalizationFailed lookupKind path message)
        (sourceCandidatePath candidate)
    case canonicalized of
        Left err ->
            pure (Left err)
        Right canonical -> do
            statusResult <- try
                (PosixFiles.getFileStatus
                    (canonicalPathFilePath canonical))
                :: IO (Either IOException PosixFiles.FileStatus)
            pure case statusResult of
                Left err ->
                    Left
                        (SelectedSourceInspectionFailed
                            lookupKind
                            (sourceCandidatePath candidate)
                            (Text.pack (displayException err)))
                Right status
                    | not (PosixFiles.isRegularFile status) ->
                        Left
                            (SelectedSourceNotRegular
                                lookupKind
                                (sourceCandidatePath candidate)
                                canonical)
                    | otherwise ->
                        attributeSelectedSource
                            (sourceCandidatePath candidate)
                            mounts
                            canonical

attributeSelectedSource
    :: FilePath
    -> SourceMounts
    -> CanonicalPath
    -> Either SourceError ResolvedSource
attributeSelectedSource spelling mounts canonical =
    first retainSpelling (attributeCanonicalSource mounts canonical)
  where
    retainSpelling = \case
        RootOutsideConfiguredMount _defaultSpelling outside ->
            RootOutsideConfiguredMount spelling outside
        err ->
            err

loadResolvedSource :: ResolvedSource -> IO (Either SourceError LoadedSource)
loadResolvedSource source = do
    let path =
            canonicalPathFilePath (resolvedSourceCanonicalPath source)
    statusResult <- try (PosixFiles.getFileStatus path)
        :: IO (Either IOException PosixFiles.FileStatus)
    case statusResult of
        Left err ->
            pure
                (Left
                    (SourceReadFailed
                        source
                        (Text.pack (displayException err))))
        Right status
            | not (PosixFiles.isRegularFile status) ->
                pure (Left (SourceReadTargetNotRegular source))
            | otherwise -> do
                bytesResult <- try (ByteString.readFile path)
                    :: IO (Either IOException ByteString.ByteString)
                pure case bytesResult of
                    Left err ->
                        Left
                            (SourceReadFailed
                                source
                                (Text.pack (displayException err)))
                    Right bytes ->
                        case Encoding.decodeUtf8' bytes of
                            Left _ ->
                                let (validPrefixLength, _state) =
                                        Encoding.validateUtf8Chunk bytes
                                in
                                    Left
                                        (SourceDecodeError
                                            source
                                            validPrefixLength)
                            Right text ->
                                Right
                                    (LoadedSource
                                        source
                                        bytes
                                        text)
