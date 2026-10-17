{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Connection-owned access to the disposable SQLite store.
module Felix.Store
    ( Store
    , storeTheoryId
    , StoreCheck
    , newStoreCheck
    , StoreSelection(..)
    , StorePlan
    , storePlanPersistentPath
    , StorePath
    , storePathFilePath
    , storeLockPath
    , storeRollbackJournalPath
    , storeWriteAheadLogPath
    , storeSharedMemoryPath
    , StorePlanningError(..)
    , renderStorePlanningError
    , planStore
    , StoreLease
    , storeLeasePath
    , StoreLeaseError(..)
    , renderStoreLeaseError
    , withStoreLease
    , refreshStore
    , StoreLifecycleError(..)
    , renderStoreLifecycleError
    , withOpenStore
    , StoreStartup(..)
    , StoreCompatibility(..)
    , currentStoreCompatibility
    , StoreIncompatibility(..)
    , renderStoreIncompatibility
    , StoreOpenError(..)
    , renderStoreOpenError
    , StoreRelation(..)
    , StoreFailure(..)
    , renderStoreFailure
    , maximumStoreBlobBytes
    , checkStoreBlobByteCount
    , openStore
    , closeStore
    , loadProofValidation
    , loadDeclarationValidation
    , loadParsedArtefact
    , writeParsedArtefact
    , CachedModuleCandidate
    , cachedCandidateSyntax
    , cachedCandidateSemantic
    , cachedCandidateObjects
    , cachedCandidatePropositions
    , cachedCandidateCertificates
    , loadCachedModuleCandidate
    , writePendingModulePrefix
    , writeSealedModule
    , StoreMemoVisits(..)
    , storeCheckMemoVisits
    ) where

import Base
import Felix.Checking.Authority (ValidationCertificate)
import Felix.Checking.Core
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Identity
import Felix.Checking.Materialization qualified as Materialization
import Felix.Checking.Semantic
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Module (ModuleName)
import Felix.Parsed.Identity qualified as Parsed
import Felix.Parsed.Payload qualified as ParsedPayload
import Felix.Report.Location (SourceDescriptor)
import Felix.Syntax.Interface qualified as Syntax

import Control.Concurrent.MVar
    ( MVar
    , newMVar
    , withMVar
    )
import Control.Exception qualified as Exception
import Control.Monad (foldM, unless, when)
import Control.Monad.Except qualified as Except
import Data.Maybe (catMaybes)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Int (Int64)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word32)
import Data.IORef qualified as IORef
import Database.SQLite.Simple qualified as SQLite
import Database.SQLite.Simple.FromRow (RowParser, field)
import Database.SQLite.Simple.Types
    ( Only(..)
    , Query(..)
    )
import System.Directory qualified as Directory
import System.FileLock qualified as FileLock
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import System.Posix.Files qualified as PosixFiles
import UnliftIO.Exception qualified as UnliftIO




data Store = Store
    !FilePath
    !TheoryId
    !SQLite.Connection
    !(MVar ())

storeTheoryId :: Store -> TheoryId
storeTheoryId (Store _path theory _connection _gate) = theory

-- | Run one complete operation against the connection-owned serialization
-- gate.  Callers hold this only around SQLite and check-memo work, never
-- around parsing, checking, scheduling, or prover execution.
withStoreOperation :: Store -> IO value -> IO value
withStoreOperation (Store _path _theory _connection gate) action =
    withMVar gate (const action)

-- | Decoded rows associated with one exact requested module root. This
-- candidate grants no semantic importability; Declaration admits it locally.
data CachedModuleCandidate = CachedModuleCandidate
    !Syntax.ModuleSyntaxInterface
    !SemanticInterface
    ![AssertedObject]
    ![StoredPropositionCandidate]
    ![ValidationCertificate]

cachedCandidateSyntax :: CachedModuleCandidate -> Syntax.ModuleSyntaxInterface
cachedCandidateSyntax (CachedModuleCandidate syntax _ _ _ _) = syntax

cachedCandidateSemantic :: CachedModuleCandidate -> SemanticInterface
cachedCandidateSemantic (CachedModuleCandidate _ semantic _ _ _) = semantic

cachedCandidateObjects :: CachedModuleCandidate -> [AssertedObject]
cachedCandidateObjects (CachedModuleCandidate _ _ objects _ _) = objects

cachedCandidatePropositions :: CachedModuleCandidate -> [StoredPropositionCandidate]
cachedCandidatePropositions (CachedModuleCandidate _ _ _ propositions _) = propositions

cachedCandidateCertificates :: CachedModuleCandidate -> [ValidationCertificate]
cachedCandidateCertificates (CachedModuleCandidate _ _ _ _ certificates) = certificates

-- | Check-local decoded row memo.  It never changes a persistent row and is
-- discarded with its 'StoreCheck'.  Its ordinary IORefs are confined by the
-- owning store connection's operation gate.
data StoreMemo = StoreMemo
    { memoArtefactRows :: !(IORef.IORef (Map ModuleArtefactId ModuleArtefactResult))
    , memoSyntaxRows :: !(IORef.IORef (Map Syntax.SyntaxInterfaceId Syntax.ModuleSyntaxInterface))
    , memoSemanticRows :: !(IORef.IORef (Map SemanticInterfaceId SemanticInterface))
    , memoObjectRows :: !(IORef.IORef (Map ObjectId AssertedObject))
    , memoPropositionRows :: !(IORef.IORef (Map PropositionId StoredPropositionCandidate))
    , memoValidatedSyntax :: !(IORef.IORef (Set Syntax.SyntaxInterfaceId))
    , memoSyntaxValidationVisits :: !(IORef.IORef Int)
    }

data StoreMemoVisits = StoreMemoVisits
    { storeArtefactRowsDecoded :: !Int
    , storeSyntaxRowsDecoded :: !Int
    , storeSyntaxRowsValidated :: !Int
    , storeSemanticRowsDecoded :: !Int
    , storeObjectRowsDecoded :: !Int
    , storePropositionRowsDecoded :: !Int
    }
    deriving stock (Show, Eq)

-- | One semantic checking run against a store.  The store supplies the sole
-- connection gate; the memo is fresh for this check and cannot be paired with
-- another store by callers.  Checks created from the same store share that
-- gate but have independent memo contents.
data StoreCheck = StoreCheck
    !Store
    !StoreMemo

newStoreCheck :: Store -> IO StoreCheck
newStoreCheck store =
    StoreCheck store <$> newStoreMemo

newStoreMemo :: IO StoreMemo
newStoreMemo =
    StoreMemo <$> IORef.newIORef Map.empty <*> IORef.newIORef Map.empty
        <*> IORef.newIORef Map.empty <*> IORef.newIORef Map.empty
        <*> IORef.newIORef Map.empty <*> IORef.newIORef Set.empty
        <*> IORef.newIORef 0

storeCheckMemoVisits :: StoreCheck -> IO StoreMemoVisits
storeCheckMemoVisits (StoreCheck store memo) =
    withStoreOperation store (storeMemoVisits memo)

storeMemoVisits :: StoreMemo -> IO StoreMemoVisits
storeMemoVisits memo =
    StoreMemoVisits
        <$> (Map.size <$> IORef.readIORef (memoArtefactRows memo))
        <*> (Map.size <$> IORef.readIORef (memoSyntaxRows memo))
        <*> IORef.readIORef (memoSyntaxValidationVisits memo)
        <*> (Map.size <$> IORef.readIORef (memoSemanticRows memo))
        <*> (Map.size <$> IORef.readIORef (memoObjectRows memo))
        <*> (Map.size <$> IORef.readIORef (memoPropositionRows memo))


data StoreSelection
    = DefaultStore
    | ExplicitStore !FilePath
    | FreshTemporaryStore
    deriving stock (Show, Eq)

data StorePlan
    = DefaultStorePlan !StorePath
    | ExplicitStorePlan !StorePath
    | FreshStorePlan
    deriving stock (Show, Eq)

storePlanPersistentPath :: StorePlan -> Maybe StorePath
storePlanPersistentPath = \case
    DefaultStorePlan path -> Just path
    ExplicitStorePlan path -> Just path
    FreshStorePlan -> Nothing

newtype StorePath = StorePath FilePath
    deriving stock (Show, Eq, Ord)

storePathFilePath :: StorePath -> FilePath
storePathFilePath (StorePath path) =
    path

storeLockPath :: StorePath -> FilePath
storeLockPath storePath =
    storePathFilePath storePath <> ".lock"

storeRollbackJournalPath :: StorePath -> FilePath
storeRollbackJournalPath storePath =
    storePathFilePath storePath <> "-journal"

storeWriteAheadLogPath :: StorePath -> FilePath
storeWriteAheadLogPath storePath =
    storePathFilePath storePath <> "-wal"

storeSharedMemoryPath :: StorePath -> FilePath
storeSharedMemoryPath storePath =
    storePathFilePath storePath <> "-shm"

data StorePlanningError
    = StorePathResolutionFailed !FilePath !Text
    | ExplicitStoreParentMissing !FilePath
    | ExplicitStoreParentNotDirectory !FilePath
    deriving stock (Show, Eq)

renderStorePlanningError :: StorePlanningError -> Text
renderStorePlanningError = \case
    StorePathResolutionFailed path reason ->
        "could not resolve store path " <> quotePath path <> ": " <> reason
    ExplicitStoreParentMissing parent ->
        "the parent of --store does not exist: " <> quotePath parent
    ExplicitStoreParentNotDirectory parent ->
        "the parent of --store is not a directory: " <> quotePath parent

data StoreLease = PersistentStoreLease
    !StorePath
    !FileLock.FileLock
    | FreshStoreLease
        !StorePath

storeLeasePath :: StoreLease -> StorePath
storeLeasePath = \case
    PersistentStoreLease path _lock -> path
    FreshStoreLease path -> path

data StoreLeaseError
    = StoreLeaseParentCreationFailed !FilePath !Text
    | StoreLeaseContended !StorePath
    | StoreLeaseAcquisitionFailed !StorePath !Text
    deriving stock (Show, Eq)

renderStoreLeaseError :: StoreLeaseError -> Text
renderStoreLeaseError = \case
    StoreLeaseParentCreationFailed parent reason ->
        "could not create default store directory " <> quotePath parent
            <> ": " <> reason
    StoreLeaseContended path ->
        "another Felix process owns the selected store "
            <> quotePath (storePathFilePath path)
    StoreLeaseAcquisitionFailed path reason ->
        "could not acquire the lock for the selected store "
            <> quotePath (storePathFilePath path) <> ": " <> reason

data StoreLifecycleError
    = StoreLifecycleOpenFailed !StoreOpenError
    | StoreRefreshFailed !StoreFailure
    | StoreCloseFailed !StoreFailure
    deriving stock (Show, Eq)

renderStoreLifecycleError :: StoreLifecycleError -> Text
renderStoreLifecycleError = \case
    StoreLifecycleOpenFailed failure ->
        renderStoreOpenError failure
    StoreRefreshFailed failure ->
        "could not refresh the selected store: "
            <> renderStoreFailure failure
    StoreCloseFailed failure ->
        "could not close the selected store: " <> renderStoreFailure failure

data StoreStartup
    = InitializedNewStore
    | OpenedCurrentStore
    deriving stock (Show, Eq)


planStore
    :: StoreSelection
    -> IO (Either StorePlanningError StorePlan)
planStore = \case
    DefaultStore -> do
        resolved <- trySynchronous do
            cacheDirectory <-
                Directory.getXdgDirectory
                    Directory.XdgCache
                    "felix"
            normalizeAbsolutePath
                (cacheDirectory Posix.</> "store.sqlite")
        pure
            (case resolved of
                Left failure ->
                    Left
                        (StorePathResolutionFailed
                            "felix/store.sqlite"
                            (exceptionText failure))
                Right path ->
                    Right
                        (DefaultStorePlan
                            (StorePath path)))
    ExplicitStore requested -> do
        resolved <- trySynchronous
            (normalizeAbsolutePath requested)
        case resolved of
            Left failure ->
                pure
                    (Left
                        (StorePathResolutionFailed
                            requested
                            (exceptionText failure)))
            Right path -> do
                let parent = Posix.takeDirectory path
                inspected <- trySynchronous do
                    exists <- Directory.doesPathExist parent
                    directory <- Directory.doesDirectoryExist parent
                    pure (exists, directory)
                pure
                    (case inspected of
                        Left failure ->
                            Left
                                (StorePathResolutionFailed
                                    parent
                                    (exceptionText failure))
                        Right (False, _isDirectory) ->
                            Left
                                (ExplicitStoreParentMissing parent)
                        Right (True, False) ->
                            Left
                                (ExplicitStoreParentNotDirectory parent)
                        Right (True, True) ->
                            Right
                                (ExplicitStorePlan
                                    (StorePath path)))
    FreshTemporaryStore ->
        pure (Right FreshStorePlan)

withStoreLease
    :: StorePlan
    -> (StoreLease -> IO value)
    -> IO (Either StoreLeaseError value)
withStoreLease plan action =
    case plan of
        DefaultStorePlan path ->
            withPersistentStoreLease plan path action
        ExplicitStorePlan path ->
            withPersistentStoreLease plan path action
        FreshStorePlan ->
            Right
                <$> Temp.withSystemTempDirectory
                    "felix-store"
                    (\directory -> do
                        path <- normalizeAbsolutePath
                            (directory Posix.</> "store.sqlite")
                        action
                            (FreshStoreLease
                                (StorePath path)))

withPersistentStoreLease
    :: StorePlan
    -> StorePath
    -> (StoreLease -> IO value)
    -> IO (Either StoreLeaseError value)
withPersistentStoreLease plan path action = do
    prepared <- prepareStoreParent plan path
    case prepared of
        Left failure ->
            pure (Left failure)
        Right () ->
            Exception.mask \restore -> do
                acquired <- trySynchronous
                    (FileLock.tryLockFile
                        (storeLockPath path)
                        FileLock.Exclusive)
                case acquired of
                    Left failure ->
                        pure
                            (Left
                                (StoreLeaseAcquisitionFailed
                                    path
                                    (exceptionText failure)))
                    Right Nothing ->
                        pure (Left (StoreLeaseContended path))
                    Right (Just lock) ->
                        Exception.finally
                            (Right
                                <$> restore
                                    (action
                                        (PersistentStoreLease
                                            path lock)))
                            (FileLock.unlockFile lock)

-- | Discard a selected persistent store after leasing it and before opening
-- SQLite. Symbolic links are removed as entries rather than followed, and the
-- persistent lock sidecar remains in place.
refreshStore
    :: StoreLease
    -> IO (Either StoreLifecycleError ())
refreshStore = \case
    FreshStoreLease _path ->
        pure (Right ())
    PersistentStoreLease path _lock ->
        Exception.mask_ do
            refreshed <- trySynchronous do
                let primary = storePathFilePath path
                exists <- pathEntryExists primary
                when exists do
                    for_
                        [ storeRollbackJournalPath path
                        , storeWriteAheadLogPath path
                        , storeSharedMemoryPath path
                        ]
                        removeFileIfPresent
                    removeFileIfPresent primary
            pure case refreshed of
                Left failure ->
                    Left
                        (StoreRefreshFailed
                            (operationFailure
                                ("remove selected store "
                                    <> quotePath
                                        (storePathFilePath path))
                                failure))
                Right () ->
                    Right ()

pathEntryExists :: FilePath -> IO Bool
pathEntryExists path =
    tryIOError (PosixFiles.getSymbolicLinkStatus path) >>= \case
        Left failure
            | isDoesNotExistError failure ->
                pure False
            | otherwise ->
                ioError failure
        Right _status ->
            pure True

removeFileIfPresent :: FilePath -> IO ()
removeFileIfPresent path =
    tryIOError (Directory.removeFile path) >>= \case
        Left failure
            | isDoesNotExistError failure ->
                pure ()
            | otherwise ->
                ioError failure
        Right () ->
            pure ()

withOpenStore
    :: StoreLease
    -> TheoryId
    -> (StoreStartup -> Store -> IO value)
    -> IO (Either StoreLifecycleError value)
withOpenStore
        lease
        theory
        action =
    let StorePath filePath = storeLeasePath lease
    in Exception.mask \restore -> do
        opened <- restore (openStore filePath theory)
        case opened of
            Left failure ->
                pure
                    (Left
                        (StoreLifecycleOpenFailed failure))
            Right (startup, store) -> do
                result <- Exception.try
                    (restore (action startup store))
                closed <- trySynchronous
                    (closeStore store)
                case result of
                    Left failure ->
                        Exception.throwIO
                            (failure
                                :: Exception.SomeException)
                    Right value ->
                        pure
                            (case closed of
                                Left failure ->
                                    Left
                                        (StoreCloseFailed
                                            (operationFailure
                                                "close store"
                                                failure))
                                Right () ->
                                    Right value)

prepareStoreParent
    :: StorePlan
    -> StorePath
    -> IO (Either StoreLeaseError ())
prepareStoreParent plan (StorePath path) =
    case plan of
        DefaultStorePlan _ -> do
            let parent = Posix.takeDirectory path
            created <- trySynchronous
                (Directory.createDirectoryIfMissing
                    True
                    parent)
            pure
                (case created of
                    Left failure ->
                        Left
                            (StoreLeaseParentCreationFailed
                                parent
                                (exceptionText failure))
                    Right () ->
                        Right ())
        ExplicitStorePlan _ ->
            pure (Right ())
        FreshStorePlan ->
            pure (Right ())

normalizeAbsolutePath :: FilePath -> IO FilePath
normalizeAbsolutePath path =
    Posix.normalise <$> Directory.makeAbsolute path

data StoreCompatibility = StoreCompatibility
    !CacheEpoch
    !TheoryId
    deriving stock (Show, Eq)

currentStoreCompatibility :: TheoryId -> StoreCompatibility
currentStoreCompatibility =
    StoreCompatibility currentCacheEpoch

data StoreIncompatibility
    = StoreCompatibilityMissing
    | StoreCompatibilityMalformed !Text
    | StoreCompatibilityMismatch
        !StoreCompatibility
        !StoreCompatibility
    deriving stock (Show, Eq)

renderStoreIncompatibility :: StoreIncompatibility -> Text
renderStoreIncompatibility = \case
    StoreCompatibilityMissing ->
        "compatibility metadata is missing"
    StoreCompatibilityMalformed reason ->
        "compatibility metadata is malformed: " <> reason
    StoreCompatibilityMismatch expected actual ->
        "compatibility differs: expected " <> renderCompatibility expected
            <> ", found " <> renderCompatibility actual

renderCompatibility :: StoreCompatibility -> Text
renderCompatibility (StoreCompatibility epoch theory) =
    "cache epoch " <> Text.pack (show (cacheEpochValue epoch))
        <> " and theory " <> Text.pack (show theory)

data StoreOpenError
    = IncompatibleStore !StoreIncompatibility
    | FatalStoreStartup !StoreFailure
    deriving stock (Show, Eq)

renderStoreOpenError :: StoreOpenError -> Text
renderStoreOpenError = \case
    IncompatibleStore incompatibility ->
        renderStoreIncompatibility incompatibility
    FatalStoreStartup failure ->
        renderStoreFailure failure

data StoreRelation
    = CompatibilityMetadata
    | CanonicalObjects
    | CanonicalPropositions
    | ProofValidations
    | DeclarationValidations
    | SyntaxInterfaces
    | SemanticInterfaces
    | ModuleArtefacts
    | ParsedArtefacts
    deriving stock (Show, Eq, Ord)

data StoreFailure
    = StoreOperationFailed !Text !Text
    | StoreSchemaIntegrityFailure !Text
    | StoreConfigurationFailure !Text
    | StoreBlobResourceLimitExceeded
        !StoreRelation
        !Word64
        !Word64
    | StoreRowPayloadMismatch
        !StoreRelation
        !ByteString
    | StoreRowDecodeFailure
        !StoreRelation
        !ByteString
        !CacheDecodeError
    | StoreRowResourceLimitExceeded !StoreRelation !DecoderLimitFailure
    | StoreObjectReentryFailure !ObjectReentryError
    | StoreTermReentryFailure !TermReentryError
    | StorePropositionReentryFailure !PropositionReentryError
    | StoreObjectValidationFailure !ObjectValidationError
    | StorePropositionValidationFailure !PropositionValidationError
    | StoreValidationRecordKeyMismatch !StoreRelation
    | StoreInterfaceIdMismatch !StoreRelation
    | StoreSyntaxInterfaceValidationFailure
        !Syntax.SyntaxInterfaceError
    | StoreSemanticInterfaceValidationFailure
        !SemanticInterfaceError
    | StoreModuleArtefactIdMismatch
    | StoreParsedArtefactIdMismatch
    | StoreModuleArtefactColumnsMismatch
    | StoreModuleArtefactSyntaxMismatch
        !Syntax.SyntaxInterfaceId !Syntax.SyntaxInterfaceId
    | StoreModuleArtefactOwnerMismatch !ModuleName !ModuleName
    | StoreModuleArtefactDirectMismatch
        ![SemanticInterfaceId] ![SemanticInterfaceId]
    | StoreModuleArtefactTheoryMismatch !TheoryId !TheoryId
    | StoreModulePrefixFailure !PrefixContextError
    | StoreModulePrefixMismatch
    | StoreImportedOccurrenceValidationFailure
        !Materialization.MaterializationError
    | StoreSemanticAliasTargetMissing
        !SemanticFactOccurrenceFingerprint
    | StoreSemanticAliasCollision !SemanticName
    | StoreSemanticGlobalTargetFailure
        !SemanticGlobalKey
        !SemanticGlobalTarget
        !SemanticGlobalTargetError
    | StoreFormationContractMaterializationFailure
        !GlobalBindingRef
        !FormationContractMaterializationError
    | StoreSemanticGlobalCollision
        !SemanticGlobalKey
        !SemanticGlobalTarget
        !SemanticGlobalTarget
    | StoreAssertedChildMissing
        !StoreRelation
        !ByteString
    deriving stock (Show, Eq)

renderStoreFailure :: StoreFailure -> Text
renderStoreFailure = \case
    StoreOperationFailed operation reason ->
        operation <> " failed: " <> reason
    StoreSchemaIntegrityFailure reason ->
        "current store schema is incomplete or inconsistent: " <> reason
    StoreConfigurationFailure reason ->
        "could not configure the current store: " <> reason
    StoreBlobResourceLimitExceeded relation actual limit ->
        "store blob in " <> renderStoreRelation relation
            <> " is " <> Text.pack (show actual) <> " bytes; limit is "
            <> Text.pack (show limit) <> " bytes"
    StoreRowPayloadMismatch relation _key ->
        "stored canonical payload disagrees with an equal key in "
            <> renderStoreRelation relation
    StoreRowDecodeFailure relation _key _failure ->
        "stored canonical payload is malformed in "
            <> renderStoreRelation relation
    StoreRowResourceLimitExceeded relation failure ->
        "stored payload in " <> renderStoreRelation relation
            <> " exceeds the " <> decoderResourceName (decoderLimitedResource failure)
            <> " limit (" <> Text.pack (show (decoderRequestedAmount failure))
            <> " > " <> Text.pack (show (decoderResourceLimit failure)) <> ")"
    StoreObjectReentryFailure{} ->
        "stored canonical object disagrees with its row key or store theory"
    StoreTermReentryFailure{} ->
        "stored canonical term disagrees with its root"
    StorePropositionReentryFailure{} ->
        "stored canonical proposition disagrees with its term root"
    StoreObjectValidationFailure{} ->
        "stored canonical object failed identity validation"
    StorePropositionValidationFailure{} ->
        "stored canonical proposition failed identity validation"
    StoreValidationRecordKeyMismatch relation ->
        "stored validation row has the wrong key in "
            <> renderStoreRelation relation
    StoreInterfaceIdMismatch relation ->
        "stored interface row has the wrong asserted identity in "
            <> renderStoreRelation relation
    StoreSyntaxInterfaceValidationFailure failure ->
        "supplied syntax interface failed validation: "
            <> Text.pack (show failure)
    StoreSemanticInterfaceValidationFailure failure ->
        "supplied semantic interface failed validation: "
            <> Text.pack (show failure)
    StoreModuleArtefactIdMismatch ->
        "stored module artefact row has the wrong identity"
    StoreParsedArtefactIdMismatch ->
        "parsed artefact identity disagrees with its key and payload"
    StoreModuleArtefactColumnsMismatch ->
        "stored module artefact columns disagree with its canonical payload"
    StoreModuleArtefactSyntaxMismatch{} ->
        "stored module artefact does not match the current syntax interface"
    StoreModuleArtefactOwnerMismatch{} ->
        "stored module artefact has the wrong semantic owner"
    StoreModuleArtefactDirectMismatch{} ->
        "stored module artefact has the wrong direct semantic inputs"
    StoreModuleArtefactTheoryMismatch{} ->
        "stored module artefact belongs to a different theory"
    StoreModulePrefixFailure{} ->
        "stored module artefact has an invalid initial prefix"
    StoreModulePrefixMismatch ->
        "published module prefix does not match its semantic interface"
    StoreImportedOccurrenceValidationFailure{} ->
        "stored semantic occurrence failed authority validation"
    StoreSemanticAliasTargetMissing{} ->
        "stored semantic alias targets a missing occurrence"
    StoreSemanticAliasCollision{} ->
        "stored semantic aliases conflict across the import closure"
    StoreSemanticGlobalTargetFailure{} ->
        "stored semantic global has an invalid target"
    StoreFormationContractMaterializationFailure reference failure ->
        "stored global " <> Text.pack (show reference)
            <> " has an invalid formation contract: "
            <> Text.pack (show failure)
    StoreSemanticGlobalCollision{} ->
        "stored semantic globals conflict across the import closure"
    StoreAssertedChildMissing relation _key ->
        "a module row asserts a missing child in "
            <> renderStoreRelation relation

decoderResourceName :: DecoderResource -> Text
decoderResourceName = \case
    DecoderInputBytes -> "input byte count"
    DecoderNodes -> "decoded node count"
    DecoderElements -> "container element and text character count"
    DecoderDepth -> "nesting depth"
    DecoderIntegerBytes -> "integer encoding byte count"
    DecoderByteFieldBytes -> "byte field length"
    DecoderListElements -> "list length"

renderStoreRelation :: StoreRelation -> Text
renderStoreRelation = \case
    CompatibilityMetadata -> "store_compatibility"
    CanonicalObjects -> "canonical_objects"
    CanonicalPropositions -> "canonical_propositions"
    ProofValidations -> "proof_validations"
    DeclarationValidations -> "declaration_validations"
    SyntaxInterfaces -> "syntax_interfaces"
    SemanticInterfaces -> "semantic_interfaces"
    ModuleArtefacts -> "module_artefacts"
    ParsedArtefacts -> "parsed_artefacts"

-- The full 203-module library store measured on 2026-08-24 had a largest
-- outer blob of 684,927 bytes (a parsed artefact). The 16 MiB cap is a
-- store-admissibility bound with more than 24 times that observed headroom.
maximumStoreBlobBytes :: Word64
maximumStoreBlobBytes =
    maximumDecoderInputBytes standardDecoderLimits

checkStoreBlobByteCount
    :: StoreRelation
    -> Word64
    -> Either StoreFailure ()
checkStoreBlobByteCount relation actual
    | actual > maximumStoreBlobBytes =
        Left
            (StoreBlobResourceLimitExceeded
                relation
                actual
                maximumStoreBlobBytes)
    | otherwise =
        Right ()

-- Only the payload and these fixed-width identity columns cross the SQLite
-- byte boundary. The query returns rejection metadata in the same snapshot,
-- while a rejected value itself is NULL and is never copied into Haskell.
data StoreByteColumn
    = PayloadColumn
    | TheoryIdColumn
    | SyntaxInterfaceIdColumn
    | SemanticInterfaceIdColumn
    | ParsedModuleIdColumn

storeByteColumnName :: StoreByteColumn -> Text
storeByteColumnName = \case
    PayloadColumn -> "payload"
    TheoryIdColumn -> "theory_id"
    SyntaxInterfaceIdColumn -> "syntax_interface_id"
    SemanticInterfaceIdColumn -> "semantic_interface_id"
    ParsedModuleIdColumn -> "parsed_module_id"

-- The identity codecs all declare exactly 32 bytes. Payloads have an admission
-- ceiling instead of an exact width; these policies must remain distinct.
storeByteColumnLimit :: StoreByteColumn -> Word64
storeByteColumnLimit = \case
    PayloadColumn -> maximumStoreBlobBytes
    _ -> 32

guardedColumnQuery :: StoreByteColumn -> Query
guardedColumnQuery column =
    "typeof(" <> name <> "), "
        <> "CASE typeof(" <> name <> ") WHEN 'blob' THEN length(" <> name
        <> ") ELSE NULL END, "
        <> "CASE typeof(" <> name <> ") WHEN 'blob' THEN CASE WHEN length("
        <> name <> ") " <> comparison <> limit <> " THEN " <> name
        <> " ELSE NULL END ELSE NULL END"
  where
    name = Query (storeByteColumnName column)
    limit = Query (Text.pack (show (storeByteColumnLimit column)))
    comparison = case column of
        PayloadColumn -> "<= "
        _ -> "= "

data GuardedStoreColumn = GuardedStoreColumn
    !Text !(Maybe Int64) !(Maybe ByteString)

guardedColumnRow :: RowParser GuardedStoreColumn
guardedColumnRow = GuardedStoreColumn <$> field <*> field <*> field

parsedArtefactRow :: RowParser (GuardedStoreColumn, GuardedStoreColumn)
parsedArtefactRow = (,) <$> guardedColumnRow <*> guardedColumnRow

moduleArtefactRow
    :: RowParser (GuardedStoreColumn, GuardedStoreColumn, GuardedStoreColumn)
moduleArtefactRow = (,,) <$> guardedColumnRow <*> guardedColumnRow <*> guardedColumnRow

checkedStoreColumn
    :: StoreRelation
    -> ByteString
    -> StoreByteColumn
    -> GuardedStoreColumn
    -> Either StoreFailure ByteString
checkedStoreColumn relation key column (GuardedStoreColumn storageType count payload)
    | storageType /= "blob" =
        Left (malformed ("expected BLOB, found " <> storageType))
    | otherwise = do
        byteCount <- case count of
            Just n | n >= 0 -> Right (fromIntegral n)
            _ -> Left (invariant "BLOB byte count is missing or negative")
        case column of
            PayloadColumn -> checkStoreBlobByteCount relation byteCount
            _ -> unless (byteCount == storeByteColumnLimit column)
                (Left (malformed ("expected exactly " <> Text.pack (show (storeByteColumnLimit column))
                    <> " bytes, found " <> Text.pack (show byteCount))))
        case payload of
            Just bytes
                | fromIntegral (ByteString.length bytes) == byteCount -> Right bytes
                | otherwise -> Left (invariant "returned byte count differs from query metadata")
            Nothing -> Left (invariant "admitted bytes were not returned by the query")
  where
    malformed message = StoreRowDecodeFailure relation key
        (CacheBinaryDecodeError (Text.unpack (storeByteColumnName column <> ": " <> message)))
    invariant message = StoreSchemaIntegrityFailure
        (relationName relation <> "." <> storeByteColumnName column <> ": " <> message)

quotePath :: FilePath -> Text
quotePath = Text.pack . show

newtype StoreAbort = StoreAbort StoreFailure
    deriving stock (Show)

instance Exception.Exception StoreAbort


openStore
    :: FilePath
    -> TheoryId
    -> IO
        (Either
            StoreOpenError
            (StoreStartup, Store))
openStore path theory =
    Exception.mask \restore -> do
        opened <- trySynchronous (SQLite.open path)
        case opened of
            Left failure ->
                pure
                    (Left
                        (FatalStoreStartup
                            (startupOperationFailure "open store" failure)))
            Right connection -> do
                startup <-
                    trySynchronous
                        (restore
                            (classifyAndStart connection theory))
                    `Exception.onException`
                        closeIgnoringFailure connection
                case startup of
                    Left failure -> do
                        closeIgnoringFailure connection
                        pure
                            (Left
                                (FatalStoreStartup
                                    (startupOperationFailure
                                        "start store"
                                        failure)))
                    Right (Left openError) -> do
                        closeIgnoringFailure connection
                        pure (Left openError)
                    Right (Right status) -> do
                        gate <- newMVar ()
                        pure
                            (Right
                                ( status
                                , Store path theory connection gate
                                ))

-- SQLite can itself report schema text before the guarded inventory query
-- runs. Keep that exceptional startup diagnostic bounded as well.
startupOperationFailure :: Text -> Exception.SomeException -> StoreFailure
startupOperationFailure label =
    StoreOperationFailed label . Text.pack . take 512 . Exception.displayException

closeStore :: Store -> IO ()
closeStore store@(Store _path _theory connection _gate) =
    withStoreOperation store (SQLite.close connection)

classifyAndStart
    :: SQLite.Connection
    -> TheoryId
    -> IO (Either StoreOpenError StoreStartup)
classifyAndStart connection theory = do
    -- Classification and admission observe one schema snapshot. Journal-mode
    -- configuration must happen after this short transaction has ended.
    admitted <- SQLite.withTransaction connection do
        existing <- SQLite.query_ connection
            "SELECT EXISTS (SELECT 1 FROM sqlite_master)" :: IO [Only Bool]
        case existing of
            [Only False] -> do
                initializeSchema connection theory
                first FatalStoreStartup . (InitializedNewStore <$)
                    <$> validateCurrentSchema connection
            _ -> do
                compatibility <- readExistingCompatibility connection
                case compatibility of
                    Left failure -> pure (Left (IncompatibleStore failure))
                    Right actual
                        | actual /= expected -> pure (Left (IncompatibleStore
                            (StoreCompatibilityMismatch expected actual)))
                        | otherwise -> first FatalStoreStartup . (OpenedCurrentStore <$)
                            <$> validateCurrentSchema connection
    case admitted of
        Left failure -> pure (Left failure)
        Right startup -> fmap (first FatalStoreStartup . (startup <$))
            (configureConnection connection)
  where
    expected = currentStoreCompatibility theory

readExistingCompatibility
    :: SQLite.Connection
    -> IO (Either StoreIncompatibility StoreCompatibility)
readExistingCompatibility connection = do
    -- Return booleans, never arbitrary metadata, and never query a view posing
    -- as the compatibility table. Older table definitions remain classifiable.
    kinds <- SQLite.query connection
        ("SELECT EXISTS (SELECT 1 FROM sqlite_master WHERE name = ? AND type = 'table'), "
            <> "EXISTS (SELECT 1 FROM sqlite_master WHERE name = ?)")
        (compatibilityTableName, compatibilityTableName) :: IO [(Bool, Bool)]
    case kinds of
        [(True, _)] -> readRow
        [(False, False)] -> pure (Left StoreCompatibilityMissing)
        _ -> pure (Left (StoreCompatibilityMalformed "compatibility object is not a table"))
  where
    readRow = do
        rowResult <- trySynchronous
            (SQLite.queryWith_
                ((,,) <$> field <*> field <*> guardedColumnRow)
                connection
                ("SELECT typeof(cache_epoch), "
                    <> "CASE typeof(cache_epoch) WHEN 'integer' THEN cache_epoch ELSE NULL END, "
                    <> guardedColumnQuery TheoryIdColumn
                    <> " FROM store_compatibility ORDER BY singleton LIMIT 2")
                :: IO [(Text, Maybe Int64, GuardedStoreColumn)])
        case rowResult of
            Left failure -> pure (Left (StoreCompatibilityMalformed
                (Text.pack (take 512 (Exception.displayException failure)))))
            Right [("integer", Just epoch, theoryColumn)] ->
                pure (decodeCompatibility (epoch, theoryColumn))
            Right rows -> pure (Left (StoreCompatibilityMalformed
                ("expected one integer compatibility epoch, found "
                    <> Text.pack (show (fmap (\(kind, _, _) -> kind) rows)))))

decodeCompatibility
    :: (Int64, GuardedStoreColumn)
    -> Either StoreIncompatibility StoreCompatibility
decodeCompatibility (epoch, theoryColumn)
    | epoch < 0
        || toInteger epoch > toInteger (maxBound :: Word32) =
        Left
            (StoreCompatibilityMalformed
                "cache epoch is outside the Word32 range")
    | otherwise = do
        checkedTheoryBytes <-
            first
                (StoreCompatibilityMalformed . renderStoreFailure)
                (checkedStoreColumn CompatibilityMetadata "" TheoryIdColumn theoryColumn)
        case decodeCache getTheoryIdCache checkedTheoryBytes of
            Left failure ->
                Left
                    (StoreCompatibilityMalformed
                        (Text.pack (show failure)))
            Right theory ->
                Right
                    (StoreCompatibility
                        (cacheEpochFromValue (fromIntegral epoch))
                        theory)

initializeSchema
    :: SQLite.Connection
    -> TheoryId
    -> IO ()
initializeSchema connection theory = do
    traverse_
        (SQLite.execute_ connection . schemaQuery . snd)
        schemaStatements
    SQLite.execute connection
        ("INSERT INTO store_compatibility "
            <> "(singleton, cache_epoch, theory_id) VALUES (1, ?, ?)")
        ( fromIntegral (cacheEpochValue currentCacheEpoch) :: Int64
        , encodeCache (putTheoryIdCache theory)
        )

validateCurrentSchema
    :: SQLite.Connection
    -> IO (Either StoreFailure ())
validateCurrentSchema connection = do
    -- CASE guards run before sqlite-simple materializes Text. The extra row
    -- detects excess inventory; no unbounded names, SQL, or diagnostics escape.
    rows <- SQLite.query_ connection (Query
        ("SELECT " <> boundedTextColumn "type" 16 <> ", "
            <> boundedTextColumn "name" 128 <> ", "
            <> boundedTextColumn "tbl_name" 128 <> ", "
            <> boundedTextColumn "sql" 4096 <> ", sql IS NULL FROM sqlite_master LIMIT "
            <> Text.pack (show (maximumObjects + 1))))
        :: IO [(Maybe Text, Maybe Text, Maybe Text, Maybe Text, Bool)]
    pure do
        unless (length rows <= maximumObjects)
            (invalid "schema object count exceeds the admitted inventory")
        objects <- traverse admit rows
        let names = [name | (_, Just name, _, _, _) <- rows]
        unless (length names == Set.size (Set.fromList names))
            (invalid "duplicate schema object names")
        let found = Map.fromList (catMaybes objects)
        unless (found == expected)
            (invalid (schemaDifference expected found))
  where
    expectedTables = Map.fromList [(name, normalizeSchema sql) | (name, sql) <- schemaStatements]
    expected = Map.union expectedTables (Map.map (const "") indexes)
    -- Every declared table has one primary key. INTEGER PRIMARY KEY and
    -- WITHOUT ROWID declarations do not create a sqlite_master index row.
    indexes = Map.fromList
        [("sqlite_autoindex_" <> name <> "_1", name)
        | (name, sql) <- schemaStatements
        , name /= compatibilityTableName
        , not ("WITHOUT ROWID" `Text.isSuffixOf` sql)]
    statistics = ["sqlite_stat1", "sqlite_stat4"]
    maximumObjects = Map.size expected + length statistics
    invalid = Left . StoreSchemaIntegrityFailure . Text.take 512
    admit (Just "table", Just name, Just owner, Just sql, False)
        | name == owner, Map.member name expectedTables = Right (Just (name, normalizeSchema sql))
        -- ANALYZE/PRAGMA optimize may create these reserved tables. Their SQL
        -- spelling is SQLite-owned; application tables retain exact comparison.
        | name == owner, name `elem` statistics = Right Nothing
    admit (Just "index", Just name, Just owner, Nothing, True)
        | Map.lookup name indexes == Just owner = Right (Just (name, ""))
    admit (Nothing, _, _, _, _) = invalid "schema object type exceeds its text admission limit"
    admit (_, Nothing, _, _, _) = invalid "schema object name exceeds its text admission limit"
    admit (_, _, Nothing, _, _) = invalid "schema object owner exceeds its text admission limit"
    admit (_, _, _, Nothing, False) = invalid "schema definition exceeds its text admission limit"
    admit _ = invalid "unexpected schema object kind, ownership, or definition"

    boundedTextColumn column limit =
        "CASE WHEN typeof(" <> column <> ") = 'text' THEN CASE WHEN length(CAST("
            <> column <> " AS BLOB)) <= " <> Text.pack (show (limit :: Int))
            <> " THEN " <> column <> " ELSE NULL END ELSE NULL END"

configureConnection
    :: SQLite.Connection
    -> IO (Either StoreFailure ())
configureConnection connection = do
    journal <- SQLite.query_ connection
        "PRAGMA journal_mode = DELETE"
        :: IO [Only Text]
    SQLite.execute_ connection
        "PRAGMA synchronous = NORMAL"
    synchronous <- SQLite.query_ connection
        "PRAGMA synchronous"
        :: IO [Only Int]
    SQLite.execute_ connection
        "PRAGMA foreign_keys = ON"
    foreignKeys <- SQLite.query_ connection
        "PRAGMA foreign_keys"
        :: IO [Only Int]
    pure do
        unless
            (journal == [Only "delete"])
            (Left
                (StoreConfigurationFailure
                    ("unexpected journal mode: "
                        <> Text.pack (show journal))))
        unless
            (synchronous == [Only 1])
            (Left
                (StoreConfigurationFailure
                    ("unexpected synchronous mode: "
                        <> Text.pack (show synchronous))))
        unless
            (foreignKeys == [Only 1])
            (Left
                (StoreConfigurationFailure
                    ("foreign keys were not enabled: "
                        <> Text.pack (show foreignKeys))))


writeCanonicalRows
    :: Store
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> Except.ExceptT StoreFailure IO ()
writeCanonicalRows store objects propositions = do
    let Store _path theory connection _gate = store
    proposed <- Except.liftEither
        (indexProposedObjects objects)
    stored <- loadReferencedObjects
        store
        proposed
        (Set.unions
            ( (objectReferences . assertedObjectContent
                <$> objects)
            <> (canonicalTermGlobals
                    . frozenCoreTerm
                    . checkedPropositionTerm
                <$> propositions)
            ))
    closure <- Except.liftEither
        (first StoreObjectValidationFailure
            (validateObjectClosure
                theory
                (Map.elems proposed <> Map.elems stored)))
    checkedPropositions <-
        traverse
            (Except.liftEither
                . first StorePropositionValidationFailure
                . revalidatePropositionContent closure)
            propositions
    traverse_ (insertCanonicalObject theory connection) objects
    traverse_
        (insertCanonicalProposition connection)
        checkedPropositions

loadCanonicalObject
    :: Store
    -> ObjectId
    -> IO (Either StoreFailure (Maybe AssertedObject))
loadCanonicalObject store identity =
    runStoreOperation "load canonical object" do
        root <- Except.runExceptT
            (loadObjectRow store identity)
        case root of
            Left failure ->
                throwIO (StoreAbort failure)
            Right Nothing ->
                pure Nothing
            Right (Just asserted) -> do
                let proposed =
                        Map.singleton identity asserted
                storedResult <- Except.runExceptT
                    (loadReferencedObjects
                        store
                        proposed
                        (objectReferences
                            (assertedObjectContent asserted)))
                stored <-
                    either (throwIO . StoreAbort) pure storedResult
                closure <-
                    either
                        (throwIO
                            . StoreAbort
                            . StoreObjectValidationFailure)
                        pure
                        (validateObjectClosure
                            theory
                            (asserted : Map.elems stored))
                pure
                    (asserted <$ lookupCheckedObjectContent identity closure)
  where
    Store _path theory _connection _gate = store

loadCanonicalProposition
    :: Store
    -> PropositionId
    -> IO
        (Either
            StoreFailure
            (Maybe CheckedPropositionContent))
loadCanonicalProposition store identity =
    runStoreOperation "load canonical proposition" do
        rowResult <- Except.runExceptT
            (loadPropositionRow store identity)
        row <- either (throwIO . StoreAbort) pure rowResult
        case row of
            Nothing ->
                pure Nothing
            Just candidate -> do
                storedResult <- Except.runExceptT
                    (loadReferencedObjects
                        store
                        Map.empty
                        (canonicalTermGlobals
                            (storedPropositionCandidateTerm candidate)))
                stored <-
                    either (throwIO . StoreAbort) pure storedResult
                closure <-
                    either
                        (throwIO
                            . StoreAbort
                            . StoreObjectValidationFailure)
                        pure
                        (validateObjectClosure theory (Map.elems stored))
                Just
                    <$> either
                        (throwIO
                            . StoreAbort
                            . StorePropositionValidationFailure)
                        pure
                        (validateStoredPropositionCandidate
                            closure candidate)
  where
    Store _path theory _connection _gate = store

loadProofValidation
    :: StoreCheck
    -> ProofValidationKey
    -> IO (Either StoreFailure (Maybe ProofValidationRecord))
loadProofValidation (StoreCheck store _memo) key =
    withStoreOperation store
        (loadExactTyped
            store
            ProofValidations
            (cacheDigestBytes (proofValidationKeyDigest key))
            proofValidationSelect
            getProofValidationRecordCache
            (\record -> proofValidationRecordKey record == key)
            StoreValidationRecordKeyMismatch)

loadDeclarationValidation
    :: StoreCheck
    -> DeclarationValidationKey
    -> IO (Either StoreFailure (Maybe DeclarationValidationRecord))
loadDeclarationValidation (StoreCheck store _memo) key =
    withStoreOperation store
        (loadExactTyped
            store
            DeclarationValidations
            (cacheDigestBytes (declarationValidationKeyDigest key))
            declarationValidationSelect
            getDeclarationValidationRecordCache
            (\record -> declarationValidationRecordKey record == key)
            StoreValidationRecordKeyMismatch)

loadParsedArtefact
    :: Store
    -> SourceDescriptor
    -> Parsed.ParsedModuleKey
    -> IO
        (Either
            StoreFailure
            (Maybe ParsedPayload.DecodedParsedArtefact))
loadParsedArtefact store@(Store _path _theory connection _gate) descriptor key =
    withStoreOperation store $ runStoreOperation "load parsed artefact" do
        result <- Except.runExceptT do
            let encodedKey =
                    cacheDigestBytes (Parsed.parsedModuleKeyDigest key)
            rows <- liftIO
                (SQLite.queryWith parsedArtefactRow connection parsedArtefactSelect (Only encodedKey))
            case rows of
                [] ->
                    pure Nothing
                [(encodedIdentity, encodedPayload)] -> do
                    checkedIdentity <- Except.liftEither
                        (checkedStoreColumn ParsedArtefacts encodedKey ParsedModuleIdColumn encodedIdentity)
                    checkedPayload <- Except.liftEither
                        (checkedStoreColumn ParsedArtefacts encodedKey PayloadColumn encodedPayload)
                    decoded <- Except.liftEither
                        (first
                            (storeCacheDecodeFailure
                                ParsedArtefacts encodedKey)
                            (ParsedPayload.decodedParsedArtefactFromBytes
                                descriptor key checkedPayload))
                    let artefact = ParsedPayload.decodedParsedArtefact decoded
                    unless
                        (checkedIdentity == cacheDigestBytes
                            (Parsed.parsedModuleIdDigest
                                (ParsedPayload.parsedArtefactId artefact)))
                        (Except.throwError StoreParsedArtefactIdMismatch)
                    pure (Just decoded)
                _ ->
                    Except.throwError
                        (StoreSchemaIntegrityFailure
                            "primary key returned several parsed artefact rows")
        either (throwIO . StoreAbort) pure result

writeParsedArtefact
    :: Store
    -> ParsedPayload.ParsedArtefact
    -> IO (Either StoreFailure ParsedPayload.ParsedArtefact)
writeParsedArtefact store@(Store _path _theory connection _gate) artefact =
    withStoreOperation store $ runStoreOperation "write parsed artefact" do
        SQLite.withTransaction connection do
            outcome <- Except.runExceptT
                (insertParsedArtefact connection artefact)
            either (throwIO . StoreAbort) (const (pure artefact)) outcome

loadSyntaxInterface
    :: Store
    -> Syntax.SyntaxInterfaceId
    -> IO (Either StoreFailure (Maybe Syntax.ModuleSyntaxInterface))
loadSyntaxInterface store key =
    loadExactTyped
        store
        SyntaxInterfaces
        (cacheDigestBytes (Syntax.syntaxInterfaceIdDigest key))
        syntaxInterfaceSelect
        Syntax.getModuleSyntaxInterfaceCache
        (\interface -> Syntax.moduleSyntaxAssertedId interface == key)
        StoreInterfaceIdMismatch

loadSemanticInterface
    :: Store
    -> SemanticInterfaceId
    -> IO (Either StoreFailure (Maybe SemanticInterface))
loadSemanticInterface store key =
    loadExactTyped
        store
        SemanticInterfaces
        (cacheDigestBytes (semanticInterfaceIdDigest key))
        semanticInterfaceSelect
        getSemanticInterfaceCache
        (\interface -> semanticInterfaceAssertedId interface == key)
        StoreInterfaceIdMismatch

loadModuleArtefactResult
    :: Store
    -> ModuleArtefactId
    -> IO (Either StoreFailure (Maybe ModuleArtefactResult))
loadModuleArtefactResult (Store _path _theory connection _gate) key =
    runStoreOperation "load module artefact" do
        result <- Except.runExceptT
            (loadModuleArtefactRow connection key)
        either (throwIO . StoreAbort) pure result

loadModuleArtefactRow
    :: SQLite.Connection
    -> ModuleArtefactId
    -> Except.ExceptT StoreFailure IO (Maybe ModuleArtefactResult)
loadModuleArtefactRow connection key = do
    let encodedKey = cacheDigestBytes (moduleArtefactIdDigest key)
    rows <- liftIO
        (SQLite.queryWith moduleArtefactRow connection moduleArtefactSelect (Only encodedKey))
    case rows of
        [] ->
            pure Nothing
        [(syntaxColumn, semanticColumn, payload)] -> do
            checkedSyntax <- Except.liftEither
                (checkedStoreColumn ModuleArtefacts encodedKey SyntaxInterfaceIdColumn syntaxColumn)
            checkedSemantic <- Except.liftEither
                (checkedStoreColumn ModuleArtefacts encodedKey SemanticInterfaceIdColumn semanticColumn)
            checkedPayload <- Except.liftEither
                (checkedStoreColumn ModuleArtefacts encodedKey PayloadColumn payload)
            result <- Except.liftEither
                (first
                    (storeCacheDecodeFailure ModuleArtefacts encodedKey)
                    (decodeCache
                        (getModuleArtefactResultCache key)
                        checkedPayload))
            unless
                (moduleArtefactResultId result == key)
                (Except.throwError StoreModuleArtefactIdMismatch)
            let expectedSyntax =
                    cacheDigestBytes
                        (Syntax.syntaxInterfaceIdDigest
                            (moduleArtefactResultSyntax result))
                expectedSemantic =
                    cacheDigestBytes
                        (semanticInterfaceIdDigest
                            (moduleArtefactResultSemantic result))
            unless
                (checkedSyntax == expectedSyntax
                    && checkedSemantic == expectedSemantic)
                (Except.throwError StoreModuleArtefactColumnsMismatch)
            pure (Just result)
        _ ->
            Except.throwError
                (StoreSchemaIntegrityFailure
                    "primary key returned several module artefact rows")

-- | Read only this producer's declared rows. Dependencies can be supplied
-- only by the checked direct parents used by Declaration's local admission.
loadCachedModuleCandidate
    :: StoreCheck -> ModuleArtefactKey -> Syntax.SyntaxInterfaceId
    -> IO (Either StoreFailure (Maybe CachedModuleCandidate))
loadCachedModuleCandidate (StoreCheck store memo) expectedKey expectedSyntax =
    withStoreOperation store (Except.runExceptT loadCandidate)
  where
    loadCandidate = do
        validateModuleTheory (storeTheoryId store) expectedKey
        loaded <- Except.ExceptT (memoArtefact memo store (moduleArtefactId expectedKey))
        case loaded of
            Nothing -> pure Nothing
            Just artefact -> do
                unless (moduleArtefactResultSyntax artefact == expectedSyntax)
                    (Except.throwError (StoreModuleArtefactSyntaxMismatch
                        expectedSyntax (moduleArtefactResultSyntax artefact)))
                validateCachedSyntax memo store Set.empty expectedSyntax
                syntax <- requireMemo SyntaxInterfaces
                    (cacheDigestBytes (Syntax.syntaxInterfaceIdDigest expectedSyntax))
                    (memoSyntax memo store expectedSyntax)
                let semanticId = moduleArtefactResultSemantic artefact
                semantic <- requireMemo SemanticInterfaces
                    (cacheDigestBytes (semanticInterfaceIdDigest semanticId))
                    (memoSemantic memo store semanticId)
                validateModuleSemanticKey expectedKey semantic
                let declarations = semanticInterfaceDeclarations semantic
                objects <- for (concatMap declarationDeltaObjects declarations) \identity ->
                    requireMemo CanonicalObjects (encodeCache (putObjectIdCache identity))
                        (memoObject memo store identity)
                propositions <- for (nubOrd (concatMap declarationDeltaPropositions declarations)) \identity ->
                    requireMemo CanonicalPropositions (encodeCache (putPropositionIdCache identity))
                        (memoPropositionRow memo store identity)
                pure (Just (CachedModuleCandidate syntax semantic objects propositions
                    (moduleArtefactResultCertificates artefact)))

-- | Flush only completed declaration batches.  This operation does not make
-- any interface or module root visible to importers.
writePendingModulePrefix
    :: StoreCheck
    -> Commit.PendingModulePrefix
    -> IO (Either StoreFailure ())
writePendingModulePrefix (StoreCheck store _memo) prefix =
    withStoreOperation store
        $ runStoreOperation "write pending module prefix" do
            SQLite.withTransaction connection do
                outcome <- Except.runExceptT do
                    writeCanonicalRows
                        store
                        objects
                        propositions
                    traverse_
                        (insertProofValidation connection)
                        proofValidations
                    traverse_
                        (insertDeclarationValidation connection)
                        declarationValidations
                either (throwIO . StoreAbort) pure outcome
  where
    Store _path _theory connection _gate = store
    batches = Commit.pendingModulePrefixBatches prefix
    objects = concatMap Commit.committedBatchObjects batches
    propositions = concatMap Commit.committedBatchPropositions batches
    proofValidations =
        concatMap Commit.committedBatchProofValidations batches
    declarationValidations =
        [ validation
        | batch <- batches
        , Just validation <-
            [Commit.committedBatchDeclarationValidation batch]
        ]

-- | Publish one completed module atomically. The key and actual committed
-- prefix determine the root and certificates; callers supply only its interfaces.
writeSealedModule
    :: StoreCheck
    -> ModuleArtefactKey
    -> Commit.PendingModulePrefix
    -> Syntax.ModuleSyntaxInterface
    -> SemanticInterface
    -> IO (Either StoreFailure ())
writeSealedModule (StoreCheck store _memo) key prefix syntax semantic =
    withStoreOperation store $ runStoreOperation "write sealed module" do
        SQLite.withTransaction connection do
            outcome <- Except.runExceptT do
                validatePublishedPrefix
                writeCanonicalRows store objects propositions
                validateSyntaxInputs store syntax
                validateSemanticInputs store semantic
                traverse_ (insertProofValidation connection) proofValidations
                traverse_ (insertDeclarationValidation connection) declarationValidations
                insertSyntaxInterface connection syntax
                insertSemanticInterface connection semantic
                insertModuleArtefact connection artefact
            either (throwIO . StoreAbort) pure outcome
  where
    Store _path theory connection _gate = store
    batches = Commit.pendingModulePrefixBatches prefix
    objects = concatMap Commit.committedBatchObjects batches
    propositions = concatMap Commit.committedBatchPropositions batches
    proofValidations = concatMap Commit.committedBatchProofValidations batches
    declarationValidations =
        [ validation
        | batch <- batches
        , Just validation <- [Commit.committedBatchDeclarationValidation batch]
        ]
    artefact = moduleArtefactResult key
        (Syntax.moduleSyntaxAssertedId syntax)
        (semanticInterfaceAssertedId semantic)
        (concatMap Commit.committedBatchValidationCertificates batches)
    validatePublishedPrefix = do
        validateModuleTheory theory key
        validateModuleSemanticKey key semantic
        initial <- Except.liftEither
            (first StoreModulePrefixFailure
                (initialPrefixContextId theory (semanticInterfaceOwner semantic)
                    (semanticInterfaceDirectInputs semantic)))
        let declarations = semanticInterfaceDeclarations semantic
            expectedFinal = foldl' nextPrefixContextId initial declarations
        unless ((Commit.committedBatchDelta <$> batches) == declarations
                && Commit.pendingModulePrefixCurrent prefix == expectedFinal)
            (Except.throwError StoreModulePrefixMismatch)

validateModuleTheory :: TheoryId -> ModuleArtefactKey -> Except.ExceptT StoreFailure IO ()
validateModuleTheory theory key =
    unless (moduleArtefactKeyTheory key == theory)
        (Except.throwError (StoreModuleArtefactTheoryMismatch theory (moduleArtefactKeyTheory key)))

validateModuleSemanticKey :: ModuleArtefactKey -> SemanticInterface -> Except.ExceptT StoreFailure IO ()
validateModuleSemanticKey key semantic = do
    unless (semanticInterfaceOwner semantic == moduleArtefactKeyOwner key)
        (Except.throwError (StoreModuleArtefactOwnerMismatch
            (moduleArtefactKeyOwner key) (semanticInterfaceOwner semantic)))
    unless (semanticInterfaceDirectInputs semantic == moduleArtefactKeyDirectSemanticInputs key)
        (Except.throwError (StoreModuleArtefactDirectMismatch
            (moduleArtefactKeyDirectSemanticInputs key) (semanticInterfaceDirectInputs semantic)))

validateSyntaxInputs
    :: Store -> Syntax.ModuleSyntaxInterface -> Except.ExceptT StoreFailure IO ()
validateSyntaxInputs store = traverse_ (requireSyntax store) . Syntax.moduleSyntaxDirectInputs

requireSyntax :: Store -> Syntax.SyntaxInterfaceId -> Except.ExceptT StoreFailure IO ()
requireSyntax store identity = do
    loaded <- liftIO (loadSyntaxInterface store identity) >>= Except.liftEither
    when (isNothing loaded)
        (Except.throwError (StoreAssertedChildMissing SyntaxInterfaces
            (cacheDigestBytes (Syntax.syntaxInterfaceIdDigest identity))))

validateSemanticInputs
    :: Store
    -> SemanticInterface
    -> Except.ExceptT StoreFailure IO ()
validateSemanticInputs store interface = do
    traverse_
        (requireSemantic store)
        (semanticInterfaceDirectInputs interface)
    let declarations = semanticInterfaceDeclarations interface
        objectIds =
            concatMap declarationDeltaObjects declarations
            <> [ semanticGlobalTargetObject
                    (semanticGlobalBindingTarget binding)
               | declaration <- declarations
               , binding <- semanticEnvironmentBindings
                    (declarationDeltaEnvironment declaration)
               ]
        propositionIds =
            concatMap declarationDeltaPropositions declarations
            <> [ semanticFactProposition occurrence
               | declaration <- declarations
               , occurrence <- declarationDeltaFacts declaration
               ]
    traverse_ (requireObject store) (nubOrd objectIds)
    traverse_ (requireProposition store) (nubOrd propositionIds)

requireSemantic :: Store -> SemanticInterfaceId -> Except.ExceptT StoreFailure IO ()
requireSemantic store identity = do
    loaded <- liftIO (loadSemanticInterface store identity) >>= Except.liftEither
    when (isNothing loaded)
        (Except.throwError (StoreAssertedChildMissing SemanticInterfaces
            (cacheDigestBytes (semanticInterfaceIdDigest identity))))

requireObject
    :: Store
    -> ObjectId
    -> Except.ExceptT StoreFailure IO ()
requireObject store identity = do
    loaded <- liftIO
        (loadCanonicalObject store identity)
    case loaded of
        Left failure ->
            Except.throwError failure
        Right (Just _) ->
            pure ()
        Right Nothing ->
            Except.throwError
                (StoreAssertedChildMissing
                    CanonicalObjects
                    (encodeCache (putObjectIdCache identity)))

requireProposition
    :: Store
    -> PropositionId
    -> Except.ExceptT StoreFailure IO ()
requireProposition store identity = do
    loaded <- liftIO
        (loadCanonicalProposition store identity)
    case loaded of
        Left failure ->
            Except.throwError failure
        Right (Just _) ->
            pure ()
        Right Nothing ->
            Except.throwError
                (StoreAssertedChildMissing
                    CanonicalPropositions
                    (encodeCache (putPropositionIdCache identity)))

loadExactTyped
    :: Store
    -> StoreRelation
    -> ByteString
    -> Query
    -> CacheGet value
    -> (value -> Bool)
    -> (StoreRelation -> StoreFailure)
    -> IO (Either StoreFailure (Maybe value))
loadExactTyped store relation key selectRow decoder validates identityFailure =
    runStoreOperation ("load " <> relationName relation) do
        row <- Except.runExceptT
            (loadPayload relation selectRow key connection)
        payload <- either (throwIO . StoreAbort) pure row
        case payload of
            Nothing ->
                pure Nothing
            Just bytes ->
                case decodeCache decoder bytes of
                    Left failure ->
                        throwIO
                            (StoreAbort
                                (storeCacheDecodeFailure
                                    relation key failure))
                    Right value
                        | validates value ->
                            pure (Just value)
                        | otherwise ->
                            throwIO
                                (StoreAbort (identityFailure relation))
  where
    Store _path _theory connection _gate = store

-- Syntax closure checking is independent of semantic admission and retains
-- its own positive validation memo.
validateCachedSyntax
    :: StoreMemo -> Store -> Set Syntax.SyntaxInterfaceId -> Syntax.SyntaxInterfaceId
    -> Except.ExceptT StoreFailure IO ()
validateCachedSyntax memo store path identity = do
    validated <- liftIO (IORef.readIORef (memoValidatedSyntax memo))
    unless (identity `Set.member` validated || identity `Set.member` path) do
        interface <- requireMemo SyntaxInterfaces
            (cacheDigestBytes (Syntax.syntaxInterfaceIdDigest identity))
            (memoSyntax memo store identity)
        traverse_ (validateCachedSyntax memo store (Set.insert identity path))
            (Syntax.moduleSyntaxDirectInputs interface)
        liftIO do
            IORef.modifyIORef' (memoValidatedSyntax memo) (Set.insert identity)
            IORef.modifyIORef' (memoSyntaxValidationVisits memo) (+ 1)

requireMemo
    :: StoreRelation -> ByteString -> IO (Either StoreFailure (Maybe value))
    -> Except.ExceptT StoreFailure IO value
requireMemo relation key action = do
    loaded <- Except.ExceptT action
    maybe (Except.throwError (StoreAssertedChildMissing relation key)) pure loaded

memoArtefact
    :: StoreMemo
    -> Store
    -> ModuleArtefactId
    -> IO (Either StoreFailure (Maybe ModuleArtefactResult))
memoArtefact memo store identity =
    memoized (memoArtefactRows memo) identity
        (loadModuleArtefactResult store identity)

memoSyntax
    :: StoreMemo
    -> Store
    -> Syntax.SyntaxInterfaceId
    -> IO (Either StoreFailure (Maybe Syntax.ModuleSyntaxInterface))
memoSyntax memo store identity =
    memoized (memoSyntaxRows memo) identity
        (loadSyntaxInterface store identity)

memoSemantic
    :: StoreMemo
    -> Store
    -> SemanticInterfaceId
    -> IO (Either StoreFailure (Maybe SemanticInterface))
memoSemantic memo store identity =
    memoized (memoSemanticRows memo) identity
        (loadSemanticInterface store identity)

memoObject
    :: StoreMemo
    -> Store
    -> ObjectId
    -> IO (Either StoreFailure (Maybe AssertedObject))
memoObject memo store identity =
    memoized (memoObjectRows memo) identity
        (loadShallowObject store identity)

memoPropositionRow
    :: StoreMemo
    -> Store
    -> PropositionId
    -> IO (Either StoreFailure (Maybe StoredPropositionCandidate))
memoPropositionRow memo store identity =
    memoized (memoPropositionRows memo) identity
        (loadShallowProposition store identity)

loadShallowObject
    :: Store
    -> ObjectId
    -> IO (Either StoreFailure (Maybe AssertedObject))
loadShallowObject store identity =
    runStoreOperation "load shallow canonical object" do
        row <- Except.runExceptT (loadObjectRow store identity)
        either (throwIO . StoreAbort) pure row

loadShallowProposition
    :: Store
    -> PropositionId
    -> IO
        (Either
            StoreFailure
            (Maybe StoredPropositionCandidate))
loadShallowProposition store identity =
    runStoreOperation "load shallow canonical proposition" do
        result <- Except.runExceptT
            (loadPropositionRow store identity)
        either (throwIO . StoreAbort) pure result

-- Absence can be followed by publication within the same StoreCheck. Only
-- existing rows are stable under the store's immutable exact-write policy.
memoized
    :: Ord key
    => IORef.IORef (Map key value)
    -> key
    -> IO (Either StoreFailure (Maybe value))
    -> IO (Either StoreFailure (Maybe value))
memoized reference key action = do
    entries <- IORef.readIORef reference
    case Map.lookup key entries of
        Just value -> pure (Right (Just value))
        Nothing -> do
            result <- action
            case result of
                Right (Just value) -> IORef.modifyIORef' reference (Map.insert key value)
                _ -> pure ()
            pure result

indexProposedObjects
    :: [AssertedObject]
    -> Either StoreFailure (Map ObjectId AssertedObject)
indexProposedObjects =
    foldM insertOne Map.empty
  where
    insertOne indexed asserted
        | Map.member identity indexed =
            Left
                (StoreObjectValidationFailure
                    (DuplicateAssertedObjectId identity))
        | otherwise =
            Right (Map.insert identity asserted indexed)
      where
        identity = assertedObjectId asserted

loadReferencedObjects
    :: Store
    -> Map ObjectId AssertedObject
    -> Set ObjectId
    -> Except.ExceptT
        StoreFailure
        IO
        (Map ObjectId AssertedObject)
loadReferencedObjects store proposed =
    go Set.empty Map.empty . Set.toAscList
  where
    go _seen loaded [] =
        pure loaded
    go seen loaded (identity : remaining)
        | identity `Set.member` seen
            || Map.member identity proposed =
            go seen loaded remaining
        | otherwise = do
            row <- loadObjectRow store identity
            case row of
                Nothing ->
                    go
                        (Set.insert identity seen)
                        loaded
                        remaining
                Just asserted ->
                    go
                        (Set.insert identity seen)
                        (Map.insert identity asserted loaded)
                        ( Set.toAscList
                            (objectReferences
                                (assertedObjectContent asserted))
                            <> remaining
                        )

loadPropositionRow
    :: Store
    -> PropositionId
    -> Except.ExceptT
        StoreFailure
        IO
        (Maybe StoredPropositionCandidate)
loadPropositionRow
        _store@(Store _path _theory connection _gate)
        identity = do
    let key = encodeCache (putPropositionIdCache identity)
    payload <- loadPayload
        CanonicalPropositions propositionSelect key connection
    Except.liftEither (traverse (decodePropositionPayload identity) payload)

decodePropositionPayload
    :: PropositionId -> ByteString -> Either StoreFailure StoredPropositionCandidate
decodePropositionPayload identity bytes = do
    reentered <- first (storeTermReentryFailure CanonicalPropositions)
        (reenterCanonicalTerm (termDigestFromPropositionId identity) bytes)
    first StorePropositionReentryFailure
        (storedPropositionCandidate identity reentered)

loadObjectRow
    :: Store
    -> ObjectId
    -> Except.ExceptT
        StoreFailure
        IO
        (Maybe AssertedObject)
loadObjectRow _store@(Store _path theory connection _gate) identity = do
    let key = encodeCache (putObjectIdCache identity)
    payload <- loadPayload
        CanonicalObjects
        objectSelect
        key
        connection
    Except.liftEither (traverse (decodeObjectPayload theory identity) payload)

decodeObjectPayload
    :: TheoryId -> ObjectId -> ByteString -> Either StoreFailure AssertedObject
decodeObjectPayload theory identity bytes =
    case objectIdFamily identity of
        IntrinsicObject -> do
            tag <- decodePayload getCoreIntrinsicTagCache
            first StoreObjectReentryFailure
                (reenterIntrinsicObject theory identity tag)
        TransparentObject -> do
            (coreType, reentered) <- decodePayload
                ((,) <$> getCoreTypeCache <*> getReenteredCanonicalTermCache)
            first StoreObjectReentryFailure
                (reenterTransparentObject theory identity coreType reentered)
        OpaqueObject -> do
            (seed, coreType) <- decodePayload
                ((,) <$> getOpaqueDeclarationSeedCache <*> getCoreTypeCache)
            first StoreObjectReentryFailure
                (reenterOpaqueObject theory identity seed coreType)
  where
    key = encodeCache (putObjectIdCache identity)
    decodePayload :: CacheGet value -> Either StoreFailure value
    decodePayload decoder = decodeStorePayload CanonicalObjects key decoder bytes

decodeStorePayload
    :: StoreRelation -> ByteString -> CacheGet value -> ByteString
    -> Either StoreFailure value
decodeStorePayload relation key decoder =
    first (storeCacheDecodeFailure relation key) . decodeCache decoder

storeCacheDecodeFailure :: StoreRelation -> ByteString -> CacheDecodeError -> StoreFailure
storeCacheDecodeFailure relation key = \case
    CacheResourceLimitExceeded failure -> StoreRowResourceLimitExceeded relation failure
    CacheMathematicalDecodeError failure ->
        storeTermReentryFailure relation (TermCodecFailure failure)
    failure -> StoreRowDecodeFailure relation key failure

storeTermReentryFailure :: StoreRelation -> TermReentryError -> StoreFailure
storeTermReentryFailure relation = \case
    TermCodecFailure (MathematicalResourceLimitExceeded failure) ->
        StoreRowResourceLimitExceeded relation failure
    failure -> StoreTermReentryFailure failure

insertCanonicalObject
    :: TheoryId
    -> SQLite.Connection
    -> AssertedObject
    -> Except.ExceptT StoreFailure IO ()
insertCanonicalObject theory connection asserted = do
    let identity = assertedObjectId asserted
        payload = encodeCache case assertedObjectContent asserted of
            IntrinsicObjectContent _storedTheory tag ->
                putCoreIntrinsicTagCache tag
            TransparentObjectContent _storedTheory coreType body -> do
                putCoreTypeCache coreType
                putCacheBytes (encodeCanonicalTerm objectIdBuilder body)
            OpaqueObjectContent _storedTheory seed coreType -> do
                putOpaqueDeclarationSeedCache seed
                putCoreTypeCache coreType
    insertExact
        CanonicalObjects
        objectSelect
        objectInsert
        (encodeCache (putObjectIdCache identity))
        (decodeObjectPayload theory identity)
        payload
        connection

insertCanonicalProposition
    :: SQLite.Connection
    -> CheckedPropositionContent
    -> Except.ExceptT StoreFailure IO ()
insertCanonicalProposition connection proposition = do
    let identity = checkedPropositionId proposition
        term = frozenCoreTerm (checkedPropositionTerm proposition)
        bytes = encodeCanonicalTerm objectIdBuilder term
    insertExact
        CanonicalPropositions
        propositionSelect
        propositionInsert
        (encodeCache (putPropositionIdCache identity))
        (decodePropositionPayload identity)
        bytes
        connection

insertProofValidation
    :: SQLite.Connection
    -> ProofValidationRecord
    -> Except.ExceptT StoreFailure IO ()
insertProofValidation connection record =
    insertExact
        ProofValidations
        proofValidationSelect
        proofValidationInsert
        key
        (decodeStorePayload ProofValidations key getProofValidationRecordCache)
        (encodeCache (putProofValidationRecordCache record))
        connection
  where
    key = cacheDigestBytes (proofValidationKeyDigest (proofValidationRecordKey record))

insertDeclarationValidation
    :: SQLite.Connection
    -> DeclarationValidationRecord
    -> Except.ExceptT StoreFailure IO ()
insertDeclarationValidation connection record =
    insertExact
        DeclarationValidations
        declarationValidationSelect
        declarationValidationInsert
        key
        (decodeStorePayload DeclarationValidations key getDeclarationValidationRecordCache)
        (encodeCache (putDeclarationValidationRecordCache record))
        connection
  where
    key = cacheDigestBytes (declarationValidationKeyDigest (declarationValidationRecordKey record))

insertSyntaxInterface
    :: SQLite.Connection
    -> Syntax.ModuleSyntaxInterface
    -> Except.ExceptT StoreFailure IO ()
insertSyntaxInterface connection interface =
    insertExact
        SyntaxInterfaces
        syntaxInterfaceSelect
        syntaxInterfaceInsert
        key
        (decodeStorePayload SyntaxInterfaces key Syntax.getModuleSyntaxInterfaceCache)
        (encodeCache (Syntax.putModuleSyntaxInterfaceCache interface))
        connection
  where
    key = cacheDigestBytes (Syntax.syntaxInterfaceIdDigest (Syntax.moduleSyntaxAssertedId interface))

insertSemanticInterface
    :: SQLite.Connection
    -> SemanticInterface
    -> Except.ExceptT StoreFailure IO ()
insertSemanticInterface connection interface =
    insertExact
        SemanticInterfaces
        semanticInterfaceSelect
        semanticInterfaceInsert
        key
        (decodeStorePayload SemanticInterfaces key getSemanticInterfaceCache)
        (encodeCache (putSemanticInterfaceCache interface))
        connection
  where
    key = cacheDigestBytes (semanticInterfaceIdDigest (semanticInterfaceAssertedId interface))

insertModuleArtefact
    :: SQLite.Connection
    -> ModuleArtefactResult
    -> Except.ExceptT StoreFailure IO ()
insertModuleArtefact connection result =
    do
        let key = cacheDigestBytes
                (moduleArtefactIdDigest
                    (moduleArtefactResultId result))
            syntax = cacheDigestBytes
                (Syntax.syntaxInterfaceIdDigest
                    (moduleArtefactResultSyntax result))
            semantic = cacheDigestBytes
                (semanticInterfaceIdDigest
                    (moduleArtefactResultSemantic result))
            payload = encodeCache (putModuleArtefactResultCache result)
        Except.liftEither
            (checkStoreBlobByteCount
                ModuleArtefacts
                (fromIntegral (ByteString.length payload)))
        _ <- Except.liftEither
            (decodeStorePayload ModuleArtefacts key
                (getModuleArtefactResultCache (moduleArtefactResultId result)) payload)
        rows <- liftIO
            (SQLite.queryWith moduleArtefactRow connection moduleArtefactSelect (Only key))
        existing <- case rows of
            [] -> pure Nothing
            [(storedSyntax, storedSemantic, storedPayload)] -> do
                checkedSyntax <- Except.liftEither
                    (checkedStoreColumn ModuleArtefacts key SyntaxInterfaceIdColumn storedSyntax)
                checkedSemantic <- Except.liftEither
                    (checkedStoreColumn ModuleArtefacts key SemanticInterfaceIdColumn storedSemantic)
                checkedPayload <- Except.liftEither
                    (checkedStoreColumn ModuleArtefacts key PayloadColumn storedPayload)
                pure
                    (Just
                        (checkedSyntax, checkedSemantic, checkedPayload))
            _ ->
                Except.throwError
                    (StoreSchemaIntegrityFailure
                        "primary key returned several module artefact rows")
        case existing of
            Just stored
                | stored /= (syntax, semantic, payload) ->
                    Except.throwError
                        (StoreRowPayloadMismatch ModuleArtefacts key)
                | otherwise ->
                    pure ()
            _ ->
                liftIO
                    (SQLite.execute
                        connection
                        moduleArtefactInsert
                        ( key
                        , syntax
                        , semantic
                        , payload
                        ))

insertParsedArtefact
    :: SQLite.Connection
    -> ParsedPayload.ParsedArtefact
    -> Except.ExceptT StoreFailure IO ()
insertParsedArtefact connection artefact = do
    let encodedKey =
            cacheDigestBytes
                (Parsed.parsedModuleKeyDigest
                    (ParsedPayload.parsedArtefactKey artefact))
        encodedIdentity =
            cacheDigestBytes
                (Parsed.parsedModuleIdDigest
                    (ParsedPayload.parsedArtefactId artefact))
        encodedPayload =
            ParsedPayload.canonicalParsedPayloadBytes
                (ParsedPayload.parsedArtefactPayload artefact)
    Except.liftEither
        (checkStoreBlobByteCount
            ParsedArtefacts
            (fromIntegral (ByteString.length encodedPayload)))
    -- Canonical syntax can exceed the resource policy. Establish standard
    -- load admissibility before inserting or accepting an identical row.
    _ <- Except.liftEither
        (first (storeCacheDecodeFailure ParsedArtefacts encodedKey)
            (ParsedPayload.canonicalParsedPayloadFromBytes encodedPayload))
    rows <- liftIO
        (SQLite.queryWith parsedArtefactRow connection parsedArtefactSelect (Only encodedKey))
    case rows of
        [] ->
            liftIO
                (SQLite.execute
                    connection
                    parsedArtefactInsert
                    ( encodedKey
                    , encodedIdentity
                    , encodedPayload
                    ))
        [(storedIdentity, storedPayload)] -> do
            checkedIdentity <- Except.liftEither
                (checkedStoreColumn ParsedArtefacts encodedKey ParsedModuleIdColumn storedIdentity)
            checkedPayload <- Except.liftEither
                (checkedStoreColumn ParsedArtefacts encodedKey PayloadColumn storedPayload)
            if (checkedIdentity, checkedPayload)
                    == (encodedIdentity, encodedPayload)
                then
                    pure ()
                else
                    Except.throwError
                        (StoreRowPayloadMismatch ParsedArtefacts encodedKey)
        _ ->
            Except.throwError
                (StoreSchemaIntegrityFailure
                    "primary key returned several parsed artefact rows")

insertExact
    :: StoreRelation
    -> Query
    -> Query
    -> ByteString
    -> (ByteString -> Either StoreFailure value)
    -> ByteString
    -> SQLite.Connection
    -> Except.ExceptT StoreFailure IO ()
insertExact relation selectRow insertRow key decoder payload connection = do
    Except.liftEither
        (checkStoreBlobByteCount
            relation
            (fromIntegral (ByteString.length payload)))
    -- Typed, canonical values need not fit the reader's reconstruction policy.
    -- Every publisher supplies its reader's decoder; check it before insertion
    -- or acceptance of identical bytes, including completed-prefix writes.
    _ <- Except.liftEither (decoder payload)
    existing <- loadPayload relation selectRow key connection
    case existing of
        Nothing ->
            liftIO
                (SQLite.execute connection
                    insertRow
                    (key, payload))
        Just stored
            | stored == payload ->
                pure ()
            | otherwise ->
                Except.throwError
                    (StoreRowPayloadMismatch relation key)

loadPayload
    :: StoreRelation
    -> Query
    -> ByteString
    -> SQLite.Connection
    -> Except.ExceptT
        StoreFailure
        IO
        (Maybe ByteString)
loadPayload relation selectRow key connection = do
    rows <- liftIO
        (SQLite.queryWith guardedColumnRow connection selectRow (Only key))
    case rows of
        [] ->
            pure Nothing
        [payload] ->
            Just <$> Except.liftEither (checkedStoreColumn relation key PayloadColumn payload)
        _ ->
            Except.throwError
                (StoreSchemaIntegrityFailure
                    ("primary key returned several "
                        <> relationName relation
                        <> " rows"))

objectReferences :: ObjectContent -> Set ObjectId
objectReferences = \case
    IntrinsicObjectContent{} ->
        Set.empty
    TransparentObjectContent _theory _coreType body ->
        canonicalTermGlobals body
    OpaqueObjectContent{} ->
        Set.empty

termDigestFromPropositionId :: PropositionId -> TermDigest
termDigestFromPropositionId identity =
    maybe
        (impossible "proposition digest is not 32 bytes")
        id
        (termDigestFromBytes
            (mathematicalDigestBytes (propositionIdDigest identity)))


schemaStatements :: [(Text, Text)]
schemaStatements =
    [ ( compatibilityTableName
      , "CREATE TABLE store_compatibility ( "
            <> "singleton INTEGER NOT NULL PRIMARY KEY "
            <> "CHECK (singleton = 1), "
            <> "cache_epoch INTEGER NOT NULL CHECK (cache_epoch >= 0), "
            <> "theory_id BLOB NOT NULL CHECK (length(theory_id) = 32) )"
      )
    , canonicalRow
        "canonical_objects"
        "object_id"
        33
    , canonicalRow
        "canonical_propositions"
        "proposition_id"
        32
    , exactRow
        "proof_validations"
        "validation_key"
        32
    , exactRow
        "declaration_validations"
        "validation_key"
        32
    , exactRow
        "syntax_interfaces"
        "syntax_interface_id"
        32
    , exactRow
        "semantic_interfaces"
        "semantic_interface_id"
        32
    , ( "module_artefacts"
      , "CREATE TABLE module_artefacts ( "
            <> "module_artefact_id BLOB NOT NULL PRIMARY KEY "
            <> "CHECK (length(module_artefact_id) = 32), "
            <> "syntax_interface_id BLOB NOT NULL "
            <> "CHECK (length(syntax_interface_id) = 32), "
            <> "semantic_interface_id BLOB NOT NULL "
            <> "CHECK (length(semantic_interface_id) = 32), "
            <> "payload BLOB NOT NULL, "
            <> "FOREIGN KEY (syntax_interface_id) "
            <> "REFERENCES syntax_interfaces(syntax_interface_id), "
            <> "FOREIGN KEY (semantic_interface_id) "
            <> "REFERENCES semantic_interfaces(semantic_interface_id) )"
      )
    , ( "parsed_artefacts"
      , "CREATE TABLE parsed_artefacts ( "
            <> "parsed_module_key BLOB NOT NULL PRIMARY KEY "
            <> "CHECK (length(parsed_module_key) = 32), "
            <> "parsed_module_id BLOB NOT NULL "
            <> "CHECK (length(parsed_module_id) = 32), "
            <> "payload BLOB NOT NULL )"
      )
    ]
  where
    canonicalRow :: Text -> Text -> Int -> (Text, Text)
    canonicalRow table key keyBytes =
        let (name, statement) = exactRow table key keyBytes
        in (name, statement <> " WITHOUT ROWID")

    exactRow :: Text -> Text -> Int -> (Text, Text)
    exactRow table key keyBytes =
        ( table
        , "CREATE TABLE " <> table <> " ( "
            <> key <> " BLOB NOT NULL PRIMARY KEY "
            <> "CHECK (length(" <> key <> ") = "
            <> Text.pack (show keyBytes) <> "), "
            <> "payload BLOB NOT NULL )"
        )

compatibilityTableName :: Text
compatibilityTableName =
    "store_compatibility"

schemaQuery :: Text -> Query
schemaQuery =
    Query

normalizeSchema :: Text -> Text
normalizeSchema =
    Text.unwords
        . Text.words
        . Text.dropWhileEnd (== ';')

schemaDifference
    :: Map Text Text
    -> Map Text Text
    -> Text
schemaDifference expected actual =
    "expected current schema "
        <> Text.pack (show (Map.keys expected))
        <> ", found "
        <> Text.pack (show (Map.keys actual))
        <> changed
  where
    altered =
        [ name
        | name <- Map.keys expected
        , Map.lookup name expected /= Map.lookup name actual
        , Map.member name actual
        ]
    changed
        | null altered =
            ""
        | otherwise =
            "; altered definitions: "
                <> Text.pack (show altered)

objectSelect, objectInsert, propositionSelect, propositionInsert :: Query
objectSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM canonical_objects WHERE object_id = ? LIMIT 2"
objectInsert =
    "INSERT INTO canonical_objects (object_id, payload) VALUES (?, ?)"
propositionSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM canonical_propositions WHERE proposition_id = ? LIMIT 2"
propositionInsert =
    "INSERT INTO canonical_propositions (proposition_id, payload) VALUES (?, ?)"

proofValidationSelect, proofValidationInsert :: Query
proofValidationSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM proof_validations WHERE validation_key = ? LIMIT 2"
proofValidationInsert =
    "INSERT INTO proof_validations (validation_key, payload) VALUES (?, ?)"

declarationValidationSelect, declarationValidationInsert :: Query
declarationValidationSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM declaration_validations WHERE validation_key = ? LIMIT 2"
declarationValidationInsert =
    "INSERT INTO declaration_validations (validation_key, payload) VALUES (?, ?)"

syntaxInterfaceSelect, syntaxInterfaceInsert :: Query
syntaxInterfaceSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM syntax_interfaces WHERE syntax_interface_id = ? LIMIT 2"
syntaxInterfaceInsert =
    "INSERT INTO syntax_interfaces (syntax_interface_id, payload) VALUES (?, ?)"

semanticInterfaceSelect, semanticInterfaceInsert :: Query
semanticInterfaceSelect =
    "SELECT " <> guardedColumnQuery PayloadColumn
        <> " FROM semantic_interfaces WHERE semantic_interface_id = ? LIMIT 2"
semanticInterfaceInsert =
    "INSERT INTO semantic_interfaces (semantic_interface_id, payload) VALUES (?, ?)"

moduleArtefactSelect, moduleArtefactInsert :: Query
moduleArtefactSelect =
    "SELECT " <> guardedColumnQuery SyntaxInterfaceIdColumn <> ", "
        <> guardedColumnQuery SemanticInterfaceIdColumn <> ", "
        <> guardedColumnQuery PayloadColumn
        <> " FROM module_artefacts WHERE module_artefact_id = ? LIMIT 2"
moduleArtefactInsert =
    "INSERT INTO module_artefacts "
        <> "(module_artefact_id, syntax_interface_id, "
        <> "semantic_interface_id, payload) VALUES (?, ?, ?, ?)"

parsedArtefactSelect, parsedArtefactInsert :: Query
parsedArtefactSelect =
    "SELECT " <> guardedColumnQuery ParsedModuleIdColumn <> ", "
        <> guardedColumnQuery PayloadColumn
        <> " FROM parsed_artefacts WHERE parsed_module_key = ? LIMIT 2"
parsedArtefactInsert =
    "INSERT INTO parsed_artefacts "
        <> "(parsed_module_key, parsed_module_id, payload) VALUES (?, ?, ?)"

relationName :: StoreRelation -> Text
relationName = \case
    CompatibilityMetadata -> "store compatibility"
    CanonicalObjects -> "canonical object"
    CanonicalPropositions -> "canonical proposition"
    ProofValidations -> "proof validation"
    DeclarationValidations -> "declaration validation"
    SyntaxInterfaces -> "syntax interface"
    SemanticInterfaces -> "semantic interface"
    ModuleArtefacts -> "module artefact"
    ParsedArtefacts -> "parsed artefact"

runStoreOperation
    :: Text
    -> IO value
    -> IO (Either StoreFailure value)
runStoreOperation label action = do
    result <- trySynchronous action
    pure
        (case result of
            Right value ->
                Right value
            Left failure ->
                case Exception.fromException failure of
                    Just (StoreAbort storeFailure) ->
                        Left storeFailure
                    Nothing ->
                        Left (operationFailure label failure))

operationFailure :: Text -> Exception.SomeException -> StoreFailure
operationFailure label =
    StoreOperationFailed label . exceptionText

exceptionText :: Exception.SomeException -> Text
exceptionText =
    Text.pack . Exception.displayException

trySynchronous
    :: IO value
    -> IO (Either Exception.SomeException value)
trySynchronous =
    UnliftIO.tryAny

closeIgnoringFailure :: SQLite.Connection -> IO ()
closeIgnoringFailure connection =
    void
        (trySynchronous
            (SQLite.close connection))
