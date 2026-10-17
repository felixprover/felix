{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Store (unitTests) where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Typed
import Felix.Checking.Semantic qualified as Semantic
import Felix.Cache.Codec qualified as Cache
import Felix.Math.Codec
import Felix.Module
import Felix.Parsed.Identity qualified as Parsed
import Felix.Parsed.Payload qualified as ParsedPayload
import Felix.Source.Content qualified as Content
import Felix.Source
import Felix.Store qualified as Store
import Felix.Test.Support.Declarations qualified as DeclTest
import Felix.Test.Support.Imports
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface qualified as Syntax

import Control.Concurrent.MVar qualified as MVar
import Control.DeepSeq (force)
import Control.Exception qualified as Exception
import Control.Monad (when)
import Data.ByteString qualified as ByteString
import Data.ByteString.Char8 qualified as ByteString.Char8
import Data.Binary.Put qualified as Put
import Data.IORef qualified as IORef
import Data.List (filter)
import Data.Text qualified as Text
import Data.Maybe (catMaybes)
import Data.Vector qualified as Vector
import Database.SQLite.Simple qualified as SQLite
import Database.SQLite.Simple.Types (Only(..))
import System.Directory qualified as Directory
import System.Environment qualified as Environment
import System.Exit (ExitCode(..))
import System.FilePath.Posix qualified as Posix
import System.IO qualified as IO
import System.IO.Temp qualified as Temp
import System.Process qualified as Process
import Test.Tasty
import Test.Tasty.HUnit
import UnliftIO.Async qualified as Async




unitTests :: TestTree
unitTests =
    testGroup "SQLite store"
        [ testCase "initializes and reopens the current schema"
            initializesAndReopensCurrentSchema
        , testCase "admits SQLite maintenance objects" admitsMaintenanceSchema
        , testCase "rejects unexpected schema objects before publication" rejectsSchemaObjects
        , testCase "bounds schema names, definitions and inventory" boundsSchemaMetadata
        , testCase "does not read a compatibility view" rejectsCompatibilityView
        , testCase "bounds store blob resources without allocating fixtures"
            boundsStoreBlobResources
        , testCase "guards every payload read and insertion comparison"
            guardsStoredPayloads
        , testCase "guards associated identity widths and storage types"
            guardsStoredIdentities
        , testCase "guards compatibility identity bytes in one read"
            guardsCompatibilityIdentity
        , testCase "admits exact parsed depth and classifies exhaustion"
            parsedDecoderAdmission
        , testCase "admits stored object depth through checked module ingress"
            objectDecoderAdmission
        , testCase "bounds proposition depth before completed-prefix publication"
            propositionDecoderAdmission
        , testCase "bounds syntax payloads before sealed publication"
            syntaxPublicationAdmission
        , testCase "rejects inconsistent publication keys and prefixes atomically"
            rejectsInconsistentPublication
        , testCase "bounds raw module artefact payloads before cached admission"
            moduleArtefactDecoderAdmission
        , testCase "rejects nested semantic terms before reading the unadmitted tail"
            semanticDecoderAdmission
        , testCase "rejects a stale cache epoch or calculus without configuring the store"
            rejectsIncompatibilityWithoutConfiguration
        , testCase "rejects malformed compatibility metadata"
            rejectsMalformedCompatibilityMetadata
        , testCase "rejects a compatible incomplete schema"
            rejectsCompatibleIncompleteSchema
        , testCase "round-trips exact parsed artefacts"
            roundTripsExactParsedArtefacts
        , testCase "resumes a large canonical parsed artefact after reopening"
            resumesLargeParsedArtefact
        , testCase "rejects parsed publication beyond the standard node budget"
            rejectsParsedNodePublication
        , testCase "loads parsed syntax with the current file's locations"
            loadsParsedArtefactLocations
        , testCase "rejects malformed parsed payloads"
            rejectsMalformedParsedPayloads
        , testCase "rejects disagreeing parsed artefact identities"
            rejectsDisagreeingParsedArtefactIdentities
        , testCase "rejects malformed typed validation rows"
            rejectsMalformedTypedValidationRows
        , testCase "publishes a completed prefix before readiness"
            publishesCompletedPrefixBeforeReadiness
        , testCase "installs a sealed producer for a cached importer"
            installsSealedProducerForCachedImporter
        , testCase "validates exact cached installation inputs"
            validatesExactCachedInstallationInputs
        , testCase "rejects invalid cached root authority and closure"
            rejectsInvalidCachedRootAuthorityAndClosure
        , testCase "rejects forward formation contracts on re-entry"
            rejectsForwardFormationContractsOnReentry
        , testCase "rejects disagreeing module artefact columns"
            rejectsDisagreeingModuleArtefactColumns
        , testCase "decodes only requested local semantic contents"
            validatesSharedClosuresOncePerCheck
        , testCase "rolls back a failed readiness transaction"
            rollsBackFailedReadiness
        , testCase "rolls back an unequal duplicate batch"
            rollsBackUnequalDuplicateBatch
        , testCase "rejects malformed canonical payloads"
            rejectsMalformedCanonicalPayloads
        , testCase "rejects malformed transparent term payloads"
            rejectsMalformedTransparentTermPayloads
        , testCase "rejects mismatched canonical objects on re-entry"
            rejectsMismatchedCanonicalObjectReentry
        , testCase "stores and re-enters exact canonical rows"
            storesAndReentersCanonicalRows
        , testCase "plans default and explicit persistent stores"
            plansPersistentStores
        , testCase "refreshes a leased persistent store"
            refreshesPersistentStore
        , testCase "leaves auxiliaries when the primary store is absent"
            leavesAuxiliariesWithoutPrimary
        , testCase "reports refresh deletion failures"
            reportsRefreshDeletionFailure
        , testCase "rejects a concurrently owned persistent store"
            rejectsConcurrentPersistentLease
        , testCase "releases persistent leases after exceptions"
            releasesLeaseAfterException
        , testCase "releases persistent leases after cancellation"
            releasesLeaseAfterCancellation
        , testCase "reports lock-system acquisition failures"
            reportsLeaseAcquisitionFailure
        , testCase "cleans fresh stores on return and exceptions"
            cleansFreshStores
        , testCase "does not fall back after fatal startup"
            doesNotFallBackAfterFatalStartup
        ]

boundsStoreBlobResources :: Assertion
boundsStoreBlobResources = do
    let relations =
            [ Store.CompatibilityMetadata
            , Store.CanonicalObjects
            , Store.CanonicalPropositions
            , Store.ProofValidations
            , Store.DeclarationValidations
            , Store.SyntaxInterfaces
            , Store.SemanticInterfaces
            , Store.ModuleArtefacts
            , Store.ParsedArtefacts
            ]
        limit = Store.maximumStoreBlobBytes
    for_ relations \relation -> do
        assertEqual
            ("accepts the store blob boundary for " <> show relation)
            (Right ())
            (Store.checkStoreBlobByteCount relation limit)
        case Store.checkStoreBlobByteCount relation (limit + 1) of
            Left
                (Store.StoreBlobResourceLimitExceeded
                    actualRelation
                    actual
                    actualLimit) -> do
                        assertEqual "resource-limit relation"
                            relation actualRelation
                        assertEqual "resource-limit size" (limit + 1) actual
                        assertEqual "resource-limit ceiling" limit actualLimit
            other ->
                assertFailure
                    ("unexpected store blob boundary result: " <> show other)

parsedDecoderAdmission :: Assertion
parsedDecoderAdmission =
    withStoreFixture "felix-parsed-admission" \path theory _fixture ->
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            (key, _artefact, _other) <- makeParsedArtefacts
            delta <- expectRight (Syntax.canonicalSyntaxDelta [])
            syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
            let payload depth = ParsedPayload.canonicalParsedPayload []
                    [Raw.BlockAxiom Nowhere Nothing "depth" (Raw.Axiom []
                        (iterate (Raw.StmtNeg Nowhere)
                            (Raw.StmtFormula (Raw.PropositionalConstant Nowhere Raw.IsTop)) !! depth))]
                    [] (Syntax.moduleSyntaxAssertedId syntax)
                bytes = ParsedPayload.canonicalParsedPayloadBytes . payload
            (_, baseUsage) <- expectRight (ParsedPayload.decodedParsedArtefactFromBytesWithLimits
                standardDecoderLimits anonymousSourceDescriptor key (bytes 0))
            let maximumNegations = fromIntegral
                    (maximumDecoderDepth standardDecoderLimits - decoderPeakDepth baseUsage)
            for_ [maximumNegations - 1, maximumNegations, maximumNegations + 1] \depth -> do
                -- Each depth gets its own exact key so publication remains
                -- byte-exact and never relies on an unequal insertion.
                depthKey <- expectRight (Parsed.parsedModuleKey
                    (Content.sourceContentIdBytes (ByteString.Char8.pack (show depth)))
                    Syntax.baseSyntaxInterfaceId [])
                let artefact = ParsedPayload.parsedArtefact depthKey (payload depth)
                if depth <= maximumNegations then do
                    _ <- expectRightIO (Store.writeParsedArtefact store artefact)
                    found <- Store.loadParsedArtefact store anonymousSourceDescriptor depthKey
                    decoded <- maybe (fail "missing parsed row") pure =<< expectRight found
                    _ <- Exception.evaluate (force decoded)
                    ParsedPayload.decodedParsedArtefact decoded @?= artefact
                    (_, usage) <- expectRight (ParsedPayload.decodedParsedArtefactFromBytesWithLimits
                        standardDecoderLimits anonymousSourceDescriptor depthKey (bytes depth))
                    decoderPeakDepth usage @?= fromIntegral depth + decoderPeakDepth baseUsage
                else rejectsParsedPublication path store DecoderDepth artefact

-- Publication must reject both a new row and an identical pre-existing row.
-- Seed the latter directly to model stores written before admission was fixed.
rejectsParsedPublication
    :: FilePath -> Store.Store -> DecoderResource -> ParsedPayload.ParsedArtefact -> Assertion
rejectsParsedPublication path store resource artefact = do
    Store.writeParsedArtefact store artefact >>= assertLimit
    assertEqual "rejected publication leaves no row" (Right Nothing)
        . fmap (fmap ParsedPayload.decodedParsedArtefact)
        =<< Store.loadParsedArtefact store anonymousSourceDescriptor key
    Exception.bracket (SQLite.open path) SQLite.close \connection ->
        SQLite.execute connection
            "INSERT INTO parsed_artefacts (parsed_module_key, parsed_module_id, payload) VALUES (?, ?, ?)"
            ( Cache.cacheDigestBytes (Parsed.parsedModuleKeyDigest key)
            , Cache.cacheDigestBytes (Parsed.parsedModuleIdDigest (ParsedPayload.parsedArtefactId artefact))
            , ParsedPayload.canonicalParsedPayloadBytes (ParsedPayload.parsedArtefactPayload artefact)
            )
    Store.loadParsedArtefact store anonymousSourceDescriptor key >>= assertLimit
    Store.writeParsedArtefact store artefact >>= assertLimit
  where
    key = ParsedPayload.parsedArtefactKey artefact
    assertLimit :: Show value => Either Store.StoreFailure value -> Assertion
    assertLimit = \case
        Left (Store.StoreRowResourceLimitExceeded Store.ParsedArtefacts failure) ->
            decoderLimitedResource failure @?= resource
        other -> assertFailure ("parsed store admission: " <> show other)

objectDecoderAdmission :: Assertion
objectDecoderAdmission = for_ [False, True] \transparent -> do
    let maximumDepth = fromIntegral (maximumDecoderDepth standardDecoderLimits)
            - if transparent then 1 else 0
    for_ [maximumDepth - 1, maximumDepth, maximumDepth + 1] \depth ->
        withStoreFixture "felix-object-admission" \path theory _fixture -> do
            relative <- expectRight (safeRelativePath "depth.tex")
            let owner = moduleNameFromParts
                    (sourceNamespaceIdFromDigest (hashBlake2b256 "decoder-admission")) relative
                seed = Identity.opaqueDeclarationSeed owner (localDeclarationOrdinal 0)
                    SignatureDeclaration (generatedObjectSlot 0)
                coreType = iterate (Core.TyArrow Core.TySet) Core.TyProp !! (depth - 1)
                object = if transparent
                    then Identity.transparentObject theory Core.TyProp
                        (iterate Core.CNot Core.CTruth !! (depth - 1))
                    else Identity.opaqueObject theory seed coreType
            closure <- expectRight (Identity.validateObjectClosure theory [object])
            proposition <- expectRight (Identity.validatePropositionContent closure Core.CTruth)
            let fixture = StoreFixture object object proposition
            (_owner, prefix, syntax, semantic, key, artefact, _proposition) <-
                makeCommittedModule theory fixture
            Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
                writer <- Store.newStoreCheck store
                written <- Store.writePendingModulePrefix writer prefix
                if depth <= maximumDepth then do
                    _ <- expectRight written
                    _ <- expectRightIO (Store.writeSealedModule writer key prefix syntax semantic)
                    reader <- Store.newStoreCheck store
                    result <- Store.loadCachedModuleCandidate reader key (Syntax.moduleSyntaxAssertedId syntax)
                    candidate <- maybe (fail "missing cached module") pure =<< expectRight result
                    let objects = Store.cachedCandidateObjects candidate
                    checked <- expectRight (Identity.validateObjectClosure theory objects)
                    _ <- Exception.evaluate (force
                        (Identity.lookupCheckedObjectContent (Identity.assertedObjectId object) checked))
                    assertBool "checked module contains the admitted object" (not (null objects))
                else do
                    assertStoreLimit Store.CanonicalObjects DecoderDepth written
                    assertEmptyPublication path
                    seedCanonicalModule path fixture proposition syntax semantic artefact
                    reader <- Store.newStoreCheck store
                    Store.loadCachedModuleCandidate reader key (Syntax.moduleSyntaxAssertedId syntax)
                        >>= assertStoreLimit Store.CanonicalObjects DecoderDepth
                    Store.writePendingModulePrefix writer prefix
                        >>= assertStoreLimit Store.CanonicalObjects DecoderDepth

propositionDecoderAdmission :: Assertion
propositionDecoderAdmission = do
    let maximumDepth = fromIntegral (maximumDecoderDepth standardDecoderLimits)
    for_ [maximumDepth - 1, maximumDepth, maximumDepth + 1] \depth ->
        withStoreFixture "felix-proposition-admission" \path theory fixture -> do
            closure <- expectRight (Identity.validateObjectClosure theory [])
            proposition <- expectRight (Identity.validatePropositionContent closure
                (iterate Core.CNot Core.CTruth !! (depth - 1)))
            (_owner, prefix, syntax, semantic, key, artefact, _proposition) <-
                makeCommittedModuleWithProposition theory fixture proposition
            Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
                writer <- Store.newStoreCheck store
                written <- Store.writePendingModulePrefix writer prefix
                if depth <= maximumDepth then do
                    expectRight written
                    -- An identical publication must obey the same admission policy.
                    expectRightIO (Store.writePendingModulePrefix writer prefix)
                    void (expectRightIO (Store.writeSealedModule writer key prefix syntax semantic))
                else do
                    assertStoreLimit Store.CanonicalPropositions DecoderDepth written
                    -- Objects inserted earlier in this transaction must roll back too.
                    assertEmptyPublication path
                    seedCanonicalModule path fixture proposition syntax semantic artefact
                    Store.writePendingModulePrefix writer prefix
                        >>= assertStoreLimit Store.CanonicalPropositions DecoderDepth
            Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
                reader <- Store.newStoreCheck store
                loaded <- Store.loadCachedModuleCandidate reader key (Syntax.moduleSyntaxAssertedId syntax)
                if depth <= maximumDepth then do
                    candidate <- maybe (fail "missing module") pure =<< expectRight loaded
                    checked <- expectRight (Identity.validateObjectClosure theory
                        (Store.cachedCandidateObjects candidate))
                    admitted <- traverse (expectRight . Identity.validateStoredPropositionCandidate checked)
                        (Store.cachedCandidatePropositions candidate)
                    (Identity.checkedPropositionTerm <$> admitted) @?= [Identity.checkedPropositionTerm proposition]
                else assertStoreLimit Store.CanonicalPropositions DecoderDepth loaded

seedCanonicalModule :: FilePath -> StoreFixture -> Identity.CheckedPropositionContent
    -> Syntax.ModuleSyntaxInterface -> Semantic.SemanticInterface
    -> Semantic.ModuleArtefactResult -> IO ()
seedCanonicalModule path fixture proposition syntax semantic artefact =
    Exception.bracket (SQLite.open path) SQLite.close \connection -> do
        insertRawObject connection (fixtureFirstObject fixture)
        insertRawProposition connection proposition
        insertRawSyntaxInterface connection syntax
        insertRawSemanticInterface connection semantic
        insertRawModuleArtefact connection artefact

rejectsInconsistentPublication :: Assertion
rejectsInconsistentPublication =
    withStoreFixture "felix-publication-key" \path theory fixture -> do
        (owner, prefix, syntax, semantic, key, _artefact, _proposition) <- makeCommittedModule theory fixture
        otherOwner <- testModuleName "other-publication.tex"
        otherTheory <- expectRight (Cache.decodeCache Identity.getTheoryIdCache (ByteString.replicate 32 0x5a))
        wrongOwner <- makeArtefactKey otherOwner theory "publication-owner"
        wrongTheory <- makeArtefactKey owner otherTheory "publication-theory"
        let direct = [Semantic.semanticInterfaceAssertedId semantic]
        wrongInputs <- makeArtefactKeyWithDirect owner theory direct "publication-inputs"
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            writer <- Store.newStoreCheck store
            for_
                [ (wrongOwner, prefix, Store.StoreModuleArtefactOwnerMismatch otherOwner owner)
                , (wrongTheory, prefix, Store.StoreModuleArtefactTheoryMismatch theory otherTheory)
                , (wrongInputs, prefix, Store.StoreModuleArtefactDirectMismatch direct [])
                , (key, Commit.emptyPendingModulePrefix (Commit.pendingModulePrefixCurrent prefix), Store.StoreModulePrefixMismatch)
                ] \(badKey, badPrefix, expected) -> do
                    result <- Store.writeSealedModule writer badKey badPrefix syntax semantic
                    assertEqual "invalid publication is rejected before any row escapes" (Left expected) result
                    assertEmptyPublication path

syntaxPublicationAdmission :: Assertion
syntaxPublicationAdmission =
    withStoreFixture "felix-syntax-publication-admission" \path theory fixture -> do
        (_owner, prefix, _syntax, semantic, key, _artefact, _proposition) <-
            makeCommittedModule theory fixture
        -- The root itself is canonical but exceeds reconstruction limits.
        delta <- expectRight (Syntax.canonicalSyntaxDelta
            [Syntax.CanonicalStructureOperation
                (fromString (replicate (fromIntegral
                    (maximumDecoderElements standardDecoderLimits) + 1) 'x'))])
        syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            writer <- Store.newStoreCheck store
            let publish = Store.writeSealedModule writer key prefix syntax semantic
            publish >>= assertStoreLimit Store.SyntaxInterfaces DecoderElements
            assertEmptyPublication path
            Exception.bracket (SQLite.open path) SQLite.close \connection ->
                insertRawSyntaxInterface connection syntax
            publish >>= assertStoreLimit Store.SyntaxInterfaces DecoderElements

moduleArtefactDecoderAdmission :: Assertion
moduleArtefactDecoderAdmission =
    withStoreFixture "felix-module-publication-admission" \path theory fixture -> do
        (_owner, _prefix, syntax, semantic, key, artefact, proposition) <-
            makeCommittedModule theory fixture
        certificate <- case Semantic.moduleArtefactResultCertificates artefact of
            [value] -> pure value
            _ -> fail "expected one fixture certificate"
        let oversized = Semantic.moduleArtefactResult key
                (Syntax.moduleSyntaxAssertedId syntax)
                (Semantic.semanticInterfaceAssertedId semantic)
                (replicate (fromIntegral (maximumDecoderListElements standardDecoderLimits) + 1) certificate)
        -- Production publication derives this inventory from committed batches.
        -- Raw rows still require the independent decoder admission boundary.
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            seedCanonicalModule path fixture proposition syntax semantic oversized
            reader <- Store.newStoreCheck store
            Store.loadCachedModuleCandidate reader key (Syntax.moduleSyntaxAssertedId syntax)
                >>= assertStoreLimit Store.ModuleArtefacts DecoderListElements

assertStoreLimit :: Store.StoreRelation -> DecoderResource
    -> Either Store.StoreFailure value -> Assertion
assertStoreLimit relation resource = \case
    Left (Store.StoreRowResourceLimitExceeded actual failure) -> do
        actual @?= relation
        decoderLimitedResource failure @?= resource
    Left other -> assertFailure ("store admission: " <> show other)
    Right _ -> assertFailure "accepted an inadmissible payload"

assertEmptyPublication :: FilePath -> Assertion
assertEmptyPublication path = Exception.bracket (SQLite.open path) SQLite.close \connection ->
    for_ ["canonical_objects", "canonical_propositions", "proof_validations",
          "declaration_validations", "syntax_interfaces", "semantic_interfaces", "module_artefacts"] \table -> do
        rows <- SQLite.query_ connection (SQLite.Query ("SELECT count(*) FROM " <> table))
            :: IO [Only Int]
        assertEqual ("publication rolled back " <> show table) [Only 0] rows

semanticDecoderAdmission :: Assertion
semanticDecoderAdmission = withStoredByteCases \connection rows ->
    for_ (filter ((== Store.SemanticInterfaces) . byteCaseRelation) rows) \row -> do
        originals <- SQLite.query connection
            "SELECT payload FROM semantic_interfaces WHERE semantic_interface_id = ?"
            (Only (byteCaseKey row)) :: IO [Only ByteString.ByteString]
        original <- case originals of
            [Only bytes] -> pure bytes
            _ -> fail "expected one semantic fixture"
        let update bytes = SQLite.execute connection
                "UPDATE semantic_interfaces SET payload = ? WHERE semantic_interface_id = ?"
                (bytes, byteCaseKey row)
            owner = Cache.putMathematicalDigestCache (hashBlake2b256 "admission-owner")
                >> Cache.putCacheText "depth.tex"
            emptyList = Put.putWord64be 0
            -- A semantic-interface prefix ending inside its first structure
            -- preamble. The omitted tail is intentionally not validated once
            -- the recursive term exceeds the enclosing row's allowance.
            payload depth = Cache.encodeCache do
                owner
                emptyList
                Put.putWord64be 1
                owner
                Cache.putCacheNatural 0
                sequence_ (replicate 12 emptyList)
                emptyList -- environment bindings
                Put.putWord64be 1 -- structures
                Cache.putCacheNatural 0 -- structure slot
                emptyList -- parameters
                Put.putWord64be 1 -- preamble
                sequence_ (replicate 3 (Cache.putCacheNatural 0))
                Cache.putCanonicalTermCache Identity.putObjectIdCache
                    (iterate Core.CNot Core.CTruth !! (depth - 1))
            -- Declarations, structures and preambles each retain one level.
            boundary = fromIntegral (maximumDecoderDepth standardDecoderLimits) - 3
        for_ [boundary - 1, boundary, boundary + 1] \depth ->
            Exception.bracket_ (update (payload depth)) (update original) do
                byteCaseRead row >>= \case
                    Left (Store.StoreRowResourceLimitExceeded Store.SemanticInterfaces failure)
                        | depth > boundary -> decoderLimitedResource failure @?= DecoderDepth
                    Left Store.StoreRowDecodeFailure{}
                        | depth <= boundary -> pure () -- reaches the deliberately omitted tail
                    other -> assertFailure ("semantic admission boundary: " <> show other)

data StoredByteCase = StoredByteCase
    { byteCaseRelation :: Store.StoreRelation
    , byteCaseTable :: Text
    , byteCaseKeyColumn :: Text
    , byteCaseKey :: ByteString.ByteString
    , byteCaseRead :: IO (Either Store.StoreFailure ())
    , byteCaseWrite :: IO (Either Store.StoreFailure ())
    }

withStoredByteCases :: (SQLite.Connection -> [StoredByteCase] -> Assertion) -> Assertion
withStoredByteCases action =
    withStoreFixture "felix-store-byte-guards" \path theory fixture ->
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            (_owner, prefix, syntax, semantic, key, artefact, proposition) <-
                makeCommittedModuleWithDeclaration True theory fixture (fixtureProposition fixture)
            let fresh :: (Store.StoreCheck -> IO (Either Store.StoreFailure value))
                    -> IO (Either Store.StoreFailure ())
                fresh operation = do
                    check <- Store.newStoreCheck store
                    void <$> operation check
                writeModule = fresh \check ->
                    Store.writeSealedModule check key prefix syntax semantic
                readModule = fresh \check ->
                    Store.loadCachedModuleCandidate check key (Syntax.moduleSyntaxAssertedId syntax)
                payloadCase relation table keyColumn encodedKey readRow =
                    StoredByteCase relation table keyColumn encodedKey readRow writeModule
            expectRightIO writeModule
            (parsedKey, parsed, _unequal) <- makeParsedArtefacts
            _ <- expectRightIO (Store.writeParsedArtefact store parsed)
            proofKey <- case concatMap Commit.committedBatchProofValidations
                    (Commit.pendingModulePrefixBatches prefix) of
                [proof] -> pure (Semantic.proofValidationRecordKey proof)
                _ -> fail "byte-guard fixture must have one proof validation"
            declarationKey <- case catMaybes
                    (Commit.committedBatchDeclarationValidation <$>
                        Commit.pendingModulePrefixBatches prefix) of
                [declaration] -> pure (Semantic.declarationValidationRecordKey declaration)
                _ -> fail "byte-guard fixture must have one declaration validation"
            let cases =
                    [ payloadCase Store.CanonicalObjects "canonical_objects" "object_id"
                        (Cache.encodeCache (Identity.putObjectIdCache
                            (Identity.assertedObjectId (fixtureFirstObject fixture)))) readModule
                    , payloadCase Store.CanonicalPropositions "canonical_propositions" "proposition_id"
                        (Cache.encodeCache (Identity.putPropositionIdCache
                            (Identity.checkedPropositionId proposition))) readModule
                    , payloadCase Store.ProofValidations "proof_validations" "validation_key"
                        (Cache.cacheDigestBytes (Semantic.proofValidationKeyDigest proofKey))
                        (fresh (\check -> Store.loadProofValidation check proofKey))
                    , payloadCase Store.DeclarationValidations "declaration_validations" "validation_key"
                        (Cache.cacheDigestBytes (Semantic.declarationValidationKeyDigest declarationKey))
                        (fresh (\check -> Store.loadDeclarationValidation check declarationKey))
                    , payloadCase Store.SyntaxInterfaces "syntax_interfaces" "syntax_interface_id"
                        (Cache.cacheDigestBytes (Syntax.syntaxInterfaceIdDigest
                            (Syntax.moduleSyntaxAssertedId syntax))) readModule
                    , payloadCase Store.SemanticInterfaces "semantic_interfaces" "semantic_interface_id"
                        (Cache.cacheDigestBytes (Semantic.semanticInterfaceIdDigest
                            (Semantic.semanticInterfaceAssertedId semantic))) readModule
                    , payloadCase Store.ModuleArtefacts "module_artefacts" "module_artefact_id"
                        (Cache.cacheDigestBytes (Semantic.moduleArtefactIdDigest
                            (Semantic.moduleArtefactResultId artefact))) readModule
                    , StoredByteCase Store.ParsedArtefacts "parsed_artefacts" "parsed_module_key"
                        (Cache.cacheDigestBytes (Parsed.parsedModuleKeyDigest parsedKey))
                        (void <$> Store.loadParsedArtefact store anonymousSourceDescriptor parsedKey)
                        (void <$> Store.writeParsedArtefact store parsed)
                    ]
            Exception.bracket (SQLite.open path) SQLite.close \connection -> do
                SQLite.execute_ connection "PRAGMA foreign_keys = OFF"
                SQLite.execute_ connection "PRAGMA ignore_check_constraints = ON"
                action connection cases

withDamagedByteColumn
    :: SQLite.Connection -> StoredByteCase -> Text -> Text -> Assertion -> Assertion
withDamagedByteColumn connection row column expression action = do
    let suffix = " FROM " <> byteCaseTable row <> " WHERE " <> byteCaseKeyColumn row <> " = ?"
        update value = SQLite.Query
            ("UPDATE " <> byteCaseTable row <> " SET " <> column <> " = " <> value
                <> " WHERE " <> byteCaseKeyColumn row <> " = ?")
    originals <- SQLite.query connection (SQLite.Query ("SELECT " <> column <> suffix))
        (Only (byteCaseKey row)) :: IO [Only ByteString.ByteString]
    original <- case originals of
        [Only bytes] -> pure bytes
        _ -> fail "byte-guard fixture must select exactly one original row"
    Exception.bracket_
        (SQLite.execute connection (update expression) (Only (byteCaseKey row)))
        (SQLite.execute connection (update "?") (original, byteCaseKey row))
        action

guardsStoredPayloads :: Assertion
guardsStoredPayloads = withStoredByteCases \connection rows ->
    for_ rows \row -> do
        for_ ["'not-a-blob'", "123", "0.5"] \expression ->
            withDamagedByteColumn connection row "payload" expression do
                byteCaseRead row >>= assertColumnDecodeFailure (byteCaseRelation row)
                byteCaseWrite row >>= assertColumnDecodeFailure (byteCaseRelation row)
        withDamagedByteColumn connection row "payload" "zeroblob(16777217)" do
            byteCaseRead row >>= assertPayloadLimit (byteCaseRelation row)
            byteCaseWrite row >>= assertPayloadLimit (byteCaseRelation row)
        for_ ["zeroblob(16777216)", "X'ff'"] \expression ->
            withDamagedByteColumn connection row "payload" expression do
                byteCaseRead row >>= \case
                    -- All-zero term rows reach the existing digest check.
                    Left Store.StoreTermReentryFailure{}
                        | byteCaseRelation row `elem`
                            [Store.CanonicalObjects, Store.CanonicalPropositions] -> pure ()
                    result -> assertColumnDecodeFailure (byteCaseRelation row) result
                byteCaseWrite row >>= \case
                    Left (Store.StoreRowPayloadMismatch relation _) ->
                        relation @?= byteCaseRelation row
                    other -> assertFailure
                        ("admitted-size comparison for " <> show (byteCaseRelation row) <> ": " <> show other)
  where
    assertPayloadLimit expected = \case
        Left (Store.StoreBlobResourceLimitExceeded relation actual limit) -> do
            relation @?= expected
            actual @?= Store.maximumStoreBlobBytes + 1
            limit @?= Store.maximumStoreBlobBytes
        other -> assertFailure ("payload resource classification: " <> show other)

guardsStoredIdentities :: Assertion
guardsStoredIdentities = withStoredByteCases \connection rows ->
    for_ rows \row ->
        for_ (identityColumns (byteCaseRelation row)) \column ->
            for_ ["'not-a-blob'", "123", "0.5", "zeroblob(31)", "zeroblob(33)",
                    "zeroblob(67108864)"] \expression ->
                withDamagedByteColumn connection row column expression do
                    byteCaseRead row >>= assertColumnDecodeFailure (byteCaseRelation row)
                    byteCaseWrite row >>= assertColumnDecodeFailure (byteCaseRelation row)
  where
    identityColumns = \case
        Store.ModuleArtefacts -> ["syntax_interface_id", "semantic_interface_id"]
        Store.ParsedArtefacts -> ["parsed_module_id"]
        _ -> []

assertColumnDecodeFailure :: Store.StoreRelation -> Either Store.StoreFailure () -> Assertion
assertColumnDecodeFailure expected = \case
    Left (Store.StoreRowDecodeFailure relation _ _) -> relation @?= expected
    other -> assertFailure ("column decode classification for " <> show expected <> ": " <> show other)

guardsCompatibilityIdentity :: Assertion
guardsCompatibilityIdentity =
    for_ ["'not-a-blob'", "123", "0.5", "NULL", "zeroblob(31)",
            "zeroblob(33)", "zeroblob(67108864)"] \expression ->
        withStoreFixture "felix-store-compatibility-guard" \path theory _fixture -> do
            Exception.bracket (SQLite.open path) SQLite.close \connection -> do
                SQLite.execute_ connection
                    "CREATE TABLE store_compatibility (singleton INTEGER, cache_epoch, theory_id)"
                SQLite.execute_ connection (SQLite.Query
                    ("INSERT INTO store_compatibility VALUES (1, 111, " <> expression <> ")"))
            Store.openStore path theory >>= \case
                Left (Store.IncompatibleStore Store.StoreCompatibilityMalformed{}) -> pure ()
                Left other -> assertFailure ("compatibility byte classification: " <> show other)
                Right (_, store) -> Store.closeStore store >> assertFailure "damaged compatibility was accepted"

roundTripsExactParsedArtefacts :: Assertion
roundTripsExactParsedArtefacts =
    withStoreFixture "felix-store-parsed" \path theory _fixture -> do
        (_startup, store) <- expectOpen path theory
        (key, artefact, unequal) <- makeParsedArtefacts
        assertEqual "initial exact lookup misses" (Right Nothing)
            . fmap (fmap ParsedPayload.decodedParsedArtefact)
            =<< Store.loadParsedArtefact store anonymousSourceDescriptor key
        assertEqual "published parsed artefact"
            (Right artefact)
            =<< Store.writeParsedArtefact store artefact
        assertEqual "exact parsed round trip"
            (Right (Just artefact))
            . fmap (fmap ParsedPayload.decodedParsedArtefact)
            =<< Store.loadParsedArtefact store anonymousSourceDescriptor key
        assertEqual "equal publication is idempotent"
            (Right artefact)
            =<< Store.writeParsedArtefact store artefact
        Store.writeParsedArtefact store unequal >>= \case
            Left Store.StoreRowPayloadMismatch{} ->
                pure ()
            other ->
                assertFailure
                    ("unexpected unequal parsed publication: " <> show other)
        Store.closeStore store

wideParsedArtefact :: Int -> IO ParsedPayload.ParsedArtefact
wideParsedArtefact count = do
    key <- expectRight (Parsed.parsedModuleKey
        (Content.sourceContentIdBytes "wide-parsed-source") Syntax.baseSyntaxInterfaceId [])
    delta <- expectRight (Syntax.canonicalSyntaxDelta [])
    syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
    pure (ParsedPayload.parsedArtefact key (ParsedPayload.canonicalParsedPayload []
        (replicate count (Raw.BlockAxiom Nowhere Nothing "wide" (Raw.Axiom []
            (Raw.StmtFormula (Raw.PropositionalConstant Nowhere Raw.IsTop)))))
        [] (Syntax.moduleSyntaxAssertedId syntax)))

resumesLargeParsedArtefact :: Assertion
resumesLargeParsedArtefact =
    withStoreFixture "felix-store-large-parsed" \path theory _fixture -> do
        -- A shallow, sub-MiB payload with more work than the observed 300,114
        -- node row: the old 262,144-node policy admitted its write but not load.
        artefact <- wideParsedArtefact 14000
        let key = ParsedPayload.parsedArtefactKey artefact
            bytes = ParsedPayload.canonicalParsedPayloadBytes (ParsedPayload.parsedArtefactPayload artefact)
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            Store.writeParsedArtefact store artefact >>= (@?= Right artefact)
            Store.writeParsedArtefact store artefact >>= (@?= Right artefact)
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            decoded <- maybe (fail "missing parsed row after reopen") pure
                =<< expectRightIO (Store.loadParsedArtefact store anonymousSourceDescriptor key)
            _ <- Exception.evaluate (force decoded)
            ParsedPayload.decodedParsedArtefact decoded @?= artefact
            let reconstructed = ParsedPayload.canonicalParsedPayload
                    (ParsedPayload.decodedParsedImports decoded) (ParsedPayload.decodedParsedBlocks decoded)
                    (ParsedPayload.decodedParsedOccurrences decoded) (ParsedPayload.decodedParsedSyntaxInterface decoded)
            ParsedPayload.canonicalParsedPayloadBytes reconstructed @?= bytes
        (_, usage) <- expectRight (ParsedPayload.decodedParsedArtefactFromBytesWithLimits
            standardDecoderLimits anonymousSourceDescriptor key bytes)
        assertBool "fixture exceeds the observed failing row" (decoderUsedNodes usage > 300114)
        assertBool "fixture stays below 1 MiB" (ByteString.length bytes < 1024 * 1024)

rejectsParsedNodePublication :: Assertion
rejectsParsedNodePublication =
    withStoreFixture "felix-store-parsed-nodes" \path theory _fixture ->
        Exception.bracket (snd <$> expectOpen path theory) Store.closeStore \store -> do
            artefact <- wideParsedArtefact 50000
            rejectsParsedPublication path store DecoderNodes artefact

loadsParsedArtefactLocations :: Assertion
loadsParsedArtefactLocations =
    withStoreFixture "felix-store-parsed-locations" $ \path theory _fixture -> do
        (_startup, store) <- expectOpen path theory
        (key, _original, _unequal) <- makeParsedArtefacts
        let firstFile = sourceDescriptorForPath (path <> "-first.tex")
        let secondFile = sourceDescriptorForPath (path <> "-second.tex")
        delta <- expectRight (Syntax.canonicalSyntaxDelta [])
        syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
        let expected descriptor = do
                let location = mkLocation descriptor 7 3
                    nestedLocation = mkLocation descriptor 8 5
                reference <- expectRight (importRef location "parent.tex")
                pure (ParsedPayload.freshParsedArtefact key
                    [reference]
                    [ Raw.BlockAxiom location Nothing "located"
                        (Raw.Axiom []
                            (Raw.StmtFormula
                                (Raw.FormulaSetMap nestedLocation
                                    (Raw.ExprVar "f")
                                    (Raw.ExprVar "A")
                                    (Raw.ExprVar "B"))))
                    , setMapParsedBlock
                    ]
                    [ParsedPayload.parsedSyntaxOccurrence 0 location "located"
                        (Syntax.CanonicalStructureOperation "operation")]
                    (Syntax.moduleSyntaxAssertedId syntax))
        original <- expected firstFile
        let artefact = ParsedPayload.decodedParsedArtefact original
        _ <- expectRightIO (Store.writeParsedArtefact store artefact)
        for_ [secondFile, firstFile] $ \descriptor -> do
            wanted <- expected descriptor
            found <- expectRightIO (Store.loadParsedArtefact store descriptor key)
            case found of
                Nothing -> assertFailure "published parsed artefact was absent"
                Just actual -> do
                    assertEqual "rebinding preserves exact artifact" artefact
                        (ParsedPayload.decodedParsedArtefact actual)
                    assertEqual "imports use the current file"
                        (ParsedPayload.decodedParsedImports wanted)
                        (ParsedPayload.decodedParsedImports actual)
                    assertEqual "nested locations rebind and Nowhere survives"
                        (ParsedPayload.decodedParsedBlocks wanted)
                        (ParsedPayload.decodedParsedBlocks actual)
                    assertEqual "occurrence locations use the current file"
                        (ParsedPayload.decodedParsedOccurrences wanted)
                        (ParsedPayload.decodedParsedOccurrences actual)
                    assertEqual "syntax identity survives loading"
                        (ParsedPayload.decodedParsedSyntaxInterface wanted)
                        (ParsedPayload.decodedParsedSyntaxInterface actual)
        Store.closeStore store

rejectsMalformedParsedPayloads :: Assertion
rejectsMalformedParsedPayloads = do
    check "malformed" (ByteString.singleton 0xff)
    check "noncanonical" . (<> ByteString.singleton 0x00)
        =<< parsedPayloadBytes
  where
    check label corrupted =
        withStoreFixture ("felix-store-parsed-" <> label)
            \path theory _fixture -> do
                (_startup, store) <- expectOpen path theory
                (key, artefact, _unequal) <- makeParsedArtefacts
                _ <- expectRightIO
                    (Store.writeParsedArtefact store artefact)
                Store.closeStore store
                updateParsedPayload path key corrupted
                (_reopened, current) <- expectOpen path theory
                Store.loadParsedArtefact current anonymousSourceDescriptor key >>= \case
                    Left Store.StoreRowDecodeFailure{} ->
                        pure ()
                    other ->
                        assertFailure
                            ("unexpected " <> label
                                <> " parsed row result: " <> show other)
                Store.closeStore current

    parsedPayloadBytes = do
        (_key, artefact, _unequal) <- makeParsedArtefacts
        pure
            (ParsedPayload.canonicalParsedPayloadBytes
                (ParsedPayload.parsedArtefactPayload artefact))

rejectsDisagreeingParsedArtefactIdentities :: Assertion
rejectsDisagreeingParsedArtefactIdentities =
    withStoreFixture "felix-store-parsed-id" \path theory _fixture -> do
        (_startup, store) <- expectOpen path theory
        (key, artefact, _unequal) <- makeParsedArtefacts
        _ <- expectRightIO (Store.writeParsedArtefact store artefact)
        Store.closeStore store
        connection <- SQLite.open path
        SQLite.execute connection
            ("UPDATE parsed_artefacts SET parsed_module_id = ? "
                <> "WHERE parsed_module_key = ?")
            ( ByteString.replicate 32 0
            , Cache.cacheDigestBytes (Parsed.parsedModuleKeyDigest key)
            )
        SQLite.close connection
        (_reopened, current) <- expectOpen path theory
        Store.loadParsedArtefact current anonymousSourceDescriptor key >>= \case
            Left Store.StoreParsedArtefactIdMismatch ->
                pure ()
            other ->
                assertFailure
                    ("unexpected parsed identity result: " <> show other)
        Store.closeStore current

makeParsedArtefacts
    :: IO
        ( Parsed.ParsedModuleKey
        , ParsedPayload.ParsedArtefact
        , ParsedPayload.ParsedArtefact
        )
makeParsedArtefacts = do
    key <- expectRight
        (Parsed.parsedModuleKey
            (Content.sourceContentIdBytes "parsed-source")
            Syntax.baseSyntaxInterfaceId
            [])
    emptyDelta <- expectRight (Syntax.canonicalSyntaxDelta [])
    emptySyntax <- expectRight (Syntax.moduleSyntaxInterface [] emptyDelta)
    otherDelta <- expectRight
        (Syntax.canonicalSyntaxDelta
            [Syntax.CanonicalStructureOperation "other"])
    otherSyntax <- expectRight
        (Syntax.moduleSyntaxInterface [] otherDelta)
    let payload syntax =
            ParsedPayload.canonicalParsedPayload
                []
                [ setMapParsedBlock
                , parameterizedStructureParsedBlock
                , typedStructureParsedBlock
                , structureAggregateParsedBlock
                , structureReductParsedBlock
                , structureReconstructionParsedBlock
                , constructionParsedBlock
                , exactStructureParsedBlock
                , largeIntegerParsedBlock
                ]
                []
                (Syntax.moduleSyntaxAssertedId syntax)
    pure
        ( key
        , ParsedPayload.parsedArtefact key (payload emptySyntax)
        , ParsedPayload.parsedArtefact key (payload otherSyntax)
        )


setMapParsedBlock :: Raw.Block
setMapParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "set_map_cache"
        (Raw.Axiom
            []
            (Raw.StmtFormula
                (Raw.FormulaSetMap
                    Nowhere
                    (Raw.ExprVar "f")
                    (Raw.ExprVar "A")
                    (Raw.ExprVar "B"))))

parameterizedStructureParsedBlock :: Raw.Block
parameterizedStructureParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "parameterized_structure_cache"
        (Raw.Axiom
            [Raw.AsmLetStruct
                ("M" :| ["N"])
                (Raw.StructNounPhrase []
                    (Raw.StructApplication
                        parameterizedStructurePhrase
                        [Raw.TermExpr (Raw.ExprVar "R")])
                    []
                    Nothing)]
            (Raw.StmtStruct
                (Raw.TermExpr (Raw.ExprVar "M"))
                (Raw.StructNounPhrase []
                    (Raw.StructApplication
                        parameterizedStructurePhrase
                        [Raw.TermExpr (Raw.ExprVar "R")])
                    []
                    Nothing)))

parameterizedStructurePhrase :: Raw.StructPhrase
parameterizedStructurePhrase =
    Raw.LexicalItemSgPl
        (Raw.SgPl
            (Raw.TokenCons (Raw.Word "action")
                (Raw.TokenCons (Raw.Word "over")
                    (Raw.HoleCons Raw.End)))
            (Raw.TokenCons (Raw.Word "actions")
                (Raw.TokenCons (Raw.Word "over")
                    (Raw.HoleCons Raw.End))))
        "parameterized_structure_cache"

typedStructureParsedBlock :: Raw.Block
typedStructureParsedBlock =
    Raw.BlockStruct
        Nowhere
        Nothing
        "typed_structure_cache"
        Raw.StructDefn
            { Raw.structPreamble = []
            , Raw.structPhrase = typedStructureParsedPhrase
            , Raw.structParameters = []
            , Raw.structParents = []
            , Raw.structLabel = "X"
            , Raw.structFields =
                [ Raw.StructField
                    Nowhere
                    [Raw.Word "a", Raw.Word "transition", Raw.Word "map"]
                    (Just "typed_structure_field_cache")
                    (Raw.StructSymbol "fieldMap")
                    (Just
                        (Raw.StmtFormula
                            (Raw.FormulaSetMap
                                Nowhere
                                (Raw.ExprStructOp
                                    Nowhere
                                    (Raw.StructSymbol "fieldMap")
                                    (Just (Raw.ExprVar "X")))
                                (Raw.ExprVar "A")
                                (Raw.ExprVar "A"))))
                ]
            , Raw.structAssumes = []
            }

typedStructureParsedPhrase :: Raw.StructPhrase
typedStructureParsedPhrase =
    Raw.LexicalItemSgPl
        (Raw.SgPl
            (Raw.TokenCons (Raw.Word "typed")
                (Raw.TokenCons (Raw.Word "structure") Raw.End))
            (Raw.TokenCons (Raw.Word "typed")
                (Raw.TokenCons (Raw.Word "structures") Raw.End)))
        "typed_structure_cache"

structureAggregateParsedBlock :: Raw.Block
structureAggregateParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "structure_aggregate_cache"
        (Raw.Axiom
            []
            (Raw.StmtStruct
                (Raw.TermExpr
                    (Raw.ExprStructAggregate
                        Nowhere
                        (Just
                            (Raw.StructApplication
                                typedStructureParsedPhrase
                                []))
                        [ Raw.StructAggregateNamed
                            Nowhere
                            Raw.CarrierSymbol
                            (Raw.ExprVar "A")
                        , Raw.StructAggregateNamed
                            Nowhere
                            (Raw.StructSymbol "fieldMap")
                            (Raw.ExprVar "f")
                        ]))
                (Raw.StructNounPhrase []
                    (Raw.StructApplication typedStructureParsedPhrase [])
                    []
                    Nothing)))

structureReductParsedBlock :: Raw.Block
structureReductParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "structure_reduct_cache"
        (Raw.Axiom
            []
            (Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        ( Raw.ExprStructReduct
                            Nowhere
                            (Raw.StructApplication
                                typedStructureParsedPhrase
                                [])
                            (Raw.ExprVar "T")
                            :| []
                        )
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (Raw.ExprVar "R" :| [])))))

structureReconstructionParsedBlock :: Raw.Block
structureReconstructionParsedBlock =
    Raw.BlockAxiom Nowhere Nothing "structure_reconstruction_cache"
        (Raw.Axiom [] (Raw.StmtFormula (Raw.FormulaChain
            (Raw.ChainBase
                (Raw.ExprStructReconstruction Nowhere
                    (Raw.StructApplication typedStructureParsedPhrase [])
                    (Raw.ExprVar "T")
                    [Raw.StructAggregateNamed Nowhere Raw.CarrierSymbol (Raw.ExprVar "A")]
                    :| [])
                Raw.Positive (Raw.Relation Nowhere Raw.EqSymbol [])
                (Raw.ExprVar "R" :| [])))))

constructionParsedBlock :: Raw.Block
constructionParsedBlock = Raw.BlockConstruction Nowhere Nothing "construction_cache"
    (Raw.Construction [] (Raw.StructApplication typedStructureParsedPhrase [])
        (Raw.SymbolPattern Raw.PairSymbol ["X", "Y"])
        (Raw.ExprStructReconstruction Nowhere
            (Raw.StructApplication typedStructureParsedPhrase []) (Raw.ExprVar "X")
            [Raw.StructAggregateNamed Nowhere Raw.CarrierSymbol (Raw.ExprVar "Y")]))

exactStructureParsedBlock :: Raw.Block
exactStructureParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "exact_structure_cache"
        (Raw.Axiom
            []
            (Raw.StmtExactStruct
                (Raw.TermExpr (Raw.ExprVar "T"))
                (Raw.StructApplication typedStructureParsedPhrase [])))

largeIntegerParsedBlock :: Raw.Block
largeIntegerParsedBlock =
    Raw.BlockAxiom
        Nowhere
        Nothing
        "large_integer_cache"
        (Raw.Axiom
            []
            (Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (Raw.ExprNaturalNumeral
                            Nowhere
                            18446744073709551616 :| [])
                        Raw.Positive
                        (Raw.Relation Nowhere Raw.EqSymbol [])
                        (Raw.ExprOpaqueInteger Nowhere (-1) :| [])))))

updateParsedPayload
    :: FilePath
    -> Parsed.ParsedModuleKey
    -> ByteString.ByteString
    -> IO ()
updateParsedPayload path key payload = do
    connection <- SQLite.open path
    SQLite.execute connection
        ("UPDATE parsed_artefacts SET payload = ? "
            <> "WHERE parsed_module_key = ?")
        ( payload
        , Cache.cacheDigestBytes (Parsed.parsedModuleKeyDigest key)
        )
    SQLite.close connection

rejectsMalformedTypedValidationRows :: Assertion
rejectsMalformedTypedValidationRows =
    withStoreFixture "felix-store-malformed-typed" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        (_owner, prefix, _syntax, _semantic, _key, _artefact, _proposition) <-
            makeCommittedModule theory fixture
        batch <- case Commit.pendingModulePrefixBatches prefix of
            [one] -> pure one
            batches ->
                assertFailure
                    ("unexpected prefix batch count: " <> show (length batches))
                    >> fail "unreachable"
        proof <- case Commit.committedBatchProofValidations batch of
            [one] -> pure one
            proofs ->
                assertFailure
                    ("unexpected proof validation count: " <> show (length proofs))
                    >> fail "unreachable"
        let key = Semantic.proofValidationRecordKey proof
            certificate = Semantic.proofValidationRecordCertificate proof
            theorem = Identity.theoremId
                (Authority.factAuthorityTheorem
                    (Authority.validationTarget certificate))
            wrongKey = Semantic.proofValidationKey
                theorem
                (Semantic.proofSyntaxId "other-row")
                (Commit.committedBatchPreviousPrefix batch)
            wrongProof =
                Semantic.proofValidationRecord wrongKey certificate
        storeCheck <- Store.newStoreCheck store
        expectRightIO (Store.writePendingModulePrefix storeCheck prefix)
        Store.closeStore store
        connection <- SQLite.open path
        SQLite.execute connection
            ("UPDATE proof_validations SET payload = ? "
                <> "WHERE validation_key = ?")
            ( Cache.encodeCache
                (Semantic.putProofValidationRecordCache wrongProof)
            , Cache.cacheDigestBytes
                (Semantic.proofValidationKeyDigest key)
            )
        SQLite.close connection
        (_reopened, current) <- expectOpen path theory
        currentCheck <- Store.newStoreCheck current
        Store.loadProofValidation currentCheck key >>= \case
            Left Store.StoreValidationRecordKeyMismatch{} -> pure ()
            Left other ->
                assertFailure
                    ("unexpected typed key mismatch: " <> show other)
            Right _ ->
                assertFailure "typed key mismatch was accepted"
        Store.closeStore current
        connection' <- SQLite.open path
        SQLite.execute connection'
            ("UPDATE proof_validations SET payload = ? "
                <> "WHERE validation_key = ?")
            ( ByteString.singleton 0xff
            , Cache.cacheDigestBytes
                (Semantic.proofValidationKeyDigest key)
            )
        SQLite.close connection'
        (_reopenedMalformed, malformed) <- expectOpen path theory
        malformedCheck <- Store.newStoreCheck malformed
        Store.loadProofValidation malformedCheck key >>= \case
            Left Store.StoreRowDecodeFailure{} -> pure ()
            Left other ->
                assertFailure
                    ("unexpected malformed typed row: " <> show other)
            Right _ ->
                assertFailure "malformed typed row was accepted"
        Store.closeStore malformed

publishesCompletedPrefixBeforeReadiness :: Assertion
publishesCompletedPrefixBeforeReadiness =
    withStoreFixture "felix-store-prefix" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        (_owner, prefix, syntax, semantic, artefactKey, artefact, proposition) <-
            makeCommittedModule theory fixture
        expectRightIO (Store.writePendingModulePrefix storeCheck prefix)
        connection <- SQLite.open path
        [Only propositionRows] <- SQLite.query connection
            ("SELECT COUNT(*) FROM canonical_propositions "
                <> "WHERE proposition_id = ?")
            (Only
                (Cache.encodeCache
                    (Identity.putPropositionIdCache
                        (Identity.checkedPropositionId proposition))))
            :: IO [Only Int]
        [Only artefactRowsBefore] <- SQLite.query_ connection
            "SELECT COUNT(*) FROM module_artefacts"
            :: IO [Only Int]
        SQLite.close connection
        assertEqual "completed prefix proposition is visible" 1 propositionRows
        assertEqual "prefix publication does not publish readiness"
            0 artefactRowsBefore
        _ <- expectRightIO
            (Store.writeSealedModule storeCheck artefactKey prefix syntax semantic)
        installation <- expectRightIO
            (Store.loadCachedModuleCandidate
                storeCheck
                artefactKey
                (Syntax.moduleSyntaxAssertedId syntax))
        case installation of
            Just loaded -> do
                assertEqual "validated semantic interface" semantic
                    (Store.cachedCandidateSemantic loaded)
                assertEqual "validated imported proposition count" 1
                    (length (Store.cachedCandidatePropositions loaded))
                assertEqual "validated certificate inventory"
                    (Semantic.moduleArtefactResultCertificates artefact)
                    (Store.cachedCandidateCertificates loaded)
            Nothing ->
                assertFailure "validated module installation was absent"
        Store.closeStore store

installsSealedProducerForCachedImporter :: Assertion
installsSealedProducerForCachedImporter =
    withStoreFixture "felix-store-cached-import" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        foundation <- expectRight Foundation.checkedFoundation
        (_owner, prefix, syntax, semantic, artefactKey, _artefact, proposition) <-
            makeCommittedModule theory fixture
        absent <- expectRightIO
            (Store.loadCachedModuleCandidate storeCheck artefactKey
                (Syntax.moduleSyntaxAssertedId syntax))
        assertBool "root is absent before publication" (isNothing absent)
        _ <- expectRightIO
            (Store.writeSealedModule storeCheck artefactKey prefix syntax semantic)
        installation <-
            expectRightIO
                (Store.loadCachedModuleCandidate
                    storeCheck
                    artefactKey
                    (Syntax.moduleSyntaxAssertedId syntax))
            >>= \case
                Nothing ->
                    assertFailure "sealed producer was not loadable"
                        >> fail "unreachable"
                Just loaded ->
                    pure loaded
        emptyImports <- prepareTestImports (Identity.theoryId foundation) []
        cached <- expectRight =<< Typed.cachedSealedTypedModule emptyImports installation
        let loadedSemantic = Store.cachedCandidateSemantic installation
        fingerprint <-
            case concatMap
                    Semantic.declarationDeltaFacts
                    (Semantic.semanticInterfaceDeclarations loadedSemantic) of
                [occurrence] ->
                    pure (Semantic.semanticFactFingerprint occurrence)
                occurrences ->
                    assertFailure
                        ("unexpected cached producer facts: "
                            <> show (length occurrences))
                        >> fail "unreachable"
        let namespaceDigest =
                hashBlake2b256 "store-cached-import-consumer\NULconsumer"
        relative <- expectRight (safeRelativePath "consumer.tex")
        let consumerOwner =
                moduleNameFromParts
                    (sourceNamespaceIdFromDigest namespaceDigest)
                    relative
            resolver = Declaration.vampireResolver \prepared ->
                pure
                    (Provers.processFailedVampireResolution
                        (Provers.preparedTypedProverRequest prepared)
                        (Provers.ProverLaunchFailed
                            "unused"
                            "cached importer does not run Vampire"))
        checkedImports <- prepareTestImports (Identity.theoryId foundation)
            [Typed.sealedTypedModuleEvidence cached]
        result <-
            (Declaration.runModuleDriverFreshIO
                foundation
                consumerOwner
                checkedImports
                resolver
                do
                    (_value, batch) <- DeclTest.admitProof
                        (Semantic.proofSyntaxId "cached-import-consumer") []
                            (Declaration.checkedCandidate (Declaration.candidateSpec
                                    proposition
                                    Semantic.SearchIneligible
                                    [])
                                (Declaration.checkedOmittedPlanning [] [fingerprint] [])) \candidate -> do
                            Declaration.authorizeOmittedCandidate candidate do
                                _ <- Declaration.useAuthorizedFact fingerprint
                                Declaration.recordOmittedUse
                    pure batch
                :: IO
                    (Either
                        Declaration.DriverOpenError
                        (Declaration.DriverResult Text
                            Commit.CommittedDeclarationBatch)))
        case result of
            Left failure ->
                assertFailure ("cached importer could not open: " <> show failure)
            Right (Declaration.DriverSucceeded _ _ _) ->
                pure ()
            Right (Declaration.DriverFailed failure _prefix) ->
                assertFailure ("cached importer failed: " <> show failure)
            Right (Declaration.DriverSealFailed failure _prefix) ->
                assertFailure ("cached importer did not seal: " <> show failure)
        Store.closeStore store

validatesExactCachedInstallationInputs :: Assertion
validatesExactCachedInstallationInputs =
    withStoreFixture "felix-store-exact-install" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        (owner, prefix, syntax, semantic, artefactKey, artefact, proposition) <-
            makeCommittedModule theory fixture
        _ <- expectRightIO
            (Store.writeSealedModule storeCheck artefactKey prefix syntax semantic)
        otherDelta <- expectRight
            (Syntax.canonicalSyntaxDelta
                [Syntax.CanonicalStructureOperation "other-syntax"])
        otherSyntax <- expectRight
            (Syntax.moduleSyntaxInterface [] otherDelta)
        wrongSyntaxCheck <- Store.newStoreCheck store
        Store.loadCachedModuleCandidate
            wrongSyntaxCheck
            artefactKey
            (Syntax.moduleSyntaxAssertedId otherSyntax)
            >>= \case
                Left Store.StoreModuleArtefactSyntaxMismatch{} -> pure ()
                _ ->
                    assertFailure "unexpected syntax-input result"

        parent <- expectRight
            (Semantic.semanticInterface preludeModuleName [] [])
        mismatched <- expectRight
            (Semantic.semanticInterface
                owner
                [Semantic.semanticInterfaceAssertedId parent]
                (Semantic.semanticInterfaceDeclarations semantic))
        mismatchKey <- makeArtefactKey owner theory "direct-mismatch"
        let mismatchArtefact =
                Semantic.moduleArtefactResult
                    mismatchKey
                    (Syntax.moduleSyntaxAssertedId syntax)
                    (Semantic.semanticInterfaceAssertedId mismatched)
                    (Semantic.moduleArtefactResultCertificates artefact)
        writeRawModuleRows
            path
            [fixtureFirstObject fixture]
            [proposition]
            syntax
            [parent, mismatched]
            mismatchArtefact
        directCheck <- Store.newStoreCheck store
        Store.loadCachedModuleCandidate
            directCheck
            mismatchKey
            (Syntax.moduleSyntaxAssertedId syntax)
            >>= \case
                Left Store.StoreModuleArtefactDirectMismatch{} -> pure ()
                _ ->
                    assertFailure "unexpected direct-input result"
        Store.closeStore store

rejectsInvalidCachedRootAuthorityAndClosure :: Assertion
rejectsInvalidCachedRootAuthorityAndClosure =
    withStoreFixture "felix-store-invalid-install" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        (owner, _prefix, syntax, semantic, _artefactKey, originalArtefact, proposition) <-
            makeCommittedModule theory fixture
        otherTheory <- expectRight
            (Cache.decodeCache
                Identity.getTheoryIdCache
                (ByteString.replicate 32 0x5a))
        original <- case Semantic.semanticInterfaceDeclarations semantic of
            [delta] -> pure delta
            deltas ->
                assertFailure
                    ("unexpected declaration count: " <> show (length deltas))
                    >> fail "unreachable"
        occurrence <- case Semantic.declarationDeltaFacts original of
            [fact] -> pure fact
            facts ->
                assertFailure
                    ("unexpected fact count: " <> show (length facts))
                    >> fail "unreachable"
        let badAuthority =
                Authority.factAuthority
                    (Identity.theoremRef
                        otherTheory
                        (Semantic.semanticFactProposition occurrence))
                    (Authority.factAuthoritySafety
                        (Semantic.semanticFactAuthority occurrence))
            badOccurrence =
                Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
                    (Semantic.semanticFactSlot occurrence)
                    badAuthority
                    (Semantic.semanticFactSearchEligibility occurrence)
        badDelta <- expectRight
            (Semantic.declarationInterfaceDelta
                (Semantic.declarationDeltaSlot original)
                [badOccurrence]
                (Semantic.declarationDeltaAliases original)
                (Semantic.declarationDeltaObjects original)
                (Semantic.declarationDeltaPropositions original)
                (Semantic.declarationDeltaDefinitionViews original)
                (Semantic.declarationDeltaRegistrations original)
                (Semantic.declarationDeltaEnvironment original))
        badSemantic <- expectRight
            (Semantic.semanticInterface owner [] [badDelta])
        badKey <- makeArtefactKey owner theory "bad-authority"
        let badArtefact =
                Semantic.moduleArtefactResult
                    badKey
                    (Syntax.moduleSyntaxAssertedId syntax)
                    (Semantic.semanticInterfaceAssertedId badSemantic)
                    (Semantic.moduleArtefactResultCertificates originalArtefact)
        writeRawModuleRows
            path
            [fixtureFirstObject fixture]
            [proposition]
            syntax
            [badSemantic]
            badArtefact
        badCheck <- Store.newStoreCheck store
        badCandidate <- expectRight
            =<< Store.loadCachedModuleCandidate
                badCheck badKey (Syntax.moduleSyntaxAssertedId syntax)
        candidate <- maybe (assertFailure "bad root is absent" >> fail "unreachable")
            pure badCandidate
        checkedImports <- prepareTestImports theory []
        Typed.cachedSealedTypedModule checkedImports candidate >>= \case
                Left (Typed.CachedTypedModuleEvidenceError
                    Declaration.ImportedEvidenceCertificateTargetMismatch{}) -> pure ()
                _ ->
                    assertFailure "unexpected root-authority result"

        childKey <- makeArtefactKey owner theory "missing-late-child"
        let childArtefact =
                Semantic.moduleArtefactResult
                    childKey
                    (Syntax.moduleSyntaxAssertedId syntax)
                    (Semantic.semanticInterfaceAssertedId semantic)
                    (Semantic.moduleArtefactResultCertificates originalArtefact)
        writeRawModuleRows
            path
            [fixtureFirstObject fixture]
            [proposition]
            syntax
            [semantic]
            childArtefact
        connection <- SQLite.open path
        SQLite.execute connection
            "DELETE FROM canonical_objects WHERE object_id = ?"
            (Only
                (Cache.encodeCache
                    (Identity.putObjectIdCache
                        (Identity.assertedObjectId
                            (fixtureFirstObject fixture)))))
        SQLite.close connection
        childCheck <- Store.newStoreCheck store
        Store.loadCachedModuleCandidate
            childCheck childKey (Syntax.moduleSyntaxAssertedId syntax)
            >>= \case
                Left Store.StoreAssertedChildMissing{} -> pure ()
                _ ->
                    assertFailure "unexpected missing-child result"
        Store.closeStore store

rejectsForwardFormationContractsOnReentry :: Assertion
rejectsForwardFormationContractsOnReentry =
    withStoreFixture "felix-store-forward-contract" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        (owner, _prefix, syntax, _semantic, _key, _artefact, _proposition) <-
            makeCommittedModule theory fixture
        let predicateObject = Identity.transparentObject
                theory
                (Core.TyArrow Core.TySet Core.TyProp)
                (Core.CLam Core.TySet Core.CTruth)
            predicate = Identity.assertedObjectId predicateObject
            firstSlot = Semantic.declarationSlot owner
                (localDeclarationOrdinal 0)
            laterSlot = Semantic.declarationSlot owner
                (localDeclarationOrdinal 1)
            wordPattern word = Raw.TokenCons (Raw.Word word) Raw.End
            hostKey = Semantic.SemanticNoun
                (wordPattern "contract-host")
                (wordPattern "contract-hosts")
            requiredKey = Semantic.SemanticNoun
                (wordPattern "contract-requirement")
                (wordPattern "contract-requirements")
            laterReference = Semantic.globalBindingRef laterSlot requiredKey
            requirement = Semantic.GlobalAtomTemplate
                (Semantic.NounNotionHead laterReference)
                (Vector.singleton
                    (Semantic.TemplateVariable
                        (Semantic.OccurrenceArgumentIx 0)))
            hostBinding = Semantic.semanticGlobalBindingWithContract
                hostKey
                (Semantic.semanticBindingLabel "contract-host")
                (Semantic.GlobalReference predicate)
                (Just (Semantic.formationContract (Semantic.AtomicLeaf requirement :| [])))
            requiredBinding = Semantic.semanticGlobalBinding
                requiredKey
                (Semantic.semanticBindingLabel "contract-requirement")
                (Semantic.GlobalReference predicate)
            makeDelta slot objects bindings = do
                environment <- expectRight
                    (Semantic.semanticEnvironmentDelta bindings)
                expectRight
                    (Semantic.declarationInterfaceDelta
                        slot
                        []
                        []
                        objects
                        []
                        []
                        []
                        environment)
        firstDelta <- makeDelta firstSlot [predicate] [hostBinding]
        laterDelta <- makeDelta laterSlot [] [requiredBinding]
        malformed <- expectRight
            (Semantic.semanticInterface owner [] [firstDelta, laterDelta])
        artefactKey <- makeArtefactKey owner theory "forward-contract"
        let artefact = Semantic.moduleArtefactResult
                artefactKey
                (Syntax.moduleSyntaxAssertedId syntax)
                (Semantic.semanticInterfaceAssertedId malformed)
                []
        writeRawModuleRows
            path [predicateObject] [] syntax [malformed] artefact
        storeCheck <- Store.newStoreCheck store
        loaded <- expectRight
            =<< Store.loadCachedModuleCandidate
                storeCheck artefactKey (Syntax.moduleSyntaxAssertedId syntax)
        candidate <- maybe (assertFailure "forward-contract root is absent" >> fail "unreachable")
            pure loaded
        checkedImports <- prepareTestImports theory []
        Typed.cachedSealedTypedModule checkedImports candidate >>= \case
                Left (Typed.CachedTypedModuleEvidenceError
                    (Declaration.GlobalFormationContractInvalid
                        actualHost
                        (Semantic.FormationContractGlobalBindingMissing
                            actualRequired))) -> do
                    assertEqual "forward contract host"
                        (Semantic.globalBindingRef firstSlot hostKey)
                        actualHost
                    assertEqual "forward contract requirement"
                        laterReference actualRequired
                Left failure ->
                    assertFailure
                        ("unexpected forward-contract re-entry result: "
                            <> show failure)
                Right _ ->
                    assertFailure
                        "forward contract survived cached admission"
        Store.closeStore store

rejectsDisagreeingModuleArtefactColumns :: Assertion
rejectsDisagreeingModuleArtefactColumns =
    withStoreFixture "felix-store-artefact-columns" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        (_owner, prefix, syntax, semantic, key, artefact, _proposition) <-
            makeCommittedModule theory fixture
        _ <- expectRightIO
            (Store.writeSealedModule storeCheck key prefix syntax semantic)
        connection <- SQLite.open path
        SQLite.execute_ connection "PRAGMA foreign_keys = OFF"
        SQLite.execute connection
            ("UPDATE module_artefacts SET syntax_interface_id = ? "
                <> "WHERE module_artefact_id = ?")
            ( ByteString.replicate 32 0x3c
            , Cache.cacheDigestBytes
                (Semantic.moduleArtefactIdDigest
                    (Semantic.moduleArtefactResultId artefact))
            )
        SQLite.close connection
        Store.loadCachedModuleCandidate
            storeCheck
            key
            (Syntax.moduleSyntaxAssertedId syntax)
            >>= \case
                Left Store.StoreModuleArtefactColumnsMismatch -> pure ()
                Left other ->
                    assertFailure
                        ("unexpected artefact-column load: " <> show other)
                Right _ ->
                    assertFailure "disagreeing artefact columns were accepted"
        Store.writeSealedModule storeCheck key prefix syntax semantic >>= \case
            Left Store.StoreRowPayloadMismatch{} -> pure ()
            other ->
                assertFailure
                    ("unexpected artefact-column rewrite: " <> show other)
        Store.closeStore store

validatesSharedClosuresOncePerCheck :: Assertion
validatesSharedClosuresOncePerCheck =
    withStoreFixture "felix-store-linear-closure" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        let baseObject = fixtureFirstObject fixture
            first = transparentSetObject theory baseObject
            second = transparentSetObject theory first
            third = transparentSetObject theory second
            native = nativeLogicalObject theory third
            objects = [baseObject, first, second, third, native]
        closure <- expectRight
            (Identity.validateObjectClosure theory objects)
        proposition <- expectRight
            (Identity.validatePropositionContent
                closure
                (Core.CGlobal (Identity.assertedObjectId native)))
        baseOwner <- testModuleName "linear-base.tex"
        leftOwner <- testModuleName "linear-left.tex"
        rightOwner <- testModuleName "linear-right.tex"
        rootOwner <- testModuleName "linear-root.tex"
        let theorem = Identity.theoremRef
                theory
                (Identity.checkedPropositionId proposition)
            occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
                (Semantic.factSlot baseOwner (localFactOrdinal 0))
                (Authority.factAuthority
                    theorem Authority.cleanAuthoritySafety)
                Semantic.SearchEligible
        baseDelta <- expectRight
            (Semantic.declarationInterfaceDelta
                (Semantic.declarationSlot
                    baseOwner
                    (localDeclarationOrdinal 0))
                [occurrence]
                []
                (Identity.assertedObjectId <$> objects)
                [Identity.checkedPropositionId proposition]
                []
                []
                Semantic.emptySemanticEnvironmentDelta)
        baseSemantic <- expectRight
            (Semantic.semanticInterface baseOwner [] [baseDelta])
        leftSemantic <- expectRight
            (Semantic.semanticInterface
                leftOwner
                [Semantic.semanticInterfaceAssertedId baseSemantic]
                [])
        rightSemantic <- expectRight
            (Semantic.semanticInterface
                rightOwner
                [Semantic.semanticInterfaceAssertedId baseSemantic]
                [])
        rootSemantic <- expectRight
            (Semantic.semanticInterface
                rootOwner
                [ Semantic.semanticInterfaceAssertedId leftSemantic
                , Semantic.semanticInterfaceAssertedId rightSemantic
                ]
                [])

        emptyDelta <- expectRight (Syntax.canonicalSyntaxDelta [])
        leftDelta <- expectRight
            (Syntax.canonicalSyntaxDelta
                [Syntax.CanonicalStructureOperation "linear-left"])
        rightDelta <- expectRight
            (Syntax.canonicalSyntaxDelta
                [Syntax.CanonicalStructureOperation "linear-right"])
        baseSyntax <- expectRight
            (Syntax.moduleSyntaxInterface [] emptyDelta)
        leftSyntax <- expectRight
            (Syntax.moduleSyntaxInterface
                [Syntax.moduleSyntaxAssertedId baseSyntax]
                leftDelta)
        rightSyntax <- expectRight
            (Syntax.moduleSyntaxInterface
                [Syntax.moduleSyntaxAssertedId baseSyntax]
                rightDelta)
        rootSyntax <- expectRight
            (Syntax.moduleSyntaxInterface
                [ Syntax.moduleSyntaxAssertedId leftSyntax
                , Syntax.moduleSyntaxAssertedId rightSyntax
                ]
                emptyDelta)

        rootKey <- makeArtefactKeyWithDirect
            rootOwner
            theory
            [ Semantic.semanticInterfaceAssertedId leftSemantic
            , Semantic.semanticInterfaceAssertedId rightSemantic
            ]
            "linear-root"
        leftKey <- makeArtefactKeyWithDirect
            leftOwner
            theory
            [Semantic.semanticInterfaceAssertedId baseSemantic]
            "linear-left"
        let rootArtefact = Semantic.moduleArtefactResult
                rootKey
                (Syntax.moduleSyntaxAssertedId rootSyntax)
                (Semantic.semanticInterfaceAssertedId rootSemantic)
                []
            leftArtefact = Semantic.moduleArtefactResult
                leftKey
                (Syntax.moduleSyntaxAssertedId leftSyntax)
                (Semantic.semanticInterfaceAssertedId leftSemantic)
                []
        connection <- SQLite.open path
        SQLite.withTransaction connection do
            traverse_ (insertRawObject connection) objects
            insertRawProposition connection proposition
            traverse_
                (insertRawSyntaxInterface connection)
                [baseSyntax, leftSyntax, rightSyntax, rootSyntax]
            traverse_
                (insertRawSemanticInterface connection)
                [baseSemantic, leftSemantic, rightSemantic, rootSemantic]
            insertRawModuleArtefact connection rootArtefact
            insertRawModuleArtefact connection leftArtefact
        SQLite.close connection

        storeCheck <- Store.newStoreCheck store
        expectInstallation storeCheck rootKey rootSyntax
        expectInstallation storeCheck leftKey leftSyntax
        expectInstallation storeCheck rootKey rootSyntax
        visits <- Store.storeCheckMemoVisits storeCheck
        assertEqual "unique artefact rows" 2
            (Store.storeArtefactRowsDecoded visits)
        assertEqual "syntax diamond rows" 4
            (Store.storeSyntaxRowsDecoded visits)
        assertEqual "syntax diamond validations" 4
            (Store.storeSyntaxRowsValidated visits)
        assertEqual "only requested local semantic rows" 2
            (Store.storeSemanticRowsDecoded visits)
        assertEqual "ancestor objects are not decoded" 0
            (Store.storeObjectRowsDecoded visits)
        assertEqual "ancestor propositions are not decoded" 0
            (Store.storePropositionRowsDecoded visits)
        Store.closeStore store
  where
    expectInstallation storeCheck key syntax =
        Store.loadCachedModuleCandidate
            storeCheck key (Syntax.moduleSyntaxAssertedId syntax)
            >>= \case
                Right (Just _installation) -> pure ()
                _ -> assertFailure "cached closure installation failed"

transparentSetObject
    :: Identity.TheoryId
    -> Identity.AssertedObject
    -> Identity.AssertedObject
transparentSetObject theory dependency =
    Identity.transparentObject
        theory
        Core.TySet
        (Core.CGlobal (Identity.assertedObjectId dependency))

nativeLogicalObject
    :: Identity.TheoryId
    -> Identity.AssertedObject
    -> Identity.AssertedObject
nativeLogicalObject theory dependency =
    Identity.transparentObject theory Core.TyProp body
  where
    dependencyTerm =
        Core.CGlobal (Identity.assertedObjectId dependency)
    body =
        Core.CExists Core.TySet
            (Core.CAnd
                Core.CTruth
                (Core.COr
                    (Core.CNot Core.CFalsum)
                    (Core.CEq
                        Core.TySet
                        dependencyTerm
                        dependencyTerm)))

testModuleName :: FilePath -> IO ModuleName
testModuleName path = do
    let digest =
            hashBlake2b256
                ("store-linear-module\NUL" <> ByteString.Char8.pack path)
    relative <- expectRight (safeRelativePath path)
    pure
        (moduleNameFromParts
            (sourceNamespaceIdFromDigest digest)
            relative)

makeArtefactKey
    :: ModuleName
    -> Identity.TheoryId
    -> ByteString.ByteString
    -> IO Semantic.ModuleArtefactKey
makeArtefactKey owner theory label = do
    makeArtefactKeyWithDirect owner theory [] label

makeArtefactKeyWithDirect
    :: ModuleName
    -> Identity.TheoryId
    -> [Semantic.SemanticInterfaceId]
    -> ByteString.ByteString
    -> IO Semantic.ModuleArtefactKey
makeArtefactKeyWithDirect owner theory direct label = do
    parsedKey <- expectRight
        (Parsed.parsedModuleKey
            (Content.sourceContentIdBytes label)
            Syntax.baseSyntaxInterfaceId
            [])
    expectRight
        (Semantic.moduleArtefactKey
            owner
            (Parsed.parsedModuleId parsedKey label)
            direct
            theory)

writeRawModuleRows
    :: FilePath
    -> [Identity.AssertedObject]
    -> [Identity.CheckedPropositionContent]
    -> Syntax.ModuleSyntaxInterface
    -> [Semantic.SemanticInterface]
    -> Semantic.ModuleArtefactResult
    -> IO ()
writeRawModuleRows path objects propositions syntax semantics artefact = do
    connection <- SQLite.open path
    SQLite.withTransaction connection do
        traverse_ (insertRawObject connection) objects
        traverse_ (insertRawProposition connection) propositions
        insertRawSyntaxInterface connection syntax
        traverse_ (insertRawSemanticInterface connection) semantics
        insertRawModuleArtefact connection artefact
    SQLite.close connection

insertRawObject :: SQLite.Connection -> Identity.AssertedObject -> IO ()
insertRawObject connection object = do
    payload <- rawObjectPayload connection object
    SQLite.execute connection
        ("INSERT OR IGNORE INTO canonical_objects (object_id, payload) "
            <> "VALUES (?, ?)")
        ( Cache.encodeCache
            (Identity.putObjectIdCache
                (Identity.assertedObjectId object))
        , payload
        )

rawObjectPayload
    :: SQLite.Connection
    -> Identity.AssertedObject
    -> IO ByteString.ByteString
rawObjectPayload _connection object =
    pure
        (case Identity.assertedObjectContent object of
            Identity.IntrinsicObjectContent _theory tag ->
                Cache.encodeCache (Cache.putCoreIntrinsicTagCache tag)
            Identity.TransparentObjectContent _theory coreType body ->
                Cache.encodeCache do
                    Cache.putCoreTypeCache coreType
                    Cache.putCacheBytes
                        (encodeCanonicalTerm
                            Identity.objectIdBuilder body)
            Identity.OpaqueObjectContent _theory seed coreType ->
                Cache.encodeCache do
                    Identity.putOpaqueDeclarationSeedCache seed
                    Cache.putCoreTypeCache coreType)

insertRawProposition
    :: SQLite.Connection
    -> Identity.CheckedPropositionContent
    -> IO ()
insertRawProposition connection proposition = do
    payload <- rawPropositionPayload connection proposition
    SQLite.execute connection
        ("INSERT OR IGNORE INTO canonical_propositions "
            <> "(proposition_id, payload) VALUES (?, ?)")
        ( Cache.encodeCache
            (Identity.putPropositionIdCache
                (Identity.checkedPropositionId proposition))
        , payload
        )

rawPropositionPayload
    :: SQLite.Connection
    -> Identity.CheckedPropositionContent
    -> IO ByteString.ByteString
rawPropositionPayload _connection proposition =
    pure
        (encodeCanonicalTerm
            Identity.objectIdBuilder
            (Core.frozenCoreTerm
                (Identity.checkedPropositionTerm proposition)))


insertRawSyntaxInterface
    :: SQLite.Connection
    -> Syntax.ModuleSyntaxInterface
    -> IO ()
insertRawSyntaxInterface connection interface =
    SQLite.execute connection
        ("INSERT OR IGNORE INTO syntax_interfaces "
            <> "(syntax_interface_id, payload) VALUES (?, ?)")
        ( Cache.cacheDigestBytes
            (Syntax.syntaxInterfaceIdDigest
                (Syntax.moduleSyntaxAssertedId interface))
        , Cache.encodeCache
            (Syntax.putModuleSyntaxInterfaceCache interface)
        )

insertRawSemanticInterface
    :: SQLite.Connection
    -> Semantic.SemanticInterface
    -> IO ()
insertRawSemanticInterface connection interface =
    SQLite.execute connection
        ("INSERT OR IGNORE INTO semantic_interfaces "
            <> "(semantic_interface_id, payload) VALUES (?, ?)")
        ( Cache.cacheDigestBytes
            (Semantic.semanticInterfaceIdDigest
                (Semantic.semanticInterfaceAssertedId interface))
        , Cache.encodeCache
            (Semantic.putSemanticInterfaceCache interface)
        )

insertRawModuleArtefact
    :: SQLite.Connection
    -> Semantic.ModuleArtefactResult
    -> IO ()
insertRawModuleArtefact connection artefact =
    SQLite.execute connection
        ("INSERT OR IGNORE INTO module_artefacts "
            <> "(module_artefact_id, syntax_interface_id, "
            <> "semantic_interface_id, payload) VALUES (?, ?, ?, ?)")
        ( Cache.cacheDigestBytes
            (Semantic.moduleArtefactIdDigest
                (Semantic.moduleArtefactResultId artefact))
        , Cache.cacheDigestBytes
            (Syntax.syntaxInterfaceIdDigest
                (Semantic.moduleArtefactResultSyntax artefact))
        , Cache.cacheDigestBytes
            (Semantic.semanticInterfaceIdDigest
                (Semantic.moduleArtefactResultSemantic artefact))
        , Cache.encodeCache
            (Semantic.putModuleArtefactResultCache artefact)
        )

storedPropositionCount
    :: FilePath
    -> Identity.PropositionId
    -> IO Int
storedPropositionCount path identity = do
    connection <- SQLite.open path
    [Only rowCount] <- SQLite.query connection
        ("SELECT COUNT(*) FROM canonical_propositions "
            <> "WHERE proposition_id = ?")
        (Only
            (Cache.encodeCache
                (Identity.putPropositionIdCache identity)))
    SQLite.close connection
    pure rowCount

storedObjectCount
    :: FilePath
    -> Identity.ObjectId
    -> IO Int
storedObjectCount path identity = do
    connection <- SQLite.open path
    [Only rowCount] <- SQLite.query connection
        "SELECT COUNT(*) FROM canonical_objects WHERE object_id = ?"
        (Only
            (Cache.encodeCache
                (Identity.putObjectIdCache identity)))
    SQLite.close connection
    pure rowCount

storedArtefactCount
    :: FilePath
    -> Semantic.ModuleArtefactId
    -> IO Int
storedArtefactCount path identity = do
    connection <- SQLite.open path
    [Only rowCount] <- SQLite.query connection
        ("SELECT COUNT(*) FROM module_artefacts "
            <> "WHERE module_artefact_id = ?")
        (Only
            (Cache.cacheDigestBytes
                (Semantic.moduleArtefactIdDigest identity)))
    SQLite.close connection
    pure rowCount

rollsBackFailedReadiness :: Assertion
rollsBackFailedReadiness =
    withStoreFixture "felix-store-readiness-rollback" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        (owner, prefix, _syntax, semantic, _artefactKey, artefact, proposition) <-
            makeCommittedModule theory fixture
        missingDelta <- expectRight
            (Syntax.canonicalSyntaxDelta
                [Syntax.CanonicalStructureOperation "missing-child"])
        missingInterface <- expectRight
            (Syntax.moduleSyntaxInterface [] missingDelta)
        syntaxDelta <- expectRight
            (Syntax.canonicalSyntaxDelta [])
        brokenSyntax <- expectRight
            (Syntax.moduleSyntaxInterface
                [Syntax.moduleSyntaxAssertedId missingInterface]
                syntaxDelta)
        brokenParsedKey <- expectRight
            (Parsed.parsedModuleKey
                (Content.sourceContentIdBytes "rollback-source")
                Syntax.baseSyntaxInterfaceId
                [])
        brokenArtefactKey <- expectRight
            (Semantic.moduleArtefactKey
                owner
                (Parsed.parsedModuleId
                    brokenParsedKey
                    "rollback-parsed")
                []
                theory)
        result <- Store.writeSealedModule storeCheck brokenArtefactKey prefix brokenSyntax semantic
        case result of
            Left Store.StoreAssertedChildMissing{} ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected readiness failure: " <> show other)
            Right _ ->
                assertFailure "broken readiness transaction was accepted"
        assertEqual "failed readiness did not publish the prefix" 0
            =<< storedPropositionCount
                path
                (Identity.checkedPropositionId proposition)
        assertEqual "failed readiness leaves no module root" 0
            =<< storedArtefactCount
                path
                (Semantic.moduleArtefactResultId artefact)
        -- A later failed seal must not erase a prefix published by an
        -- earlier successful source prefix flush.
        expectRightIO (Store.writePendingModulePrefix storeCheck prefix)
        assertEqual "successful prefix is visible before retry" 1
            =<< storedPropositionCount
                path
                (Identity.checkedPropositionId proposition)
        retry <- Store.writeSealedModule storeCheck brokenArtefactKey prefix brokenSyntax semantic
        case retry of
            Left Store.StoreAssertedChildMissing{} ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected retry readiness failure: " <> show other)
            Right _ ->
                assertFailure "broken readiness retry was accepted"
        assertEqual "failed retry retains successful prefix" 1
            =<< storedPropositionCount
                path
                (Identity.checkedPropositionId proposition)
        assertEqual "failed retry still leaves no module root" 0
            =<< storedArtefactCount
                path
                (Semantic.moduleArtefactResultId artefact)
        Store.closeStore store
makeCommittedModule
    :: Identity.TheoryId
    -> StoreFixture
    -> IO
        ( ModuleName
        , Commit.PendingModulePrefix
        , Syntax.ModuleSyntaxInterface
        , Semantic.SemanticInterface
        , Semantic.ModuleArtefactKey
        , Semantic.ModuleArtefactResult
        , Identity.CheckedPropositionContent
        )
makeCommittedModule theory fixture =
    makeCommittedModuleWithProposition
        theory fixture (fixtureProposition fixture)

makeCommittedModuleWithProposition
    :: Identity.TheoryId
    -> StoreFixture
    -> Identity.CheckedPropositionContent
    -> IO
        ( ModuleName
        , Commit.PendingModulePrefix
        , Syntax.ModuleSyntaxInterface
        , Semantic.SemanticInterface
        , Semantic.ModuleArtefactKey
        , Semantic.ModuleArtefactResult
        , Identity.CheckedPropositionContent
        )
makeCommittedModuleWithProposition = makeCommittedModuleWithDeclaration False

makeCommittedModuleWithDeclaration
    :: Bool
    -> Identity.TheoryId
    -> StoreFixture
    -> Identity.CheckedPropositionContent
    -> IO
        ( ModuleName
        , Commit.PendingModulePrefix
        , Syntax.ModuleSyntaxInterface
        , Semantic.SemanticInterface
        , Semantic.ModuleArtefactKey
        , Semantic.ModuleArtefactResult
        , Identity.CheckedPropositionContent
        )
makeCommittedModuleWithDeclaration includeDeclaration theory fixture proposition = do
    foundation <- expectRight Foundation.checkedFoundation
    let namespaceDigest =
            hashBlake2b256 "store-module-test\NULprefix"
    relative <- expectRight (safeRelativePath "module.tex")
    let owner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest namespaceDigest)
                relative
        resolver = Declaration.vampireResolver \prepared ->
            pure
                (Provers.processFailedVampireResolution
                    (Provers.preparedTypedProverRequest prepared)
                    (Provers.ProverLaunchFailed
                        "unused"
                        "store fixture does not run Vampire"))
    checkedImports <- prepareTestImports (Identity.theoryId foundation) []
    driver <- Declaration.runModuleDriverFreshIO
        foundation
        owner
        checkedImports
        resolver
        do
            (_value, _batch) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "store-prefix") [fixtureFirstObject fixture]
                (Declaration.checkedCandidate
                    (Declaration.candidateSpec proposition Semantic.SearchIneligible [])
                    (Declaration.checkedOmittedPlanning [] [] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate
                        Declaration.recordOmittedUse
            when includeDeclaration do
                void (DeclTest.admitCompiled
                    (Semantic.declarationSyntaxId "store-byte-guard-declaration")
                    [fixtureSecondObject fixture] [] [] (const (pure ())))
            pure ()
    (_value, prefix, semantic) <-
        case driver of
            Right (Declaration.DriverSucceeded value evidence pending) ->
                pure (value, pending, Declaration.evidenceInterface evidence)
            Right (Declaration.DriverFailed failure _prefix) ->
                assertFailure
                    ("unexpected declaration failure: "
                        <> show
                            (failure
                                :: Declaration.DriverFailure
                                    Declaration.DeclarationError))
                    >> fail "unreachable"
            Right (Declaration.DriverSealFailed failure _prefix) ->
                assertFailure ("unexpected seal failure: " <> show failure)
                    >> fail "unreachable"
            Left failure ->
                assertFailure ("unexpected driver-open failure: " <> show failure)
                    >> fail "unreachable"
    delta <- expectRight (Syntax.canonicalSyntaxDelta [])
    syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
    parsedKey <- expectRight
        (Parsed.parsedModuleKey
            (Content.sourceContentIdBytes "store-module-source")
            Syntax.baseSyntaxInterfaceId
            [])
    artefactKey <- expectRight
        (Semantic.moduleArtefactKey
            owner
            (Parsed.parsedModuleId parsedKey "store-module-parsed")
            []
            theory)
    let artefact =
            Semantic.moduleArtefactResult
                artefactKey
                (Syntax.moduleSyntaxAssertedId syntax)
                (Semantic.semanticInterfaceAssertedId semantic)
                (concatMap
                    Commit.committedBatchValidationCertificates
                    (Commit.pendingModulePrefixBatches prefix))
    pure
        ( owner
        , prefix
        , syntax
        , semantic
        , artefactKey
        , artefact
        , proposition
        )

makePendingPrefix
    :: StoreFixture
    -> [Identity.AssertedObject]
    -> IO Commit.PendingModulePrefix
makePendingPrefix fixture objects = do
    foundation <- expectRight Foundation.checkedFoundation
    owner <- testModuleName "rollback-prefix.tex"
    let proposition = fixtureProposition fixture
        resolver = Declaration.vampireResolver \prepared ->
            pure
                (Provers.processFailedVampireResolution
                    (Provers.preparedTypedProverRequest prepared)
                    (Provers.ProverLaunchFailed
                        "unused"
                        "store fixture does not run Vampire"))
    checkedImports <- prepareTestImports (Identity.theoryId foundation) []
    driver <- Declaration.runModuleDriverFreshIO
        foundation
        owner
        checkedImports
        resolver
        do
            (_value, _batch) <- DeclTest.admitProof
                (Semantic.proofSyntaxId "store-rollback") objects
                (Declaration.checkedCandidate
                    (Declaration.candidateSpec proposition Semantic.SearchIneligible [])
                    (Declaration.checkedOmittedPlanning [] [] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate
                        Declaration.recordOmittedUse
            pure ()
    case driver of
        Right (Declaration.DriverSucceeded _value _interface prefix) ->
            pure prefix
        Right (Declaration.DriverFailed failure _prefix) ->
            assertFailure
                ("unexpected declaration failure: "
                    <> show
                        (failure
                            :: Declaration.DriverFailure
                                Declaration.DeclarationError))
                >> fail "unreachable"
        Right (Declaration.DriverSealFailed failure _prefix) ->
            assertFailure ("unexpected seal failure: " <> show failure)
                >> fail "unreachable"
        Left failure ->
            assertFailure ("unexpected driver-open failure: " <> show failure)
                >> fail "unreachable"

initializesAndReopensCurrentSchema :: Assertion
initializesAndReopensCurrentSchema =
    withStoreFixture "felix-store-startup" \path theory _fixture -> do
        (startup, store) <- expectOpen path theory
        assertEqual "new store status"
            Store.InitializedNewStore startup
        Store.closeStore store

        (reopened, current) <- expectOpen path theory
        assertEqual "current store status"
            Store.OpenedCurrentStore reopened
        Store.closeStore current

        connection <- SQLite.open path
        names <- SQLite.query_ connection
            ("SELECT name FROM sqlite_master "
                <> "WHERE type = 'table' AND name NOT LIKE 'sqlite_%' "
                <> "ORDER BY name")
            :: IO [Only Text]
        journal <- SQLite.query_ connection
            "PRAGMA journal_mode"
            :: IO [Only Text]
        SQLite.close connection
        assertEqual "complete schema table count"
            9
            (length names)
        assertEqual "rollback journal persists"
            [Only "delete"] journal

admitsMaintenanceSchema :: Assertion
admitsMaintenanceSchema = withStoreFixture "store-maintenance" \path theory _ -> do
    (_, store) <- expectOpen path theory
    Store.closeStore store
    Exception.bracket (SQLite.open path) SQLite.close $ \connection -> do
        SQLite.execute_ connection "ANALYZE"
        SQLite.execute_ connection "PRAGMA optimize"
        SQLite.execute_ connection "VACUUM"
    (_, reopened) <- expectOpen path theory
    Store.closeStore reopened

rejectsSchemaObjects :: Assertion
rejectsSchemaObjects = for_ statements $ \statement ->
    withStoreFixture "store-unexpected-schema" $ \path theory _ -> do
        (_, store) <- expectOpen path theory
        Store.closeStore store
        Exception.bracket (SQLite.open path) SQLite.close $ \connection -> do
            SQLite.execute_ connection statement
            -- A rejected current schema must not be configured on reopen.
            void (SQLite.query_ connection "PRAGMA journal_mode = WAL" :: IO [Only Text])
        assertSchemaRejected path theory
        Exception.bracket (SQLite.open path) SQLite.close $ \connection -> do
            journal <- SQLite.query_ connection "PRAGMA journal_mode" :: IO [Only Text]
            assertEqual "damaged schema is rejected before configuration" [Only "wal"] journal
  where
    statements =
        [ "CREATE TRIGGER drop_validation AFTER INSERT ON proof_validations BEGIN DELETE FROM proof_validations WHERE validation_key = NEW.validation_key; END"
        , "CREATE TRIGGER store_compatibility AFTER INSERT ON proof_validations BEGIN DELETE FROM proof_validations; END"
        , "CREATE TRIGGER sqliteXdrop AFTER INSERT ON proof_validations BEGIN DELETE FROM proof_validations; END"
        , "CREATE VIEW unexpected AS SELECT * FROM proof_validations"
        , "CREATE INDEX unexpected ON parsed_artefacts(parsed_module_id)"
        , "ALTER TABLE proof_validations ADD COLUMN unexpected INTEGER"
        ]

boundsSchemaMetadata :: Assertion
boundsSchemaMetadata = for_ mutations $ \mutate ->
    withStoreFixture "store-schema-limits" $ \path theory _ -> do
        (_, store) <- expectOpen path theory
        Store.closeStore store
        Exception.bracket (SQLite.open path) SQLite.close mutate
        assertSchemaRejected path theory
  where
    mutations =
        [ \connection -> SQLite.execute_ connection (SQLite.Query
            ("CREATE TABLE \"" <> Text.replicate (128 * 1024) "n" <> "\"(x)"))
        , \connection -> SQLite.execute_ connection (SQLite.Query
            ("CREATE TABLE unexpected(x /*" <> Text.replicate (20 * 1024 * 1024) "x" <> "*/)"))
        , \connection -> for_ [1..20 :: Int] $ \i -> SQLite.execute_ connection
            (SQLite.Query ("CREATE VIEW extra" <> Text.pack (show i) <> " AS SELECT 1"))
        ]

rejectsCompatibilityView :: Assertion
rejectsCompatibilityView = withStoreFixture "store-compatibility-view" $ \path theory _ -> do
    Exception.bracket (SQLite.open path) SQLite.close $ \connection ->
        -- Reading this view would fail; startup must classify its kind first.
        SQLite.execute_ connection
            "CREATE VIEW store_compatibility AS SELECT missing FROM nonexistent"
    result <- Store.openStore path theory
    case result of
        Left (Store.IncompatibleStore (Store.StoreCompatibilityMalformed message)) ->
            assertEqual "view is rejected before query evaluation"
                "compatibility object is not a table" message
        Right (_, store) -> Store.closeStore store >> assertFailure "compatibility view was admitted"
        Left other -> assertFailure (show other)

assertSchemaRejected :: FilePath -> Identity.TheoryId -> Assertion
assertSchemaRejected path theory = Store.openStore path theory >>= \case
    Left (Store.FatalStoreStartup (Store.StoreSchemaIntegrityFailure message)) ->
        assertBool "bounded schema diagnostic" (Text.length message <= 512)
    Right (_, store) -> Store.closeStore store >> assertFailure "unexpected schema was admitted"
    Left other -> assertFailure (show other)

rejectsIncompatibilityWithoutConfiguration :: Assertion
rejectsIncompatibilityWithoutConfiguration = for_ [False, True] \changedCalculus ->
    withStoreFixture "felix-store-incompatible" \path theory _fixture -> do
        otherTheory <- expectRight (Cache.decodeCache Identity.getTheoryIdCache
            (ByteString.replicate 32 0x5a))
        let currentEpoch = Cache.cacheEpochValue Cache.currentCacheEpoch
            (storedEpoch, storedTheory) = if changedCalculus
                then (currentEpoch, otherTheory)
                else (currentEpoch - 1, theory)
        connection <- SQLite.open path
        _ <- SQLite.query_ connection
            "PRAGMA journal_mode = WAL"
            :: IO [Only Text]
        SQLite.execute_ connection
            ("CREATE TABLE store_compatibility ( "
                <> "singleton INTEGER, cache_epoch INTEGER, theory_id BLOB )")
        SQLite.execute connection
            "INSERT INTO store_compatibility VALUES (1, ?, ?)"
            ( fromIntegral storedEpoch :: Int
            , Cache.encodeCache (Identity.putTheoryIdCache storedTheory)
            )
        SQLite.execute_ connection
            "CREATE TABLE untouched (value INTEGER)"
        SQLite.close connection

        result <- Store.openStore path theory
        case result of
            Left
                (Store.IncompatibleStore
                    Store.StoreCompatibilityMismatch{}) ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected incompatibility result: " <> show other)
            Right (_startup, store) -> do
                Store.closeStore store
                assertFailure "incompatible store was accepted"

        inspected <- SQLite.open path
        names <- SQLite.query_ inspected
            ("SELECT name FROM sqlite_master "
                <> "WHERE type = 'table' AND name NOT LIKE 'sqlite_%' "
                <> "ORDER BY name")
            :: IO [Only Text]
        journal <- SQLite.query_ inspected
            "PRAGMA journal_mode"
            :: IO [Only Text]
        SQLite.close inspected
        assertEqual "startup creates no schema"
            [Only "store_compatibility", Only "untouched"] names
        assertEqual "startup applies no journal configuration"
            [Only "wal"] journal

rejectsMalformedCompatibilityMetadata :: Assertion
rejectsMalformedCompatibilityMetadata =
    withStoreFixture "felix-store-malformed" \path theory _fixture -> do
        connection <- SQLite.open path
        SQLite.execute_ connection
            ("CREATE TABLE store_compatibility ( "
                <> "singleton INTEGER, cache_epoch, theory_id )")
        SQLite.execute connection
            "INSERT INTO store_compatibility VALUES (1, ?, ?)"
            ( "not-an-epoch" :: Text
            , Cache.encodeCache (Identity.putTheoryIdCache theory)
            )
        SQLite.close connection

        result <- Store.openStore path theory
        case result of
            Left
                (Store.IncompatibleStore
                    Store.StoreCompatibilityMalformed{}) ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected malformed result: " <> show other)
            Right (_startup, store) -> do
                Store.closeStore store
                assertFailure "malformed metadata was accepted"

rejectsCompatibleIncompleteSchema :: Assertion
rejectsCompatibleIncompleteSchema =
    withStoreFixture "felix-store-incomplete" \path theory _fixture -> do
        (_startup, store) <- expectOpen path theory
        Store.closeStore store
        connection <- SQLite.open path
        SQLite.execute_ connection
            "DROP TABLE canonical_propositions"
        SQLite.close connection

        result <- Store.openStore path theory
        case result of
            Left
                (Store.FatalStoreStartup
                    Store.StoreSchemaIntegrityFailure{}) ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected incomplete-schema result: " <> show other)
            Right (_startup, current) -> do
                Store.closeStore current
                assertFailure "incomplete current schema was accepted"

rollsBackUnequalDuplicateBatch :: Assertion
rollsBackUnequalDuplicateBatch =
    withStoreFixture "felix-store-rollback" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        let first = fixtureFirstObject fixture
            second = fixtureSecondObject fixture
        prefix <- makePendingPrefix fixture [first, second]
        Store.closeStore store

        connection <- SQLite.open path
        SQLite.execute connection
            "INSERT INTO canonical_objects (object_id, payload) VALUES (?, ?)"
            ( Cache.encodeCache
                (Identity.putObjectIdCache
                    (Identity.assertedObjectId second))
            , ("unequal canonical object payload"
                :: ByteString.ByteString)
            )
        SQLite.close connection

        (_reopened, current) <- expectOpen path theory
        currentCheck <- Store.newStoreCheck current
        result <- Store.writePendingModulePrefix currentCheck prefix
        case result of
            Left Store.StoreRowPayloadMismatch{} ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected duplicate result: " <> show other)
            Right () ->
                assertFailure "unequal duplicate was accepted"
        assertEqual "earlier insertion was rolled back" 0
            =<< storedObjectCount path (Identity.assertedObjectId first)
        Store.closeStore current

rejectsMalformedCanonicalPayloads :: Assertion
rejectsMalformedCanonicalPayloads =
    withStoreFixture "felix-store-decode" \path theory fixture -> do
        (_startup, store) <- expectOpen path theory
        storeCheck <- Store.newStoreCheck store
        let object = fixtureFirstObject fixture
        (_owner, prefix, syntax, semantic, key, _artefact, _proposition) <-
            makeCommittedModule theory fixture
        _ <- expectRightIO
            (Store.writeSealedModule storeCheck key prefix syntax semantic)
        Store.closeStore store

        connection <- SQLite.open path
        SQLite.execute connection
            ("UPDATE canonical_objects SET payload = ? "
                <> "WHERE object_id = ?")
            ( ByteString.singleton 0xff
            , Cache.encodeCache
                (Identity.putObjectIdCache
                    (Identity.assertedObjectId object))
            )
        SQLite.close connection

        (_reopened, current) <- expectOpen path theory
        currentCheck <- Store.newStoreCheck current
        result <- Store.loadCachedModuleCandidate
            currentCheck key (Syntax.moduleSyntaxAssertedId syntax)
        case result of
            Left Store.StoreRowDecodeFailure{} ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected malformed-row result: " <> show other)
            Right _ ->
                assertFailure "malformed canonical payload was accepted"
        Store.closeStore current

rejectsMalformedTransparentTermPayloads :: Assertion
rejectsMalformedTransparentTermPayloads =
    withStoreFixture "felix-store-transparent-decode"
        \path theory _fixture -> do
            fixture <- makeTransparentStoreFixture theory
            (_startup, store) <- expectOpen path theory
            storeCheck <- Store.newStoreCheck store
            let object = fixtureFirstObject fixture
            (_owner, prefix, syntax, semantic, key, _artefact, _proposition) <-
                makeCommittedModule theory fixture
            _ <- expectRightIO
                (Store.writeSealedModule storeCheck key prefix syntax semantic)
            Store.closeStore store

            connection <- SQLite.open path
            let malformedPayload = Cache.encodeCache do
                    Cache.putCoreTypeCache Core.TySet
                    Cache.putCacheBytes (ByteString.singleton 0xff)
            SQLite.execute connection
                ("UPDATE canonical_objects SET payload = ? "
                    <> "WHERE object_id = ?")
                ( malformedPayload
                , Cache.encodeCache
                    (Identity.putObjectIdCache
                        (Identity.assertedObjectId object))
                )
            SQLite.close connection

            (_reopened, current) <- expectOpen path theory
            currentCheck <- Store.newStoreCheck current
            result <- Store.loadCachedModuleCandidate
                currentCheck key (Syntax.moduleSyntaxAssertedId syntax)
            case result of
                Left
                        (Store.StoreTermReentryFailure
                            (Identity.TermCodecFailure
                                (MathematicalUnknownTermTag 0xff))) ->
                    pure ()
                Left other ->
                    assertFailure
                        ("unexpected transparent decode failure: "
                            <> show other)
                Right _ ->
                    assertFailure
                        "malformed transparent term was accepted"
            Store.closeStore current

rejectsMismatchedCanonicalObjectReentry :: Assertion
rejectsMismatchedCanonicalObjectReentry =
    withStoreFixture "felix-store-object-reentry"
        \path theory _fixture -> do
            fixture <- makeTransparentStoreFixture theory
            (_startup, store) <- expectOpen path theory
            storeCheck <- Store.newStoreCheck store
            let suppliedObject = fixtureFirstObject fixture
                storedObject = fixtureSecondObject fixture
                suppliedId = Identity.assertedObjectId suppliedObject
                computedId = Identity.assertedObjectId storedObject
            (_owner, prefix, syntax, semantic, key, _artefact, _proposition) <-
                makeCommittedModule theory fixture
            _ <- expectRightIO
                (Store.writeSealedModule storeCheck key prefix syntax semantic)
            Store.closeStore store

            connection <- SQLite.open path
            replacement <- rawObjectPayload connection storedObject
            SQLite.execute connection
                ("UPDATE canonical_objects SET payload = ? "
                    <> "WHERE object_id = ?")
                ( replacement
                , Cache.encodeCache
                    (Identity.putObjectIdCache suppliedId)
                )
            SQLite.close connection

            (_reopened, current) <- expectOpen path theory
            currentCheck <- Store.newStoreCheck current
            result <- Store.loadCachedModuleCandidate
                currentCheck key (Syntax.moduleSyntaxAssertedId syntax)
            case result of
                Left
                        (Store.StoreObjectReentryFailure
                            (Identity.ObjectReentryIdMismatch
                                actualSupplied actualComputed)) -> do
                    assertEqual "supplied row key"
                        suppliedId actualSupplied
                    assertEqual "computed payload identity"
                        computedId actualComputed
                Left other ->
                    assertFailure
                        ("unexpected object re-entry failure: " <> show other)
                Right _ ->
                    assertFailure "mismatched canonical object was accepted"
            Store.closeStore current

storesAndReentersCanonicalRows :: Assertion
storesAndReentersCanonicalRows =
    withStoreFixture "felix-store-canonical-row"
        \path theory fixture -> do
            (_startup, store) <- expectOpen path theory
            storeCheck <- Store.newStoreCheck store
            (_owner, prefix, syntax, semantic, key, _artefact, proposition) <-
                makeCommittedModule theory fixture
            _ <- expectRightIO
                (Store.writeSealedModule storeCheck key prefix syntax semantic)
            let identity = Identity.checkedPropositionId proposition
                expected = encodeCanonicalTerm
                    Identity.objectIdBuilder
                    (Core.frozenCoreTerm
                        (Identity.checkedPropositionTerm proposition))
            connection <- SQLite.open path
            payloads <- SQLite.query connection
                "SELECT payload FROM canonical_propositions WHERE proposition_id = ?"
                (Only
                    (Cache.encodeCache
                        (Identity.putPropositionIdCache identity)))
                :: IO [Only ByteString.ByteString]
            assertEqual "exact proposition term payload"
                [Only expected] payloads
            SQLite.execute connection
                "UPDATE canonical_propositions SET payload = ? WHERE proposition_id = ?"
                ( expected <> ByteString.singleton 0
                , Cache.encodeCache
                    (Identity.putPropositionIdCache identity)
                )
            SQLite.close connection
            Store.loadCachedModuleCandidate
                storeCheck key (Syntax.moduleSyntaxAssertedId syntax)
                >>= \case
                    Left
                            (Store.StoreTermReentryFailure
                                Identity.TermRootMismatch{}) -> pure ()
                    Left other -> assertFailure
                        ("unexpected canonical corruption failure: " <> show other)
                    Right _ -> assertFailure
                        "corrupt canonical row was accepted"
            Store.closeStore store

plansPersistentStores :: Assertion
plansPersistentStores =
    Temp.withSystemTempDirectory "felix-store-planning" \root -> do
        (theory, _fixture) <- makeStoreFixture
        let cacheRoot = root Posix.</> "cache"
            expectedDefault =
                cacheRoot Posix.</> "felix" Posix.</> "store.sqlite"
            explicitParent = root Posix.</> "explicit"
            explicitPath = explicitParent Posix.</> "selected.sqlite"
        Directory.createDirectory cacheRoot
        Directory.createDirectory explicitParent
        withEnvironment "XDG_CACHE_HOME" cacheRoot do
            defaultPlan <- expectRightIO
                (Store.planStore Store.DefaultStore)
            assertBool "planning does not create the default parent"
                . not
                =<< Directory.doesPathExist
                    (cacheRoot Posix.</> "felix")
            defaultResult <- withTestStoreLease defaultPlan \lease -> do
                assertEqual "default store path"
                    expectedDefault
                    (Store.storePathFilePath
                        (Store.storeLeasePath lease))
                Store.withOpenStore lease theory \_startup _store ->
                    Directory.doesFileExist expectedDefault
            assertEqual "default store opens at the XDG path"
                (Right True) defaultResult

        explicitPlan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore explicitPath))
        explicitResult <- withTestStoreLease explicitPlan \lease -> do
            assertEqual "explicit store path"
                explicitPath
                (Store.storePathFilePath
                    (Store.storeLeasePath lease))
            Store.withOpenStore lease theory \_startup _store ->
                Directory.doesFileExist explicitPath
        assertEqual "explicit store opens without creating its parent"
            (Right True) explicitResult

        missing <- Store.planStore
            (Store.ExplicitStore
                (root Posix.</> "missing" Posix.</> "store.sqlite"))
        case missing of
            Left Store.ExplicitStoreParentMissing{} ->
                pure ()
            Left other ->
                assertFailure
                    ("unexpected missing-parent result: " <> show other)
            Right _ ->
                assertFailure "missing explicit parent was accepted"

refreshesPersistentStore :: Assertion
refreshesPersistentStore =
    Temp.withSystemTempDirectory "felix-store-refresh" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        storePath <- case Store.storePlanPersistentPath plan of
            Nothing ->
                assertFailure "explicit store plan was not persistent"
                    >> fail "unreachable"
            Just selected ->
                pure selected
        let removedPaths =
                [ path
                , Store.storeRollbackJournalPath storePath
                , Store.storeWriteAheadLogPath storePath
                , Store.storeSharedMemoryPath storePath
                ]
        for_ removedPaths \file ->
            writeFile file "disposable"

        withTestStoreLease plan \lease -> do
            refreshed <- Store.refreshStore lease
            assertEqual "persistent refresh result" (Right ()) refreshed
            for_ removedPaths \file ->
                assertBool ("refresh removed " <> file)
                    . not
                    =<< Directory.doesPathExist file
            assertBool "refresh retains the held lock sidecar"
                =<< Directory.doesFileExist
                    (Store.storeLockPath storePath)

        assertBool "refresh retains the lock sidecar after release"
            =<< Directory.doesFileExist
                (Store.storeLockPath storePath)

        let linkedTarget = root Posix.</> "linked-target.sqlite"
        writeFile linkedTarget "keep target"
        Directory.createFileLink linkedTarget path
        withTestStoreLease plan \lease -> do
            refreshed <- Store.refreshStore lease
            assertEqual "linked-store refresh result" (Right ()) refreshed
        assertBool "refresh removes the selected symbolic link"
            . not
            =<< Directory.doesPathExist path
        linkedContents <- readFile linkedTarget
        assertEqual "refresh does not follow the selected symbolic link"
            "keep target" linkedContents

leavesAuxiliariesWithoutPrimary :: Assertion
leavesAuxiliariesWithoutPrimary =
    Temp.withSystemTempDirectory "felix-store-refresh-absent" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        storePath <- case Store.storePlanPersistentPath plan of
            Nothing ->
                assertFailure "explicit store plan was not persistent"
                    >> fail "unreachable"
            Just selected ->
                pure selected
        let auxiliaries =
                [ Store.storeRollbackJournalPath storePath
                , Store.storeWriteAheadLogPath storePath
                , Store.storeSharedMemoryPath storePath
                ]
        for_ auxiliaries \file ->
            writeFile file "orphan"

        withTestStoreLease plan \lease -> do
            refreshed <- Store.refreshStore lease
            assertEqual "absent-store refresh result" (Right ()) refreshed

        for_ auxiliaries \file ->
            assertBool ("absent primary preserves " <> file)
                =<< Directory.doesFileExist file
        assertBool "refresh did not create the primary store"
            . not
            =<< Directory.doesPathExist path

reportsRefreshDeletionFailure :: Assertion
reportsRefreshDeletionFailure =
    Temp.withSystemTempDirectory "felix-store-refresh-failure" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        storePath <- case Store.storePlanPersistentPath plan of
            Nothing ->
                assertFailure "explicit store plan was not persistent"
                    >> fail "unreachable"
            Just selected ->
                pure selected
        writeFile path "disposable"
        Directory.createDirectory
            (Store.storeWriteAheadLogPath storePath)

        result <- withTestStoreLease plan Store.refreshStore
        case result of
            Left
                (Store.StoreRefreshFailed
                    Store.StoreOperationFailed{}) ->
                        pure ()
            Left other ->
                assertFailure
                    ("unexpected refresh failure: " <> show other)
            Right () ->
                assertFailure "directory auxiliary was removed as a file"
        assertBool "failed refresh retains the primary store"
            =<< Directory.doesFileExist path

rejectsConcurrentPersistentLease :: Assertion
rejectsConcurrentPersistentLease =
    Temp.withSystemTempDirectory "felix-store-process-lease" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        executable <- Environment.getExecutablePath
        environment <- Environment.getEnvironment
        let helperEnvironment =
                ("FELIX_TEST_STORE_LEASE_HELPER", path)
                    : filter
                        ((/= "FELIX_TEST_STORE_LEASE_HELPER") . fst)
                        environment
            process =
                (Process.proc executable [])
                    { Process.env = Just helperEnvironment
                    , Process.std_in = Process.CreatePipe
                    , Process.std_out = Process.CreatePipe
                    }
        Process.withCreateProcess process
            \childInput childOutput _childError processHandle -> do
                input <- maybe
                    (assertFailure "lease helper has no stdin"
                        >> fail "unreachable")
                    pure
                    childInput
                output <- maybe
                    (assertFailure "lease helper has no stdout"
                        >> fail "unreachable")
                    pure
                    childOutput
                ready <- IO.hGetLine output
                assertEqual "helper acquisition handshake" "ready" ready

                contended <- Store.withStoreLease plan \_lease ->
                    pure ()
                case contended of
                    Left (Store.StoreLeaseContended selected) ->
                        assertEqual "contended store path"
                            path
                            (Store.storePathFilePath selected)
                    Left other ->
                        assertFailure
                            ("unexpected lease contention result: "
                                <> show other)
                    Right () ->
                        assertFailure "concurrently owned store was acquired"

                IO.hPutStrLn input "release"
                IO.hFlush input
                exitCode <- Process.waitForProcess processHandle
                assertEqual "lease helper exit" ExitSuccess exitCode

        _ <- expectRightIO
            (Store.withStoreLease plan \_lease -> pure ())
        let selectedPath =
                fromMaybe
                    (impossible "persistent plan has no path")
                    (Store.storePlanPersistentPath plan)
        assertBool "persistent lock sidecar remains after release"
            =<< Directory.doesFileExist
                (Store.storeLockPath selectedPath)

releasesLeaseAfterException :: Assertion
releasesLeaseAfterException =
    Temp.withSystemTempDirectory "felix-store-exception-lease" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        thrown <- Exception.try
            (Store.withStoreLease plan \_lease ->
                ioError (userError "lease action failed"))
            :: IO
                (Either
                    IOError
                    (Either Store.StoreLeaseError ()))
        case thrown of
            Left _ -> pure ()
            Right _ -> assertFailure "lease action exception did not escape"
        void (expectRightIO (Store.withStoreLease plan \_lease -> pure ()))

releasesLeaseAfterCancellation :: Assertion
releasesLeaseAfterCancellation =
    Temp.withSystemTempDirectory "felix-store-cancel-lease" \root -> do
        let path = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        entered <- MVar.newEmptyMVar
        blocker <- MVar.newEmptyMVar
        owner <- Async.async
            (Store.withStoreLease plan \_lease -> do
                MVar.putMVar entered ()
                MVar.takeMVar blocker)
        MVar.takeMVar entered
        Async.cancel owner
        void (Async.waitCatch owner)
        void (expectRightIO (Store.withStoreLease plan \_lease -> pure ()))

reportsLeaseAcquisitionFailure :: Assertion
reportsLeaseAcquisitionFailure =
    Temp.withSystemTempDirectory "felix-store-bad-lock" \root -> do
        let path = root Posix.</> "store.sqlite"
            lockPath = path <> ".lock"
        Directory.createDirectory lockPath
        plan <- expectRightIO
            (Store.planStore (Store.ExplicitStore path))
        acquired <- Store.withStoreLease plan \_lease -> pure ()
        case acquired of
            Left (Store.StoreLeaseAcquisitionFailed selected _reason) ->
                assertEqual "failed lock store path"
                    path
                    (Store.storePathFilePath selected)
            Left other ->
                assertFailure
                    ("unexpected lock-system failure: " <> show other)
            Right () ->
                assertFailure "directory lock path was acquired"

cleansFreshStores :: Assertion
cleansFreshStores = do
    (theory, _fixture) <- makeStoreFixture
    plan <- expectRightIO
        (Store.planStore Store.FreshTemporaryStore)

    successPath <- IORef.newIORef Nothing
    success <- withTestStoreLease plan \lease -> do
        let path = Store.storePathFilePath
                (Store.storeLeasePath lease)
        IORef.writeIORef successPath (Just path)
        refreshed <- Store.refreshStore lease
        assertEqual "fresh-store refresh result" (Right ()) refreshed
        Store.withOpenStore lease theory \_startup _store -> do
            databaseExists <- Directory.doesFileExist path
            lockExists <- Directory.doesPathExist
                (Store.storeLockPath (Store.storeLeasePath lease))
            pure (databaseExists, lockExists)
    assertEqual "fresh store opens without a lock sidecar"
        (Right (True, False)) success
    assertFreshRemoved successPath

    failurePath <- IORef.newIORef Nothing
    failed <- Exception.try
        (withTestStoreLease plan \lease -> do
            let path = Store.storePathFilePath
                    (Store.storeLeasePath lease)
            IORef.writeIORef failurePath (Just path)
            void
                (Store.withOpenStore lease theory \_startup _store ->
                    ioError (userError "fresh action failed")))
        :: IO (Either IOError ())
    case failed of
        Left _ ->
            pure ()
        Right () ->
            assertFailure "fresh-store action exception did not escape"
    assertFreshRemoved failurePath

doesNotFallBackAfterFatalStartup :: Assertion
doesNotFallBackAfterFatalStartup =
    Temp.withSystemTempDirectory "felix-store-no-fallback" \root -> do
        (theory, _fixture) <- makeStoreFixture
        let persistentParent = root Posix.</> "persistent"
            persistentPath = persistentParent Posix.</> "store.sqlite"
            cacheRoot = root Posix.</> "cache"
        Directory.createDirectory persistentParent
        Directory.createDirectory cacheRoot
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore persistentPath))
        initialized <- withTestStoreLease plan \lease ->
            Store.withOpenStore lease theory \_startup _store ->
                pure ()
        assertEqual "fixture store initialized"
            (Right ()) initialized
        connection <- SQLite.open persistentPath
        SQLite.execute_ connection
            "DROP TABLE canonical_objects"
        SQLite.close connection

        withEnvironment "XDG_CACHE_HOME" cacheRoot do
            result <- withTestStoreLease plan \lease ->
                Store.withOpenStore lease theory \_startup _store ->
                    pure ()
            case result of
                Left
                    (Store.StoreLifecycleOpenFailed
                        (Store.FatalStoreStartup
                            Store.StoreSchemaIntegrityFailure{})) ->
                    pure ()
                Left other ->
                    assertFailure
                        ("unexpected fatal-startup result: " <> show other)
                Right () ->
                    assertFailure "corrupt persistent store was accepted"
            assertBool "fatal startup creates no default fallback"
                . not
                =<< Directory.doesPathExist
                    (cacheRoot Posix.</> "felix")


data StoreFixture = StoreFixture
    !Identity.AssertedObject
    !Identity.AssertedObject
    !Identity.CheckedPropositionContent

fixtureFirstObject :: StoreFixture -> Identity.AssertedObject
fixtureFirstObject (StoreFixture object _second _proposition) =
    object

fixtureSecondObject :: StoreFixture -> Identity.AssertedObject
fixtureSecondObject (StoreFixture _first object _proposition) =
    object

fixtureProposition
    :: StoreFixture
    -> Identity.CheckedPropositionContent
fixtureProposition (StoreFixture _first _second proposition) =
    proposition

makeStoreFixture
    :: IO (Identity.TheoryId, StoreFixture)
makeStoreFixture = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        first = intrinsicObject theory Core.Empty
        second = intrinsicObject theory Core.PairSet
    closure <- expectRight
        (Identity.validateObjectClosure theory [first, second])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure
            (Core.CEq
                Core.TySet
                (Core.CGlobal (Identity.assertedObjectId first))
                (Core.CGlobal (Identity.assertedObjectId first))))
    pure
        ( theory
        , StoreFixture first second proposition
        )

makeTransparentStoreFixture
    :: Identity.TheoryId
    -> IO StoreFixture
makeTransparentStoreFixture theory = do
    let emptyTerm = Core.CIntrinsic Core.Empty
        pair = Core.CApp
            (Core.CApp (Core.CIntrinsic Core.PairSet) emptyTerm)
            emptyTerm
        first = Identity.transparentObject theory Core.TySet emptyTerm
        second = Identity.transparentObject theory Core.TySet pair
    closure <- expectRight
        (Identity.validateObjectClosure theory [first, second])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure
            (Core.CEq
                Core.TySet
                (Core.CGlobal (Identity.assertedObjectId first))
                (Core.CGlobal (Identity.assertedObjectId first))))
    pure (StoreFixture first second proposition)

intrinsicObject
    :: Identity.TheoryId
    -> Core.CoreIntrinsicTag
    -> Identity.AssertedObject
intrinsicObject theory tag =
    Identity.intrinsicObject theory tag

withStoreFixture
    :: String
    -> ( FilePath
        -> Identity.TheoryId
        -> StoreFixture
        -> IO a
       )
    -> IO a
withStoreFixture template action =
    Temp.withSystemTempDirectory template \root -> do
        (theory, fixture) <- makeStoreFixture
        action
            (root Posix.</> "store.sqlite")
            theory
            fixture

expectOpen
    :: FilePath
    -> Identity.TheoryId
    -> IO (Store.StoreStartup, Store.Store)
expectOpen path theory = do
    result <- Store.openStore path theory
    case result of
        Left failure ->
            assertFailure (show failure) >> fail "unreachable"
        Right opened ->
            pure opened

expectRight :: Show failure => Either failure value -> IO value
expectRight = \case
    Left failure ->
        assertFailure (show failure) >> fail "unreachable"
    Right value ->
        pure value

expectRightIO
    :: Show failure
    => IO (Either failure value)
    -> IO value
expectRightIO action =
    expectRight =<< action

withTestStoreLease
    :: Store.StorePlan
    -> (Store.StoreLease -> IO value)
    -> IO value
withTestStoreLease plan action =
    expectRightIO (Store.withStoreLease plan action)

assertFreshRemoved :: IORef.IORef (Maybe FilePath) -> Assertion
assertFreshRemoved pathReference = do
    selected <- IORef.readIORef pathReference
    case selected of
        Nothing ->
            assertFailure "fresh store path was not allocated"
        Just path -> do
            assertBool "fresh database was removed"
                . not
                =<< Directory.doesPathExist path
            assertBool "fresh database directory was removed"
                . not
                =<< Directory.doesPathExist
                    (Posix.takeDirectory path)

withEnvironment
    :: String
    -> String
    -> IO value
    -> IO value
withEnvironment name value action =
    Exception.bracket
        (Environment.lookupEnv name)
        restore
        \_previous -> do
            Environment.setEnv name value
            action
  where
    restore = \case
        Nothing ->
            Environment.unsetEnv name
        Just previous ->
            Environment.setEnv name previous
