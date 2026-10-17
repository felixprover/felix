{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Module.Cache (tests) where

import Base
import Felix.Cache.Codec
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.LooseDeduction qualified as LooseDeduction
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Math.Codec
import Felix.Module
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Source
import Felix.Store qualified as Store
import Felix.Syntax.Interface qualified as Syntax
import Felix.Verification qualified as Verification
import Felix.Test.Support.Declarations qualified as DeclTest
import Felix.Test.Support.Imports
import Felix.Test.Unit.Module.Support

import Control.Exception (bracket)
import Control.Monad (foldM, replicateM_)
import Control.Exception qualified as Exception
import Data.ByteString qualified as ByteString
import Data.Text qualified as StrictText
import Data.Text.Encoding qualified as Text
import Data.IORef
    ( modifyIORef'
    , newIORef
    , readIORef
    )
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import System.Directory
    ( createDirectoryIfMissing
    , getCurrentDirectory
    , getPermissions
    , setOwnerExecutable
    , setPermissions
    )
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import Test.Tasty
import Test.Tasty.HUnit


tests :: [TestTree]
tests =
    [ testCase "reuses separation validation"
        reusesSeparationValidation
    , testCase "retains normalized structure diamonds without rechecking ancestors"
        retainsNormalizedStructures
    , testCase "reuses proof validation across module misses"
        reusesProofValidationAcrossModuleMisses
    , testCase "loads a cached producer for a fresh importer"
        loadsCachedProducerForFreshImporter
    , testCase "reports admitted source escapes on fresh, warm, and failure paths"
        reportsAdmittedSourceEscapes
    , testCase "retains the exact prefix before a later failure"
        retainsPrefixBeforeFailure
    , testCase "installs nonempty implicit prelude evidence"
        installsNonemptyImplicitPreludeEvidence
    ]


retainsNormalizedStructures :: Assertion
retainsNormalizedStructures =
    Temp.withSystemTempDirectory "felix-retained-structures" \root -> do
        foundation <- expectRight Foundation.checkedFoundation
        let sources =
                [("base.tex", unlines
                    [ "\\begin{struct}\\label{retained_base}"
                    , "A retained base $S$ is a onesorted structure equipped with"
                    , "\\begin{enumerate}"
                    , "\\item a set $\\retainedValue[S]$;"
                    , "\\end{enumerate}."
                    , "\\end{struct}"
                    , "\\begin{struct}\\label{retained_family}"
                    , "Let $X$ be a set."
                    , "A retained family $S$ over $X$ is a retained base such that"
                    , "\\begin{enumerate}"
                    , "\\item\\label{retained_parameter} $X=X$."
                    , "\\end{enumerate}"
                    , "\\end{struct}" ])
                , ("left.tex", child "base.tex" "retained_left" "retained left" "a retained family over $\\{X\\}$")
                , ("right.tex", child "base.tex" "retained_right" "retained right" "a retained family over $X$")
                , ("join.tex", "\\import{left.tex}\n" <>
                    child "right.tex" "retained_join" "retained join" "a retained left over $X$ and a retained right over $X$")]
        for_ sources \(path, source) -> ByteString.writeFile (root Posix.</> path)
            (Text.encodeUtf8 (StrictText.pack source))
        (_startup, store) <- expectRightIO (Store.openStore (root Posix.</> "store.sqlite") (Identity.theoryId foundation))
        bracket (pure store) Store.closeStore \opened -> do
            prelude <- expectRightIO (acquireFinalPreludeSession opened foundation finalPreludeResolver)
            mounts <- exactFixtureMounts root
            workspace <- parseFinalWorkspace prelude mounts "join.tex"
            fresh <- compileFinalParsedWorkspaceWithResolver foundation prelude unusedResolver workspace
            assertEqual "four structure-bearing modules seal" 4 (length fresh)
            let declarations = concatMap (Semantic.semanticInterfaceDeclarations . completedModuleSemantic) fresh
                wires = concatMap (Semantic.semanticEnvironmentStructures . Semantic.declarationDeltaEnvironment) declarations
            assertEqual "compound inheritance retains laws but contributes no notion edge" 5
                (sum (length . (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterNotionView rule) <- Semantic.declarationDeltaRegistrations entry]) <$> declarations))
            assertEqual "the diamond retains distinct specialized ancestor laws" 20
                (length [() | wire <- wires, Schema.ParentInheritanceLaw{} <- Map.keys (Semantic.structureWireLawIndex wire)])
            check <- Declaration.newImportCheck foundation
            let preludeEvidence = Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude)
                initial = Map.singleton
                    (Semantic.semanticInterfaceAssertedId (Declaration.evidenceInterface preludeEvidence)) preludeEvidence
                replay known sealed = do
                    semantic <- expectRight (decodeCache Semantic.getSemanticInterfaceCache
                        (encodeCache (Semantic.putSemanticInterfaceCache (completedModuleSemantic sealed))))
                    parents <- traverse (\identity -> maybe (assertFailure "missing fixture parent" >> fail "unreachable") pure
                        (Map.lookup identity known)) (Semantic.semanticInterfaceDirectInputs semantic)
                    prepared <- expectRightIO (Declaration.prepareImports check parents)
                    let batches = Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)
                    propositions <- traverse stored (concatMap Commit.committedBatchPropositions batches)
                    evidence <- expectRightIO (Declaration.admitCachedModuleEvidence prepared semantic
                        (concatMap Commit.committedBatchObjects batches) propositions
                        (concatMap Commit.committedBatchValidationCertificates batches))
                    assertEqual "cold admission preserves semantic identity" semantic (Declaration.evidenceInterface evidence)
                    assertEqual "cold admission preserves normalized mathematics"
                        (Schema.resolvedSchemaContentDigest <$> Declaration.evidenceLocalStructureSchemas (completedModuleEvidence sealed))
                        (Schema.resolvedSchemaContentDigest <$> Declaration.evidenceLocalStructureSchemas evidence)
                    pure (Map.insert (Semantic.semanticInterfaceAssertedId semantic) evidence known)
            admitted <- foldM replay initial fresh
            work <- Declaration.importCheckWork check
            assertEqual "each local schema input is checked once" 5 (Declaration.importStructureInputChecks work)
            assertEqual "each local predicate is checked once" 5 (Declaration.importStructurePredicateChecks work)
            assertEqual "each local interface is checked once" 5 (Declaration.importStructureChecks work)
            rootModule <- sole "fresh diamond root" (take 1 (reverse fresh))
            let rootSemantic = completedModuleSemantic rootModule
            rootEvidence <- maybe (fail "missing admitted root") pure
                (Map.lookup (Semantic.semanticInterfaceAssertedId rootSemantic) admitted)
            _ <- expectRightIO (Declaration.prepareImports check [rootEvidence])
            warmed <- Declaration.importCheckWork check
            replicateM_ 4 (expectRightIO (Declaration.prepareImports check [rootEvidence]))
            repeated <- Declaration.importCheckWork check
            assertEqual "retained preparation does not recheck local inputs"
                (Declaration.importStructureInputChecks work) (Declaration.importStructureInputChecks repeated)
            assertEqual "retained preparation does not reopen predicates"
                (Declaration.importStructurePredicateChecks work) (Declaration.importStructurePredicateChecks repeated)
            assertEqual "repeated parent preparation uses its memo" 4
                (Declaration.importParentMemoHits repeated - Declaration.importParentMemoHits warmed)
            assertEqual "memo reuse inserts no contribution"
                (Declaration.importContributionInsertions warmed) (Declaration.importContributionInsertions repeated)
            producer <- sole "fresh structure producer" (take 1 fresh)
            let producerSemantic = completedModuleSemantic producer
                producerDeltas = Semantic.semanticInterfaceDeclarations producerSemantic
                producerBatches = Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix producer)
                producerFacts = concatMap Semantic.declarationDeltaFacts producerDeltas
                producerCertificates = concatMap Commit.committedBatchValidationCertificates producerBatches
            familyWire <- sole "later producer structure"
                (concatMap (Semantic.semanticEnvironmentStructures . Semantic.declarationDeltaEnvironment) (drop 1 producerDeltas))
            definition <- maybe (fail "family definition resource missing") pure
                (Map.lookup Schema.PredicateDefinitionResource (Semantic.structureWireResourceIndex familyWire))
            tampered <- for (zip producerFacts producerCertificates) \(fact, certificate) ->
                if Semantic.semanticFactFingerprint fact == definition
                    then expectRight (Authority.validationCertificate (Semantic.semanticFactAuthority fact)
                        (Authority.CheckedSourceProof Authority.NoExternalProofUse))
                    else pure certificate
            prepared <- expectRightIO (Declaration.prepareImports check [preludeEvidence])
            propositions <- traverse stored (concatMap Commit.committedBatchPropositions producerBatches)
            beforeFailure <- Declaration.importCheckWork check
            result <- Declaration.admitCachedModuleEvidence prepared producerSemantic
                (concatMap Commit.committedBatchObjects producerBatches) propositions tampered
            case result of
                Left Declaration.StructureInterfaceInvalid{} -> pure ()
                Left failure -> assertFailure ("unexpected resource authority rejection: " <> show failure)
                Right _ -> assertFailure "a later corrupted resource exposed module evidence"
            afterFailure <- Declaration.importCheckWork check
            assertEqual "late resource rejection checks both local predicates" 2
                (Declaration.importStructurePredicateChecks afterFailure - Declaration.importStructurePredicateChecks beforeFailure)
  where
    child parent marker phrase inherited = unlines
        [ "\\import{" <> parent <> "}"
        , "\\begin{struct}\\label{" <> marker <> "}"
        , "Let $X$ be a set."
        , "A " <> phrase <> " $S$ over $X$ is " <> inherited <> "."
        , "\\end{struct}" ]
    stored proposition = do
        reentered <- expectRight (Identity.identifyAndReenterCanonicalTerm
            (encodeCanonicalTerm Identity.objectIdBuilder
                (Core.frozenCoreTerm (Identity.checkedPropositionTerm proposition))))
        expectRight (Identity.storedPropositionCandidate (Identity.checkedPropositionId proposition) reentered)

reusesSeparationValidation :: Assertion
reusesSeparationValidation =
    Temp.withSystemTempDirectory "felix-exact-separation-cache" \root -> do
        let relative = "test/phase5/exact-separation.tex"
            sourcePath = root Posix.</> relative
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        createDirectoryIfMissing True (Posix.takeDirectory sourcePath)
        ByteString.readFile relative >>= ByteString.writeFile sourcePath
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-separation-cache'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        workspace <- parseWorkspace bootstrap mounts relative
        freshRequests <- newIORef []
        let freshResolver = Declaration.vampireResolver \prepared -> do
                modifyIORef' freshRequests
                    (<> [Provers.preparedTypedProverRequest prepared])
                (Provers.runPreparedTypedProver
                        (Provers.vampire
                            executable
                            Provers.defaultTimeLimit
                            Provers.defaultMemoryLimit)
                        prepared)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation
                bootstrap
                freshResolver
                AlwaysMissValidation
                workspace
        assertEqual "fresh separation proof runs Vampire once"
            1
            . length
            =<< readIORef freshRequests
        fresh <- sole "fresh exact separation module" freshModules
        assertSeparationModule "fresh cached" fresh
        freshDefinitionBatch <-
            case Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix fresh) of
                batch : _theorem : [] -> pure batch
                batches ->
                    assertFailure
                        ("fresh separation declaration count: "
                            <> show (length batches))
                        >> fail "unreachable"
        freshDefinitionValidation <-
            maybe
                (assertFailure "fresh separation definition validation absent"
                    >> fail "unreachable")
                pure
                (Commit.committedBatchDeclarationValidation
                    freshDefinitionBatch)
        corruptedDefinitionValidation <-
            case Semantic.declarationValidationRecordCertificates
                    freshDefinitionValidation of
                [equation, extensional] -> do
                    corruptedExtensional <-
                        expectRight
                            (Authority.validationCertificate
                                (Authority.validationTarget extensional)
                                (Authority.validationDirectAuthorization
                                    equation))
                    pure
                        (Semantic.declarationValidationRecord
                            (Semantic.declarationValidationRecordKey
                                freshDefinitionValidation)
                            [equation, corruptedExtensional])
                certificates ->
                    assertFailure
                        ("fresh separation certificate count: "
                            <> show (length certificates))
                        >> fail "unreachable"
        freshRequest <-
            sole "fresh separation request"
                =<< readIORef freshRequests
        freshAcceptedRequest <-
            acceptedRequestId "fresh separation" fresh
        assertEqual "fresh authority binds the exact request bytes"
            freshAcceptedRequest
            (Provers.preparedVerificationRequestId freshRequest)
        assertBool "fresh separation request bytes are retained by the caller"
            (Provers.preparedVerificationByteCount freshRequest > 0)
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                expectRightIO
                    (Store.writePendingModulePrefix storeCheck
                        (Module.completedTypedModulePrefix fresh))
                let validation = storeValidationPolicy storeCheck
                warmRuns <- newIORef (0 :: Int)
                warmModules <-
                    compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        (countingAcceptedResolver executable warmRuns)
                        validation
                        workspace
                assertEqual "warm separation proof skips Vampire"
                    0
                    =<< readIORef warmRuns
                warm <- sole "warm exact separation module" warmModules
                assertSeparationModule "warm cached" warm
                warmAcceptedRequest <-
                    acceptedRequestId "warm separation" warm
                assertEqual
                    "warm validation retains the fresh request-byte identity"
                    freshAcceptedRequest
                    warmAcceptedRequest
                assertEqual "warm separation semantic interface"
                    (completedModuleSemantic fresh)
                    (completedModuleSemantic warm)
                assertEqual "warm separation final prefix"
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix fresh))
                    (Commit.pendingModulePrefixCurrent
                        (Module.completedTypedModulePrefix warm))
                let components sealed =
                        let batches =
                                Commit.pendingModulePrefixBatches
                                    (Module.completedTypedModulePrefix sealed)
                        in ( concatMap
                                Commit.committedBatchObjects
                                batches
                           , concatMap
                                (fmap Identity.checkedPropositionId
                                    . Commit.committedBatchPropositions)
                                batches
                           , concatMap
                                Commit.committedBatchProofValidations
                                batches
                           , Commit.committedBatchDeclarationValidation
                                <$> batches
                           )
                assertEqual "warm separation checked artefacts"
                    (components fresh)
                    (components warm)
                corruptRuns <- newIORef (0 :: Int)
                let corruptedValidation =
                        WithValidationHandlers
                            (validationHandlers
                                (expectRightIO
                                    . Store.loadProofValidation storeCheck)
                                (\key ->
                                    if key
                                        == Semantic.declarationValidationRecordKey
                                            corruptedDefinitionValidation
                                        then pure
                                            (Just corruptedDefinitionValidation)
                                        else expectRightIO
                                            (Store.loadDeclarationValidation
                                                storeCheck key)))
                corrupted <- Exception.try
                    (compileParsedWorkspaceWithValidation
                        foundation
                        bootstrap
                        (countingAcceptedResolver executable corruptRuns)
                        corruptedValidation
                        workspace)
                    :: IO
                        (Either
                            Declaration.ValidationIntegrityError
                            [Module.CompletedTypedModule])
                case corrupted of
                    Left Declaration.CachedValidationIntegrityError{} ->
                        pure ()
                    Right _ ->
                        assertFailure
                            "mismatched generated authority replay succeeded"
                assertEqual
                    "mismatched generated authority does not invoke Vampire"
                    0
                    =<< readIORef corruptRuns
  where
    acceptedRequestId label sealed = do
        theoremBatch <-
            case Commit.pendingModulePrefixBatches
                    (Module.completedTypedModulePrefix sealed) of
                [_definitionBatch, batch] -> pure batch
                batches ->
                    assertFailure
                        (label <> ": unexpected declaration count "
                            <> show (length batches))
                        >> fail "unreachable"
        validation <- sole
            (label <> " proof validation")
            (Commit.committedBatchProofValidations theoremBatch)
        case Authority.validationDirectAuthorization
                (Semantic.proofValidationRecordCertificate validation) of
            Authority.CheckedSourceProof
                    (Authority.UsesExternalProof (request :| [])) ->
                pure request
            authorization ->
                assertFailure
                    (label <> ": unexpected direct authorization "
                        <> show authorization)
                    >> fail "unreachable"

reusesProofValidationAcrossModuleMisses :: Assertion
reusesProofValidationAcrossModuleMisses =
    Temp.withSystemTempDirectory "felix-exact-proof-cache" \root -> do
        let relative = "test/phase5/exact-proofs.tex"
            producerRelative = "test/phase5/exact-producer.tex"
            sourcePath = root Posix.</> relative
            producerPath = root Posix.</> producerRelative
            executable = root Posix.</> "vampire"
            storePath = root Posix.</> "store.sqlite"
        createDirectoryIfMissing True (Posix.takeDirectory sourcePath)
        original <- ByteString.readFile relative
        producer <- ByteString.readFile producerRelative
        ByteString.writeFile sourcePath original
        ByteString.writeFile producerPath producer
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for exact-cache'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        foundation <- expectRight Foundation.checkedFoundation
        bootstrap <-
            expectRight
                =<< Module.buildBootstrapPreludeFixture
                    foundation
                    unusedResolver
        mounts <- exactFixtureMounts root
        freshWorkspace <- parseWorkspace bootstrap mounts relative
        freshRuns <- newIORef (0 :: Int)
        freshModules <-
            compileParsedWorkspaceWithValidation
                foundation bootstrap
                (countingAcceptedResolver executable freshRuns)
                AlwaysMissValidation
                freshWorkspace
        assertEqual "only the unresolved proof obligation runs Vampire"
            1
            =<< readIORef freshRuns
        freshRoot <- sole "fresh proof root" (drop 1 freshModules)
        bracket
            (snd <$> (Store.openStore storePath
                (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore
            \store -> do
                storeCheck <- Store.newStoreCheck store
                traverse_
                    (expectRightIO
                        . Store.writePendingModulePrefix storeCheck
                        . Module.completedTypedModulePrefix)
                    freshModules
                let validation = storeValidationPolicy storeCheck
                    compileWarm workspace = do
                        runs <- newIORef (0 :: Int)
                        modules <-
                            compileParsedWorkspaceWithValidation
                                foundation bootstrap
                                (countingAcceptedResolver executable runs)
                                validation
                                workspace
                        rootModule <- sole "warm proof root" (drop 1 modules)
                        runCount <- readIORef runs
                        pure (rootModule, runCount)
                (unchangedRoot, unchangedRuns) <-
                    compileWarm freshWorkspace
                assertEqual "exact warm hit skips Vampire"
                    0 unchangedRuns
                assertEqual "exact warm hit preserves public semantics"
                    (completedModuleSemantic freshRoot)
                    (completedModuleSemantic unchangedRoot)

                let formattingOnly =
                        Text.encodeUtf8
                            (StrictText.replace
                                "\\begin{proposition}\\label{phase5_structural_proof}"
                                ("% shifted source location\n"
                                    <> "\\begin{proposition}\\label{phase5_structural_proof}")
                                (Text.decodeUtf8 original))
                ByteString.writeFile sourcePath formattingOnly
                formattedWorkspace <-
                    parseWorkspace bootstrap mounts relative
                assertBool "formatting changes parsed module identity"
                    (Parsed.parsedModuleId
                        (Parsed.parsedWorkspaceRootModule freshWorkspace)
                        /= Parsed.parsedModuleId
                            (Parsed.parsedWorkspaceRootModule formattedWorkspace))
                (formattedRoot, formattedRuns) <-
                    compileWarm formattedWorkspace
                assertEqual "formatting-only module miss reuses proof validation"
                    0 formattedRuns
                assertEqual "formatting-only miss preserves public semantics"
                    (completedModuleSemantic freshRoot)
                    (completedModuleSemantic formattedRoot)

                let semanticEdit =
                        Text.encodeUtf8
                            (StrictText.replace
                                "    We have $x = x$ by assumption."
                                (StrictText.intercalate "\n"
                                    [ "    Show $x = x$."
                                    , "    \\begin{subproof}"
                                    , "        Follows by assumption."
                                    , "    \\end{subproof}"
                                    ])
                                (Text.decodeUtf8 original))
                ByteString.writeFile sourcePath semanticEdit
                editedWorkspace <-
                    parseWorkspace bootstrap mounts relative
                (editedRoot, editedRuns) <-
                    compileWarm editedWorkspace
                assertEqual "the edited exact proof still needs no ATP"
                    0 editedRuns
                let validationKeys = fmap Semantic.proofValidationRecordKey
                        . concatMap Commit.committedBatchProofValidations
                        . Commit.pendingModulePrefixBatches . Module.completedTypedModulePrefix
                assertBool "the source proof edit changes validation identity"
                    (validationKeys freshRoot /= validationKeys editedRoot)
                assertEqual "request-equivalent proof preserves public semantics"
                    (completedModuleSemantic freshRoot)
                    (completedModuleSemantic editedRoot)
loadsCachedProducerForFreshImporter :: Assertion
loadsCachedProducerForFreshImporter = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-exact-cache" \root -> do
        let path = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore path (Identity.theoryId foundation)
                >>= expectRight
        let observer = Verification.verificationRequestObserver \_ordinal _request ->
                pure ()
            prover =
                Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            verify mode source =
                    (checkResultWithStore
                        store mode observer prover source)
                    >>= expectRight
        producer <-
            verify Verification.FreshStoreValidation
                "test/phase5/exact-producer.tex"
        importer <-
            verify Verification.WarmStoreValidation
                "test/phase5/exact-importer.tex"
        assertTypedSuccess "fresh producer" producer
        assertTypedSuccess "warm producer/fresh importer" importer
        storeCheck <- Store.newStoreCheck store
        importCheck <- Declaration.newImportCheck foundation
        prelude <-
            expectRight
                =<< Module.acquireFinalPreludeSession
                    importCheck storeCheck foundation unusedResolver
        preludeVisits <- Store.storeCheckMemoVisits storeCheck
        repository <- getCurrentDirectory
        mounts <- exactFixtureMounts repository
        workspace <- parseFinalWorkspace
            prelude mounts "test/phase5/exact-importer.tex"
        let parsedModules =
                toList
                    (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
            preludeSemantic =
                Module.sealedTypedModuleSemantic
                    (Module.finalPreludeModule prelude)
            preludeId =
                Semantic.semanticInterfaceAssertedId preludeSemantic
            theory = Identity.theoryId foundation
            loadInstallation parsed direct = do
                key <- expectRight
                    (Semantic.moduleArtefactKey
                        (moduleName (Parsed.parsedModuleAddress parsed))
                        (Parsed.parsedModuleId parsed)
                        direct
                        theory)
                loaded <- expectRight
                    =<< Store.loadCachedModuleCandidate
                        storeCheck
                        key
                        (Syntax.moduleSyntaxAssertedId
                            (Parsed.parsedModuleSyntaxInterface parsed))
                maybe
                    (assertFailure "exact cached installation is absent"
                        >> fail "unreachable")
                    pure
                    loaded
            environmentBindings installation =
                [ binding
                | delta <- Semantic.semanticInterfaceDeclarations
                    (Store.cachedCandidateSemantic installation)
                , binding <- Semantic.semanticEnvironmentBindings
                    (Semantic.declarationDeltaEnvironment delta)
                ]
        case parsedModules of
            [producerParsed, importerParsed] -> do
                producerInstallation <-
                    loadInstallation producerParsed [preludeId]
                producerVisits <- Store.storeCheckMemoVisits storeCheck
                assertEqual "ordinary root adds one artefact decode"
                    (Store.storeArtefactRowsDecoded preludeVisits + 1)
                    (Store.storeArtefactRowsDecoded producerVisits)
                assertEqual "ordinary root reuses prelude syntax validation"
                    (Store.storeSyntaxRowsValidated preludeVisits + 1)
                    (Store.storeSyntaxRowsValidated producerVisits)
                assertEqual "ordinary root reuses prelude semantic decode"
                    (Store.storeSemanticRowsDecoded preludeVisits + 1)
                    (Store.storeSemanticRowsDecoded producerVisits)
                let producerSemanticId =
                        Semantic.semanticInterfaceAssertedId
                            (Store.cachedCandidateSemantic
                                producerInstallation)
                importerInstallation <-
                    loadInstallation
                        importerParsed [preludeId, producerSemanticId]
                case ( environmentBindings producerInstallation
                     , environmentBindings importerInstallation
                     ) of
                    (seedBinding : aliasBinding : _definitionBinding : [],
                     [importerBinding]) -> do
                        let seedTarget =
                                Semantic.semanticGlobalTargetObject
                                    (Semantic.semanticGlobalBindingTarget
                                        seedBinding)
                            aliasTarget =
                                Semantic.semanticGlobalTargetObject
                                    (Semantic.semanticGlobalBindingTarget
                                        aliasBinding)
                            importerTarget =
                                Semantic.semanticGlobalTargetObject
                                    (Semantic.semanticGlobalBindingTarget
                                        importerBinding)
                        assertEqual "cached importer reuses expanded content"
                            aliasTarget importerTarget
                        assertEqual "cached importer adds no object"
                            []
                            (Store.cachedCandidateObjects
                                importerInstallation)
                        expandedObject <-
                            maybe
                                (assertFailure
                                    "cached expanded object is absent"
                                    >> fail "unreachable")
                                pure
                                (find
                                    ((== aliasTarget)
                                        . Identity.assertedObjectId)
                                    (Store.cachedCandidateObjects
                                        producerInstallation))
                        case Identity.assertedObjectContent expandedObject of
                            Identity.TransparentObjectContent
                                    _identity _coreType body ->
                                assertEqual
                                    "cached expansion retains the opaque seed"
                                    (Set.singleton seedTarget)
                                    (Core.canonicalTermGlobals body)
                            content ->
                                assertFailure
                                    ("cached expansion is not transparent: "
                                        <> show content)
                    (producerBindings, importerBindings) ->
                        assertFailure
                            ("unexpected cached exact bindings: "
                                <> show
                                    ( length producerBindings
                                    , length importerBindings
                                    ))
            modules ->
                assertFailure
                    ("unexpected cached exact module count: "
                        <> show (length modules))
        Store.closeStore store

reportsAdmittedSourceEscapes :: Assertion
reportsAdmittedSourceEscapes = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-admitted-source-report" \root -> do
        let storePath = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
            unavailable = root Posix.</> "must-not-run-vampire"
            observer =
                Verification.verificationRequestObserver \_ordinal _request -> pure ()
            prover path =
                Provers.vampire
                    path
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            let verify mode vampirePath source =
                        (checkFileWithStore
                            openStore
                            mode
                            observer
                            (prover vampirePath)
                            source)
                        >>= expectRight
                reportEntries =
                    fmap
                        (\escape ->
                            ( Verification.reportedEscapeKind escape
                            , locFile (Verification.reportedEscapeLocation escape)
                            , locLine (Verification.reportedEscapeLocation escape)
                            ))
                        . Verification.verificationDirectEscapes
                expectedConsumer =
                    [ ( Verification.ReportedSourceAxiom
                      , "test/phase5/exact-escape-producer.tex"
                      , 1
                      )
                    , ( Verification.ReportedOmitted
                      , "test/phase5/exact-escape-producer.tex"
                      , 9
                      )
                    , ( Verification.ReportedOmitted
                      , "test/phase5/exact-escape-consumer.tex"
                      , 35
                      )
                    ]
            (freshResult, _freshSlowReport) <-
                verify
                    Verification.FreshStoreValidation
                    executable
                    "test/phase5/exact-escape-consumer.tex"
            freshReport <- case freshResult of
                Verification.CompletedWithExplicitGaps report _presentation -> pure report
                other ->
                    assertFailure
                        ("fresh escape report did not complete with gaps: "
                            <> show other)
                        >> fail "unreachable"
            assertEqual "fresh direct escapes"
                expectedConsumer
                (reportEntries freshReport)
            (warmResult, _warmSlowReport) <-
                verify
                    Verification.WarmStoreValidation
                    unavailable
                    "test/phase5/exact-escape-consumer.tex"
            warmReport <- case warmResult of
                Verification.CompletedWithExplicitGaps report _presentation -> pure report
                other ->
                    assertFailure
                        ("warm escape report did not complete with gaps: "
                            <> show other)
                        >> fail "unreachable"
            assertEqual "warm report uses rebound current locations"
                freshReport warmReport

            void
                (verify
                    Verification.FreshStoreValidation
                    executable
                    "test/phase5/exact-source-axiom.tex")
            (failedResult, _failedSlowReport) <-
                verify
                    Verification.WarmStoreValidation
                    unavailable
                    "test/phase6/admitted-prefix-failure.tex"
            failedReport <- case failedResult of
                Verification.VerificationCheckingFailure report _failure -> pure report
                other ->
                    assertFailure
                        ("typed suffix failure was not report-bearing: "
                            <> show other)
                        >> fail "unreachable"
            assertEqual "failure report retains only admitted source prefix"
                (take 2 expectedConsumer
                    <> [ ( Verification.ReportedOmitted
                         , "test/phase6/admitted-prefix-failure.tex"
                         , 7
                         )
                       ])
                (reportEntries failedReport)

retainsPrefixBeforeFailure :: Assertion
retainsPrefixBeforeFailure = do
    result <-
        withAcceptedFixtureVampire "felix-exact-failure" \prover ->
                (checkFileFresh
                    prover
                    "test/phase5/exact-failure.tex")
    case result of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                source
                (Module.TypedActionFailed
                    (Module.TypedElaborationFailed
                        (Elaboration.ElaborationGuardedOpaqueSignature location)))
                prefix)
            , _slowReport
            ) -> do
            assertEqual "failed exact source"
                "test/phase5/exact-failure.tex"
                (safeRelativePathFilePath
                    (resolvedSourceRelativePath source))
            assertEqual "unsupported declaration line" 6 (locLine location)
            assertEqual "earlier declaration remains committed"
                1
                (length (Commit.pendingModulePrefixBatches prefix))
        Left err ->
            assertFailure ("unexpected exact failure: " <> show err)
        Right{} ->
            assertFailure "unsupported declaration was admitted"

    proofFailure <-
        withAcceptedFixtureVampire "felix-exact-proof-failure" \prover ->
                (checkFileFresh
                    prover
                    "test/phase5/exact-proof-failure.tex")
    case proofFailure of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                _source
                    (Module.TypedActionFailed
                    (Module.TypedProofFailed
                        (Proof.ProofAssumptionOpeningFailed
                            location
                            (LooseDeduction.AssumptionPartUnavailable{}))))
                prefix)
            , _slowReport
            ) -> do
            assertEqual "mismatched assumption line" 10 (locLine location)
            assertEqual "failed proof publishes no theorem"
                1
                (length (Commit.pendingModulePrefixBatches prefix))
        Left err ->
            assertFailure
                ("unexpected proof failure: " <> show err)
        Right{} ->
            assertFailure "mismatched proof was admitted"

    unmatched <-
        withAcceptedFixtureVampire "felix-unmatched-proof" \prover ->
                (checkFileFresh
                    prover
                    "test/phase5/unmatched-proof.tex")
    case unmatched of
        Right
            ( Verification.VerificationCheckingFailure _report
                (Verification.VerificationTypedModuleError
                _source
                (Module.TypedActionFailed
                    (Module.TypedUnmatchedProof location))
                prefix)
            , _slowReport
            ) -> do
            assertEqual "unmatched proof line" 1 (locLine location)
            assertEqual "unmatched proof publishes no declaration"
                0
                (length (Commit.pendingModulePrefixBatches prefix))
        Left err ->
            assertFailure
                ("unexpected unmatched-proof failure: " <> show err)
        Right{} ->
            assertFailure "unmatched proof was admitted"

    runtimeFailure <-
        Temp.withSystemTempDirectory "felix-runtime-proof-failure" \root -> do
            foundation <- expectRight Foundation.checkedFoundation
            bootstrap <-
                expectRight
                    =<< Module.buildBootstrapPreludeFixture
                        foundation
                        unusedResolver
            repository <- getCurrentDirectory
            mounts <- exactFixtureMounts repository
            workspace <- parseWorkspace
                bootstrap mounts "test/phase5/exact-runtime-failure.tex"
            let executable = root Posix.</> "vampire"
            writeFile executable
                (unlines
                    [ "#!/bin/sh"
                    , "cat >/dev/null"
                    , "printf '%s\\n' '% SZS status Theorem for located-proof'"
                    ])
            permissions <- getPermissions executable
            setPermissions executable
                (setOwnerExecutable True permissions)
            runs <- newIORef (0 :: Int)
            let resolver = Declaration.vampireResolver \prepared -> do
                    runNumber <- readIORef runs
                    modifyIORef' runs (+ 1)
                    if runNumber == 0
                        then
                            (Provers.runPreparedTypedProver
                                    (Provers.vampire
                                        executable
                                        Provers.defaultTimeLimit
                                        Provers.defaultMemoryLimit)
                                    prepared)
                        else
                            pure
                                (counterexampleResolution prepared)
                parsed = Parsed.parsedWorkspaceRootModule workspace
            input <- expectRightIO
                (typedModuleInput
                    foundation
                    (Module.bootstrapPreludeReadiness bootstrap)
                    resolver
                    AlwaysMissValidation
                    parsed
                    [])
            runTypedModule input
    case runtimeFailure of
        Module.TypedModuleFailed
                failure@(Module.TypedDeclarationFailed
                    (Declaration.ProofObligationFailedAt
                        location
                        Declaration.VampireObligationFailed{}))
                prefix -> do
            assertEqual "later rejected obligation line"
                11
                (locLine location)
            assertEqual "typed failure retains obligation location"
                (Just location)
                (Module.typedModuleFailureLocation failure)
            assertEqual "runtime proof failure publishes no theorem"
                1
                (length (Commit.pendingModulePrefixBatches prefix))
        _result ->
            assertFailure "unexpected runtime proof failure"

installsNonemptyImplicitPreludeEvidence :: Assertion
installsNonemptyImplicitPreludeEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    closure <- expectRight
        (Identity.validateObjectClosure
            (Identity.theoryId foundation)
            [])
    proposition <- expectRight
        (Identity.validatePropositionContent closure Core.CFalsum)
    let successorObject =
            Identity.transparentObject
                (Identity.theoryId foundation)
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet
                    (Core.canonicalSetInsert
                        (Core.CBound 0)
                        (Core.CBound 0)))
        successor = Identity.assertedObjectId successorObject
        wrongTypedSuccessor =
            Identity.transparentObject
                (Identity.theoryId foundation)
                Core.TySet
                (Core.CIntrinsic Core.Empty)
        opaqueSuccessor =
            Identity.opaqueObject
                (Identity.theoryId foundation)
                (Identity.opaqueDeclarationSeed
                    preludeModuleName
                    (localDeclarationOrdinal 99)
                    SignatureDeclaration
                    (generatedObjectSlot 0))
                (Core.TyArrow Core.TySet Core.TySet)
        wrongBodiedSuccessor =
            Identity.transparentObject
                (Identity.theoryId foundation)
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet (Core.CBound 0))
        absentSuccessor =
            Identity.transparentObject
                (Identity.theoryId foundation)
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet (Core.CIntrinsic Core.Empty))
        retainedSuccessorCandidates =
            [ successorObject
            , wrongTypedSuccessor
            , opaqueSuccessor
            , wrongBodiedSuccessor
            ]
    preludeDriver <- runModuleDriver
        foundation
        preludeModuleName
        []
        unusedResolver
        AlwaysMissValidation
        do
            _ <- DeclTest.admitCompiled
                (Semantic.declarationSyntaxId "natural-numeral-successor")
                retainedSuccessorCandidates [] [] (const (pure ()))
            DeclTest.admitProof
                (Semantic.proofSyntaxId "nonempty-prelude") []
                    (Declaration.checkedCandidate (Declaration.candidateSpec
                            proposition
                            Semantic.SearchEligible
                            [Semantic.semanticName "prelude-fact"]) Declaration.checkedSourceAxiomPlanning) \candidate -> do
                    Declaration.authorizeSourceAxiomCandidate candidate
    preludeResult <- expectRight preludeDriver
    (preludeSemantic, preludePrefix) <-
        case preludeResult of
            Declaration.DriverSucceeded _value evidence prefix ->
                pure (Declaration.evidenceInterface evidence, prefix)
            _ ->
                assertFailure "nonempty prelude fixture did not seal"
                    >> fail "unreachable"
    preludeFingerprint <-
        case concatMap
                Semantic.declarationDeltaFacts
                (Semantic.semanticInterfaceDeclarations preludeSemantic) of
            [occurrence] ->
                pure (Semantic.semanticFactFingerprint occurrence)
            facts ->
                assertFailure
                    ("unexpected prelude fact count: "
                        <> show (length facts))
                    >> fail "unreachable"
    let preludeSyntax =
            completedModuleSyntax
                (Module.bootstrapPreludeCompleted bootstrap)
    nonemptyPrelude <-
        Temp.withSystemTempDirectory "felix-nonempty-prelude" \directory -> do
            let path = directory Posix.</> "store.sqlite"
                theory = Identity.theoryId foundation
                parsed =
                    Module.identifiedModuleParsed
                        (Module.bootstrapPreludeInput bootstrap)
            (_startup, store) <-
                Store.openStore path theory >>= expectRight
            storeCheck <- Store.newStoreCheck store
            artefactKey <- expectRight
                (Semantic.moduleArtefactKey
                    preludeModuleName
                    (Parsed.identifiedParsedModuleId parsed)
                    []
                    theory)
            expectRight =<< Store.writeSealedModule storeCheck artefactKey
                preludePrefix preludeSyntax preludeSemantic
            loaded <- expectRight
                =<< Store.loadCachedModuleCandidate
                    storeCheck
                    artefactKey
                    (Syntax.moduleSyntaxAssertedId preludeSyntax)
            installation <- maybe
                (assertFailure "nonempty prelude was not installed"
                    >> fail "unreachable")
                pure
                loaded
            checkedImports <- prepareTestImports theory []
            sealed <- expectRightIO
                (Module.cachedSealedTypedModule checkedImports installation)
            Store.closeStore store
            pure sealed

    root <- getCurrentDirectory
    mounts <-
        expectRight
            =<< prepareSourceMounts
                [ (sourceMountId "project", root)
                , (sourceMountId "library", root Posix.</> "library")
                , (sourceMountId "debug", root Posix.</> "debug")
                ]
    request <- expectRight
        (searchedRoot "test/phase3/typed-producer.tex")
    workspace <-
        expectRight
            =<< Parse.parseSourceWorkspaceWithSyntaxInputs
                mounts
                request
                (const [preludeSyntax])
    let parsed = Parsed.parsedWorkspaceRootModule workspace
        expectRejected label object =
            case Module.fixtureFinalPreludeReadinessFromSealed
                    foundation
                    (Identity.assertedObjectId object)
                    nonemptyPrelude of
                Left{} -> pure ()
                Right{} ->
                    assertFailure
                        (label <> " entered final-prelude readiness")
    expectRejected "wrong-typed successor" wrongTypedSuccessor
    expectRejected "opaque successor" opaqueSuccessor
    expectRejected "wrong-bodied successor" wrongBodiedSuccessor
    expectRejected "successor absent from the retained closure" absentSuccessor
    readiness <- expectRight
        (Module.fixtureFinalPreludeReadinessFromSealed
            foundation
            successor
            nonemptyPrelude)
    input <- expectRightIO
        (typedModuleInput
            foundation
            readiness
            unusedResolver
            AlwaysMissValidation
            parsed
            [])
    ordinary <- runTypedModule input >>= \case
        Module.TypedModuleSucceeded sealed -> pure sealed
        _ ->
            assertFailure "ordinary module rejected the nonempty prelude"
                >> fail "unreachable"

    let consumerDigest =
            hashBlake2b256 "implicit-prelude-consumer\NULconsumer"
    consumerPath <- expectRight (safeRelativePath "consumer.tex")
    let consumerOwner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest consumerDigest)
                consumerPath
    consumed <- runModuleDriver
        foundation
        consumerOwner
        [completedModuleEvidence ordinary]
        unusedResolver
        AlwaysMissValidation
        do
            DeclTest.admitProof
                (Semantic.proofSyntaxId "use-implicit-prelude") []
                    (Declaration.checkedCandidate (Declaration.candidateSpec
                            proposition
                            Semantic.SearchIneligible
                            [])
                        (Declaration.checkedOmittedPlanning [] [preludeFingerprint] [])) \candidate -> do
                    Declaration.authorizeOmittedCandidate candidate do
                        void
                            (Declaration.useAuthorizedFact
                                preludeFingerprint)
                        Declaration.recordOmittedUse
    consumedResult <- expectRight consumed
    case consumedResult of
        Declaration.DriverSucceeded{} -> pure ()
        _ ->
            assertFailure
                "implicit prelude fact was not transitively visible"
