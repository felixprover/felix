{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Shared typed-module fixtures used by both behavioural test groups.
module Felix.Test.Unit.Module.Support where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.ValidationCache qualified as ValidationCache
import Felix.Module
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Provers qualified as Provers
import Felix.Source
import Felix.Store qualified as Store
import Felix.Syntax.Interface qualified as Syntax
import Felix.Test.Support.Imports
import Felix.Verification qualified as Verification
import Felix.Workspace qualified as Workspace

import Control.Concurrent (threadDelay)
import Control.Monad (foldM)
import Data.IORef
    ( IORef
    , modifyIORef'
    )
import Data.Map.Strict qualified as Map
import Effectful (Eff, IOE, (:>), runEff)
import System.Directory
    ( doesFileExist
    , getCurrentDirectory
    , getPermissions
    , setOwnerExecutable
    , setPermissions
    )
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import System.Timeout qualified as Timeout
import Test.Tasty.HUnit


-- Fresh compiler fixtures retain their actual batches. Observations used by
-- mathematical assertions project the importable view explicitly.
completedModuleOwner :: Module.CompletedTypedModule -> ModuleName
completedModuleOwner = Module.sealedTypedModuleOwner . Module.completedTypedModuleSealed

completedModuleSyntax :: Module.CompletedTypedModule -> Syntax.ModuleSyntaxInterface
completedModuleSyntax = Module.sealedTypedModuleSyntax . Module.completedTypedModuleSealed

completedModuleSemantic :: Module.CompletedTypedModule -> Semantic.SemanticInterface
completedModuleSemantic = Module.sealedTypedModuleSemantic . Module.completedTypedModuleSealed

completedModuleEvidence :: Module.CompletedTypedModule -> Declaration.ImportedModuleEvidence
completedModuleEvidence = Module.sealedTypedModuleEvidence . Module.completedTypedModuleSealed

data ValidationHandlers = ValidationHandlers
    !(Semantic.ProofValidationKey
        -> IO (Maybe Semantic.ProofValidationRecord))
    !(Semantic.DeclarationValidationKey
        -> IO (Maybe Semantic.DeclarationValidationRecord))

data TestValidationPolicy
    = AlwaysMissValidation
    | WithValidationHandlers !ValidationHandlers

validationHandlers
    :: (Semantic.ProofValidationKey
        -> IO (Maybe Semantic.ProofValidationRecord))
    -> (Semantic.DeclarationValidationKey
        -> IO (Maybe Semantic.DeclarationValidationRecord))
    -> ValidationHandlers
validationHandlers = ValidationHandlers

runTestValidation
    :: IOE :> es
    => TestValidationPolicy
    -> Eff (ValidationCache.ValidationCache : es) value
    -> Eff es value
runTestValidation AlwaysMissValidation =
    ValidationCache.runValidationCacheAlwaysMiss
runTestValidation (WithValidationHandlers (ValidationHandlers proof declaration)) =
    ValidationCache.runValidationCacheWith
        (liftIO . proof)
        (liftIO . declaration)

storeValidationPolicy :: Store.StoreCheck -> TestValidationPolicy
storeValidationPolicy storeCheck =
    WithValidationHandlers
        (validationHandlers
            (expectRightIO . Store.loadProofValidation storeCheck)
            (expectRightIO . Store.loadDeclarationValidation storeCheck))

runModuleDriver
    :: Foundation.CheckedFoundation
    -> ModuleName
    -> [Declaration.ImportedModuleEvidence]
    -> Declaration.VampireResolver
    -> TestValidationPolicy
    -> Declaration.ModuleDriver failure value
    -> IO
        (Either
            Declaration.DriverOpenError
            (Declaration.DriverResult failure value))
runModuleDriver foundation owner direct resolver validation action = do
    imports <- prepareTestImports (Identity.theoryId foundation) direct
    runEff
        (runTestValidation validation
            (Declaration.runModuleDriverEff
                foundation owner imports resolver action))

data TestTypedModuleInput = TestTypedModuleInput
    !TestValidationPolicy
    !Module.TypedModuleInput

typedModuleInput
    :: Foundation.CheckedFoundation
    -> Module.FinalPreludeReadiness
    -> Declaration.VampireResolver
    -> TestValidationPolicy
    -> Parsed.ParsedModule
    -> [Module.CompletedTypedModule]
    -> IO (Either Module.TypedModuleInputError TestTypedModuleInput)
typedModuleInput foundation readiness resolver validation parsed direct =
    typedSealedModuleInput foundation readiness resolver validation parsed
        (Module.completedTypedModuleSealed <$> direct)

typedSealedModuleInput
    :: Foundation.CheckedFoundation
    -> Module.FinalPreludeReadiness
    -> Declaration.VampireResolver
    -> TestValidationPolicy
    -> Parsed.ParsedModule
    -> [Module.SealedTypedModule]
    -> IO (Either Module.TypedModuleInputError TestTypedModuleInput)
typedSealedModuleInput foundation readiness resolver validation parsed direct = do
    check <- Declaration.newImportCheck foundation
    fmap (TestTypedModuleInput validation)
        <$> Module.typedModuleInput check foundation readiness resolver parsed direct

runTypedModule
    :: TestTypedModuleInput
    -> IO Module.TypedModuleResult
runTypedModule (TestTypedModuleInput validation input) =
    runEff
        (runTestValidation validation
            (Module.runTypedModuleEff input))


counterexampleResolution
    :: Provers.PreparedTypedProverTask ref local origin global
    -> Provers.VampireResolution
counterexampleResolution prepared =
    Provers.rejectedVampireResolution
        (Provers.preparedTypedProverRequest prepared)
        Provers.RejectedCounterexample

unusedResolver :: Declaration.VampireResolver
unusedResolver =
    Declaration.vampireResolver \_prepared ->
        fail "empty bootstrap invoked Vampire"

writeAcceptedFixtureVampire :: FilePath -> IO ()
writeAcceptedFixtureVampire executable = do
    writeFile executable
        (unlines
            [ "#!/bin/sh"
            , "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for typed-fixture'"
            ])
    permissions <- getPermissions executable
    setPermissions executable
        (setOwnerExecutable True permissions)

withAcceptedFixtureVampire
    :: String
    -> (Provers.Vampire -> IO value)
    -> IO value
withAcceptedFixtureVampire label action =
    Temp.withSystemTempDirectory label \directory -> do
        let executable = directory Posix.</> "vampire"
        writeAcceptedFixtureVampire executable
        action
            (Provers.vampire
                executable
                Provers.defaultTimeLimit
                Provers.defaultMemoryLimit)

finalPreludeResolver :: Declaration.VampireResolver
finalPreludeResolver =
    Declaration.vampireResolver \prepared ->
        (Provers.runPreparedTypedProver
                (Provers.vampire
                    "vampire"
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared)

countingAcceptedResolver
    :: FilePath
    -> IORef Int
    -> Declaration.VampireResolver
countingAcceptedResolver executable runs =
    Declaration.vampireResolver \prepared -> do
        modifyIORef' runs (+ 1)
        (Provers.runPreparedTypedProver
                (Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit)
                prepared)

compileFixture
    :: FilePath
    -> IO
        ( Foundation.CheckedFoundation
        , Module.BootstrapPreludeFixture
        , Parsed.ParsedSourceWorkspace
        , [Module.CompletedTypedModule]
        )
compileFixture relative = do
    root <- getCurrentDirectory
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts root
    workspace <- parseWorkspace bootstrap mounts relative
    sealed <- compileParsedWorkspace foundation bootstrap workspace
    pure (foundation, bootstrap, workspace, sealed)

compileRootAt
    :: FilePath
    -> FilePath
    -> IO (Parsed.ParsedSourceWorkspace, Module.CompletedTypedModule)
compileRootAt projectRoot relative = do
    foundation <- expectRight Foundation.checkedFoundation
    bootstrap <-
        expectRight
            =<< Module.buildBootstrapPreludeFixture
                foundation
                unusedResolver
    mounts <- exactFixtureMounts projectRoot
    workspace <- parseWorkspace bootstrap mounts relative
    sealed <- compileParsedWorkspace foundation bootstrap workspace
    rootModule <- sole "exact root module" (reverse sealed)
    pure (workspace, rootModule)

exactFixtureMounts :: FilePath -> IO SourceMounts
exactFixtureMounts projectRoot = do
    repository <- getCurrentDirectory
    expectRight
        =<< prepareSourceMounts
            [ (sourceMountId "project", projectRoot)
            , (sourceMountId "library", repository Posix.</> "library")
            , (sourceMountId "debug", repository Posix.</> "debug")
            ]

parseWorkspace
    :: Module.BootstrapPreludeFixture
    -> SourceMounts
    -> FilePath
    -> IO Parsed.ParsedSourceWorkspace
parseWorkspace bootstrap mounts relative =
    parseWorkspaceWithPrelude
        (Module.completedTypedModuleSealed (Module.bootstrapPreludeCompleted bootstrap))
        mounts
        relative

parseFinalWorkspace
    :: Module.FinalPreludeSession
    -> SourceMounts
    -> FilePath
    -> IO Parsed.ParsedSourceWorkspace
parseFinalWorkspace prelude mounts relative =
    parseWorkspaceWithPrelude
        (Module.finalPreludeModule prelude)
        mounts
        relative

parseWorkspaceWithPrelude
    :: Module.SealedTypedModule
    -> SourceMounts
    -> FilePath
    -> IO Parsed.ParsedSourceWorkspace
parseWorkspaceWithPrelude prelude mounts relative = do
    request <- expectRight (searchedRoot relative)
    let preludeSyntax =
            Module.sealedTypedModuleSyntax
                prelude
    expectRight
        =<< Parse.parseSourceWorkspaceWithSyntaxInputs
            mounts
            request
            (const [preludeSyntax])

compileParsedWorkspace
    :: Foundation.CheckedFoundation
    -> Module.BootstrapPreludeFixture
    -> Parsed.ParsedSourceWorkspace
    -> IO [Module.CompletedTypedModule]
compileParsedWorkspace foundation bootstrap workspace =
    compileParsedWorkspaceWithResolver
        foundation
        bootstrap
        unusedResolver
        workspace

compileParsedWorkspaceWithResolver
    :: Foundation.CheckedFoundation
    -> Module.BootstrapPreludeFixture
    -> Declaration.VampireResolver
    -> Parsed.ParsedSourceWorkspace
    -> IO [Module.CompletedTypedModule]
compileParsedWorkspaceWithResolver foundation bootstrap resolver workspace =
    compileParsedWorkspaceWithValidation
        foundation
        bootstrap
        resolver
        AlwaysMissValidation
        workspace

compileParsedWorkspaceWithValidation
    :: Foundation.CheckedFoundation
    -> Module.BootstrapPreludeFixture
    -> Declaration.VampireResolver
    -> TestValidationPolicy
    -> Parsed.ParsedSourceWorkspace
    -> IO [Module.CompletedTypedModule]
compileParsedWorkspaceWithValidation
        foundation bootstrap resolver validation workspace =
    compileParsedWorkspaceWithReadiness
        foundation
        (Module.bootstrapPreludeReadiness bootstrap)
        resolver
        validation
        workspace

compileFinalParsedWorkspaceWithResolver
    :: Foundation.CheckedFoundation
    -> Module.FinalPreludeSession
    -> Declaration.VampireResolver
    -> Parsed.ParsedSourceWorkspace
    -> IO [Module.CompletedTypedModule]
compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace =
    compileParsedWorkspaceWithReadiness
        foundation
        (Module.finalPreludeReadiness prelude)
        resolver
        AlwaysMissValidation
        workspace

compileParsedWorkspaceWithReadiness
    :: Foundation.CheckedFoundation
    -> Module.FinalPreludeReadiness
    -> Declaration.VampireResolver
    -> TestValidationPolicy
    -> Parsed.ParsedSourceWorkspace
    -> IO [Module.CompletedTypedModule]
compileParsedWorkspaceWithReadiness
        foundation readiness resolver validation workspace =
    snd
        <$> foldM
            compileOne
            (Map.empty, [])
            (toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))
  where
    compileOne (admitted, ordered) parsed = do
        direct <-
            traverse
                (\address ->
                    maybe
                        (assertFailure
                            ("missing exact direct module: " <> show address)
                            >> fail "unreachable")
                        pure
                        (Map.lookup address admitted))
                (nubOrd
                    (Parsed.parsedImportedAddress
                        <$> Parsed.parsedModuleImports parsed))
        input <-
            expectRightIO
                (typedModuleInput
                    foundation
                    readiness
                    resolver
                    validation
                    parsed
                    direct)
        sealed <-
            runTypedModule input >>= \case
                Module.TypedModuleSucceeded module' -> pure module'
                Module.TypedModuleOpenFailed failure ->
                    assertFailure
                        ("exact module did not open: " <> show failure)
                        >> fail "unreachable"
                Module.TypedModuleFailed failure _prefix ->
                    assertFailure
                        ("exact module did not seal: " <> show failure)
                        >> fail "unreachable"
        pure
            ( Map.insert (Parsed.parsedModuleAddress parsed) sealed admitted
            , ordered <> [sealed]
            )

checkFileFresh
    :: Provers.Vampire
    -> FilePath
    -> IO
        (Either
            Verification.VerificationDriverError
            (Verification.VerificationResult, Provers.SlowAtpReport))
checkFileFresh prover source =
    withFreshVerificationSession \session ->
        checkFileWithSession
            session
            Verification.FreshStoreValidation
            testSequentialJobs
            ignoredVerificationRequests
            prover
            source

withFreshVerificationSession
    :: (Verification.VerificationSession -> IO value)
    -> IO value
withFreshVerificationSession action = do
    plan <- Store.planStore Store.FreshTemporaryStore >>= expectRight
    withTestStoreLease plan \lease -> do
        opened <- Verification.withVerificationSession lease action
        case opened of
            Left failure ->
                assertFailure
                    ("test verification session failed: " <> show failure)
                    >> fail "unreachable"
            Right result -> pure result

checkFileWithStore
    :: Store.Store
    -> Verification.StoreValidationMode
    -> Verification.VerificationRequestObserver
    -> Provers.Vampire
    -> FilePath
    -> IO
        (Either
            Verification.VerificationDriverError
            (Verification.VerificationResult, Provers.SlowAtpReport))
checkFileWithStore store mode =
    checkFileWithStoreAndJobs store mode testSequentialJobs

checkFileWithStoreAndJobs
    :: Store.Store
    -> Verification.StoreValidationMode
    -> Provers.EffectiveJobs
    -> Verification.VerificationRequestObserver
    -> Provers.Vampire
    -> FilePath
    -> IO
        (Either
            Verification.VerificationDriverError
            (Verification.VerificationResult, Provers.SlowAtpReport))
checkFileWithStoreAndJobs store mode jobs observer prover source = do
    opened <- Verification.withVerificationSessionUsingStore store
        (\session ->
            checkFileWithSession session mode jobs observer prover source)
    case opened of
        Left failure ->
            assertFailure
                ("test verification session failed: " <> show failure)
                >> fail "unreachable"
        Right result -> pure result

checkResultWithStore
    :: Store.Store
    -> Verification.StoreValidationMode
    -> Verification.VerificationRequestObserver
    -> Provers.Vampire
    -> FilePath
    -> IO
        (Either
            Verification.VerificationDriverError
            Verification.VerificationResult)
checkResultWithStore store mode observer prover source =
    fmap (fmap fst)
        (checkFileWithStore store mode observer prover source)

checkFileWithSession
    :: Verification.VerificationSession
    -> Verification.StoreValidationMode
    -> Provers.EffectiveJobs
    -> Verification.VerificationRequestObserver
    -> Provers.Vampire
    -> FilePath
    -> IO
        (Either
            Verification.VerificationDriverError
            (Verification.VerificationResult, Provers.SlowAtpReport))
checkFileWithSession session mode jobs observer prover source =
    Workspace.prepareDefaultSourceGraph source >>= \case
        Left failure ->
            pure (Left (Verification.VerificationWorkspaceError failure))
        Right graph ->
            fmap
                (fmap
                    (\outcome ->
                        ( Verification.checkVerificationResult outcome
                        , Verification.checkSlowAtpReport outcome
                        )))
                (Verification.checkWorkspace
                    session
                    Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand =
                            Parse.NoPresentation
                        , Verification.checkStoreValidationMode = mode
                        , Verification.checkModuleJobs = jobs
                        , Verification.checkProverJobs = jobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = observer
                        })

ignoredVerificationRequests :: Verification.VerificationRequestObserver
ignoredVerificationRequests =
    Verification.verificationRequestObserver
        (\_position _request -> pure ())

testSequentialJobs :: Provers.EffectiveJobs
testSequentialJobs =
    fromMaybe
        (impossible "one is a positive worker count")
        (Provers.effectiveJobs 1)

assertTypedSuccess :: String -> Verification.VerificationResult -> Assertion
assertTypedSuccess label = \case
    Verification.VerificationCompleted
            _report Verification.PresentationNotRequested ->
        pure ()
    Verification.VerificationCompleted
            _report Verification.PresentationAvailable{} ->
        assertFailure (label <> " retained unrequested presentation")
    Verification.CompletedWithExplicitGaps
            _report Verification.PresentationNotRequested ->
        assertFailure (label <> " completed with gaps")
    Verification.CompletedWithExplicitGaps
            _report Verification.PresentationAvailable{} ->
        assertFailure (label <> " retained unrequested presentation")
    Verification.VerificationFailure _report failure ->
        assertFailure (label <> " failed: " <> show failure)
    Verification.VerificationCheckingFailure _report failure ->
        assertFailure (label <> " failed: " <> show failure)

assertConstructionAliasTargetsFirstOrderView
    :: String
    -> Commit.CommittedDeclarationBatch
    -> Assertion
assertConstructionAliasTargetsFirstOrderView label batch = do
    let delta = Commit.committedBatchDelta batch
        facts = Semantic.declarationDeltaFacts delta
    alias <- sole
        (label <> " alias")
        (Semantic.declarationDeltaAliases delta)
    extensional <- sole
        (label <> " searchable extensional fact")
        [ occurrence
        | occurrence <- facts
        , Semantic.semanticFactSearchEligibility occurrence
            == Semantic.SearchEligible
        ]
    assertEqual
        (label <> " alias targets the extensional fact")
        (Semantic.semanticFactFingerprint extensional)
        (Semantic.semanticAliasTarget alias)
    proposition <- sole
        (label <> " extensional proposition")
        [ candidate
        | candidate <- Commit.committedBatchPropositions batch
        , Identity.checkedPropositionId candidate
            == Semantic.semanticFactProposition extensional
        ]
    assertEqual
        (label <> " public definition view is first-order")
        Foundation.FoundationFofProjectable
        (Foundation.classifyFrozenCore
            (Identity.checkedPropositionTerm proposition))

assertSeparationModule
    :: String
    -> Module.CompletedTypedModule
    -> Assertion
assertSeparationModule label sealed = do
    case Commit.pendingModulePrefixBatches
            (Module.completedTypedModulePrefix sealed) of
        [definitionBatch, theoremBatch] -> do
            assertEqual (label <> " separation definition object count")
                1
                (length
                    (Commit.committedBatchObjects definitionBatch))
            definitionObject <- sole
                (label <> " separation definition object")
                (Commit.committedBatchObjects definitionBatch)
            case Identity.assertedObjectContent definitionObject of
                Identity.TransparentObjectContent
                        _theory coreType body -> do
                    assertEqual (label <> " separation definition type")
                        (Core.TyArrow Core.TySet Core.TySet)
                        coreType
                    assertEqual (label <> " separation definition body")
                        (Core.CLam Core.TySet
                            (Core.CApp
                                (Core.CApp
                                    (Core.CIntrinsic Core.Sep)
                                    (Core.CBound 0))
                                (Core.CLam Core.TySet
                                    (Core.CEq Core.TySet
                                        (Core.CBound 0)
                                        (Core.CBound 0)))))
                        body
                content ->
                    assertFailure
                        (label <> ": unexpected separation object "
                            <> show content)
            let definitionDelta =
                    Commit.committedBatchDelta definitionBatch
                definitionFacts =
                    Semantic.declarationDeltaFacts definitionDelta
            assertEqual (label <> " definition fact count")
                2 (length definitionFacts)
            assertEqual (label <> " exact equation is internal-only")
                [Semantic.SearchIneligible, Semantic.SearchEligible]
                (Semantic.semanticFactSearchEligibility <$> definitionFacts)
            assertConstructionAliasTargetsFirstOrderView
                (label <> " definition") definitionBatch
            assertEqual (label <> " definition proposition count")
                2
                (length
                    (Commit.committedBatchPropositions definitionBatch))
            assertEqual (label <> " definition proof validations")
                []
                (Commit.committedBatchProofValidations definitionBatch)
            definitionValidation <-
                maybe
                    (assertFailure
                        (label <> ": definition validation is absent")
                        >> fail "unreachable")
                    pure
                    (Commit.committedBatchDeclarationValidation
                        definitionBatch)
            case Authority.validationDirectAuthorization
                    <$> Semantic.declarationValidationRecordCertificates
                        definitionValidation of
                [ Authority.CheckedKernelConstruction
                        (Authority.CheckedDefinitionEquation target)
                  , Authority.CheckedKernelConstruction
                        (Authority.CheckedSetConstructionExtensionality
                            generatedTarget _descriptor)
                  ] ->
                    assertEqual
                        (label <> " construction authority object")
                        target generatedTarget
                authorizations ->
                    assertFailure
                        (label <> ": unexpected definition authorities "
                            <> show authorizations)

            assertEqual (label <> " theorem adds no object")
                []
                (Commit.committedBatchObjects theoremBatch)
            theoremFact <- sole
                (label <> " separation theorem fact")
                (Semantic.declarationDeltaFacts
                    (Commit.committedBatchDelta theoremBatch))
            assertEqual (label <> " theorem safety")
                Authority.cleanAuthoritySafety
                (Authority.factAuthoritySafety
                    (Semantic.semanticFactAuthority theoremFact))
            theoremValidation <- sole
                (label <> " separation theorem validation")
                (Commit.committedBatchProofValidations theoremBatch)
            case Authority.validationDirectAuthorization
                    (Semantic.proofValidationRecordCertificate
                        theoremValidation) of
                Authority.CheckedSourceProof
                        (Authority.UsesExternalProof (_request :| [])) ->
                    pure ()
                authorization ->
                    assertFailure
                        (label <> ": unexpected theorem authority "
                            <> show authorization)
        batches ->
            assertFailure
                (label <> ": expected definition and theorem, found "
                    <> show (length batches))

waitForFileSignal :: String -> FilePath -> Assertion
waitForFileSignal label path = do
    guarded <- Timeout.timeout 10000000 loop
    case guarded of
        Just () ->
            pure ()
        Nothing ->
            assertFailure (label <> " was not observed")
  where
    loop = do
        exists <- doesFileExist path
        if exists
            then pure ()
            else do
                threadDelay 10000
                loop

canonicalAnd
    :: Core.CanonicalTerm global
    -> Core.CanonicalTerm global
    -> Core.CanonicalTerm global
canonicalAnd = Core.CAnd

sole :: String -> [value] -> IO value
sole label = \case
    [value] -> pure value
    values ->
        assertFailure
            (label <> ": expected one value, found " <> show (length values))
            >> fail "unreachable"

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err -> assertFailure (show err) >> fail "unreachable"
    Right value -> pure value

expectRightIO :: Show error => IO (Either error value) -> IO value
expectRightIO action =
    action >>= expectRight

withTestStoreLease
    :: Store.StorePlan
    -> (Store.StoreLease -> IO value)
    -> IO value
withTestStoreLease plan action =
    expectRightIO (Store.withStoreLease plan action)

acquireFinalPreludeSession
    :: Store.Store
    -> Foundation.CheckedFoundation
    -> Declaration.VampireResolver
    -> IO
        (Either
            Module.FinalPreludeReadinessError
            Module.FinalPreludeSession)
acquireFinalPreludeSession store foundation resolver = do
    storeCheck <- Store.newStoreCheck store
    check <- Declaration.newImportCheck foundation
    Module.acquireFinalPreludeSession
        check storeCheck foundation resolver
