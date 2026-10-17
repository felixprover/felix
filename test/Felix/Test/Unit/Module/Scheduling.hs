{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

module Felix.Test.Unit.Module.Scheduling (tests) where

import Base
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.CommandLine qualified as CommandLine
import Felix.Parse qualified as Parse
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Store qualified as Store
import Felix.Verification qualified as Verification
import Felix.Workspace qualified as Workspace
import Felix.Test.Unit.Module.Support

import Control.Concurrent (threadDelay)
import Control.Concurrent.STM
    ( atomically
    , check
    , newEmptyTMVarIO
    , newTQueueIO
    , newTVarIO
    , putTMVar
    , readTQueue
    , readTVar
    , takeTMVar
    , tryReadTMVar
    , tryReadTQueue
    , writeTQueue
    , writeTVar
    )
import Control.Exception (bracket)
import Control.Exception qualified as Exception
import Control.Monad (when)
import Data.Text qualified as StrictText
import Data.IORef
    ( IORef
    , atomicModifyIORef'
    , modifyIORef'
    , newIORef
    , readIORef
    )
import Data.List (sort)
import System.Directory
    ( getPermissions
    , setOwnerExecutable
    , setPermissions
    )
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import System.Timeout qualified as Timeout
import Test.Tasty
import Test.Tasty.HUnit
import UnliftIO.Async (withAsync, wait)
import UnliftIO.Async qualified as Async


tests :: [TestTree]
tests =
    [ testCase "reuses one verification session for successive checks"
        reusesVerificationSession
    , testCase "serializes and cancellation-safely gates session checks"
        serializesVerificationSessionChecks
    , moduleWorkerAcquisitionTests
    , testCase "selects concurrent module failures by source order"
        selectsConcurrentModuleFailureDeterministically
    , testCase "checks structure laws without Vampire"
        structuresRequireNoProver
    , testCase "speculates dependent proof obligations without admitting ahead"
        speculatesDependentProofObligationsWithoutAdmittingAhead
    , testCase "starts diamond consumers after sealed acknowledgements"
        schedulesDiamondAfterSealedImports
    , testCase "classifies typed Vampire failures conservatively"
        classifiesTypedVampireFailures
    , testCase "routes every production root through checking"
        routesProductionVerification
    ]

moduleWorkerAcquisitionTests :: TestTree
moduleWorkerAcquisitionTests = testGroup "module worker acquisition"
    [ testCase "joins worker one when starting worker two fails" $
        withRecordedModuleWorkers \workers -> do
            starts <- newIORef (0 :: Int)
            blocked <- newEmptyTMVarIO
            let start :: forall value. IO value -> IO (Async.Async value)
                start action = do
                    ordinal <- atomicModifyIORef' starts (\n -> (n + 1, n + 1))
                    when (ordinal == 2)
                        (Exception.throwIO (userError "module worker two start failed"))
                    recordModuleWorker workers (atomically (takeTMVar blocked) >> action)
            result <- Exception.try (run start)
            case result of
                Left (failure :: Exception.IOException) ->
                    Exception.displayException failure
                        @?= "user error (module worker two start failed)"
                Right _ -> assertFailure "module startup failure was swallowed"
            assertModuleWorkersJoined 1 workers
    , testCase "joins the acquired workers when setup is cancelled" $
        withRecordedModuleWorkers \workers -> do
            starts <- newIORef (0 :: Int)
            secondEntered <- newEmptyTMVarIO
            blocked <- newEmptyTMVarIO
            let start :: forall value. IO value -> IO (Async.Async value)
                start action = do
                    ordinal <- atomicModifyIORef' starts (\n -> (n + 1, n + 1))
                    when (ordinal == 2) do
                        atomically (putTMVar secondEntered ())
                        atomically (takeTMVar blocked)
                    recordModuleWorker workers (atomically (takeTMVar blocked) >> action)
            withAsync (run start) \checking -> do
                entered <- Timeout.timeout 10000000
                    (atomically (takeTMVar secondEntered))
                entered @?= Just ()
                Async.cancel checking
                Async.waitCatch checking >>= \case
                    Left failure -> assertBool "preserves asynchronous cancellation"
                        (isJust (Exception.fromException failure :: Maybe Async.AsyncCancelled))
                    Right _ -> assertFailure "module startup swallowed cancellation"
                assertModuleWorkersJoined 1 workers
    , testCase "joins all active workers before returning from cancellation" $
        withRecordedModuleWorkers \workers -> do
            entered <- newTVarIO (0 :: Int)
            blocked <- newEmptyTMVarIO
            let start :: forall value. IO value -> IO (Async.Async value)
                start action = recordModuleWorker workers do
                    atomically do
                        count <- readTVar entered
                        writeTVar entered (count + 1)
                    atomically (takeTMVar blocked)
                    action
            withAsync (run start) \checking -> do
                ready <- Timeout.timeout 10000000
                    (atomically (readTVar entered >>= check . (== 2)))
                ready @?= Just ()
                Async.cancel checking
                assertModuleWorkersJoined 2 workers
    ]
  where
    run :: (forall value. IO value -> IO (Async.Async value)) -> IO ()
    run start =
        withAcceptedFixtureVampire "felix-module-acquisition" \prover -> do
            graph <- Workspace.prepareDefaultSourceGraph
                "test/phase7/concurrent-failure-root.tex" >>= expectRight
            jobs <- Provers.selectEffectiveJobs (Provers.effectiveJobs 2)
                (fail "explicit jobs unexpectedly detected processors")
            withFreshVerificationSession \session -> do
                result <- Verification.checkWorkspaceUsingModuleStarter start session
                    Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.FreshStoreValidation
                        , Verification.checkModuleJobs = jobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = ignoredVerificationRequests
                        }
                void (expectRight result)

withRecordedModuleWorkers :: (IORef [Async.Async ()] -> Assertion) -> Assertion
withRecordedModuleWorkers =
    bracket (newIORef []) (\workers -> readIORef workers >>= traverse_ Async.cancel)

recordModuleWorker :: IORef [Async.Async ()] -> IO value -> IO (Async.Async value)
recordModuleWorker workers action = do
    Exception.getMaskingState >>= (@?= Exception.MaskedInterruptible)
    worker <- Async.async action
    modifyIORef' workers (void worker :)
    pure worker

assertModuleWorkersJoined :: Int -> IORef [Async.Async ()] -> Assertion
assertModuleWorkersJoined expected workers = do
    started <- readIORef workers
    length started @?= expected
    for_ started \worker -> do
        settled <- Async.poll worker
        assertBool "module worker still runs after verification returned" (isJust settled)


reusesVerificationSession :: Assertion
reusesVerificationSession =
    withAcceptedFixtureVampire "felix-session-reuse" \prover -> do
        plan <- Store.planStore Store.FreshTemporaryStore >>= expectRight
        graph <- Workspace.prepareDefaultSourceGraph source >>= expectRight
        withTestStoreLease plan \lease -> do
            opened <- Verification.withVerificationSession lease \session -> do
                let request =
                        Verification.CheckRequest
                            { Verification.checkSourceGraph = graph
                            , Verification.checkPresentationDemand =
                                Parse.NoPresentation
                            , Verification.checkStoreValidationMode =
                                Verification.FreshStoreValidation
                            , Verification.checkModuleJobs = testSequentialJobs
                            , Verification.checkProverJobs = testSequentialJobs
                            , Verification.checkVampire = prover
                            , Verification.checkRequestObserver =
                                ignoredVerificationRequests
                            }
                first <-
                    Verification.checkWorkspace session request >>= expectRight
                second <-
                    Verification.checkWorkspace session request >>= expectRight
                Verification.moduleInstallationDecisions
                    (Verification.checkOperationalReport first)
                    @?= Verification.LookupDecisionCounts
                        { Verification.lookupRowsFound = 0
                        , Verification.lookupMisses = 1
                        , Verification.lookupBypasses = 1
                        }
                Verification.moduleInstallationDecisions
                    (Verification.checkOperationalReport second)
                    @?= Verification.LookupDecisionCounts
                        { Verification.lookupRowsFound = 1
                        , Verification.lookupMisses = 0
                        , Verification.lookupBypasses = 1
                        }
                assertBool
                    "fresh report retains live Vampire starts"
                    (Verification.liveVampireRunsStarted
                        (Verification.checkOperationalReport first) > 0)
                traverse_
                    assertUnsupported
                    [ Verification.checkVerificationResult first
                    , Verification.checkVerificationResult second
                    ]
            void (expectRight opened)
  where
    source = "test/phase3/typed-unsupported.tex"

    assertUnsupported = \case
        Verification.VerificationCheckingFailure
                _report
                Verification.VerificationTypedModuleError{} ->
            pure ()
        other ->
            assertFailure
                ("successive session check had unexpected result: "
                    <> show other)

serializesVerificationSessionChecks :: Assertion
serializesVerificationSessionChecks =
    withAcceptedFixtureVampire "felix-session-gate" \prover -> do
        plan <- Store.planStore Store.FreshTemporaryStore >>= expectRight
        graph <- Workspace.prepareDefaultSourceGraph source >>= expectRight
        withTestStoreLease plan \lease -> do
            opened <- Verification.withVerificationSession lease \session -> do
                firstEntered <- newEmptyTMVarIO
                releaseFirst <- newEmptyTMVarIO
                secondEntered <- newEmptyTMVarIO
                firstObservation <- newIORef True
                let blockingObserver =
                        Verification.verificationRequestObserver
                            (\_position _request -> do
                                first <- atomicModifyIORef' firstObservation
                                    (\pending -> (False, pending))
                                when first do
                                    atomically (putTMVar firstEntered ())
                                    atomically (takeTMVar releaseFirst))
                    notifyingObserver =
                        Verification.verificationRequestObserver
                            (\_position _request ->
                                atomically (putTMVar secondEntered ()))
                    request observer = Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand =
                            Parse.NoPresentation
                        , Verification.checkStoreValidationMode =
                            Verification.FreshStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = observer
                        }
                first <- Async.async
                    (Verification.checkWorkspace session
                        (request blockingObserver))
                atomically (takeTMVar firstEntered)
                waiting <- Async.async
                    (Verification.checkWorkspace session
                        (request notifyingObserver))
                observedWhileWaiting <- Timeout.timeout 200000
                    (atomically (takeTMVar secondEntered))
                assertEqual
                    "the waiting check does not enter the verification pipeline"
                    Nothing
                    observedWhileWaiting
                Async.cancel waiting
                atomically (putTMVar releaseFirst ())
                firstResult <- Timeout.timeout 30000000 (Async.wait first)
                case firstResult of
                    Nothing -> assertFailure "the active check did not finish"
                    Just result -> void (expectRight result)
                thirdResult <- Timeout.timeout 30000000
                    (Verification.checkWorkspace session
                        (request ignoredVerificationRequests))
                case thirdResult of
                    Nothing ->
                        assertFailure
                            "cancelling a gate waiter leaked the session gate"
                    Just result -> void (expectRight result)
            void (expectRight opened)
  where
    source = "test/phase5/exact-proofs.tex"

selectsConcurrentModuleFailureDeterministically :: Assertion
selectsConcurrentModuleFailureDeterministically = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-concurrent-module-failure" \root -> do
        let executable = root Posix.</> "vampire"
            source = "test/phase7/concurrent-failure-root.tex"
            prover =
                Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            ignored =
                Verification.verificationRequestObserver
                    (\_position _request -> pure ())
            select amount =
                Provers.selectEffectiveJobs
                    (Provers.effectiveJobs amount)
                    (fail "explicit jobs unexpectedly detected processors")
            reportEntry escape =
                ( Verification.reportedEscapeKind escape
                , locFile (Verification.reportedEscapeLocation escape)
                , locLine (Verification.reportedEscapeLocation escape)
                )
            inspect label expectedPositions
                    (result, _slowReport, positions) = do
                case result of
                    Verification.VerificationFailure report failed -> do
                        assertEqual (label <> " selected earlier failure")
                            "test/phase7/concurrent-earlier.tex"
                            (locFile (Verification.failedVerificationLocation failed))
                        assertEqual (label <> " admitted source prefix")
                            [ ( Verification.ReportedSourceAxiom
                              , "test/phase7/concurrent-earlier.tex"
                              , 1
                              )
                            ]
                            (reportEntry
                                <$> Verification.verificationDirectEscapes report)
                    other ->
                        assertFailure
                            (label <> " did not reject deterministically: "
                                <> show other)
                assertEqual (label <> " executed only sibling obligations")
                    expectedPositions
                    (sort
                        [ ( Provers.workPositionModuleOrdinal position
                          , Provers.workPositionLocalRequestOrdinal position
                          )
                        | position <- positions
                        ])
            runCase label jobsAmount = do
                let storePath = root Posix.</> (label <> ".sqlite")
                    processLock = root Posix.</> (label <> ".process-lock")
                    processStarted =
                        root Posix.</> (label <> ".process-started")
                writeAcceptedFixtureVampire executable
                (_startup, store) <-
                    Store.openStore storePath (Identity.theoryId foundation)
                        >>= expectRight
                bracket (pure store) Store.closeStore \openStore -> do
                    -- Seed only the final prelude.  The unsupported ordinary
                    -- module cannot publish a root.
                    void
                        (
                            (checkFileWithStore
                                openStore
                                Verification.WarmStoreValidation
                                ignored
                                prover
                                "test/phase3/typed-unsupported.tex")
                            >>= expectRight)
                    writeFile executable
                        (unlines
                            [ "#!/bin/sh"
                            , "while ! mkdir \"" <> processLock
                                <> "\" 2>/dev/null; do sleep 0.01; done"
                            , "trap 'rmdir \"" <> processLock
                                <> "\"' EXIT"
                            , ": > \"" <> processStarted <> "\""
                            , "cat >/dev/null"
                            , "printf '%s\\n' '% SZS status CounterSatisfiable for concurrent-fixture'"
                            ])
                    permissions <- getPermissions executable
                    setPermissions executable
                        (setOwnerExecutable True permissions)
                    positionsRef <- newIORef []
                    let observer =
                            Verification.verificationRequestObserver
                                (\position _request -> do
                                    atomicModifyIORef' positionsRef
                                        (\positions ->
                                            (position : positions, ()))
                                    when
                                        (jobsAmount > 1
                                            && Provers.workPositionModuleOrdinal
                                                position == 1)
                                        (waitForFileSignal
                                            "later module process"
                                            processStarted))
                    jobs <- select jobsAmount
                    (result, slowReport) <-
                            (checkFileWithStoreAndJobs
                                openStore
                                Verification.WarmStoreValidation
                                jobs
                                observer
                                prover
                                source)
                            >>= expectRight
                    positions <- readIORef positionsRef
                    pure (result, slowReport, positions)
        void $ runCase "parallel" 2
                >>= inspect "parallel" [(1, 1), (2, 1)]
        void $ runCase "sequential" 1
                >>= inspect "sequential" [(1, 1)]


structuresRequireNoProver :: Assertion
structuresRequireNoProver = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-structure-kernel-laws" \root -> do
        let storePath = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
            unavailable = root Posix.</> "must-not-run-vampire"
            source = "test/phase7/structure-obligation-batch.tex"
            prover =
                Provers.vampire
                    unavailable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            forbiddenObserver =
                Verification.verificationRequestObserver \position _request ->
                    assertFailure
                        ("generated structure law invoked Vampire at "
                            <> show position)
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            writeAcceptedFixtureVampire executable
            let ignored =
                    Verification.verificationRequestObserver
                        (\_position _request -> pure ())
            void
                (checkFileWithStore
                    openStore
                    Verification.WarmStoreValidation
                    ignored
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    "test/phase3/typed-unsupported.tex"
                    >>= expectRight)
            let run =
                    checkFileWithStore
                        openStore
                        Verification.WarmStoreValidation
                        forbiddenObserver
                        prover
                        source
            (fresh, _freshSlowReport) <- run >>= expectRight
            case fresh of
                Verification.VerificationCompleted report _presentation ->
                    assertEqual
                        "only the source axiom is an escape hatch"
                        [Verification.ReportedSourceAxiom]
                        (Verification.reportedEscapeKind
                            <$> Verification.verificationDirectEscapes report)
                other ->
                    assertFailure
                        ("fresh deterministic structure verification failed: "
                            <> show other)
            (warm, _warmSlowReport) <- run >>= expectRight
            case warm of
                Verification.VerificationCompleted{} -> pure ()
                other ->
                    assertFailure
                        ("warm deterministic structure verification failed: "
                            <> show other)
speculatesDependentProofObligationsWithoutAdmittingAhead :: Assertion
speculatesDependentProofObligationsWithoutAdmittingAhead = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-dependent-proof-chain" \root -> do
        let executable = root Posix.</> "vampire"
            unavailable = root Posix.</> "must-not-run-vampire"
            storePath = root Posix.</> "store.sqlite"
            source = "test/phase7/dependent-proof-chain.tex"
            prover path =
                Provers.vampire
                    path
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            ignored =
                Verification.verificationRequestObserver
                    (\_position _request -> pure ())
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            -- Seed only the final prelude so the observed work belongs to the
            -- ordinary proof module.
            void
                (
                    (checkFileWithStore
                        openStore
                        Verification.WarmStoreValidation
                        ignored
                        (prover executable)
                        "test/phase3/typed-unsupported.tex")
                    >>= expectRight)
            jobs <-
                Provers.selectEffectiveJobs
                    (Provers.effectiveJobs 2)
                    (fail "explicit jobs unexpectedly detected processors")
            firstStarted <- newEmptyTMVarIO
            secondStarted <- newEmptyTMVarIO
            releaseFirst <- newEmptyTMVarIO
            positionsRef <- newIORef []
            let observer =
                    Verification.verificationRequestObserver \position _request -> do
                        let ordinal =
                                Provers.workPositionLocalRequestOrdinal position
                        atomicModifyIORef' positionsRef
                            (\positions ->
                                ( ( Provers.workPositionModuleOrdinal position
                                  , ordinal
                                  ) : positions
                                , ()
                                ))
                        case ordinal of
                            1 -> do
                                atomically (putTMVar firstStarted ())
                                atomically (takeTMVar releaseFirst)
                            2 -> atomically (putTMVar secondStarted ())
                            _ ->
                                assertFailure
                                    ("unexpected dependent proof request: "
                                        <> show ordinal)
            withAsync
                (
                    (checkFileWithStoreAndJobs
                        openStore
                        Verification.WarmStoreValidation
                        jobs
                        observer
                        (prover executable)
                        source)
                    >>= expectRight)
                \checking -> do
                    void
                        (awaitSignal "local subclaim request"
                            (atomically (takeTMVar firstStarted)))
                    -- The continuation is semantically dependent, but its
                    -- already checked request may execute prospectively.  It
                    -- cannot be admitted until the local claim succeeds.
                    void
                        (awaitSignal "dependent continuation request"
                            (atomically (takeTMVar secondStarted)))
                    atomically (putTMVar releaseFirst ())
                    (result, _slowReport) <- wait checking
                    case result of
                        Verification.VerificationCompleted report _presentation ->
                            assertEqual "only the preceding axiom is reported"
                                [Verification.ReportedSourceAxiom]
                                (Verification.reportedEscapeKind
                                    <$> Verification.verificationDirectEscapes report)
                        other ->
                            assertFailure
                                ("dependent proof module did not seal: "
                                    <> show other)
            positions <- readIORef positionsRef
            assertEqual "dependent requests retain source positions"
                [(1, 1), (1, 2)]
                (sort positions)

            let forbiddenObserver =
                    Verification.verificationRequestObserver \position _request ->
                        assertFailure
                            ("warm dependent proof invoked Vampire at "
                                <> show position)
            (warm, _warmSlowReport) <-
                    (checkFileWithStoreAndJobs
                        openStore
                        Verification.WarmStoreValidation
                        jobs
                        forbiddenObserver
                        (prover unavailable)
                        source)
                    >>= expectRight
            case warm of
                Verification.VerificationCompleted{} -> pure ()
                other ->
                    assertFailure
                        ("warm dependent proof did not install: " <> show other)
  where
    awaitSignal label action = do
        result <- Timeout.timeout 10000000 action
        maybe
            (assertFailure (label <> " was not observed")
                >> fail "unreachable")
            pure
            result

schedulesDiamondAfterSealedImports :: Assertion
schedulesDiamondAfterSealedImports = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-concurrent-diamond" \root -> do
        let storePath = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
            unavailable = root Posix.</> "must-not-run-vampire"
            source = "test/phase7/diamond-root.tex"
            prover path =
                Provers.vampire
                    path
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
            ignored =
                Verification.verificationRequestObserver
                    (\_position _request -> pure ())
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            -- Acquire the final prelude before introducing scheduler gates.
            void
                (
                    (checkFileWithStore
                        openStore
                        Verification.WarmStoreValidation
                        ignored
                        (prover executable)
                        "test/phase3/typed-unsupported.tex")
                    >>= expectRight)
            jobs <- Provers.selectEffectiveJobs
                (Provers.effectiveJobs 2)
                (fail "explicit jobs unexpectedly detected processors")
            baseStarted <- newEmptyTMVarIO
            branchStarted <- newTQueueIO
            rootStarted <- newEmptyTMVarIO
            releaseBase <- newTVarIO False
            releaseBranches <- newTVarIO False
            let awaitRelease released =
                    atomically (readTVar released >>= check)
                observer =
                    Verification.verificationRequestObserver
                        (\position _request ->
                            case Provers.workPositionModuleOrdinal position of
                                1 -> do
                                    atomically (putTMVar baseStarted ())
                                    awaitRelease releaseBase
                                ordinal@2 -> do
                                    atomically
                                        (writeTQueue branchStarted ordinal)
                                    awaitRelease releaseBranches
                                ordinal@3 -> do
                                    atomically
                                        (writeTQueue branchStarted ordinal)
                                    awaitRelease releaseBranches
                                4 ->
                                    atomically (putTMVar rootStarted ())
                                _ ->
                                    pure ())
                verify vampireCommand requestObserver =
                        (checkFileWithStoreAndJobs
                            openStore
                            Verification.WarmStoreValidation
                            jobs
                            requestObserver
                            vampireCommand
                            source)
                        >>= expectRight
                await label action = do
                    result <- Timeout.timeout 10000000 action
                    maybe
                        (assertFailure (label <> " was not observed")
                            >> fail "unreachable")
                        pure
                        result
            withAsync (verify (prover executable) observer) \verification -> do
                void (await "base request" (atomically (takeTMVar baseStarted)))
                threadDelay 50000
                atomically (tryReadTQueue branchStarted) >>= \case
                    Nothing -> pure ()
                    Just ordinal ->
                        assertFailure
                            ("dependent module started before base seal: "
                                <> show ordinal)
                atomically (writeTVar releaseBase True)
                firstBranch <- await "first branch"
                    (atomically (readTQueue branchStarted))
                secondBranch <- await "second branch"
                    (atomically (readTQueue branchStarted))
                assertEqual "both diamond branches became ready together"
                    [2, 3]
                    (sort [firstBranch, secondBranch])
                atomically (tryReadTMVar rootStarted) >>= \case
                    Nothing -> pure ()
                    Just () ->
                        assertFailure
                            "diamond root started before both branch seals"
                atomically (writeTVar releaseBranches True)
                void (await "diamond root" (atomically (takeTMVar rootStarted)))
                (coldResult, _coldSlowReport) <- wait verification
                case coldResult of
                    Verification.VerificationCompleted{} -> pure ()
                    other ->
                        assertFailure
                            ("cold diamond did not complete: " <> show other)
            let forbiddenObserver =
                    Verification.verificationRequestObserver
                        (\position _request ->
                            assertFailure
                                ("warm diamond invoked Vampire at "
                                    <> show position))
            (warmResult, _warmSlowReport) <-
                verify (prover unavailable) forbiddenObserver
            case warmResult of
                Verification.VerificationCompleted{} -> pure ()
                other ->
                    assertFailure
                        ("warm diamond did not install: " <> show other)

classifiesTypedVampireFailures :: Assertion
classifiesTypedVampireFailures = do
    foundation <- expectRight Foundation.checkedFoundation
    Temp.withSystemTempDirectory "felix-typed-failure-classification" \root -> do
        let storePath = root Posix.</> "store.sqlite"
            executable = root Posix.</> "vampire"
            observer =
                Verification.verificationRequestObserver \_ordinal _request -> pure ()
            prover =
                Provers.vampire
                    executable
                    Provers.defaultTimeLimit
                    Provers.defaultMemoryLimit
        writeAcceptedFixtureVampire executable
        (_startup, store) <-
            Store.openStore storePath (Identity.theoryId foundation)
                >>= expectRight
        bracket (pure store) Store.closeStore \openStore -> do
            let verify source =
                        (checkFileWithStore
                            openStore
                            Verification.WarmStoreValidation
                            observer
                            prover
                            source)
                        >>= expectRight
                writeProtocol lines = do
                    writeFile executable
                        (unlines (["#!/bin/sh", "cat >/dev/null"] <> lines))
                    permissions <- getPermissions executable
                    setPermissions executable
                        (setOwnerExecutable True permissions)
                expectTypedFailure classify = do
                    (result, slowReport) <-
                        verify "test/phase5/exact-runtime-failure.tex"
                    case result of
                        Verification.VerificationFailure report failed -> do
                            assertEqual "typed failure has no direct escapes"
                                []
                                (Verification.verificationDirectEscapes report)
                            assertEqual "typed failure retains source location"
                                "test/phase5/exact-runtime-failure.tex"
                                (locFile
                                    (Verification.failedVerificationLocation failed))
                            classify
                                (Provers.failedVampireResolutionFailure
                                    (Verification.failedVerificationResolution
                                        failed))
                                (CommandLine.verificationCommandOutcome
                                    result Nothing slowReport)
                        other ->
                            assertFailure
                                ("typed prover outcome was misclassified: "
                                    <> show other)

            -- Populate only the confined prelude.  The selected ordinary
            -- module then remains a miss for each classified live failure.
            (_preludeResult, _preludeSlowReport) <-
                verify "test/phase3/typed-unsupported.tex"

            writeProtocol
                [ "printf '%s\\n' '% SZS status CounterSatisfiable for typed-failure'"
                , "exit 0"
                ]
            expectTypedFailure \reason outcome -> do
                case reason of
                    Provers.VampireFailureRejected
                            Provers.RejectedCounterexample _evidence -> pure ()
                    other -> assertFailure ("expected countermodel: " <> show other)
                case outcome of
                    CommandLine.VerificationRejected{} -> pure ()
                    other -> assertFailure ("expected rejection: " <> show other)

            writeProtocol
                [ "printf '%s\\n' '% SZS status Timeout for typed-failure'"
                , "exit 0"
                ]
            expectTypedFailure \reason outcome -> do
                case reason of
                    Provers.VampireFailureRejected
                            (Provers.RejectedIndeterminate
                                (Provers.AtpTimedOut :| []))
                            _evidence -> pure ()
                    other -> assertFailure ("expected indeterminate result: " <> show other)
                case outcome of
                    CommandLine.VerificationRejected{} -> pure ()
                    other -> assertFailure ("expected prover failure: " <> show other)

            writeProtocol
                [ "printf '%s\\n' '% SZS status Theorem for typed-failure'"
                , "exit 7"
                ]
            expectTypedFailure \reason outcome -> do
                case reason of
                    Provers.VampireFailureProtocol{} -> pure ()
                    other -> assertFailure ("expected protocol failure: " <> show other)
                case outcome of
                    CommandLine.VerificationRejected{} -> pure ()
                    other -> assertFailure ("expected prover failure: " <> show other)

            writeFile executable "not executable"
            permissions <- getPermissions executable
            setPermissions executable
                (setOwnerExecutable False permissions)
            expectTypedFailure \reason outcome -> do
                case reason of
                    Provers.VampireFailureProcess{} -> pure ()
                    other -> assertFailure ("expected transport failure: " <> show other)
                case outcome of
                    CommandLine.VerificationRejected{} -> pure ()
                    other -> assertFailure ("expected prover failure: " <> show other)

routesProductionVerification :: Assertion
routesProductionVerification =
    Temp.withSystemTempDirectory "felix-production-route" \directory -> do
        let executable = directory Posix.</> "vampire"
            counter = directory Posix.</> "runs"
        writeFile executable
            (unlines
                [ "#!/bin/sh"
                , "cat >/dev/null"
                , "printf '%s\\n' run >> " <> show counter
                , "printf '%s\\n' '% SZS status Theorem for production-route'"
                ])
        permissions <- getPermissions executable
        setPermissions executable
            (setOwnerExecutable True permissions)
        producer <- verifyFixture executable "test/phase3/typed-producer.tex"
        assertTypedSuccess "exact producer" producer
        selectedRuns <- runCount counter
        assertBool "ordinary roots construct the final prelude"
            (selectedRuns > 0)
        importer <- verifyFixture executable "test/phase3/typed-importer.tex"
        assertTypedSuccess "ordinary importer" importer
        assertBool "every root constructs the final prelude"
            . (> selectedRuns)
            =<< runCount counter
  where
    verifyFixture executable path =
        fst
            <$> (
                (checkFileFresh
                    (Provers.vampire
                        executable
                        Provers.defaultTimeLimit
                        Provers.defaultMemoryLimit)
                    path)
                >>= expectRight)

    runCount path =
        length . StrictText.lines . StrictText.pack <$> readFile path
