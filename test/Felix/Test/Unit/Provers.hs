{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Provers (unitTests, runClosedDescriptorsHelper) where

import Base hiding (Empty)
import Felix.Checking.Backend.Problem
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Provers
import Felix.Report.Render.Terminal qualified as Terminal
import Felix.RequestDump qualified as RequestDump
import Felix.Test.Temp (withTemporaryDirectory)

import Control.Concurrent
    ( newEmptyMVar
    , putMVar
    , readMVar
    , runInBoundThread
    , rtsSupportsBoundThreads
    , takeMVar
    , threadDelay
    , throwTo
    , tryPutMVar
    )
import Control.Exception qualified as Exception
import Control.Monad (replicateM_, when)
import Data.IORef
    ( IORef
    , atomicModifyIORef'
    , newIORef
    , readIORef
    , writeIORef
    )
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Vector qualified as Vector
import Felix.Report.Location (Location, mkLocation, sourceDescriptorForPath, pattern Nowhere)
import System.Directory qualified as Directory
import System.Environment qualified as Environment
import System.Exit (ExitCode(..))
import System.FilePath.Posix ((</>))
import System.Posix.Signals
    ( nullSignal
    , sigTERM
    , signalProcess
    )
import System.Posix.Signals qualified as Signals
import System.Posix.IO qualified as Posix
import System.Posix.Resource qualified as Resource
import System.Process qualified as Process
import System.Posix.Types (ProcessID)
import System.IO (hGetContents, stdin)
import System.Timeout qualified as Timeout
import Test.Tasty
import Test.Tasty.HUnit
import Text.Read (readMaybe)
import Text.Megaparsec (parseMaybe)
import UnliftIO.Async (cancel, mapConcurrently, withAsync)
import UnliftIO.Async qualified as Async

unitTests :: TestTree
unitTests =
    testGroup "Provers"
        [ vampireStatusParserTests
        , vampireClassifierTests
        , jobsSelectionTests
        , vampireExecutorTests
        , supervisorOwnershipTests
        , vampireProcessTests
        ]

supervisorOwnershipTests :: TestTree
supervisorOwnershipTests = testGroup "supervisor ownership"
    [ testCase "isolates concurrent launches at high descriptor limits and owns pipes under pressure" $
        withTemporaryDirectory "closed-prover-descriptors" \temp -> do
            executable <- Environment.getExecutablePath
            environment <- Environment.getEnvironment
            let resultFile = temp </> "result"
                command = (Process.proc executable [])
                    { Process.env = Just (("FELIX_TEST_CLOSED_PROVER_PIPES", resultFile) : environment) }
            (exitCode, _, stderr) <- Process.readCreateProcessWithExitCode command ""
            assertEqual ("descriptor helper failed: " <> stderr) ExitSuccess exitCode
            Text.readFile resultFile >>= (`shouldBe` "accepted")
    , testCase "prover receives SIGINT even when the launching thread blocks it" $
        withTemporaryDirectory "prover-signal-mask" \temp -> do
            let executable = temp </> "signal-probe"
            (code, _, err) <- Process.readProcessWithExitCode "cc"
                ["-std=c99", "-D_POSIX_C_SOURCE=200809L", "-Wall", "-Wextra", "-Werror",
                 "test/prover-supervision/signal-probe.c", "-o", executable] ""
            assertEqual ("native signal probe failed to compile: " <> err) ExitSuccess code
            prepared <- preparedTypedTask 0
            -- Signal masks belong to OS threads. Keep the deliberate block and
            -- the spawn on the same bound thread, and restore its original mask.
            (if rtsSupportsBoundThreads then runInBoundThread else id) $
                Exception.bracket Signals.getSignalMask Signals.setSignalMask $ \original -> do
                    Signals.blockSignals (Signals.addSignal Signals.sigINT Signals.emptySignalSet)
                    runPreparedTypedProver (vampire executable defaultTimeLimit defaultMemoryLimit)
                        prepared >>= assertProved
                    after <- Signals.getSignalMask
                    assertBool "launch changed the parent's signal mask"
                        (Signals.inSignalSet Signals.sigINT after)
                    for_ [Signals.sigTERM, Signals.sigQUIT, Signals.sigCHLD] $ \signal ->
                        Signals.inSignalSet signal after `shouldBe` Signals.inSignalSet signal original
    , testCase "settles every acquired pipe-task prefix" $
        for_ [1..3] \failingStart -> do
            prepared <- preparedTypedTask 20000
            withRecordedWorkerHandles \tasks ->
                withProcessGroupFake defaultTimeLimit [] \pidFile command -> do
                    starts <- newIORef (0 :: Int)
                    let start action = do
                            ordinal <- atomicModifyIORef' starts \n -> (n + 1, n + 1)
                            if ordinal == failingStart
                                then ioError (userError "pipe acquisition failed")
                                else recordWorker tasks action
                        runtime = defaultVampireExecutorRuntime { vampireRuntimeStartPipe = start }
                    withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                        (\_ _ -> void (waitForProcessIds pidFile)) \executor ->
                        withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                                (preparedTypedProverRequest prepared)
                            completion <- awaitVampireRequest handle
                            case vampireCompletionTerminal completion of
                                VampireProcessFailed (ProverLifecycleFailed _ message) ->
                                    assertBool "original acquisition error retained"
                                        ("pipe acquisition failed" `Text.isInfixOf` message)
                                other -> assertFailure ("unexpected acquisition result: " <> show other)
                            readProcessIds pidFile >>= assertProcessesGone
                            assertWorkersJoined (failingStart - 1) tasks
    , testGroup "preserves repeated cleanup cancellation after handled request failures"
        [ testCase label do
            prepared <- preparedTypedTask (if failDuringAcquisition then 0 else 20000)
            closing <- newEmptyMVar
            releaseClose <- newEmptyMVar
            closes <- newIORef (0 :: Int)
            withRecordedWorkerHandles \workers -> do
                let runtime = defaultVampireExecutorRuntime
                        { vampireRuntimeStartWorker = recordWorker workers
                        , vampireRuntimeStartPipe = \action ->
                            if failDuringAcquisition
                                then ioError (userError "injected pipe start failure")
                                else vampireRuntimeStartPipe defaultVampireExecutorRuntime action
                        , vampireRuntimeClosePipe = \pipe -> do
                            void (tryPutMVar closing ())
                            readMVar releaseClose
                            vampireRuntimeClosePipe defaultVampireExecutorRuntime pipe
                            atomicModifyIORef' closes \n -> (n + 1, ())
                        }
                    -- Exercise both handled-primary branches: IOException
                    -- during acquisition and SupervisorAbort from broken stdin.
                    body = if failDuringAcquisition then [] else
                        [ "exec 0<&-"
                        -- The fixture's descendant inherited stdin too.
                        , "kill -KILL \"$!\""
                        , "wait \"$!\" 2>/dev/null || :"
                        ]
                withProcessGroupFake defaultTimeLimit body \pidFile command ->
                    withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                        (\_ _ -> void (waitForProcessIds pidFile)) \executor ->
                        withVampireRequestOwner executor \owner ->
                            (do
                                handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                                    (preparedTypedProverRequest prepared)
                                Timeout.timeout 5000000 (takeMVar closing) >>= (`shouldBe` Just ())
                                owned <- readIORef workers
                                worker <- case owned of
                                    [one] -> pure one
                                    _ -> assertFailure "expected exactly one supervisor"
                                -- Synchronous delivery ensures both interrupts
                                -- arrive while the cleanup owner is gated.
                                throwTo (Async.asyncThreadId worker) Async.AsyncCancelled
                                throwTo (Async.asyncThreadId worker) Async.AsyncCancelled
                                Async.poll worker >>= \case
                                    Nothing -> pure ()
                                    Just _ -> assertFailure "supervisor abandoned owned cleanup"
                                readIORef closes >>= (`shouldBe` 0)
                                queued <- submitVampireRequest owner (workPosition 1 2) testLocation
                                    (preparedTypedProverRequest prepared)
                                vampireExecutorLiveRunsStarted executor >>= (`shouldBe` 1)
                                cancelVampireRequest queued
                                putMVar releaseClose ()
                                -- Before the repair the handled primary was
                                -- published and both interruptions disappeared.
                                assertExecutorMessage "AsyncCancelled" (awaitVampireRequest handle)
                                Async.wait worker
                                cancelVampireRequest handle
                                readIORef closes >>= (`shouldBe` 6)
                                readProcessIds pidFile >>= assertProcessesGone)
                            `Exception.finally` void (tryPutMVar releaseClose ())
        | (label, failDuringAcquisition) <- [("IOException", True), ("SupervisorAbort", False)]
        ]
    , testCase "accepts completed requests after slow successful pipe closure" do
        prepared <- preparedTypedTask 0
        closes <- newIORef (0 :: Int)
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeClosePipe = \pipe -> do
                    ordinal <- readIORef closes
                    -- Longer than the former two-second cleanup cutoff.
                    -- Delay is not an OS failure: each close still succeeds.
                    when (ordinal == 0) (threadDelay 2200000)
                    vampireRuntimeClosePipe defaultVampireExecutorRuntime pipe
                    writeIORef closes (ordinal + 1)
                }
        withFakeVampire
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for fake'"
            ] \command ->
                withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                    (\_ _ -> pure ()) \executor ->
                    withVampireRequestOwner executor \owner ->
                        for_ [1, 2] \ordinal -> do
                            handle <- submitVampireRequest owner (workPosition 1 ordinal) testLocation
                                (preparedTypedProverRequest prepared)
                            completion <- awaitVampireRequest handle
                            vampireCompletionTerminal completion `shouldBe` VampireAccepted
                            -- The next request can reuse the worker only after
                            -- all six pipe handles have completed closure.
                            readIORef closes >>= (`shouldBe` (6 * fromIntegral ordinal))
    , testCase "completed-request pipe-close faults identify the source" do
        prepared <- preparedTypedTask 0
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeClosePipe = \pipe -> do
                    vampireRuntimeClosePipe defaultVampireExecutorRuntime pipe
                    ioError (userError "injected close failure")
                }
            location = mkLocation (sourceDescriptorForPath "cleanup.tex") 12 3
        withFakeVampire
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for fake'"
            ] \command ->
                withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                    (\_ _ -> pure ()) \executor ->
                    withVampireRequestOwner executor \owner -> do
                        handle <- submitVampireRequest owner (workPosition 1 1) location
                            (preparedTypedProverRequest prepared)
                        assertExecutorMessage
                            "cleanup.tex 12:3: request completed; cleanup: closing pipe:"
                            (awaitVampireRequest handle)
                        assertExecutorMessage "injected close failure" (awaitVampireRequest handle)
    , testCase "delayed reaping retains cancellation and the worker slot until settlement" do
        prepared <- preparedTypedTask 0
        waiting <- newEmptyMVar
        releaseReaping <- newEmptyMVar
        terminated <- newEmptyMVar
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeWaitForProcess = \process -> do
                    void (tryPutMVar waiting ())
                    readMVar releaseReaping
                    vampireRuntimeWaitForProcess defaultVampireExecutorRuntime process
                , vampireRuntimeTerminateGroup = \group -> do
                    vampireRuntimeTerminateGroup defaultVampireExecutorRuntime group
                    void (tryPutMVar terminated ())
                }
        withProcessGroupFake defaultTimeLimit [] \pidFile command ->
            withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                (\_ _ -> void (waitForProcessIds pidFile)) \executor ->
                withVampireRequestOwner executor \owner -> do
                    handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                        (preparedTypedProverRequest prepared)
                    takeMVar waiting
                    queued <- submitVampireRequest owner (workPosition 1 2) testLocation
                        (preparedTypedProverRequest prepared)
                    (withAsync (cancelVampireRequest handle) \cancelling -> do
                        takeMVar terminated
                        Async.poll cancelling >>= \case
                            Nothing -> pure ()
                            Just _ -> assertFailure "cancellation returned before reaping"
                        vampireExecutorLiveRunsStarted executor >>= (`shouldBe` 1)
                        cancelVampireRequest queued
                        putMVar releaseReaping ()
                        Async.wait cancelling
                        cancelVampireRequest handle
                        completion <- awaitVampireRequest handle
                        vampireCompletionTerminal completion `shouldBe` VampireCancelled
                        readProcessIds pidFile >>= assertProcessesGone)
                        `Exception.finally` void (tryPutMVar releaseReaping ())
    , testCase "shutdown retains ownership and completes after delayed reaping" do
        prepared <- preparedTypedTask 0
        waiting <- newEmptyMVar
        releaseReaping <- newEmptyMVar
        publishedExecutor <- newEmptyMVar
        closeScope <- newEmptyMVar
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeWaitForProcess = \process -> do
                    void (tryPutMVar waiting ())
                    readMVar releaseReaping
                    vampireRuntimeWaitForProcess defaultVampireExecutorRuntime process
                }
        withProcessGroupFake defaultTimeLimit [] \pidFile command ->
            withAsync
                (withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                    (\_ _ -> void (waitForProcessIds pidFile)) \executor -> do
                        putMVar publishedExecutor executor
                        takeMVar closeScope)
                \scope -> do
                    executor <- takeMVar publishedExecutor
                    withVampireRequestOwner executor \owner ->
                        (do
                            handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                                (preparedTypedProverRequest prepared)
                            takeMVar waiting
                            putMVar closeScope ()
                            assertExecutorMessage "VampireExecutorClosed" (awaitVampireRequest handle)
                            Async.poll scope >>= \case
                                Nothing -> pure ()
                                Just _ -> assertFailure "executor shutdown abandoned an unsettled child"
                            putMVar releaseReaping ()
                            Async.wait scope
                            cancelVampireRequest handle
                            readProcessIds pidFile >>= assertProcessesGone)
                        `Exception.finally` void (tryPutMVar releaseReaping ())
    , testCase "termination failure retains cancellation and is retried before settlement" do
        prepared <- preparedTypedTask 0
        attempts <- newIORef (0 :: Int)
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeTerminateGroup = \group -> do
                    ordinal <- atomicModifyIORef' attempts \n -> (n + 1, n + 1)
                    if ordinal == 1 then ioError (userError "injected signal failure")
                    else vampireRuntimeTerminateGroup defaultVampireExecutorRuntime group
                }
        withProcessGroupFake defaultTimeLimit [] \pidFile command ->
            withVampireExecutorUsingRuntime runtime (positiveJobs 1) command (\_ _ -> pure ()) \executor ->
                withVampireRequestOwner executor \owner -> do
                    handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                        (preparedTypedProverRequest prepared)
                    processIds <- waitForProcessIds pidFile
                    cancelVampireRequest handle
                    assertExecutorMessage "request cancelled; cleanup: termination:" (awaitVampireRequest handle)
                    assertExecutorMessage "injected signal failure" (awaitVampireRequest handle)
                    readIORef attempts >>= (`shouldBe` 2)
                    assertProcessesGone processIds
    , testCase "reaping failure faults the executor and retains the child until a successful wait" do
        prepared <- preparedTypedTask 0
        attempts <- newIORef (0 :: Int)
        let runtime = defaultVampireExecutorRuntime
                { vampireRuntimeWaitForProcess = \process -> do
                    ordinal <- atomicModifyIORef' attempts \n -> (n + 1, n + 1)
                    if ordinal == 1 then ioError (userError "injected wait failure")
                    else vampireRuntimeWaitForProcess defaultVampireExecutorRuntime process
                }
        withProcessGroupFake defaultTimeLimit [] \pidFile command ->
            withVampireExecutorUsingRuntime runtime (positiveJobs 1) command
                (\_ _ -> void (waitForProcessIds pidFile)) \executor ->
                withVampireRequestOwner executor \owner -> do
                    handle <- submitVampireRequest owner (workPosition 1 1) testLocation
                        (preparedTypedProverRequest prepared)
                    assertExecutorMessage "injected wait failure" (awaitVampireRequest handle)
                    cancelVampireRequest handle
                    readIORef attempts >>= (`shouldBe` 2)
                    readProcessIds pidFile >>= assertProcessesGone
    ]

assertExecutorMessage :: Text -> IO value -> Assertion
assertExecutorMessage expected action = do
    result <- Timeout.timeout 5000000 (Exception.try action)
    case result of
        Just (Left (problem :: Exception.SomeException)) ->
            assertBool ("expected executor fault containing " <> Text.unpack expected <> ", got " <> show problem)
                (expected `Text.isInfixOf` Text.pack (Exception.displayException problem))
        Just (Right _) -> assertFailure "expected an executor fault"
        Nothing -> assertFailure "executor fault did not wake the caller"

-- Run only in a separate native test process: closing these descriptors in
-- the test runner would invalidate Tasty's own handles.
runClosedDescriptorsHelper :: FilePath -> IO ()
runClosedDescriptorsHelper resultFile = do
    arguments <- Environment.getArgs
    if null arguments then runDescriptorParent resultFile else do
        -- This native helper is also the prover executable. A shell could close
        -- inherited descriptors itself and conceal a launcher regression.
        descriptor <- Environment.getEnv "FELIX_TEST_PROVER_SENTINEL" >>= \value ->
            maybe (ioError (userError "invalid descriptor sentinel")) pure (readMaybe value)
        inherited <- tryIOError (Posix.queryFdOption descriptor Posix.CloseOnExec)
        case inherited of
            Right _ -> ioError (userError "unrelated descriptor inherited by prover")
            Left _ -> pure ()
        contents <- hGetContents stdin
        Exception.evaluate (length contents) >>= \_ ->
            putStrLn "% SZS status Theorem for descriptor helper"

runDescriptorParent :: FilePath -> IO ()
runDescriptorParent resultFile = do
    outcome <- Exception.try do
        -- Limits are process-wide: only change them in this isolated helper.
        limits <- Resource.getResourceLimit Resource.ResourceOpenFiles
        let highLimit = case Resource.hardLimit limits of
                Resource.ResourceLimit value -> Resource.ResourceLimit (min value 1048575)
                _ -> Resource.ResourceLimit 1048575
        Resource.setResourceLimit Resource.ResourceOpenFiles
            limits { Resource.softLimit = highLimit }
        executable <- Environment.getExecutablePath
        let descriptor = case highLimit of
                Resource.ResourceLimit value -> fromIntegral (min 4096 (value - 1))
                _ -> 4096
        Environment.setEnv "FELIX_TEST_PROVER_SENTINEL" (show descriptor)
        Exception.bracket (Posix.dupTo 1 descriptor) Posix.closeFd \sentinel -> do
            Posix.setFdOption sentinel Posix.CloseOnExec False
            small <- preparedTypedTask 1
            -- Native launches can overlap; each must close unrelated descriptors
            -- without closing the parent's sentinel or another request's pipes.
            void $ mapConcurrently (\_ ->
                runPreparedTypedProver (vampire executable defaultTimeLimit defaultMemoryLimit) small
                    >>= assertProved) [1..20 :: Int]
            Posix.queryFdOption sentinel Posix.CloseOnExec >>= (`shouldBe` False)
            current <- Resource.getResourceLimit Resource.ResourceOpenFiles
            Resource.softLimit current `shouldBe` highLimit
        prepared <- preparedTypedTask 20000
        withFakeVampire
            [ "head -c 1048576 /dev/zero"
            , "printf '\\n'"
            , "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for fake'"
            ] \command -> do
                assertPrelaunchPipeOwnership command prepared
                traverse_ Posix.closeFd [0, 1, 2]
                runPreparedTypedProver command prepared >>= assertProved
    Text.writeFile resultFile $ case outcome of
        Left (problem :: Exception.SomeException) -> Text.pack (Exception.displayException problem)
        Right () -> "accepted"

assertPrelaunchPipeOwnership
    :: Vampire -> PreparedTypedProverTask ref local origin global -> Assertion
assertPrelaunchPipeOwnership command prepared =
    Exception.bracket
        (do
            previous <- Resource.getResourceLimit Resource.ResourceOpenFiles
            Resource.setResourceLimit Resource.ResourceOpenFiles
                previous { Resource.softLimit = Resource.ResourceLimit 64 }
            pure previous)
        (Resource.setResourceLimit Resource.ResourceOpenFiles)
        \_ -> do
            held <- fillDescriptors []
            let (available, retained) = splitAt 3 held
            length available `shouldBe` 3
            traverse_ Posix.closeFd available
            (do
                -- Three spare descriptors permit the first pipe, then force
                -- acquisition of the second pipe to fail before launch.
                result <- runPreparedTypedProver command prepared
                case resolutionFailure result of
                    Just (VampireFailureProcess ProverLaunchFailed{}) -> pure ()
                    _ -> assertFailure ("expected prelaunch acquisition failure: " <> show result)
                Exception.bracket (fillDescriptors []) (traverse_ Posix.closeFd) \recovered ->
                    length recovered `shouldBe` 3)
                `Exception.finally` traverse_ Posix.closeFd retained
  where
    fillDescriptors accumulated = do
        next <- Exception.try (Posix.dup 0)
        case next of
            Left (_ :: Exception.IOException) -> pure accumulated
            Right descriptor -> fillDescriptors (descriptor : accumulated)

jobsSelectionTests :: TestTree
jobsSelectionTests =
    testGroup "effective jobs"
        [ testCase "uses a positive override exactly" do
            detectorCalled <- newIORef False
            selected <- selectEffectiveJobs
                (effectiveJobs 3)
                (writeIORef detectorCalled True >> pure 99)
            selected `shouldBe` positiveJobs 3
            readIORef detectorCalled >>= (`shouldBe` False)
        , testCase "scales module and prover defaults from logical processors" do
            for_
                [(1, 1, 1), (4, 2, 1), (8, 5, 1), (12, 8, 2),
                 (16, 10, 3), (18, 12, 4), (24, 16, 4), (32, 16, 4)]
                \(detected, modules, provers) -> do
                    automatic <- selectAutomaticJobs (pure detected)
                    automatic `shouldBe` (positiveJobs modules, positiveJobs provers)
                    selected <- selectEffectiveJobs Nothing (pure detected)
                    selected `shouldBe` positiveJobs provers
        , testCase "caps automatic jobs without overflowing" do
            selected <- selectAutomaticJobs (pure maxBound)
            selected `shouldBe` (positiveJobs 16, positiveJobs 4)
        , testCase "falls back to one after bad detection" do
            nonPositive <- selectEffectiveJobs Nothing (pure 0)
            nonPositive `shouldBe` positiveJobs 1
            failed <- selectEffectiveJobs Nothing
                (Exception.throwIO (userError "processor detection failed"))
            failed `shouldBe` positiveJobs 1
            for_ [0, -1, minBound] \detected -> do
                automatic <- selectAutomaticJobs (pure detected)
                automatic `shouldBe` (positiveJobs 1, positiveJobs 1)
        , testCase "preserves async processor-detection cancellation" do
            detectionStarted <- newEmptyMVar
            withAsync
                (selectEffectiveJobs Nothing do
                    putMVar detectionStarted ()
                    threadDelay maxBound
                    pure 1)
                \worker -> do
                    takeMVar detectionStarted
                    cancel worker
                    Async.waitCatch worker >>= \case
                        Left failure ->
                            case Exception.fromException failure
                                    :: Maybe Async.AsyncCancelled of
                                Just _cancelled -> pure ()
                                Nothing ->
                                    assertFailure
                                        ("expected AsyncCancelled, got "
                                            <> show failure)
                        Right selected ->
                            assertFailure
                                ("processor detection swallowed cancellation: "
                                    <> show selected)
        ]

workerAcquisitionTests :: TestTree
workerAcquisitionTests = testGroup "worker acquisition"
    [ testCase "joins worker one when starting worker two fails" $
        withRecordedWorkerHandles \handles -> do
            starts <- newIORef (0 :: Int)
            entered <- newIORef False
            let start action = do
                    ordinal <- atomicModifyIORef' starts \n -> (n + 1, n + 1)
                    if ordinal == 2
                        then Exception.throwIO (userError "worker two start failed")
                        else recordWorker handles action
            result <- Exception.try
                (run start \_ -> writeIORef entered True)
            assertOriginalFailure "worker two start failed" result
            readIORef entered >>= (`shouldBe` False)
            assertWorkersJoined 1 handles
    , testCase "joins the acquired prefix when setup is cancelled" $
        withRecordedWorkerHandles \handles -> do
            starts <- newIORef (0 :: Int)
            secondEntered <- newEmptyMVar
            releaseSecond <- newEmptyMVar
            let start action = do
                    ordinal <- atomicModifyIORef' starts \n -> (n + 1, n + 1)
                    when (ordinal == 2) do
                        putMVar secondEntered ()
                        takeMVar releaseSecond
                    recordWorker handles action
            withAsync (run start (\_ -> assertFailure "setup unexpectedly completed")) \acquiring -> do
                takeMVar secondEntered
                cancel acquiring
                Async.waitCatch acquiring >>= \case
                    Left failure -> assertBool "setup preserves asynchronous cancellation"
                        (isJust (Exception.fromException failure :: Maybe Async.AsyncCancelled))
                    Right () -> assertFailure "setup swallowed cancellation"
                assertWorkersJoined 1 handles
    , testCase "joins all acquired workers after an action failure" $
        withRecordedWorkerHandles \handles -> do
            result <- Exception.try
                (run (recordWorker handles) \_ ->
                    Exception.throwIO (userError "executor action failed"))
            assertOriginalFailure "executor action failed" result
            assertWorkersJoined 2 handles
    ]
  where
    run start = withVampireExecutorUsingRuntime
        defaultVampireExecutorRuntime { vampireRuntimeStartWorker = start }
        (positiveJobs 2)
        (vampire "unused-during-acquisition" defaultTimeLimit defaultMemoryLimit)
        (\_ _ -> pure ())

    assertOriginalFailure :: String -> Either Exception.IOException () -> Assertion
    assertOriginalFailure expected = \case
        Left failure -> Exception.displayException failure
            `shouldBe` ("user error (" <> expected <> ")")
        Right () -> assertFailure "injected executor failure was swallowed"

withRecordedWorkerHandles :: (IORef [Async.Async ()] -> Assertion) -> Assertion
withRecordedWorkerHandles =
    Exception.bracket (newIORef []) (\handles -> readIORef handles >>= traverse_ cancel)

recordWorker :: IORef [Async.Async ()] -> IO () -> IO (Async.Async ())
recordWorker handles action = do
    worker <- Async.async action
    atomicModifyIORef' handles \owned -> (worker : owned, ())
    pure worker

assertWorkersJoined :: Int -> IORef [Async.Async ()] -> Assertion
assertWorkersJoined expected handles = do
    workers <- readIORef handles
    length workers `shouldBe` expected
    for_ workers \worker -> do
        settled <- Async.poll worker
        assertBool "every started worker was joined before scope return" (isJust settled)

vampireExecutorTests :: TestTree
vampireExecutorTests =
    testGroup "bounded Vampire executor"
        [ workerAcquisitionTests
        , testCase "records completed qualifying tasks with runtime context" do
            prepared <- preparedTypedTask 0
            clock <- scriptedClock [10, 5000000010]
            let position = workPosition 2 3
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' '% SZS status Theorem for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutorUsingClock
                        clock
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest
                                owner
                                position
                                testLocation
                                (preparedTypedProverRequest prepared)
                            awaitVampireRequest handle
                                >>= assertAcceptedRequest prepared
                            report <- vampireExecutorSlowAtpReport executor
                            slowAtpQualifyingTaskCount report `shouldBe` 1
                            case slowAtpTasks report of
                                [task] -> do
                                    atpDurationNanoseconds
                                        (slowAtpDuration task)
                                        `shouldBe` 5000000000
                                    slowAtpOutcome task `shouldBe` SlowAtpAccepted
                                    slowAtpPosition task `shouldBe` position
                                    slowAtpLocation task `shouldBe` testLocation
                                    slowAtpRequestId task `shouldBe`
                                        preparedVerificationRequestId
                                            (preparedTypedProverRequest prepared)
                                tasks ->
                                    assertFailure
                                        ("unexpected slow-task report: "
                                            <> show tasks)
                            execution <-
                                vampireExecutorExecutionReport executor
                            vampireExecutionWorkerCount execution `shouldBe` 1
                            vampireExecutionCompletedRuns execution `shouldBe` 1
                            vampireExecutionAggregateNanoseconds execution
                                `shouldBe` 5000000000
                            vampireExecutionLongestNanoseconds execution
                                `shouldBe` 5000000000
                            vampireExecutionActiveSpanNanoseconds execution
                                `shouldBe` 5000000000
                            vampireExecutionMaximumQueueDepth execution
                                `shouldBe` 1
        , testCase "does not report a cancelled partial task" do
            prepared <- preparedTypedTask 0
            clock <- scriptedClock [0, 6000000000]
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand ->
                    withVampireExecutorUsingClock
                        clock
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            processIds <- waitForProcessIds pidFile
                            cancelVampireRequest handle
                            report <- vampireExecutorSlowAtpReport executor
                            slowAtpQualifyingTaskCount report `shouldBe` 0
                            assertBool "cancelled report is empty"
                                (null (slowAtpTasks report))
                            assertProcessesGone processIds
        , testCase "opaque handles complete out of submission order" do
            prepared <- preparedTypedTask 0
            firstStarted <- newEmptyMVar
            releaseFirst <- newEmptyMVar
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' '% SZS status Theorem for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 2)
                        vampireCommand
                        (\position _request ->
                            when
                                (workPositionLocalRequestOrdinal position == 1)
                                (putMVar firstStarted () >> takeMVar releaseFirst))
                        \executor -> withVampireRequestOwner executor \owner -> do
                            first <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            takeMVar firstStarted
                            second <- submitVampireRequest
                                owner
                                (workPosition 1 2)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            secondCompletion <- awaitVampireRequest second
                            assertAcceptedRequest prepared secondCompletion
                            putMVar releaseFirst ()
                            firstCompletion <- awaitVampireRequest first
                            assertAcceptedRequest prepared firstCompletion
        , testCase "validates request identity before a rejection" do
            submitted <- preparedTypedTask 0
            mismatched <- preparedTypedTask 1
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' '% SZS status CounterSatisfiable for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest submitted)
                            outcome <- Exception.try
                                (awaitPreparedVampireRequest
                                    (preparedTypedProverRequest mismatched)
                                    handle)
                            case outcome of
                                Left (failure :: VampireExecutorFault) ->
                                    assertBool
                                        "request mismatch is an integrity fault"
                                        ("wrong request id"
                                            `Text.isInfixOf`
                                                Text.pack (show failure))
                                Right answer ->
                                    assertFailure
                                        ("mismatched rejection was accepted: "
                                            <> show answer)
        , testCase "runs requests through the bounded worker pool" do
            prepared <- preparedTypedTask 0
            withFakeVampire
                [ "previous=''"
                , "found=0"
                , "for argument in \"$@\"; do"
                , "  if [ \"$previous\" = '--cores' ]; then"
                , "    [ \"$argument\" = '2' ] || exit 17"
                , "    found=1"
                , "  fi"
                , "  previous=$argument"
                , "done"
                , "[ \"$found\" = '1' ] || exit 18"
                , "cat >/dev/null"
                , "sleep 0.2"
                , "printf '%s\n' '% SZS status Theorem for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 2)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            answers <- mapConcurrently
                                (\ordinal ->
                                    runPreparedTypedProverWithExecutor
                                        owner
                                        (workPosition 1 ordinal)
                                        testLocation
                                        prepared)
                                [1..4]
                            traverse_ assertProved answers
                            vampireExecutorLiveRunsStarted executor
                                >>= (`shouldBe` 4)
        , testCase "propagates observer failure to the submitter" do
            prepared <- preparedTypedTask 0
            let position = workPosition 1 1
                expected = RequestDump.DumpRequestWriteFailed
                    position
                    "/unwritable/request.p"
                    "observer failed"
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' '% SZS status Theorem for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request ->
                            Exception.throwIO expected)
                        \executor -> withVampireRequestOwner executor \owner -> do
                            result <- Exception.try
                                (runPreparedTypedProverWithExecutor
                                    owner
                                    position
                                    testLocation
                                    prepared)
                            case result of
                                Left failure ->
                                    failure @?= expected
                                Right answer ->
                                    assertFailure
                                        ("observer failure was lost: "
                                            <> show answer)
        , testCase "cancels queued and running jobs independently" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner ->
                            withAsync
                                (runPreparedTypedProverWithExecutor
                                    owner
                                    (workPosition 1 1)
                                    testLocation
                                    prepared)
                                \running -> do
                                    processIds <- waitForProcessIds pidFile
                                    queuedSubmitted <- newEmptyMVar
                                    withAsync
                                        (do
                                            handle <- submitVampireRequest
                                                owner
                                                (workPosition 2 1)
                                                testLocation
                                                (preparedTypedProverRequest prepared)
                                            putMVar queuedSubmitted ()
                                            awaitPreparedVampireRequest
                                                (preparedTypedProverRequest prepared)
                                                handle)
                                        \queued -> do
                                            takeMVar queuedSubmitted
                                            cancel queued
                                            cancel running
                                    assertProcessesGone processIds
        , testCase "explicit cancellation completes queued and running handles" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            running <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            processIds <- waitForProcessIds pidFile
                            queued <- submitVampireRequest
                                owner
                                (workPosition 1 2)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            cancelVampireRequest queued
                            awaitVampireRequest queued
                                >>= assertCancelled prepared
                            cancelVampireRequest running
                            awaitVampireRequest running
                                >>= assertCancelled prepared
                            assertProcessesGone processIds
                            vampireExecutorLiveRunsStarted executor
                                >>= (`shouldBe` 1)
        , testCase "structured shutdown wakes waiter and full-queue submitter" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand -> do
                    (waiter, blockedSubmit, processIds) <-
                        withVampireExecutor
                            (positiveJobs 1)
                            vampireCommand
                            (\_position _request -> pure ())
                            \executor ->
                                withVampireRequestOwner executor \owner -> do
                                    running <- submitVampireRequest
                                        owner
                                        (workPosition 1 1)
                                        testLocation
                                        (preparedTypedProverRequest prepared)
                                    processIds <- waitForProcessIds pidFile
                                    _queuedOne <- submitVampireRequest
                                        owner
                                        (workPosition 1 2)
                                        testLocation
                                        (preparedTypedProverRequest prepared)
                                    _queuedTwo <- submitVampireRequest
                                        owner
                                        (workPosition 1 3)
                                        testLocation
                                        (preparedTypedProverRequest prepared)
                                    waiter <- Async.async
                                        (awaitVampireRequest running)
                                    submitStarted <- newEmptyMVar
                                    blockedSubmit <- Async.async do
                                        putMVar submitStarted ()
                                        submitVampireRequest
                                            owner
                                            (workPosition 1 4)
                                            testLocation
                                            (preparedTypedProverRequest prepared)
                                    takeMVar submitStarted
                                    pure (waiter, blockedSubmit, processIds)
                    Async.waitCatch waiter >>= \case
                        Right completion ->
                            assertCancelled prepared completion
                        Left failure ->
                            assertFailure
                                ("shutdown waiter failed: " <> show failure)
                    Async.waitCatch blockedSubmit >>= \case
                        Left failure ->
                            assertBool
                                "backpressured submit observes owner shutdown"
                                ("VampireRequestOwnerClosed"
                                    `Text.isInfixOf`
                                        Text.pack (show failure))
                        Right _handle ->
                            assertFailure
                                "backpressured submit survived structured shutdown"
                    assertProcessesGone processIds
        , testCase "an owner can settle its handles after the executor has closed" do
            prepared <- preparedTypedTask 0
            publishedExecutor <- newEmptyMVar
            closeExecutor <- newEmptyMVar
            withProcessGroupFake defaultTimeLimit [] \pidFile command ->
                withAsync
                    (withVampireExecutor (positiveJobs 1) command (\_ _ -> pure ()) \executor -> do
                        putMVar publishedExecutor executor
                        takeMVar closeExecutor)
                    \executorScope -> do
                        executor <- takeMVar publishedExecutor
                        -- The timeout surrounds the owner's release itself.
                        -- All processes are already gone before that release;
                        -- an empty terminal cell must not keep it waiting.
                        closed <- Timeout.timeout 5000000 $
                            withVampireRequestOwner executor \owner -> do
                                running <- submitVampireRequest owner (workPosition 1 1)
                                    testLocation (preparedTypedProverRequest prepared)
                                processIds <- waitForProcessIds pidFile
                                queued <- submitVampireRequest owner (workPosition 1 2)
                                    testLocation (preparedTypedProverRequest prepared)
                                putMVar closeExecutor ()
                                Async.wait executorScope
                                assertProcessesGone processIds
                                pure (running, queued)
                        case closed of
                            Nothing -> assertFailure "owner release waited on an unpublished terminal after settlement"
                            Just (running, queued) -> do
                                cancelVampireRequest running
                                cancelVampireRequest queued
                                awaitVampireRequest queued >>= assertCancelled prepared
                                vampireExecutorLiveRunsStarted executor >>= (`shouldBe` 1)
        , testCase "worker fault wakes a waiter and a full-queue submitter" do
            prepared <- preparedTypedTask 0
            observerEntered <- newEmptyMVar
            failObserver <- newEmptyMVar
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' '% SZS status Theorem for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\position _request ->
                            when
                                (workPositionLocalRequestOrdinal position == 1)
                                (putMVar observerEntered ()
                                    >> takeMVar failObserver
                                    >> Exception.throwIO
                                        (userError "fatal observer fault")))
                        \executor -> withVampireRequestOwner executor \owner -> do
                            first <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            takeMVar observerEntered
                            _second <- submitVampireRequest
                                owner
                                (workPosition 1 2)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            _third <- submitVampireRequest
                                owner
                                (workPosition 1 3)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            withAsync
                                (submitVampireRequest
                                    owner
                                    (workPosition 1 4)
                                    testLocation
                                    (preparedTypedProverRequest prepared))
                                \blockedSubmit -> do
                                    putMVar failObserver ()
                                    awaitObserverFault
                                        (awaitVampireRequest first)
                                    Async.waitCatch blockedSubmit >>= \case
                                        Left failure ->
                                            assertObserverFault failure
                                        Right _handle ->
                                            assertFailure
                                                "full-queue submission survived executor fault"
        , testCase "declared launch failure remains request-local" do
            prepared <- preparedTypedTask 0
            let missing = vampire
                    "/definitely/missing/felix-vampire"
                    defaultTimeLimit
                    defaultMemoryLimit
            withVampireExecutor
                (positiveJobs 1)
                missing
                (\_position _request -> pure ())
                \executor -> withVampireRequestOwner executor \owner -> do
                    handle <- submitVampireRequest
                        owner
                        (workPosition 1 1)
                        testLocation
                        (preparedTypedProverRequest prepared)
                    completion <- awaitVampireRequest handle
                    assertCompletionRequest prepared completion
                    case vampireCompletionTerminal completion of
                        VampireProcessFailed ProverLaunchFailed{} -> pure ()
                        terminal ->
                            assertFailure
                                ("expected a local launch failure, got "
                                    <> show terminal)
        , testCase "protocol failure is distinct from ATP rejection" do
            prepared <- preparedTypedTask 0
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\n' 'completed without an SZS status'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            completion <- awaitVampireRequest handle
                            assertCompletionRequest prepared completion
                            case vampireCompletionTerminal completion of
                                VampireProtocolFailed{} -> pure ()
                                terminal ->
                                    assertFailure
                                        ("expected a protocol terminal, got "
                                            <> show terminal)
        , testCase "completed rejection diagnostics are compact" do
            prepared <- preparedTypedTask 0
            let headMarker :: Text
                headMarker = "HEAD-MARKER"
                tailMarker :: Text
                tailMarker = "TAIL-MARKER"
            withFakeVampire
                [ "printf '%s' 'HEAD-MARKER'"
                , "head -c 1048576 /dev/zero"
                , "printf '%s\n' 'TAIL-MARKER'"
                , "printf '%s\n' '% SZS status CounterSatisfiable for fake'"
                ]
                \vampireCommand ->
                    withVampireExecutor
                        (positiveJobs 1)
                        vampireCommand
                        (\_position _request -> pure ())
                        \executor -> withVampireRequestOwner executor \owner -> do
                            handle <- submitVampireRequest
                                owner
                                (workPosition 1 1)
                                testLocation
                                (preparedTypedProverRequest prepared)
                            resolution <-
                                awaitPreparedVampireRequest
                                    (preparedTypedProverRequest prepared)
                                    handle
                            vampireResolutionWorkPosition resolution
                                `shouldBe` Just (workPosition 1 1)
                            case vampireResolutionFailure resolution of
                                Just failed -> do
                                    let diagnostic =
                                            Terminal.renderTerminalDiagnostic
                                                (failedVampireResolutionDiagnostic
                                                    testLocation failed)
                                    assertBool
                                        "default diagnostic is compact"
                                        (Text.length diagnostic < 3000)
                                    assertBool
                                        "default diagnostic identifies the outcome"
                                        ("FELIX-ATP-COUNTERMODEL"
                                            `Text.isInfixOf` diagnostic)
                                    assertBool
                                        "default diagnostic identifies live execution"
                                        ("this obligation ran live in this invocation"
                                            `Text.isInfixOf` diagnostic)
                                    assertBool
                                        "default diagnostic identifies the obligation"
                                        ("obligation id:"
                                            `Text.isInfixOf` diagnostic)
                                    assertBool
                                        "default diagnostic identifies the dump position"
                                        ("run-local live position: module 1, task 1"
                                            `Text.isInfixOf` diagnostic)
                                    assertBool
                                        "default diagnostic avoids the old request label"
                                        (not ("prover request"
                                            `Text.isInfixOf` diagnostic))
                                    assertBool
                                        "default diagnostic omits captured stdout"
                                        (not (headMarker `Text.isInfixOf` diagnostic))
                                    assertBool
                                        "default diagnostic omits captured stdout tail"
                                        (not (tailMarker `Text.isInfixOf` diagnostic))
                                Nothing ->
                                    assertFailure "expected a rejected resolution"
        ]

positiveJobs :: Int -> EffectiveJobs
positiveJobs amount =
    fromMaybe
        (error "test requested a non-positive job count")
        (effectiveJobs amount)

scriptedClock :: [Word64] -> IO (IO Word64)
scriptedClock ticks = do
    remaining <- newIORef ticks
    pure
        (atomicModifyIORef' remaining \case
            next : rest -> (rest, next)
            [] -> error "test monotonic clock exhausted")

testLocation :: Location
testLocation = Nowhere

vampireStatusParserTests :: TestTree
vampireStatusParserTests =
    testGroup "Vampire status parser"
        [ testCase "parses canonical status lines" do
            parseMaybe
                vampireStatusParser
                "% SZS status ContradictoryAxioms for 2260"
                `shouldBe` Just StatusContradictoryAxioms
        , testCase "parses worker-prefixed status lines" do
            parseMaybe
                vampireStatusParser
                "% (2581105)SZS status Timeout for "
                `shouldBe` Just StatusTimeout
        , testCase "parses ResourceOut status" do
            parseMaybe
                vampireStatusParser
                "% SZS status ResourceOut for 2260"
                `shouldBe` Just StatusResourceOut
        , testCase "retains unsupported status values" do
            parseMaybe
                vampireStatusParser
                "% SZS status AlienResult for 2260"
                `shouldBe` Just (UnsupportedStatus "AlienResult")
        ]

vampireClassifierTests :: TestTree
vampireClassifierTests =
    testGroup "Vampire completed transcript classifier"
        [ testCase "maps each terminal status in both task modes" do
            classify DirectTask [StatusTheorem]
                `shouldBe` Right Proved
            classify DirectTask [StatusCounterSatisfiable]
                `shouldBe` Right Counterexample
            classify DirectTask [StatusContradictoryAxioms]
                `shouldBe` Right ContradictoryInput
            classify IndirectTask [StatusContradictoryAxioms]
                `shouldBe` Right Proved
        , testCase "maps every resource status to indeterminate" do
            for_ indeterminateStatusReasons \(status, reason) ->
                classify DirectTask [status]
                    `shouldBe` Right (Indeterminate (reason :| []))
        , testCase "retains compatible indeterminate reasons deterministically" do
            classify DirectTask
                [StatusUnknown, StatusTimeout, StatusResourceOut]
                `shouldBe`
                    Right
                        (Indeterminate
                            (AtpTimedOut :| [AtpResourceOut, AtpUnknown]))
        , testCase "lets a unique terminal outcome override resource statuses" do
            for_ indeterminateStatuses \status ->
                classify DirectTask [status, StatusTheorem]
                    `shouldBe` Right Proved
        , testCase "accepts duplicate and equivalent terminal statuses" do
            classify DirectTask [StatusTheorem, StatusTheorem]
                `shouldBe` Right Proved
            classify
                IndirectTask
                [StatusTheorem, StatusContradictoryAxioms]
                `shouldBe` Right Proved
        , testCase "rejects every pair of different terminal outcomes" do
            for_ conflictingTerminalCases
                \(mode, statuses, outcomes) ->
                    classify mode statuses
                        `shouldBe`
                            Left (ConflictingTerminalOutcomes outcomes)
        , testCase "is independent of status order" do
            for_ orderCases \(mode, statuses) ->
                classify mode statuses
                    `shouldBe` classify mode (reverse statuses)
        , testCase "rejects unsupported status values" do
            classify
                DirectTask
                [StatusTheorem, UnsupportedStatus "AlienResult"]
                `shouldBe`
                    Left
                        (UnsupportedVampireStatuses
                            (Set.singleton "AlienResult"))
        , testCase "rejects a successful exit without an outcome" do
            classify DirectTask []
                `shouldBe` Left MissingVampireOutcome
        , testCase "accepts resource statuses after a nonzero exit" do
            for_ indeterminateStatusReasons \(status, reason) ->
                classifyVampireProtocol
                    DirectTask
                    (ExitFailure 1)
                    [status]
                    `shouldBe` Right (Indeterminate (reason :| []))
        , testCase "rejects a terminal status after a nonzero exit" do
            classifyVampireProtocol
                DirectTask
                (ExitFailure 7)
                [StatusTheorem]
                `shouldBe`
                    Left (UnsuccessfulVampireExit (ExitFailure 7))
        ]

vampireProcessTests :: TestTree
vampireProcessTests =
    testGroup "Vampire process boundary"
        [ testCase "classifies statuses from both completed streams" do
            answer <- runFakeVampire
                [ "printf '%s\\n' '% SZS status Timeout for fake'"
                , "printf '%s\\n' '% SZS status Theorem for fake' >&2"
                , "exit 0"
                ]
            assertProved answer
        , testCase "rejects a split-stream terminal conflict" do
            answer <- runFakeVampire
                [ "printf '%s\\n' '% SZS status Theorem for fake'"
                , "printf '%s\\n' '% SZS status CounterSatisfiable for fake' >&2"
                , "exit 0"
                ]
            assertProtocolError "ConflictingTerminalOutcomes" answer
        , testCase "rejects a theorem from a nonzero exit" do
            answer <- runFakeVampire
                [ "printf '%s\\n' '% SZS status Theorem for fake'"
                , "exit 7"
                ]
            assertProtocolError "ExitFailure 7" answer
        , testCase "reports a timeout from a nonzero exit as indeterminate" do
            answer <- runFakeVampire
                [ "printf '%s\\n' '% SZS status Timeout for fake'"
                , "exit 1"
                ]
            assertRejected
                (RejectedIndeterminate (AtpTimedOut :| []))
                answer
        , testCase "validates UTF-8 and status lines across separate writes" do
            prepared <- preparedTypedTask 0
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '\\303'"
                , "sleep 0.01"
                , "printf '\\251\\n%% SZS status Theo'"
                , "sleep 0.01"
                , "printf 'rem for fake\\n'"
                ] \command -> runPreparedTypedProver command prepared >>= assertProved
        , testCase "rejects malformed stderr after a theorem line" do
            prepared <- preparedTypedTask 0
            withFakeVampire
                [ "cat >/dev/null"
                , "printf '%s\\n' '% SZS status Theorem for fake'"
                , "sleep 0.01"
                , "printf '\\377' >&2"
                ] \command -> do
                    result <- runPreparedTypedProver command prepared
                    case resolutionFailure result of
                        Just (VampireFailureProcess (ProverOutputMalformedUtf8 _ ProverOutputStderr _)) -> pure ()
                        _ -> assertFailure ("late malformed output was accepted: " <> show result)
        , testCase "rejects malformed UTF-8 output" do
            answer <- runFakeVampire
                [ "printf '\\377'"
                , "exit 0"
                ]
            case resolutionFailure answer of
                Just
                    (VampireFailureProcess
                        (ProverOutputMalformedUtf8
                            _
                            ProverOutputStdout
                            _)) ->
                        pure ()
                _ ->
                    assertFailure
                        ("expected malformed stdout, got " <> show answer)
        , testCase "returns a broken stdin pipe" do
            prepared <- preparedTypedTask 20000
            result <- withFakeVampire
                [ "exec 0<&-"
                , "sleep 1"
                ]
                \vampireCommand ->
                    runPreparedTypedProver vampireCommand prepared
            case resolutionFailure result of
                Just
                    (VampireFailureProcess
                        (ProverCommunicationFailed _ ProverStdin _)) ->
                    pure ()
                _ ->
                    assertFailure
                        ("expected a communication failure, got "
                            <> show result)
        , testCase "drains output while feeding prover input" do
            prepared <- preparedTypedTask 20000
            guardedAnswer <- Timeout.timeout
                30000000
                (withFakeVampire
                    [ "head -c 1048576 /dev/zero &"
                    , "head -c 1048576 /dev/zero >&2 &"
                    , "wait"
                    , "printf '\\n'"
                    , "printf '\\n' >&2"
                    , "cat >/dev/null"
                    , "printf '%s\\n' '% SZS status Theorem for fake'"
                    , "exit 0"
                    ]
                    \vampireCommand -> do
                        runPreparedTypedProver vampireCommand prepared)
            case guardedAnswer of
                Nothing ->
                    assertFailure "prover communication did not finish"
                Just answer ->
                    assertProved answer
        , testCase "reports signal termination separately" do
            prepared <- preparedTypedTask 0
            result <- withFakeVampire
                [ "cat >/dev/null"
                , "kill -TERM $$"
                ]
                \vampireCommand ->
                    runPreparedTypedProver vampireCommand prepared
            case resolutionFailure result of
                Just
                    (VampireFailureProcess
                        (ProverTerminatedBySignal
                            _
                            signalNumber
                            _)) ->
                            assertEqual
                                "termination signal"
                                (fromIntegral sigTERM)
                                signalNumber
                _ ->
                    assertFailure
                        ("expected signal termination, got "
                            <> show result)
        , testCase "deadline terminates and reaps the process group" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                (Seconds 0)
                []
                \pidFile vampireCommand -> do
                    result <-
                        runPreparedTypedProverWithObserver
                            (\_ -> void (waitForProcessIds pidFile))
                            vampireCommand prepared
                    assertTimedOut result
                    processIds <- readProcessIds pidFile
                    assertProcessesGone processIds
        , testCase "output exhaustion terminates the process group" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                defaultTimeLimit
                [ "head -c 33554432 /dev/zero"
                ]
                \pidFile vampireCommand -> do
                    result <-
                        runPreparedTypedProver vampireCommand prepared
                    case resolutionFailure result of
                        Just
                            (VampireFailureProcess
                                (ProverOutputLimitExceeded
                                    _
                                    ProverOutputStdout
                                    _)) ->
                                    pure ()
                        _ ->
                            assertFailure
                                ("expected stdout limit exhaustion, got "
                                    <> show result)
                    processIds <- readProcessIds pidFile
                    assertProcessesGone processIds
        , testCase "cancellation terminates and reaps the process group" do
            prepared <- preparedTypedTask 0
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand ->
                    withAsync
                        (runPreparedTypedProver vampireCommand prepared)
                        \worker -> do
                            processIds <- waitForProcessIds pidFile
                            cancel worker
                            assertProcessesGone processIds
        , testCase "observer cancellation remains asynchronous" do
            prepared <- preparedTypedTask 0
            observerEntered <- newEmptyMVar
            withProcessGroupFake
                defaultTimeLimit
                []
                \pidFile vampireCommand ->
                    withAsync
                        (runPreparedTypedProverWithObserver
                            (\_request -> do
                                putMVar observerEntered ()
                                threadDelay maxBound)
                            vampireCommand
                            prepared)
                        \worker -> do
                            takeMVar observerEntered
                            processIds <- waitForProcessIds pidFile
                            cancel worker
                            Async.waitCatch worker >>= \case
                                Left failure ->
                                    case Exception.fromException failure
                                            :: Maybe Async.AsyncCancelled of
                                        Just _cancelled -> pure ()
                                        Nothing ->
                                            assertFailure
                                                ("expected AsyncCancelled, got "
                                                    <> show failure)
                                Right answer ->
                                    assertFailure
                                        ("observer swallowed cancellation: "
                                            <> show answer)
                            assertProcessesGone processIds
        ]

classify
    :: VampireTaskMode
    -> [VampireStatus]
    -> Either VampireProtocolError CanonicalAtpOutcome
classify mode =
    classifyVampireProtocol mode ExitSuccess

indeterminateStatuses :: [VampireStatus]
indeterminateStatuses = fst <$> indeterminateStatusReasons

indeterminateStatusReasons
    :: [(VampireStatus, AtpIndeterminateReason)]
indeterminateStatusReasons =
    [ (StatusTimeout, AtpTimedOut)
    , (StatusResourceOut, AtpResourceOut)
    , (StatusGaveUp, AtpGaveUp)
    , (StatusUnknown, AtpUnknown)
    ]

conflictingTerminalCases
    :: [(VampireTaskMode, [VampireStatus], Set CanonicalAtpOutcome)]
conflictingTerminalCases =
    [ ( DirectTask
      , [StatusTheorem, StatusCounterSatisfiable]
      , Set.fromList [Proved, Counterexample]
      )
    , ( DirectTask
      , [StatusTheorem, StatusContradictoryAxioms]
      , Set.fromList [Proved, ContradictoryInput]
      )
    , ( DirectTask
      , [StatusCounterSatisfiable, StatusContradictoryAxioms]
      , Set.fromList [Counterexample, ContradictoryInput]
      )
    , ( IndirectTask
      , [StatusTheorem, StatusCounterSatisfiable]
      , Set.fromList [Proved, Counterexample]
      )
    , ( IndirectTask
      , [StatusCounterSatisfiable, StatusContradictoryAxioms]
      , Set.fromList [Proved, Counterexample]
      )
    ]

orderCases :: [(VampireTaskMode, [VampireStatus])]
orderCases =
    [ (DirectTask, StatusTheorem : indeterminateStatuses)
    , (DirectTask, [StatusTheorem, StatusCounterSatisfiable])
    , (IndirectTask, [StatusTheorem, StatusContradictoryAxioms])
    , (DirectTask, [UnsupportedStatus "B", UnsupportedStatus "A"])
    ]

assertProved
    :: VampireResolution
    -> Assertion
assertProved answer =
    case vampireResolutionAcceptedRequestId answer of
        Just _requestId -> pure ()
        Nothing ->
            assertFailure ("expected a proof, got " <> show answer)

assertRejected
    :: CanonicalAtpRejection
    -> VampireResolution
    -> Assertion
assertRejected expected resolution =
    case resolutionFailure resolution of
        Just (VampireFailureRejected actual _evidence) ->
            actual `shouldBe` expected
        _ ->
            assertFailure
                ("expected ATP rejection " <> show expected
                    <> ", got " <> show resolution)

resolutionFailure :: VampireResolution -> Maybe VampireFailure
resolutionFailure resolution =
    failedVampireResolutionFailure
        <$> vampireResolutionFailure resolution

assertAcceptedRequest
    :: PreparedTypedProverTask ref local origin global
    -> VampireCompletion
    -> Assertion
assertAcceptedRequest prepared completion = do
    assertCompletionRequest prepared completion
    case vampireCompletionTerminal completion of
        VampireAccepted -> pure ()
        terminal ->
            assertFailure ("expected an accepted terminal, got " <> show terminal)

assertCompletionRequest
    :: PreparedTypedProverTask ref local origin global
    -> VampireCompletion
    -> Assertion
assertCompletionRequest prepared completion =
    vampireCompletionRequestId completion
        `shouldBe`
            preparedVerificationRequestId
                (preparedTypedProverRequest prepared)

assertCancelled
    :: PreparedTypedProverTask ref local origin global
    -> VampireCompletion
    -> Assertion
assertCancelled prepared completion = do
    assertCompletionRequest prepared completion
    vampireCompletionTerminal completion `shouldBe` VampireCancelled

awaitObserverFault :: IO value -> Assertion
awaitObserverFault action = do
    result <- Exception.try action
    case result of
        Left failure -> assertObserverFault failure
        Right _value -> assertFailure "expected a global executor fault"

assertObserverFault :: Exception.SomeException -> Assertion
assertObserverFault failure =
    case Exception.fromException failure :: Maybe Exception.IOException of
        Just observerFailure ->
            assertBool
                "observer failure message"
                ("fatal observer fault"
                    `Text.isInfixOf` Text.pack (show observerFailure))
        Nothing ->
            assertFailure
                ("expected the original observer exception, got "
                    <> show failure)

assertProtocolError
    :: Text
    -> VampireResolution
    -> Assertion
assertProtocolError expected resolution =
    case resolutionFailure resolution of
        Just (VampireFailureProtocol protocolFailure _evidence) ->
            assertBool
                ( "expected protocol error containing "
                    <> show expected
                    <> ", got "
                    <> show protocolFailure
                )
                (expected `Text.isInfixOf` Text.pack (show protocolFailure))
        _ ->
            assertFailure
                ("expected a protocol error, got " <> show resolution)

assertTimedOut
    :: VampireResolution
    -> Assertion
assertTimedOut result =
    case resolutionFailure result of
        Just (VampireFailureProcess ProverTimedOut{}) -> pure ()
        _ ->
            assertFailure ("expected prover timeout, got " <> show result)

withProcessGroupFake
    :: TimeLimit
    -> [String]
    -> (FilePath -> Vampire -> IO a)
    -> IO a
withProcessGroupFake timeLimit body action =
    withFakeVampireIn
        (\temp ->
            let pidFile = temp </> "process-ids"
            in [ "trap '' TERM"
               , "sleep 60 &"
               , "printf '%s %s\\n' \"$$\" \"$!\" > " <> pidFile
               ]
                <> body
                <> ["wait"])
        timeLimit
        \temp ->
            action (temp </> "process-ids")

readProcessIds :: FilePath -> IO [ProcessID]
readProcessIds path = do
    contents <- Text.readFile path
    case traverse
        (readMaybe . Text.unpack)
        (Text.words contents) of
        Just processIds@[_leader, _descendant] ->
            pure processIds
        _ ->
            assertFailure
                ("expected leader and descendant process ids, got "
                    <> show contents)

waitForProcessIds :: FilePath -> IO [ProcessID]
waitForProcessIds path = do
    guarded <- Timeout.timeout 10000000 loop
    case guarded of
        Just processIds ->
            pure processIds
        Nothing ->
            assertFailure "fake prover did not publish its process ids"
  where
    loop = do
        exists <- Directory.doesFileExist path
        if exists
            then readProcessIds path
            else do
                threadDelay 10000
                loop

assertProcessesGone :: [ProcessID] -> Assertion
assertProcessesGone processIds = do
    guarded <- Timeout.timeout 10000000 loop
    case guarded of
        Just () ->
            pure ()
        Nothing ->
            assertFailure
                ("supervisor left processes running: "
                    <> show processIds)
  where
    loop = do
        alive <- traverse processIsAlive processIds
        if or alive
            then do
                threadDelay 10000
                loop
            else pure ()

processIsAlive :: ProcessID -> IO Bool
processIsAlive processId =
    (signalProcess nullSignal processId >> pure True)
        `Exception.catch` \(err :: Exception.IOException) ->
            if isDoesNotExistError err
                then pure False
                else throwIO err

runFakeVampire
    :: [String]
    -> IO VampireResolution
runFakeVampire scriptLines =
    withFakeVampire
        (["cat >/dev/null"] <> scriptLines)
        \vampireCommand -> do
            prepared <- preparedTypedTask 0
            runPreparedTypedProver vampireCommand prepared

withFakeVampire
    :: [String]
    -> (Vampire -> IO a)
    -> IO a
withFakeVampire scriptLines action =
    withFakeVampireIn
        (const scriptLines)
        defaultTimeLimit
        (const action)

withFakeVampireIn
    :: (FilePath -> [String])
    -> TimeLimit
    -> (FilePath -> Vampire -> IO a)
    -> IO a
withFakeVampireIn makeScript timeLimit action =
    withTemporaryDirectory "felix-fake-vampire" \temp -> do
        let executablePath = temp </> "vampire"
        writeFile executablePath
            (unlines
                ( [ "#!/bin/sh"
                  ]
                    <> makeScript temp
                ))
        permissions <- Directory.getPermissions executablePath
        Directory.setPermissions executablePath
            (Directory.setOwnerExecutable True permissions)
        action
            temp
            (vampire
                executablePath
                timeLimit
                defaultMemoryLimit)


shouldBe :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
shouldBe =
    flip (assertEqual "")

preparedTypedTask
    :: Int
    -> IO (PreparedTypedProverTask Int Void Void Void)
preparedTypedTask factCount = do
    checked <- expectRight
        (checkScopedCanonicalCore
            emptyGlobalTyping
            []
            propositionTerm)
    proposition <- expectRight
        (supportedProposition Vector.empty checked)
    capability <- expectRight
        (classifySupportedProposition emptyGlobalTyping proposition)
    let facts =
            Vector.generate
                factCount
                (\reference ->
                    typedBackendFact reference proposition capability)
    problem <- expectRight
        (planTypedProblem
            emptyGlobalTyping
            facts
            proposition
            []
            []
            FirstOrderLocals)
    expectRight (prepareTypedProverTask DirectTask problem)
  where
    propositionTerm =
        CEq TySet
            (CIntrinsic Empty)
            (CIntrinsic Empty)

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left failure ->
        assertFailure (show failure) >> fail "unreachable"
    Right value ->
        pure value
