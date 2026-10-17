{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.OutputPlan (unitTests) where

import Base
import Felix.OutputPlan qualified as Output
import Felix.Render.Html.Output qualified as Html
import Felix.Source
import Felix.Store qualified as Store

import Control.Exception qualified as Exception
import System.Directory qualified as Directory
import System.Environment qualified as Environment
import System.FilePath.Posix qualified as Posix
import System.IO.Temp qualified as Temp
import System.Posix.Files qualified as PosixFiles
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Verification output preflight"
        [ testCase "accepts absent and empty dump destinations"
            acceptsAbsentAndEmptyDumpDestinations
        , testCase "rejects a nonempty dump before store startup"
            rejectsNonemptyDumpBeforeStoreStartup
        , testCase "rejects persistent and fresh store collisions"
            rejectsStoreCollisions
        , testCase "reserves the store rollback journal"
            reservesRollbackJournal
        , testCase "reserves refresh-only SQLite auxiliaries"
            reservesRefreshAuxiliaries
        , testCase "reserves the store lock sidecar"
            reservesStoreLock
        , testCase "rejects dump and HTML route collisions"
            rejectsDumpHtmlCollisions
        , testCase "reserves the complete HTML publication workspace"
            reservesPublicationWorkspace
        , testCase "checks directory aliases and absent descendant namespaces"
            checksDirectoryAliases
        , testCase "protects entries and only the referents actually followed"
            checksFinalSymlinks
        ]

checksDirectoryAliases :: Assertion
checksDirectoryAliases =
    Temp.withSystemTempDirectory "felix-output-alias" \root -> do
        let real = root Posix.</> "real"
            alias = root Posix.</> "alias"
        Directory.createDirectory real
        PosixFiles.createSymbolicLink real alias
        relative <- expectRight (safeRelativePath "page.html")
        for_ [(real, alias), (alias, real)] \(storeParent, outputParent) -> do
            plan <- expectRightIO (Store.planStore (Store.ExplicitStore (storeParent Posix.</> "absent")))
            path <- expectPersistentPath plan
            expectCollision =<< Output.planVerificationOutputs path False Nothing
                (Just (outputParent Posix.</> "absent", [relative]))
            expectCollision =<< Output.planVerificationOutputs path False
                (Just (outputParent Posix.</> "absent/nested")) Nothing
            expectCollision =<< Output.planVerificationOutputs path True Nothing
                (Just (outputParent Posix.</> "absent.lock", [relative]))

checksFinalSymlinks :: Assertion
checksFinalSymlinks =
    Temp.withSystemTempDirectory "felix-output-final-link" \root -> do
        let html = root Posix.</> "html"
            selected = root Posix.</> "selected.sqlite"
            target = html Posix.</> "database"
            lock = selected <> ".lock"
        relative <- expectRight (safeRelativePath "page.html")
        PosixFiles.createSymbolicLink target selected
        plan <- expectRightIO (Store.planStore (Store.ExplicitStore selected))
        path <- expectPersistentPath plan
        -- A dangling selected link is followed by ordinary open, but refresh
        -- removes that entry. Its operational spelling must stay unchanged.
        Store.storePathFilePath path @?= selected
        expectCollision =<< Output.planVerificationOutputs path False Nothing (Just (html, [relative]))
        void . expectOutputRight =<< Output.planVerificationOutputs path True Nothing (Just (html, [relative]))
        PosixFiles.readSymbolicLink selected >>= (@?= target)
        PosixFiles.createSymbolicLink (html Posix.</> "lock-target") lock
        expectCollision =<< Output.planVerificationOutputs path True Nothing (Just (html, [relative]))
        Directory.removeFile lock

        -- Removing an HTML root also removes entries whose referents lie outside it.
        Directory.createDirectory html
        PosixFiles.createSymbolicLink (root Posix.</> "outside.sqlite") target
        insidePlan <- expectRightIO (Store.planStore (Store.ExplicitStore target))
        inside <- expectPersistentPath insidePlan
        expectCollision =<< Output.planVerificationOutputs inside False Nothing (Just (html, [relative]))

        let dump = root Posix.</> "dump"
            emptyDirectory = root Posix.</> "empty"
        Directory.createDirectory emptyDirectory
        PosixFiles.createSymbolicLink emptyDirectory dump
        nestedPlan <- expectRightIO (Store.planStore (Store.ExplicitStore (emptyDirectory Posix.</> "store.sqlite")))
        nested <- expectPersistentPath nestedPlan
        expectCollision =<< Output.planVerificationOutputs nested False (Just dump) Nothing
        Directory.removeFile dump
        PosixFiles.createSymbolicLink (root Posix.</> "missing") dump
        expectInspectionFailure =<< Output.planVerificationOutputs nested False (Just dump) Nothing

        let journal = selected <> "-journal"
        PosixFiles.createSymbolicLink (html Posix.</> "journal") journal
        void . expectOutputRight =<< Output.planVerificationOutputs path True Nothing (Just (html, [relative]))
        Directory.removeFile selected
        expectCollision =<< Output.planVerificationOutputs path True Nothing (Just (html, [relative]))
        Directory.removeFile journal
        PosixFiles.createSymbolicLink selected selected
        expectInspectionFailure =<< Output.planVerificationOutputs path False Nothing (Just (html, [relative]))
  where
    expectInspectionFailure = \case
        Left Output.OutputPathInspectionFailed{} -> pure ()
        Left other -> assertFailure ("unexpected path inspection failure: " <> show other)
        Right _ -> assertFailure "an unresolvable path was treated as absent"

acceptsAbsentAndEmptyDumpDestinations :: Assertion
acceptsAbsentAndEmptyDumpDestinations =
    Temp.withSystemTempDirectory "felix-output-dump" \root -> do
        let storeParent = root Posix.</> "store"
            storeFile = storeParent Posix.</> "store.sqlite"
            dump = root Posix.</> "dump"
        Directory.createDirectory storeParent
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore storeFile))
        storePath <- expectPersistentPath plan
        absent <- Output.planVerificationOutputs
            storePath
            False
            (Just dump)
            Nothing
        plannedAbsent <- expectOutputRight absent
        assertEqual "absent dump path"
            (Just dump)
            (Output.dumpOutputPath
                <$> Output.verificationDumpOutput plannedAbsent)

        Directory.createDirectory dump
        emptyResult <- Output.planVerificationOutputs
            storePath
            False
            (Just dump)
            Nothing
        void (expectOutputRight emptyResult)

rejectsNonemptyDumpBeforeStoreStartup :: Assertion
rejectsNonemptyDumpBeforeStoreStartup =
    Temp.withSystemTempDirectory "felix-output-before-store" \root -> do
        let cacheRoot = root Posix.</> "cache"
            dump = root Posix.</> "dump"
        Directory.createDirectory cacheRoot
        Directory.createDirectory dump
        writeFile (dump Posix.</> "old.p") "stale"
        withEnvironment "XDG_CACHE_HOME" cacheRoot do
            plan <- expectRightIO
                (Store.planStore Store.DefaultStore)
            storePath <- expectPersistentPath plan
            result <- Output.planVerificationOutputs
                storePath
                False
                (Just dump)
                Nothing
            case result of
                Left Output.DumpDestinationNotEmpty{} ->
                    pure ()
                Left other ->
                    assertFailure
                        ("unexpected nonempty result: " <> show other)
                Right _ ->
                    assertFailure "nonempty dump was accepted"
            assertBool "preflight did not create the default store"
                . not
                =<< Directory.doesPathExist
                    (cacheRoot Posix.</> "felix")

rejectsStoreCollisions :: Assertion
rejectsStoreCollisions =
    Temp.withSystemTempDirectory "felix-output-store-collision" \root -> do
        let dump = root Posix.</> "dump"
            persistentStore = dump Posix.</> "store.sqlite"
        Directory.createDirectory dump
        persistentPlan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore persistentStore))
        persistentPath <- expectPersistentPath persistentPlan
        persistentResult <- Output.planVerificationOutputs
            persistentPath
            False
            (Just dump)
            Nothing
        expectCollision persistentResult

        freshPlan <- expectRightIO
            (Store.planStore Store.FreshTemporaryStore)
        withTestStoreLease freshPlan \lease -> do
            let freshParent =
                    Posix.takeDirectory
                        (Store.storePathFilePath
                            (Store.storeLeasePath lease))
            freshResult <- Output.planVerificationOutputs
                (Store.storeLeasePath lease)
                False
                (Just freshParent)
                Nothing
            expectCollision freshResult

        relative <- expectRight (safeRelativePath "page.html")
        let htmlRoot = root Posix.</> "html"
            htmlStore = htmlRoot Posix.</> "page.html"
        Directory.createDirectory htmlRoot
        htmlPlan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore htmlStore))
        htmlPath <- expectPersistentPath htmlPlan
        htmlResult <- Output.planVerificationOutputs
            htmlPath
            False
            Nothing
            (Just (htmlRoot, [relative]))
        expectCollision htmlResult

reservesPublicationWorkspace :: Assertion
reservesPublicationWorkspace =
    Temp.withSystemTempDirectory "felix-output-publication" \root -> do
        let htmlRoot = root Posix.</> "html"
            workspace = htmlRoot <> ".felix-publication"
        relative <- expectRight (safeRelativePath "page.html")
        for_ [workspace, workspace <> ".lock"] \storeFile -> do
            plan <- expectRightIO (Store.planStore (Store.ExplicitStore storeFile))
            path <- expectPersistentPath plan
            result <- Output.planVerificationOutputs path False Nothing (Just (htmlRoot, [relative]))
            if storeFile == workspace then expectCollision result
                else void (expectOutputRight result)
        plan <- expectRightIO (Store.planStore (Store.ExplicitStore (root Posix.</> "store.sqlite")))
        path <- expectPersistentPath plan
        for_ [workspace, workspace Posix.</> "lock", workspace Posix.</> "nested/dump"] \dump ->
            expectCollision =<< Output.planVerificationOutputs path False (Just dump) (Just (htmlRoot, [relative]))
        assertBool "planning created the workspace" . not =<< Directory.doesPathExist workspace
        htmlPlan <- expectRightIO (Html.planHtmlOutput htmlRoot [Html.preparedHtmlArtefact relative (Right "page")])
        expectRightIO (Html.writeHtmlOutput htmlPlan)
        for_ [workspace Posix.</> "store.sqlite", workspace Posix.</> "lock"] \storeFile -> do
            selected <- expectRightIO (Store.planStore (Store.ExplicitStore storeFile))
            selectedPath <- expectPersistentPath selected
            expectCollision =<< Output.planVerificationOutputs selectedPath False Nothing (Just (htmlRoot, [relative]))

rejectsDumpHtmlCollisions :: Assertion
rejectsDumpHtmlCollisions =
    Temp.withSystemTempDirectory "felix-output-cross-collision" \root -> do
        let storeParent = root Posix.</> "store"
            storeFile = storeParent Posix.</> "store.sqlite"
            htmlRoot = root Posix.</> "html"
        Directory.createDirectory storeParent
        Directory.createDirectory htmlRoot
        relative <- expectRight (safeRelativePath "nested/page.html")
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore storeFile))
        storePath <- expectPersistentPath plan
        result <- Output.planVerificationOutputs
            storePath
            False
            (Just htmlRoot)
            (Just (htmlRoot, [relative]))
        expectCollision result

reservesRollbackJournal :: Assertion
reservesRollbackJournal =
    Temp.withSystemTempDirectory "felix-output-journal" \root -> do
        let storeParent = root Posix.</> "store"
            storeFile = storeParent Posix.</> "store.sqlite"
            journal = storeFile <> "-journal"
        Directory.createDirectory storeParent
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore storeFile))
        storePath <- expectPersistentPath plan
        result <- Output.planVerificationOutputs
            storePath
            False
            (Just journal)
            Nothing
        case result of
            Left
                (Output.CollidingOutputNamespaces
                    (Output.OutputNamespaceCollision
                        Output.StoreJournalOutputNamespace
                        reserved
                        Output.DumpOutputNamespace
                        requested :| [])) -> do
                            assertEqual "reserved journal" journal reserved
                            assertEqual "requested dump" journal requested
            Left other ->
                assertFailure
                    ("unexpected journal collision: " <> show other)
            Right _ ->
                assertFailure "store rollback journal was not reserved"

reservesRefreshAuxiliaries :: Assertion
reservesRefreshAuxiliaries =
    Temp.withSystemTempDirectory "felix-output-refresh" \root -> do
        let storeFile = root Posix.</> "store.sqlite"
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore storeFile))
        storePath <- expectPersistentPath plan
        let auxiliaries =
                [ ( Output.StoreWriteAheadLogOutputNamespace
                  , Store.storeWriteAheadLogPath storePath
                  )
                , ( Output.StoreSharedMemoryOutputNamespace
                  , Store.storeSharedMemoryPath storePath
                  )
                ]
        for_ auxiliaries \(owner, auxiliary) -> do
            result <- Output.planVerificationOutputs
                storePath
                True
                (Just auxiliary)
                Nothing
            case result of
                Left
                    (Output.CollidingOutputNamespaces
                        (Output.OutputNamespaceCollision
                            actualOwner
                            reserved
                            Output.DumpOutputNamespace
                            requested :| [])) -> do
                                assertEqual "auxiliary owner"
                                    owner actualOwner
                                assertEqual "reserved auxiliary"
                                    auxiliary reserved
                                assertEqual "requested dump"
                                    auxiliary requested
                Left other ->
                    assertFailure
                        ("unexpected auxiliary collision: " <> show other)
                Right _ ->
                    assertFailure "refresh auxiliary was not reserved"

        ordinary <- Output.planVerificationOutputs
            storePath
            False
            (Just (Store.storeWriteAheadLogPath storePath))
            Nothing
        void (expectOutputRight ordinary)

reservesStoreLock :: Assertion
reservesStoreLock =
    Temp.withSystemTempDirectory "felix-output-lock" \root -> do
        let storeParent = root Posix.</> "store"
            storeFile = storeParent Posix.</> "store.sqlite"
            lock = storeFile <> ".lock"
        Directory.createDirectory storeParent
        plan <- expectRightIO
            (Store.planStore
                (Store.ExplicitStore storeFile))
        storePath <- expectPersistentPath plan
        result <- Output.planVerificationOutputs
            storePath
            False
            (Just lock)
            Nothing
        case result of
            Left
                (Output.CollidingOutputNamespaces
                    (Output.OutputNamespaceCollision
                        Output.StoreLockOutputNamespace
                        reserved
                        Output.DumpOutputNamespace
                        requested :| [])) -> do
                            assertEqual "reserved lock" lock reserved
                            assertEqual "requested dump" lock requested
            Left other ->
                assertFailure
                    ("unexpected lock collision: " <> show other)
            Right _ ->
                assertFailure "store lock sidecar was not reserved"

expectCollision
    :: Either Output.OutputPlanError Output.VerificationOutputPlan
    -> Assertion
expectCollision = \case
    Left Output.CollidingOutputNamespaces{} ->
        pure ()
    Left other ->
        assertFailure
            ("unexpected output-plan result: " <> show other)
    Right _ ->
        assertFailure "colliding output namespaces were accepted"

expectOutputRight
    :: Either Output.OutputPlanError Output.VerificationOutputPlan
    -> IO Output.VerificationOutputPlan
expectOutputRight = \case
    Left failure ->
        assertFailure (show failure) >> fail "unreachable"
    Right plan ->
        pure plan

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

expectPersistentPath :: Store.StorePlan -> IO Store.StorePath
expectPersistentPath plan =
    maybe
        (assertFailure "persistent store plan has no path"
            >> fail "unreachable")
        pure
        (Store.storePlanPersistentPath plan)

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
