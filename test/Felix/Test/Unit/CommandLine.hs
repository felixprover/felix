{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.CommandLine (unitTests) where

import Base
import Felix.Checking.Declaration qualified as Declaration
import Felix.CommandLine
import Felix.Checking.Proof qualified as Proof
import Felix.Output.Atomic qualified as Atomic
import Felix.Parse qualified as Parse
import Felix.Store qualified as Store
import Felix.Verification qualified as Verification
import Felix.Provers qualified as Provers
import Felix.Render.Html.Output qualified as HtmlOutput
import Felix.Report.Diagnostic
import Felix.Report.Location (pattern Nowhere)
import Felix.Report.Render.Terminal qualified as Terminal
import Felix.Source.Graph qualified as SourceGraph
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Token (Located(..), Token, Whitespace(..))
import Felix.Test.Temp (withTemporaryDirectory)

import Control.Exception (IOException)
import Control.Exception qualified as Exception
import Data.ByteString qualified as ByteString
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Database.SQLite.Simple qualified as SQLite
import Options.Applicative (ParserResult(..))
import Options.Applicative qualified as Options
import System.Directory qualified as Directory
import System.Environment (getEnvironment)
import System.Exit (ExitCode(..))
import System.FilePath.Posix ((</>))
import System.Process
    ( CreateProcess(..)
    , proc
    , readCreateProcessWithExitCode
    )
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests =
    testGroup "Command line"
        [ testCase "parses the closed command model"
            parsesClosedCommands
        , testCase "normalizes independent concurrency overrides"
            normalizesConcurrencyOptions
        , testCase "normalizes presentation options once"
            normalizesPresentationOptions
        , testCase "rejects conflicting command options"
            rejectsConflictingOptions
        , testCase "checks numeric options before narrowing"
            checksNumericOptions
        , testCase "maps structured outcomes to process status" do
            for_ outcomeCases \(outcome, expectedExitCode) ->
                commandOutcomeExitCode outcome
                    `shouldBe` expectedExitCode
        , testCase "reports distinct cache decisions and wall-time measures"
            rendersOperationalReport
        , testCase "reports a retained completed HTML staging tree"
            reportsRetainedHtmlStagingTree
        , testCase "assigns unique public diagnostic codes" do
            let codeTexts = diagnosticCodeText <$> allDiagnosticCodes
            length codeTexts `shouldBe` length (nubOrd codeTexts)
        , testCase "bounds and deduplicates parser expectations"
            boundsParserExpectations
        , testCase "summarizes ambiguity without parse trees"
            summarizesAmbiguousParse
        , testCase "bounds induction names only at presentation"
            boundsInductionNamesAtPresentation
        , testCase "removes an unpublished dump temporary"
            removesFailedDumpTemporary
        , testGroup "process boundary"
            [ testCase "version needs no input or store"
                versionNeedsNoInputOrStore
            , testCase "help documents store options"
                helpDocumentsStoreOptions
            , testCase "routes independent concurrency limits through verification"
                reportsIndependentConcurrency
            , testCase "parse-only uses no store or Vampire"
                parseOnlyUsesNoAuthority
            , testCase "malformed source has a stable failure class"
                malformedSourceHasStableFailure
            , testCase "reports the actual goal shape for an invalid fix"
                invalidFixReportsGoalShape
            , testCase "rejects out-of-order grouped Fix bounds"
                rejectsOutOfOrderGroupedFix
            , testCase "reports the actual goal shape for an invalid assumption"
                invalidAssumeReportsGoalShape
            , testCase "reports a structured loose-assumption mismatch"
                structuredAssumptionMismatchIsSourceLevel
            , testCase "reports an unknown proof reference"
                unknownReferenceIsSourceLevel
            , testCase "reports contextual obvious-inference evidence"
                contextualObviousFailureIsSourceLevel
            , testCase "distinguishes obvious invocation sites and methods"
                distinguishesObviousInvocationSites
            , testCase "reports all ambiguous induction binders"
                ambiguousInductionReportsBinders
            , testCase "invalid output needs no source pass or store startup"
                invalidOutputPrecedesStoreStartup
            , testCase "invalid numeric options precede store and worker startup"
                invalidNumbersPrecedeStartup
            , testCase "nested HTML routes fail before store startup"
                nestedHtmlRoutesPrecedeStoreStartup
            , testCase "verified theorem exits successfully" do
                (exitCode, stdout, stderr) <- runCliWithFakeVampire
                    [ "printf '%s\\n' '% SZS status Theorem for cli'"
                    , "exit 0"
                    ]
                exitCode `shouldBe` ExitSuccess
                stdout `shouldBe` ""
                stderr `shouldContain` "Verification successful."
                assertBool "store report is opt-in"
                    (not ("Store lookup and live execution report"
                        `List.isInfixOf` stderr))
            , testCase "reports fresh and warm store decisions"
                reportsFreshAndWarmStoreDecisions
            , testCase "refreshes only an explicitly selected store"
                refreshesOnlyExplicitStore
            , testCase "refresh is silent when the store is absent"
                refreshIsSilentWithoutStore
            , testCase "failed verification retains its store report"
                failedVerificationRetainsStoreReport
            , testCase "omitted proof reports a located explicit gap" do
                (exitCode, stdout, stderr) <-
                    runCliWithSourceAndConfiguredVampire
                        cliGapSource
                        writeNonExecutableFile
                exitCode `shouldBe` ExitSuccess
                stdout `shouldBe` ""
                stderr `shouldContain`
                    "Verification completed with explicit proof gaps."
                stderr `shouldContain` "1 explicit proof gap"
                stderr `shouldContain` "input.tex 5:5"
            , testCase "countermodel exits as verification rejection" do
                (exitCode, stdout, stderr) <- runCliWithFakeVampire
                    [ "printf '%s\\n' '% SZS status CounterSatisfiable for cli'"
                    , "exit 0"
                    ]
                exitCode `shouldBe` ExitFailure 1
                stdout `shouldBe` ""
                stderr `shouldContain`
                    "error[FELIX-ATP-COUNTERMODEL]"
                assertBool "does not print the complete TPTP request"
                    (not ("Failed TPTP task" `List.isInfixOf` stderr))
                assertBool "does not speculate about missing citations"
                    (not ("\\cref" `List.isInfixOf` stderr))
                assertBool "does not speculate about omitted proofs"
                    (not ("proof omitted" `List.isInfixOf` stderr))
            , testCase "contradictory direct input is a logical rejection" do
                (exitCode, stdout, stderr) <- runCliWithFakeVampire
                    [ "printf '%s\\n' '% SZS status ContradictoryAxioms for cli'"
                    , "exit 0"
                    ]
                exitCode `shouldBe` ExitFailure 1
                stdout `shouldBe` ""
                stderr `shouldContain`
                    "error[FELIX-ATP-CONTRADICTORY-INPUT]"
                assertBool "does not speculate about source axioms"
                    (not ("incorrect axiom" `List.isInfixOf` stderr))
                assertBool "does not speculate about omitted proofs"
                    (not ("proof omitted" `List.isInfixOf` stderr))
            , testCase "failed prover exits as infrastructure failure" do
                (exitCode, stdout, stderr) <- runCliWithFakeVampire
                    [ "printf '%s\\n' '% SZS status Theorem for cli'"
                    , "exit 7"
                    ]
                exitCode `shouldBe` ExitFailure 2
                stdout `shouldBe` ""
                stderr `shouldContain`
                    "error[FELIX-ATP-PROTOCOL]"
                stderr `shouldContain` "exit status 7"
                stderr `shouldContain`
                    "this obligation ran live in this invocation"
                stderr `shouldContain` "obligation id:"
                stderr `shouldContain`
                    "run-local live position: module 1, task 1"
            , testCase "prover launch failure exits as infrastructure failure" do
                (exitCode, stdout, stderr) <-
                    runCliWithConfiguredVampire writeNonExecutableFile
                exitCode `shouldBe` ExitFailure 2
                stdout `shouldBe` ""
                stderr `shouldContain` "Vampire could not be started"
                stderr `shouldContain`
                    "a live run was attempted for this obligation in this invocation"
                stderr `shouldContain` "obligation id:"
                stderr `shouldContain`
                    "run-local live position: module 1, task 1"
            , testCase "dumps the exact executed request once"
                dumpsExactExecutedRequest
            , testCase "launch failure dumps no request"
                launchFailureDumpsNoRequest
            , testCase "failed verification retains its executed dump subset"
                dumpsOnlyExecutedPrefix
            , testCase "dump and HTML share one verification"
                dumpAndHtmlVerifyOnce
            , testCase "semantic failure publishes no HTML"
                semanticFailurePublishesNoHtml
            , testCase "fresh and cached presentation publish equal HTML"
                freshAndCachedPresentationAgree
            , testCase "ordinary verification rejects missing render hints"
                renderHintCheckRejectsWithoutHtml
            , testCase "ordinary verification checks hints without HTML"
                renderHintCheckSucceedsWithoutHtml
            , testCase "warm verification checks hint-only edits without ATP"
                checksWarmHintEditsWithoutAtp
            , testCase
                "HTML also rejects missing hints before publication"
                combinedRenderHintCheckRejectsBeforePublication
            , testCase
                "render-hint check reports renderer failure as infrastructure"
                renderHintCheckRendererFailureIsInfrastructure
            , testCase "missing renderer data is a typed failure"
                missingRendererDataIsTyped
            , testCase
                "post-verification HTML failure retains authorization report"
                htmlFailureRetainsAuthorizationReport
            ]
        ]

boundsParserExpectations :: Assertion
boundsParserExpectations = do
    let unique = ["expected-" <> Text.pack (show index) | index <- [1..12 :: Int]]
        expectations = "expected-1" : unique
        token = Located Nowhere ("unexpected" :: Token) NoSpace
        failure = Parse.UnconsumedTokens expectations (token :| [])
    diagnostic <- maybe
        (assertFailure "unconsumed input did not produce a diagnostic"
            >> fail "unreachable")
        pure
        (Parse.parseExceptionDiagnostic failure)
    diagnosticCode diagnostic `shouldBe` DiagnosticParseUnconsumedInput
    let rendered = Terminal.renderTerminalDiagnostic diagnostic
    rendered `textShouldContain` "4 additional expectations omitted"
    Text.count "expected-1" rendered `shouldBe` 1
    assertBool "ninth expectation is not displayed"
        (not ("expected-9" `Text.isInfixOf` rendered))

summarizesAmbiguousParse :: Assertion
summarizesAmbiguousParse = do
    diagnostic <- maybe
        (assertFailure "ambiguous input did not produce a diagnostic"
            >> fail "unreachable")
        pure
        (Parse.parseExceptionDiagnostic (Parse.AmbiguousParse 3))
    diagnosticCode diagnostic `shouldBe` DiagnosticParseAmbiguous
    diagnosticPrimary diagnostic `shouldBe` Nothing
    Terminal.renderTerminalDiagnostic diagnostic
        `textShouldContain` "3 distinct parses remain"

boundsInductionNamesAtPresentation :: Assertion
boundsInductionNamesAtPresentation = do
    let names = NonEmpty.fromList
            [ Raw.NamedVar ("x" <> Text.pack (show index))
            | index <- [1..10 :: Int]
            ]
        failure =
            Proof.ProofTransfiniteInductionFocusAmbiguous
                Nowhere names
    case failure of
        Proof.ProofTransfiniteInductionFocusAmbiguous
                _location retained ->
            retained `shouldBe` names
        _other ->
            assertFailure "constructed induction ambiguity changed shape"
    diagnostic <- maybe
        (assertFailure "induction ambiguity did not produce a diagnostic"
            >> fail "unreachable")
        pure
        (Proof.proofErrorDiagnostic failure)
    let rendered = Terminal.renderTerminalDiagnostic diagnostic
    rendered `textShouldContain` "eligible binders: `x1`, `x2`"
    rendered `textShouldContain` "2 additional eligible binders omitted"
    assertBool "ninth binder is not displayed"
        (not ("`x9`" `Text.isInfixOf` rendered))

textShouldContain :: Text -> Text -> Assertion
textShouldContain actual expected =
    assertBool
        ("expected " <> show actual <> " to contain " <> show expected)
        (expected `Text.isInfixOf` actual)

parsesClosedCommands :: Assertion
parsesClosedCommands = do
    case parseCommandArguments ["--version"] of
        Success Version ->
            pure ()
        other ->
            assertFailure
                ("unexpected version parse: " <> showParserResult other)
    case parseCommandArguments ["input.tex", "--parseonly"] of
        Success (ParseOnly (Input "input.tex")) ->
            pure ()
        other ->
            assertFailure
                ("unexpected parse-only parse: " <> showParserResult other)
    case parseCommandArguments ["input.tex"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreSelection =
                            Store.DefaultStore
                        , verificationStoreRefreshRequested = False
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected default verify parse: "
                    <> showParserResult other)
    case parseCommandArguments ["input.tex", "--jobs", "3"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationModuleJobsOverride = Just jobs
                        }) ->
                            Provers.effectiveJobsValue jobs `shouldBe` 3
        other ->
            assertFailure
                ("unexpected jobs parse: " <> showParserResult other)
    case parseCommandArguments ["input.tex", "--fresh"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreSelection =
                            Store.FreshTemporaryStore
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected verify parse: " <> showParserResult other)
    case parseCommandArguments ["input.tex", "--refresh"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreSelection =
                            Store.DefaultStore
                        , verificationStoreRefreshRequested = True
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected default refresh parse: "
                    <> showParserResult other)
    case parseCommandArguments
            ["input.tex", "--store", "selected.sqlite", "--refresh"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreSelection =
                            Store.ExplicitStore "selected.sqlite"
                        , verificationStoreRefreshRequested = True
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected explicit refresh parse: "
                    <> showParserResult other)
    case parseCommandArguments ["input.tex", "--fresh", "--refresh"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreSelection =
                            Store.FreshTemporaryStore
                        , verificationStoreRefreshRequested = False
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected fresh refresh parse: "
                    <> showParserResult other)
    case parseCommandArguments ["input.tex", "--store-report"] of
        Success
                (Verify
                    (Input "input.tex")
                    VerificationOptions
                        { verificationStoreReportRequested = True
                        }) ->
            pure ()
        other ->
            assertFailure
                ("unexpected store-report parse: " <> showParserResult other)

normalizesPresentationOptions :: Assertion
normalizesPresentationOptions =
    for_
        [ ([], CheckRenderHints, False)
        , (["--check-render-hints"], CheckRenderHints, False)
        , (["--html"], PublishHtml, True)
        , ( ["--html", "--check-render-hints"]
          , PublishHtml
          , True
          )
        ]
        \(arguments, expectedRequest, expectedHtml) ->
            case parseCommandArguments ("input.tex" : arguments) of
                Success (Verify _input options) -> do
                    verificationPresentationRequest options
                        `shouldBe` expectedRequest
                    verificationHtmlRequested options
                        `shouldBe` expectedHtml
                other ->
                    assertFailure
                        ("unexpected presentation option parse: "
                            <> showParserResult other)

rejectsConflictingOptions :: Assertion
rejectsConflictingOptions = do
    for_
        [ ["input.tex", "--parseonly", "--fresh"]
        , ["input.tex", "--parseonly", "--refresh"]
        , ["input.tex", "--parseonly", "--jobs", "2"]
        , ["input.tex", "--parseonly", "--dump", "dump"]
        , ["input.tex", "--parseonly", "--html"]
        , ["input.tex", "--parseonly", "--check-render-hints"]
        , ["input.tex", "--parseonly", "--store-report"]
        , ["input.tex", "--store", "store.sqlite", "--fresh"]
        ]
        \arguments ->
            case parseCommandArguments arguments of
                Failure _failure ->
                    pure ()
                other ->
                    assertFailure
                        ("conflicting options were accepted: "
                            <> show arguments
                            <> " as "
                            <> showParserResult other)
    case parseCommandArguments ["input.tex", "--jobs", "0"] of
        Failure _failure -> pure ()
        other ->
            assertFailure
                ("non-positive jobs were accepted as "
                    <> showParserResult other)

normalizesConcurrencyOptions :: Assertion
normalizesConcurrencyOptions = do
    for_ [ ([], Nothing, Nothing)
         , (["--jobs", "3"], Just 3, Just 3)
         , (["--module-jobs", "2"], Just 2, Nothing)
         , (["--prover-jobs", "5"], Nothing, Just 5)
         , (["--jobs", "3", "--module-jobs", "2"], Just 2, Just 3)
         , (["--jobs", "3", "--prover-jobs", "5"], Just 3, Just 5)
         ] \(arguments, modules, provers) -> check arguments modules provers
    for_ (List.permutations [["--jobs", "3"], ["--module-jobs", "2"], ["--prover-jobs", "5"]]) \arguments ->
        check (concat arguments) (Just 2) (Just 5)
    for_ ["--module-jobs", "--prover-jobs"] \flag ->
        case parseCommandArguments ["input.tex", "--parseonly", flag, "2"] of
            Failure _ -> pure ()
            other -> assertFailure ("verification-only concurrency accepted: " <> showParserResult other)
  where
    check arguments modules provers =
        case parseCommandArguments ("input.tex" : arguments) of
            Success (Verify _ selected) -> do
                fmap Provers.effectiveJobsValue (verificationModuleJobsOverride selected) `shouldBe` modules
                fmap Provers.effectiveJobsValue (verificationProverJobsOverride selected) `shouldBe` provers
            other -> assertFailure (showParserResult other)

checksNumericOptions :: Assertion
checksNumericOptions =
    for_ options \(flag, lower, upper, value) -> do
        for_ [lower, upper] \expected ->
            case parseCommandArguments ["input.tex", flag, show expected] of
                Success (Verify _ selected) -> value selected `shouldBe` expected
                other -> assertFailure (showParserResult other)
        for_ [show (lower - 1), show (upper + 1), "18446744073709551617",
                replicate 10000 '9'] \raw ->
            case parseCommandArguments ["input.tex", flag <> "=" <> raw] of
                Failure _ -> pure ()
                other -> assertFailure ("invalid " <> flag <> ": " <> showParserResult other)
  where
    options :: [(String, Integer, Integer, VerificationOptions -> Integer)]
    options =
        [ ("--jobs", 1, toInteger (maxBound :: Int),
            maybe (-1) (toInteger . Provers.effectiveJobsValue) . verificationModuleJobsOverride)
        , ("--module-jobs", 1, toInteger (maxBound :: Int),
            maybe (-1) (toInteger . Provers.effectiveJobsValue) . verificationModuleJobsOverride)
        , ("--prover-jobs", 1, toInteger (maxBound :: Int),
            maybe (-1) (toInteger . Provers.effectiveJobsValue) . verificationProverJobsOverride)
        , ("--timelimit", 0, toInteger (maxBound :: Word64),
            \selected -> case verificationTimeLimit selected of Provers.Seconds n -> toInteger n)
        , ("--memlimit", 0, toInteger (maxBound :: Word64),
            \selected -> case verificationMemoryLimit selected of Provers.Megabytes n -> toInteger n)
        ]

invalidNumbersPrecedeStartup :: Assertion
invalidNumbersPrecedeStartup =
    for_ ["--jobs", "--module-jobs", "--prover-jobs", "--timelimit", "--memlimit"] \flag ->
        withCliFixture cliSource \fixture -> do
            let selected = cliFixtureRoot fixture </> "selected.sqlite"
                launched = cliFixtureRoot fixture </> "launched"
            writeFile selected "retained store"
            writeExecutableScript (cliFixtureVampire fixture) ["touch launched", "exit 1"]
            (exitCode, stdout, stderr) <- runCliFixture fixture
                ["input.tex", "--store", "selected.sqlite", "--refresh",
                    flag, "18446744073709551617"]
            exitCode `shouldBe` ExitFailure 1
            stdout `shouldBe` ""
            stderr `shouldContain` "must be"
            ByteString.readFile selected >>= (`shouldBe` "retained store")
            for_ [selected <> ".lock", launched] \path ->
                Directory.doesPathExist path >>= (`shouldBe` False)
            assertNoDefaultStore fixture

showParserResult :: ParserResult Command -> String
showParserResult = \case
    Success selected ->
        show selected
    Failure failure ->
        fst (Options.renderFailure failure "felix")
    CompletionInvoked _completion ->
        "completion invoked"

rendersOperationalReport :: Assertion
rendersOperationalReport = do
    let rendered = Text.unwords (Text.words (renderOperationalReport report))
    for_
        [ "module installations 3 1 0"
        , "proof validations 7 2 0"
        , "declaration validations 1 0 0"
        , "live Vampire runs started: 4"
        , "source graph preparation: 0.500s"
        , "aggregate executor wall: 6.000s"
        , "first-start to last-completion span: 4.000s"
        , "completed-run worker occupancy: 75.0%"
        ] \expected ->
            assertBool ("missing report measurement: " <> Text.unpack expected)
                (expected `Text.isInfixOf` rendered)
  where
    report = Verification.completeVerificationOperationalReport
        (SourceGraph.SourcePlanningMeasurements 500000000 6)
        Verification.CheckOperationalReport
            { Verification.moduleInstallationDecisions =
                Verification.LookupDecisionCounts 3 1 0
            , Verification.proofValidationDecisions =
                Verification.LookupDecisionCounts 7 2 0
            , Verification.declarationValidationDecisions =
                Verification.LookupDecisionCounts 1 0 0
            , Verification.liveVampireRunsStarted = 4
            , Verification.finalPreludeWallNanoseconds = 1000000000
            , Verification.sourceParsingWallNanoseconds = 2000000000
            , Verification.sourceCompletionMeasurements =
                Parse.SourceCompletionMeasurements
                    { Parse.verificationCompletionWorkNanoseconds = 250000000
                    , Parse.presentationOnlyCompletionWorkNanoseconds = 125000000
                    , Parse.verificationCompletionCount = 5
                    , Parse.presentationOnlyCompletionCount = 1
                    }
            , Verification.modulePipelineWorkerLimit = 3
            , Verification.moduleCheckingWallNanoseconds = 3000000000
            , Verification.importPreparationWork = Declaration.ImportWork 1 2 3 4 5 6 7 8 9 10 11 14 15 12 13 16 16 0
            , Verification.vampireExecutionMeasurements =
                Provers.VampireExecutionReport
                    { Provers.vampireExecutionWorkerCount = 2
                    , Provers.vampireExecutionCompletedRuns = 4
                    , Provers.vampireExecutionAggregateNanoseconds = 6000000000
                    , Provers.vampireExecutionLongestNanoseconds = 2000000000
                    , Provers.vampireExecutionActiveSpanNanoseconds = 4000000000
                    , Provers.vampireExecutionMaximumQueueDepth = 3
                    }
            }

versionNeedsNoInputOrStore :: Assertion
versionNeedsNoInputOrStore =
    withCliFixture cliSource \fixture -> do
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["--version"]
        exitCode `shouldBe` ExitSuccess
        stdout `shouldContain` "Version 0.3.0.0"
        stderr `shouldBe` ""
        assertNoDefaultStore fixture

helpDocumentsStoreOptions :: Assertion
helpDocumentsStoreOptions =
    withCliFixture cliSource \fixture -> do
        (exitCode, stdout, stderr) <- runCliFixture fixture ["--help"]
        exitCode `shouldBe` ExitSuccess
        (stdout <> stderr) `shouldContain` "--store-report"
        (stdout <> stderr) `shouldContain` "--refresh"
        (stdout <> stderr) `shouldContain` "--check-render-hints"
        (stdout <> stderr) `shouldContain` "--module-jobs"
        (stdout <> stderr) `shouldContain` "--prover-jobs"
        assertNoDefaultStore fixture

reportsIndependentConcurrency :: Assertion
reportsIndependentConcurrency =
    withCliFixture cliSource \fixture -> do
        writeExecutableScript (cliFixtureVampire fixture)
            ["cat >/dev/null", "printf '%s\\n' '% SZS status Theorem for concurrency'"]
        (exitCode, stdout, stderr) <- runCliFixture fixture
            [ "input.tex", "--store", "selected.sqlite", "--store-report"
            , "--module-jobs", "2", "--prover-jobs", "3", "--jobs", "1"
            ]
        exitCode `shouldBe` ExitSuccess
        stdout `shouldBe` ""
        stderr `shouldContain` "Verification successful."
        stderr `shouldContain` "module pipeline limit: 2"
        stderr `shouldContain` "workers: 3"
        assertNoDefaultStore fixture

parseOnlyUsesNoAuthority :: Assertion
parseOnlyUsesNoAuthority =
    withCliFixture cliPreludeSyntaxSource \fixture -> do
        writeNonExecutableFile (cliFixtureVampire fixture)
        (exitCode, stdout, stderr) <-
            runCliFixture
                fixture
                ["input.tex", "--parseonly"]
        exitCode `shouldBe` ExitSuccess
        stdout `shouldBe` ""
        stderr `shouldBe` ""
        assertNoDefaultStore fixture

malformedSourceHasStableFailure :: Assertion
malformedSourceHasStableFailure =
    withCliFixture malformedCliSource \fixture -> do
        (exitCode, stdout, stderr) <-
            runCliFixture
                fixture
                ["input.tex", "--parseonly"]
        exitCode `shouldBe` ExitFailure 1
        stdout `shouldBe` ""
        stderr `shouldContain` "error[FELIX-PARSE-UNCONSUMED-INPUT]"
        stderr `shouldContain` "input.tex:2:5"
        stderr `shouldContain` "unconsumed word"
        assertBool "does not print an internal error constructor"
            (not ("SourceParseError" `List.isInfixOf` stderr))
        assertNoDefaultStore fixture

invalidFixReportsGoalShape :: Assertion
invalidFixReportsGoalShape = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliInvalidFixSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-EXPECTED-UNIVERSAL]"
    stderr `shouldContain` "actual goal shape: equality"

rejectsOutOfOrderGroupedFix :: Assertion
rejectsOutOfOrderGroupedFix = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliOutOfOrderGroupedFixSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "free variable"

invalidAssumeReportsGoalShape :: Assertion
invalidAssumeReportsGoalShape = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliInvalidAssumeSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-EXPECTED-ASSUMPTIVE-GOAL]"
    stderr `shouldContain` "actual goal shape: equality"

structuredAssumptionMismatchIsSourceLevel :: Assertion
structuredAssumptionMismatchIsSourceLevel = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliStructuredAssumptionMismatchSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-ASSUMPTION-MISMATCH]"
    stderr `shouldContain` "unavailable in the goal frontier"
    assertBool "does not expose checked-core constructors"
        (not ("ScopedCheckedCore" `List.isInfixOf` stderr))

unknownReferenceIsSourceLevel :: Assertion
unknownReferenceIsSourceLevel = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliUnknownReferenceSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-UNKNOWN-REFERENCE]"
    stderr `shouldContain` "unknown proof reference `missing_fact`"

contextualObviousFailureIsSourceLevel :: Assertion
contextualObviousFailureIsSourceLevel = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliObviousFailureSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-OBVIOUS-NO-MATCH]"
    stderr `shouldContain` "obligation: final Follows; method: cited Obvious"
    stderr `shouldContain` "checked goal:"
    stderr `shouldContain` "obvious inference found no local or cited fact whose conclusion matches the goal"
    stderr `shouldContain` "cited facts (showing 1 of 1)"
    stderr `shouldContain` "`cli_obvious_irrelevant`"
    stderr `shouldContain` "2 occurrence(s), 1 spelling(s)"
    stderr `shouldContain` "focused tier: no proof"
    stderr `shouldContain` "refutation tier: no proof"
    stderr `shouldContain` "focused candidate coverage: finished"
    stderr `shouldContain` "best observed focused candidate #1"
    stderr `shouldContain` "view: direct exact"
    stderr `shouldContain` "outcome: comparison rejected"
    stderr `shouldContain` "definition participation: none"
    assertBool "does not expose checked-core constructors"
        (not ("ScopedCheckedCore" `List.isInfixOf` stderr))

distinguishesObviousInvocationSites :: Assertion
distinguishesObviousInvocationSites =
    for_ cases \(source, expected) -> do
        (exitCode, stdout, stderr) <-
            runCliWithSourceAndConfiguredVampire source writeNonExecutableFile
        exitCode `shouldBe` ExitFailure 1
        stdout `shouldBe` ""
        stderr `shouldContain` expected
  where
    cases =
        [ ( cliImplicitObviousFailureSource
          , "obligation: implicit theorem close; method: implicit Obvious"
          )
        , ( cliContradictionObviousFailureSource
          , "obligation: contradiction obligation; method: implicit Obvious"
          )
        , ( cliInlineObviousFailureSource
          , "obligation: inline inference; method: implicit Obvious"
          )
        , ( cliDefinitionObviousFailureSource
          , "obligation: final Follows; method: definition-aware Obvious"
          )
        ]

ambiguousInductionReportsBinders :: Assertion
ambiguousInductionReportsBinders = do
    (exitCode, stdout, stderr) <-
        runCliWithSourceAndConfiguredVampire
            cliAmbiguousInductionSource
            writeNonExecutableFile
    exitCode `shouldBe` ExitFailure 1
    stdout `shouldBe` ""
    stderr `shouldContain` "error[FELIX-PROOF-SET-INDUCTION-AMBIGUOUS]"
    stderr `shouldContain` "eligible binders: `A`, `B`"

invalidOutputPrecedesStoreStartup :: Assertion
invalidOutputPrecedesStoreStartup =
    withCliFixture cliSource \fixture -> do
        let dump = cliFixtureRoot fixture </> "dump"
            selected = cliFixtureRoot fixture </> "selected.sqlite"
        Directory.removeFile
            (cliFixtureRoot fixture </> "input.tex")
        Directory.createDirectory dump
        writeFile (dump </> "stale.p") "stale"
        writeFile selected "retained store"
        (exitCode, stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--store", "selected.sqlite"
                , "--refresh"
                , "--dump", "dump"
                ]
        exitCode `shouldBe` ExitFailure 2
        stdout `shouldBe` ""
        stderr `shouldContain` "Verification output preflight failed:"
        stderr `shouldContain` (Text.pack (show dump))
        stderr `shouldContain` "choose an absent or empty directory"
        stderr `shouldContain` "stale.p"
        retained <- ByteString.readFile selected
        retained `shouldBe` "retained store"
        assertBool "preflight did not acquire the selected store lease"
            . not
            =<< Directory.doesPathExist (selected <> ".lock")
        assertNoDefaultStore fixture

reportsRetainedHtmlStagingTree :: Assertion
reportsRetainedHtmlStagingTree = do
    assertEqual
        "replacement recovery path"
        [ "could not replace HTML snapshot \"/tmp/html\": disk full"
        , "the completed staging snapshot was retained at \"/tmp/html.staging.1\""
        ]
        (HtmlOutput.renderHtmlPublicationError
            (HtmlOutput.HtmlSnapshotReplacementFailed
                "/tmp/html"
                "/tmp/html.staging.1"
                "disk full"))

nestedHtmlRoutesPrecedeStoreStartup :: Assertion
nestedHtmlRoutesPrecedeStoreStartup =
    withCliFixture nestedHtmlRootSource \fixture -> do
        let root = cliFixtureRoot fixture
            nested = root </> "a.html"
        Directory.createDirectory nested
        writeFile (root </> "a.tex") cliSource
        writeFile (nested </> "b.tex") cliSource
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--html"]
        exitCode `shouldBe` ExitFailure 2
        stdout `shouldBe` ""
        stderr `shouldContain` "HTML route planning failed:"
        stderr `shouldContain` "\"a.html\""
        stderr `shouldContain` "\"a.html/b.html\""
        assertNoDefaultStore fixture

removesFailedDumpTemporary :: Assertion
removesFailedDumpTemporary =
    withTemporaryDirectory "felix-dump-atomic" \root -> do
        let destination = root </> "1.p"
        Directory.createDirectory destination
        result <- Exception.try
            (Atomic.writeBytesAtomically
                destination
                (TextEncoding.encodeUtf8 "complete request"))
            :: IO (Either IOException ())
        case result of
            Left _failure ->
                pure ()
            Right () ->
                assertFailure "dump publication unexpectedly succeeded"
        contents <- List.sort <$> Directory.listDirectory root
        assertEqual
            "only the pre-existing final target remains"
            ["1.p"]
            contents

dumpsExactExecutedRequest :: Assertion
dumpsExactExecutedRequest =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        let captured = cliFixtureRoot fixture </> "captured.p"
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat > " <> show captured
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, _stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--dump"
                , "dump"
                ]
        exitCode `shouldBe` ExitSuccess
        stderr `shouldContain` "Verification successful."
        dumped <- ByteString.readFile
            (cliFixtureRoot fixture </> "dump" </> "1-1.p")
        sent <- ByteString.readFile captured
        assertEqual "dump is the exact process input" sent dumped
        assertBool "request is dumped only once"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "dump" </> "1-2.p")

launchFailureDumpsNoRequest :: Assertion
launchFailureDumpsNoRequest =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeNonExecutableFile (cliFixtureVampire fixture)
        (exitCode, _stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--dump"
                , "dump"
                ]
        exitCode `shouldBe` ExitFailure 2
        stderr `shouldContain` "Vampire could not be started"
        assertBool "no request was dumped before process launch"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "dump" </> "1-1.p")

dumpsOnlyExecutedPrefix :: Assertion
dumpsOnlyExecutedPrefix =
    withCliFixture cliTwoSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status CounterSatisfiable for cli'"
            ]
        (exitCode, _stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--dump"
                , "dump"
                ]
        exitCode `shouldBe` ExitFailure 1
        stderr `shouldContain` "error[FELIX-ATP-COUNTERMODEL]"
        assertBool "executed request was dumped"
            =<< Directory.doesFileExist
                (cliFixtureRoot fixture </> "dump" </> "1-1.p")
        -- Prospective execution may start a source-later request before the
        -- admission cursor observes this first rejection.  Dump ownership is
        -- therefore the actual executed subset, not a semantic prefix.

dumpAndHtmlVerifyOnce :: Assertion
dumpAndHtmlVerifyOnce =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        let countPath = cliFixtureRoot fixture </> "vampire-runs"
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' run >> " <> show countPath
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, _stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--dump"
                , "dump"
                , "--html"
                , "--store-report"
                ]
        exitCode `shouldBe` ExitSuccess
        stderr `shouldContain` "Verification successful."
        stderr `shouldContain` "source prefixes scanned: 1"
        runs <- List.lines <$> readFile countPath
        assertEqual "one semantic verification" ["run"] runs
        assertBool "request dump was published"
            =<< Directory.doesFileExist
                (cliFixtureRoot fixture </> "dump" </> "1-1.p")
        assertBool "root HTML page was published"
            =<< Directory.doesFileExist
                (cliFixtureRoot fixture </> "html" </> "input.html")
        assertBool "HTML support asset was published"
            =<< Directory.doesFileExist
                (cliFixtureRoot fixture
                    </> "html"
                    </> "_static"
                    </> "naproche-html.js")

semanticFailurePublishesNoHtml :: Assertion
semanticFailurePublishesNoHtml =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status CounterSatisfiable for cli'"
            ]
        (exitCode, _stdout, stderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--dump"
                , "dump"
                , "--html"
                ]
        exitCode `shouldBe` ExitFailure 1
        stderr `shouldContain` "error[FELIX-ATP-COUNTERMODEL]"
        assertBool "semantic failure retains the executed request dump"
            =<< Directory.doesFileExist
                (cliFixtureRoot fixture </> "dump" </> "1-1.p")
        assertBool "semantic failure publishes no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

freshAndCachedPresentationAgree :: Assertion
freshAndCachedPresentationAgree =
    withCliFixture cliAggregateSource \fixture -> do
        addAggregateRenderHint fixture
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (freshExit, _freshStdout, freshStderr) <-
            runCliFixture fixture ["input.tex", "--html"]
        freshExit `shouldBe` ExitSuccess
        freshStderr `shouldContain` "Verification successful."
        let htmlRoot = cliFixtureRoot fixture </> "html"
            page = htmlRoot </> "input.html"
            support =
                htmlRoot </> "_static" </> "naproche-html.js"
        freshPage <- ByteString.readFile page
        freshSupport <- ByteString.readFile support
        let freshHtml = TextEncoding.decodeUtf8 freshPage
        assertBool
            "checked aggregate exposes semantic schema metadata"
            ("has-schema-tooltip" `Text.isInfixOf` freshHtml)
        assertBool
            "tooltip names the checked exact record schema"
            ( "Exact record for cached presentation structure"
                `Text.isInfixOf` freshHtml
            )
        assertBool
            "tooltip maps canonical carrier order to the named source entry"
            ("carrier ← entry 2" `Text.isInfixOf` freshHtml)
        assertBool
            "tooltip maps the checked local field to the named source entry"
            ( "cachedPresentationPoint ← entry 1"
                `Text.isInfixOf` freshHtml
            )
        assertBool
            "tooltip distinguishes record exactness from structure laws"
            ( "field specifications and laws require the structure predicate"
                `Text.isInfixOf` freshHtml
            )
        Directory.removePathForcibly htmlRoot
        writeNonExecutableFile (cliFixtureVampire fixture)
        (warmExit, _warmStdout, warmStderr) <-
            runCliFixture fixture ["input.tex", "--html"]
        warmExit `shouldBe` ExitSuccess
        warmStderr `shouldContain` "Verification successful."
        warmPage <- ByteString.readFile page
        warmSupport <- ByteString.readFile support
        assertEqual "fresh/cache-hit page bytes" freshPage warmPage
        assertEqual "fresh/cache-hit support bytes"
            freshSupport warmSupport

checksWarmHintEditsWithoutAtp :: Assertion
checksWarmHintEditsWithoutAtp =
    withCliFixture (cliAggregateSource <> unlines
        [ "\\begin{definition}\\label{cached_presentation_adjective}"
        , "    $x$ is \\cachedPresentationClass\\ iff $x=x$."
        , "\\end{definition}"
        , "The phrase \\cachedPresentationClass."
        ]) \fixture -> do
        seedPackagedPreludeCache fixture
        let hintsPath = cliFixtureRoot fixture </> "library" </> "lexicon.tsv"
            callsPath = cliFixtureRoot fixture </> "vampire-calls"
            arguments = ["input.tex", "--store", "verification.sqlite"]
            hint = "\nstructop\tcachedPresentationPoint\t1\tpoint(<x1/>)\n"
            phraseHint = "\nphrase\tcached_presentation_adjective\t0\t<mi>checked-class</mi>\n"
        base <- ByteString.readFile hintsPath
        let original = base <> phraseHint
        ByteString.writeFile hintsPath (original <> hint)
        writeExecutableScript (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' called >> vampire-calls"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (freshExit, _, _) <- runCliFixture fixture arguments
        freshExit `shouldBe` ExitSuccess
        calls <- ByteString.readFile callsPath
        assertBool "the cold fixture actually used ATP" (not (ByteString.null calls))
        writeNonExecutableFile (cliFixtureVampire fixture)
        for_
            [ ("missing", original, ExitFailure 1, "FELIX-HTML-MISSING-RENDER-HINT")
            , ("wrong arity", original <> "\nstructop\tcachedPresentationPoint\t2\tpoint(<x1/>)\n",
                ExitFailure 2, "invalid structop arity 2")
            , ("wrong receiver form", original <> "\nstructop\tcachedPresentationPoint\t0\t<mi>point</mi>\n",
                ExitFailure 1, "FELIX-HTML-MISSING-RENDER-HINT")
            , ("unused phrase operands", original <> hint <> "\nphrase\tunused\t1\t<mi>P</mi>\n",
                ExitFailure 2, "invalid phrase arity 1")
            , ("missing bound phrase", base <> hint, ExitFailure 1, "cached_presentation_adjective")
            , ("command spelling is not the phrase owner",
                base <> hint <> "\nphrase\tcachedPresentationClass\t0\t<mi>wrong-class</mi>\n",
                ExitFailure 1, "cached_presentation_adjective")
            , ("duplicate", original <> hint <> hint, ExitFailure 2, "duplicate structop hint")
            , ("changed valid template", original <> "\nstructop\tcachedPresentationPoint\t1\tp(<x1/>)\n",
                ExitSuccess, "Verification successful.")
            ] \(label, hints, expected, diagnostic) -> do
                ByteString.writeFile hintsPath hints
                (status, _, stderr) <- runCliFixture fixture arguments
                assertEqual label expected status
                stderr `shouldContain` diagnostic
                assertEqual (label <> " starts no new ATP") calls =<< ByteString.readFile callsPath
        assertBool "ordinary hint checks publish no HTML"
            . not =<< Directory.doesPathExist (cliFixtureRoot fixture </> "html")

        ByteString.writeFile hintsPath (base <> hint <> phraseHint)
        (htmlExit, _, _) <- runCliFixture fixture (arguments <> ["--html"])
        htmlExit `shouldBe` ExitSuccess
        page <- readFile (cliFixtureRoot fixture </> "html" </> "input.html")
        page `shouldContain` "<mi>checked-class</mi>"
        assertEqual "warm phrase rendering starts no new ATP" calls =<< ByteString.readFile callsPath

addAggregateRenderHint :: CliFixture -> IO ()
addAggregateRenderHint fixture = appendFile
    (cliFixtureRoot fixture </> "library" </> "lexicon.tsv")
    "\nstructop\tcachedPresentationPoint\t1\tpoint(<x1/>)\n"

renderHintCheckRejectsWithoutHtml :: Assertion
renderHintCheckRejectsWithoutHtml =
    withCliFixture cliAggregateSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex"]
        exitCode `shouldBe` ExitFailure 1
        stdout `shouldBe` ""
        stderr `shouldContain` "error[FELIX-HTML-MISSING-RENDER-HINT]"
        stderr `shouldContain` "structop"
        stderr `shouldContain` "arity 1"
        stderr `shouldContain` "input.tex"
        stderr `shouldContain`
            "Verification rejected because render hints are missing."
        assertBool "check-only mode wrote no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

renderHintCheckSucceedsWithoutHtml :: Assertion
renderHintCheckSucceedsWithoutHtml =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex"]
        exitCode `shouldBe` ExitSuccess
        stdout `shouldBe` ""
        stderr `shouldContain` "Verification successful."
        assertBool "successful check-only mode wrote no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

combinedRenderHintCheckRejectsBeforePublication :: Assertion
combinedRenderHintCheckRejectsBeforePublication =
    withCliFixture cliAggregateSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture
                fixture
                ["input.tex", "--html", "--check-render-hints"]
        exitCode `shouldBe` ExitFailure 1
        stdout `shouldBe` ""
        stderr `shouldContain` "error[FELIX-HTML-MISSING-RENDER-HINT]"
        assertBool "rejected HTML mode publishes no output"
            . not
            =<< Directory.doesPathExist (cliFixtureRoot fixture </> "html")

renderHintCheckRendererFailureIsInfrastructure :: Assertion
renderHintCheckRendererFailureIsInfrastructure =
    withCliFixture cliAggregateSource \fixture -> do
        seedPackagedPreludeCache fixture
        Directory.removeFile
            (cliFixtureRoot fixture </> "library" </> "lexicon.tsv")
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--check-render-hints"]
        exitCode `shouldBe` ExitFailure 2
        stdout `shouldBe` ""
        stderr `shouldContain` "presentation analysis failed:"
        stderr `shouldContain` "renderer data \"lexicon.tsv\" was not found"
        assertBool "analysis failure was not labelled as HTML preparation"
            (not ("HTML preparation failed" `List.isInfixOf` stderr))
        assertBool "analysis failure emitted no missing-hint content error"
            (not ("FELIX-HTML-MISSING-RENDER-HINT" `List.isInfixOf` stderr))
        assertBool "failed check-only analysis wrote no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

missingRendererDataIsTyped :: Assertion
missingRendererDataIsTyped =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        Directory.removeFile
            (cliFixtureRoot fixture </> "library" </> "lexicon.tsv")
        -- Renderer data belongs to the configured library. Ambient files in
        -- the project and debug directories must not mask a broken library.
        writeFile
            (cliFixtureRoot fixture </> "lexicon.tsv")
            "operator\tambient\t0\t<mi>A</mi>\n"
        writeFile
            (cliFixtureRoot fixture </> "debug" </> "lexicon.tsv")
            "operator\tdebug\t0\t<mi>D</mi>\n"
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for cli'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--html"]
        exitCode `shouldBe` ExitFailure 2
        stdout `shouldBe` ""
        stderr `shouldContain` "presentation analysis failed:"
        stderr `shouldContain` "renderer data \"lexicon.tsv\" was not found"
        assertBool "does not expose an ErrorCall"
            (not ("ErrorCall" `List.isInfixOf` stderr))
        assertBool "failed preparation publishes no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

htmlFailureRetainsAuthorizationReport :: Assertion
htmlFailureRetainsAuthorizationReport =
    withCliFixture cliGapSource \fixture -> do
        seedPackagedPreludeCache fixture
        Directory.removeFile
            (cliFixtureRoot fixture </> "library" </> "lexicon.tsv")
        writeNonExecutableFile (cliFixtureVampire fixture)
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--html", "--store-report"]
        exitCode `shouldBe` ExitFailure 2
        stdout `shouldBe` ""
        stderr `shouldContain`
            "Verification succeeded, but presentation analysis failed:"
        stderr `shouldContain`
            "Direct source authorization summary: 0 source axioms, 1 explicit proof gap."
        stderr `shouldContain` "Explicit proof gap at input.tex 5:5"
        stderr `shouldContain` "Store lookup and live execution report"
        assertBool "failed output publishes no HTML"
            . not
            =<< Directory.doesPathExist
                (cliFixtureRoot fixture </> "html")

reportsFreshAndWarmStoreDecisions :: Assertion
reportsFreshAndWarmStoreDecisions =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for store report'"
            ]
        (freshExit, freshStdout, freshStderr) <-
            runCliFixture fixture
                ["input.tex", "--fresh", "--store-report"]
        freshExit `shouldBe` ExitSuccess
        freshStdout `shouldBe` ""
        assertReportRow
            "module installations"
            ["module", "installations", "0", "1", "1"]
            freshStderr
        freshStderr `shouldContain` "source prefixes scanned: 1"

        (firstWarmExit, firstWarmStdout, firstWarmStderr) <-
            runCliFixture fixture ["input.tex", "--store-report"]
        firstWarmExit `shouldBe` ExitSuccess
        firstWarmStdout `shouldBe` ""
        assertReportRow
            "module installations"
            ["module", "installations", "1", "1", "0"]
            firstWarmStderr
        firstWarmStderr `shouldContain` "live Vampire runs started: 1"

        (cachedExit, cachedStdout, cachedStderr) <-
            runCliFixture fixture ["input.tex", "--store-report"]
        cachedExit `shouldBe` ExitSuccess
        cachedStdout `shouldBe` ""
        assertReportRow
            "module installations"
            ["module", "installations", "2", "0", "0"]
            cachedStderr
        assertReportRow
            "proof validations"
            ["proof", "validations", "0", "0", "0"]
            cachedStderr
        assertReportRow
            "declaration validations"
            ["declaration", "validations", "0", "0", "0"]
            cachedStderr
        cachedStderr `shouldContain` "live Vampire runs started: 0"

        writeFile
            (cliFixtureRoot fixture </> "input.tex")
            ("% shifted source location\n" <> cliSource)
        writeNonExecutableFile (cliFixtureVampire fixture)
        (formattedExit, formattedStdout, formattedStderr) <-
            runCliFixture fixture ["input.tex", "--store-report", "--jobs", "1"]
        formattedExit `shouldBe` ExitSuccess
        formattedStdout `shouldBe` ""
        assertReportRow
            "module installations"
            ["module", "installations", "1", "1", "0"]
            formattedStderr
        assertReportRow
            "proof validations"
            ["proof", "validations", "1", "0", "0"]
            formattedStderr
        formattedStderr `shouldContain` "live Vampire runs started: 0"

refreshesOnlyExplicitStore :: Assertion
refreshesOnlyExplicitStore =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        let defaultStore =
                cliFixtureCacheRoot fixture
                    </> "felix"
                    </> "store.sqlite"
            selectedStore =
                cliFixtureRoot fixture </> "selected.sqlite"
        defaultBefore <- ByteString.readFile defaultStore
        oldStore <- SQLite.open selectedStore
        SQLite.execute_ oldStore
            "CREATE TABLE old_store (value INTEGER)"
        SQLite.close oldStore

        (incompatibleExit, incompatibleStdout, incompatibleStderr) <-
            runCliFixture fixture
                ["input.tex", "--store", "selected.sqlite"]
        incompatibleExit `shouldBe` ExitFailure 2
        incompatibleStdout `shouldBe` ""
        incompatibleStderr `shouldContain` "is incompatible"
        incompatibleStderr `shouldContain` "--refresh"

        (refreshedExit, refreshedStdout, refreshedStderr) <-
            runCliFixture fixture
                [ "input.tex"
                , "--store", "selected.sqlite"
                , "--refresh"
                ]
        refreshedExit `shouldBe` ExitSuccess
        refreshedStdout `shouldBe` ""
        refreshedStderr `shouldContain` "Verification successful."
        assertBool "successful refresh has no separate message"
            (not ("refresh" `List.isInfixOf` refreshedStderr))

        defaultAfter <- ByteString.readFile defaultStore
        assertEqual "explicit refresh leaves the default store unchanged"
            defaultBefore defaultAfter

refreshIsSilentWithoutStore :: Assertion
refreshIsSilentWithoutStore =
    withCliFixture cliSource \fixture -> do
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status Theorem for refresh'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--refresh"]
        exitCode `shouldBe` ExitSuccess
        stdout `shouldBe` ""
        stderr `shouldContain` "Verification successful."
        assertBool "missing-store refresh is silent"
            (not ("refresh" `List.isInfixOf` stderr))

failedVerificationRetainsStoreReport :: Assertion
failedVerificationRetainsStoreReport =
    withCliFixture cliSource \fixture -> do
        seedPackagedPreludeCache fixture
        writeExecutableScript
            (cliFixtureVampire fixture)
            [ "cat >/dev/null"
            , "printf '%s\\n' '% SZS status CounterSatisfiable for report'"
            ]
        (exitCode, stdout, stderr) <-
            runCliFixture fixture ["input.tex", "--store-report"]
        exitCode `shouldBe` ExitFailure 1
        stdout `shouldBe` ""
        stderr `shouldContain` "error[FELIX-ATP-COUNTERMODEL]"
        stderr `shouldContain` "Store lookup and live execution report"
        stderr `shouldContain` "live Vampire runs started: 1"
        assertReportRow
            "proof validations"
            ["proof", "validations", "0", "1", "0"]
            stderr
        firstObligation <- requireOutputLine "obligation id:" stderr

        (secondExitCode, secondStdout, secondStderr) <-
            runCliFixture fixture ["input.tex", "--store-report"]
        secondExitCode `shouldBe` ExitFailure 1
        secondStdout `shouldBe` ""
        assertReportRow
            "proof validations"
            ["proof", "validations", "0", "1", "0"]
            secondStderr
        secondStderr `shouldContain` "live Vampire runs started: 1"
        secondObligation <- requireOutputLine "obligation id:" secondStderr
        secondObligation `shouldBe` firstObligation

assertReportRow :: String -> [String] -> String -> Assertion
assertReportRow label expected output = do
    row <- requireOutputLine label output
    List.words row `shouldBe` expected

requireOutputLine :: String -> String -> IO String
requireOutputLine label output =
    case List.find (List.isInfixOf label) (List.lines output) of
        Nothing ->
            assertFailure
                ("missing output line " <> show label <> " in " <> output)
                >> fail "unreachable"
        Just row ->
            pure row

outcomeCases :: [(CommandOutcome, ExitCode)]
outcomeCases =
    [ (CommandCompleted, ExitSuccess)
    , (VerificationSucceeded emptyReport Nothing emptySlowReport, ExitSuccess)
    , ( VerificationCompletedWithGaps emptyReport Nothing emptySlowReport
      , ExitSuccess
      )
    , ( VerificationCheckingRejected
            emptyReport
            (Verification.VerificationModuleSchedulerInvariant "test")
            Nothing
            emptySlowReport
      , ExitFailure 2
      )
    , ( VerifiedOutputFailed
            emptyReport
            VerifiedHtmlLayoutUnavailable
            Nothing
            emptySlowReport
      , ExitFailure 2
      )
    ]

emptyReport :: Verification.VerificationReport
emptyReport =
    Verification.VerificationReport
        { Verification.verificationDirectEscapes = []
        }

emptySlowReport :: Provers.SlowAtpReport
emptySlowReport = Provers.SlowAtpReport 0 []

runCliWithFakeVampire
    :: [String]
    -> IO (ExitCode, String, String)
runCliWithFakeVampire scriptLines =
    runCliWithConfiguredVampire \vampirePath -> do
        writeExecutableScript vampirePath
            (["cat >/dev/null"] <> scriptLines)

runCliWithConfiguredVampire
    :: (FilePath -> IO ())
    -> IO (ExitCode, String, String)
runCliWithConfiguredVampire =
    runCliWithSourceAndConfiguredVampire cliSource

runCliWithSourceAndConfiguredVampire
    :: String
    -> (FilePath -> IO ())
    -> IO (ExitCode, String, String)
runCliWithSourceAndConfiguredVampire source prepareVampire =
    withCliFixture source \fixture -> do
        seedPackagedPreludeCache fixture
        prepareVampire (cliFixtureVampire fixture)
        runCliFixture fixture ["input.tex"]

data CliFixture = CliFixture
    { cliFixtureRoot :: !FilePath
    , cliFixtureExecutable :: !FilePath
    , cliFixtureVampire :: !FilePath
    , cliFixtureCacheRoot :: !FilePath
    , cliFixtureEnvironment :: ![(String, String)]
    }

withCliFixture
    :: String
    -> (CliFixture -> IO value)
    -> IO value
withCliFixture source action =
    withTemporaryDirectory "felix-cli" \temp -> do
        felixExecutable <- requireFelixExecutable
        repositoryRoot <- Directory.getCurrentDirectory
        let sourcePath = temp </> "input.tex"
            vampirePath = temp </> "vampire"
            libraryPath = temp </> "library"
            debugPath = temp </> "debug"
            cacheRoot = temp </> "cache"
        Directory.createDirectory libraryPath
        Directory.createDirectory debugPath
        Directory.createDirectory cacheRoot
        writeFile sourcePath source
        ByteString.readFile
            (repositoryRoot </> "library" </> "lexicon.tsv")
            >>= ByteString.writeFile
                (libraryPath </> "lexicon.tsv")
        inheritedEnvironment <- getEnvironment
        let processEnvironment =
                setEnvironmentVariable
                    "XDG_CACHE_HOME"
                    cacheRoot
                    (setEnvironmentVariable
                        "FELIX_VAMPIRE"
                        vampirePath
                        (setEnvironmentVariable
                            "NAPROCHE_LIB"
                            libraryPath
                            inheritedEnvironment))
        action
            CliFixture
                { cliFixtureRoot = temp
                , cliFixtureExecutable = felixExecutable
                , cliFixtureVampire = vampirePath
                , cliFixtureCacheRoot = cacheRoot
                , cliFixtureEnvironment = processEnvironment
                }

runCliFixture
    :: CliFixture
    -> [String]
    -> IO (ExitCode, String, String)
runCliFixture fixture arguments =
    readCreateProcessWithExitCode
        ((proc
            (cliFixtureExecutable fixture)
            arguments)
            { cwd = Just (cliFixtureRoot fixture)
            -- The production executable defaults to one capability per CPU.
            -- Process-boundary tests are deliberately serial and must remain
            -- viable on high-core hosts under a bounded-memory test run.
            , env = Just
                (setEnvironmentVariable
                    "GHCRTS"
                    "-N1"
                    (cliFixtureEnvironment fixture))
            })
        ""

-- | Populate only the packaged final-prelude root.  Process-boundary tests
-- can then exercise the requested ordinary module outcome without making
-- their fake prover depend on the prelude's private obligation count.
seedPackagedPreludeCache :: CliFixture -> Assertion
seedPackagedPreludeCache fixture = do
    let sourcePath = cliFixtureRoot fixture </> "input.tex"
    original <- ByteString.readFile sourcePath
    writeExecutableScript
        (cliFixtureVampire fixture)
        [ "cat >/dev/null"
        , "printf '%s\\n' '% SZS status Theorem for prelude seed'"
        ]
    (exitCode, stdout, stderr) <-
        (do
            writeFile sourcePath "% cache the packaged prelude\n"
            runCliFixture fixture ["input.tex"])
        `Exception.finally` ByteString.writeFile sourcePath original
    exitCode `shouldBe` ExitSuccess
    stdout `shouldBe` ""
    stderr `shouldContain` "Verification successful."

assertNoDefaultStore :: CliFixture -> Assertion
assertNoDefaultStore fixture =
    assertBool "default store was not created"
        . not
        =<< Directory.doesPathExist
            (cliFixtureCacheRoot fixture </> "felix")

writeExecutableScript :: FilePath -> [String] -> IO ()
writeExecutableScript path scriptLines = do
    writeFile path
        (unlines (["#!/bin/sh"] <> scriptLines))
    permissions <- Directory.getPermissions path
    Directory.setPermissions path
        (Directory.setOwnerExecutable True permissions)

writeNonExecutableFile :: FilePath -> IO ()
writeNonExecutableFile path = do
    exists <- Directory.doesPathExist path
    if exists
        then Directory.removeFile path
        else pure ()
    writeFile path "not executable"

requireFelixExecutable :: IO FilePath
requireFelixExecutable = do
    executable <- Directory.findExecutable "felix"
    case executable of
        Just path ->
            pure path
        Nothing ->
            assertFailure "felix build tool is not available on PATH"
                >> pure "felix"

setEnvironmentVariable
    :: String
    -> String
    -> [(String, String)]
    -> [(String, String)]
setEnvironmentVariable name value environment =
    (name, value) : List.filter ((/= name) . fst) environment

cliSource :: String
cliSource =
    unlines
        [ "\\begin{proposition}\\label{cli_test}"
        , "    $\\forall x. x = x$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\auto."
        , "\\end{proof}"
        ]

cliAggregateSource :: String
cliAggregateSource =
    unlines
        [ "\\begin{struct}\\label{cached_presentation_structure}"
        , "    A cached presentation structure $X$ is a onesorted structure equipped with"
        , "    \\begin{enumerate}"
        , "        \\item\\label{cached_presentation_point}"
        , "            a point $\\cachedPresentationPoint[X]\\in\\carrier[X]$;"
        , "    \\end{enumerate}"
        , "    ."
        , "\\end{struct}"
        , ""
        , "\\begin{proposition}\\label{cached_presentation_aggregate}"
        , "    Suppose $x\\in A$."
        , "    Then $\\structure{"
        , "        \\cachedPresentationPoint=x,"
        , "        \\carrier=A"
        , "    }$ is a cached presentation structure."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\auto."
        , "\\end{proof}"
        , ""
        , "\\begin{proposition}\\label{cached_presentation_projection}"
        , "    Suppose $X$ is a cached presentation structure."
        , "    Then $\\cachedPresentationPoint[X]=\\cachedPresentationPoint[X]$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows."
        , "\\end{proof}"
        ]

cliPreludeSyntaxSource :: String
cliPreludeSyntaxSource =
    unlines
        [ "\\begin{proposition}\\label{parse_prelude_syntax}"
        , "    For all $x$ we have $\\suc{x} = \\suc{x}$."
        , "\\end{proposition}"
        ]

cliGapSource :: String
cliGapSource =
    unlines
        [ "\\begin{proposition}\\label{cli_gap}"
        , "    $\\forall x. x = x$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Omitted."
        , "\\end{proof}"
        ]

cliTwoSource :: String
cliTwoSource =
    unlines
        [ "\\begin{proposition}\\label{cli_first}"
        , "    $\\forall x. x = x$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\auto."
        , "\\end{proof}"
        , "\\begin{proposition}\\label{cli_second}"
        , "    $\\forall y. y = y$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\auto."
        , "\\end{proof}"
        ]

malformedCliSource :: String
malformedCliSource =
    unlines
        [ "\\begin{proposition}\\label{malformed}"
        , "    This is not a proposition."
        , "\\end{proposition}"
        ]

cliInvalidFixSource :: String
cliInvalidFixSource =
    unlines
        [ "\\begin{proposition}\\label{cli_invalid_fix}"
        , "    Let $A$ be a set."
        , "    $A=A$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Fix $x\\in A$."
        , "    Follows."
        , "\\end{proof}"
        ]

cliOutOfOrderGroupedFixSource :: String
cliOutOfOrderGroupedFixSource =
    unlines
        [ "\\begin{proposition}\\label{cli_out_of_order_grouped_fix}"
        , "    $\\forall x. \\forall A. x\\in A \\implies x\\in A$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Fix $x,A\\in A$."
        , "    Follows."
        , "\\end{proof}"
        ]

cliInvalidAssumeSource :: String
cliInvalidAssumeSource =
    unlines
        [ "\\begin{proposition}\\label{cli_invalid_assume}"
        , "    Let $A$ be a set."
        , "    $A=A$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Assume $A=A$."
        , "    Follows."
        , "\\end{proof}"
        ]

cliStructuredAssumptionMismatchSource :: String
cliStructuredAssumptionMismatchSource =
    unlines
        [ "\\begin{proposition}\\label{cli_structured_assumption_mismatch}"
        , "    Let $A$ be a set."
        , "    $A=A \\implies A\\neq A$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Assume $A\\neq A$."
        , "    Follows."
        , "\\end{proof}"
        ]

cliUnknownReferenceSource :: String
cliUnknownReferenceSource =
    unlines
        [ "\\begin{proposition}\\label{cli_unknown_reference}"
        , "    Let $A$ be a set."
        , "    $A=A$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\auto{missing_fact}."
        , "\\end{proof}"
        ]

cliObviousFailureSource :: String
cliObviousFailureSource =
    unlines
        [ "\\begin{axiom}\\label{cli_obvious_irrelevant}"
        , "    $\\emptyset = \\emptyset$."
        , "\\end{axiom}"
        , ""
        , "\\begin{proposition}\\label{cli_obvious_failure}"
        , "    $\\emptyset \\in \\emptyset$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by \\obv{cli_obvious_irrelevant,cli_obvious_irrelevant}."
        , "\\end{proof}"
        ]

cliImplicitObviousFailureSource :: String
cliImplicitObviousFailureSource =
    unlines
        [ "\\begin{proposition}\\label{cli_implicit_obvious_failure}"
        , "    $\\emptyset \\in \\emptyset$."
        , "\\end{proposition}"
        ]

cliContradictionObviousFailureSource :: String
cliContradictionObviousFailureSource =
    unlines
        [ "\\begin{proposition}\\label{cli_contradiction_obvious_failure}"
        , "    $\\emptyset = \\emptyset$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Contradiction."
        , "\\end{proof}"
        ]

cliInlineObviousFailureSource :: String
cliInlineObviousFailureSource =
    unlines
        [ "\\begin{proposition}\\label{cli_inline_obvious_failure}"
        , "    $\\emptyset = \\emptyset$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    We have $\\emptyset \\in \\emptyset$."
        , "    Follows."
        , "\\end{proof}"
        ]

cliDefinitionObviousFailureSource :: String
cliDefinitionObviousFailureSource =
    unlines
        [ "\\begin{proposition}\\label{cli_definition_obvious_failure}"
        , "    $\\emptyset \\in \\emptyset$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "    Follows by definition."
        , "\\end{proof}"
        ]

cliAmbiguousInductionSource :: String
cliAmbiguousInductionSource =
    unlines
        [ "\\begin{proposition}\\label{cli_ambiguous_induction}"
        , "    Let $A,B$ be sets."
        , "    Then $A=A$."
        , "\\end{proposition}"
        , "\\begin{proof}[Proof by \\in-induction]"
        , "    Follows."
        , "\\end{proof}"
        ]

nestedHtmlRootSource :: String
nestedHtmlRootSource =
    unlines
        [ "\\import{a.tex}"
        , "\\import{a.html/b.tex}"
        ]

shouldContain :: String -> Text -> Assertion
shouldContain actual expected =
    assertBool
        ("expected " <> show actual <> " to contain " <> show expected)
        (expected `Text.isInfixOf` Text.pack actual)

shouldBe :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
shouldBe =
    flip (assertEqual "")
