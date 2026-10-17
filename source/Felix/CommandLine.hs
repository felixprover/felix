{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.CommandLine
    ( runCommandLine
    , Input(..)
    , PresentationRequest(..)
    , VerificationOptions(..)
    , verificationHtmlRequested
    , Command(..)
    , CommandOutcome(..)
    , VerifiedOutputFailure(..)
    , parseCommandArguments
    , verificationCommandOutcome
    , commandOutcomeExitCode
    , renderCommandOutcome
    , renderOperationalReport
    ) where

import Base
import Felix.Checking.Declaration qualified as Declaration
import Felix.OutputPlan qualified as Output
import Felix.Parse (ParseWorkspaceError)
import Felix.Parse qualified as Parse
import Felix.Provers qualified as Provers
import Felix.RequestDump qualified as RequestDump
import Felix.Source (SafeRelativePath)
import Felix.Source.Graph qualified as SourceGraph
import Felix.Store qualified as Store
import Felix.Text.BoundedInteger (readBoundedIntegral)
import Felix.Verification qualified as Verification
import Felix.Version qualified as Version
import Felix.Workspace qualified as Workspace
import Felix.Render.Html qualified as Html
import Felix.Render.Html.Export qualified as HtmlExport
import Felix.Render.Html.Layout qualified as HtmlLayout
import Felix.Render.Html.Output qualified as HtmlOutput
import Felix.Report.Location
import Felix.Report.Diagnostic (Diagnostic, DiagnosticSeverity(..))
import Felix.Report.Render.Terminal qualified as Terminal

import Control.Monad (unless, when)
import Data.Maybe (catMaybes)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as StrictText
import Data.Text.IO qualified as Text
import GHC.Conc qualified
import Numeric (showFFloat)
import Options.Applicative hiding (renderFailure)
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode(..), exitWith)
import System.IO (stderr)


newtype Input = Input
    { inputFilePath :: FilePath
    }
    deriving stock (Show, Eq)

data VerificationOptions = VerificationOptions
    { verificationStoreSelection :: !Store.StoreSelection
    , verificationStoreRefreshRequested :: !Bool
    , verificationTimeLimit :: !Provers.TimeLimit
    , verificationMemoryLimit :: !Provers.MemoryLimit
    , verificationModuleJobsOverride :: !(Maybe Provers.EffectiveJobs)
    , verificationProverJobsOverride :: !(Maybe Provers.EffectiveJobs)
    , verificationDumpDestination :: !(Maybe FilePath)
    , verificationPresentationRequest :: !PresentationRequest
    , verificationStoreReportRequested :: !Bool
    }
    deriving stock (Show, Eq)

data PresentationRequest
    = CheckRenderHints
    | PublishHtml
    deriving stock (Show, Eq)

verificationHtmlRequested :: VerificationOptions -> Bool
verificationHtmlRequested options =
    case verificationPresentationRequest options of
        PublishHtml -> True
        CheckRenderHints -> False

data Command
    = Version
    | ParseOnly !Input
    | Verify !Input !VerificationOptions
    deriving stock (Show, Eq)

data CommandOutcome
    = CommandCompleted
    | VerificationSucceeded
        !Verification.VerificationReport
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    | VerificationCompletedWithGaps
        !Verification.VerificationReport
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    | VerificationRejected
        !Verification.VerificationReport
        !Verification.FailedVerification
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    | VerificationCheckingRejected
        !Verification.VerificationReport
        !Verification.VerificationDriverError
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    | VerificationRenderHintsRejected
        !Verification.VerificationReport
        !(NonEmpty Html.MissingRenderHint)
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    | SourcePlanningFailed !ParseWorkspaceError
    | ParseOnlyFailed !Workspace.AuthorityFreeParseError
    | VerificationDriverFailed !Verification.VerificationDriverError
    | VerificationSessionFailed
        !Store.StorePath
        !Verification.VerificationSessionError
    | StorePlanningFailed !Store.StorePlanningError
    | StoreLeaseFailed !Store.StoreLeaseError
    | StoreIncompatible !Store.StorePath !Store.StoreIncompatibility
    | StoreFailed !Store.StorePath !Store.StoreLifecycleError
    | OutputPlanningFailed !Output.OutputPlanError
    | HtmlLayoutFailed !HtmlLayout.HtmlLayoutError
    | DumpObservationFailed !RequestDump.DumpObservationError
    | VerifiedOutputFailed
        !Verification.VerificationReport
        !VerifiedOutputFailure
        !(Maybe Verification.VerificationOperationalReport)
        !Provers.SlowAtpReport
    deriving stock (Show)

data VerifiedOutputFailure
    = VerifiedPresentationAnalysisFailed
        !HtmlExport.PresentationAnalysisError
    | VerifiedHtmlArtefactFailed !HtmlExport.HtmlArtefactError
    | VerifiedHtmlOutputPlanningFailed !HtmlOutput.HtmlOutputError
    | VerifiedHtmlPublicationFailed !HtmlOutput.HtmlPublicationError
    | VerifiedHtmlLayoutUnavailable
    deriving stock (Show)

data PresentationPreflight = PresentationPreflight
    !Workspace.WorkspaceEnvironment
    !SourceGraph.SourceGraphPreparation
    !(Maybe (HtmlLayout.HtmlLayout, [SafeRelativePath]))


runCommandLine :: IO ()
runCommandLine = do
    arguments <- getArgs
    selected <- handleParseResult (parseCommandArguments arguments)
    outcome <- runCommand selected
    renderCommandOutcome outcome
    exitWith (commandOutcomeExitCode outcome)

rawCommandParserInfo :: ParserInfo RawCommand
rawCommandParserInfo =
    info
        (helper <*> rawCommandParser)
        (fullDesc <> header "Felix")

runCommand :: Command -> IO CommandOutcome
runCommand = \case
    Version -> do
        Text.putStrLn Version.info
        pure CommandCompleted
    ParseOnly (Input input) ->
        Workspace.parseWorkspace input >>= \case
            Left failure ->
                pure (ParseOnlyFailed failure)
            Right _blocks ->
                pure CommandCompleted
    Verify input options ->
        runVerification input options

runVerification
    :: Input
    -> VerificationOptions
    -> IO CommandOutcome
runVerification input options = do
    plannedStore <-
        Store.planStore
            (verificationStoreSelection options)
    case plannedStore of
        Left failure ->
            pure (StorePlanningFailed failure)
        Right storePlan
            | Just storePath <- Store.storePlanPersistentPath storePlan
            , verificationPresentationRequest options == CheckRenderHints -> do
                -- Dump/store namespaces do not depend on the source graph.
                -- Preserve their preflight before reading source or taking a lease.
                outputResult <- planOutputs storePath options Nothing
                case outputResult of
                    Left failure -> pure (OutputPlanningFailed failure)
                    Right outputPlan -> discoverPresentationPreflight input options >>= \case
                        Left failure -> pure failure
                        Right preflight -> acquireStoreAndOpen options storePlan outputPlan preflight
        Right storePlan -> do
            presentationResult <- discoverPresentationPreflight input options
            case presentationResult of
                Left failure ->
                    pure failure
                Right presentationPreflight@(PresentationPreflight _ _ html) ->
                    case Store.storePlanPersistentPath storePlan of
                        Just storePath -> do
                            outputResult <- planOutputs
                                storePath options html
                            case outputResult of
                                Left failure ->
                                    pure (OutputPlanningFailed failure)
                                Right outputPlan ->
                                    acquireStoreAndOpen
                                        options storePlan outputPlan
                                        presentationPreflight
                        Nothing -> do
                            leased <- Store.withStoreLease storePlan \lease -> do
                                outputResult <- planOutputs
                                    (Store.storeLeasePath lease)
                                    options
                                    html
                                case outputResult of
                                    Left failure ->
                                        pure (OutputPlanningFailed failure)
                                    Right outputPlan ->
                                        refreshAndOpenVerificationSession
                                            options
                                            lease
                                            outputPlan
                                            presentationPreflight
                            pure (either StoreLeaseFailed id leased)

planOutputs
    :: Store.StorePath
    -> VerificationOptions
    -> Maybe (HtmlLayout.HtmlLayout, [SafeRelativePath])
    -> IO (Either Output.OutputPlanError Output.VerificationOutputPlan)
planOutputs storePath options html =
    Output.planVerificationOutputs
        storePath
        (verificationStoreRefreshRequested options)
        (verificationDumpDestination options)
        ((\(_layout, destinations) -> ("html", destinations)) <$> html)


acquireStoreAndOpen
    :: VerificationOptions
    -> Store.StorePlan
    -> Output.VerificationOutputPlan
    -> PresentationPreflight
    -> IO CommandOutcome
acquireStoreAndOpen options storePlan outputPlan presentationPreflight = do
    leased <- Store.withStoreLease storePlan \lease ->
        refreshAndOpenVerificationSession
            options
            lease
            outputPlan
            presentationPreflight
    pure (either StoreLeaseFailed id leased)

refreshAndOpenVerificationSession
    :: VerificationOptions
    -> Store.StoreLease
    -> Output.VerificationOutputPlan
    -> PresentationPreflight
    -> IO CommandOutcome
refreshAndOpenVerificationSession
        options lease outputPlan presentationPreflight
    | not (verificationStoreRefreshRequested options) =
        openVerificationSession
            options lease outputPlan presentationPreflight
    | otherwise =
        Store.refreshStore lease >>= \case
            Left failure ->
                pure (StoreFailed (Store.storeLeasePath lease) failure)
            Right () ->
                openVerificationSession
                    options lease outputPlan presentationPreflight

discoverPresentationPreflight
    :: Input
    -> VerificationOptions
    -> IO (Either CommandOutcome PresentationPreflight)
discoverPresentationPreflight input options = do
    prepared <- prepareInputSourceGraph input
    pure case prepared of
        Left failure -> Left (SourcePlanningFailed failure)
        Right (environment, preparation) -> case verificationPresentationRequest options of
            CheckRenderHints -> Right (PresentationPreflight environment preparation Nothing)
            PublishHtml ->
                case planHtmlDestinations environment (SourceGraph.sourceGraphPreparationGraph preparation) of
                    Left failure -> Left (HtmlLayoutFailed failure)
                    Right html -> Right (PresentationPreflight environment preparation (Just html))

planHtmlDestinations
    :: Workspace.WorkspaceEnvironment
    -> SourceGraph.ResolvedSourceGraph
    -> Either
        HtmlLayout.HtmlLayoutError
        (HtmlLayout.HtmlLayout, [SafeRelativePath])
planHtmlDestinations environment graph = do
    layout <-
        HtmlLayout.layoutHtmlSourceGraph
            (Workspace.workspaceHtmlMountPrefixes environment)
            graph
    pure
        ( layout
        , HtmlLayout.htmlLayoutDestinations layout
        )

prepareInputSourceGraph
    :: Input
    -> IO
        (Either
            ParseWorkspaceError
            ( Workspace.WorkspaceEnvironment
            , SourceGraph.SourceGraphPreparation
            ))
prepareInputSourceGraph input = do
    preparedEnvironment <- Workspace.prepareDefaultWorkspaceEnvironment
    case preparedEnvironment of
        Left failure -> pure (Left failure)
        Right environment -> do
            preparedRoot <- Workspace.prepareWorkspaceRoot
                environment
                (inputFilePath input)
            case preparedRoot of
                Left failure -> pure (Left failure)
                Right root ->
                    fmap (fmap (\preparation -> (environment, preparation)))
                        (Workspace.prepareSourceGraphMeasured environment root)

openVerificationSession
    :: VerificationOptions
    -> Store.StoreLease
    -> Output.VerificationOutputPlan
    -> PresentationPreflight
    -> IO CommandOutcome
openVerificationSession options lease outputPlan presentationPreflight = do
    opened <- Verification.withVerificationSession lease
        (\session ->
            runOpenVerification
                options
                outputPlan
                presentationPreflight
                session)
    pure case opened of
        Left
            (Verification.VerificationSessionStoreError
                (Store.StoreLifecycleOpenFailed
                    (Store.IncompatibleStore incompatibility))) ->
                        StoreIncompatible
                            (Store.storeLeasePath lease)
                            incompatibility
        Left (Verification.VerificationSessionStoreError failure) ->
            StoreFailed (Store.storeLeasePath lease) failure
        Left failure ->
            VerificationSessionFailed (Store.storeLeasePath lease) failure
        Right outcome -> outcome

runOpenVerification
    :: VerificationOptions
    -> Output.VerificationOutputPlan
    -> PresentationPreflight
    -> Verification.VerificationSession
    -> IO CommandOutcome
runOpenVerification options outputPlan
        presentationPreflight@(PresentationPreflight _environment preparation _html) session = do
    observerResult <-
        RequestDump.prepareRequestObserver
            (Output.verificationDumpOutput outputPlan)
    case observerResult of
        Left failure -> pure (DumpObservationFailed failure)
        Right observer -> do
            let graph =
                    SourceGraph.sourceGraphPreparationGraph preparation
            vampirePath <- getVampireExecutable
            (moduleJobs, proverJobs) <-
                case (verificationModuleJobsOverride options, verificationProverJobsOverride options) of
                    (Just modules, Just provers) -> pure (modules, provers)
                    (modules, provers) -> do
                        (automaticModules, automaticProvers) <-
                            Provers.selectAutomaticJobs GHC.Conc.getNumProcessors
                        pure (fromMaybe automaticModules modules, fromMaybe automaticProvers provers)
            let vampire =
                    Provers.vampire
                        vampirePath
                        (verificationTimeLimit options)
                        (verificationMemoryLimit options)
                validationMode =
                    case verificationStoreSelection options of
                        Store.FreshTemporaryStore ->
                            Verification.FreshStoreValidation
                        Store.DefaultStore ->
                            Verification.WarmStoreValidation
                        Store.ExplicitStore{} ->
                            Verification.WarmStoreValidation
                request = Verification.CheckRequest
                    { Verification.checkSourceGraph = graph
                    , Verification.checkPresentationDemand =
                        Parse.HtmlPresentationRequested
                    , Verification.checkStoreValidationMode =
                        validationMode
                    , Verification.checkModuleJobs = moduleJobs
                    , Verification.checkProverJobs = proverJobs
                    , Verification.checkVampire = vampire
                    , Verification.checkRequestObserver = observer
                    }
            observed <- RequestDump.captureDumpFailure
                (Verification.checkWorkspace session request)
            case observed of
                Left failure -> pure (DumpObservationFailed failure)
                Right (Left failure) ->
                    pure (VerificationDriverFailed failure)
                Right (Right outcome) ->
                    let operationalReport =
                            Verification.completeVerificationOperationalReport
                                (SourceGraph.sourceGraphPreparationMeasurements
                                    preparation)
                                (Verification.checkOperationalReport outcome)
                    in
                    finishVerification
                        (verificationStoreReportRequested options)
                        outputPlan
                        presentationPreflight
                        operationalReport
                        outcome

finishVerification
    :: Bool
    -> Output.VerificationOutputPlan
    -> PresentationPreflight
    -> Verification.VerificationOperationalReport
    -> Verification.CheckOutcome
    -> IO CommandOutcome
finishVerification
        reportRequested outputPlan presentationPreflight completedReport outcome =
    case result of
        Verification.VerificationFailure{} ->
            pure (verificationCommandOutcome result operationalReport slowReport)
        Verification.VerificationCheckingFailure{} ->
            pure (verificationCommandOutcome result operationalReport slowReport)
        Verification.VerificationCompleted report presentation ->
            finalizePresentation
                outputPlan
                presentationPreflight
                report
                presentation
                (VerificationSucceeded report operationalReport slowReport)
                operationalReport
                slowReport
        Verification.CompletedWithExplicitGaps report presentation ->
            finalizePresentation
                outputPlan
                presentationPreflight
                report
                presentation
                (VerificationCompletedWithGaps
                    report operationalReport slowReport)
                operationalReport
                slowReport
  where
    result = Verification.checkVerificationResult outcome
    slowReport = Verification.checkSlowAtpReport outcome
    operationalReport =
        if reportRequested
            then Just completedReport
            else Nothing

finalizePresentation
    :: Output.VerificationOutputPlan
    -> PresentationPreflight
    -> Verification.VerificationReport
    -> Verification.PresentationDisposition
    -> CommandOutcome
    -> Maybe Verification.VerificationOperationalReport
    -> Provers.SlowAtpReport
    -> IO CommandOutcome
finalizePresentation
        outputPlan presentationPreflight report disposition successOutcome
        operationalReport slowReport =
    case disposition of
        Verification.PresentationAvailable presentation ->
            prepareAndFinalize (Verification.verificationHtmlPresentation presentation)
        Verification.PresentationNotRequested ->
            impossible "verification completed without its required presentation"
  where
    PresentationPreflight environment _preparation html = presentationPreflight
    prepareAndFinalize presentation = do
        analysisResult <-
            HtmlExport.preparePresentationAnalysisFromLibraryRoot
                (Workspace.workspaceLibraryRoot environment)
                presentation
        case analysisResult of
            Left failure ->
                pure (VerifiedOutputFailed report
                    (VerifiedPresentationAnalysisFailed failure) operationalReport slowReport)
            Right analysis -> do
                emitDiagnostics (HtmlExport.preparedPresentationDiagnostics analysis)
                case NonEmpty.nonEmpty (HtmlExport.preparedPresentationMissingHints analysis) of
                    Just missing -> pure (VerificationRenderHintsRejected
                        report missing operationalReport slowReport)
                    Nothing -> case html of
                        Nothing -> pure successOutcome
                        Just (layout, _destinations) -> publishHtml layout analysis

    publishHtml layout analysis = do
        case HtmlExport.prepareHtmlArtefacts layout analysis of
            Left failure ->
                pure
                    (VerifiedOutputFailed
                        report
                        (VerifiedHtmlArtefactFailed failure)
                        operationalReport
                        slowReport)
            Right preparedExport -> do
                let routes =
                        fromMaybe
                            (impossible
                                "HTML preflight has no reserved output routes")
                            (Output.verificationHtmlRoutes outputPlan)
                    artefacts =
                        HtmlExport.preparedHtmlExportArtefacts preparedExport
                case HtmlOutput.planHtmlOutputAgainst routes artefacts of
                    Left failure ->
                        pure
                            (VerifiedOutputFailed
                                report
                                (VerifiedHtmlOutputPlanningFailed failure)
                                operationalReport
                                slowReport)
                    Right plan ->
                        HtmlOutput.writeHtmlOutput plan >>= \case
                            Left failure ->
                                pure
                                    (VerifiedOutputFailed
                                        report
                                        (VerifiedHtmlPublicationFailed failure)
                                        operationalReport
                                        slowReport)
                            Right () ->
                                pure successOutcome

    emitDiagnostics =
        traverse_
            (Text.hPutStrLn stderr . Terminal.renderTerminalDiagnostic)

verificationCommandOutcome
    :: Verification.VerificationResult
    -> Maybe Verification.VerificationOperationalReport
    -> Provers.SlowAtpReport
    -> CommandOutcome
verificationCommandOutcome result operationalReport slowReport = case result of
    Verification.VerificationCompleted report _presentation ->
        VerificationSucceeded report operationalReport slowReport
    Verification.CompletedWithExplicitGaps report _presentation ->
        VerificationCompletedWithGaps report operationalReport slowReport
    Verification.VerificationFailure report failure ->
        VerificationRejected report failure operationalReport slowReport
    Verification.VerificationCheckingFailure report failure ->
        VerificationCheckingRejected report failure operationalReport slowReport

commandOutcomeExitCode :: CommandOutcome -> ExitCode
commandOutcomeExitCode = \case
    CommandCompleted ->
        ExitSuccess
    VerificationSucceeded{} ->
        ExitSuccess
    VerificationCompletedWithGaps{} ->
        ExitSuccess
    VerificationRejected _report failed _operational _slow ->
        if Verification.failedVerificationIsLogicalRejection failed
            then ExitFailure 1
            else ExitFailure 2
    VerificationCheckingRejected _report failure _operational _slow ->
        case Verification.verificationDriverErrorKind failure of
            Verification.VerificationSourceFailure -> ExitFailure 1
            Verification.VerificationInfrastructureFailure -> ExitFailure 2
    VerificationRenderHintsRejected{} ->
        ExitFailure 1
    SourcePlanningFailed{} ->
        ExitFailure 1
    ParseOnlyFailed{} ->
        ExitFailure 1
    VerificationDriverFailed failure ->
        case Verification.verificationDriverErrorKind failure of
            Verification.VerificationSourceFailure -> ExitFailure 1
            Verification.VerificationInfrastructureFailure -> ExitFailure 2
    VerificationSessionFailed{} ->
        ExitFailure 2
    StorePlanningFailed{} ->
        ExitFailure 2
    StoreLeaseFailed{} ->
        ExitFailure 2
    StoreIncompatible{} ->
        ExitFailure 2
    StoreFailed{} ->
        ExitFailure 2
    OutputPlanningFailed{} ->
        ExitFailure 2
    HtmlLayoutFailed{} ->
        ExitFailure 2
    DumpObservationFailed{} ->
        ExitFailure 2
    VerifiedOutputFailed{} ->
        ExitFailure 2

renderCommandOutcome :: CommandOutcome -> IO ()
renderCommandOutcome = \case
    CommandCompleted ->
        pure ()
    VerificationSucceeded report operationalReport slowReport -> do
        Text.hPutStrLn stderr "Verification successful."
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport
    VerificationCompletedWithGaps report operationalReport slowReport -> do
        Text.hPutStrLn stderr
            "Verification completed with explicit proof gaps."
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport
    VerificationRejected report failure operationalReport slowReport -> do
        renderFailedVerification failure
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport
    VerificationCheckingRejected report failure operationalReport slowReport -> do
        renderVerificationDriverFailure failure
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport
    VerificationRenderHintsRejected
            report missing operationalReport slowReport -> do
        traverse_
            (Text.hPutStrLn stderr . Terminal.renderTerminalDiagnostic)
            (Html.renderMissingRenderHintDiagnostics
                DiagnosticError
                (NonEmpty.toList missing))
        Text.hPutStrLn stderr
            "Verification rejected because render hints are missing."
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport
    SourcePlanningFailed failure ->
        renderDiagnosticOr
            ("Source planning failed: "
                <> Parse.renderParseWorkspaceError failure)
            (Parse.parseWorkspaceErrorDiagnostic failure)
    ParseOnlyFailed failure ->
        renderDiagnosticOr
            ("Parsing failed: "
                <> Workspace.renderAuthorityFreeParseError failure)
            (Workspace.authorityFreeParseDiagnostic failure)
    VerificationDriverFailed failure ->
        renderVerificationDriverFailure failure
    VerificationSessionFailed path failure ->
        renderFailure case failure of
            Verification.VerificationSessionFoundationError{} ->
                "The fixed foundation manifest is invalid."
            Verification.VerificationSessionStoreError storeFailure ->
                "Store failure at "
                    <> quotePath (Store.storePathFilePath path)
                    <> ": "
                    <> Store.renderStoreLifecycleError storeFailure
            Verification.VerificationSessionTheoryMismatch expected actual ->
                "Store theory mismatch at "
                    <> quotePath (Store.storePathFilePath path)
                    <> ": expected "
                    <> StrictText.pack (show expected)
                    <> ", found "
                    <> StrictText.pack (show actual)
    StorePlanningFailed failure ->
        renderFailure
            ("Store path planning failed: "
                <> Store.renderStorePlanningError failure)
    StoreLeaseFailed failure ->
        renderFailure
            ("Store lease failed: "
                <> Store.renderStoreLeaseError failure)
    StoreIncompatible path failure ->
        renderFailure
            ("Disposable store "
                <> quotePath (Store.storePathFilePath path)
                <> " is incompatible: "
                <> Store.renderStoreIncompatibility failure
                <> ". Use --refresh to rebuild it, use --fresh, or choose another --store path.")
    StoreFailed path failure ->
        renderFailure
            ("Store failure at "
                <> quotePath (Store.storePathFilePath path)
                <> ": " <> Store.renderStoreLifecycleError failure)
    OutputPlanningFailed failure ->
        renderFailure
            ("Verification output preflight failed: "
                <> Output.renderOutputPlanError failure)
    HtmlLayoutFailed failure ->
        renderFailure
            ("HTML route planning failed: "
                <> HtmlLayout.renderHtmlLayoutError failure)
    DumpObservationFailed failure ->
        renderFailure (RequestDump.renderDumpObservationError failure)
    VerifiedOutputFailed report failure operationalReport slowReport -> do
        renderVerifiedOutputFailure failure
        renderVerificationReport report
        traverse_ writeOperationalReport operationalReport
        renderSlowAtpReport slowReport

renderFailure :: Text -> IO ()
renderFailure =
    Text.hPutStrLn stderr

renderVerificationDriverFailure
    :: Verification.VerificationDriverError
    -> IO ()
renderVerificationDriverFailure failure =
    renderDiagnosticOr
        (Verification.renderVerificationDriverError failure)
        (Verification.verificationDriverDiagnostic failure)

renderDiagnosticOr :: Text -> Maybe Diagnostic -> IO ()
renderDiagnosticOr fallback =
    maybe
        (renderFailure fallback)
        (renderFailure . Terminal.renderTerminalDiagnostic)

quotePath :: FilePath -> Text
quotePath = StrictText.pack . show

renderFailedVerification :: Verification.FailedVerification -> IO ()
renderFailedVerification =
    renderFailure
        . Terminal.renderTerminalDiagnostic
        . Verification.failedVerificationDiagnostic

renderVerifiedOutputFailure :: VerifiedOutputFailure -> IO ()
renderVerifiedOutputFailure = \case
    VerifiedPresentationAnalysisFailed failure ->
        renderFailure
            ("Verification succeeded, but presentation analysis failed: "
                <> HtmlExport.renderPresentationAnalysisError failure)
    VerifiedHtmlArtefactFailed failure ->
        renderFailure
            ("Verification succeeded, but HTML preparation failed: "
                <> HtmlExport.renderHtmlArtefactError failure)
    VerifiedHtmlOutputPlanningFailed failure ->
        renderFailure
            ("Verification succeeded, but prepared HTML did not match the reserved routes: "
                <> HtmlOutput.renderHtmlOutputError failure)
    VerifiedHtmlPublicationFailed failure -> do
        renderFailure
            "Verification succeeded, but HTML publication did not complete."
        traverse_
            renderFailure
            (HtmlOutput.renderHtmlPublicationError failure)
    VerifiedHtmlLayoutUnavailable ->
        renderFailure
            "Verification succeeded, but the preflight HTML layout was unavailable."

renderVerificationReport :: Verification.VerificationReport -> IO ()
renderVerificationReport report = do
    Text.hPutStrLn stderr
        ( "Direct source authorization summary: "
            <> renderCount
                sourceAxiomCount
                "source axiom"
            <> ", "
            <> renderCount
                omittedCount
                "explicit proof gap"
            <> "."
        )
    for_
        (Verification.verificationDirectEscapes report)
        \escape ->
            Text.hPutStrLn stderr case Verification.reportedEscapeKind escape of
                Verification.ReportedSourceAxiom ->
                    "Source axiom at "
                        <> locationToText
                            (Verification.reportedEscapeLocation escape)
                Verification.ReportedOmitted ->
                    "Explicit proof gap at "
                        <> locationToText
                            (Verification.reportedEscapeLocation escape)
  where
    sourceAxiomCount =
        length
            [ ()
            | escape <- Verification.verificationDirectEscapes report
            , Verification.reportedEscapeKind escape
                == Verification.ReportedSourceAxiom
            ]
    omittedCount =
        length
            [ ()
            | escape <- Verification.verificationDirectEscapes report
            , Verification.reportedEscapeKind escape
                == Verification.ReportedOmitted
            ]
    renderCount amount noun =
        StrictText.pack (show amount)
            <> " "
            <> noun
            <> if amount == 1 then "" else "s"

renderOperationalReport
    :: Verification.VerificationOperationalReport
    -> Text
renderOperationalReport report =
    StrictText.unlines
        [ "Source planning"
        , durationRow
            "source graph preparation"
            (SourceGraph.sourceGraphPreparationWallNanoseconds planning)
        , "  source prefixes scanned: "
            <> showNatural (SourceGraph.sourcePrefixScanCount planning)
        , "Store lookup and live execution report"
        , columnHeading "" "found" "missed" "bypassed"
        , lookupRow
            "module installations"
            (Verification.moduleInstallationDecisions checkReport)
        , lookupRow
            "proof validations"
            (Verification.proofValidationDecisions checkReport)
        , lookupRow
            "declaration validations"
            (Verification.declarationValidationDecisions checkReport)
        , "  live Vampire runs started: "
            <> StrictText.pack
                (show (Verification.liveVampireRunsStarted checkReport))
        , "Checked import work"
        , "  node visits: " <> showInt (Declaration.importNodeVisits importWork)
        , "  local contributions inserted: " <> showInt (Declaration.importContributionInsertions importWork)
        , "  parent memo hits: " <> showInt (Declaration.importParentMemoHits importWork)
        , "  parent memo misses: " <> showInt (Declaration.importParentMemoMisses importWork)
        , "  object closure checks: " <> showInt (Declaration.importObjectClosureChecks importWork)
        , "  proposition checks: " <> showInt (Declaration.importPropositionChecks importWork)
        , "  composition metadata checks: " <> showInt (Declaration.importCompositionChecks importWork)
        , "  occurrence checks: " <> showInt (Declaration.importOccurrenceChecks importWork)
        , "  environment materializations: " <> showInt (Declaration.importEnvironmentMaterializations importWork)
        , "  global target checks: " <> showInt (Declaration.importGlobalTargetChecks importWork)
        , "  structure checks: " <> showInt (Declaration.importStructureChecks importWork)
        , "  local structure input checks: " <> showInt (Declaration.importStructureInputChecks importWork)
        , "  structure predicate checks: " <> showInt (Declaration.importStructurePredicateChecks importWork)
        , "  definition checks: " <> showInt (Declaration.importDefinitionChecks importWork)
        , "  registration checks: " <> showInt (Declaration.importRegistrationChecks importWork)
        , "  formation compilation inspections: " <> StrictText.pack (show (Declaration.importFormationPreparationWork importWork))
        , "Check-local monotonic phase wall time"
        , "  module pipeline limit: " <> showInt (Verification.modulePipelineWorkerLimit checkReport)
        , durationRow
            "prelude acquisition"
            (Verification.finalPreludeWallNanoseconds checkReport)
        , durationRow
            "source parsing"
            (Verification.sourceParsingWallNanoseconds checkReport)
        , durationRow
            "verification source completion"
            (Parse.verificationCompletionWorkNanoseconds completion)
        , "  verification completions: "
            <> showNatural (Parse.verificationCompletionCount completion)
        , durationRow
            "presentation-only source completion"
            (Parse.presentationOnlyCompletionWorkNanoseconds completion)
        , "  presentation-only completions: "
            <> showNatural (Parse.presentationOnlyCompletionCount completion)
        , durationRow
            "module checking"
            (Verification.moduleCheckingWallNanoseconds checkReport)
        , "Live Vampire lifecycle measurements"
        , "  workers: "
            <> showInt
                (Provers.vampireExecutionWorkerCount vampireMeasurements)
        , "  completed runs: "
            <> showNatural
                (Provers.vampireExecutionCompletedRuns vampireMeasurements)
        , durationRow
            "aggregate executor wall"
            (Provers.vampireExecutionAggregateNanoseconds
                vampireMeasurements)
        , durationRow
            "first-start to last-completion span"
            (Provers.vampireExecutionActiveSpanNanoseconds
                vampireMeasurements)
        , durationRow
            "longest completed run"
            (Provers.vampireExecutionLongestNanoseconds
                vampireMeasurements)
        , "  maximum queue depth: "
            <> showNatural
                (Provers.vampireExecutionMaximumQueueDepth
                    vampireMeasurements)
        , "  completed-run worker occupancy: "
            <> renderVampireOccupancy vampireMeasurements
        ]
  where
    importWork = Verification.importPreparationWork checkReport
    planning =
        Verification.verificationSourcePlanningMeasurements report
    checkReport =
        Verification.verificationCheckOperationalReport report
    completion = Verification.sourceCompletionMeasurements checkReport
    vampireMeasurements =
        Verification.vampireExecutionMeasurements checkReport
    lookupRow label counts =
        columnHeading
            ("  " <> label)
            (showNatural (Verification.lookupRowsFound counts))
            (showNatural (Verification.lookupMisses counts))
            (showNatural (Verification.lookupBypasses counts))
    columnHeading label found missed bypassed =
        StrictText.justifyLeft 31 ' ' label
            <> StrictText.justifyRight 5 ' ' found
            <> StrictText.justifyRight 8 ' ' missed
            <> StrictText.justifyRight 10 ' ' bypassed
    showNatural = StrictText.pack . show
    showInt = StrictText.pack . show
    durationRow label nanoseconds =
        StrictText.justifyLeft 43 ' ' ("  " <> label <> ":")
            <> renderNanoseconds nanoseconds

renderVampireOccupancy :: Provers.VampireExecutionReport -> Text
renderVampireOccupancy report
    | workers <= 0 || spanNanoseconds == 0 = "n/a"
    | otherwise =
        StrictText.pack
            (showFFloat (Just 1) percentage "%")
  where
    workers = Provers.vampireExecutionWorkerCount report
    spanNanoseconds = Provers.vampireExecutionActiveSpanNanoseconds report
    aggregate = Provers.vampireExecutionAggregateNanoseconds report
    percentage =
        100 * fromIntegral aggregate
            / (fromIntegral workers * fromIntegral spanNanoseconds :: Double)

renderNanoseconds :: Word64 -> Text
renderNanoseconds nanoseconds =
    StrictText.pack
        (showFFloat
            (Just 3)
            (fromIntegral nanoseconds / (1000000000 :: Double))
            "s")

writeOperationalReport
    :: Verification.VerificationOperationalReport
    -> IO ()
writeOperationalReport = Text.hPutStr stderr . renderOperationalReport

renderSlowAtpReport :: Provers.SlowAtpReport -> IO ()
renderSlowAtpReport report =
    unless (null (Provers.slowAtpTasks report)) do
        Text.hPutStrLn stderr
            "Slow completed live Vampire runs"
        Text.hPutStrLn stderr
            "(executor wall time; reused validations are excluded):"
        traverse_ renderTask (Provers.slowAtpTasks report)
        let omitted = Provers.slowAtpOmittedTaskCount report
        when (omitted > 0)
            (Text.hPutStrLn stderr
                ( StrictText.pack
                    (show (length (Provers.slowAtpTasks report)))
                    <> " slowest shown; "
                    <> StrictText.pack (show omitted)
                    <> " additional tasks took at least 4.0 seconds."
                ))
  where
    renderTask task =
        Text.hPutStrLn stderr
            ( "  "
                <> renderAtpDuration (Provers.slowAtpDuration task)
                <> " "
                <> renderSlowAtpOutcome (Provers.slowAtpOutcome task)
                <> " at "
                <> locationToText (Provers.slowAtpLocation task)
                <> " ("
                <> Provers.renderVampireLiveTaskReference
                    (Provers.slowAtpPosition task)
                    (Provers.slowAtpRequestId task)
                <> ")"
            )

renderAtpDuration :: Provers.AtpDuration -> Text
renderAtpDuration duration =
    StrictText.pack
        (showFFloat
            (Just 2)
            (fromIntegral (Provers.atpDurationNanoseconds duration)
                / (1000000000 :: Double))
            "s")

renderSlowAtpOutcome :: Provers.SlowAtpOutcome -> Text
renderSlowAtpOutcome = \case
    Provers.SlowAtpAccepted -> "accepted"
    Provers.SlowAtpRejected rejection ->
        "rejected (" <> StrictText.pack (show rejection) <> ")"
    Provers.SlowAtpProtocolFailed -> "protocol failure"
    Provers.SlowAtpProcessFailed -> "process failure"

getVampireExecutable :: IO FilePath
getVampireExecutable =
    fromMaybe "vampire" <$> lookupEnv "FELIX_VAMPIRE"


data RawCommand
    = RawVersion
    | RawFile !RawFileCommand

data RawFileCommand = RawFileCommand
    { rawInput :: !Input
    , rawParseOnly :: !Bool
    , rawStore :: !(Maybe FilePath)
    , rawRefresh :: !Bool
    , rawFresh :: !Bool
    , rawTimeLimit :: !(Maybe Provers.TimeLimit)
    , rawMemoryLimit :: !(Maybe Provers.MemoryLimit)
    , rawJobs :: !(Maybe Provers.EffectiveJobs)
    , rawModuleJobs :: !(Maybe Provers.EffectiveJobs)
    , rawProverJobs :: !(Maybe Provers.EffectiveJobs)
    , rawDump :: !(Maybe FilePath)
    , rawHtml :: !Bool
    , rawCheckRenderHints :: !Bool
    , rawStoreReport :: !Bool
    }

rawCommandParser :: Parser RawCommand
rawCommandParser =
    versionParser
        <|> (RawFile <$> rawFileCommandParser)

versionParser :: Parser RawCommand
versionParser =
    flag'
        RawVersion
        (long "version" <> help "Show the Felix version.")

inputParser :: Parser Input
inputParser =
    Input
        <$> strArgument
            (help "Source file" <> metavar "FILE")

rawFileCommandParser :: Parser RawFileCommand
rawFileCommandParser =
    RawFileCommand
        <$> inputParser
        <*> switch
            (long "parseonly"
                <> help "Resolve and parse source without verification.")
        <*> optional
            (strOption
                (long "store"
                    <> metavar "PATH"
                    <> help "Use the disposable SQLite store at PATH."))
        <*> switch
            (long "refresh"
                <> help "Discard the selected store before verification.")
        <*> switch
            (long "fresh"
                <> help "Use a fresh temporary disposable store.")
        <*> optional timeLimitParser
        <*> optional memoryLimitParser
        <*> optional jobsParser
        <*> optional (componentJobsParser "module-jobs" "module pipelines")
        <*> optional (componentJobsParser "prover-jobs" "Vampire invocations")
        <*> optional
            (strOption
                (long "dump"
                    <> metavar "DUMPDIR"
                    <> help "Dump exact Vampire requests as they execute."))
        <*> switch
            (long "html"
                <> help "Publish verified HTML under ./html.")
        <*> switch
            (long "check-render-hints"
                <> help
                    "Compatibility flag: verification always checks presentation render hints.")
        <*> switch
            (long "store-report"
                <> help "Report store lookup decisions and live Vampire starts.")

parseCommandArguments :: [String] -> ParserResult Command
parseCommandArguments arguments =
    case execParserPure
            defaultPrefs
            rawCommandParserInfo
            arguments of
        Success raw ->
            case validateRawCommand raw of
                Left message ->
                    Failure
                        (parserFailure
                            defaultPrefs
                            rawCommandParserInfo
                            (ErrorMsg message)
                            [])
                Right selected ->
                    Success selected
        Failure failure ->
            Failure failure
        CompletionInvoked completion ->
            CompletionInvoked completion

validateRawCommand :: RawCommand -> Either String Command
validateRawCommand = \case
    RawVersion ->
        Right Version
    RawFile raw
        | rawParseOnly raw
        , not (null verificationOnlyOptions) ->
            Left
                ("--parseonly cannot be combined with verification options: "
                    <> unwords verificationOnlyOptions)
        | rawParseOnly raw ->
            Right (ParseOnly (rawInput raw))
        | isJust (rawStore raw) && rawFresh raw ->
            Left "--store and --fresh are mutually exclusive"
        | otherwise ->
            Right
                (Verify
                    (rawInput raw)
                    VerificationOptions
                        { verificationStoreSelection =
                            case rawStore raw of
                                Just path ->
                                    Store.ExplicitStore path
                                Nothing
                                    | rawFresh raw ->
                                        Store.FreshTemporaryStore
                                    | otherwise ->
                                        Store.DefaultStore
                        , verificationStoreRefreshRequested =
                            rawRefresh raw && not (rawFresh raw)
                        , verificationTimeLimit =
                            fromMaybe
                                Provers.defaultTimeLimit
                                (rawTimeLimit raw)
                        , verificationMemoryLimit =
                            fromMaybe
                                Provers.defaultMemoryLimit
                                (rawMemoryLimit raw)
                        , verificationModuleJobsOverride = rawModuleJobs raw <|> rawJobs raw
                        , verificationProverJobsOverride = rawProverJobs raw <|> rawJobs raw
                        , verificationDumpDestination =
                            rawDump raw
                        , verificationPresentationRequest =
                            if rawHtml raw then PublishHtml else CheckRenderHints
                        , verificationStoreReportRequested =
                            rawStoreReport raw
                        })
      where
        verificationOnlyOptions =
            catMaybes
                [ "--store" <$ rawStore raw
                , if rawRefresh raw then Just "--refresh" else Nothing
                , if rawFresh raw then Just "--fresh" else Nothing
                , "--timelimit" <$ rawTimeLimit raw
                , "--memlimit" <$ rawMemoryLimit raw
                , "--jobs" <$ rawJobs raw
                , "--module-jobs" <$ rawModuleJobs raw
                , "--prover-jobs" <$ rawProverJobs raw
                , "--dump" <$ rawDump raw
                , if rawHtml raw then Just "--html" else Nothing
                , if rawCheckRenderHints raw
                    then Just "--check-render-hints"
                    else Nothing
                , if rawStoreReport raw
                    then Just "--store-report"
                    else Nothing
                ]

timeLimitParser :: Parser Provers.TimeLimit
timeLimitParser =
    Provers.Seconds
        <$> option (boundedLimitReader "SECONDS")
            ( long "timelimit"
                <> short 't'
                <> metavar "SECONDS"
                <> help "Time limit for each Vampire request."
            )

memoryLimitParser :: Parser Provers.MemoryLimit
memoryLimitParser =
    Provers.Megabytes
        <$> option (boundedLimitReader "MB")
            ( long "memlimit"
                <> short 'm'
                <> metavar "MB"
                <> help "Memory limit for each Vampire process."
            )

boundedLimitReader :: String -> ReadM Word64
boundedLimitReader name = eitherReader \raw ->
    case readBoundedIntegral raw of
        Just parsed -> Right parsed
        Nothing -> Left
            (name <> " must be an integer from 0 to " <> show (maxBound :: Word64))

jobsParser :: Parser Provers.EffectiveJobs
jobsParser =
    option
        jobsReader
        ( long "jobs"
            <> short 'j'
            <> metavar "JOBS"
            <> help
                "Run at most JOBS module checkers and Vampire invocations."
        )

componentJobsParser :: String -> String -> Parser Provers.EffectiveJobs
componentJobsParser name component =
    option jobsReader
        (long name <> metavar "JOBS"
            <> help ("Run at most JOBS " <> component <> "; overrides --jobs for this component."))

jobsReader :: ReadM Provers.EffectiveJobs
jobsReader = eitherReader \raw ->
    case readBoundedIntegral raw >>= Provers.effectiveJobs of
        Just jobs -> Right jobs
        Nothing -> Left "JOBS must be a positive integer"
