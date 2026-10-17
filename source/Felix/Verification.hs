{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Felix.Verification
    ( VerificationSession
    , VerificationSessionError(..)
    , withVerificationSession
    , withVerificationSessionUsingStore
    , CheckRequest(..)
    , CheckOutcome(..)
    , LookupDecisionCounts(..)
    , CheckOperationalReport(..)
    , VerificationOperationalReport(..)
    , completeVerificationOperationalReport
    , checkWorkspace
    , checkWorkspaceUsingModuleStarter
    , StoreValidationMode(..)
    , WorkPosition
    , workPosition
    , workPositionModuleOrdinal
    , workPositionLocalRequestOrdinal
    , VerificationRequestObserver
    , verificationRequestObserver
    , PreparedVerificationRequest
    , SlowAtpOutcome(..)
    , SlowAtpTask(..)
    , SlowAtpReport(..)
    , slowAtpOmittedTaskCount
    , VerificationResult(..)
    , PresentationDisposition(..)
    , VerificationPresentation
    , verificationHtmlPresentation
    , ReportedEscapeKind(..)
    , ReportedEscape(..)
    , VerificationReport(..)
    , VerificationDriverError(..)
    , VerificationDriverErrorKind(..)
    , verificationDriverErrorKind
    , renderVerificationDriverError
    , verificationDriverDiagnostic
    , FailedVerification(..)
    , failedVerificationIsLogicalRejection
    , failedVerificationDiagnostic
    ) where


import Base
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Preparation qualified as Preparation
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.FinalPrelude qualified as FinalPrelude
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Typed
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Structure.Obligation qualified as Obligation
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.ValidationCache qualified as ValidationCache
import Felix.Module (localDeclarationOrdinal)
import Felix.Parse (ParseWorkspaceError(..))
import Felix.Parse qualified as Felix
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace
import Felix.Prelude qualified as Prelude
import Felix.Provers
import Felix.Source
import Felix.Source.Graph
    ( ResolvedSourceGraph
    , SourcePlanningMeasurements
    )
import Felix.Store qualified as Store
import Felix.Render.Html.Export qualified as HtmlExport
import Felix.Report.Diagnostic (Diagnostic(..))
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface qualified as Syntax

import Control.Exception qualified as Exception
import Control.Concurrent.MVar (MVar, newMVar, putMVar, takeMVar)
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.IORef (IORef, atomicModifyIORef', modifyIORef', newIORef, readIORef)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Effectful (Eff, IOE, (:>), runEff)
import Effectful.Error.Static (Error)
import Effectful.Error.Static qualified as Error
import Numeric.Natural (Natural)
import UnliftIO.Async qualified as Async

data VerificationResult
    = VerificationCompleted
        !VerificationReport
        !PresentationDisposition
    | CompletedWithExplicitGaps
        !VerificationReport
        !PresentationDisposition
    | VerificationFailure !VerificationReport !FailedVerification
    | VerificationCheckingFailure
        !VerificationReport
        !VerificationDriverError
    deriving (Show)

data PresentationDisposition
    = PresentationNotRequested
    | PresentationAvailable !VerificationPresentation
    deriving (Show)

-- | Strict owner-independent source presentation retained only after the
-- complete typed workspace succeeds.
data VerificationPresentation = VerificationPresentation
    !HtmlExport.HtmlPresentation

instance Show VerificationPresentation where
    show _presentation =
        "VerificationPresentation <HTML presentation>"

verificationHtmlPresentation
    :: VerificationPresentation
    -> HtmlExport.HtmlPresentation
verificationHtmlPresentation (VerificationPresentation presentation) =
    presentation

data ReportedEscapeKind
    = ReportedSourceAxiom
    | ReportedOmitted
    deriving (Show, Eq)

data ReportedEscape = ReportedEscape
    { reportedEscapeKind :: !ReportedEscapeKind
    , reportedEscapeLocation :: !Location
    }
    deriving (Show, Eq)

data VerificationReport = VerificationReport
    { verificationDirectEscapes :: ![ReportedEscape]
    }
    deriving (Show, Eq)

newtype VerificationRequestObserver = VerificationRequestObserver
    { observeVerificationRequest
        :: WorkPosition
        -> PreparedVerificationRequest
        -> IO ()
    }

verificationRequestObserver
    :: (WorkPosition
        -> PreparedVerificationRequest
        -> IO ())
    -> VerificationRequestObserver
verificationRequestObserver =
    VerificationRequestObserver

data FailedVerification = FailedVerification
    { failedVerificationLocation :: !Location
    , failedVerificationResolution :: !FailedVampireResolution
    , failedVerificationPreparation :: ![Preparation.PreparationStatistics]
    , failedVerificationObligations :: ![Obligation.ObligationContext]
    }
    deriving (Show)

failedVerificationIsLogicalRejection :: FailedVerification -> Bool
failedVerificationIsLogicalRejection failed =
    case failedVampireResolutionFailure
            (failedVerificationResolution failed) of
        VampireFailureRejected RejectedCounterexample _evidence -> True
        VampireFailureRejected RejectedContradictoryInput _evidence -> True
        VampireFailureRejected RejectedIndeterminate{} _evidence -> False
        VampireFailureProtocol{} -> False
        VampireFailureProcess{} -> False

failedVerificationDiagnostic :: FailedVerification -> Diagnostic
failedVerificationDiagnostic failed =
    let diagnostic = failedVampireResolutionDiagnostic
            (failedVerificationLocation failed) (failedVerificationResolution failed)
    in diagnostic {diagnosticNotes = diagnosticNotes diagnostic
        <> (pretty . Preparation.renderPreparationExhaustion <$> failedVerificationPreparation failed)
        <> (pretty <$> concatMap Obligation.renderObligationContext (failedVerificationObligations failed))}

data VerificationDriverError
    = VerificationWorkspaceError
        !ParseWorkspaceError
    | VerificationMissingImportedModule
        !ResolvedSourceAddress
    | VerificationMissingRootModule
        !ResolvedSourceAddress
    | VerificationFinalPreludeReadinessError
        !Typed.FinalPreludeReadinessError
    | VerificationTypedInputError
        !ResolvedSource
        !Typed.TypedModuleInputError
    | VerificationTypedOpenError
        !ResolvedSource
        !Declaration.DriverOpenError
    | VerificationTypedCachedModuleError
        !ResolvedSource
        !Typed.CachedTypedModuleError
    | VerificationTypedModuleError
        !ResolvedSource
        !Typed.TypedModuleFailure
        !Commit.PendingModulePrefix
    | VerificationValidationIntegrityError
        !ResolvedSource
        !Declaration.ValidationIntegrityError
    | VerificationAdmittedViewError
        !ResolvedSource
        !AdmittedViewError
    | VerificationParsedArtefactIntegrityError
        !ResolvedSource
        !Felix.ParsedArtefactIntegrityError
    | VerificationStoreFailure !Store.StoreFailure
    | VerificationModuleArtefactKeyError !Semantic.ModuleArtefactKeyError
    | VerificationModuleSchedulerInvariant !Text
    | VerificationPresentationInvariantError
        !HtmlExport.HtmlPresentationAssemblyError
    | VerificationPresentationDemandMismatch
        !Felix.PresentationDemand
        !Felix.PresentationDemand
    deriving (Show)

instance Exception.Exception VerificationDriverError

data VerificationDriverErrorKind
    = VerificationSourceFailure
    | VerificationInfrastructureFailure
    deriving (Show, Eq)

verificationDriverErrorKind
    :: VerificationDriverError
    -> VerificationDriverErrorKind
verificationDriverErrorKind = \case
    VerificationWorkspaceError SourceParsedModuleBindingInvariant{} ->
        VerificationInfrastructureFailure
    VerificationWorkspaceError
            (SourceWorkspaceError SourceGraphScanningInvariantViolation{}) ->
        VerificationInfrastructureFailure
    VerificationWorkspaceError{} -> VerificationSourceFailure
    VerificationTypedInputError{} -> VerificationSourceFailure
    VerificationTypedModuleError _source failure _prefix ->
        case failure of
            Typed.TypedActionFailed path ->
                case Typed.typedPathErrorDisposition path of
                    Proof.ProofSourceRejection ->
                        VerificationSourceFailure
                    Proof.ProofInfrastructureFailure ->
                        VerificationInfrastructureFailure
            _ -> VerificationInfrastructureFailure
    VerificationMissingImportedModule{} -> VerificationInfrastructureFailure
    VerificationMissingRootModule{} -> VerificationInfrastructureFailure
    VerificationFinalPreludeReadinessError{} ->
        VerificationInfrastructureFailure
    VerificationTypedOpenError{} -> VerificationInfrastructureFailure
    VerificationTypedCachedModuleError{} -> VerificationInfrastructureFailure
    VerificationValidationIntegrityError{} ->
        VerificationInfrastructureFailure
    VerificationAdmittedViewError{} -> VerificationInfrastructureFailure
    VerificationParsedArtefactIntegrityError{} ->
        VerificationInfrastructureFailure
    VerificationStoreFailure{} -> VerificationInfrastructureFailure
    VerificationModuleArtefactKeyError{} ->
        VerificationInfrastructureFailure
    VerificationModuleSchedulerInvariant{} ->
        VerificationInfrastructureFailure
    VerificationPresentationInvariantError{} ->
        VerificationInfrastructureFailure
    VerificationPresentationDemandMismatch{} ->
        VerificationInfrastructureFailure

renderVerificationDriverError :: VerificationDriverError -> Text
renderVerificationDriverError = \case
    VerificationWorkspaceError failure ->
        "Verification input failed: "
            <> Felix.renderParseWorkspaceError failure
    VerificationTypedInputError source failure ->
        "Typed module input failed in "
            <> resolvedSourceDisplay source
            <> ": " <> Typed.renderTypedModuleInputError failure
    VerificationTypedOpenError source failure ->
        "Typed module startup failed in "
            <> resolvedSourceDisplay source
            <> ": " <> Declaration.renderDriverOpenError failure
    VerificationTypedCachedModuleError source failure ->
        "Cached typed module is invalid in "
            <> resolvedSourceDisplay source
            <> ": " <> Typed.renderCachedTypedModuleError failure
    VerificationTypedModuleError source failure _prefix ->
        "Typed module checking failed in "
            <> resolvedSourceDisplay source
            <> ": " <> Typed.renderTypedModuleFailure failure
    VerificationValidationIntegrityError source failure ->
        "Typed module validation store is inconsistent in "
            <> resolvedSourceDisplay source
            <> ": " <> Declaration.renderValidationIntegrityError failure
    VerificationAdmittedViewError source failure ->
        "Typed admitted-source association is inconsistent in "
            <> resolvedSourceDisplay source
            <> ": " <> Text.pack (show failure)
    VerificationParsedArtefactIntegrityError source failure ->
        "Parsed artefact is inconsistent in "
            <> resolvedSourceDisplay source
            <> ": " <> Text.pack (show failure)
    VerificationStoreFailure failure ->
        "Verification store failed: " <> Store.renderStoreFailure failure
    VerificationModuleArtefactKeyError{} ->
        "Typed module artefact inputs are inconsistent."
    VerificationModuleSchedulerInvariant message ->
        "Typed module scheduler invariant failed: " <> message
    VerificationPresentationInvariantError failure ->
        "HTML presentation assembly invariant failed: "
            <> HtmlExport.renderHtmlPresentationAssemblyError failure
    VerificationPresentationDemandMismatch expected actual ->
        "Presentation demand mismatch: expected "
            <> Text.pack (show expected)
            <> ", parsed " <> Text.pack (show actual)
    VerificationMissingImportedModule address ->
        "Verification could not find checked imported module "
            <> Text.pack (show address) <> "."
    VerificationMissingRootModule address ->
        "Verification could not find checked root module "
            <> Text.pack (show address) <> "."
    VerificationFinalPreludeReadinessError{} ->
        "The prelude failed."

verificationDriverDiagnostic
    :: VerificationDriverError
    -> Maybe Diagnostic
verificationDriverDiagnostic = \case
    VerificationWorkspaceError failure ->
        Felix.parseWorkspaceErrorDiagnostic failure
    VerificationFinalPreludeReadinessError
        (Typed.FinalPreludeReadinessBuildFailed
            (FinalPrelude.FinalPreludeDeclarationFailed failure))
        | Just (location, resolution, preparation) <- Declaration.locatedVampireFailure failure ->
        let diagnostic = failedVerificationDiagnostic (FailedVerification location resolution preparation
                (Declaration.declarationRecordObligations failure))
        in Just
            diagnostic
                { diagnosticTitle =
                    "the prelude failed: "
                        <> diagnosticTitle diagnostic
                }
    VerificationTypedModuleError _source failure _prefix ->
        Typed.typedModuleFailureDiagnostic failure
    _failure -> Nothing

resolvedSourceDisplay :: ResolvedSource -> Text
resolvedSourceDisplay source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack (resolvedSourceLocationPath source)

data TypedWorkspaceOutcome
    = TypedWorkspaceSucceeded
        !AdmittedTypedWorkspace
        !(Map ResolvedSourceAddress Typed.SealedTypedModule)
    | TypedWorkspaceRejected
        !AdmittedTypedWorkspace
        !TypedWorkspaceFailure

data TypedWorkspaceFailure
    = TypedWorkspaceCheckingRejected !VerificationDriverError
    | TypedWorkspaceProverRejected !FailedVerification

data ModuleTask = ModuleTask
    { moduleTaskOrdinal :: !Natural
    , moduleTaskParsed :: !Parsed.ParsedModule
    , moduleTaskDirectAddresses :: ![ResolvedSourceAddress]
    }

data ModuleCheckResult
    = ModuleCheckSucceeded
        !ResolvedSourceAddress
        !Typed.SealedTypedModule
        !AdmittedTypedModule
    | ModuleCheckRejected
        !AdmittedTypedModule
        !TypedWorkspaceFailure

data ModuleFailureCandidate = ModuleFailureCandidate
    !Natural
    !AdmittedTypedModule
    !TypedWorkspaceFailure

data AdmittedTypedDeclaration = AdmittedTypedDeclaration
    !Semantic.DeclarationSlot
    !Typed.TypedSourceDeclaration

newtype AdmittedTypedModule = AdmittedTypedModule
    [AdmittedTypedDeclaration]

newtype AdmittedTypedWorkspace = AdmittedTypedWorkspace
    [AdmittedTypedModule]

data AdmittedViewError
    = AdmittedDeclarationCountMismatch
        !Int
        !Int
    | AdmittedDeclarationSlotMismatch
        ![Semantic.DeclarationSlot]
        ![Semantic.DeclarationSlot]
    deriving (Show, Eq)

completeAdmittedModule
    :: Typed.IdentifiedModuleInput
    -> AdmittedTypedModule
completeAdmittedModule input =
    AdmittedTypedModule
        (uncurry AdmittedTypedDeclaration <$> expectedDeclarations input)

checkedAdmittedModule
    :: Bool
    -> Typed.IdentifiedModuleInput
    -> Commit.PendingModulePrefix
    -> Either AdmittedViewError AdmittedTypedModule
checkedAdmittedModule requireComplete input prefix = do
    let expected = expectedDeclarations input
        expectedSlots = fst <$> expected
        actualSlots =
            Commit.committedBatchSlot
                <$> Commit.pendingModulePrefixBatches prefix
        admittedCount = length actualSlots
    if requireComplete
        then unless
            (admittedCount == length expected)
            (Left
                (AdmittedDeclarationCountMismatch
                    (length expected)
                    admittedCount))
        else unless
            (admittedCount <= length expected)
            (Left
                (AdmittedDeclarationCountMismatch
                    (length expected)
                    admittedCount))
    unless
        (actualSlots == take admittedCount expectedSlots)
        (Left
            (AdmittedDeclarationSlotMismatch
                (take admittedCount expectedSlots)
                actualSlots))
    pure
        (AdmittedTypedModule
            [ AdmittedTypedDeclaration slot declaration
            | (slot, declaration) <- take admittedCount expected
            ])

expectedDeclarations
    :: Typed.IdentifiedModuleInput
    -> [(Semantic.DeclarationSlot, Typed.TypedSourceDeclaration)]
expectedDeclarations input =
    zipWith
        (\ordinal declaration ->
            ( Semantic.declarationSlot
                (Typed.identifiedModuleOwner input)
                (localDeclarationOrdinal ordinal)
            , declaration
            ))
        [0..]
        (Typed.typedSourceDeclarations
            (Typed.identifiedModuleParsed input))

data StoreValidationMode
    = FreshStoreValidation
    | WarmStoreValidation
    deriving (Show, Eq)

data VerificationSession = VerificationSession
    !Foundation.CheckedFoundation
    !Store.Store
    !(MVar ())

data VerificationSessionError
    = VerificationSessionFoundationError
        !Foundation.FoundationError
    | VerificationSessionStoreError !Store.StoreLifecycleError
    | VerificationSessionTheoryMismatch !Identity.TheoryId !Identity.TheoryId
    deriving (Show)

withVerificationSession
    :: Store.StoreLease
    -> (VerificationSession -> IO value)
    -> IO (Either VerificationSessionError value)
withVerificationSession lease action =
    case Foundation.checkedFoundation of
        Left failure ->
            pure (Left (VerificationSessionFoundationError failure))
        Right foundation -> do
            checkGate <- newMVar ()
            opened <- Store.withOpenStore
                lease
                (Identity.theoryId foundation)
                (\_startup store ->
                    action (VerificationSession foundation store checkGate))
            pure (first VerificationSessionStoreError opened)

-- | Borrow an already-open store while preserving the session's
-- foundation/store identity invariant.  The caller retains ownership of the
-- store lifetime; ordinary hosts should prefer 'withVerificationSession'.
withVerificationSessionUsingStore
    :: Store.Store
    -> (VerificationSession -> IO value)
    -> IO (Either VerificationSessionError value)
withVerificationSessionUsingStore store action =
    case Foundation.checkedFoundation of
        Left failure ->
            pure (Left (VerificationSessionFoundationError failure))
        Right foundation ->
            let expected = Identity.theoryId foundation
                actual = Store.storeTheoryId store
            in if expected == actual
                then do
                    checkGate <- newMVar ()
                    Right
                        <$> action
                            (VerificationSession foundation store checkGate)
                else pure
                    (Left
                        (VerificationSessionTheoryMismatch expected actual))

data CheckRequest = CheckRequest
    { checkSourceGraph :: !ResolvedSourceGraph
    , checkPresentationDemand :: !Felix.PresentationDemand
    , checkStoreValidationMode :: !StoreValidationMode
    , checkModuleJobs :: !EffectiveJobs
    , checkProverJobs :: !EffectiveJobs
    , checkVampire :: !Vampire
    , checkRequestObserver :: !VerificationRequestObserver
    }

data CheckOutcome = CheckOutcome
    { checkVerificationResult :: !VerificationResult
    , checkSlowAtpReport :: !SlowAtpReport
    , checkOperationalReport :: !CheckOperationalReport
    }
    deriving (Show)

data LookupDecisionCounts = LookupDecisionCounts
    { lookupRowsFound :: !Natural
    , lookupMisses :: !Natural
    , lookupBypasses :: !Natural
    }
    deriving (Show, Eq)

data CheckOperationalReport = CheckOperationalReport
    { moduleInstallationDecisions :: !LookupDecisionCounts
    , proofValidationDecisions :: !LookupDecisionCounts
    , declarationValidationDecisions :: !LookupDecisionCounts
    , liveVampireRunsStarted :: !Natural
    , finalPreludeWallNanoseconds :: !Word64
    , sourceParsingWallNanoseconds :: !Word64
    , sourceCompletionMeasurements :: !Felix.SourceCompletionMeasurements
    , moduleCheckingWallNanoseconds :: !Word64
    , importPreparationWork :: !Declaration.ImportWork
    , vampireExecutionMeasurements :: !VampireExecutionReport
    , modulePipelineWorkerLimit :: !Int
    }
    deriving (Show, Eq)

data VerificationOperationalReport = VerificationOperationalReport
    { verificationSourcePlanningMeasurements :: !SourcePlanningMeasurements
    , verificationCheckOperationalReport :: !CheckOperationalReport
    }
    deriving (Show, Eq)

completeVerificationOperationalReport
    :: SourcePlanningMeasurements
    -> CheckOperationalReport
    -> VerificationOperationalReport
completeVerificationOperationalReport =
    VerificationOperationalReport

data VerificationPhaseMeasurements = VerificationPhaseMeasurements
    { measuredFinalPreludeWallNanoseconds :: !Word64
    , measuredSourceParsingWallNanoseconds :: !Word64
    , measuredSourceCompletionMeasurements
        :: !Felix.SourceCompletionMeasurements
    , measuredModuleCheckingWallNanoseconds :: !Word64
    }

data LookupDecision
    = LookupFound
    | LookupMissed
    | LookupBypassed

data OperationalCollector = OperationalCollector
    { collectedModuleInstallationDecisions :: !(IORef LookupDecisionCounts)
    , collectedProofValidationDecisions :: !(IORef LookupDecisionCounts)
    , collectedDeclarationValidationDecisions :: !(IORef LookupDecisionCounts)
    }

emptyLookupDecisionCounts :: LookupDecisionCounts
emptyLookupDecisionCounts = LookupDecisionCounts 0 0 0

newOperationalCollector :: IO OperationalCollector
newOperationalCollector = OperationalCollector
    <$> newIORef emptyLookupDecisionCounts
    <*> newIORef emptyLookupDecisionCounts
    <*> newIORef emptyLookupDecisionCounts

recordLookupDecision
    :: IORef LookupDecisionCounts
    -> LookupDecision
    -> IO ()
recordLookupDecision countsRef decision =
    atomicModifyIORef' countsRef \counts ->
        (incrementDecision decision counts, ())
  where
    incrementDecision lookupDecision counts =
        case lookupDecision of
            LookupFound ->
                counts { lookupRowsFound = lookupRowsFound counts + 1 }
            LookupMissed ->
                counts { lookupMisses = lookupMisses counts + 1 }
            LookupBypassed ->
                counts { lookupBypasses = lookupBypasses counts + 1 }

finishCheckOperationalReport
    :: OperationalCollector
    -> Declaration.ImportWork
    -> Natural
    -> VerificationPhaseMeasurements
    -> VampireExecutionReport
    -> EffectiveJobs
    -> IO CheckOperationalReport
finishCheckOperationalReport collector importWork liveRuns phases vampireMeasurements moduleJobs =
    CheckOperationalReport
        <$> readIORef (collectedModuleInstallationDecisions collector)
        <*> readIORef (collectedProofValidationDecisions collector)
        <*> readIORef (collectedDeclarationValidationDecisions collector)
        <*> pure liveRuns
        <*> pure (measuredFinalPreludeWallNanoseconds phases)
        <*> pure (measuredSourceParsingWallNanoseconds phases)
        <*> pure (measuredSourceCompletionMeasurements phases)
        <*> pure (measuredModuleCheckingWallNanoseconds phases)
        <*> pure importWork
        <*> pure vampireMeasurements
        <*> pure (effectiveJobsValue moduleJobs)

measureMonotonicWall :: IO value -> IO (Word64, value)
measureMonotonicWall action = do
    started <- getMonotonicTimeNSec
    result <- action
    finished <- getMonotonicTimeNSec
    pure (finished - started, result)

checkWorkspace
    :: VerificationSession
    -> CheckRequest
    -> IO (Either VerificationDriverError CheckOutcome)
checkWorkspace = checkWorkspaceUsingModuleStarter Async.async

-- | Inject module-worker creation for lifecycle tests. The starter is called
-- masked and must leave no worker behind if it throws. The supplied action
-- restores the caller's masking state before checking a module.
checkWorkspaceUsingModuleStarter
    :: (forall value. IO value -> IO (Async.Async value))
    -> VerificationSession
    -> CheckRequest
    -> IO (Either VerificationDriverError CheckOutcome)
checkWorkspaceUsingModuleStarter startModule session request =
    withSessionCheckGate session
        (Exception.try (checkWorkspaceThrowing startModule session request))

withSessionCheckGate :: VerificationSession -> IO value -> IO value
withSessionCheckGate (VerificationSession _foundation _store checkGate) =
    Exception.bracket_
        (takeMVar checkGate)
        (putMVar checkGate ())

checkWorkspaceThrowing
    :: (forall value. IO value -> IO (Async.Async value))
    -> VerificationSession
    -> CheckRequest
    -> IO CheckOutcome
checkWorkspaceThrowing
        startModule
        (VerificationSession foundation store _checkGate)
        request = do
    storeCheck <- Store.newStoreCheck store
    importCheck <- Declaration.newImportCheck foundation
    operationalCollector <- newOperationalCollector
    Exception.finally (withVampireExecutor
        (checkProverJobs request)
        (checkVampire request)
        (observeVerificationRequest (checkRequestObserver request))
        \executor -> do
            (preludeWall, prelude) <- measureMonotonicWall
                (withVampireRequestOwner executor \owner -> do
                    preludeResolver <- typedVampireResolver owner 0
                    Typed.acquireFinalPreludeSession
                        importCheck storeCheck foundation preludeResolver
                        >>= either
                            (throwIO . VerificationFinalPreludeReadinessError)
                            pure)
            recordLookupDecision
                (collectedModuleInstallationDecisions operationalCollector)
                (case Typed.finalPreludeAcquisition prelude of
                    Typed.ModuleRootHit -> LookupFound
                    Typed.ModuleRootMiss -> LookupMissed)
            let preludeSyntax =
                    Typed.sealedTypedModuleSyntax
                        (Typed.finalPreludeModule prelude)
                syntaxInputs _source = [preludeSyntax]
            (parsingWall, parseExecution) <- measureMonotonicWall
                (Felix.parseResolvedSourceGraphExecution
                    (Felix.PersistentParsedArtefacts store)
                    (checkPresentationDemand request)
                    (checkSourceGraph request)
                    syntaxInputs
                    (Prelude.rejectOrdinaryPreludeSourceGraph
                        (Typed.finalPreludeSource prelude))
                    >>= either throwParseExecutionError pure)
            let parsed = Felix.parseExecutionWorkspace parseExecution
                parsePresentation =
                    Felix.parseExecutionPresentation parseExecution
                actualDemand = case parsePresentation of
                    Felix.ParseWithoutPresentation -> Felix.NoPresentation
                    Felix.ParseWithPresentation{} ->
                        Felix.HtmlPresentationRequested
            unless (actualDemand == checkPresentationDemand request)
                (throwIO
                    (VerificationPresentationDemandMismatch
                        (checkPresentationDemand request)
                        actualDemand))
            (checkingWall, admittedResult) <- measureMonotonicWall
                (checkTypedWorkspace
                    startModule
                    importCheck
                    storeCheck
                    foundation
                    prelude
                    executor
                    (checkModuleJobs request)
                    (checkStoreValidationMode request)
                    operationalCollector
                    parsed)
            slowReport <- vampireExecutorSlowAtpReport executor
            liveRuns <- vampireExecutorLiveRunsStarted executor
            vampireMeasurements <- vampireExecutorExecutionReport executor
            importWork <- Declaration.importCheckWork importCheck
            operationalReport <-
                finishCheckOperationalReport
                    operationalCollector
                    importWork
                    liveRuns
                    (VerificationPhaseMeasurements
                        preludeWall
                        parsingWall
                        (Felix.parseExecutionMeasurements parseExecution)
                        checkingWall)
                    vampireMeasurements
                    (checkModuleJobs request)
            let result =
                    case admittedResult of
                        TypedWorkspaceRejected admitted failure ->
                            let report = admittedWorkspaceReport admitted
                            in case failure of
                                TypedWorkspaceCheckingRejected checkingFailure ->
                                    VerificationCheckingFailure
                                        report checkingFailure
                                TypedWorkspaceProverRejected proverFailure ->
                                    VerificationFailure report proverFailure
                        TypedWorkspaceSucceeded admitted sealedByAddress ->
                            let report = admittedWorkspaceReport admitted
                            in case parsePresentation of
                                Felix.ParseWithoutPresentation ->
                                    completedResult
                                        report
                                        PresentationNotRequested
                                Felix.ParseWithPresentation sidecar ->
                                    case
                                        HtmlExport.htmlPresentationFromCheckedWorkspace
                                            (Typed.finalPreludeModule prelude)
                                            sealedByAddress
                                            parsed
                                            sidecar of
                                        Left failure ->
                                            VerificationCheckingFailure
                                                report
                                                (VerificationPresentationInvariantError
                                                    failure)
                                        Right presentation ->
                                            completedResult
                                                report
                                                (PresentationAvailable
                                                    (VerificationPresentation
                                                        presentation))
            pure (CheckOutcome result slowReport operationalReport))
        (Declaration.finishFormationReport importCheck)
  where
    throwParseExecutionError = \case
        Felix.ParseExecutionWorkspaceError failure ->
            throwIO (VerificationWorkspaceError failure)
        Felix.ParseExecutionStoreFailure failure ->
            throwIO (VerificationStoreFailure failure)
        Felix.ParseExecutionArtefactIntegrityFailure source failure ->
            throwIO
                (VerificationParsedArtefactIntegrityError source failure)

checkTypedWorkspace
    :: (forall value. IO value -> IO (Async.Async value))
    -> Declaration.ImportCheck
    -> Store.StoreCheck
    -> Foundation.CheckedFoundation
    -> Typed.FinalPreludeSession
    -> VampireExecutor
    -> EffectiveJobs
    -> StoreValidationMode
    -> OperationalCollector
    -> ParsedSourceWorkspace
    -> IO TypedWorkspaceOutcome
checkTypedWorkspace
        startModule
        importCheck
        storeCheck
        foundation
        prelude
        executor
        selectedJobs
        validationMode
        operationalCollector
        workspace = do
    let modules =
            zipWith
                makeTask
                [1..]
                (toList
                    (parsedWorkspaceImportedBeforeImporter workspace))
        rootAddress =
            Parsed.parsedModuleAddress
                (parsedWorkspaceRootModule workspace)
    -- Cleanup covers acquisition as well as execution. Retire completed
    -- workers as the scheduler consumes their results.
    Exception.bracket
        (newIORef Map.empty)
        (\workers -> readIORef workers >>= cancelModuleCheckers)
        \workers ->
            scheduleModules workers rootAddress modules Map.empty Map.empty Nothing
  where
    workerBound = effectiveJobsValue selectedJobs

    makeTask ordinal parsed =
        ModuleTask
            { moduleTaskOrdinal = ordinal
            , moduleTaskParsed = parsed
            , moduleTaskDirectAddresses =
                nubOrd
                    (Parsed.parsedImportedAddress
                        <$> Parsed.parsedModuleImports parsed)
            }

    scheduleModules
        workers
        rootAddress
        pending
        sealedByAddress
        admittedByOrdinal
        candidate = do
            pending' <-
                startReadyModules
                    workers
                    pending
                    sealedByAddress
                    candidate
            running <- readIORef workers
            if Map.null running
                then case candidate of
                    Just selected
                        | any
                            (\task ->
                                moduleTaskOrdinal task
                                    < candidateOrdinal selected)
                            pending' ->
                                throwIO
                                    (VerificationModuleSchedulerInvariant
                                        "an earlier module is not terminal")
                        | otherwise ->
                            pure
                                (TypedWorkspaceRejected
                                    (admittedWorkspaceThrough
                                        admittedByOrdinal
                                        selected)
                                    (candidateFailure selected))
                    Nothing
                        | null pending' -> do
                            unless
                                (Map.member rootAddress sealedByAddress)
                                (throwIO
                                    (VerificationMissingRootModule
                                        rootAddress))
                            pure
                                (TypedWorkspaceSucceeded
                                    (completeAdmittedWorkspace
                                        admittedByOrdinal)
                                    sealedByAddress)
                        | otherwise ->
                            throwIO
                                (VerificationModuleSchedulerInvariant
                                    "no ready module and no running module")
                else do
                    (_completedAsync, (ordinal, completed)) <-
                        Async.waitAny (Map.elems running)
                    let runningWithoutCompleted =
                            Map.delete ordinal running
                    modifyIORef' workers (Map.delete ordinal)
                    case completed of
                        Left fatal ->
                            Exception.throwIO fatal
                        Right (ModuleCheckSucceeded
                                address sealed admittedModule) ->
                            scheduleModules
                                workers
                                rootAddress
                                pending'
                                (Map.insert address sealed sealedByAddress)
                                (Map.insert
                                    ordinal
                                    admittedModule
                                    admittedByOrdinal)
                                candidate
                        Right (ModuleCheckRejected
                                admittedModule failure) -> do
                            let selected =
                                    chooseEarlierFailure
                                        candidate
                                        (ModuleFailureCandidate
                                            ordinal
                                            admittedModule
                                            failure)
                                cutoff = candidateOrdinal selected
                                later =
                                    Map.filterWithKey
                                        (\runningOrdinal _async ->
                                            runningOrdinal > cutoff)
                                        runningWithoutCompleted
                            cancelModuleCheckers later
                            modifyIORef' workers (`Map.difference` later)
                            scheduleModules
                                workers
                                rootAddress
                                pending'
                                sealedByAddress
                                admittedByOrdinal
                                (Just selected)

    startReadyModules
        workers
        pending
        sealedByAddress
        candidate = do
            running <- readIORef workers
            if Map.size running >= workerBound
                then pure pending
                else case extractFirstReady candidate sealedByAddress pending of
                    Nothing ->
                        pure pending
                    Just (task, remaining) -> do
                        -- Register each returned handle before cancellation
                        -- can interrupt the scheduler again.
                        Exception.mask \restore -> do
                            checker <- startModule (restore do
                                completed <-
                                    (Exception.try
                                        (checkModule task sealedByAddress)
                                        :: IO
                                            (Either
                                                Exception.SomeException
                                                ModuleCheckResult))
                                pure (moduleTaskOrdinal task, completed))
                            modifyIORef' workers
                                (Map.insert (moduleTaskOrdinal task) checker)
                        startReadyModules
                            workers
                            remaining
                            sealedByAddress
                            candidate

    checkModule task sealedByAddress =
      withVampireRequestOwner executor \requestOwner -> do
        let parsed = moduleTaskParsed task
            source = Parsed.parsedModuleResolved parsed
            address = Parsed.parsedModuleAddress parsed
        direct <-
            traverse
                (\directAddress ->
                    maybe
                        (throwIO
                            (VerificationMissingImportedModule
                                directAddress))
                        pure
                        (Map.lookup directAddress sealedByAddress))
                (moduleTaskDirectAddresses task)
        resolver <-
            typedVampireResolver
                requestOwner
                (moduleTaskOrdinal task)
        input <-
            either
                (throwIO . VerificationTypedInputError source)
                pure =<< Typed.typedModuleInput
                    importCheck
                    foundation
                    (Typed.finalPreludeReadiness prelude)
                    resolver
                    parsed
                    direct
        loadCachedModule parsed (Typed.typedModulePreparedImports input) >>= \case
            Just sealed -> do
                pure
                    (ModuleCheckSucceeded
                        address
                        sealed
                        (completeAdmittedModule
                            (Typed.identifiedPhysicalModule parsed)))
            Nothing -> do
                validationResult <-
                    Exception.catch
                        (runEff
                            (Error.runErrorNoCallStack @Store.StoreFailure
                                (runSelectedValidationCache
                                    (Typed.runTypedModuleEff input))))
                        (\failure ->
                            throwIO
                                (VerificationValidationIntegrityError
                                    source
                                    failure))
                typedResult <-
                    either
                        (throwIO . VerificationStoreFailure)
                        pure
                        validationResult
                case typedResult of
                    Typed.TypedModuleOpenFailed err ->
                        throwIO (VerificationTypedOpenError source err)
                    Typed.TypedModuleFailed err prefix -> do
                        let driverFailure =
                                VerificationTypedModuleError
                                    source err prefix
                        case classifyTypedModuleFailure err of
                            TypedIntegrityFailure ->
                                throwIO driverFailure
                            TypedCheckingRejection ->
                                reportFailure
                                    parsed
                                    prefix
                                    (TypedWorkspaceCheckingRejected
                                        driverFailure)
                            TypedVerificationRejection failed ->
                                reportFailure
                                    parsed
                                    prefix
                                    (TypedWorkspaceProverRejected failed)
                            TypedProverFailure failed ->
                                reportFailure
                                    parsed
                                    prefix
                                    (TypedWorkspaceProverRejected failed)
                    Typed.TypedModuleSucceeded completed -> do
                        admittedModule <-
                            either
                                (throwIO
                                    . VerificationAdmittedViewError source)
                                pure
                                (checkedAdmittedModule
                                    True
                                    (Typed.identifiedPhysicalModule parsed)
                                    (Typed.completedTypedModulePrefix completed))
                        sealed <- persistCompleted
                            (Typed.identifiedPhysicalModule parsed)
                            completed
                        pure
                            (ModuleCheckSucceeded
                                address sealed admittedModule)

    reportFailure parsed prefix failure = do
        let source = Parsed.parsedModuleResolved parsed
        admittedModule <-
            either
                (throwIO . VerificationAdmittedViewError source)
                pure
                (checkedAdmittedModule
                    False
                    (Typed.identifiedPhysicalModule parsed)
                    prefix)
        Store.writePendingModulePrefix storeCheck prefix
            >>= either
                (throwIO . VerificationStoreFailure)
                pure
        pure (ModuleCheckRejected admittedModule failure)

    runSelectedValidationCache =
        case validationMode of
            FreshStoreValidation ->
                ValidationCache.runValidationCacheWith
                    (\_key -> do
                        liftIO
                            (recordLookupDecision
                                (collectedProofValidationDecisions
                                    operationalCollector)
                                LookupBypassed)
                        pure Nothing)
                    (\_key -> do
                        liftIO
                            (recordLookupDecision
                                (collectedDeclarationValidationDecisions
                                    operationalCollector)
                                LookupBypassed)
                        pure Nothing)
            WarmStoreValidation ->
                runStoreValidationCache

    runStoreValidationCache
        :: (Error Store.StoreFailure :> es, IOE :> es)
        => Eff (ValidationCache.ValidationCache : es) value
        -> Eff es value
    runStoreValidationCache =
        ValidationCache.runValidationCacheWith
            (\key -> do
                found <- liftIO
                    (Store.loadProofValidation storeCheck key)
                    >>= either Error.throwError_ pure
                liftIO
                    (recordLookupDecision
                        (collectedProofValidationDecisions operationalCollector)
                        (maybe LookupMissed (const LookupFound) found))
                pure found)
            (\key -> do
                found <- liftIO
                    (Store.loadDeclarationValidation storeCheck key)
                    >>= either Error.throwError_ pure
                liftIO
                    (recordLookupDecision
                        (collectedDeclarationValidationDecisions
                            operationalCollector)
                        (maybe LookupMissed (const LookupFound) found))
                pure found)

    persistCompleted input completed = do
        let sealed = Typed.completedTypedModuleSealed completed
        artefactKey <-
            either
                (throwIO . VerificationModuleArtefactKeyError)
                pure
                (Semantic.moduleArtefactKey
                    (Typed.identifiedModuleOwner input)
                    (Parsed.identifiedParsedModuleId
                        (Typed.identifiedModuleParsed input))
                    (Semantic.semanticInterfaceDirectInputs
                        (Typed.sealedTypedModuleSemantic sealed))
                    (Identity.theoryId foundation))
        Typed.publishCompletedModule storeCheck artefactKey completed
            >>= either (throwIO . VerificationStoreFailure) pure

    loadCachedModule parsed prepared =
        case validationMode of
            WarmStoreValidation -> do
                let owner =
                        Typed.identifiedModuleOwner
                            (Typed.identifiedPhysicalModule parsed)
                    directSemantic = Declaration.preparedImportIds prepared
                artefactKey <-
                    either
                        (throwIO . VerificationModuleArtefactKeyError)
                        pure
                        (Semantic.moduleArtefactKey
                            owner
                            (Parsed.identifiedParsedModuleId
                                (Typed.identifiedModuleParsed
                                    (Typed.identifiedPhysicalModule parsed)))
                            directSemantic
                            (Identity.theoryId foundation))
                loaded <-
                    Store.loadCachedModuleCandidate
                        storeCheck
                        artefactKey
                        (Syntax.moduleSyntaxAssertedId
                            (Parsed.parsedModuleSyntaxInterface parsed))
                case loaded of
                    Left failure ->
                        throwIO (VerificationStoreFailure failure)
                    Right Nothing -> do
                        recordLookupDecision
                            (collectedModuleInstallationDecisions
                                operationalCollector)
                            LookupMissed
                        pure Nothing
                    Right (Just installation) -> do
                        recordLookupDecision
                            (collectedModuleInstallationDecisions
                                operationalCollector)
                            LookupFound
                        Typed.cachedSealedTypedModule prepared installation >>= either
                            (throwIO . VerificationTypedCachedModuleError
                                (Parsed.parsedModuleResolved parsed))
                            (pure . Just)
            FreshStoreValidation -> do
                recordLookupDecision
                    (collectedModuleInstallationDecisions operationalCollector)
                    LookupBypassed
                pure Nothing

    taskMayStart candidate sealedByAddress task =
        maybe True
            (moduleTaskOrdinal task <)
            (candidateOrdinal <$> candidate)
            && all
                (`Map.member` sealedByAddress)
                (moduleTaskDirectAddresses task)

    extractFirstReady candidate sealedByAddress = go []
      where
        go _before [] = Nothing
        go before (task : after)
            | taskMayStart candidate sealedByAddress task =
                Just (task, reverse before <> after)
            | otherwise =
                go (task : before) after

    chooseEarlierFailure Nothing incoming = incoming
    chooseEarlierFailure (Just current) incoming
        | candidateOrdinal incoming < candidateOrdinal current = incoming
        | otherwise = current

    candidateOrdinal (ModuleFailureCandidate ordinal _admitted _failure) =
        ordinal

    candidateFailure (ModuleFailureCandidate _ordinal _admitted failure) =
        failure

    candidateAdmitted (ModuleFailureCandidate _ordinal admitted _failure) =
        admitted

    completeAdmittedWorkspace admittedByOrdinal =
        AdmittedTypedWorkspace
            ( completeAdmittedModule (Typed.finalPreludeInput prelude)
                : fmap snd (Map.toAscList admittedByOrdinal)
            )

    admittedWorkspaceThrough admittedByOrdinal selected =
        let cutoff = candidateOrdinal selected
            earlier = Map.filterWithKey
                (\ordinal _admitted -> ordinal < cutoff)
                admittedByOrdinal
        in AdmittedTypedWorkspace
            ( completeAdmittedModule (Typed.finalPreludeInput prelude)
                : ( fmap snd (Map.toAscList earlier)
                        <> [candidateAdmitted selected]
                  )
            )

    -- Like withAsync, finish joining each worker even if cancellation repeats.
    -- Its request-owner cleanup must complete before the executor/store close.
    cancelModuleCheckers = traverse_ Async.uninterruptibleCancel . Map.elems

data TypedFailureClassification
    = TypedCheckingRejection
    | TypedVerificationRejection !FailedVerification
    | TypedProverFailure !FailedVerification
    | TypedIntegrityFailure

-- | Classify failures at the typed checking boundary conservatively.
--
-- Only source elaboration and recognized prover outcomes may retain an
-- admitted source report.  Every declaration/sealing invariant, including a
-- future constructor not explicitly recognized below, remains fatal.
classifyTypedModuleFailure
    :: Typed.TypedModuleFailure
    -> TypedFailureClassification
classifyTypedModuleFailure = \case
    Typed.TypedActionFailed path ->
        case Typed.typedPathErrorDisposition path of
            Proof.ProofSourceRejection -> TypedCheckingRejection
            Proof.ProofInfrastructureFailure -> TypedIntegrityFailure
    Typed.TypedDeclarationFailed failure
        | Just (location, resolution, preparation) <- Declaration.locatedVampireFailure failure ->
            classifyTypedProverFailure location resolution preparation
                (Declaration.declarationRecordObligations failure)
    _failure ->
        TypedIntegrityFailure

classifyTypedProverFailure
    :: Location
    -> FailedVampireResolution
    -> [Preparation.PreparationStatistics]
    -> [Obligation.ObligationContext]
    -> TypedFailureClassification
classifyTypedProverFailure location resolution preparation obligations =
    let failed = FailedVerification location resolution preparation obligations
    in if failedVerificationIsLogicalRejection failed
        then TypedVerificationRejection failed
        else TypedProverFailure failed

typedVampireResolver
    :: VampireRequestOwner
    -> Natural
    -> IO Declaration.VampireResolver
typedVampireResolver
        requestOwner moduleOrdinal = do
    localOrdinalRef <- newIORef 1
    let reserve requests = do
            let batchSize = NonEmpty.length requests
                ordinalCount = fromIntegral batchSize
            firstOrdinal <- atomicModifyIORef' localOrdinalRef
                (\current -> (current + ordinalCount, current))
            let positions =
                    NonEmpty.fromList
                        [ workPosition moduleOrdinal ordinal
                        | ordinal <-
                            [firstOrdinal .. firstOrdinal + ordinalCount - 1]
                        ]
            pure positions
        submit requests = do
            positions <- reserve requests
            traverse
                (\(position, Declaration.VampireSubmission location request) ->
                    submitVampireRequest
                        requestOwner position location request)
                (NonEmpty.zip positions requests)
    pure (Declaration.vampireSubmissionResolver submit)

admittedWorkspaceReport
    :: AdmittedTypedWorkspace
    -> VerificationReport
admittedWorkspaceReport (AdmittedTypedWorkspace modules) =
    VerificationReport
        { verificationDirectEscapes =
            concatMap admittedModuleEscapes modules
        }

admittedModuleEscapes
    :: AdmittedTypedModule
    -> [ReportedEscape]
admittedModuleEscapes (AdmittedTypedModule declarations) =
    concatMap admittedDeclarationEscapes declarations

admittedDeclarationEscapes
    :: AdmittedTypedDeclaration
    -> [ReportedEscape]
admittedDeclarationEscapes
        (AdmittedTypedDeclaration _slot declaration) =
    axiomEscape <> proofEscapes
  where
    axiomEscape =
        case Typed.typedSourceDeclarationHead declaration of
            Raw.BlockAxiom location _title _marker _axiom ->
                [ReportedEscape ReportedSourceAxiom location]
            _ ->
                []
    proofEscapes =
        maybe [] omittedProofEscapes
            (Typed.typedSourceDeclarationProof declaration)

omittedProofEscapes :: Raw.Proof -> [ReportedEscape]
omittedProofEscapes = \case
    Raw.Omitted location ->
        [ReportedEscape ReportedOmitted location]
    Raw.Qed{} ->
        []
    Raw.Contradiction{} ->
        []
    Raw.ByCase _location cases ->
        concatMap (omittedProofEscapes . Raw.caseProof) cases
    Raw.ByContradiction _location proof ->
        omittedProofEscapes proof
    Raw.BySetInduction _location _term proof ->
        omittedProofEscapes proof
    Raw.ByOrdInduction _location proof ->
        omittedProofEscapes proof
    Raw.ByStructuralInduction _location _focus cases ->
        concatMap (omittedProofEscapes . Raw.namedCaseProof) cases
    Raw.Assume _location _intro _statement proof ->
        omittedProofEscapes proof
    Raw.Fix _location _binders _condition proof ->
        omittedProofEscapes proof
    Raw.Calc _location _quantifier _calculation proof ->
        omittedProofEscapes proof
    Raw.TakeVar _location _variables _bound _statement _justification proof ->
        omittedProofEscapes proof
    Raw.TakeTyped _location _variables _coreType _statement _justification proof ->
        omittedProofEscapes proof
    Raw.TakeNoun _location _noun _justification proof ->
        omittedProofEscapes proof
    Raw.Have _location _intro _statement _justification proof ->
        omittedProofEscapes proof
    Raw.Since
            _premiseLocation _premise _premiseJustification
            _claimLocation _claim _claimJustification proof ->
        omittedProofEscapes proof
    Raw.Suffices _location _statement _justification proof ->
        omittedProofEscapes proof
    Raw.Subclaim _location _statement subproof continuation ->
        omittedProofEscapes subproof <> omittedProofEscapes continuation
    Raw.Define _location _variable _expression proof ->
        omittedProofEscapes proof
    Raw.DefineTyped _location _variable _coreType _body proof ->
        omittedProofEscapes proof
    Raw.DefineFunction
            _location _function _argument _value _domainVariable _domain
            proof ->
        omittedProofEscapes proof
    Raw.DefineFunctionLocal
            _location _function _argument _domain _target _ruleVariable
            _rules proof ->
        omittedProofEscapes proof

completedResult
    :: VerificationReport
    -> PresentationDisposition
    -> VerificationResult
completedResult report presentation
    | any ((== ReportedOmitted) . reportedEscapeKind)
        (verificationDirectEscapes report) =
            CompletedWithExplicitGaps report presentation
    | otherwise =
        VerificationCompleted report presentation
