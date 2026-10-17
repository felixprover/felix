{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Felix.Provers
    ( Vampire
    , vampire
    , VampireTaskMode(..)
    , VampireStatus(..)
    , AtpIndeterminateReason(..)
    , CanonicalAtpOutcome(..)
    , CanonicalAtpRejection(..)
    , VampireProtocolError(..)
    , classifyVampireProtocol
    , vampireStatusParser
    , TimeLimit(..)
    , MemoryLimit(..)
    , defaultTimeLimit
    , defaultMemoryLimit
    , ProverStream(..)
    , ProverOutputStream(..)
    , ProverProcessError(..)
    , VerificationDialect(..)
    , PreparedVerificationRequest
    , preparedVerificationDialect
    , preparedVerificationText
    , preparedVerificationBytes
    , preparedVerificationByteCount
    , preparedVerificationRequestId
    , PreparedTypedProverTask
    , prepareTypedProverTask
    , preparedTypedProverLogicalProblem
    , preparedTypedProverRequest
    , VampireFailure(..)
    , VampireResolution
    , vampireResolutionRequestId
    , vampireResolutionWorkPosition
    , vampireResolutionAcceptedRequestId
    , FailedVampireResolution
    , vampireResolutionFailure
    , failedVampireResolutionRequestId
    , failedVampireResolutionWorkPosition
    , failedVampireResolutionFailure
    , failedVampireResolutionDiagnostic
    , renderVampireLiveTaskReference
    , rejectedVampireResolution
    , processFailedVampireResolution
    , runPreparedTypedProver
    , runPreparedTypedProverWithObserver
    , EffectiveJobs
    , effectiveJobs
    , effectiveJobsValue
    , selectEffectiveJobs
    , selectAutomaticJobs
    , WorkPosition
    , workPosition
    , workPositionModuleOrdinal
    , workPositionLocalRequestOrdinal
    , VampireExecutor
    , VampireExecutorFault
    , VampireRequestOwner
    , VampireHandle
    , VampireTerminal(..)
    , VampireCompletion
    , vampireCompletionRequestId
    , vampireCompletionTerminal
    , AtpDuration
    , atpDurationNanoseconds
    , SlowAtpOutcome(..)
    , SlowAtpTask(..)
    , SlowAtpReport(..)
    , slowAtpOmittedTaskCount
    , VampireExecutionReport(..)
    , withVampireExecutor
    , withVampireExecutorUsingClock
    , VampireExecutorRuntime(..)
    , defaultVampireExecutorRuntime
    , withVampireExecutorUsingRuntime
    , withVampireRequestOwner
    , submitVampireRequest
    , awaitVampireRequest
    , awaitPreparedVampireRequest
    , cancelVampireRequest
    , runPreparedTypedProverWithExecutor
    , vampireExecutorSlowAtpReport
    , vampireExecutorExecutionReport
    , vampireExecutorLiveRunsStarted
    ) where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Backend.Problem
import Felix.Checking.Backend.Tptp
import Felix.Provers.Pipes (withVampirePipes)
import Felix.Provers.Timer qualified as Timer

import Control.Concurrent.STM
    ( STM
    , TBQueue
    , TMVar
    , TVar
    , atomically
    , check
    , lengthTBQueue
    , modifyTVar'
    , newEmptyTMVarIO
    , newTBQueueIO
    , newTVarIO
    , orElse
    , readTMVar
    , readTBQueue
    , readTVar
    , readTVarIO
    , retry
    , throwSTM
    , tryPutTMVar
    , writeTBQueue
    , writeTVar
    )
import Control.Concurrent (rtsSupportsBoundThreads, threadDelay, throwTo)
import Control.Exception
    ( IOException
    , SomeException
    , displayException
    , fromException
    )
import Control.Exception qualified as Exception
import Control.Monad (replicateM_, unless, when)
import Data.ByteString qualified as ByteString
import Data.IntMap.Strict qualified as IntMap
import Data.IORef
    ( IORef
    , atomicModifyIORef'
    , newIORef
    , modifyIORef'
    , readIORef
    , writeIORef
    )
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Ord (Down(..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Data.Text.Encoding.Error qualified as TextEncodingError
import Numeric.Natural (Natural)
import Felix.Report.Diagnostic
import Felix.Report.Location (Location, locationToText)
import System.Exit (ExitCode(..))
import System.Posix.Signals (sigKILL, signalProcessGroup)
import System.Posix.Types (ProcessGroupID)
import System.Process
    ( ProcessHandle
    , getProcessExitCode
    , getPid
    , waitForProcess
    )
import Prettyprinter (Doc)
import Text.Megaparsec hiding (failure, label)
import Text.Megaparsec.Char qualified as Char
import UnliftIO.Async
    ( Async
    , AsyncCancelled(..)
    , async
    , asyncWithUnmask
    , asyncThreadId
    , waitCatch
    , waitCatchSTM
    )
import UnliftIO.Exception qualified as UnliftIO

data Vampire = Vampire
    { vampireExecutable :: FilePath
    , vampireTimeLimit :: TimeLimit
    , vampireMemoryLimit :: MemoryLimit
    }
    deriving (Show, Eq)

newtype TimeLimit = Seconds Word64 deriving (Show, Eq)
newtype MemoryLimit = Megabytes Word64 deriving (Show, Eq)

defaultTimeLimit :: TimeLimit
defaultTimeLimit = Seconds 10

defaultMemoryLimit :: MemoryLimit
defaultMemoryLimit = Megabytes 5000

vampire :: FilePath -> TimeLimit -> MemoryLimit -> Vampire
vampire = Vampire

vampireArguments :: Vampire -> [String]
vampireArguments Vampire{..} =
    [ "--input_syntax", "tptp"
    , "--mode", "casc"
    , "--time_limit", toSeconds vampireTimeLimit
    , "--memory_limit", toMegabytes vampireMemoryLimit
    , "--cores", "2"
    ]

-- | A strictly positive invocation-local bound for module pipelines and
-- top-level Vampire invocations.
newtype EffectiveJobs = EffectiveJobs Int
    deriving (Show, Eq, Ord)

effectiveJobs :: Int -> Maybe EffectiveJobs
effectiveJobs amount
    | amount > 0 = Just (EffectiveJobs amount)
    | otherwise = Nothing

effectiveJobsValue :: EffectiveJobs -> Int
effectiveJobsValue (EffectiveJobs amount) = amount

-- | Select the prover worker bound, with processor discovery injected for focused
-- testing.  Asynchronous cancellation is never mistaken for failed discovery.
selectEffectiveJobs
    :: Maybe EffectiveJobs
    -> IO Int
    -> IO EffectiveJobs
selectEffectiveJobs override detectProcessors =
    case override of
        Just selected ->
            pure selected
        Nothing -> snd <$> selectAutomaticJobs detectProcessors

-- | Automatic module and prover limits from logical processors, independently
-- of explicit RTS settings. N uses the same rule as M in runtime-defaults.c.
selectAutomaticJobs :: IO Int -> IO (EffectiveJobs, EffectiveJobs)
selectAutomaticJobs detectProcessors = do
    detectedResult <- UnliftIO.tryAny detectProcessors
    let detected = either (const 1) (max 1) detectedResult
        -- Clamp before multiplication to keep the arithmetic bounded.
        modules = max 1 (2 * min 24 detected `div` 3)
        provers = max 1 (2 * min 18 detected `div` 9)
    pure (EffectiveJobs modules, EffectiveJobs provers)

-- | Stable runtime diagnostic position.  It is deliberately separate from
-- request, validation, cache, and mathematical identities.
data WorkPosition = WorkPosition !Natural !Natural
    deriving (Show, Eq, Ord)

workPosition :: Natural -> Natural -> WorkPosition
workPosition = WorkPosition

workPositionModuleOrdinal :: WorkPosition -> Natural
workPositionModuleOrdinal (WorkPosition moduleOrdinal _localOrdinal) =
    moduleOrdinal

workPositionLocalRequestOrdinal :: WorkPosition -> Natural
workPositionLocalRequestOrdinal (WorkPosition _moduleOrdinal localOrdinal) =
    localOrdinal

toSeconds :: TimeLimit -> String
toSeconds (Seconds secs) = show secs

toMegabytes :: MemoryLimit -> String
toMegabytes (Megabytes mbs) = show mbs

data VampireTaskMode
    = DirectTask
    | IndirectTask
    deriving (Show, Eq)

data VampireStatus
    = StatusTheorem
    | StatusCounterSatisfiable
    | StatusContradictoryAxioms
    | StatusTimeout
    | StatusResourceOut
    | StatusGaveUp
    | StatusUnknown
    | UnsupportedStatus Text
    deriving (Show, Eq)

data AtpIndeterminateReason
    = AtpTimedOut
    | AtpResourceOut
    | AtpGaveUp
    | AtpUnknown
    deriving (Show, Eq, Ord)

data CanonicalAtpOutcome
    = Proved
    | Counterexample
    | ContradictoryInput
    | Indeterminate !(NonEmpty AtpIndeterminateReason)
    deriving (Show, Eq, Ord)

-- | The closed non-accepting subset of canonical ATP outcomes.  Protocol
-- disagreement is represented separately from a semantic non-proof, while an
-- accepting result is unrepresentable here.
data CanonicalAtpRejection
    = RejectedCounterexample
    | RejectedContradictoryInput
    | RejectedIndeterminate !(NonEmpty AtpIndeterminateReason)
    deriving (Show, Eq)

data VampireProtocolError
    = UnsuccessfulVampireExit ExitCode
    | UnsupportedVampireStatuses (Set Text)
    | MalformedVampireStatusLines (Set Text)
    | MissingVampireOutcome
    | ConflictingTerminalOutcomes (Set CanonicalAtpOutcome)
    deriving (Show, Eq)

data CompleteCapturedStreams = CompleteCapturedStreams
    { completedStdout :: !Text
    , completedStderr :: !Text
    }
    deriving (Show, Eq)

data CompletedTranscript = CompletedTranscript
    { completedExitCode :: !ExitCode
    , completedStreams :: !CompleteCapturedStreams
    }
    deriving (Show, Eq)

data PartialCapturedStreams = PartialCapturedStreams
    { partialStdout :: !ByteString.ByteString
    , partialStderr :: !ByteString.ByteString
    }
    deriving (Eq)

instance Show PartialCapturedStreams where
    showsPrec precedence PartialCapturedStreams{..} =
        showParen (precedence > applicationPrecedence)
            ( showString "PartialCapturedStreams "
                . shows
                    ( ByteString.length partialStdout
                    , ByteString.length partialStderr
                    )
            )

data BoundedBytes = BoundedBytes
    { boundedBytesOriginalCount :: !Int
    , boundedBytesRetained :: !ByteString.ByteString
    , boundedBytesTruncated :: !Bool
    }
    deriving (Eq)

instance Show BoundedBytes where
    showsPrec precedence BoundedBytes{..} =
        showParen (precedence > applicationPrecedence)
            ( showString "BoundedBytes "
                . shows
                    ( boundedBytesOriginalCount
                    , ByteString.length boundedBytesRetained
                    , boundedBytesTruncated
                    )
            )

data BoundedCapturedStreams = BoundedCapturedStreams
    { boundedStdout :: !BoundedBytes
    , boundedStderr :: !BoundedBytes
    }
    deriving (Show, Eq)

applicationPrecedence :: Int
applicationPrecedence = 10

-- | Classify parsed Vampire statuses without depending on stream or line order.
classifyVampireProtocol
    :: VampireTaskMode
    -> ExitCode
    -> [VampireStatus]
    -> Either VampireProtocolError CanonicalAtpOutcome
classifyVampireProtocol mode exitCode statuses =
    if not (Set.null unsupported)
        then Left (UnsupportedVampireStatuses unsupported)
        else case exitCode of
            ExitFailure _
                | Set.null terminalOutcomes
                , Just reasons <- nonemptyIndeterminateReasons ->
                    Right (Indeterminate reasons)
                | otherwise ->
                    Left (UnsuccessfulVampireExit exitCode)
            ExitSuccess ->
                classifyOutcomes terminalOutcomes nonemptyIndeterminateReasons
  where
    unsupported =
        Set.fromList
            [ status
            | UnsupportedStatus status <- statuses
            ]
    terminalOutcomes =
        Set.fromList
            [ outcome
            | status <- statuses
            , Just outcome <- [vampireStatusTerminalOutcome mode status]
            ]
    nonemptyIndeterminateReasons =
        NonEmpty.nonEmpty
            (Set.toAscList
                (Set.fromList
                    [ reason
                    | status <- statuses
                    , Just reason <- [vampireStatusIndeterminateReason status]
                    ]))

classifyOutcomes
    :: Set CanonicalAtpOutcome
    -> Maybe (NonEmpty AtpIndeterminateReason)
    -> Either VampireProtocolError CanonicalAtpOutcome
classifyOutcomes terminalOutcomes indeterminateReasons =
    case Set.toList terminalOutcomes of
        [] ->
            maybe
                (Left MissingVampireOutcome)
                (Right . Indeterminate)
                indeterminateReasons
        [outcome] ->
            Right outcome
        _ ->
            Left (ConflictingTerminalOutcomes terminalOutcomes)

vampireStatusTerminalOutcome
    :: VampireTaskMode
    -> VampireStatus
    -> Maybe CanonicalAtpOutcome
vampireStatusTerminalOutcome mode = \case
    StatusTheorem ->
        Just Proved
    StatusCounterSatisfiable ->
        Just Counterexample
    StatusContradictoryAxioms ->
        Just case mode of
            DirectTask -> ContradictoryInput
            IndirectTask -> Proved
    StatusTimeout -> Nothing
    StatusResourceOut -> Nothing
    StatusGaveUp -> Nothing
    StatusUnknown -> Nothing
    UnsupportedStatus{} ->
        Nothing

vampireStatusIndeterminateReason
    :: VampireStatus
    -> Maybe AtpIndeterminateReason
vampireStatusIndeterminateReason = \case
    StatusTimeout -> Just AtpTimedOut
    StatusResourceOut -> Just AtpResourceOut
    StatusGaveUp -> Just AtpGaveUp
    StatusUnknown -> Just AtpUnknown
    StatusTheorem -> Nothing
    StatusCounterSatisfiable -> Nothing
    StatusContradictoryAxioms -> Nothing
    UnsupportedStatus{} -> Nothing

data VerificationDialect
    = VerificationFof
    | VerificationTh0
    deriving (Show, Eq)

data PreparedVerificationRequest = PreparedVerificationRequest
    { preparedVerificationDialect :: !VerificationDialect
    , preparedVerificationMode :: !VampireTaskMode
    , preparedVerificationInput :: !ByteString.ByteString
    , preparedVerificationIdentity :: !Authority.PreparedRequestId
    }
    deriving (Eq)

-- | Decode the one canonical serialized request only at a textual boundary.
-- Prepared requests deliberately do not retain an equivalent 'Text' copy.
preparedVerificationText :: PreparedVerificationRequest -> Text
preparedVerificationText request =
    let encoded = preparedVerificationInput request
        withoutFinalNewline =
            case ByteString.unsnoc encoded of
                Just (body, 10) -> body
                _ -> encoded
    in TextEncoding.decodeUtf8 withoutFinalNewline

preparedVerificationByteCount
    :: PreparedVerificationRequest
    -> Int
preparedVerificationByteCount =
    ByteString.length . preparedVerificationInput

preparedVerificationBytes
    :: PreparedVerificationRequest
    -> ByteString.ByteString
preparedVerificationBytes =
    preparedVerificationInput

preparedVerificationRequestId
    :: PreparedVerificationRequest
    -> Authority.PreparedRequestId
preparedVerificationRequestId =
    preparedVerificationIdentity

data PreparedTypedProverTask ref local origin global =
    PreparedTypedProverTask
        !(TypedProblem ref local origin global)
        !PreparedVerificationRequest

prepareTypedProverTask
    :: (Ord local, Ord global)
    => VampireTaskMode
    -> TypedProblem ref local origin global
    -> Either
        (TypedTptpPreparationError local global)
        (PreparedTypedProverTask ref local origin global)
prepareTypedProverTask mode problem = do
    prepared <-
        prepareTypedTptpProblem problem
    let dialect =
            case preparedTypedTptpRoute prepared of
                RouteFof -> VerificationFof
                RouteTh0 -> VerificationTh0
        bytes =
            TextEncoding.encodeUtf8
                (preparedTypedTptpTextNewline prepared)
        identity =
            Authority.preparedRequestId
                (case dialect of
                    VerificationFof -> Authority.PreparedRequestFof
                    VerificationTh0 -> Authority.PreparedRequestTh0)
                (case mode of
                    DirectTask -> Authority.PreparedRequestDirect
                    IndirectTask -> Authority.PreparedRequestIndirect)
                bytes
        preparedRequest =
            PreparedVerificationRequest
                { preparedVerificationDialect = dialect
                , preparedVerificationMode = mode
                , preparedVerificationInput = bytes
                , preparedVerificationIdentity = identity
                }
    pure
        (PreparedTypedProverTask
            problem
            preparedRequest)

preparedTypedProverLogicalProblem
    :: PreparedTypedProverTask ref local origin global
    -> TypedProblem ref local origin global
preparedTypedProverLogicalProblem
        (PreparedTypedProverTask
            problem
            _request) =
    problem

preparedTypedProverRequest
    :: PreparedTypedProverTask ref local origin global
    -> PreparedVerificationRequest
preparedTypedProverRequest
        (PreparedTypedProverTask
            _problem
            request) =
    request

data ProverStream
    = ProverStdin
    | ProverStdout
    | ProverStderr
    deriving (Show, Eq)

data ProverOutputStream
    = ProverOutputStdout
    | ProverOutputStderr
    deriving (Show, Eq)

data ProverProcessError
    = ProverLaunchFailed !FilePath !Text
    | ProverCommunicationFailed !FilePath !ProverStream !Text
    | ProverOutputMalformedUtf8 !FilePath !ProverOutputStream !Text
    | ProverTimedOut
        !FilePath
        !TimeLimit
        !BoundedCapturedStreams
    | ProverOutputLimitExceeded
        !FilePath
        !ProverOutputStream
        !BoundedCapturedStreams
    | ProverTerminatedBySignal
        !FilePath
        !Int
        !BoundedCapturedStreams
    | ProverLifecycleFailed !FilePath !Text
    | ProverCleanupFailed !ProverProcessError ![Text]
    deriving (Show, Eq)

data VampireFailure
    = VampireFailureRejected
        !CanonicalAtpRejection
        !BoundedCapturedStreams
    | VampireFailureProtocol
        !VampireProtocolError
        !BoundedCapturedStreams
    | VampireFailureProcess !ProverProcessError
    deriving (Show, Eq)

data VampireResolutionOutcome
    = VampireResolutionAccepted
    | VampireResolutionFailed !VampireFailure
    deriving (Show, Eq)

-- | A request-identified result that has crossed the process/protocol
-- boundary.  Executor-backed results additionally retain their stable dump
-- position; direct synchronous runs have no such position.
data VampireResolution = VampireResolution
    { vampireResolutionRequestId :: !Authority.PreparedRequestId
    , vampireResolutionWorkPosition :: !(Maybe WorkPosition)
    , vampireResolutionOutcome :: !VampireResolutionOutcome
    }
    deriving (Show, Eq)

-- | The non-accepting subset of 'VampireResolution'.  The constructor is
-- private so checking errors cannot accidentally contain an accepted result.
newtype FailedVampireResolution =
    FailedVampireResolution VampireResolution
    deriving (Show, Eq)

vampireResolutionAcceptedRequestId
    :: VampireResolution
    -> Maybe Authority.PreparedRequestId
vampireResolutionAcceptedRequestId resolution =
    case vampireResolutionOutcome resolution of
        VampireResolutionAccepted ->
            Just (vampireResolutionRequestId resolution)
        VampireResolutionFailed{} ->
            Nothing

vampireResolutionFailure
    :: VampireResolution
    -> Maybe FailedVampireResolution
vampireResolutionFailure resolution =
    case vampireResolutionOutcome resolution of
        VampireResolutionAccepted -> Nothing
        VampireResolutionFailed{} ->
            Just (FailedVampireResolution resolution)

failedVampireResolutionRequestId
    :: FailedVampireResolution
    -> Authority.PreparedRequestId
failedVampireResolutionRequestId
        (FailedVampireResolution resolution) =
    vampireResolutionRequestId resolution

failedVampireResolutionWorkPosition
    :: FailedVampireResolution
    -> Maybe WorkPosition
failedVampireResolutionWorkPosition
        (FailedVampireResolution resolution) =
    vampireResolutionWorkPosition resolution

failedVampireResolutionFailure
    :: FailedVampireResolution
    -> VampireFailure
failedVampireResolutionFailure
        (FailedVampireResolution resolution) =
    case vampireResolutionOutcome resolution of
        VampireResolutionAccepted ->
            impossible "accepted Vampire resolution escaped as a failure"
        VampireResolutionFailed resolutionFailure ->
            resolutionFailure

failedVampireResolutionDiagnostic
    :: Location
    -> FailedVampireResolution
    -> Diagnostic
failedVampireResolutionDiagnostic location failed =
    case failedVampireResolutionFailure failed of
        VampireFailureRejected rejection _evidence ->
            rejectionDiagnostic rejection
        VampireFailureProtocol protocolFailure evidence ->
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticAtpProtocol
                , diagnosticTitle =
                    "Vampire returned an invalid protocol result"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty (renderVampireProtocolError protocolFailure)
                , diagnosticNotes =
                    liveRequestNotes <> boundedStreamNotes evidence
                , diagnosticHelp = [dumpHelp]
                }
        VampireFailureProcess processFailure ->
            processDiagnostic processFailure
  where
    liveRequestNotes =
        pretty liveProvenance
            : pretty (renderVampireObligationId
                (failedVampireResolutionRequestId failed))
            : maybe
                []
                (pure . pretty . renderVampireLivePosition)
                (failedVampireResolutionWorkPosition failed)
    liveProvenance :: Text
    liveProvenance =
        case failedVampireResolutionFailure failed of
            VampireFailureProcess ProverLaunchFailed{} ->
                "a live run was attempted for this obligation in this invocation"
            _ ->
                "this obligation ran live in this invocation"
    dumpHelp =
        pretty
            ("rerun with --dump DIRECTORY to retain the complete ATP request"
                :: Text)

    rejectionDiagnostic = \case
        RejectedCounterexample ->
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticAtpCountermodel
                , diagnosticTitle =
                    "the selected premises do not imply this proof obligation"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("Vampire found the encoded obligation counter-satisfiable."
                            :: Text)
                , diagnosticNotes = liveRequestNotes
                , diagnosticHelp =
                    [ pretty
                        ("check the claim, its hypotheses, and the premises selected for this step"
                            :: Text)
                    , dumpHelp
                    ]
                }
        RejectedContradictoryInput ->
            Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = DiagnosticAtpContradictoryInput
                , diagnosticTitle =
                    "the selected premises are contradictory"
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("Vampire derived falsity from the encoded premises of this direct obligation."
                            :: Text)
                , diagnosticNotes = liveRequestNotes
                , diagnosticHelp =
                    [ pretty
                        ("check the assumptions and premises selected for this step"
                            :: Text)
                    , dumpHelp
                    ]
                }
        RejectedIndeterminate reasons ->
            let (code, title) = indeterminateHeading reasons
            in Diagnostic
                { diagnosticSeverity = DiagnosticError
                , diagnosticCode = code
                , diagnosticTitle = title
                , diagnosticPrimary = Just location
                , diagnosticMessage =
                    pretty
                        ("Vampire did not establish the encoded obligation; reported outcomes: "
                            <> Text.intercalate ", "
                                (renderAtpIndeterminateReason
                                    <$> NonEmpty.toList reasons)
                            <> ".")
                , diagnosticNotes = liveRequestNotes
                , diagnosticHelp = [dumpHelp]
                }

    processDiagnostic processFailure =
        let (code, title, message, evidence, dumpAvailable) =
                processDiagnosticParts processFailure
        in Diagnostic
            { diagnosticSeverity = DiagnosticError
            , diagnosticCode = code
            , diagnosticTitle = title
            , diagnosticPrimary = Just location
            , diagnosticMessage = pretty message
            , diagnosticNotes =
                liveRequestNotes <> maybe [] boundedStreamNotes evidence
            , diagnosticHelp = [dumpHelp | dumpAvailable]
            }

renderVampireObligationId :: Authority.PreparedRequestId -> Text
renderVampireObligationId requestId =
    "obligation id: " <> Text.pack (show requestId)

renderVampireLivePosition :: WorkPosition -> Text
renderVampireLivePosition work =
    "run-local live position: module "
        <> Text.pack (show (workPositionModuleOrdinal work))
        <> ", task "
        <> Text.pack (show (workPositionLocalRequestOrdinal work))

renderVampireLiveTaskReference
    :: WorkPosition
    -> Authority.PreparedRequestId
    -> Text
renderVampireLiveTaskReference work requestId =
    "live task: module "
        <> Text.pack (show (workPositionModuleOrdinal work))
        <> ", task "
        <> Text.pack (show (workPositionLocalRequestOrdinal work))
        <> "; "
        <> renderVampireObligationId requestId

indeterminateHeading
    :: NonEmpty AtpIndeterminateReason
    -> (DiagnosticCode, Text)
indeterminateHeading (reason :| []) =
    case reason of
        AtpTimedOut ->
            (DiagnosticAtpTimeout, "Vampire reached its time limit")
        AtpResourceOut ->
            (DiagnosticAtpResourceOut, "Vampire exhausted a resource limit")
        AtpGaveUp ->
            (DiagnosticAtpGaveUp, "Vampire gave up on this obligation")
        AtpUnknown ->
            (DiagnosticAtpUnknown, "Vampire returned an unknown result")
indeterminateHeading _reasons =
    ( DiagnosticAtpIndeterminate
    , "Vampire returned indeterminate results"
    )

renderAtpIndeterminateReason :: AtpIndeterminateReason -> Text
renderAtpIndeterminateReason = \case
    AtpTimedOut -> "timeout"
    AtpResourceOut -> "resource exhaustion"
    AtpGaveUp -> "gave up"
    AtpUnknown -> "unknown"

renderVampireProtocolError :: VampireProtocolError -> Text
renderVampireProtocolError = \case
    UnsuccessfulVampireExit exitCode ->
        "Vampire exited with " <> renderExitCode exitCode
            <> " without a compatible terminal outcome."
    UnsupportedVampireStatuses statuses ->
        "Vampire reported unsupported SZS statuses: "
            <> Text.intercalate ", " (Set.toAscList statuses) <> "."
    MalformedVampireStatusLines lines' ->
        "Vampire emitted malformed SZS status lines: "
            <> Text.intercalate "; " (Set.toAscList lines') <> "."
    MissingVampireOutcome ->
        "Vampire emitted no recognized terminal SZS outcome."
    ConflictingTerminalOutcomes outcomes ->
        "Vampire emitted conflicting terminal outcomes: "
            <> Text.intercalate ", "
                (renderCanonicalAtpOutcome <$> Set.toAscList outcomes)
            <> "."

renderCanonicalAtpOutcome :: CanonicalAtpOutcome -> Text
renderCanonicalAtpOutcome = \case
    Proved -> "theorem"
    Counterexample -> "counter-satisfiable"
    ContradictoryInput -> "contradictory axioms"
    Indeterminate reasons ->
        Text.intercalate ", "
            (renderAtpIndeterminateReason <$> NonEmpty.toList reasons)

renderExitCode :: ExitCode -> Text
renderExitCode = \case
    ExitSuccess -> "exit status 0"
    ExitFailure status -> "exit status " <> Text.pack (show status)

processDiagnosticParts
    :: ProverProcessError
    -> ( DiagnosticCode
       , Text
       , Text
       , Maybe BoundedCapturedStreams
       , Bool
       )
processDiagnosticParts = \case
    ProverLaunchFailed executable message ->
        ( DiagnosticAtpProcess
        , "Vampire could not be started"
        , "Launching " <> Text.pack executable <> " failed: " <> message
        , Nothing
        , False
        )
    ProverCommunicationFailed executable stream message ->
        ( DiagnosticAtpProcess
        , "communication with Vampire failed"
        , "Communication with " <> Text.pack executable <> " on "
            <> renderProverStream stream <> " failed: " <> message
        , Nothing
        , True
        )
    ProverOutputMalformedUtf8 executable stream message ->
        ( DiagnosticAtpProcess
        , "Vampire emitted malformed UTF-8"
        , Text.pack executable <> " emitted malformed UTF-8 on "
            <> renderProverOutputStream stream <> ": " <> message
        , Nothing
        , True
        )
    ProverTimedOut executable (Seconds seconds) evidence ->
        ( DiagnosticAtpTimeout
        , "Vampire exceeded its supervised time limit"
        , Text.pack executable <> " did not finish within "
            <> Text.pack (show seconds) <> " seconds plus shutdown grace."
        , Just evidence
        , True
        )
    ProverOutputLimitExceeded executable stream evidence ->
        ( DiagnosticAtpProcess
        , "Vampire exceeded its output limit"
        , Text.pack executable <> " produced too much data on "
            <> renderProverOutputStream stream <> "."
        , Just evidence
        , True
        )
    ProverTerminatedBySignal executable signal evidence ->
        ( DiagnosticAtpProcess
        , "Vampire was terminated by a signal"
        , Text.pack executable <> " was terminated by signal "
            <> Text.pack (show signal) <> "."
        , Just evidence
        , True
        )
    ProverLifecycleFailed executable message ->
        ( DiagnosticAtpProcess
        , "the Vampire process lifecycle failed"
        , "Managing " <> Text.pack executable <> " failed: " <> message
        , Nothing
        , True
        )
    ProverCleanupFailed primary failures ->
        let (code, title, message, evidence, live) = processDiagnosticParts primary
        in (code, title, message <> " Cleanup: " <> Text.intercalate "; " failures,
            evidence, live)

renderProverStream :: ProverStream -> Text
renderProverStream = \case
    ProverStdin -> "standard input"
    ProverStdout -> "standard output"
    ProverStderr -> "standard error"

renderProverOutputStream :: ProverOutputStream -> Text
renderProverOutputStream = \case
    ProverOutputStdout -> "standard output"
    ProverOutputStderr -> "standard error"

boundedStreamNotes :: BoundedCapturedStreams -> [Doc ()]
boundedStreamNotes BoundedCapturedStreams{..} =
    boundedStreamNote "Vampire stdout" boundedStdout
        <> boundedStreamNote "Vampire stderr" boundedStderr

boundedStreamNote :: Text -> BoundedBytes -> [Doc ()]
boundedStreamNote streamLabel bytes
    | Text.null stripped = []
    | otherwise =
        [ pretty
            (streamLabel <> " excerpt: " <> excerpt
                <> if omitted then " …" else "")
        ]
  where
    stripped = Text.strip (decodeBoundedBytes bytes)
    excerptLimit = 800
    excerpt = Text.take excerptLimit stripped
    omitted =
        Text.length stripped > excerptLimit || boundedBytesTruncated bytes

-- | Trusted synthetic outcomes for an alternate resolver or focused tests.
-- The request supplies the identity; no serialized task is retained.
rejectedVampireResolution
    :: PreparedVerificationRequest
    -> CanonicalAtpRejection
    -> VampireResolution
rejectedVampireResolution request rejection =
    resolutionForRequest request Nothing
        (VampireResolutionFailed
            (VampireFailureRejected rejection emptyBoundedCapturedStreams))

processFailedVampireResolution
    :: PreparedVerificationRequest
    -> ProverProcessError
    -> VampireResolution
processFailedVampireResolution request processFailure =
    resolutionForRequest request Nothing
        (VampireResolutionFailed
            (VampireFailureProcess processFailure))

data SupervisorAbort
    = SupervisorCommunicationFailed !ProverStream !Text
    | SupervisorOutputLimitExceeded !ProverOutputStream
    | SupervisorLifecycleFailed !Text
    deriving (Show)

instance Exception.Exception SupervisorAbort

data CaptureBuffer = CaptureBuffer
    { captureByteCount :: !Int
    , captureChunksReversed :: ![ByteString.ByteString]
    }

vampireOutputByteLimit :: Int
vampireOutputByteLimit =
    16 * 1024 * 1024

vampireWallGraceSeconds :: Integer
vampireWallGraceSeconds =
    2

captureChunkSize :: Int
captureChunkSize =
    32 * 1024

runPreparedTypedProver
    :: Vampire
    -> PreparedTypedProverTask ref local origin global
    -> IO VampireResolution
runPreparedTypedProver
        vampireCommand =
    runPreparedTypedProverWithObserver
        (\_request -> pure ())
        vampireCommand

runPreparedTypedProverWithObserver
    :: (PreparedVerificationRequest -> IO ())
    -> Vampire
    -> PreparedTypedProverTask ref local origin global
    -> IO VampireResolution
runPreparedTypedProverWithObserver
        observer
        vampireCommand
        (PreparedTypedProverTask
            _problem
            preparedRequest) = do
    terminal <- runPreparedVerificationTerminal
        observer
        vampireCommand
        preparedRequest
    completionVampireResolution
        Nothing
        preparedRequest
        (VampireCompletion
            (preparedVerificationRequestId preparedRequest)
            terminal)

-- | Invocation-local bounded owner of Vampire subprocesses.  The finite queue
-- carries only immutable prepared bytes plus runtime diagnostic position;
-- checker builders and typed tasks never cross this boundary.
data VampireExecutor = VampireExecutor
    { executorQueue :: !(TBQueue ExecutorJob)
    , executorState :: !(TVar VampireExecutorState)
    , executorNextHandle :: !(TVar Int)
    , executorCommand :: !Vampire
    , executorRequestObserver
        :: !(WorkPosition -> PreparedVerificationRequest -> IO ())
    , executorRuntime :: !VampireExecutorRuntime
    , executorSlowAtpAccumulator :: !(TVar SlowAtpAccumulator)
    , executorExecutionAccumulator :: !(TVar VampireExecutionAccumulator)
    , executorLiveRunsStarted :: !(TVar Natural)
    , executorMaximumQueueDepth :: !(TVar Natural)
    , executorWorkerCount :: !Int
    }

data ExecutorJob = ExecutorJob
    { executorJobPosition :: !WorkPosition
    , executorJobLocation :: !Location
    , executorJobRequest :: !PreparedVerificationRequest
    , executorJobPhase :: !(TVar VampireRequestPhase)
    , executorJobCompletion
        :: !(TMVar VampireCompletion)
    }

-- Publication and settlement are separate transitions. A settled request has
-- no worker/process left to own, even when an executor fault prevented an
-- ordinary completion. Queued cancellation settles without starting a process.
data VampireRequestPhase
    = RequestQueued
    | RequestRunning
    | RequestCancelRequested
    | RequestResultPublished
    | RequestSettled
    deriving (Eq)

data VampireExecutorState
    = ExecutorRunning
    | ExecutorClosing
    | ExecutorFaulted !ExecutorFault

data ExecutorFault
    = ExecutorWorkerFault !VampireExecutorFault
    | ExecutorObserverFault !SomeException

-- | A global executor fault is distinct from one request's declared process
-- or protocol outcome.  Its bounded message carries no process transcript.
newtype VampireExecutorFault = VampireExecutorFault Text
    deriving (Show)

instance Exception.Exception VampireExecutorFault

data VampireRequestOwner = VampireRequestOwner
    { requestOwnerExecutor :: !VampireExecutor
    , requestOwnerState :: !(TVar VampireRequestOwnerState)
    }

data VampireRequestOwnerState
    = RequestOwnerOpen !(IntMap VampireHandle)
    | RequestOwnerClosed

-- | An opaque, owner-scoped completion handle.  It deliberately retains no
-- prepared request, command, transcript, builder, or parser state.
data VampireHandle = VampireHandle
    { vampireHandleOrdinal :: !Int
    , vampireHandleOwner :: !VampireRequestOwner
    , vampireHandleRequestId :: !Authority.PreparedRequestId
    , vampireHandleWorkPosition :: !WorkPosition
    , vampireHandlePhase :: !(TVar VampireRequestPhase)
    , vampireHandleCompletion :: !(TMVar VampireCompletion)
    }

data VampireTerminal
    = VampireAccepted
    | VampireRejected !CanonicalAtpRejection !BoundedCapturedStreams
    | VampireProtocolFailed
        !VampireProtocolError
        !BoundedCapturedStreams
    | VampireProcessFailed !ProverProcessError
    | VampireCancelled
    deriving (Show, Eq)

data VampireCompletion = VampireCompletion
    { vampireCompletionRequestId :: !Authority.PreparedRequestId
    , vampireCompletionTerminal :: !VampireTerminal
    }
    deriving (Show, Eq)

-- | Monotonic executor wall time in nanoseconds.
newtype AtpDuration = AtpDuration Word64
    deriving (Show, Eq, Ord)

atpDurationNanoseconds :: AtpDuration -> Word64
atpDurationNanoseconds (AtpDuration nanoseconds) = nanoseconds

data SlowAtpOutcome
    = SlowAtpAccepted
    | SlowAtpRejected !CanonicalAtpRejection
    | SlowAtpProtocolFailed
    | SlowAtpProcessFailed
    deriving (Show, Eq)

data SlowAtpTask = SlowAtpTask
    { slowAtpDuration :: !AtpDuration
    , slowAtpOutcome :: !SlowAtpOutcome
    , slowAtpPosition :: !WorkPosition
    , slowAtpLocation :: !Location
    , slowAtpRequestId :: !Authority.PreparedRequestId
    }
    deriving (Show, Eq)

data SlowAtpReport = SlowAtpReport
    { slowAtpQualifyingTaskCount :: !Int
    , slowAtpTasks :: ![SlowAtpTask]
    }
    deriving (Show, Eq)

slowAtpOmittedTaskCount :: SlowAtpReport -> Int
slowAtpOmittedTaskCount report =
    slowAtpQualifyingTaskCount report - length (slowAtpTasks report)

data SlowAtpRank = SlowAtpRank
    !AtpDuration
    !(Down WorkPosition)
    deriving (Eq, Ord)

data SlowAtpAccumulator = SlowAtpAccumulator
    { slowAtpAccumulatorQualifyingTaskCount :: !Int
    , slowAtpAccumulatorRetained :: !(Map.Map SlowAtpRank SlowAtpTask)
    }

slowAtpThreshold :: AtpDuration
slowAtpThreshold = AtpDuration 4000000000

slowAtpRetainedLimit :: Int
slowAtpRetainedLimit = 12

emptySlowAtpAccumulator :: SlowAtpAccumulator
emptySlowAtpAccumulator = SlowAtpAccumulator 0 Map.empty

-- | Aggregate monotonic wall measurements for completed live Vampire
-- lifecycles. The aggregate duration is a process-wall-time integral, so
-- overlapping requests contribute independently.
data VampireExecutionReport = VampireExecutionReport
    { vampireExecutionWorkerCount :: !Int
    , vampireExecutionCompletedRuns :: !Natural
    , vampireExecutionAggregateNanoseconds :: !Word64
    , vampireExecutionLongestNanoseconds :: !Word64
    , vampireExecutionActiveSpanNanoseconds :: !Word64
    , vampireExecutionMaximumQueueDepth :: !Natural
    }
    deriving (Show, Eq)

data VampireExecutionAccumulator = VampireExecutionAccumulator
    { accumulatedCompletedRuns :: !Natural
    , accumulatedNanoseconds :: !Word64
    , accumulatedLongestNanoseconds :: !Word64
    , accumulatedFirstStart :: !(Maybe Word64)
    , accumulatedLastCompletion :: !(Maybe Word64)
    }

emptyVampireExecutionAccumulator :: VampireExecutionAccumulator
emptyVampireExecutionAccumulator =
    VampireExecutionAccumulator 0 0 0 Nothing Nothing

recordVampireExecutionStart
    :: Word64
    -> VampireExecutionAccumulator
    -> VampireExecutionAccumulator
recordVampireExecutionStart started accumulator =
    accumulator
        { accumulatedFirstStart =
            Just case accumulatedFirstStart accumulator of
                Nothing -> started
                Just previous -> min previous started
        }

recordCompletedVampireExecution
    :: Word64
    -> Word64
    -> VampireExecutionAccumulator
    -> VampireExecutionAccumulator
recordCompletedVampireExecution duration finished accumulator =
    accumulator
        { accumulatedCompletedRuns =
            accumulatedCompletedRuns accumulator + 1
        , accumulatedNanoseconds =
            accumulatedNanoseconds accumulator + duration
        , accumulatedLongestNanoseconds =
            max duration (accumulatedLongestNanoseconds accumulator)
        , accumulatedLastCompletion =
            Just case accumulatedLastCompletion accumulator of
                Nothing -> finished
                Just previous -> max previous finished
        }

recordSlowAtpTask
    :: SlowAtpTask
    -> SlowAtpAccumulator
    -> SlowAtpAccumulator
recordSlowAtpTask task accumulator
    | slowAtpDuration task < slowAtpThreshold = accumulator
    | otherwise =
        accumulator
            { slowAtpAccumulatorQualifyingTaskCount =
                slowAtpAccumulatorQualifyingTaskCount accumulator + 1
            , slowAtpAccumulatorRetained = bounded
            }
  where
    rank = SlowAtpRank
        (slowAtpDuration task)
        (Down (slowAtpPosition task))
    inserted = Map.insert rank task (slowAtpAccumulatorRetained accumulator)
    bounded
        | Map.size inserted > slowAtpRetainedLimit = Map.deleteMin inserted
        | otherwise = inserted

finalizeSlowAtpReport :: SlowAtpAccumulator -> SlowAtpReport
finalizeSlowAtpReport accumulator =
    SlowAtpReport
        { slowAtpQualifyingTaskCount =
            slowAtpAccumulatorQualifyingTaskCount accumulator
        , slowAtpTasks =
            snd <$> Map.toDescList (slowAtpAccumulatorRetained accumulator)
        }

data VampireExecutorClosed = VampireExecutorClosed
    deriving (Show)

instance Exception.Exception VampireExecutorClosed

data VampireRequestOwnerClosed = VampireRequestOwnerClosed
    deriving (Show)

instance Exception.Exception VampireRequestOwnerClosed

data RequestObserverFailure = RequestObserverFailure SomeException

instance Show RequestObserverFailure where
    show (RequestObserverFailure observerError) =
        "request observer failed: " <> displayException observerError

instance Exception.Exception RequestObserverFailure

data ExecutorObserverFailure = ExecutorObserverFailure SomeException

instance Show ExecutorObserverFailure where
    show (ExecutorObserverFailure observerError) =
        "executor request observer failed: " <> displayException observerError

instance Exception.Exception ExecutorObserverFailure

-- | Bracket exactly the selected number of workers.  Cancelling the bracket
-- cancels each worker; a worker owning a subprocess in turn terminates and
-- reaps that process group through the ordinary supervisor boundary.
withVampireExecutor
    :: EffectiveJobs
    -> Vampire
    -> (WorkPosition -> PreparedVerificationRequest -> IO ())
    -> (VampireExecutor -> IO value)
    -> IO value
withVampireExecutor selected command observer action =
    withVampireExecutorUsingRuntime
        defaultVampireExecutorRuntime
        selected
        command
        observer
        action

-- | Executor constructor with an injected monotonic clock for focused timing
-- policy tests. Production callers use 'withVampireExecutor'.
withVampireExecutorUsingClock
    :: IO Word64
    -> EffectiveJobs
    -> Vampire
    -> (WorkPosition -> PreparedVerificationRequest -> IO ())
    -> (VampireExecutor -> IO value)
    -> IO value
withVampireExecutorUsingClock clock =
    withVampireExecutorUsingRuntime
        defaultVampireExecutorRuntime { vampireRuntimeClock = clock }

-- | Runtime operations at the executor's acquisition and cleanup boundaries. A worker
-- starter must return its owned handle, or leave no worker behind if it throws,
-- as 'async' does. It is called masked; the supplied worker action restores the
-- caller's masking state. This also permits deterministic acquisition failures.
data VampireExecutorRuntime = VampireExecutorRuntime
    { vampireRuntimeClock :: IO Word64
    , vampireRuntimeStartWorker :: IO () -> IO (Async ())
    , vampireRuntimeStartPipe :: IO () -> IO (Async ())
    , vampireRuntimeTerminateGroup :: ProcessGroupID -> IO ()
    , vampireRuntimeWaitForProcess :: ProcessHandle -> IO ExitCode
    , vampireRuntimeClosePipe :: Handle -> IO ()
    }

defaultVampireExecutorRuntime :: VampireExecutorRuntime
defaultVampireExecutorRuntime = VampireExecutorRuntime
    { vampireRuntimeClock = getMonotonicTimeNSec
    , vampireRuntimeStartWorker = async
    , vampireRuntimeStartPipe = async
    , vampireRuntimeTerminateGroup = terminateRemainingProcessGroup
    , vampireRuntimeWaitForProcess = waitForVampireProcess
    , vampireRuntimeClosePipe = hClose
    }

-- waitForProcess blocks the entire non-threaded RTS. Polling there preserves
-- concurrent drains and cancellation; threaded clients
-- retain the ordinary blocking wait without per-request polling overhead.
waitForVampireProcess :: ProcessHandle -> IO ExitCode
waitForVampireProcess process
    | rtsSupportsBoundThreads = waitForProcess process
    | otherwise = do
        exited <- getProcessExitCode process
        case exited of
            Just exitCode -> pure exitCode
            Nothing -> threadDelay 1000 >> waitForVampireProcess process

withVampireExecutorUsingRuntime
    :: VampireExecutorRuntime
    -> EffectiveJobs
    -> Vampire
    -> (WorkPosition -> PreparedVerificationRequest -> IO ())
    -> (VampireExecutor -> IO value)
    -> IO value
withVampireExecutorUsingRuntime runtime selected command observer action = do
    executor <- createExecutor
    -- The prefix has an owner before the first start. Mask only the handoff
    -- from a successful start into that prefix, including during acquisition.
    Exception.bracket (newIORef []) (release executor) \owned ->
        Exception.mask \restore -> do
            replicateM_ workerCount do
                restore Exception.allowInterrupt
                worker <- vampireRuntimeStartWorker runtime
                    (restore (superviseExecutorWorker executor))
                modifyIORef' owned (worker :)
            restore (action executor)
  where
    workerCount = effectiveJobsValue selected

    createExecutor = do
        queue <- newTBQueueIO
            (fromIntegral workerCount * 2)
        state <- newTVarIO ExecutorRunning
        nextHandle <- newTVarIO 0
        slowTasks <- newTVarIO emptySlowAtpAccumulator
        executionMeasurements <-
            newTVarIO emptyVampireExecutionAccumulator
        liveRunsStarted <- newTVarIO 0
        maximumQueueDepth <- newTVarIO 0
        let executor =
                VampireExecutor
                    { executorQueue = queue
                    , executorState = state
                    , executorNextHandle = nextHandle
                    , executorCommand = command
                    , executorRequestObserver = observer
                    , executorRuntime = runtime
                    , executorSlowAtpAccumulator = slowTasks
                    , executorExecutionAccumulator = executionMeasurements
                    , executorLiveRunsStarted = liveRunsStarted
                    , executorMaximumQueueDepth = maximumQueueDepth
                    , executorWorkerCount = workerCount
                    }
        pure executor

    release executor owned = do
        alreadyFaulted <- atomically do
            state <- readTVar (executorState executor)
            case state of
                ExecutorRunning ->
                    writeTVar (executorState executor) ExecutorClosing >> pure False
                ExecutorClosing ->
                    pure False
                ExecutorFaulted{} ->
                    pure True
        -- Closing signals all supervisors. Workers keep their slots through
        -- settlement; shutdown never cancels the sole process-cleanup owner.
        workers <- readIORef owned
        interruptions <- traverse (awaitOwnedTask . waitCatchSTM) workers
        unless alreadyFaulted $ atomically do
            state <- readTVar (executorState executor)
            case state of
                ExecutorFaulted fault -> throwExecutorFaultSTM fault
                _ -> pure ()
        traverse_ Exception.throwIO (firstInterruption (snd <$> interruptions))

-- | Bracket the complete set of handles submitted by one module pipeline.
-- Normal early return, failure, and asynchronous cancellation all cancel and
-- reap the remaining owned work before the scope is left.
withVampireRequestOwner
    :: VampireExecutor
    -> (VampireRequestOwner -> IO value)
    -> IO value
withVampireRequestOwner executor =
    Exception.bracket acquire release
  where
    acquire =
        VampireRequestOwner executor
            <$> newTVarIO (RequestOwnerOpen IntMap.empty)

    release owner = Exception.mask_ do
        handles <- atomically do
            state <- readTVar (requestOwnerState owner)
            case state of
                RequestOwnerClosed ->
                    pure []
                RequestOwnerOpen owned -> do
                    writeTVar (requestOwnerState owner) RequestOwnerClosed
                    pure (IntMap.elems owned)
        traverse_ signalVampireCancellation handles
        traverse_ awaitVampireCancellation handles
        traverse_ deregisterVampireHandle handles

runPreparedTypedProverWithExecutor
    :: VampireRequestOwner
    -> WorkPosition
    -> Location
    -> PreparedTypedProverTask ref local origin global
    -> IO VampireResolution
runPreparedTypedProverWithExecutor
        owner
        position
        location
        (PreparedTypedProverTask
            _problem
            preparedRequest) = do
    handle <- submitVampireRequest owner position location preparedRequest
    awaitPreparedVampireRequest preparedRequest handle
        `Exception.onException` cancelVampireRequest handle

vampireExecutorSlowAtpReport :: VampireExecutor -> IO SlowAtpReport
vampireExecutorSlowAtpReport executor =
    finalizeSlowAtpReport
        <$> readTVarIO (executorSlowAtpAccumulator executor)

vampireExecutorLiveRunsStarted :: VampireExecutor -> IO Natural
vampireExecutorLiveRunsStarted = readTVarIO . executorLiveRunsStarted

vampireExecutorExecutionReport
    :: VampireExecutor
    -> IO VampireExecutionReport
vampireExecutorExecutionReport executor = do
    accumulator <- readTVarIO (executorExecutionAccumulator executor)
    maximumQueueDepth <- readTVarIO (executorMaximumQueueDepth executor)
    let activeSpan =
            case
                ( accumulatedFirstStart accumulator
                , accumulatedLastCompletion accumulator
                ) of
                (Just started, Just finished) -> finished - started
                _ -> 0
    pure
        VampireExecutionReport
            { vampireExecutionWorkerCount = executorWorkerCount executor
            , vampireExecutionCompletedRuns =
                accumulatedCompletedRuns accumulator
            , vampireExecutionAggregateNanoseconds =
                accumulatedNanoseconds accumulator
            , vampireExecutionLongestNanoseconds =
                accumulatedLongestNanoseconds accumulator
            , vampireExecutionActiveSpanNanoseconds = activeSpan
            , vampireExecutionMaximumQueueDepth = maximumQueueDepth
            }

submitVampireRequest
    :: VampireRequestOwner
    -> WorkPosition
    -> Location
    -> PreparedVerificationRequest
    -> IO VampireHandle
submitVampireRequest owner position location request = do
    -- Force the compact queue payload before masked ownership acquisition.
    _ <- Exception.evaluate (preparedVerificationByteCount request)
    _ <- Exception.evaluate (preparedVerificationRequestId request)
    Exception.mask_ do
        phase <- newTVarIO RequestQueued
        completion <- newEmptyTMVarIO
        let executor = requestOwnerExecutor owner
        handle <- atomically do
            executorStatus <- readTVar (executorState executor)
            case executorStatus of
                ExecutorClosing -> throwSTM VampireExecutorClosed
                ExecutorFaulted fault -> throwExecutorFaultSTM fault
                ExecutorRunning -> pure ()
            ownerStatus <- readTVar (requestOwnerState owner)
            owned <- case ownerStatus of
                RequestOwnerClosed -> throwSTM VampireRequestOwnerClosed
                RequestOwnerOpen current -> pure current
            ordinal <- readTVar (executorNextHandle executor)
            writeTVar (executorNextHandle executor) (ordinal + 1)
            let acquired =
                    VampireHandle
                        { vampireHandleOrdinal = ordinal
                        , vampireHandleOwner = owner
                        , vampireHandleRequestId =
                            preparedVerificationRequestId request
                        , vampireHandleWorkPosition = position
                        , vampireHandlePhase = phase
                        , vampireHandleCompletion = completion
                        }
                job =
                    ExecutorJob
                        { executorJobPosition = position
                        , executorJobLocation = location
                        , executorJobRequest = request
                        , executorJobPhase = phase
                        , executorJobCompletion = completion
                        }
            writeTBQueue (executorQueue executor) job
            queueDepth <- lengthTBQueue (executorQueue executor)
            modifyTVar'
                (executorMaximumQueueDepth executor)
                (max queueDepth)
            writeTVar
                (requestOwnerState owner)
                (RequestOwnerOpen (IntMap.insert ordinal acquired owned))
            pure acquired
        pure handle

awaitVampireRequest :: VampireHandle -> IO VampireCompletion
awaitVampireRequest handle = Exception.mask \restore -> do
    let executor = requestOwnerExecutor (vampireHandleOwner handle)
    completion <- restore (atomically do
        executorStatus <- readTVar (executorState executor)
        case executorStatus of
            ExecutorFaulted fault -> throwExecutorFaultSTM fault
            ExecutorRunning -> settledCompletion handle
            ExecutorClosing ->
                settledCompletion handle
                    `orElse` throwSTM VampireExecutorClosed)
    deregisterVampireHandle handle
    pure completion

settledCompletion :: VampireHandle -> STM VampireCompletion
settledCompletion handle = do
    phase <- readTVar (vampireHandlePhase handle)
    check (phase == RequestSettled)
    readTMVar (vampireHandleCompletion handle)

-- | Await one already submitted request and recover the ordinary typed
-- prover result.  The supplied immutable request is checked against every
-- completion before any caller may interpret its terminal outcome.
awaitPreparedVampireRequest
    :: PreparedVerificationRequest
    -> VampireHandle
    -> IO VampireResolution
awaitPreparedVampireRequest request handle =
    awaitVampireRequest handle
        >>= completionVampireResolution
            (Just (vampireHandleWorkPosition handle))
            request

cancelVampireRequest :: VampireHandle -> IO ()
cancelVampireRequest handle = Exception.mask_ do
    signalVampireCancellation handle
    awaitVampireCancellation handle
    deregisterVampireHandle handle

signalVampireCancellation :: VampireHandle -> IO ()
signalVampireCancellation handle = do
    let completion =
            VampireCompletion
                (vampireHandleRequestId handle)
                VampireCancelled
    _ <- Exception.evaluate completion
    atomically do
        phase <- readTVar (vampireHandlePhase handle)
        case phase of
            RequestQueued -> do
                void (publishVampireTerminalSTM (vampireHandleCompletion handle) completion)
                writeTVar (vampireHandlePhase handle) RequestSettled
            RequestRunning -> writeTVar (vampireHandlePhase handle) RequestCancelRequested
            RequestCancelRequested -> pure ()
            RequestResultPublished -> pure ()
            RequestSettled -> pure ()

awaitVampireCancellation :: VampireHandle -> IO ()
awaitVampireCancellation handle = atomically do
    phase <- readTVar (vampireHandlePhase handle)
    check (phase == RequestSettled)

deregisterVampireHandle :: VampireHandle -> IO ()
deregisterVampireHandle handle = atomically do
    let owner = vampireHandleOwner handle
    state <- readTVar (requestOwnerState owner)
    case state of
        RequestOwnerClosed -> pure ()
        RequestOwnerOpen owned ->
            writeTVar
                (requestOwnerState owner)
                (RequestOwnerOpen
                    (IntMap.delete (vampireHandleOrdinal handle) owned))

superviseExecutorWorker :: VampireExecutor -> IO ()
superviseExecutorWorker executor = do
    result <- Exception.try (executorWorker executor)
    case result of
        Right () -> pure ()
        Left workerFailure -> do
            state <- readTVarIO (executorState executor)
            case state of
                ExecutorRunning ->
                    recordExecutorFault executor workerFailure
                ExecutorClosing ->
                    pure ()
                ExecutorFaulted{} ->
                    pure ()

recordExecutorFault :: VampireExecutor -> SomeException -> IO ()
recordExecutorFault executor workerFailure = atomically do
    state <- readTVar (executorState executor)
    case state of
        ExecutorRunning ->
            writeTVar
                (executorState executor)
                (ExecutorFaulted (classifyExecutorFault workerFailure))
        ExecutorClosing -> pure ()
        ExecutorFaulted{} -> pure ()

-- Cleanup failures also matter during scoped shutdown, when ordinary worker
-- cancellation is expected. Preserve the first executor fault in either case.
recordExecutorCleanupFault :: VampireExecutor -> Text -> IO ()
recordExecutorCleanupFault executor message = atomically do
    state <- readTVar (executorState executor)
    case state of
        ExecutorFaulted{} -> pure ()
        _ -> writeTVar (executorState executor)
            (ExecutorFaulted (ExecutorWorkerFault (VampireExecutorFault message)))

classifyExecutorFault :: SomeException -> ExecutorFault
classifyExecutorFault workerFailure =
    case fromException workerFailure of
        Just (ExecutorObserverFailure observerFailure) ->
            ExecutorObserverFault observerFailure
        Nothing ->
            ExecutorWorkerFault
                (VampireExecutorFault
                    (boundedText
                        (Text.pack (displayException workerFailure))))

throwExecutorFaultSTM :: ExecutorFault -> STM value
throwExecutorFaultSTM = \case
    ExecutorWorkerFault fault -> throwSTM fault
    ExecutorObserverFault observerFailure -> throwSTM observerFailure

executorWorker :: VampireExecutor -> IO ()
executorWorker executor = Exception.mask \restore -> do
    -- Dequeue, mark ownership, and install the release action before allowing
    -- cancellation. Waiting on an empty queue remains interruptible.
    next <- atomically do
        state <- readTVar (executorState executor)
        case state of
            ExecutorRunning -> Just <$> readTBQueue (executorQueue executor)
            ExecutorClosing -> pure Nothing
            ExecutorFaulted{} -> pure Nothing
    case next of
        Nothing -> pure ()
        Just job -> do
            shouldRun <- atomically do
                phase <- readTVar (executorJobPhase job)
                case phase of
                    RequestQueued -> do
                        writeTVar (executorJobPhase job) RequestRunning
                        pure True
                    RequestSettled -> pure False
                    _ -> throwSTM (VampireExecutorFault "a Vampire request was dequeued twice")
            when shouldRun
                (restore (executeJob executor job)
                    `Exception.finally`
                        atomically (writeTVar (executorJobPhase job) RequestSettled))
            restore (executorWorker executor)

executeJob :: VampireExecutor -> ExecutorJob -> IO ()
executeJob executor job = do
    terminal <- timedExecutorRun executor job
    publishJobTerminal job terminal

executorRequestStopped :: VampireExecutor -> ExecutorJob -> STM ()
executorRequestStopped executor job = do
    state <- readTVar (executorState executor)
    case state of
        ExecutorRunning -> do
            phase <- readTVar (executorJobPhase job)
            check (phase == RequestCancelRequested)
        ExecutorClosing -> pure ()
        ExecutorFaulted{} -> pure ()

publishJobTerminal :: ExecutorJob -> VampireTerminal -> IO ()
publishJobTerminal job terminal = do
    let completion = VampireCompletion
            (preparedVerificationRequestId (executorJobRequest job)) terminal
    _ <- Exception.evaluate completion
    atomically do
        published <- publishVampireTerminalSTM (executorJobCompletion job) completion
        when published (writeTVar (executorJobPhase job) RequestResultPublished)

timedExecutorRun
    :: VampireExecutor
    -> ExecutorJob
    -> IO VampireTerminal
timedExecutorRun executor job = Exception.mask \restore -> do
    started <- vampireRuntimeClock (executorRuntime executor)
    atomically do
        modifyTVar' (executorLiveRunsStarted executor) (+ 1)
        modifyTVar'
            (executorExecutionAccumulator executor)
            (recordVampireExecutionStart started)
    terminal <- restore
        (runPreparedVerificationTerminalWithControl
            (executorRuntime executor)
            (executorRequestStopped executor job)
            (\message -> recordExecutorCleanupFault executor
                (boundedText (locationToText (executorJobLocation job)) <> ": " <> message))
            (markExecutorObserver
                (executorRequestObserver executor (executorJobPosition job)))
            (executorCommand executor)
            (executorJobRequest job))
    finished <- vampireRuntimeClock (executorRuntime executor)
    let elapsed = finished - started
    let task = SlowAtpTask
            { slowAtpDuration = AtpDuration elapsed
            , slowAtpOutcome = slowAtpOutcomeFromTerminal terminal
            , slowAtpPosition = executorJobPosition job
            , slowAtpLocation = executorJobLocation job
            , slowAtpRequestId =
                preparedVerificationRequestId (executorJobRequest job)
            }
    unless (isCancelled terminal) $ atomically do
        modifyTVar'
            (executorSlowAtpAccumulator executor)
            (recordSlowAtpTask task)
        modifyTVar'
            (executorExecutionAccumulator executor)
            (recordCompletedVampireExecution elapsed finished)
    pure terminal
  where
    isCancelled VampireCancelled = True
    isCancelled _ = False

markExecutorObserver
    :: (PreparedVerificationRequest -> IO ())
    -> PreparedVerificationRequest
    -> IO ()
markExecutorObserver observer request =
    UnliftIO.catchAny
        (observer request)
        (Exception.throwIO . ExecutorObserverFailure)

slowAtpOutcomeFromTerminal :: VampireTerminal -> SlowAtpOutcome
slowAtpOutcomeFromTerminal = \case
    VampireAccepted -> SlowAtpAccepted
    VampireRejected rejection _diagnostic -> SlowAtpRejected rejection
    VampireProtocolFailed{} -> SlowAtpProtocolFailed
    VampireProcessFailed{} -> SlowAtpProcessFailed
    VampireCancelled ->
        impossible "cancelled Vampire task was recorded as completed"

publishVampireTerminalSTM
    :: TMVar VampireCompletion
    -> VampireCompletion
    -> STM Bool
publishVampireTerminalSTM = tryPutTMVar

runPreparedVerificationTerminal
    :: (PreparedVerificationRequest -> IO ())
    -> Vampire
    -> PreparedVerificationRequest
    -> IO VampireTerminal
runPreparedVerificationTerminal =
    runPreparedVerificationTerminalWithControl
        defaultVampireExecutorRuntime retry (const (pure ()))

runPreparedVerificationTerminalWithControl
    :: VampireExecutorRuntime
    -> STM ()
    -> (Text -> IO ())
    -> (PreparedVerificationRequest -> IO ())
    -> Vampire
    -> PreparedVerificationRequest
    -> IO VampireTerminal
runPreparedVerificationTerminalWithControl runtime stopped fault observer command request = do
    transcriptResult <-
        runPreparedVampireProcessWithObserver runtime stopped fault observer command request
    pure case transcriptResult of
        ProcessCancelled -> VampireCancelled
        ProcessFinished (Left processFailure) ->
            VampireProcessFailed processFailure
        ProcessFinished (Right transcript) ->
            let evidence = boundedCompletedStreams transcript
            in
            case classifyVampireCompleted
                (preparedVerificationMode request)
                transcript of
                Left protocolFailure ->
                    VampireProtocolFailed
                        protocolFailure
                        evidence
                Right Proved ->
                    VampireAccepted
                Right Counterexample ->
                    VampireRejected
                        RejectedCounterexample
                        evidence
                Right ContradictoryInput ->
                    VampireRejected
                        RejectedContradictoryInput
                        evidence
                Right (Indeterminate reasons) ->
                    VampireRejected
                        (RejectedIndeterminate reasons)
                        evidence

completionVampireResolution
    :: Maybe WorkPosition
    -> PreparedVerificationRequest
    -> VampireCompletion
    -> IO VampireResolution
completionVampireResolution position request completion = do
    unless (actualId == expectedId)
        (Exception.throwIO
            (VampireExecutorFault
                "Vampire completion has the wrong request id"))
    case vampireCompletionTerminal completion of
        VampireAccepted ->
            pure (resolutionForRequest request position VampireResolutionAccepted)
        VampireRejected rejection evidence ->
            pure
                (resolutionForRequest request position
                    (VampireResolutionFailed
                        (VampireFailureRejected rejection evidence)))
        VampireProtocolFailed protocolFailure evidence ->
            pure
                (resolutionForRequest request position
                    (VampireResolutionFailed
                        (VampireFailureProtocol protocolFailure evidence)))
        VampireProcessFailed processFailure ->
            pure
                (resolutionForRequest request position
                    (VampireResolutionFailed
                        (VampireFailureProcess processFailure)))
        VampireCancelled ->
            Exception.throwIO
                (VampireExecutorFault
                    "active admission encountered a cancelled Vampire request")
  where
    expectedId = preparedVerificationRequestId request
    actualId = vampireCompletionRequestId completion

resolutionForRequest
    :: PreparedVerificationRequest
    -> Maybe WorkPosition
    -> VampireResolutionOutcome
    -> VampireResolution
resolutionForRequest request position outcome =
    VampireResolution
        { vampireResolutionRequestId = preparedVerificationRequestId request
        , vampireResolutionWorkPosition = position
        , vampireResolutionOutcome = outcome
        }

data VampireProcessResult
    = ProcessCancelled
    | ProcessFinished !(Either ProverProcessError CompletedTranscript)

data ProcessWait
    = ProcessCompleted !ExitCode
    | ProcessDeadline
    | ProcessStopped

data ProverTimer
    = RegisteredTimer !Timer.Timer
    | SleepingTimer !(Async ())

startProverTimer :: Int -> IO ProverTimer
startProverTimer microseconds
    | rtsSupportsBoundThreads = RegisteredTimer <$> Timer.startTimer microseconds
    | otherwise = SleepingTimer <$> asyncWithUnmask (\unmask ->
        unmask (threadDelay microseconds))

awaitProverTimer :: ProverTimer -> STM ()
awaitProverTimer (RegisteredTimer timer) = Timer.awaitTimer timer
awaitProverTimer (SleepingTimer task) = taskSucceeded task

stopProverTimer :: ProverTimer -> IO ()
stopProverTimer (RegisteredTimer timer) = Timer.stopTimer timer
stopProverTimer (SleepingTimer task) = stopOwnedTask task

runPreparedVampireProcessWithObserver
    :: VampireExecutorRuntime
    -> STM ()
    -> (Text -> IO ())
    -> (PreparedVerificationRequest -> IO ())
    -> Vampire
    -> PreparedVerificationRequest
    -> IO VampireProcessResult
runPreparedVampireProcessWithObserver runtime stopped fault observer command request = do
    launched <- newIORef False
    result <- UnliftIO.tryAny $
        withVampirePipes \input output err childInput childOutput childError spawn ->
            Exception.mask \restore -> do
                pipeTasks <- newIORef []
                timers <- newIORef []
                reaper <- newIORef Nothing
                group <- newIORef Nothing
                cleanupFailures <- newIORef []
                stdoutCapture <- newIORef emptyCaptureBuffer
                stderrCapture <- newIORef emptyCaptureBuffer
                process <- spawn executable (vampireArguments command)
                writeIORef launched True
                let processGroup = do
                        known <- readIORef group
                        case known of
                            Just value -> pure value
                            Nothing -> do
                                pid <- getPid process
                                case pid of
                                    Nothing -> ioError (userError "new Vampire process has no group identifier")
                                    Just value -> do
                                        let ownedGroup = fromIntegral value
                                        writeIORef group (Just ownedGroup)
                                        pure ownedGroup
                    startPipe action = do
                        task <- vampireRuntimeStartPipe runtime (restore action)
                        modifyIORef' pipeTasks (task :)
                        pure task
                    run = do
                        _ <- processGroup
                        traverse_ hClose [childInput, childOutput, childError]
                        -- Observer work is owned and cancellable too. The wall
                        -- deadline still starts after the observer, as before.
                        observed <- async (restore (runRequestObserver observer request))
                        modifyIORef' pipeTasks (observed :)
                        proceed <- restore $ atomically $
                            (taskSucceeded observed >> pure True)
                                `orElse` (stopped >> pure False)
                        if not proceed then pure ProcessStopped else do
                            deadline <- startProverTimer (wallTimeoutMicroseconds (vampireTimeLimit command))
                            modifyIORef' timers (deadline :)
                            _ <- startPipe $
                                captureCommunication ProverStdin
                                    (ByteString.hPut input (preparedVerificationInput request)
                                        `Exception.finally` hClose input)
                            _ <- startPipe (captureOutput ProverOutputStdout output stdoutCapture)
                            _ <- startPipe (captureOutput ProverOutputStderr err stderrCapture)
                            waiting <- async (restore (captureLifecycle
                                (vampireRuntimeWaitForProcess runtime process)))
                            writeIORef reaper (Just waiting)
                            pipes <- reverse <$> readIORef pipeTasks
                            restore $ atomically $
                                foldr orElse retry (taskFailed <$> pipes)
                                    `orElse` taskFailed waiting
                                    `orElse` (do
                                        traverse_ taskSucceeded pipes
                                        ProcessCompleted <$> taskSucceeded waiting)
                                    `orElse` (stopped >> pure ProcessStopped)
                                    `orElse` (awaitProverTimer deadline >> pure ProcessDeadline)
                -- The supervisor is the only cleanup owner. Catch cancellation
                -- here, before leaving any of its acquired resources behind.
                primary <- Exception.try run
                let primaryDescription = case primary of
                        Left failure -> boundedText (Text.pack (displayException (failure :: SomeException)))
                        Right ProcessStopped -> "request cancelled"
                        Right ProcessDeadline -> "request deadline exceeded"
                        Right ProcessCompleted{} -> "request completed"
                    noteCleanup message = do
                        let bounded = boundedText message
                        atomicModifyIORef' cleanupFailures \failures ->
                            (if bounded `elem` failures || length failures == 8
                                then failures else failures <> [bounded], ())
                        fault (primaryDescription <> "; cleanup: " <> bounded)
                    retryCleanup :: Text -> IO value -> IO value
                    retryCleanup stage action = Exception.mask \unmask ->
                        let again = do
                                attempt <- Exception.try (unmask action)
                                case attempt of
                                    Right value -> pure value
                                    Left (failure :: SomeException) -> do
                                        noteCleanup (stage <> ": " <> boundedText (Text.pack (displayException failure)))
                                        -- Even a second cancellation during
                                        -- backoff cannot abandon cleanup.
                                        void (Exception.try (unmask (threadDelay 10000))
                                            :: IO (Either SomeException ()))
                                        again
                        in again
                    cleanup = do
                        -- Killing the group first releases blocked pipe IO.
                        -- A failed signal/wait never relinquishes the process.
                        ownedGroup <- retryCleanup "process group" processGroup
                        retryCleanup "termination" (vampireRuntimeTerminateGroup runtime ownedGroup)
                        pipes <- readIORef pipeTasks
                        clocks <- readIORef timers
                        traverse_ stopOwnedTask pipes
                        traverse_ stopProverTimer clocks
                        waiting <- readIORef reaper
                        case waiting of
                            Nothing -> void (retryCleanup "reaping" (vampireRuntimeWaitForProcess runtime process))
                            Just task -> do
                                waited <- waitCatch task
                                case waited of
                                    Right _ -> pure ()
                                    Left failure -> do
                                        noteCleanup ("reaping: " <> boundedText (Text.pack (displayException failure)))
                                        void (retryCleanup "reaping" (vampireRuntimeWaitForProcess runtime process))
                        forM_ [input, output, err, childInput, childOutput, childError] \handle -> do
                            closed <- Exception.try (vampireRuntimeClosePipe runtime handle)
                            case closed of
                                Right () -> pure ()
                                Left (failure :: IOException) ->
                                    noteCleanup ("closing pipe: " <> exceptionText failure)
                    -- Keep cleanup insulated from further cancellation of the
                    -- supervisor, which always joins this task. Elapsed time
                    -- alone is not a cleanup failure: the worker slot and all
                    -- resources stay owned until settlement.
                    settle = retryCleanup "settlement" cleanup
                Exception.bracket
                    (async (restore settle) `Exception.catch` \(failure :: SomeException) -> do
                        noteCleanup ("starting cleanup: " <> Text.pack (displayException failure))
                        settle
                        Exception.throwIO failure)
                    (\cleanupTask -> do
                        (settled, interrupted) <- awaitOwnedTask (waitCatchSTM cleanupTask)
                        either Exception.throwIO pure settled
                        traverse_ Exception.throwIO interrupted)
                    \cleanupTask -> do
                        (settled, interrupted) <- awaitOwnedTask (waitCatchSTM cleanupTask)
                        either Exception.throwIO pure settled
                        partial <- capturedStreams stdoutCapture stderrCapture
                        failures <- readIORef cleanupFailures
                        let annotate result' = case (failures, result') of
                                ([], _) -> result'
                                (_, ProcessCancelled) -> ProcessCancelled
                                (_, ProcessFinished transcript) -> ProcessFinished (Left
                                    (ProverCleanupFailed
                                        (either id (const (ProverLifecycleFailed executable "cleanup failed")) transcript)
                                        failures))
                            finish result' = do
                                -- A handled request failure is still a normal
                                -- return, so it must not swallow cancellation
                                -- received while waiting for owned cleanup.
                                traverse_ Exception.throwIO interrupted
                                pure (annotate result')
                        case primary of
                            Left failure
                                | Just abort <- fromException failure -> finish (ProcessFinished
                                    (Left (supervisorAbortError executable partial abort)))
                                | Just (ioFailure :: IOException) <- fromException failure ->
                                    finish (ProcessFinished (Left
                                        (ProverLifecycleFailed executable (boundedText (exceptionText ioFailure)))))
                                | otherwise -> Exception.throwIO failure
                            Right completed -> finish $ case completed of
                                ProcessStopped -> ProcessCancelled
                                ProcessDeadline -> ProcessFinished (Left (ProverTimedOut executable
                                    (vampireTimeLimit command) (boundedCapturedStreams partial)))
                                ProcessCompleted exitCode -> ProcessFinished (completeTranscript executable exitCode partial)
    case result of
        Right value -> pure value
        Left failure
            | Just (RequestObserverFailure original) <- fromException failure ->
                Exception.throwIO original
            | Just (ioFailure :: IOException) <- fromException failure -> do
                started <- readIORef launched
                pure (ProcessFinished (Left
                    ((if started then ProverLifecycleFailed else ProverLaunchFailed)
                        executable (boundedText (exceptionText ioFailure)))))
            | otherwise -> Exception.throwIO failure
  where
    executable = vampireExecutable command

-- Wait only on owned-task completion cells (which do not throw in STM).
-- Further asynchronous cancellation is retained and rethrown after settlement;
-- it cannot sever the last reference to the process or a pipe task.
awaitOwnedTask :: STM value -> IO (value, Maybe SomeException)
awaitOwnedTask completed = Exception.mask \restore -> go restore Nothing
  where
    go restore interrupted = do
        result <- Exception.try (restore (atomically completed))
        case result of
            Right value -> pure (value, interrupted)
            Left failure -> go restore (firstInterruption [interrupted, Just failure])

stopOwnedTask :: Async value -> IO ()
stopOwnedTask task = Exception.mask_ do
    throwTo (asyncThreadId task) AsyncCancelled
    (_, interrupted) <- awaitOwnedTask (waitCatchSTM task)
    traverse_ Exception.throwIO interrupted

firstInterruption :: [Maybe SomeException] -> Maybe SomeException
firstInterruption [] = Nothing
firstInterruption (Just failure : _) = Just failure
firstInterruption (Nothing : rest) = firstInterruption rest

taskSucceeded :: Async value -> STM value
taskSucceeded task = waitCatchSTM task >>= either throwSTM pure

taskFailed :: Async value -> STM result
taskFailed task = waitCatchSTM task >>= either throwSTM (const retry)

completeTranscript
    :: FilePath -> ExitCode -> PartialCapturedStreams
    -> Either ProverProcessError CompletedTranscript
completeTranscript executable exitCode partial = case exitCode of
    ExitFailure signalCode | signalCode < 0 ->
        Left (ProverTerminatedBySignal executable (negate signalCode) (boundedCapturedStreams partial))
    _ -> do
        stdout <- decodeOutput executable ProverOutputStdout (partialStdout partial)
        stderr <- decodeOutput executable ProverOutputStderr (partialStderr partial)
        pure (CompletedTranscript exitCode (CompleteCapturedStreams stdout stderr))

runRequestObserver
    :: (PreparedVerificationRequest -> IO ())
    -> PreparedVerificationRequest
    -> IO ()
runRequestObserver observer request =
    UnliftIO.catchAny (observer request) (Exception.throwIO . RequestObserverFailure)

captureCommunication
    :: ProverStream
    -> IO a
    -> IO a
captureCommunication stream action =
    action `Exception.catch` \(err :: IOException) ->
        throwIO
            (SupervisorCommunicationFailed
                stream
                (exceptionText err))

captureOutput
    :: ProverOutputStream
    -> Handle
    -> IORef CaptureBuffer
    -> IO ()
captureOutput stream handle capture =
    captureCommunication (outputStream stream) go
  where
    go = do
        bytes <- ByteString.hGetSome handle captureChunkSize
        if ByteString.null bytes
            then pure ()
            else do
                exceeded <- appendCapturedChunk capture bytes
                if exceeded
                    then
                        throwIO
                            (SupervisorOutputLimitExceeded stream)
                    else go

outputStream :: ProverOutputStream -> ProverStream
outputStream = \case
    ProverOutputStdout ->
        ProverStdout
    ProverOutputStderr ->
        ProverStderr

captureLifecycle :: IO a -> IO a
captureLifecycle action =
    action `Exception.catch` \(err :: IOException) ->
        throwIO (SupervisorLifecycleFailed (exceptionText err))

emptyCaptureBuffer :: CaptureBuffer
emptyCaptureBuffer =
    CaptureBuffer
        { captureByteCount = 0
        , captureChunksReversed = []
        }

appendCapturedChunk
    :: IORef CaptureBuffer
    -> ByteString.ByteString
    -> IO Bool
appendCapturedChunk capture bytes =
    atomicModifyIORef' capture \buffer@CaptureBuffer{..} ->
        let remaining =
                vampireOutputByteLimit - captureByteCount
            retained =
                ByteString.take remaining bytes
            retainedLength =
                ByteString.length retained
            buffer' =
                buffer
                    { captureByteCount =
                        captureByteCount + retainedLength
                    , captureChunksReversed =
                        if ByteString.null retained
                            then captureChunksReversed
                            else retained : captureChunksReversed
                    }
        in (buffer', ByteString.length bytes > remaining)

capturedStreams
    :: IORef CaptureBuffer
    -> IORef CaptureBuffer
    -> IO PartialCapturedStreams
capturedStreams stdoutCapture stderrCapture =
    PartialCapturedStreams
        <$> capturedBytes stdoutCapture
        <*> capturedBytes stderrCapture

capturedBytes :: IORef CaptureBuffer -> IO ByteString.ByteString
capturedBytes capture =
    ByteString.concat
        . reverse
        . captureChunksReversed
        <$> readIORef capture

boundedTranscriptBytes :: Int
boundedTranscriptBytes = 32 * 1024

boundedTranscriptHalf :: Int
boundedTranscriptHalf = boundedTranscriptBytes `div` 2

boundedBytes :: ByteString.ByteString -> BoundedBytes
boundedBytes bytes =
    let original = ByteString.length bytes
    in if original <= boundedTranscriptBytes
        then
            BoundedBytes
                { boundedBytesOriginalCount = original
                , boundedBytesRetained = bytes
                , boundedBytesTruncated = False
                }
        else
            BoundedBytes
                { boundedBytesOriginalCount = original
                , boundedBytesRetained =
                    ByteString.take boundedTranscriptHalf bytes
                        <> ByteString.drop
                            (original - boundedTranscriptHalf)
                            bytes
                , boundedBytesTruncated = True
                }

boundedText :: Text -> Text
boundedText =
    decodeBoundedBytes . boundedBytes . TextEncoding.encodeUtf8

decodeBoundedBytes :: BoundedBytes -> Text
decodeBoundedBytes =
    TextEncoding.decodeUtf8With TextEncodingError.lenientDecode
        . boundedBytesRetained

boundedCapturedStreams
    :: PartialCapturedStreams
    -> BoundedCapturedStreams
boundedCapturedStreams PartialCapturedStreams{..} =
    BoundedCapturedStreams
        { boundedStdout = boundedBytes partialStdout
        , boundedStderr = boundedBytes partialStderr
        }

emptyBoundedCapturedStreams :: BoundedCapturedStreams
emptyBoundedCapturedStreams =
    BoundedCapturedStreams
        { boundedStdout = boundedBytes ByteString.empty
        , boundedStderr = boundedBytes ByteString.empty
        }

boundedCompletedStreams
    :: CompletedTranscript
    -> BoundedCapturedStreams
boundedCompletedStreams
        CompletedTranscript{completedStreams = CompleteCapturedStreams{..}} =
    BoundedCapturedStreams
        { boundedStdout =
            boundedBytes (TextEncoding.encodeUtf8 completedStdout)
        , boundedStderr =
            boundedBytes (TextEncoding.encodeUtf8 completedStderr)
        }

supervisorAbortError
    :: FilePath
    -> PartialCapturedStreams
    -> SupervisorAbort
    -> ProverProcessError
supervisorAbortError executable partial = \case
    SupervisorCommunicationFailed stream message ->
        ProverCommunicationFailed executable stream (boundedText message)
    SupervisorOutputLimitExceeded stream ->
        ProverOutputLimitExceeded
            executable
            stream
            (boundedCapturedStreams partial)
    SupervisorLifecycleFailed message ->
        ProverLifecycleFailed executable (boundedText message)

wallTimeoutMicroseconds :: TimeLimit -> Int
wallTimeoutMicroseconds (Seconds seconds) =
    fromInteger
        (min
            (toInteger (maxBound :: Int))
            ((toInteger seconds + vampireWallGraceSeconds)
                * 1000000))

terminateRemainingProcessGroup :: ProcessGroupID -> IO ()
terminateRemainingProcessGroup processGroup =
    ignoreMissingProcess
        (signalProcessGroup sigKILL processGroup)

ignoreMissingProcess :: IO () -> IO ()
ignoreMissingProcess action =
    action `Exception.catch` \(err :: IOException) ->
        if isDoesNotExistError err
            then pure ()
            else throwIO err

decodeOutput
    :: FilePath
    -> ProverOutputStream
    -> ByteString.ByteString
    -> Either ProverProcessError Text
decodeOutput executable stream bytes =
    case TextEncoding.decodeUtf8' bytes of
        Left err ->
            Left
                (ProverOutputMalformedUtf8
                    executable
                    stream
                    (boundedText (Text.pack (show err))))
        Right output ->
            Right output

exceptionText :: IOException -> Text
exceptionText =
    Text.pack . displayException

classifyVampireCompleted
    :: VampireTaskMode
    -> CompletedTranscript
    -> Either VampireProtocolError CanonicalAtpOutcome
classifyVampireCompleted mode CompletedTranscript{..} =
    do
        statuses <- statusesFromCompleteStreams completedStreams
        classifyVampireProtocol mode completedExitCode statuses

statusesFromCompleteStreams
    :: CompleteCapturedStreams
    -> Either VampireProtocolError [VampireStatus]
statusesFromCompleteStreams CompleteCapturedStreams{..}
    | Set.null malformed =
        Right statuses
    | otherwise =
        Left (MalformedVampireStatusLines malformed)
  where
    (malformed, statuses) =
        foldMap classifyLine
            (Text.lines completedStdout <> Text.lines completedStderr)

    classifyLine line =
        case parseMaybe vampireStatusParser line of
            Just status ->
                (mempty, [status])
            Nothing
                | "SZS status" `Text.isInfixOf` line ->
                    (Set.singleton line, [])
                | otherwise ->
                    mempty

vampireStatusFromText :: Text -> VampireStatus
vampireStatusFromText = \case
    "Theorem" -> StatusTheorem
    "CounterSatisfiable" -> StatusCounterSatisfiable
    "ContradictoryAxioms" -> StatusContradictoryAxioms
    "Timeout" -> StatusTimeout
    "ResourceOut" -> StatusResourceOut
    "GaveUp" -> StatusGaveUp
    "Unknown" -> StatusUnknown
    status -> UnsupportedStatus status

-- | Parse a Vampire SZS status line.
--
-- Recognizes both standard lines like:
--   % SZS status Timeout for 123
-- and lines prefixed by worker ids (seen with portfolio output), e.g.:
--   % (2581105)SZS status Timeout for
vampireStatusParser :: Parsec Void Text VampireStatus
vampireStatusParser = do
    _ <- Char.char '%'
    Char.hspace
    _ <- optional do
        _ <- Char.char '('
        _ <- some Char.digitChar
        _ <- Char.char ')'
        Char.hspace
    _ <- chunk "SZS"
    Char.hspace1
    _ <- chunk "status"
    Char.hspace1
    status <-
        takeWhile1P
            (Just "SZS status")
            (\character -> character /= ' ' && character /= '\t')
    _ <- takeRest
    pure (vampireStatusFromText status)
