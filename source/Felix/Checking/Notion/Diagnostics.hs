{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Bounded, descriptive counters. These never grant evidence or another
-- allowance. The fixed key domains keep tracing independent of source size.
module Felix.Checking.Notion.Diagnostics
    ( Operation(..), RegistrationFamily(..), RuleEvent(..), Phase(..), Outcome(..)
    , Diagnostics(..), emptyDiagnostics, countOperation, countFamilyWork
    , countPhaseWork, countCoreWork, countOutcome, addDiagnostics, subtractDiagnostics
    , Measurement(..), emptyMeasurement, addMeasurement
    , Report, Recorder, newReport, withRecorder, finishReport, withPhase
    , recordMeasurement, recordGroup, captureMeasurement, event, recordLeaf, recordWholeLeaf, measuringPhase, hasRejectedDebit
    , Completion(..), extendCompletion, complete, continueCompletion, finishCompletion
    ) where

import Base
import Control.Monad (when)
import Control.Concurrent.MVar qualified as MVar
import Data.Map.Strict qualified as Map
import Data.IORef
import Data.Text qualified as Text
import Data.Text.IO qualified as TextIO
import Numeric.Natural (Natural)
import System.Environment qualified as Environment
import System.IO qualified as IO
import UnliftIO qualified

data Operation
    = RegistryVisit | DuplicateRegistration | TemplateVisit | TemplateInterned
    | DescriptionLookup | DescriptionLookupWork | CatalogExtensionWork
    | SelectionPreparation | SelectionReuse | SourceInputMaterialization
    | OperandValueLeaf | OperandValueMemoHit | OperandValueNormalization
    | InitialRow | InitialResult | InitialView | ForwardView
    | ComponentRequest | ComponentResult
    | GroundInstance | PreparedGroundPremise | GroundDelivery | AnswerTuple
    | CandidatePair | SelectedProducer | AttemptedProducer | UniqueRequest | Delivery | CompletedRule | RepeatedJoin
    | ScopeInsertion | ScopeRebase | ProducerCompilation | LeafSearch | ReusedLeaf
    | ProofNode | SelectedProofNode | ProjectionNode | EmittedNode | ReplayNode
    deriving (Show, Eq, Ord)

-- Owners charge disjoint phases. Core work is a breakdown of phase work,
-- never an additional debit. Timings are collected only at owner boundaries.
data Phase = DeclarationPreparation | ScopePreparation | Expansion | Query | Proof
    deriving (Show, Eq, Ord, Enum, Bounded)

data Outcome = ExactDirect | FlexibleUniversal | SearchedSuccess | CompletedFailure | Exhausted
    deriving (Show, Eq, Ord, Enum, Bounded)

data RegistrationFamily
    = ViewFamily | NullaryFamily | ProviderFamily | BackwardFamily | FiniteFamily | GraphFamily
    | WholeFamily | SuppliedUniversalFamily
    deriving (Show, Eq, Ord)

data RuleEvent
    = Count !Operation !Natural
    | EnterRegistration !Natural
    | LeaveRegistration

data Diagnostics = Diagnostics
    { operationCounts :: !(Map Operation Natural)
    , familyInspections :: !(Map RegistrationFamily Natural)
    , phaseInspections :: !(Map Phase Natural)
    , coreInspections :: !(Map Phase Natural)
    , outcomeCounts :: !(Map Outcome Natural)
    } deriving (Show, Eq)

emptyDiagnostics :: Diagnostics
emptyDiagnostics = Diagnostics Map.empty Map.empty Map.empty Map.empty Map.empty

countOperation :: Operation -> Natural -> Diagnostics -> Diagnostics
countOperation operation amount counts = counts
    {operationCounts = Map.insertWith (+) operation amount (operationCounts counts)}

countFamilyWork :: RegistrationFamily -> Natural -> Diagnostics -> Diagnostics
countFamilyWork family amount counts = counts
    {familyInspections = Map.insertWith (+) family amount (familyInspections counts)}

countPhaseWork :: Phase -> Natural -> Diagnostics -> Diagnostics
countPhaseWork _ 0 counts = counts
countPhaseWork phase amount counts = counts
    {phaseInspections = Map.insertWith (+) phase amount (phaseInspections counts)}

countCoreWork :: Phase -> Natural -> Diagnostics -> Diagnostics
countCoreWork _ 0 counts = counts
countCoreWork phase amount counts = counts
    {coreInspections = Map.insertWith (+) phase amount (coreInspections counts)}

countOutcome :: Outcome -> Diagnostics -> Diagnostics
countOutcome outcome counts = counts
    {outcomeCounts = Map.insertWith (+) outcome 1 (outcomeCounts counts)}

addDiagnostics :: Diagnostics -> Diagnostics -> Diagnostics
addDiagnostics left right = Diagnostics
    (Map.unionWith (+) (operationCounts left) (operationCounts right))
    (Map.unionWith (+) (familyInspections left) (familyInspections right))
    (Map.unionWith (+) (phaseInspections left) (phaseInspections right))
    (Map.unionWith (+) (coreInspections left) (coreInspections right))
    (Map.unionWith (+) (outcomeCounts left) (outcomeCounts right))

-- The owner supplies successive snapshots of the same monotone account.
-- A reused prefix is not completed work and must not be added again.
subtractDiagnostics :: Diagnostics -> Diagnostics -> Diagnostics
subtractDiagnostics after before = Diagnostics
    (difference (operationCounts after) (operationCounts before))
    (difference (familyInspections after) (familyInspections before))
    (difference (phaseInspections after) (phaseInspections before))
    (difference (coreInspections after) (coreInspections before))
    (difference (outcomeCounts after) (outcomeCounts before))
  where
    difference :: Ord key => Map key Natural -> Map key Natural -> Map key Natural
    difference newer older = Map.filter (> 0) (Map.differenceWith (\new old -> Just (new - old)) newer older)

-- Physical work is additive; limit utilization is a high-water mark. A group
-- summary is a view of this account, not a second contribution to it.
data Measurement = Measurement
    { measuredDiagnostics :: !Diagnostics
    , phaseNanoseconds :: !(Map Phase Natural)
    , limitHighWater :: !(Map Text Natural)
    } deriving (Show, Eq)

emptyMeasurement :: Measurement
emptyMeasurement = Measurement emptyDiagnostics Map.empty Map.empty

addMeasurement :: Measurement -> Measurement -> Measurement
addMeasurement left right = Measurement
    (addDiagnostics (measuredDiagnostics left) (measuredDiagnostics right))
    (Map.unionWith (+) (phaseNanoseconds left) (phaseNanoseconds right))
    (Map.unionWith max (limitHighWater left) (limitHighWater right))

-- Owners publish a .rejected entry only when a resource debit was refused.
-- This is distinct from merely reaching a high-water mark equal to the cap.
hasRejectedDebit :: Measurement -> Bool
hasRejectedDebit = any (Text.isSuffixOf ".rejected") . Map.keys . limitHighWater


data Totals = Totals !Measurement !Natural !Natural !(Map Natural Natural)

-- Configuration is read once per verification. Each module has its own clock,
-- so concurrent module work cannot pause another module's phase.
data Report = DisabledReport | Report !(Maybe Text) !(IORef Totals) !(MVar.MVar ())
data Recorder = DisabledRecorder | Recorder !Report !(IORef Measurement) !(IORef (Maybe (Phase, Word64)))

-- A consumer carries this small value with its prepared proof until ordinary
-- authorization completes. It contains no recorder, search state or evidence.
data Completion = Completion
    { completionConsumer :: !Text
    , completionOrigin :: !Text
    , completionLeaves :: !Natural
    , completionOutcome :: !Text
    , completionMeasurement :: !Measurement
    , completionFields :: ![(Text, Text)]
    }

extendCompletion :: Measurement -> Completion -> Completion
extendCompletion measured completion = completion
    {completionMeasurement = addMeasurement (completionMeasurement completion) measured}

complete :: Recorder -> Completion -> IO ()
complete recorder completion = recordGroup recorder
    (completionConsumer completion) (completionOrigin completion) (completionLeaves completion)
    (completionOutcome completion) (completionMeasurement completion) (completionFields completion)

-- A resumed proof owner adds only its own delta. Physical totals were already
-- recorded by that owner; completing a group adds its histogram entry once.
continueCompletion
    :: UnliftIO.MonadUnliftIO m
    => Recorder -> Completion -> m (Either failure value)
    -> m (Either failure (value, Completion))
continueCompletion recorder completion action = do
    (result, measured) <- captureMeasurement recorder (withPhase recorder Proof action)
    let next = extendCompletion measured completion
    case result of
        Left failure -> do
            liftIO (complete recorder next{completionOutcome = if hasRejectedDebit measured then "exhausted" else "failed"})
            pure (Left failure)
        Right value -> pure (Right (value, next))

finishCompletion
    :: UnliftIO.MonadUnliftIO m
    => Recorder -> Completion -> m (Either failure value) -> m (Either failure value)
finishCompletion recorder completion action = do
    result <- continueCompletion recorder completion action
    for result (\(value, finished) -> liftIO (complete recorder finished) >> pure value)

newReport :: IO Report
newReport = do
    aggregate <- Environment.lookupEnv "FELIX_FORMATION_STATS"
    detailed <- fmap Text.pack <$> Environment.lookupEnv "FELIX_FORMATION_COST"
    if aggregate /= Just "1" && isNothing detailed
        then pure DisabledReport
        else Report detailed <$> newIORef (Totals emptyMeasurement 0 0 Map.empty) <*> MVar.newMVar ()

newRecorder :: Report -> IO Recorder
newRecorder DisabledReport = pure DisabledRecorder
newRecorder report = Recorder report <$> newIORef emptyMeasurement <*> newIORef Nothing

withRecorder :: UnliftIO.MonadUnliftIO m => Report -> (Recorder -> m value) -> m value
withRecorder DisabledReport action = action DisabledRecorder
withRecorder report action = UnliftIO.bracket (liftIO (newRecorder report))
    (liftIO . finishRecorder) action

withPhase :: UnliftIO.MonadUnliftIO m => Recorder -> Phase -> m value -> m value
withPhase DisabledRecorder _ action = action
withPhase recorder phase action = UnliftIO.bracket (liftIO (enterPhase recorder phase))
    (liftIO . leavePhase recorder) (const action)

recordMeasurement :: Recorder -> Measurement -> IO ()
recordMeasurement DisabledRecorder _ = pure ()
recordMeasurement (Recorder _ reference _) delta = modifyIORef' reference (`addMeasurement` delta)

-- Select optional instrumentation before evaluating an expensive pure owner.
measuringPhase :: Recorder -> Phase -> IO Bool
measuringPhase DisabledRecorder _ = pure False
measuringPhase (Recorder _ _ clock) phase = (== Just phase) . fmap fst <$> readIORef clock

snapshot :: Recorder -> IO Measurement
snapshot DisabledRecorder = pure emptyMeasurement
snapshot (Recorder _ reference clock) = do
    measured <- readIORef reference
    active <- readIORef clock
    case active of
        Nothing -> pure measured
        Just (phase, start) -> do
            now <- getMonotonicTimeNSec
            pure (addElapsed phase start now measured)

-- Capture an owner's complete local account, including maxima, then merge it
-- back exactly once. Subtracting cumulative maxima would retain an unrelated
-- earlier group's high-water mark. Nested owners use the same module recorder;
-- brackets restore the enclosing account even on cancellation.
captureMeasurement :: UnliftIO.MonadUnliftIO m => Recorder -> m value -> m (value, Measurement)
captureMeasurement DisabledRecorder action = (\value -> (value, emptyMeasurement)) <$> action
captureMeasurement recorder@(Recorder _ reference clock) action = UnliftIO.bracket
    (liftIO takeAccount)
    (\enclosing -> liftIO do
        completed <- takeAccount
        writeIORef reference (addMeasurement enclosing completed))
    (\_ -> do
        value <- action
        measured <- liftIO (snapshot recorder)
        pure (value, measured))
  where
    takeAccount = do
        now <- getMonotonicTimeNSec
        measured <- readIORef reference
        active <- readIORef clock
        let completed = maybe measured (\(phase, start) -> addElapsed phase start now measured) active
        writeIORef reference emptyMeasurement
        writeIORef clock ((\(phase, _) -> (phase, now)) <$> active)
        pure completed

addElapsed :: Phase -> Word64 -> Word64 -> Measurement -> Measurement
addElapsed phase start end measured = measured
    {phaseNanoseconds = Map.insertWith (+) phase (fromIntegral (end - start)) (phaseNanoseconds measured)}

-- Owner boundaries use bracket, including ordinary failures and exceptions.
-- The token contains only the enclosing phase; no span tree is retained.
enterPhase :: Recorder -> Phase -> IO (Maybe Phase)
enterPhase DisabledRecorder _ = pure Nothing
enterPhase (Recorder _ reference clock) phase = do
    now <- getMonotonicTimeNSec
    previous <- readIORef clock
    for_ previous (\(enclosing, start) -> modifyIORef' reference (addElapsed enclosing start now))
    writeIORef clock (Just (phase, now))
    pure (fst <$> previous)

leavePhase :: Recorder -> Maybe Phase -> IO ()
leavePhase DisabledRecorder _ = pure ()
leavePhase (Recorder _ reference clock) previous = do
    now <- getMonotonicTimeNSec
    active <- readIORef clock
    for_ active (\(phase, start) -> modifyIORef' reference (addElapsed phase start now))
    writeIORef clock ((\phase -> (phase, now)) <$> previous)

finishRecorder :: Recorder -> IO ()
finishRecorder DisabledRecorder = pure ()
finishRecorder recorder@(Recorder (Report _ reference _) _ _) = do
    measured <- snapshot recorder
    atomicModifyIORef' reference (\(Totals total groups leaves histogram) ->
        (Totals (addMeasurement total measured) groups leaves histogram, ()))
finishRecorder Recorder{} = impossible "enabled formation recorder has no report"

recordGroup :: Recorder -> Text -> Text -> Natural -> Text -> Measurement -> [(Text, Text)] -> IO ()
recordGroup DisabledRecorder _ _ _ _ _ _ = pure ()
recordGroup (Recorder (Report detailed reference lock) _ _) consumer origin leaves outcome measured fields = do
    let work = sum (phaseInspections (measuredDiagnostics measured))
    atomicModifyIORef' reference (\(Totals total groups count histogram) ->
        (Totals total (groups + 1) (count + leaves) (Map.insertWith (+) work 1 histogram), ()))
    for_ detailed (\selected -> when (selected `Text.isInfixOf` origin)
        (emit lock "group" (("consumer", consumer) : ("source", origin) :
            ("leaves", shown leaves) : ("outcome", outcome) : fields <> measurementFields measured)))
recordGroup Recorder{} _ _ _ _ _ _ = impossible "enabled formation recorder has no report"

-- Optional events use cached selection and no clock or RTS sampling. They are
-- explanations, never inputs to aggregate work or timing totals.
event :: Recorder -> Text -> Text -> IO ()
event (Recorder (Report (Just selected) _ lock) _ _) origin detail =
    when (selected `Text.isInfixOf` origin) (emit lock "event" [("source", origin), ("detail", detail)])
event _ _ _ = pure ()

-- Atomic cohort labels deliberately use the logical requirement and source
-- site, never transient formula/arena IDs. Reused leaves keep their occurrences.
recordLeaf :: Recorder -> Text -> Text -> Text -> Outcome -> Bool -> IO ()
recordLeaf = recordRequirement "atomic"

recordWholeLeaf :: Recorder -> Text -> Text -> Text -> Outcome -> Bool -> IO ()
recordWholeLeaf = recordRequirement "whole"

recordRequirement :: Text -> Recorder -> Text -> Text -> Text -> Outcome -> Bool -> IO ()
recordRequirement kind (Recorder (Report (Just selected) _ lock) _ _) consumer origin requirement outcome reused =
    when (selected `Text.isInfixOf` origin) (emit lock "leaf"
        [("consumer", consumer), ("source", origin), ("kind", kind),
         ("requirement", requirement), ("outcome", shown outcome), ("reused", shown reused)])
recordRequirement _ _ _ _ _ _ _ = pure ()

finishReport :: Report -> IO ()
finishReport DisabledReport = pure ()
finishReport (Report _ reference lock) = do
    Totals measured groups leaves histogram <- readIORef reference
    emit lock "summary" (("work-version", "1") : ("groups", shown groups) : ("leaves", shown leaves)
        : measurementFields measured <> [("hist." <> shown work, shown count) | (work, count) <- Map.toAscList histogram])

measurementFields :: Measurement -> [(Text, Text)]
measurementFields measured =
    enumFields "count." (operationCounts counts)
    <> enumFields "family-work." (familyInspections counts)
    <> enumFields "phase-work." (phaseInspections counts)
    <> enumFields "core-work." (coreInspections counts)
    <> enumFields "leaf." (outcomeCounts counts)
    <> enumFields "time-ns." (phaseNanoseconds measured)
    <> [("limit." <> key, shown value) | (key, value) <- Map.toAscList (limitHighWater measured)]
  where
    counts = measuredDiagnostics measured
    enumFields :: Show key => Text -> Map key Natural -> [(Text, Text)]
    enumFields prefix fields = [(prefix <> shown key, shown value) | (key, value) <- Map.toAscList fields]

shown :: Show value => value -> Text
shown = Text.pack . show

-- Text IO can release the handle between buffer chunks. One report lock keeps
-- records from concurrent module workers intact, including long leaf labels.
emit :: MVar.MVar () -> Text -> [(Text, Text)] -> IO ()
emit lock kind fields = do
    record <- UnliftIO.evaluate (Text.intercalate "\t"
        ("formation-v1" : kind : [key <> "=" <> escape value | (key, value) <- fields]))
    MVar.withMVar lock (\_ -> TextIO.hPutStrLn IO.stderr record)
  where
    escape = Text.concatMap (\character -> case character of
        '\\' -> "\\\\"; '\t' -> "\\t"; '\n' -> "\\n"; '\r' -> "\\r"; _ -> Text.singleton character)
