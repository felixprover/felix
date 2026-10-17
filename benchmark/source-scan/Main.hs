{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Main where

import Base

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Control.Monad (unless)
import Criterion.Main (bench, bgroup, defaultMain, whnf)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Int (Int64)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Felix.Cache.Codec (cacheEpochValue, currentCacheEpoch)
import Felix.Math.Codec (mathematicalDigestHex)
import Felix.Source
import Felix.Source.Content (IdentifiedLoadedSource)
import Felix.Source.Graph qualified as SourceGraph
import Felix.Test.SourceScan.Candidate
import Felix.Test.SourceScan.Observation
import Felix.Workspace qualified as Workspace
import GHC.Conc (getAllocationCounter)
import GHC.Stats (RTSStats)
import GHC.Stats qualified as RTS
import System.Environment (getArgs, withArgs)
import System.IO (stdout)
import System.Mem (performGC)


data BenchmarkSource = BenchmarkSource
    { benchmarkSourceAddress :: !LogicalSourceAddress
    , benchmarkSourceReadPath :: !FilePath
    , benchmarkSourceIdentified :: !IdentifiedLoadedSource
    , benchmarkSourceBytes :: !ByteString
    }
    deriving stock (Generic)
    deriving anyclass (NFData)

data BenchmarkCorpus = BenchmarkCorpus
    { benchmarkCorpusManifest :: !CorpusManifest
    , benchmarkCorpusSources :: ![BenchmarkSource]
    , benchmarkCorpusByteCount :: !Word64
    , benchmarkCorpusLineCount :: !Word64
    }
    deriving stock (Generic)
    deriving anyclass (NFData)

data BenchmarkCaseInputs = BenchmarkCaseInputs
    { benchmarkCandidateInputs :: ![CandidateSourceInput] }

data BenchmarkCaseResult
    = BenchmarkCandidateResult !CandidateCaseResult

main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        "criterion" : root : criterionArguments ->
            runCriterion root criterionArguments
        ["space", root, rawCase] ->
            case parseObservationCase rawCase of
                Nothing -> fail ("unknown source-scan case: " <> rawCase)
                Just selectedCase -> runSpace root selectedCase
        ["manifest", root] ->
            runManifest root
        _ ->
            fail
                (unlines
                    [ "usage: source-scan-bench criterion ROOT [CRITERION-OPTIONS...]"
                    , "       source-scan-bench space ROOT CASE"
                    , "       source-scan-bench manifest ROOT"
                    ])

runManifest :: FilePath -> IO ()
runManifest root = do
    corpus <- prepareBenchmarkCorpus root
    writeText (renderCorpusManifest (benchmarkCorpusManifest corpus))
    writeText
        ("source-bytes "
            <> Text.pack (show (benchmarkCorpusByteCount corpus))
            <> "\n")
    writeText
        ("source-lines "
            <> Text.pack (show (benchmarkCorpusLineCount corpus))
            <> "\n")
    writeText
        ("cache-epoch "
            <> Text.pack (show (cacheEpochValue currentCacheEpoch))
            <> "\n")

runCriterion :: FilePath -> [String] -> IO ()
runCriterion root criterionArguments = do
    corpus <- prepareBenchmarkCorpus root
    let inputs = benchmarkCaseInputs corpus
    _ <- evaluate (forceBenchmarkCaseInputs inputs)
    comparativeRecords <- traverse
        (prepareCompactRecord corpus inputs)
        comparativeObservationCases
    spanRecord <- prepareCompactRecord corpus inputs PresentationSpansCase
    let records =
            take 2 comparativeRecords
                <> [spanRecord]
                <> drop 2 comparativeRecords
    _ <- evaluate (force records)
    writeBenchmarkHeader root corpus
    traverse_ (writeText . renderCompactCaseRecord) records
    hFlush stdout
    performGC
    withArgs criterionArguments
        (defaultMain
            [ bgroup "source-scan"
                [ bench (Text.unpack (observationCaseName selectedCase))
                    (whnf
                        (runAndForceBenchmarkCase selectedCase)
                        inputs)
                | selectedCase <- candidateObservationCases
                ]
            ])

runSpace :: FilePath -> ObservationCase -> IO ()
runSpace root selectedCase = do
    corpus <- prepareBenchmarkCorpus root
    enabled <- RTS.getRTSStatsEnabled
    unless enabled
        (fail "space mode requires +RTS -T")
    let inputs = benchmarkCaseInputs corpus
        action =
            either
                (error . Text.unpack)
                id
                (runBenchmarkCase selectedCase inputs)
    _ <- evaluate (force corpus)
    _ <- evaluate (forceBenchmarkCaseInputs inputs)
    performGC
    initialStats <- RTS.getRTSStats
    initialMonotonic <- getMonotonicTimeNSec
    initialAllocationCounter <- getAllocationCounter
    raw <- evaluate action
    evaluate (forceBenchmarkCaseResult raw)
    finalAllocationCounter <- getAllocationCounter
    finalMonotonic <- getMonotonicTimeNSec
    finalStats <- RTS.getRTSStats
    normalized <- either (fail . Text.unpack) pure
        (normalizeBenchmarkCaseResult inputs raw)
    let record = compactCaseRecord
            selectedCase
            (corpusManifestDigest (benchmarkCorpusManifest corpus))
            normalized
    _ <- evaluate (force record)
    writeBenchmarkHeader root corpus
    writeText (renderCompactCaseRecord record)
    writeStatsDelta
        (finalMonotonic - initialMonotonic)
        (initialAllocationCounter - finalAllocationCounter)
        initialStats
        finalStats

prepareCompactRecord
    :: BenchmarkCorpus
    -> BenchmarkCaseInputs
    -> ObservationCase
    -> IO CompactCaseRecord
prepareCompactRecord corpus inputs selectedCase = do
    raw <- either (fail . Text.unpack) pure
        (runBenchmarkCase selectedCase inputs)
    evaluate (forceBenchmarkCaseResult raw)
    normalized <- either (fail . Text.unpack) pure
        (normalizeBenchmarkCaseResult inputs raw)
    let record = compactCaseRecord
            selectedCase
            (corpusManifestDigest (benchmarkCorpusManifest corpus))
            normalized
    evaluate (force record)

runAndForceBenchmarkCase
    :: ObservationCase
    -> BenchmarkCaseInputs
    -> ()
runAndForceBenchmarkCase selectedCase inputs =
    case runBenchmarkCase selectedCase inputs of
        Left failure -> error (Text.unpack failure)
        Right result -> forceBenchmarkCaseResult result

runBenchmarkCase
    :: ObservationCase
    -> BenchmarkCaseInputs
    -> Either Text BenchmarkCaseResult
runBenchmarkCase selectedCase inputs =
    BenchmarkCandidateResult
        <$> runCandidateCase
            selectedCase
            (benchmarkCandidateInputs inputs)

forceBenchmarkCaseResult :: BenchmarkCaseResult -> ()
forceBenchmarkCaseResult = \case
    BenchmarkCandidateResult result ->
        forceCandidateCaseResult result

normalizeBenchmarkCaseResult
    :: BenchmarkCaseInputs
    -> BenchmarkCaseResult
    -> Either Text [(LogicalSourceAddress, NormalizedSourceOutcome)]
normalizeBenchmarkCaseResult inputs = \case
    BenchmarkCandidateResult result ->
        normalizeCandidateCaseResult
            (benchmarkCandidateInputs inputs)
            result

benchmarkCaseInputs :: BenchmarkCorpus -> BenchmarkCaseInputs
benchmarkCaseInputs corpus =
    BenchmarkCaseInputs
        { benchmarkCandidateInputs = candidateInputs corpus }

candidateObservationCases :: [ObservationCase]
candidateObservationCases =
    [ PrefixCase
    , VerificationCompletionCase
    , PresentationSpansCase
    , PresentationDecodedCase
    ]

forceBenchmarkCaseInputs :: BenchmarkCaseInputs -> ()
forceBenchmarkCaseInputs inputs =
    forceCandidateSourceInputs (benchmarkCandidateInputs inputs)

candidateInputs :: BenchmarkCorpus -> [CandidateSourceInput]
candidateInputs corpus =
    [ CandidateSourceInput
        { candidateSourceAddress = benchmarkSourceAddress source
        , candidateSourceIdentified = benchmarkSourceIdentified source
        }
    | source <- benchmarkCorpusSources corpus
    ]

prepareBenchmarkCorpus :: FilePath -> IO BenchmarkCorpus
prepareBenchmarkCorpus root = do
    environment <- Workspace.prepareDefaultWorkspaceEnvironment
        >>= either (fail . show) pure
    request <- Workspace.prepareWorkspaceRoot environment root
        >>= either (fail . show) pure
    graph <- Workspace.prepareSourceGraph environment request
        >>= either (fail . show) pure
    let nodes = NonEmpty.toList
            (SourceGraph.sourceGraphImportedBeforeImporter graph)
        sources = benchmarkSource <$> nodes
        rootAddress = logicalAddress
            (SourceGraph.sourceGraphRootSource graph)
        mountOrder =
            [ sourceMountIdText (sourceMountIdentifier mount)
            | mount <- sourceMountList
                (Workspace.workspaceSourceMounts environment)
            ]
        manifestInputs =
            [ ManifestSourceInput
                { manifestInputAddress = benchmarkSourceAddress source
                , manifestInputReadPath = benchmarkSourceReadPath source
                , manifestInputBytes = benchmarkSourceBytes source
                }
            | source <- sources
            ]
        manifest = makeCorpusManifest rootAddress mountOrder manifestInputs
        corpus = BenchmarkCorpus
            { benchmarkCorpusManifest = manifest
            , benchmarkCorpusSources = sources
            , benchmarkCorpusByteCount =
                sum
                    (fromIntegral . ByteString.length . benchmarkSourceBytes
                        <$> sources)
            , benchmarkCorpusLineCount =
                sum (sourceLineCount . benchmarkSourceBytes <$> sources)
            }
    evaluate (force corpus)
  where
    benchmarkSource node =
        let loaded = SourceGraph.sourceNodeLoaded node
            source = loadedSource loaded
        in BenchmarkSource
            { benchmarkSourceAddress = logicalAddress source
            , benchmarkSourceReadPath =
                canonicalPathFilePath (resolvedSourceCanonicalPath source)
            , benchmarkSourceIdentified =
                SourceGraph.sourceNodeIdentified node
            , benchmarkSourceBytes = loadedBytes loaded
            }

logicalAddress :: ResolvedSource -> LogicalSourceAddress
logicalAddress source =
    LogicalSourceAddress
        { logicalSourceMount = sourceMountIdText (resolvedSourceMount source)
        , logicalSourceRelativePath =
            Text.pack
                (safeRelativePathFilePath
                    (resolvedSourceRelativePath source))
        }

sourceLineCount :: ByteString -> Word64
sourceLineCount bytes
    | ByteString.null bytes = 0
    | ByteString.last bytes == 0x0a =
        fromIntegral (ByteString.count 0x0a bytes)
    | otherwise =
        fromIntegral (ByteString.count 0x0a bytes) + 1

writeBenchmarkHeader :: FilePath -> BenchmarkCorpus -> IO ()
writeBenchmarkHeader root corpus = do
    writeText "source-scan-benchmark-v1\n"
    writeText ("root-command " <> Text.pack root <> "\n")
    writeText
        ("corpus-digest "
            <> mathematicalDigestHex
                (corpusManifestDigest (benchmarkCorpusManifest corpus))
            <> "\n")
    writeText
        ("source-count "
            <> Text.pack
                (show
                    (corpusManifestSourceCount
                        (benchmarkCorpusManifest corpus)))
            <> "\n")
    writeText
        ("source-bytes "
            <> Text.pack (show (benchmarkCorpusByteCount corpus))
            <> "\n")
    writeText
        ("source-lines "
            <> Text.pack (show (benchmarkCorpusLineCount corpus))
            <> "\n")
    writeText
        ("cache-epoch "
            <> Text.pack (show (cacheEpochValue currentCacheEpoch))
            <> "\n")

writeStatsDelta :: Word64 -> Int64 -> RTSStats -> RTSStats -> IO ()
writeStatsDelta monotonicDelta allocationCounterDelta initial final =
    writeText
        (Text.unlines
            [ "source-scan-space-delta-v1"
            , field "monotonic_elapsed_ns" monotonicDelta
            , field "thread_allocated_bytes" allocationCounterDelta
            , field "allocated_bytes"
                (RTS.allocated_bytes final - RTS.allocated_bytes initial)
            , field "copied_bytes"
                (RTS.copied_bytes final - RTS.copied_bytes initial)
            , field "gcs"
                (RTS.gcs final - RTS.gcs initial)
            , field "major_gcs"
                (RTS.major_gcs final - RTS.major_gcs initial)
            , field "mutator_cpu_ns"
                (RTS.mutator_cpu_ns final - RTS.mutator_cpu_ns initial)
            , field "mutator_elapsed_ns"
                (RTS.mutator_elapsed_ns final - RTS.mutator_elapsed_ns initial)
            , field "gc_cpu_ns"
                (RTS.gc_cpu_ns final - RTS.gc_cpu_ns initial)
            , field "gc_elapsed_ns"
                (RTS.gc_elapsed_ns final - RTS.gc_elapsed_ns initial)
            , field "cpu_ns"
                (RTS.cpu_ns final - RTS.cpu_ns initial)
            , field "elapsed_ns"
                (RTS.elapsed_ns final - RTS.elapsed_ns initial)
            ])
  where
    field :: Show value => Text -> value -> Text
    field name value = name <> " " <> Text.pack (show value)

writeText :: Text -> IO ()
writeText = ByteString.hPut stdout . Text.encodeUtf8
