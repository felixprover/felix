{-# LANGUAGE NoImplicitPrelude #-}

module Scaling (runScaling) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation (checkedFoundation)
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Math.Codec (hashBlake2b256)
import Felix.Module
import Felix.Source (safeRelativePath)

import Control.DeepSeq (force, rnf)
import Control.Exception (evaluate)
import Control.Monad (foldM, unless)
import Data.IORef (newIORef, readIORef)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.IO.Utf8 qualified as Text
import Data.Word (Word)
import GHC.Conc (getAllocationCounter)
import GHC.Stats qualified as RTS
import System.Mem (performMajorGC)


data Prepared
    = Compare
        !(GlobalTyping ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
    | Normalize
        !(Conversion.ConversionRecoveryTyping ObjectId)
        !(ScopedCheckedCore ObjectId)
    | Residualize
        !(Conversion.ConversionRecoveryTyping ObjectId)
        !(ScopedCheckedCore ObjectId)

type Observation = (Text, Word, Word)

operationLimit :: Conversion.ConversionLimit
operationLimit = Conversion.conversionLimit 2000000

runScaling :: String -> Int -> Int -> IO ()
runScaling family size repetitions = do
    unless (size > 0 && size <= 4096 && repetitions > 0)
        (fail "scaling needs size 1..4096 and positive repetitions")
    setupStarted <- getMonotonicTimeNSec
    setupAllocation <- getAllocationCounter
    prepared <- prepare family size
    forcePrepared prepared
    setupAfterAllocation <- getAllocationCounter
    setupFinished <- getMonotonicTimeNSec
    let observation = runConversion prepared
    _ <- evaluate (force observation)
    Text.putStrLn (Text.unwords
        [ "conversion-scaling-v2", Text.pack family
        , "size=" <> shown size, "repetitions=" <> shown repetitions
        , "c5-limit=2000000"
        ])
    Text.putStrLn ("observation=" <> shown observation)
    Text.putStrLn (Text.unwords
        [ "setup-bytes=" <> shown (setupAllocation - setupAfterAllocation)
        , "setup-ns=" <> shown (setupFinished - setupStarted)
        ])
    measure repetitions prepared observation

measure :: Int -> Prepared -> Observation -> IO ()
measure repetitions prepared (expectedOutcome, expectedCost, expectedNodes) = do
    enabled <- RTS.getRTSStatsEnabled
    unless enabled (fail "scaling measurements require +RTS -T -RTS")
    -- Reading the input inside the IO loop prevents a pure result from being
    -- shared across iterations. Setup is outside the measured batch.
    input <- newIORef prepared
    performMajorGC
    beforeStats <- RTS.getRTSStats
    beforeAllocation <- getAllocationCounter
    started <- getMonotonicTimeNSec
    total <- foldM (\accumulator _ -> do
        current <- readIORef input
        (outcome, cost, nodes) <- evaluate (force (runConversion current))
        evaluate (accumulator + cost + nodes + fromIntegral (Text.length outcome)))
        (0 :: Word) [1 .. repetitions]
    finished <- getMonotonicTimeNSec
    afterAllocation <- getAllocationCounter
    afterStats <- RTS.getRTSStats
    unless
        (total == fromIntegral repetitions
            * (expectedCost + expectedNodes + fromIntegral (Text.length expectedOutcome)))
        (fail "repeated scaling observations changed")
    performMajorGC
    finalStats <- RTS.getRTSStats
    Text.putStrLn (Text.unwords
        [ "batch-bytes=" <> shown (beforeAllocation - afterAllocation)
        , "batch-ns=" <> shown (finished - started)
        , "batch-gc-ns=" <> shown
            (RTS.gc_elapsed_ns afterStats - RTS.gc_elapsed_ns beforeStats)
        , "process-max-live-bytes=" <> shown (RTS.max_live_bytes finalStats)
        , "checksum=" <> shown total
        ])

prepare :: String -> Int -> IO Prepared
prepare family size = do
    foundation <- require checkedFoundation
    relative <- require (safeRelativePath "benchmark/conversion/scaling.tex")
    let theory = theoryId foundation
        owner = moduleNameFromParts
            (sourceNamespaceIdFromDigest
                (hashBlake2b256 "felix/conversion/scaling-v1"))
            relative
        width = if family == "snapshot-width" then size else 1
        objectType = if family == "spine-normalization"
            then foldr (const (TyArrow TySet)) TySet [1 .. size]
            else TySet
        objects =
            [ opaqueObject theory
                (opaqueDeclarationSeed owner (localDeclarationOrdinal ordinal)
                    SignatureDeclaration (generatedObjectSlot 0)) objectType
            | ordinal <- [0 .. fromIntegral width - 1]
            ]
    closure <- require (validateObjectClosure theory objects)
    emptyClosure <- require (validateObjectClosure theory [])
    _ <- evaluate (force (Set.toList (checkedObjectIds closure)))
    let typing = globalTypingFromClosure closure
        emptyTyping = globalTypingFromClosure emptyClosure
        recovery = Conversion.ConversionRecoveryTyping typing typing
        global = case objects of
            firstObject : _ -> CGlobal (assertedObjectId firstObject)
            [] -> error "positive scaling width produced no object"
        check context = require . checkScopedCanonicalCore typing context
        compareRoots operation context left right =
            Compare operation <$> check context left <*> check context right
        normalize context term = Normalize recovery <$> check context term
        residualize context term = Residualize recovery <$> check context term
        deepSet = iterateTerm size (CApp (CIntrinsic PowerSet)) global
        deepBeta = iterateTerm size (CApp (CLam TySet (CBound 0))) global
        repeated count term = foldr CAnd CTruth (replicate count term)
        forceArgument count = CApp
            (CLam TySet (repeated count (CEq TySet (CBound 0) (COpaqueInteger 0))))
            deepBeta
        unusedDefinition operation = do
            unless (size <= 32) (fail "unused definition argument is bounded to 32 source layers")
            let pair left right = CApp (CApp (CIntrinsic PairSet) left) right
                argument = iterateTerm size
                    (CApp (CLam TySet (pair (CBound 0) (CBound 0))))
                    (CIntrinsic Empty)
            operation [TyArrow TySet TySet] (CApp (CBound 0) argument)
    case family of
        "context-outer" -> normalize (replicate size TySet)
            (repeated size (CEq TySet (CBound (fromIntegral size - 1)) global))
        "unused-argument" -> compareRoots typing []
            (CApp (CLam TySet CTruth) deepSet) CFalsum
        "unused-missing-global" -> compareRoots emptyTyping []
            (CApp (CLam TySet CTruth) deepSet) CTruth
        "spine-normalization" -> normalize []
            (foldl' CApp global (replicate size (COpaqueInteger 0)))
        "repeated-forcing" -> normalize [] (forceArgument size)
        "rare-forcing" -> normalize [] (forceArgument 2)
        "output-growth" -> do
            unless (size <= 32) (fail "output-growth is bounded to 32 source layers")
            normalize [] (iterateTerm size
                (CApp (CLam TyProp (CAnd (CBound 0) (CBound 0)))) CTruth)
        "definition-unused-output" -> unusedDefinition normalize
        "definition-unused-head" -> unusedDefinition residualize
        "matcher-unused-output" -> do
            unless (size <= 32) (fail "unused matcher argument is bounded to 32 source layers")
            let pair left right = CApp (CApp (CIntrinsic PairSet) left) right
                argument = iterateTerm size
                    (CApp (CLam TySet (pair (CBound 0) (CBound 0))))
                    (CIntrinsic Empty)
            normalize [TySet] (CApp (CApp (CIntrinsic Member) argument) (CBound 0))
        "matcher-unused-replay" -> do
            unless (size <= 32) (fail "unused matcher replay is bounded to 32 source layers")
            let pair left right = CApp (CApp (CIntrinsic PairSet) left) right
                duplicate = CLam TySet (pair (CBound 0) (CBound 0))
                previous = iterateTerm (size - 1) (CApp duplicate) (CIntrinsic Empty)
                member term = CApp (CApp (CIntrinsic Member) term) (CBound 0)
            compareRoots typing [TySet]
                (member (pair previous previous)) (member (CApp duplicate previous))
        "neutral-late-mismatch" -> compareRoots typing []
            (iterateTerm size (CApp (CIntrinsic PowerSet)) (COpaqueInteger 0))
            (iterateTerm size (CApp (CIntrinsic PowerSet)) (COpaqueInteger 1))
        "logical-root" -> residualize []
            (CApp (CLam TyProp (CBound 0))
                (iterateTerm size (CAnd CTruth) (CEq TySet global global)))
        "snapshot-width" -> compareRoots typing []
            (CApp (CLam TySet (CBound 0)) global) global
        _ -> fail "unknown scaling family"

iterateTerm :: Int -> (value -> value) -> value -> value
iterateTerm count step initial = foldl' (\value _ -> step value) initial [1 .. count]

forcePrepared :: Prepared -> IO ()
forcePrepared = \case
    Compare _ left right -> evaluate (rnf left `seq` rnf right)
    Normalize _ root -> evaluate (rnf root)
    Residualize _ root -> evaluate (rnf root)

runConversion :: Prepared -> Observation
runConversion = \case
    Compare typing left right -> observeDecision
        (Conversion.convertibleChecked typing operationLimit left right)
    Normalize typing root -> observeSyntax
        (Conversion.betaNormalizeChecked typing operationLimit root)
    Residualize typing root -> observeSyntax
        (Conversion.residualizeHeadChecked typing operationLimit root)

observeDecision :: Conversion.ConversionReport Conversion.ConversionDecision -> Observation
observeDecision report =
    ( either (Text.pack . show) (Text.pack . show) (Conversion.conversionResult report)
    , Conversion.conversionCostAmount (Conversion.conversionCost report)
    , 0
    )

observeSyntax
    :: Conversion.ConversionReport (ScopedCheckedCore ObjectId)
    -> Observation
observeSyntax report = case Conversion.conversionResult report of
    Left failure -> (shown failure, cost, 0)
    Right root ->
        rnf (scopedCoreContext root, scopedCoreType root) `seq`
            ("recovered", cost, termNodes (scopedCoreTerm root))
  where
    cost = Conversion.conversionCostAmount (Conversion.conversionCost report)

termNodes :: CanonicalTerm ObjectId -> Word
termNodes = \case
    CBound index -> rnf index `seq` 1
    CGlobal global -> rnf global `seq` 1
    CIntrinsic intrinsic -> rnf intrinsic `seq` 1
    CLogicalSelect coreType -> rnf coreType `seq` 1
    COpaqueInteger number -> rnf number `seq` 1
    CApp function argument -> 1 + termNodes function + termNodes argument
    CLam coreType body -> rnf coreType `seq` (1 + termNodes body)
    CTruth -> 1
    CFalsum -> 1
    CNot body -> 1 + termNodes body
    CAnd left right -> 1 + termNodes left + termNodes right
    COr left right -> 1 + termNodes left + termNodes right
    CImp left right -> 1 + termNodes left + termNodes right
    CEq coreType left right -> rnf coreType `seq` (1 + termNodes left + termNodes right)
    CForall coreType body -> rnf coreType `seq` (1 + termNodes body)
    CExists coreType body -> rnf coreType `seq` (1 + termNodes body)


require :: Show failure => Either failure value -> IO value
require = either (fail . show) pure

shown :: Show value => value -> Text
shown = Text.pack . show
