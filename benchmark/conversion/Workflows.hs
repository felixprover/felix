{-# LANGUAGE NoImplicitPrelude #-}

module Workflows (runWorkflowScaling, measure) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious qualified as Obvious
import Felix.Checking.Semantic (DefinitionViewKind(..))

import Control.DeepSeq (NFData, force, rnf)
import Control.Exception (evaluate)
import Control.Monad (foldM, unless)
import Data.IORef (newIORef, readIORef)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.IO.Utf8 qualified as Text
import Data.Vector qualified as Vector
import Data.Word (Word)
import GHC.Conc (getAllocationCounter)
import GHC.Stats qualified as RTS
import System.Mem (performMajorGC)


data Tier = Focused | Refutation !Word | Mixed | NoProof

data Workflow = Workflow
    !CheckedFoundation
    !Obvious.ObviousBudget
    !Tier
    ![ScopedCheckedCore Void]
    ![Obvious.ObviousDefinitionView Void]
    !(ScopedCheckedCore Void)
    !(Set HypothesisIx)

type Observation = (Text, Text, [Word])

runWorkflowScaling :: String -> Int -> Int -> IO ()
runWorkflowScaling family size repetitions = do
    unless (size > 0 && size <= 128 && repetitions > 0)
        (fail "workflow scaling needs size 1..128 and positive repetitions")
    enabled <- RTS.getRTSStatsEnabled
    unless enabled (fail "workflow measurements require +RTS -T -RTS")
    if family == "function-replay"
        then runFunctionReplay size repetitions
        else runObviousScaling family size repetitions

runFunctionReplay :: Int -> Int -> IO ()
runFunctionReplay size repetitions = do
    Workflow foundation budget _ hypotheses views target expectedUses <- prepare "function-pointwise" size
    proof <- require (Obvious.obviousProof budget foundation emptyGlobalTyping
        hypotheses [] views target)
    let derivation = Proof.builtProofDerivation (Obvious.obviousBuiltProof proof)
        replay (facts, goal, tree) = do
            checked <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList facts) goal tree)
            unless (replayedScopedKernelTarget checked == goal
                && replayedScopedKernelExternalHypothesisUses checked == expectedUses)
                (fail "fresh replay changed target or dependencies")
            pure [fromIntegral (replayedScopedKernelNodeCount checked),
                fromIntegral (replayedScopedKernelMaximumDepth checked)]
        input = (hypotheses, target, derivation)
    expected <- replay input
    Text.putStrLn (Text.unwords ["conversion-workflow-fresh-replay-v1", "function-pointwise",
        "size=" <> shown size, "repetitions=" <> shown repetitions, "nodes-depth=" <> shown expected])
    measure repetitions replay sum input expected

runObviousScaling :: String -> Int -> Int -> IO ()
runObviousScaling family size repetitions = do
    setupStarted <- getMonotonicTimeNSec
    setupAllocation <- getAllocationCounter
    prepared@(Workflow _foundation budget _tier hypotheses _views target _uses) <-
        prepare family size
    _ <- evaluate (rnf hypotheses `seq` rnf target)
    setupAfterAllocation <- getAllocationCounter
    setupFinished <- getMonotonicTimeNSec
    expected <- require (run prepared)
    _ <- evaluate (force expected)
    Text.putStrLn (Text.unwords
        [ "conversion-workflow-scaling-v1", Text.pack family
        , "size=" <> shown size, "repetitions=" <> shown repetitions
        , "conversion-pool=" <> shown (Conversion.conversionPoolAmount (Obvious.obviousConversionPool budget))
        , "focused-work-limit=" <> shown (Obvious.obviousFocusedWorkLimit budget)
        , "refutation-work-limit=" <> shown (Obvious.obviousRefutationWorkLimit budget)
        ])
    renderObservation expected
    Text.putStrLn (Text.unwords
        [ "setup-bytes=" <> shown (setupAllocation - setupAfterAllocation)
        , "setup-ns=" <> shown (setupFinished - setupStarted)
        ])
    measure repetitions (require . run)
        (\(_focused, _refutation, counts) -> sum counts) prepared expected

prepare :: String -> Int -> IO Workflow
prepare family size = do
    foundation <- require checkedFoundation
    let positions = [0 .. size - 1]
        index = CBound . fromIntegral
        boundTuple = tuple [index (size - position - 1) | position <- positions]
        concreteTuple = tuple [betaSet (COpaqueInteger (500 + toInteger position))
            | position <- positions]
        duplicatedSet = foldl' (\term _ ->
            CApp (CLam TySet (pair (index 0) (index 0))) term)
            (CIntrinsic Empty) positions
        closeAll body = foldr (\_ rest -> CForall TySet rest) body positions
        target = member concreteTuple (index 0)
        focused = Obvious.defaultObviousBudget
            { Obvious.obviousRefutationWorkLimit = 0 }
        refutation = Obvious.defaultObviousBudget
            { Obvious.obviousFocusedWorkLimit = 0 }
        make tier budget context hypotheses views goal uses =
            Workflow foundation budget tier
                <$> traverse (checked context) hypotheses
                <*> pure views
                <*> checked context goal
                <*> pure (Set.fromList (hypothesisIx <$> uses))
    case family of
        "function-pointwise" -> do
            let function = foldr (const (TyArrow TySet)) TySet positions
                applied headIndex = foldl' CApp (index headIndex) (index <$> reverse positions)
            make Focused focused [function, function]
                [closeAll (CEq TySet (applied size) (applied (size + 1)))]
                [] (CEq function (index 0) (index 1)) [0]
        "argument-pointwise" -> do
            let function = foldr (const (TyArrow TySet)) TySet positions
                applied headIndex = foldl' CApp (index headIndex) (index <$> reverse positions)
                predicate = CApp (index 2)
            make Focused focused [function, function, TyArrow function TyProp]
                [predicate (index 0), closeAll (CEq TySet (applied size) (applied (size + 1)))]
                [] (predicate (index 1)) [0, 1]
        "boolean-directional" -> do
            let beta term = foldr (const betaProp) term positions
                a = index 0
                b = index 1
                c = index 2
            make Mixed Obvious.defaultObviousBudget (replicate 3 TyProp) [] []
                (CEq TyProp (CAnd (COr (beta a) (beta b)) (beta c))
                    (COr (CAnd a c) (CAnd b c))) []
        "function-miss" -> do
            let function = foldr (const (TyArrow TySet)) TySet positions
                applied = foldl' CApp (index size) (index <$> reverse positions)
            make NoProof focused [function, function]
                [closeAll (CEq TySet applied applied)] [] (CEq function (index 0) (index 1)) []
        "focused-spine" -> make Focused focused [TySet]
            [ foldr (\_ rest -> betaProp
                    (CForall TySet (betaProp (CImp (betaProp CTruth) rest))))
                (betaProp (member boundTuple (index size))) positions ]
            [] (betaProp target) [0]
        "higher-order-spine" -> do
            let functionType = TyArrow TySet TySet
                betaFunction = CApp (CLam functionType (CBound 0))
                sourceTuple = tuple
                    [ CApp (index (2 * (size - position - 1) + 1))
                        (index (2 * (size - position - 1)))
                    | position <- positions ]
                goalTuple = tuple
                    [ CApp (betaFunction (CIntrinsic FamilyUnion))
                        (betaSet (COpaqueInteger (500 + toInteger position)))
                    | position <- positions ]
                block rest = betaProp (CForall functionType
                    (betaProp (CImp (betaProp CTruth)
                        (betaProp (CForall TySet
                            (betaProp (CImp (betaProp CTruth) rest)))))))
                theorem = foldr (const block)
                    (betaProp (member sourceTuple (index (2 * size)))) positions
            make Focused focused [TySet] [theorem]
                [] (betaProp (member goalTuple (index 0))) [0]
        "distinct-slots" -> make Focused focused [TySet]
            [closeAll (member boundTuple (index size))]
            [] target [0]
        "repeated-slots" -> make Focused focused [TySet]
            [CForall TySet (member (tuple (replicate size (index 0))) (index 1))]
            [] (member (tuple (replicate size (betaSet (COpaqueInteger 500))))
                (index 0)) [0]
        "matcher-unused-output" -> make Focused focused [TySet]
            [CForall TySet (member (index 0) (index 1))]
            [] (member duplicatedSet (index 0)) [0]
        "refutation-spine" -> do
            let p term = member term (COpaqueInteger 0)
                q term = member term (COpaqueInteger 1)
                value = COpaqueInteger 47
                rule = betaProp (CForall TySet
                    (foldr (\premise rest -> betaProp (CImp premise rest))
                        (betaProp (q (index 0)))
                        (replicate size (betaProp (p (index 0))))))
            make (Refutation 1) refutation [] [p value, rule]
                [] (q value) [0, 1]
        "refutation-binders" -> do
            let p term = member term (COpaqueInteger 0)
                q term = member term (COpaqueInteger 1)
                rule = closeAll (betaProp
                    (CImp (betaProp (p boundTuple)) (betaProp (q boundTuple))))
            make (Refutation 1) refutation [] [p concreteTuple, rule]
                [] (q concreteTuple) [0, 1]
        "nested-signed-views" -> do
            let proposition = member (index 0) (CIntrinsic Empty)
                nested = foldr (\_ rest -> betaProp (CAnd (betaProp CTruth) rest))
                    (betaProp proposition) positions
            make (Refutation 0) refutation [TySet, TyProp]
                [index 1, nested, CNot (betaProp proposition)]
                [] (member (COpaqueInteger 900) (COpaqueInteger 901)) [1, 2]
        "premise-backtracking" -> do
            let p term = member term (COpaqueInteger 0)
                q term = member term (COpaqueInteger 1)
                goal = member (COpaqueInteger 900) (COpaqueInteger 901)
                rule = CForall TySet (CImp (p (index 0)) (CImp (q (index 0)) goal))
                lastIndex = fromIntegral size
                premises = [p (COpaqueInteger (toInteger position)) | position <- [0 .. size]]
                    <> [q (COpaqueInteger (toInteger size)), rule]
            make Focused focused [] premises [] goal
                [lastIndex, lastIndex + 1, lastIndex + 2]
        "definition-spine" -> do
            let functionType = foldr (const (TyArrow TySet)) TySet positions
                apply = foldl' CApp
                arguments = [index (size - position - 1) | position <- positions]
                definition = closeAll
                    (CEq TySet (apply (index size) arguments) (COpaqueInteger 0))
                goal = CEq TySet
                    (betaSet (apply (index 0)
                        [ betaSet (COpaqueInteger (toInteger position))
                        | position <- positions ]))
                    (COpaqueInteger 0)
            make Focused focused [functionType] [definition]
                [Obvious.obviousLocalDefinitionView 0 DefinitionPointwiseView]
                goal [0]
        "definition-unused-output" -> do
            let definition = CForall TySet
                    (CEq TySet (CApp (index 1) (index 0)) (CIntrinsic Empty))
                goal = CEq TySet (CApp (index 0) duplicatedSet) (CIntrinsic Empty)
            make Focused focused [TyArrow TySet TySet] [definition]
                [Obvious.obviousLocalDefinitionView 0 DefinitionPointwiseView]
                goal [0]
        _ -> fail "unknown workflow scaling family"
  where
    checked context = require . checkScopedCanonicalCore emptyGlobalTyping context
    member element set = CApp (CApp (CIntrinsic Member) element) set
    pair left right = CApp (CApp (CIntrinsic PairSet) left) right
    tuple = foldr pair (CIntrinsic Empty)
    betaSet = CApp (CLam TySet (CBound 0))
    betaProp = CApp (CLam TyProp (CBound 0))

run :: Workflow -> Either Text Observation
run (Workflow foundation budget NoProof hypotheses views target _) = do
    let (statistics, result) = Obvious.obviousProofDetailed
            budget Obvious.AnyObviousProof foundation emptyGlobalTyping hypotheses [] views target
    case result of
        Right _ -> Left "failed workflow unexpectedly proved its target"
        Left failure -> case failure of
            Obvious.ObviousResourceExhausted{} -> Left "failed workflow exhausted its budget"
            _ | Obvious.obviousFailureClass failure `elem` [Obvious.ObviousMalformedClass, Obvious.ObviousIntegrityClass] ->
                Left (shown failure)
              | otherwise -> pure (statisticsObservation statistics)
run (Workflow foundation budget tier hypotheses views target expectedUses) = do
    let (statistics, result) = Obvious.obviousProofDetailed
            budget Obvious.AnyObviousProof foundation emptyGlobalTyping
            hypotheses [] views target
    proof <- renderFailure result
    let built = Obvious.obviousBuiltProof proof
    unless (Proof.builtProofStatement built == target)
        (Left "workflow changed its exact checked target")
    unless (Set.null (Obvious.obviousUsedImports proof))
        (Left "workflow acquired imported authority")
    case tier of
        Focused -> unless
            (Obvious.obviousFocusedTierOutcome statistics == Obvious.ObviousTierCandidateBuilt
                && Obvious.obviousRefutationWorkConsumed statistics == 0)
            (Left "focused workflow used the wrong search tier")
        Refutation expectedInstances -> unless
            (Obvious.obviousRefutationTierOutcome statistics == Obvious.ObviousTierCandidateBuilt
                && Obvious.obviousRuleInstancesAdmitted statistics == expectedInstances)
            (Left "refutation workflow reconstructed the wrong rule count")
        Mixed -> unless (Obvious.obviousRefutationWorkConsumed statistics > 0)
            (Left "mixed workflow did not need ground reasoning")
    replayed <- renderFailure (replayScopedKernelDerivation
        foundation defaultKernelReplayLimits emptyGlobalTyping
        Vector.empty (Vector.fromList hypotheses) target
        (Proof.builtProofDerivation built))
    unless
        ( replayedScopedKernelExternalHypothesisUses replayed == expectedUses
        && Set.null (replayedScopedKernelImportUses replayed)
        && replayedScopedKernelTarget replayed == target
        )
        (Left "workflow replay changed its target or exact authority")
    pure (statisticsObservation statistics)

statisticsObservation :: Obvious.ObviousStatistics -> Observation
statisticsObservation statistics =
        ( shown (Obvious.obviousFocusedTierOutcome statistics)
        , shown (Obvious.obviousRefutationTierOutcome statistics)
        , [ Obvious.obviousFocusedWorkConsumed statistics
          , Obvious.obviousRefutationWorkConsumed statistics
          , Obvious.obviousConversionWorkConsumed statistics
          , Obvious.obviousSignedFormulasAdmitted statistics
          , Obvious.obviousRuleInstancesAdmitted statistics
          , Obvious.obviousBranchNodesCreated statistics
          , Obvious.obviousTermsAdmitted statistics
          , Obvious.obviousEqualityEventsProcessed statistics
          ]
        )

renderObservation :: Observation -> IO ()
renderObservation (focused, refutation, counts) = do
    Text.putStrLn ("focused-tier=" <> focused <> " refutation-tier=" <> refutation)
    Text.putStrLn (Text.unwords (zipWith (\name count -> name <> "=" <> shown count)
        [ "focused-work", "refutation-work", "conversion-work", "signed-formulas"
        , "rule-instances", "branch-nodes", "terms", "equality-events" ] counts))

measure
    :: (Eq observation, NFData observation)
    => Int
    -> (input -> IO observation)
    -> (observation -> Word)
    -> input
    -> observation
    -> IO ()
measure repetitions observe checksum prepared expected = do
    input <- newIORef prepared
    performMajorGC
    beforeStats <- RTS.getRTSStats
    beforeAllocation <- getAllocationCounter
    started <- getMonotonicTimeNSec
    total <- foldM (\accumulator _ -> do
        current <- readIORef input
        actual <- observe current >>= evaluate . force
        unless (actual == expected) (fail "workflow observations changed during the batch")
        evaluate (accumulator + checksum actual)) (0 :: Word) [1 .. repetitions]
    finished <- getMonotonicTimeNSec
    afterAllocation <- getAllocationCounter
    afterStats <- RTS.getRTSStats
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

renderFailure :: Show failure => Either failure value -> Either Text value
renderFailure = either (Left . shown) Right

require :: Show failure => Either failure value -> IO value
require = either (fail . show) pure

shown :: Show value => value -> Text
shown = Text.pack . show
