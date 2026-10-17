{-# LANGUAGE BangPatterns #-}

module EqualityChecks (tests, benchmark) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious.Equality qualified as Equality
import Felix.Checking.Obvious.LogicalView qualified as Logical
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (foldM, replicateM)
import Data.IORef
import Data.List (permutations)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import GHC.Stats
import System.CPUTime (getCPUTime)
import System.Mem (performGC)
import Test.Tasty
import Test.Tasty.HUnit

type Edge = (Search.TermId, Search.TermId, Int)
type Path = [(Int, Equality.EqualityDirection)]

tests :: TestTree
tests = testGroup "Equality adjacency"
    [ testCase "preserves exact paths for finite edge histories" exactPaths
    , testCase "replays ordinary and supported reasons in both orientations" replayPaths
    , testCase "charges only reached adjacency and distinguishes exhaustion" countedPaths
    , testCase "retains type and unknown-term checks" invalidTerms
    , testCase "supported adjacency preserves admission-ordered evidence" supportedPaths
    , testCase "supported traversal and alternate admission have bounded work" supportedWork
    ]

right :: Show failure => Either failure value -> IO value
right = either (fail . show) pure

makeCatalogue :: Int -> IO (Search.Catalogue Void, [Search.TermId])
makeCatalogue count = do
    roots <- traverse makeRoot [0 .. count - 1]
    let (prepared, _, _) = Search.collectInitialCatalogue emptyGlobalTyping maxBound maxBound []
            (fromListNonEmpty roots)
    catalogue <- Search.initialCatalogue <$> right prepared
    foundType <- right (fst (Search.findCatalogueTypeCounted maxBound catalogue TySet))
    typeId <- maybe (fail "catalogue omitted Set") pure foundType
    identities <- traverse (findTerm catalogue typeId) [0 .. count - 1]
    pure (catalogue, identities)
  where
    makeRoot number = do
        checked <- right (checkScopedCanonicalCore emptyGlobalTyping []
            (CEq TySet (COpaqueInteger (toInteger number)) (COpaqueInteger (toInteger number))))
        template <- right (Template.retainCheckedPropositionTemplate checked)
        view <- right =<< Logical.prepareCompiledLogicalViewCounted (const (pure Nothing)) (pure ()) template
        pure (number, view)
    findTerm catalogue typeId number = do
        found <- right (fst (Search.findCatalogueTermCounted maxBound catalogue typeId (COpaqueInteger (toInteger number))))
        maybe (fail "catalogue omitted an equality operand") pure found
    fromListNonEmpty (first : rest) = first :| rest
    fromListNonEmpty [] = error "empty equality fixture"

makeState :: Search.Catalogue Void -> [Edge] -> IO (Equality.EqualityState Int)
makeState catalogue events = do
    initial <- right (fst (Equality.initializeEqualityState maxBound catalogue))
    foldM admit initial events
  where
    admit state (left, rightTerm, reason) = do
        (updated, _clash, _merged) <- right
            (fst (Equality.recordEquality maxBound catalogue left rightTerm reason state))
        pure updated

makeSupportedState :: Search.Catalogue Void -> [Edge] -> IO (Equality.EqualityState Int)
makeSupportedState catalogue events = do
    initial <- makeState catalogue []
    foldM (\state (left, rightTerm, reason) -> do
        (updated, _, _) <- right (fst
            (Equality.recordEqualityWithSupport maxBound catalogue left rightTerm reason state))
        pure updated) initial events

-- The old supported BFS scans every retained edge per (term, supportSeen).
-- Keep it independent of the production adjacency and admission helpers.
referenceSupported :: (Int -> Maybe Int) -> [Edge] -> Search.TermId -> Search.TermId -> Maybe Path
referenceSupported supported edges source target =
    search (Set.singleton (source, False)) Map.empty (Seq.singleton (source, False))
  where
    destination = (target, True)
    search visited predecessors queue = case Seq.viewl queue of
        Seq.EmptyL -> Nothing
        current Seq.:< rest ->
            let (seen, paths, pending) = foldl' (scan current) (visited, predecessors, rest) edges
            in if Set.member destination seen then Just (rebuild paths destination [])
                else search seen paths pending
    scan current@(term, seenSupport) state (left, rightTerm, reason) =
        let resolved = supported reason
            withSupport = seenSupport || isJust resolved
            chosen = fromMaybe reason resolved
        in foldl' (admit current) state
            ([((rightTerm, withSupport), (chosen, Equality.EqualityForward)) | term == left]
                <> [((left, withSupport), (chosen, Equality.EqualityReverse)) | term == rightTerm && left /= rightTerm])
    admit previous (seen, paths, queue) (next, step)
        | Set.member next seen = (seen, paths, queue)
        | otherwise = (Set.insert next seen, Map.insert next (previous, step) paths, queue Seq.|> next)
    rebuild paths current steps
        | current == (source, False) = steps
        | otherwise = case Map.lookup current paths of
            Just (previous, step) -> rebuild paths previous (step : steps)
            Nothing -> error "supported reference lost a predecessor"

supportedPaths :: Assertion
supportedPaths = do
    (catalogue, ids) <- makeCatalogue 4
    [a, b, c, d] <- pure ids
    let pairs = [(left, rightTerm) | left <- ids, rightTerm <- ids]
        small = [(left, rightTerm) | left <- take 3 ids, rightTerm <- take 3 ids]
        histories = concat [replicateM count small | count <- [0..3]]
            <> permutations [(a, b), (b, d), (a, c), (c, d)]
    for_ histories \history -> do
        let events = [(left, rightTerm, reason) | ((left, rightTerm), reason) <- zip history [0..]]
        state <- makeSupportedState catalogue events
        -- Reuse the same graph with changing support, including a replacement
        -- certificate label and support available only on a late alternate.
        for_ [const Nothing, \reason -> if even reason then Just (reason + 100) else Nothing,
                \reason -> if reason == 2 then Just reason else Nothing] \resolve ->
            for_ pairs \(source, target) -> do
                actual <- right (fst (Equality.equalitySupportedPath maxBound catalogue resolve state source target))
                fmap normalizePath actual @?= referenceSupported resolve events source target
                ordinary <- right (fst (actualPath maxBound catalogue state source target))
                ordinary @?= fst (referencePath (admittedEdges events) source target)

supportedWork :: Assertion
supportedWork = do
    (catalogue, ids) <- makeCatalogue 80
    let source = ids !! 0
        target = ids !! 1
        edge = (source, target, 0)
        unrelated = [(left, rightTerm, 1) | (left, rightTerm) <- zip (drop 2 ids) (drop 3 ids)]
        query fuel = Equality.equalitySupportedPath fuel catalogue Just
        normalized (answer, remaining) = (fmap (fmap normalizePath) answer, maxBound - remaining)
    small <- makeSupportedState catalogue [edge]
    large <- makeSupportedState catalogue (edge : unrelated)
    let (answer, spent) = normalized (query maxBound small source target)
    -- A one-edge old scan cost five; the explicit lookup makes this six.
    spent @?= 6
    for_ [0, 2, 3, 4] \fuel -> do
        assertExhausted (fst (query fuel small source target))
        snd (query fuel small source target) @?= 0
    normalized (query maxBound large source target) @?= (answer, spent)
    fmap (fmap normalizePath) (fst (query spent large source target)) @?= answer
    assertExhausted (fst (query (spent - 1) large source target))
    -- The old scan charged every unrelated edge even for this one-hop proof.
    assertBool "old supported scan exceeds the sufficient new budget"
        (fromIntegral (length unrelated + 1) + 4 > spent)
    -- Pair/type probes consume three units. Ordinary duplicates remain free
    -- thereafter, but retaining an alternate now pays two incident insertions.
    let ordinary = Equality.recordEquality 3 catalogue source target 2 small
        alternate fuel = Equality.recordEqualityWithSupport fuel catalogue source target 2 small
    case fst ordinary of
        Right (_, _, False) -> snd ordinary @?= 0
        _ -> assertFailure "ordinary duplicate changed its work policy"
    assertExhausted (fst (alternate 4))
    snd (alternate 4) @?= 0
    (updated, _, merged) <- right (fst (alternate 5))
    assertBool "alternate is not a new merge" (not merged)
    result <- right (fst (Equality.equalitySupportedPath maxBound catalogue
        (\reason -> if reason == 2 then Just reason else Nothing) updated source target))
    fmap normalizePath result @?= Just [(2, Equality.EqualityForward)]
    normalized (query maxBound small source target) @?= (answer, spent)
    -- Once the views diverge, a new pair must update both before publication.
    let addNew fuel = Equality.recordEquality fuel catalogue target (ids !! 2) 3 updated
        (ample, remaining) = addNew maxBound
        required = maxBound - remaining
    (extended, _, _) <- right ample
    assertExhausted (fst (addNew (required - 1)))
    snd (addNew (required - 1)) @?= 0
    _ <- right (fst (addNew required))
    ordinaryPath <- right (fst (actualPath maxBound catalogue extended source (ids !! 2)))
    supportedPath <- right (fst (Equality.equalitySupportedPath maxBound catalogue
        (\reason -> if reason == 2 then Just reason else Nothing) extended source (ids !! 2)))
    ordinaryPath @?= Just [(0, Equality.EqualityForward), (3, Equality.EqualityForward)]
    fmap normalizePath supportedPath @?= Just [(2, Equality.EqualityForward), (3, Equality.EqualityForward)]
  where
    assertExhausted result = case result of
        Left Equality.EqualityWorkExhausted -> pure ()
        _ -> assertFailure "expected equality work exhaustion"

normalizePath :: Equality.EqualityPath Int -> Path
normalizePath = map step . Equality.equalityPathSteps
  where step (Equality.EqualityStep reason direction) = (reason, direction)

admittedEdges :: [Edge] -> Seq Edge
admittedEdges = Seq.fromList . reverse . snd . foldl' unique (Set.empty, [])
  where
    unique (seen, retained) edge@(left, rightTerm, _)
        | pair `Set.member` seen = (seen, retained)
        | otherwise = (Set.insert pair seen, edge : retained)
      where pair = (min left rightTerm, max left rightTerm)

-- The previous scan in a small independent reference. Its input is the
-- retained admission-order sequence: pair deduplication happens at admission,
-- outside the measured query. Check the target after scanning the full row.
referencePath :: Seq Edge -> Search.TermId -> Search.TermId -> (Maybe Path, Word)
referencePath edges source target
    | source == target = (Just [], 2)
    | otherwise = search (Set.singleton source) Map.empty (Seq.singleton source) 2
  where
    search visited predecessors queue !work = case Seq.viewl queue of
        Seq.EmptyL -> (Nothing, work + 1)
        current Seq.:< rest ->
            let (seen, previous, pending) = foldl' (scan current) (visited, predecessors, rest) edges
                spent = work + 1 + fromIntegral (length edges)
            in if target `Set.member` seen then
                let selected = rebuild previous target []
                in (Just selected, spent + fromIntegral (length selected))
            else search seen previous pending spent
    scan current state (left, rightTerm, reason) = foldl' (admit current) state
        ([(rightTerm, (reason, Equality.EqualityForward)) | current == left]
            <> [(left, (reason, Equality.EqualityReverse)) | current == rightTerm && left /= rightTerm])
    admit previous (seen, predecessors, queue) (next, step)
        | next `Set.member` seen = (seen, predecessors, queue)
        | otherwise = (Set.insert next seen, Map.insert next (previous, step) predecessors, queue Seq.|> next)
    rebuild predecessors current path
        | current == source = path
        | otherwise = case Map.lookup current predecessors of
            Just (previous, step) -> rebuild predecessors previous (step : path)
            Nothing -> error "reference lost a predecessor"

actualPath :: Word -> Search.Catalogue Void -> Equality.EqualityState Int
    -> Search.TermId -> Search.TermId -> (Either Equality.EqualityFailure (Maybe Path), Word)
actualPath work catalogue state source target =
    let (result, remaining) = Equality.equalityPath work catalogue state source target
    in (fmap (fmap normalizePath) result, work - remaining)

exactPaths :: Assertion
exactPaths = do
    (catalogue, ids) <- makeCatalogue 4
    [a, b, c, d] <- pure ids
    let small = take 3 ids
        edges = [(left, rightTerm) | left <- small, rightTerm <- small]
        histories = concat [replicateM count edges | count <- [0 .. 3]]
        ties = permutations [(a, b), (b, d), (a, c), (c, d)]
    for_ (histories <> ties) \history -> do
        let events = [(left, rightTerm, ordinal) | ((left, rightTerm), ordinal) <- zip history [0 ..]]
        state <- makeState catalogue events
        for_ [(left, rightTerm) | left <- ids, rightTerm <- ids] \(source, target) -> do
            let expected = fst (referencePath (admittedEdges events) source target)
            actual <- right (fst (actualPath maxBound catalogue state source target))
            assertEqual (show (history, source, target)) expected actual

replayPaths :: Assertion
replayPaths = do
    foundation <- right Foundation.checkedFoundation
    (catalogue, ids) <- makeCatalogue 4
    [a, b, c, d] <- pure ids
    let edges = [(b, a, 0), (b, d, 1), (a, c, 2), (c, d, 3), (a, b, 4), (a, a, 5)]
        operand identity = maybe (error "missing operand") Search.catalogueTermValue (Search.catalogueTerm catalogue identity)
    hypotheses <- traverse (\(left, rightTerm, _) -> right (checkScopedCanonicalCore emptyGlobalTyping []
        (CEq TySet (scopedCoreTerm (operand left)) (scopedCoreTerm (operand rightTerm))))) edges
    context <- right (Proof.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    state <- makeSupportedState catalogue edges
    for_ [(left, rightTerm) | left <- ids, rightTerm <- ids] \(source, target) -> do
        selected <- right (fst (actualPath maxBound catalogue state source target))
        supported <- right (fst (Equality.equalitySupportedPath maxBound catalogue
            (\reason -> if even reason then Just reason else Nothing) state source target))
        for_ [selected, fmap normalizePath supported] \path -> do
            steps <- maybe (fail "connected replay fixture lost its path") pure path
            start <- right (Proof.equalityReflexivityProof context (operand source))
            proof <- foldM (extend context) start steps
            goal <- right (checkScopedCanonicalCore emptyGlobalTyping []
                (CEq TySet (scopedCoreTerm (operand source)) (scopedCoreTerm (operand target))))
            replayed <- right (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
                Vector.empty (Vector.fromList hypotheses) goal (Proof.builtProofDerivation proof))
            replayedScopedKernelExternalHypothesisUses replayed @?=
                Set.fromList [hypothesisIx (fromIntegral reason) | (reason, _) <- steps]
  where
    extend context previous (reason, direction) = do
        given <- right (Proof.indexedHypothesisProof context (hypothesisIx (fromIntegral reason)))
        oriented <- case direction of
            Equality.EqualityForward -> pure given
            Equality.EqualityReverse -> right (Proof.equalityReverseProof context given)
        right (Proof.composeEqualityProof context previous oriented)

countedPaths :: Assertion
countedPaths = do
    (catalogue, ids) <- makeCatalogue 80
    let chain = zipWith (\(left, rightTerm) reason -> (left, rightTerm, reason))
            (zip (take 4 ids) (take 4 (drop 1 ids))) [0 ..]
        unrelated = zipWith (\(left, rightTerm) reason -> (left, rightTerm, reason))
            (zip (drop 5 ids) (drop 6 ids)) [100 ..]
        source = ids !! 0
        target = ids !! 4
    small <- makeState catalogue chain
    large <- makeState catalogue (chain <> unrelated)
    let (result, spent) = actualPath maxBound catalogue small source target
        (largerResult, largerSpent) = actualPath maxBound catalogue large source target
    result @?= largerResult
    spent @?= largerSpent
    assertBool "reference work grows with unrelated edges"
        (snd (referencePath (admittedEdges (chain <> unrelated)) source target) > snd (referencePath (admittedEdges chain) source target))
    fst (actualPath (spent - 1) catalogue large source target) @?= Left Equality.EqualityWorkExhausted
    fst (actualPath spent catalogue large source target) @?= result
    (selfLoop, _, _) <- right (fst (Equality.recordEquality maxBound catalogue source source 999 small))
    actualPath maxBound catalogue selfLoop source target @?= (result, spent + 1)
    (duplicate, _, _) <- right (fst (Equality.recordEquality maxBound catalogue source source 1000 selfLoop))
    actualPath maxBound catalogue duplicate source target @?= (result, spent + 1)
    let (missing, noPathCost) = actualPath maxBound catalogue small source (ids !! 79)
    missing @?= Right Nothing
    fst (actualPath (noPathCost - 1) catalogue small source (ids !! 79)) @?= Left Equality.EqualityWorkExhausted
    fst (actualPath noPathCost catalogue small source (ids !! 79)) @?= Right Nothing
    -- Failure cannot publish a partially updated persistent index.
    let failed = fst (Equality.recordEquality 0 catalogue source target 999 small)
    case failed of
        Left Equality.EqualityWorkExhausted -> pure ()
        _ -> assertFailure "zero-work insertion unexpectedly succeeded"
    actualPath maxBound catalogue small source target @?= (result, spent)

invalidTerms :: Assertion
invalidTerms = do
    (catalogue, ids) <- makeCatalogue 1
    state <- makeState catalogue []
    let setTerm = ids !! 0
        propositions = [Search.TermId index | index <- [0 .. fromIntegral (Search.catalogueTermCount catalogue) - 1]
            , Just term <- [Search.catalogueTerm catalogue (Search.TermId index)]
            , scopedCoreType (Search.catalogueTermValue term) == TyProp]
    case propositions of
        proposition : _ -> fst (actualPath maxBound catalogue state setTerm proposition)
            @?= Left (Equality.EqualityTypeMismatch setTerm proposition)
        [] -> assertFailure "missing proposition fixture"
    let unknown = Search.TermId (-1)
    fst (actualPath maxBound catalogue state setTerm unknown) @?= Left (Equality.EqualityUnknownTerm unknown)

-- Preparation is outside allocation observations, and the state remains live
-- through GC. Distinct query endpoints prevent sharing one precomputed path.
benchmark :: String -> String -> Int -> IO ()
benchmark _ _ size | size < 4 = fail "equality benchmark size must be at least four"
benchmark operation shape size
    | operation `elem` ["ordinary-build", "alternate-build", "supported-query"] =
        benchmarkSupported operation shape size
benchmark algorithm shape size = do
    (catalogue, ids) <- makeCatalogue (size + 8)
    let adjacent = zip ids (drop 1 ids)
        selected = case shape of
            "chain" -> take size adjacent
            "unrelated" -> take 4 adjacent <> drop 5 adjacent
            _ -> error "unknown equality benchmark shape"
        edges = [(left, rightTerm, reason) | ((left, rightTerm), reason) <- zip selected [0 ..]]
        target = if shape == "chain" then ids !! size else ids !! 4
        queries = [(ids !! index, target) | index <- [0 .. 3]]
    let referenceEdges = admittedEdges edges
        pairs = Set.fromList [(min left rightTerm, max left rightTerm) | (left, rightTerm, _) <- edges]
    initial <- makeState catalogue []
    retained <- case algorithm of
        "candidate" -> Left <$> makeState catalogue edges
        "reference" -> pure (Right (initial, referenceEdges, pairs))
        _ -> fail "unknown equality benchmark algorithm"
    -- Both modes retain the same prepared reference inputs used to check the
    -- answer. The reference owner adds the old edge sequence and pair set to
    -- an initialized empty state, differing only by a small tuple wrapper.
    _ <- evaluate (sum [left + rightTerm + reason
        | (Search.TermId left, Search.TermId rightTerm, reason) <- toList referenceEdges])
    _ <- evaluate (Set.size pairs)
    owner <- newIORef (Just retained)
    performGC
    before <- getRTSStats
    outcomes <- traverse (query catalogue retained referenceEdges) queries
    -- Force the normalized paths without requiring public proof-label instances.
    checksums <- evaluate (force [(fmap (map (\(reason, direction) ->
        (reason, direction == Equality.EqualityForward))) path, cost) | (path, cost) <- outcomes])
    performGC
    finalStats <- getRTSStats
    print (allocated_bytes finalStats - allocated_bytes before, gcdetails_live_bytes (gc finalStats), map snd checksums)
    for_ (zip queries outcomes) \((source, destination), (path, _)) ->
        path @?= fst (referencePath referenceEdges source destination)
    readIORef owner >>= \case
        Just _ -> writeIORef owner Nothing
        Nothing -> fail "equality owner was lost"
  where
    query _catalogue (Right _) edges (source, target) = pure (referencePath edges source target)
    query catalogue (Left state) _edges (source, target) = do
        let (outcome, work) = actualPath maxBound catalogue state source target
        path <- right outcome
        pure (path, work)

-- Run this same harness against parent and candidate Equality.hs. Construction
-- uses disconnected pairs so connectivity discovery does not dominate insertion.
-- Query preparation is excluded; retained branches remain live through the GC.
benchmarkSupported :: String -> String -> Int -> IO ()
benchmarkSupported operation shape size = do
    (catalogue, ids) <- makeCatalogue (2 * size + 8)
    let disconnected = [(ids !! (2 * n + 6), ids !! (2 * n + 7), n + 4) | n <- [0 .. size - 1]]
        relevant = [(ids !! n, ids !! (n + 1), n) | n <- [0..3]]
        edges = if shape == "unrelated" then relevant <> disconnected else relevant
        source = ids !! 0
        target = ids !! 4
        build record initial events = foldM (\(state, cost) (left, rightTerm, reason) -> do
            let (result, remaining) = record maxBound catalogue left rightTerm reason state
            (updated, _, _) <- right result
            _ <- evaluate updated
            pure (updated, cost + (maxBound - remaining))) (initial, 0 :: Word) events
    -- Force fixture lists before recording allocation; reasons are scalar labels.
    _ <- evaluate (sum [left + rightTerm + reason
        | (Search.TermId left, Search.TermId rightTerm, reason) <- disconnected <> edges])
    initial <- makeState catalogue []
    prepared <- if operation == "ordinary-build" then pure (initial, 0)
        else build Equality.recordEquality initial edges
    owner <- newIORef ([] :: [Equality.EqualityState Int])
    performGC
    before <- getRTSStats
    started <- getCPUTime
    (states, costs, checksum) <- case operation of
        "ordinary-build" -> do
            (state, work) <- build Equality.recordEquality initial disconnected
            pure ([state], [work], 0)
        "alternate-build" -> do
            branches <- traverse (\branch -> build Equality.recordEqualityWithSupport (fst prepared)
                [(rightTerm, left, reason + branch * (size + 4))
                | (left, rightTerm, reason) <- edges <> edges]) [1..8]
            pure (map fst branches, map snd branches, 0)
        _ -> do
            results <- traverse (\start -> do
                let (result, remaining) = Equality.equalitySupportedPath maxBound catalogue Just
                        (fst prepared) start target
                path <- right result
                let labels = maybe [] normalizePath path
                total <- evaluate (sum [reason + if direction == Equality.EqualityForward then 1 else 0
                    | (reason, direction) <- labels])
                pure (maxBound - remaining, total)) (take 4 ids)
            pure ([fst prepared], map fst results, sum (map snd results))
    -- A rooted owner survives through the residency observation. Query it below
    -- so neither the branches nor their explanations can die before that GC.
    writeIORef owner states
    _ <- evaluate (sum costs + fromIntegral checksum)
    ended <- getCPUTime
    performGC
    finalStats <- getRTSStats
    print (allocated_bytes finalStats - allocated_bytes before, gcdetails_live_bytes (gc finalStats),
        ended - started, snd prepared, costs, checksum)
    retained <- readIORef owner
    for_ retained \state -> do
        let (answer, _) = Equality.equalitySupportedPath maxBound catalogue Just state source target
        _ <- right answer
        pure ()
