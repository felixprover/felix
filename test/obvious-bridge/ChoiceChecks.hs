module ChoiceChecks (tests) where

import Base hiding (empty)
import Control.Monad (foldM, unless)
import Data.Maybe (mapMaybe)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Felix.Checking.Obvious.Choice qualified as Choice
import Felix.Checking.Obvious.Driver (FocusedObligationId(..), focusedOwnerDemanded)
import Felix.Checking.Obvious.Driver qualified as Driver
import Felix.Checking.Core (CountedCoreFailure(..))
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Focused choice ownership"
    [ testCase "matches ancestry liveness through nested admission and retirement" histories
    , testCase "preserves producer demand through cycles and consumer cancellation" demandGraphs
    , testCase "retains an undemanded producer for a later consumer" lateConsumer
    , testCase "visits a rootless shared demand graph without expanding every path" sharedOwnerDemand
    , testCase "short-circuits demand before inspecting unused consumers" earlyOwnerDemand
    , testCase "requires driving paths without inheriting canonical requirements" drivingDemand
    , testCase "bounds shared cyclic driving paths by requirement-labelled visits" sharedDrivingDemand
    , testCase "keeps links private across payload updates and rejects stale parents" admission
    , testCase "retires deep choices iteratively without narrowing identifiers" deepRetirement
    ]

-- The preceding representation retains ancestry lists and lazily removes only
-- the completed choice. Descendants are live only while every ancestor remains.
data Reference = Reference
    !(Map.Map Natural [Natural]) !(Set Natural) !(Map.Map Natural Natural)

referenceLive :: Reference -> [Natural] -> Bool
referenceLive (Reference _ present _) = all (`Set.member` present)

referenceProducer :: Reference -> [Natural] -> Maybe (Maybe Natural)
referenceProducer reference@(Reference _ _ producers) path
    | referenceLive reference path = Just (listToMaybe (mapMaybe (`Map.lookup` producers) path))
    | otherwise = Nothing

referenceNeeded :: Map.Map Natural [[Natural]] -> Reference -> [Natural] -> Bool
referenceNeeded consumers reference = needed Set.empty
  where
    needed seen path = case referenceProducer reference path of
        Nothing -> False
        Just Nothing -> True
        Just (Just identifier)
            | Set.member identifier seen -> False
            | otherwise -> any (needed (Set.insert identifier seen))
                (Map.findWithDefault [] identifier consumers)

histories :: Assertion
histories = visit (5 :: Int) 1 (Reference Map.empty Set.empty Map.empty) Choice.empty
  where
    visit remaining next reference@(Reference paths present producers) forest = do
        let live = [(identifier, path) | (identifier, path) <- Map.toAscList paths, referenceLive reference path]
        assertEqual "every present choice has a live ancestor chain"
            (map fst live) (map fst (Choice.rows forest))
        forM_ (Map.toAscList paths) \(identifier, path) -> do
            assertEqual "single lookup agrees with the complete preceding ancestry"
                (referenceProducer reference path)
                (Choice.ownerProducer (Choice.OwnedChoice identifier) forest)
            forM_ (Choice.lookup identifier forest) \choice ->
                assertEqual "retirement does not substitute a continuation" identifier (Choice.payload choice)
        unless (remaining == 0) do
            forM_ ((Choice.RootContinuation, []) : [(Choice.OwnedChoice identifier, path) | (identifier, path) <- live])
                \(owner, parents) -> do
                    updated <- require (Choice.insert next owner next forest)
                    visit (remaining - 1) (next + 1)
                        (Reference (Map.insert next (next : parents) paths) (Set.insert next present) producers) updated
            producer <- require (Choice.insertProducer next next next forest)
            visit (remaining - 1) (next + 1)
                (Reference (Map.insert next [next] paths) (Set.insert next present) (Map.insert next next producers)) producer
            forM_ live \(identifier, _) -> visit (remaining - 1) next
                (Reference paths (Set.delete identifier present) producers) (Choice.retire identifier forest)

demandGraphs :: Assertion
demandGraphs = do
    roots <- foldM (\forest identifier -> require (Choice.insertProducer identifier (FocusedObligationId (fromIntegral identifier)) () forest)) Choice.empty [1, 2, 3]
    withExternal <- require (Choice.insert 4 Choice.RootContinuation () roots)
    withDead <- require (Choice.insert 5 Choice.RootContinuation () withExternal)
    let forest = Choice.retire 5 withDead
        reference = Reference (Map.fromList [(n, [n]) | n <- [1..5]]) (Set.fromList [1..4])
            (Map.fromList [(n, n) | n <- [1..3]])
        paths = [[], [1], [2], [3], [4], [5]]
        lists = [] : [[x] | x <- paths] <> [[x, y] | x <- paths, y <- paths]
        owner [] = Choice.RootContinuation
        owner (identifier : _) = Choice.OwnedChoice identifier
    forM_ lists \a -> forM_ lists \b -> forM_ lists \c -> do
        let consumers = Map.fromList [(1, a), (2, b), (3, c)]
            attached (FocusedObligationId identifier) = Seq.fromList (map owner (Map.findWithDefault [] (fromIntegral identifier) consumers))
        forM_ paths \path -> assertEqual "cycle handling, short-circuit order and retired consumers"
            (referenceNeeded consumers reference path)
            (focusedOwnerDemanded id attached forest (owner path))

sharedOwnerDemand :: Assertion
sharedOwnerDemand = forM_ [64, 128 :: Natural] \size -> do
    forest <- foldM (\choices key -> require (Choice.insertProducer key key () choices))
        Choice.empty [1 .. size]
    let consumers key
            | key == size = Seq.empty
            | otherwise = Seq.replicate 2 (Choice.OwnedChoice (key + 1))
    assertBool "a shared graph without a root has no demand"
        (not (focusedOwnerDemanded id consumers forest (Choice.OwnedChoice 1)))

earlyOwnerDemand :: Assertion
earlyOwnerDemand = do
    forest <- require (Choice.insertProducer 1 (1 :: Natural) () Choice.empty)
    let consumers _ = Seq.fromList [Choice.RootContinuation, error "unused consumer was inspected"]
    assertBool "root demand does not inspect later consumers"
        (focusedOwnerDemanded id consumers forest (Choice.OwnedChoice 1))

lateConsumer :: Assertion
lateConsumer = do
    producer <- require (Choice.insertProducer 1 (FocusedObligationId 11) ("cursor" :: String) Choice.empty)
    first <- require (Choice.insert 2 Choice.RootContinuation "first continuation" producer)
    both <- require (Choice.insert 3 Choice.RootContinuation "second continuation" first)
    let source = Choice.OwnedChoice 1
        consumers = Seq.fromList [Choice.OwnedChoice 2, Choice.OwnedChoice 3]
        needed = focusedOwnerDemanded id (const consumers)
        oneCanceled = Choice.retire 2 both
        dormant = Choice.retire 3 oneCanceled
    assertBool "one canceled consumer leaves demand" (needed oneCanceled source)
    assertBool "no remaining live consumer parks the producer" (not (needed dormant source))
    later <- require (Choice.insert 4 Choice.RootContinuation "late continuation" dormant)
    assertBool "a later registration wakes the same producer"
        (focusedOwnerDemanded id (const (Seq.singleton (Choice.OwnedChoice 4))) later source)
    assertEqual "dormancy preserves the cursor" (Just "cursor") (Choice.payload <$> Choice.lookup 1 later)
    assertBool "producer retirement does not cancel an external consumer"
        (Choice.live (Choice.OwnedChoice 4) (Choice.retire 1 later))

drivingDemand :: Assertion
drivingDemand = do
    let target = Driver.FocusedProducerKey (FocusedObligationId 0) Driver.GeneralSearch
        otherPhase = Driver.FocusedProducerKey (FocusedObligationId 0) Driver.DirectEvidence
        ancestor n = Driver.FocusedProducerKey (FocusedObligationId n) Driver.GeneralSearch
        anyProof = Driver.AnyObviousProof
        canonical = Driver.MustUseCanonicalDefinition
        drives requirement owner = (Driver.SearchDependency, requirement, owner)
        observes requirement owner = (Driver.ExistingEvidenceWait, requirement, owner)
    first <- require (Choice.insertProducer 1 (ancestor 1) () Choice.empty)
    second <- require (Choice.insertProducer 2 (ancestor 2) () first)
    forest <- require (Choice.insertProducer 3 target () second)
    let registry edge = Map.fromList
            [ (target, [drives anyProof (Choice.OwnedChoice 1)])
            , (otherPhase, [drives canonical Choice.RootContinuation])
            , (ancestor 1, [drives canonical (Choice.OwnedChoice 2)])
            , (ancestor 2, [edge])
            ]
        run work rows choices = Driver.countedFocusedDrivingRequirement work id
            (\key -> Seq.fromList (Map.findWithDefault [] key rows)) choices target
        blocked = registry (observes anyProof Choice.RootContinuation)
        live = registry (drives canonical Choice.RootContinuation)
    assertEqual "an indirect observer cannot drive a different producer phase" (Right Nothing)
        (fst (run 1000 blocked forest))
    assertEqual "canonical ancestry does not upgrade an ordinary child" (Right (Just anyProof))
        (fst (run 1000 live forest))
    let delegate = (Driver.PhaseDelegation, canonical, Choice.OwnedChoice 1)
        delegated = Map.fromList
            [(target, [delegate]), (ancestor 1, [drives anyProof Choice.RootContinuation])]
    assertEqual "delegation capacity is not canonical demand" (Right (Just anyProof))
        (fst (run 1000 delegated forest))
    assertEqual "delegation can receive later canonical demand" (Right (Just canonical))
        (fst (run 1000 (Map.insert (ancestor 1) [drives canonical Choice.RootContinuation] delegated) forest))
    assertEqual "delegation cannot pass an observer barrier" (Right Nothing)
        (fst (run 1000 (Map.insert (ancestor 1) [observes canonical Choice.RootContinuation] delegated) forest))
    let stronger = Map.insert target
            [drives anyProof (Choice.OwnedChoice 1), drives canonical (Choice.OwnedChoice 1)] live
    assertEqual "a later stronger label survives convergence on the same producer" (Right (Just canonical))
        (fst (run 1000 stronger forest))
    assertEqual "a shared observational cycle has no driving root" (Right Nothing)
        (fst (run 1000 (registry (drives anyProof (Choice.OwnedChoice 1))) forest))
    assertEqual "canceled continuations cannot authorize new work" (Right Nothing)
        (fst (run 1000 live (Choice.retire 1 forest)))
    let reattached = Map.insert target [drives anyProof Choice.RootContinuation] live
    assertEqual "a later real requester restores demand on the retained target" (Right (Just anyProof))
        (fst (run 1000 reattached (Choice.retire 1 forest)))
    let (expected, remaining) = run 1000 stronger forest
        used = 1000 - remaining
    assertEqual "exact authorization cost" (expected, 0) (run used stronger forest)
    assertEqual "insufficient authorization credit is not inactivity"
        (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1) stronger forest)

sharedDrivingDemand :: Assertion
sharedDrivingDemand = forM_ [16, 32, 64 :: Natural] \size -> do
    forest <- foldM (\choices key -> require (Choice.insertProducer key key () choices))
        Choice.empty [1 .. size]
    let driving owner = (Driver.SearchDependency, Driver.AnyObviousProof, owner)
        consumers key
            | key == size = Seq.fromList [driving (Choice.OwnedChoice 1), driving Choice.RootContinuation]
            | otherwise = Seq.replicate 2 (driving (Choice.OwnedChoice (key + 1)))
        (result, remaining) = Driver.countedFocusedDrivingRequirement 100000 id consumers forest 1
    assertEqual "a cyclic diamond retains its real root demand"
        (Right (Just Driver.AnyObviousProof)) result
    assertBool "shared paths are visited linearly, not once per path"
        (100000 - remaining < 20 * fromIntegral size)

admission :: Assertion
admission = do
    root <- require (Choice.insertProducer 1 (9 :: Natural) (10 :: Int) Choice.empty)
    child <- require (Choice.insert 2 (Choice.OwnedChoice 1) 20 root)
    let changed = Choice.adjust (+ 1) 1 child
        retired = Choice.retire 1 changed
    assertEqual "payload updates preserve inherited producer" (Just (Just 9))
        (Choice.ownerProducer (Choice.OwnedChoice 2) changed)
    assertBool "duplicate identifier rejected" (isNothing (Choice.insert 1 Choice.RootContinuation 0 child))
    assertBool "retired parent rejected" (isNothing (Choice.insert 3 (Choice.OwnedChoice 2) 0 retired))
    assertBool "descendants retire even without ready tasks" (null (Choice.rows retired))
    assertBool "repeated retirement is inert" (null (Choice.rows (Choice.retire 2 retired)))

deepRetirement :: Assertion
deepRetirement = do
    let first = fromIntegral (maxBound :: Int) + 100 :: Natural
    (forest, _) <- foldM (\(forest, owner) identifier -> do
        updated <- require (Choice.insert identifier owner () forest)
        pure (updated, Choice.OwnedChoice identifier)) (Choice.empty :: Choice.Forest Natural (), Choice.RootContinuation)
        [first .. first + 9999]
    assertBool "deep descendant live" (Choice.live (Choice.OwnedChoice (first + 9999)) forest)
    assertBool "deep subtree removed" (null (Choice.rows (Choice.retire first forest)))

require :: Maybe value -> IO value
require = maybe (assertFailure "fixture choice admission failed" >> fail "choice admission") pure
