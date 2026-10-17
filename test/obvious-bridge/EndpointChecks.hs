module EndpointChecks (tests) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious.Driver qualified as Obvious
import Felix.Checking.Semantic qualified as Semantic

import Control.Monad (when)
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Endpoint equality applications"
    [ testCase "constructs guarded commutativity without a ground query" guarded
    , testCase "uses projected, truth, and repeated guard evidence" guardEvidence
    , testCase "keeps missing guards and undetermined parameters out of reconstruction" missingEvidence
    , testCase "rejects inconsistent repeated slots before spending an application" repeatedSlots
    , testCase "reconstructs equations with different rigid heads in either direction" orientations
    , testCase "tries the whole pair before nested congruence" nested
    , testCase "shares its allowance across separate changed arguments" multiple
    , testCase "reuses duplicate and reversed equality demands" reuse
    , testCase "combines concrete equality paths and endpoint applications" mixed
    , testCase "retains canonical support from one consumed guard" canonicalGuard
    , testCase "upgrades a repeated demand from a later canonical guard" canonicalReuse
    , testCase "orients an ordinary equation before publishing it for support" canonicalReverse
    , testCase "does not count an unused definition as support" unusedDefinition
    , testCase "reuses an established guard without starting its proof search" establishedGuard
    , testCase "waits for a live guard producer and reuses its canonical result" liveGuard
    , testCase "finishes a guard wait when its producer cannot prove the premise" failedGuardProducer
    , testCase "keeps guard certificates inside their nominal assumption scope" guardScopes
    , testCase "settles a cyclic guard wait without losing its continuation" cyclicGuardProducer
    , testCase "assembles guards from separately established components" assembledGuard
    ]

binary :: CanonicalTerm global -> CanonicalTerm global -> CanonicalTerm global -> CanonicalTerm global
binary function left right = CApp (CApp function left) right

binaryType :: CoreType
binaryType = TyArrow TySet (TyArrow TySet TySet)

context :: [CoreType]
context = [TySet, TySet, binaryType, TyArrow TySet TyProp, TyArrow TySet TyProp]

a, b, ga, gb, source, target, equation, commutativity :: CanonicalTerm Void
a = CBound 0
b = CBound 1
ga = CApp (CBound 3) a
gb = CApp (CBound 3) b
source = CApp (CBound 4) (binary (CBound 2) b a)
target = CApp (CBound 4) (binary (CBound 2) a b)
equation = CEq TySet (binary (CBound 4) (CBound 1) (CBound 0))
    (binary (CBound 4) (CBound 0) (CBound 1))
commutativity = CForall TySet (CForall TySet
    (CImp (CApp (CBound 5) (CBound 1)) (CImp (CApp (CBound 5) (CBound 0)) equation)))

guarded :: Assertion
guarded = do
    check 0 False (0, True) context [ga, gb, source, commutativity] target
    check 1 True (1, False) context [ga, gb, source, commutativity] target

guardEvidence :: Assertion
guardEvidence = do
    check 1 True (1, False) context [CAnd ga gb, source, commutativity] target
    let truth = CForall TySet (CForall TySet (CImp CTruth equation))
        repeated = CForall TySet (CForall TySet
            (CImp (CApp (CBound 5) (CBound 1)) (CImp (CApp (CBound 5) (CBound 1)) equation)))
    check 1 True (1, False) context [source, truth] target
    check 1 True (1, False) context [ga, gb, source, repeated] target

missingEvidence :: Assertion
missingEvidence = do
    check 16 False (2, False) context [ga, source, commutativity] target
    let guardOnly = CForall TySet (CForall TySet (CForall TySet
            (CImp (CApp (CBound 6) (CBound 0))
                (CEq TySet (binary (CBound 5) (CBound 2) (CBound 1))
                    (binary (CBound 5) (CBound 1) (CBound 2))))))
    check 16 False (0, False) context [ga, gb, source, guardOnly] target

repeatedSlots :: Assertion
repeatedSlots = do
    let same = binary (CBound 3) (CBound 0) (CBound 0)
        theorem = CForall TySet (CImp (CApp (CBound 4) (CBound 0)) (CEq TySet same same))
    check 16 False (0, False) context [ga, gb, source, theorem] target

orientations :: Assertion
orientations = do
    let types = [TySet, TyArrow TySet TySet, TyArrow TySet TySet,
            TyArrow TySet TyProp, TyArrow TySet TyProp]
        f = CApp (CBound 1) a
        g = CApp (CBound 2) a
        predicate = CApp (CBound 4)
        theorem = CForall TySet (CImp (CApp (CBound 4) (CBound 0))
            (CEq TySet (CApp (CBound 2) (CBound 0)) (CApp (CBound 3) (CBound 0))))
    check 1 True (1, False) types [ga, predicate f, theorem] (predicate g)
    check 1 True (1, False) types [ga, predicate g, theorem] (predicate f)

nested :: Assertion
nested = do
    let predicate value = CApp (CBound 4) (CApp (CBound 5) value)
    check 1 True (1, False) (context <> [TyArrow TySet TySet])
        [ga, gb, predicate (binary (CBound 2) b a), commutativity]
        (predicate (binary (CBound 2) a b))

multiple :: Assertion
multiple = do
    let types = replicate 4 TySet <> [binaryType, TyArrow TySet (TyArrow TySet TyProp)]
        op = binary (CBound 4)
        predicate = binary (CBound 5)
        theorem = CForall TySet (CForall TySet (CImp CTruth
            (CEq TySet (binary (CBound 6) (CBound 1) (CBound 0))
                (binary (CBound 6) (CBound 0) (CBound 1)))))
        facts = [predicate (op b a) (op (CBound 3) (CBound 2)), theorem]
        goal = predicate (op a b) (op (CBound 2) (CBound 3))
    check 1 False (1, True) types facts goal
    check 2 True (2, False) types facts goal

reuse :: Assertion
reuse = do
    let types = [TySet, TySet, binaryType, TyArrow TySet (TyArrow TySet TyProp)]
        op = binary (CBound 2)
        predicate = binary (CBound 3)
        theorem = CForall TySet (CForall TySet (CImp CTruth equation))
    check 1 True (1, False) types [predicate (op b a) (op b a), theorem]
        (predicate (op a b) (op a b))
    check 1 True (1, False) types [predicate (op b a) (op a b), theorem]
        (predicate (op a b) (op b a))

mixed :: Assertion
mixed = do
    let types = replicate 4 TySet <> [binaryType, TyArrow TySet (TyArrow TySet TyProp)]
        op = binary (CBound 4)
        predicate = binary (CBound 5)
        theorem = CForall TySet (CForall TySet (CImp CTruth
            (CEq TySet (binary (CBound 6) (CBound 1) (CBound 0))
                (binary (CBound 6) (CBound 0) (CBound 1)))))
    check 1 True (1, False) types
        [CEq TySet (CBound 2) (CBound 3), predicate (CBound 3) (op b a), theorem]
        (predicate (CBound 2) (op a b))

canonicalGuard :: Assertion
canonicalGuard = do
    let guardA = CEq TyProp (CBound 5) CTruth
        guardB = CEq TyProp (CBound 6) CTruth
        theorem = CForall TySet (CForall TySet
            (CImp (CEq TyProp (CBound 7) CTruth)
                (CImp (CEq TyProp (CBound 8) CTruth) equation)))
    checkWith Obvious.MustUseCanonicalDefinition [0] 1 True (1, False)
        (context <> [TyProp, TyProp]) [guardA, guardB, source, theorem] target

canonicalReuse :: Assertion
canonicalReuse = do
    let guardA = CEq TyProp (CBound 5) CTruth
        guardB = CEq TyProp (CBound 6) CTruth
        theorem = CForall TySet (CForall TySet
            (CImp (CEq TyProp (CBound 7) CTruth)
                (CImp (CEq TyProp (CBound 8) CTruth) equation)))
    checkWith Obvious.MustUseCanonicalDefinition [4] 1 True (1, False)
        (context <> [TyProp, TyProp]) [guardA, guardB, source, theorem, guardA] (CAnd target target)

canonicalReverse :: Assertion
canonicalReverse = do
    let types = [TySet, TyArrow TySet TySet, TyArrow TySet TySet,
            TyProp, TyArrow TySet TyProp]
        guardFact = CEq TyProp (CBound 3) CTruth
        f = CApp (CBound 1) a
        g = CApp (CBound 2) a
        predicate = CApp (CBound 4)
        theorem = CForall TySet (CImp (CEq TyProp (CBound 4) CTruth)
            (CEq TySet (CApp (CBound 2) (CBound 0)) (CApp (CBound 3) (CBound 0))))
    checkWith Obvious.MustUseCanonicalDefinition [3] 1 True (1, False)
        types [guardFact, predicate g, theorem, guardFact] (CAnd (predicate f) (predicate f))

unusedDefinition :: Assertion
unusedDefinition = checkWith Obvious.MustUseCanonicalDefinition [4] 1 False (1, True)
    (context <> [TyProp]) [ga, gb, source, commutativity, CEq TyProp (CBound 5) CTruth] target

establishedGuard :: Assertion
establishedGuard = do
    let evidence = CBound 5
        theorem = CForall TySet (CForall TySet (CImp (CBound 7) equation))
        facts = [source, theorem, CImp CTruth evidence]
    check 1 True (1, False) (context <> [TyProp]) facts (CAnd evidence target)
    -- The same implication is not permission to start a new guard search.
    check 1 False (1, True) (context <> [TyProp]) facts target

assembledGuard :: Assertion
assembledGuard = do
    let evidence = CBound 5
        theorem = CForall TySet (CForall TySet (CImp (CAnd (CBound 7) CTruth) equation))
        facts = [source, theorem, CImp CTruth evidence]
    check 1 True (1, False) (context <> [TyProp]) facts (CAnd evidence target)
    check 1 False (1, True) (context <> [TyProp]) facts target

liveGuard :: Assertion
liveGuard = for_ [Obvious.AnyObviousProof, Obvious.MustUseCanonicalDefinition] \requirement ->
  for_ [False, True] \compound -> do
    let evidence = CBound 5
        prerequisite = CBound 6
        definition = CEq TyProp (CBound 8) CTruth
        antecedent = if compound then CAnd (CBound 7) CTruth else CBound 7
        theorem = CForall TySet (CForall TySet (CImp antecedent equation))
        facts = [source, theorem, CImp prerequisite evidence, CImp definition prerequisite, definition]
        goal = COr (CAnd evidence (CBound 7)) target
    statistics <- checkReport requirement [4] 1 True (1, False)
        (context <> replicate 4 TyProp) facts goal
    assertBool "the guard certificate was unavailable when its live producer was subscribed"
        (Obvious.obviousEndpointGuardWaits statistics > 0)

failedGuardProducer :: Assertion
failedGuardProducer = for_ [Obvious.AnyObviousProof, Obvious.MustUseCanonicalDefinition] \requirement -> do
    let evidence = CBound 5
        definition = CEq TyProp (CBound 8) CTruth
        theorem = CForall TySet (CForall TySet (CImp (CBound 7) equation))
        facts = [source, theorem, CImp (CBound 6) evidence, definition]
        goal = COr (CAnd evidence (CBound 7)) target
    statistics <- checkReport requirement [3] 1 False (1, True)
        (context <> replicate 4 TyProp) facts goal
    assertBool "a missing result completes an actually registered wait"
        (Obvious.obviousEndpointGuardWaits statistics > 0)

guardScopes :: Assertion
guardScopes = do
    let evidence = CBound 5
        theorem = CForall TySet (CForall TySet (CImp (CBound 7) equation))
        facts = [source, theorem]
    check 3 False (3, False) (context <> [TyProp, TyProp]) facts
        (CAnd (CImp evidence target) (CImp (CBound 6) target))

cyclicGuardProducer :: Assertion
cyclicGuardProducer = for_ [Obvious.AnyObviousProof, Obvious.MustUseCanonicalDefinition] \requirement -> do
    let evidence = CBound 5
        prerequisite = CBound 6
        definition = CEq TyProp (CBound 8) CTruth
        theorem = CForall TySet (CForall TySet (CImp (CBound 7) equation))
        facts = [source, theorem, CImp prerequisite evidence, CImp evidence prerequisite, definition]
        goal = COr (CAnd evidence (CBound 7)) target
    -- Ordinary recursion returns through its active-request guard and reaches
    -- the next orientation; canonical demand retains the shared fixed point.
    statistics <- checkReport requirement [4] 1 False (1, requirement == Obvious.AnyObviousProof)
        (context <> replicate 4 TyProp) facts goal
    assertBool "the cyclic dependency included an endpoint guard consumer"
        (Obvious.obviousEndpointGuardWaits statistics > 0)

check
    :: Word -> Bool -> (Word, Bool) -> [CoreType]
    -> [CanonicalTerm Void] -> CanonicalTerm Void -> Assertion
check = checkWith Obvious.AnyObviousProof []

checkWith
    :: Obvious.ProofRequirement -> [Natural]
    -> Word -> Bool -> (Word, Bool) -> [CoreType]
    -> [CanonicalTerm Void] -> CanonicalTerm Void -> Assertion
checkWith requirement definitions limit expected expectedBreadth types rawFacts rawGoal =
    void (checkReport requirement definitions limit expected expectedBreadth types rawFacts rawGoal)

checkReport
    :: Obvious.ProofRequirement -> [Natural]
    -> Word -> Bool -> (Word, Bool) -> [CoreType]
    -> [CanonicalTerm Void] -> CanonicalTerm Void -> IO Obvious.ObviousStatistics
checkReport requirement definitions limit expected expectedBreadth types rawFacts rawGoal = do
    foundation <- require Foundation.checkedFoundation
    facts <- traverse (require . checkScopedCanonicalCore emptyGlobalTyping types) rawFacts
    goal <- require (checkScopedCanonicalCore emptyGlobalTyping types rawGoal)
    let report = Obvious.obviousProofReportWithPolicy
            (Obvious.disabledSearchPolicy { Obvious.policyEndpoints = Obvious.EndpointApplications limit })
            Obvious.defaultObviousBudget {Obvious.obviousRefutationWorkLimit = 0}
            requirement foundation emptyGlobalTyping facts []
            [Obvious.obviousLocalDefinitionView index Semantic.DefinitionExactView | index <- definitions] goal
        statistics = Obvious.obviousRunStatistics report
    case Obvious.obviousRunResult report of
        Left failure -> do
            assertBool ("expected a checked proof, got " <> show failure) (not expected)
            assertBool ("search miss must not hide malformed input or an integrity defect: " <> show failure)
                (Obvious.obviousFailureClass failure `notElem` [Obvious.ObviousMalformedClass, Obvious.ObviousIntegrityClass])
        Right proof -> do
            assertBool "negative control unexpectedly proved its target" expected
            replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                emptyGlobalTyping Vector.empty (Vector.fromList facts) goal
                (Proof.builtProofDerivation (Obvious.obviousBuiltProof proof)))
            assertEqual "independent replay has the exact target" goal (replayedScopedKernelTarget replayed)
            when (requirement == Obvious.MustUseCanonicalDefinition) do
                assertBool "replayed proof consumes a selected definition"
                    (any (\index -> Set.member (hypothesisIx index)
                        (replayedScopedKernelExternalHypothesisUses replayed)) definitions)
    assertEqual "no ground work" 0 (Obvious.obviousRefutationWorkConsumed statistics)
    assertEqual "no ground terms" 0 (Obvious.obviousTermsAdmitted statistics)
    assertEqual "request-wide endpoint allowance" [expectedBreadth]
        [(used, deferred) | Obvious.ObviousEndpointBreadth _ used deferred <- Obvious.obviousBreadthObservations statistics]
    pure statistics

require :: Show error => Either error value -> IO value
require = either (assertFailure . show) pure
