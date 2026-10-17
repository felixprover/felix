module ExtensionalityChecks (tests) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious.Driver qualified as Driver
import Felix.Checking.Semantic qualified as Semantic

import Control.Monad (foldM, when)
import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Retained extensional reconstruction"
    [ testCase "wraps only the selected function prefix and retries only its final conversion" functionPrefixes
    , testCase "uses actual Boolean directions and the propositional foundation leaf" booleanDirections
    , testCase "runs pointwise prefix publication through ordinary scheduling" scheduledPrefixes
    , testCase "keeps general premise search outside intermediate prefixes" prefixFragment
    , testCase "integrates Boolean directions and genuinely ground-needed distributivity" scheduledBooleans
    , testCase "resumes ordinary body search after a native miss and retains directional support" booleanBodyFallback
    , testGroup "blocked Boolean bodies"
        [testCase label (booleanBodyHandoff exhaustGround)
        | (label, exhaustGround) <- [("ground exhausted: releases focused fallback", True),
            ("focused exhausted: retains native query and late delivery", False)]]
    , testCase "selected-fact opportunity failure releases the saved body fallback" selectedFactBodyHandoff
    , testCase "completes function arguments but not operators, guards, or nested completion" restrictedArguments
    , testCase "a canonical parent consumes an ordinary equality without upgrading it" delegatedOrdinary
    , testCase "an indirect observer cannot resume canceled equality inference" delegatedObserver
    , testCase "directional inventories keep their selected catalogue and common ancestor" directionalInventories
    , testCase "Boolean extensionality does not manufacture definition use" unusedBooleanDefinition
    ]

require :: Show failure => Either failure value -> IO value
require = either (\failure -> assertFailure (show failure) >> fail "unreachable") pure

booleanBodyHandoff :: Bool -> Assertion
booleanBodyHandoff exhaustGround = do
    foundation <- require Foundation.checkedFoundation
    let types = [TyProp, TyProp]
    implication <- checked types (CImp (CBound 0) (CBound 1))
    antecedent <- checked types (CBound 0)
    let hypotheses = [antecedent, implication]
    target <- checked types (CApp (CLam TyProp (CBound 0)) (CBound 1))
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    parent <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [implication])
    theorem <- require (Proof.hypothesisProof context implication)
    premise <- require (Proof.hypothesisProof context antecedent)
    late <- require (Proof.implicationEliminationProof context theorem premise)
    let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
            (Driver.GroundAllowance 2000000 4096 4096 4096 Driver.UniversalsDisabled) parent Map.empty \scope ->
                Driver.scopeBooleanBodyHandoff
                    (if exhaustGround then Driver.BodyGroundExhausted else Driver.BodyFocusedExhausted)
                    scope antecedent target late
    (proof, focused, ground, retained) <- require result
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target (Proof.builtProofDerivation proof))
    assertEqual "exact written body target" target (replayedScopedKernelTarget replayed)
    assertEqual "only the actual theorem and antecedent" (Set.fromList (hypothesisIx <$> [0, 1]))
        (replayedScopedKernelExternalHypothesisUses replayed)
    if exhaustGround then do
        assertEqual "authorization and partially paid fork are not refunded" 6 ground
        assertBool "the ordinary theorem fallback consumed its own credit" (focused > 0)
    else do
        assertEqual "native work does not borrow focused credit" 0 focused
        assertBool "late evidence completes the same query" retained
        assertBool "fork, demand checks and native work remain charged" (ground > 4)

selectedFactBodyHandoff :: Assertion
selectedFactBodyHandoff = do
    foundation <- require Foundation.checkedFoundation
    let types = [TyProp, TyProp, TyArrow TySet TyProp, TySet]
    antecedent <- checked types (CBound 0)
    implication <- checked types (CImp (CBound 0) (CBound 1))
    universal <- checked types (CForall TySet (CApp (CBound 3) (CBound 0)))
    argument <- checked types (CBound 3)
    target <- checked types (CApp (CLam TyProp (CBound 0)) (CBound 1))
    let hypotheses = [antecedent, universal, implication]
    parent <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [universal, implication])
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    source <- require (Proof.hypothesisProof context universal)
    -- The selected instance introduces a concrete term absent from the frozen
    -- body domain. Its source remains authorized, but the fallback needs neither.
    selected <- require (Proof.forallEliminationProof context source argument)
    let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
            (Driver.GroundAllowance 2000000 4096 4096 4096 Driver.UniversalsDisabled) parent Map.empty \scope ->
                Driver.scopeBooleanBodyHandoff Driver.BodySelectedFactExhausted scope antecedent target selected
    (proof, focused, ground, _) <- require result
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList hypotheses) target (Proof.builtProofDerivation proof))
    assertEqual "exact written body target" target (replayedScopedKernelTarget replayed)
    assertEqual "the unused selected fact is not a proof dependency"
        (Set.fromList (hypothesisIx <$> [0, 2])) (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "authorization and partially completed capture stay charged" 4 ground
    assertBool "the retained theorem fallback pays for its own inference" (focused > 0)

checked :: [CoreType] -> CanonicalTerm Void -> IO (ScopedCheckedCore Void)
checked types = require . checkScopedCanonicalCore emptyGlobalTyping types

scheduledPrefixes :: Assertion
scheduledPrefixes = for_ [(1, 1, 1), (3, 1, 1), (3, 1, 2), (3, 2, 3), (3, 3, 3), (16, 16, 16) :: (Int, Int, Int)] \(arity, depth, supportDepth) -> do
    let arrow count = foldr (const (TyArrow TySet)) TySet [1 .. count]
        types = [arrow arity, arrow arity, TyProp]
        applied count index = foldl' CApp (CBound index) (CBound <$> reverse [0 .. fromIntegral count - 1])
        leaf count = CEq (arrow (arity - count)) (applied count (fromIntegral count)) (applied count (fromIntegral count + 1))
        pointwise = foldr (const (CForall TySet)) (leaf depth) [1 .. depth]
    foundation <- require Foundation.checkedFoundation
    hypothesis <- checked types pointwise
    guardFact <- checked types (CEq TyProp (CBound 2) CTruth)
    supported <- checked types (foldr (const (CForall TySet))
        (CImp (CEq TyProp (CBound (fromIntegral supportDepth + 2)) CTruth) (leaf supportDepth)) [1 .. supportDepth])
    target <- checked types (CEq (arrow arity) (CBound 0) (CBound 1))
    for_ [Driver.AnyObviousProof, Driver.MustUseCanonicalDefinition] \requirement -> do
        let report = Driver.obviousProofReportWithPolicy Driver.disabledSearchPolicy
                Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
                requirement foundation emptyGlobalTyping [hypothesis, guardFact, supported] []
                [Driver.obviousLocalDefinitionView 1 Semantic.DefinitionExactView
                    | requirement == Driver.MustUseCanonicalDefinition] target
        proof <- either (\failure -> assertFailure (show (arity, depth, requirement) <> ": " <> show failure)
            >> fail "unreachable") pure (Driver.obviousRunResult report)
        replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList [hypothesis, guardFact, supported]) target
            (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
        assertEqual "scheduled exact target" target (replayedScopedKernelTarget replayed)
        assertEqual "only the selected prefix sources" (Set.fromList (hypothesisIx <$>
            if requirement == Driver.AnyObviousProof then [0] else [1, 2]))
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual "function equality adds no axiom" Set.empty (replayedScopedKernelFoundationUses replayed)
        when (arity == 16 && requirement == Driver.AnyObviousProof) do
            -- This is the same genuine SmallPreparation retry exercised by
            -- functionPrefixes, now reached through the scheduler and sources.
            assertEqual "final conversion retains exactly one wrapper per paid binder" 34
                (replayedScopedKernelNodeCount replayed)
            assertEqual "retry does not reopen the pointwise spine" 16
                (fst (Driver.obviousScopeInventory (Driver.obviousRunStatistics report)))
        assertEqual "no leaf ground execution was enabled" 0
            (Driver.obviousRefutationWorkConsumed (Driver.obviousRunStatistics report))
        when (requirement == Driver.AnyObviousProof && depth < arity) do
            assertEqual "an immediate prefix closes without opening the unused suffix" depth
                (fst (Driver.obviousScopeInventory (Driver.obviousRunStatistics report)))
            assertEqual "an immediate prefix creates no unused leaf family" 1
                (snd (Driver.obviousScopeInventory (Driver.obviousRunStatistics report)))

prefixFragment :: Assertion
prefixFragment = do
    foundation <- require Foundation.checkedFoundation
    let unary = TyArrow TySet TySet
        binary = TyArrow TySet unary
        types = [binary, binary, TyProp, TyProp, TySet]
        equation x f g = CEq unary (CApp f x) (CApp g x)
        theorem = CForall TySet (CImp (CBound 4) (equation (CBound 0) (CBound 1) (CBound 2)))
    facts <- traverse (checked types) [CBound 2, CImp (CBound 2) (CBound 3), theorem]
    for_ [(False, CEq binary (CBound 0) (CBound 1)),
            (True, equation (CBound 4) (CBound 0) (CBound 1))] \(expected, raw) -> do
        target <- checked types raw
        let report = Driver.obviousProofReportWithPolicy Driver.disabledSearchPolicy
                Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
                Driver.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        case Driver.obviousRunResult report of
            Left failure -> do
                assertBool ("ordinary equality unexpectedly failed: " <> show failure) (not expected)
                assertBool ("a route miss must not hide an infrastructure failure: " <> show failure)
                    (case failure of
                        Driver.ObviousResourceExhausted{} -> False
                        _ -> Driver.obviousFailureClass failure `notElem`
                            [Driver.ObviousMalformedClass, Driver.ObviousIntegrityClass])
            Right proof -> do
                assertBool "prefix proof recursively searched its premise" expected
                replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                    emptyGlobalTyping Vector.empty (Vector.fromList facts) target
                    (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
                assertEqual "exact ordinary target" target (replayedScopedKernelTarget replayed)

scheduledBooleans :: Assertion
scheduledBooleans = do
    foundation <- require Foundation.checkedFoundation
    let types = replicate 3 TyProp
        a = CBound 0
        b = CBound 1
        c = CBound 2
        beta term = foldr (const (CApp (CLam TyProp (CBound 0)))) term [1 .. 24 :: Int]
        left = CAnd (COr (beta a) (beta b)) (beta c)
        right = COr (CAnd a c) (CAnd b c)
    for_ [(False, a, b, [CImp a b, CImp b a]),
            (True, left, right, []), (True, right, left, [])] \(groundNeeded, p, q, rawFacts) -> do
        facts <- traverse (checked types) rawFacts
        target <- checked types (CEq TyProp p q)
        let report = Driver.obviousProofReportWithPolicy Driver.disabledSearchPolicy
                (if groundNeeded then Driver.defaultObviousBudget
                    else Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0})
                Driver.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        proof <- require (Driver.obviousRunResult report)
        replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.fromList facts) target
            (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
        assertEqual "Boolean worker restores exact endpoints" target (replayedScopedKernelTarget replayed)
        assertBool "actual propositional extensionality is consumed"
            (Set.member Foundation.PropositionalExtensionality (replayedScopedKernelFoundationUses replayed))
        when groundNeeded (assertBool "conversion and focused introduction cannot mask the ground route"
            (Driver.obviousRefutationWorkConsumed (Driver.obviousRunStatistics report) > 0))

restrictedArguments :: Assertion
restrictedArguments = do
    foundation <- require Foundation.checkedFoundation
    let function = TyArrow TySet TySet
        pointwise = CForall TySet (CEq TySet (CApp (CBound 1) (CBound 0)) (CApp (CBound 2) (CBound 0)))
        argumentTypes = [function, function, TyArrow function TyProp]
        predicate = CApp (CBound 2)
        operatorTypes = [function, function, TyArrow TySet TyProp, TySet, TySet]
        guardedTypes = argumentTypes <> [function, function]
        guarded = CForall TySet (CImp (CEq function (CBound 4) (CBound 5))
            (CEq TySet (CApp (CBound 1) (CBound 0)) (CApp (CBound 2) (CBound 0))))
        guardSource = CForall TySet (CEq TySet (CApp (CBound 4) (CBound 0)) (CApp (CBound 5) (CBound 0)))
        nestedTypes = argumentTypes <> [TyArrow function function]
        nested index = CLam TySet (CApp (CApp (CBound 4) (CBound index)) (CBound 0))
        cases =
            [ ("argument", True, argumentTypes, [predicate (CBound 0), pointwise], predicate (CBound 1))
            , ("operator", False, operatorTypes,
                [predicate (CApp (CBound 0) (CBound 3)), pointwise, CEq TySet (CBound 3) (CBound 4)],
                predicate (CApp (CBound 1) (CBound 4)))
            , ("guard", False, guardedTypes, [predicate (CBound 0), guarded, guardSource], predicate (CBound 1))
            , ("nested", False, nestedTypes, [predicate (nested 1), pointwise], predicate (nested 2))
            ]
    for_ cases \(label, expected, types, rawFacts, rawGoal) -> do
        facts <- traverse (checked types) rawFacts
        target <- checked types rawGoal
        let report = Driver.obviousProofReportWithPolicy
                (Driver.disabledSearchPolicy { Driver.policyEndpoints = Driver.EndpointApplications 16 })
                Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
                Driver.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        case Driver.obviousRunResult report of
            Left failure -> do
                assertBool (label <> ": " <> show failure) (not expected)
                assertBool (label <> " must be a route miss: " <> show failure) (case failure of
                    Driver.ObviousResourceExhausted{} -> False
                    _ -> Driver.obviousFailureClass failure `notElem`
                        [Driver.ObviousMalformedClass, Driver.ObviousIntegrityClass])
            Right proof -> do
                assertBool (label <> " acquired forbidden completion permission") expected
                replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                    emptyGlobalTyping Vector.empty (Vector.fromList facts) target
                    (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
                assertEqual "exact transported target" target (replayedScopedKernelTarget replayed)
                assertEqual "only supplied transport and pointwise evidence" (Set.fromList [hypothesisIx 0, hypothesisIx 1])
                    (replayedScopedKernelExternalHypothesisUses replayed)
                assertEqual "no function-extensionality foundation leaf" Set.empty (replayedScopedKernelFoundationUses replayed)
        assertEqual "restricted completion creates no ground work" 0
            (Driver.obviousRefutationWorkConsumed (Driver.obviousRunStatistics report))

delegatedOrdinary :: Assertion
delegatedOrdinary = do
    foundation <- require Foundation.checkedFoundation
    let function = TyArrow TySet TySet
        binary = TyArrow TySet function
        types = [binary, binary, TyProp]
        pointwise = CForall TySet (CEq function (CApp (CBound 1) (CBound 0)) (CApp (CBound 2) (CBound 0)))
        definition = CEq TyProp (CBound 2) CTruth
    facts <- traverse (checked types) [pointwise, definition]
    target <- checked types (CAnd (CEq binary (CBound 0) (CBound 1)) definition)
    let report = Driver.obviousProofReportWithPolicy Driver.disabledSearchPolicy
            Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
            Driver.MustUseCanonicalDefinition foundation emptyGlobalTyping facts []
            [Driver.obviousLocalDefinitionView 1 Semantic.DefinitionExactView] target
    proof <- require (Driver.obviousRunResult report)
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList facts) target
        (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
    assertEqual "both actual branches are consumed" (Set.fromList [hypothesisIx 0, hypothesisIx 1])
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "ordinary child needs no canonical descent or unused leaf" (1, 1)
        (Driver.obviousScopeInventory (Driver.obviousRunStatistics report))

delegatedObserver :: Assertion
delegatedObserver = do
    foundation <- require Foundation.checkedFoundation
    let function = TyArrow TySet TySet
        types = [function, function, TyProp, TyProp, TySet, TySet, TyArrow TySet TyProp]
        equation = CEq function (CBound 0) (CBound 1)
        pointwise = CForall TySet (CEq TySet (CApp (CBound 1) (CBound 0)) (CApp (CBound 2) (CBound 0)))
        predicate = CApp (CBound 6)
        targetTerm = CAnd (COr (CBound 2) (CBound 3)) (predicate (CBound 5))
        factsTerm = [CImp equation (CBound 2), CImp CTruth (CBound 3),
            CImp (CBound 2) (CEq TySet (CBound 4) (CBound 5)), predicate (CBound 4), pointwise]
    facts <- traverse (checked types) factsTerm
    target <- checked types targetTerm
    let report = Driver.obviousProofReportWithPolicy
            (Driver.disabledSearchPolicy { Driver.policyEndpoints = Driver.EndpointApplications 16 })
            Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
            Driver.AnyObviousProof foundation emptyGlobalTyping facts [] [] target
        statistics = Driver.obviousRunStatistics report
    assertBool "the canceled branch registered an actual observational wait"
        (Driver.obviousEndpointGuardWaits statistics > 0)
    assertEqual "the indirect observer cannot pay for a new pointwise binder" 0
        (fst (Driver.obviousScopeInventory statistics))
    case Driver.obviousRunResult report of
        Right _ -> assertFailure "an observer proved its canceled equality dependency"
        Left failure -> assertBool ("observer settlement is a local miss: " <> show failure)
            (Driver.obviousFailureClass failure `notElem` [Driver.ObviousMalformedClass, Driver.ObviousIntegrityClass])

booleanBodyFallback :: Assertion
booleanBodyFallback = do
    foundation <- require Foundation.checkedFoundation
    let function = TyArrow TySet TySet
        types = [function, function, TyArrow function TyProp, TyProp]
        p = CAnd (CApp (CBound 2) (CBound 0)) (CBound 3)
        q = CAnd (CApp (CBound 2) (CBound 1)) (CBound 3)
    pointwise <- checked types (CForall TySet (CEq TySet
        (CApp (CBound 1) (CBound 0)) (CApp (CBound 2) (CBound 0))))
    target <- checked types (CEq TyProp p q)
    let report = Driver.obviousProofReport Driver.defaultObviousBudget Driver.AnyObviousProof
            foundation emptyGlobalTyping [pointwise] [] [] target
    proof <- require (Driver.obviousRunResult report)
    assertBool "native body work really ran" (Driver.obviousRefutationWorkConsumed (Driver.obviousRunStatistics report) > 0)
    assertBool "ordinary fallback completed a function argument"
        (fst (Driver.obviousScopeInventory (Driver.obviousRunStatistics report)) > 0)
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
        Vector.empty (Vector.singleton pointwise) target (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
    assertEqual "fallback exact target" target (replayedScopedKernelTarget replayed)
    assertEqual "only pointwise evidence is consumed" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertBool "both actual directions enter extensional reconstruction"
        (Foundation.PropositionalExtensionality `Set.member` replayedScopedKernelFoundationUses replayed)

    facts <- traverse (checked [TyProp, TyProp])
        [CImp (CBound 0) (CBound 1), CImp (CBound 1) (CBound 0), CEq TyProp (CBound 0) CTruth]
    supportedTarget <- checked [TyProp, TyProp] (CEq TyProp (CBound 0) (CBound 1))
    let supported = Driver.obviousProofReport Driver.defaultObviousBudget Driver.MustUseCanonicalDefinition
            foundation emptyGlobalTyping facts []
            [Driver.obviousLocalDefinitionView 2 Semantic.DefinitionExactView] supportedTarget
    supportedProof <- require (Driver.obviousRunResult supported)
    supportedReplay <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
        Vector.empty (Vector.fromList facts) supportedTarget
        (Proof.builtProofDerivation (Driver.obviousBuiltProof supportedProof)))
    assertEqual "support upgrade keeps the exact target" supportedTarget (replayedScopedKernelTarget supportedReplay)
    assertBool "one consumed direction supplies actual definition use"
        (hypothesisIx 2 `Set.member` replayedScopedKernelExternalHypothesisUses supportedReplay)

directionalInventories :: Assertion
directionalInventories = do
    foundation <- require Foundation.checkedFoundation
    let types = [TySet, TySet, TySet, TyArrow TySet TyProp, TyProp]
    unrelated <- checked types (CBound 4)
    left <- checked types (CApp (CBound 3) (CBound 0))
    right <- checked types (CApp (CBound 3) (CBound 1))
    selected <- checked types (CApp (CBound 3) (CBound 2))
    compatible <- checked types (COr (scopedCoreTerm left) (scopedCoreTerm right))
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [])
    for_ [(left, right), (right, left)] \(p, q) -> for_ [unrelated, compatible] \anchor -> do
        let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
                (Driver.GroundAllowance 2000000 100 100 100 Driver.UniversalsDisabled) context Map.empty \scope ->
                    Driver.scopeDirectionalInventories scope anchor p q selected TySet
        (inventories, common) <- require result
        assertBool "the selected family belongs to the equality entry, not an assumption child" common
        case inventories of
            [original, forward, descendant, backward, outside, retained] -> do
                assertEqual "both directions use the same concrete inventory" forward backward
                assertEqual "the selected domain has both actual seed operands" (Set.fromList [CBound 0, CBound 1])
                    (Set.fromList (scopedCoreTerm <$> forward))
                assertEqual "the descendant keeps its selected-goal term above the common pair"
                    (Set.fromList [CBound 0, CBound 1, CBound 2])
                    (Set.fromList (scopedCoreTerm <$> descendant))
                assertEqual "read-only original authority gains no selection rights" original outside
                assertEqual "selected-family witness cursors do not contaminate the original cache" original retained
            _ -> assertFailure "incomplete directional inventory observation"

unusedBooleanDefinition :: Assertion
unusedBooleanDefinition = do
    foundation <- require Foundation.checkedFoundation
    let types = replicate 3 TyProp
        p = CBound 0
        q = CBound 1
    facts <- traverse (checked types) [CImp p q, CImp q p, CEq TyProp (CBound 2) CTruth]
    target <- checked types (CEq TyProp p q)
    let report = Driver.obviousProofReportWithPolicy Driver.disabledSearchPolicy
            Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
            Driver.MustUseCanonicalDefinition foundation emptyGlobalTyping facts []
            [Driver.obviousLocalDefinitionView 2 Semantic.DefinitionExactView] target
    case Driver.obviousRunResult report of
        Right _ -> assertFailure "propositional extensionality or unused syntax supplied definition use"
        Left failure -> assertEqual "ordinary directions do not meet the support requirement"
            Driver.ObviousDefinitionEvidenceRequiredClass (Driver.obviousFailureClass failure)

functionPrefixes :: Assertion
functionPrefixes = for_ [(1, 1), (3, 1), (3, 3), (16, 16) :: (Int, Int)] \(arity, depth) -> do
    foundation <- require Foundation.checkedFoundation
    let arrow count = foldr (const (TyArrow TySet)) TySet [1 .. count]
        types = [arrow arity, arrow arity]
        arguments = reverse [0 .. fromIntegral depth - 1]
        applied index = foldl' CApp (CBound index) (CBound <$> arguments)
        leafTerm = CEq (arrow (arity - depth))
            (applied (fromIntegral depth)) (applied (fromIntegral depth + 1))
        pointwise = foldr (const (CForall TySet)) leafTerm [1 .. depth]
    hypothesis <- checked types pointwise
    target <- checked types (CEq (arrow arity) (CBound 0) (CBound 1))
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [hypothesis])
    inner <- foldM (\owner _ -> fst <$> require (Proof.extendProofContextBinder owner TySet)) context [1 .. depth]
    universal <- require (Proof.indexedHypothesisProof inner (hypothesisIx 0))
    leaf <- foldM (\proof index -> do
        argument <- checked (Proof.proofContextTypes inner) (CBound index)
        require (Proof.forallEliminationProof inner proof argument)) universal arguments
    let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
            (Driver.GroundAllowance 0 0 0 0 Driver.UniversalsDisabled) context Map.empty \outerScope -> do
                childScope <- foldM (\scope _ -> Driver.scopeBind scope TySet) outerScope [1 .. depth]
                Driver.scopeReconstructFunctionEquality outerScope childScope target
                    (Proof.builtProofStatement leaf) (replicate depth TySet) leaf
    (proof, wrappers, attempts) <- require result
    assertEqual "unselected suffixes contribute no abstraction" (fromIntegral depth) wrappers
    when (depth == 16) (assertEqual "a genuine final conversion retry occurs" 2 attempts)
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.singleton hypothesis) target (Proof.builtProofDerivation proof))
    assertEqual "exact outer endpoints" target (replayedScopedKernelTarget replayed)
    assertEqual "only selected pointwise evidence" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "no extensionality axiom" Set.empty (replayedScopedKernelFoundationUses replayed)

booleanDirections :: Assertion
booleanDirections = do
    foundation <- require Foundation.checkedFoundation
    let types = [TyProp, TyProp]
    left <- checked types (CBound 0)
    right <- checked types (CBound 1)
    forward <- checked types (CImp (CBound 0) (CBound 1))
    backward <- checked types (CImp (CBound 1) (CBound 0))
    target <- checked types (CEq TyProp (CBound 0) (CBound 1))
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [forward, backward])
    first <- require (Proof.indexedHypothesisProof context (hypothesisIx 0))
    second <- require (Proof.indexedHypothesisProof context (hypothesisIx 1))
    let build other = let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
                            (Driver.GroundAllowance 0 0 0 0 Driver.UniversalsDisabled) context Map.empty \scope ->
                                Driver.scopeReconstructBooleanEquality scope left right first other
                     in result
    proof <- require (build second)
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.fromList [forward, backward]) target (Proof.builtProofDerivation proof))
    assertEqual "exact Boolean equality" target (replayedScopedKernelTarget replayed)
    assertEqual "both directions are consumed" (Set.fromList [hypothesisIx 0, hypothesisIx 1])
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "only propositional extensionality is added" (Set.singleton Foundation.PropositionalExtensionality)
        (replayedScopedKernelFoundationUses replayed)
    assertBool "one direction cannot be used twice" (isLeft (build first))
