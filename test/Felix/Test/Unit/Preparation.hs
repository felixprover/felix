{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Preparation (unitTests) where

import Base hiding (Empty)
import Control.Monad (when)
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Data.Vector qualified as Vector
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (GlobalTyping, emptyGlobalTyping)
import Felix.Test.Support.GlobalTyping
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Kernel
import Felix.Checking.Preparation qualified as Preparation
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Structural preparation"
    [ testCase "replays exact nested projections" exactProjection
    , testCase "retains solved components at every exhaustion boundary" partialExhaustion
    , testCase "continues one account across residual roots" sharedAccount
    , testCase "assembles more than sixteen supplied components" manyComponents
    , testCase "refines registered component boundaries under one account" structureRequirements
    , testCase "retains proved predicate components in residual scopes" retainedPredicateEvidence
    , testCase "applies only the supplied selected theorem" selectedEvidence
    , testCase "countedly specializes the owned predicate equality" predicateEquality
    , testCase "normalizes ordered compiler aliases on both sides with replay" aliasEvidence
    , testCase "transports exact local evidence through supplied equalities" localTransport
    , testCase "does not promote hidden equalities or chain transport" transportBoundaries
    , testCase "leaves unproved conjunctions intact" noProgress
    , testCase "replays universal and implication introductions" scopedIntroductions
    , testCase "retains scoped residuals through exhaustion" scopedExhaustion
    , testCase "keeps an introduced assumption out of its sibling" siblingScope
    , testCase "applies interleaved local eliminations with one account" localClause
    , testCase "leaves missing and inconsistent clause evidence unresolved" missingClauseEvidence
    , testCase "matches templates without capturing target binders" templateScope
    , testCase "replays positive predicate chains and partial import use" predicateViews
    , testCase "confines predicate views to positive active facts" predicatePolarity
    ]

checked :: [CoreType] -> CanonicalTerm Void -> IO (ScopedCheckedCore Void)
checked types = expectRight . checkScopedCanonicalCore emptyGlobalTyping types

fixture :: IO (Kernel.ProofContext Void, ScopedCheckedCore Void)
fixture = do
    foundation <- expectRight Foundation.checkedFoundation
    hypothesis <- checked [TyProp, TyProp] (CAnd (CBound 0) (CAnd (CBound 0) (CBound 0)))
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping
        [TyProp, TyProp] [hypothesis])
    goal <- checked [TyProp, TyProp] (CAnd (CBound 0) (CBound 1))
    pure (context, goal)

exactProjection :: Assertion
exactProjection = do
    (context, _goal) <- fixture
    target <- checked [TyProp, TyProp] (CBound 0)
    let (result, session) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 100000) context target
    plan <- expectRight result
    assertEqual "exact projection is solved" Preparation.Solved
        (Preparation.preparationOutcome session plan)
    replayClosed context plan
    let used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
        (atBoundary, boundarySession) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession used) context target
    boundary <- expectRight atBoundary
    assertEqual "exact accounting has no hidden extra debit" Preparation.Solved
        (Preparation.preparationOutcome boundarySession boundary)

partialExhaustion :: Assertion
partialExhaustion = do
    (context, goal) <- fixture
    let (completeResult, completeSession) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 100000) context goal
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics completeSession)
    complete <- expectRight completeResult
    assertEqual "only the missing component remains" Preparation.Residual
        (Preparation.preparationOutcome completeSession complete)
    assertEqual "complete residual" [CBound 1] (scopedCoreTerm <$> holes complete)
    observedPartial <- for [0 .. used - 1] \work -> do
        let (result, session) = Preparation.prepareLocalEvidence
                (Preparation.preparationSession work) context goal
        plan <- expectRight result
        assertEqual "root is preserved" goal (Preparation.preparationGoal plan)
        assertEqual "short budget is explicit" Preparation.Exhausted
            (Preparation.preparationOutcome session plan)
        assertEqual "failed attempts retain their debit" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics session))
        replayClosed context plan
        case Preparation.preparationView plan of
            Preparation.PreparationConjunction _ left right -> do
                assertEqual "a solved left child is never reopened" [] (holes left)
                assertEqual "the remaining right hole stays scoped" [CBound 1]
                    (scopedCoreTerm <$> holes right)
                pure True
            _ -> pure False
    assertBool "the sweep reached exhaustion after real partial progress" (or observedPartial)

sharedAccount :: Assertion
sharedAccount = do
    (context, goal) <- fixture
    let (first, spent) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 1) context goal
    _ <- expectRight first
    let (second, final) = Preparation.prepareLocalEvidence spent context goal
    plan <- expectRight second
    assertEqual "the account is not replenished" spent final
    assertEqual "the next root stays an ATP hole" [goal] (holes plan)

manyComponents :: Assertion
manyComponents = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 17 TyProp
        terms = CBound <$> [0..16]
    hypotheses <- traverse (checked types) terms
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    goal <- checked types (foldr1 CAnd terms)
    let (result, session) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 100000) context goal
    plan <- expectRight result
    assertEqual "seventeen components form one internal proof" Preparation.Solved
        (Preparation.preparationOutcome session plan)
    assertEqual "no external holes" [] (holes plan)
    replayClosed context plan

structureRequirements :: Assertion
structureRequirements = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 19 TyProp
        supplied = CBound <$> [0 .. 16]
        missing = CAnd (CBound 17) (CBound 18)
    hypotheses <- traverse (checked types) supplied
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    goal <- checked types (foldl1 CAnd (supplied <> [missing]))
    let run work = Preparation.prepareStructureRequirements 18 (const Nothing)
            (Preparation.preparationSession work) context goal
        (completeResult, completeSession) = run 100000
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics completeSession)
    (complete, _) <- expectRight completeResult
    assertEqual "the conjunction inside the final requirement stays intact"
        [missing] (scopedCoreTerm <$> holes complete)
    replayClosed context complete
    let (boundaryResult, boundarySession) = run used
    (boundary, _) <- expectRight boundaryResult
    assertEqual "exact budget leaves just the missing requirement" Preparation.Residual
        (Preparation.preparationOutcome boundarySession boundary)
    -- Sample across the large spine, including the exact last debit. Every
    -- retained proof is independently replayed in its original local scope.
    partial <- for (List.nub ([0, used - 1] <> [0, max 1 (used `div` 40) .. used - 1])) \work -> do
        let (result, session) = run work
        (plan, _) <- expectRight result
        assertEqual "exhaustion is explicit" Preparation.Exhausted
            (Preparation.preparationOutcome session plan)
        assertEqual "splitting never replenishes the account" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics session))
        assertEqual "the retained tree proves the original body" goal (Preparation.preparationGoal plan)
        replayClosed context plan
        pure (case Preparation.preparationView plan of
            Preparation.PreparationConjunction{} -> True
            _ -> False)
    assertBool "partial component splits survive exhaustion" (or partial)
    emptyContext <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types [])
    pair <- checked types (CAnd (CBound 0) missing)
    let (unsolved, _) = Preparation.prepareStructureRequirements 2 (const Nothing)
            (Preparation.preparationSession 100000) emptyContext pair
    (unsolvedPlan, _) <- expectRight unsolved
    assertEqual "registered boundaries remain even without a solved child"
        [CBound 0, missing] (scopedCoreTerm <$> holes unsolvedPlan)
    atom <- checked types (CBound 0)
    let (invalid, _) = Preparation.prepareStructureRequirements 2 (const Nothing)
            (Preparation.preparationSession 100000) emptyContext atom
    case invalid of
        Left Kernel.ProofStructuralCompositionMismatch{} -> pure ()
        _ -> assertFailure "a broken registered spine was silently accepted"

retainedPredicateEvidence :: Assertion
retainedPredicateEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let globals = globalTypingFixture (replicate 3 (TyArrow TySet TyProp))
        typing = fixtureGlobalTyping globals
        check types = expectRight . checkScopedCanonicalCore typing types
        eq = CEq TySet
        member term = CApp (CApp (CIntrinsic Member) term) (CIntrinsic Empty)
        predicate object = CApp (CGlobal object)
    (p, q, r) <- case fixtureObjectIds globals of
        [p, q, r] -> pure (p, q, r)
        _ -> fail "missing predicate fixtures"
    definitions <- for
        [(p, CAnd (predicate q (CBound 0)) (eq (CBound 0) (CBound 0))),
         (q, member (CBound 0)), (r, eq (CBound 0) (CIntrinsic Empty))] \(object, body) -> do
            equation <- check [] (CForall TySet (CEq TyProp (predicate object (CBound 0)) body))
            definition <- maybe (fail "open definition") pure (closeScopedCore equation)
            pure (object, definition)
    let catalogue = Map.fromList definitions
        missing = CForall TySet (eq (CBound 0) (CBound 0))
    -- The later original source must be found after two new hypotheses have
    -- been prepended; the duplicate first source must not add another view.
    hypotheses <- traverse (check [TySet, TySet])
        [predicate p (CBound 0), predicate r (CBound 1), predicate p (CBound 0)]
    context <- expectRight (Kernel.scopedProofContext foundation typing [TySet, TySet] hypotheses)
    target <- check [TySet, TySet]
        (CAnd (CAnd (member (CBound 0)) (eq (CBound 1) (CIntrinsic Empty))) missing)
    let run work = Preparation.prepareStructureRequirements 3 (`Map.lookup` catalogue)
            (Preparation.preparationSession work) context target
        replay (plan, objects) = do
            imports <- traverse (\(_, object) -> expectRight
                (derivationImportJudgement (catalogue Map.! object))) (List.sortOn fst objects)
            replayUsing typing (Vector.fromList imports) context plan
        (result, session) = run 100000
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
    complete@(plan, objects) <- expectRight result
    assertEqual "only the missing mathematical requirement remains" [missing]
        (scopedCoreTerm <$> holes plan)
    assertEqual "all three canonical equations remain associated" (Set.fromList [p, q, r])
        (Set.fromList (snd <$> objects))
    assertEqual "each distinct positive body is introduced once" 3 (evidenceCount plan)
    replay complete
    let (boundary, _) = run used
    expectRight boundary >>= replay
    partial <- for (List.nub ([0, used - 1] <> [0, max 1 (used `div` 40) .. used - 1])) \work -> do
        let (shortResult, remaining) = run work
        short@(shortPlan, _) <- expectRight shortResult
        assertEqual "partial evidence keeps the original goal" target (Preparation.preparationGoal shortPlan)
        assertEqual "evidence exhaustion remains explicit" Preparation.Exhausted
            (Preparation.preparationOutcome remaining shortPlan)
        assertEqual "evidence work never resets" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics remaining))
        replay short
        pure (evidenceCount shortPlan > 0)
    assertBool "completed evidence survives an exhausted continuation" (or partial)
  where
    evidenceCount plan = case Preparation.preparationView plan of
        Preparation.PreparationEvidence _ _ _ child -> 1 + evidenceCount child
        Preparation.PreparationConjunction _ left right -> evidenceCount left + evidenceCount right
        Preparation.PreparationUniversal _ _ _ child -> evidenceCount child
        Preparation.PreparationImplication _ _ _ child -> evidenceCount child
        _ -> 0 :: Int

selectedEvidence :: Assertion
selectedEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    statement <- checked [] (CForall TySet (CForall TySet
        (CImp (CEq TySet (CBound 1) (CBound 0))
            (CAnd (CEq TySet (CBound 0) (CBound 1)) CTruth))))
    theorem <- maybe (fail "selected theorem is open") pure (closeScopedCore statement)
    premise <- checked [TySet, TySet] (CEq TySet (CBound 1) (CBound 0))
    goal <- checked [TySet, TySet] (CEq TySet (CBound 0) (CBound 1))
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [TySet, TySet] [premise])
    let run work = Preparation.prepareSelectedImport (Preparation.preparationSession work) context goal theorem
        (result, session) = run 100000
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
    proof <- expectRight result >>= maybe (fail "selected theorem was not applied") pure
    imported <- expectRight (derivationImportJudgement theorem)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping (Vector.singleton imported) (Vector.singleton premise)
        goal (Kernel.builtProofDerivation proof))
    assertEqual "the actual selected theorem is used" (Set.singleton (importIx 0))
        (replayedScopedKernelImportUses replayed)
    assertEqual "the implication premise is actual local evidence" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)
    let (boundary, _) = run used
    expectRight boundary >>= maybe (fail "exact selected-clause budget exhausted") (const (pure ()))
    for_ [0, used - 1] \work -> do
        let (short, remaining) = run work
        case short of
            Right Nothing -> pure ()
            _ -> assertFailure "a partial selected-clause proof escaped"
        assertBool "the same account reports exhaustion"
            (Preparation.preparationExhausted (Preparation.preparationStatistics remaining))
    emptyContext <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [TySet, TySet] [])
    case fst (Preparation.prepareSelectedImport (Preparation.preparationSession 100000) emptyContext goal theorem) of
        Right Nothing -> pure ()
        _ -> assertFailure "a selected theorem invented its missing antecedent"

predicateEquality :: Assertion
predicateEquality = do
    foundation <- expectRight Foundation.checkedFoundation
    let globals = globalTypingFixture [TyArrow TySet TyProp]
        typing = fixtureGlobalTyping globals
        check types = expectRight . checkScopedCanonicalCore typing types
    p <- case fixtureObjectIds globals of
        [object] -> pure object
        _ -> fail "missing predicate fixture object"
    equation <- check [] (CForall TySet
        (CEq TyProp (CApp (CGlobal p) (CBound 0)) (CEq TySet (CBound 0) (CBound 0))))
    definition <- maybe (fail "definition is not closed") pure (closeScopedCore equation)
    imported <- expectRight (derivationImportJudgement definition)
    context <- expectRight (Kernel.scopedProofContext foundation typing [TySet] [])
    target <- check [TySet] (CApp (CGlobal p) (CBound 0))
    let run work = Preparation.preparePredicateEquality
            (Preparation.preparationSession work) context target definition
        (result, session) = run 100000
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
        replay (proof, body) = do
            assertEqual "the opening has the exact application and body"
                (Just (TyProp, target, body)) (splitScopedEquality (Kernel.builtProofStatement proof))
            replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
                typing (Vector.singleton imported) Vector.empty
                (Kernel.builtProofStatement proof) (Kernel.builtProofDerivation proof))
            assertEqual "the opening consumes exactly its owned equation"
                (Set.singleton (importIx 0)) (replayedScopedKernelImportUses replayed)
    opening <- expectRight result >>= maybe (fail "predicate opening exhausted") pure
    replay opening
    let (boundaryResult, _) = run used
    expectRight boundaryResult >>= maybe (fail "exact opening budget exhausted") replay
    for_ [0 .. used - 1] \work -> do
        let (short, remaining) = run work
        case short of
            Right Nothing -> pure ()
            _ -> assertFailure "an unfinished equality was published"
        assertEqual "opening retains every debit" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics remaining))
        let (next, final) = Preparation.preparePredicateEquality remaining context target definition
        assertEqual "the next opening cannot reset an exhausted account" remaining final
        case next of
            Right Nothing -> pure ()
            _ -> assertFailure "a second opening replenished the budget"

aliasEvidence :: Assertion
aliasEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = replicate 3 TySet
        fact index = CForall TySet (CApp (CApp (CIntrinsic Member) (CBound 0)) (CBound (index + 1)))
    first <- checked types (CEq TySet (CBound 0) (CBound 1))
    second <- checked types (CEq TySet (CBound 1) (CBound 2))
    for_ [(0, 2), (2, 0), (0, 1)] \(sourceIndex, targetIndex) -> do
        source <- checked types (fact sourceIndex)
        target <- checked types (fact targetIndex)
        context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types [first, second, source])
        let run work = Preparation.prepareAliasEvidence [0, 1] (const Nothing)
                (Preparation.preparationSession work) context target
            (result, session) = run 1000000
            used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
        (plan, imports) <- expectRight result
        assertEqual "alias transport introduces no imported theorem" [] imports
        assertEqual "the ordered aliases solve the original proposition" [] (holes plan)
        assertEqual "the original scoped target is retained" target (Preparation.preparationGoal plan)
        assertEqual "a complete transported proof is solved" Preparation.Solved (Preparation.preparationOutcome session plan)
        replayClosed context plan
        when (sourceIndex == 0 && targetIndex == 2) do
            let (unselected, _) = Preparation.prepareAliasEvidence [] (const Nothing)
                    (Preparation.preparationSession 1000000) context target
            (ordinary, _) <- expectRight unselected
            assertBool "ordinary equalities are not silently promoted to an alias chain"
                (not (null (holes ordinary)))
        for_ [0, 1, used `div` 4, used `div` 2, used - 1, used] \work -> do
            let (bounded, remaining) = run work
            (partial, _) <- expectRight bounded
            assertEqual "exhaustion retains the exact original target" target (Preparation.preparationGoal partial)
            assertBool "normalization and reconstruction share the configured allowance"
                (Preparation.preparationUsedWork (Preparation.preparationStatistics remaining) <= work)
            replayClosed context partial
    unsupplied <- checked types (fact 0)
    equationsOnly <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types [first, second])
    let (unhelpful, spent) = Preparation.prepareAliasEvidence [0, 1] (const Nothing)
            (Preparation.preparationSession 1000000) equationsOnly unsupplied
    (unchanged, _) <- expectRight unhelpful
    assertEqual "unsolved mathematics keeps its original ATP abstraction" [unsupplied] (holes unchanged)
    assertBool "declining an unhelpful alias view retains its actual work debit"
        (Preparation.preparationUsedWork (Preparation.preparationStatistics spent) > 0)
    source <- checked types (fact 0)
    missing <- checked types (CAnd (fact 2) CFalsum)
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types [first, second, source])
    let (result, _) = Preparation.prepareAliasEvidence [0, 1] (const Nothing)
            (Preparation.preparationSession 1000000) context missing
    (partial, _) <- expectRight result
    falsehood <- checked types CFalsum
    assertEqual "normalized facts do not invent a missing sibling" [falsehood] (holes partial)
    replayClosed context partial

localTransport :: Assertion
localTransport = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TySet, TySet, TySet]
        member element setTerm = CApp (CApp (CIntrinsic Member) element) setTerm
        a = CBound 0
        b = CBound 1
        predicates =
            [ (member a (CBound 2), member b (CBound 2))
            , (member a a, member b b)
            , (CForall TySet (member (CBound 0) (CBound 1)),
                CForall TySet (member (CBound 0) (CBound 2)))
            ]
    for_ [CEq TySet a b, CEq TySet b a] \equation ->
        for_ predicates \(supplied, requested) -> do
            premise <- checked types (CAnd equation supplied)
            target <- checked types requested
            context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types [premise])
            let run work = Preparation.prepareLocalEvidence (Preparation.preparationSession work) context target
                (result, session) = run 100000
                used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
            complete <- expectRight result
            assertEqual "transport closes without ATP" Preparation.Solved
                (Preparation.preparationOutcome session complete)
            replayClosed context complete
            let (boundaryResult, boundarySession) = run used
            boundary <- expectRight boundaryResult
            assertEqual "conversion and construction fit the exact common debit" Preparation.Solved
                (Preparation.preparationOutcome boundarySession boundary)
            replayClosed context boundary
            for_ [0, used `div` 3, used `div` 2, used - 1] \work -> do
                let (short, remaining) = run work
                plan <- expectRight short
                assertEqual "incomplete transport remains an explicit exhaustion" Preparation.Exhausted
                    (Preparation.preparationOutcome remaining plan)
                assertEqual "failed transport retains structural and conversion debit" work
                    (Preparation.preparationUsedWork (Preparation.preparationStatistics remaining))
                replayClosed context plan

transportBoundaries :: Assertion
transportBoundaries = do
    foundation <- expectRight Foundation.checkedFoundation
    let types = [TySet, TySet, TySet]
        member a = CApp (CApp (CIntrinsic Member) a) (CIntrinsic Empty)
        equation = CEq TySet (CBound 0) (CBound 1)
    target <- checked types (member (CBound 1))
    for_ [CNot equation, COr equation equation, CImp equation equation] \hidden -> do
        hypotheses <- traverse (checked types) [hidden, member (CBound 0)]
        context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        let (result, session) = Preparation.prepareLocalEvidence (Preparation.preparationSession 100000) context target
        plan <- expectRight result
        assertEqual "a hidden equality grants no transport" Preparation.NoApplicableView
            (Preparation.preparationOutcome session plan)
    hypotheses <- traverse (checked types)
        [equation, CEq TySet (CBound 1) (CBound 2), member (CBound 0)]
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types hypotheses)
    chained <- checked types (member (CBound 2))
    let (result, session) = Preparation.prepareLocalEvidence (Preparation.preparationSession 100000) context chained
    plan <- expectRight result
    assertEqual "failed orientations do not seed recursive transport" Preparation.NoApplicableView
        (Preparation.preparationOutcome session plan)

noProgress :: Assertion
noProgress = do
    foundation <- expectRight Foundation.checkedFoundation
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [TyProp] [])
    goal <- checked [TyProp] (CAnd (CBound 0) (CBound 0))
    let (result, session) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 100000) context goal
    plan <- expectRight result
    assertEqual "no gratuitous ATP splitting" Preparation.NoApplicableView
        (Preparation.preparationOutcome session plan)
    assertEqual "the original obligation remains" [goal] (holes plan)

holes :: Preparation.PreparationPlan global -> [ScopedCheckedCore global]
holes plan = case Preparation.preparationView plan of
    Preparation.PreparationHole goal -> [goal]
    Preparation.PreparationProof{} -> []
    Preparation.PreparationConjunction _ left right -> holes left <> holes right
    Preparation.PreparationUniversal _ _ _ child -> holes child
    Preparation.PreparationImplication _ _ _ child -> holes child
    Preparation.PreparationEvidence _ _ _ child -> holes child
    Preparation.PreparationRewrite _ _ child -> holes child

replayClosed :: Kernel.ProofContext Void -> Preparation.PreparationPlan Void -> Assertion
replayClosed = replayUsing emptyGlobalTyping Vector.empty

replayUsing :: Ord global => GlobalTyping global -> Vector.Vector (DerivationImportJudgement global)
    -> Kernel.ProofContext global -> Preparation.PreparationPlan global -> Assertion
replayUsing typing imports context plan = case Preparation.preparationView plan of
    Preparation.PreparationHole{} -> pure ()
    Preparation.PreparationConjunction _ left right -> do
        replayUsing typing imports context left
        replayUsing typing imports context right
    Preparation.PreparationUniversal _ _ nested child -> replayUsing typing imports nested child
    Preparation.PreparationImplication _ _ nested child -> replayUsing typing imports nested child
    Preparation.PreparationEvidence proof used nested child -> do
        replayProof proof used
        assertBool "a view extends only its continuation with a proved premise"
            (Kernel.builtProofStatement proof : Kernel.proofContextHypotheses context
                == Kernel.proofContextHypotheses nested)
        replayUsing typing imports nested child
    Preparation.PreparationRewrite goal equation child -> do
        replayProof equation Set.empty
        assertBool "a rewrite retains its exact original and child goals"
            (splitScopedEquality (Kernel.builtProofStatement equation)
                == Just (TyProp, goal, Preparation.preparationGoal child))
        replayUsing typing imports context child
    Preparation.PreparationProof proof used -> replayProof proof used
  where
    replayProof proof used = do
        foundation <- expectRight Foundation.checkedFoundation
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            typing imports (Vector.fromList (Kernel.proofContextHypotheses context))
            (Kernel.builtProofStatement proof) (Kernel.builtProofDerivation proof))
        assertEqual "prepared dependencies agree with independent replay" used
            (replayedScopedKernelImportUses replayed)

scopedIntroductions :: Assertion
scopedIntroductions = do
    foundation <- expectRight Foundation.checkedFoundation
    for_ [TySet, TyArrow TySet TySet] \binderType -> do
        context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [] [])
        let equality = CEq binderType (CBound 0) (CBound 0)
        goal <- checked [] (CForall binderType (CImp equality equality))
        let (result, session) = Preparation.prepareLocalEvidence
                (Preparation.preparationSession 100000) context goal
        plan <- expectRight result
        assertEqual "logical introductions close without external hypotheses" Preparation.Solved
            (Preparation.preparationOutcome session plan)
        replayClosed context plan
        let used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
            (shortResult, shortSession) = Preparation.prepareLocalEvidence
                (Preparation.preparationSession (used - 1)) context goal
        short <- expectRight shortResult
        assertEqual "closing exhaustion retains its already solved body" [] (holes short)
        assertEqual "closing exhaustion is still reported" Preparation.Exhausted
            (Preparation.preparationOutcome shortSession short)
        replayClosed context short

scopedExhaustion :: Assertion
scopedExhaustion = do
    foundation <- expectRight Foundation.checkedFoundation
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [] [])
    let premise = CEq TySet (CBound 0) (CIntrinsic Empty)
        residual = CEq TySet (CIntrinsic Empty) (CBound 0)
    goal <- checked [] (CForall TySet (CImp premise (CAnd premise residual)))
    let run work = Preparation.prepareLocalEvidence (Preparation.preparationSession work) context goal
        (completeResult, completeSession) = run 100000
        used = Preparation.preparationUsedWork (Preparation.preparationStatistics completeSession)
    complete <- expectRight completeResult
    assertEqual "the residual stays below its binder" [[TySet]] (scopedCoreContext <$> holes complete)
    assertEqual "only the missing equality remains" [residual] (scopedCoreTerm <$> holes complete)
    observedScoped <- for [0 .. used - 1] \work -> do
        let (result, session) = run work
        plan <- expectRight result
        assertEqual "short scoped allowance is explicit" Preparation.Exhausted
            (Preparation.preparationOutcome session plan)
        assertEqual "scoped work is not replenished" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics session))
        replayClosed context plan
        case Preparation.preparationView plan of
            Preparation.PreparationUniversal _ TySet _ child -> case Preparation.preparationView child of
                Preparation.PreparationImplication _ assumed nested _ -> do
                    assertEqual "the retained hypothesis is the owned antecedent" premise (scopedCoreTerm assumed)
                    assertEqual "the residual has exactly that local hypothesis" [assumed]
                        (Kernel.proofContextHypotheses nested)
                    assertEqual "solved work survives in the opened scope" [residual]
                        (scopedCoreTerm <$> holes plan)
                    pure True
                _ -> assertFailure "a partial universal lost its implication scope" >> pure False
            _ -> pure False
    assertBool "exhaustion was reached with a real scoped partial plan" (or observedScoped)

siblingScope :: Assertion
siblingScope = do
    foundation <- expectRight Foundation.checkedFoundation
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [TyProp] [])
    goal <- checked [TyProp] (CAnd (CImp (CBound 0) (CBound 0)) (CBound 0))
    let (result, session) = Preparation.prepareLocalEvidence
            (Preparation.preparationSession 100000) context goal
    plan <- expectRight result
    assertEqual "the sibling remains unproved" Preparation.Residual
        (Preparation.preparationOutcome session plan)
    assertEqual "the implication's assumption does not escape" [CBound 0]
        (scopedCoreTerm <$> holes plan)
    replayClosed context plan

localClause :: Assertion
localClause = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptySet = CIntrinsic Empty
        singleton = CApp (CApp (CIntrinsic PairSet) emptySet) emptySet
        eq = CEq TySet
        clause = CAnd (CImp CFalsum (eq emptySet singleton))
            (CForall TySet (CImp (CAnd (eq (CBound 0) emptySet) CTruth)
                (CAnd (eq (CBound 0) (CBound 0)) (CForall TySet (eq (CBound 1) (CBound 0))))))
    hypotheses <- traverse (checked []) [clause, eq emptySet emptySet]
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [] hypotheses)
    target <- checked [] (eq emptySet singleton)
    let run work = Preparation.prepareLocalEvidence (Preparation.preparationSession work) context target
        (result, session) = run 100000
    plan <- expectRight result
    assertEqual "projection, binder, antecedent, projection, binder replay in source order"
        Preparation.Solved (Preparation.preparationOutcome session plan)
    replayClosed context plan
    let used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
    for_ [0 .. used - 1] \work -> do
        let (shortResult, shortSession) = run work
        short <- expectRight shortResult
        assertEqual "failed clause attempts keep their debit" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics shortSession))
        assertEqual "short clause work is explicit" Preparation.Exhausted
            (Preparation.preparationOutcome shortSession short)
        assertEqual "no incomplete clause is published" [target] (holes short)
    let (boundaryResult, boundarySession) = run used
    boundary <- expectRight boundaryResult
    assertEqual "exact clause debit is sufficient" Preparation.Solved
        (Preparation.preparationOutcome boundarySession boundary)
    replayClosed context boundary

missingClauseEvidence :: Assertion
missingClauseEvidence = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptySet = CIntrinsic Empty
        singleton = CApp (CApp (CIntrinsic PairSet) emptySet) emptySet
        eq = CEq TySet
        p = CBound 0
        q = CBound 1
        cases =
            [ ("inconsistent repeated parameter", [],
                [CForall TySet (eq (CBound 0) (CBound 0))], eq emptySet singleton)
            , ("missing antecedent", [],
                [CForall TySet (CImp (eq (CBound 0) singleton) (eq (CBound 0) (CBound 0)))], eq emptySet emptySet)
            , ("undetermined parameter", [],
                [CForall TySet (eq emptySet emptySet)], eq emptySet emptySet)
            , ("incompatible parameter type", [TyArrow TySet TySet],
                [CForall TySet (eq (CBound 0) (CBound 0))],
                CEq (TyArrow TySet TySet) (CBound 0) (CBound 0))
            , ("rules are not recursively chained", [TyProp, TyProp], [CImp p q, CImp q p], p)
            ]
    for_ cases \(label, types, terms, goal) -> do
        hypotheses <- traverse (checked types) terms
        context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping types hypotheses)
        target <- checked types goal
        let (result, session) = Preparation.prepareLocalEvidence
                (Preparation.preparationSession 100000) context target
        plan <- expectRight result
        assertEqual label Preparation.NoApplicableView (Preparation.preparationOutcome session plan)
        assertEqual "unproved mathematics stays a residual" [target] (holes plan)

templateScope :: Assertion
templateScope = do
    foundation <- expectRight Foundation.checkedFoundation
    let eq = CEq TySet
    source <- checked [TySet] (CForall TySet (CExists TySet (eq (CBound 1) (CBound 0))))
    context <- expectRight (Kernel.scopedProofContext foundation emptyGlobalTyping [TySet] [source])
    positive <- checked [TySet] (CExists TySet (eq (CBound 1) (CBound 0)))
    capture <- checked [TySet] (CExists TySet (eq (CBound 0) (CBound 0)))
    let run = Preparation.prepareLocalEvidence (Preparation.preparationSession 100000) context
        (result, session) = run positive
    plan <- expectRight result
    assertEqual "the argument is rebased into the ambient scope" Preparation.Solved
        (Preparation.preparationOutcome session plan)
    replayClosed context plan
    let (rejectedResult, rejectedSession) = run capture
    rejected <- expectRight rejectedResult
    assertEqual "a target's inner binder cannot instantiate an outer slot" Preparation.NoApplicableView
        (Preparation.preparationOutcome rejectedSession rejected)
    assertEqual "no witness is guessed for the residual existential" [capture] (holes rejected)

predicateViews :: Assertion
predicateViews = do
    foundation <- expectRight Foundation.checkedFoundation
    let globals = globalTypingFixture [TyArrow TySet TyProp, TyArrow TySet TyProp]
        typing = fixtureGlobalTyping globals
        check types = expectRight . checkScopedCanonicalCore typing types
        eq = CEq TySet
    (p, q) <- case fixtureObjectIds globals of
        [p, q] -> pure (p, q)
        _ -> fail "missing predicate fixture objects"
    let predicate object = CApp (CGlobal object)
        law = CForall TySet (CImp (eq (CBound 0) (CBound 1)) (eq (CBound 1) (CBound 0)))
    definitions <- traverse (\(object, body) -> do
        equation <- check [] (CForall TySet (CEq TyProp (predicate object (CBound 0)) body))
        frozen <- maybe (fail "definition is not closed") pure (closeScopedCore equation)
        pure (object, frozen))
        [ (p, CAnd (predicate q (CBound 0)) (eq (CBound 0) (CBound 0)))
        , (q, law)
        ]
    hypothesis <- check [TySet] (predicate p (CBound 0))
    context <- expectRight (Kernel.scopedProofContext foundation typing [TySet] [hypothesis])
    target <- check [TySet] (CAnd (eq (CBound 0) (CBound 0)) law)
    let catalogue = Map.fromList definitions
        run work = Preparation.prepareLocalEvidenceWithDefinitions (`Map.lookup` catalogue)
            (Preparation.preparationSession work) context target
        replay (plan, objects) = do
            imports <- traverse (\(_, object) ->
                expectRight (derivationImportJudgement (catalogue Map.! object))) (List.sortOn fst objects)
            replayUsing typing (Vector.fromList imports) context plan
        (result, session) = run 100000
    complete@(plan, imports) <- expectRight result
    assertEqual "the chain supplies a quantified requirement" Preparation.Solved
        (Preparation.preparationOutcome session plan)
    assertEqual "both canonical equations are retained" (Set.fromList [p, q])
        (Set.fromList (snd <$> imports))
    replay complete
    let used = Preparation.preparationUsedWork (Preparation.preparationStatistics session)
    partial <- for [0 .. used - 1] \work -> do
        let (shortResult, shortSession) = run work
        short@(shortPlan, _) <- expectRight shortResult
        assertEqual "view work and failed attempts share the allowance" work
            (Preparation.preparationUsedWork (Preparation.preparationStatistics shortSession))
        assertEqual "view exhaustion is explicit" Preparation.Exhausted
            (Preparation.preparationOutcome shortSession shortPlan)
        replay short
        pure (not (null (solvedUses shortPlan)))
    assertBool "completed view proofs survive exhaustion" (or partial)
    let (boundaryResult, boundarySession) = run used
    boundary@(boundaryPlan, _) <- expectRight boundaryResult
    assertEqual "exact view debit suffices" Preparation.Solved
        (Preparation.preparationOutcome boundarySession boundaryPlan)
    replay boundary
    -- The pure service treats a contradictory association as integrity failure.
    let wrong = Map.lookup q catalogue
        (invalid, _) = Preparation.prepareLocalEvidenceWithDefinitions (const wrong)
            (Preparation.preparationSession 100000) context target
    case invalid of
        Left Kernel.ProofStructuralCompositionMismatch{} -> pure ()
        _ -> assertFailure "a wrong predicate equation was treated as optional absence"
  where
    solvedUses plan = case Preparation.preparationView plan of
        Preparation.PreparationHole{} -> []
        Preparation.PreparationProof _ used -> [used]
        Preparation.PreparationConjunction _ left right -> solvedUses left <> solvedUses right
        Preparation.PreparationUniversal _ _ _ child -> solvedUses child
        Preparation.PreparationImplication _ _ _ child -> solvedUses child
        Preparation.PreparationEvidence _ _ _ child -> solvedUses child
        Preparation.PreparationRewrite _ _ child -> solvedUses child

predicatePolarity :: Assertion
predicatePolarity = do
    foundation <- expectRight Foundation.checkedFoundation
    let globals = globalTypingFixture [TyArrow TySet TyProp]
        typing = fixtureGlobalTyping globals
        check types = expectRight . checkScopedCanonicalCore typing types
        eq = CEq TySet
    p <- case fixtureObjectIds globals of
        [p] -> pure p
        _ -> fail "missing predicate fixture object"
    let predicate term = CApp (CGlobal p) term
        atom = predicate (CBound 0)
    equation <- check [] (CForall TySet (CEq TyProp atom (eq (CBound 0) (CBound 0))))
    definition <- maybe (fail "definition is not closed") pure (closeScopedCore equation)
    target <- check [TySet] (eq (CBound 0) (CBound 0))
    for_ [CNot atom, COr atom atom, CImp atom atom, CForall TySet (predicate (CBound 0))] \term -> do
        hypothesis <- check [TySet] term
        context <- expectRight (Kernel.scopedProofContext foundation typing [TySet] [hypothesis])
        let (result, session) = Preparation.prepareLocalEvidenceWithDefinitions
                (\object -> definition <$ guard (object == p))
                (Preparation.preparationSession 100000) context target
        (plan, imports) <- expectRight result
        assertEqual "non-active predicate evidence is not promoted" Preparation.NoApplicableView
            (Preparation.preparationOutcome session plan)
        assertEqual "no definition is even entered for a hidden predicate" [] imports
    -- A repeated positive head terminates instead of getting fresh view fuel.
    self <- check [] (CForall TySet (CEq TyProp atom atom))
    selfDefinition <- maybe (fail "self equation is not closed") pure (closeScopedCore self)
    hypothesis <- check [TySet] atom
    context <- expectRight (Kernel.scopedProofContext foundation typing [TySet] [hypothesis])
    let (cyclic, session) = Preparation.prepareLocalEvidenceWithDefinitions (const (Just selfDefinition))
            (Preparation.preparationSession 100000) context target
    (plan, _) <- expectRight cyclic
    assertEqual "cyclic views do not synthesize a result or exhaust the account" Preparation.NoApplicableView
        (Preparation.preparationOutcome session plan)

expectRight :: Show error => Either error value -> IO value
expectRight = either (\failure -> assertFailure (show failure) >> fail "unreachable") pure
