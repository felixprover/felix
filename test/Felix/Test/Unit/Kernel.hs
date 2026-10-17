{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}

module Felix.Test.Unit.Kernel (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (GlobalTyping, emptyGlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Kernel.Semantics qualified as Semantics
import Felix.Checking.Kernel.SetLfp qualified as SetLfp
import Felix.Checking.Inductive.Construction qualified as Inductive
import Felix.Report.Location (pattern Nowhere)
import Felix.Test.Support.GlobalTyping
import Felix.Test.Support.KernelSemanticsVectors (ruleVectors)

import Control.Monad (foldM, when)
import Data.Either (isLeft)
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit


testGlobalFixture :: GlobalTypingFixture
testGlobalFixture = globalTypingFixture [TySet]

testGlobalType :: GlobalTyping ObjectId
testGlobalType = fixtureGlobalTyping testGlobalFixture

unitTests :: TestTree
unitTests =
    testGroup "Kernel replay"
        [ testCase "preserves logical rule outcomes and every work boundary" ruleVectors
        , testCase
            "replays equality reflexivity through kernel semantics"
            replaysEqualityReflexivity
        , testCase
            "replays logical scopes and elimination"
            replaysLogicalScopes
        , testCase
            "replays quantifier and equality structure"
            replaysQuantifierAndEqualityStructure
        , testCase
            "builds replayable directional equality transport"
            buildsDirectionalEqualityTransport
        , testCase
            "remaps only external hypotheses below introductions"
            remapsOnlyExternalHypotheses
        , testCase "summarizes exact source uses through proof and term binders"
            summarizesSourceUses
        , testCase
            "replays native logical rules"
            replaysNativeLogicalRules
        , testCase
            "rejects invalid native logical branches"
            rejectsInvalidNativeLogicalBranches
        , testCase
            "records foundation and import leaves"
            recordsAuthorityLeaves
        , testCase
            "validates exactly the declared replay environment"
            validatesDeclaredReplayEnvironment
        , testCase
            "checks and replays the exact set fixed-point rules"
            checksSetLfpRules
        , testCase
            "replays direct inductive facts"
            replaysDirectInductiveFacts
        , testCase
            "rejects altered set fixed-point applications"
            rejectsAlteredSetLfpApplications
        , testCase
            "rejects invalid scoped replay"
            rejectsInvalidScopedReplay
        , testCase
            "rejects a caller-supplied target mismatch"
            rejectsTargetMismatch
        , testCase
            "reassembles exact local conjunctions structurally"
            reassemblesLocalConjunctions
        , testCase
            "preserves conjunction fallback and typed exhaustion"
            characterizesConjunctionConversionFallback
        , testCase
            "propagates conjunction conversion input failures"
            characterizesConjunctionContextFailure
        , testCase
            "replays exact scoped locals and reports external uses"
            replaysScopedLocals
        , testCase "replays conversion source first under the current snapshot"
            replaysConversionUnderCurrentSnapshot
        , testCase "accounts and replays fresh proof conversions"
            accountsProofConversion
        , testCase "replays beta-eta conversions to their exact stored targets"
            replaysEtaConversion
        , testCase "constructs and independently replays pointwise abstraction prefixes"
            replaysPointwiseAbstraction
        , testCase "admits checked inputs under the exact proof owner before erasure"
            admitsCheckedProofInputs
        , testCase "composes checked conjunctions with bounded premise work"
            countsCheckedConjunctions
        , testCase
            "counts focused proof materializers at exact boundaries"
            countsFocusedMaterializers
        , testCase "measured replay preserves conclusions and retains rejected work"
            measuresReplayWork
        , testCase "counts and replays existential introduction through nested binders"
            countsExistentialIntroduction
        , testCase "preserves existential introduction mismatches under counted construction"
            rejectsCountedExistentialMismatches
        , testCase "counts and replays prepared existential elimination through ambient binders"
            countsExistentialElimination
        , testCase "rejects escaping existential results and preserves counted failures"
            rejectsCountedExistentialElimination
        ]

countsExistentialIntroduction :: Assertion
countsExistentialIntroduction = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptyTerm = CIntrinsic Empty
        functionType = TyArrow TySet TySet
        large = foldr (\_ term -> CApp (CApp (CIntrinsic OrderedPair) term) emptyTerm) emptyTerm [1 :: Int .. 32]
        cases =
            [ ([], TySet, CEq TySet (CBound 0) emptyTerm, emptyTerm)
            , ([TySet], TySet, CEq TySet (CBound 0) (CBound 1), CBound 0)
            , ([functionType], functionType, CEq functionType (CBound 0) (CBound 1), CBound 0)
            , ([TySet], TySet, CForall TySet (CEq TySet (CBound 1) (CBound 2)), CBound 0)
            , ([], TySet, CExists TySet (CEq TySet (CBound 0) (CBound 1)), emptyTerm)
            , ([], TySet, nestedNegation 64 (CEq TySet (CBound 0) (CBound 0)), large)
            ]
    forM_ cases \(types, binderType, bodyTerm, witnessTerm) -> do
        body <- checkedScoped (binderType : types) bodyTerm
        witness <- checkedScoped types witnessTerm
        premise <- checkedScoped types (instantiateCanonical witnessTerm bodyTerm)
        context <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping types [premise])
        premiseProof <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
        ordinary <- expectRight (KernelProof.existentialIntroductionProof context binderType body witness premiseProof)
        let build work = KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedExistentialIntroductionProof
                context binderType body witness premiseProof
        countedProofBoundary "existential introduction" (KernelProof.builtProofStatement ordinary) build
        proof <- expectCounted "existential introduction replay" (build 100000)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.singleton premise)
            (KernelProof.builtProofStatement ordinary) (KernelProof.builtProofDerivation proof))
        assertEqual "the existential retains exactly its body's authority"
            (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
        let (semantics, remaining) = Semantics.countedExistentialIntroduction
                emptyGlobalTyping 100000 body witness premise
            used = 100000 - remaining
        assertEqual "counted existential semantics agree with the original rule"
            (Right (KernelProof.builtProofStatement ordinary)) semantics
        assertEqual "exact semantic budget"
            (semantics, 0) (Semantics.countedExistentialIntroduction emptyGlobalTyping used body witness premise)
        assertEqual "one-short semantic budget"
            (Left CountedCoreStructuralWorkExhausted, 0)
            (Semantics.countedExistentialIntroduction emptyGlobalTyping (used - 1) body witness premise)

rejectsCountedExistentialMismatches :: Assertion
rejectsCountedExistentialMismatches = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptyTerm = CIntrinsic Empty
        cases =
            [ (([], CTruth), ([], emptyTerm), ([], CTruth))
            , (([TySet], CTruth), ([], CTruth), ([], CTruth))
            , (([TySet, TySet], CTruth), ([], emptyTerm), ([], CTruth))
            , (([TySet, TySet], CTruth), ([TySet], CBound 0), ([], CTruth))
            , (([TySet], CTruth), ([], emptyTerm), ([], emptyTerm))
            , (([TySet], CBound 0), ([], emptyTerm), ([], CTruth))
            , (([TySet], CEq TySet (CBound 0) emptyTerm), ([], emptyTerm), ([], CFalsum))
            ]
    forM_ cases \(bodyInput, witnessInput, premiseInput) -> do
        body <- uncurry checkedScoped bodyInput
        witness <- uncurry checkedScoped witnessInput
        premise <- uncurry checkedScoped premiseInput
        expected <- case Semantics.existentialIntroduction emptyGlobalTyping body witness premise of
            Left failure -> pure failure
            Right _ -> assertFailure "invalid existential fixture was accepted" >> fail "invalid fixture"
        let run work = Semantics.countedExistentialIntroduction emptyGlobalTyping work body witness premise
            (actual, remaining) = run 100000
            used = 100000 - remaining
        assertEqual "the original semantic failure is preserved"
            (Left (CountedCoreOperationFailed expected)) actual
        assertEqual "failed semantic work is charged at its exact boundary" (actual, 0) (run used)
        -- Core can reject an empty/nonempty context mismatch without traversal.
        -- Its exact zero boundary above has no smaller representable budget.
        when (used > 0) $
            assertEqual "resource exhaustion remains distinct from invalid premises"
                (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    body <- checkedScoped [TySet] CTruth
    witness <- checkedScoped [] emptyTerm
    proposition <- checkedScoped [] CTruth
    context <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping [] [proposition])
    differentContext <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping [TySet] [])
    premiseProof <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    forM_ [(context, TyProp), (differentContext, TySet)] \(owner, binderType) -> do
        let ordinary = KernelProof.existentialIntroductionProof owner binderType body witness premiseProof
            run work = KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedExistentialIntroductionProof
                owner binderType body witness premiseProof
            (actual, remaining, pool) = run 100000
            used = 100000 - remaining
        assertEqual "the original builder rejects a different binder or owner"
            (Left KernelProof.ProofExpectedUnaryBinder) (KernelProof.builtProofStatement <$> ordinary)
        assertEqual "the bounded builder preserves that rejection"
            (Left (CountedCoreOperationFailed KernelProof.ProofExpectedUnaryBinder))
            (KernelProof.builtProofStatement <$> actual)
        assertEqual "rejection uses no conversion work" (Conversion.conversionPool 0) pool
        let (short, structural, _) = run (used - 1)
        assertEqual "one-short owner checking is exhaustion"
            (Left CountedCoreStructuralWorkExhausted, 0) (KernelProof.builtProofStatement <$> short, structural)

countsExistentialElimination :: Assertion
countsExistentialElimination = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptyTerm = CIntrinsic Empty
        functionType = TyArrow TySet TySet
        application = CApp (CBound 1) (CBound 0)
        cases =
            [ ([], TySet, CTruth)
            , ([TySet], TySet, CEq TySet (CBound 0) emptyTerm)
            , ([functionType], functionType, CForall TySet (CEq TySet application application))
            , ([], TySet, CExists TySet (CEq TySet (CBound 0) emptyTerm))
            , ([TySet], TySet, nestedNegation 64 (CEq TySet (CBound 0) (CBound 0)))
            ]
    forM_ cases \(types, binderType, resultTerm) -> do
        let bodyTerm = CAnd (CEq binderType (CBound 0) (CBound 0)) (shiftCanonical 1 0 resultTerm)
        body <- checkedScoped (binderType : types) bodyTerm
        existential <- checkedScoped types (CExists binderType bodyTerm)
        result <- checkedScoped types resultTerm
        context <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping types [existential])
        source <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
        ordinary <- expectRight (KernelProof.existentialEliminationProof context binderType body source result
            (\underBinder _variable -> KernelProof.conjunctionRightProof underBinder))
        (withBinder, _variable) <- expectRight (KernelProof.extendProofContextBinder context binderType)
        withBody <- expectRight (KernelProof.extendProofContextHypothesis withBinder body)
        bodyProof <- expectRight (KernelProof.indexedHypothesisProof withBody (hypothesisIx 0))
        branch <- expectRight (KernelProof.conjunctionRightProof withBody bodyProof)
        let build work = KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedPreparedExistentialEliminationProof
                context binderType bodyTerm source result branch
        countedProofBoundary "prepared existential elimination" (KernelProof.builtProofStatement ordinary) build
        proof <- expectCounted "prepared existential replay" (build 100000)
        replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.singleton existential) result (KernelProof.builtProofDerivation proof))
        assertEqual "elimination discharges the body hypothesis and retains its existential source"
            (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
        let run work = Semantics.countedExistentialElimination emptyGlobalTyping work
                existential result (KernelProof.builtProofStatement branch)
            (semantics, remaining) = run 100000
            used = 100000 - remaining
        assertEqual "counted elimination agrees with the original semantics"
            (Right (KernelProof.builtProofStatement ordinary)) semantics
        assertEqual "exact semantic elimination budget" (semantics, 0) (run used)
        assertEqual "one-short semantic elimination budget"
            (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))

rejectsCountedExistentialElimination :: Assertion
rejectsCountedExistentialElimination = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptyTerm = CIntrinsic Empty
        existsTruth = CExists TySet CTruth
        ambientEquality = CEq TySet (CBound 0) emptyTerm
        cases =
            [ (([], CTruth), ([], CTruth), ([TySet], CTruth))
            , (([], existsTruth), ([TySet], CTruth), ([TySet], CTruth))
            , (([], existsTruth), ([], emptyTerm), ([TySet], CTruth))
            , (([], existsTruth), ([], CTruth), ([], CTruth))
            , (([], existsTruth), ([], CTruth), ([TyProp], CTruth))
            , (([], existsTruth), ([], CTruth), ([TySet], CBound 0))
            , (([], CExists TySet ambientEquality), ([], CEq TySet emptyTerm emptyTerm), ([TySet], ambientEquality))
            , (([TySet], existsTruth), ([TySet], ambientEquality), ([TySet, TySet], ambientEquality))
            ]
    forM_ cases \(sourceInput, resultInput, branchInput) -> do
        source <- uncurry checkedScoped sourceInput
        result <- uncurry checkedScoped resultInput
        branch <- uncurry checkedScoped branchInput
        expected <- case Semantics.existentialElimination emptyGlobalTyping source result branch of
            Left failure -> pure failure
            Right _ -> assertFailure "invalid elimination fixture was accepted" >> fail "invalid fixture"
        let run work = Semantics.countedExistentialElimination emptyGlobalTyping work source result branch
            (actual, remaining) = run 100000
            used = 100000 - remaining
        assertEqual "the original elimination failure is preserved"
            (Left (CountedCoreOperationFailed expected)) actual
        assertEqual "failed elimination work is charged" (actual, 0) (run used)
        when (used > 0) $
            assertEqual "one-short invalid elimination exhausts actual work"
                (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    body <- checkedScoped [TySet] ambientEquality
    existential <- checkedScoped [] (CExists TySet ambientEquality)
    result <- checkedScoped [] (CEq TySet emptyTerm emptyTerm)
    context <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping [] [existential])
    source <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    (withBinder, _variable) <- expectRight (KernelProof.extendProofContextBinder context TySet)
    withBody <- expectRight (KernelProof.extendProofContextHypothesis withBinder body)
    branch <- expectRight (KernelProof.indexedHypothesisProof withBody (hypothesisIx 0))
    forM_ [ambientEquality, CTruth] \expectedBody -> do
        let run work = KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedPreparedExistentialEliminationProof
                context TySet expectedBody source result branch
            (actual, remaining, pool) = run 100000
            used = 100000 - remaining
            expected = if expectedBody == ambientEquality then
                KernelProof.ProofSemanticsFailed Semantics.KernelExistentialResultMismatch
                else KernelProof.ProofStructuralCompositionMismatch
                    "existential elimination received a different binder body"
        assertEqual "prepared construction rejects an escaping result or different source"
            (Left (CountedCoreOperationFailed expected)) (KernelProof.builtProofStatement <$> actual)
        assertEqual "failed elimination uses no conversion" (Conversion.conversionPool 0) pool
        let (short, afterShort, _) = run (used - 1)
        assertEqual "one-short rejected construction remains exhaustion"
            (Left CountedCoreStructuralWorkExhausted, 0) (KernelProof.builtProofStatement <$> short, afterShort)

admitsCheckedProofInputs :: Assertion
admitsCheckedProofInputs = do
    foundation <- expectRight Foundation.checkedFoundation
    let object = case fixtureObjectIds testGlobalFixture of
            [single] -> single
            _ -> error "proof input fixture changed arity"
    source <- expectRight (checkScopedCanonicalCore testGlobalType []
        (CApp (CLam TySet CTruth) (CGlobal object)))
    full <- expectRight (KernelProof.scopedProofContext
        foundation testGlobalType [] [])
    let missingTyping = fixtureGlobalTyping (globalTypingFixture [])
    missing <- expectRight (KernelProof.scopedProofContext
        foundation missingTyping [] [])
    otherScope <- expectRight (KernelProof.scopedProofContext
        foundation missingTyping [TySet] [])
    assertEqual "checked typing admits in the source's visible snapshot"
        (Right source) (KernelProof.admitScopedTerm full source)
    assertEqual "an unused beta argument cannot erase a missing global at entry"
        (Left (KernelProof.ProofTermIllTyped UnknownCoreGlobal))
        (KernelProof.admitScopedTerm missing source)
    let pool = Conversion.conversionPool 17
        run work context = KernelProof.runCountedProof work pool $ KernelProof.countedAdmitScopedTerm context source
    assertEqual "admission charges source syntax and preserves conversion credit"
        (Right source, 0, pool) (run 5 full)
    assertEqual "failure retains the complete spent admission work"
        (Left (CountedCoreOperationFailed
            (KernelProof.ProofTermIllTyped UnknownCoreGlobal)), 0, pool)
        (run 5 missing)
    assertEqual "short admission cannot inspect an uncharged missing global"
        (Left CountedCoreStructuralWorkExhausted, 0, pool) (run 4 missing)
    case run 5 otherScope of
        (Left (CountedCoreOperationFailed
                KernelProof.ProofStructuralCompositionMismatch{}), 4, remaining) ->
            assertEqual "context failure preserves pool" pool remaining
        other -> assertFailure ("context admission failure changed: " <> show other)

    -- A later preserving projection cannot supply the admission skipped by a
    -- caller. The authorizing checker still re-enters the original evidence.
    sourceContext <- expectRight (KernelProof.scopedProofContext
        foundation testGlobalType [] [source])
    _admitted <- expectRight (KernelProof.admitScopedTerm sourceContext source)
    sourceProof <- expectRight (KernelProof.indexedHypothesisProof
        sourceContext (hypothesisIx 0))
    truthProof <- expectRight (KernelProof.truthIntroductionProof sourceContext)
    joined <- expectCounted "checked conjunction"
        (KernelProof.runCountedProof 4 pool $ KernelProof.countedConjunctionIntroductionProof sourceProof truthProof)
    projected <- expectRight (KernelProof.conjunctionRightProof sourceContext joined)
    let replay typing = replayScopedKernelDerivation foundation defaultKernelReplayLimits
            typing Vector.empty (Vector.singleton source)
            (KernelProof.builtProofStatement projected) (KernelProof.builtProofDerivation projected)
    replayed <- expectRight (replay testGlobalType)
    assertEqual "projection retains its exact source hypothesis origin"
        (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "fresh replay rejects an unused global erased from the conclusion"
        (Left (KernelReplayStoredTermIllTyped UnknownCoreGlobal))
        (replayedScopedKernelTarget <$> replay missingTyping)

countsCheckedConjunctions :: Assertion
countsCheckedConjunctions = do
    foundation <- expectRight Foundation.checkedFoundation
    for_ [0, 64] \depth -> do
        let context = [TyProp, TySet]
            atom = CBound 0
            term = foldl' (\left _ -> CAnd left atom) atom [1 .. depth :: Int]
        left <- checkedScoped context term
        right <- checkedScoped context CTruth
        ordinary <- expectRight (Semantics.conjunctionIntroduction left right)
        assertEqual "retain the complete exact conjunction, including truth"
            (CAnd term CTruth) (scopedCoreTerm ordinary)
        -- One node, two context rows/types and two proposition checks.
        assertEqual "composition work is independent of checked operand size"
            (Right ordinary, 0) (Semantics.countedConjunctionIntroduction 7 left right)
        for_ [0 .. 6] \work ->
            assertEqual "every shorter allowance fails without checked output"
                (Left CountedCoreStructuralWorkExhausted, 0)
                (Semantics.countedConjunctionIntroduction work left right)
        proofContext <- expectRight (KernelProof.scopedProofContext
            foundation emptyGlobalTyping context [left, right])
        leftProof <- expectRight (KernelProof.indexedHypothesisProof proofContext (hypothesisIx 0))
        rightProof <- expectRight (KernelProof.indexedHypothesisProof proofContext (hypothesisIx 1))
        let pool = Conversion.conversionPool 19
            build work = KernelProof.runCountedProof work pool $ KernelProof.countedConjunctionIntroductionProof leftProof rightProof
            (built, remaining, afterPool) = build 8
        proof <- expectRight built
        assertEqual "proof construction charges one entry and no conversion credit"
            (0, pool) (remaining, afterPool)
        let (short, shortWork, shortPool) = build 7
        assertEqual "proof exhaustion retains its spent structural work"
            (Left CountedCoreStructuralWorkExhausted, 0, pool)
            (KernelProof.builtProofStatement <$> short, shortWork, shortPool)
        replayed <- expectRight (replayScopedKernelDerivation
            foundation defaultKernelReplayLimits emptyGlobalTyping Vector.empty
            (Vector.fromList [left, right]) ordinary (KernelProof.builtProofDerivation proof))
        assertEqual "both distinct hypothesis origins survive independent replay"
            (Set.fromList [hypothesisIx 0, hypothesisIx 1])
            (replayedScopedKernelExternalHypothesisUses replayed)

    proposition <- checkedScoped [TyProp] (CBound 0)
    otherContext <- checkedScoped [TySet] CTruth
    set <- checkedScoped [TySet] (CBound 0)
    let check work left right expected remaining =
            assertEqual "malformed premises keep the semantic error and spent work"
                (Left (CountedCoreOperationFailed expected), remaining)
                (Semantics.countedConjunctionIntroduction work left right)
    check 10 proposition otherContext (Semantics.KernelContextMismatch [TyProp] [TySet]) 7
    check 10 set otherContext (Semantics.KernelExpectedProposition TySet) 6
    check 10 otherContext set (Semantics.KernelExpectedProposition TySet) 5

replaysConversionUnderCurrentSnapshot :: Assertion
replaysConversionUnderCurrentSnapshot = do
    foundation <- expectRight Foundation.checkedFoundation
    let fullFixture = globalTypingFixture [TySet]
        full = fixtureGlobalTyping fullFixture
        missing = fixtureGlobalTyping (globalTypingFixture [])
        object = case fixtureObjectIds fullFixture of
            [single] -> single
            _ -> error "conversion replay fixture changed arity"
    source <- expectRight (checkScopedCanonicalCore full [] CTruth)
    target <- expectRight (checkScopedCanonicalCore full []
        (CApp (CLam TySet CTruth) (CGlobal object)))
    context <- expectRight (KernelProof.scopedProofContext foundation full [] [source])
    sourceProof <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    proof <- expectRight (KernelProof.conversionProof context sourceProof target)
    let derivation = KernelProof.builtProofDerivation proof
        replay typing hypotheses = replayedScopedKernelTarget <$>
            replayScopedKernelDerivation foundation defaultKernelReplayLimits
                typing Vector.empty hypotheses target derivation
    assertEqual "the exact stored pair replays in its lawful snapshot"
        (Right target) (replay full (Vector.singleton source))
    assertEqual "even an unused stored global is re-admitted during fresh conversion"
        (Left (KernelReplayConversionFailed
            (Conversion.ConversionInputFailure
                (Conversion.ConversionAdmissionFailure UnknownCoreGlobal))))
        (replay missing (Vector.singleton source))
    assertEqual "source failure wins before stored-target admission or expected-target checks"
        (Left (KernelReplayHypothesisOutOfBounds (hypothesisIx 0)))
        (replay missing Vector.empty)

replaysPointwiseAbstraction :: Assertion
replaysPointwiseAbstraction = for_ [1, 2, 3 :: Int] \depth -> do
    foundation <- expectRight Foundation.checkedFoundation
    let arrow = foldr (const (TyArrow TySet)) TySet [1 .. depth]
        types = [arrow, arrow]
        arguments = reverse [0 .. fromIntegral depth - 1]
        applied index = foldl' CApp (CBound index) (CBound <$> arguments)
        leafTerm = CEq TySet (applied (fromIntegral depth)) (applied (fromIntegral depth + 1))
        pointwise = foldr (const (CForall TySet)) leafTerm [1 .. depth]
    hypothesis <- checkedScoped types pointwise
    target <- checkedScoped types (CEq arrow (CBound 0) (CBound 1))
    context <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping types [hypothesis])
    inner <- foldM (\owner _ -> fst <$> expectRight (KernelProof.extendProofContextBinder owner TySet))
        context [1 .. depth]
    universal <- expectRight (KernelProof.indexedHypothesisProof inner (hypothesisIx 0))
    leaf <- foldM (\proof index -> do
        argument <- checkedScoped (KernelProof.proofContextTypes inner) (CBound index)
        expectRight (KernelProof.forallEliminationProof inner proof argument)) universal arguments
    abstracted <- foldM (\body _ -> do
        ordinary <- expectRight (KernelProof.equalityCongruenceLambdaProof TySet body)
        let build work = KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedEqualityCongruenceLambdaProof TySet body
        countedProofBoundary "lambda congruence" (KernelProof.builtProofStatement ordinary) build
        expectCounted "lambda congruence" (build 100000)) leaf [1 .. depth]
    proof <- expectRight (KernelProof.conversionProof context abstracted target)
    replayed <- expectRight (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.singleton hypothesis) target (KernelProof.builtProofDerivation proof))
    assertEqual "exact outer endpoints survive all wrappers" target (replayedScopedKernelTarget replayed)
    assertEqual "only the pointwise hypothesis is used" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "function extensionality requires no foundation leaf" Set.empty
        (replayedScopedKernelFoundationUses replayed)
    assertBool "a wrong binder cannot close the child"
        (isLeft (KernelProof.equalityCongruenceLambdaProof TyProp leaf))
    truth <- expectRight (KernelProof.truthIntroductionProof inner)
    assertBool "a non-equality child cannot be abstracted"
        (isLeft (KernelProof.equalityCongruenceLambdaProof TySet truth))
    -- A builder can assemble the same conclusion from an unauthorized local
    -- equality. Independent replay must not treat that as pointwise evidence.
    let leafStatement = KernelProof.builtProofStatement leaf
    badContext <- expectRight (KernelProof.scopedProofContext foundation emptyGlobalTyping
        (KernelProof.proofContextTypes inner) [leafStatement])
    badLeaf <- expectRight (KernelProof.indexedHypothesisProof badContext (hypothesisIx 0))
    badWrappers <- foldM (\body _ -> expectRight (KernelProof.equalityCongruenceLambdaProof TySet body))
        badLeaf [1 .. depth]
    badProof <- expectRight (KernelProof.conversionProof context badWrappers target)
    assertBool "an argument-dependent assumption is not an outer permitted hypothesis"
        (isLeft (replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.singleton hypothesis) target
            (KernelProof.builtProofDerivation badProof)))

replaysEtaConversion :: Assertion
replaysEtaConversion = do
    foundation <- expectRight Foundation.checkedFoundation
    let function = TyArrow TySet TySet
        types = [function]
        eta = CLam TySet (CApp (CBound 1) (CBound 0))
    original <- checkedScoped types (CEq function (CBound 0) (CBound 0))
    target <- checkedScoped types (CEq function eta (CBound 0))
    context <- expectRight (KernelProof.scopedProofContext
        foundation emptyGlobalTyping types [original])
    premise <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    let report = Conversion.convertibleChecked emptyGlobalTyping
            (Conversion.conversionLimit 100000) original target
        cost = Conversion.conversionCostAmount (Conversion.conversionCost report)
        build amount = KernelProof.conversionProofWithPool
            (Conversion.conversionPool amount) context premise target
    proof <- expectRight (fst (build cost))
    assertEqual "exact conversion cost is consumed" (Conversion.conversionPool 0)
        (snd (build cost))
    assertBool "one less cannot mint an eta witness" (isLeft (fst (build (cost - 1))))
    let replay expected = replayScopedKernelDerivation foundation defaultKernelReplayLimits
            emptyGlobalTyping Vector.empty (Vector.singleton original)
            expected (KernelProof.builtProofDerivation proof)
    replayed <- expectRight (replay target)
    assertEqual "eta conversion preserves the exact written target" target
        (replayedScopedKernelTarget replayed)
    assertEqual "conversion adds no foundation authority" Set.empty
        (replayedScopedKernelFoundationUses replayed)
    assertEqual "only the source hypothesis is used" (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertBool "convertible is not a substitute for the exact replay target"
        (isLeft (replay original))

accountsProofConversion :: Assertion
accountsProofConversion = do
    foundation <- expectRight Foundation.checkedFoundation
    source <- checkedScoped [] (CApp (CLam TyProp (CBound 0)) CTruth)
    target <- checkedScoped [] CTruth
    mismatch <- checkedScoped [] CFalsum
    context <- expectRight (KernelProof.scopedProofContext
        foundation emptyGlobalTyping [] [source])
    premise <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    let direct = Conversion.convertibleChecked emptyGlobalTyping
            (Conversion.conversionLimit 100000) source target
        amount = Conversion.conversionCostAmount (Conversion.conversionCost direct)
        run pool = KernelProof.conversionProofWithPool pool context premise target
        (exactResult, exactPool) = run (Conversion.conversionPool amount)
        (shortResult, shortPool) = run (Conversion.conversionPool (amount - 1))
    proof <- expectRight exactResult
    assertEqual "the witness target is the built proof statement"
        target (KernelProof.builtProofStatement proof)
    assertEqual "exact success debits the complete facade cost"
        (Conversion.conversionPool 0) exactPool
    assertEqual "one less cannot produce a proof"
        (Left (KernelProof.ProofConversionLimitExhausted
            KernelProof.ProofConversionAggregatePool (Conversion.conversionLimit (amount - 1))))
        (KernelProof.builtProofStatement <$> shortResult)
    assertEqual "failure debits before returning" (Conversion.conversionPool 0) shortPool
    replayed <- expectRight (replayScopedKernelDerivation
        foundation defaultKernelReplayLimits emptyGlobalTyping Vector.empty
        (Vector.singleton source) target (KernelProof.builtProofDerivation proof))
    assertEqual "fresh replay preserves exactly the source hypothesis authority"
        (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
    let mismatchReport = Conversion.convertibleChecked emptyGlobalTyping
            (Conversion.conversionLimit 100000) source mismatch
        mismatchCost = Conversion.conversionCostAmount (Conversion.conversionCost mismatchReport)
        (mismatchResult, mismatchPool) = KernelProof.conversionProofWithPool
            (Conversion.conversionPool 100000) context premise mismatch
    assertEqual "non-convertibility remains a distinct proof outcome"
        (Left KernelProof.ProofConversionNotConvertible)
        (KernelProof.builtProofStatement <$> mismatchResult)
    assertEqual "mismatch preserves its consumed work"
        (Conversion.conversionPool (100000 - mismatchCost)) mismatchPool

    let secondReport = Conversion.convertibleChecked emptyGlobalTyping
            (Conversion.conversionLimit 100000) target mismatch
        secondCost = Conversion.conversionCostAmount (Conversion.conversionCost secondReport)
        (firstResult, afterFirst) = run (Conversion.conversionPool (amount + secondCost))
    firstProof <- expectRight firstResult
    assertEqual "the first conversion leaves the next operation's exact allowance"
        (Conversion.conversionPool secondCost) afterFirst
    let (secondResult, afterSecond) = KernelProof.conversionProofWithPool
            afterFirst context firstProof mismatch
    assertEqual "sequential non-convertibility debits the shared remainder"
        (Left KernelProof.ProofConversionNotConvertible, Conversion.conversionPool 0)
        (KernelProof.builtProofStatement <$> secondResult, afterSecond)
    let (thirdResult, afterThird) = KernelProof.conversionProofWithPool
            afterSecond context firstProof target
    assertEqual "a later conversion cannot reset the exhausted pool"
        (Left (KernelProof.ProofConversionLimitExhausted
            KernelProof.ProofConversionAggregatePool (Conversion.conversionLimit 0)), afterSecond)
        (KernelProof.builtProofStatement <$> thirdResult, afterThird)

    let (countedResult, structural, countedPool) = KernelProof.runCountedProof 1 (Conversion.conversionPool amount) $ KernelProof.countedConversionProof context premise target
    _ <- expectRight countedResult
    assertEqual "the counted proof owner charges an entry and the same conversion cost"
        (0, exactPool) (structural, countedPool)

    let initialPool = Conversion.conversionPool amount
        (notStarted, structuralZero, untouchedPool) = KernelProof.runCountedProof 0 initialPool $ KernelProof.countedConversionProof context premise target
    assertEqual "structural exhaustion prevents conversion from starting"
        (Left CountedCoreStructuralWorkExhausted)
        (KernelProof.builtProofStatement <$> notStarted)
    assertEqual "no conversion means no pool debit"
        (0, initialPool) (structuralZero, untouchedPool)

    let composed work = KernelProof.runCountedProof work
            (Conversion.conversionPool (amount + secondCost)) do
                first <- KernelProof.countedConversionProof context premise target
                KernelProof.countedConversionProof context first mismatch
        observe (outcome, work, pool) = (KernelProof.builtProofStatement <$> outcome, work, pool)
    assertEqual "a composed failure retains both conversions' expenditure"
        (Left (CountedCoreOperationFailed KernelProof.ProofConversionNotConvertible),
            0, Conversion.conversionPool 0)
        (observe (composed 2))
    assertEqual "a later exhausted entry preserves the first operation's pool debit"
        (Left CountedCoreStructuralWorkExhausted, 0, Conversion.conversionPool secondCost)
        (observe (composed 1))

countsFocusedMaterializers :: Assertion
countsFocusedMaterializers = do
    foundation <- expectRight Foundation.checkedFoundation
    let deep = nestedNegation 80 CTruth
    conjunction <- checkedScoped [] (CAnd deep CTruth)
    conjunctionContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [conjunction])
    conjunctionRoots <-
        expectCounted
            "counted conjunction root"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs conjunctionContext)
    conjunctionProof <-
        case conjunctionRoots of
            [proof] -> pure proof
            _ -> assertFailure "expected one conjunction root"
                >> fail "missing conjunction root"
    ordinaryProjection <-
        expectRight
            (KernelProof.conjunctionLeftProof
                conjunctionContext conjunctionProof)
    countedProofBoundary
        "deep conjunction projection"
        (KernelProof.builtProofStatement ordinaryProjection)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedConjunctionLeftProof conjunctionContext deep CTruth conjunctionProof)

    premise <- checkedScoped [] deep
    implication <- checkedScoped [] (CImp deep deep)
    implicationContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [implication, premise])
    implicationRoots <-
        expectCounted
            "counted implication roots"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs implicationContext)
    (implicationProof, premiseProof) <-
        case implicationRoots of
            [first, second] -> pure (first, second)
            _ -> assertFailure "expected two implication roots"
                >> fail "missing implication roots"
    ordinaryElimination <-
        expectRight
            (KernelProof.implicationEliminationProof
                implicationContext implicationProof premiseProof)
    countedProofBoundary
        "deep implication elimination"
        (KernelProof.builtProofStatement ordinaryElimination)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedImplicationEliminationProof implicationContext implicationProof premiseProof)

    ordinaryLeftDisjunction <-
        expectRight
            (KernelProof.disjunctionLeftProof
                implicationContext CTruth premiseProof)
    countedProofBoundary
        "left disjunction introduction"
        (KernelProof.builtProofStatement ordinaryLeftDisjunction)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedDisjunctionLeftProof implicationContext CTruth premiseProof)
    truthProof <-
        expectRight
            (KernelProof.truthIntroductionProof implicationContext)
    ordinaryRightDisjunction <-
        expectRight
            (KernelProof.disjunctionRightProof
                implicationContext deep truthProof)
    countedProofBoundary
        "right disjunction introduction"
        (KernelProof.builtProofStatement ordinaryRightDisjunction)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedDisjunctionRightProof implicationContext deep truthProof)

    let quantifiedBody = repeatedConjunction 40 (CBound 0)
    quantified <-
        checkedScoped [] (CForall TyProp quantifiedBody)
    argument <- checkedScoped [] CTruth
    quantifiedContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [quantified])
    quantifiedRoots <-
        expectCounted
            "counted quantified root"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs quantifiedContext)
    quantifiedProof <-
        case quantifiedRoots of
            [proof] -> pure proof
            _ -> assertFailure "expected one quantified root"
                >> fail "missing quantified root"
    ordinaryInstantiation <-
        expectRight
            (KernelProof.forallEliminationProof
                quantifiedContext quantifiedProof argument)
    countedProofBoundary
        "large universal instantiation"
        (KernelProof.builtProofStatement ordinaryInstantiation)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedForallEliminationProof quantifiedContext quantifiedProof argument)

    let ordinaryWeakened = KernelProof.weakenProofHypotheses 1 quantifiedProof
        initialPool = Conversion.conversionPool 17
        (ampleWeakened, afterWeaken, afterPool) =
            KernelProof.runCountedProof 100000 initialPool $ KernelProof.countedWeakenProofHypotheses 1 quantifiedProof
    weakened <- expectRight ampleWeakened
    assertEqual "counted weakening preserves the statement"
        (KernelProof.builtProofStatement ordinaryWeakened)
        (KernelProof.builtProofStatement weakened)
    assertEqual "weakening does not spend conversion work" initialPool afterPool
    let (unchanged, zeroWork, zeroPool) =
            KernelProof.runCountedProof 0 initialPool $ KernelProof.countedWeakenProofHypotheses 0 quantifiedProof
    _ <- expectRight unchanged
    assertEqual "zero weakening preserves both resources" (0, initialPool) (zeroWork, zeroPool)
    let weakenWork = 100000 - afterWeaken
    _ <- expectCounted "exact weakening"
        (KernelProof.runCountedProof weakenWork initialPool $ KernelProof.countedWeakenProofHypotheses 1 quantifiedProof)
    case KernelProof.runCountedProof (weakenWork - 1) initialPool $ KernelProof.countedWeakenProofHypotheses 1 quantifiedProof of
        (Left CountedCoreStructuralWorkExhausted, 0, remainingPool) ->
            assertEqual "failed weakening preserves the conversion pool" initialPool remainingPool
        (result, remaining, remainingPool) ->
            assertFailure ("unexpected weakening boundary: "
                <> show (KernelProof.builtProofStatement <$> result, remaining, remainingPool))

    let emptySet = CIntrinsic Empty
        pairSet = CApp (CApp (CIntrinsic PairSet) emptySet) emptySet
        unionSet = CApp (CIntrinsic FamilyUnion) emptySet
    firstEquality <- checkedScoped [] (CEq TySet emptySet pairSet)
    secondEquality <- checkedScoped [] (CEq TySet pairSet unionSet)
    equalityContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [firstEquality, secondEquality])
    equalityRoots <-
        expectCounted
            "counted equality roots"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs equalityContext)
    (firstProof, secondProof) <-
        case equalityRoots of
            [first, second] -> pure (first, second)
            _ -> assertFailure "expected two equality roots"
                >> fail "missing equality roots"
    ordinaryComposition <-
        expectRight
            (KernelProof.composeEqualityProof
                equalityContext firstProof secondProof)
    countedProofBoundaryWithConversion
        "equality path composition"
        (KernelProof.builtProofStatement ordinaryComposition)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 100000) $ KernelProof.countedComposeEqualityProof equalityContext firstProof secondProof)

    doubleNegation <- checkedScoped [] (CNot (CNot deep))
    doubleNegationContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [doubleNegation])
    doubleNegationRoots <-
        expectCounted
            "counted double-negation root"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs doubleNegationContext)
    doubleNegationProof <-
        case doubleNegationRoots of
            [proof] -> pure proof
            _ -> assertFailure "expected one double-negation root"
                >> fail "missing double-negation root"
    deepTarget <- checkedScoped [] deep
    ordinaryDoubleNegation <-
        expectRight
            (KernelProof.doubleNegationEliminationProof
                doubleNegationContext deepTarget doubleNegationProof)
    countedProofBoundary
        "double-negation elimination"
        (KernelProof.builtProofStatement ordinaryDoubleNegation)
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedDoubleNegationEliminationProof doubleNegationContext deepTarget
                doubleNegationProof)

    disjunction <- checkedScoped [] (COr deep CTruth)
    disjunctionContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [disjunction])
    disjunctionRoots <-
        expectCounted
            "counted disjunction root"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedHypothesisProofs disjunctionContext)
    disjunctionProof <-
        case disjunctionRoots of
            [proof] -> pure proof
            _ -> assertFailure "expected one disjunction root"
                >> fail "missing disjunction root"
    leftTarget <- checkedScoped [] deep
    rightTarget <- checkedScoped [] CTruth
    leftContext <-
        expectRight
            (KernelProof.extendProofContextHypothesis
                disjunctionContext leftTarget)
    rightContext <-
        expectRight
            (KernelProof.extendProofContextHypothesis
                disjunctionContext rightTarget)
    leftTruth <- expectRight (KernelProof.truthIntroductionProof leftContext)
    rightTruth <- expectRight (KernelProof.truthIntroductionProof rightContext)
    truthTarget <- checkedScoped [] CTruth
    countedProofBoundary
        "prepared disjunction elimination"
        truthTarget
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedPreparedDisjunctionEliminationProof disjunctionContext deep CTruth
                disjunctionProof truthTarget leftTruth rightTruth)

    let excludedMiddleTerm = COr deep (CNot deep)
    excludedMiddleTarget <- checkedScoped [] excludedMiddleTerm
    emptyContext <-
        expectRight
            (KernelProof.scopedProofContext
                foundation emptyGlobalTyping [] [])
    countedProofBoundary
        "excluded middle"
        excludedMiddleTarget
        (\work ->
            KernelProof.runCountedProof work (Conversion.conversionPool 0) $ KernelProof.countedExcludedMiddleProof emptyContext deepTarget)
    excludedMiddleProof <-
        expectCounted
            "excluded middle replay"
            (KernelProof.runCountedProof 100000 (Conversion.conversionPool 0) $ KernelProof.countedExcludedMiddleProof emptyContext deepTarget)
    excludedMiddleReplay <-
        expectRight
            (replayScopedKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                Vector.empty
                excludedMiddleTarget
                (KernelProof.builtProofDerivation excludedMiddleProof))
    assertEqual "excluded middle has no external hypotheses"
        Set.empty
        (replayedScopedKernelExternalHypothesisUses
            excludedMiddleReplay)

    replayed <-
        expectRight
            (replayScopedKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                (Vector.singleton quantified)
                (KernelProof.builtProofStatement ordinaryInstantiation)
                (KernelProof.builtProofDerivation ordinaryInstantiation))
    assertEqual "counted universal materialization remains replayable"
        (Set.singleton (hypothesisIx 0))
        (replayedScopedKernelExternalHypothesisUses replayed)

countedProofBoundary
    :: String
    -> ScopedCheckedCore Void
    -> ( Word
         -> ( Either
                (CountedCoreFailure KernelProof.KernelProofBuildError)
                (KernelProof.BuiltProof Void)
            , Word
            , Conversion.ConversionPool
            )
       )
    -> Assertion
countedProofBoundary label expected operation = do
    let ample = 100000
        (ampleResult, ampleRemaining, amplePool) = operation ample
    proof <- expectRight ampleResult
    assertEqual (label <> " agrees with the ordinary builder")
        expected
        (KernelProof.builtProofStatement proof)
    assertEqual (label <> " preserves the empty conversion pool")
        (Conversion.conversionPool 0) amplePool
    let used = ample - ampleRemaining
    assertBool (label <> " traverses more than its entry constructor")
        (used > 1)
    exact <- expectCounted (label <> " exact boundary") (operation used)
    assertEqual (label <> " exact-boundary statement")
        expected
        (KernelProof.builtProofStatement exact)
    case operation (used - 1) of
        (Left CountedCoreStructuralWorkExhausted, 0, remainingPool) ->
            assertEqual (label <> " failure preserves the pool")
                (Conversion.conversionPool 0) remainingPool
        (Left failure, remaining, pool) ->
            assertFailure
                (label <> " reported the wrong boundary: "
                    <> show (failure, remaining, pool))
        (Right _proof, remaining, pool) ->
            assertFailure
                (label <> " published a proof past its boundary: "
                    <> show (remaining, pool))

countedProofBoundaryWithConversion
    :: String
    -> ScopedCheckedCore Void
    -> ( Word
         -> ( Either
                (CountedCoreFailure KernelProof.KernelProofBuildError)
                (KernelProof.BuiltProof Void)
            , Word
            , Conversion.ConversionPool
            )
       )
    -> Assertion
countedProofBoundaryWithConversion label expected operation = do
    let ample = 100000
        (ampleResult, ampleRemaining, amplePool) = operation ample
    proof <- expectRight ampleResult
    assertEqual (label <> " agrees with the ordinary builder")
        expected
        (KernelProof.builtProofStatement proof)
    assertBool (label <> " records its semantic conversion work")
        (Conversion.conversionPoolAmount amplePool < 100000)
    let used = ample - ampleRemaining
    exact <- expectCounted (label <> " exact boundary") (operation used)
    assertEqual (label <> " exact-boundary statement")
        expected
        (KernelProof.builtProofStatement exact)
    case operation (used - 1) of
        (Left CountedCoreStructuralWorkExhausted, _, _) -> pure ()
        (Left failure, remaining, pool) ->
            assertFailure
                (label <> " reported the wrong boundary: "
                    <> show (failure, remaining, pool))
        (Right _proof, remaining, pool) ->
            assertFailure
                (label <> " published a proof past its boundary: "
                    <> show (remaining, pool))

expectCounted
    :: Show error
    => String
    -> (Either error value, Word, Conversion.ConversionPool)
    -> IO value
expectCounted label (result, _structural, _pool) =
    either
        (assertFailure . ((label <> ": ") <>) . show)
        pure
        result

nestedNegation
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
nestedNegation 0 proposition = proposition
nestedNegation amount proposition =
    CNot (nestedNegation (amount - 1) proposition)

repeatedConjunction
    :: Natural
    -> CanonicalTerm global
    -> CanonicalTerm global
repeatedConjunction 0 proposition = proposition
repeatedConjunction amount proposition =
    CAnd proposition (repeatedConjunction (amount - 1) proposition)

replaysEqualityReflexivity :: Assertion
replaysEqualityReflexivity = do
    foundation <-
        expectRight Foundation.checkedFoundation
    operand <-
        expectRight
            (checkCanonicalCore
                emptyGlobalTyping
                (CIntrinsic Empty))
    direct <-
        expectRight
            (Semantics.equalityReflexivity
                (embedClosedCore [] operand))
    directClosed <-
        maybe
            (assertFailure
                "closed reflexivity result remained scoped")
            pure
            (closeScopedCore direct)
    replayed <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                directClosed
                (equalityReflexivityDerivation operand))
    assertEqual
        "replay agrees with direct semantics"
        directClosed
        (replayedKernelTarget replayed)
    assertEqual
        "one replayed inference"
        1
        (replayedKernelNodeCount replayed)
    assertEqual "a root inference has depth zero" 0
        (replayedKernelMaximumDepth replayed)

replaysLogicalScopes :: Assertion
replaysLogicalScopes = do
    foundation <-
        expectRight Foundation.checkedFoundation
    proposition <-
        checkedClosed
            (CEq TySet
                (CIntrinsic Empty)
                (CIntrinsic Empty))
    implication <-
        checkedScoped []
            (CImp
                (frozenCoreTerm proposition)
                (frozenCoreTerm proposition))
    let propositionScoped =
            embedClosedCore [] proposition
        identity =
            implicationIntroductionDerivation
                propositionScoped
                (localHypothesisDerivation
                    (hypothesisIx 0))
        elimination =
            implicationIntroductionDerivation
                propositionScoped
                (implicationIntroductionDerivation
                    implication
                    (implicationEliminationDerivation
                        (localHypothesisDerivation
                            (hypothesisIx 0))
                        (localHypothesisDerivation
                            (hypothesisIx 1))))
        fromFalsum =
            implicationIntroductionDerivation
                falsum
                (falsumEliminationDerivation
                    (localHypothesisDerivation
                        (hypothesisIx 0))
                    propositionScoped)
        falsum =
            unsafeScoped [] CFalsum
    assertReplayTarget
        foundation
        (CImp
            (frozenCoreTerm proposition)
            (frozenCoreTerm proposition))
        identity
    assertReplayTarget
        foundation
        (CImp
            (frozenCoreTerm proposition)
            (CImp
                (scopedCoreTerm implication)
                (frozenCoreTerm proposition)))
        elimination
    assertReplayTarget
        foundation
        (CImp
            CFalsum
            (frozenCoreTerm proposition))
        fromFalsum

replaysQuantifierAndEqualityStructure :: Assertion
replaysQuantifierAndEqualityStructure = do
    foundation <-
        expectRight Foundation.checkedFoundation
    boundSet <-
        checkedScoped [TySet] (CBound 0)
    emptySet <-
        checkedScoped [] (CIntrinsic Empty)
    unionFunction <-
        checkedScoped [] (CIntrinsic FamilyUnion)
    proposition <-
        checkedClosed
            (CEq TySet
                (CIntrinsic Empty)
                (CIntrinsic Empty))
    convertedTarget <-
        checkedScoped []
            (CEq TySet
                (CApp
                    (CLam TySet (CBound 0))
                    (CIntrinsic Empty))
                (CIntrinsic Empty))
    context <- expectRight
        (KernelProof.scopedProofContext foundation emptyGlobalTyping [] [])
    sourceProof <- expectRight (KernelProof.equalityReflexivityProof context emptySet)
    converted <- expectRight (KernelProof.conversionProof context sourceProof convertedTarget)
    let boundReflexivity =
            scopedEqualityReflexivityDerivation boundSet
        universalReflexivity =
            forallIntroductionDerivation
                TySet
                boundReflexivity
        specializedReflexivity =
            forallEliminationDerivation
                universalReflexivity
                emptySet
        applicationCongruence =
            equalityCongruenceApplicationDerivation
                (scopedEqualityReflexivityDerivation
                    unionFunction)
                (scopedEqualityReflexivityDerivation
                    emptySet)
        lambdaCongruence =
            equalityCongruenceLambdaDerivation
                TySet
                boundReflexivity
        equalityMp =
            implicationIntroductionDerivation
                (embedClosedCore [] proposition)
                (equalityModusPonensDerivation
                    (scopedEqualityReflexivityDerivation
                        (embedClosedCore []
                            proposition))
                    (localHypothesisDerivation
                        (hypothesisIx 0)))
        conversion = KernelProof.builtProofDerivation converted
    assertReplayTarget
        foundation
        (CForall TySet
            (CEq TySet
                (CBound 0)
                (CBound 0)))
        universalReflexivity
    assertReplayTarget
        foundation
        (CEq TySet
            (CIntrinsic Empty)
            (CIntrinsic Empty))
        specializedReflexivity
    assertReplayTarget
        foundation
        (CEq TySet
            (CApp
                (CIntrinsic FamilyUnion)
                (CIntrinsic Empty))
            (CApp
                (CIntrinsic FamilyUnion)
                (CIntrinsic Empty)))
        applicationCongruence
    assertReplayTarget
        foundation
        (CEq
            (TySet `TyArrow` TySet)
            (CLam TySet (CBound 0))
            (CLam TySet (CBound 0)))
        lambdaCongruence
    assertReplayTarget
        foundation
        (CImp
            (frozenCoreTerm proposition)
            (frozenCoreTerm proposition))
        equalityMp
    assertReplayTarget
        foundation
        (scopedCoreTerm convertedTarget)
        conversion

buildsDirectionalEqualityTransport :: Assertion
buildsDirectionalEqualityTransport = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptySet = CIntrinsic Empty
        pair = CApp (CApp (CIntrinsic PairSet) emptySet) emptySet
    equality <- checkedScoped [] (CEq TySet pair emptySet)
    premise <- checkedScoped [] (CEq TySet emptySet emptySet)
    predicate <- checkedScoped []
        (CLam TySet (CEq TySet (CBound 0) emptySet))
    expected <- checkedScoped [] (CEq TySet pair emptySet)
    context <- expectRight
        (KernelProof.scopedProofContext
            foundation
            emptyGlobalTyping
            []
            [equality, premise])
    transported <- expectRight
        (KernelProof.equalityTransportDerivationProof
            context
            KernelProof.EqualityRightToLeft
            equality
            (localHypothesisDerivation (hypothesisIx 0))
            predicate
            premise
            (localHypothesisDerivation (hypothesisIx 1))
            expected)
    assertEqual "directional transport target"
        expected
        (KernelProof.builtProofStatement transported)
    replayed <- expectRight
        (replayScopedKernelDerivation
            foundation
            defaultKernelReplayLimits
            emptyGlobalTyping
            Vector.empty
            (Vector.fromList [equality, premise])
            expected
            (KernelProof.builtProofDerivation transported))
    assertEqual "directional transport uses both exact hypotheses"
        (Set.fromList [hypothesisIx 0, hypothesisIx 1])
        (replayedScopedKernelExternalHypothesisUses replayed)

remapsOnlyExternalHypotheses :: Assertion
remapsOnlyExternalHypotheses = do
    foundation <- expectRight Foundation.checkedFoundation
    let pTerm = CEq TySet (CIntrinsic Empty) (CIntrinsic Empty)
    p <- checkedScoped [] pTerm
    implication <- checkedScoped [] (CImp pTerm (CAnd pTerm pTerm))
    let original =
            implicationIntroductionDerivation p
                (conjunctionIntroductionDerivation
                    (localHypothesisDerivation (hypothesisIx 0))
                    (localHypothesisDerivation (hypothesisIx 1)))
        remapped =
            remapDerivationExternalHypotheses
                (hypothesisIx . (+ 1) . hypothesisIxValue)
                original
    replayed <- expectRight
        (replayScopedKernelDerivation
            foundation
            defaultKernelReplayLimits
            emptyGlobalTyping
            Vector.empty
            (Vector.fromList [p, p])
            implication
            remapped)
    assertEqual "only the remapped external leaf survives"
        (Set.singleton (hypothesisIx 1))
        (replayedScopedKernelExternalHypothesisUses replayed)

summarizesSourceUses :: Assertion
summarizesSourceUses = do
    foundation <- expectRight Foundation.checkedFoundation
    truth <- checkedScoped [] CTruth
    truthUnderBinder <- checkedScoped [TySet] CTruth
    existential <- checkedScoped [] (CExists TySet CTruth)
    falsum <- checkedScoped [] CFalsum
    imported <- expectRight . derivationImportJudgement =<< checkedClosed CTruth
    let hypothesis = localHypothesisDerivation . hypothesisIx
        importedProof = importedFactDerivation (importIx 7)
        quantifiedCases = forallIntroductionDerivation TySet
            (implicationIntroductionDerivation truthUnderBinder
                (conjunctionIntroductionDerivation importedProof
                    (disjunctionEliminationDerivation
                        (disjunctionLeftIntroductionDerivation (hypothesis 0) truthUnderBinder)
                        (hypothesis 3)
                        (hypothesis 3))))
        existentialCase = existentialEliminationDerivation
            (hypothesis 0) (unsafeScoped [] (CAnd CTruth CTruth))
            (conjunctionIntroductionDerivation importedProof (hypothesis 2))
        negated = negationIntroductionDerivation falsum (hypothesis 2)
        cases =
            [ ( "universal and disjunction binders"
              , [truth, truth]
              , CForall TySet (CImp CTruth (CAnd CTruth CTruth))
              , quantifiedCases
              , Set.singleton (importIx 7)
              , Set.singleton (hypothesisIx 1)
              , (9, 5)
              )
            , ( "existential term and proof binder"
              , [existential, truth]
              , CAnd CTruth CTruth
              , existentialCase
              , Set.singleton (importIx 7)
              , Set.fromList [hypothesisIx 0, hypothesisIx 1]
              , (5, 2)
              )
            , ( "negation binder"
              , [truth, falsum]
              , CNot CFalsum
              , negated
              , Set.empty
              , Set.singleton (hypothesisIx 1)
              , (2, 1)
              )
            ]
    for_ cases \(label, hypotheses, targetTerm, derivation, expectedImports, expectedHypotheses, expectedSize) -> do
        target <- checkedScoped [] targetTerm
        replayed <- expectRight (replayScopedKernelDerivation
            foundation defaultKernelReplayLimits emptyGlobalTyping
            (Vector.replicate 8 imported) (Vector.fromList hypotheses) target derivation)
        assertEqual (label <> ": node count and absolute maximum depth") expectedSize
            (replayedScopedKernelNodeCount replayed, replayedScopedKernelMaximumDepth replayed)
        let work = fromIntegral (replayedScopedKernelNodeCount replayed)
            (result, remaining) = countedKernelDerivationSourceUses work derivation
        uses <- maybe (assertFailure (label <> ": source summary exhausted") >> fail "missing summary") pure result
        assertEqual (label <> ": exact counted boundary") 0 remaining
        assertEqual (label <> ": import references") expectedImports (kernelSourceImportUses uses)
        assertEqual (label <> ": external hypothesis references")
            expectedHypotheses (kernelSourceExternalHypothesisUses uses)
        assertEqual (label <> ": independently replayed imports")
            (replayedScopedKernelImportUses replayed) (kernelSourceImportUses uses)
        assertEqual (label <> ": independently replayed hypotheses")
            (replayedScopedKernelExternalHypothesisUses replayed) (kernelSourceExternalHypothesisUses uses)
        assertEqual (label <> ": zero allowance publishes no summary")
            (Nothing, 0) (countedKernelDerivationSourceUses 0 derivation)
        assertEqual (label <> ": one-short allowance publishes no partial summary")
            (Nothing, 0) (countedKernelDerivationSourceUses (work - 1) derivation)

replaysNativeLogicalRules :: Assertion
replaysNativeLogicalRules = do
    foundation <- expectRight Foundation.checkedFoundation
    emptyOperand <- checkedScoped [] (CIntrinsic Empty)
    emptyUnderBinder <- checkedScoped [TySet] (CIntrinsic Empty)
    p <- checkedScoped [] pTerm
    falsum <- checkedScoped [] CFalsum
    disjunction <- checkedScoped [] (COr pTerm pTerm)
    existential <- checkedScoped [] (CExists TySet bodyTerm)
    body <- checkedScoped [TySet] bodyTerm
    let proofP = scopedEqualityReflexivityDerivation emptyOperand
        proofTruth = truthIntroductionDerivation
        proofConjunction =
            conjunctionIntroductionDerivation proofP proofTruth
        proofExists =
            existentialIntroductionDerivation body emptyOperand proofP
        contradiction =
            implicationIntroductionDerivation p
                (implicationIntroductionDerivation
                    (unsafeScoped [] (CNot pTerm))
                    (negationEliminationDerivation
                        (localHypothesisDerivation (hypothesisIx 1))
                        (localHypothesisDerivation (hypothesisIx 0))))
        disjunctionCases =
            implicationIntroductionDerivation disjunction
                (disjunctionEliminationDerivation
                    (localHypothesisDerivation (hypothesisIx 0))
                    (localHypothesisDerivation (hypothesisIx 0))
                    (localHypothesisDerivation (hypothesisIx 0)))
        existentialCase =
            implicationIntroductionDerivation existential
                (existentialEliminationDerivation
                    (localHypothesisDerivation (hypothesisIx 0))
                    p
                    (scopedEqualityReflexivityDerivation
                        emptyUnderBinder))
    traverse_
        (\(target, derivation) ->
            assertReplayTarget foundation target derivation)
        [ (CTruth, truthIntroductionDerivation)
        , (CNot CFalsum,
            negationIntroductionDerivation
                falsum
                (localHypothesisDerivation (hypothesisIx 0)))
        , (CImp pTerm (CImp (CNot pTerm) CFalsum), contradiction)
        , (CAnd pTerm CTruth, proofConjunction)
        , (pTerm, conjunctionLeftEliminationDerivation proofConjunction)
        , (CTruth, conjunctionRightEliminationDerivation proofConjunction)
        , (COr pTerm CTruth,
            disjunctionLeftIntroductionDerivation proofP
                (unsafeScoped [] CTruth))
        , (COr CTruth pTerm,
            disjunctionRightIntroductionDerivation
                (unsafeScoped [] CTruth)
                proofP)
        , (CImp (COr pTerm pTerm) pTerm, disjunctionCases)
        , (CExists TySet bodyTerm, proofExists)
        , (CImp (CExists TySet bodyTerm) pTerm, existentialCase)
        ]
    replayed <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                (unsafeClosed (CAnd pTerm CTruth))
                proofConjunction)
    assertEqual
        "ordinary logical rules are not foundation rule tags"
        mempty
        (replayedKernelRuleUses replayed)
  where
    pTerm =
        CEq TySet (CIntrinsic Empty) (CIntrinsic Empty)
    bodyTerm =
        CEq TySet (CBound 0) (CBound 0)

rejectsInvalidNativeLogicalBranches :: Assertion
rejectsInvalidNativeLogicalBranches = do
    foundation <- expectRight Foundation.checkedFoundation
    p <- checkedScoped [] pTerm
    disjunction <- checkedScoped [] (COr pTerm pTerm)
    wrongContextOperand <- checkedScoped [TySet] (CIntrinsic Empty)
    let malformedCase =
            implicationIntroductionDerivation disjunction
                (disjunctionEliminationDerivation
                    (localHypothesisDerivation (hypothesisIx 0))
                    (scopedEqualityReflexivityDerivation
                        wrongContextOperand)
                    (localHypothesisDerivation (hypothesisIx 0)))
    assertEqual
        "disjunction branch cannot change the term context"
        (Left
            (KernelReplayStoredContextMismatch
                []
                [TySet]))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                (unsafeClosed (CImp (COr pTerm pTerm) pTerm))
                malformedCase)

    existential <- checkedScoped [] (CExists TySet bodyTerm)
    let escapingCase =
            implicationIntroductionDerivation existential
                (existentialEliminationDerivation
                    (localHypothesisDerivation (hypothesisIx 0))
                    p
                    (localHypothesisDerivation (hypothesisIx 0)))
    assertEqual
        "existential eigenvariable cannot escape through the branch result"
        (Left
            (KernelReplaySemanticsError
                Semantics.KernelExistentialResultMismatch))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                (unsafeClosed (CImp (CExists TySet bodyTerm) pTerm))
                escapingCase)
  where
    pTerm =
        CEq TySet (CIntrinsic Empty) (CIntrinsic Empty)
    bodyTerm =
        CEq TySet (CBound 0) (CBound 0)

recordsAuthorityLeaves :: Assertion
recordsAuthorityLeaves = do
    foundation <-
        expectRight Foundation.checkedFoundation
    let foundationTag =
            Foundation.EmptyCharacteristic
        foundationTarget =
            eliminateFrozenVoid
                (Foundation.foundationAxiomFrozen
                    foundation
                    foundationTag)
    foundationReplay <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                foundationTarget
                (foundationFactDerivation
                    foundationTag))
    assertEqual
        "exact foundation use"
        (Set.singleton foundationTag)
        (replayedKernelFoundationUses
            foundationReplay)
    importedStatement <-
        checkedClosed
            (CEq TySet
                (CIntrinsic Empty)
                (CIntrinsic Empty))
    importedJudgement <-
        expectRight
            (derivationImportJudgement
                importedStatement)
    importedReplay <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                (Vector.singleton importedJudgement)
                importedStatement
                (importedFactDerivation
                    (importIx 0)))
    assertEqual
        "exact import use"
        (Set.singleton (importIx 0))
        (replayedKernelImportUses importedReplay)

validatesDeclaredReplayEnvironment :: Assertion
validatesDeclaredReplayEnvironment = do
    foundation <- expectRight Foundation.checkedFoundation
    object <-
        case fixtureObjectIds testGlobalFixture of
            [identity] -> pure identity
            identities ->
                assertFailure
                    ("unexpected global fixture size: "
                        <> show (length identities))
                    >> fail "unreachable"
    let staleProposition =
            CAnd CTruth
                (CEq TySet (CGlobal object) (CGlobal object))
        destinationTyping =
            fixtureGlobalTyping (globalTypingFixture [])
    checkedStale <- expectRight
        (checkCanonicalCore testGlobalType staleProposition)
    staleImport <- expectRight
        (derivationImportJudgement checkedStale)
    target <- expectRight
        (checkCanonicalCore destinationTyping
            (CTruth :: CanonicalTerm ObjectId))

    unused <- expectRight
        (replayKernelDerivation
            foundation
            defaultKernelReplayLimits
            destinationTyping
            (Vector.singleton staleImport)
            target
            truthIntroductionDerivation)
    assertEqual
        "unused import entries are not preflighted"
        Set.empty
        (replayedKernelImportUses unused)

    assertEqual
        "a referenced import is rechecked before its index is reported"
        (Left
            (KernelReplayStoredTermIllTyped UnknownCoreGlobal))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                destinationTyping
                (Vector.singleton staleImport)
                target
                (conjunctionLeftEliminationDerivation
                    (importedFactDerivation (importIx 0))))

    let staleHypothesis = embedClosedCore [] checkedStale
        scopedTarget = embedClosedCore [] target
    assertEqual
        "every declared scoped hypothesis is rechecked even when unused"
        (Left
            (KernelReplayStoredTermIllTyped UnknownCoreGlobal))
        (replayedScopedKernelTarget
            <$> replayScopedKernelDerivation
                foundation
                defaultKernelReplayLimits
                destinationTyping
                Vector.empty
                (Vector.singleton staleHypothesis)
                scopedTarget
                truthIntroductionDerivation)

checksSetLfpRules :: Assertion
checksSetLfpRules = do
    foundation <-
        expectRight Foundation.checkedFoundation
    ( domain
        , operator
        , predicate
        , element
        , fixedPoint
        , closedPremise
        , boundedPremise
        , monotonePremise
        , memberPremise
        , closurePremise
        ) <-
            setLfpFixture
    bound <-
        expectRight
            (SetLfp.setLfpBound
                foundation
                emptyGlobalTyping
                domain
                operator)
    least <-
        expectRight
            (SetLfp.setLfpLeast
                foundation
                emptyGlobalTyping
                domain
                operator
                domain
                closedPremise
                boundedPremise)
    fixed <-
        expectRight
            (SetLfp.setLfpFixed
                foundation
                emptyGlobalTyping
                domain
                operator
                monotonePremise)
    inducted <-
        expectRight
            (SetLfp.setLfpInduct
                foundation
                emptyGlobalTyping
                domain
                operator
                predicate
                element
                monotonePremise
                memberPremise
                closurePremise)
    expectedSubset <-
        expectRight
            (SetLfp.subsetProposition
                emptyGlobalTyping
                fixedPoint
                domain)
    expectedFixed <-
        checkedScoped []
            (CEq TySet
                (scopedCoreTerm fixedPoint)
                (CApp
                    (scopedCoreTerm operator)
                    (scopedCoreTerm fixedPoint)))
    expectedPredicate <-
        checkedScoped []
            (CApp
                (scopedCoreTerm predicate)
                (scopedCoreTerm element))
    assertEqual "bound conclusion" expectedSubset bound
    assertEqual "least conclusion" expectedSubset least
    assertEqual "fixed conclusion" expectedFixed fixed
    assertEqual "induction conclusion" expectedPredicate inducted

    target <-
        maybe
            (assertFailure
                "closed fixed-point bound remained scoped")
            pure
            (closeScopedCore bound)
    replayed <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                target
                (setLfpBoundDerivation
                    domain
                    operator))
    assertEqual
        "exact guarded-rule use"
        (Set.singleton Foundation.SetLfpBound)
        (replayedKernelRuleUses replayed)

replaysDirectInductiveFacts :: Assertion
replaysDirectInductiveFacts = do
    foundation <-
        expectRight Foundation.checkedFoundation
    emptyTerm <- checkedInductiveTerm [] [] (CIntrinsic Empty)
    let x = (Inductive.InductiveVariable 0, TySet)
    variable <- checkedInductiveTerm [x] [TySet] (CBound 0)
    carrierTemplate <-
        expectRight
            =<< (Inductive.directRecursiveCarrierContext
                    testGlobalType
                    Nowhere
                    [x]
                <$> checkedInductiveScoped
                    [TySet, TySet]
                    (CBound 0))
    traverse_
        (replayInductive foundation)
        [ Inductive.DirectInductive
            []
            emptyTerm
            (Inductive.DirectInductiveClause
                []
                []
                emptyTerm
                :| [])
        , Inductive.DirectInductive
                []
                emptyTerm
                ( Inductive.DirectInductiveClause
                    []
                    []
                    emptyTerm
                :| [ Inductive.DirectInductiveClause
                        [x]
                        [Inductive.DirectRecursiveCondition
                            variable
                            carrierTemplate]
                        variable
                   ]
                )
        ]
    let functionType = TyArrow TySet TySet
        parameters =
            [ (Inductive.InductiveVariable 0, TySet)
            , (Inductive.InductiveVariable 1, functionType)
            , (Inductive.InductiveVariable 2, TyProp)
            ]
        local = (Inductive.InductiveVariable 3, TySet)
        binders = parameters <> [local]
        context = reverse (snd <$> binders)
        member element set = CApp (CApp (CIntrinsic Member) element) set
        bound = member (CBound 0) (CBound 3)
        checkedFormula term = do
            scoped <- checkedInductiveScoped context term
            expectRight (Inductive.prepareCheckedInductiveFormula testGlobalType binders scoped)
    domain <- checkedInductiveTerm parameters (reverse (snd <$> parameters)) (CBound 2)
    result <- checkedInductiveTerm binders context (CBound 0)
    recursiveIndex <- checkedInductiveTerm binders context (CApp (CBound 2) (CBound 0))
    condition <- checkedFormula bound
    propositionParameter <- checkedFormula (CBound 1)
    recursiveCarrier <- expectRight =<<
        (Inductive.directRecursiveCarrierContext testGlobalType Nowhere binders <$>
            checkedInductiveScoped (TySet : context) (CBound 0))
    let base = Inductive.DirectInductiveClause [local]
            [Inductive.DirectSideCondition propositionParameter, Inductive.DirectSideCondition condition] result
        step = Inductive.DirectInductiveClause [local]
            [ Inductive.DirectSideCondition condition
            , Inductive.DirectRecursiveCondition recursiveIndex recursiveCarrier
            ] result
        mixed = Inductive.DirectInductive parameters domain (base :| [step])
    prepared <- replayInductive foundation mixed
    assertEqual "carrier retains parameter type order"
        (foldr TyArrow TySet (snd <$> parameters))
        (Inductive.typedInductiveCarrierType prepared)
    assertEqual "guard quantifies the mixed telescope in source order"
        (foldr CForall (CImp (CAnd (CBound 1) bound) bound) (snd <$> binders))
        (frozenCoreTerm (Inductive.typedInductiveGuardTargets prepared Vector.! 0))
    assertBool "same identities cannot be read at a different type"
        (isLeft (Inductive.prepareTypedInductive testGlobalType foundation "wrong_types"
            (mixed {Inductive.directInductiveParams =
                [(identity, TySet) | (identity, _) <- parameters]})))
    assertBool "rule locals remain Set-valued"
        (isLeft (Inductive.prepareTypedInductive testGlobalType foundation "typed_local"
            (mixed {Inductive.directInductiveClauses =
                base {Inductive.directClauseVariables = [(fst local, TyProp)]} :| []})))
    wrongContext <- checkedInductiveScoped (snd <$> parameters) (CIntrinsic Empty)
    assertBool "template context order is checked"
        (isLeft (Inductive.prepareCheckedInductiveTerm testGlobalType parameters wrongContext))
  where
    checkedInductiveScoped context term =
        expectRight
            (checkScopedCanonicalCore
                testGlobalType
                context
                term)

    checkedInductiveTerm variables context term = do
        scoped <- checkedInductiveScoped context term
        expectRight
            (Inductive.prepareCheckedInductiveTerm
                testGlobalType
                variables
                scoped)

    replayInductive foundation inductive = do
        prepared <-
            expectRight
                (Inductive.prepareTypedInductive
                    testGlobalType
                    foundation
                    "direct_inductive"
                    inductive)
        imports <-
            traverse
                (expectRight . derivationImportJudgement)
                (Inductive.typedInductiveGuardTargets
                    prepared)
        traverse_
            (\fact -> do
                replayed <-
                    expectRight
                        (replayKernelDerivation
                            foundation
                            defaultKernelReplayLimits
                            testGlobalType
                            imports
                            (Inductive.typedInductiveFactTarget
                                fact)
                            (Inductive.typedInductiveFactDerivation
                                fact))
                assertEqual
                    "replay target"
                    (Inductive.typedInductiveFactTarget
                        fact)
                    (replayedKernelTarget replayed))
            (Inductive.typedInductiveFacts
                prepared)
        pure prepared

rejectsAlteredSetLfpApplications :: Assertion
rejectsAlteredSetLfpApplications = do
    foundation <-
        expectRight Foundation.checkedFoundation
    ( domain
        , operator
        , predicate
        , _element
        , _fixedPoint
        , _closedPremise
        , boundedPremise
        , _monotonePremise
        , _memberPremise
        , _closurePremise
        ) <-
            setLfpFixture
    falsum <-
        checkedScoped [] CFalsum
    assertEqual
        "altered leastness premise"
        (Left
            (SetLfp.SetLfpRulePremiseMismatch
                Foundation.SetLfpLeast
                0))
        (SetLfp.setLfpLeast
            foundation
            emptyGlobalTyping
            domain
            operator
            domain
            falsum
            boundedPremise)
    assertEqual
        "operator type mismatch"
        (Left
            (SetLfp.SetLfpRuleArgumentTypeMismatch
                Foundation.SetLfpBound
                1
                (TySet `TyArrow` TySet)
                (TySet `TyArrow` TyProp)))
        (SetLfp.setLfpBound
            foundation
            emptyGlobalTyping
            domain
            predicate)
    bound <-
        expectRight
            (SetLfp.setLfpBound
                foundation
                emptyGlobalTyping
                domain
                operator)
    wrongTarget <-
        checkedClosed CFalsum
    assertEqual
        "altered replay target"
        (Left KernelReplayTargetMismatch)
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                wrongTarget
                (setLfpBoundDerivation
                    domain
                    operator))
    assertEqual
        "the direct bound remains well formed"
        TyProp
        (scopedCoreType bound)

setLfpFixture
    :: IO
        ( ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        , ScopedCheckedCore Void
        )
setLfpFixture = do
    domain <-
        checkedScoped [] (CIntrinsic Empty)
    operator <-
        checkedScoped []
            (CLam TySet (CBound 0))
    predicate <-
        checkedScoped []
            (CLam TySet
                (CEq TySet
                    (CBound 0)
                    (CBound 0)))
    element <-
        checkedScoped [] (CIntrinsic Empty)
    fixedPoint <-
        expectRight
            (SetLfp.setLfpTerm
                emptyGlobalTyping
                domain
                operator)
    operatorDomain <-
        checkedScoped []
            (CApp
                (scopedCoreTerm operator)
                (scopedCoreTerm domain))
    closedPremise <-
        expectRight
            (SetLfp.subsetProposition
                emptyGlobalTyping
                operatorDomain
                domain)
    boundedPremise <-
        expectRight
            (SetLfp.subsetProposition
                emptyGlobalTyping
                domain
                domain)
    monotonePremise <-
        expectRight
            (SetLfp.boundedMonoProposition
                emptyGlobalTyping
                domain
                operator)
    memberPremise <-
        expectRight
            (SetLfp.memberProposition
                emptyGlobalTyping
                element
                fixedPoint)
    closurePremise <-
        expectRight
            (SetLfp.inductionClosureProposition
                emptyGlobalTyping
                domain
                operator
                predicate)
    pure
        ( domain
        , operator
        , predicate
        , element
        , fixedPoint
        , closedPremise
        , boundedPremise
        , monotonePremise
        , memberPremise
        , closurePremise
        )

rejectsInvalidScopedReplay :: Assertion
rejectsInvalidScopedReplay = do
    foundation <-
        expectRight Foundation.checkedFoundation
    proposition <-
        checkedClosed
            (CEq TySet
                (CIntrinsic Empty)
                (CIntrinsic Empty))
    boundSet <-
        checkedScoped [TySet] (CBound 0)
    assertEqual
        "missing local hypothesis"
        (Left
            (KernelReplayHypothesisOutOfBounds
                (hypothesisIx 0)))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                proposition
                (localHypothesisDerivation
                    (hypothesisIx 0)))
    assertEqual
        "stored term from another lexical context"
        (Left
            (KernelReplayStoredContextMismatch
                []
                [TySet]))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                proposition
                (scopedEqualityReflexivityDerivation
                    boundSet))
    expanded <-
        checkedScoped []
            (CEq TySet
                (CApp
                    (CLam TySet (CBound 0))
                    (CIntrinsic Empty))
                (CIntrinsic Empty))
    context <- expectRight
        (KernelProof.scopedProofContext foundation emptyGlobalTyping [] [])
    emptySet <- checkedScoped [] (CIntrinsic Empty)
    sourceProof <- expectRight (KernelProof.equalityReflexivityProof context emptySet)
    let (rejected, remainingPool) = KernelProof.conversionProofWithPool
            (Conversion.conversionPool 0) context sourceProof expanded
    assertEqual "a zero pool cannot publish conversion evidence"
        (Left (KernelProof.ProofConversionLimitExhausted
            KernelProof.ProofConversionAggregatePool (Conversion.conversionLimit 0)))
        (KernelProof.builtProofStatement <$> rejected)
    assertEqual "exhaustion returns the depleted pool"
        (Conversion.conversionPool 0) remainingPool
    oneNode <-
        expectRight (kernelReplayLimits 1 10)
    let propositionScoped =
            embedClosedCore [] proposition
        identityTarget =
            unsafeClosed
                (CImp
                    (frozenCoreTerm proposition)
                    (frozenCoreTerm proposition))
    assertEqual
        "replay node limit"
        (Left
            (KernelReplayNodeLimitExceeded 1))
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                oneNode
                emptyGlobalTyping
                Vector.empty
                identityTarget
                (implicationIntroductionDerivation
                    propositionScoped
                    (localHypothesisDerivation
                        (hypothesisIx 0))))

measuresReplayWork :: Assertion
measuresReplayWork = do
    foundation <- expectRight Foundation.checkedFoundation
    oneNode <- expectRight (kernelReplayLimits 1 10)
    proposition <- checkedScoped [] CFalsum
    conjunction <- checkedScoped [] (CAnd CFalsum CFalsum)
    implication <- checkedScoped [] (CImp CFalsum CFalsum)
    let hypothesis = localHypothesisDerivation (hypothesisIx 0)
        joined = conjunctionIntroductionDerivation hypothesis hypothesis
        examples =
            [ (defaultKernelReplayLimits, proposition, hypothesis)
            , (defaultKernelReplayLimits, conjunction, joined)
            , (defaultKernelReplayLimits, proposition, conjunctionLeftEliminationDerivation joined)
            , (defaultKernelReplayLimits, implication, implicationIntroductionDerivation proposition hypothesis)
            , (defaultKernelReplayLimits, implication, joined)
            , (oneNode, conjunction, joined)
            , (defaultKernelReplayLimits, proposition, localHypothesisDerivation (hypothesisIx 1))
            ]
    for_ examples \(limits, target, derivation) -> do
        let ordinary = replayScopedKernelDerivation foundation limits emptyGlobalTyping
                Vector.empty (Vector.singleton proposition) target derivation
            (measured, work) = replayScopedKernelDerivationMeasured foundation limits emptyGlobalTyping
                Vector.empty (Vector.singleton proposition) target derivation
            result value = (replayedScopedKernelTarget value,
                replayedScopedKernelExternalHypothesisUses value,
                replayedScopedKernelNodeCount value, replayedScopedKernelMaximumDepth value)
        assertEqual "measurement uses the same replay and error ordering" (result <$> ordinary) (result <$> measured)
        assertBool "entry and rule work survives rejection" (replayWorkCore work > 0)
        assertBool "attempted replay nodes survive rejection" (replayWorkNodes work > 0)
    growth <- for [16,32,64] \width -> do
        large <- checkedScoped [] (foldr CAnd CFalsum (replicate width CTruth))
        let derivation = conjunctionLeftEliminationDerivation (localHypothesisDerivation (hypothesisIx 0))
        target <- checkedScoped [] CTruth
        let (result, work) = replayScopedKernelDerivationMeasured foundation defaultKernelReplayLimits emptyGlobalTyping
                Vector.empty (Vector.singleton large) target derivation
        _ <- expectRight result
        assertEqual "projection node count" 2 (replayWorkNodes work)
        pure (replayWorkCore work)
    assertBool "large input validation is visible despite constant replay node count"
        (and (zipWith (<) growth (drop 1 growth)))

rejectsTargetMismatch :: Assertion
rejectsTargetMismatch = do
    foundation <-
        expectRight Foundation.checkedFoundation
    operand <-
        expectRight
            (checkCanonicalCore
                emptyGlobalTyping
                (CIntrinsic Empty))
    wrongTarget <-
        expectRight
            (checkCanonicalCore
                emptyGlobalTyping
                (CImp CFalsum CFalsum))
    assertEqual
        "the expected target is comparison input, not evidence"
        (Left KernelReplayTargetMismatch)
        (replayedKernelTarget
            <$> replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                wrongTarget
                (equalityReflexivityDerivation operand))

reassemblesLocalConjunctions :: Assertion
reassemblesLocalConjunctions = do
    foundation <- expectRight Foundation.checkedFoundation
    hypothesis <- checkedScoped []
        (KernelProof.conjunctionTerm first
            (KernelProof.conjunctionTerm second third))
    target <- checkedScoped []
        (KernelProof.conjunctionTerm third first)
    identity <- checkedScoped [] (CImp first first)
    missing <- checkedScoped []
        (KernelProof.conjunctionTerm first fourth)
    expectRight
        (KernelProof.validateStructuralLogicalComposition
            foundation emptyGlobalTyping target [hypothesis])
    expectRight
        (KernelProof.validateStructuralLogicalComposition
            foundation emptyGlobalTyping identity [])
    case KernelProof.validateStructuralLogicalComposition
            foundation emptyGlobalTyping missing [hypothesis] of
        Left KernelProof.ProofStructuralCompositionMismatch{} ->
            pure ()
        result ->
            assertFailure
                ("expected unavailable conjunction closure, got "
                    <> show result)
  where
    emptySet = CIntrinsic Empty
    pair = CApp (CApp (CIntrinsic PairSet) emptySet) emptySet
    union = CApp (CIntrinsic FamilyUnion) emptySet
    member = CApp (CApp (CIntrinsic Member) emptySet) emptySet
    first = CEq TySet emptySet emptySet
    second = CEq TySet emptySet pair
    third = CEq TySet emptySet union
    fourth = member

characterizesConjunctionConversionFallback :: Assertion
characterizesConjunctionConversionFallback = do
    foundation <- expectRight Foundation.checkedFoundation
    forM_ cases \(scenario, premiseTerms, targetTerm, used) -> do
        hypotheses <- traverse (checkedScoped [TySet]) premiseTerms
        target <- checkedScoped [TySet] targetTerm
        context <- expectRight (KernelProof.scopedProofContext
            foundation emptyGlobalTyping [TySet] hypotheses)
        premises <- expectRight (traverse
            (KernelProof.indexedHypothesisProof context . hypothesisIx)
            [0 .. fromIntegral (length hypotheses) - 1])
        candidate <- expectRight
            (KernelProof.conjunctionAssumptionProof context premises target)
        proof <- maybe (assertFailure (scenario <> " produced no proof")) pure candidate
        assertEqual (scenario <> " exact checked target")
            target (KernelProof.builtProofStatement proof)
        replayed <- expectRight (replayScopedKernelDerivation
            foundation defaultKernelReplayLimits emptyGlobalTyping
            Vector.empty (Vector.fromList hypotheses) target
            (KernelProof.builtProofDerivation proof))
        assertEqual (scenario <> " exact authority")
            (Set.singleton (hypothesisIx used))
            (replayedScopedKernelExternalHypothesisUses replayed)
        assertEqual (scenario <> " imports") Set.empty
            (replayedScopedKernelImportUses replayed)

    slow <- checkedScoped [TySet] slowTruth
    falsum <- checkedScoped [TySet] CFalsum
    target <- checkedScoped [TySet] CTruth
    context <- expectRight (KernelProof.scopedProofContext
        foundation emptyGlobalTyping [TySet] [slow, falsum])
    source <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    mismatch <- expectRight (KernelProof.indexedHypothesisProof context (hypothesisIx 1))
    assertEqual "the first candidate exhausts its ordinary operation allowance"
        (Left (KernelProof.ProofConversionLimitExhausted
            KernelProof.ProofConversionOperationLimit (Conversion.conversionLimit 2000000)))
        (KernelProof.builtProofStatement <$> KernelProof.conversionProof context source target)
    forM_ [1999999, 2000000, 2000001] $ \poolAmount -> do
        let limitAmount = min poolAmount 2000000
            owner = if poolAmount <= 2000000
                then KernelProof.ProofConversionAggregatePool
                else KernelProof.ProofConversionOperationLimit
            (outcome, remainder) = KernelProof.conversionProofWithPool
                (Conversion.conversionPool poolAmount) context source target
        assertEqual "the smaller allowance owns exhaustion, including ties"
            (Left (KernelProof.ProofConversionLimitExhausted
                owner (Conversion.conversionLimit limitAmount)))
            (KernelProof.builtProofStatement <$> outcome)
        assertEqual "exhaustion debits once before reporting its owner"
            (Conversion.conversionPool (poolAmount - limitAmount)) remainder
    assertEqual "ordinary non-convertibility means no assumption was found"
        (Right Nothing)
        (fmap (fmap KernelProof.builtProofStatement)
            (KernelProof.conjunctionAssumptionProof context [mismatch] target))
    assertEqual "search remembers exhaustion when no later candidate works"
        (Left (KernelProof.ProofConversionLimitExhausted
            KernelProof.ProofConversionOperationLimit (Conversion.conversionLimit 2000000)))
        (fmap (fmap KernelProof.builtProofStatement)
            (KernelProof.conjunctionAssumptionProof context [source, mismatch] target))
  where
    beta = CApp (CLam TyProp (CBound 0))
    slowTruth = CApp
        (foldr (\_ term -> CApp twice term)
            (CLam TyProp (CBound 0)) [1 .. 16 :: Int]) CTruth
    twice = CLam (TyArrow TyProp TyProp)
        (CLam TyProp (CApp (CBound 1) (CApp (CBound 1) (CBound 0))))
    p = CEq TySet (CBound 0) (CIntrinsic Empty)
    q = CNot p
    cases =
        [ ("reordered reusable projections", [CAnd p (CAnd q p)], CAnd q p, 0)
        , ("exact match before conversion", [beta CTruth, CTruth], CTruth, 1)
        , ("first convertible candidate", [beta CTruth, beta (beta CTruth)], CTruth, 0)
        , ("later match after non-convertibility", [CFalsum, beta CTruth], CTruth, 1)
        , ("later match after exhaustion", [slowTruth, beta CTruth], CTruth, 1)
        ]

characterizesConjunctionContextFailure :: Assertion
characterizesConjunctionContextFailure = do
    foundation <- expectRight Foundation.checkedFoundation
    let writtenTruth = CApp (CLam TyProp (CBound 0)) CTruth
    outer <- checkedScoped [TySet] writtenTruth
    local <- checkedScoped [] writtenTruth
    target <- checkedScoped [] CTruth
    outerContext <- expectRight (KernelProof.scopedProofContext
        foundation emptyGlobalTyping [TySet] [outer])
    context <- expectRight (KernelProof.scopedProofContext
        foundation emptyGlobalTyping [] [local])
    outerProof <- expectRight
        (KernelProof.indexedHypothesisProof outerContext (hypothesisIx 0))
    localProof <- expectRight
        (KernelProof.indexedHypothesisProof context (hypothesisIx 0))
    let expected = KernelProof.ProofConversionFailed
            (Conversion.ConversionInputFailure
                (Conversion.ConversionContextMismatch [TySet] []))
    assertEqual "lawful proof supplied at the wrong lexical context"
        (Left expected)
        (KernelProof.builtProofStatement <$>
            KernelProof.conversionProof context outerProof target)
    assertEqual "an input failure stops the fallback before a later candidate"
        (Left expected)
        (fmap (fmap KernelProof.builtProofStatement)
            (KernelProof.conjunctionAssumptionProof context [outerProof, localProof] target))

replaysScopedLocals :: Assertion
replaysScopedLocals = do
    foundation <- expectRight Foundation.checkedFoundation
    first <- checkedScoped [TySet]
        (CEq TySet (CBound 0) (CBound 0))
    second <- checkedScoped [TySet]
        (CEq TySet (CIntrinsic Empty) (CIntrinsic Empty))
    replayed <- expectRight
        (replayScopedKernelDerivation
            foundation
            defaultKernelReplayLimits
            emptyGlobalTyping
            Vector.empty
            (Vector.fromList [first, second])
            second
            (localHypothesisDerivation (hypothesisIx 1)))
    assertEqual
        "the exact source-level hypothesis is reported"
        (Set.singleton (hypothesisIx 1))
        (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual
        "the caller-owned scoped target is retained"
        second
        (replayedScopedKernelTarget replayed)
    assertEqual
        "changing local order changes the derivation meaning"
        (Left KernelReplayTargetMismatch)
        (replayedScopedKernelTarget
            <$> replayScopedKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                (Vector.fromList [second, first])
                second
                (localHypothesisDerivation (hypothesisIx 1)))
    let introducedOnly =
            implicationIntroductionDerivation
                first
                (localHypothesisDerivation (hypothesisIx 0))
    implication <- checkedScoped [TySet]
        (CImp (scopedCoreTerm first) (scopedCoreTerm first))
    introduced <- expectRight
        (replayScopedKernelDerivation
            foundation
            defaultKernelReplayLimits
            emptyGlobalTyping
            Vector.empty
            (Vector.singleton second)
            implication
            introducedOnly)
    assertEqual
        "derivation-local assumptions are not reported as external uses"
        Set.empty
        (replayedScopedKernelExternalHypothesisUses introduced)

assertReplayTarget
    :: Foundation.CheckedFoundation
    -> CanonicalTerm Void
    -> KernelDerivation Void
    -> Assertion
assertReplayTarget foundation expectedTerm derivation = do
    expected <-
        checkedClosed expectedTerm
    replayed <-
        expectRight
            (replayKernelDerivation
                foundation
                defaultKernelReplayLimits
                emptyGlobalTyping
                Vector.empty
                expected
                derivation)
    assertEqual
        "replayed exact target"
        expected
        (replayedKernelTarget replayed)
    let (summary, remaining) = countedKernelDerivationSourceUses
            (fromIntegral (replayedKernelNodeCount replayed)) derivation
    uses <- maybe (assertFailure "source summary exhausted" >> fail "missing summary") pure summary
    assertEqual "closed replay source-summary boundary" 0 remaining
    assertEqual "source summary agrees with closed replay imports"
        (replayedKernelImportUses replayed) (kernelSourceImportUses uses)
    assertEqual "closed replay has no external hypothesis references"
        Set.empty (kernelSourceExternalHypothesisUses uses)

checkedClosed
    :: CanonicalTerm Void
    -> IO (FrozenCheckedCore Void)
checkedClosed =
    expectRight . checkCanonicalCore emptyGlobalTyping

checkedScoped
    :: [CoreType]
    -> CanonicalTerm Void
    -> IO (ScopedCheckedCore Void)
checkedScoped context =
    expectRight
        . checkScopedCanonicalCore emptyGlobalTyping context

unsafeScoped
    :: [CoreType]
    -> CanonicalTerm Void
    -> ScopedCheckedCore Void
unsafeScoped context term =
    case checkScopedCanonicalCore emptyGlobalTyping context term of
        Left coreError ->
            impossible
                ("invalid static kernel fixture: "
                    <> show coreError)
        Right checked ->
            checked

unsafeClosed
    :: CanonicalTerm Void
    -> FrozenCheckedCore Void
unsafeClosed term =
    case checkCanonicalCore emptyGlobalTyping term of
        Left coreError ->
            impossible
                ("invalid static closed kernel fixture: "
                    <> show coreError)
        Right checked ->
            checked

expectRight
    :: Show error
    => Either error value
    -> IO value
expectRight =
    either
        (assertFailure . show)
        pure
