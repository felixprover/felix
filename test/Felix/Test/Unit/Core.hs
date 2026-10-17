{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Core (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.StableCode qualified as StableCode
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (GlobalTyping, emptyGlobalTyping)
import Felix.Checking.Record qualified as Record
import Felix.Checking.SetConstruction
import Felix.Checking.Identity (ObjectId)
import Felix.Test.Support.GlobalTyping

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.Vector qualified as Vector
import Data.Word (Word)
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)


testGlobalFixture :: GlobalTypingFixture
testGlobalFixture =
    globalTypingFixture
        [ TySet
        , TySet `TyArrow` (TySet `TyArrow` TySet)
        ]

testGlobalType :: GlobalTyping ObjectId
testGlobalType = fixtureGlobalTyping testGlobalFixture

testGlobal, testPairGlobal :: ObjectId
(testGlobal, testPairGlobal) =
    case fixtureObjectIds testGlobalFixture of
        [single, pair] -> (single, pair)
        _ -> error "the checked-core global fixture changed arity"

unitTests :: TestTree
unitTests =
    testGroup "Checked core"
        [ testCase "bounds global collection across binders and repeated references" countsGlobalCollection
        , testCase "constructs counted pointwise bodies and abstractions without re-admission"
            constructsPointwiseBodies
        , testCase "aligns checked scopes with one bounded capture-safe shift"
            alignsCountedScopes
        , testCase "counts canonical ordering without changing constructor or operand order"
            countsCanonicalOrdering
        , testCase
            "uses the frozen core-intrinsic code table"
            usesFrozenCoreIntrinsicCodes
        , testCase
            "splits canonical applications in argument order"
            splitsCanonicalApplications
        , testCase
            "builds truth-eliding right-associated conjunctions"
            buildsCanonicalConjunctions
        , testCase
            "rechecks canonical terms without unchecked construction"
            rechecksCanonicalTerms
        , testCase
            "admits checked terms only when destination globals are visible"
            admitsVisibleCheckedTerms
        , testCase
            "counts scoped admission by visited canonical constructors"
            countsScopedAdmission
        , testCase
            "preserves left-to-right canonical checking failures"
            preservesCanonicalFailureOrder
        , testCase
            "checks and freezes native logical forms"
            checksNativeLogicalForms
        , testCase
            "checks scoped canonical weakening and substitution"
            checksScopedCanonicalOperations
        , testCase
            "splits checked equality operands without changing syntax or scope"
            splitsScopedEquality
        , testCase
            "splits checked membership without reducing its operands"
            splitsScopedMembership
        , testCase
            "replaces exact checked proposition occurrences capture-safely"
            replacesScopedPropositionOccurrences
        , testCase
            "rejects overflowing checked weakening depths"
            rejectsOverflowingCheckedWeakeningDepths
        , testCase
            "counts exact identity, checking, shifting, and substitution"
            countsCoreWork
        , testCase "transforms every constructor with exact capture and work boundaries"
            transformsCanonicalBindings
        , testCase "substitutes abbreviation formals simultaneously with shared weakening"
            substitutesCanonicalPrefix
        , testCase "preserves inference policy, error order, and exact work vectors"
            preservesInferenceVectors
        , testCase
            "instantiates checked prefixes with partial source-order slots"
            instantiatesCheckedPrefixes
        , testCase
            "rejects invalid checked substitution premises before traversal"
            rejectsCheckedInstantiationPremises
        , testCase
            "charges checked transformations through exact exhaustion"
            countsCheckedTransformations
        , testCase
            "retains one counted checked occurrence analysis"
            retainsCheckedOccurrenceAnalysis
        , testCase
            "exposes every exact checked occurrence view"
            reconstructsCheckedOccurrenceViews
        , testCase
            "rebases retained ground occurrences without rechecking"
            rebasesCheckedOccurrences
        , testCase
            "analyses checked occurrences beneath a logical binder scope"
            analysesScopedOccurrencesUnderBinders
        , testCase
            "builds set-induction hypotheses from the complete property"
            buildsSetInductionHypotheses
        , testCase
            "specializes the checked separation characteristic"
            specializesCheckedSeparationCharacteristic
        , testCase
            "specializes the checked replacement characteristic"
            specializesCheckedReplacementCharacteristic
        , testCase
            "derives named construction views from checked components"
            derivesNamedConstructionViews
        , testPropertyNamed
            "retained occurrence rebasing agrees with checked closure"
            "prop_occurrenceRebaseAgrees"
            prop_occurrenceRebaseAgrees
        , testPropertyNamed
            "checked simultaneous substitution agrees with sequential reference"
            "prop_checkedPrefixInstantiationAgrees"
            prop_checkedPrefixInstantiationAgrees
        ]

constructsPointwiseBodies :: Assertion
constructsPointwiseBodies = do
    let function = TyArrow TySet TySet
        cases =
            [ ([], CGlobal testPairGlobal)
            , ([function, TySet], CBound 0)
            , ([TySet], CLam TySet (CBound 1))
            , ([], CLam function (CBound 0))
            , ([TyProp], CLam TySet (CForall TySet (CBound 2)))
            ]
        check types = expectRight . checkScopedCanonicalCore testGlobalType types
        boundary expected operation = do
            let (result, remaining) = operation 100000
                used = 100000 - remaining
            assertEqual "counted and uncounted construction agree" (Right expected) result
            assertEqual "exact structural allowance" (Right expected, 0) (operation used)
            assertEqual "one-short construction returns no partial evidence"
                (Left CountedCoreStructuralWorkExhausted, 0) (operation (used - 1))
    for_ cases \(types, term) -> do
        operand <- check types term
        body <- maybe (assertFailure "expected a function" >> fail "unreachable") pure
            (pointwiseBodyScopedCore operand)
        assertEqual "fresh application is independently well typed" (Right body)
            (checkScopedCanonicalCore testGlobalType (scopedCoreContext body) (scopedCoreTerm body))
        boundary (Just body) (\work -> countedPointwiseBodyScopedCore work operand)
        case scopedCoreType operand of
            TyArrow domain _ -> do
                boundary (abstractScopedCore domain body)
                    (\work -> countedAbstractScopedCore work domain body)
                boundary Nothing (\work -> countedAbstractScopedCore work
                    (TyArrow domain domain) body)
            _ -> assertFailure "pointwise construction accepted a non-arrow"
        boundary (equalScopedCore body body) (\work -> countedEqualScopedCore work body body)
        boundary Nothing (\work -> countedEqualScopedCore work operand body)
    truth <- check [] CTruth
    boundary Nothing (\work -> countedPointwiseBodyScopedCore work truth)
    boundary Nothing (\work -> countedAbstractScopedCore work TySet truth)
    integer <- check [] (COpaqueInteger 0)
    boundary Nothing (\work -> countedEqualScopedCore work truth integer)

splitsCanonicalApplications :: Assertion
splitsCanonicalApplications = do
    let first = CGlobal testGlobal
        second = CIntrinsic Empty
        headTerm = CGlobal testPairGlobal
        application = CApp (CApp headTerm first) second
    assertEqual
        "application spine"
        (headTerm, [first, second])
        (canonicalApplicationSpine application)
    assertEqual
        "bare head"
        (headTerm, [])
        (canonicalApplicationSpine headTerm)

buildsCanonicalConjunctions :: Assertion
buildsCanonicalConjunctions = do
    let first = CGlobal testGlobal
        second = CIntrinsic Empty
        third = COpaqueInteger 3
    assertEqual
        "empty conjunction"
        CTruth
        (canonicalConjunction ([] :: [CanonicalTerm ObjectId]))
    assertEqual
        "truth-eliding singleton"
        first
        (canonicalConjunction [CTruth, first, CTruth])
    assertEqual
        "right-associated conjunction"
        (CAnd first (CAnd second third))
        (canonicalConjunction [first, second, third])

splitsScopedEquality :: Assertion
splitsScopedEquality = do
    forM_ equalities \(context, operandType, leftTerm, rightTerm) -> do
        proposition <- checked context (CEq operandType leftTerm rightTerm)
        case splitScopedEquality proposition of
            Nothing -> assertFailure "a checked equality did not split"
            Just (actualType, left, right) -> do
                assertEqual "shared operand type" operandType actualType
                assertEqual "left syntax, type, and unchanged context"
                    (leftTerm, operandType, context)
                    (scopedCoreTerm left, scopedCoreType left, scopedCoreContext left)
                assertEqual "right syntax, type, and unchanged context"
                    (rightTerm, operandType, context)
                    (scopedCoreTerm right, scopedCoreType right, scopedCoreContext right)
                assertEqual "checked operands reconstruct the original equality"
                    (Just proposition) (equalScopedCore left right)
    forM_ otherRoots \term -> do
        root <- checked [] term
        assertEqual "only a syntactic equality root splits"
            Nothing (splitScopedEquality root)
  where
    checked context term =
        expectRight (checkScopedCanonicalCore testGlobalType context term)
    functionType = TyArrow TySet TySet
    equalities =
        [ ( []
          , TySet
          , CApp (CLam TySet (CBound 0)) (CGlobal testGlobal)
          , COpaqueInteger 0
          )
        , ([TyProp, TySet], TyProp, CBound 0, CNot CTruth)
        , ( [TyProp, TySet, functionType]
          , functionType
          , CBound 2
          , CLam TySet (CBound 0)
          )
        ]
    otherRoots =
        [ CTruth
        , CIntrinsic Empty
        , CLam TySet (CBound 0)
        , CNot (CEq TySet (COpaqueInteger 0) (COpaqueInteger 0))
        , CApp (CLam TyProp (CBound 0)) (CEq TyProp CTruth CFalsum)
        ]

splitsScopedMembership :: Assertion
splitsScopedMembership = do
    let context = [TySet]
        elementTerm = CApp (CLam TySet (CBound 0)) (CBound 0)
        setTerm = CApp (CLam TySet (CBound 0)) (CGlobal testGlobal)
        member = CApp (CApp (CIntrinsic Member) elementTerm) setTerm
    proposition <- checked context member
    case splitScopedMembership proposition of
        Nothing -> assertFailure "a checked membership did not split"
        Just (element, set) -> do
            assertEqual "element keeps its written redex and ambient context"
                (elementTerm, context) (scopedCoreTerm element, scopedCoreContext element)
            assertEqual "set keeps its written redex and ambient context"
                (setTerm, context) (scopedCoreTerm set, scopedCoreContext set)
            assertEqual "checked operands reconstruct the original membership"
                (Just proposition) (memberScopedCore element set)
    forM_
        [ CTruth
        , CApp (CIntrinsic Member) elementTerm
        , CEq TySet elementTerm setTerm
        , CApp (CLam TyProp (CBound 0)) member
        ] \term -> do
            root <- checked context term
            assertEqual "only a syntactic membership root splits"
                Nothing (splitScopedMembership root)
  where
    checked context term =
        expectRight (checkScopedCanonicalCore testGlobalType context term)

replacesScopedPropositionOccurrences :: Assertion
replacesScopedPropositionOccurrences = do
    target <- checked [] (CIntrinsic Empty)
    replacement <- checked [] (CGlobal testGlobal)
    repeated <- checked []
        (CEq TySet (CIntrinsic Empty) (CIntrinsic Empty))
    repeatedResult <- expectReplacement target replacement repeated
    assertEqual "every top-level occurrence is replaced"
        (CEq TySet (CGlobal testGlobal) (CGlobal testGlobal))
        (scopedCoreTerm
            (scopedCoreReplacementResult repeatedResult))
    assertEqual "the replacement predicate recovers the original"
        (scopedCoreTerm repeated)
        (betaNormalizeCanonical
            (CApp
                (scopedCoreTerm
                    (scopedCoreReplacementAbstraction repeatedResult))
                (scopedCoreTerm target)))
    assertEqual "the replacement predicate produces the direct contractum"
        (scopedCoreTerm
            (scopedCoreReplacementResult repeatedResult))
        (betaNormalizeCanonical
            (CApp
                (scopedCoreTerm
                    (scopedCoreReplacementAbstraction repeatedResult))
                (scopedCoreTerm replacement)))

    quantified <- checked []
        (CForall TySet
            (CEq TySet (CIntrinsic Empty) (CBound 0)))
    quantifiedResult <- expectReplacement target replacement quantified
    assertEqual "replacement shifts safely beneath a quantifier"
        (CForall TySet
            (CEq TySet (CGlobal testGlobal) (CBound 0)))
        (scopedCoreTerm
            (scopedCoreReplacementResult quantifiedResult))

    exactShape <- checked []
        (Record.recordExactShape [] (CIntrinsic Empty))
    exactResult <- expectReplacement target replacement exactShape
    assertEqual "exact-record syntax remains directly recognizable"
        (Just (CGlobal testGlobal, []))
        (Record.recognizeRecordExactGlobalShape
            (scopedCoreReplacementResult exactResult))

    absent <- checked [] CTruth
    case replaceScopedCoreOccurrence target replacement absent of
        Right Nothing -> pure ()
        _ -> assertFailure "absence was not returned as Right Nothing"
    boundTarget <- checked [TySet,TySet] (CBound 0)
    boundReplacement <- checked [TySet,TySet] (CBound 1)
    setFunction <- checked [TySet,TySet]
        (CLam TySet (CApp (CApp (CIntrinsic OrderedPair) (CBound 1)) (CBound 0)))
    functionResult <- expectReplacement boundTarget boundReplacement setFunction
    expectedFunction <- checked [TySet,TySet]
        (CLam TySet (CApp (CApp (CIntrinsic OrderedPair) (CBound 2)) (CBound 0)))
    assertEqual "set-valued lambda replacement preserves its local binder" expectedFunction
        (scopedCoreReplacementResult functionResult)
    let abstraction = scopedCoreReplacementAbstraction functionResult
    assertEqual "the generalized abstraction is independently well typed"
        (Right abstraction)
        (checkScopedCanonicalCore testGlobalType [TySet,TySet] (scopedCoreTerm abstraction))
    replacementInBinder <- checked [TySet] (CBound 0)
    assertReplacementError "contexts must agree"
        ScopedOccurrenceReplacementContextMismatch
        (replaceScopedCoreOccurrence
            target replacementInBinder repeated)
    propositionReplacement <- checked [] CTruth
    assertReplacementError "target and replacement types must agree"
        (ScopedOccurrenceReplacementTypeMismatch TySet TyProp)
        (replaceScopedCoreOccurrence
            target propositionReplacement repeated)
    replacedTerm <- expectReplacement target replacement target
    assertEqual "checked term replacement preserves the result type" TySet
        (scopedCoreType (scopedCoreReplacementResult replacedTerm))
    assertEqual "replacing the whole set term gives the replacement" replacement
        (scopedCoreReplacementResult replacedTerm)
  where
    checked context term =
        expectRight (checkScopedCanonicalCore testGlobalType context term)

    expectReplacement target replacement proposition =
        case replaceScopedCoreOccurrence
                target replacement proposition of
            Right (Just result) -> do
                let run work = countedReplaceScopedCoreOccurrence work target replacement proposition
                    (counted, remaining) = run 100000
                    used = 100000 - remaining
                    compareResult = \case
                        Right (Just actual) -> do
                            assertEqual "counted replacement preserves the checked abstraction"
                                (scopedCoreReplacementAbstraction result) (scopedCoreReplacementAbstraction actual)
                            assertEqual "counted replacement preserves the direct contractum"
                                (scopedCoreReplacementResult result) (scopedCoreReplacementResult actual)
                        _ -> assertFailure "counted occurrence replacement failed"
                compareResult counted
                compareResult (fst (run used))
                for_ [0 .. used - 1] \work -> do
                    let (short, after) = run work
                    assertEqual "failed abstraction/substitution keeps its debit" 0 after
                    case short of
                        Left CountedCoreStructuralWorkExhausted -> pure ()
                        _ -> assertFailure "an incomplete occurrence replacement escaped"
                pure result
            result ->
                result `seq`
                    assertFailure "an exact occurrence was not replaced"
                    >> fail "unreachable"

    assertReplacementError message expected = \case
        Left actual -> assertEqual message expected actual
        Right _ ->
            assertFailure (message <> ": replacement unexpectedly succeeded")

admitsVisibleCheckedTerms :: Assertion
admitsVisibleCheckedTerms = do
    let olderTyping =
            fixtureGlobalTyping (globalTypingFixture [TySet])
    frozen <- expectRight
        (checkCanonicalCore testGlobalType (CGlobal testPairGlobal))
    scoped <- expectRight
        (checkScopedCanonicalCore
            testGlobalType
            [TySet]
            (CGlobal testPairGlobal))
    assertEqual "current snapshot admits a closed checked term"
        (Right frozen)
        (admitFrozenCheckedCore testGlobalType frozen)
    assertEqual "older snapshot rejects a closed checked term"
        (Left UnknownCoreGlobal)
        (admitFrozenCheckedCore olderTyping frozen)
    assertEqual "current snapshot admits a scoped checked term"
        (Right scoped)
        (admitScopedCheckedCore testGlobalType scoped)
    assertEqual "older snapshot rejects a scoped checked term"
        (Left UnknownCoreGlobal)
        (admitScopedCheckedCore olderTyping scoped)

countsScopedAdmission :: Assertion
countsScopedAdmission = do
    let term =
            CImp
                (CEq TySet
                    (CGlobal testGlobal)
                    (CGlobal testGlobal))
                (CAnd CTruth (CNot CFalsum))
        nodeCount = canonicalNodeCount term
        surplus = nodeCount + 7
    checked <-
        expectRight
            (checkScopedCanonicalCore testGlobalType [] term)

    assertEqual "counted and ordinary admission agree on success"
        (Right checked)
        (fst
            (countedAdmitScopedCheckedCore
                testGlobalType surplus checked))
    assertEqual "successful admission charges every repeated occurrence"
        (Right checked, 7)
        (countedAdmitScopedCheckedCore
            testGlobalType surplus checked)
    assertEqual "exact constructor budget succeeds"
        (Right checked, 0)
        (countedAdmitScopedCheckedCore
            testGlobalType nodeCount checked)
    for_ [0 .. nodeCount - 1] \prefix ->
        assertEqual
            ("constructor prefix " <> show prefix <> " exhausts exactly")
            (Left CountedCoreStructuralWorkExhausted, 0)
            (countedAdmitScopedCheckedCore
                testGlobalType prefix checked)

    let repeated = CEq TySet
            (CGlobal testGlobal)
            (CGlobal testGlobal)
    repeatedChecked <-
        expectRight
            (checkScopedCanonicalCore testGlobalType [] repeated)
    assertEqual "repeated globals are charged by occurrence, not identity"
        (Right repeatedChecked, 0)
        (countedAdmitScopedCheckedCore
            testGlobalType
            (canonicalNodeCount repeated)
            repeatedChecked)
    assertEqual "one-short repeated occurrence is not deduplicated"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedAdmitScopedCheckedCore
            testGlobalType
            (canonicalNodeCount repeated - 1)
            repeatedChecked)

    let orderFixture = globalTypingFixture [TySet, TySet]
        richTyping = fixtureGlobalTyping orderFixture
        narrowTyping =
            fixtureGlobalTyping (globalTypingFixture [TySet])
        emptyOrderTyping =
            fixtureGlobalTyping (globalTypingFixture [])
        (visibleGlobal, missingGlobal) =
            case fixtureObjectIds orderFixture of
                [visible, missing] -> (visible, missing)
                _ -> error "admission order fixture changed arity"
        orderedMissing =
            CEq TySet
                (CGlobal visibleGlobal)
                (CGlobal missingGlobal)
    orderedChecked <-
        expectRight
            (checkScopedCanonicalCore richTyping [] orderedMissing)
    assertEqual "ordinary admission rejects the narrower snapshot"
        (Left UnknownCoreGlobal)
        (admitScopedCheckedCore narrowTyping orderedChecked)
    assertEqual "a missing right global is reached after the visible left"
        (Left (CountedCoreOperationFailed UnknownCoreGlobal), 4)
        (countedAdmitScopedCheckedCore
            narrowTyping 7 orderedChecked)
    assertEqual "exhaustion charges before inspecting the missing global"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedAdmitScopedCheckedCore
            narrowTyping 2 orderedChecked)
    assertEqual "the charged missing global reports its ordinary error"
        (Left (CountedCoreOperationFailed UnknownCoreGlobal), 0)
        (countedAdmitScopedCheckedCore
            narrowTyping 3 orderedChecked)
    assertEqual "the first missing global stops left-to-right traversal"
        (Left (CountedCoreOperationFailed UnknownCoreGlobal), 5)
        (countedAdmitScopedCheckedCore
            emptyOrderTyping 7 orderedChecked)

    let deepType =
            foldr TyArrow TySet (replicate 256 TySet)
    shallowOpen <-
        expectRight
            (checkScopedCanonicalCore
                emptyGlobalTyping [TySet] (CBound 0))
    deepOpen <-
        expectRight
            (checkScopedCanonicalCore
                emptyGlobalTyping
                (deepType : replicate 512 TyProp)
                (CBound 0))
    assertEqual "open admission does not inspect a short context"
        (Right shallowOpen, 0)
        (countedAdmitScopedCheckedCore
            emptyGlobalTyping 1 shallowOpen)
    assertEqual "open admission does not inspect a large context or type"
        (Right deepOpen, 0)
        (countedAdmitScopedCheckedCore
            emptyGlobalTyping 1 deepOpen)

    shallowAnnotation <-
        expectRight
            (checkScopedCanonicalCore
                emptyGlobalTyping [] (CLogicalSelect TySet))
    deepAnnotation <-
        expectRight
            (checkScopedCanonicalCore
                emptyGlobalTyping [] (CLogicalSelect deepType))
    assertEqual "small annotation has one structural node"
        (Right shallowAnnotation, 0)
        (countedAdmitScopedCheckedCore
            emptyGlobalTyping 1 shallowAnnotation)
    assertEqual "large annotation has the same admission cost"
        (Right deepAnnotation, 0)
        (countedAdmitScopedCheckedCore
            emptyGlobalTyping 1 deepAnnotation)

canonicalNodeCount :: CanonicalTerm global -> Word
canonicalNodeCount = \case
    CBound{} -> 1
    CGlobal{} -> 1
    CIntrinsic{} -> 1
    CLogicalSelect{} -> 1
    COpaqueInteger{} -> 1
    CApp function argument ->
        1 + canonicalNodeCount function + canonicalNodeCount argument
    CLam _binderType body ->
        1 + canonicalNodeCount body
    CFalsum -> 1
    CTruth -> 1
    CNot proposition ->
        1 + canonicalNodeCount proposition
    CAnd left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    COr left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    CImp premise conclusion ->
        1 + canonicalNodeCount premise + canonicalNodeCount conclusion
    CEq _operandType left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    CForall _binderType body ->
        1 + canonicalNodeCount body
    CExists _binderType body ->
        1 + canonicalNodeCount body

alignsCountedScopes :: Assertion
alignsCountedScopes = do
    original <- expectRight (checkScopedCanonicalCore emptyGlobalTyping [TySet]
        (CLam TySet (CEq TySet (CBound 0) (CBound 1))))
    let prefix = [TyProp, TyArrow TySet TyProp, TySet]
        target = prefix <> [TySet]
        expected = foldr weakenCheckedScopedCore original prefix
        run allowance = countedAlignScopedCore allowance target original
        (answer, remaining) = run 1000
        used = 1000 - remaining
    assertEqual "one shift agrees with successive checked weakenings" (Right (Just expected)) answer
    assertEqual "alignment exact boundary" (answer, 0) (run used)
    assertEqual "alignment retains exhaustion rather than an incomplete term"
        (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    for_ [[], [TyProp], [TySet, TyProp]] \invalid ->
        assertEqual "incompatible contexts are distinct from exhaustion" (Right Nothing)
            (fst (countedAlignScopedCore 1000 invalid original))
    let largePrefix = replicate 100 TySet <> [TySet]
    assertEqual "context traversal itself is bounded"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedAlignScopedCore 10 largePrefix original)

    nested <- expectRight (checkScopedCanonicalCore emptyGlobalTyping [TySet, TySet]
        (CEq TySet (CBound 0) (CBound 1)))
    expectedNested <- expectRight (checkScopedCanonicalCore emptyGlobalTyping [TySet, TyProp, TySet]
        (CEq TySet (CBound 0) (CBound 2)))
    let runNested allowance = countedAlignScopedCoreAt allowance 1 [TySet, TyProp, TySet] nested
        (nestedAnswer, nestedRemaining) = runNested 1000
        nestedUsed = 1000 - nestedRemaining
    assertEqual "inner source binders stay fixed while the ambient context grows"
        (Right (Just expectedNested)) nestedAnswer
    assertEqual "nested alignment exact budget" (nestedAnswer, 0) (runNested nestedUsed)
    assertEqual "nested alignment one-short budget"
        (Left CountedCoreStructuralWorkExhausted, 0) (runNested (nestedUsed - 1))
    assertEqual "a different inner binder type is not an aligned source"
        (Right Nothing) (fst (countedAlignScopedCoreAt 1000 1 [TyProp, TySet, TySet] nested))
    assertEqual "a nonexistent binder prefix is rejected"
        (Right Nothing) (fst (countedAlignScopedCoreAt 1000 3 [TySet, TySet, TySet] nested))

countsCanonicalOrdering :: Assertion
countsCanonicalOrdering = do
    let leaves = [CBound 0, CBound 1, CGlobal testGlobal, CGlobal testPairGlobal,
            CIntrinsic Empty, CIntrinsic Member, CLogicalSelect TySet,
            CLogicalSelect (TyArrow TySet TyProp), COpaqueInteger (-2), COpaqueInteger 3,
            CFalsum, CTruth]
        terms = leaves <> [CApp CTruth CFalsum, CLam TySet (CBound 0), CNot CTruth,
            CAnd CTruth CFalsum, COr CTruth CFalsum, CImp CTruth CFalsum,
            CEq TySet (CBound 0) (CBound 1), CForall TySet CTruth, CExists TySet CTruth]
        types = [TyProp, TySet, TyArrow TyProp TySet, TyArrow TySet TyProp,
            TyArrow TySet TySet, TyArrow (TyArrow TySet TyProp) TySet]
        typed = concat [[CLogicalSelect kind, CLam kind (CBound 0),
            CEq kind (CBound 0) (CBound 1), CForall kind CTruth, CExists kind CTruth] | kind <- types]
        nested = terms <> typed <> [CApp term (CLam TySet (CBound 0)) | term <- terms]
    for_ nested \left -> for_ nested \right -> do
        let (answer, remaining) = countedCanonicalOrdering 1000 left right
            used = 1000 - remaining
        assertEqual "ordering matches derived Ord" (Right (compare left right)) answer
        assertEqual "ordering succeeds at its exact allowance" (answer, 0)
            (countedCanonicalOrdering used left right)
        assertEqual "ordering stops before an uncharged comparison"
            (Left CountedCoreStructuralWorkExhausted, 0)
            (countedCanonicalOrdering (used - 1) left right)
    let deepType = foldr TyArrow TyProp (replicate 64 TySet)
        deep = CLogicalSelect deepType :: CanonicalTerm Void
    assertEqual "type annotation traversal is bounded"
        (Left CountedCoreStructuralWorkExhausted, 0) (countedCanonicalOrdering 20 deep deep)
    assertEqual "constructor mismatch does not inspect an irrelevant subtree"
        (Right LT, 0) (countedCanonicalOrdering 1 (CBound 0) deep)

countsGlobalCollection :: Assertion
countsGlobalCollection = do
    let reference = CGlobal testGlobal
        application = CApp (CGlobal testPairGlobal) reference
        terms = [CBound 0, reference, CIntrinsic Empty, CLogicalSelect TySet,
            COpaqueInteger 2, CFalsum, CTruth, application, CLam TySet application,
            CNot application, CAnd application reference, COr reference application,
            CImp application reference, CEq TySet application reference,
            CForall TySet application, CExists TySet application]
    for_ terms \term -> do
        let (result, remaining) = countedCanonicalGlobals 1000 term
            used = 1000 - remaining
        assertEqual "collection matches the ordinary global inventory" (Right (canonicalTermGlobals term)) result
        assertEqual "collection shares its exact allowance" (result, 0) (countedCanonicalGlobals used term)
        assertEqual "one-short collection returns no partial inventory"
            (Left CountedCoreStructuralWorkExhausted, 0) (countedCanonicalGlobals (used - 1) term)

countsCoreWork :: Assertion
countsCoreWork = do
    let term :: CanonicalTerm Void
        term = CAnd CTruth (CNot CTruth)
        ample = 100
        (identityResult, identityRemaining) =
            countedCanonicalIdentity ample term term
    assertEqual "counted identity result"
        (Right True)
        identityResult
    let identityUsed = ample - identityRemaining
    assertBool "identity traverses the complete term" (identityUsed > 1)
    assertEqual "identity exact boundary"
        (Right True, 0)
        (countedCanonicalIdentity identityUsed term term)
    assertEqual "identity stops before an uncharged final pair"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedCanonicalIdentity (identityUsed - 1) term term)

    let mismatch = CAnd CTruth (CNot CFalsum)
        ordinaryMismatch = countedCanonicalIdentity ample term mismatch
        detailedMismatch =
            countedCanonicalIdentityDetailed ample term mismatch
    assertEqual "detailed identity preserves remaining work"
        (snd ordinaryMismatch)
        (snd detailedMismatch)
    assertEqual "detailed identity records the deciding structural path"
        (Right
            (CountedDifferent
                (CoreIdentityDifference
                    CoreConstructorDifference
                    [CoreSecondChild, CoreBodyChild]
                    False)))
        (fst detailedMismatch)
    assertEqual "ordinary identity is the semantic projection"
        (Right False)
        (fst ordinaryMismatch)

    let (checkResult, checkRemaining) =
            countedCheckScopedCanonicalCore
                emptyGlobalTyping ample [] term
    checked <- expectRight checkResult
    assertEqual "counted check agrees with the ordinary check"
        (checkScopedCanonicalCore emptyGlobalTyping [] term)
        (Right checked)
    let checkUsed = ample - checkRemaining
    assertEqual "checked recovery exact boundary"
        (Right checked, 0)
        (countedCheckScopedCanonicalCore
            emptyGlobalTyping checkUsed [] term)
    assertEqual "checked recovery publishes nothing on exhaustion"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedCheckScopedCanonicalCore
            emptyGlobalTyping (checkUsed - 1) [] term)

    let argument :: CanonicalTerm Void
        argument = CNot CTruth
        body :: CanonicalTerm Void
        body = CAnd (CBound 0) (CBound 0)
        expectedInstantiation = instantiateCanonical argument body
        (instantiationResult, instantiationRemaining) =
            countedInstantiateCanonical ample argument body
    assertEqual "counted instantiation"
        (Right expectedInstantiation)
        instantiationResult
    let instantiationUsed = ample - instantiationRemaining
    assertBool "each substituted occurrence copies the argument"
        (instantiationUsed > 3)
    assertEqual "instantiation exact boundary"
        (Right expectedInstantiation, 0)
        (countedInstantiateCanonical instantiationUsed argument body)
    assertEqual "instantiation publishes nothing on exhaustion"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedInstantiateCanonical
            (instantiationUsed - 1) argument body)

    let shifted = shiftCanonical 2 0 body
        (shiftResult, shiftRemaining) =
            countedShiftCanonical ample 2 0 body
    assertEqual "counted shift" (Right shifted) shiftResult
    let shiftUsed = ample - shiftRemaining
    assertEqual "shift exact boundary"
        (Right shifted, 0)
        (countedShiftCanonical shiftUsed 2 0 body)

-- Explicit results are independent of both production runners. The cases
-- exercise all constructors, retained binders, and repeated replacement copies.
substitutesCanonicalPrefix :: Assertion
substitutesCanonicalPrefix = do
    let arguments = Vector.fromList [CBound 0, CApp (CIntrinsic PowerSet) (CBound 1)]
        body = CForall TySet (CAnd
            (CEq TySet (CBound 0) (CBound 1))
            (CEq TySet (CBound 2) (CBound 3))) :: CanonicalTerm ObjectId
        expected = CForall TySet (CAnd
            (CEq TySet (CBound 0) (CBound 1))
            (CEq TySet (CApp (CIntrinsic PowerSet) (CBound 2)) (CBound 1)))
        run allowance = countedInstantiateCanonicalPrefix allowance arguments body
        (result, remaining) = run 10000
        used = 10000 - remaining
    assertEqual "formals are substituted simultaneously without capturing inner or ambient binders"
        (Right expected) result
    assertEqual "prefix substitution shares one exact allowance" (result, 0) (run used)
    assertEqual "one-short substitution retains exhaustion"
        (Left CountedCoreStructuralWorkExhausted, 0) (run (used - 1))
    let cost size copies = do
            let argument = iterate (CApp (CIntrinsic PowerSet)) (CBound 0) !! size
                goal = CForall TySet (foldr1 CAnd
                    (replicate copies (CEq TySet (CBound 0) (CBound 1)))) :: CanonicalTerm ObjectId
                (answer, after) = countedInstantiateCanonicalPrefix 100000 (Vector.singleton argument) goal
            void (expectRight answer)
            pure (100000 - after)
    small <- cost 8 4
    largeArgument <- cost 128 4
    repeated <- cost 8 64
    largeRepeated <- cost 128 64
    assertEqual "repeating one formal does not repeat its weakening traversal"
        (largeArgument - small) (largeRepeated - repeated)

transformsCanonicalBindings :: Assertion
transformsCanonicalBindings = do
    let argument = CApp (CGlobal testGlobal) (CBound 0)
        lifted = CApp (CGlobal testGlobal) (CBound 1)
        leaves = [CGlobal testGlobal, CIntrinsic Empty, CLogicalSelect TySet,
            COpaqueInteger 7, CFalsum, CTruth]
        vectors = [(term, term, term, 1) | term <- leaves]
            <> [(CBound 0, CBound 2, argument, 4), (CBound 1, CBound 3, CBound 0, 1)]
            <> [(construct (CBound 0) (CBound 1), construct (CBound 2) (CBound 3),
                    construct argument (CBound 0), 6)
                | construct <- [CApp, CAnd, COr, CImp, CEq TySet]]
            <> [(CNot (CBound 0), CNot (CBound 2), CNot argument, 5)]
            <> [(bind (CAnd (CBound 0) (CBound 1)), bind (CAnd (CBound 0) (CBound 3)),
                    bind (CAnd (CBound 0) lifted), 7)
                | bind <- [CLam TySet, CForall TySet, CExists TySet]]
            <> [(CForall TySet (CLam TySet (CBound 2)),
                CForall TySet (CLam TySet (CBound 4)),
                CForall TySet (CLam TySet (CApp (CGlobal testGlobal) (CBound 2))), 6)]
    for_ vectors \(term, shifted, substituted, substitutionCost) -> do
        assertEqual "capture-safe shift" shifted (shiftCanonical 2 0 term)
        assertEqual "capture-safe substitution" substituted (instantiateCanonical argument term)
        boundary shifted (canonicalNodeCount term) (\work -> countedShiftCanonical work 2 0 term)
        boundary substituted substitutionCost (\work -> countedInstantiateCanonical work argument term)
    let unused = error "unused transformation input was demanded"
    assertEqual "unused replacement stays lazy" (CTruth :: CanonicalTerm Void)
        (instantiateCanonical unused CTruth)
    assertEqual "closed shift does not demand amount" (CBound 0 :: CanonicalTerm Void)
        (shiftCanonical unused 1 (CBound 0))
    assertEqual "exhaustion precedes input inspection"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedShiftCanonical 0 1 0 (unused :: CanonicalTerm Void))
  where
    boundary expected cost run = do
        assertEqual "exact allowance" (Right expected, 0) (run cost)
        assertEqual "surplus stays available" (Right expected, 3) (run (cost + 3))
        for_ [0 .. cost - 1] \work ->
            assertEqual "every partial expenditure is retained"
                (Left CountedCoreStructuralWorkExhausted, 0) (run work)

-- Frozen before unification. In particular, ordinary binder failure names the
-- requested index, while charged lookup names the residual index.
preservesInferenceVectors :: Assertion
preservesInferenceVectors = for_ vectors \(context, term, ordinary, counted, cost) -> do
    assertEqual "ordinary type-only inference" ordinary
        (scopedCoreType <$> checkScopedCanonicalCore emptyGlobalTyping context term)
    let run work = let (result, remaining) = countedCheckScopedCanonicalCore emptyGlobalTyping work context term
                   in (scopedCoreType <$> result, remaining)
    assertEqual "exact inference allowance" (counted, 0) (run cost)
    assertEqual "retained surplus on success and semantic failure" (counted, 3) (run (cost + 3))
    for_ [0 .. cost - 1] \work -> assertEqual "partial inference cannot publish a result"
        (Left CountedCoreStructuralWorkExhausted, 0) (run work)
  where
    vectors :: [([CoreType], CanonicalTerm Void, Either CoreCheckError CoreType,
        Either (CountedCoreFailure CoreCheckError) CoreType, Word)]
    vectors =
        [ ([],CTruth,Right TyProp,Right TyProp,1)
        , ([],CFalsum,Right TyProp,Right TyProp,1)
        , ([],CIntrinsic Empty,Right TySet,Right TySet,1)
        , ([],CLogicalSelect TySet,Right (TyArrow (TyArrow TySet TyProp) TySet),Right (TyArrow (TyArrow TySet TyProp) TySet),1)
        , ([],COpaqueInteger 7,Right TySet,Right TySet,1)
        , ([TySet],CBound 0,Right TySet,Right TySet,2)
        , ([TyProp,TySet],CBound 1,Right TySet,Right TySet,3)
        , ([TySet],CBound 2,Left (UnboundCoreIndex 2),Left (CountedCoreOperationFailed (UnboundCoreIndex 1)),2)
        , ([],CLam TySet (CBound 0),Right (TyArrow TySet TySet),Right (TyArrow TySet TySet),3)
        , ([],CApp (CLam TySet (CBound 0)) (COpaqueInteger 1),Right TySet,Right TySet,6)
        , ([],CApp CTruth (CBound 0),Left (UnboundCoreIndex 0),Left (CountedCoreOperationFailed (UnboundCoreIndex 0)),3)
        , ([],CApp CTruth CFalsum,Left (AppliedNonFunction TyProp),Left (CountedCoreOperationFailed (AppliedNonFunction TyProp)),3)
        , ([],CApp (CLam TySet (CBound 0)) CTruth,Left (ApplicationArgumentTypeMismatch TySet TyProp),Left (CountedCoreOperationFailed (ApplicationArgumentTypeMismatch TySet TyProp)),6)
        , ([],CNot CTruth,Right TyProp,Right TyProp,3)
        , ([],CNot (COpaqueInteger 1),Left (ExpectedCoreType TyProp TySet),Left (CountedCoreOperationFailed (ExpectedCoreType TyProp TySet)),3)
        , ([],CAnd CTruth CFalsum,Right TyProp,Right TyProp,5)
        , ([],COr CTruth CFalsum,Right TyProp,Right TyProp,5)
        , ([],CImp CTruth CFalsum,Right TyProp,Right TyProp,5)
        , ([],CAnd (COpaqueInteger 1) (CBound 0),Left (ExpectedCoreType TyProp TySet),Left (CountedCoreOperationFailed (ExpectedCoreType TyProp TySet)),3)
        , ([],COr CTruth (COpaqueInteger 1),Left (ExpectedCoreType TyProp TySet),Left (CountedCoreOperationFailed (ExpectedCoreType TyProp TySet)),5)
        , ([],CImp (COpaqueInteger 1) (CBound 0),Left (ImplicationOperandTypeMismatch TySet),Left (CountedCoreOperationFailed (ImplicationOperandTypeMismatch TySet)),3)
        , ([],CEq TySet (COpaqueInteger 1) (COpaqueInteger 2),Right TyProp,Right TyProp,5)
        , ([],CEq TySet CTruth (CBound 0),Left (EqualityOperandTypeMismatch TySet TyProp),Left (CountedCoreOperationFailed (EqualityOperandTypeMismatch TySet TyProp)),3)
        , ([],CEq TyProp CTruth (COpaqueInteger 1),Left (EqualityOperandTypeMismatch TyProp TySet),Left (CountedCoreOperationFailed (EqualityOperandTypeMismatch TyProp TySet)),5)
        , ([],CForall TySet (CEq TySet (CBound 0) (CBound 0)),Right TyProp,Right TyProp,9)
        , ([],CExists TySet (CEq TySet (CBound 0) (CBound 0)),Right TyProp,Right TyProp,9)
        , ([],CForall TySet (CBound 0),Left (QuantifierBodyTypeMismatch TySet),Left (CountedCoreOperationFailed (QuantifierBodyTypeMismatch TySet)),4)
        , ([],CExists TySet (CBound 0),Left (QuantifierBodyTypeMismatch TySet),Left (CountedCoreOperationFailed (QuantifierBodyTypeMismatch TySet)),4)
        ]

instantiatesCheckedPrefixes :: Assertion
instantiatesCheckedPrefixes = do
    let ambient = [TySet]
        term = CAnd (CBound 0) (CEq TySet (CBound 1) (CBound 2))
    body <- expectRight
        (checkScopedCanonicalCore testGlobalType
            (TyProp : TySet : ambient) term)
    argument <- expectRight
        (checkScopedCanonicalCore testGlobalType ambient (CBound 0))
    truth <- expectRight
        (checkScopedCanonicalCore testGlobalType ambient CTruth)
    expected <- expectRight
        (checkScopedCanonicalCore testGlobalType ambient
            (CAnd CTruth (CEq TySet (CBound 0) (CBound 0))))
    assertEqual "source-order slots, despite nearest-first lexical context"
        (Right (ScopedInstantiationClosed expected))
        (fst (countedInstantiateScopedPrefix 100 2
            (Map.fromList [(0, argument), (1, truth)]) body))
    assertEqual "only missing used assignments are open"
        (Right (ScopedInstantiationOpen (Set.singleton 1)))
        (fst (countedInstantiateScopedPrefix 100 2
            (Map.singleton 0 argument) body))
    unused <- expectRight
        (checkScopedCanonicalCore testGlobalType
            [TyProp, TySet, TySet] (CBound 2))
    assertEqual "missing unused slots do not prevent closure"
        (Right (ScopedInstantiationClosed argument))
        (fst (countedInstantiateScopedPrefix 100 2 Map.empty unused))
    closedTruth <- expectRight
        (checkScopedCanonicalCore testGlobalType [] CTruth)
    assertEqual "later slots are outside this premise's lexical prefix"
        (Right (ScopedInstantiationClosed argument))
        (fst (countedInstantiateScopedPrefix 100 2
            (Map.singleton 2 closedTruth) unused))

rejectsCheckedInstantiationPremises :: Assertion
rejectsCheckedInstantiationPremises = do
    body <- expectRight
        (checkScopedCanonicalCore testGlobalType [TySet] CTruth)
    wrongType <- expectRight
        (checkScopedCanonicalCore testGlobalType [] CTruth)
    wrongContext <- expectRight
        (checkScopedCanonicalCore testGlobalType [TySet] (CBound 0))
    let substitute argument = countedInstantiateScopedPrefix 100 1
            (Map.singleton 0 argument) body
    assertEqual "unused assignment still obeys the type premise"
        ( Left (CountedCoreOperationFailed
            (ScopedInstantiationTypeMismatch 0 TySet TyProp))
        , 98
        )
        (substitute wrongType)
    assertEqual "context premise precedes type and syntax inspection"
        ( Left (CountedCoreOperationFailed
            (ScopedInstantiationContextMismatch 0 [] [TySet]))
        , 99
        )
        (substitute wrongContext)
    assertEqual "ordinary instantiation preserves the same typed cause"
        (Left (ScopedInstantiationTypeMismatch 0 TySet TyProp))
        (instantiateScopedCore wrongType body)
    let hugePrefix = fromIntegral (maxBound :: Word) + 1
    assertEqual "oversized Natural prefix is rejected without narrowing"
        ( Left (CountedCoreOperationFailed
            (ScopedInstantiationPrefixTooLong hugePrefix 1))
        , 98
        )
        (countedInstantiateScopedPrefix 100 hugePrefix Map.empty body)

countsCheckedTransformations :: Assertion
countsCheckedTransformations = do
    argument <- expectRight
        (checkScopedCanonicalCore testGlobalType [TySet] (CBound 0))
    body <- expectRight
        (checkScopedCanonicalCore testGlobalType [TySet, TySet]
            (CForall TySet (CEq TySet (CBound 1) (CBound 2))))
    expected <- expectRight (instantiateScopedCore argument body)
    let instantiate available = countedInstantiateScopedPrefix available 1
            (Map.singleton 0 argument) body
        (result, remaining) = instantiate 100
        used = 100 - remaining
    assertEqual "checked result agrees with single instantiation"
        (Right (ScopedInstantiationClosed expected)) result
    assertEqual "all body and copied nodes plus metadata are charged"
        9 used
    assertEqual "exact allowance closes" (result, 0) (instantiate used)
    assertEqual "complete counted instantiation has no open-result case"
        (Right expected, 0)
        (countedInstantiateScopedCore used argument body)
    for_ [0 .. used - 1] \available ->
        assertEqual "no partial checked result at any exhaustion boundary"
            (Left CountedCoreStructuralWorkExhausted, 0)
            (instantiate available)
    for_ [0 .. used - 1] \available ->
        assertEqual "complete instantiation exhausts without checked output"
            (Left CountedCoreStructuralWorkExhausted, 0)
            (countedInstantiateScopedCore available argument body)
    truth <- expectRight (checkScopedCanonicalCore testGlobalType [] CTruth)
    assertEqual "proof conjunction retains truth operands exactly"
        (Just (CAnd CTruth CTruth))
        (scopedCoreTerm <$> conjoinExactScopedCore truth truth)
    assertEqual "counted weakening agrees with preserving weakening"
        (Right (weakenCheckedScopedCore TyProp body), 0)
        (countedWeakenCheckedScopedCore 4 TyProp body)
    assertEqual "weakening exhaustion returns no value"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedWeakenCheckedScopedCore 3 TyProp body)

prop_checkedPrefixInstantiationAgrees :: Property
prop_checkedPrefixInstantiationAgrees = property do
    prefix <- forAll (Gen.list (Range.linear 0 8)
        (Gen.element [TySet, TyProp, TyArrow TySet TySet]))
    innerDepth <- forAll (Gen.int (Range.linear 0 5))
    useAmbient <- forAll Gen.bool
    let ambient = [TySet, TyProp]
        argument TySet = CBound 0
        argument TyProp = CNot (CBound 1)
        argument (TyArrow _ _) = CLam TySet (CBound 1)
        args = map argument prefix
        equations =
            [ CEq coreType
                (CBound (fromIntegral (index + innerDepth)))
                (shiftCanonical
                    (fromIntegral (length prefix + innerDepth)) 0
                    (argument coreType))
            | (index, coreType) <- zip [0 ..] prefix
            ]
        ambientProposition =
            if useAmbient
                then [CBound (fromIntegral (length prefix + innerDepth + 1))]
                else []
        redexes =
            [ CEq TySet
                (CApp (CBound (fromIntegral (index + innerDepth)))
                    (CIntrinsic Empty))
                (CIntrinsic Empty)
            | (index, TyArrow _ _) <- zip [0 ..] prefix
            ]
        term = foldr (\_ -> CForall TySet)
            (foldr CAnd CTruth (equations <> redexes <> ambientProposition))
            [1 .. innerDepth]
        -- Sequentially remove nearest binders. Arguments remain under the
        -- yet unremoved prefix so later steps cannot substitute inside them.
        reference = foldl'
            (\current (remainingBinders, replacement) ->
                instantiateCanonical
                    (shiftCanonical (fromIntegral remainingBinders) 0 replacement)
                    current)
            term
            (zip (reverse [0 .. length prefix - 1]) args)
    checked <- evalEither
        (checkScopedCanonicalCore testGlobalType (prefix <> ambient) term)
    replacements <- evalEither
        (traverse (checkScopedCanonicalCore testGlobalType ambient) args)
    expected <- evalEither
        (checkScopedCanonicalCore testGlobalType ambient reference)
    fst (countedInstantiateScopedPrefix 100000 (fromIntegral (length prefix))
        (Map.fromList (zip [0 ..] (reverse replacements))) checked)
        === Right (ScopedInstantiationClosed expected)

reconstructsCheckedOccurrenceViews :: Assertion
reconstructsCheckedOccurrenceViews =
    for_ cases \(context, term) -> do
        occurrence <-
            expectRight
                (fst
                    (countedAnalyseCanonicalOccurrences
                        testGlobalType 100000 context term))
        assertEqual "checked occurrence reconstruction"
            term
            (reconstructOccurrence occurrence)
        checkRows context occurrence
  where
    emptySet = CIntrinsic Empty
    equality = CEq TySet emptySet emptySet
    cases :: [([CoreType], CanonicalTerm ObjectId)]
    cases =
        [ ([TySet], CBound 0)
        , ([], CGlobal testGlobal)
        , ([], emptySet)
        , ([], CLogicalSelect TySet)
        , ([], COpaqueInteger 17)
        , ([], CApp (CIntrinsic FamilyUnion) emptySet)
        , ([], CLam TySet (CBound 0))
        , ([], CFalsum)
        , ([], CTruth)
        , ([], CNot CTruth)
        , ([], CAnd CTruth CFalsum)
        , ([], COr CTruth CFalsum)
        , ([], CImp CTruth CFalsum)
        , ([], equality)
        , ([], CForall TySet equality)
        , ([], CExists TySet equality)
        , ( [TySet, TyProp]
          , CLam (TyArrow TySet TySet)
                (CForall TySet
                    (CExists TyProp
                        (CAnd (CBound 0)
                            (CEq TySet
                                (CApp (CBound 2) (CBound 1))
                                (CBound 3)))))
          )
        ]

    checkRows context row = do
        reference <- expectRight
            (checkScopedCanonicalCore testGlobalType context
                (reconstructOccurrence row))
        assertEqual "occurrence projection agrees with independent scoped checking"
            reference (checkedOccurrenceScopedCore row)
        let childContext = case checkedOccurrenceView row of
                OccurrenceLambda binderType _body -> binderType : context
                OccurrenceUniversal binderType _body -> binderType : context
                OccurrenceExistential binderType _body -> binderType : context
                _ -> context
        for_ (occurrenceChildren row) (checkRows childContext)

reconstructOccurrence
    :: CheckedOccurrence global
    -> CanonicalTerm global
reconstructOccurrence row =
    case checkedOccurrenceView row of
        OccurrenceBound index -> CBound index
        OccurrenceGlobal global -> CGlobal global
        OccurrenceIntrinsic intrinsic -> CIntrinsic intrinsic
        OccurrenceLogicalSelect coreType -> CLogicalSelect coreType
        OccurrenceOpaqueInteger integer -> COpaqueInteger integer
        OccurrenceApplication function argument ->
            CApp
                (reconstructOccurrence function)
                (reconstructOccurrence argument)
        OccurrenceLambda binderType body ->
            CLam binderType (reconstructOccurrence body)
        OccurrenceFalsum -> CFalsum
        OccurrenceTruth -> CTruth
        OccurrenceNegation proposition ->
            CNot (reconstructOccurrence proposition)
        OccurrenceConjunction left right ->
            CAnd
                (reconstructOccurrence left)
                (reconstructOccurrence right)
        OccurrenceDisjunction left right ->
            COr
                (reconstructOccurrence left)
                (reconstructOccurrence right)
        OccurrenceImplication premise conclusion ->
            CImp
                (reconstructOccurrence premise)
                (reconstructOccurrence conclusion)
        OccurrenceEquality operandType left right ->
            CEq operandType
                (reconstructOccurrence left)
                (reconstructOccurrence right)
        OccurrenceUniversal binderType body ->
            CForall binderType (reconstructOccurrence body)
        OccurrenceExistential binderType body ->
            CExists binderType (reconstructOccurrence body)

occurrenceChildren
    :: CheckedOccurrence global
    -> [CheckedOccurrence global]
occurrenceChildren = occurrenceViewChildren . checkedOccurrenceView

occurrenceViewChildren
    :: CheckedOccurrenceView global
    -> [CheckedOccurrence global]
occurrenceViewChildren = \case
    OccurrenceBound{} -> []
    OccurrenceGlobal{} -> []
    OccurrenceIntrinsic{} -> []
    OccurrenceLogicalSelect{} -> []
    OccurrenceOpaqueInteger{} -> []
    OccurrenceApplication function argument -> [function, argument]
    OccurrenceLambda _binderType body -> [body]
    OccurrenceFalsum -> []
    OccurrenceTruth -> []
    OccurrenceNegation proposition -> [proposition]
    OccurrenceConjunction left right -> [left, right]
    OccurrenceDisjunction left right -> [left, right]
    OccurrenceImplication premise conclusion -> [premise, conclusion]
    OccurrenceEquality _operandType left right -> [left, right]
    OccurrenceUniversal _binderType body -> [body]
    OccurrenceExistential _binderType body -> [body]

retainsCheckedOccurrenceAnalysis :: Assertion
retainsCheckedOccurrenceAnalysis = do
    let term =
            CForall TySet
                (CImp
                    (CEq TySet (CBound 0) (CGlobal testGlobal))
                    CTruth)
        ample = 1000
        (checkedResult, checkedRemaining) =
            countedCheckScopedCanonicalCore testGlobalType ample [] term
        (analysisResult, analysisRemaining) =
            countedAnalyseCanonicalOccurrences testGlobalType ample [] term
    checked <- expectRight checkedResult
    root <- expectRight analysisResult
    assertEqual "retained and ordinary inference use the same allowance"
        checkedRemaining analysisRemaining
    assertEqual "retained root type"
        (scopedCoreType checked)
        (checkedOccurrenceType root)
    assertEqual "retained root syntax"
        term
        (reconstructOccurrence root)
    assertEqual "the complete occurrence spine is available"
        6
        (occurrenceCount root)
    equalityRow <-
        case occurrenceChildren root of
            [implicationRow] ->
                case occurrenceChildren implicationRow of
                    [candidate, _conclusion] -> pure candidate
                    _ -> assertFailure "implication occurrence lost child order"
            _ -> assertFailure "universal occurrence lost child order"
    assertEqual "binary child roles remain in source order"
        [CBound 0, CGlobal testGlobal]
        (map reconstructOccurrence
            (occurrenceChildren equalityRow))
    let used = ample - analysisRemaining
        (exactResult, exactRemaining) =
            countedAnalyseCanonicalOccurrences
                testGlobalType used [] term
    _exact <- expectRight exactResult
    assertEqual "retained analysis exact remainder" 0 exactRemaining
    case countedAnalyseCanonicalOccurrences
            testGlobalType (used - 1) [] term of
        (Left CountedCoreStructuralWorkExhausted, 0) -> pure ()
        _ ->
            assertFailure
                "retained analysis published a row one unit short"

    let malformed = CApp (CGlobal testGlobal) (CGlobal testGlobal)
        (ordinaryFailure, ordinaryRemaining) =
            countedCheckScopedCanonicalCore
                testGlobalType ample [] malformed
        (retainedFailure, retainedRemaining) =
            countedAnalyseCanonicalOccurrences
                testGlobalType ample [] malformed
    assertEqual "retained inference preserves constructor errors"
        (void ordinaryFailure)
        (void retainedFailure)
    assertEqual "retained inference preserves failure remainder"
        ordinaryRemaining retainedRemaining

    let chain :: Int -> CanonicalTerm ObjectId
        chain depth
            | depth == 0 = CGlobal testGlobal
            | otherwise =
                CApp
                    (CApp (CGlobal testPairGlobal) (CGlobal testGlobal))
                    (chain (depth - 1))
        analysisCost source =
            let (_result, remaining) =
                    countedAnalyseCanonicalOccurrences
                        testGlobalType ample [] source
            in ample - remaining
        firstDelta = analysisCost (chain 6) - analysisCost (chain 5)
        secondDelta = analysisCost (chain 7) - analysisCost (chain 6)
    assertEqual "one fixed-shape application row has fixed counted growth"
        firstDelta secondDelta
  where
    occurrenceCount :: CheckedOccurrence global -> Int
    occurrenceCount row =
        1 + sum (map occurrenceCount (occurrenceChildren row))

rebasesCheckedOccurrences :: Assertion
rebasesCheckedOccurrences = do
    let ambient = [TySet]
        body = CEq TySet (CBound 1) (CBound 1)
        proposition = CForall TySet body
        ample = 1000
        (analysisResult, _analysisRemaining) =
            countedAnalyseCanonicalOccurrences
                testGlobalType ample ambient proposition
    root <- expectRight analysisResult
    bodyRow <-
        case occurrenceChildren root of
            [child] -> pure child
            _ -> assertFailure "universal occurrence lost its body row"
    originalBody <- expectRight
        (checkScopedCanonicalCore testGlobalType (TySet : ambient) body)
    assertEqual "projection preserves an unused surrounding binder"
        originalBody (checkedOccurrenceScopedCore bodyRow)
    assertBool "ambient-only body is ground under the removable prefix"
        (not (checkedOccurrenceDependsOnBinderPrefix bodyRow))
    let (rebaseResult, rebaseRemaining) =
            countedRebaseCheckedOccurrence ample bodyRow
    rebased <-
        expectRight rebaseResult
            >>= maybe (assertFailure "ground occurrence remained open") pure
    reference <-
        expectRight
            (checkScopedCanonicalCore
                testGlobalType ambient
                (CEq TySet (CBound 0) (CBound 0)))
    assertEqual "checked rebase agrees with checked closing semantics"
        reference rebased
    let rebaseUsed = ample - rebaseRemaining
    assertEqual "checked rebase exact boundary"
        (Right (Just rebased), 0)
        (countedRebaseCheckedOccurrence rebaseUsed bodyRow)
    assertEqual "checked rebase publishes nothing one unit short"
        (Left CountedCoreStructuralWorkExhausted, 0)
        (countedRebaseCheckedOccurrence (rebaseUsed - 1) bodyRow)

    let openBody = CEq TySet (CBound 0) (CBound 1)
        openProposition = CForall TySet openBody
        (openAnalysis, _openRemaining) =
            countedAnalyseCanonicalOccurrences
                testGlobalType ample ambient openProposition
    openRoot <- expectRight openAnalysis
    openRow <-
        case occurrenceChildren openRoot of
            [child] -> pure child
            _ -> assertFailure "open universal lost its body row"
    assertBool "body records its dependency on the removed binder"
        (checkedOccurrenceDependsOnBinderPrefix openRow)
    assertEqual "dependent occurrence is rejected without rebase work"
        (Right Nothing, ample)
        (countedRebaseCheckedOccurrence ample openRow)

analysesScopedOccurrencesUnderBinders :: Assertion
analysesScopedOccurrencesUnderBinders = do
    let ample = 1000
        ambient = [TySet]
        scopedContext = TySet : ambient
    dependent <-
        expectRight
            (checkScopedCanonicalCore testGlobalType scopedContext
                (CEq TySet (CBound 0) (CBound 1)))
    let (dependentResult, _dependentRemaining) =
            countedAnalyseScopedOccurrencesUnderBinders
                testGlobalType ample 1 dependent
    dependentRow <- expectRight dependentResult
    assertEqual "a dependent root keeps its original logical prefix"
        dependent (checkedOccurrenceScopedCore dependentRow)
    assertBool "nearest logical binder remains a dependency"
        (checkedOccurrenceDependsOnBinderPrefix dependentRow)

    rigid <-
        expectRight
            (checkScopedCanonicalCore testGlobalType scopedContext
                (CEq TySet (CBound 1) (CBound 1)))
    let (rigidResult, rigidRemaining) =
            countedAnalyseScopedOccurrencesUnderBinders
                testGlobalType ample 1 rigid
    rigidRow <- expectRight rigidResult
    assertEqual "a ground root keeps its original logical prefix until rebased"
        rigid (checkedOccurrenceScopedCore rigidRow)
    assertBool "ambient occurrence is ground beneath logical binder"
        (not (checkedOccurrenceDependsOnBinderPrefix rigidRow))
    rebased <-
        expectRight (fst (countedRebaseCheckedOccurrence ample rigidRow))
            >>= maybe (assertFailure "ambient occurrence did not rebase") pure
    reference <-
        expectRight
            (checkScopedCanonicalCore testGlobalType ambient
                (CEq TySet (CBound 0) (CBound 0)))
    assertEqual "logical-prefix rebase reaches the fixed ambient context"
        reference rebased

    let rigidUsed = ample - rigidRemaining
    case countedAnalyseScopedOccurrencesUnderBinders
            testGlobalType rigidUsed 1 rigid of
        (Right exact, 0) ->
            assertEqual "exact analysis retains the checked root"
                (reconstructOccurrence rigidRow)
                (reconstructOccurrence exact)
        _ -> assertFailure "logical-prefix analysis missed exact boundary"
    case countedAnalyseScopedOccurrencesUnderBinders
            testGlobalType (rigidUsed - 1) 1 rigid of
        (Left CountedCoreStructuralWorkExhausted, 0) -> pure ()
        _ -> assertFailure "one-short analysis published an occurrence tree"

    depthZero <-
        expectRight
            (checkScopedCanonicalCore testGlobalType ambient
                (CEq TySet (CBound 0) (CBound 0)))
    ordinary <-
        expectRight
            (fst (countedAnalyseCanonicalOccurrences
                testGlobalType ample ambient (scopedCoreTerm depthZero)))
    checked <-
        expectRight
            (fst (countedAnalyseScopedOccurrencesUnderBinders
                testGlobalType ample 0 depthZero))
    assertEqual "depth-zero entry points retain the same root syntax"
        (reconstructOccurrence ordinary)
        (reconstructOccurrence checked)
    assertEqual "depth-zero entry points retain the same root type"
        (checkedOccurrenceType ordinary)
        (checkedOccurrenceType checked)

    case countedAnalyseScopedOccurrencesUnderBinders
            testGlobalType ample 2 depthZero of
        ( Left
            (CountedCoreOperationFailed
                CheckedOccurrenceBinderDepthOutOfScope)
         , remaining
         ) -> assertEqual "only the present prefix row was charged"
                (ample - 1) remaining
        _ -> assertFailure "impossible binder depth was not rejected"

prop_occurrenceRebaseAgrees :: Property
prop_occurrenceRebaseAgrees = property do
    binderDepth <- forAll (Gen.int (Range.linear 1 8))
    ambientDepth <- forAll (Gen.int (Range.linear 0 8))
    selected <-
        forAll
            (Gen.int
                (Range.linear 0 (binderDepth + ambientDepth - 1)))
    let ambient = replicate ambientDepth TySet
        index = fromIntegral selected
        body = CEq TySet (CBound index) (CBound index)
        proposition =
            foldr
                (\_ remaining -> CForall TySet remaining)
                body
                [1 .. binderDepth]
        (analysisResult, _analysisRemaining) =
            countedAnalyseCanonicalOccurrences
                testGlobalType 100000 ambient proposition
    root <- evalEither analysisResult
    row <- evalMaybe (descend binderDepth root)
    if selected < binderDepth
        then do
            assert (checkedOccurrenceDependsOnBinderPrefix row)
            fst (countedRebaseCheckedOccurrence 100000 row)
                === Right Nothing
        else do
            assert (not (checkedOccurrenceDependsOnBinderPrefix row))
            expected <-
                evalEither
                    (checkScopedCanonicalCore
                        testGlobalType ambient
                        (CEq TySet
                            (CBound (fromIntegral (selected - binderDepth)))
                            (CBound (fromIntegral (selected - binderDepth)))))
            fst (countedRebaseCheckedOccurrence 100000 row)
                === Right (Just expected)
  where
    descend 0 row = Just row
    descend depth row =
        case occurrenceChildren row of
            [child] -> descend (depth - 1) child
            _ -> Nothing

expectRight
    :: Show error
    => Either error value
    -> IO value
expectRight =
    either (assertFailure . show) pure

usesFrozenCoreIntrinsicCodes :: Assertion
usesFrozenCoreIntrinsicCodes = do
    let expected =
            [ (Member, 0x00)
            , (Empty, 0x01)
            , (PairSet, 0x02)
            , (FamilyUnion, 0x03)
            , (PowerSet, 0x04)
            , (Sep, 0x05)
            , (Repl, 0x06)
            , (UnivOf, 0x07)
            , (ISetLfp, 0x08)
            , (GlobalChoice, 0x09)
            , (OrderedPair, 0x0a)
            , (FirstProjection, 0x0b)
            , (SecondProjection, 0x0c)
            ]
    assertEqual
        "stable intrinsic codes"
        expected
        [ (tag, StableCode.coreIntrinsicTagCode tag)
        | tag <- StableCode.allCoreIntrinsicTags
        ]
    for_ StableCode.allCoreIntrinsicTags \tag ->
        assertEqual
            ("stable intrinsic round trip for " <> show tag)
            (Right tag)
            (StableCode.coreIntrinsicTagFromCode
                (StableCode.coreIntrinsicTagCode tag))
    assertEqual
        "unknown intrinsic code"
        (Left (StableCode.UnknownCoreIntrinsicCode 0xff))
        (StableCode.coreIntrinsicTagFromCode 0xff)

rechecksCanonicalTerms :: Assertion
rechecksCanonicalTerms = do
    let term =
            CForall TySet
                (CEq TySet
                    (CBound 0)
                    (CBound 0))
    assertEqual
        "well-typed canonical proposition"
        (Right (TyProp, term))
        ( (\checked ->
                ( frozenCoreType checked
                , frozenCoreTerm checked
                ))
            <$> checkCanonicalCore testGlobalType term
        )
    assertEqual
        "out-of-scope de Bruijn index"
        (Left (UnboundCoreIndex 1))
        (frozenCoreType
            <$> checkCanonicalCore
                testGlobalType
                (CForall TySet (CBound 1)))
    assertEqual
        "canonical application still checks argument types"
        (Left
            (ApplicationArgumentTypeMismatch
                TySet
                TyProp))
        (frozenCoreType
            <$> checkCanonicalCore
                testGlobalType
                (CApp
                    (CIntrinsic FamilyUnion)
                    CFalsum))
    let selectedType = TyArrow TySet TySet
    assertEqual
        "logical selection retains its concrete type index"
        (Right (logicalSelectionType selectedType))
        (frozenCoreType
            <$> checkCanonicalCore
                testGlobalType
                (CLogicalSelect selectedType))
    assertEqual
        "logical selection witness is a closed proposition"
        TyProp
        (frozenCoreType
            (logicalSelectionWitness selectedType))

preservesCanonicalFailureOrder :: Assertion
preservesCanonicalFailureOrder =
    for_ cases \(caseName, term, expected) -> do
        assertEqual
            (caseName <> " ordinary failure")
            (Left expected)
            (frozenCoreType <$> checkCanonicalCore emptyGlobalTyping term)
        assertEqual
            (caseName <> " counted failure")
            (Left (CountedCoreOperationFailed expected))
            (fst
                (countedCheckScopedCanonicalCore
                    emptyGlobalTyping
                    100
                    []
                    term))
  where
    cases :: [(String, CanonicalTerm Void, CoreCheckError)]
    cases =
        [ ( "conjunction"
          , CAnd (CIntrinsic Empty) (CBound 0)
          , ExpectedCoreType TyProp TySet
          )
        , ( "disjunction"
          , COr (CIntrinsic Empty) (CBound 0)
          , ExpectedCoreType TyProp TySet
          )
        , ( "implication"
          , CImp (CIntrinsic Empty) (CBound 0)
          , ImplicationOperandTypeMismatch TySet
          )
        , ( "equality"
          , CEq TyProp (CIntrinsic Empty) (CBound 0)
          , EqualityOperandTypeMismatch TyProp TySet
          )
        ]

checksNativeLogicalForms :: Assertion
checksNativeLogicalForms = do
    let expected =
            CAnd
                CTruth
                (CNot
                    (CExists TySet
                        (COr
                            (CEq TySet (CBound 0) (CBound 0))
                            CFalsum)))
    frozen <-
        either
            (assertFailure . show)
            pure
            (checkCanonicalCore testGlobalType expected)
    assertEqual "native proposition type" TyProp (frozenCoreType frozen)
    assertEqual "native canonical form" expected (frozenCoreTerm frozen)
    assertEqual
        "native proposition operands are type checked"
        (Left (ExpectedCoreType TyProp TySet))
        (frozenCoreType
            <$> checkCanonicalCore
                testGlobalType
                (CNot (CIntrinsic Empty)))
    assertEqual
        "existential instantiation traverses native forms"
        (CAnd
            (CEq TySet
                (CIntrinsic Empty)
                (CIntrinsic Empty))
            CTruth)
        (instantiateCanonical
            (CIntrinsic Empty :: CanonicalTerm ObjectId)
            (CAnd
                (CEq TySet (CBound 0) (CBound 0))
                CTruth))

checksScopedCanonicalOperations :: Assertion
checksScopedCanonicalOperations = do
    scoped <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalType
                [TySet]
                (CBound 0))
    weakened <-
        either
            (assertFailure . show)
            pure
            (weakenScopedCore
                testGlobalType
                TyProp
                scoped)
    assertEqual
        "nearest binder insertion shifts the prior local"
        ( [TyProp, TySet]
        , TySet
        , CBound 1
        )
        ( scopedCoreContext weakened
        , scopedCoreType weakened
        , scopedCoreTerm weakened
        )
    assertEqual
        "top-level binder substitution removes its index"
        (CEq TySet
            (CIntrinsic Empty)
            (CIntrinsic Empty))
        (instantiateCanonical
            (CIntrinsic Empty
                :: CanonicalTerm ObjectId)
            (CEq TySet
                (CBound 0)
                (CBound 0)))
    root <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalType
                []
                (CGlobal testGlobal))
    assertEqual
        "empty scoped context closes"
        (Just
            (TySet, CGlobal testGlobal))
        ( (\closed ->
                ( frozenCoreType closed
                , frozenCoreTerm closed
                ))
            <$> closeScopedCore root
        )

rejectsOverflowingCheckedWeakeningDepths :: Assertion
rejectsOverflowingCheckedWeakeningDepths = do
    scoped <-
        expectRight
            (checkScopedCanonicalCore
                emptyGlobalTyping
                [TySet, TyProp]
                (CBound 1))
    let overflowingDepth = fromIntegral (maxBound :: Word64) + 2
    case weakenCheckedScopedCoreAt overflowingDepth TySet scoped of
        Nothing -> pure ()
        Just _ ->
            assertFailure
                "an overflowing depth produced checked scoped evidence"

buildsSetInductionHypotheses :: Assertion
buildsSetInductionHypotheses = do
    let propertyTerm =
            CImp
                (CEq TySet
                    (CBound 0)
                    (CIntrinsic Empty))
                (CEq TySet
                    (CBound 0)
                    (CBound 0))
    claimProperty <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalType
                [TySet]
                propertyTerm)
    (predicate, hypothesis, step, result) <-
        maybe
            (assertFailure "set-induction instance was not constructed")
            pure
            (scopedSetInductionInstance 0 claimProperty)
    let abstractedProperty =
            CImp
                (CEq TySet
                    (CBound 0)
                    (CIntrinsic Empty))
                (CEq TySet
                    (CBound 0)
                    (CBound 0))
        memberHypothesis =
            CForall TySet
                (CImp
                    (CApp
                        (CApp
                            (CIntrinsic Member)
                            (CBound 0))
                        (CBound 1))
                    abstractedProperty)
    assertEqual
        "set induction abstracts the selected property once"
        (CLam TySet abstractedProperty)
        (scopedCoreTerm predicate)
    assertEqual
        "antecedent and goal are both generalized over the member"
        memberHypothesis
        (scopedCoreTerm hypothesis)
    assertEqual
        "set-induction step owns its member-wise hypothesis"
        (CForall TySet
            (CImp memberHypothesis abstractedProperty))
        (scopedCoreTerm step)
    assertEqual
        "set-induction result closes the complete property"
        (CForall TySet abstractedProperty)
        (scopedCoreTerm result)

specializesCheckedSeparationCharacteristic :: Assertion
specializesCheckedSeparationCharacteristic = do
    foundation <-
        either
            (assertFailure . show)
            pure
            Foundation.checkedFoundation
    let bound = CIntrinsic Empty
        predicate =
            CLam TySet
                (CEq TySet (CBound 0) (CBound 0))
        separation =
            CApp
                (CApp (CIntrinsic Sep) bound)
                predicate
    body <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalType
                []
                separation)
    definition <-
        maybe
            (assertFailure "separation did not form a set definition")
            pure
            (scopedSetDefinition
                (Foundation.foundationAxiomFrozen
                    foundation
                    Foundation.SeparationCharacteristic)
                body)
    let generated =
            instantiateCanonical
                separation
                (scopedCoreTerm definition)
        expected =
            betaNormalize
                (specializeForall predicate
                (specializeForall bound
                    (mapCanonicalGlobals absurd
                        (frozenCoreTerm
                            (Foundation.foundationAxiomFrozen
                                foundation
                                Foundation.SeparationCharacteristic)))))
    assertEqual
        "local characteristic is the checked rule specialization"
        expected
        generated

specializesCheckedReplacementCharacteristic :: Assertion
specializesCheckedReplacementCharacteristic = do
    foundation <-
        either
            (assertFailure . show)
            pure
            Foundation.checkedFoundation
    pair <- checked [] (CGlobal testPairGlobal)
    domain <- checked [] (CIntrinsic Empty)
    value <- checked [TySet] (CBound 0)
    (graph, checkedDomain, function) <-
        maybe
            (assertFailure "checked values did not form a replacement graph")
            pure
            (scopedReplacementGraph pair domain value)
    definition <-
        maybe
            (assertFailure "replacement graph did not form a definition")
            pure
            (scopedCharacteristicDefinition
                (Foundation.foundationAxiomFrozen
                    foundation
                    Foundation.ReplacementCharacteristic)
                graph
                (checkedDomain :| [function]))
    let generated =
            instantiateCanonical
                (scopedCoreTerm graph)
                (scopedCoreTerm definition)
        expected =
            betaNormalize
                (specializeForall (scopedCoreTerm function)
                (specializeForall (scopedCoreTerm checkedDomain)
                    (mapCanonicalGlobals absurd
                        (frozenCoreTerm
                            (Foundation.foundationAxiomFrozen
                                foundation
                                Foundation.ReplacementCharacteristic)))))
    assertEqual
        "local graph characteristic is the checked rule specialization"
        expected
        generated
  where
    checked context term =
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore testGlobalType context term)

derivesNamedConstructionViews :: Assertion
derivesNamedConstructionViews = do
    foundation <-
        either (assertFailure . show) pure Foundation.checkedFoundation
    bound <- checked [] (CIntrinsic Empty)
    predicate <- checked [TySet] (CEq TySet (CBound 0) (CBound 0))
    separation <-
        maybe
            (assertFailure "checked separation descriptor failed")
            pure
            (checkedSeparationConstruction testGlobalType bound predicate)
    (separationView, separationEquation) <-
        maybe
            (assertFailure "checked separation views failed")
            pure
            (namedSetConstructionLocalViews
                (checkedFoundationSetConstruction foundation)
                separation)
    expectedSeparationView <-
        maybe
            (assertFailure "checked separation characteristic failed")
            pure
            (scopedSetDefinition
                (Foundation.foundationAxiomFrozen foundation
                    Foundation.SeparationCharacteristic)
                (namedSetConstructionTerm separation))
    assertEqual "separation view is the checked specialization"
        expectedSeparationView separationView
    assertEqual "separation view is first-order"
        (Set.singleton Foundation.EmptyCharacteristic)
        (Foundation.foundationAxiomDependencies
            (scopedCoreTerm separationView))
    assertEqual "separation equation retains exact construction"
        (Set.fromList
            [ Foundation.EmptyCharacteristic
            , Foundation.SeparationCharacteristic
            ])
        (Foundation.foundationAxiomDependencies
            (scopedCoreTerm separationEquation))

    firstDomain <- checked [] (CIntrinsic Empty)
    singleValue <- checked [TySet] (CBound 0)
    singleCondition <- checked [TySet]
        (CEq TySet (CBound 0) (CBound 0))
    singleReplacement <-
        maybe
            (assertFailure "checked one-domain replacement failed")
            pure
            (checkedFunctionalReplacementConstruction
                testGlobalType
                (firstDomain :| [])
                singleValue
                (Just singleCondition))
    assertEqual "one-domain replacement has one canonical term"
        (CApp
            (CApp
                (CIntrinsic Repl)
                (CApp
                    (CApp (CIntrinsic Sep) (CIntrinsic Empty))
                    (CLam TySet
                        (CEq TySet (CBound 0) (CBound 0)))))
            (CLam TySet (CBound 0)))
        (scopedCoreTerm
            (namedSetConstructionTerm singleReplacement))

    secondDomain <- checked [TySet] (CBound 0)
    value <- checked [TySet, TySet] (CBound 0)
    condition <- checked [TySet, TySet]
        (CEq TySet (CBound 0) (CBound 0))
    replacement <-
        maybe
            (assertFailure "checked replacement descriptor failed")
            pure
            (checkedFunctionalReplacementConstruction
                testGlobalType
                (firstDomain :| [secondDomain])
                value
                (Just condition))
    (replacementView, replacementEquation) <-
        maybe
            (assertFailure "checked replacement views failed")
            pure
            (namedSetConstructionLocalViews
                (checkedFoundationSetConstruction foundation)
                replacement)
    let terminal =
            andP
                (CEq TySet (CBound 0) (CBound 0))
                (CEq TySet (CBound 2) (CBound 0))
        secondWitness =
            existsP
                (andP
                    (memberP (CBound 0) (CBound 1))
                    terminal)
        firstWitness =
            existsP
                (andP
                    (memberP (CBound 0) (CIntrinsic Empty))
                    secondWitness)
        expectedReplacementTerm =
            CForall TySet
                (CEq TyProp
                    (memberP (CBound 0) (CBound 1))
                    firstWitness)
    expectedReplacementView <- checked [TySet] expectedReplacementTerm
    assertEqual "replacement view preserves bounds and condition"
        expectedReplacementView replacementView
    assertEqual "flattened replacement view is first-order"
        (Set.singleton Foundation.EmptyCharacteristic)
        (Foundation.foundationAxiomDependencies
            (scopedCoreTerm replacementView))
    assertEqual "replacement equation retains every helper"
        (Set.fromList
            [ Foundation.FamilyUnionCharacteristic
            , Foundation.EmptyCharacteristic
            , Foundation.SeparationCharacteristic
            , Foundation.ReplacementCharacteristic
            ])
        (Foundation.foundationAxiomDependencies
            (scopedCoreTerm replacementEquation))
  where
    checked context term =
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore testGlobalType context term)

    memberP element set =
        CApp (CApp (CIntrinsic Member) element) set

    andP = CAnd

    existsP = CExists TySet

specializeForall
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
specializeForall argument = \case
    CForall _binderType body ->
        instantiateCanonical argument body
    _ ->
        error "the checked characteristic lost a binder"

betaNormalize :: CanonicalTerm global -> CanonicalTerm global
betaNormalize = \case
    CApp function argument ->
        case betaNormalize function of
            CLam _binderType body ->
                betaNormalize
                    (instantiateCanonical
                        (betaNormalize argument)
                        body)
            normalizedFunction ->
                CApp normalizedFunction (betaNormalize argument)
    CLam binderType body ->
        CLam binderType (betaNormalize body)
    CNot proposition ->
        CNot (betaNormalize proposition)
    CAnd left right ->
        CAnd (betaNormalize left) (betaNormalize right)
    COr left right ->
        COr (betaNormalize left) (betaNormalize right)
    CImp premise conclusion ->
        CImp
            (betaNormalize premise)
            (betaNormalize conclusion)
    CEq operandType left right ->
        CEq operandType
            (betaNormalize left)
            (betaNormalize right)
    CForall binderType body ->
        CForall binderType (betaNormalize body)
    CExists binderType body ->
        CExists binderType (betaNormalize body)
    term -> term
