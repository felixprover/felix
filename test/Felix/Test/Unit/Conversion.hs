{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Conversion (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion
import Felix.Test.Support.ConversionReference (referenceConvertibleWithLimit)
import Felix.Test.Support.GlobalTyping

import Data.Word (Word)
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)


unitTests :: TestTree
unitTests =
    testGroup "Checked closure conversion"
        [ testCase "compares beta-equivalent checked roots" comparesBetaRoots
        , testCase "normalizes through checked recovery" normalizesCheckedRoot
        , testCase "projects checked children after head residualization"
            projectsResidualizedConjunction
        , testCase "preserves neutral applications during head residualization"
            residualizesNeutralApplication
        , testCase "residualizes a checked membership operand without normalizing its sibling"
            residualizesCheckedMembershipSet
        , testCase "keeps neutral-spine traversal linear and charged"
            chargesNeutralSpineTraversal
        , testCase "charges every recursive selector payload comparison"
            chargesSelectorPayloadComparison
        , testCase "distinguishes selector heads, payloads, and arguments"
            distinguishesSelectorComparisons
        , testCase "keeps pending arguments in their capture environments"
            preservesPendingArgumentEnvironment
        , testCase "distinguishes identical closure code in different environments"
            distinguishesCapturedFunctionEnvironments
        , testCase "compares compact replay without expanding equal delayed arguments"
            comparesCompactReplay
        , testCase "checks congruence under captured and written binders"
            checksClosureCongruenceEnvironments
        , testCase "does not rescan a long neutral prefix with failed congruence probes"
            avoidsRepeatedCongruenceProbes
        , testCase "preserves higher-order neutral applications under binders"
            preservesHigherOrderNeutralApplications
        , testCase "compares opaque eta expansions but keeps beta readback distinct"
            comparesOpaqueFunctionEta
        , testCase "compares beta-eta through typed binders and neutral arguments"
            comparesTypedEta
        , testCase "bounds the independent reference including identical syntax"
            boundsReference
        , testCase "reports an exact deterministic exhaustion boundary"
            reportsExactBoundary
        , testCase "caps and debits zero and maximum currency values"
            checksCurrencyBoundaries
        , testCase "pins exact boundaries for representative outcomes"
            pinsRepresentativeBoundaries
        , testCase "ignores unrelated lawful snapshot extension"
            ignoresSnapshotExtension
        , testCase "does not force unrequested proposition children"
            leavesUnrequestedChildrenSuspended
        , testCase "residualizes the head without normalizing delayed children"
            preservesDelayedRedexesDuringResidualization
        , testCase "residualizes typed heads with capture-safe delayed arguments and bodies"
            residualizesTypedHeads
        , testCase "admits the whole head input and independently recovers its residual"
            admitsAndRecoversTypedHeads
        , testCase "prepares interleaved spines with exact prefixes and one allowance"
            preparesInterleavedSpines
        , testCase "admits complete spine inputs and independently recovers components"
            admitsAndRecoversSpines
        , testCase "obeys the checked conversion laws"
            obeysCheckedConversionLaws
        , testCase "preserves levels through quotation and binder extension"
            preservesLevelsThroughQuotation
        , testCase "pins identity, comparison, quotation, and materialization costs"
            pinsCoreConversionCosts
        , testCase "covers every canonical constructor without invariants"
            coversCanonicalConstructors
        , testCase "residualizes every neutral-head category"
            coversNeutralHeads
        , testPropertyNamed
            "agrees with substitution on generated checked terms"
            "prop_generatedDifferential"
            prop_generatedDifferential
        , testPropertyNamed
            "obeys conversion laws on generated checked terms"
            "prop_generatedConversionLaws"
            prop_generatedConversionLaws
        ]

ampleLimit :: ConversionLimit
ampleLimit = conversionLimit 10000

checked
    :: [CoreType]
    -> CanonicalTerm Void
    -> ScopedCheckedCore Void
checked context term =
    either (error . show) id
        (checkScopedCanonicalCore emptyGlobalTyping context term)

expectResult :: Show error => Either error value -> IO value
expectResult = either (assertFailure . show) pure

comparesBetaRoots :: Assertion
comparesBetaRoots = do
    let left = checked [] (CApp (CLam TyProp (CBound 0)) CTruth)
        right = checked [] CTruth
        report = convertibleChecked emptyGlobalTyping ampleLimit left right
    assertEqual "decision" (Right Convertible) (conversionResult report)
    assertBool "logical work is recorded"
        (conversionCostAmount (conversionCost report) > 0)

normalizesCheckedRoot :: Assertion
normalizesCheckedRoot = do
    let original = checked []
            (CApp (CLam TyProp (CNot (CBound 0))) CTruth)
        typing = ConversionRecoveryTyping
            emptyGlobalTyping emptyGlobalTyping
        report = betaNormalizeChecked typing ampleLimit original
    normal <- expectResult (conversionResult report)
    assertEqual "normal form" (CNot CTruth) (scopedCoreTerm normal)
    assertEqual "normal type" TyProp (scopedCoreType normal)
    assertEqual "normal context" [] (scopedCoreContext normal)

projectsResidualizedConjunction :: Assertion
projectsResidualizedConjunction = do
    let proposition = checked []
            (CApp (CLam TyProp (CAnd (CBound 0) CTruth)) CFalsum)
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    residual <- expectResult
        (conversionResult (residualizeHeadChecked typing ampleLimit proposition))
    case splitScopedConjunction residual of
        Just (left, right) -> do
            assertEqual "left checked child" (checked [] CFalsum) left
            assertEqual "right checked child" (checked [] CTruth) right
        Nothing -> assertFailure "head residualization lost the conjunction"

residualizesNeutralApplication :: Assertion
residualizesNeutralApplication = do
    let functionType = TySet `TyArrow` TySet
        application = checked [functionType]
            (CApp (CBound 0) (COpaqueInteger 7))
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    residual <- expectResult
        (conversionResult (residualizeHeadChecked typing ampleLimit application))
    assertEqual "neutral head, argument, type, and context" application residual

residualizesCheckedMembershipSet :: Assertion
residualizesCheckedMembershipSet = do
    let context = [TyArrow TySet TySet, TySet]
        identity = CLam TySet (CBound 0)
        element = foldl' (\term _ -> CApp identity term)
            (CBound 1) [1 .. 128 :: Int]
        delayed = CApp identity (CBound 1)
        selected = CApp identity (CApp (CBound 0) delayed)
        membership = checked context
            (CApp (CApp (CIntrinsic Member) element) selected)
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    case splitScopedMembership membership of
        Nothing -> assertFailure "checked membership projection failed"
        Just (projectedElement, projectedSet) -> do
            assertEqual "the sibling retains its written redexes"
                element (scopedCoreTerm projectedElement)
            let run limit = residualizeHeadChecked typing limit projectedSet
            residual <- expectResult (conversionResult (run ampleLimit))
            assertEqual "only the selected head is reduced, with its context retained"
                (checked context (CApp (CBound 0) delayed)) residual
            assertReportBoundary "selected membership set head" run

chargesNeutralSpineTraversal :: Assertion
chargesNeutralSpineTraversal = do
    costs <- forM [0, 1, 2, 8, 32] \arity -> do
        let functionType = foldr TyArrow TySet (replicate arity TySet)
            term = foldl' CApp (CBound 0)
                [COpaqueInteger integer | integer <- [0 .. fromIntegral arity - 1]]
            original = checked [functionType] term
            typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
            run limit = residualizeHeadChecked typing limit original
            report = run ampleLimit
        assertEqual "neutral application order, type, and context"
            (Right original) (conversionResult report)
        assertReportBoundary ("neutral residual arity " <> show arity) run
        pure (arity, conversionCostAmount (conversionCost report))
    case costs of
        [(0, base), (1, one), (2, two), (8, eight), (32, thirtyTwo)] -> do
            let step = one - base
            assertBool "arguments consume work" (step > 0)
            assertEqual "neutral residualization has a linear traversal cost"
                [base + 2 * step, base + 8 * step, base + 32 * step]
                [two, eight, thirtyTwo]
        _ -> assertFailure "neutral spine fixture changed"

chargesSelectorPayloadComparison :: Assertion
chargesSelectorPayloadComparison =
    forM_ [0, 1, 4, 16, 64] \depth -> do
        let payload = foldr TyArrow TySet (replicate depth TySet)
            selectorType = logicalSelectionType payload
            selector = CLogicalSelect payload
            left = checked [] selector
            right = checked [] (CApp (CLam selectorType (CBound 0)) selector)
            run limit = convertibleChecked emptyGlobalTyping limit left right
            report = run ampleLimit
            payloadSize = typeSize payload
            -- C1 costs T + 6; evaluation costs 9 + 3T; comparing semantic
            -- values, head types, and result types costs 1 + 2T. The head's
            -- payload comparison additionally visits every constructor of A.
            expectedCost = 16 + 6 * typeSize selectorType + payloadSize
        assertEqual "independent arrow-family constructor count"
            (2 * fromIntegral depth + 1) payloadSize
        assertEqual "selector beta equivalence"
            (Right Convertible) (conversionResult report)
        assertEqual "one charged visit per selector payload constructor"
            expectedCost (conversionCostAmount (conversionCost report))
        assertEqual "the independent substitution converter agrees"
            (Just True)
            (referenceConvertibleWithLimit 100000
                (scopedCoreTerm left) (scopedCoreTerm right))
        assertPinnedBoundary ("selector payload depth " <> show depth)
            expectedCost run

        let delayed = CApp (CLam TyProp (CBound 0))
                (CEq selectorType selector selector)
            delayedLeft = checked [] (CNot delayed)
            delayedRight = checked []
                (CApp (CLam TyProp (CNot (CBound 0))) delayed)
            compareDelayed limit = convertibleChecked emptyGlobalTyping limit
                delayedLeft delayedRight
            -- The congruence walk compares the equality operand type once
            -- and the two written selector payloads once each. Its remaining
            -- code, binder, environment and facade work is fixed.
            delayedCost = 51 + typeSize selectorType + 2 * payloadSize
        assertEqual "delayed selector equivalence"
            (Right Convertible)
            (conversionResult (compareDelayed ampleLimit))
        assertPinnedBoundary ("congruent selector payload depth " <> show depth)
            delayedCost compareDelayed
  where
    typeSize :: CoreType -> Word
    typeSize TyProp = 1
    typeSize TySet = 1
    typeSize (TyArrow domain result) = 1 + typeSize domain + typeSize result

distinguishesSelectorComparisons :: Assertion
distinguishesSelectorComparisons =
    forM_ fixtures \(scenario, leftTerm, rightTerm) -> do
        let left = checked [] leftTerm
            right = checked [] rightTerm
        assertEqual (scenario <> " has the same result type")
            (scopedCoreType left) (scopedCoreType right)
        forM_ [(left, right), (right, left)] \(first, second) -> do
            let run limit =
                    convertibleChecked emptyGlobalTyping limit first second
                report = run ampleLimit
            assertEqual (scenario <> " decision") (Right NotConvertible)
                (conversionResult report)
            assertEqual (scenario <> " substitution agreement")
                (Just False)
                (referenceConvertibleWithLimit 100000
                    (scopedCoreTerm first) (scopedCoreTerm second))
            assertReportBoundary scenario run
  where
    selectSet proposition =
        CApp (CLogicalSelect TySet) (CLam TySet proposition)
    fixtures =
        [ ("different head families", selectSet CTruth, COpaqueInteger 0)
        , ( "different selector payloads"
          , selectSet CTruth
          , CApp
                (CApp (CLogicalSelect (TyArrow TySet TySet))
                    (CLam (TyArrow TySet TySet) CTruth))
                (COpaqueInteger 0)
          )
        , ( "equal payloads with different arguments"
          , selectSet CTruth
          , selectSet CFalsum
          )
        ]

preservesPendingArgumentEnvironment :: Assertion
preservesPendingArgumentEnvironment = do
    let term =
            CApp
                (CApp
                    (CLam TySet
                        (CApp
                            (CLam TySet (CLam TySet (CBound 0)))
                            (CBound 0)))
                    (COpaqueInteger 1))
                (CBound 0)
        left = checked [TySet] term
        right = checked [TySet] (CBound 0)
        report = convertibleChecked emptyGlobalTyping ampleLimit left right
    assertEqual "captured outer argument"
        (Right Convertible) (conversionResult report)

reportsExactBoundary :: Assertion
reportsExactBoundary = do
    let left = checked [] (CApp (CLam TyProp (CBound 0)) CTruth)
        right = checked [] CTruth
        completed = convertibleChecked emptyGlobalTyping ampleLimit left right
        exactCost = conversionCostAmount (conversionCost completed)
        exact = convertibleChecked emptyGlobalTyping
            (conversionLimit exactCost) left right
        oneLess = convertibleChecked emptyGlobalTyping
            (conversionLimit (exactCost - 1)) left right
    assertEqual "exact limit result"
        (conversionResult completed) (conversionResult exact)
    assertEqual "exact repeated cost"
        (conversionCost completed) (conversionCost exact)
    assertEqual "one-less result"
        (Left (ConversionLimitExhausted (conversionLimit (exactCost - 1))))
        (conversionResult oneLess)
    assertEqual "one-less consumed cost"
        (exactCost - 1) (conversionCostAmount (conversionCost oneLess))

checksCurrencyBoundaries :: Assertion
checksCurrencyBoundaries = do
    let truth = checked [] CTruth
        maximumAmount = maxBound :: Word
        report = convertibleChecked emptyGlobalTyping (conversionLimit maximumAmount) truth truth
        cost = conversionCost report
        zero = convertibleChecked emptyGlobalTyping (conversionLimit 0) truth truth
    assertEqual "maximum allowance preserves the fixed root-identity cost"
        (Right Convertible, 4) (conversionResult report, conversionCostAmount cost)
    assertEqual "zero allowance records no unavailable work"
        (Left (ConversionLimitExhausted (conversionLimit 0)), 0)
        (conversionResult zero, conversionCostAmount (conversionCost zero))
    assertEqual "zero cost preserves the full pool"
        (Just (conversionPool maximumAmount))
        (debitConversionCost (conversionCost zero) (conversionPool maximumAmount))
    assertEqual "debit never wraps at the Word boundary"
        (Just (conversionPool (maximumAmount - 4))) (debitConversionCost cost (conversionPool maximumAmount))
    assertEqual "exact debit" (Just (conversionPool 0)) (debitConversionCost cost (conversionPool 4))
    assertEqual "overdraft is rejected" Nothing (debitConversionCost cost (conversionPool 3))
    forM_
        [ (0, maximumAmount, 0)
        , (maximumAmount, 0, 0)
        , (maximumAmount, maximumAmount, maximumAmount)
        , (3, 4, 3)
        , (4, 3, 3)
        ] $
        \(pool, request, expected) ->
            assertEqual "cap preserves the smaller allowance" (conversionLimit expected)
                (capConversionLimit (conversionPool pool) (conversionLimit request))

pinsRepresentativeBoundaries :: Assertion
pinsRepresentativeBoundaries = do
    let truth = checked [] CTruth
        falsum = checked [] CFalsum
        setValue = checked [] (COpaqueInteger 1)
    assertReportBoundary "not convertible"
        (\limit -> convertibleChecked emptyGlobalTyping limit truth falsum)
    assertReportBoundary "input failure"
        (\limit -> convertibleChecked emptyGlobalTyping limit truth setValue)
    let fullFixture = globalTypingFixture [TySet]
        emptyFixture = globalTypingFixture []
        operation = fixtureGlobalTyping fullFixture
        destination = fixtureGlobalTyping emptyFixture
        object = case fixtureObjectIds fullFixture of
            [single] -> single
            _ -> error "conversion recovery fixture changed arity"
    globalChecked <- expectResult
        (checkScopedCanonicalCore operation [] (CGlobal object))
    assertReportBoundary "recovery failure"
        (\limit ->
            betaNormalizeChecked
                (ConversionRecoveryTyping operation destination)
                limit globalChecked)

assertReportBoundary
    :: (Eq result, Show result)
    => String
    -> (ConversionLimit -> ConversionReport result)
    -> Assertion
assertReportBoundary scenario run = do
    let completed = run (conversionLimit 2000000)
        amount = conversionCostAmount (conversionCost completed)
        exact = run (conversionLimit amount)
        oneLess = run (conversionLimit (amount - 1))
    assertBool (scenario <> " consumed no work") (amount > 0)
    assertEqual (scenario <> " exact result")
        (conversionResult completed) (conversionResult exact)
    assertEqual (scenario <> " exact cost")
        (conversionCost completed) (conversionCost exact)
    assertEqual (scenario <> " one-less exhaustion")
        (Left (ConversionLimitExhausted (conversionLimit (amount - 1))))
        (conversionResult oneLess)

ignoresSnapshotExtension :: Assertion
ignoresSnapshotExtension = do
    let smallFixture = globalTypingFixture [TySet]
        extendedFixture = globalTypingFixture [TySet, TyProp]
        smallTyping = fixtureGlobalTyping smallFixture
        extendedTyping = fixtureGlobalTyping extendedFixture
        smallObject = case fixtureObjectIds smallFixture of
            [single] -> single
            _ -> error "small snapshot fixture changed arity"
        extendedObject = case fixtureObjectIds extendedFixture of
            firstObject : _ -> firstObject
            _ -> error "extended snapshot fixture is empty"
    assertEqual "stable object identity" smallObject extendedObject
    checkedGlobal <- expectResult
        (checkScopedCanonicalCore smallTyping [] (CGlobal smallObject))
    let underSmall = convertibleChecked smallTyping ampleLimit
            checkedGlobal checkedGlobal
        underExtended = convertibleChecked extendedTyping ampleLimit
            checkedGlobal checkedGlobal
    assertEqual "extension result"
        (conversionResult underSmall) (conversionResult underExtended)
    assertEqual "extension cost"
        (conversionCost underSmall) (conversionCost underExtended)

leavesUnrequestedChildrenSuspended :: Assertion
leavesUnrequestedChildrenSuspended = do
    let proposition = checked []
            (CAnd
                (CApp (CLam TyProp (CBound 0)) CTruth)
                (CApp (CLam TyProp (CBound 0)) CFalsum))
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    assertEqual "both delayed child redexes remain written"
        (Right proposition)
        (conversionResult (residualizeHeadChecked typing ampleLimit proposition))

preservesDelayedRedexesDuringResidualization :: Assertion
preservesDelayedRedexesDuringResidualization = do
    let delayedPremise = CApp (CLam TyProp (CBound 0)) CTruth
        original = checked []
            (CApp
                (CLam TySet
                    (CImp
                        delayedPremise
                        (CEq TySet (CBound 0) (CBound 0))))
                (COpaqueInteger 7))
        expected =
            CImp
                delayedPremise
                (CEq TySet
                    (COpaqueInteger 7)
                    (COpaqueInteger 7))
        typing = ConversionRecoveryTyping
            emptyGlobalTyping emptyGlobalTyping
        report = residualizeHeadChecked
            typing ampleLimit original
    residual <- expectResult (conversionResult report)
    assertEqual "weak-head residual"
        expected (scopedCoreTerm residual)

    assertReportBoundary "delayed premise head"
        (\limit -> residualizeHeadChecked typing limit original)

residualizesTypedHeads :: Assertion
residualizesTypedHeads = do
    forM_ cases \(scenario, context, originalTerm, expectedTerm) -> do
        let original = checked context originalTerm
            run limit = residualizeHeadChecked typing limit original
            report = run ampleLimit
        residual <- expectResult (conversionResult report)
        assertEqual (scenario <> " residual, type, and context")
            (expectedTerm, scopedCoreType original, context)
            (scopedCoreTerm residual, scopedCoreType residual, scopedCoreContext residual)
        assertEqual (scenario <> " independent beta equivalence")
            (Just True)
            (referenceConvertibleWithLimit 100000 originalTerm (scopedCoreTerm residual))
        assertReportBoundary scenario run
  where
    typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    betaSet = CApp (CLam TySet (CBound 0))
    pair left right = CApp (CApp (CIntrinsic PairSet) left) right
    cases =
        ( "open neutral application"
        , [TySet, TyArrow TySet TySet]
        , CApp
            (CLam (TyArrow TySet TySet) (CApp (CBound 0) (betaSet (CBound 1))))
            (CBound 1)
        , CApp (CBound 1) (betaSet (CBound 0))
        ) :
        [ ( "captured lambda " <> show ambient
          , [TySet, TySet]
          , CApp
                (CLam TySet (CLam TySet (pair (CBound 1) (betaSet (CBound 0)))))
                (betaSet (CBound ambient))
          , CLam TySet (pair (betaSet (CBound (ambient + 1))) (betaSet (CBound 0)))
          )
        | ambient <- [0, 1]
        ]

admitsAndRecoversTypedHeads :: Assertion
admitsAndRecoversTypedHeads = do
    let fixture = globalTypingFixture [TySet]
        full = fixtureGlobalTyping fixture
        missingTyping = fixtureGlobalTyping (globalTypingFixture [])
        object = case fixtureObjectIds fixture of
            [single] -> single
            _ -> error "typed head fixture changed arity"
        checkedGlobal = checkScopedCanonicalCore full []
        run operation destination root limit = residualizeHeadChecked
            (ConversionRecoveryTyping operation destination) limit root
    unused <- expectResult (checkedGlobal
        (CApp (CLam TySet (COpaqueInteger 0)) (CGlobal object)))
    global <- expectResult (checkedGlobal (CGlobal object))
    let missingUnused = run missingTyping full unused
        removedGlobal = run full missingTyping unused
        missingResidual = run full missingTyping global
    assertEqual "admission includes a global in an unused argument"
        (Left (ConversionInputFailure (ConversionAdmissionFailure UnknownCoreGlobal)))
        (conversionResult (missingUnused ampleLimit))
    assertEqual "destination admits only the materialized residual"
        (Right (COpaqueInteger 0))
        (fmap scopedCoreTerm (conversionResult (removedGlobal ampleLimit)))
    assertEqual "surviving globals must be visible in the destination"
        (Left (ConversionCheckedRecoveryFailure UnknownCoreGlobal))
        (conversionResult (missingResidual ampleLimit))
    forM_
        [ ("unused global admission", missingUnused)
        , ("discarded global recovery", removedGlobal)
        , ("missing residual global", missingResidual)
        ] (uncurry assertReportBoundary)

obeysCheckedConversionLaws :: Assertion
obeysCheckedConversionLaws = do
    let directTerm = COpaqueInteger 7
        betaTerm = CApp (CLam TySet (CBound 0)) directTerm
        nestedTerm = CApp (CLam TySet (CBound 0)) betaTerm
        direct = checked [] directTerm
        beta = checked [] betaTerm
        nested = checked [] nestedTerm
        decide left right =
            conversionResult
                (convertibleChecked emptyGlobalTyping ampleLimit left right)
    assertEqual "reflexivity" (Right Convertible) (decide beta beta)
    assertEqual "symmetry, forward" (decide beta direct)
        (decide direct beta)
    assertEqual "symmetry, decision" (Right Convertible)
        (decide beta direct)
    assertEqual "transitivity premise 1" (Right Convertible)
        (decide nested beta)
    assertEqual "transitivity premise 2" (Right Convertible)
        (decide beta direct)
    assertEqual "transitivity conclusion" (Right Convertible)
        (decide nested direct)

    let openLeftTerm =
            CApp (CLam TySet (CBound 1)) (COpaqueInteger 9)
        openRightTerm = CBound 0
        openLeft = checked [TySet] openLeftTerm
        openRight = checked [TySet] openRightTerm
        weakenedLeft = checked [TyProp, TySet]
            (shiftCanonical 1 0 openLeftTerm)
        weakenedRight = checked [TyProp, TySet]
            (shiftCanonical 1 0 openRightTerm)
    assertEqual "open conversion" (Right Convertible)
        (decide openLeft openRight)
    assertEqual "weakening" (Right Convertible)
        (decide weakenedLeft weakenedRight)

    let completed = convertibleChecked emptyGlobalTyping ampleLimit nested direct
        amount = conversionCostAmount (conversionCost completed)
        exact = convertibleChecked emptyGlobalTyping
            (conversionLimit amount) nested direct
        raised = convertibleChecked emptyGlobalTyping
            (conversionLimit (amount + 17)) nested direct
        repeated = convertibleChecked emptyGlobalTyping ampleLimit nested direct
    assertEqual "exact-limit result"
        (conversionResult completed) (conversionResult exact)
    assertEqual "raising-limit result"
        (conversionResult completed) (conversionResult raised)
    assertEqual "raising-limit completed cost"
        (conversionCost completed) (conversionCost raised)
    assertEqual "repeated result"
        (conversionResult completed) (conversionResult repeated)
    assertEqual "repeated cost"
        (conversionCost completed) (conversionCost repeated)

preservesLevelsThroughQuotation :: Assertion
preservesLevelsThroughQuotation = do
    let context = [TySet, TyProp, TyArrow TySet TySet]
        indexed = zip [0..] context
        typing = ConversionRecoveryTyping
            emptyGlobalTyping emptyGlobalTyping
    traverse_ (checkRoundTrip typing context) indexed

    let nestedTerm =
            CLam TyProp
                (CLam TySet
                    (CImp (CBound 1) (CBound 3)))
        nested = checked [TySet, TyProp] nestedTerm
        nestedNormal = betaNormalizeChecked typing ampleLimit nested
    normal <- expectResult (conversionResult nestedNormal)
    assertEqual "nested reflected and root levels"
        nestedTerm (scopedCoreTerm normal)

    let capturedTerm =
            CLam TyProp
                (CApp
                    (CLam TySet (CBound 1))
                    (COpaqueInteger 0))
        directTerm = CLam TyProp (CBound 0)
        captured = checked [] capturedTerm
        direct = checked [] directTerm
        comparison = convertibleChecked
            emptyGlobalTyping ampleLimit captured direct
        capturedNormal = betaNormalizeChecked typing ampleLimit captured
    assertEqual "closures captured at different depths"
        (Right Convertible) (conversionResult comparison)
    quoted <- expectResult (conversionResult capturedNormal)
    assertEqual "quotation preserves the reflected index"
        directTerm (scopedCoreTerm quoted)
  where
    checkRoundTrip typing context (index, coreType) = do
        let term = CBound index
            value = checked context term
            normalized = betaNormalizeChecked typing ampleLimit value
        normal <- expectResult (conversionResult normalized)
        assertEqual ("quoted index " <> show index)
            term (scopedCoreTerm normal)
        assertEqual ("quoted type " <> show index)
            coreType (scopedCoreType normal)

pinsCoreConversionCosts :: Assertion
pinsCoreConversionCosts = do
    let truth = checked [] CTruth
        identityReport limit =
            convertibleChecked emptyGlobalTyping limit truth truth
        captured = checked []
            (CLam TyProp
                (CApp
                    (CLam TySet (CBound 1))
                    (COpaqueInteger 0)))
        direct = checked [] (CLam TyProp (CBound 0))
        compareCaptured limit =
            convertibleChecked emptyGlobalTyping limit captured direct
        recoveryTyping = ConversionRecoveryTyping
            emptyGlobalTyping emptyGlobalTyping
        normalizeTruth limit =
            betaNormalizeChecked recoveryTyping limit truth
        delayedPremise = CApp (CLam TyProp (CBound 0)) CTruth
        residualInput = checked []
            (CApp
                (CLam TySet
                    (CImp delayedPremise
                        (CEq TySet (CBound 0) (CBound 0))))
                (COpaqueInteger 7))
        residualize limit =
            residualizeHeadChecked
                recoveryTyping limit residualInput
    assertPinnedBoundary "delegated pair identity" 4 identityReport
    assertPinnedBoundary "reflection and semantic comparison" 43 compareCaptured
    assertPinnedBoundary "quotation and checked recovery" 6 normalizeTruth
    assertPinnedBoundary "weak-head materialization" 51 residualize

    let early = checked [] (CAnd CTruth CTruth)
        mismatchFirst = checked [] (CAnd CFalsum CTruth)
        mismatchSecond = checked [] (CAnd CTruth CFalsum)
        firstReport = convertibleChecked
            emptyGlobalTyping ampleLimit early mismatchFirst
        secondReport = convertibleChecked
            emptyGlobalTyping ampleLimit early mismatchSecond
    assertEqual "first-child mismatch" (Right NotConvertible)
        (conversionResult firstReport)
    assertEqual "second-child mismatch" (Right NotConvertible)
        (conversionResult secondReport)
    assertBool "left-to-right comparison stops at the first mismatch"
        (conversionCostAmount (conversionCost firstReport)
            < conversionCostAmount (conversionCost secondReport))

assertPinnedBoundary
    :: (Eq result, Show result)
    => String
    -> Word
    -> (ConversionLimit -> ConversionReport result)
    -> Assertion
assertPinnedBoundary scenario expectedCost run = do
    let completed = run ampleLimit
        actualCost = conversionCostAmount (conversionCost completed)
    assertEqual (scenario <> " cost") expectedCost actualCost
    assertReportBoundary scenario run

coversCanonicalConstructors :: Assertion
coversCanonicalConstructors =
    traverse_ checkFixture fixtures
  where
    typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    checkFixture fixture = do
        _ <- expectResult (conversionResult (betaNormalizeChecked typing ampleLimit fixture))
        residual <- expectResult
            (conversionResult (residualizeHeadChecked typing ampleLimit fixture))
        assertEqual "typed head preserves independent beta semantics"
            (Just True)
            (referenceConvertibleWithLimit 100000
                (scopedCoreTerm fixture) (scopedCoreTerm residual))
    fixtures =
        [ checked [TySet] (CBound 0)
        , checked [] (CIntrinsic Empty)
        , checked [] (CLogicalSelect TySet)
        , checked [] (COpaqueInteger 1)
        , checked [] (CApp (CLam TySet (CBound 0)) (COpaqueInteger 1))
        , checked [] (CLam TySet (CBound 0))
        , checked [] CFalsum
        , checked [] CTruth
        , checked [] (CNot CTruth)
        , checked [] (CAnd CTruth CFalsum)
        , checked [] (COr CTruth CFalsum)
        , checked [] (CImp CTruth CFalsum)
        , checked [] (CEq TySet (COpaqueInteger 1) (CIntrinsic Empty))
        , checked [] (CForall TySet (CEq TySet (CBound 0) (CBound 0)))
        , checked [] (CExists TySet (CEq TySet (CBound 0) (CBound 0)))
        ]

coversNeutralHeads :: Assertion
coversNeutralHeads = do
    let fixture = globalTypingFixture [TySet]
        typing = fixtureGlobalTyping fixture
        object = case fixtureObjectIds fixture of
            [single] -> single
            _ -> error "conversion global fixture changed arity"
    globalChecked <- expectResult
        (checkScopedCanonicalCore typing [] (CGlobal object))
    checkHead typing globalChecked
    traverse_ (checkHead emptyGlobalTyping)
        [ checked [TySet] (CBound 0)
        , checked [] (CIntrinsic Empty)
        , checked [] (CLogicalSelect TySet)
        , checked [] (COpaqueInteger 1)
        ]
  where
    checkHead typing fixture =
        assertEqual "neutral head, type, and lexical context"
            (Right fixture)
            (conversionResult (residualizeHeadChecked
                (ConversionRecoveryTyping typing typing) ampleLimit fixture))

distinguishesCapturedFunctionEnvironments :: Assertion
distinguishesCapturedFunctionEnvironments = do
    let context = [TySet, TySet]
        capture argument =
            CApp (CLam TySet (CLam TySet (CBound 1))) argument
        left = checked context (capture (CBound 0))
        right = checked context (capture (CBound 1))
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
        compareAt limit = convertibleChecked emptyGlobalTyping limit left right
    assertEqual "the same lambda code retains different captured locals"
        (Right NotConvertible) (conversionResult (compareAt ampleLimit))
    leftNormal <- expectResult (conversionResult (betaNormalizeChecked typing ampleLimit left))
    rightNormal <- expectResult (conversionResult (betaNormalizeChecked typing ampleLimit right))
    assertEqual "the first closure captures the nearest outer set"
        (CLam TySet (CBound 1)) (scopedCoreTerm leftNormal)
    assertEqual "the second closure captures the next outer set"
        (CLam TySet (CBound 2)) (scopedCoreTerm rightNormal)
    assertReportBoundary "different captured function environments" compareAt

comparesCompactReplay :: Assertion
comparesCompactReplay =
    for_ [4, 8, 12, 16, 20 :: Int] \size -> do
        let pair first second = CApp (CApp (CIntrinsic PairSet) first) second
            duplicate = CLam TySet (pair (CBound 0) (CBound 0))
            previous = foldl' (\term _ -> CApp duplicate term)
                (CIntrinsic Empty) [1 .. size - 1]
            member term = CApp (CApp (CIntrinsic Member) term) (CBound 0)
            left = checked [TySet] (member (pair previous previous))
            right = checked [TySet] (member (CApp duplicate previous))
            compareAt limit = convertibleChecked emptyGlobalTyping limit left right
            report = compareAt ampleLimit
        assertEqual "compact replay completes at the ordinary test limit"
            (Right Convertible) (conversionResult report)
        assertEqual "compact written input determines linear replay cost"
            (73 * fromIntegral size + 65)
            (conversionCostAmount (conversionCost report))
        assertEqual "reverse compact replay"
            (Right Convertible)
            (conversionResult (convertibleChecked emptyGlobalTyping ampleLimit right left))
        assertReportBoundary ("compact replay " <> show size) compareAt

checksClosureCongruenceEnvironments :: Assertion
checksClosureCongruenceEnvironments =
    for_ cases \(scenario, leftTerm, rightTerm, expected) -> do
        let context = [TySet, TySet]
            left = checked context leftTerm
            right = checked context rightTerm
            compareAt limit = convertibleChecked emptyGlobalTyping limit left right
        assertEqual (scenario <> " independent reference")
            (Just (expected == Convertible))
            (referenceConvertibleWithLimit 100000 leftTerm rightTerm)
        assertEqual scenario (Right expected) (conversionResult (compareAt ampleLimit))
        assertEqual (scenario <> " reversed") (Right expected)
            (conversionResult (convertibleChecked emptyGlobalTyping ampleLimit right left))
        assertReportBoundary scenario compareAt
  where
    simple = CEq TySet (CBound 0) (COpaqueInteger 7)
    nested = CForall TyProp (CExists TySet
        (CEq (TyArrow TySet TySet)
            (CLam TySet (CBound 3)) (CLam TySet (CBound 1))))
    delayed body = CApp (CLam TyProp (CBound 0)) body
    capture body argument = CApp (CLam TySet (CNot (delayed body))) argument
    identity term = CApp (CLam TySet (CBound 0)) term
    cases =
        [ ( "same code with different captured locals"
          , capture simple (CBound 0), capture simple (CBound 1), NotConvertible)
        , ( "equivalent captured and direct environments"
          , capture simple (CBound 0), CNot (delayed simple), Convertible)
        , ( "captured alias chain"
          , CApp (CLam TySet (capture simple (CBound 0))) (CBound 0)
          , CNot (delayed simple), Convertible)
        , ( "unproved syntax falls through to beta conversion"
          , capture simple (identity (CBound 0)), CNot (delayed simple), Convertible)
        , ( "heterogeneous written binders with an open captured argument"
          , capture nested (CBound 0), CNot (delayed nested), Convertible)
        , ( "written binders do not hide a different captured local"
          , capture nested (CBound 1), CNot (delayed nested), NotConvertible)
        , ( "unused captured entries need not agree"
          , capture CTruth (CBound 0), capture CTruth (CBound 1), Convertible)
        ]

avoidsRepeatedCongruenceProbes :: Assertion
avoidsRepeatedCongruenceProbes = do
    costs <- forM [4, 8, 16, 32, 64 :: Int] \size -> do
        let term integer = foldl' (\child _ -> CApp (CIntrinsic PowerSet) child)
                (COpaqueInteger integer) [1 .. size]
            left = checked [] (term 0)
            right = checked [] (term 1)
            compareAt limit = convertibleChecked emptyGlobalTyping limit left right
            report = compareAt ampleLimit
        assertEqual "a difference after a long common neutral prefix"
            (Right NotConvertible) (conversionResult report)
        assertReportBoundary ("neutral prefix " <> show size) compareAt
        pure (conversionCostAmount (conversionCost report))
    for_ (zip costs (drop 1 costs)) \(smaller, larger) ->
        assertBool "doubling the input must not introduce quadratic probing"
            (larger <= 3 * smaller)

preservesHigherOrderNeutralApplications :: Assertion
preservesHigherOrderNeutralApplications = do
    let functionType = TyArrow TySet TySet
        higherType = TyArrow functionType functionType
        context = [higherType, TySet, TyProp]
        neutralTerm = CApp (CBound 0) (CLam TySet (CBound 2))
        betaTerm = CApp
            (CLam higherType
                (CApp (CBound 0) (CLam TySet (CBound 3))))
            (CBound 0)
        neutral = checked context neutralTerm
        beta = checked context betaTerm
        typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
        compareAt limit = convertibleChecked emptyGlobalTyping limit beta neutral
    assertEqual "a higher-order beta argument preserves its captured context"
        (Right Convertible) (conversionResult (compareAt ampleLimit))
    normal <- expectResult (conversionResult (betaNormalizeChecked typing ampleLimit beta))
    assertEqual "quotation retains the function-valued neutral application"
        neutralTerm (scopedCoreTerm normal)
    assertEqual "quotation preserves all ambient binders"
        context (scopedCoreContext normal)
    assertEqual "quotation preserves the arrow result type"
        functionType (scopedCoreType normal)
    assertReportBoundary "higher-order neutral application" compareAt

comparesOpaqueFunctionEta :: Assertion
comparesOpaqueFunctionEta = do
    let fixture = globalTypingFixture [TyArrow TySet TySet]
        typing = fixtureGlobalTyping fixture
    identity <- case fixtureObjectIds fixture of
        [single] -> pure single
        _ -> assertFailure "function fixture changed arity" >> fail "unreachable"
    opaqueFunction <- expectResult (checkScopedCanonicalCore typing [] (CGlobal identity))
    eta <- expectResult
        (checkScopedCanonicalCore typing []
            (CLam TySet (CApp (CGlobal identity) (CBound 0))))
    let compareAt limit = convertibleChecked typing limit opaqueFunction eta
    assertEqual "opaque functions compare extensionally without unfolding"
        (Right Convertible) (conversionResult (compareAt ampleLimit))
    assertEqual "the reverse orientation also opens the neutral"
        (Right Convertible)
        (conversionResult (convertibleChecked typing ampleLimit eta opaqueFunction))
    assertBool "structural equality remains distinct" (eta /= opaqueFunction)
    normal <- expectResult
        (conversionResult
            (betaNormalizeChecked (ConversionRecoveryTyping typing typing) ampleLimit eta))
    assertEqual "normalization leaves the opaque application and lambda intact"
        (scopedCoreTerm eta) (scopedCoreTerm normal)
    assertReportBoundary "opaque function eta" compareAt
    let missing = fixtureGlobalTyping (globalTypingFixture [])
    for_ [(opaqueFunction, eta), (eta, opaqueFunction)] \(left, right) ->
        assertEqual "eta cannot conceal a global missing from the current snapshot"
            (Left (ConversionInputFailure (ConversionAdmissionFailure UnknownCoreGlobal)))
            (conversionResult (convertibleChecked missing ampleLimit left right))

comparesTypedEta :: Assertion
comparesTypedEta = for_ cases \(scenario, context, leftTerm, rightTerm, expected) -> do
    let left = checked context leftTerm
        right = checked context rightTerm
    assertEqual (scenario <> " independent reference") (Just (expected == Convertible))
        (referenceConvertibleWithLimit 100000 leftTerm rightTerm)
    for_ [(left, right), (right, left)] \(source, target) -> do
        let compareAt limit = convertibleChecked emptyGlobalTyping limit source target
        assertEqual scenario (Right expected) (conversionResult (compareAt ampleLimit))
        assertReportBoundary scenario compareAt
  where
    function = TyArrow TySet TySet
    curried = TyArrow TySet function
    eta index = CLam TySet (CApp (CBound index) (CBound 0))
    cases =
        [ ("local function", [function], CBound 0, eta 1, Convertible)
        , ("curried function", [curried], CBound 0,
            CLam TySet (CLam TySet (CApp (CApp (CBound 2) (CBound 1)) (CBound 0))), Convertible)
        , ("arrow-valued binder", [], CLam function (CBound 0),
            CLam function (eta 1), Convertible)
        , ("neutral argument", [TyArrow function TyProp, function],
            CApp (CBound 0) (CBound 1), CApp (CBound 0) (eta 2), Convertible)
        , ("logical binder", [], CForall function (CEq function (CBound 0) (CBound 0)),
            CForall function (CEq function (CBound 0) (eta 1)), Convertible)
        , ("captured beta-eta", [function],
            CApp (CLam function (eta 1)) (CBound 0), CBound 0, Convertible)
        , ("fresh argument dependence", [curried],
            CLam TySet (CApp (CApp (CBound 1) (CBound 0)) (CBound 0)),
            CApp (CBound 0) (COpaqueInteger 0), NotConvertible)
        , ("distinct rigid heads", [function, function], eta 1, CBound 1, NotConvertible)
        , ("Boolean equivalence is not conversion", [TyProp],
            CAnd (CBound 0) CTruth, CBound 0, NotConvertible)
        , ("binder removal through quantifiers", [],
            CLam TySet (CForall TySet (CEq TySet (CBound 1) (CBound 0))),
            CLam TySet (CApp (CLam TySet (CForall TySet
                (CEq TySet (CBound 1) (CBound 0)))) (CBound 0)), Convertible)
        ]

boundsReference :: Assertion
boundsReference = do
    let truth = CTruth :: CanonicalTerm Void
    assertEqual "zero fuel is not an identity shortcut" Nothing
        (referenceConvertibleWithLimit 0 truth truth)
    assertEqual "final comparison is charged" Nothing
        (referenceConvertibleWithLimit 2 truth truth)
    assertEqual "two visits and the final comparison suffice" (Just True)
        (referenceConvertibleWithLimit 3 truth truth)

data TypedSource = TypedSource
    ![CoreType]
    !CoreType
    !(CanonicalTerm Void)
    deriving stock (Show, Eq)

prop_generatedDifferential :: Property
prop_generatedDifferential = withTests 120 $ property do
    TypedSource context coreType leftTerm <- forAll genTypedSource
    rightTerm <- forAll (genTypedTerm 5 context coreType)
    left <- evalEither
        (checkScopedCanonicalCore emptyGlobalTyping context leftTerm)
    right <- evalEither
        (checkScopedCanonicalCore emptyGlobalTyping context rightTerm)
    let referenceLimit = 100000
        reference = referenceConvertibleWithLimit referenceLimit leftTerm rightTerm
        production = convertibleChecked emptyGlobalTyping
            (conversionLimit 2000000) left right
    annotate ("independent substitution limit: " <> show referenceLimit)
    referenceDecision <- evalMaybe reference
    conversionResult production
        === Right (if referenceDecision then Convertible else NotConvertible)
    conversionResult (convertibleChecked emptyGlobalTyping
        (conversionLimit 2000000) right left) === conversionResult production
    let typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
    normal <- evalEither (conversionResult
        (betaNormalizeChecked typing (conversionLimit 2000000) left))
    residual <- evalEither (conversionResult
        (residualizeHeadChecked typing (conversionLimit 2000000) left))
    forM_ [normal, residual] \result -> do
        (scopedCoreType result, scopedCoreContext result) === (coreType, context)
        equivalence <- evalMaybe
            (referenceConvertibleWithLimit referenceLimit leftTerm (scopedCoreTerm result))
        equivalence === True

prop_generatedConversionLaws :: Property
prop_generatedConversionLaws = withTests 80 $ property do
    TypedSource context coreType term <- forAll genTypedSource
    original <- evalEither
        (checkScopedCanonicalCore emptyGlobalTyping context term)
    let betaTerm = CApp (CLam coreType (CBound 0)) term
        nestedTerm = CApp (CLam coreType (CBound 0)) betaTerm
    beta <- evalEither
        (checkScopedCanonicalCore emptyGlobalTyping context betaTerm)
    nested <- evalEither
        (checkScopedCanonicalCore emptyGlobalTyping context nestedTerm)
    let decide left right =
            convertibleChecked emptyGlobalTyping
                (conversionLimit 2000000) left right
    conversionResult (decide original original) === Right Convertible
    conversionResult (decide original beta) === Right Convertible
    conversionResult (decide beta original) === Right Convertible
    conversionResult (decide beta nested) === Right Convertible
    conversionResult (decide original nested) === Right Convertible

    let weakenedContext = TySet : context
        weakenedTerm = shiftCanonical 1 0 term
        weakenedBetaTerm = shiftCanonical 1 0 betaTerm
    weakened <- evalEither
        (checkScopedCanonicalCore
            emptyGlobalTyping weakenedContext weakenedTerm)
    weakenedBeta <- evalEither
        (checkScopedCanonicalCore
            emptyGlobalTyping weakenedContext weakenedBetaTerm)
    conversionResult (decide weakened weakenedBeta) === Right Convertible

    let completed = decide original nested
        amount = conversionCostAmount (conversionCost completed)
        exact = convertibleChecked emptyGlobalTyping
            (conversionLimit amount) original nested
        raised = convertibleChecked emptyGlobalTyping
            (conversionLimit (amount + 9)) original nested
    conversionResult exact === conversionResult completed
    conversionCost exact === conversionCost completed
    conversionResult raised === conversionResult completed
    conversionCost raised === conversionCost completed

    let typing = ConversionRecoveryTyping
            emptyGlobalTyping emptyGlobalTyping
        firstNormal = betaNormalizeChecked typing
            (conversionLimit 2000000) original
    normal <- evalEither (conversionResult firstNormal)
    let secondNormal = betaNormalizeChecked typing
            (conversionLimit 2000000) normal
    fmap scopedCoreTerm (conversionResult secondNormal)
        === Right (scopedCoreTerm normal)

genTypedSource :: Gen TypedSource
genTypedSource = do
    context <- Gen.list (Range.linear 0 5) genSmallType
    coreType <- genSmallType
    size <- Gen.int (Range.linear 0 6)
    TypedSource context coreType <$> genTypedTerm size context coreType

genSmallType :: Gen CoreType
genSmallType = go (3 :: Int)
  where
    go 0 = Gen.element [TySet, TyProp]
    go depth = Gen.frequency
        [ (3, Gen.element [TySet, TyProp])
        , (2, TyArrow <$> go (depth - 1) <*> go (depth - 1))
        ]

genTypedTerm
    :: Int
    -> [CoreType]
    -> CoreType
    -> Gen (CanonicalTerm Void)
genTypedTerm size context expected
    | size <= 0 = Gen.element (typedAtoms context expected)
    | otherwise = Gen.choice (terminal : recursive)
  where
    terminal = Gen.element (typedAtoms context expected)
    smaller = size - 1
    beta = do
        argumentType <- genSmallType
        body <- genTypedTerm smaller (argumentType : context) expected
        argument <- genTypedTerm (smaller `div` 2) context argumentType
        pure (CApp (CLam argumentType body) argument)
    neutralApplications =
        [ foldl' CApp headTerm
            <$> traverse (genTypedTerm (smaller `div` 2) context) domains
        | (headTerm, headType) <-
            [ (CBound (fromIntegral index), coreType)
            | (index, coreType) <- zip [0 :: Int ..] context
            ] <> [(CIntrinsic tag, coreIntrinsicType tag) | tag <- allIntrinsics]
        , domains <- applicationDomains headType
        ]
    applicationDomains = \case
        TyArrow domain result ->
            [[domain] | result == expected]
                <> ((domain :) <$> applicationDomains result)
        _ -> []
    equality = do
        operandType <- genSmallType
        CEq operandType
            <$> genTypedTerm smaller context operandType
            <*> genTypedTerm smaller context operandType
    quantified constructor = do
        binderType <- genSmallType
        constructor binderType
            <$> genTypedTerm smaller (binderType : context) TyProp
    recursive =
        beta : neutralApplications <> case expected of
            TySet -> []
            TyArrow domain result ->
                [ CLam domain <$> genTypedTerm smaller (domain : context) result
                , do
                    operand <- genTypedTerm smaller context expected
                    pure (CLam domain (CApp (shiftCanonical 1 0 operand) (CBound 0)))
                ]
            TyProp ->
                [ CNot <$> genTypedTerm smaller context TyProp
                , CAnd
                    <$> genTypedTerm smaller context TyProp
                    <*> genTypedTerm smaller context TyProp
                , COr
                    <$> genTypedTerm smaller context TyProp
                    <*> genTypedTerm smaller context TyProp
                , CImp
                    <$> genTypedTerm smaller context TyProp
                    <*> genTypedTerm smaller context TyProp
                , equality
                , quantified CForall
                , quantified CExists
                ]

typedAtoms :: [CoreType] -> CoreType -> [CanonicalTerm Void]
typedAtoms context expected =
    boundAtoms <> intrinsicAtoms <> structuralAtoms
  where
    boundAtoms =
        [ CBound (fromIntegral index)
        | (index, actual) <- zip [0 :: Int ..] context
        , actual == expected
        ]
    intrinsicAtoms =
        [ CIntrinsic intrinsic
        | intrinsic <- allIntrinsics
        , coreIntrinsicType intrinsic == expected
        ]
    structuralAtoms =
        case expected of
            TySet -> [COpaqueInteger 0, CIntrinsic Empty]
            TyProp -> [CTruth, CFalsum]
            TyArrow domain result ->
                [CLam domain (constantTerm result)]

    constantTerm = \case
        TySet -> COpaqueInteger 0
        TyProp -> CTruth
        TyArrow domain result -> CLam domain (constantTerm result)

allIntrinsics :: [CoreIntrinsicTag]
allIntrinsics =
    [ Member
    , Empty
    , PairSet
    , FamilyUnion
    , PowerSet
    , Sep
    , Repl
    , UnivOf
    , ISetLfp
    , GlobalChoice
    , OrderedPair
    , FirstProjection
    , SecondProjection
    ]

-- Observe ordinary checked components; the closed result itself stays opaque.
observeSpine
    :: PreparedSpine global
    -> ([Either CoreType (ScopedCheckedCore global)], ScopedCheckedCore global)
observeSpine prepared =
    (map step (preparedSpineSteps prepared), preparedSpineTerminal prepared)
  where
    step (PreparedUniversal coreType) = Left coreType
    step (PreparedPremise premise) = Right premise

preparesInterleavedSpines :: Assertion
preparesInterleavedSpines =
    forM_ [0 .. 32 :: Int] \size -> do
        let beta proposition = CApp (CLam TyProp (CBound 0)) proposition
            member left right = CApp (CApp (CIntrinsic Member) left) right
            -- Each block has heterogeneous binders and refers past its local
            -- binder to the preceding prefix. Premise redexes stay written.
            block rest = beta (CForall TySet
                (beta (CImp (beta (member (CBound 0) (CBound 1)))
                    (CForall TyProp (CImp (CBound 0)
                        (shiftCanonical 1 0 rest))))))
            source = checked [TySet] (foldr (const block) (beta CTruth) [1..size])
            typing = ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping
            run limit = prepareImplicationSpineChecked typing limit source
            completed = run (conversionLimit 2000000)
            amount = conversionCostAmount (conversionCost completed)
        prepared <- expectResult (conversionResult completed)
        assertEqual "source-order metadata and premises" (4 * size)
            (length (preparedSpineSteps prepared))
        let verify context [] =
                assertEqual "terminal lexical context" context
                    (scopedCoreContext (preparedSpineTerminal prepared))
            verify context (step : rest) = case step of
                PreparedUniversal coreType -> verify (coreType : context) rest
                PreparedPremise premise -> do
                    assertEqual "premise lexical prefix" context (scopedCoreContext premise)
                    assertBool "unrequested premise redexes stay written"
                        (case scopedCoreTerm premise of
                            CApp (CLam TyProp (CBound 0)) _ -> True
                            CBound 0 -> True
                            _ -> False)
                    assertEqual "full checker agrees" (Right premise)
                        (checkScopedCanonicalCore emptyGlobalTyping context
                            (scopedCoreTerm premise))
                    verify context rest
        verify [TySet] (preparedSpineSteps prepared)
        let rebuilt = foldr (\step rest -> case step of
                PreparedUniversal coreType -> CForall coreType rest
                PreparedPremise premise -> CImp (scopedCoreTerm premise) rest)
                (scopedCoreTerm (preparedSpineTerminal prepared))
                (preparedSpineSteps prepared)
        _ <- expectResult (checkScopedCanonicalCore emptyGlobalTyping [TySet] rebuilt)
        assertEqual "independent substitution semantics" (Just True)
            (referenceConvertibleWithLimit 2000000 (scopedCoreTerm source) rebuilt)
        assertEqual "zero compound allowance"
            (Left (ConversionLimitExhausted (conversionLimit 0)))
            (observeSpine <$> conversionResult (run (conversionLimit 0)))
        assertEqual "exact compound allowance" (Right (observeSpine prepared))
            (observeSpine <$> conversionResult (run (conversionLimit amount)))
        assertEqual "deterministic completed cost" (conversionCost completed)
            (conversionCost (run (conversionLimit amount)))
        let short = run (conversionLimit (amount - 1))
        assertEqual "one-short allowance is shared by every suffix"
            (Left (ConversionLimitExhausted (conversionLimit (amount - 1))))
            (observeSpine <$> conversionResult short)
        assertEqual "failure retains consumed work" (amount - 1)
            (conversionCostAmount (conversionCost short))

admitsAndRecoversSpines :: Assertion
admitsAndRecoversSpines = do
    let fixture = globalTypingFixture [TySet]
        full = fixtureGlobalTyping fixture
        missing = fixtureGlobalTyping (globalTypingFixture [])
        extended = fixtureGlobalTyping (globalTypingFixture [TySet, TyProp])
    identity <- case fixtureObjectIds fixture of
        [object] -> pure object
        _ -> assertFailure "expected one global" >> fail "unreachable"
    let erased = CApp (CLam TySet (CImp CTruth CTruth)) (CGlobal identity)
        surviving = CImp CTruth (CEq TySet (CGlobal identity) (CGlobal identity))
        unusedBody = CImp CTruth (CApp (CLam (TyArrow TySet TySet) CTruth)
            (CLam TySet (CGlobal identity)))
    forM_ [erased, surviving, unusedBody] \term -> do
        source <- expectResult (checkScopedCanonicalCore full [] term)
        let run typing limit = prepareImplicationSpineChecked typing limit source
            rejected = run (ConversionRecoveryTyping missing full) ampleLimit
            amount = conversionCostAmount (conversionCost rejected)
            inputFailure = Left (ConversionInputFailure
                (ConversionAdmissionFailure UnknownCoreGlobal))
        assertEqual "admission precedes any projection or erasure" inputFailure
            (observeSpine <$> conversionResult rejected)
        assertEqual "failure exact cost" (conversionCost rejected)
            (conversionCost (run (ConversionRecoveryTyping missing full)
                (conversionLimit amount)))
        assertEqual "failure one short"
            (Left (ConversionLimitExhausted (conversionLimit (amount - 1))))
            (observeSpine <$> conversionResult
                (run (ConversionRecoveryTyping missing full) (conversionLimit (amount - 1))))
        let current = run (ConversionRecoveryTyping full full) ampleLimit
            extension = run (ConversionRecoveryTyping extended extended) ampleLimit
        assertEqual "lawful extension preserves components"
            (observeSpine <$> conversionResult current)
            (observeSpine <$> conversionResult extension)
        assertEqual "unrelated extension adds no work"
            (conversionCost current) (conversionCost extension)
    source <- expectResult (checkScopedCanonicalCore full [] erased)
    result <- expectResult (conversionResult (prepareImplicationSpineChecked
        (ConversionRecoveryTyping full missing) ampleLimit source))
    assertEqual "erased globals are absent from recovered output" CTruth
        (scopedCoreTerm (preparedSpineTerminal result))
    retained <- expectResult (checkScopedCanonicalCore full [] surviving)
    case conversionResult (prepareImplicationSpineChecked
            (ConversionRecoveryTyping full missing) ampleLimit retained) of
        Left (ConversionCheckedRecoveryFailure UnknownCoreGlobal) -> pure ()
        other -> assertFailure ("surviving global recovery: " <> show (observeSpine <$> other))
    let wrongType = prepareImplicationSpineChecked
            (ConversionRecoveryTyping emptyGlobalTyping emptyGlobalTyping)
            ampleLimit (checked [] (COpaqueInteger 0))
    case conversionResult wrongType of
        Left (ConversionInputFailure (ConversionRootTypeMismatch TyProp TySet)) -> pure ()
        other -> assertFailure ("spine root type: " <> show (observeSpine <$> other))
