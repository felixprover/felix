{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Backend (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Backend.Problem
import Felix.Checking.Backend.Tptp
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , emptyGlobalTyping
    )
import Felix.Checking.Identity (ObjectId)
import Felix.Provers
import Felix.Test.Support.GlobalTyping
import Tptp.UnsortedFirstOrder qualified as Tptp

import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit


testGlobalFixture :: GlobalTypingFixture
testGlobalFixture =
    globalTypingFixture
        [ TySet `TyArrow` TyProp
        , (TySet `TyArrow` TyProp) `TyArrow` TyProp
        ]

testGlobalTyping :: GlobalTyping ObjectId
testGlobalTyping = fixtureGlobalTyping testGlobalFixture

firstOrderPredicate, higherOrderPredicate :: ObjectId
(firstOrderPredicate, higherOrderPredicate) =
    case fixtureObjectIds testGlobalFixture of
        [firstOrder, higherOrder] -> (firstOrder, higherOrder)
        _ -> error "the backend global fixture changed arity"

data TestLocal
    = ObjectLocal
    | PredicateLocal
    deriving (Show, Eq, Ord)

unitTests :: TestTree
unitTests =
    testGroup "Typed backend problem"
        [ testCase
            "projects proposition equality as equivalence"
            classifiesPropositionEquality
        , testCase
            "projects exact ambient support"
            projectsExactAmbientSupport
        , testCase
            "routes selected and local-only problems"
            routesCompleteProblems
        , testCase
            "routes checked higher-order constructions"
            routesHigherOrderConstructions
        , testCase
            "renders checked FOF and TH0 problems"
            rendersCheckedProblems
        , testCase
            "renders native Core with tuned prover Boolean forms"
            rendersNativeLogicalForms
        , testCase
            "renders one logical-selection witness per selected type"
            rendersTypeIndexedLogicalSelection
        , testCase
            "renders predicate equality through TH0"
            rendersPredicateEquality
        , testCase
            "projects global choice through FOF"
            projectsGlobalChoiceThroughFof
        ]

classifiesPropositionEquality :: Assertion
classifiesPropositionEquality = do
    proposition <-
        checkedProposition
            Vector.empty
            (CEq TyProp CFalsum CFalsum)
    capability <-
        either
            (assertFailure . show)
            pure
            (classifySupportedProposition
                testGlobalTyping
                proposition)
    case capability of
        FofProjectable{} ->
            pure ()
        RequiresTh0 exclusions ->
            assertFailure
                ("proposition equality was not projected: "
                    <> show exclusions)

projectsExactAmbientSupport :: Assertion
projectsExactAmbientSupport = do
    let term :: CanonicalTerm Void
        term =
            CForall TySet
                (CEq TySet
                    (CBound 1)
                    (CBound 3))
    scoped <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                emptyGlobalTyping
                [TySet, TySet, TySet]
                term)
    projected <-
        either
            (assertFailure . show)
            pure
            (projectSupportedProposition
                emptyGlobalTyping
                (Vector.fromList
                    [ (0 :: Int, TySet)
                    , (1, TySet)
                    , (2, TySet)
                    ])
                scoped)
    assertEqual
        "unused middle support is removed"
        (Vector.fromList
            [ (0 :: Int, TySet)
            , (2, TySet)
            ])
        (supportedPropositionSupport projected)
    assertEqual
        "indices are remapped below nested binders"
        (CForall TySet
            (CEq TySet
                (CBound 1)
                (CBound 2)))
        (supportedPropositionTerm projected)

routesCompleteProblems :: Assertion
routesCompleteProblems = do
    fofFact <-
        checkedBackendFact
            (0 :: Int)
            firstOrderClaim
    th0Fact <-
        checkedBackendFact
            (1 :: Int)
            higherOrderClaim
    let fofFacts =
            Vector.singleton fofFact
        th0Facts =
            Vector.singleton th0Fact
    claim <-
        checkedProposition
            (Vector.singleton
                (ObjectLocal, TySet))
            (CApp
                (CGlobal firstOrderPredicate)
                (CBound 0))
    firstOrderLocal <-
        checkedLocalPremise
            0
            "first-order local"
            claim
    higherOrderLocalProposition <-
        checkedProposition
            (Vector.singleton
                (PredicateLocal,
                    TySet `TyArrow` TyProp))
            (CApp
                (CGlobal higherOrderPredicate)
                (CBound 0))
    higherOrderLocal <-
        checkedLocalPremise
            1
            "higher-order local"
            higherOrderLocalProposition

    projected <-
        planned
            fofFacts
            claim
            [higherOrderLocal, firstOrderLocal]
            []
            FirstOrderLocals
    assertEqual "projected route" RouteFof
        (typedProblemRoute projected)
    assertEqual "projected FOF globals" [0]
        (typedBackendFactReference
            <$> toList
                (typedProblemGlobalPremises
                    projected))
    assertEqual "first-order local only" [0]
        (localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList
                (typedProblemLocalPremises
                    projected))

    explicitFof <-
        planned
            fofFacts
            claim
            [higherOrderLocal, firstOrderLocal]
            []
            FirstOrderLocals
    assertEqual "explicit FOF route" RouteFof
        (typedProblemRoute explicitFof)
    assertEqual "explicit FOF references retain only FOF locals" [0]
        (localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList
                (typedProblemLocalPremises explicitFof))

    explicitTh0 <-
        planned
            th0Facts
            claim
            [higherOrderLocal, firstOrderLocal]
            []
            CompleteLocals
    assertEqual "explicit TH0 route" RouteTh0
        (typedProblemRoute explicitTh0)
    assertEqual "explicit TH0 references retain complete locals" [0, 1]
        (localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList
                (typedProblemLocalPremises explicitTh0))

    localOnly <-
        planned
            Vector.empty
            claim
            [higherOrderLocal, firstOrderLocal]
            []
            CompleteLocals
    assertEqual "local-only TH0 route" RouteTh0
        (typedProblemRoute localOnly)
    assertEqual "local order restored" [0, 1]
        (localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList
                (typedProblemLocalPremises
                    localOnly))
    assertEqual
        "complete ambient local inventory"
        (Map.fromList
            [ (ObjectLocal, TySet)
            , (PredicateLocal,
                TySet `TyArrow` TyProp)
            ])
        (typedProblemLocalTypes localOnly)

    case planTypedProblem
            testGlobalTyping
            Vector.empty
            claim
            [firstOrderLocal, firstOrderLocal]
            []
            CompleteLocals of
        Left
            (TypedProblemDuplicateLocalPremiseOrdinal
                duplicateOrdinal) ->
                    assertEqual
                        "duplicate local ordinal"
                        0
                        (localPremiseOrdinalValue
                            duplicateOrdinal)
        result ->
            assertFailure
                ("expected duplicate local ordinal error, got "
                    <> showProblemResult result)

    higherOrderClaimProposition <-
        checkedProposition
            Vector.empty
            higherOrderClaim
    higherOrderProblem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                fofFacts
                higherOrderClaimProposition
                []
                []
                FirstOrderLocals)
    assertEqual "higher-order claim route" RouteTh0
        (typedProblemRoute higherOrderProblem)
    checkedFoundationValue <-
        either
            (assertFailure . show)
            pure
            Foundation.checkedFoundation
    auxiliaryProblem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                fofFacts
                claim
                []
                [typedFoundationAuxiliaryInput
                    checkedFoundationValue
                    Foundation.SeparationCharacteristic]
                FirstOrderLocals)
    assertEqual "higher-order auxiliary route" RouteTh0
        (typedProblemRoute auxiliaryProblem)
    unusedContext <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalTyping
                [TySet `TyArrow` TyProp]
                firstOrderClaim)
    case supportedProposition
            (Vector.singleton
                (PredicateLocal,
                    TySet `TyArrow` TyProp))
            unusedContext of
        Left (UnusedSupportedLocal PredicateLocal) ->
            pure ()
        Left err ->
            assertFailure
                ("unexpected exact-support error: "
                    <> show err)
        Right _ ->
            assertFailure
                "unused ambient local entered exact support"
  where
    planned selectedFacts claim locals auxiliaries localPolicy =
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                selectedFacts
                claim
                locals
                auxiliaries
                localPolicy)

    showProblemResult = \case
        Left err ->
            show err
        Right problem ->
            show (typedProblemRoute problem)

routesHigherOrderConstructions :: Assertion
routesHigherOrderConstructions = do
    checkedFoundationValue <-
        either
            (assertFailure . show)
            pure
            Foundation.checkedFoundation
    let separation =
            CApp
                (CApp
                    (CIntrinsic Sep)
                    (CIntrinsic Empty))
                (CLam TySet
                    (CApp
                        (CGlobal higherOrderPredicate)
                        (CLam TySet CFalsum)))
        separationClaim =
            CEq TySet separation separation
        filteredDomain =
            CApp
                (CApp
                    (CIntrinsic Sep)
                    (CBound 0))
                (CLam TySet
                    (CEq TySet (CBound 0) (CBound 0)))
        innerReplacement =
            CApp
                (CApp (CIntrinsic Repl) filteredDomain)
                (CLam TySet (CBound 0))
        functionalReplacement =
            CApp
                (CIntrinsic FamilyUnion)
                (CApp
                    (CApp
                        (CIntrinsic Repl)
                        (CIntrinsic Empty))
                    (CLam TySet innerReplacement))
        replacementClaim =
            CEq TySet functionalReplacement functionalReplacement
        replacementTags =
            [ Foundation.FamilyUnionCharacteristic
            , Foundation.SeparationCharacteristic
            , Foundation.ReplacementCharacteristic
            ]
        auxiliary tag =
            typedFoundationAuxiliaryInput
                checkedFoundationValue tag
        plan selected claim locals tags =
            planTypedProblem
                testGlobalTyping
                selected
                claim
                locals
                (auxiliary <$> tags)
                FirstOrderLocals

    separationProposition <-
        checkedProposition Vector.empty separationClaim
    separationProblem <-
        either
            (assertFailure . show)
            pure
            (plan
                Vector.empty
                separationProposition
                []
                [Foundation.SeparationCharacteristic])
    assertEqual "separation route" RouteTh0
        (typedProblemRoute separationProblem)
    assertEqual "separation characteristic only"
        [Foundation.SeparationCharacteristic]
        (typedProblemAuxiliaryTag
            <$> toList (typedProblemAuxiliaries separationProblem))
    assertEqual "separation selects no global premise"
        0
        (Vector.length (typedProblemGlobalPremises separationProblem))

    replacementProposition <-
        checkedProposition Vector.empty replacementClaim
    replacementProblem <-
        either
            (assertFailure . show)
            pure
            (plan
                Vector.empty
                replacementProposition
                []
                replacementTags)
    assertEqual "functional replacement route" RouteTh0
        (typedProblemRoute replacementProblem)
    assertEqual "functional replacement exact helper set"
        replacementTags
        (typedProblemAuxiliaryTag
            <$> toList (typedProblemAuxiliaries replacementProblem))

    firstOrderProposition <-
        checkedProposition Vector.empty firstOrderClaim
    firstOrderLocal <-
        checkedLocalPremise 0 "first-order" firstOrderProposition
    separationLocal <-
        checkedLocalPremise 2 "separation" separationProposition
    unrelatedLocalProposition <-
        checkedProposition
            (Vector.singleton
                (PredicateLocal, TySet `TyArrow` TyProp))
            (CApp
                (CGlobal higherOrderPredicate)
                (CBound 0))
    unrelatedLocal <-
        checkedLocalPremise 1 "unrelated higher-order" unrelatedLocalProposition
    separationWithLocals <-
        either
            (assertFailure . show)
            pure
            (plan
                Vector.empty
                separationProposition
                [unrelatedLocal, firstOrderLocal]
                [Foundation.SeparationCharacteristic])
    assertEqual "inline separation keeps unrelated HO local out" RouteTh0
        (typedProblemRoute separationWithLocals)
    assertEqual "inline separation retains only FOF local" [0]
        ( localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList (typedProblemLocalPremises separationWithLocals)
        )
    assertEqual "excluded HO local adds no auxiliary"
        [Foundation.SeparationCharacteristic]
        (typedProblemAuxiliaryTag
            <$> toList (typedProblemAuxiliaries separationWithLocals))
    localProblem <-
        either
            (assertFailure . show)
            pure
            (plan
                Vector.empty
                firstOrderProposition
                [unrelatedLocal, separationLocal, firstOrderLocal]
                [])
    assertEqual "higher-order local remains excluded" RouteFof
        (typedProblemRoute localProblem)
    assertEqual "unrelated higher-order local remains unselected"
        [0]
        ( localPremiseOrdinalValue
            . typedLocalPremiseOrdinal
            <$> toList (typedProblemLocalPremises localProblem)
        )

    higherOrderFact <- checkedBackendFact (1 :: Int) higherOrderClaim
    expectRoute
        "higher-order global selects TH0"
        RouteTh0
        (plan
            (Vector.singleton higherOrderFact)
            separationProposition
            []
            [Foundation.SeparationCharacteristic])

    ordinaryHigherOrder <-
        checkedProposition Vector.empty
            (CEq TySet
                (CApp
                    (CLogicalSelect TySet)
                    (CLam TySet CFalsum))
                (CIntrinsic Empty))
    expectRoute
        "ordinary higher-order target selects TH0"
        RouteTh0
        (plan Vector.empty ordinaryHigherOrder [] [])
    mixedHigherOrder <-
        checkedProposition Vector.empty
            (CImp
                separationClaim
                (supportedPropositionTerm ordinaryHigherOrder))
    expectRoute
        "mixed higher-order target selects TH0"
        RouteTh0
        (plan
            Vector.empty
            mixedHigherOrder
            []
            [Foundation.SeparationCharacteristic])

    expectRoute
        "higher-order auxiliary selects TH0"
        RouteTh0
        (plan
            Vector.empty
            firstOrderProposition
            []
            [Foundation.SeparationCharacteristic])
  where
    expectRoute label expected =
        either
            (assertFailure . ((label <> ": ") <>) . show)
            (assertEqual label expected . typedProblemRoute)

rendersCheckedProblems :: Assertion
rendersCheckedProblems = do
    fofFact <-
        checkedBackendFact
            (0 :: Int)
            firstOrderClaim
    th0Fact <-
        checkedBackendFact
            (1 :: Int)
            higherOrderClaim
    claim <-
        checkedProposition
            (Vector.singleton
                (ObjectLocal, TySet))
            (CApp
                (CGlobal firstOrderPredicate)
                (CBound 0))
    fofProblem <-
        planned
            (Vector.singleton fofFact)
            claim
            FirstOrderLocals
    th0Problem <-
        planned
            (Vector.singleton th0Fact)
            claim
            CompleteLocals
    preparedFof <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem
                fofProblem)
    preparedTh0 <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem
                th0Problem)
    proverTask <-
        either
            (assertFailure . show)
            pure
            (prepareTypedProverTask
                DirectTask
                th0Problem)
    assertEqual "FOF route" RouteFof
        (preparedTypedTptpRoute preparedFof)
    assertBool "FOF formulas"
        ("fof(tg_h0,axiom,"
            `Text.isInfixOf`
                preparedTypedTptpText
                    preparedFof)
    assertBool "FOF has no TH0 declarations"
        (not
            ("thf("
                `Text.isInfixOf`
                    preparedTypedTptpText
                        preparedFof))
    assertEqual "TH0 route" RouteTh0
        (preparedTypedTptpRoute preparedTh0)
    assertEqual "TH0 request dialect"
        VerificationTh0
        (preparedVerificationDialect
            (preparedTypedProverRequest
                proverTask))
    assertEqual "request preserves exact prepared text"
        (preparedTypedTptpText preparedTh0)
        (preparedVerificationText
            (preparedTypedProverRequest
                proverTask))
    for_
        [ "thf(tg_h0,axiom,"
        , "^ [V0:$i]"
        , "thf(tg_q0,conjecture,"
        ]
        \fragment ->
            assertBool
                ("TH0 contains " <> Text.unpack fragment)
                (fragment
                    `Text.isInfixOf`
                        preparedTypedTptpText
                            preparedTh0)
    for_
        (Map.keys
            (preparedTypedTptpNameOrigins
                preparedTh0))
        \target ->
            assertBool
                ("valid generated name " <> Text.unpack target)
                (if "V" `Text.isPrefixOf` target
                    then Tptp.isProperVariable target
                    else Tptp.isProperAtomicWord target)
  where
    planned selectedFacts claim localPolicy =
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                selectedFacts
                claim
                []
                []
                localPolicy)

rendersNativeLogicalForms :: Assertion
rendersNativeLogicalForms = do
    let atom index =
            CApp
                (CGlobal firstOrderPredicate)
                (CBound index)
        firstOrderTerm =
            CForall TySet
                (CAnd
                    CTruth
                    (COr
                        (CNot (atom 0))
                        (CExists TySet
                            (CAnd (atom 1) (atom 0)))))
        predicateType = TySet `TyArrow` TyProp
        higherOrderTerm =
            CForall predicateType
                (CExists TySet
                    (CAnd
                        CTruth
                        (COr
                            (CNot
                                (CApp (CBound 1) (CBound 0)))
                            (atom 0))))
    firstOrder <- checkedClosedProposition firstOrderTerm
    firstOrderProblem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                Vector.empty
                firstOrder
                []
                []
                FirstOrderLocals)
    assertEqual
        "native logical nodes preserve first-order eligibility"
        RouteFof
        (typedProblemRoute firstOrderProblem)
    renderedFof <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem firstOrderProblem)
    let fofText = preparedTypedTptpText renderedFof
    traverse_
        (\fragment ->
            assertBool
                ("FOF contains " <> Text.unpack fragment)
                (fragment `Text.isInfixOf` fofText))
        [ "$true"
        , "~"
        , "?["
        , "=>$false"
        ]
    assertBool
        "FOF normalizes conjunction and disjunction"
        (not ("&" `Text.isInfixOf` fofText)
            && not ("|" `Text.isInfixOf` fofText))

    higherOrder <- checkedClosedProposition higherOrderTerm
    higherOrderProblem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                Vector.empty
                higherOrder
                []
                []
                CompleteLocals)
    assertEqual "higher-order binder route" RouteTh0
        (typedProblemRoute higherOrderProblem)
    renderedTh0 <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem higherOrderProblem)
    let th0Text = preparedTypedTptpText renderedTh0
    traverse_
        (\fragment ->
            assertBool
                ("TH0 contains " <> Text.unpack fragment)
                (fragment `Text.isInfixOf` th0Text))
        [ "$true"
        , "~"
        , "? ["
        , "=>$false"
        ]
    assertBool
        "TH0 normalizes conjunction and disjunction"
        (not ("&" `Text.isInfixOf` th0Text)
            && not ("|" `Text.isInfixOf` th0Text))

rendersTypeIndexedLogicalSelection :: Assertion
rendersTypeIndexedLogicalSelection = do
    let selectedType = TyArrow TySet TySet
        noFacts :: Vector (TypedBackendFact Int ObjectId)
        noFacts = Vector.empty
        predicate =
            CLam selectedType
                (CEq selectedType (CBound 0) (CBound 0))
        selected =
            CApp
                (CLogicalSelect selectedType)
                predicate
    claim <-
        checkedClosedProposition
            (CEq selectedType selected selected)
    problem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                noFacts
                claim
                []
                []
                CompleteLocals)
    assertEqual "selection route" RouteTh0
        (typedProblemRoute problem)
    assertEqual "one selected type despite repeated occurrences"
        [selectedType]
        ( typedLogicalSelectionAuxiliaryType
            <$> toList (typedProblemLogicalSelections problem)
        )
    prepared <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem problem)
    let problemText = preparedTypedTptpText prepared
        origins = Map.elems (preparedTypedTptpNameOrigins prepared)
    assertBool "selection operation has its exact TH0 arrow type"
        ("thf(tg_s_type_0,type,(tg_s0:" `Text.isInfixOf` problemText
            && "(($i>$i)>$o)>($i>$i)" `Text.isInfixOf` problemText)
    assertEqual "one selection operation name"
        [TypedLogicalSelectionNameOrigin selectedType]
        [ origin
        | origin@TypedLogicalSelectionNameOrigin{} <- origins
        ]
    assertBool "selection witness is a named axiom"
        (TypedFormulaNameOrigin
            (TypedLogicalSelectionOccurrence 0 selectedType)
            `elem` origins)
    assertBool "selection witness and conjecture use the same operation"
        (Text.count "tg_s0" problemText >= 3)

rendersPredicateEquality :: Assertion
rendersPredicateEquality = do
    let predicateType = TyArrow TySet TyProp
        predicate = CLam TySet CFalsum
        noFacts :: Vector (TypedBackendFact Int ObjectId)
        noFacts = Vector.empty
    claim <-
        checkedClosedProposition
            (CEq predicateType predicate predicate)
    problem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                noFacts
                claim
                []
                []
                CompleteLocals)
    assertEqual "predicate equality route" RouteTh0
        (typedProblemRoute problem)
    prepared <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem problem)
    let problemText = preparedTypedTptpText prepared
    assertBool "predicate equality is exported as typed equality"
        ("thf(tg_q0,conjecture," `Text.isInfixOf` problemText
            && Text.count "^ [" problemText == 2
            && "=" `Text.isInfixOf` problemText)

projectsGlobalChoiceThroughFof :: Assertion
projectsGlobalChoiceThroughFof = do
    let choice =
            CApp
                (CIntrinsic GlobalChoice)
                (CIntrinsic Empty)
    claim <-
        checkedClosedProposition
            (CEq TySet choice choice)
    problem <-
        either
            (assertFailure . show)
            pure
            (planTypedProblem
                testGlobalTyping
                Vector.empty
                claim
                []
                []
                FirstOrderLocals)
    assertEqual "global choice route" RouteFof
        (typedProblemRoute problem)
    prepared <-
        either
            (assertFailure . show)
            pure
            (prepareTypedTptpProblem problem)
    assertBool "global choice is rendered in a FOF conjecture"
        ("fof(tg_q0,conjecture,"
            `Text.isInfixOf`
                preparedTypedTptpText prepared)
    assertBool "global choice receives an intrinsic symbol"
        (GlobalChoice
            `elem`
                [ intrinsic
                | TypedIntrinsicNameOrigin intrinsic <-
                    Map.elems
                        (preparedTypedTptpNameOrigins prepared)
                ])

firstOrderClaim :: CanonicalTerm ObjectId
firstOrderClaim =
    CApp
        (CGlobal firstOrderPredicate)
        (CIntrinsic Empty)

higherOrderClaim :: CanonicalTerm ObjectId
higherOrderClaim =
    CApp
        (CGlobal higherOrderPredicate)
        (CLam TySet
            (CApp
                (CGlobal firstOrderPredicate)
                (CBound 0)))

checkedProposition
    :: Vector (TestLocal, CoreType)
    -> CanonicalTerm ObjectId
    -> IO
        (SupportedProposition
            TestLocal
            ObjectId)
checkedProposition support term = do
    checked <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalTyping
                (snd <$> Vector.toList support)
                term)
    either
        (assertFailure . show)
        pure
        (supportedProposition support checked)

checkedClosedProposition
    :: CanonicalTerm ObjectId
    -> IO
        (SupportedProposition
            Void
            ObjectId)
checkedClosedProposition term = do
    checked <-
        either
            (assertFailure . show)
            pure
            (checkScopedCanonicalCore
                testGlobalTyping
                []
                term)
    either
        (assertFailure . show)
        pure
        (supportedProposition
            Vector.empty
            checked)

checkedBackendFact
    :: ref
    -> CanonicalTerm ObjectId
    -> IO (TypedBackendFact ref ObjectId)
checkedBackendFact reference term = do
    proposition <-
        checkedClosedProposition term
    capability <-
        either
            (assertFailure . show)
            pure
            (classifySupportedProposition
                testGlobalTyping
                proposition)
    pure
        (typedBackendFact
            reference
            proposition
            capability)

checkedLocalPremise
    :: Natural
    -> Text
    -> SupportedProposition TestLocal ObjectId
    -> IO
        (TypedLocalPremise
            TestLocal
            Text
            ObjectId)
checkedLocalPremise ordinal premiseOrigin proposition =
    either
        (assertFailure . show)
        pure
        (typedLocalPremise
            testGlobalTyping
            (localPremiseOrdinal ordinal)
            premiseOrigin
            proposition)
