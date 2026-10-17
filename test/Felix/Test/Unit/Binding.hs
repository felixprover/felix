{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Binding (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.Resolved qualified as Resolved
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , emptyGlobalTyping
    )
import Felix.Checking.Identity (ObjectId)
import Felix.Test.Support.BindingReference
import Felix.Test.Support.GlobalTyping

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)


unitTests :: TestTree
unitTests =
    testGroup "Stable-local Core builder"
        [ testPropertyNamed
            "agrees with the independent symbolic fold"
            "prop_builderAgreesWithReference"
            prop_builderAgreesWithReference
        , testPropertyNamed
            "is invariant under symbolic alpha-renaming"
            "prop_builderAlphaInvariant"
            prop_builderAlphaInvariant
        , testPropertyNamed
            "rejects malformed symbolic references independently"
            "prop_referenceRejectsUnbound"
            prop_referenceRejectsUnbound
        , testCase
            "supports deep scopes and active-ancestor reuse"
            supportsDeepScopes
        , testCase
            "supports binders with constant bodies"
            supportsConstantBodies
        , testCase
            "checks object-language premises during construction"
            rejectsMalformedApplication
        , testCase
            "rejects malformed logical premises during construction"
            rejectsMalformedLogicalPremises
        , testCase
            "uses a visible global with its exact type"
            usesVisibleGlobal
        , testCase
            "rejects a missing global while retaining its key"
            rejectsMissingGlobal
        , testCase
            "embeds an admitted checked value unchanged"
            embedsAdmittedClosed
        , testCase
            "rejects a checked value outside the destination snapshot"
            rejectsUnseenEmbeddedGlobal
        , testCase
            "keeps the Void runner equal to the generalized runner"
            voidRunnerMatchesGeneralRunner
        ]

prop_builderAgreesWithReference :: Property
prop_builderAgreesWithReference = property do
    depth <- forAll (Gen.int (Range.linear 0 24))
    salt <- forAll (Gen.int (Range.linear 0 100000))
    let term = scopedProgram salt depth
    reference <-
        evalEither (referenceClosed term)
    frozen <-
        evalEither (buildClosed term)
    (frozenCoreType frozen, frozenCoreTerm frozen) === reference
    checkCanonicalCore emptyGlobalTyping (frozenCoreTerm frozen)
        === Right frozen

prop_builderAlphaInvariant :: Property
prop_builderAlphaInvariant = property do
    depth <- forAll (Gen.int (Range.linear 0 24))
    firstSalt <- forAll (Gen.int (Range.linear 0 100000))
    secondSalt <-
        forAll
            (Gen.filter (/= firstSalt)
                (Gen.int (Range.linear 0 100000)))
    firstFrozen <-
        evalEither (buildClosed (scopedProgram firstSalt depth))
    secondFrozen <-
        evalEither (buildClosed (scopedProgram secondSalt depth))
    firstFrozen === secondFrozen

prop_referenceRejectsUnbound :: Property
prop_referenceRejectsUnbound = property do
    unique <- forAll (Gen.int (Range.linear 0 100000))
    let missing = SymbolicKey "missing" unique
    referenceClosed (SymbolicLocal missing)
        === Left (ReferenceUnboundLocal missing)

supportsDeepScopes :: Assertion
supportsDeepScopes = do
    let depth = 256
        term = scopedProgram 17 depth
    reference <-
        either (assertFailure . show) pure
            (referenceClosed term)
    frozen <-
        either (assertFailure . show) pure
            (buildClosed term)
    assertEqual
        "deep frozen observation"
        reference
        (frozenCoreType frozen, frozenCoreTerm frozen)

supportsConstantBodies :: Assertion
supportsConstantBodies = do
    expected <-
        either (assertFailure . show) pure
            (checkCanonicalCore
                emptyGlobalTyping
                (CForall TySet CFalsum))
    actual <-
        either (assertFailure . show) pure
            (Resolved.runClosedBuilderVoid
                (Resolved.forAll TySet \_local -> Resolved.falsum))
    assertEqual
        "constant binder body"
        expected
        actual

rejectsMalformedApplication :: Assertion
rejectsMalformedApplication =
    case Resolved.runClosedBuilderVoid do
            emptySet <- Resolved.intrinsic Empty
            Resolved.apply emptySet emptySet of
        Left
            (Resolved.CoreBuilderCheckError
                (AppliedNonFunction TySet)) ->
                    pure ()
        other ->
            assertFailure
                ("unexpected builder result: " <> show other)

rejectsMalformedLogicalPremises :: Assertion
rejectsMalformedLogicalPremises = do
    let emptySet = Resolved.intrinsic Empty
        expectCheckError description expected result =
            case result of
                Left (Resolved.CoreBuilderCheckError actual) ->
                    assertEqual description expected actual
                other ->
                    assertFailure
                        (description
                            <> ": unexpected builder result: "
                            <> show other)
    expectCheckError
        "negation"
        (ExpectedCoreType TyProp TySet)
        (Resolved.runClosedBuilderVoid do
            set <- emptySet
            Resolved.negation set)
    expectCheckError
        "conjunction"
        (ExpectedCoreType TyProp TySet)
        (Resolved.runClosedBuilderVoid do
            proposition <- Resolved.falsum
            set <- emptySet
            Resolved.conjunction proposition set)
    expectCheckError
        "equality"
        (EqualityOperandTypeMismatch TySet TyProp)
        (Resolved.runClosedBuilderVoid do
            proposition <- Resolved.falsum
            set <- emptySet
            Resolved.equality TySet set proposition)
    expectCheckError
        "existential body"
        (QuantifierBodyTypeMismatch TySet)
        (Resolved.runClosedBuilderVoid
            (Resolved.exists TySet \_local -> emptySet))

usesVisibleGlobal :: Assertion
usesVisibleGlobal =
    case Resolved.runClosedBuilder
            newerGlobalTyping
            (Resolved.useGlobal visibleGlobal) of
        Right frozen -> do
            assertEqual
                "visible global type"
                TySet
                (frozenCoreType frozen)
            assertEqual
                "visible global term"
                (CGlobal visibleGlobal)
                (frozenCoreTerm frozen)
        other ->
            assertFailure
                ("unexpected builder result: " <> show other)

rejectsMissingGlobal :: Assertion
rejectsMissingGlobal =
    case Resolved.runClosedBuilder
            olderGlobalTyping
            (Resolved.useGlobal newerOnlyGlobal) of
        Left
            (Resolved.CoreBuilderGlobalNotVisible missing) ->
                    assertEqual
                        "missing global key"
                        newerOnlyGlobal
                        missing
        other ->
            assertFailure
                ("unexpected builder result: " <> show other)

embedsAdmittedClosed :: Assertion
embedsAdmittedClosed = do
    frozen <- checkedNewerOnlyGlobal
    assertEqual
        "admitted checked value"
        (Right frozen)
        (Resolved.runClosedBuilder
            newerGlobalTyping
            (Resolved.embedClosed frozen))

rejectsUnseenEmbeddedGlobal :: Assertion
rejectsUnseenEmbeddedGlobal = do
    frozen <- checkedNewerOnlyGlobal
    case Resolved.runClosedBuilder
            olderGlobalTyping
            (Resolved.embedClosed frozen) of
        Left
            (Resolved.CoreBuilderCheckedIngressRejected cause) ->
                    assertEqual
                        "complete checked-ingress cause"
                        UnknownCoreGlobal
                        cause
        other ->
            assertFailure
                ("unexpected builder result: " <> show other)

voidRunnerMatchesGeneralRunner :: Assertion
voidRunnerMatchesGeneralRunner =
    assertEqual
        "Void convenience runner"
        (Resolved.runClosedBuilder
            emptyGlobalTyping
            representativeVoidProgram)
        (Resolved.runClosedBuilderVoid representativeVoidProgram)

representativeVoidProgram
    :: Resolved.CoreBuilder region Void
        (Resolved.CheckedExpr region Void)
representativeVoidProgram =
    Resolved.lambda TySet \local -> do
        localExpr <- Resolved.useLocal local
        Resolved.equality TySet localExpr localExpr

checkedNewerOnlyGlobal :: IO (FrozenCheckedCore ObjectId)
checkedNewerOnlyGlobal =
    either (assertFailure . show) pure
        (checkCanonicalCore
            newerGlobalTyping
            (CGlobal newerOnlyGlobal))

olderGlobalTyping :: GlobalTyping ObjectId
olderGlobalTyping =
    fixtureGlobalTyping olderGlobalTypingFixture

newerGlobalTyping :: GlobalTyping ObjectId
newerGlobalTyping =
    fixtureGlobalTyping newerGlobalTypingFixture

visibleGlobal :: ObjectId
visibleGlobal =
    case fixtureObjectIds newerGlobalTypingFixture of
        visible : _newerOnly : [] ->
            visible
        identifiers ->
            error
                ("unexpected newer fixture identities: "
                    <> show (length identifiers))

newerOnlyGlobal :: ObjectId
newerOnlyGlobal =
    case fixtureObjectIds newerGlobalTypingFixture of
        _visible : newerOnly : [] ->
            newerOnly
        identifiers ->
            error
                ("unexpected newer fixture identities: "
                    <> show (length identifiers))

olderGlobalTypingFixture :: GlobalTypingFixture
olderGlobalTypingFixture =
    globalTypingFixture [TySet]

newerGlobalTypingFixture :: GlobalTypingFixture
newerGlobalTypingFixture =
    globalTypingFixture [TySet, TyProp]

scopedProgram :: Int -> Int -> SymbolicTerm
scopedProgram salt depth =
    SymbolicForAll propertyKey (TySet `TyArrow` TyProp)
        (SymbolicForAll outerSetKey TySet
            (foldr
                (\binder nested ->
                    SymbolicForAll binder TySet nested)
                body
                interveningKeys))
  where
    key spelling offset =
        SymbolicKey spelling (salt * 1024 + offset)
    propertyKey = key "P" 0
    outerSetKey = key "x" 1
    lambdaKey = key "x" 2
    existentialKey = key "x" 3
    interveningKeys =
        [ key "x" offset
        | offset <- [4 .. depth + 3]
        ]
    outerSet = SymbolicLocal outerSetKey
    lambdaMembership =
        SymbolicApply
            (SymbolicLambda lambdaKey TySet
                (symbolicMember
                    (SymbolicLocal lambdaKey)
                    outerSet))
            outerSet
    propertyAtOuterSet =
        SymbolicApply
            (SymbolicLocal propertyKey)
            outerSet
    reflexiveEquality =
        SymbolicEquality TySet outerSet outerSet
    existentialEquality =
        SymbolicExists existentialKey TySet
            (SymbolicEquality
                TySet
                (SymbolicLocal existentialKey)
                outerSet)
    logicalVocabulary =
        SymbolicAnd
            SymbolicFalsum
            (SymbolicAnd
                propertyAtOuterSet
                (SymbolicOr
                    (SymbolicNot SymbolicFalsum)
                    (SymbolicAnd
                        reflexiveEquality
                        existentialEquality)))
    body =
        SymbolicImply lambdaMembership logicalVocabulary

symbolicMember :: SymbolicTerm -> SymbolicTerm -> SymbolicTerm
symbolicMember element set =
    SymbolicApply
        (SymbolicApply
            (SymbolicIntrinsic Member)
            element)
        set
