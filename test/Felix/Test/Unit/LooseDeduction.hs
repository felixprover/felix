{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.LooseDeduction (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.LooseDeduction
import Felix.Test.Support.GlobalTyping

import Test.Tasty
import Test.Tasty.HUnit


globalFixture :: GlobalTypingFixture
globalFixture = globalTypingFixture (replicate 5 TyProp)

globalType :: GlobalTyping ObjectId
globalType = fixtureGlobalTyping globalFixture

aObject, bObject, cObject, dObject, eObject :: ObjectId
(aObject, bObject, cObject, dObject, eObject) =
    case fixtureObjectIds globalFixture of
        [a, b, c, d, e] -> (a, b, c, d, e)
        _ -> error "the loose-deduction global fixture changed arity"

checked :: CanonicalTerm ObjectId -> ScopedCheckedCore ObjectId
checked term =
    either (error . show) id (checkScopedCanonicalCore globalType [] term)

proposition :: ObjectId -> ScopedCheckedCore ObjectId
proposition = checked . CGlobal

andCore
    :: ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
andCore left right =
    fromMaybe (error "test conjunction context") (conjoinScopedCore left right)

impCore
    :: ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId
impCore left right =
    fromMaybe (error "test implication context") (implyScopedCore left right)

requireOpening
    :: Either
        (AssumptionOpeningFailure ObjectId)
        (DetailedAssumptionOpening ObjectId)
    -> IO (DetailedAssumptionOpening ObjectId)
requireOpening =
    either
        (\failure ->
            assertFailure ("opening failed: " <> show failure)
                >> fail "unreachable")
        pure

unitTests :: TestTree
unitTests =
    testGroup "Loose deduction"
        [ testCase
            "preserves nested positive conjunction shape"
            preservesPositiveShape
        , testCase
            "matches a supplied conjunction across implication premises"
            matchesAcrossPremises
        , testCase
            "consumes positive occurrences before negative occurrences"
            positivePrecedence
        , testCase
            "keeps exact and classical openings distinct"
            keepsOpeningKinds
        , testCase
            "reports classical disjunction mismatches"
            rejectsUnsupported
        , testCase
            "reports missing frontier components"
            rejectsMissingComponent
        , testCase
            "reports insufficient frontier multiplicity"
            rejectsInsufficientMultiplicity
        , testCase
            "builds a reordered multi-premise kernel bridge"
            buildsReorderedBridge
        , testCase
            "builds a terminal-negation kernel bridge"
            buildsTerminalNegationBridge
        , testCase
            "reuses projected local facts when constructing conjunctions"
            reusesProjectedFacts
        ]

preservesPositiveShape :: Assertion
preservesPositiveShape = do
    let a = proposition aObject
        b = proposition bObject
        c = proposition cObject
        e = proposition eObject
        goal = impCore (andCore (andCore a b) c) e
        supplied = c
    opening <- requireOpening (findAssumptionOpening supplied goal)
    assertEqual
        "frontier opening"
        ConjunctiveFrontierOpening
        (detailedOpeningKind opening)
    assertEqual
        "shape-preserving residual"
        (scopedCoreTerm (impCore (andCore a b) e))
        (scopedCoreTerm (detailedOpeningResidual opening))

matchesAcrossPremises :: Assertion
matchesAcrossPremises = do
    let a = proposition aObject
        b = proposition bObject
        c = proposition cObject
        d = proposition dObject
        e = proposition eObject
        goal = impCore (andCore a b) (impCore (andCore c d) e)
        supplied = andCore d a
    opening <- requireOpening (findAssumptionOpening supplied goal)
    assertEqual
        "residual keeps both premise boundaries"
        (scopedCoreTerm (impCore b (impCore c e)))
        (scopedCoreTerm (detailedOpeningResidual opening))
    assertEqual
        "supplied proposition is not reordered"
        (scopedCoreTerm supplied)
        (scopedCoreTerm (detailedOpeningSupplied opening))

positivePrecedence :: Assertion
positivePrecedence = do
    let a = proposition aObject
        x = proposition bObject
        negation = fromMaybe (error "test negation") (negateScopedCore a)
        goal = impCore (andCore x a) negation
    opening <- requireOpening (findAssumptionOpening a goal)
    assertEqual
        "positive occurrence wins"
        (scopedCoreTerm (impCore x negation))
        (scopedCoreTerm (detailedOpeningResidual opening))

keepsOpeningKinds :: Assertion
keepsOpeningKinds = do
    let a = proposition aObject
        b = proposition bObject
        implication = impCore a b
        negation = fromMaybe (error "test negation") (negateScopedCore a)
        disjunction =
            fromMaybe (error "test disjunction") (disjoinScopedCore a b)
        negatedLeft =
            fromMaybe (error "test negated left") (negateScopedCore a)
    implicationOpening <- requireOpening
        (findAssumptionOpening a implication)
    negationOpening <- requireOpening
        (findAssumptionOpening a negation)
    classicalOpening <- requireOpening
        (findAssumptionOpening negatedLeft disjunction)
    assertEqual "implication opening kind" DirectImplicationOpening
        (detailedOpeningKind implicationOpening)
    assertEqual "negation opening kind" DirectNegationOpening
        (detailedOpeningKind negationOpening)
    assertEqual "classical opening kind" ClassicalDisjunctionOpening
        (detailedOpeningKind classicalOpening)

rejectsUnsupported :: Assertion
rejectsUnsupported = do
    let a = proposition aObject
        b = proposition bObject
        disjunction =
            fromMaybe (error "test disjunction") (disjoinScopedCore a b)
    case findAssumptionOpening a disjunction of
        Left
                (AssumptionOpeningDoesNotMatch
                    AssumptionClassicalDisjunctionMismatch{}) ->
            pure ()
        result ->
            assertFailure
                ("unexpected disjunction mismatch: " <> show result)

rejectsMissingComponent :: Assertion
rejectsMissingComponent = do
    let a = proposition aObject
        b = proposition bObject
        c = proposition cObject
        r = proposition eObject
        goal = impCore a (impCore b r)
    case findAssumptionOpening c goal of
        Left
                (AssumptionOpeningDoesNotMatch
                    AssumptionPartUnavailable{}) ->
            pure ()
        result ->
            assertFailure
                ("unexpected missing-component result: " <> show result)

rejectsInsufficientMultiplicity :: Assertion
rejectsInsufficientMultiplicity = do
    let a = proposition aObject
        r = proposition eObject
        goal = impCore a r
        supplied = andCore a a
    case findAssumptionOpening supplied goal of
        Left
                (AssumptionOpeningDoesNotMatch
                    (AssumptionInsufficientMultiplicity
                        _part required available)) -> do
            assertEqual "required multiplicity" 2 required
            assertEqual "available multiplicity" 1 available
        result ->
            assertFailure
                ("unexpected multiplicity result: " <> show result)

buildsReorderedBridge :: Assertion
buildsReorderedBridge = do
    let a = proposition aObject
        b = proposition bObject
        c = proposition cObject
        d = proposition dObject
        e = proposition eObject
        goal = impCore (andCore a b) (impCore (andCore c d) e)
        supplied = andCore d a
    opening <- requireOpening (findAssumptionOpening supplied goal)
    built <-
        either
            (\failure -> assertFailure (show failure) >> fail "unreachable")
            pure
            (KernelProof.buildAssumptionOpeningComposition
                kernelFoundation
                globalType
                opening)
    assertEqual
        "bridge reconstructs the original target"
        goal
        (KernelProof.builtProofStatement built)

buildsTerminalNegationBridge :: Assertion
buildsTerminalNegationBridge = do
    let a = proposition aObject
        b = proposition bObject
        c = proposition cObject
        negative = fromMaybe (error "test negation")
            (negateScopedCore (andCore b c))
        goal = impCore a negative
        supplied = andCore a b
    opening <- requireOpening (findAssumptionOpening supplied goal)
    built <-
        either
            (\failure -> assertFailure (show failure) >> fail "unreachable")
            pure
            (KernelProof.buildAssumptionOpeningComposition
                kernelFoundation
                globalType
                opening)
    assertEqual
        "terminal bridge reconstructs the original target"
        goal
        (KernelProof.builtProofStatement built)

reusesProjectedFacts :: Assertion
reusesProjectedFacts = do
    let a = proposition aObject
        b = proposition bObject
        local = andCore a b
        target = andCore a a
        context = either
            (error . show)
            id
            (KernelProof.scopedProofContext
                kernelFoundation
                globalType
                []
                [local])
    premise <-
        either
            (\failure -> assertFailure (show failure) >> fail "unreachable")
            pure
            (KernelProof.hypothesisProof context local)
    built <-
        either
            (\failure -> assertFailure (show failure) >> fail "unreachable")
            pure
            (KernelProof.conjunctionAssumptionProof
                context
                [premise]
                target)
    assertEqual
        "conjunction closure reconstructs the target"
        (Just target)
        (KernelProof.builtProofStatement <$> built)

kernelFoundation :: Foundation.CheckedFoundation
kernelFoundation =
    either (error . show) id Foundation.checkedFoundation
