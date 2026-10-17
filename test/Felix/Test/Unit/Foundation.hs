{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Foundation (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.Resolved qualified as Resolved
import Felix.Checking.Core.StableCode (allCoreIntrinsicTags)
import Felix.Checking.Foundation

import Data.List qualified as List
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Foundation manifest"
        [ testCase
            "accepts the exact compiled foundation"
            acceptsCompiledFoundation
        , testCase
            "rejects incomplete and altered manifests"
            rejectsManifestMutations
        , testCase
            "classifies the exact UnivOf schemas"
            classifiesUnivOfSchemas
        , testCase
            "keeps global choice distinct from logical selection"
            classifiesChoicePrinciples
        , testCase
            "keeps the ordered-pair interface first-order and minimal"
            classifiesOrderedPairs
        , testCase
            "selects only intrinsic characteristic dependencies"
            selectsOnlyIntrinsicCharacteristicDependencies
        ]

acceptsCompiledFoundation :: Assertion
acceptsCompiledFoundation = do
    compiledRows <-
        either
            (assertFailure . show)
            pure
            compiledFoundationAxiomRows
    foundation <-
        either
            (assertFailure . show)
            pure
            checkedFoundation
    assertEqual
        "intrinsic coverage"
        allCoreIntrinsicTags
        (fst <$> compiledFoundationIntrinsicRows)
    assertEqual
        "guarded-rule coverage"
        [minBound .. maxBound]
        [ tag
        | FoundationRuleInput tag _signature <-
            compiledFoundationRuleRows
        ]
    assertEqual
        "axiom coverage"
        allFoundationAxiomTags
        [ tag
        | FoundationAxiomInput tag _frozen _backendClass <-
            compiledRows
        ]
    for_ [minBound .. maxBound] \tag ->
        assertEqual
            ("closed proposition type for " <> show tag)
            TyProp
            (frozenCoreType
                (foundationAxiomFrozen foundation tag))

selectsOnlyIntrinsicCharacteristicDependencies :: Assertion
selectsOnlyIntrinsicCharacteristicDependencies = do
    let separation =
            CApp
                (CApp (CIntrinsic Sep) (CBound 0))
                (CLam TySet CFalsum)
        underUniverse =
            CApp (CIntrinsic UnivOf) separation
    assertEqual
        "separation is found recursively without a universe bundle"
        (Set.singleton SeparationCharacteristic)
        (foundationAxiomDependencies underUniverse)
    assertEqual
        "global choice selects only its first-order membership law"
        (Set.singleton GlobalChoiceMember)
        (foundationAxiomDependencies
            (CApp (CIntrinsic GlobalChoice) (CBound 0)))
    assertEqual
        "logical selection is not a foundation dependency"
        Set.empty
        (foundationAxiomDependencies
            (CApp
                (CLogicalSelect TySet)
                (CLam TySet CFalsum)))

rejectsManifestMutations :: Assertion
rejectsManifestMutations = do
    compiledRows <-
        either
            (assertFailure . show)
            pure
            compiledFoundationAxiomRows
    nonProposition <-
        either
            (assertFailure . show)
            pure
            (Resolved.runClosedBuilderVoid
                (Resolved.intrinsic Empty))
    let withoutMinimal =
            List.filter
                (\case
                    FoundationAxiomInput
                        UnivOfMinimal
                        _frozen
                        _backendClass ->
                            False
                    _ ->
                        True)
                compiledRows
        wrongUnivType =
            [ if tag == UnivOf
                then (tag, TySet)
                else row
            | row@(tag, _coreType) <-
                compiledFoundationIntrinsicRows
            ]
        duplicatedEmpty =
            case findAxiomInput compiledRows EmptyCharacteristic of
                Just row ->
                    row : compiledRows
                Nothing ->
                    impossible
                        "compiled manifest omitted EmptyCharacteristic"
        alteredEmpty =
            replaceAxiomInput compiledRows
                EmptyCharacteristic
                (FoundationAxiomInput
                    EmptyCharacteristic
                    nonProposition
                    FoundationFofProjectable)
        alteredExtensionality =
            case findAxiomInput compiledRows EmptyCharacteristic of
                Just
                    (FoundationAxiomInput
                        _tag
                        frozen
                        backendClass) ->
                            replaceAxiomInput compiledRows
                                SetExtensionality
                                (FoundationAxiomInput
                                    SetExtensionality
                                    frozen
                                    backendClass)
                Nothing ->
                    impossible
                        "compiled manifest omitted EmptyCharacteristic"
        misclassifiedEmpty =
            case findAxiomInput compiledRows EmptyCharacteristic of
                Just
                    (FoundationAxiomInput
                        tag
                        frozen
                        _backendClass) ->
                            replaceAxiomInput compiledRows
                                tag
                                (FoundationAxiomInput
                                    tag
                                    frozen
                                    (FoundationRequiresTh0
                                        (HigherOrderLambda :| [])))
                Nothing ->
                    impossible
                        "compiled manifest omitted EmptyCharacteristic"
        withoutLeast =
            [ row
            | row@(FoundationRuleInput tag _signature) <-
                compiledFoundationRuleRows
            , tag /= SetLfpLeast
            ]
        alteredInductSignature =
            [ if tag == SetLfpInduct
                then
                    FoundationRuleInput
                        tag
                        (KernelRuleSignature [TySet] 0)
                else row
            | row@(FoundationRuleInput tag _signature) <-
                compiledFoundationRuleRows
            ]
    assertAuditContains
        (== MissingFoundationAxiom UnivOfMinimal)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            compiledFoundationRuleRows
            withoutMinimal)
    assertAuditContains
        (== FoundationIntrinsicTypeMismatch
                UnivOf
                (TySet `TyArrow` TySet)
                TySet)
        (auditFoundationManifest
            wrongUnivType
            compiledFoundationRuleRows
            compiledRows)
    assertAuditContains
        (== MissingFoundationRule SetLfpLeast)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            withoutLeast
            compiledRows)
    assertAuditContains
        (\case
            FoundationRuleSignatureMismatch
                SetLfpInduct
                _expected
                (KernelRuleSignature [TySet] 0) ->
                    True
            _ ->
                False)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            alteredInductSignature
            compiledRows)
    assertAuditContains
        (== DuplicateFoundationAxiom EmptyCharacteristic)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            compiledFoundationRuleRows
            duplicatedEmpty)
    assertAuditContains
        (\case
            FoundationAxiomTypeMismatch
                EmptyCharacteristic TySet ->
                    True
            _ ->
                False)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            compiledFoundationRuleRows
            alteredEmpty)
    assertAuditContains
        (== FoundationAxiomStatementMismatch
                SetExtensionality)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            compiledFoundationRuleRows
            alteredExtensionality)
    assertAuditContains
        (== FoundationAxiomBackendClassMismatch
                EmptyCharacteristic
                (FoundationRequiresTh0
                    (HigherOrderLambda :| []))
                FoundationFofProjectable)
        (auditFoundationManifest
            compiledFoundationIntrinsicRows
            compiledFoundationRuleRows
            misclassifiedEmpty)

classifiesUnivOfSchemas :: Assertion
classifiesUnivOfSchemas = do
    foundation <-
        either
            (assertFailure . show)
            pure
            checkedFoundation
    for_
        [ UnivOfContains
        , UnivOfTransitive
        , UnivOfFamilyUnionClosed
        , UnivOfPowerSetClosed
        ]
        \tag ->
            assertEqual
                (show tag)
                FoundationFofProjectable
                (foundationAxiomBackendClass foundation tag)
    for_
        [ UnivOfReplacementClosed
        , UnivOfMinimal
        ]
        \tag ->
            case foundationAxiomBackendClass foundation tag of
                FoundationRequiresTh0 exclusions ->
                    assertBool
                        (show tag <> " has a structural exclusion")
                        (not (null exclusions))
                FoundationFofProjectable ->
                    assertFailure
                        (show tag <> " was classified as FOF")

classifiesChoicePrinciples :: Assertion
classifiesChoicePrinciples = do
    foundation <-
        either
            (assertFailure . show)
            pure
            checkedFoundation
    assertEqual
        "global choice type"
        (TySet `TyArrow` TySet)
        (coreIntrinsicType GlobalChoice)
    assertEqual
        "global-choice membership is first-order"
        FoundationFofProjectable
        (foundationAxiomBackendClass foundation GlobalChoiceMember)
    assertEqual
        "set logical-selection type"
        ((TySet `TyArrow` TyProp) `TyArrow` TySet)
        (logicalSelectionType TySet)
    case classifyCanonicalFofStructure (CLogicalSelect TySet) of
        FoundationRequiresTh0 exclusions ->
            assertBool
                "logical selection has a structural TH0 exclusion"
                (HigherOrderLogicalSelection TySet `elem` exclusions)
        FoundationFofProjectable ->
            assertFailure "logical selection was classified as FOF"

classifiesOrderedPairs :: Assertion
classifiesOrderedPairs = do
    foundation <-
        either
            (assertFailure . show)
            pure
            checkedFoundation
    assertEqual
        "ordered-pair type"
        (TySet `TyArrow` (TySet `TyArrow` TySet))
        (coreIntrinsicType OrderedPair)
    assertEqual
        "first-projection type"
        (TySet `TyArrow` TySet)
        (coreIntrinsicType FirstProjection)
    assertEqual
        "second-projection type"
        (TySet `TyArrow` TySet)
        (coreIntrinsicType SecondProjection)
    for_
        [ OrderedPairInjective
        , OrderedPairFirst
        , OrderedPairSecond
        ]
        \tag ->
            assertEqual
                (show tag)
                FoundationFofProjectable
                (foundationAxiomBackendClass foundation tag)
    assertEqual
        "ordered pair selects only injectivity"
        (Set.singleton OrderedPairInjective)
        (foundationAxiomDependencies
            (CApp
                (CApp (CIntrinsic OrderedPair) (CBound 0))
                (CBound 1)))
    assertEqual
        "first projection selects its pair equation"
        (Set.singleton OrderedPairFirst)
        (foundationAxiomDependencies
            (CApp (CIntrinsic FirstProjection) (CBound 0)))
    assertEqual
        "second projection selects its pair equation"
        (Set.singleton OrderedPairSecond)
        (foundationAxiomDependencies
            (CApp (CIntrinsic SecondProjection) (CBound 0)))

findAxiomInput
    :: [FoundationAxiomInput]
    -> FoundationAxiomTag
    -> Maybe FoundationAxiomInput
findAxiomInput rows wanted =
    List.find
        (\case
            FoundationAxiomInput tag _frozen _backendClass ->
                tag == wanted)
        rows

replaceAxiomInput
    :: [FoundationAxiomInput]
    -> FoundationAxiomTag
    -> FoundationAxiomInput
    -> [FoundationAxiomInput]
replaceAxiomInput rows wanted replacement =
    fmap
        (\row ->
            case row of
                FoundationAxiomInput tag _frozen _backendClass
                    | tag == wanted ->
                        replacement
                _ ->
                    row)
        rows

assertAuditContains
    :: (FoundationManifestError -> Bool)
    -> Either FoundationError FoundationManifestAudit
    -> Assertion
assertAuditContains predicate = \case
    Left (FoundationManifestRejected errors) ->
        assertBool
            ("expected error not found in " <> show errors)
            (any predicate errors)
    Left constructionFailure@FoundationConstructionFailed{} ->
        assertFailure
            ("fixed Foundation construction failed: "
                <> show constructionFailure)
    Right _audit ->
        assertFailure
            "expected foundation-manifest audit to fail"
