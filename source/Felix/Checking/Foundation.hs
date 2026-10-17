{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

-- | The one compiled monomorphic HOL/HOTG foundation.
--
-- Constructing 'CheckedFoundation' requires exact manifest coverage, closed
-- well-typed schemas, and structural backend classification.  This gate
-- certifies manifest conformance only; it is not a consistency proof.
module Felix.Checking.Foundation
    ( FoundationAxiomTag(..)
    , foundationAxiomTagCode
    , foundationAxiomTagFromCode
    , FoundationAxiomCodeError(..)
    , allFoundationAxiomTags
    , KernelRuleTag(..)
    , kernelRuleTagCode
    , kernelRuleTagFromCode
    , KernelRuleCodeError(..)
    , allKernelRuleTags
    , KernelRuleSignature(..)
    , FoundationRuleInput(..)
    , FoundationBackendClass(..)
    , FofExclusion(..)
    , FoundationAxiomInput(..)
    , FoundationAxiomConstructionError(..)
    , FoundationManifestError(..)
    , FoundationError(..)
    , FoundationManifestAudit
    , auditFoundationManifest
    , compiledFoundationIntrinsicRows
    , compiledFoundationRuleRows
    , compiledFoundationAxiomRows
    , CheckedFoundation
    , checkedFoundation
    , foundationAxiomFrozen
    , foundationAxiomBackendClass
    , foundationRuleSignature
    , foundationAxiomDependencies
    , classifyCanonicalFofStructure
    , classifyFrozenCore
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Core.Resolved qualified as Resolved
import Felix.Checking.Core.StableCode (allCoreIntrinsicTags)

import Data.Bifunctor (first)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)
import Data.Word (Word8)


-- | The complete axiom inventory. Ordinary implication, quantifier, equality,
-- and falsum rules are dedicated kernel operations rather than manifest rows.
data FoundationAxiomTag
    = EmptyCharacteristic
    | PairSetCharacteristic
    | FamilyUnionCharacteristic
    | PowerSetCharacteristic
    | SeparationCharacteristic
    | ReplacementCharacteristic
    | SetExtensionality
    | SetInduction
    | PropositionalExtensionality
    | DoubleNegationElim
    | UnivOfContains
    | UnivOfTransitive
    | UnivOfFamilyUnionClosed
    | UnivOfPowerSetClosed
    | UnivOfReplacementClosed
    | UnivOfMinimal
    -- | The membership law for object-level global choice.
    | GlobalChoiceMember
    -- | Ordered pairs are a deliberately small foundation interface.  Their
    -- representation remains opaque; these three first-order laws are the
    -- complete public contract.
    | OrderedPairInjective
    | OrderedPairFirst
    | OrderedPairSecond
    deriving stock (Show, Eq, Ord, Enum, Bounded)

-- | Stable external codes for the complete axiom inventory.
foundationAxiomTagCode :: FoundationAxiomTag -> Word8
foundationAxiomTagCode = \case
    EmptyCharacteristic -> 0x00
    PairSetCharacteristic -> 0x01
    FamilyUnionCharacteristic -> 0x02
    PowerSetCharacteristic -> 0x03
    SeparationCharacteristic -> 0x04
    ReplacementCharacteristic -> 0x05
    SetExtensionality -> 0x06
    SetInduction -> 0x07
    PropositionalExtensionality -> 0x08
    DoubleNegationElim -> 0x09
    UnivOfContains -> 0x0a
    UnivOfTransitive -> 0x0b
    UnivOfFamilyUnionClosed -> 0x0c
    UnivOfPowerSetClosed -> 0x0d
    UnivOfReplacementClosed -> 0x0e
    UnivOfMinimal -> 0x0f
    GlobalChoiceMember -> 0x10
    OrderedPairInjective -> 0x11
    OrderedPairFirst -> 0x12
    OrderedPairSecond -> 0x13

data FoundationAxiomCodeError
    = UnknownFoundationAxiomCode !Word8
    deriving stock (Show, Eq)

foundationAxiomTagFromCode
    :: Word8
    -> Either FoundationAxiomCodeError FoundationAxiomTag
foundationAxiomTagFromCode code =
    maybe
        (Left (UnknownFoundationAxiomCode code))
        Right
        (List.find
            ((== code) . foundationAxiomTagCode)
            allFoundationAxiomTags)

-- | The complete guarded-rule inventory.
data KernelRuleTag
    = SetLfpBound
    | SetLfpLeast
    | SetLfpFixed
    | SetLfpInduct
    deriving stock (Show, Eq, Ord, Enum, Bounded)

kernelRuleTagCode :: KernelRuleTag -> Word8
kernelRuleTagCode = \case
    SetLfpBound -> 0x00
    SetLfpLeast -> 0x01
    SetLfpFixed -> 0x02
    SetLfpInduct -> 0x03

data KernelRuleCodeError
    = UnknownKernelRuleCode !Word8
    deriving stock (Show, Eq)

kernelRuleTagFromCode
    :: Word8
    -> Either KernelRuleCodeError KernelRuleTag
kernelRuleTagFromCode code =
    maybe
        (Left (UnknownKernelRuleCode code))
        Right
        (List.find ((== code) . kernelRuleTagCode) allKernelRuleTags)

data KernelRuleSignature = KernelRuleSignature
    ![CoreType]
    !Natural
    deriving stock (Show, Eq)

data FoundationRuleInput = FoundationRuleInput
    !KernelRuleTag
    !KernelRuleSignature
    deriving stock (Show, Eq)

data FofExclusion
    = HigherOrderBinder !CoreType
    | HigherOrderEquality !CoreType
    | HigherOrderLambda
    | HigherOrderIntrinsic !CoreIntrinsicTag
    | HigherOrderLogicalSelection !CoreType
    deriving stock (Show, Eq, Ord)

data FoundationBackendClass
    = FoundationFofProjectable
    | FoundationRequiresTh0 !(NonEmpty FofExclusion)
    deriving stock (Show, Eq)

-- | One proposed manifest row.  This is deliberately not an authority-bearing
-- fact; only the fixed compiled rows can produce 'CheckedFoundation'.
data FoundationAxiomInput = FoundationAxiomInput
    !FoundationAxiomTag
    !(FrozenCheckedCore Void)
    !FoundationBackendClass

data FoundationAxiomConstructionError
    = FoundationAxiomBuilderFailed
        !FoundationAxiomTag
        !(Resolved.CoreBuilderError Void)
    | FoundationAxiomConstructionTypeMismatch
        !FoundationAxiomTag
        !CoreType
    deriving stock (Show, Eq)

data FoundationManifestError
    = MissingFoundationIntrinsic !CoreIntrinsicTag
    | DuplicateFoundationIntrinsic !CoreIntrinsicTag
    | FoundationIntrinsicTypeMismatch
        !CoreIntrinsicTag
        !CoreType
        !CoreType
    | MissingFoundationRule !KernelRuleTag
    | DuplicateFoundationRule !KernelRuleTag
    | FoundationRuleSignatureMismatch
        !KernelRuleTag
        !KernelRuleSignature
        !KernelRuleSignature
    | MissingFoundationAxiom !FoundationAxiomTag
    | DuplicateFoundationAxiom !FoundationAxiomTag
    | FoundationAxiomTypeMismatch
        !FoundationAxiomTag
        !CoreType
    | FoundationAxiomStatementMismatch
        !FoundationAxiomTag
    | FoundationAxiomBackendClassMismatch
        !FoundationAxiomTag
        !FoundationBackendClass
        !FoundationBackendClass
    deriving stock (Show, Eq)

data FoundationError
    = FoundationConstructionFailed
        !(NonEmpty FoundationAxiomConstructionError)
    | FoundationManifestRejected
        !(NonEmpty FoundationManifestError)
    deriving stock (Show, Eq)

data CheckedFoundationAxiom = CheckedFoundationAxiom
    !(FrozenCheckedCore Void)
    !FoundationBackendClass

newtype FoundationManifestAudit = FoundationManifestAudit
    ( Map FoundationAxiomTag CheckedFoundationAxiom
    , Map KernelRuleTag KernelRuleSignature
    )

data CheckedFoundation = CheckedFoundation
    !(Map FoundationAxiomTag CheckedFoundationAxiom)
    !(Map KernelRuleTag KernelRuleSignature)


compiledFoundationIntrinsicRows
    :: [(CoreIntrinsicTag, CoreType)]
compiledFoundationIntrinsicRows =
    [ (Member, TySet `TyArrow` (TySet `TyArrow` TyProp))
    , (Empty, TySet)
    , (PairSet, TySet `TyArrow` (TySet `TyArrow` TySet))
    , (FamilyUnion, TySet `TyArrow` TySet)
    , (PowerSet, TySet `TyArrow` TySet)
    , ( Sep
      , TySet
            `TyArrow`
                ((TySet `TyArrow` TyProp) `TyArrow` TySet)
      )
    , ( Repl
      , TySet
            `TyArrow`
                ((TySet `TyArrow` TySet) `TyArrow` TySet)
      )
    , (UnivOf, TySet `TyArrow` TySet)
    , ( ISetLfp
      , TySet
            `TyArrow`
                ((TySet `TyArrow` TySet) `TyArrow` TySet)
      )
    , (GlobalChoice, TySet `TyArrow` TySet)
    , (OrderedPair, TySet `TyArrow` (TySet `TyArrow` TySet))
    , (FirstProjection, TySet `TyArrow` TySet)
    , (SecondProjection, TySet `TyArrow` TySet)
    ]

compiledFoundationRuleRows :: [FoundationRuleInput]
compiledFoundationRuleRows =
    [ FoundationRuleInput
        tag
        (expectedKernelRuleSignature tag)
    | tag <- allKernelRuleTags
    ]

compiledFoundationAxiomRows
    :: Either
        (NonEmpty FoundationAxiomConstructionError)
        [FoundationAxiomInput]
compiledFoundationAxiomRows =
    case partitionConstructionResults
            (buildFoundationAxiomRow
                <$> allFoundationAxiomTags) of
        ([], rows) ->
            Right rows
        (firstFailure : remainingFailures, _rows) ->
            Left (firstFailure :| remainingFailures)

checkedFoundation
    :: Either FoundationError CheckedFoundation
checkedFoundation = do
    rows <-
        first FoundationConstructionFailed
            compiledFoundationAxiomRows
    FoundationManifestAudit (axioms, rules) <-
        first FoundationManifestRejected
            (auditFoundationRows
                rows
                compiledFoundationIntrinsicRows
                compiledFoundationRuleRows
                rows)
    pure (CheckedFoundation axioms rules)

-- | Audit arbitrary proposed rows without granting foundation authority.
-- This is also the pure mutation boundary used by conformance tests.
auditFoundationManifest
    :: [(CoreIntrinsicTag, CoreType)]
    -> [FoundationRuleInput]
    -> [FoundationAxiomInput]
    -> Either FoundationError FoundationManifestAudit
auditFoundationManifest intrinsicRows ruleRows axiomRows =
    case compiledFoundationAxiomRows of
        Left failures ->
            Left (FoundationConstructionFailed failures)
        Right expectedRows ->
            first FoundationManifestRejected
                (auditFoundationRows
                    expectedRows
                    intrinsicRows
                    ruleRows
                    axiomRows)

auditFoundationRows
    :: [FoundationAxiomInput]
    -> [(CoreIntrinsicTag, CoreType)]
    -> [FoundationRuleInput]
    -> [FoundationAxiomInput]
    -> Either
        (NonEmpty FoundationManifestError)
        FoundationManifestAudit
auditFoundationRows
        expectedAxiomRows
        intrinsicRows
        ruleRows
        axiomRows =
    case
        intrinsicErrors
            <> ruleErrors
            <> axiomCoverageErrors
            <> axiomErrors of
        [] ->
            Right
                (FoundationManifestAudit
                    ( Map.fromList
                        (checkedAxiomRow <$> axiomRows)
                    , Map.fromList
                        [ (tag, signature)
                        | FoundationRuleInput
                            tag
                            signature <-
                                ruleRows
                        ]
                    ))
        firstError : remainingErrors ->
            Left (firstError :| remainingErrors)
  where
    expectedAxioms =
        Map.fromList
            [ (tag, frozen)
            | FoundationAxiomInput
                tag
                frozen
                _backendClass <-
                    expectedAxiomRows
            ]
    intrinsicErrors =
        coverageErrors
            MissingFoundationIntrinsic
            DuplicateFoundationIntrinsic
            allCoreIntrinsicTags
            (fst <$> intrinsicRows)
            <> [ FoundationIntrinsicTypeMismatch
                    tag
                    (coreIntrinsicType tag)
                    actual
               | (tag, actual) <- intrinsicRows
               , actual /= coreIntrinsicType tag
               ]
    axiomCoverageErrors =
        coverageErrors
            MissingFoundationAxiom
            DuplicateFoundationAxiom
            allFoundationAxiomTags
            [ tag
            | FoundationAxiomInput tag _frozen _backendClass <-
                axiomRows
            ]
    ruleErrors =
        coverageErrors
            MissingFoundationRule
            DuplicateFoundationRule
            allKernelRuleTags
            [ tag
            | FoundationRuleInput tag _signature <-
                ruleRows
            ]
            <> [ FoundationRuleSignatureMismatch
                    tag
                    (expectedKernelRuleSignature tag)
                    actual
               | FoundationRuleInput tag actual <-
                    ruleRows
               , actual /= expectedKernelRuleSignature tag
               ]
    axiomErrors =
        concatMap
            (foundationAxiomRowErrors expectedAxioms)
            axiomRows

foundationAxiomRowErrors
    :: Map FoundationAxiomTag (FrozenCheckedCore Void)
    -> FoundationAxiomInput
    -> [FoundationManifestError]
foundationAxiomRowErrors
        expectedAxioms
        (FoundationAxiomInput
            tag
            frozen
            declaredBackendClass)
    | frozenCoreType frozen /= TyProp =
        [ FoundationAxiomTypeMismatch
            tag
            (frozenCoreType frozen)
        ]
    | otherwise =
        statementErrors <> backendErrors
  where
    statementErrors =
        case Map.lookup tag expectedAxioms of
            Just expectedFrozen
                | frozen == expectedFrozen ->
                    []
            _ ->
                [FoundationAxiomStatementMismatch tag]
    actualBackendClass =
        classifyFrozenCore frozen
    backendErrors
        | declaredBackendClass == actualBackendClass =
            []
        | otherwise =
            [ FoundationAxiomBackendClassMismatch
                tag
                declaredBackendClass
                actualBackendClass
            ]

checkedAxiomRow
    :: FoundationAxiomInput
    -> (FoundationAxiomTag, CheckedFoundationAxiom)
checkedAxiomRow
        (FoundationAxiomInput tag frozen backendClass) =
    (tag, CheckedFoundationAxiom frozen backendClass)

foundationAxiomFrozen
    :: CheckedFoundation
    -> FoundationAxiomTag
    -> FrozenCheckedCore Void
foundationAxiomFrozen foundation tag =
    case lookupFoundationAxiom foundation tag of
        CheckedFoundationAxiom frozen _backendClass ->
            frozen

foundationAxiomBackendClass
    :: CheckedFoundation
    -> FoundationAxiomTag
    -> FoundationBackendClass
foundationAxiomBackendClass foundation tag =
    case lookupFoundationAxiom foundation tag of
        CheckedFoundationAxiom _frozen backendClass ->
            backendClass

lookupFoundationAxiom
    :: CheckedFoundation
    -> FoundationAxiomTag
    -> CheckedFoundationAxiom
lookupFoundationAxiom
        (CheckedFoundation axioms _rules)
        tag =
    case Map.lookup tag axioms of
        Just axiom ->
            axiom
        Nothing ->
            impossible
                "checked foundation omitted a validated axiom tag"

foundationRuleSignature
    :: CheckedFoundation
    -> KernelRuleTag
    -> KernelRuleSignature
foundationRuleSignature
        (CheckedFoundation _axioms rules)
        tag =
    case Map.lookup tag rules of
        Just signature ->
            signature
        Nothing ->
            impossible
                "checked foundation omitted a validated kernel rule"


classifyFrozenCore
    :: FrozenCheckedCore global
    -> FoundationBackendClass
classifyFrozenCore =
    classifyCanonicalFofStructure
        . frozenCoreTerm

classifyCanonicalFofStructure
    :: CanonicalTerm global
    -> FoundationBackendClass
classifyCanonicalFofStructure term =
    case Set.toAscList
            (termFofExclusions
                term) of
        [] ->
            FoundationFofProjectable
        firstExclusion : remainingExclusions ->
            FoundationRequiresTh0
                (firstExclusion :| remainingExclusions)

foundationAxiomDependencies
    :: CanonicalTerm global
    -> Set FoundationAxiomTag
foundationAxiomDependencies = \case
    CBound{} ->
        mempty
    CGlobal{} ->
        mempty
    CIntrinsic intrinsic ->
        intrinsicFoundationAxioms intrinsic
    CLogicalSelect{} ->
        mempty
    COpaqueInteger{} ->
        mempty
    CApp function argument ->
        foundationAxiomDependencies function
            <> foundationAxiomDependencies argument
    CLam _binderType body ->
        foundationAxiomDependencies body
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        foundationAxiomDependencies proposition
    CAnd left right ->
        foundationAxiomDependencies left
            <> foundationAxiomDependencies right
    COr left right ->
        foundationAxiomDependencies left
            <> foundationAxiomDependencies right
    CImp premise conclusion ->
        foundationAxiomDependencies premise
            <> foundationAxiomDependencies conclusion
    CEq _operandType left right ->
        foundationAxiomDependencies left
            <> foundationAxiomDependencies right
    CForall _binderType body ->
        foundationAxiomDependencies body
    CExists _binderType body ->
        foundationAxiomDependencies body

intrinsicFoundationAxioms
    :: CoreIntrinsicTag
    -> Set FoundationAxiomTag
intrinsicFoundationAxioms = Set.fromList . \case
    Member ->
        []
    Empty ->
        [EmptyCharacteristic]
    PairSet ->
        [PairSetCharacteristic]
    FamilyUnion ->
        [FamilyUnionCharacteristic]
    PowerSet ->
        [PowerSetCharacteristic]
    Sep ->
        [SeparationCharacteristic]
    Repl ->
        [ReplacementCharacteristic]
    UnivOf ->
        []
    ISetLfp ->
        []
    GlobalChoice ->
        [GlobalChoiceMember]
    OrderedPair ->
        [OrderedPairInjective]
    FirstProjection ->
        [OrderedPairFirst]
    SecondProjection ->
        [OrderedPairSecond]

termFofExclusions
    :: CanonicalTerm global
    -> Set FofExclusion
termFofExclusions = \case
    CBound{} ->
        mempty
    CGlobal{} ->
        mempty
    CIntrinsic intrinsic
        | intrinsic `elem`
            [Sep, Repl, ISetLfp] ->
            Set.singleton
                (HigherOrderIntrinsic intrinsic)
        | otherwise ->
            mempty
    CLogicalSelect coreType ->
        Set.singleton (HigherOrderLogicalSelection coreType)
    COpaqueInteger{} ->
        mempty
    CApp function argument ->
        termFofExclusions function
            <> termFofExclusions argument
    CLam _binderType body ->
        Set.insert HigherOrderLambda
            (termFofExclusions body)
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        termFofExclusions proposition
    CAnd left right ->
        termFofExclusions left
            <> termFofExclusions right
    COr left right ->
        termFofExclusions left
            <> termFofExclusions right
    CImp premise conclusion ->
        termFofExclusions premise
            <> termFofExclusions conclusion
    CEq operandType left right ->
        (case operandType of
            TyArrow{} ->
                Set.singleton
                    (HigherOrderEquality operandType)
            _ ->
                mempty)
            <> termFofExclusions left
            <> termFofExclusions right
    CForall binderType body ->
        (case binderType of
            TySet ->
                mempty
            _ ->
                Set.singleton
                    (HigherOrderBinder binderType))
            <> termFofExclusions body
    CExists binderType body ->
        (case binderType of
            TySet ->
                mempty
            _ ->
                Set.singleton
                    (HigherOrderBinder binderType))
            <> termFofExclusions body


allFoundationAxiomTags :: [FoundationAxiomTag]
allFoundationAxiomTags =
    [minBound .. maxBound]

allKernelRuleTags :: [KernelRuleTag]
allKernelRuleTags =
    [minBound .. maxBound]

expectedKernelRuleSignature
    :: KernelRuleTag
    -> KernelRuleSignature
expectedKernelRuleSignature = \case
    SetLfpBound ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet]
            0
    SetLfpLeast ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet, TySet]
            2
    SetLfpFixed ->
        KernelRuleSignature
            [TySet, TySet `TyArrow` TySet]
            1
    SetLfpInduct ->
        KernelRuleSignature
            [ TySet
            , TySet `TyArrow` TySet
            , TySet `TyArrow` TyProp
            , TySet
            ]
            3

coverageErrors
    :: Ord tag
    => (tag -> error)
    -> (tag -> error)
    -> [tag]
    -> [tag]
    -> [error]
coverageErrors missing duplicate expected actual =
    [ missing tag
    | tag <- expected
    , occurrenceCount tag == 0
    ]
        <> [ duplicate tag
           | tag <- expected
           , occurrenceCount tag > 1
           ]
  where
    occurrenceCount tag =
        length (List.filter (== tag) actual)

partitionConstructionResults
    :: [Either FoundationAxiomConstructionError FoundationAxiomInput]
    -> ([FoundationAxiomConstructionError], [FoundationAxiomInput])
partitionConstructionResults =
    foldr collect ([], [])
  where
    collect result (failures, rows) =
        case result of
            Left failure ->
                (failure : failures, rows)
            Right row ->
                (failures, row : rows)

buildFoundationAxiomRow
    :: FoundationAxiomTag
    -> Either FoundationAxiomConstructionError FoundationAxiomInput
buildFoundationAxiomRow tag = do
    frozen <-
        first (FoundationAxiomBuilderFailed tag)
            (Resolved.runClosedBuilderVoid
                (foundationAxiomBuilder tag))
    if frozenCoreType frozen == TyProp
        then
            Right
                (FoundationAxiomInput
                    tag
                    frozen
                    (expectedFoundationBackendClass tag))
        else
            Left
                (FoundationAxiomConstructionTypeMismatch
                    tag
                    (frozenCoreType frozen))

foundationAxiomBuilder
    :: FoundationAxiomTag
    -> (forall region. FoundationBuilder region)
foundationAxiomBuilder = \case
    EmptyCharacteristic ->
        forAllB TySet \element ->
            iffB
                (memberB (localB element) emptySetB)
                falsumB
    PairSetCharacteristic ->
        forAllB TySet \left ->
            forAllB TySet \right ->
                forAllB TySet \element ->
                    iffB
                        (memberB
                            (localB element)
                            (pairSetB
                                (localB left)
                                (localB right)))
                        (orB
                            (eqSetB
                                (localB element)
                                (localB left))
                            (eqSetB
                                (localB element)
                                (localB right)))
    FamilyUnionCharacteristic ->
        forAllB TySet \family ->
            forAllB TySet \element ->
                iffB
                    (memberB
                        (localB element)
                        (familyUnionB (localB family)))
                    (existsB TySet \memberSet ->
                        andB
                            (memberB
                                (localB memberSet)
                                (localB family))
                            (memberB
                                (localB element)
                                (localB memberSet)))
    PowerSetCharacteristic ->
        forAllB TySet \set ->
            forAllB TySet \candidate ->
                iffB
                    (memberB
                        (localB candidate)
                        (powerSetB (localB set)))
                    (subsetB
                        (localB candidate)
                        (localB set))
    SeparationCharacteristic ->
        forAllB TySet \set ->
            forAllB (TySet `TyArrow` TyProp) \predicate ->
                forAllB TySet \element ->
                    iffB
                        (memberB
                            (localB element)
                            (separationB
                                (localB set)
                                (localB predicate)))
                        (andB
                            (memberB
                                (localB element)
                                (localB set))
                            (applyB
                                (localB predicate)
                                (localB element)))
    ReplacementCharacteristic ->
        forAllB TySet \set ->
            forAllB (TySet `TyArrow` TySet) \function ->
                forAllB TySet \image ->
                    iffB
                        (memberB
                            (localB image)
                            (replacementB
                                (localB set)
                                (localB function)))
                        (existsB TySet \element ->
                            andB
                                (memberB
                                    (localB element)
                                    (localB set))
                                (eqSetB
                                    (localB image)
                                    (applyB
                                        (localB function)
                                        (localB element))))
    SetExtensionality ->
        forAllB TySet \left ->
            forAllB TySet \right ->
                impliesB
                    (subsetB (localB left) (localB right))
                    (impliesB
                        (subsetB (localB right) (localB left))
                        (eqSetB (localB left) (localB right)))
    SetInduction ->
        forAllB (TySet `TyArrow` TyProp) \predicate ->
            impliesB
                (forAllB TySet \set ->
                    impliesB
                        (forAllB TySet \element ->
                            impliesB
                                (memberB
                                    (localB element)
                                    (localB set))
                                (applyB
                                    (localB predicate)
                                    (localB element)))
                        (applyB
                            (localB predicate)
                            (localB set)))
                (forAllB TySet \set ->
                    applyB
                        (localB predicate)
                        (localB set))
    PropositionalExtensionality ->
        forAllB TyProp \left ->
            forAllB TyProp \right ->
                impliesB
                    (impliesB (localB left) (localB right))
                    (impliesB
                        (impliesB (localB right) (localB left))
                        (equalityB
                            TyProp
                            (localB left)
                            (localB right)))
    DoubleNegationElim ->
        forAllB TyProp \proposition ->
            impliesB
                (notB (notB (localB proposition)))
                (localB proposition)
    UnivOfContains ->
        forAllB TySet \rank ->
            memberB
                (localB rank)
                (univOfB (localB rank))
    UnivOfTransitive ->
        forAllB TySet \rank ->
            transitiveB (univOfB (localB rank))
    UnivOfFamilyUnionClosed ->
        forAllB TySet \rank ->
            familyUnionClosedB (univOfB (localB rank))
    UnivOfPowerSetClosed ->
        forAllB TySet \rank ->
            powerSetClosedB (univOfB (localB rank))
    UnivOfReplacementClosed ->
        forAllB TySet \rank ->
            replacementClosedB (univOfB (localB rank))
    UnivOfMinimal ->
        forAllB TySet \rank ->
            forAllB TySet \universe ->
                impliesB
                    (memberB (localB rank) (localB universe))
                    (impliesB
                        (transitiveB (localB universe))
                        (impliesB
                            (familyUnionClosedB (localB universe))
                            (impliesB
                                (powerSetClosedB (localB universe))
                                (impliesB
                                    (replacementClosedB
                                        (localB universe))
                                    (subsetB
                                        (univOfB (localB rank))
                                        (localB universe))))))
    GlobalChoiceMember ->
        forAllB TySet \set ->
            forAllB TySet \element ->
                impliesB
                    (memberB (localB element) (localB set))
                    (memberB
                        (globalChoiceB (localB set))
                        (localB set))
    OrderedPairInjective ->
        forAllB TySet \firstLeft ->
            forAllB TySet \secondLeft ->
                forAllB TySet \firstRight ->
                    forAllB TySet \secondRight ->
                        iffB
                            (eqSetB
                                (orderedPairB
                                    (localB firstLeft)
                                    (localB secondLeft))
                                (orderedPairB
                                    (localB firstRight)
                                    (localB secondRight)))
                            (andB
                                (eqSetB
                                    (localB firstLeft)
                                    (localB firstRight))
                                (eqSetB
                                    (localB secondLeft)
                                    (localB secondRight)))
    OrderedPairFirst ->
        forAllB TySet \firstComponent ->
            forAllB TySet \second ->
                eqSetB
                    (firstProjectionB
                        (orderedPairB
                            (localB firstComponent)
                            (localB second)))
                    (localB firstComponent)
    OrderedPairSecond ->
        forAllB TySet \firstComponent ->
            forAllB TySet \second ->
                eqSetB
                    (secondProjectionB
                        (orderedPairB
                            (localB firstComponent)
                            (localB second)))
                    (localB second)

expectedFoundationBackendClass
    :: FoundationAxiomTag
    -> FoundationBackendClass
expectedFoundationBackendClass = \case
    EmptyCharacteristic ->
        FoundationFofProjectable
    PairSetCharacteristic ->
        FoundationFofProjectable
    FamilyUnionCharacteristic ->
        FoundationFofProjectable
    PowerSetCharacteristic ->
        FoundationFofProjectable
    SeparationCharacteristic ->
        requiresTh0
            (HigherOrderBinder
                (TySet `TyArrow` TyProp))
            [HigherOrderIntrinsic Sep]
    ReplacementCharacteristic ->
        requiresTh0
            (HigherOrderBinder
                (TySet `TyArrow` TySet))
            [HigherOrderIntrinsic Repl]
    SetExtensionality ->
        FoundationFofProjectable
    SetInduction ->
        requiresTh0
            (HigherOrderBinder
                (TySet `TyArrow` TyProp))
            []
    PropositionalExtensionality ->
        requiresTh0
            (HigherOrderBinder TyProp)
            []
    DoubleNegationElim ->
        requiresTh0
            (HigherOrderBinder TyProp)
            []
    UnivOfContains ->
        FoundationFofProjectable
    UnivOfTransitive ->
        FoundationFofProjectable
    UnivOfFamilyUnionClosed ->
        FoundationFofProjectable
    UnivOfPowerSetClosed ->
        FoundationFofProjectable
    UnivOfReplacementClosed ->
        requiresTh0
            (HigherOrderBinder
                (TySet `TyArrow` TySet))
            [HigherOrderIntrinsic Repl]
    UnivOfMinimal ->
        requiresTh0
            (HigherOrderBinder
                (TySet `TyArrow` TySet))
            [HigherOrderIntrinsic Repl]
    GlobalChoiceMember ->
        FoundationFofProjectable
    OrderedPairInjective ->
        FoundationFofProjectable
    OrderedPairFirst ->
        FoundationFofProjectable
    OrderedPairSecond ->
        FoundationFofProjectable
  where
    requiresTh0 firstExclusion remainingExclusions =
        FoundationRequiresTh0
            (firstExclusion :| remainingExclusions)


type FoundationBuilder region =
    Resolved.CoreBuilder region Void
        (Resolved.CheckedExpr region Void)

localB :: Resolved.LocalRef region -> FoundationBuilder region
localB =
    Resolved.useLocal

intrinsicB :: CoreIntrinsicTag -> FoundationBuilder region
intrinsicB =
    Resolved.intrinsic

applyB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
applyB function argument = do
    functionExpr <- function
    argumentExpr <- argument
    Resolved.apply functionExpr argumentExpr

apply2B
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
apply2B function firstArgument secondArgument =
    applyB
        (applyB function firstArgument)
        secondArgument

memberB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
memberB =
    apply2B (intrinsicB Member)

emptySetB :: FoundationBuilder region
emptySetB =
    intrinsicB Empty

pairSetB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
pairSetB =
    apply2B (intrinsicB PairSet)

familyUnionB :: FoundationBuilder region -> FoundationBuilder region
familyUnionB =
    applyB (intrinsicB FamilyUnion)

powerSetB :: FoundationBuilder region -> FoundationBuilder region
powerSetB =
    applyB (intrinsicB PowerSet)

separationB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
separationB =
    apply2B (intrinsicB Sep)

replacementB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
replacementB =
    apply2B (intrinsicB Repl)

globalChoiceB :: FoundationBuilder region -> FoundationBuilder region
globalChoiceB =
    applyB (intrinsicB GlobalChoice)

orderedPairB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
orderedPairB =
    apply2B (intrinsicB OrderedPair)

firstProjectionB
    :: FoundationBuilder region
    -> FoundationBuilder region
firstProjectionB =
    applyB (intrinsicB FirstProjection)

secondProjectionB
    :: FoundationBuilder region
    -> FoundationBuilder region
secondProjectionB =
    applyB (intrinsicB SecondProjection)

univOfB :: FoundationBuilder region -> FoundationBuilder region
univOfB =
    applyB (intrinsicB UnivOf)

falsumB :: FoundationBuilder region
falsumB =
    Resolved.falsum

notB :: FoundationBuilder region -> FoundationBuilder region
notB proposition = do
    propositionExpr <- proposition
    Resolved.negation propositionExpr

andB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
andB left right = do
    leftExpr <- left
    rightExpr <- right
    Resolved.conjunction leftExpr rightExpr

orB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
orB left right = do
    leftExpr <- left
    rightExpr <- right
    Resolved.disjunction leftExpr rightExpr

impliesB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
impliesB premise conclusion = do
    premiseExpr <- premise
    conclusionExpr <- conclusion
    Resolved.imply premiseExpr conclusionExpr

equalityB
    :: CoreType
    -> FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
equalityB operandType left right = do
    leftExpr <- left
    rightExpr <- right
    Resolved.equality operandType leftExpr rightExpr

iffB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
iffB =
    equalityB TyProp

eqSetB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
eqSetB =
    equalityB TySet

forAllB
    :: CoreType
    -> (Resolved.LocalRef region -> FoundationBuilder region)
    -> FoundationBuilder region
forAllB =
    Resolved.forAll

existsB
    :: CoreType
    -> (Resolved.LocalRef region -> FoundationBuilder region)
    -> FoundationBuilder region
existsB =
    Resolved.exists

subsetB
    :: FoundationBuilder region
    -> FoundationBuilder region
    -> FoundationBuilder region
subsetB left right =
    forAllB TySet \element ->
        impliesB
            (memberB (localB element) left)
            (memberB (localB element) right)

transitiveB :: FoundationBuilder region -> FoundationBuilder region
transitiveB universe =
    forAllB TySet \set ->
        impliesB
            (memberB (localB set) universe)
            (subsetB (localB set) universe)

familyUnionClosedB
    :: FoundationBuilder region
    -> FoundationBuilder region
familyUnionClosedB universe =
    forAllB TySet \set ->
        impliesB
            (memberB (localB set) universe)
            (memberB
                (familyUnionB (localB set))
                universe)

powerSetClosedB
    :: FoundationBuilder region
    -> FoundationBuilder region
powerSetClosedB universe =
    forAllB TySet \set ->
        impliesB
            (memberB (localB set) universe)
            (memberB
                (powerSetB (localB set))
                universe)

replacementClosedB
    :: FoundationBuilder region
    -> FoundationBuilder region
replacementClosedB universe =
    forAllB TySet \set ->
        forAllB (TySet `TyArrow` TySet) \function ->
            impliesB
                (memberB (localB set) universe)
                (impliesB
                    (forAllB TySet \element ->
                        impliesB
                            (memberB
                                (localB element)
                                (localB set))
                            (memberB
                                (applyB
                                    (localB function)
                                    (localB element))
                                universe))
                    (memberB
                        (replacementB
                            (localB set)
                            (localB function))
                        universe))
