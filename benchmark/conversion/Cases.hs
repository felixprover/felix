{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Cases
    ( BenchmarkGlobalId(..)
    , SnapshotName(..)
    , GlobalCatalogue(..)
    , CatalogueEntry(..)
    , NamedVisibility(..)
    , FocusedSuite
    , ValidatedFocusedSuite
    , CaseMetadata
    , caseIdentifier
    , RawCheckingRecipe
    , rawCheckingSnapshot
    , CheckedIngressRecipe
    , operandConstructionSnapshot
    , operationIngressSnapshot
    , RecoveryTypingRecipe
    , recoveryIngressRecipe
    , recoveryDestinationSnapshot
    , FocusedOperand(..)
    , FocusedCase(..)
    , focusedSuite
    , validateFocusedSuite
    , validatedFocusedSuiteName
    , validatedFocusedSuiteCatalogue
    , validatedFocusedSuiteCases
    , validatedFocusedSuiteCaseCount
    , checkRejectedFocusedSuites
    ) where

import Base hiding (Empty)
import Felix.Checking.Core

import Control.Monad (unless, when)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word32)
import Numeric.Natural (Natural)


newtype BenchmarkGlobalId = BenchmarkGlobalId Word32
    deriving stock (Show, Eq, Ord)

newtype SnapshotName = SnapshotName Word32
    deriving stock (Show, Eq, Ord)

data GlobalCatalogue = GlobalCatalogue
    ![CatalogueEntry]
    ![NamedVisibility]
    deriving stock (Show, Eq, Ord)

data CatalogueEntry = CatalogueEntry
    !BenchmarkGlobalId
    !CoreType
    deriving stock (Show, Eq, Ord)

data NamedVisibility = NamedVisibility
    !SnapshotName
    ![BenchmarkGlobalId]
    deriving stock (Show, Eq, Ord)


data FocusedSuite = FocusedSuite
    { focusedSuiteName :: !Text
    , focusedSuiteCatalogue :: !GlobalCatalogue
    , focusedSuiteCases :: !(NonEmpty FocusedCase)
    }
    deriving stock (Show, Eq)

newtype ValidatedFocusedSuite =
    ValidatedFocusedSuite FocusedSuite

data CaseMetadata = CaseMetadata
    { caseIdentifier :: !Text
    , caseSeed :: !(Maybe Word64)
    }
    deriving stock (Show, Eq, Ord)

data RawCheckingRecipe = RawCheckingRecipe
    { rawCheckingSnapshot :: !SnapshotName
    }
    deriving stock (Show, Eq, Ord)

data CheckedIngressRecipe = CheckedIngressRecipe
    { operandConstructionSnapshot :: !SnapshotName
    , operationIngressSnapshot :: !SnapshotName
    }
    deriving stock (Show, Eq, Ord)

data RecoveryTypingRecipe = RecoveryTypingRecipe
    { recoveryIngressRecipe :: !CheckedIngressRecipe
    , recoveryDestinationSnapshot :: !SnapshotName
    }
    deriving stock (Show, Eq, Ord)

data FocusedOperand = FocusedOperand
    !(CanonicalTerm BenchmarkGlobalId)
    ![CoreType]
    !CoreType
    deriving stock (Show, Eq, Ord)


data FocusedCase
    = EqualityCase
        !CaseMetadata !CheckedIngressRecipe !FocusedOperand !FocusedOperand
    | NormalizationCase
        !CaseMetadata !RecoveryTypingRecipe !FocusedOperand
    | ResidualizationCase
        !CaseMetadata !RecoveryTypingRecipe !FocusedOperand
    | RawCheckingFailureCase
        !CaseMetadata !RawCheckingRecipe !FocusedOperand !CoreCheckError
    | CheckedIngressFailureCase
        !CaseMetadata !CheckedIngressRecipe !FocusedOperand !BenchmarkGlobalId
    deriving stock (Show, Eq)


focusedSuite :: FocusedSuite
focusedSuite = FocusedSuite
    { focusedSuiteName = "conversion-focused-suite-v1"
    , focusedSuiteCatalogue = focusedCatalogue
    , focusedSuiteCases = focusedCases
    }

focusedCases :: NonEmpty FocusedCase
focusedCases =
    equality "syntactic-truth" truthOperand truthOperand :|
        [ equality "beta-identity"
            (focusedOperand
                (CApp (CLam TySet (CBound 0)) (COpaqueInteger 7)) [] TySet)
            (focusedOperand (COpaqueInteger 7) [] TySet)
        , equality "unused-argument"
            (focusedOperand
                (CApp (CLam TySet CTruth) (deepIdentity 12)) [] TyProp)
            truthOperand
        , equality "duplicated-argument"
            (focusedOperand
                (CApp
                    (CLam TySet (CEq TySet (CBound 0) (CBound 0)))
                    (CGlobal globalSet))
                [] TyProp)
            (focusedOperand
                (CEq TySet (CGlobal globalSet) (CGlobal globalSet))
                [] TyProp)
        , equality "deep-beta"
            (focusedOperand (deepIdentity 32) [] TySet)
            (focusedOperand (COpaqueInteger 1) [] TySet)
        , equality "early-mismatch" truthOperand falsumOperand
        , equality "open-outer-local"
            (focusedOperand
                (CApp (CLam TySet (CBound 1)) (CGlobal globalSet))
                [TySet] TySet)
            (focusedOperand (CBound 0) [TySet] TySet)
        , equality "opaque-global"
            (focusedOperand (CGlobal globalSet) [] TySet)
            (focusedOperand (CGlobal globalSet) [] TySet)
        , NormalizationCase
            (caseMeta "normalize-beta")
            fullRecovery
            (focusedOperand
                (CApp (CLam TySet (CBound 0)) (CGlobal globalSet))
                [] TySet)
        , NormalizationCase
            (caseMeta "normalize-recovery-missing-global")
            missingRecovery
            (focusedOperand (CGlobal globalSet) [] TySet)
        , ResidualizationCase
            (caseMeta "residualized-head-after-beta")
            fullRecovery
            (focusedOperand
                (CApp
                    (CLam mixedFunctionType
                        (CApp
                            (CApp (CBound 0) (COpaqueInteger 17))
                            CTruth))
                    (CGlobal globalMixedFunction))
                [] TyProp)
        , RawCheckingFailureCase
            (caseMeta "raw-unbound-index")
            (RawCheckingRecipe snapshotFull)
            (focusedOperand (CBound 0) [] TySet)
            (UnboundCoreIndex 0)
        , RawCheckingFailureCase
            (caseMeta "raw-missing-global")
            (RawCheckingRecipe snapshotEmpty)
            (focusedOperand (CGlobal globalSet) [] TySet)
            UnknownCoreGlobal
        , CheckedIngressFailureCase
            (caseMeta "checked-ingress-missing-global")
            missingIngress
            (focusedOperand (CGlobal globalSet) [] TySet)
            globalSet
        ]
  where
    equality identifier left right =
        EqualityCase (caseMeta identifier) fullIngress left right

caseMeta :: Text -> CaseMetadata
caseMeta identifier = CaseMetadata identifier Nothing

focusedOperand
    :: CanonicalTerm BenchmarkGlobalId
    -> [CoreType]
    -> CoreType
    -> FocusedOperand
focusedOperand = FocusedOperand

truthOperand :: FocusedOperand
truthOperand = focusedOperand CTruth [] TyProp

falsumOperand :: FocusedOperand
falsumOperand = focusedOperand CFalsum [] TyProp

globalSet :: BenchmarkGlobalId
globalSet = BenchmarkGlobalId 1

globalProposition :: BenchmarkGlobalId
globalProposition = BenchmarkGlobalId 2

globalMixedFunction :: BenchmarkGlobalId
globalMixedFunction = BenchmarkGlobalId 3

mixedFunctionType :: CoreType
mixedFunctionType = TyArrow TySet (TyArrow TyProp TyProp)


snapshotFull, snapshotSet, snapshotEmpty :: SnapshotName
snapshotFull = SnapshotName 1
snapshotSet = SnapshotName 2
snapshotEmpty = SnapshotName 3

focusedCatalogue :: GlobalCatalogue
focusedCatalogue =
    GlobalCatalogue
        [ CatalogueEntry globalSet TySet
        , CatalogueEntry globalProposition TyProp
        , CatalogueEntry globalMixedFunction mixedFunctionType
        ]
        [ NamedVisibility snapshotFull
            [globalSet, globalProposition, globalMixedFunction]
        , NamedVisibility snapshotSet [globalSet]
        , NamedVisibility snapshotEmpty []
        ]

fullIngress :: CheckedIngressRecipe
fullIngress = CheckedIngressRecipe snapshotFull snapshotFull

missingIngress :: CheckedIngressRecipe
missingIngress = CheckedIngressRecipe snapshotFull snapshotEmpty

fullRecovery :: RecoveryTypingRecipe
fullRecovery = RecoveryTypingRecipe fullIngress snapshotFull

missingRecovery :: RecoveryTypingRecipe
missingRecovery = RecoveryTypingRecipe fullIngress snapshotEmpty

deepIdentity :: Natural -> CanonicalTerm BenchmarkGlobalId
deepIdentity 0 = COpaqueInteger 1
deepIdentity depth =
    CApp (CLam TySet (CBound 0)) (deepIdentity (depth - 1))


validateFocusedSuite
    :: FocusedSuite -> Either Text ValidatedFocusedSuite
validateFocusedSuite suite = do
    validateSuiteName (focusedSuiteName suite)
    validateCatalogue catalogue
    ensureUnique "case identifier"
        (caseIdentifier . focusedCaseMetadata
            <$> NonEmpty.toList (focusedSuiteCases suite))
    traverse_ (validateCase catalogue) (focusedSuiteCases suite)
    pure (ValidatedFocusedSuite suite)
  where
    catalogue = focusedSuiteCatalogue suite

validatedFocusedSuiteName :: ValidatedFocusedSuite -> Text
validatedFocusedSuiteName (ValidatedFocusedSuite suite) =
    focusedSuiteName suite

validatedFocusedSuiteCatalogue
    :: ValidatedFocusedSuite -> GlobalCatalogue
validatedFocusedSuiteCatalogue (ValidatedFocusedSuite suite) =
    focusedSuiteCatalogue suite

validatedFocusedSuiteCases
    :: ValidatedFocusedSuite -> NonEmpty FocusedCase
validatedFocusedSuiteCases (ValidatedFocusedSuite suite) =
    focusedSuiteCases suite

validatedFocusedSuiteCaseCount :: ValidatedFocusedSuite -> Int
validatedFocusedSuiteCaseCount =
    NonEmpty.length . validatedFocusedSuiteCases

checkRejectedFocusedSuites :: Either Text ()
checkRejectedFocusedSuites = do
    expectRejected "duplicate case identifier" duplicateCaseSuite
    expectRejected "duplicate catalogue alias"
        (singleEqualitySuite duplicateAliasCatalogue fullIngress truthOperand)
    expectRejected "duplicate snapshot name"
        (singleEqualitySuite duplicateSnapshotCatalogue fullIngress truthOperand)
    expectRejected "duplicate visibility alias"
        (singleEqualitySuite duplicateVisibilityCatalogue fullIngress truthOperand)
    expectRejected "unknown operand alias"
        (singleEqualitySuite focusedCatalogue fullIngress unknownAliasOperand)
    expectRejected "unknown recipe snapshot"
        (singleEqualitySuite focusedCatalogue unknownSnapshotIngress truthOperand)
    expectRejected "missing construction visibility"
        (singleEqualitySuite focusedCatalogue missingConstructionIngress setOperand)
    expectRejected "missing successful operation visibility"
        (singleEqualitySuite focusedCatalogue missingOperationIngress setOperand)
    expectRejected "checked-ingress omission disagrees with its declared alias"
        wrongIngressOmissionSuite
    expectRejected "checked-ingress omits no used alias"
        nonFailingIngressSuite
    expectRejected "checked-ingress omits multiple used aliases"
        ambiguousIngressSuite
  where
    expectRejected label suite =
        case validateFocusedSuite suite of
            Left _failure -> Right ()
            Right _validated -> Left (label <> " was accepted")

    duplicateCaseSuite = focusedSuite
        { focusedSuiteCases =
            focusedCases <> NonEmpty.singleton (NonEmpty.head focusedCases)
        }

    duplicateAliasCatalogue =
        GlobalCatalogue
            [CatalogueEntry globalSet TySet, CatalogueEntry globalSet TySet]
            [NamedVisibility snapshotFull [globalSet]]

    duplicateSnapshotCatalogue =
        GlobalCatalogue
            [CatalogueEntry globalSet TySet]
            [ NamedVisibility snapshotFull [globalSet]
            , NamedVisibility snapshotFull [globalSet]
            ]

    duplicateVisibilityCatalogue =
        GlobalCatalogue
            [CatalogueEntry globalSet TySet]
            [NamedVisibility snapshotFull [globalSet, globalSet]]

    unknownAliasOperand =
        focusedOperand (CGlobal (BenchmarkGlobalId 999)) [] TySet

    unknownSnapshotIngress =
        CheckedIngressRecipe (SnapshotName 999) snapshotFull

    missingConstructionIngress =
        CheckedIngressRecipe snapshotEmpty snapshotFull

    missingOperationIngress =
        CheckedIngressRecipe snapshotFull snapshotEmpty

    setOperand = focusedOperand (CGlobal globalSet) [] TySet

    propositionOperand =
        focusedOperand (CGlobal globalProposition) [] TyProp

    wrongIngressOmissionSuite =
        singleCaseSuite focusedCatalogue
            (CheckedIngressFailureCase
                (caseMeta "reject-wrong-omission")
                (CheckedIngressRecipe snapshotFull snapshotSet)
                propositionOperand
                globalSet)

    nonFailingIngressSuite =
        singleCaseSuite focusedCatalogue
            (CheckedIngressFailureCase
                (caseMeta "reject-nonfailure")
                fullIngress
                setOperand
                globalSet)

    ambiguousIngressSuite =
        singleCaseSuite focusedCatalogue
            (CheckedIngressFailureCase
                (caseMeta "reject-ambiguous-omission")
                missingIngress
                (focusedOperand
                    (CImp
                        (CGlobal globalProposition)
                        (CEq TySet
                            (CGlobal globalSet)
                            (CGlobal globalSet)))
                    [] TyProp)
                globalSet)

singleEqualitySuite
    :: GlobalCatalogue
    -> CheckedIngressRecipe
    -> FocusedOperand
    -> FocusedSuite
singleEqualitySuite catalogue recipe operand =
    singleCaseSuite catalogue
        (EqualityCase
            (caseMeta "rejected-equality")
            recipe
            operand
            operand)

singleCaseSuite :: GlobalCatalogue -> FocusedCase -> FocusedSuite
singleCaseSuite catalogue focused = FocusedSuite
    { focusedSuiteName = "rejected-focused-suite"
    , focusedSuiteCatalogue = catalogue
    , focusedSuiteCases = focused :| []
    }

validateSuiteName :: Text -> Either Text ()
validateSuiteName name
    | Text.null name = Left "focused suite name is empty"
    | hasLineBreak name = Left "focused suite name contains a line break"
    | otherwise = Right ()

validateCase :: GlobalCatalogue -> FocusedCase -> Either Text ()
validateCase catalogue focused = do
    validateMetadata (focusedCaseMetadata focused)
    case focused of
        EqualityCase _metadata recipe left right -> do
            validateCheckedOperand catalogue recipe True left
            validateCheckedOperand catalogue recipe True right
        NormalizationCase _metadata recovery operand ->
            validateRecovery catalogue recovery operand
        ResidualizationCase _metadata recovery operand ->
            validateRecovery catalogue recovery operand
        RawCheckingFailureCase _metadata recipe operand _expected -> do
            requireSnapshot catalogue (rawCheckingSnapshot recipe)
            validateKnownGlobals catalogue operand
        CheckedIngressFailureCase _metadata recipe operand expected -> do
            validateCheckedOperand catalogue recipe False operand
            let omitted =
                    operandGlobals operand
                        `Set.difference`
                    visibilitySet catalogue (operationIngressSnapshot recipe)
            case Set.toList omitted of
                [omittedGlobal] ->
                    unless (omittedGlobal == expected)
                        (Left "checked-ingress omitted alias differs from its declaration")
                [] -> Left "checked-ingress failure omits no used global"
                _multiple ->
                    Left "checked-ingress failure omits multiple used globals"

validateRecovery
    :: GlobalCatalogue
    -> RecoveryTypingRecipe
    -> FocusedOperand
    -> Either Text ()
validateRecovery catalogue recovery operand = do
    validateCheckedOperand
        catalogue (recoveryIngressRecipe recovery) True operand
    requireSnapshot catalogue (recoveryDestinationSnapshot recovery)

validateMetadata :: CaseMetadata -> Either Text ()
validateMetadata metadata
    | Text.null identifier = Left "case identifier is empty"
    | hasLineBreak identifier = Left "case identifier contains a line break"
    | otherwise = Right ()
  where
    identifier = caseIdentifier metadata

hasLineBreak :: Text -> Bool
hasLineBreak =
    Text.any (\character -> character == '\n' || character == '\r')

validateCatalogue :: GlobalCatalogue -> Either Text ()
validateCatalogue catalogue@(GlobalCatalogue entries visibilities) = do
    ensureUnique "catalogue alias"
        [alias | CatalogueEntry alias _coreType <- entries]
    ensureUnique "snapshot name"
        [name | NamedVisibility name _aliases <- visibilities]
    unless (not (null visibilities))
        (Left "catalogue defines no snapshots")
    let aliases =
            Set.fromList [alias | CatalogueEntry alias _coreType <- entries]
    traverse_ (validateVisibility aliases) visibilities
    traverse_ (requireSnapshot catalogue . visibilityName) visibilities
  where
    validateVisibility aliases (NamedVisibility _name visible) = do
        ensureUnique "visibility alias" visible
        unless (Set.fromList visible `Set.isSubsetOf` aliases)
            (Left "snapshot visibility references an unknown catalogue alias")
    visibilityName (NamedVisibility name _aliases) = name

validateCheckedOperand
    :: GlobalCatalogue
    -> CheckedIngressRecipe
    -> Bool
    -> FocusedOperand
    -> Either Text ()
validateCheckedOperand catalogue recipe requireOperation operand = do
    requireSnapshot catalogue (operandConstructionSnapshot recipe)
    requireSnapshot catalogue (operationIngressSnapshot recipe)
    validateKnownGlobals catalogue operand
    let used = operandGlobals operand
        construction =
            visibilitySet catalogue (operandConstructionSnapshot recipe)
        operation =
            visibilitySet catalogue (operationIngressSnapshot recipe)
    unless (used `Set.isSubsetOf` construction)
        (Left "checked operand is not visible at construction")
    when requireOperation
        (unless (used `Set.isSubsetOf` operation)
            (Left "successful checked operand is not visible at operation ingress"))

validateKnownGlobals
    :: GlobalCatalogue -> FocusedOperand -> Either Text ()
validateKnownGlobals (GlobalCatalogue entries _visibilities) operand =
    unless (operandGlobals operand `Set.isSubsetOf` known)
        (Left "operand term references an alias outside its catalogue")
  where
    known = Set.fromList [alias | CatalogueEntry alias _coreType <- entries]

operandGlobals :: FocusedOperand -> Set.Set BenchmarkGlobalId
operandGlobals (FocusedOperand term _context _expectedType) =
    canonicalTermGlobals term

visibilitySet :: GlobalCatalogue -> SnapshotName -> Set.Set BenchmarkGlobalId
visibilitySet (GlobalCatalogue _entries visibilities) name =
    case [aliases | NamedVisibility found aliases <- visibilities, found == name] of
        aliases : _rest -> Set.fromList aliases
        [] -> mempty

requireSnapshot :: GlobalCatalogue -> SnapshotName -> Either Text ()
requireSnapshot (GlobalCatalogue _entries visibilities) name =
    unless
        (any (\(NamedVisibility found _aliases) -> found == name) visibilities)
        (Left "recipe references an unknown snapshot")

focusedCaseMetadata :: FocusedCase -> CaseMetadata
focusedCaseMetadata = \case
    EqualityCase metadata _recipe _left _right -> metadata
    NormalizationCase metadata _recipe _operand -> metadata
    ResidualizationCase metadata _recipe _operand -> metadata
    RawCheckingFailureCase metadata _recipe _operand _expected -> metadata
    CheckedIngressFailureCase metadata _recipe _operand _expected -> metadata

ensureUnique :: Ord value => Text -> [value] -> Either Text ()
ensureUnique label values =
    unless (Set.size (Set.fromList values) == length values)
        (Left ("duplicate " <> label))
