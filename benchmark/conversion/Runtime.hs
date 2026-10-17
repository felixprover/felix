{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Runtime
    ( benchmarkNamespaceDigestText
    , conversionWorkLimit
    , runFocusedSuite
    , selfCheckSuite
    ) where

import Base hiding (Empty)
import Cases
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Math.Codec
import Felix.Module
import Felix.Source

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Word (Word)


data RuntimeCatalogue = RuntimeCatalogue
    { runtimeAliases :: !(Map BenchmarkGlobalId ObjectId)
    , runtimeInverseAliases :: !(Map ObjectId BenchmarkGlobalId)
    , runtimeSnapshots :: !(Map SnapshotName (GlobalTyping ObjectId))
    }

data PreparedSuite = PreparedSuite
    !RuntimeCatalogue
    !(NonEmpty PreparedCase)

data PreparedRecoveryTyping = PreparedRecoveryTyping
    !(GlobalTyping ObjectId)
    !(GlobalTyping ObjectId)


data PreparedCase
    = PreparedEquality
        !Text
        !(GlobalTyping ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
    | PreparedNormalization
        !Text
        !PreparedRecoveryTyping
        !(ScopedCheckedCore ObjectId)
    | PreparedResidualization
        !Text
        !PreparedRecoveryTyping
        !(ScopedCheckedCore ObjectId)
    | PreparedRawBoundary !Text !Text
    | PreparedCheckedIngressFailure
        !Text
        !(GlobalTyping ObjectId)
        !(ScopedCheckedCore ObjectId)
        !BenchmarkGlobalId

conversionWorkLimit :: Word
conversionWorkLimit = 2000000

benchmarkNamespaceBytes :: ByteString
benchmarkNamespaceBytes =
    "felix/conversion/focused\NULbenchmark-owner-v1"

benchmarkNamespaceDigestText :: Text
benchmarkNamespaceDigestText =
    mathematicalDigestHex (hashBlake2b256 benchmarkNamespaceBytes)

runFocusedSuite :: ValidatedFocusedSuite -> Either Text (NonEmpty Text)
runFocusedSuite suite = prepareSuite suite >>= runPreparedSuite

selfCheckSuite :: ValidatedFocusedSuite -> Either Text ()
selfCheckSuite suite = do
    prepared <- prepareSuite suite
    firstRun <- runPreparedSuite prepared
    secondRun <- runPreparedSuite prepared
    unless (firstRun == secondRun)
        (Left "repeated conversion observations are not deterministic")

prepareSuite :: ValidatedFocusedSuite -> Either Text PreparedSuite
prepareSuite suite = do
    foundation <- first (prefix "foundation: " . showText) checkedFoundation
    runtime <- buildRuntimeCatalogue
        foundation (validatedFocusedSuiteCatalogue suite)
    cases <- traverse (prepareCase runtime) (validatedFocusedSuiteCases suite)
    pure (PreparedSuite runtime cases)

runPreparedSuite :: PreparedSuite -> Either Text (NonEmpty Text)
runPreparedSuite (PreparedSuite runtime cases) = traverse (runCase runtime) cases

prepareCase :: RuntimeCatalogue -> FocusedCase -> Either Text PreparedCase
prepareCase runtime focused =
    case focused of
        EqualityCase metadata recipe leftOperand rightOperand -> do
            left <- checkOperand runtime
                (operandConstructionSnapshot recipe) leftOperand
            right <- checkOperand runtime
                (operandConstructionSnapshot recipe) rightOperand
            operationTyping <- snapshot runtime
                (operationIngressSnapshot recipe)
            pure
                (PreparedEquality (caseIdentifier metadata)
                    operationTyping left right)
        NormalizationCase metadata recipe operand -> do
            let ingress = recoveryIngressRecipe recipe
            checked <- checkOperand runtime
                (operandConstructionSnapshot ingress) operand
            typing <- prepareRecoveryTyping runtime recipe
            pure
                (PreparedNormalization (caseIdentifier metadata)
                    typing checked)
        ResidualizationCase metadata recipe operand -> do
            let ingress = recoveryIngressRecipe recipe
            checked <- checkOperand runtime
                (operandConstructionSnapshot ingress) operand
            typing <- prepareRecoveryTyping runtime recipe
            pure
                (PreparedResidualization (caseIdentifier metadata)
                    typing checked)
        RawCheckingFailureCase metadata recipe operand expected -> do
            rendered <- runRawFailure runtime recipe operand expected
            pure
                (PreparedRawBoundary (caseIdentifier metadata) rendered)
        CheckedIngressFailureCase metadata recipe operand expected -> do
            checked <- checkOperand runtime
                (operandConstructionSnapshot recipe) operand
            operationTyping <- snapshot runtime
                (operationIngressSnapshot recipe)
            pure
                (PreparedCheckedIngressFailure (caseIdentifier metadata)
                    operationTyping checked expected)

prepareRecoveryTyping
    :: RuntimeCatalogue
    -> RecoveryTypingRecipe
    -> Either Text PreparedRecoveryTyping
prepareRecoveryTyping runtime recipe = do
    operation <- snapshot runtime
        (operationIngressSnapshot (recoveryIngressRecipe recipe))
    destination <- snapshot runtime (recoveryDestinationSnapshot recipe)
    pure (PreparedRecoveryTyping operation destination)


runCase
    :: RuntimeCatalogue
    -> PreparedCase
    -> Either Text Text
runCase runtime = \case
    PreparedEquality identifier operationTyping left right -> do
        let report = Conversion.convertibleChecked
                operationTyping operationLimit left right
        decision <- reportResult "equality" report
        let semantic = "case " <> identifier <> " equality decision="
                <> decisionText decision
        pure (renderReport semantic report)
    PreparedNormalization identifier
            (PreparedRecoveryTyping operation destination) checked -> do
        let report = Conversion.betaNormalizeChecked
                (Conversion.ConversionRecoveryTyping operation destination)
                operationLimit checked
        case Conversion.conversionResult report of
            Right recovered -> do
                observation <- checkedObservation runtime recovered
                pure
                    (renderReport
                        ("case " <> identifier
                            <> " normalization success=" <> observation)
                        report)
            Left (Conversion.ConversionCheckedRecoveryFailure failure) ->
                pure
                    (renderReport
                        ("case " <> identifier
                            <> " normalization recovery-failure="
                            <> coreCheckErrorText failure)
                        report)
            Left failure -> reportFailure "normalization" failure
    PreparedResidualization identifier
            (PreparedRecoveryTyping operation destination) checked -> do
        let report = Conversion.residualizeHeadChecked
                (Conversion.ConversionRecoveryTyping operation destination)
                operationLimit checked
        recovered <- reportResult "head residualization" report
        observation <- checkedObservation runtime recovered
        pure (renderReport
            ("case " <> identifier <> " residualized-head=" <> observation) report)
    PreparedRawBoundary identifier rendered ->
        let complete = "case " <> identifier <> " " <> rendered
        in pure complete
    PreparedCheckedIngressFailure identifier operation checked expected -> do
        let report = Conversion.convertibleChecked operation operationLimit checked checked
        case Conversion.conversionResult report of
            Left
                (Conversion.ConversionInputFailure
                    (Conversion.ConversionAdmissionFailure UnknownCoreGlobal)) ->
                pure
                    (renderReport
                        ("case " <> identifier
                            <> " checked-ingress boundary-failure=unknown-global alias="
                            <> benchmarkGlobalText expected)
                        report)
            Left failure -> reportFailure "checked ingress" failure
            Right _ -> Left "conversion checked-ingress failure unexpectedly succeeded"
  where
    operationLimit = Conversion.conversionLimit conversionWorkLimit


reportResult
    :: Text
    -> Conversion.ConversionReport result
    -> Either Text result
reportResult label report =
    first
        (\failure -> label <> " conversion failure: " <> showText failure)
        (Conversion.conversionResult report)

reportFailure :: Text -> Conversion.ConversionFailure -> Either Text value
reportFailure label failure =
    Left (label <> " conversion failure: " <> showText failure)

renderReport :: Text -> Conversion.ConversionReport result -> Text
renderReport observation report =
    observation <> " c5-cost="
        <> showText (Conversion.conversionCostAmount (Conversion.conversionCost report))

decisionText :: Conversion.ConversionDecision -> Text
decisionText Conversion.Convertible = "convertible"
decisionText Conversion.NotConvertible = "not-convertible"


runRawFailure
    :: RuntimeCatalogue
    -> RawCheckingRecipe
    -> FocusedOperand
    -> CoreCheckError
    -> Either Text Text
runRawFailure runtime recipe serialized expected = do
    typing <- snapshot runtime (rawCheckingSnapshot recipe)
    raw <- translateOperand runtime serialized
    case checkScopedCanonicalCore typing (rawContext raw) (rawTerm raw) of
        Right _checked -> Left "raw checking failure case unexpectedly succeeded"
        Left actual
            | actual == expected ->
                pure ("raw-check failure=" <> coreCheckErrorText actual)
            | otherwise ->
                Left
                    ("raw checking failure mismatch: expected "
                        <> coreCheckErrorText expected
                        <> ", found "
                        <> coreCheckErrorText actual)


data RawOperand = RawOperand
    { rawTerm :: !(CanonicalTerm ObjectId)
    , rawContext :: ![CoreType]
    , rawExpectedType :: !CoreType
    }

checkOperand
    :: RuntimeCatalogue
    -> SnapshotName
    -> FocusedOperand
    -> Either Text (ScopedCheckedCore ObjectId)
checkOperand runtime snapshotName serialized = do
    raw <- translateOperand runtime serialized
    typing <- snapshot runtime snapshotName
    checked <- first (prefix "operand check: " . showText)
        (checkScopedCanonicalCore typing (rawContext raw) (rawTerm raw))
    unless (scopedCoreContext checked == rawContext raw)
        (Left "complete checker returned a different context")
    unless (scopedCoreType checked == rawExpectedType raw)
        (Left
            ("complete checker type mismatch: expected "
                <> coreTypeText (rawExpectedType raw)
                <> ", found "
                <> coreTypeText (scopedCoreType checked)))
    pure checked

translateOperand
    :: RuntimeCatalogue
    -> FocusedOperand
    -> Either Text RawOperand
translateOperand runtime (FocusedOperand term context expectedType) =
    RawOperand
        <$> traverseTermGlobals lookupAlias term
        <*> pure context
        <*> pure expectedType
  where
    lookupAlias alias =
        maybe
            (Left ("runtime catalogue has no alias " <> benchmarkGlobalText alias))
            Right
            (Map.lookup alias (runtimeAliases runtime))

checkedObservation
    :: RuntimeCatalogue
    -> ScopedCheckedCore ObjectId
    -> Either Text Text
checkedObservation runtime checked = do
    aliased <- traverseTermGlobals lookupObject (scopedCoreTerm checked)
    pure
        ("term-observation-digest="
            <> termObservationDigestText aliased
            <> " context="
            <> coreTypeListText (scopedCoreContext checked)
            <> " type="
            <> coreTypeText (scopedCoreType checked))
  where
    lookupObject object =
        maybe
            (Left "runtime result contains an object outside the benchmark catalogue")
            Right
            (Map.lookup object (runtimeInverseAliases runtime))

termObservationDomain :: ByteString
termObservationDomain = "felix/conversion/term-observation\NULv1"

termObservationDigestText
    :: CanonicalTerm BenchmarkGlobalId -> Text
termObservationDigestText term =
    mathematicalDigestHex
        (hashBlake2b256
            (termObservationDomain
                <> encodeCanonicalTerm putAlias term))
  where
    putAlias (BenchmarkGlobalId alias) =
        compactNaturalBuilder (fromIntegral alias)


buildRuntimeCatalogue
    :: CheckedFoundation
    -> GlobalCatalogue
    -> Either Text RuntimeCatalogue
buildRuntimeCatalogue foundation (GlobalCatalogue entries visibilities) = do
    relative <- first (prefix "benchmark path: " . showText)
        (safeRelativePath "benchmark/conversion/focused.tex")
    let theory = theoryId foundation
        namespace =
            sourceNamespaceIdFromDigest (hashBlake2b256 benchmarkNamespaceBytes)
        owner = moduleNameFromParts namespace relative
        aliasObjects =
            [ ( alias
              , opaqueObject
                    theory
                    (opaqueDeclarationSeed
                        owner
                        (localDeclarationOrdinal
                            (fromIntegral aliasValue))
                        SignatureDeclaration
                        (generatedObjectSlot 0))
                    coreType
              )
            | CatalogueEntry alias@(BenchmarkGlobalId aliasValue) coreType <- entries
            ]
        aliasMap = Map.fromList
            [(alias, assertedObjectId object) | (alias, object) <- aliasObjects]
        inverseMap = Map.fromList
            [(assertedObjectId object, alias) | (alias, object) <- aliasObjects]
    unless (Map.size aliasMap == length aliasObjects)
        (Left "runtime alias map is not injective")
    unless (Map.size inverseMap == length aliasObjects)
        (Left "production object reconstruction is not injective")
    _fullClosure <- first (prefix "full catalogue validation: " . showText)
        (validateObjectClosure theory (snd <$> aliasObjects))
    snapshots <- Map.fromList <$> traverse
        (runtimeSnapshot theory aliasObjects)
        visibilities
    pure
        RuntimeCatalogue
            { runtimeAliases = aliasMap
            , runtimeInverseAliases = inverseMap
            , runtimeSnapshots = snapshots
            }

runtimeSnapshot
    :: TheoryId
    -> [(BenchmarkGlobalId, AssertedObject)]
    -> NamedVisibility
    -> Either Text (SnapshotName, GlobalTyping ObjectId)
runtimeSnapshot theory objects (NamedVisibility name visible) = do
    let objectMap = Map.fromList objects
    selected <- traverse
        (\alias ->
            maybe
                (Left "validated visibility lost a catalogue alias")
                Right
                (Map.lookup alias objectMap))
        visible
    closure <- first (prefix "snapshot validation: " . showText)
        (validateObjectClosure theory selected)
    pure (name, globalTypingFromClosure closure)

snapshot
    :: RuntimeCatalogue
    -> SnapshotName
    -> Either Text (GlobalTyping ObjectId)
snapshot runtime name =
    maybe (Left "runtime snapshot is absent") Right
        (Map.lookup name (runtimeSnapshots runtime))


traverseTermGlobals
    :: Applicative effect
    => (left -> effect right)
    -> CanonicalTerm left
    -> effect (CanonicalTerm right)
traverseTermGlobals transform = \case
    CBound index -> pure (CBound index)
    CGlobal global -> CGlobal <$> transform global
    CIntrinsic intrinsic -> pure (CIntrinsic intrinsic)
    CLogicalSelect coreType -> pure (CLogicalSelect coreType)
    COpaqueInteger integer -> pure (COpaqueInteger integer)
    CApp function argument ->
        CApp <$> traverseTermGlobals transform function
            <*> traverseTermGlobals transform argument
    CLam binderType body ->
        CLam binderType <$> traverseTermGlobals transform body
    CFalsum -> pure CFalsum
    CTruth -> pure CTruth
    CNot proposition -> CNot <$> traverseTermGlobals transform proposition
    CAnd left right ->
        CAnd <$> traverseTermGlobals transform left
            <*> traverseTermGlobals transform right
    COr left right ->
        COr <$> traverseTermGlobals transform left
            <*> traverseTermGlobals transform right
    CImp premise conclusion ->
        CImp <$> traverseTermGlobals transform premise
            <*> traverseTermGlobals transform conclusion
    CEq operandType left right ->
        CEq operandType <$> traverseTermGlobals transform left
            <*> traverseTermGlobals transform right
    CForall binderType body ->
        CForall binderType <$> traverseTermGlobals transform body
    CExists binderType body ->
        CExists binderType <$> traverseTermGlobals transform body



coreCheckErrorText :: CoreCheckError -> Text
coreCheckErrorText = \case
    UnknownCoreGlobal -> "unknown-global"
    UnboundCoreIndex index -> "unbound-index:" <> showText index
    AppliedNonFunction actual -> "applied-non-function:" <> coreTypeText actual
    ApplicationArgumentTypeMismatch expected actual ->
        "application-argument-type-mismatch:"
            <> coreTypeText expected <> ":" <> coreTypeText actual
    ImplicationOperandTypeMismatch actual ->
        "implication-operand-type-mismatch:" <> coreTypeText actual
    EqualityOperandTypeMismatch expected actual ->
        "equality-operand-type-mismatch:"
            <> coreTypeText expected <> ":" <> coreTypeText actual
    QuantifierBodyTypeMismatch actual ->
        "quantifier-body-type-mismatch:" <> coreTypeText actual
    ExpectedCoreType expected actual ->
        "expected-core-type:"
            <> coreTypeText expected <> ":" <> coreTypeText actual

coreTypeText :: CoreType -> Text
coreTypeText = \case
    TyProp -> "prop"
    TySet -> "set"
    TyArrow domain codomain ->
        "arrow(" <> coreTypeText domain <> "," <> coreTypeText codomain <> ")"

coreTypeListText :: [CoreType] -> Text
coreTypeListText types =
    "[" <> Text.intercalate "," (coreTypeText <$> types) <> "]"

benchmarkGlobalText :: BenchmarkGlobalId -> Text
benchmarkGlobalText (BenchmarkGlobalId alias) = showText alias


showText :: Show value => value -> Text
showText = Text.pack . show

prefix :: Text -> Text -> Text
prefix label message = label <> message
