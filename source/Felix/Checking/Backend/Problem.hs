{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Complete-problem FOF/TH0 classification and construction.
module Felix.Checking.Backend.Problem
    ( SupportedProposition
    , supportedProposition
    , projectSupportedProposition
    , supportedPropositionSupport
    , supportedPropositionTerm
    , weakenClosedSupportedProposition
    , SupportedPropositionError(..)
    , SupportedPropositionProjectionError(..)
    , CheckedFofProjection
    , checkedFofProjectionProposition
    , FofCapability(..)
    , BackendFofExclusion(..)
    , BackendClassificationError(..)
    , classifySupportedProposition
    , TypedBackendFact
    , typedBackendFact
    , typedBackendFactReference
    , typedBackendFactProposition
    , typedBackendFactCapability
    , LocalPremiseOrdinal
    , localPremiseOrdinal
    , localPremiseOrdinalValue
    , TypedLocalPremise
    , typedLocalPremise
    , typedLocalPremiseOrdinal
    , typedLocalPremiseOrigin
    , typedLocalPremiseProposition
    , typedLocalPremiseCapability
    , TypedFoundationAuxiliaryInput
    , typedFoundationAuxiliaryInput
    , TypedProblemAuxiliary
    , typedProblemAuxiliaryOrdinal
    , typedProblemAuxiliaryTag
    , typedProblemAuxiliaryProposition
    , typedProblemAuxiliaryCapability
    , TypedLogicalSelectionAuxiliary
    , typedLogicalSelectionAuxiliaryOrdinal
    , typedLogicalSelectionAuxiliaryType
    , typedLogicalSelectionAuxiliaryProposition
    , LocalPremisePolicy(..)
    , selectTypedLocalPremises
    , TypedProblemRoute(..)
    , TypedProblem
    , planTypedProblem
    , typedProblemRoute
    , typedProblemClaim
    , typedProblemGlobalPremises
    , typedProblemLocalPremises
    , typedProblemAuxiliaries
    , typedProblemLogicalSelections
    , typedProblemGlobalTypes
    , typedProblemLocalTypes
    , TypedProblemError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping
    ( GlobalTyping
    , lookupGlobalType
    )
import Felix.Checking.Foundation

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


-- | A proposition under its exact nearest-first ambient-local support.
data SupportedProposition local global =
    SupportedProposition
        !(Vector (local, CoreType))
        !(ScopedCheckedCore global)
    deriving stock (Eq)

data SupportedPropositionError local
    = SupportedPropositionIsNotProposition !CoreType
    | SupportedPropositionContextMismatch
        ![CoreType]
        ![CoreType]
    | DuplicateSupportedLocal !local
    | UnusedSupportedLocal !local
    deriving stock (Show, Eq)

data SupportedPropositionProjectionError local
    = SupportedProjectionContextMismatch
        ![CoreType]
        ![CoreType]
    | SupportedProjectionDuplicateLocal !local
    | SupportedProjectionIndexMissing !Natural
    | SupportedProjectionCoreCheckFailed !CoreCheckError
    | SupportedProjectionValidationFailed
        !(SupportedPropositionError local)
    deriving stock (Show, Eq)

supportedProposition
    :: Ord local
    => Vector (local, CoreType)
    -> ScopedCheckedCore global
    -> Either
        (SupportedPropositionError local)
        (SupportedProposition local global)
supportedProposition support statement = do
    unless
        (scopedCoreType statement == TyProp)
        (Left
            (SupportedPropositionIsNotProposition
                (scopedCoreType statement)))
    let expectedContext =
            snd <$> Vector.toList support
        actualContext =
            scopedCoreContext statement
    unless
        (actualContext == expectedContext)
        (Left
            (SupportedPropositionContextMismatch
                expectedContext
                actualContext))
    void
        (foldM
            (\seen (local, _coreType) ->
                if local `Set.member` seen
                    then
                        Left
                            (DuplicateSupportedLocal local)
                    else
                        Right (Set.insert local seen))
            Set.empty
            support)
    case
        List.find
            (\(ordinal, _entry) ->
                fromIntegral ordinal
                    `Set.notMember`
                        ambientIndices
                            (scopedCoreTerm statement))
            (Vector.toList
                (Vector.indexed support)) of
        Just (_ordinal, (local, _coreType)) ->
            Left (UnusedSupportedLocal local)
        Nothing ->
            pure ()
    pure
        (SupportedProposition
            support
            statement)

-- | Retain exactly the ambient locals used by a checked proposition and
-- remap its indices to that dense nearest-first support.
projectSupportedProposition
    :: Ord local
    => GlobalTyping global
    -> Vector (local, CoreType)
    -> ScopedCheckedCore global
    -> Either
        (SupportedPropositionProjectionError local)
        (SupportedProposition local global)
projectSupportedProposition globalType available statement = do
    let expectedContext = snd <$> Vector.toList available
        actualContext = scopedCoreContext statement
    unless (expectedContext == actualContext)
        (Left
            (SupportedProjectionContextMismatch
                expectedContext
                actualContext))
    void
        (foldM
            (\seen (local, _coreType) ->
                if local `Set.member` seen
                    then Left (SupportedProjectionDuplicateLocal local)
                    else Right (Set.insert local seen))
            Set.empty
            available)
    let used =
            Set.toAscList
                (ambientIndices
                    (scopedCoreTerm statement))
    selected <- traverse (lookupNatural available) used
    let remapping =
            Map.fromAscList
                (zip used [0 ..])
    remapped <- remapAmbientIndices remapping 0
        (scopedCoreTerm statement)
    checked <-
        first SupportedProjectionCoreCheckFailed
            (checkScopedCanonicalCore
                globalType
                (snd <$> selected)
                remapped)
    first SupportedProjectionValidationFailed
        (supportedProposition
            (Vector.fromList selected)
            checked)
  where
    lookupNatural values index =
        maybe
            (Left (SupportedProjectionIndexMissing index))
            Right
            (nth index (Vector.toList values))

    remapAmbientIndices remapping depth = \case
        CBound index
            | index < depth ->
                Right (CBound index)
            | otherwise ->
                maybe
                    (Left
                        (SupportedProjectionIndexMissing
                            (index - depth)))
                    (Right . CBound . (+ depth))
                    (Map.lookup (index - depth) remapping)
        CGlobal global ->
            Right (CGlobal global)
        CIntrinsic intrinsic ->
            Right (CIntrinsic intrinsic)
        CLogicalSelect coreType ->
            Right (CLogicalSelect coreType)
        COpaqueInteger integer ->
            Right (COpaqueInteger integer)
        CApp function argument ->
            CApp
                <$> remapAmbientIndices remapping depth function
                <*> remapAmbientIndices remapping depth argument
        CLam binderType body ->
            CLam binderType
                <$> remapAmbientIndices remapping (depth + 1) body
        CFalsum ->
            Right CFalsum
        CTruth ->
            Right CTruth
        CNot proposition ->
            CNot
                <$> remapAmbientIndices remapping depth proposition
        CAnd left right ->
            CAnd
                <$> remapAmbientIndices remapping depth left
                <*> remapAmbientIndices remapping depth right
        COr left right ->
            COr
                <$> remapAmbientIndices remapping depth left
                <*> remapAmbientIndices remapping depth right
        CImp premise conclusion ->
            CImp
                <$> remapAmbientIndices remapping depth premise
                <*> remapAmbientIndices remapping depth conclusion
        CEq operandType left right ->
            CEq operandType
                <$> remapAmbientIndices remapping depth left
                <*> remapAmbientIndices remapping depth right
        CForall binderType body ->
            CForall binderType
                <$> remapAmbientIndices remapping (depth + 1) body
        CExists binderType body ->
            CExists binderType
                <$> remapAmbientIndices remapping (depth + 1) body

ambientIndices
    :: CanonicalTerm global
    -> Set Natural
ambientIndices =
    go 0
  where
    go depth = \case
        CBound index
            | index < depth ->
                mempty
            | otherwise ->
                Set.singleton (index - depth)
        CGlobal{} ->
            mempty
        CIntrinsic{} ->
            mempty
        CLogicalSelect{} ->
            mempty
        COpaqueInteger{} ->
            mempty
        CApp function argument ->
            go depth function <> go depth argument
        CLam _binderType body ->
            go (depth + 1) body
        CFalsum ->
            mempty
        CTruth ->
            mempty
        CNot proposition ->
            go depth proposition
        CAnd left right ->
            go depth left <> go depth right
        COr left right ->
            go depth left <> go depth right
        CImp premise conclusion ->
            go depth premise <> go depth conclusion
        CEq _operandType left right ->
            go depth left <> go depth right
        CForall _binderType body ->
            go (depth + 1) body
        CExists _binderType body ->
            go (depth + 1) body

supportedPropositionSupport
    :: SupportedProposition local global
    -> Vector (local, CoreType)
supportedPropositionSupport
        (SupportedProposition support _statement) =
    support

supportedPropositionTerm
    :: SupportedProposition local global
    -> CanonicalTerm global
supportedPropositionTerm
        (SupportedProposition _support statement) =
    scopedCoreTerm statement

weakenClosedSupportedProposition
    :: SupportedProposition Void global
    -> SupportedProposition local global
weakenClosedSupportedProposition
        (SupportedProposition support statement) =
    SupportedProposition
        (fmap
            (\(local, coreType) ->
                (absurd local, coreType))
            support)
        statement


newtype CheckedFofProjection local global =
    CheckedFofProjection
        (SupportedProposition local global)
    deriving stock (Eq)

checkedFofProjectionProposition
    :: CheckedFofProjection local global
    -> SupportedProposition local global
checkedFofProjectionProposition
        (CheckedFofProjection proposition) =
    proposition

data FofCapability projection
    = FofProjectable !projection
    | RequiresTh0 !(NonEmpty BackendFofExclusion)
    deriving stock (Eq)

data BackendFofExclusion
    = StructuralFofExclusion !FofExclusion
    | HigherOrderGlobalType !CoreType
    | HigherOrderAmbientLocal !CoreType
    deriving stock (Show, Eq, Ord)

data BackendClassificationError global
    = UnknownBackendGlobal !global
    | BackendFofProjectionInvariantFailed
    deriving stock (Show, Eq)

classifySupportedProposition
    :: Ord global
    => GlobalTyping global
    -> SupportedProposition local global
    -> Either
        (BackendClassificationError global)
        (FofCapability
            (CheckedFofProjection local global))
classifySupportedProposition globalTyping proposition = do
    globalExclusions <-
        foldM
            collectGlobal
            Set.empty
            (Set.toAscList
                (canonicalGlobals
                    (supportedPropositionTerm proposition)))
    let structuralExclusions =
            case classifyScopedStructure proposition of
                FoundationFofProjectable ->
                    Set.empty
                FoundationRequiresTh0 structural ->
                    Set.fromList
                        (StructuralFofExclusion
                            <$> toList structural)
        localExclusions =
            Set.fromList
                [ HigherOrderAmbientLocal coreType
                | (_local, coreType) <-
                    Vector.toList
                        (supportedPropositionSupport
                            proposition)
                , coreType /= TySet
                ]
        exclusions =
            structuralExclusions
                <> globalExclusions
                <> localExclusions
    case Set.toAscList exclusions of
        [] ->
            if isFirstOrderProposition
                    (lookupGlobalType globalTyping)
                    proposition
                then
                    Right
                        (FofProjectable
                            (CheckedFofProjection
                                proposition))
                else
                    Left BackendFofProjectionInvariantFailed
        firstExclusion : remainingExclusions ->
            Right
                (RequiresTh0
                    (firstExclusion
                        :| remainingExclusions))
  where
    collectGlobal exclusions global =
        case lookupGlobalType globalTyping global of
            Nothing ->
                Left (UnknownBackendGlobal global)
            Just coreType ->
                Right
                    (if isJust (firstOrderSymbolShape coreType)
                        then exclusions
                        else
                            Set.insert
                                (HigherOrderGlobalType
                                    coreType)
                                exclusions)

classifyScopedStructure
    :: SupportedProposition local global
    -> FoundationBackendClass
classifyScopedStructure =
    classifyCanonicalFofStructure
        . supportedPropositionTerm

-- The structural and type exclusions make this projection total. This final
-- walk catches an accidentally unsaturated first-order head.
isFirstOrderProposition
    :: (global -> Maybe CoreType)
    -> SupportedProposition local global
    -> Bool
isFirstOrderProposition globalType proposition =
    isFormula initialContext
        (supportedPropositionTerm proposition)
  where
    initialContext =
        snd
            <$> Vector.toList
                (supportedPropositionSupport
                    proposition)

    isFormula context = \case
        CFalsum ->
            True
        CTruth ->
            True
        CNot negated ->
            isFormula context negated
        CAnd left right ->
            isFormula context left
                && isFormula context right
        COr left right ->
            isFormula context left
                && isFormula context right
        CImp premise conclusion ->
            isFormula context premise
                && isFormula context conclusion
        CEq TySet left right ->
            isTerm context left
                && isTerm context right
        CEq TyProp left right ->
            isFormula context left
                && isFormula context right
        CForall TySet body ->
            isFormula (TySet : context) body
        CExists TySet body ->
            isFormula (TySet : context) body
        application ->
            case canonicalApplicationSpine application of
                (CGlobal global, arguments) ->
                    maybe
                        False
                        (\coreType ->
                            applicationResult
                                coreType
                                arguments
                                == Just TyProp
                                && all
                                    (isTerm context)
                                    arguments)
                        (globalType global)
                (CIntrinsic intrinsic, arguments) ->
                    applicationResult
                        (coreIntrinsicType intrinsic)
                        arguments
                        == Just TyProp
                        && all
                            (isTerm context)
                            arguments
                _ ->
                    False

    isTerm context = \case
        CBound index ->
            nth index context
                == Just TySet
        CGlobal global ->
            globalType global == Just TySet
        CIntrinsic intrinsic ->
            coreIntrinsicType intrinsic == TySet
        COpaqueInteger{} ->
            True
        application ->
            case canonicalApplicationSpine application of
                (CGlobal global, arguments) ->
                    maybe
                        False
                        (\coreType ->
                            applicationResult
                                coreType
                                arguments
                                == Just TySet
                                && all
                                    (isTerm context)
                                    arguments)
                        (globalType global)
                (CIntrinsic intrinsic, arguments) ->
                    applicationResult
                        (coreIntrinsicType intrinsic)
                        arguments
                        == Just TySet
                        && all
                            (isTerm context)
                            arguments
                _ ->
                    False

applicationResult
    :: CoreType
    -> [CanonicalTerm global]
    -> Maybe CoreType
applicationResult =
    foldM
        (\coreType _argument ->
            case coreType of
                TyArrow TySet result ->
                    Just result
                _ ->
                    Nothing)

canonicalGlobals
    :: Ord global
    => CanonicalTerm global
    -> Set global
canonicalGlobals = \case
    CBound{} ->
        mempty
    CGlobal global ->
        Set.singleton global
    CIntrinsic{} ->
        mempty
    CLogicalSelect{} ->
        mempty
    COpaqueInteger{} ->
        mempty
    CApp function argument ->
        canonicalGlobals function
            <> canonicalGlobals argument
    CLam _binderType body ->
        canonicalGlobals body
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        canonicalGlobals proposition
    CAnd left right ->
        canonicalGlobals left
            <> canonicalGlobals right
    COr left right ->
        canonicalGlobals left
            <> canonicalGlobals right
    CImp premise conclusion ->
        canonicalGlobals premise
            <> canonicalGlobals conclusion
    CEq _operandType left right ->
        canonicalGlobals left
            <> canonicalGlobals right
    CForall _binderType body ->
        canonicalGlobals body
    CExists _binderType body ->
        canonicalGlobals body


data TypedBackendFact ref global =
    TypedBackendFact
        !ref
        !(SupportedProposition Void global)
        !(FofCapability
            (CheckedFofProjection Void global))
    deriving stock (Eq)

typedBackendFact
    :: ref
    -> SupportedProposition Void global
    -> FofCapability
        (CheckedFofProjection Void global)
    -> TypedBackendFact ref global
typedBackendFact =
    TypedBackendFact

typedBackendFactReference
    :: TypedBackendFact ref global
    -> ref
typedBackendFactReference
        (TypedBackendFact
            reference
            _proposition
            _capability) =
    reference

typedBackendFactProposition
    :: TypedBackendFact ref global
    -> SupportedProposition Void global
typedBackendFactProposition
        (TypedBackendFact
            _reference
            proposition
            _capability) =
    proposition

typedBackendFactCapability
    :: TypedBackendFact ref global
    -> FofCapability
        (CheckedFofProjection Void global)
typedBackendFactCapability
        (TypedBackendFact
            _reference
            _proposition
            capability) =
    capability


newtype LocalPremiseOrdinal =
    LocalPremiseOrdinal Natural
    deriving stock (Show, Eq, Ord)

localPremiseOrdinal :: Natural -> LocalPremiseOrdinal
localPremiseOrdinal =
    LocalPremiseOrdinal

localPremiseOrdinalValue
    :: LocalPremiseOrdinal
    -> Natural
localPremiseOrdinalValue
        (LocalPremiseOrdinal ordinal) =
    ordinal

data TypedLocalPremise local origin global =
    TypedLocalPremise
        !LocalPremiseOrdinal
        !origin
        !(SupportedProposition local global)
        !(FofCapability
            (CheckedFofProjection local global))
    deriving stock (Eq)

typedLocalPremise
    :: Ord global
    => GlobalTyping global
    -> LocalPremiseOrdinal
    -> origin
    -> SupportedProposition local global
    -> Either
        (BackendClassificationError global)
        (TypedLocalPremise local origin global)
typedLocalPremise globalTyping ordinal premiseOrigin proposition =
    TypedLocalPremise
        ordinal
        premiseOrigin
        proposition
        <$> classifySupportedProposition
            globalTyping
            proposition

typedLocalPremiseOrdinal
    :: TypedLocalPremise local origin global
    -> LocalPremiseOrdinal
typedLocalPremiseOrdinal
        (TypedLocalPremise
            ordinal
            _origin
            _proposition
            _capability) =
    ordinal

typedLocalPremiseOrigin
    :: TypedLocalPremise local origin global
    -> origin
typedLocalPremiseOrigin
        (TypedLocalPremise
            _ordinal
            premiseOrigin
            _proposition
            _capability) =
    premiseOrigin

typedLocalPremiseProposition
    :: TypedLocalPremise local origin global
    -> SupportedProposition local global
typedLocalPremiseProposition
        (TypedLocalPremise
            _ordinal
            _origin
            proposition
            _capability) =
    proposition

typedLocalPremiseCapability
    :: TypedLocalPremise local origin global
    -> FofCapability
        (CheckedFofProjection local global)
typedLocalPremiseCapability
        (TypedLocalPremise
            _ordinal
            _origin
            _proposition
            capability) =
    capability


data TypedFoundationAuxiliaryInput global =
    TypedFoundationAuxiliaryInput
        !FoundationAxiomTag
        !(SupportedProposition Void global)
        !(FofCapability
            (CheckedFofProjection Void global))

typedFoundationAuxiliaryInput
    :: CheckedFoundation
    -> FoundationAxiomTag
    -> TypedFoundationAuxiliaryInput global
typedFoundationAuxiliaryInput foundation tag =
    TypedFoundationAuxiliaryInput
        tag
        proposition
        capability
  where
    proposition =
        SupportedProposition
            Vector.empty
            (embedClosedCore
                []
                (eliminateFrozenVoid
                    (foundationAxiomFrozen
                        foundation
                        tag)))
    capability =
        case foundationAxiomBackendClass
                foundation
                tag of
            FoundationFofProjectable ->
                FofProjectable
                    (CheckedFofProjection
                        proposition)
            FoundationRequiresTh0 exclusions ->
                RequiresTh0
                    (StructuralFofExclusion
                        <$> exclusions)

data TypedProblemAuxiliary global =
    TypedProblemAuxiliary
        !Natural
        !FoundationAxiomTag
        !(SupportedProposition Void global)
        !(FofCapability
            (CheckedFofProjection Void global))
    deriving stock (Eq)

typedProblemAuxiliaryOrdinal
    :: TypedProblemAuxiliary global
    -> Natural
typedProblemAuxiliaryOrdinal
        (TypedProblemAuxiliary
            ordinal
            _tag
            _proposition
            _capability) =
    ordinal

typedProblemAuxiliaryTag
    :: TypedProblemAuxiliary global
    -> FoundationAxiomTag
typedProblemAuxiliaryTag
        (TypedProblemAuxiliary
            _ordinal
            tag
            _proposition
            _capability) =
    tag

typedProblemAuxiliaryProposition
    :: TypedProblemAuxiliary global
    -> SupportedProposition Void global
typedProblemAuxiliaryProposition
        (TypedProblemAuxiliary
            _ordinal
            _tag
            proposition
            _capability) =
    proposition

typedProblemAuxiliaryCapability
    :: TypedProblemAuxiliary global
    -> FofCapability
        (CheckedFofProjection Void global)
typedProblemAuxiliaryCapability
        (TypedProblemAuxiliary
            _ordinal
            _tag
            _proposition
            capability) =
    capability

data TypedLogicalSelectionAuxiliary global =
    TypedLogicalSelectionAuxiliary
        !Natural
        !CoreType
        !(SupportedProposition Void global)
    deriving stock (Eq)

typedLogicalSelectionAuxiliaryOrdinal
    :: TypedLogicalSelectionAuxiliary global
    -> Natural
typedLogicalSelectionAuxiliaryOrdinal
        (TypedLogicalSelectionAuxiliary ordinal _coreType _proposition) =
    ordinal

typedLogicalSelectionAuxiliaryType
    :: TypedLogicalSelectionAuxiliary global
    -> CoreType
typedLogicalSelectionAuxiliaryType
        (TypedLogicalSelectionAuxiliary _ordinal coreType _proposition) =
    coreType

typedLogicalSelectionAuxiliaryProposition
    :: TypedLogicalSelectionAuxiliary global
    -> SupportedProposition Void global
typedLogicalSelectionAuxiliaryProposition
        (TypedLogicalSelectionAuxiliary _ordinal _coreType proposition) =
    proposition


data LocalPremisePolicy
    = FirstOrderLocals
    | CompleteLocals
    deriving stock (Show, Eq)

selectTypedLocalPremises
    :: LocalPremisePolicy
    -> [TypedLocalPremise local origin global]
    -> Vector (TypedLocalPremise local origin global)
selectTypedLocalPremises selection availableLocals =
    Vector.fromList
        (List.sortOn
            typedLocalPremiseOrdinal
            (case selection of
                FirstOrderLocals ->
                    List.filter
                        (isFofCapability
                            . typedLocalPremiseCapability)
                        availableLocals
                CompleteLocals ->
                    availableLocals))

data TypedProblemRoute
    = RouteFof
    | RouteTh0
    deriving stock (Show, Eq)

data TypedProblem ref local origin global =
    TypedProblem
        !TypedProblemRoute
        !(SupportedProposition local global)
        !(Vector (TypedBackendFact ref global))
        !(Vector (TypedLocalPremise local origin global))
        !(Vector (TypedProblemAuxiliary global))
        !(Vector (TypedLogicalSelectionAuxiliary global))
        !(Map global CoreType)
        !(Map local CoreType)
    deriving stock (Eq)

data TypedProblemError local global
    = TypedProblemClaimClassificationFailed
        !(BackendClassificationError global)
    | TypedProblemDuplicateLocalPremiseOrdinal
        !LocalPremiseOrdinal
    | TypedProblemLocalTypeMismatch
        !local
        !CoreType
        !CoreType
    deriving stock (Show, Eq)

planTypedProblem
    :: (Ord local, Ord global)
    => GlobalTyping global
    -> Vector (TypedBackendFact ref global)
    -> SupportedProposition local global
    -> [TypedLocalPremise local origin global]
    -> [TypedFoundationAuxiliaryInput global]
    -> LocalPremisePolicy
    -> Either
        (TypedProblemError local global)
        (TypedProblem ref local origin global)
planTypedProblem
        globalTyping
        selectedFacts
        claim
        availableLocals
        auxiliaries
        localPolicy = do
    validateLocalPremiseOrdinals
        availableLocals
    claimCapability <-
        first
            TypedProblemClaimClassificationFailed
            (classifySupportedProposition
                globalTyping
                claim)
    let selectedLocals =
            selectTypedLocalPremises
                localPolicy
                availableLocals
    let preparedAuxiliaries =
            zipWith
                prepareAuxiliary
                [0..]
                auxiliaries
        logicalSelections =
            zipWith
                prepareLogicalSelection
                [0..]
                (Set.toAscList
                    (requiredLogicalSelectionTypes
                        claim
                        selectedFacts
                        selectedLocals
                        preparedAuxiliaries))
    let selectedFofCapabilities =
            isFofCapability claimCapability
                : (isFofCapability
                    . typedBackendFactCapability
                    <$> Vector.toList selectedFacts)
                <> (isFofCapability
                    . typedLocalPremiseCapability
                    <$> Vector.toList selectedLocals)
                <> (isFofCapability
                    . typedProblemAuxiliaryCapability
                    <$> preparedAuxiliaries)
                <> replicate (length logicalSelections) False
        route =
            if and selectedFofCapabilities
                then RouteFof
                else RouteTh0
    globalTypes <-
        collectProblemGlobals
            (lookupGlobalType globalTyping)
            claim
            selectedFacts
            selectedLocals
            preparedAuxiliaries
            logicalSelections
    localTypes <-
        collectProblemLocals
            claim
            selectedLocals
    pure
        (TypedProblem
            route
            claim
            selectedFacts
            selectedLocals
            (Vector.fromList preparedAuxiliaries)
            (Vector.fromList logicalSelections)
            globalTypes
            localTypes)
  where
    prepareAuxiliary
            ordinal
            (TypedFoundationAuxiliaryInput
                tag
                proposition
                capability) =
        TypedProblemAuxiliary
            ordinal
            tag
            proposition
            capability

    prepareLogicalSelection ordinal coreType =
        TypedLogicalSelectionAuxiliary
            ordinal
            coreType
            (SupportedProposition
                Vector.empty
                (embedClosedCore []
                    (eliminateFrozenVoid
                        (logicalSelectionWitness coreType))))

requiredLogicalSelectionTypes
    :: SupportedProposition local global
    -> Vector (TypedBackendFact ref global)
    -> Vector (TypedLocalPremise local origin global)
    -> [TypedProblemAuxiliary global]
    -> Set CoreType
requiredLogicalSelectionTypes claim facts locals auxiliaries =
    foldMap canonicalLogicalSelectionTypes
        ( supportedPropositionTerm claim
            : (supportedPropositionTerm . typedBackendFactProposition
                <$> Vector.toList facts)
            <> (supportedPropositionTerm . typedLocalPremiseProposition
                <$> Vector.toList locals)
            <> (supportedPropositionTerm . typedProblemAuxiliaryProposition
                <$> auxiliaries)
        )

canonicalLogicalSelectionTypes
    :: CanonicalTerm global
    -> Set CoreType
canonicalLogicalSelectionTypes = \case
    CBound{} -> mempty
    CGlobal{} -> mempty
    CIntrinsic{} -> mempty
    CLogicalSelect coreType -> Set.singleton coreType
    COpaqueInteger{} -> mempty
    CApp function argument ->
        canonicalLogicalSelectionTypes function
            <> canonicalLogicalSelectionTypes argument
    CLam _binderType body -> canonicalLogicalSelectionTypes body
    CFalsum -> mempty
    CTruth -> mempty
    CNot proposition -> canonicalLogicalSelectionTypes proposition
    CAnd left right ->
        canonicalLogicalSelectionTypes left
            <> canonicalLogicalSelectionTypes right
    COr left right ->
        canonicalLogicalSelectionTypes left
            <> canonicalLogicalSelectionTypes right
    CImp premise conclusion ->
        canonicalLogicalSelectionTypes premise
            <> canonicalLogicalSelectionTypes conclusion
    CEq _operandType left right ->
        canonicalLogicalSelectionTypes left
            <> canonicalLogicalSelectionTypes right
    CForall _binderType body -> canonicalLogicalSelectionTypes body
    CExists _binderType body -> canonicalLogicalSelectionTypes body

validateLocalPremiseOrdinals
    :: [TypedLocalPremise local origin global]
    -> Either
        (TypedProblemError local global)
        ()
validateLocalPremiseOrdinals =
    void
        . foldM
            (\seen premise ->
                let ordinal =
                        typedLocalPremiseOrdinal premise
                in
                    if ordinal `Set.member` seen
                        then
                            Left
                                (TypedProblemDuplicateLocalPremiseOrdinal
                                    ordinal)
                        else
                            Right
                                (Set.insert
                                    ordinal
                                    seen))
            Set.empty

isFofCapability :: FofCapability projection -> Bool
isFofCapability = \case
    FofProjectable{} ->
        True
    RequiresTh0{} ->
        False

collectProblemGlobals
    :: Ord global
    => (global -> Maybe CoreType)
    -> SupportedProposition local global
    -> Vector (TypedBackendFact ref global)
    -> Vector (TypedLocalPremise local origin global)
    -> [TypedProblemAuxiliary global]
    -> [TypedLogicalSelectionAuxiliary global]
    -> Either
        (TypedProblemError local global)
        (Map global CoreType)
collectProblemGlobals
        globalType
        claim
        facts
        locals
        auxiliaries
        logicalSelections =
    Map.fromAscList
        <$> traverse
            resolveGlobal
            (Set.toAscList globals)
  where
    globals =
        canonicalGlobals
            (supportedPropositionTerm claim)
            <> foldMap
                (canonicalGlobals
                    . supportedPropositionTerm
                    . typedBackendFactProposition)
                facts
            <> foldMap
                (canonicalGlobals
                    . supportedPropositionTerm
                    . typedLocalPremiseProposition)
                locals
            <> foldMap
                (canonicalGlobals
                    . supportedPropositionTerm
                    . typedProblemAuxiliaryProposition)
                auxiliaries
            <> foldMap
                (canonicalGlobals
                    . supportedPropositionTerm
                    . typedLogicalSelectionAuxiliaryProposition)
                logicalSelections

    resolveGlobal global =
        case globalType global of
            Nothing ->
                Left
                    (TypedProblemClaimClassificationFailed
                        (UnknownBackendGlobal global))
            Just coreType ->
                Right (global, coreType)

collectProblemLocals
    :: Ord local
    => SupportedProposition local global
    -> Vector (TypedLocalPremise local origin global)
    -> Either
        (TypedProblemError local global)
        (Map local CoreType)
collectProblemLocals claim locals =
    foldM
        insertSupport
        Map.empty
        supports
  where
    supports =
        Vector.toList
            (supportedPropositionSupport claim)
            <> concatMap
                (Vector.toList
                    . supportedPropositionSupport
                    . typedLocalPremiseProposition)
                (Vector.toList locals)

    insertSupport current (local, coreType) =
        case Map.lookup local current of
            Nothing ->
                Right
                    (Map.insert
                        local
                        coreType
                        current)
            Just previousType
                | previousType == coreType ->
                    Right current
                | otherwise ->
                    Left
                        (TypedProblemLocalTypeMismatch
                            local
                            previousType
                            coreType)

typedProblemRoute
    :: TypedProblem ref local origin global
    -> TypedProblemRoute
typedProblemRoute
        (TypedProblem
            route
            _claim
            _facts
            _locals
            _auxiliaries
            _logicalSelections
            _globals
            _localTypes) =
    route

typedProblemClaim
    :: TypedProblem ref local origin global
    -> SupportedProposition local global
typedProblemClaim
        (TypedProblem
            _route
            claim
            _facts
            _locals
            _auxiliaries
            _logicalSelections
            _globals
            _localTypes) =
    claim

typedProblemGlobalPremises
    :: TypedProblem ref local origin global
    -> Vector (TypedBackendFact ref global)
typedProblemGlobalPremises
        (TypedProblem
            _route
            _claim
            facts
            _locals
            _auxiliaries
            _logicalSelections
            _globals
            _localTypes) =
    facts

typedProblemLocalPremises
    :: TypedProblem ref local origin global
    -> Vector (TypedLocalPremise local origin global)
typedProblemLocalPremises
        (TypedProblem
            _route
            _claim
            _facts
            locals
            _auxiliaries
            _logicalSelections
            _globals
            _localTypes) =
    locals

typedProblemAuxiliaries
    :: TypedProblem ref local origin global
    -> Vector (TypedProblemAuxiliary global)
typedProblemAuxiliaries
        (TypedProblem
            _route
            _claim
            _facts
            _locals
            auxiliaries
            _logicalSelections
            _globals
            _localTypes) =
    auxiliaries

typedProblemLogicalSelections
    :: TypedProblem ref local origin global
    -> Vector (TypedLogicalSelectionAuxiliary global)
typedProblemLogicalSelections
        (TypedProblem
            _route
            _claim
            _facts
            _locals
            _auxiliaries
            logicalSelections
            _globals
            _localTypes) =
    logicalSelections

typedProblemGlobalTypes
    :: TypedProblem ref local origin global
    -> Map global CoreType
typedProblemGlobalTypes
        (TypedProblem
            _route
            _claim
            _facts
            _locals
            _auxiliaries
            _logicalSelections
            globals
            _localTypes) =
    globals

typedProblemLocalTypes
    :: TypedProblem ref local origin global
    -> Map local CoreType
typedProblemLocalTypes
        (TypedProblem
            _route
            _claim
            _facts
            _locals
            _auxiliaries
            _logicalSelections
            _globals
            localTypes) =
    localTypes
