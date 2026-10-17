{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Schema-checked identities and targets for the extensional record
-- metatheory.  Proof construction lives here as it is implemented; this
-- initial layer deliberately contains no declaration or authority concepts.
module Felix.Checking.Record.Proof
    ( PreparedRecordField(..)
    , PreparedRecordSchema
    , prepareRecordSchema
    , preparedRecordSchemaFields
    , CheckedRecordSchema
    , checkRecordSchema
    , recordLawInventory
    , recordLawTarget
    , CheckedRecordSchemaLaw
    , checkRecordSchemaLaw
    , RecordLawDependency(..)
    , recordLawDependencies
    , CheckedRecordImport(..)
    , buildRecordLawProof
    , buildRecordOpenShapeWeakeningProof
    , weakenRecordOpenShape
    , RecordProofError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Record (RecordSchemaLaw(..))
import Felix.Checking.Record qualified as Record

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)


data PreparedRecordField = PreparedRecordField
    { preparedRecordFieldId         :: !FieldId
    , preparedRecordFieldSelector   :: !ObjectId
    , preparedRecordFieldProjection :: !ObjectId
    }
    deriving stock (Show, Eq, Ord)

data PreparedRecordSchema = PreparedRecordSchema
    { preparedRecordSchemaTheory  :: !TheoryId
    , schemaFields  :: ![PreparedRecordField]
    , preparedRecordSchemaCatalogue :: !RecordLawCatalogue
    }

data CheckedRecordSchema = CheckedRecordSchema
    { checkedRecordSchemaPrepared :: !PreparedRecordSchema
    , checkedRecordSchemaClosure  :: !CheckedObjectClosure
    }

data RecordLawEntry = RecordLawEntry
    { recordLawEntryTarget
        :: !(FrozenCheckedCore ObjectId)
    , recordLawEntryDependencies
        :: ![RecordLawDependency]
    }

data RecordLawCatalogue = RecordLawCatalogue
    { recordLawCatalogueOrder
        :: ![RecordSchemaLaw]
    , recordLawCatalogueEntries
        :: !(Map RecordSchemaLaw RecordLawEntry)
    }

data CheckedRecordSchemaLaw = CheckedRecordSchemaLaw
    { checkedRecordSchemaLawSchema
        :: !CheckedRecordSchema
    , checkedRecordSchemaLawIdentity
        :: !RecordSchemaLaw
    , checkedRecordSchemaLawTarget
        :: !(FrozenCheckedCore ObjectId)
    , checkedRecordSchemaLawDependencies
        :: ![RecordLawDependency]
    }

data RecordLawDependency
    = RecordSelectorDefinition !FieldId
    | RecordProjectionMembership !FieldId
    | RecordGeneratedDependency !RecordSchemaLaw
    deriving stock (Show, Eq, Ord)

data CheckedRecordImport = CheckedRecordImport
    { checkedRecordImportDependency  :: !RecordLawDependency
    , checkedRecordImportProposition :: !(FrozenCheckedCore ObjectId)
    }
    deriving stock (Show, Eq, Ord)

data IndexedRecordImport = IndexedRecordImport
    !RecordLawDependency
    !Kernel.ImportIx
    !(FrozenCheckedCore ObjectId)

data RecordProofError
    = DuplicateRecordField !FieldId
    | DuplicateRecordResource !ObjectId
    | NoncanonicalRecordSelector !FieldId !ObjectId !ObjectId
    | NoncanonicalRecordProjection !FieldId !ObjectId !ObjectId
    | RecordLawCardinalityMismatch !Text !Int !Int
    | RecordLawTargetCoreInvalid
        !RecordSchemaLaw !CoreCheckError
    | RecordLawTargetNotProposition
        !RecordSchemaLaw !CoreType
    | RecordSchemaTheoryMismatch !TheoryId !TheoryId
    | RecordSchemaObjectMissing !ObjectId
    | RecordWeakeningFieldMissing !FieldId
    | RecordSchemaLawUnavailable !RecordSchemaLaw
    | RecordProofFoundationTheoryMismatch !TheoryId !TheoryId
    | RecordProofDependencySequenceMismatch
        ![RecordLawDependency] ![RecordLawDependency]
    | RecordProofDependencyPropositionMismatch
        !RecordLawDependency
        !(FrozenCheckedCore ObjectId)
        !(FrozenCheckedCore ObjectId)
    | RecordProofDependencyTargetUnavailable !RecordLawDependency
    | RecordProofKernelBuildFailed !KernelProof.KernelProofBuildError
    | RecordProofFinalTargetMismatch
        !(FrozenCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
    deriving stock (Show, Eq)

prepareRecordSchema
    :: TheoryId
    -> GlobalTyping ObjectId
    -> [PreparedRecordField]
    -> Either RecordProofError PreparedRecordSchema
prepareRecordSchema theory globalTyping fields = do
    validatePreparedFields theory fields
    catalogue <- buildRecordLawCatalogue globalTyping fields
    pure
        PreparedRecordSchema
            { preparedRecordSchemaTheory = theory
            , schemaFields = fields
            , preparedRecordSchemaCatalogue = catalogue
            }

-- | An observation, not an exported record label: callers cannot update a
-- prepared schema's fields independently of its checked law catalogue.
preparedRecordSchemaFields :: PreparedRecordSchema -> [PreparedRecordField]
preparedRecordSchemaFields = schemaFields

checkRecordSchema
    :: CheckedObjectClosure
    -> PreparedRecordSchema
    -> Either RecordProofError CheckedRecordSchema
checkRecordSchema closure schema = do
    unless (checkedObjectClosureTheory closure == theory)
        (Left
            (RecordSchemaTheoryMismatch
                theory
                (checkedObjectClosureTheory closure)))
    traverse_ requireObject
        [ object
        | field <- fields
        , object <-
            [ preparedRecordFieldSelector field
            , preparedRecordFieldProjection field
            ]
        ]
    pure
        CheckedRecordSchema
            { checkedRecordSchemaPrepared = schema
            , checkedRecordSchemaClosure = closure
            }
  where
    theory = preparedRecordSchemaTheory schema
    fields = preparedRecordSchemaFields schema

    requireObject object =
        unless (isJust (lookupCheckedObjectContent object closure))
            (Left (RecordSchemaObjectMissing object))

-- | Inclusion of checked field families induces open-shape weakening. This
-- derivation needs no imported facts: it only projects and rebuilds the
-- conjunction of functionality and field-presence requirements.
buildRecordOpenShapeWeakeningProof
    :: CheckedFoundation
    -> CheckedRecordSchema
    -> CheckedRecordSchema
    -> Either RecordProofError (KernelProof.BuiltProof ObjectId)
buildRecordOpenShapeWeakeningProof foundation child parent = do
    unless (parentTheory == childTheory)
        (Left (RecordSchemaTheoryMismatch childTheory parentTheory))
    unless (theoryId foundation == childTheory)
        (Left
            (RecordProofFoundationTheoryMismatch
                childTheory (theoryId foundation)))
    traverse_ requireIncluded (preparedRecordSchemaFields parentSchema)
    first RecordProofKernelBuildFailed
        (KernelProof.forallIntroductionProof root TySet
            (\withRecord record -> do
                premise <- KernelProof.scopedTerm withRecord
                    (Record.recordOpenShape
                        (schemaSelectors childSchema) (scopedCoreTerm record))
                KernelProof.implicationIntroductionProof
                    withRecord premise
                    (\withPremise assumption ->
                        weakenOpenShapeInContext withPremise
                            (schemaSelectors childSchema) (schemaSelectors parentSchema)
                            (scopedCoreTerm record) assumption)))
  where
    childSchema = checkedRecordSchemaPrepared child
    parentSchema = checkedRecordSchemaPrepared parent
    childTheory = preparedRecordSchemaTheory childSchema
    parentTheory = preparedRecordSchemaTheory parentSchema
    root = KernelProof.rootProofContext foundation
        (globalTypingFromClosure (checkedRecordSchemaClosure child))
    childFields = Set.fromList (preparedRecordSchemaFields childSchema)
    requireIncluded field =
        unless (Set.member field childFields)
            (Left (RecordWeakeningFieldMissing (preparedRecordFieldId field)))

-- | Use a checked field subfamily inside a larger derivation. Selecting by
-- field identity retains the child's canonical resources and avoids building
-- another complete law catalogue merely to weaken a shape.
weakenRecordOpenShape
    :: KernelProof.ProofContext ObjectId
    -> CheckedRecordSchema
    -> [FieldId]
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either RecordProofError (KernelProof.BuiltProof ObjectId)
weakenRecordOpenShape context child parentFields subject premise = do
    case firstDuplicate parentFields of
        Just field -> Left (DuplicateRecordField field)
        Nothing -> pure ()
    selectors <- traverse
        (\field -> maybe (Left (RecordWeakeningFieldMissing field))
            (Right . CGlobal . preparedRecordFieldSelector)
            (Map.lookup field fields)) parentFields
    first RecordProofKernelBuildFailed
        (weakenOpenShapeInContext context (schemaSelectors schema) selectors subject premise)
  where
    schema = checkedRecordSchemaPrepared child
    fields = Map.fromList
        [(preparedRecordFieldId field, field) | field <- preparedRecordSchemaFields schema]

weakenOpenShapeInContext
    :: KernelProof.ProofContext ObjectId
    -> [CanonicalTerm ObjectId]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either KernelProof.KernelProofBuildError (KernelProof.BuiltProof ObjectId)
weakenOpenShapeInContext context childSelectors parentSelectors subject premise = do
    expected <- KernelProof.scopedTerm context (Record.recordOpenShape childSelectors subject)
    unless (KernelProof.builtProofStatement premise == expected)
        (Left (KernelProof.ProofStructuralCompositionMismatch
            "open-shape weakening requires the checked child shape"))
    deriveConjunct context [premise] (Record.recordOpenShape parentSelectors subject)

recordLawInventory
    :: PreparedRecordSchema
    -> [RecordSchemaLaw]
recordLawInventory =
    recordLawCatalogueOrder . preparedRecordSchemaCatalogue

recordLawTarget
    :: PreparedRecordSchema
    -> RecordSchemaLaw
    -> Either RecordProofError (FrozenCheckedCore ObjectId)
recordLawTarget schema law =
    recordLawEntryTarget <$> lookupRecordLawEntry schema law

checkRecordSchemaLaw
    :: CheckedRecordSchema
    -> RecordSchemaLaw
    -> Either RecordProofError CheckedRecordSchemaLaw
checkRecordSchemaLaw checked law = do
    entry <- lookupRecordLawEntry schema law
    pure
        CheckedRecordSchemaLaw
            { checkedRecordSchemaLawSchema = checked
            , checkedRecordSchemaLawIdentity = law
            , checkedRecordSchemaLawTarget = recordLawEntryTarget entry
            , checkedRecordSchemaLawDependencies =
                recordLawEntryDependencies entry
            }
  where
    schema = checkedRecordSchemaPrepared checked

recordLawDependencies
    :: PreparedRecordSchema
    -> RecordSchemaLaw
    -> Either RecordProofError [RecordLawDependency]
recordLawDependencies schema law =
    recordLawEntryDependencies <$> lookupRecordLawEntry schema law

lookupRecordLawEntry
    :: PreparedRecordSchema
    -> RecordSchemaLaw
    -> Either RecordProofError RecordLawEntry
lookupRecordLawEntry schema law =
    maybe
        (Left (RecordSchemaLawUnavailable law))
        Right
        (Map.lookup law
            (recordLawCatalogueEntries
                (preparedRecordSchemaCatalogue schema)))

-- | Build one deterministic certificate from the exact declared imports.
buildRecordLawProof
    :: CheckedFoundation
    -> CheckedRecordSchemaLaw
    -> [CheckedRecordImport]
    -> Either RecordProofError (KernelProof.BuiltProof ObjectId)
buildRecordLawProof
        foundation
        checkedLaw
        imports = do
    unless (theoryId foundation == theory)
        (Left
            (RecordProofFoundationTheoryMismatch
                theory
                (theoryId foundation)))
    let suppliedDependencies = checkedRecordImportDependency <$> imports
    unless (suppliedDependencies == expectedDependencies)
        (Left
            (RecordProofDependencySequenceMismatch
                expectedDependencies
                suppliedDependencies))
    traverse_ (validateImport closure schema) imports
    let root = KernelProof.rootProofContext
            foundation
            (globalTypingFromClosure closure)
    let indexedImports = indexRecordImports imports
    proof <-
        case law of
            RecordExactGraphLaw ->
                first RecordProofKernelBuildFailed
                    (buildExactGraphProof root schema)
            RecordReductMembershipLaw ->
                first RecordProofKernelBuildFailed
                    (buildReductMembershipProof
                        root
                        (schemaSelectors schema))
            RecordReductExactLaw ->
                first RecordProofKernelBuildFailed
                    (buildReductExactProof root schema indexedImports)
            RecordProjectionEntryLaw field ->
                first RecordProofKernelBuildFailed
                    (buildProjectionEntryProof
                        root
                        schema
                        field
                        indexedImports)
            RecordProjectionAgreementLaw field ->
                first RecordProofKernelBuildFailed
                    (buildProjectionAgreementProof
                        root schema field indexedImports)
            RecordProjectionEntryAgreementLaw ->
                first RecordProofKernelBuildFailed
                    (buildProjectionEntryAgreementProof
                        root schema indexedImports)
            RecordProjectionGraphAgreementLaw ->
                first RecordProofKernelBuildFailed
                    (buildProjectionGraphAgreementProof
                        root schema indexedImports)
            RecordProjectionExtensionalityLaw ->
                first RecordProofKernelBuildFailed
                    (buildProjectionExtensionalityProof
                        root schema indexedImports)
            RecordReductIdentityLaw ->
                first RecordProofKernelBuildFailed
                    (buildReductIdentityProof root schema indexedImports)
            RecordReductProjectionLaw field ->
                first RecordProofKernelBuildFailed
                    (buildReductProjectionProof
                        root schema field indexedImports)
            RecordSelectorPairDistinctLaw left right ->
                do
                    selectorImports <-
                        first RecordProofKernelBuildFailed
                            (traverse (importedProofAt root) indexedImports)
                    first RecordProofKernelBuildFailed
                        (buildSelectorPairDistinctProof
                            root
                            schema
                            left
                            right
                            selectorImports)
            RecordSelectorDistinctLaw ->
                first RecordProofKernelBuildFailed
                    (buildImportedConjunction root indexedImports)
            RecordAggregateEntryLaw field ->
                first RecordProofKernelBuildFailed
                    (buildAggregateEntryProof root schema field)
            RecordAggregatePairCodedLaw ->
                first RecordProofKernelBuildFailed
                    (buildAggregatePairCodedProof root schema)
            RecordAggregateValueUniqueLaw field ->
                first RecordProofKernelBuildFailed
                    (buildAggregateValueUniqueProof
                        root
                        schema
                        field
                        indexedImports)
            RecordAggregateSelectorClosedLaw ->
                first RecordProofKernelBuildFailed
                    (buildAggregateSelectorClosedProof root schema)
            RecordAggregateProjectionApplicationLaw field ->
                first RecordProofKernelBuildFailed
                    (buildAggregateProjectionApplicationProof
                        root schema field indexedImports)
            RecordAggregateFunctionalLaw ->
                first RecordProofKernelBuildFailed
                    (buildAggregateFunctionalProof
                        root
                        schema
                        indexedImports)
            RecordAggregateExactLaw ->
                first RecordProofKernelBuildFailed
                    (buildAggregateExactProof root schema indexedImports)
            RecordAggregateProjectionLaw field ->
                first RecordProofKernelBuildFailed
                    (buildAggregateProjectionProof
                        root schema field indexedImports)
    let actual = KernelProof.builtProofStatement proof
    unless (actual == embedClosedCore [] expected)
        (Left (RecordProofFinalTargetMismatch expected actual))
    pure proof
  where
    checkedSchema = checkedRecordSchemaLawSchema checkedLaw
    schema = checkedRecordSchemaPrepared checkedSchema
    closure = checkedRecordSchemaClosure checkedSchema
    law = checkedRecordSchemaLawIdentity checkedLaw
    expected = checkedRecordSchemaLawTarget checkedLaw
    expectedDependencies = checkedRecordSchemaLawDependencies checkedLaw
    theory = preparedRecordSchemaTheory schema

indexRecordImports :: [CheckedRecordImport] -> [IndexedRecordImport]
indexRecordImports = go 0
  where
    go _index [] = []
    go index (checkedImport : remaining) =
        IndexedRecordImport
            (checkedRecordImportDependency checkedImport)
            (Kernel.importIx index)
            (checkedRecordImportProposition checkedImport)
            : go (index + 1) remaining

importedProofAt
    :: KernelProof.ProofContext ObjectId
    -> IndexedRecordImport
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
importedProofAt context
        (IndexedRecordImport _dependency index proposition) =
    KernelProof.importedProof context index proposition

buildImportedConjunction
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildImportedConjunction context imports = do
    proofs <- traverse (importedProofAt context) imports
    KernelProof.buildLeftAssociatedConjunction context proofs

validateImport
    :: CheckedObjectClosure
    -> PreparedRecordSchema
    -> CheckedRecordImport
    -> Either RecordProofError ()
validateImport closure schema checkedImport = do
    expected <- dependencyTarget closure schema dependency
    unless (checkedRecordImportProposition checkedImport == expected)
        (Left
            (RecordProofDependencyPropositionMismatch
                dependency
                expected
                (checkedRecordImportProposition checkedImport)))
  where
    dependency = checkedRecordImportDependency checkedImport

dependencyTarget
    :: CheckedObjectClosure
    -> PreparedRecordSchema
    -> RecordLawDependency
    -> Either RecordProofError (FrozenCheckedCore ObjectId)
dependencyTarget closure schema = \case
    RecordGeneratedDependency dependency ->
        recordLawTarget schema dependency
    dependency@(RecordProjectionMembership field) -> do
        prepared <- schemaField schema field
        checkDependencyTarget dependency closure
            (Record.recordProjectionMembershipLaw
                (CGlobal (preparedRecordFieldSelector prepared))
                (CGlobal (preparedRecordFieldProjection prepared)))
    dependency@(RecordSelectorDefinition field) -> do
        prepared <- schemaFieldForDependency schema dependency field
        case lookupCheckedObjectContent
                (preparedRecordFieldSelector prepared)
                closure of
            Just (TransparentObjectContent _theory coreType body) ->
                checkDependencyTarget dependency closure
                    (canonicalDefinitionEquationTarget
                        (preparedRecordFieldSelector prepared)
                        coreType
                        body)
            _ -> Left (RecordProofDependencyTargetUnavailable dependency)

checkDependencyTarget
    :: RecordLawDependency
    -> CheckedObjectClosure
    -> CanonicalTerm ObjectId
    -> Either RecordProofError (FrozenCheckedCore ObjectId)
checkDependencyTarget dependency closure term = do
    target <-
        first
            (const (RecordProofDependencyTargetUnavailable dependency))
            (checkCanonicalCore
                (globalTypingFromClosure closure)
                term)
    unless (frozenCoreType target == TyProp)
        (Left (RecordProofDependencyTargetUnavailable dependency))
    pure target

schemaField
    :: PreparedRecordSchema
    -> FieldId
    -> Either RecordProofError PreparedRecordField
schemaField schema identity =
    schemaFieldForDependency
        schema
        (RecordProjectionMembership identity)
        identity

schemaFieldForDependency
    :: PreparedRecordSchema
    -> RecordLawDependency
    -> FieldId
    -> Either RecordProofError PreparedRecordField
schemaFieldForDependency schema dependency identity =
    maybe
        (Left (RecordProofDependencyTargetUnavailable dependency))
        Right
        (List.find
            ((== identity) . preparedRecordFieldId)
            (preparedRecordSchemaFields schema))

schemaSelectors
    :: PreparedRecordSchema
    -> [CanonicalTerm ObjectId]
schemaSelectors schema =
    [ CGlobal (preparedRecordFieldSelector field)
    | field <- preparedRecordSchemaFields schema
    ]

buildProjectionEntryProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionEntryProof root schema field imports = do
    preparedField <- kernelSchemaField schema field
    let selector = CGlobal (preparedRecordFieldSelector preparedField)
        projection = CGlobal (preparedRecordFieldProjection preparedField)
    KernelProof.forallIntroductionProof root TySet
        (\withRecord _record ->
            KernelProof.forallIntroductionProof withRecord TySet
                (\context _value -> do
                    let record = CBound 1
                        value = CBound 0
                        functional = Record.recordFunctional record
                        entry = orderedPair selector value
                        entryMembership = membership entry record
                        projectionValue = CApp projection record
                    functionalPremise <-
                        KernelProof.scopedTerm context functional
                    KernelProof.implicationIntroductionProof
                        context
                        functionalPremise
                        (\withFunctional _functionalProof -> do
                            membershipPremise <-
                                KernelProof.scopedTerm
                                    withFunctional
                                    entryMembership
                            KernelProof.implicationIntroductionProof
                                withFunctional
                                membershipPremise
                                (\withEntry _entryProof ->
                                    buildProjectionExtensionality
                                        withEntry
                                        field
                                        imports
                                        selector
                                        projectionValue
                                        record
                                        value))))

buildProjectionExtensionality
    :: KernelProof.ProofContext ObjectId
    -> FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionExtensionality
        context
        field
        imports
        selector
        projectionValue
        record
        value = do
    forward <-
        buildMembershipSubset context projectionValue value
            (proveProjectionMemberForward
                field imports selector projectionValue record value)
    backward <-
        buildMembershipSubset context value projectionValue
            (proveProjectionMemberBackward
                field imports selector projectionValue record value)
    left <- KernelProof.scopedTerm context projectionValue
    right <- KernelProof.scopedTerm context value
    extensionality <-
        KernelProof.foundationInstanceProof
            context
            SetExtensionality
            [left, right]
    afterForward <-
        applyImplicationConverted context extensionality forward
    applyImplicationConverted context afterForward backward

buildMembershipSubset
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> ( KernelProof.ProofContext ObjectId
         -> CanonicalTerm ObjectId
         -> KernelProof.BuiltProof ObjectId
         -> Either
            KernelProof.KernelProofBuildError
            (KernelProof.BuiltProof ObjectId)
       )
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildMembershipSubset context source target prove =
    KernelProof.forallIntroductionProof context TySet
        (\withElement _element -> do
            let shiftedSource = shiftCanonical 1 0 source
                shiftedTarget = shiftCanonical 1 0 target
                element = CBound 0
            premise <- KernelProof.scopedTerm withElement
                (membership element shiftedSource)
            KernelProof.implicationIntroductionProof
                withElement
                premise
                (\withMembership membershipProof ->
                    prove
                        withMembership
                        element
                        membershipProof
                    >>= \proof -> do
                        expected <- KernelProof.scopedTerm withMembership
                            (membership element shiftedTarget)
                        KernelProof.conversionProof
                            withMembership
                            proof
                            expected))

proveProjectionMemberForward
    :: FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveProjectionMemberForward
        field
        imports
        selector
        projectionValue
        record
        value
        context
        element
        projectionMembership = do
    let shiftedRecord = shiftCanonical 1 0 record
        shiftedValue = shiftCanonical 1 0 value
        shiftedProjection = shiftCanonical 1 0 projectionValue
    membershipLaw <-
        specializedProjectionMembership
            context
            field
            imports
            shiftedRecord
            element
    expectedMembership <- KernelProof.scopedTerm context
        (membership element shiftedProjection)
    checkedMembership <-
        KernelProof.conversionProof
            context
            projectionMembership
            expectedMembership
    existential <-
        KernelProof.equalityModusPonensProof
            context
            membershipLaw
            checkedMembership
    bodyUnderBinder <-
        existentialBodyProofContext context existential
    target <- KernelProof.scopedTerm context
        (membership element shiftedValue)
    KernelProof.existentialEliminationProof
        context
        TySet
        bodyUnderBinder
        existential
        target
        (\withWitness _witness bodyProof ->
            proveProjectionWitnessForward
                withWitness
                selector
                record
                value
                element
                bodyProof)

proveProjectionWitnessForward
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveProjectionWitnessForward
        context
        selector
        record
        value
        element
        bodyProof = do
    let witness = CBound 0
        shiftedElement = shiftCanonical 1 0 element
        shiftedRecord = shiftCanonical 2 0 record
        shiftedValue = shiftCanonical 2 0 value
    entryInRecord <-
        KernelProof.conjunctionLeftProof
            context
            bodyProof
    conditions <-
        KernelProof.conjunctionRightProof
            context
            bodyProof
    firstEqualsSelector <-
        KernelProof.conjunctionLeftProof
            context
            conditions
    elementInSecond <-
        KernelProof.conjunctionRightProof
            context
            conditions
    let knownEntry = orderedPair selector shiftedValue
        knownMembership = membership knownEntry shiftedRecord
        functional = Record.recordFunctional shiftedRecord
    knownMembershipTerm <- KernelProof.scopedTerm context knownMembership
    knownEntryProof <- KernelProof.hypothesisProof context knownMembershipTerm
    functionalTerm <- KernelProof.scopedTerm context functional
    functionalProof <- KernelProof.hypothesisProof context functionalTerm
    rightUnique <- projectRecordRightUnique context shiftedRecord functionalProof
    firstProjection <- orderedPairProjectionProof
        context OrderedPairFirst selector shiftedValue
    selectorToKnownFirst <-
        KernelProof.equalityReverseProof context firstProjection
    firstCoordinatesEqual <-
        KernelProof.composeEqualityProof
            context
            firstEqualsSelector
            selectorToKnownFirst
    uniquenessPremise <-
        KernelProof.buildLeftAssociatedConjunction
            context
            [entryInRecord, knownEntryProof, firstCoordinatesEqual]
    witnessUnique <- KernelProof.specializeForalls
        context rightUnique [witness, knownEntry]
    secondsEqual <-
        applyImplicationConverted context witnessUnique uniquenessPremise
    secondProjection <- orderedPairProjectionProof
        context OrderedPairSecond selector shiftedValue
    witnessSecondEqualsValue <-
        KernelProof.composeEqualityProof
            context
            secondsEqual
            secondProjection
    shiftedElementTerm <- KernelProof.scopedTerm context shiftedElement
    KernelProof.transportMembershipProof
        context
        shiftedElementTerm
        witnessSecondEqualsValue
        elementInSecond

proveProjectionMemberBackward
    :: FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveProjectionMemberBackward
        field
        imports
        selector
        projectionValue
        record
        value
        context
        element
        valueMembership = do
    let shiftedRecord = shiftCanonical 1 0 record
        shiftedValue = shiftCanonical 1 0 value
        shiftedProjection = shiftCanonical 1 0 projectionValue
        knownEntry = orderedPair selector shiftedValue
        knownMembership = membership knownEntry shiftedRecord
    knownMembershipTerm <- KernelProof.scopedTerm context knownMembership
    knownEntryProof <- KernelProof.hypothesisProof context knownMembershipTerm
    firstProjection <- orderedPairProjectionProof
        context OrderedPairFirst selector shiftedValue
    secondProjection <- orderedPairProjectionProof
        context OrderedPairSecond selector shiftedValue
    shiftedElement <- KernelProof.scopedTerm context element
    valueToSecond <-
        KernelProof.equalityReverseProof context secondProjection
    elementInSecond <-
        KernelProof.transportMembershipProof
            context
            shiftedElement
            valueToSecond
            valueMembership
    bodyProof <-
        KernelProof.conjunctionIntroductionProof
            context
            knownEntryProof
            =<< KernelProof.conjunctionIntroductionProof
                context
                firstProjection
                elementInSecond
    membershipLaw <-
        specializedProjectionMembership
            context
            field
            imports
            shiftedRecord
            element
    existentialTarget <-
        case scopedCoreTerm (KernelProof.builtProofStatement membershipLaw) of
            CEq TyProp _left right -> KernelProof.scopedTerm context right
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "projection membership import is not an equivalence")
    (underBinder, _witnessVariable) <-
        KernelProof.extendProofContextBinder context TySet
    bodyUnderBinder <-
        case scopedCoreTerm existentialTarget of
            CExists TySet body -> KernelProof.scopedTerm underBinder body
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "projection membership import lacks its witness")
    witness <- KernelProof.scopedTerm context knownEntry
    existential <-
        KernelProof.existentialIntroductionProof
            context
            TySet
            bodyUnderBinder
            witness
            bodyProof
    reversed <- KernelProof.equalityReverseProof context membershipLaw
    projected <-
        KernelProof.equalityModusPonensProof context reversed existential
    expected <- KernelProof.scopedTerm context
        (membership element shiftedProjection)
    KernelProof.conversionProof context projected expected

specializedProjectionMembership
    :: KernelProof.ProofContext ObjectId
    -> FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
specializedProjectionMembership context field imports record element = do
    checkedImport <-
        case
            [ candidate
            | candidate@(IndexedRecordImport dependency _index _proposition) <-
                imports
            , dependency == RecordProjectionMembership field
            ] of
            [candidate] -> Right candidate
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "projection entry lacks its membership import")
    imported <- importedProofAt context checkedImport
    KernelProof.specializeForalls context imported [record, element]

applyImplicationConverted
    :: KernelProof.ProofContext ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
applyImplicationConverted context implication premise = do
    expectedPremise <-
        case scopedCoreTerm (KernelProof.builtProofStatement implication) of
            CImp expected _conclusion -> KernelProof.scopedTerm context expected
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "record proof expected an implication")
    converted <- KernelProof.conversionProof context premise expectedPremise
    KernelProof.implicationEliminationProof context implication converted

existentialBodyProofContext
    :: KernelProof.ProofContext ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (ScopedCheckedCore ObjectId)
existentialBodyProofContext context existential = do
    body <-
        case scopedCoreTerm (KernelProof.builtProofStatement existential) of
            CExists TySet existentialBody -> Right existentialBody
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "record proof expected a set witness")
    (underBinder, _witness) <-
        KernelProof.extendProofContextBinder context TySet
    KernelProof.scopedTerm underBinder body

projectRecordRightUnique
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
projectRecordRightUnique context record functional = do
    let pairCoded = Record.recordPairCoded record
        rightUnique = Record.recordRightUnique record
    unless (scopedCoreTerm (KernelProof.builtProofStatement functional)
            == CAnd pairCoded rightUnique)
        (Left (KernelProof.ProofStructuralCompositionMismatch
            "record functionality describes a different record"))
    KernelProof.conjunctionRightProof
        context
        functional

orderedPairProjectionProof
    :: KernelProof.ProofContext ObjectId
    -> FoundationAxiomTag
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
orderedPairProjectionProof context tag selector value = do
    selectorTerm <- KernelProof.scopedTerm context selector
    valueTerm <- KernelProof.scopedTerm context value
    KernelProof.foundationInstanceProof
        context
        tag
        [selectorTerm, valueTerm]

buildProjectionEntryAgreementProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionEntryAgreementProof root schema imports =
    introduceRecordComparison
        root
        schema
        (\context left right -> do
            (leftExact, rightExact, projectionEqualities) <-
                recordComparisonHypotheses context schema left right
            fieldProofs <- traverse
                (\field -> do
                    let identity = preparedRecordFieldId field
                        selector = CGlobal (preparedRecordFieldSelector field)
                        projection = CGlobal (preparedRecordFieldProjection field)
                    leftFunctional <- deriveConjunct
                        context
                        [leftExact]
                        (Record.recordFunctional left)
                    rightFunctional <- deriveConjunct
                        context
                        [rightExact]
                        (Record.recordFunctional right)
                    leftPresence <- deriveConjunct
                        context
                        [leftExact]
                        (Record.selectorPresent selector left)
                    rightPresence <- deriveConjunct
                        context
                        [rightExact]
                        (Record.selectorPresent selector right)
                    projectionEquality <- deriveConjunct
                        context
                        [projectionEqualities]
                        (CEq TySet
                            (CApp projection left)
                            (CApp projection right))
                    agreementImport <-
                        indexedGeneratedImport
                            (RecordProjectionAgreementLaw identity)
                            imports
                    imported <- importedProofAt context agreementImport
                    agreement <- KernelProof.specializeForalls
                        context imported [left, right]
                    afterLeft <- applyImplicationConverted
                        context agreement leftFunctional
                    afterRight <- applyImplicationConverted
                        context afterLeft rightFunctional
                    afterLeftPresence <- applyImplicationConverted
                        context afterRight leftPresence
                    afterRightPresence <- applyImplicationConverted
                        context afterLeftPresence rightPresence
                    applyImplicationConverted
                        context afterRightPresence projectionEquality)
                (preparedRecordSchemaFields schema)
            KernelProof.buildLeftAssociatedConjunction context fieldProofs)

buildProjectionExtensionalityProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionExtensionalityProof root schema imports =
    introduceRecordComparison root schema
        (\context left right ->
            deriveProjectionRecordEquality
                context schema imports left right)

buildProjectionGraphAgreementProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionGraphAgreementProof root schema imports =
    introduceRecordComparison root schema
        (\context left right ->
            KernelProof.forallIntroductionProof context TySet
                (\withEntry _entry -> do
                    let shiftedLeft = shiftCanonical 1 0 left
                        shiftedRight = shiftCanonical 1 0 right
                        entry = CBound 0
                    equality <- deriveProjectionRecordEquality
                        withEntry schema imports shiftedLeft shiftedRight
                    forwardPremise <- KernelProof.scopedTerm withEntry
                        (membership entry shiftedLeft)
                    forward <- KernelProof.implicationIntroductionProof
                        withEntry
                        forwardPremise
                        (\forwardContext membershipProof -> do
                            entryTerm <- KernelProof.scopedTerm
                                forwardContext entry
                            KernelProof.transportMembershipProof
                                forwardContext
                                entryTerm
                                (KernelProof.weakenProofHypotheses 1 equality)
                                membershipProof)
                    reversed <- KernelProof.equalityReverseProof withEntry equality
                    backwardPremise <- KernelProof.scopedTerm withEntry
                        (membership entry shiftedRight)
                    backward <- KernelProof.implicationIntroductionProof
                        withEntry
                        backwardPremise
                        (\backwardContext membershipProof -> do
                            entryTerm <- KernelProof.scopedTerm
                                backwardContext entry
                            KernelProof.transportMembershipProof
                                backwardContext
                                entryTerm
                                (KernelProof.weakenProofHypotheses 1 reversed)
                                membershipProof)
                    KernelProof.conjunctionIntroductionProof
                        withEntry forward backward))

introduceRecordComparison
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> ( KernelProof.ProofContext ObjectId
         -> CanonicalTerm ObjectId
         -> CanonicalTerm ObjectId
         -> Either
            KernelProof.KernelProofBuildError
            (KernelProof.BuiltProof ObjectId)
       )
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
introduceRecordComparison root schema build =
    KernelProof.forallIntroductionProof root TySet
        (\withLeft _left ->
            KernelProof.forallIntroductionProof withLeft TySet
                (\context _right -> do
                    let left = CBound 1
                        right = CBound 0
                        selectors = schemaSelectors schema
                        leftExact = Record.recordExactShape selectors left
                        rightExact = Record.recordExactShape selectors right
                        projectionEqualities =
                            leftAssociatedConjunction
                                [ CEq TySet
                                    (CApp
                                        (CGlobal
                                            (preparedRecordFieldProjection field))
                                        left)
                                    (CApp
                                        (CGlobal
                                            (preparedRecordFieldProjection field))
                                        right)
                                | field <- preparedRecordSchemaFields schema
                                ]
                    leftPremise <- KernelProof.scopedTerm context leftExact
                    KernelProof.implicationIntroductionProof
                        context
                        leftPremise
                        (\withLeftExact _leftProof -> do
                            rightPremise <- KernelProof.scopedTerm
                                withLeftExact rightExact
                            KernelProof.implicationIntroductionProof
                                withLeftExact
                                rightPremise
                                (\withRightExact _rightProof -> do
                                    equalityPremise <- KernelProof.scopedTerm
                                        withRightExact projectionEqualities
                                    KernelProof.implicationIntroductionProof
                                        withRightExact
                                        equalityPremise
                                        (\withEqualities _equalityProof ->
                                            build
                                                withEqualities
                                                left
                                                right)))))

recordComparisonHypotheses
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        ( KernelProof.BuiltProof ObjectId
        , KernelProof.BuiltProof ObjectId
        , KernelProof.BuiltProof ObjectId
        )
recordComparisonHypotheses context schema left right = do
    let selectors = schemaSelectors schema
        projectionEqualities =
            leftAssociatedConjunction
                [ CEq TySet
                    (CApp
                        (CGlobal (preparedRecordFieldProjection field)) left)
                    (CApp
                        (CGlobal (preparedRecordFieldProjection field)) right)
                | field <- preparedRecordSchemaFields schema
                ]
    leftExact <- KernelProof.scopedTerm context
        (Record.recordExactShape selectors left)
        >>= KernelProof.hypothesisProof context
    rightExact <- KernelProof.scopedTerm context
        (Record.recordExactShape selectors right)
        >>= KernelProof.hypothesisProof context
    equalities <- KernelProof.scopedTerm context projectionEqualities
        >>= KernelProof.hypothesisProof context
    pure (leftExact, rightExact, equalities)

deriveProjectionRecordEquality
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
deriveProjectionRecordEquality context schema imports left right = do
    (leftExact, rightExact, projectionEqualities) <-
        recordComparisonHypotheses context schema left right
    entryAgreementImport <-
        indexedGeneratedImport RecordProjectionEntryAgreementLaw imports
    importedEntryAgreement <- importedProofAt context entryAgreementImport
    entryAgreement <- KernelProof.specializeForalls
        context importedEntryAgreement [left, right]
    afterEntryLeft <- applyImplicationConverted
        context entryAgreement leftExact
    afterEntryRight <- applyImplicationConverted
        context afterEntryLeft rightExact
    entries <- applyImplicationConverted
        context afterEntryRight projectionEqualities
    exactGraphImport <- indexedGeneratedImport RecordExactGraphLaw imports
    importedExactGraph <- importedProofAt context exactGraphImport
    exactGraph <- KernelProof.specializeForalls
        context importedExactGraph [left, right]
    afterGraphLeft <- applyImplicationConverted context exactGraph leftExact
    afterGraphRight <- applyImplicationConverted
        context afterGraphLeft rightExact
    applyImplicationConverted context afterGraphRight entries

deriveConjunct
    :: KernelProof.ProofContext ObjectId
    -> [KernelProof.BuiltProof ObjectId]
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
deriveConjunct context premises targetTerm = do
    target <- KernelProof.scopedTerm context targetTerm
    derived <- KernelProof.conjunctionAssumptionProof context premises target
    maybe
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "record comparison cannot project a required conjunct"))
        Right
        derived

buildProjectionAgreementProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildProjectionAgreementProof root schema field imports = do
    preparedField <- kernelSchemaField schema field
    let selector = CGlobal (preparedRecordFieldSelector preparedField)
        projection = CGlobal (preparedRecordFieldProjection preparedField)
    KernelProof.forallIntroductionProof root TySet
        (\withLeft _left ->
            KernelProof.forallIntroductionProof withLeft TySet
                (\context _right -> do
                    let left = CBound 1
                        right = CBound 0
                        premises =
                            [ Record.recordFunctional left
                            , Record.recordFunctional right
                            , Record.selectorPresent selector left
                            , Record.selectorPresent selector right
                            , CEq TySet
                                (CApp projection left)
                                (CApp projection right)
                            ]
                    KernelProof.introduceImplications context premises
                        (\withPremises ->
                            KernelProof.forallIntroductionProof
                                withPremises
                                TySet
                                (\withValue _value -> do
                                    let shiftedLeft = shiftCanonical 1 0 left
                                        shiftedRight = shiftCanonical 1 0 right
                                        value = CBound 0
                                    forwardPremise <- KernelProof.scopedTerm
                                        withValue
                                        (membership
                                            (orderedPair selector value)
                                            shiftedLeft)
                                    forward <-
                                        KernelProof.implicationIntroductionProof
                                            withValue
                                            forwardPremise
                                            (\forwardContext _member ->
                                                proveProjectionAgreementDirection
                                                    forwardContext
                                                    field
                                                    imports
                                                    selector
                                                    projection
                                                    shiftedLeft
                                                    shiftedRight
                                                    value
                                                    False)
                                    backwardPremise <- KernelProof.scopedTerm
                                        withValue
                                        (membership
                                            (orderedPair selector value)
                                            shiftedRight)
                                    backward <-
                                        KernelProof.implicationIntroductionProof
                                            withValue
                                            backwardPremise
                                            (\backwardContext _member ->
                                                proveProjectionAgreementDirection
                                                    backwardContext
                                                    field
                                                    imports
                                                    selector
                                                    projection
                                                    shiftedRight
                                                    shiftedLeft
                                                    value
                                                    True)
                                    KernelProof.conjunctionIntroductionProof
                                        withValue
                                        forward
                                        backward))))

proveProjectionAgreementDirection
    :: KernelProof.ProofContext ObjectId
    -> FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Bool
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveProjectionAgreementDirection
        context
        field
        imports
        selector
        projection
        sourceRecord
        targetRecord
        value
        reverseRecords = do
    targetPresenceTerm <- KernelProof.scopedTerm context
        (Record.selectorPresent selector targetRecord)
    targetPresence <- KernelProof.hypothesisProof context targetPresenceTerm
    bodyUnderBinder <- existentialBodyProofContext context targetPresence
    target <- KernelProof.scopedTerm context
        (membership (orderedPair selector value) targetRecord)
    KernelProof.existentialEliminationProof
        context
        TySet
        bodyUnderBinder
        targetPresence
        target
        (\withWitness _witness witnessMembership -> do
            let shiftedSelector = shiftCanonical 1 0 selector
                shiftedProjection = shiftCanonical 1 0 projection
                shiftedSource = shiftCanonical 1 0 sourceRecord
                shiftedTarget = shiftCanonical 1 0 targetRecord
                shiftedValue = shiftCanonical 1 0 value
                witness = CBound 0
                sourceEntry = orderedPair shiftedSelector shiftedValue
                sourceMembershipTerm = membership sourceEntry shiftedSource
            sourceMembership <- KernelProof.scopedTerm
                withWitness sourceMembershipTerm
                >>= KernelProof.hypothesisProof withWitness
            sourceFunctional <- KernelProof.scopedTerm withWitness
                (Record.recordFunctional shiftedSource)
                >>= KernelProof.hypothesisProof withWitness
            targetFunctional <- KernelProof.scopedTerm withWitness
                (Record.recordFunctional shiftedTarget)
                >>= KernelProof.hypothesisProof withWitness
            sourceProjection <- applyProjectionEntry
                withWitness
                field
                imports
                shiftedSource
                shiftedValue
                sourceFunctional
                sourceMembership
            targetProjection <- applyProjectionEntry
                withWitness
                field
                imports
                shiftedTarget
                witness
                targetFunctional
                witnessMembership
            mainEqualityTerm <- KernelProof.scopedTerm withWitness
                (CEq TySet
                    (CApp shiftedProjection
                        (if reverseRecords then shiftedTarget else shiftedSource))
                    (CApp shiftedProjection
                        (if reverseRecords then shiftedSource else shiftedTarget)))
            storedMainEquality <- KernelProof.hypothesisProof
                withWitness mainEqualityTerm
            sourceToTarget <-
                if reverseRecords
                    then KernelProof.equalityReverseProof
                        withWitness storedMainEquality
                    else pure storedMainEquality
            valueToSource <-
                KernelProof.equalityReverseProof
                    withWitness sourceProjection
            valueToTargetProjection <-
                KernelProof.composeEqualityProof
                    withWitness
                    valueToSource
                    sourceToTarget
            valueToWitness <-
                KernelProof.composeEqualityProof
                    withWitness
                    valueToTargetProjection
                    targetProjection
            witnessToValue <-
                KernelProof.equalityReverseProof
                    withWitness
                    valueToWitness
            selectorTerm <- KernelProof.scopedTerm
                withWitness shiftedSelector
            selectorReflexive <-
                KernelProof.equalityReflexivityProof
                    withWitness selectorTerm
            pairEquality <- orderedPairCongruenceBoth
                withWitness selectorReflexive witnessToValue
            transported <- transportElementMembership
                withWitness
                shiftedTarget
                pairEquality
                witnessMembership
            shiftedResult <- KernelProof.scopedTerm withWitness
                (shiftCanonical 1 0 (scopedCoreTerm target))
            KernelProof.conversionProof
                withWitness
                transported
                shiftedResult)

applyProjectionEntry
    :: KernelProof.ProofContext ObjectId
    -> FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
applyProjectionEntry
        context
        field
        imports
        record
        value
        functional
        member = do
    entryImport <-
        indexedGeneratedImport (RecordProjectionEntryLaw field) imports
    imported <- importedProofAt context entryImport
    entryLaw <- KernelProof.specializeForalls context imported [record, value]
    afterFunctional <-
        applyImplicationConverted context entryLaw functional
    applyImplicationConverted context afterFunctional member

buildReductMembershipProof
    :: KernelProof.ProofContext ObjectId
    -> [CanonicalTerm ObjectId]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductMembershipProof root selectors =
    KernelProof.forallIntroductionProof root TySet
        (\withRecord _record ->
            KernelProof.forallIntroductionProof withRecord TySet
                (\context _entry -> do
                    record <- KernelProof.scopedTerm context (CBound 1)
                    entry <- KernelProof.scopedTerm context (CBound 0)
                    predicate <- KernelProof.scopedTerm context
                        (CLam TySet
                            (selectorDisjunction
                                (shiftCanonical 1 0 <$> selectors)
                                (CBound 0)))
                    left <- KernelProof.scopedTerm context
                        (membership
                            (CBound 0)
                            (Record.recordReduct selectors (CBound 1)))
                    right <- KernelProof.scopedTerm context
                        (CAnd
                            (membership (CBound 0) (CBound 1))
                            (selectorDisjunction selectors (CBound 0)))
                    forward <-
                        KernelProof.implicationIntroductionProof
                            context
                            left
                            (\withLeft leftProof -> do
                                characteristic <-
                                    KernelProof.foundationInstanceProof
                                        withLeft
                                        SeparationCharacteristic
                                        [record, predicate, entry]
                                expanded <-
                                    KernelProof.equalityModusPonensProof
                                        withLeft
                                        characteristic
                                        leftProof
                                KernelProof.conversionProof
                                    withLeft
                                    expanded
                                    right)
                    backward <-
                        KernelProof.implicationIntroductionProof
                            context
                            right
                            (\withRight rightProof -> do
                                characteristic <-
                                    KernelProof.foundationInstanceProof
                                        withRight
                                        SeparationCharacteristic
                                        [record, predicate, entry]
                                reversed <-
                                    KernelProof.equalityReverseProof
                                        withRight
                                        characteristic
                                expanded <-
                                    KernelProof.scopedTerm withRight
                                        (CAnd
                                            (membership (CBound 0) (CBound 1))
                                            (CApp
                                                (scopedCoreTerm predicate)
                                                (CBound 0)))
                                expandedProof <-
                                    KernelProof.conversionProof
                                        withRight
                                        rightProof
                                        expanded
                                KernelProof.equalityModusPonensProof
                                    withRight
                                    reversed
                                    expandedProof)
                    KernelProof.conjunctionIntroductionProof
                        context
                        forward
                        backward))

buildExactGraphProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildExactGraphProof root schema =
    KernelProof.forallIntroductionProof root TySet
        (\withLeft _left ->
            KernelProof.forallIntroductionProof withLeft TySet
                (\context _right -> do
                    let left = CBound 1
                        right = CBound 0
                        selectors = schemaSelectors schema
                        leftExact = Record.recordExactShape selectors left
                        rightExact = Record.recordExactShape selectors right
                        agreements =
                            entryAgreementConjunction selectors left right
                    KernelProof.introduceImplications
                        context
                        [leftExact, rightExact, agreements]
                        (\withPremises -> do
                            leftToRight <- buildMembershipSubset
                                withPremises left right
                                (proveExactGraphMembership
                                    schema left right False)
                            rightToLeft <- buildMembershipSubset
                                withPremises right left
                                (proveExactGraphMembership
                                    schema right left True)
                            leftTerm <- KernelProof.scopedTerm
                                withPremises left
                            rightTerm <- KernelProof.scopedTerm
                                withPremises right
                            extensionality <-
                                KernelProof.foundationInstanceProof
                                    withPremises
                                    SetExtensionality
                                    [leftTerm, rightTerm]
                            afterForward <- applyImplicationConverted
                                withPremises extensionality leftToRight
                            applyImplicationConverted
                                withPremises afterForward rightToLeft)))

proveExactGraphMembership
    :: PreparedRecordSchema
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Bool
    -> KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveExactGraphMembership
        schema
        source
        targetRecord
        reverseDirection
        context
        entry
        sourceMembership = do
    let selectors = shiftCanonical 1 0 <$> schemaSelectors schema
        shiftedSource = shiftCanonical 1 0 source
        shiftedTarget = shiftCanonical 1 0 targetRecord
    exactTerm <- KernelProof.scopedTerm context
        (Record.recordExactShape selectors shiftedSource)
    exactProof <- KernelProof.hypothesisProof context exactTerm
    closure <- deriveConjunct
        context [exactProof] (Record.selectorClosed selectors shiftedSource)
    entryTerm <- KernelProof.scopedTerm context entry
    closureAtEntry <-
        KernelProof.forallEliminationProof context closure entryTerm
    selectorCases <- applyImplicationConverted
        context closureAtEntry sourceMembership
    target <- KernelProof.scopedTerm context
        (membership entry shiftedTarget)
    KernelProof.eliminateLeftAssociatedDisjunction
        context
        [ CEq TySet (firstCoordinate entry) selector
        | selector <- selectors
        ]
        selectorCases
        target
        (proveExactGraphSelectorBranch
            schema
            shiftedSource
            shiftedTarget
            entry
            reverseDirection)

proveExactGraphSelectorBranch
    :: PreparedRecordSchema
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Bool
    -> KernelProof.ProofContext ObjectId
    -> Natural
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveExactGraphSelectorBranch
        schema
        source
        targetRecord
        entry
        reverseDirection
        context
        branchIndex
        selectorEquality = do
    field <-
        maybe
            (Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "exact-graph selector branch is outside the schema"))
            Right
            (nth
                branchIndex
                (preparedRecordSchemaFields schema))
    let selector = CGlobal (preparedRecordFieldSelector field)
        sourceMemberTerm = membership entry source
        exactSourceTerm =
            Record.recordExactShape (schemaSelectors schema) source
        left = if reverseDirection then targetRecord else source
        right = if reverseDirection then source else targetRecord
        agreementsTerm =
            entryAgreementConjunction (schemaSelectors schema) left right
        value = secondCoordinate entry
    sourceMember <- KernelProof.scopedTerm context sourceMemberTerm
        >>= KernelProof.hypothesisProof context
    exactSource <- KernelProof.scopedTerm context exactSourceTerm
        >>= KernelProof.hypothesisProof context
    pairCoded <- deriveConjunct
        context [exactSource] (Record.recordPairCoded source)
    entryTerm <- KernelProof.scopedTerm context entry
    pairCodedAtEntry <-
        KernelProof.forallEliminationProof context pairCoded entryTerm
    entryToCoordinates <-
        applyImplicationConverted context pairCodedAtEntry sourceMember
    coordinatesToLiteral <-
        orderedPairCongruence context selectorEquality value
    entryToLiteral <-
        KernelProof.composeEqualityProof
            context entryToCoordinates coordinatesToLiteral
    literalMembership <-
        transportElementMembership
            context source entryToLiteral sourceMember
    agreements <- KernelProof.scopedTerm context agreementsTerm
        >>= KernelProof.hypothesisProof context
    fieldAgreement <- deriveConjunct
        context
        [agreements]
        (fieldEntryAgreement selector left right)
    valueTerm <- KernelProof.scopedTerm context value
    agreementAtValue <-
        KernelProof.forallEliminationProof
            context fieldAgreement valueTerm
    direction <-
        if reverseDirection
            then KernelProof.conjunctionRightProof
                context
                agreementAtValue
            else KernelProof.conjunctionLeftProof
                context
                agreementAtValue
    targetLiteralMembership <-
        applyImplicationConverted context direction literalMembership
    literalToEntry <-
        KernelProof.equalityReverseProof context entryToLiteral
    transported <- transportElementMembership
        context targetRecord literalToEntry targetLiteralMembership
    expected <- KernelProof.scopedTerm context
        (membership entry targetRecord)
    KernelProof.conversionProof context transported expected

entryAgreementConjunction
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
entryAgreementConjunction selectors left right =
    leftAssociatedConjunction
        [ fieldEntryAgreement selector left right
        | selector <- selectors
        ]

fieldEntryAgreement
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
fieldEntryAgreement selector left right =
    CForall TySet
        (CAnd
            (CImp
                (membership
                    (orderedPair
                        (shiftCanonical 1 0 selector)
                        (CBound 0))
                    (shiftCanonical 1 0 left))
                (membership
                    (orderedPair
                        (shiftCanonical 1 0 selector)
                        (CBound 0))
                    (shiftCanonical 1 0 right)))
            (CImp
                (membership
                    (orderedPair
                        (shiftCanonical 1 0 selector)
                        (CBound 0))
                    (shiftCanonical 1 0 right))
                (membership
                    (orderedPair
                        (shiftCanonical 1 0 selector)
                        (CBound 0))
                    (shiftCanonical 1 0 left))))

buildReductExactProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductExactProof root schema imports =
    KernelProof.forallIntroductionProof root TySet
        (\context _record -> do
            let record = CBound 0
                selectors = schemaSelectors schema
                reduct = Record.recordReduct selectors record
                open = Record.recordOpenShape selectors record
            openPremise <- KernelProof.scopedTerm context open
            KernelProof.implicationIntroductionProof
                context
                openPremise
                (\withOpen _openProof -> do
                    pairCoded <- buildReductPairCoded
                        withOpen imports selectors record reduct
                    rightUnique <- buildReductRightUnique
                        withOpen imports selectors record reduct
                    functional <- KernelProof.conjunctionIntroductionProof
                        withOpen pairCoded rightUnique
                    fieldPresences <- traverse
                        (\(index, selector) ->
                            buildReductSelectorPresence
                                withOpen
                                imports
                                selectors
                                record
                                reduct
                                index
                                selector)
                        (zip [0..] selectors)
                    reductOpen <-
                        KernelProof.buildLeftAssociatedConjunction
                            withOpen
                            (functional : fieldPresences)
                    closure <- buildReductSelectorClosure
                        withOpen imports selectors record reduct
                    KernelProof.conjunctionIntroductionProof
                        withOpen reductOpen closure))

buildReductPairCoded
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductPairCoded context imports selectors record reduct =
    KernelProof.forallIntroductionProof context TySet
        (\withEntry _entry -> do
            let shiftedSelectors = shiftCanonical 1 0 <$> selectors
                shiftedRecord = shiftCanonical 1 0 record
                shiftedReduct = shiftCanonical 1 0 reduct
                entry = CBound 0
                premiseTerm = membership entry shiftedReduct
            premise <- KernelProof.scopedTerm withEntry premiseTerm
            KernelProof.implicationIntroductionProof
                withEntry
                premise
                (\withMembership reductMember -> do
                    originalMember <- reductMemberInOriginal
                        withMembership
                        imports
                        shiftedSelectors
                        shiftedRecord
                        entry
                        reductMember
                    openTerm <- KernelProof.scopedTerm withMembership
                        (Record.recordOpenShape shiftedSelectors shiftedRecord)
                    openProof <- KernelProof.hypothesisProof
                        withMembership openTerm
                    originalPairCoded <- deriveConjunct
                        withMembership [openProof]
                        (Record.recordPairCoded shiftedRecord)
                    entryTerm <- KernelProof.scopedTerm
                        withMembership entry
                    pairCodedAtEntry <- KernelProof.forallEliminationProof
                        withMembership originalPairCoded entryTerm
                    applyImplicationConverted
                        withMembership pairCodedAtEntry originalMember))

buildReductRightUnique
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductRightUnique context imports selectors record reduct =
    KernelProof.forallIntroductionProof context TySet
        (\withFirst _first ->
            KernelProof.forallIntroductionProof withFirst TySet
                (\withSecond _second -> do
                    let shiftedSelectors = shiftCanonical 2 0 <$> selectors
                        shiftedRecord = shiftCanonical 2 0 record
                        shiftedReduct = shiftCanonical 2 0 reduct
                        firstEntry = CBound 1
                        secondEntry = CBound 0
                        premises =
                            [ membership firstEntry shiftedReduct
                            , membership secondEntry shiftedReduct
                            , CEq TySet
                                (firstCoordinate firstEntry)
                                (firstCoordinate secondEntry)
                            ]
                    premise <- KernelProof.scopedTerm withSecond
                        (leftAssociatedConjunction premises)
                    KernelProof.implicationIntroductionProof
                        withSecond
                        premise
                        (\withPremise premiseProof -> do
                            projected <-
                                KernelProof.projectLeftAssociatedConjuncts
                                    withPremise premises premiseProof
                            (firstMember, secondMember, coordinatesEqual) <-
                                case projected of
                                    [one, two, equality] ->
                                        Right (one, two, equality)
                                    _ ->
                                        Left
                                            (KernelProof.ProofStructuralCompositionMismatch
                                                "reduct uniqueness has three premises")
                            originalFirst <- reductMemberInOriginal
                                withPremise
                                imports
                                shiftedSelectors
                                shiftedRecord
                                firstEntry
                                firstMember
                            originalSecond <- reductMemberInOriginal
                                withPremise
                                imports
                                shiftedSelectors
                                shiftedRecord
                                secondEntry
                                secondMember
                            openTerm <- KernelProof.scopedTerm withPremise
                                (Record.recordOpenShape
                                    shiftedSelectors shiftedRecord)
                            openProof <- KernelProof.hypothesisProof
                                withPremise openTerm
                            originalUnique <- deriveConjunct
                                withPremise [openProof]
                                (Record.recordRightUnique shiftedRecord)
                            specialized <- KernelProof.specializeForalls
                                withPremise
                                originalUnique
                                [firstEntry, secondEntry]
                            originalPremise <-
                                KernelProof.buildLeftAssociatedConjunction
                                    withPremise
                                    [ originalFirst
                                    , originalSecond
                                    , coordinatesEqual
                                    ]
                            applyImplicationConverted
                                withPremise specialized originalPremise)))

reductMemberInOriginal
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
reductMemberInOriginal
        context imports selectors record entry reductMember = do
    characteristic <- reductMembershipInstance context imports record entry
    (forward, _backward) <- reductMembershipDirections
        context selectors record entry characteristic
    expanded <- applyImplicationConverted context forward reductMember
    KernelProof.conjunctionLeftProof
        context
        expanded

buildReductSelectorPresence
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Natural
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductSelectorPresence
        context imports selectors record reduct index selector = do
    openTerm <- KernelProof.scopedTerm context
        (Record.recordOpenShape selectors record)
    openProof <- KernelProof.hypothesisProof context openTerm
    originalPresence <- deriveConjunct
        context [openProof] (Record.selectorPresent selector record)
    bodyUnderBinder <- existentialBodyProofContext context originalPresence
    target <- KernelProof.scopedTerm context
        (Record.selectorPresent selector reduct)
    KernelProof.existentialEliminationProof
        context
        TySet
        bodyUnderBinder
        originalPresence
        target
        (\withWitness witness originalMember -> do
            let shiftedSelectors = shiftCanonical 1 0 <$> selectors
                shiftedRecord = shiftCanonical 1 0 record
                shiftedReduct = shiftCanonical 1 0 reduct
                shiftedSelector = shiftCanonical 1 0 selector
                witnessTerm = CBound 0
                entry = orderedPair shiftedSelector witnessTerm
            firstProjection <- orderedPairProjectionProof
                withWitness OrderedPairFirst shiftedSelector witnessTerm
            selectorCase <- KernelProof.introduceLeftAssociatedDisjunct
                withWitness
                index
                [ CEq TySet (firstCoordinate entry) schemaSelector
                | schemaSelector <- shiftedSelectors
                ]
                firstProjection
            expanded <- KernelProof.conjunctionIntroductionProof
                withWitness originalMember selectorCase
            characteristic <- reductMembershipInstance
                withWitness imports shiftedRecord entry
            (_forward, backward) <- reductMembershipDirections
                withWitness
                shiftedSelectors
                shiftedRecord
                entry
                characteristic
            reductMember <- applyImplicationConverted
                withWitness backward expanded
            (underNewWitness, _newVariable) <-
                KernelProof.extendProofContextBinder withWitness TySet
            targetBody <- KernelProof.scopedTerm underNewWitness
                (membership
                    (orderedPair
                        (shiftCanonical 1 0 shiftedSelector)
                        (CBound 0))
                    (shiftCanonical 1 0 shiftedReduct))
            presence <- KernelProof.existentialIntroductionProof
                withWitness TySet targetBody witness reductMember
            shiftedTarget <- KernelProof.scopedTerm withWitness
                (shiftCanonical 1 0 (scopedCoreTerm target))
            KernelProof.conversionProof
                withWitness presence shiftedTarget)

buildReductSelectorClosure
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductSelectorClosure context imports selectors record reduct =
    KernelProof.forallIntroductionProof context TySet
        (\withEntry _entry -> do
            let shiftedSelectors = shiftCanonical 1 0 <$> selectors
                shiftedRecord = shiftCanonical 1 0 record
                shiftedReduct = shiftCanonical 1 0 reduct
                entry = CBound 0
            premise <- KernelProof.scopedTerm withEntry
                (membership entry shiftedReduct)
            KernelProof.implicationIntroductionProof
                withEntry
                premise
                (\withMembership reductMember -> do
                    characteristic <- reductMembershipInstance
                        withMembership imports shiftedRecord entry
                    (forward, _backward) <- reductMembershipDirections
                        withMembership
                        shiftedSelectors
                        shiftedRecord
                        entry
                        characteristic
                    expanded <- applyImplicationConverted
                        withMembership forward reductMember
                    KernelProof.conjunctionRightProof
                        withMembership
                        expanded))

buildReductIdentityProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductIdentityProof root schema imports =
    KernelProof.forallIntroductionProof root TySet
        (\context _record -> do
            let record = CBound 0
                selectors = schemaSelectors schema
                reduct = Record.recordReduct selectors record
                exact = Record.recordExactShape selectors record
            exactPremise <- KernelProof.scopedTerm context exact
            KernelProof.implicationIntroductionProof
                context
                exactPremise
                (\withExact _exactProof -> do
                    reductToRecord <-
                        buildMembershipSubset withExact reduct record
                            (\memberContext entry member -> do
                                let shiftedSelectors =
                                        shiftCanonical 1 0 <$> selectors
                                    shiftedRecord = shiftCanonical 1 0 record
                                characteristic <- reductMembershipInstance
                                    memberContext imports shiftedRecord entry
                                (forward, _backward) <-
                                    reductMembershipDirections
                                        memberContext
                                        shiftedSelectors
                                        shiftedRecord
                                        entry
                                        characteristic
                                expanded <- applyImplicationConverted
                                    memberContext forward member
                                KernelProof.conjunctionLeftProof
                                    memberContext
                                    expanded)
                    recordToReduct <-
                        buildMembershipSubset withExact record reduct
                            (\memberContext entry member -> do
                                let shiftedSelectors =
                                        shiftCanonical 1 0 <$> selectors
                                    shiftedRecord = shiftCanonical 1 0 record
                                    selectorCases =
                                        leftAssociatedDisjunction
                                            [ CEq TySet
                                                (firstCoordinate entry)
                                                selector
                                            | selector <- shiftedSelectors
                                            ]
                                exactTerm <- KernelProof.scopedTerm
                                    memberContext
                                    (Record.recordExactShape
                                        shiftedSelectors
                                        shiftedRecord)
                                exactProof <- KernelProof.hypothesisProof
                                    memberContext exactTerm
                                closure <- deriveConjunct
                                    memberContext
                                    [exactProof]
                                    (Record.selectorClosed
                                        shiftedSelectors shiftedRecord)
                                entryTerm <- KernelProof.scopedTerm
                                    memberContext entry
                                closureAtEntry <-
                                    KernelProof.forallEliminationProof
                                        memberContext closure entryTerm
                                cases <- applyImplicationConverted
                                    memberContext closureAtEntry member
                                casesTarget <- KernelProof.scopedTerm
                                    memberContext selectorCases
                                checkedCases <- KernelProof.conversionProof
                                    memberContext cases casesTarget
                                conjunction <-
                                    KernelProof.conjunctionIntroductionProof
                                        memberContext member checkedCases
                                characteristic <- reductMembershipInstance
                                    memberContext imports shiftedRecord entry
                                (_forward, backward) <-
                                    reductMembershipDirections
                                        memberContext
                                        shiftedSelectors
                                        shiftedRecord
                                        entry
                                        characteristic
                                applyImplicationConverted
                                    memberContext backward conjunction)
                    reductTerm <- KernelProof.scopedTerm withExact reduct
                    recordTerm <- KernelProof.scopedTerm withExact record
                    extensionality <- KernelProof.foundationInstanceProof
                        withExact SetExtensionality [reductTerm, recordTerm]
                    afterForward <- applyImplicationConverted
                        withExact extensionality reductToRecord
                    applyImplicationConverted
                        withExact afterForward recordToReduct))

buildReductProjectionProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildReductProjectionProof root schema field imports = do
    preparedField <- kernelSchemaField schema field
    let selector = CGlobal (preparedRecordFieldSelector preparedField)
        projection = CGlobal (preparedRecordFieldProjection preparedField)
        selectors = schemaSelectors schema
    index <- fieldPosition schema field
    KernelProof.forallIntroductionProof root TySet
        (\context _record -> do
            let record = CBound 0
                reduct = Record.recordReduct selectors record
                reductProjection = CApp projection reduct
                originalProjection = CApp projection record
            reductToOriginal <-
                buildMembershipSubset context reductProjection originalProjection
                    (transformProjectionMembership
                        schema field imports selector projection index True)
            originalToReduct <-
                buildMembershipSubset context originalProjection reductProjection
                    (transformProjectionMembership
                        schema field imports selector projection index False)
            reductProjectionTerm <- KernelProof.scopedTerm
                context reductProjection
            originalProjectionTerm <- KernelProof.scopedTerm
                context originalProjection
            extensionality <- KernelProof.foundationInstanceProof
                context
                SetExtensionality
                [reductProjectionTerm, originalProjectionTerm]
            afterForward <- applyImplicationConverted
                context extensionality reductToOriginal
            applyImplicationConverted
                context afterForward originalToReduct)

transformProjectionMembership
    :: PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Natural
    -> Bool
    -> KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
transformProjectionMembership
        schema
        field
        imports
        selector
        projection
        selectedIndex
        sourceIsReduct
        context
        element
        sourceMembership = do
    let selectors = shiftCanonical 1 0 <$> schemaSelectors schema
        record = CBound 1
        reduct = Record.recordReduct selectors record
        sourceRecord = if sourceIsReduct then reduct else record
        targetRecord = if sourceIsReduct then record else reduct
        sourceProjection = CApp projection sourceRecord
    membershipLaw <- specializedProjectionMembership
        context field imports sourceRecord element
    expectedSource <- KernelProof.scopedTerm context
        (membership element sourceProjection)
    checkedSource <- KernelProof.conversionProof
        context sourceMembership expectedSource
    existential <- KernelProof.equalityModusPonensProof
        context membershipLaw checkedSource
    bodyUnderBinder <- existentialBodyProofContext context existential
    target <- KernelProof.scopedTerm context
        (membership element (CApp projection targetRecord))
    KernelProof.existentialEliminationProof
        context
        TySet
        bodyUnderBinder
        existential
        target
        (\withWitness witness bodyProof -> do
            let shiftedSelectors = shiftCanonical 1 0 <$> selectors
                shiftedRecord = shiftCanonical 1 0 record
                shiftedReduct = Record.recordReduct
                    shiftedSelectors shiftedRecord
                shiftedElement = shiftCanonical 1 0 element
                targetWitnessRecord =
                    if sourceIsReduct then shiftedRecord else shiftedReduct
                witnessTerm = CBound 0
            witnessMembership <- KernelProof.conjunctionLeftProof
                withWitness bodyProof
            conditions <- KernelProof.conjunctionRightProof
                withWitness bodyProof
            firstEqualsSelector <- KernelProof.conjunctionLeftProof
                withWitness
                conditions
            elementInSecond <- KernelProof.conjunctionRightProof
                withWitness
                conditions
            reductCharacteristic <- reductMembershipInstance
                withWitness imports shiftedRecord witnessTerm
            (reductForward, reductBackward) <-
                reductMembershipDirections
                    withWitness
                    shiftedSelectors
                    shiftedRecord
                    witnessTerm
                    reductCharacteristic
            targetWitnessMembership <-
                if sourceIsReduct then do
                    expanded <- applyImplicationConverted
                        withWitness reductForward witnessMembership
                    KernelProof.conjunctionLeftProof
                        withWitness
                        expanded
                else do
                    selectorCase <-
                        KernelProof.introduceLeftAssociatedDisjunct
                            withWitness
                            selectedIndex
                            [ CEq TySet
                                (firstCoordinate witnessTerm)
                                schemaSelector
                            | schemaSelector <- shiftedSelectors
                            ]
                            firstEqualsSelector
                    expanded <- KernelProof.conjunctionIntroductionProof
                        withWitness witnessMembership selectorCase
                    applyImplicationConverted
                        withWitness reductBackward expanded
            transformedBody <- KernelProof.conjunctionIntroductionProof
                withWitness
                targetWitnessMembership
                =<< KernelProof.conjunctionIntroductionProof
                    withWitness
                    firstEqualsSelector
                    elementInSecond
            (underNewWitness, _newVariable) <-
                KernelProof.extendProofContextBinder withWitness TySet
            targetBody <- KernelProof.scopedTerm underNewWitness
                (CAnd
                    (membership
                        (CBound 0)
                        (shiftCanonical 1 0 targetWitnessRecord))
                    (CAnd
                        (CEq TySet
                            (firstCoordinate (CBound 0))
                            selector)
                        (membership
                            (shiftCanonical 1 0 shiftedElement)
                            (secondCoordinate (CBound 0)))))
            transformedExistential <-
                KernelProof.existentialIntroductionProof
                    withWitness
                    TySet
                    targetBody
                    witness
                    transformedBody
            targetMembershipLaw <- specializedProjectionMembership
                withWitness
                field
                imports
                targetWitnessRecord
                shiftedElement
            reversed <- KernelProof.equalityReverseProof
                withWitness targetMembershipLaw
            projected <- KernelProof.equalityModusPonensProof
                withWitness reversed transformedExistential
            shiftedTarget <- KernelProof.scopedTerm withWitness
                (shiftCanonical 1 0 (scopedCoreTerm target))
            KernelProof.conversionProof
                withWitness projected shiftedTarget)

reductMembershipInstance
    :: KernelProof.ProofContext ObjectId
    -> [IndexedRecordImport]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
reductMembershipInstance context imports record entry = do
    checkedImport <- indexedGeneratedImport RecordReductMembershipLaw imports
    imported <- importedProofAt context checkedImport
    KernelProof.specializeForalls context imported [record, entry]

reductMembershipDirections
    :: KernelProof.ProofContext ObjectId
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        ( KernelProof.BuiltProof ObjectId
        , KernelProof.BuiltProof ObjectId
        )
reductMembershipDirections context selectors record entry characteristic = do
    let reductMember =
            membership entry (Record.recordReduct selectors record)
        expanded =
            CAnd
                (membership entry record)
                (leftAssociatedDisjunction
                    [ CEq TySet (firstCoordinate entry) selector
                    | selector <- selectors
                    ])
    unless (scopedCoreTerm (KernelProof.builtProofStatement characteristic)
            == CAnd (CImp reductMember expanded) (CImp expanded reductMember))
        (Left (KernelProof.ProofStructuralCompositionMismatch
            "reduct characteristic describes different operands"))
    forward <- KernelProof.conjunctionLeftProof
        context
        characteristic
    backward <- KernelProof.conjunctionRightProof
        context
        characteristic
    pure (forward, backward)

buildSelectorPairDistinctProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> FieldId
    -> [KernelProof.BuiltProof ObjectId]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildSelectorPairDistinctProof context schema left right imported = do
    (leftDefinition, rightDefinition) <-
        case imported of
            [leftProof, rightProof] -> Right (leftProof, rightProof)
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "selector-pair proof requires two definition imports")
    leftField <- kernelSchemaField schema left
    rightField <- kernelSchemaField schema right
    let leftSelector = preparedRecordFieldSelector leftField
        rightSelector = preparedRecordFieldSelector rightField
        leftBody = Record.fieldSelectorBody left
        rightBody = Record.fieldSelectorBody right
    selectorEquality <-
        KernelProof.scopedTerm context
            (CEq TySet
                (CGlobal leftSelector)
                (CGlobal rightSelector))
    KernelProof.negationIntroductionProof
        context
        selectorEquality
        (\withEquality equality -> do
            leftReversed <-
                KernelProof.equalityReverseProof
                    withEquality
                    leftDefinition
            leftToRightSelector <-
                KernelProof.composeEqualityProof
                    withEquality
                    leftReversed
                    equality
            bodyEquality <-
                KernelProof.composeEqualityProof
                    withEquality
                    leftToRightSelector
                    rightDefinition
            contradictSelectorBodies
                withEquality
                leftBody
                rightBody
                bodyEquality)

kernelSchemaField
    :: PreparedRecordSchema
    -> FieldId
    -> Either
        KernelProof.KernelProofBuildError
        PreparedRecordField
kernelSchemaField schema identity =
    maybe
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "selector-pair field is absent from the checked schema"))
        Right
        (List.find
            ((== identity) . preparedRecordFieldId)
            (preparedRecordSchemaFields schema))

contradictSelectorBodies
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
contradictSelectorBodies context left right equality =
    case (orderedPairChildren left, orderedPairChildren right) of
        (Just (leftFirst, leftSecond), Just (rightFirst, rightSecond)) -> do
            arguments <-
                traverse
                    (KernelProof.scopedTerm context)
                    [leftFirst, leftSecond, rightFirst, rightSecond]
            injective <-
                KernelProof.foundationInstanceProof
                    context
                    OrderedPairInjective
                    arguments
            components <-
                KernelProof.equalityModusPonensProof
                    context
                    injective
                    equality
            if leftFirst /= rightFirst then do
                firstEquality <-
                    KernelProof.conjunctionLeftProof
                        context
                        components
                contradictSelectorBodies
                    context
                    leftFirst
                    rightFirst
                    firstEquality
            else do
                secondEquality <-
                    KernelProof.conjunctionRightProof
                        context
                        components
                contradictSelectorBodies
                    context
                    leftSecond
                    rightSecond
                    secondEquality
        (Nothing, Nothing) ->
            contradictSelectorBits context left right equality
        _ ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "selector bodies have different tree shapes")

contradictSelectorBits
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
contradictSelectorBits context left right equality = do
    singletonToEmpty <-
        case (isEmptyBit left, isEmptyBit right) of
            (False, True)
                | isSingletonEmptyBit left -> pure equality
            (True, False)
                | isSingletonEmptyBit right ->
                    KernelProof.equalityReverseProof context equality
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "distinct selector leaves are not canonical bit codes")
    emptySet <- KernelProof.scopedTerm context (CIntrinsic Empty)
    reflexive <- KernelProof.equalityReflexivityProof context emptySet
    equalityTerm <- KernelProof.scopedTerm context
        (CEq TySet (CIntrinsic Empty) (CIntrinsic Empty))
    eitherOccurrence <-
        KernelProof.disjunctionLeftProof
            context
            (scopedCoreTerm equalityTerm)
            reflexive
    pairCharacteristic <-
        KernelProof.foundationInstanceProof
            context
            PairSetCharacteristic
            [emptySet, emptySet, emptySet]
    pairCharacteristicReversed <-
        KernelProof.equalityReverseProof context pairCharacteristic
    singletonMembership <-
        KernelProof.equalityModusPonensProof
            context
            pairCharacteristicReversed
            eitherOccurrence
    emptyMembership <-
        KernelProof.transportMembershipProof
            context
            emptySet
            singletonToEmpty
            singletonMembership
    emptyCharacteristic <-
        KernelProof.foundationInstanceProof
            context
            EmptyCharacteristic
            [emptySet]
    KernelProof.equalityModusPonensProof
        context
        emptyCharacteristic
        emptyMembership
orderedPairChildren
    :: CanonicalTerm global
    -> Maybe (CanonicalTerm global, CanonicalTerm global)
orderedPairChildren = \case
    CApp (CApp (CIntrinsic OrderedPair) left) right ->
        Just (left, right)
    _ -> Nothing

isEmptyBit :: CanonicalTerm global -> Bool
isEmptyBit = \case
    CIntrinsic Empty -> True
    _ -> False

isSingletonEmptyBit :: CanonicalTerm global -> Bool
isSingletonEmptyBit = \case
    CApp
        (CApp (CIntrinsic PairSet) (CIntrinsic Empty))
        (CIntrinsic Empty) -> True
    _ -> False

buildAggregateEntryProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateEntryProof root schema selectedField =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\context -> do
            let aggregateContext =
                    Record.recordSchemaAggregateContext selectors
            entries <-
                exactAssociationKernel
                    (Record.recordAggregateContextSelectors aggregateContext)
                    (Record.recordAggregateContextValues aggregateContext)
            index <- fieldPosition schema selectedField
            selected <-
                maybe
                    (Left
                        (KernelProof.ProofStructuralCompositionMismatch
                            "aggregate-entry field index is out of bounds"))
                    Right
                    (nth index entries)
            introduceAggregateMembership
                context
                selected
                entries
                index)
  where
    selectors = schemaSelectors schema

buildAggregatePairCodedProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregatePairCodedProof root schema =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\valuesContext ->
            KernelProof.forallIntroductionProof valuesContext TySet
                (\context _entry -> do
                    let aggregateContext =
                            Record.recordSchemaAggregateContext selectors
                        aggregate =
                            shiftCanonical 1 0
                                (Record.recordAggregateContextTerm aggregateContext)
                    baseEntries <-
                        exactAssociationKernel
                            (Record.recordAggregateContextSelectors
                                aggregateContext)
                            (Record.recordAggregateContextValues
                                aggregateContext)
                    let entries =
                            mapEntryTerms (shiftCanonical 1 0) baseEntries
                        entry = CBound 0
                        premiseTerm = membership entry aggregate
                        targetTerm =
                            CEq TySet
                                entry
                                (orderedPair
                                    (firstCoordinate entry)
                                    (secondCoordinate entry))
                    premise <- KernelProof.scopedTerm context premiseTerm
                    target <- KernelProof.scopedTerm context targetTerm
                    KernelProof.implicationIntroductionProof
                        context
                        premise
                        (\withMembership membershipProof -> do
                            eliminateAggregateMembership
                                withMembership
                                entry
                                entries
                                membershipProof
                                target
                                provePairCodedBranch)))
  where
    selectors = schemaSelectors schema

provePairCodedBranch
    :: KernelProof.ProofContext ObjectId
    -> Natural
    -> (CanonicalTerm ObjectId, CanonicalTerm ObjectId)
    -> KernelProof.BuiltProof ObjectId
    -> ScopedCheckedCore ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
provePairCodedBranch
        context
        _branchIndex
        (selector, value)
        entryToPair
        target = do
    (_entry, branchPair) <-
        equalityOperands "aggregate pair-coding branch" entryToPair
    firstEquality <- coordinateCongruence context FirstProjection entryToPair
    secondEquality <- coordinateCongruence context SecondProjection entryToPair
    firstProjection <- orderedPairProjectionProof
        context OrderedPairFirst selector value
    secondProjection <- orderedPairProjectionProof
        context OrderedPairSecond selector value
    entryFirstToSelector <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "pair-coding first projection composition failed"))
            (KernelProof.composeEqualityProof
                context
                firstEquality
                firstProjection)
    entrySecondToValue <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "pair-coding second projection composition failed"))
            (KernelProof.composeEqualityProof
                context
                secondEquality
                secondProjection)
    selectorToEntryFirst <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "pair-coding first projection reversal failed"))
            (KernelProof.equalityReverseProof context entryFirstToSelector)
    valueToEntrySecond <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "pair-coding second projection reversal failed"))
            (KernelProof.equalityReverseProof context entrySecondToValue)
    pairToCoordinates <-
        orderedPairCongruenceBoth
            context
            selectorToEntryFirst
            valueToEntrySecond
    unless (branchPair == orderedPair selector value)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "aggregate branch equality names a different pair"))
    composed <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "pair-coding final equality composition failed"))
            (KernelProof.composeEqualityProof
                context entryToPair pairToCoordinates)
    unless (KernelProof.builtProofStatement composed == target)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "aggregate pair-coding branch has the wrong target"))
    pure composed

buildAggregateSelectorClosedProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateSelectorClosedProof root schema =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\valuesContext ->
            KernelProof.forallIntroductionProof valuesContext TySet
                (\context _entry -> do
                    let aggregateContext =
                            Record.recordSchemaAggregateContext selectors
                        aggregate =
                            shiftCanonical 1 0
                                (Record.recordAggregateContextTerm aggregateContext)
                    baseEntries <-
                        exactAssociationKernel
                            (Record.recordAggregateContextSelectors aggregateContext)
                            (Record.recordAggregateContextValues aggregateContext)
                    let entries =
                            mapEntryTerms (shiftCanonical 1 0) baseEntries
                        entry = CBound 0
                        premiseTerm = membership entry aggregate
                        alternatives =
                            [ CEq TySet
                                (firstCoordinate entry)
                                selector
                            | selector <- selectors
                            ]
                    premise <- KernelProof.scopedTerm context premiseTerm
                    target <- KernelProof.scopedTerm context
                        (leftAssociatedDisjunction alternatives)
                    KernelProof.implicationIntroductionProof
                        context
                        premise
                        (\withMembership membershipProof ->
                            eliminateAggregateMembership
                                withMembership
                                entry
                                entries
                                membershipProof
                                target
                                (proveSelectorClosedBranch selectors))))
  where
    selectors = schemaSelectors schema

proveSelectorClosedBranch
    :: [CanonicalTerm ObjectId]
    -> KernelProof.ProofContext ObjectId
    -> Natural
    -> (CanonicalTerm ObjectId, CanonicalTerm ObjectId)
    -> KernelProof.BuiltProof ObjectId
    -> ScopedCheckedCore ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveSelectorClosedBranch
        selectors
        context
        branchIndex
        (branchSelector, value)
        entryToPair
        target = do
    (entry, _branchPair) <-
        equalityOperands "selector-closure branch" entryToPair
    let branchAlternatives =
            [ CEq TySet (firstCoordinate entry) schemaSelector
            | schemaSelector <- selectors
            ]
    firstEquality <- coordinateCongruence context FirstProjection entryToPair
    firstProjection <- orderedPairProjectionProof
        context OrderedPairFirst branchSelector value
    entryFirstToSelector <-
        first
            (const
                (KernelProof.ProofStructuralCompositionMismatch
                    "selector-closure projection composition failed"))
            (KernelProof.composeEqualityProof
                context
                firstEquality
                firstProjection)
    introduced <-
        KernelProof.introduceLeftAssociatedDisjunct
            context
            branchIndex
            branchAlternatives
            entryFirstToSelector
    unless (KernelProof.builtProofStatement introduced == target)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "selector-closure branch has the wrong target"))
    pure introduced

coordinateCongruence
    :: KernelProof.ProofContext ObjectId
    -> CoreIntrinsicTag
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
coordinateCongruence context coordinate equality = do
    function <- KernelProof.scopedTerm context (CIntrinsic coordinate)
    reflexive <- KernelProof.equalityReflexivityProof context function
    KernelProof.equalityCongruenceApplicationProof
        context
        reflexive
        equality

orderedPairCongruenceBoth
    :: KernelProof.ProofContext ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
orderedPairCongruenceBoth context firstEquality secondEquality = do
    constructor <- KernelProof.scopedTerm context (CIntrinsic OrderedPair)
    constructorReflexive <-
        KernelProof.equalityReflexivityProof context constructor
    firstApplied <-
        KernelProof.equalityCongruenceApplicationProof
            context
            constructorReflexive
            firstEquality
    KernelProof.equalityCongruenceApplicationProof
        context
        firstApplied
        secondEquality

equalityOperands
    :: Text
    -> KernelProof.BuiltProof global
    -> Either
        KernelProof.KernelProofBuildError
        (CanonicalTerm global, CanonicalTerm global)
equalityOperands label proof =
    case scopedCoreTerm (KernelProof.builtProofStatement proof) of
        CEq TySet left right -> Right (left, right)
        _ ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    (label <> " is not a set equality"))

buildAggregateProjectionApplicationProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateProjectionApplicationProof root schema field imports =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\context -> do
            let aggregateContext =
                    Record.recordSchemaAggregateContext selectors
                values = Record.recordAggregateContextValues aggregateContext
                aggregate = Record.recordAggregateContextTerm aggregateContext
            index <- fieldPosition schema field
            value <-
                maybe
                    (Left
                        (KernelProof.ProofStructuralCompositionMismatch
                            "aggregate projection field index is out of bounds"))
                    Right
                    (nth index values)
            projectionEntryImport <-
                indexedGeneratedImport
                    (RecordProjectionEntryLaw field)
                    imports
            imported <- importedProofAt context projectionEntryImport
            KernelProof.specializeForalls
                context imported [aggregate, value])
  where
    selectors = schemaSelectors schema

buildAggregateExactProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateExactProof root schema imports =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\context -> do
            let aggregateContext =
                    Record.recordSchemaAggregateContext selectors
                shiftedSelectors =
                    Record.recordAggregateContextSelectors aggregateContext
                values = Record.recordAggregateContextValues aggregateContext
                aggregate = Record.recordAggregateContextTerm aggregateContext
            functionalImport <-
                indexedGeneratedImport RecordAggregateFunctionalLaw imports
            functional <-
                specializeImportedForValues context values functionalImport
            selectorValues <-
                exactAssociationKernel shiftedSelectors values
            fieldsAndValues <-
                exactAssociationKernel
                    (preparedRecordSchemaFields schema)
                    selectorValues
            presenceProofs <- traverse
                (\(preparedField, (selector, value)) -> do
                    entryImport <-
                        indexedGeneratedImport
                            (RecordAggregateEntryLaw
                                (preparedRecordFieldId preparedField))
                            imports
                    entry <-
                        specializeImportedForValues context values entryImport
                    introduceSelectorPresence
                        context selector value aggregate entry)
                fieldsAndValues
            openShape <-
                KernelProof.buildLeftAssociatedConjunction
                    context
                    (functional : presenceProofs)
            closureImport <-
                indexedGeneratedImport
                    RecordAggregateSelectorClosedLaw
                    imports
            closure <-
                specializeImportedForValues context values closureImport
            KernelProof.conjunctionIntroductionProof
                context
                openShape
                closure)
  where
    selectors = schemaSelectors schema

introduceSelectorPresence
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
introduceSelectorPresence context selector value record entry = do
    (underBinder, _witnessVariable) <-
        KernelProof.extendProofContextBinder context TySet
    body <- KernelProof.scopedTerm underBinder
        (membership
            (orderedPair
                (shiftCanonical 1 0 selector)
                (CBound 0))
            (shiftCanonical 1 0 record))
    witness <- KernelProof.scopedTerm context value
    KernelProof.existentialIntroductionProof
        context
        TySet
        body
        witness
        entry

buildAggregateProjectionProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateProjectionProof root schema field imports =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\context -> do
            let aggregateContext =
                    Record.recordSchemaAggregateContext selectors
                values = Record.recordAggregateContextValues aggregateContext
            functionalImport <-
                indexedGeneratedImport RecordAggregateFunctionalLaw imports
            functional <-
                specializeImportedForValues context values functionalImport
            entryImport <-
                indexedGeneratedImport
                    (RecordAggregateEntryLaw field)
                    imports
            entry <-
                specializeImportedForValues context values entryImport
            applicationImport <-
                indexedGeneratedImport
                    (RecordAggregateProjectionApplicationLaw field)
                    imports
            application <-
                specializeImportedForValues context values applicationImport
            afterFunctional <-
                applyImplicationConverted context application functional
            applyImplicationConverted context afterFunctional entry)
  where
    selectors = schemaSelectors schema

buildAggregateValueUniqueProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateValueUniqueProof root schema selectedField imports =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\valuesContext ->
            KernelProof.forallIntroductionProof valuesContext TySet
                (\context _candidateValue -> do
                    let aggregateContext =
                            Record.recordSchemaAggregateContext selectors
                    baseEntries <-
                        exactAssociationKernel
                            (Record.recordAggregateContextSelectors
                                aggregateContext)
                            (Record.recordAggregateContextValues
                                aggregateContext)
                    let entries =
                            mapEntryTerms (shiftCanonical 1 0) baseEntries
                    index <- fieldPosition schema selectedField
                    (selectedSelector, selectedValue) <-
                        maybe
                            (Left
                                (KernelProof.ProofStructuralCompositionMismatch
                                    "aggregate uniqueness field index is out of bounds"))
                            Right
                            (nth index entries)
                    let candidateValue = CBound 0
                        selectedPair =
                            orderedPair selectedSelector candidateValue
                        aggregate = Record.recordAggregate entries
                    premise <- KernelProof.scopedTerm context
                        (membership selectedPair aggregate)
                    target <- KernelProof.scopedTerm context
                        (CEq TySet candidateValue selectedValue)
                    KernelProof.implicationIntroductionProof
                        context
                        premise
                        (\withMembership membershipProof ->
                            eliminateAggregateMembership
                                withMembership
                                selectedPair
                                entries
                                membershipProof
                                target
                                (proveValueUniqueBranch
                                    schema
                                    selectedField
                                    imports))))
  where
    selectors = schemaSelectors schema

proveValueUniqueBranch
    :: PreparedRecordSchema
    -> FieldId
    -> [IndexedRecordImport]
    -> KernelProof.ProofContext ObjectId
    -> Natural
    -> (CanonicalTerm ObjectId, CanonicalTerm ObjectId)
    -> KernelProof.BuiltProof ObjectId
    -> ScopedCheckedCore ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveValueUniqueBranch
        schema
        selectedField
        imports
        context
        branchIndex
        (branchSelector, branchValue)
        pairEquality
        target = do
    (selectedSelector, candidateValue) <-
        case scopedCoreTerm (KernelProof.builtProofStatement pairEquality) of
            CEq TySet selectedPair _branchPair ->
                maybe
                    (Left
                        (KernelProof.ProofStructuralCompositionMismatch
                            "aggregate branch source is not an ordered pair"))
                    Right
                    (orderedPairChildren selectedPair)
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "aggregate branch did not produce a set equality")
    arguments <-
        traverse
            (KernelProof.scopedTerm context)
            [ selectedSelector
            , candidateValue
            , branchSelector
            , branchValue
            ]
    injective <-
        KernelProof.foundationInstanceProof
            context
            OrderedPairInjective
            arguments
    components <-
        KernelProof.equalityModusPonensProof
            context
            injective
            pairEquality
    branchField <-
        maybe
            (Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "aggregate branch index is outside the schema"))
            (Right . preparedRecordFieldId)
            (nth
                branchIndex
                (preparedRecordSchemaFields schema))
    if branchField == selectedField then do
        valueEquality <-
            KernelProof.conjunctionRightProof
                context
                components
        KernelProof.conversionProof context valueEquality target
    else do
        selectorEquality <-
            KernelProof.conjunctionLeftProof
                context
                components
        (pairLaw, distinctImport) <-
            importedSelectorPair
                selectedField
                branchField
                imports
        orientedEquality <-
            case pairLaw of
                RecordSelectorPairDistinctLaw left right
                    | left == selectedField && right == branchField ->
                        pure selectorEquality
                    | left == branchField && right == selectedField ->
                        KernelProof.equalityReverseProof
                            context
                            selectorEquality
                    | otherwise ->
                        Left
                            (KernelProof.ProofStructuralCompositionMismatch
                                "selector-pair import names different fields")
                _ ->
                    Left
                        (KernelProof.ProofStructuralCompositionMismatch
                            "aggregate uniqueness imported a non-pair law")
        distinctProof <- importedProofAt context distinctImport
        contradiction <-
            KernelProof.negationEliminationProof
                context
                orientedEquality
                distinctProof
        KernelProof.falsumEliminationProof
            context
            contradiction
            target

importedSelectorPair
    :: FieldId
    -> FieldId
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (RecordSchemaLaw, IndexedRecordImport)
importedSelectorPair selected branch imports =
    case
        [ (law, checkedImport)
        | checkedImport@(IndexedRecordImport dependency _index _proposition) <-
            imports
        , RecordGeneratedDependency law <- [dependency]
        , RecordSelectorPairDistinctLaw left right <-
            [law]
        , (left == selected && right == branch)
            || (left == branch && right == selected)
        ] of
        [result] -> Right result
        _ ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "aggregate uniqueness lacks its selector-pair import")

eliminateAggregateMembership
    :: Eq global
    => KernelProof.ProofContext global
    -> CanonicalTerm global
    -> [(CanonicalTerm global, CanonicalTerm global)]
    -> KernelProof.BuiltProof global
    -> ScopedCheckedCore global
    -> ( KernelProof.ProofContext global
         -> Natural
         -> (CanonicalTerm global, CanonicalTerm global)
         -> KernelProof.BuiltProof global
         -> ScopedCheckedCore global
         -> Either
            KernelProof.KernelProofBuildError
            (KernelProof.BuiltProof global)
       )
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
eliminateAggregateMembership
        initialContext
        element
        entries
        membershipProof
        target
        handle =
    go initialContext 0 element entries membershipProof target
  where
    go context offset currentElement currentEntries currentMembership currentTarget =
        case currentEntries of
            [] -> do
                elementTerm <- KernelProof.scopedTerm context currentElement
                characteristic <-
                    KernelProof.foundationInstanceProof
                        context
                        EmptyCharacteristic
                        [elementTerm]
                contradiction <-
                    KernelProof.equalityModusPonensProof
                        context
                        characteristic
                        currentMembership
                KernelProof.falsumEliminationProof
                    context
                    contradiction
                    currentTarget
            current : remaining -> do
                let currentTerm = uncurry orderedPair current
                    tailTerm = Record.recordAggregate remaining
                    singleton = pairSet currentTerm currentTerm
                    family = pairSet singleton tailTerm
                familySet <- KernelProof.scopedTerm context family
                elementTerm <- KernelProof.scopedTerm context currentElement
                characteristic <-
                    KernelProof.foundationInstanceProof
                        context
                        FamilyUnionCharacteristic
                        [familySet, elementTerm]
                existential <-
                    KernelProof.equalityModusPonensProof
                        context
                        characteristic
                        currentMembership
                (underBinder, _witness) <-
                    KernelProof.extendProofContextBinder context TySet
                bodyUnderBinder <-
                    KernelProof.scopedTerm underBinder
                        (CAnd
                            (membership
                                (CBound 0)
                                (shiftCanonical 1 0 family))
                            (membership
                                (shiftCanonical 1 0 currentElement)
                                (CBound 0)))
                KernelProof.existentialEliminationProof
                    context
                    TySet
                    bodyUnderBinder
                    existential
                    currentTarget
                    (\withBody witness bodyProof -> do
                        let shiftedElement =
                                shiftCanonical 1 0 currentElement
                            shiftedCurrent =
                                ( shiftCanonical 1 0 (fst current)
                                , shiftCanonical 1 0 (snd current)
                                )
                            shiftedRemaining =
                                mapEntryTerms (shiftCanonical 1 0) remaining
                            shiftedSingleton =
                                shiftCanonical 1 0 singleton
                            shiftedTail = shiftCanonical 1 0 tailTerm
                        shiftedTarget <-
                            KernelProof.scopedTerm withBody
                                (shiftCanonical 1 0
                                    (scopedCoreTerm currentTarget))
                        witnessInFamily <-
                            KernelProof.conjunctionLeftProof
                                withBody
                                bodyProof
                        elementInWitness <-
                            KernelProof.conjunctionRightProof
                                withBody
                                bodyProof
                        singletonTerm <-
                            KernelProof.scopedTerm withBody shiftedSingleton
                        tailSet <-
                            KernelProof.scopedTerm withBody shiftedTail
                        outerCharacteristic <-
                            KernelProof.foundationInstanceProof
                                withBody
                                PairSetCharacteristic
                                [singletonTerm, tailSet, witness]
                        witnessCases <-
                            KernelProof.equalityModusPonensProof
                                withBody
                                outerCharacteristic
                                witnessInFamily
                        KernelProof.eliminateLeftAssociatedDisjunction
                            withBody
                            [ CEq TySet (CBound 0) shiftedSingleton
                            , CEq TySet (CBound 0) shiftedTail
                            ]
                            witnessCases
                            shiftedTarget
                            (\branchContext branch witnessEquality ->
                                case branch of
                                    0 -> do
                                        let branchElementInWitness =
                                                KernelProof.weakenProofHypotheses
                                                    1
                                                    elementInWitness
                                        shiftedElementTerm <-
                                            KernelProof.scopedTerm
                                                branchContext
                                                shiftedElement
                                        inSingleton <-
                                            KernelProof.transportMembershipProof
                                                branchContext
                                                shiftedElementTerm
                                                witnessEquality
                                                branchElementInWitness
                                        currentEntry <-
                                            KernelProof.scopedTerm
                                                branchContext
                                                (uncurry orderedPair shiftedCurrent)
                                        singletonCharacteristic <-
                                            KernelProof.foundationInstanceProof
                                                branchContext
                                                PairSetCharacteristic
                                                [ currentEntry
                                                , currentEntry
                                                , shiftedElementTerm
                                                ]
                                        elementCases <-
                                            KernelProof.equalityModusPonensProof
                                                branchContext
                                                singletonCharacteristic
                                                inSingleton
                                        let equalityTerm =
                                                CEq TySet
                                                    shiftedElement
                                                    (uncurry orderedPair
                                                        shiftedCurrent)
                                        KernelProof.eliminateLeftAssociatedDisjunction
                                            branchContext
                                            [equalityTerm, equalityTerm]
                                            elementCases
                                            shiftedTarget
                                            (\equalityContext _duplicate equalityProof ->
                                                handle
                                                    equalityContext
                                                    offset
                                                    shiftedCurrent
                                                    equalityProof
                                                    shiftedTarget)
                                    1 -> do
                                        let branchElementInWitness =
                                                KernelProof.weakenProofHypotheses
                                                    1
                                                    elementInWitness
                                        shiftedElementTerm <-
                                            KernelProof.scopedTerm
                                                branchContext
                                                shiftedElement
                                        tailMembership <-
                                            KernelProof.transportMembershipProof
                                                branchContext
                                                shiftedElementTerm
                                                witnessEquality
                                                branchElementInWitness
                                        go
                                            branchContext
                                            (offset + 1)
                                            shiftedElement
                                            shiftedRemaining
                                            tailMembership
                                            shiftedTarget
                                    _ ->
                                        Left
                                            (KernelProof.ProofStructuralCompositionMismatch
                                                "binary pair-set elimination produced another branch")))

mapEntryTerms
    :: (CanonicalTerm global -> CanonicalTerm global')
    -> [(CanonicalTerm global, CanonicalTerm global)]
    -> [(CanonicalTerm global', CanonicalTerm global')]
mapEntryTerms transform =
    fmap (\(selector, value) -> (transform selector, transform value))

buildAggregateFunctionalProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateFunctionalProof root schema imports =
    KernelProof.introduceForalls root (replicate (length selectors) TySet)
        (\valuesContext -> do
            let aggregateContext =
                    Record.recordSchemaAggregateContext selectors
                values = Record.recordAggregateContextValues aggregateContext
                aggregate = Record.recordAggregateContextTerm aggregateContext
            pairCodedImport <-
                indexedGeneratedImport RecordAggregatePairCodedLaw imports
            pairCoded <-
                specializeImportedForValues
                    valuesContext
                    values
                    pairCodedImport
            rightUnique <-
                buildAggregateRightUniqueProof
                    valuesContext
                    schema
                    imports
                    values
                    aggregate
            KernelProof.conjunctionIntroductionProof
                valuesContext
                pairCoded
                rightUnique)
  where
    selectors = schemaSelectors schema

buildAggregateRightUniqueProof
    :: KernelProof.ProofContext ObjectId
    -> PreparedRecordSchema
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
buildAggregateRightUniqueProof
        valuesContext
        schema
        imports
        values
        aggregate =
    KernelProof.forallIntroductionProof valuesContext TySet
        (\withFirst _firstEntry ->
            KernelProof.forallIntroductionProof withFirst TySet
                (\context _secondEntry -> do
                    let firstEntry = CBound 1
                        secondEntry = CBound 0
                        shiftedAggregate = shiftCanonical 2 0 aggregate
                        membershipOne = membership firstEntry shiftedAggregate
                        membershipTwo = membership secondEntry shiftedAggregate
                        firstEquality =
                            CEq TySet
                                (firstCoordinate firstEntry)
                                (firstCoordinate secondEntry)
                        premises =
                            [membershipOne, membershipTwo, firstEquality]
                        conclusion =
                            CEq TySet
                                (secondCoordinate firstEntry)
                                (secondCoordinate secondEntry)
                    premise <- KernelProof.scopedTerm context
                        (leftAssociatedConjunction premises)
                    target <- KernelProof.scopedTerm context conclusion
                    KernelProof.implicationIntroductionProof
                        context
                        premise
                        (\withPremise premiseProof -> do
                            projectedPremises <-
                                KernelProof.projectLeftAssociatedConjuncts
                                    withPremise
                                    premises
                                    premiseProof
                            firstMembership <-
                                case projectedPremises of
                                    [firstProof, _secondProof, _equalityProof] ->
                                        Right firstProof
                                    _ ->
                                        Left
                                            (KernelProof.ProofStructuralCompositionMismatch
                                                "right uniqueness has three premises")
                            let shiftedValues = shiftCanonical 2 0 <$> values
                            selectorClosedImport <-
                                indexedGeneratedImport
                                    RecordAggregateSelectorClosedLaw
                                    imports
                            selectorClosed <-
                                specializeImportedForValues
                                    withPremise
                                    shiftedValues
                                    selectorClosedImport
                            selectorCases <-
                                specializeImplication
                                    withPremise
                                    selectorClosed
                                    firstEntry
                                    firstMembership
                            KernelProof.eliminateLeftAssociatedDisjunction
                                withPremise
                                [ CEq TySet
                                    (firstCoordinate firstEntry)
                                    selector
                                | selector <- schemaSelectors schema
                                ]
                                selectorCases
                                target
                                (proveAggregateFunctionalBranch
                                    schema
                                    imports
                                    shiftedValues
                                    shiftedAggregate
                                    firstEntry
                                    secondEntry))))

proveAggregateFunctionalBranch
    :: PreparedRecordSchema
    -> [IndexedRecordImport]
    -> [CanonicalTerm ObjectId]
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.ProofContext ObjectId
    -> Natural
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
proveAggregateFunctionalBranch
        schema
        imports
        values
        aggregate
        firstEntry
        secondEntry
        context
        branchIndex
        firstSelectorEquality = do
    field <-
        maybe
            (Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "aggregate functionality branch is outside the schema"))
            Right
            (nth
                branchIndex
                (preparedRecordSchemaFields schema))
    let selector = CGlobal (preparedRecordFieldSelector field)
        firstValue = secondCoordinate firstEntry
        secondValue = secondCoordinate secondEntry
        membershipOne = membership firstEntry aggregate
        membershipTwo = membership secondEntry aggregate
        firstEquality =
            CEq TySet
                (firstCoordinate firstEntry)
                (firstCoordinate secondEntry)
        premises = [membershipOne, membershipTwo, firstEquality]
    premise <- KernelProof.scopedTerm context
        (leftAssociatedConjunction premises)
    premiseProof <- KernelProof.hypothesisProof context premise
    projectedPremises <-
        KernelProof.projectLeftAssociatedConjuncts
            context
            premises
            premiseProof
    (firstMembership, secondMembership, coordinatesEqual) <-
        case projectedPremises of
            [firstProof, secondProof, equalityProof] ->
                Right (firstProof, secondProof, equalityProof)
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "right uniqueness has three premises in its branch")
    pairCodedImport <-
        indexedGeneratedImport RecordAggregatePairCodedLaw imports
    pairCoded <-
        specializeImportedForValues context values pairCodedImport
    firstPairEquality <-
        specializeImplication
            context
            pairCoded
            firstEntry
            firstMembership
    secondPairEquality <-
        specializeImplication
            context
            pairCoded
            secondEntry
            secondMembership
    secondToFirst <-
        KernelProof.equalityReverseProof context coordinatesEqual
    secondSelectorEquality <-
        KernelProof.composeEqualityProof
            context
            secondToFirst
            firstSelectorEquality
    firstLiteralEquality <-
        literalPairEquality
            context
            firstEntry
            selector
            firstValue
            firstPairEquality
            firstSelectorEquality
    secondLiteralEquality <-
        literalPairEquality
            context
            secondEntry
            selector
            secondValue
            secondPairEquality
            secondSelectorEquality
    firstLiteralMembership <-
        transportElementMembership
            context
            aggregate
            firstLiteralEquality
            firstMembership
    secondLiteralMembership <-
        transportElementMembership
            context
            aggregate
            secondLiteralEquality
            secondMembership
    uniqueImport <-
        indexedGeneratedImport
            (RecordAggregateValueUniqueLaw
                (preparedRecordFieldId field))
            imports
    uniqueLaw <-
        specializeImportedForValues context values uniqueImport
    firstUnique <-
        specializeImplication
            context
            uniqueLaw
            firstValue
            firstLiteralMembership
    secondUnique <-
        specializeImplication
            context
            uniqueLaw
            secondValue
            secondLiteralMembership
    assignedToSecond <-
        KernelProof.equalityReverseProof context secondUnique
    KernelProof.composeEqualityProof
        context
        firstUnique
        assignedToSecond

indexedGeneratedImport
    :: RecordSchemaLaw
    -> [IndexedRecordImport]
    -> Either
        KernelProof.KernelProofBuildError
        IndexedRecordImport
indexedGeneratedImport identity imports =
    case
        [ checkedImport
        | checkedImport@(IndexedRecordImport dependency _index _proposition) <-
            imports
        , RecordGeneratedDependency law <- [dependency]
        , law == identity
        ] of
        [checkedImport] -> Right checkedImport
        _ ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "record proof lacks one exact generated-law import")

specializeImportedForValues
    :: KernelProof.ProofContext ObjectId
    -> [CanonicalTerm ObjectId]
    -> IndexedRecordImport
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
specializeImportedForValues context values checkedImport = do
    imported <- importedProofAt context checkedImport
    foldM
        (\proof value -> do
            argument <- KernelProof.scopedTerm context value
            KernelProof.forallEliminationProof context proof argument)
        imported
        values

specializeImplication
    :: KernelProof.ProofContext ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
specializeImplication context quantified argument premise = do
    checkedArgument <- KernelProof.scopedTerm context argument
    implication <-
        KernelProof.forallEliminationProof
            context
            quantified
            checkedArgument
    expectedPremise <-
        case scopedCoreTerm (KernelProof.builtProofStatement implication) of
            CImp implicationPremise _conclusion ->
                KernelProof.scopedTerm context implicationPremise
            _ ->
                Left
                    (KernelProof.ProofStructuralCompositionMismatch
                        "specialized record law is not an implication")
    convertedPremise <-
        KernelProof.conversionProof context premise expectedPremise
    KernelProof.implicationEliminationProof
        context
        implication
        convertedPremise

literalPairEquality
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
literalPairEquality
        context
        entry
        selector
        value
        pairCodedEquality
        selectorEquality = do
    firstCoordinateEquality <-
        orderedPairCongruence
            context
            selectorEquality
            value
    entryToLiteral <-
        KernelProof.composeEqualityProof
            context
            pairCodedEquality
            firstCoordinateEquality
    expected <- KernelProof.scopedTerm context
        (CEq TySet entry (orderedPair selector value))
    KernelProof.conversionProof context entryToLiteral expected

orderedPairCongruence
    :: KernelProof.ProofContext ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> CanonicalTerm ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
orderedPairCongruence context firstEquality second = do
    constructor <- KernelProof.scopedTerm context (CIntrinsic OrderedPair)
    constructorReflexive <-
        KernelProof.equalityReflexivityProof context constructor
    firstApplied <-
        KernelProof.equalityCongruenceApplicationProof
            context
            constructorReflexive
            firstEquality
    secondTerm <- KernelProof.scopedTerm context second
    secondReflexive <-
        KernelProof.equalityReflexivityProof context secondTerm
    KernelProof.equalityCongruenceApplicationProof
        context
        firstApplied
        secondReflexive

transportElementMembership
    :: KernelProof.ProofContext ObjectId
    -> CanonicalTerm ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> KernelProof.BuiltProof ObjectId
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof ObjectId)
transportElementMembership context set elementEquality member = do
    predicate <- KernelProof.scopedTerm context
        (CLam TySet
            (membership
                (CBound 0)
                (shiftCanonical 1 0 set)))
    KernelProof.equalityTransportProof
        context
        elementEquality
        predicate
        member

firstCoordinate :: CanonicalTerm global -> CanonicalTerm global
firstCoordinate = CApp (CIntrinsic FirstProjection)

secondCoordinate :: CanonicalTerm global -> CanonicalTerm global
secondCoordinate = CApp (CIntrinsic SecondProjection)

leftAssociatedConjunction
    :: [CanonicalTerm global]
    -> CanonicalTerm global
leftAssociatedConjunction = \case
    [] -> CTruth
    initial : remaining -> foldl' CAnd initial remaining

leftAssociatedDisjunction
    :: [CanonicalTerm global]
    -> CanonicalTerm global
leftAssociatedDisjunction = \case
    [] -> CFalsum
    initial : remaining -> foldl' COr initial remaining

fieldPosition
    :: PreparedRecordSchema
    -> FieldId
    -> Either KernelProof.KernelProofBuildError Natural
fieldPosition schema selected =
    go 0 (preparedRecordSchemaFields schema)
  where
    go _index [] =
        Left
            (KernelProof.ProofStructuralCompositionMismatch
                "record-law field is absent from its schema")
    go index (field : remaining)
        | preparedRecordFieldId field == selected = Right index
        | otherwise = go (index + 1) remaining

introduceAggregateMembership
    :: Eq global
    => KernelProof.ProofContext global
    -> (CanonicalTerm global, CanonicalTerm global)
    -> [(CanonicalTerm global, CanonicalTerm global)]
    -> Natural
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
introduceAggregateMembership context selected entries index =
    case (entries, index) of
        ([], _) ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "aggregate membership index is outside the entries")
        (current : remaining, 0) ->
            introduceAtCurrent context selected current remaining
        (_current : remaining, _) -> do
            tailMembership <-
                introduceAggregateMembership
                    context
                    selected
                    remaining
                    (index - 1)
            introduceFromTail
                context
                selected
                entries
                tailMembership

introduceAtCurrent
    :: Eq global
    => KernelProof.ProofContext global
    -> (CanonicalTerm global, CanonicalTerm global)
    -> (CanonicalTerm global, CanonicalTerm global)
    -> [(CanonicalTerm global, CanonicalTerm global)]
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
introduceAtCurrent context selected current remaining = do
    unless (selected == current)
        (Left
            (KernelProof.ProofStructuralCompositionMismatch
                "aggregate membership selected a different entry"))
    let currentTerm = uncurry orderedPair current
        tailTerm = Record.recordAggregate remaining
        singleton = pairSet currentTerm currentTerm
        outer = pairSet singleton tailTerm
    witness <- KernelProof.scopedTerm context singleton
    outerMembership <-
        pairSetMembershipLeft context singleton tailTerm
    innerMembership <-
        pairSetMembershipLeft context currentTerm currentTerm
    introduceFamilyUnionMembership
        context
        outer
        currentTerm
        witness
        outerMembership
        innerMembership

introduceFromTail
    :: Eq global
    => KernelProof.ProofContext global
    -> (CanonicalTerm global, CanonicalTerm global)
    -> [(CanonicalTerm global, CanonicalTerm global)]
    -> KernelProof.BuiltProof global
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
introduceFromTail context selected entries tailMembership =
    case entries of
        [] ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "aggregate tail introduction has no current entry")
        current : remaining -> do
            let currentTerm = uncurry orderedPair current
                tailTerm = Record.recordAggregate remaining
                singleton = pairSet currentTerm currentTerm
                outer = pairSet singleton tailTerm
                selectedTerm = uncurry orderedPair selected
            witness <- KernelProof.scopedTerm context tailTerm
            outerMembership <-
                pairSetMembershipRight context singleton tailTerm
            introduceFamilyUnionMembership
                context
                outer
                selectedTerm
                witness
                outerMembership
                tailMembership

introduceFamilyUnionMembership
    :: Eq global
    => KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> ScopedCheckedCore global
    -> KernelProof.BuiltProof global
    -> KernelProof.BuiltProof global
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
introduceFamilyUnionMembership
        context
        family
        element
        witness
        witnessMembership
        elementMembership = do
    bodyProof <-
        KernelProof.conjunctionIntroductionProof
            context
            witnessMembership
            elementMembership
    (underBinder, _bound) <-
        KernelProof.extendProofContextBinder context TySet
    bodyUnderBinder <-
        KernelProof.scopedTerm underBinder
            (CAnd
                (membership
                    (CBound 0)
                    (shiftCanonical 1 0 family))
                (membership
                    (shiftCanonical 1 0 element)
                    (CBound 0)))
    existential <-
        KernelProof.existentialIntroductionProof
            context
            TySet
            bodyUnderBinder
            witness
            bodyProof
    familySet <- KernelProof.scopedTerm context family
    selected <- KernelProof.scopedTerm context element
    characteristic <-
        KernelProof.foundationInstanceProof
            context
            FamilyUnionCharacteristic
            [familySet, selected]
    reversed <- KernelProof.equalityReverseProof context characteristic
    KernelProof.equalityModusPonensProof context reversed existential

pairSetMembershipLeft
    :: Eq global
    => KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
pairSetMembershipLeft context left right = do
    leftTerm <- KernelProof.scopedTerm context left
    rightTerm <- KernelProof.scopedTerm context right
    reflexive <- KernelProof.equalityReflexivityProof context leftTerm
    rightEquality <- KernelProof.scopedTerm context (CEq TySet left right)
    disjunction <-
        KernelProof.disjunctionLeftProof
            context
            (scopedCoreTerm rightEquality)
            reflexive
    characteristic <-
        KernelProof.foundationInstanceProof
            context
            PairSetCharacteristic
            [leftTerm, rightTerm, leftTerm]
    reversed <- KernelProof.equalityReverseProof context characteristic
    KernelProof.equalityModusPonensProof context reversed disjunction

pairSetMembershipRight
    :: Eq global
    => KernelProof.ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Either
        KernelProof.KernelProofBuildError
        (KernelProof.BuiltProof global)
pairSetMembershipRight context left right = do
    leftTerm <- KernelProof.scopedTerm context left
    rightTerm <- KernelProof.scopedTerm context right
    reflexive <- KernelProof.equalityReflexivityProof context rightTerm
    leftEquality <- KernelProof.scopedTerm context (CEq TySet right left)
    disjunction <-
        KernelProof.disjunctionRightProof
            context
            (scopedCoreTerm leftEquality)
            reflexive
    characteristic <-
        KernelProof.foundationInstanceProof
            context
            PairSetCharacteristic
            [leftTerm, rightTerm, rightTerm]
    reversed <- KernelProof.equalityReverseProof context characteristic
    KernelProof.equalityModusPonensProof context reversed disjunction

orderedPair
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
orderedPair left right =
    CApp (CApp (CIntrinsic OrderedPair) left) right

pairSet
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
pairSet left right =
    CApp (CApp (CIntrinsic PairSet) left) right

exactAssociationKernel
    :: [left]
    -> [right]
    -> Either KernelProof.KernelProofBuildError [(left, right)]
exactAssociationKernel lefts rights =
    case go lefts rights of
        Just associated -> Right associated
        Nothing ->
            Left
                (KernelProof.ProofStructuralCompositionMismatch
                    "checked aggregate context cardinality mismatch")
  where
    go [] [] = Just []
    go (left : leftRest) (right : rightRest) =
        ((left, right) :) <$> go leftRest rightRest
    go _ _ = Nothing

membership
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
membership element set =
    CApp (CApp (CIntrinsic Member) element) set

selectorDisjunction
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
selectorDisjunction selectors entry =
    case
        [ CEq TySet
            (CApp (CIntrinsic FirstProjection) entry)
            selector
        | selector <- selectors
        ] of
        [] -> CFalsum
        initial : remaining -> foldl' COr initial remaining

validatePreparedFields
    :: TheoryId
    -> [PreparedRecordField]
    -> Either RecordProofError ()
validatePreparedFields theory fields = do
    case firstDuplicate (preparedRecordFieldId <$> fields) of
        Just identity -> Left (DuplicateRecordField identity)
        Nothing -> pure ()
    case firstDuplicate resources of
        Just object -> Left (DuplicateRecordResource object)
        Nothing -> pure ()
    traverse_ validateCanonical fields
  where
    resources = concatMap
        (\field ->
            [ preparedRecordFieldSelector field
            , preparedRecordFieldProjection field
            ])
        fields

    validateCanonical field = do
        let identity = preparedRecordFieldId field
            expectedSelector = Record.fieldSelectorObjectId theory identity
            suppliedSelector = preparedRecordFieldSelector field
            expectedProjection = Record.fieldProjectionObjectId theory identity
            suppliedProjection = preparedRecordFieldProjection field
        unless (suppliedSelector == expectedSelector)
            (Left
                (NoncanonicalRecordSelector
                    identity expectedSelector suppliedSelector))
        unless (suppliedProjection == expectedProjection)
            (Left
                (NoncanonicalRecordProjection
                    identity expectedProjection suppliedProjection))

buildRecordLawCatalogue
    :: GlobalTyping ObjectId
    -> [PreparedRecordField]
    -> Either RecordProofError RecordLawCatalogue
buildRecordLawCatalogue globalTyping fields = do
    projectionAgreements <- fieldSpecs
        "projection-agreement laws"
        RecordProjectionAgreementLaw
        (Record.recordSchemaProjectionAgreementLaw <$> fieldTerms)
    reductProjections <- fieldSpecs
        "reduct projections"
        RecordReductProjectionLaw
        (Record.recordSchemaReductProjectionLaws fieldTerms)
    selectorPairs <- pairSpecs
        "selector-pair laws"
        RecordSelectorPairDistinctLaw
        (Record.recordSelectorDistinctLaws selectors)
    projectionEntries <- fieldSpecsWith
        (\field ->
            Record.recordProjectionEntryLaw
                (CGlobal (preparedRecordFieldSelector field))
                (CGlobal (preparedRecordFieldProjection field)))
        RecordProjectionEntryLaw
    aggregateValueUnique <- fieldSpecs
        "aggregate value-uniqueness laws"
        RecordAggregateValueUniqueLaw
        (Record.recordSchemaAggregateValueUniqueLaws selectors)
    aggregateEntries <- fieldSpecs
        "aggregate entry laws"
        RecordAggregateEntryLaw
        (Record.recordSchemaAggregateEntryLaws selectors)
    aggregateProjectionApplications <- fieldSpecs
        "aggregate projection-application laws"
        RecordAggregateProjectionApplicationLaw
        (Record.recordSchemaAggregateProjectionApplicationLaws fieldTerms)
    aggregateProjections <- fieldSpecs
        "aggregate projection laws"
        RecordAggregateProjectionLaw
        (Record.recordSchemaAggregateProjectionLaws fieldTerms)
    checked <- traverse checkTarget
        ( [ (RecordExactGraphLaw,
                Record.recordSchemaExactGraphLaw selectors)
          , (RecordReductExactLaw,
                Record.recordSchemaReductExactLaw selectors)
          , (RecordReductMembershipLaw,
                Record.recordSchemaReductMembershipLaw selectors)
          ]
            <> projectionAgreements
            <> [ (RecordProjectionEntryAgreementLaw,
                    Record.recordSchemaProjectionEntryAgreementLaw fieldTerms)
               , (RecordProjectionGraphAgreementLaw,
                    Record.recordSchemaProjectionGraphAgreementLaw fieldTerms)
               , (RecordProjectionExtensionalityLaw,
                    Record.recordSchemaProjectionExtensionalityLaw fieldTerms)
               , (RecordReductIdentityLaw,
                    Record.recordSchemaReductIdentityLaw selectors)
               ]
            <> reductProjections
            <> selectorPairs
            <> [ (RecordSelectorDistinctLaw,
                    Record.recordSelectorDistinctLaw selectors)
               ]
            <> projectionEntries
            <> [ (RecordAggregatePairCodedLaw,
                    Record.recordSchemaAggregatePairCodedLaw selectors)
               ]
            <> aggregateValueUnique
            <> aggregateEntries
            <> [ (RecordAggregateSelectorClosedLaw,
                    Record.recordSchemaAggregateSelectorClosedLaw selectors)
               ]
            <> aggregateProjectionApplications
            <> [ (RecordAggregateFunctionalLaw,
                    Record.recordSchemaAggregateFunctionalLaw selectors)
               , (RecordAggregateExactLaw,
                    Record.recordSchemaAggregateExactLaw selectors)
               ]
            <> aggregateProjections
        )
    let order = fst <$> checked
        entries =
            Map.fromList
                [ ( law
                  , RecordLawEntry
                        target
                        (recordLawDependenciesFor fields order law)
                  )
                | (law, target) <- checked
                ]
        catalogue = RecordLawCatalogue order entries
    validateRecordLawCatalogue fields catalogue
    pure catalogue
  where
    selectors = CGlobal . preparedRecordFieldSelector <$> fields
    fieldTerms =
        [ ( CGlobal (preparedRecordFieldSelector field)
          , CGlobal (preparedRecordFieldProjection field)
          )
        | field <- fields
        ]
    checkTarget (law, term) = do
        target <- first (RecordLawTargetCoreInvalid law)
            (checkCanonicalCore globalTyping term)
        unless (frozenCoreType target == TyProp)
            (Left
                (RecordLawTargetNotProposition
                    law
                    (frozenCoreType target)))
        pure (law, target)

    fieldSpecs label constructor terms = do
        associated <- associateExact label fields terms
        pure
            [ (constructor (preparedRecordFieldId field), target)
            | (field, target) <- associated
            ]

    fieldSpecsWith target constructor =
        pure
            [ (constructor (preparedRecordFieldId field), target field)
            | field <- fields
            ]

    pairSpecs label constructor terms = do
        associated <- associateExact label (orderedFieldPairs fields) terms
        pure
            [ ( constructor
                    (preparedRecordFieldId left)
                    (preparedRecordFieldId right)
              , target
              )
            | ((left, right), target) <- associated
            ]

recordLawDependenciesFor
    :: [PreparedRecordField]
    -> [RecordSchemaLaw]
    -> RecordSchemaLaw
    -> [RecordLawDependency]
recordLawDependenciesFor fields inventory = \case
    RecordExactGraphLaw -> []
    RecordReductMembershipLaw -> []
    RecordReductExactLaw ->
        generated RecordReductMembershipLaw
    RecordProjectionEntryLaw field ->
        [RecordProjectionMembership field]
    RecordProjectionAgreementLaw field ->
        generated (RecordProjectionEntryLaw field)
    RecordProjectionEntryAgreementLaw ->
        generatedEach RecordProjectionAgreementLaw
    RecordProjectionGraphAgreementLaw ->
        generated RecordExactGraphLaw
            <> generated RecordProjectionEntryAgreementLaw
    RecordProjectionExtensionalityLaw ->
        generated RecordExactGraphLaw
            <> generated RecordProjectionEntryAgreementLaw
    RecordReductIdentityLaw ->
        generated RecordReductMembershipLaw
    RecordReductProjectionLaw field ->
        generated RecordReductMembershipLaw
            <> [RecordProjectionMembership field]
    RecordSelectorPairDistinctLaw left right ->
        [ RecordSelectorDefinition left
        , RecordSelectorDefinition right
        ]
    RecordSelectorDistinctLaw ->
        RecordGeneratedDependency <$> lawsMatching isSelectorPair
    RecordAggregatePairCodedLaw -> []
    RecordAggregateValueUniqueLaw field ->
        RecordGeneratedDependency
            <$> lawsMatching (isSelectorPairInvolving field)
    RecordAggregateEntryLaw _field -> []
    RecordAggregateSelectorClosedLaw -> []
    RecordAggregateProjectionApplicationLaw field ->
        generated (RecordProjectionEntryLaw field)
    RecordAggregateFunctionalLaw ->
        generated RecordAggregatePairCodedLaw
            <> generatedEach RecordAggregateValueUniqueLaw
            <> generated RecordAggregateSelectorClosedLaw
    RecordAggregateExactLaw ->
        generated RecordAggregateFunctionalLaw
            <> generatedEach RecordAggregateEntryLaw
            <> generated RecordAggregateSelectorClosedLaw
    RecordAggregateProjectionLaw field ->
        generated RecordAggregateFunctionalLaw
            <> generated (RecordAggregateEntryLaw field)
            <> generated (RecordAggregateProjectionApplicationLaw field)
  where
    fieldIds =
        preparedRecordFieldId <$> fields

    generated law = [RecordGeneratedDependency law]
    generatedEach constructor =
        concatMap (generated . constructor) fieldIds

    lawsMatching predicate = List.filter predicate inventory

    isSelectorPair = \case
        RecordSelectorPairDistinctLaw{} -> True
        _ -> False

    isSelectorPairInvolving field = \case
        RecordSelectorPairDistinctLaw left right ->
            field == left || field == right
        _ -> False

validateRecordLawCatalogue
    :: [PreparedRecordField]
    -> RecordLawCatalogue
    -> Either RecordProofError ()
validateRecordLawCatalogue fields (RecordLawCatalogue order entries) = do
    unless (Map.size entries == length order)
        (impossible "record-law catalogue contains duplicate identities")
    unless (all (`Map.member` entries) order)
        (impossible "record-law catalogue order contains an absent identity")
    unless (all dependenciesAreAvailable (Map.elems entries))
        (impossible "record-law catalogue contains an absent generated dependency")
    unless (all dependenciesAreDistinct (Map.elems entries))
        (impossible "record-law catalogue contains duplicate dependencies")
    unless (all validSelectorPair order)
        (impossible "record-law catalogue contains a noncanonical selector pair")
  where
    fieldOrder =
        Map.fromList
            [ (preparedRecordFieldId field, index)
            | (index, field) <- zip [0 :: Int ..] fields
            ]

    dependenciesAreAvailable entry =
        all
            (\case
                RecordGeneratedDependency law -> Map.member law entries
                _ -> True)
            (recordLawEntryDependencies entry)

    dependenciesAreDistinct entry =
        let dependencies = recordLawEntryDependencies entry
        in Set.size (Set.fromList dependencies) == length dependencies

    validSelectorPair = \case
        RecordSelectorPairDistinctLaw left right ->
            case (Map.lookup left fieldOrder, Map.lookup right fieldOrder) of
                (Just leftIndex, Just rightIndex) -> leftIndex < rightIndex
                _ -> False
        _ -> True

associateExact
    :: Text
    -> [left]
    -> [right]
    -> Either RecordProofError [(left, right)]
associateExact label lefts rights =
    case go lefts rights of
        Just associated -> Right associated
        Nothing ->
            Left
                (RecordLawCardinalityMismatch
                    label
                    (length lefts)
                    (length rights))
  where
    go [] [] = Just []
    go (left : leftRest) (right : rightRest) =
        ((left, right) :) <$> go leftRest rightRest
    go _ _ = Nothing

orderedFieldPairs :: [field] -> [(field, field)]
orderedFieldPairs = \case
    [] -> []
    initial : rest ->
        ((\second -> (initial, second)) <$> rest) <> orderedFieldPairs rest
