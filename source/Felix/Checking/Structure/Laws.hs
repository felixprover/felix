{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Complete mathematical catalogues and exact-premise kernel derivations.
module Felix.Checking.Structure.Laws
    ( GeneratedDependency(..)
    , GeneratedLawSpec
    , generatedLawId
    , generatedLawTarget
    , generatedLawProposition
    , generatedLawDependencies
    , structureLawFamily
    , structureLawFoundationTags
    , structureLawPresentation
    , CheckedStructureCatalogue
    , checkStructureCatalogue
    , structureCatalogueRegistration
    , structureCatalogueLaws
    , structureCatalogueResources
    , structureDependencyTarget
    , CheckedGeneratedImport(..)
    , buildStructureLawProof
    , inheritanceViewVariables
    , StructureLawError(..)
    , StructureViewError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Authority (StructureLawFamily(..))
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Record qualified as Record
import Felix.Checking.Record.Proof qualified as RecordProof
import Felix.Checking.Semantic (ViewVariableIx(..), FactSearchEligibility(..), SemanticName, semanticName)
import Felix.Syntax.Abstract (Marker(..), StructSymbol(..))
import Data.List qualified as List
import Felix.Checking.Structure.Predicate
import Felix.Checking.Structure.Schema
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector

-- Environment dependencies cover both earlier prospective declarations and
-- admitted imports. Neither this vocabulary nor a catalogue grants authority.
data GeneratedDependency
    = BatchDependency !StructureId !StructureFactKey
    | EnvironmentDependency !StructureId !StructureFactKey
    deriving stock (Show, Eq, Ord)

-- Empty finite records have shorter derivations. The expected footprint is
-- determined by the checked schema and law, never by a caller's permission set.
structureLawFoundationTags
    :: ResolvedStructureSchema -> GeneratedStructureLawKey -> Set FoundationAxiomTag
structureLawFoundationTags schema law
    | Map.null (resolvedSchemaFields schema) = case law of
        RecordSchemaLaw Record.RecordReductExactLaw -> Set.empty
        RecordSchemaLaw Record.RecordAggregatePairCodedLaw -> Set.singleton EmptyCharacteristic
        RecordSchemaLaw Record.RecordAggregateSelectorClosedLaw -> Set.singleton EmptyCharacteristic
        _ -> nonemptyStructureLawFoundationTags (structureLawFamily law)
    | otherwise = nonemptyStructureLawFoundationTags (structureLawFamily law)

nonemptyStructureLawFoundationTags
    :: StructureLawFamily
    -> Set FoundationAxiomTag
nonemptyStructureLawFoundationTags = Set.fromList . \case
    StructurePredicateComponent -> []
    StructureExactGraph -> [SetExtensionality]
    StructureReductMembership -> [SeparationCharacteristic]
    StructureReductExact -> [OrderedPairFirst]
    StructureProjectionEntry ->
        [SetExtensionality, OrderedPairFirst, OrderedPairSecond]
    StructureProjectionAgreement -> []
    StructureProjectionEntryAgreement -> []
    StructureProjectionGraphAgreement -> []
    StructureProjectionExtensionality -> []
    StructureReductIdentity -> [SetExtensionality]
    StructureReductProjection -> [SetExtensionality]
    StructureSelectorPairDistinct ->
        [EmptyCharacteristic, PairSetCharacteristic, OrderedPairInjective]
    StructureSelectorDistinct -> []
    StructureAggregatePairCoded ->
        [ EmptyCharacteristic
        , PairSetCharacteristic
        , FamilyUnionCharacteristic
        , OrderedPairFirst
        , OrderedPairSecond
        ]
    StructureAggregateValueUnique ->
        [ EmptyCharacteristic
        , PairSetCharacteristic
        , FamilyUnionCharacteristic
        , OrderedPairInjective
        ]
    StructureAggregateEntry ->
        [PairSetCharacteristic, FamilyUnionCharacteristic]
    StructureAggregateSelectorClosed ->
        [ EmptyCharacteristic
        , PairSetCharacteristic
        , FamilyUnionCharacteristic
        , OrderedPairFirst
        ]
    StructureAggregateProjectionApplication -> []
    StructureAggregateFunctional -> []
    StructureAggregateExact -> []
    StructureAggregateProjection -> []

data GeneratedLawSpec = GeneratedLawSpec
    !StructureLawId !CheckedPropositionContent ![GeneratedDependency]
    deriving stock (Show, Eq)

generatedLawId :: GeneratedLawSpec -> StructureLawId
generatedLawId (GeneratedLawSpec identity _ _) = identity

generatedLawTarget :: GeneratedLawSpec -> FrozenCheckedCore ObjectId
generatedLawTarget = checkedPropositionTerm . generatedLawProposition

generatedLawProposition :: GeneratedLawSpec -> CheckedPropositionContent
generatedLawProposition (GeneratedLawSpec _ proposition _) = proposition

generatedLawDependencies :: GeneratedLawSpec -> [GeneratedDependency]
generatedLawDependencies (GeneratedLawSpec _ _ dependencies) = dependencies

structureLawFamily :: GeneratedStructureLawKey -> StructureLawFamily
structureLawFamily = \case
    PredicateComponentLaw{} -> StructurePredicateComponent
    ParentInheritanceLaw{} -> StructurePredicateComponent
    RecordSchemaLaw law -> case law of
        Record.RecordExactGraphLaw -> StructureExactGraph
        Record.RecordReductMembershipLaw -> StructureReductMembership
        Record.RecordReductExactLaw -> StructureReductExact
        Record.RecordProjectionEntryLaw{} -> StructureProjectionEntry
        Record.RecordProjectionAgreementLaw{} -> StructureProjectionAgreement
        Record.RecordProjectionEntryAgreementLaw -> StructureProjectionEntryAgreement
        Record.RecordProjectionGraphAgreementLaw -> StructureProjectionGraphAgreement
        Record.RecordProjectionExtensionalityLaw -> StructureProjectionExtensionality
        Record.RecordReductIdentityLaw -> StructureReductIdentity
        Record.RecordReductProjectionLaw{} -> StructureReductProjection
        Record.RecordSelectorPairDistinctLaw{} -> StructureSelectorPairDistinct
        Record.RecordSelectorDistinctLaw -> StructureSelectorDistinct
        Record.RecordAggregatePairCodedLaw -> StructureAggregatePairCoded
        Record.RecordAggregateValueUniqueLaw{} -> StructureAggregateValueUnique
        Record.RecordAggregateEntryLaw{} -> StructureAggregateEntry
        Record.RecordAggregateSelectorClosedLaw -> StructureAggregateSelectorClosed
        Record.RecordAggregateProjectionApplicationLaw{} -> StructureAggregateProjectionApplication
        Record.RecordAggregateFunctionalLaw -> StructureAggregateFunctional
        Record.RecordAggregateExactLaw -> StructureAggregateExact
        Record.RecordAggregateProjectionLaw{} -> StructureAggregateProjection

-- Public aliases select resolved field roles and complete parent applications.
-- Mathematical targets retain their canonical identities independently of names.
structureLawPresentation
    :: ResolvedStructureSchema -> GeneratedStructureLawKey
    -> (FactSearchEligibility, [SemanticName])
structureLawPresentation schema = \case
    PredicateComponentLaw PredicateShapeComponent -> (SearchEligible, [named "shape"])
    PredicateComponentLaw (PredicateRequirementComponent provenance) ->
        (SearchEligible, case requirementOrigin provenance of
            FieldSpecificationOrigin origin field | origin == owner ->
                maybe [] (maybe [] (pure . markerAlias) . fst) do
                    resolved <- Map.lookup field (resolvedSchemaFields schema)
                    Map.lookup (resolvedFieldSlot resolved) (structurePresentationFields presentation)
            LawOrigin origin ordinal | origin == owner ->
                maybe [] (pure . markerAlias . fst)
                    (Map.lookup ordinal (structurePresentationLaws presentation))
            _ -> [])
    ParentInheritanceLaw application ->
        (SearchEligible, markerAlias <$> Map.findWithDefault [] application
            (resolvedPresentationParentAliases (resolvedSchemaPresentation schema)))
    RecordSchemaLaw law ->
            let ineligible suffix =
                    recordAt SearchIneligible suffix
                fieldAt eligibility prefix field =
                    (eligibility, [named (prefix <> "_" <> fieldRole field)])
            in case law of
                Record.RecordExactGraphLaw -> ineligible "exactgraph"
                Record.RecordReductExactLaw -> ineligible "reductexact"
                Record.RecordReductMembershipLaw ->
                    ineligible "reductmembership"
                Record.RecordProjectionAgreementLaw field ->
                    fieldAt SearchIneligible "projectionagreement" field
                Record.RecordProjectionEntryAgreementLaw ->
                    ineligible "projectionentryagreement"
                Record.RecordProjectionGraphAgreementLaw ->
                    ineligible "projectiongraphagreement"
                Record.RecordProjectionExtensionalityLaw ->
                    ineligible "projectionextensionality"
                Record.RecordReductIdentityLaw ->
                    ineligible "reductidentity"
                Record.RecordReductProjectionLaw field ->
                    fieldAt SearchIneligible "reductprojection" field
                Record.RecordSelectorPairDistinctLaw left right ->
                    let roles = List.sort [fieldRole left, fieldRole right]
                    in (SearchIneligible,
                        [named ("selectordistinctpair_" <> Text.intercalate "_and_" roles)])
                Record.RecordSelectorDistinctLaw ->
                    ineligible "selectordistinct"
                Record.RecordProjectionEntryLaw field ->
                    fieldAt SearchIneligible "projectionentry" field
                Record.RecordAggregatePairCodedLaw ->
                    ineligible "aggregatepaircoded"
                Record.RecordAggregateValueUniqueLaw field ->
                    fieldAt SearchIneligible "aggregatevalueunique" field
                Record.RecordAggregateEntryLaw field ->
                    fieldAt SearchIneligible "aggregateentry" field
                Record.RecordAggregateSelectorClosedLaw ->
                    ineligible "aggregateselectorclosed"
                Record.RecordAggregateProjectionApplicationLaw field ->
                    fieldAt SearchIneligible "aggregateprojectionapplication" field
                Record.RecordAggregateFunctionalLaw ->
                    ineligible "aggregatefunctional"
                Record.RecordAggregateExactLaw ->
                    recordAt SearchEligible "aggregateexact"
                Record.RecordAggregateProjectionLaw field ->
                    fieldAt SearchEligible "aggregateprojection" field
  where
    presentation = resolvedPresentationLocal (resolvedSchemaPresentation schema)
    owner = resolvedSchemaId schema
    Marker marker = structurePhraseMarker (resolvedSchemaPhrase schema)
    markerAlias (Marker text) = semanticName text
    named suffix = semanticName (marker <> suffix)
    recordAt eligibility suffix =
        (eligibility, [named suffix])
    fieldRole identity = unStructSymbol (resolvedFieldSymbol
        (fromMaybe (impossible "a record law lost its field role")
            (Map.lookup identity (resolvedSchemaFields schema))))

-- Transient catalogue construction may consult ancestor registrations. The
-- installed interface retains its own registration and occurrence indexes.
data CheckedStructureCatalogue = CheckedStructureCatalogue
    !CheckedObjectClosure
    !PendingStructureRegistration
    !RecordProof.PreparedRecordSchema
    !RecordProof.CheckedRecordSchema
    !(Map GeneratedStructureLawKey GeneratedLawSpec)
    !(Map StructureResourceKey CheckedPropositionContent)
    !(Map StructureId PendingStructureRegistration)

data CheckedGeneratedImport = CheckedGeneratedImport
    !GeneratedDependency !(FrozenCheckedCore ObjectId)
    deriving stock (Show, Eq)

data StructureLawError
    = StructureLawRecordError !RecordProof.RecordProofError
    | StructureLawTargetInvalid !PropositionValidationError
    | StructureLawAncestorMissing !StructureId
    | StructureLawUnavailable !GeneratedStructureLawKey
    | StructureLawDependencyUnavailable !GeneratedDependency
    | StructureLawDependencySequenceMismatch ![GeneratedDependency] ![GeneratedDependency]
    | StructureLawDependencyTargetMismatch !GeneratedDependency
    | StructureLawTheoryMismatch !TheoryId !TheoryId
    | StructureLawBuildFailed !KernelProof.KernelProofBuildError
    | StructureLawFinalTargetMismatch !GeneratedStructureLawKey
    deriving stock (Show, Eq)

structureCatalogueRegistration :: CheckedStructureCatalogue -> PendingStructureRegistration
structureCatalogueRegistration (CheckedStructureCatalogue _ registration _ _ _ _ _) = registration

structureCatalogueLaws :: CheckedStructureCatalogue -> Map GeneratedStructureLawKey GeneratedLawSpec
structureCatalogueLaws (CheckedStructureCatalogue _ _ _ _ laws _ _) = laws

structureCatalogueResources :: CheckedStructureCatalogue -> Map StructureResourceKey CheckedPropositionContent
structureCatalogueResources (CheckedStructureCatalogue _ _ _ _ _ resources _) = resources

checkStructureCatalogue
    :: CheckedObjectClosure
    -> Set StructureId
    -> (StructureId -> Maybe PendingStructureRegistration)
    -> PendingStructureRegistration
    -> Either StructureLawError CheckedStructureCatalogue
checkStructureCatalogue closure batchIds lookupRegistration registration = do
    unless (checkedObjectClosureTheory closure == resolvedSchemaTheory schema)
        (Left (StructureLawTheoryMismatch (resolvedSchemaTheory schema) (checkedObjectClosureTheory closure)))
    ancestors <- traverse requireAncestor
        (Set.toAscList (Set.map structureApplicationId (resolvedSchemaAncestors schema)))
    let registrations = Map.insert identity registration
            (Map.fromList [(resolvedSchemaId (pendingStructureSchema ancestor), ancestor) | ancestor <- ancestors])
    prepared <- first StructureLawRecordError
        (RecordProof.prepareRecordSchema (resolvedSchemaTheory schema) globalTyping
            [RecordProof.PreparedRecordField (resolvedFieldIdentity field)
                (resolvedFieldSelector field) (resolvedFieldProjection field)
            | field <- Map.elems (resolvedSchemaFields schema)])
    checkedRecord <- first StructureLawRecordError (RecordProof.checkRecordSchema closure prepared)
    fieldResourcesChecked <- traverse (\(key, target) -> (,) key <$> checkTarget target)
        (concatMap fieldResources (Map.elems (resolvedSchemaFields schema)))
    let resources = Map.fromList
            ((PredicateDefinitionResource, structurePredicateDefinitionProposition registration) : fieldResourcesChecked)
    let componentKeys = PredicateShapeComponent :
            (PredicateRequirementComponent <$> Set.toAscList
                (foldMap (Map.keysSet . resolvedRequirementOccurrences) (resolvedSchemaRequirements schema)))
    components <- traverse componentSpec componentKeys
    inheritance <- traverse (inheritanceSpec registrations)
        (resolvedSchemaSemanticAncestorOrder schema)
    records <- traverse (recordSpec prepared) (RecordProof.recordLawInventory prepared)
    let laws = Map.fromList (components <> inheritance <> records)
        catalogue = CheckedStructureCatalogue closure registration prepared checkedRecord laws resources registrations
    traverse_ (traverse_ (structureDependencyTarget catalogue) . generatedLawDependencies) (Map.elems laws)
    pure catalogue
  where
    schema = pendingStructureSchema registration
    identity = resolvedSchemaId schema
    globalTyping = globalTypingFromClosure closure
    checkTarget = first StructureLawTargetInvalid . validatePropositionContent closure
    dependency owner key
        | Set.member owner batchIds = BatchDependency owner key
        | otherwise = EnvironmentDependency owner key
    ownDefinition = dependency identity (StructureResourceFact PredicateDefinitionResource)
    requireAncestor owner = maybe (Left (StructureLawAncestorMissing owner)) Right (lookupRegistration owner)
    componentSpec component = do
        let key = PredicateComponentLaw component
        term <- maybe (Left (StructureLawUnavailable key)) Right
            (structurePredicateComponentTarget registration component)
        target <- checkTarget term
        pure (key, GeneratedLawSpec (StructureLawId identity key) target [ownDefinition])
    inheritanceSpec registrations application = do
        parent <- maybe (Left (StructureLawAncestorMissing (structureApplicationId application))) Right
            (Map.lookup (structureApplicationId application) registrations)
        let key = ParentInheritanceLaw application
            parentDefinition = dependency (structureApplicationId application)
                (StructureResourceFact PredicateDefinitionResource)
            dependencies = if pendingStructurePredicate parent == pendingStructurePredicate registration
                then [ownDefinition] else [ownDefinition, parentDefinition]
        target <- checkTarget (inheritanceTarget registration parent application)
        pure (key, GeneratedLawSpec (StructureLawId identity key) target dependencies)
    recordSpec prepared law = do
        recordTarget <- first StructureLawRecordError (RecordProof.recordLawTarget prepared law)
        target <- checkTarget (frozenCoreTerm recordTarget)
        dependencies <- first StructureLawRecordError (RecordProof.recordLawDependencies prepared law)
        translated <- traverse translateRecordDependency dependencies
        let key = RecordSchemaLaw law
        pure (key, GeneratedLawSpec (StructureLawId identity key) target translated)
    translateRecordDependency = \case
        RecordProof.RecordGeneratedDependency law -> pure (dependency identity (StructureLawFact (RecordSchemaLaw law)))
        RecordProof.RecordSelectorDefinition field -> fieldDependency field (SelectorDefinitionResource field)
        RecordProof.RecordProjectionMembership field -> fieldDependency field (ProjectionMembershipResource field)
    fieldDependency field key = case Map.lookup field (resolvedSchemaFields schema) of
        Just resource -> pure (dependency (resolvedFieldOwner resource) (StructureResourceFact key))
        Nothing -> Left (StructureLawDependencyUnavailable (dependency identity (StructureResourceFact key)))
    fieldResources field =
        [ (SelectorDefinitionResource (resolvedFieldIdentity field),
            canonicalDefinitionEquationTarget (resolvedFieldSelector field) TySet
                (Record.fieldSelectorBody (resolvedFieldIdentity field)))
        , (ProjectionMembershipResource (resolvedFieldIdentity field),
            Record.recordProjectionMembershipLaw (CGlobal (resolvedFieldSelector field))
                (CGlobal (resolvedFieldProjection field)))
        ]

structureDependencyTarget
    :: CheckedStructureCatalogue -> GeneratedDependency -> Either StructureLawError (FrozenCheckedCore ObjectId)
structureDependencyTarget (CheckedStructureCatalogue _ registration _ _ laws resources registrations) dependency =
    case key of
        StructureLawFact law | owner == resolvedSchemaId schema ->
            maybe unavailable (Right . generatedLawTarget) (Map.lookup law laws)
        StructureLawFact _ -> unavailable
        StructureResourceFact PredicateDefinitionResource -> do
            parent <- maybe unavailable Right (Map.lookup owner registrations)
            pure (checkedPropositionTerm (structurePredicateDefinitionProposition parent))
        StructureResourceFact resource@(SelectorDefinitionResource field) -> fieldTarget field resource
        StructureResourceFact resource@(ProjectionMembershipResource field) -> fieldTarget field resource
  where
    schema = pendingStructureSchema registration
    (owner, key) = case dependency of
        BatchDependency identity fact -> (identity, fact)
        EnvironmentDependency identity fact -> (identity, fact)
    fieldTarget field resource = case Map.lookup field (resolvedSchemaFields schema) of
        Just resolved | resolvedFieldOwner resolved == owner ->
            maybe unavailable (Right . checkedPropositionTerm) (Map.lookup resource resources)
        _ -> unavailable
    unavailable :: Either StructureLawError result
    unavailable = Left (StructureLawDependencyUnavailable dependency)

inheritanceTarget
    :: PendingStructureRegistration -> PendingStructureRegistration -> StructureApplicationKey
    -> CanonicalTerm ObjectId
inheritanceTarget child parent application = foldr (const (CForall TySet))
    (CImp (structurePredicateApplication child) parentApplication)
    (() : map (const ()) (resolvedSchemaParameters schema))
  where
    schema = pendingStructureSchema child
    parentApplication = foldl' CApp (CGlobal (pendingStructurePredicate parent))
        (schemaSubject (resolvedSchemaParameterCount schema) : structureApplicationArguments application)

buildStructureLawProof
    :: CheckedFoundation -> CheckedStructureCatalogue -> GeneratedStructureLawKey
    -> [CheckedGeneratedImport] -> Either StructureLawError (KernelProof.BuiltProof ObjectId)
buildStructureLawProof foundation catalogue@(CheckedStructureCatalogue closure registration prepared checkedRecord laws _ registrations) key imports = do
    unless (theoryId foundation == resolvedSchemaTheory schema)
        (Left (StructureLawTheoryMismatch (resolvedSchemaTheory schema) (theoryId foundation)))
    spec <- maybe (Left (StructureLawUnavailable key)) Right (Map.lookup key laws)
    let actualDependencies = [dependency | CheckedGeneratedImport dependency _ <- imports]
    unless (actualDependencies == generatedLawDependencies spec)
        (Left (StructureLawDependencySequenceMismatch (generatedLawDependencies spec) actualDependencies))
    traverse_ (\(CheckedGeneratedImport dependency target) -> do
        expected <- structureDependencyTarget catalogue dependency
        unless (target == expected) (Left (StructureLawDependencyTargetMismatch dependency))) imports
    proof <- case key of
        RecordSchemaLaw law -> do
            checkedLaw <- first StructureLawRecordError (RecordProof.checkRecordSchemaLaw checkedRecord law)
            dependencies <- first StructureLawRecordError (RecordProof.recordLawDependencies prepared law)
            first StructureLawRecordError (RecordProof.buildRecordLawProof foundation checkedLaw
                (zipWith RecordProof.CheckedRecordImport dependencies importTargets))
        PredicateComponentLaw _ -> first StructureLawBuildFailed
            (buildPredicateProjection root (generatedLawTarget spec) Nothing)
        ParentInheritanceLaw application -> do
            parent <- maybe (Left (StructureLawAncestorMissing (structureApplicationId application))) Right
                (Map.lookup (structureApplicationId application) registrations)
            first StructureLawBuildFailed
                (buildPredicateProjection root (generatedLawTarget spec) (Just (application, parent)))
    unless (KernelProof.builtProofStatement proof == embedClosedCore [] (generatedLawTarget spec))
        (Left (StructureLawFinalTargetMismatch key))
    pure proof
  where
    schema = pendingStructureSchema registration
    count = resolvedSchemaParameterCount schema
    binders = TySet : map (const TySet) (resolvedSchemaParameters schema)
    root = KernelProof.rootProofContext foundation (globalTypingFromClosure closure)
    importTargets = [target | CheckedGeneratedImport _ target <- imports]
    importedAt context index = case nth index importTargets of
        Just target -> KernelProof.importedProof context (Kernel.importIx index) target
        Nothing -> Left (KernelProof.ProofStructuralCompositionMismatch "a checked structure import index is absent")
    specializeDefinition context index arguments = do
        imported <- importedAt context index
        KernelProof.specializeForalls context imported arguments
    buildPredicateProjection initial target parent = KernelProof.introduceForalls initial binders
        (\context -> do
            application <- KernelProof.scopedTerm context (structurePredicateApplication registration)
            KernelProof.implicationIntroductionProof context application
                (\withApplication assumption -> do
                    childDefinition <- specializeDefinition withApplication 0
                        (schemaSubject count : schemaParameterArguments count)
                    childBody <- KernelProof.equalityModusPonensProof withApplication childDefinition assumption
                    case parent of
                        Nothing -> do
                            component <- KernelProof.scopedTerm withApplication (targetConclusion (frozenCoreTerm target))
                            project withApplication [childBody] component
                        Just (parentKey, parentRegistration) -> do
                            let parentSchema = pendingStructureSchema parentRegistration
                                selectors = [CGlobal (resolvedFieldSelector field) | field <- Map.elems (resolvedSchemaFields schema)]
                            childShape <- KernelProof.scopedTerm withApplication (Record.recordOpenShape selectors (schemaSubject count))
                                >>= project withApplication [childBody]
                            parentShape <- first (KernelProof.ProofStructuralCompositionMismatch . Text.pack . show)
                                (RecordProof.weakenRecordOpenShape withApplication checkedRecord
                                    (resolvedSchemaSemanticFieldOrder parentSchema) (schemaSubject count) childShape)
                            let arguments = structureApplicationArguments parentKey
                                parentBodyTerm = specializeStructureBody count arguments
                                    (predicateBodyInContext parentSchema)
                            parentBody <- KernelProof.scopedTerm withApplication parentBodyTerm
                                >>= project withApplication [childBody, parentShape]
                            let parentIndex = if pendingStructurePredicate registration == pendingStructurePredicate parentRegistration
                                    then 0 else 1
                            parentDefinition <- specializeDefinition withApplication parentIndex (schemaSubject count : arguments)
                            reversed <- KernelProof.equalityReverseProof withApplication parentDefinition
                            KernelProof.equalityModusPonensProof withApplication reversed parentBody))
    project context premises target = do
        derived <- KernelProof.conjunctionAssumptionProof context premises target
        maybe (Left (KernelProof.ProofStructuralCompositionMismatch "normalized structure inclusion lost a required conjunct")) Right derived
    targetConclusion = \case
        CForall TySet body -> targetConclusion body
        CImp _ body -> body
        _ -> impossible "a checked structure component has no implication body"
    predicateBodyInContext parentSchema = case structurePredicateComponents parentSchema of
        [] -> CTruth
        firstComponent : rest -> foldl' CAnd firstComponent rest

data StructureViewError
    = StructureViewNotDirect !StructureApplicationKey
    | StructureViewVariableOutOfScope !StructureApplicationKey
    deriving stock (Show, Eq)

inheritanceViewVariables
    :: ResolvedStructureSchema -> StructureApplicationKey
    -> Either StructureViewError (Maybe (Vector ViewVariableIx))
inheritanceViewVariables schema application
    | not (Set.member application (resolvedSchemaDirectParents schema)) = Left (StructureViewNotDirect application)
    | otherwise = fmap (fmap Vector.fromList . sequenceA)
        (traverse variable (structureApplicationArguments application))
  where
    count = resolvedSchemaParameterCount schema
    variable = \case
        CBound index | index <= count -> Right (Just (ViewVariableIx index))
        CBound _ -> Left (StructureViewVariableOutOfScope application)
        _ -> Right Nothing
