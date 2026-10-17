{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The common declaration compiler for source and manifest structures.
module Felix.Checking.Structure.Generated
    ( CheckedStructureBatchAuthorization
    , lowerStructureBatch
    , authorizeStructureBatch
    ) where

import Base
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Planning
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic
import Felix.Checking.SetConstruction qualified as Construction
import Felix.Checking.Structure.Batch
import Felix.Checking.Structure.Environment qualified as Environment
import Felix.Checking.Structure.Interface qualified as Interface
import Felix.Checking.Structure.Laws
import Felix.Checking.Structure.Predicate
import Felix.Checking.Structure.Schema
import Felix.Syntax.Abstract (Marker(..))
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector

-- Node coordinates are private to this compilation. Only declaration stages
-- and exact environment fingerprints cross the pending-batch boundary.
data NodeKey
    = DefinitionNode !ObjectId
    | MembershipNode !FieldId
    | LawNode !StructureLawId
    deriving stock (Show, Eq, Ord)

data NodeReference
    = LocalNode !NodeKey
    | EnvironmentNode !SemanticFactOccurrenceFingerprint

data Authorization
    = DefinitionAuthorization !ObjectId
    | MembershipAuthorization !ObjectId !(Construction.NamedSetConstruction ObjectId)
    | LawAuthorization !Authority.StructureLawFamily ![PlannedFactReference] !(Kernel.KernelDerivation ObjectId)

newtype CheckedStructureBatchAuthorization =
    CheckedStructureBatchAuthorization [NonEmpty Authorization]

data PreparedNode = PreparedNode
    !Declaration.CandidateSpec ![NodeReference]
    !([PlannedFactReference] -> (Declaration.CandidatePlanningSpec, Authorization))

lowerStructureBatch
    :: CheckedObjectContribution
    -> NonEmpty LocalStructureSchema
    -> Declaration.LoweringDriver
        (Either Declaration.DeclarationError
            (Declaration.CheckedDeclaration CheckedStructureBatchAuthorization))
lowerStructureBatch fieldContribution inputs = do
    incoming <- Declaration.structureEnvironmentLowering
    initialClosure <- Declaration.checkedObjectClosureLowering
    foundation <- Declaration.currentFoundationLowering
    pure do
        let incomingInterface identity = Environment.lookupStructureById identity incoming
            incomingRegistration = fmap Interface.structureInterfaceRegistration . incomingInterface
            localFields = concatMap localSchemaFields (toList inputs)
            fieldIds = Set.fromList (concatMap (\field -> [localFieldSelector field, localFieldProjection field]) localFields)
        unless (checkedObjectContributionIds fieldContribution == fieldIds)
            (invalid "the checked field contribution differs from the batch's local resources")
        fieldClosure <- checked (insertCheckedObjectContribution initialClosure fieldContribution)
        schemas <- checked (resolveStructureBatch (fmap pendingStructureSchema . incomingRegistration) inputs)
        let theory = checkedObjectClosureTheory fieldClosure
            predicates = Map.fromList
                [(resolvedSchemaId schema, transparentObject theory (structurePredicateType schema) (structurePredicateBody schema))
                | schema <- toList schemas]
            newPredicates = Map.elems (Map.fromList
                [(assertedObjectId object, object) | object <- Map.elems predicates
                , not (checkedObjectMember (assertedObjectId object) fieldClosure)])
        closure <- checked (extendObjectClosure fieldClosure newPredicates)
        registrations <- for schemas \schema -> do
            object <- require "a resolved schema lost its predicate" (Map.lookup (resolvedSchemaId schema) predicates)
            checked (checkPendingStructureRegistration closure schema (assertedObjectId object))
        contribution <- checked (checkedObjectContribution closure
            (Set.toAscList fieldIds <> (assertedObjectId <$> newPredicates)))
        let registrationsById = Map.fromList
                [(resolvedSchemaId (pendingStructureSchema registration), registration) | registration <- toList registrations]
            registrationAt identity = Map.lookup identity registrationsById <|> incomingRegistration identity
            localOwners = Map.keysSet registrationsById
        catalogues <- traverse
            (checked . checkStructureCatalogue closure localOwners registrationAt) registrations
        let catalogueById = Map.fromList
                [(resolvedSchemaId (pendingStructureSchema (structureCatalogueRegistration catalogue)), catalogue)
                | catalogue <- toList catalogues]
            environmentReference owner key = do
                interface <- require "an environment dependency has no interface" (incomingInterface owner)
                occurrence <- require "an environment dependency is absent from its index"
                    (Interface.lookupStructureOccurrence key interface)
                pure (EnvironmentNode (semanticFactFingerprint (Interface.structureOccurrenceMetadata occurrence)))
            resourceReference owner key = do
                registration <- require "a resource owner has no registration" (registrationAt owner)
                let schema = pendingStructureSchema registration
                case key of
                    PredicateDefinitionResource
                        | Set.member owner localOwners -> pure (LocalNode (DefinitionNode (pendingStructurePredicate registration)))
                        | otherwise -> environmentReference owner (StructureResourceFact key)
                    SelectorDefinitionResource field -> fieldResource schema field key
                        (\resolved -> DefinitionNode (resolvedFieldSelector resolved))
                    ProjectionMembershipResource field -> fieldResource schema field key
                        (MembershipNode . resolvedFieldIdentity)
              where
                fieldResource schema identity resource node = do
                    field <- require "a resource names an unavailable field" (Map.lookup identity (resolvedSchemaFields schema))
                    if Set.member (resolvedFieldOwner field) localOwners
                        then pure (LocalNode (node field))
                        else environmentReference (resolvedFieldOwner field) (StructureResourceFact resource)
            dependencyReference = \case
                EnvironmentDependency owner key -> environmentReference owner key
                BatchDependency owner (StructureResourceFact key) -> resourceReference owner key
                BatchDependency owner (StructureLawFact key) -> pure (LocalNode (LawNode (StructureLawId owner key)))
            predicateAliases = Map.fromListWith (<>)
                [(pendingStructurePredicate registration,
                    [semanticName marker])
                | registration <- toList registrations
                , let Marker marker = structurePhraseMarker (resolvedSchemaPhrase (pendingStructureSchema registration))]
            definitionIds = fieldIds <> Map.keysSet predicateAliases
        definitions <- for (Set.toAscList definitionIds) \identity -> do
            content <- require "a definition resource is absent from the checked closure" (lookupCheckedObjectContent identity closure)
            (coreType, body) <- case content of
                TransparentObjectContent _ coreType body -> pure (coreType, body)
                _ -> invalid "a generated definition is not transparent"
            proposition <- checked (validatePropositionContent closure (canonicalDefinitionEquationTarget identity coreType body))
            let aliases = List.nub (Map.findWithDefault [] identity predicateAliases)
                eligibility = if null aliases then SearchIneligible else SearchEligible
            pure (DefinitionNode identity, PreparedNode (Declaration.candidateSpec proposition eligibility aliases) []
                (const (Declaration.checkedDefinitionEquationPlanning identity, DefinitionAuthorization identity)))
        memberships <- for localFields \field -> do
            construction <- require "a local projection has no canonical construction"
                (Record.fieldProjectionConstruction (globalTypingFromClosure closure) (localFieldSelector field))
            fact <- require "a local projection construction cannot be checked"
                (Construction.namedSetConstructionObjectFact (Construction.checkedFoundationSetConstruction foundation)
                    closure (localFieldProjection field) construction)
            proposition <- checked (validatePropositionContent closure
                (frozenCoreTerm (Construction.namedSetConstructionFactProposition fact)))
            let descriptor = Authority.CheckedSetConstructionExtensionality
                    (localFieldProjection field) (Construction.namedSetConstructionFactDescriptor fact)
            pure (MembershipNode (localFieldIdentity field),
                PreparedNode (Declaration.candidateSpec proposition SearchIneligible []) []
                    (const (Declaration.checkedKernelPlanning descriptor [],
                        MembershipAuthorization (localFieldProjection field) construction)))
        laws <- fmap concat $ for (toList catalogues) \catalogue ->
            for (Map.toAscList (structureCatalogueLaws catalogue)) \(key, law) -> do
                references <- traverse dependencyReference (generatedLawDependencies law)
                imports <- for (generatedLawDependencies law) \dependency ->
                    CheckedGeneratedImport dependency <$> checked (structureDependencyTarget catalogue dependency)
                proof <- checked (buildStructureLawProof foundation catalogue key imports)
                let schema = pendingStructureSchema (structureCatalogueRegistration catalogue)
                    (eligibility, aliases) = structureLawPresentation schema key
                    family = structureLawFamily key
                pure (LawNode (generatedLawId law), PreparedNode
                    (Declaration.structureLawCandidateSpec law eligibility aliases) references
                    (\planned -> (Declaration.checkedKernelPlanningReferences (Authority.CheckedStructureLaw family) planned,
                        LawAuthorization family planned (KernelProof.builtProofDerivation proof))))
        let nodes = Map.fromList (definitions <> memberships <> laws)
        layers <- scheduleNodes nodes
        let positions = Map.fromList
                [(key, PlannedCandidatePosition stage index)
                | (stage, layer) <- zip [0 ..] layers, (index, key) <- zip [0 ..] (toList layer)]
            plannedReference = \case
                EnvironmentNode fingerprint -> pure (EnvironmentOccurrenceReference fingerprint)
                LocalNode key -> LocalCandidateReference <$> require "a dependency has no scheduled candidate" (Map.lookup key positions)
        preparedStages <- for layers $ traverse \key -> do
            PreparedNode spec references prepare <- require "a scheduled node has no recipe" (Map.lookup key nodes)
            planned <- traverse plannedReference references
            let (planning, authorization) = prepare planned
            pure (Declaration.checkedCandidate spec planning, authorization)
        resources <- for catalogueById \catalogue ->
            let owner = resolvedSchemaId (pendingStructureSchema (structureCatalogueRegistration catalogue))
            in Map.traverseWithKey (\key _ -> resourceReference owner key >>= plannedReference) (structureCatalogueResources catalogue)
        let lawPositions = Map.fromList [(law, position) | (LawNode law, position) <- Map.toAscList positions]
        batch <- checked (checkPendingStructureBatch closure incomingRegistration inputs registrations lawPositions resources)
        views <- fmap concat $ for (toList registrations) \registration -> do
            let schema = pendingStructureSchema registration
                subjectArguments = Vector.fromList
                    [TemplateVariable (ViewVariableIx ordinal) | ordinal <- reverse [0 .. resolvedSchemaParameterCount schema]]
            fmap catMaybes $ for (resolvedSchemaSemanticDirectParentOrder schema) \application -> do
                eligible <- checked (inheritanceViewVariables schema application)
                for eligible \variables -> do
                    parent <- require "a direct-parent view has no registration" (registrationAt (structureApplicationId application))
                    position <- require "a direct-parent view has no law candidate"
                        (Map.lookup (StructureLawId (resolvedSchemaId schema) (ParentInheritanceLaw application)) lawPositions)
                    pure (Registration position ConjunctionHere (RegisterNotionView (NotionViewRule
                        (StructureNotionViewPremise (pendingStructureNotionHead registration) subjectArguments)
                        (AtomicLeaf (StructureAtomTemplate (pendingStructureNotionHead parent)
                            (Vector.cons (TemplateVariable (ViewVariableIx (resolvedSchemaParameterCount schema)))
                                (TemplateVariable <$> variables)))))))
        pure (Declaration.checkedStructureDeclaration (structureBatchSyntaxId inputs) contribution batch views
            (fmap fst <$> preparedStages) (CheckedStructureBatchAuthorization (fmap snd <$> preparedStages)))

-- All members of a layer depend only on completed earlier layers. Sorting by
-- structural keys makes positions independent of map insertion order.
scheduleNodes :: Map NodeKey PreparedNode -> Either Declaration.DeclarationError [NonEmpty NodeKey]
scheduleNodes = go Set.empty
  where
    go complete remaining
        | Map.null remaining = pure []
        | otherwise = do
            let ready = [key | (key, PreparedNode _ references _) <- Map.toAscList remaining
                    , all (available complete) references]
            layer <- require "generated dependencies are cyclic or name absent candidates" (NonEmpty.nonEmpty ready)
            (layer :) <$> go (complete <> Set.fromList ready) (Map.withoutKeys remaining (Set.fromList ready))
    available complete = \case
        EnvironmentNode{} -> True
        LocalNode key -> Set.member key complete

invalid :: Text -> Either Declaration.DeclarationError a
invalid = Left . Declaration.StructureDeclarationInvalid

checked :: Show error => Either error a -> Either Declaration.DeclarationError a
checked = first (Declaration.StructureDeclarationInvalid . Text.pack . show)

require :: Text -> Maybe a -> Either Declaration.DeclarationError a
require message = maybe (invalid message) Right

authorizeStructureBatch
    :: CheckedStructureBatchAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeStructureBatch (CheckedStructureBatchAuthorization recipes) stages = do
    unless (length recipes == length stages && and (zipWith (\a b -> NonEmpty.length a == NonEmpty.length b) recipes stages))
        (Declaration.failDeclaration (Declaration.CheckedAuthorizationCandidateShapeMismatch (length recipes) (length stages)))
    traverse_ (traverse_ (uncurry authorize) . uncurry NonEmpty.zip) (zip recipes stages)
  where
    authorize recipe candidate = case recipe of
        DefinitionAuthorization identity -> Declaration.authorizeDefinitionEquationCandidate identity candidate
        MembershipAuthorization identity construction -> Declaration.authorizeNamedSetConstructionCandidate identity construction candidate
        LawAuthorization family references derivation ->
            Declaration.authorizeKernelConstructionCandidate (Authority.CheckedStructureLaw family) candidate do
                actual <- traverse useReference references
                unless (actual == [Kernel.importIx index | (index, _) <- zip [0 ..] references])
                    (impossible "generated kernel imports changed their declared order")
                pure derivation
    useReference = \case
        EnvironmentOccurrenceReference fingerprint -> Declaration.useAuthorizedFact fingerprint
        LocalCandidateReference position -> Declaration.useStagedCandidate
            (fromMaybe (impossible "a generated premise lost its reserved position")
                (Declaration.candidateAtPosition position stages))
