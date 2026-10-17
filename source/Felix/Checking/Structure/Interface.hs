{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Complete mathematical interfaces. Evidence is retained, never minted here.
module Felix.Checking.Structure.Interface
    ( CheckedStructureInterface
    , StructureOccurrence(..)
    , structureOccurrenceProposition
    , structureOccurrenceMetadata
    , structureOccurrenceEvidence
    , checkStructureInterfaces
    , checkStructureInterfacesWithDependencies
    , structureInterfaceRegistration
    , structureInterfaceLawIndex
    , structureInterfaceResourceIndex
    , structureInterfaceOccurrences
    , lookupStructureOccurrence
    , sameStructureInterface
    , rebindStructureInterfaceEvidence
    , StructureInterfaceError(..)
    ) where

import Base
import Felix.Checking.Authority
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic
import Felix.Checking.SetConstruction qualified as Construction
import Felix.Checking.Structure.Batch
import Felix.Checking.Structure.Laws
import Felix.Checking.Structure.Predicate
import Felix.Checking.Structure.Schema
import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data StructureOccurrence evidence = StructureOccurrence
    !CheckedPropositionContent !SemanticFactOccurrence !evidence
    deriving stock (Show, Eq)

structureOccurrenceProposition :: StructureOccurrence evidence -> CheckedPropositionContent
structureOccurrenceProposition (StructureOccurrence proposition _ _) = proposition

structureOccurrenceMetadata :: StructureOccurrence evidence -> SemanticFactOccurrence
structureOccurrenceMetadata (StructureOccurrence _ metadata _) = metadata

structureOccurrenceEvidence :: StructureOccurrence evidence -> evidence
structureOccurrenceEvidence (StructureOccurrence _ _ evidence) = evidence

data CheckedStructureInterface evidence = CheckedStructureInterface
    !PendingStructureRegistration
    !(Map GeneratedStructureLawKey SemanticFactOccurrenceFingerprint)
    !(Map StructureResourceKey SemanticFactOccurrenceFingerprint)
    !(Map SemanticFactOccurrenceFingerprint (StructureOccurrence evidence))
    deriving stock (Show, Eq)

data StructureInterfaceError
    = StructureInterfaceBatchInvalid !StructureBatchError
    | StructureInterfaceTheoryMismatch !TheoryId !TheoryId
    | StructureInterfaceOwnerInventoryMismatch
    | StructureInterfaceFactInventoryMismatch !StructureId
    | StructureInterfaceTargetMismatch !StructureId !StructureFactKey
    | StructureInterfaceSearchEligibilityMismatch !StructureId !GeneratedStructureLawKey
    | StructureInterfacePurposeMismatch !StructureId !StructureFactKey
    | StructureInterfaceTheoremMismatch !StructureId !StructureFactKey
    | StructureInterfaceAuthorityMismatch !StructureId !StructureFactKey
    | StructureInterfaceResourceInvalid !StructureId !StructureResourceKey
    | StructureInterfaceOccurrenceConflict !SemanticFactOccurrenceFingerprint
    | StructureInterfaceEvidenceMissing !SemanticFactOccurrenceFingerprint
    | StructureInterfaceEvidenceMismatch !SemanticFactOccurrenceFingerprint
    deriving stock (Show, Eq)

structureInterfaceRegistration :: CheckedStructureInterface evidence -> PendingStructureRegistration
structureInterfaceRegistration (CheckedStructureInterface registration _ _ _) = registration

structureInterfaceLawIndex
    :: CheckedStructureInterface evidence -> Map GeneratedStructureLawKey SemanticFactOccurrenceFingerprint
structureInterfaceLawIndex (CheckedStructureInterface _ laws _ _) = laws

structureInterfaceResourceIndex
    :: CheckedStructureInterface evidence -> Map StructureResourceKey SemanticFactOccurrenceFingerprint
structureInterfaceResourceIndex (CheckedStructureInterface _ _ resources _) = resources

structureInterfaceOccurrences
    :: CheckedStructureInterface evidence -> Map SemanticFactOccurrenceFingerprint (StructureOccurrence evidence)
structureInterfaceOccurrences (CheckedStructureInterface _ _ _ occurrences) = occurrences

lookupStructureOccurrence
    :: StructureFactKey -> CheckedStructureInterface evidence -> Maybe (StructureOccurrence evidence)
lookupStructureOccurrence key (CheckedStructureInterface _ laws resources occurrences) = do
    fingerprint <- case key of
        StructureLawFact law -> Map.lookup law laws
        StructureResourceFact resource -> Map.lookup resource resources
    Map.lookup fingerprint occurrences

checkStructureInterfaces
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> (evidence -> Maybe DirectAuthorization)
    -> (StructureId -> Maybe (CheckedStructureInterface evidence))
    -> NonEmpty LocalStructureSchema
    -> NonEmpty PendingStructureRegistration
    -> Map StructureId (Map StructureFactKey (StructureOccurrence evidence))
    -> Either StructureInterfaceError (NonEmpty (CheckedStructureInterface evidence))
checkStructureInterfaces foundation closure direct incoming inputs registrations supplied =
    fst <$> checkStructureInterfacesWithDependencies foundation closure direct incoming inputs registrations supplied

-- The fresh adapter also checks the actual proof imports against this ordered
-- contract. Returning it avoids resolving and typechecking the catalogue twice.
checkStructureInterfacesWithDependencies
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> (evidence -> Maybe DirectAuthorization)
    -> (StructureId -> Maybe (CheckedStructureInterface evidence))
    -> NonEmpty LocalStructureSchema
    -> NonEmpty PendingStructureRegistration
    -> Map StructureId (Map StructureFactKey (StructureOccurrence evidence))
    -> Either StructureInterfaceError
        (NonEmpty (CheckedStructureInterface evidence), Map StructureLawId [GeneratedDependency])
checkStructureInterfacesWithDependencies foundation closure direct incoming inputs registrations supplied = do
    unless (theoryId foundation == checkedObjectClosureTheory closure)
        (Left (StructureInterfaceTheoryMismatch (theoryId foundation) (checkedObjectClosureTheory closure)))
    catalogues <- first StructureInterfaceBatchInvalid
        (checkStructureBatchRegistrations closure
            (fmap structureInterfaceRegistration . incoming) inputs registrations)
    unless (Map.keysSet supplied == Set.fromList
            [resolvedSchemaId (pendingStructureSchema (structureCatalogueRegistration catalogue))
            | catalogue <- toList catalogues])
        (Left StructureInterfaceOwnerInventoryMismatch)
    interfaces <- traverse checkInterface catalogues
    pure (interfaces, Map.fromList
        [(generatedLawId law, generatedLawDependencies law)
        | catalogue <- toList catalogues, law <- Map.elems (structureCatalogueLaws catalogue)])
  where
    checkInterface catalogue = do
        let registration = structureCatalogueRegistration catalogue
            schema = pendingStructureSchema registration
            owner = resolvedSchemaId schema
            laws = structureCatalogueLaws catalogue
            resources = structureCatalogueResources catalogue
            expected = Map.fromList
                ([(StructureLawFact key, generatedLawProposition spec) | (key, spec) <- Map.toAscList laws]
                <> [(StructureResourceFact key, target) | (key, target) <- Map.toAscList resources])
        occurrences <- maybe (Left StructureInterfaceOwnerInventoryMismatch) Right (Map.lookup owner supplied)
        unless (Map.keysSet expected == Map.keysSet occurrences)
            (Left (StructureInterfaceFactInventoryMismatch owner))
        checked <- traverse (checkOccurrence registration expected) (Map.toAscList occurrences)
        indexed <- foldM insertOccurrence Map.empty checked
        let fingerprint = semanticFactFingerprint . structureOccurrenceMetadata
        pure (CheckedStructureInterface registration
            (Map.fromList [(law, fingerprint occurrence)
                | (StructureLawFact law, occurrence) <- Map.toAscList occurrences])
            (Map.fromList [(resource, fingerprint occurrence)
                | (StructureResourceFact resource, occurrence) <- Map.toAscList occurrences])
            indexed)
    checkOccurrence registration expected (key, occurrence@(StructureOccurrence proposition metadata evidence)) = do
        let schema = pendingStructureSchema registration
            owner = resolvedSchemaId schema
            expectedPurpose = case key of
                StructureLawFact law -> structureLawPurpose (StructureLawId owner law)
                StructureResourceFact _ -> GeneralFactPurpose
        unless (Map.lookup key expected == Just proposition)
            (Left (StructureInterfaceTargetMismatch owner key))
        unless (semanticFactPurpose metadata == expectedPurpose)
            (Left (StructureInterfacePurposeMismatch owner key))
        unless (factAuthorityTheorem (semanticFactAuthority metadata)
                == theoremRef (resolvedSchemaTheory schema) (checkedPropositionId proposition))
            (Left (StructureInterfaceTheoremMismatch owner key))
        expectedDirect <- case key of
            StructureLawFact law -> do
                unless (semanticFactSearchEligibility metadata == fst (structureLawPresentation schema law))
                    (Left (StructureInterfaceSearchEligibilityMismatch owner law))
                pure (CheckedKernelConstruction (CheckedStructureLaw (structureLawFamily law)))
            StructureResourceFact resource -> resourceAuthorization registration resource
        unless (factAuthoritySafety (semanticFactAuthority metadata) == cleanAuthoritySafety
                && direct evidence == Just expectedDirect)
            (Left (StructureInterfaceAuthorityMismatch owner key))
        pure occurrence
    resourceAuthorization registration resource = do
        let schema = pendingStructureSchema registration
            failure :: Either StructureInterfaceError result
            failure = Left (StructureInterfaceResourceInvalid (resolvedSchemaId schema) resource)
            field identity = maybe failure Right (Map.lookup identity (resolvedSchemaFields schema))
        descriptor <- case resource of
            PredicateDefinitionResource -> pure (CheckedDefinitionEquation (pendingStructurePredicate registration))
            SelectorDefinitionResource identity -> CheckedDefinitionEquation . resolvedFieldSelector <$> field identity
            ProjectionMembershipResource identity -> do
                resolved <- field identity
                construction <- maybe failure Right
                    (Record.fieldProjectionConstruction (globalTypingFromClosure closure) (resolvedFieldSelector resolved))
                fact <- maybe failure Right
                    (Construction.namedSetConstructionObjectFact (Construction.checkedFoundationSetConstruction foundation)
                        closure (resolvedFieldProjection resolved) construction)
                pure (CheckedSetConstructionExtensionality (resolvedFieldProjection resolved)
                    (Construction.namedSetConstructionFactDescriptor fact))
        pure (CheckedKernelConstruction descriptor)

insertOccurrence
    :: Map SemanticFactOccurrenceFingerprint (StructureOccurrence evidence)
    -> StructureOccurrence evidence
    -> Either StructureInterfaceError (Map SemanticFactOccurrenceFingerprint (StructureOccurrence evidence))
insertOccurrence indexed occurrence = do
    let fingerprint = semanticFactFingerprint (structureOccurrenceMetadata occurrence)
    case Map.lookup fingerprint indexed of
        Just existing -> unless (sameOccurrence existing occurrence)
            (Left (StructureInterfaceOccurrenceConflict fingerprint))
        Nothing -> pure ()
    pure (Map.insert fingerprint occurrence indexed)

sameOccurrence :: StructureOccurrence left -> StructureOccurrence right -> Bool
sameOccurrence left right =
    structureOccurrenceProposition left == structureOccurrenceProposition right
        && structureOccurrenceMetadata left == structureOccurrenceMetadata right

sameStructureInterface :: CheckedStructureInterface left -> CheckedStructureInterface right -> Bool
sameStructureInterface left right =
    structureInterfaceRegistration left == structureInterfaceRegistration right
        && structureInterfaceLawIndex left == structureInterfaceLawIndex right
        && structureInterfaceResourceIndex left == structureInterfaceResourceIndex right
        && Map.keysSet (structureInterfaceOccurrences left) == Map.keysSet (structureInterfaceOccurrences right)
        && and (Map.elems (Map.intersectionWith sameOccurrence
            (structureInterfaceOccurrences left) (structureInterfaceOccurrences right)))

-- Reassociation requires exact checked registry rows, including their direct
-- contract. There is deliberately no Functor instance or unchecked evidence
-- map. Declaration supplies its phase's registry and still owns all capability
-- constructors; caller-created certificates never become registry membership.
rebindStructureInterfaceEvidence
    :: (old -> Maybe DirectAuthorization)
    -> (new -> Maybe DirectAuthorization)
    -> Map SemanticFactOccurrenceFingerprint (StructureOccurrence new)
    -> CheckedStructureInterface old
    -> Either StructureInterfaceError (CheckedStructureInterface new)
rebindStructureInterfaceEvidence oldDirect newDirect registry
        (CheckedStructureInterface registration laws resources occurrences) = do
    rebound <- Map.traverseWithKey rebind occurrences
    pure (CheckedStructureInterface registration laws resources rebound)
  where
    rebind fingerprint old = do
        new <- maybe (Left (StructureInterfaceEvidenceMissing fingerprint)) Right (Map.lookup fingerprint registry)
        unless (sameOccurrence old new
                && isJust (oldDirect (structureOccurrenceEvidence old))
                && oldDirect (structureOccurrenceEvidence old) == newDirect (structureOccurrenceEvidence new))
            (Left (StructureInterfaceEvidenceMismatch fingerprint))
        pure new
