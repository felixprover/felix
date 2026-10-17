{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Declaration-local structural effects, without authority or an environment.
module Felix.Checking.Structure.Batch
    ( PendingStructureBatch
    , checkPendingStructureBatch
    , pendingBatchInputs
    , pendingBatchRegistrations
    , pendingBatchLawPositions
    , pendingBatchResourceReferences
    , checkStructureBatchRegistrations
    , StructureBatchError(..)
    ) where

import Base
import Felix.Checking.Identity
import Felix.Checking.Planning
import Felix.Checking.Structure.Laws
import Felix.Checking.Structure.Predicate
import Felix.Checking.Structure.Schema
import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data PendingStructureBatch = PendingStructureBatch
    !(NonEmpty LocalStructureSchema)
    !(NonEmpty PendingStructureRegistration)
    !(Map StructureLawId PlannedCandidatePosition)
    !(Map StructureId (Map StructureResourceKey PlannedFactReference))
    deriving stock (Show, Eq)

data StructureBatchError
    = StructureBatchLocalInputInvalid !LocalStructureSchemaError
    | StructureBatchResolutionFailed !StructureResolutionError
    | StructureBatchCatalogueInvalid !StructureLawError
    | StructureBatchDuplicateRegistration !StructureId
    | StructureBatchRegistrationInventoryMismatch
    | StructureBatchRegistrationMismatch !StructureId
    | StructureBatchPredicateInvisible !ObjectId
    | StructureBatchLawInventoryMismatch
    | StructureBatchResourceInventoryMismatch !StructureId
    | StructureBatchLawPositionShared !PlannedCandidatePosition
    | StructureBatchResourcePositionIsLaw !PlannedCandidatePosition
    | StructureBatchResourceSharingMismatch !PlannedCandidatePosition
    | StructureBatchDependencyUnavailable !GeneratedDependency
    | StructureBatchDependencyNotEarlier !StructureLawId !PlannedCandidatePosition
    deriving stock (Show, Eq)

pendingBatchInputs :: PendingStructureBatch -> NonEmpty LocalStructureSchema
pendingBatchInputs (PendingStructureBatch inputs _ _ _) = inputs

pendingBatchRegistrations :: PendingStructureBatch -> NonEmpty PendingStructureRegistration
pendingBatchRegistrations (PendingStructureBatch _ registrations _ _) = registrations

pendingBatchLawPositions :: PendingStructureBatch -> Map StructureLawId PlannedCandidatePosition
pendingBatchLawPositions (PendingStructureBatch _ _ positions _) = positions

pendingBatchResourceReferences
    :: PendingStructureBatch -> Map StructureId (Map StructureResourceKey PlannedFactReference)
pendingBatchResourceReferences (PendingStructureBatch _ _ _ resources) = resources

-- The active closure is explicit and transient. Checked local syntax and
-- predicate bodies are not retyped; new catalogue targets are checked here.
-- Fresh and cached admission use the same whole-batch resolver.
checkStructureBatchRegistrations
    :: CheckedObjectClosure
    -> (StructureId -> Maybe PendingStructureRegistration)
    -> NonEmpty LocalStructureSchema
    -> NonEmpty PendingStructureRegistration
    -> Either StructureBatchError (NonEmpty CheckedStructureCatalogue)
checkStructureBatchRegistrations closure incoming inputs registrations = do
    traverse_ (first StructureBatchLocalInputInvalid . checkLocalSchemaVisibility closure) inputs
    resolved <- first StructureBatchResolutionFailed
        (resolveStructureBatch (fmap pendingStructureSchema . incoming) inputs)
    indexed <- foldM insertRegistration Map.empty registrations
    unless (Map.keysSet indexed == Set.fromList (resolvedSchemaId <$> toList resolved))
        (Left StructureBatchRegistrationInventoryMismatch)
    let lookupRegistration identity = Map.lookup identity indexed <|> incoming identity
    traverse (checkRegistration indexed lookupRegistration) resolved
  where
    insertRegistration indexed registration = do
        let identity = resolvedSchemaId (pendingStructureSchema registration)
        unless (Map.notMember identity indexed)
            (Left (StructureBatchDuplicateRegistration identity))
        pure (Map.insert identity registration indexed)
    checkRegistration indexed lookupRegistration schema = do
        let identity = resolvedSchemaId schema
        registration <- maybe (Left StructureBatchRegistrationInventoryMismatch) Right
            (Map.lookup identity indexed)
        unless (pendingStructureSchema registration == schema)
            (Left (StructureBatchRegistrationMismatch identity))
        unless (checkedObjectMember (pendingStructurePredicate registration) closure)
            (Left (StructureBatchPredicateInvisible (pendingStructurePredicate registration)))
        first StructureBatchCatalogueInvalid
            (checkStructureCatalogue closure (Map.keysSet indexed) lookupRegistration registration)

checkPendingStructureBatch
    :: CheckedObjectClosure
    -> (StructureId -> Maybe PendingStructureRegistration)
    -> NonEmpty LocalStructureSchema
    -> NonEmpty PendingStructureRegistration
    -> Map StructureLawId PlannedCandidatePosition
    -> Map StructureId (Map StructureResourceKey PlannedFactReference)
    -> Either StructureBatchError PendingStructureBatch
checkPendingStructureBatch closure incoming inputs registrations positions resources = do
    catalogues <- checkStructureBatchRegistrations closure incoming inputs registrations
    let indexed = Map.fromList
            [(resolvedSchemaId (pendingStructureSchema (structureCatalogueRegistration catalogue)), catalogue)
            | catalogue <- toList catalogues]
        laws = Map.fromList
            [(generatedLawId law, law) | catalogue <- toList catalogues
            , law <- Map.elems (structureCatalogueLaws catalogue)]
    unless (Map.keysSet positions == Map.keysSet laws)
        (Left StructureBatchLawInventoryMismatch)
    unless (Map.keysSet resources == Map.keysSet indexed)
        (Left StructureBatchRegistrationInventoryMismatch)
    usedPositions <- foldM insertPosition Set.empty (Map.elems positions)
    _ <- foldM (checkResources usedPositions) Map.empty (Map.toAscList indexed)
    traverse_ checkDependencies (Map.elems laws)
    pure (PendingStructureBatch inputs
        (structureCatalogueRegistration <$> catalogues) positions resources)
  where
    insertPosition used position = do
        unless (Set.notMember position used)
            (Left (StructureBatchLawPositionShared position))
        pure (Set.insert position used)
    checkResources lawPositions shared (identity, catalogue) = do
        references <- maybe (Left (StructureBatchResourceInventoryMismatch identity)) Right
            (Map.lookup identity resources)
        let expected = structureCatalogueResources catalogue
        unless (Map.keysSet references == Map.keysSet expected)
            (Left (StructureBatchResourceInventoryMismatch identity))
        foldM (checkResource lawPositions references) shared (Map.toAscList expected)
    checkResource lawPositions references shared (key, proposition) =
        case Map.lookup key references of
            Just (LocalCandidateReference position) -> do
                unless (Set.notMember position lawPositions)
                    (Left (StructureBatchResourcePositionIsLaw position))
                case Map.lookup position shared of
                    Just existing -> unless (existing == proposition)
                        (Left (StructureBatchResourceSharingMismatch position))
                    Nothing -> pure ()
                pure (Map.insert position proposition shared)
            _ -> pure shared
    checkDependencies law = do
        position <- maybe (Left StructureBatchLawInventoryMismatch) Right
            (Map.lookup (generatedLawId law) positions)
        traverse_ (checkDependency (generatedLawId law) position) (generatedLawDependencies law)
    checkDependency law position dependency = case dependency of
        EnvironmentDependency{} -> pure ()
        BatchDependency owner key -> do
            reference <- maybe (Left (StructureBatchDependencyUnavailable dependency)) Right
                (case key of
                    StructureLawFact generated -> LocalCandidateReference <$>
                        Map.lookup (StructureLawId owner generated) positions
                    StructureResourceFact resource -> Map.lookup owner resources >>= Map.lookup resource)
            case reference of
                LocalCandidateReference earlier -> unless
                    (plannedCandidateStage earlier < plannedCandidateStage position)
                    (Left (StructureBatchDependencyNotEarlier law earlier))
                EnvironmentOccurrenceReference{} -> pure ()
