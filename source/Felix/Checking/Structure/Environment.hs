{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Atomic identity and lexical indexes over complete, phase-indexed interfaces.
module Felix.Checking.Structure.Environment
    ( StructureEnvironment
    , emptyStructureEnvironment
    , installBuiltinStructureInterfaces
    , extendStructureEnvironment
    , mergeStructureEnvironments
    , rebindStructureEnvironmentEvidence
    , structureEnvironmentInterfaces
    , structureEnvironmentManifest
    , lookupStructureById
    , lookupStructureByPhrase
    , StructureEnvironmentError(..)
    ) where

import Base
import Felix.Checking.Identity
import Felix.Checking.Authority (DirectAuthorization)
import Felix.Checking.Semantic (SemanticFactOccurrenceFingerprint)
import Felix.Checking.Structure.Builtin
import Felix.Checking.Structure.Interface
import Felix.Checking.Structure.Predicate
import Felix.Checking.Structure.Schema
import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map

data StructureEnvironment evidence = StructureEnvironment
    !(Maybe BuiltinStructureManifest)
    !(Map StructureId (CheckedStructureInterface evidence))
    !(Map StructurePhrase StructureId)
    deriving stock (Show, Eq)

data StructureEnvironmentError
    = StructureEnvironmentNotRooted
    | StructureEnvironmentManifestMismatch
    | StructureEnvironmentManifestInvalid !Text
    | StructureEnvironmentRootMismatch !StructureId
    | StructureEnvironmentIdentityConflict !StructureId
    | StructureEnvironmentPhraseConflict !StructurePhrase !StructureId !StructureId
    deriving stock (Show, Eq)

emptyStructureEnvironment :: StructureEnvironment evidence
emptyStructureEnvironment = StructureEnvironment Nothing Map.empty Map.empty

structureEnvironmentManifest :: StructureEnvironment evidence -> Maybe BuiltinStructureManifest
structureEnvironmentManifest (StructureEnvironment manifest _ _) = manifest

structureEnvironmentInterfaces :: StructureEnvironment evidence -> Map StructureId (CheckedStructureInterface evidence)
structureEnvironmentInterfaces (StructureEnvironment _ interfaces _) = interfaces

lookupStructureById :: StructureId -> StructureEnvironment evidence -> Maybe (CheckedStructureInterface evidence)
lookupStructureById identity (StructureEnvironment _ interfaces _) = Map.lookup identity interfaces

lookupStructureByPhrase :: StructurePhrase -> StructureEnvironment evidence -> Maybe (CheckedStructureInterface evidence)
lookupStructureByPhrase phrase (StructureEnvironment _ interfaces phrases) =
    Map.lookup phrase phrases >>= (`Map.lookup` interfaces)

installBuiltinStructureInterfaces
    :: BuiltinStructureManifest
    -> NonEmpty (CheckedStructureInterface evidence)
    -> Either StructureEnvironmentError (StructureEnvironment evidence)
installBuiltinStructureInterfaces manifest interfaces = do
    first StructureEnvironmentManifestInvalid
        (checkBuiltinStructureSchemas manifest (interfaceSchema <$> interfaces))
    foldM insertInterface (StructureEnvironment (Just manifest) Map.empty Map.empty) interfaces

extendStructureEnvironment
    :: NonEmpty (CheckedStructureInterface evidence)
    -> StructureEnvironment evidence
    -> Either StructureEnvironmentError (StructureEnvironment evidence)
extendStructureEnvironment interfaces environment@(StructureEnvironment manifest _ _) = do
    sealed <- maybe (Left StructureEnvironmentNotRooted) Right manifest
    traverse_ (checkRoot sealed . interfaceSchema) interfaces
    foldM insertInterface environment interfaces
  where
    checkRoot sealed schema = unless
        (resolvedSchemaRoot schema == builtinRecordId sealed
            && (resolvedSchemaRole schema == OrdinaryStructure
                || resolvedSchemaId schema == builtinRecordId sealed))
        (Left (StructureEnvironmentRootMismatch (resolvedSchemaId schema)))

-- Import composition reuses checked interfaces; it does not resolve schemas,
-- reopen predicate objects, or revalidate the already admitted ancestor graph.
mergeStructureEnvironments
    :: StructureEnvironment evidence -> StructureEnvironment evidence
    -> Either StructureEnvironmentError (StructureEnvironment evidence)
mergeStructureEnvironments left@(StructureEnvironment leftManifest _ _) right@(StructureEnvironment rightManifest rightInterfaces _) =
    case (leftManifest, rightManifest) of
        (Nothing, _) -> pure right
        (_, Nothing) -> pure left
        (Just existing, Just incoming) -> do
            unless (existing == incoming) (Left StructureEnvironmentManifestMismatch)
            foldM insertInterface left (Map.elems rightInterfaces)

interfaceSchema :: CheckedStructureInterface evidence -> ResolvedStructureSchema
interfaceSchema = pendingStructureSchema . structureInterfaceRegistration

rebindStructureEnvironmentEvidence
    :: (old -> Maybe DirectAuthorization)
    -> (new -> Maybe DirectAuthorization)
    -> Map SemanticFactOccurrenceFingerprint (StructureOccurrence new)
    -> StructureEnvironment old
    -> Either StructureInterfaceError (StructureEnvironment new)
rebindStructureEnvironmentEvidence oldDirect newDirect registry (StructureEnvironment manifest interfaces phrases) = do
    rebound <- traverse (rebindStructureInterfaceEvidence oldDirect newDirect registry) interfaces
    pure (StructureEnvironment manifest rebound phrases)

insertInterface
    :: StructureEnvironment evidence -> CheckedStructureInterface evidence
    -> Either StructureEnvironmentError (StructureEnvironment evidence)
insertInterface environment@(StructureEnvironment manifest interfaces phrases) interface = do
    let schema = interfaceSchema interface
        identity = resolvedSchemaId schema
        phrase = resolvedSchemaPhrase schema
    case Map.lookup identity interfaces of
        Just existing -> do
            unless (sameStructureInterface existing interface)
                (Left (StructureEnvironmentIdentityConflict identity))
            pure environment
        Nothing -> do
            case Map.lookup phrase phrases of
                Just previous -> unless (previous == identity)
                    (Left (StructureEnvironmentPhraseConflict phrase previous identity))
                Nothing -> pure ()
            pure (StructureEnvironment manifest (Map.insert identity interface interfaces)
                (Map.insert phrase identity phrases))
