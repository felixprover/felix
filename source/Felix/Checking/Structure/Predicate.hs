{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The sole open predicate interpretation of a normalized finite schema.
module Felix.Checking.Structure.Predicate
    ( PendingStructureRegistration
    , checkPendingStructureRegistration
    , pendingStructureSchema
    , pendingStructurePredicate
    , CheckedStructurePredicateDefinition
    , pendingStructureDefinition
    , structurePredicateType
    , structurePredicateBody
    , structurePredicateApplication
    , structurePredicateComponents
    , structurePredicateComponentTarget
    , structurePredicateDefinitionTarget
    , structurePredicateDefinitionProposition
    , AppliedStructurePredicate
    , applyStructurePredicate
    , appliedStructureRegistration
    , appliedStructureTerm
    , appliedStructureShape
    , appliedStructureRequirements
    , appliedStructureRequirementOccurrences
    , appliedStructureComponents
    , StructurePredicateError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Checking.Structure.Schema
import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map

-- Both constructors and their record-update surface remain private.
data CheckedStructurePredicateDefinition = CheckedStructurePredicateDefinition
    !ObjectId !CoreType !(CanonicalTerm ObjectId)
    !CheckedPropositionContent
    deriving stock (Show, Eq)

data PendingStructureRegistration = PendingStructureRegistration
    !ResolvedStructureSchema !CheckedStructurePredicateDefinition
    deriving stock (Show, Eq)

data StructurePredicateError
    = StructurePredicateTheoryMismatch !TheoryId !TheoryId
    | StructurePredicateResourceMissing !ObjectId
    | StructurePredicateObjectInvalid !ObjectId
    | StructurePredicateDefinitionInvalid !PropositionValidationError
    deriving stock (Show, Eq)

checkPendingStructureRegistration
    :: CheckedObjectClosure -> ResolvedStructureSchema -> ObjectId
    -> Either StructurePredicateError PendingStructureRegistration
checkPendingStructureRegistration closure schema predicate = do
    let theory = resolvedSchemaTheory schema
        expectedType = structurePredicateType schema
        expectedBody = structurePredicateBody schema
    unless (checkedObjectClosureTheory closure == theory)
        (Left (StructurePredicateTheoryMismatch theory (checkedObjectClosureTheory closure)))
    traverse_ requireObject
        [object | field <- Map.elems (resolvedSchemaFields schema)
                , object <- [resolvedFieldSelector field, resolvedFieldProjection field]]
    unless (lookupCheckedObjectContent predicate closure ==
            Just (TransparentObjectContent theory expectedType expectedBody))
        (Left (StructurePredicateObjectInvalid predicate))
    equation <- first StructurePredicateDefinitionInvalid
        (validatePropositionContent closure
            (canonicalDefinitionEquationTarget predicate expectedType expectedBody))
    pure (PendingStructureRegistration schema
        (CheckedStructurePredicateDefinition predicate expectedType expectedBody equation))
  where
    requireObject object = unless (checkedObjectMember object closure)
        (Left (StructurePredicateResourceMissing object))

pendingStructureSchema :: PendingStructureRegistration -> ResolvedStructureSchema
pendingStructureSchema (PendingStructureRegistration schema _) = schema

pendingStructureDefinition :: PendingStructureRegistration -> CheckedStructurePredicateDefinition
pendingStructureDefinition (PendingStructureRegistration _ definition) = definition

pendingStructurePredicate :: PendingStructureRegistration -> ObjectId
pendingStructurePredicate (PendingStructureRegistration _ (CheckedStructurePredicateDefinition object _ _ _)) = object

structurePredicateType :: ResolvedStructureSchema -> CoreType
structurePredicateType schema = foldr (const (TyArrow TySet)) TyProp
    (() : map (const ()) (resolvedSchemaParameters schema))

-- | Subject, then parameters, in declared binder order. Empty requirement
-- families contribute no truth wrapper; both manifest predicates therefore
-- have precisely their expected record-shape bodies.
structurePredicateBody :: ResolvedStructureSchema -> CanonicalTerm ObjectId
structurePredicateBody schema = foldr (const (CLam TySet))
    (conjunction (structurePredicateComponents schema))
    (() : map (const ()) (resolvedSchemaParameters schema))

structurePredicateComponents :: ResolvedStructureSchema -> [CanonicalTerm ObjectId]
structurePredicateComponents schema =
    [resolvedRequirementBody requirement | requirement <- requirements, requirementIsAdmissibility requirement]
        <> [shape]
        <> [resolvedRequirementBody requirement | requirement <- requirements, not (requirementIsAdmissibility requirement)]
  where
    requirements = Map.elems (resolvedSchemaRequirements schema)
    shape = Record.recordOpenShape
        [CGlobal (resolvedFieldSelector field) | field <- Map.elems (resolvedSchemaFields schema)]
        (schemaSubject (resolvedSchemaParameterCount schema))

structurePredicateApplication :: PendingStructureRegistration -> CanonicalTerm ObjectId
structurePredicateApplication registration = foldl' CApp
    (CGlobal (pendingStructurePredicate registration))
    (schemaSubject count : schemaParameterArguments count)
  where
    count = resolvedSchemaParameterCount (pendingStructureSchema registration)

structurePredicateComponentTarget
    :: PendingStructureRegistration -> PredicateComponentKey -> Maybe (CanonicalTerm ObjectId)
structurePredicateComponentTarget registration component = do
    body <- case component of
        PredicateShapeComponent -> pure
            (Record.recordOpenShape
                [CGlobal (resolvedFieldSelector field) | field <- Map.elems (resolvedSchemaFields schema)]
                (schemaSubject (resolvedSchemaParameterCount schema)))
        PredicateRequirementComponent provenance ->
            case [resolvedRequirementBody requirement
                 | requirement <- Map.elems (resolvedSchemaRequirements schema)
                 , Map.member provenance (resolvedRequirementOccurrences requirement)] of
                [requirement] -> Just requirement
                [] -> Nothing
                _ -> impossible "a normalized requirement origin has multiple bodies"
    pure (foldr (const (CForall TySet))
        (CImp (structurePredicateApplication registration) body)
        (() : map (const ()) (resolvedSchemaParameters schema)))
  where
    schema = pendingStructureSchema registration

structurePredicateDefinitionTarget :: PendingStructureRegistration -> CanonicalTerm ObjectId
structurePredicateDefinitionTarget = frozenCoreTerm . checkedPropositionTerm . structurePredicateDefinitionProposition

structurePredicateDefinitionProposition :: PendingStructureRegistration -> CheckedPropositionContent
structurePredicateDefinitionProposition
        (PendingStructureRegistration _ (CheckedStructurePredicateDefinition _ _ _ equation)) = equation

data AppliedStructurePredicate = AppliedStructurePredicate
    !PendingStructureRegistration !(CanonicalTerm ObjectId) ![CanonicalTerm ObjectId]

applyStructurePredicate
    :: PendingStructureRegistration -> CanonicalTerm ObjectId -> [CanonicalTerm ObjectId]
    -> Maybe AppliedStructurePredicate
applyStructurePredicate registration subject parameters = do
    guard (fromIntegral (length parameters) == resolvedSchemaParameterCount (pendingStructureSchema registration))
    pure (AppliedStructurePredicate registration subject parameters)

appliedStructureRegistration :: AppliedStructurePredicate -> PendingStructureRegistration
appliedStructureRegistration (AppliedStructurePredicate registration _ _) = registration

appliedStructureTerm :: AppliedStructurePredicate -> CanonicalTerm ObjectId
appliedStructureTerm (AppliedStructurePredicate registration subject parameters) =
    foldl' CApp (CGlobal (pendingStructurePredicate registration)) (subject : parameters)

appliedStructureShape :: AppliedStructurePredicate -> CanonicalTerm ObjectId
appliedStructureShape (AppliedStructurePredicate registration subject _) = Record.recordOpenShape
    [CGlobal (resolvedFieldSelector field) | field <- Map.elems (resolvedSchemaFields (pendingStructureSchema registration))] subject

appliedStructureRequirements :: AppliedStructurePredicate -> [CanonicalTerm ObjectId]
appliedStructureRequirements application =
    fst <$> appliedStructureRequirementOccurrences application

-- | Specialize once, retaining every origin of semantically deduplicated laws.
-- Occurrences are current presentation data, not part of the predicate.
appliedStructureRequirementOccurrences
    :: AppliedStructurePredicate
    -> [(CanonicalTerm ObjectId, Map RequirementProvenanceKey RequirementOccurrence)]
appliedStructureRequirementOccurrences application =
    [(specializeApplied application (resolvedRequirementBody requirement),
        resolvedRequirementOccurrences requirement)
    | key <- resolvedSchemaSemanticRequirementOrder schema
    , requirement <- maybeToList (Map.lookup key (resolvedSchemaRequirements schema))]
  where
    schema = pendingStructureSchema (appliedStructureRegistration application)

appliedStructureComponents :: AppliedStructurePredicate -> [CanonicalTerm ObjectId]
appliedStructureComponents application = specializeApplied application <$>
    structurePredicateComponents (pendingStructureSchema (appliedStructureRegistration application))

specializeApplied :: AppliedStructurePredicate -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
specializeApplied (AppliedStructurePredicate _ subject parameters) body =
    foldl' apply (foldr (const (CLam TySet)) body arguments) arguments
  where
    arguments = subject : parameters
    apply (CLam TySet remaining) argument = instantiateCanonical argument remaining
    apply _ _ = impossible "a checked structure application lost its binder telescope"

conjunction :: [CanonicalTerm global] -> CanonicalTerm global
conjunction = \case
    [] -> CTruth
    firstComponent : rest -> foldl' CAnd firstComponent rest
