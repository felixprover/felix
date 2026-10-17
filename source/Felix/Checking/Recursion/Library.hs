{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}

-- | Resolve the ordinary library interface used by structural recursion.
-- Names discover candidates; canonical definition associations and exact
-- theorem targets establish which checked operations and laws are being used.
module Felix.Checking.Recursion.Library
    ( RecursionLibrary(..)
    , LoadedDatatype(..)
    , loadCheckedDatatype
    , ImportedLaw
    , loadRecursionLibrary
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Recursion.Construction qualified as Recursion
import Felix.Checking.GlobalTyping (GlobalTyping, lookupGlobalType)
import Felix.Checking.Identity
import Felix.Checking.Recursion.Graph qualified as Graph
import Felix.Checking.Recursion.Relation qualified as Relation
import Felix.Checking.Semantic

import Control.Monad (unless)
import Control.Monad.Except qualified as Except
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text

type ImportedLaw = (SemanticFactOccurrenceFingerprint, FrozenCheckedCore ObjectId)

data RecursionLibrary = RecursionLibrary
    { libraryOperations :: !Graph.GraphOperations
    , libraryRelationLaws :: !(Relation.RelationLaws ImportedLaw)
    , libraryGraphLaws :: !(Graph.GraphLaws ImportedLaw)
    }

data LoadedDatatype = LoadedDatatype
    { loadedDatatypeBinding :: !ResolvedGlobalBinding
    , loadedDatatypeParameterCount :: !Int
    , loadedDatatypeCarrier :: !ObjectId
    , loadedDatatypeClauses :: !(NonEmpty Datatype.Clause)
    , loadedDatatypeCases :: !ImportedLaw
    , loadedDatatypeInduction :: !ImportedLaw
    , loadedDatatypeConstructorLaws :: !(NonEmpty (Recursion.ConstructorLaws ImportedLaw))
    }

loadCheckedDatatype :: ResolvedGlobalBinding -> Declaration.LoweringDriver (Either Text LoadedDatatype)
loadCheckedDatatype binding = Except.runExceptT do
    let declaration = resolvedBindingDeclaration binding
    descriptor <- maybe (Except.throwError "structural domain is not a checked datatype") pure
        (semanticGlobalBindingDatatype declaration)
    carrier <- reference declaration
    closure <- Trans.lift Declaration.checkedObjectClosureLowering
    let typing = globalTypingFromClosure closure
    parameterCount <- case lookupGlobalType typing carrier >>= firstOrderSymbolShape of
        Just (count,TySet) -> pure count
        _ -> Except.throwError "checked datatype carrier has an incompatible type"
    let descriptions = datatypeDescriptorCases descriptor
        indices = Map.fromList (zip (datatypeCaseConstructor <$> toList descriptions) [0 ..])
    clauses <- for descriptions \description -> do
        resolved <- Trans.lift (Declaration.resolveVisibleGlobalLowering (datatypeCaseConstructor description))
            >>= maybe (Except.throwError "checked datatype constructor is not visible") (pure . fst)
        object <- reference (resolvedBindingDeclaration resolved)
        premises <- for (datatypeCasePremises description) \case
            DatatypeRecursivePremise -> pure Datatype.Recursive
            DatatypeFixedPremise term -> Datatype.FixedDomain <$> Except.liftEither
                (first (Text.pack . show) (checkScopedCanonicalCore typing (replicate parameterCount TySet) term))
        pure (Datatype.Clause object (datatypeCaseFields description) premises)
    laws <- for descriptions \description -> Recursion.ConstructorLaws
        <$> checkedFact (datatypeCaseIntroductionFact description)
        <*> traverse checkedFact (datatypeCaseInjectivityFact description)
        <*> for (datatypeCaseDistinctnessFacts description) (\(key,fingerprint) -> do
            index <- maybe (Except.throwError "datatype distinctness has no constructor") pure (Map.lookup key indices)
            (index,) <$> checkedFact fingerprint)
    cases <- checkedFact (datatypeDescriptorCasesFact descriptor)
    induction <- checkedFact (datatypeDescriptorPredicateInductionFact descriptor)
    pure (LoadedDatatype binding parameterCount carrier clauses cases induction laws)
  where
    reference declaration = case semanticGlobalBindingTarget declaration of
        GlobalReference object -> pure object
        _ -> Except.throwError "checked datatype binding has no ordinary object"
    checkedFact fingerprint = do
        proposition <- Trans.lift (Declaration.resolveVisibleFactLowering fingerprint)
            >>= maybe (Except.throwError "checked datatype law is not visible") pure
        pure (fingerprint,checkedPropositionTerm proposition)

type Load = Except.ExceptT Text Declaration.LoweringDriver

loadRecursionLibrary :: Declaration.LoweringDriver (Either Text RecursionLibrary)
loadRecursionLibrary = Except.runExceptT do
    closure <- Trans.lift Declaration.checkedObjectClosureLowering
    let typing = globalTypingFromClosure closure
        sets n result = foldr (const (TyArrow TySet)) result [1 .. n :: Int]
        relationType = sets 2 TyProp
        stepType = sets 3 TyProp
        operation = loadOperation typing
    relations <- Relation.RelationOperations
        <$> operation "logical_relation_on" (TyArrow TySet (TyArrow relationType TySet))
        <*> operation "subseteq" (sets 2 TyProp)
        <*> operation "times" (sets 2 TySet)
        <*> operation "relation" (sets 1 TyProp)
        <*> operation "well_founded_on" (sets 2 TyProp)
    operations <- Graph.GraphOperations relations
        <$> operation "unbounded_relational_well_founded_recursion_op" (sets 2 (TyArrow stepType TySet))
        <*> operation "unbounded_recursive_relation_step_op" (sets 2 (TyArrow stepType TyProp))
        <*> operation "unbounded_recursive_history_op" (sets 4 TyProp)
        <*> operation "recursive_set_function_op" (sets 1 TyProp)
        <*> operation "apply" (sets 2 TySet)
        <*> operation "dom" (sets 1 TySet)
        <*> operation "restrl" (sets 2 TySet)
        <*> operation "downward_closure" (sets 2 TySet)
    let expectedRelations = Relation.relationSupportTargets relations
        expectedGraphs = Graph.graphSupportTargets operations
        law name target = do
            expected <- Except.liftEither (first (Text.pack . show) (checkCanonicalCore typing target))
            actual@(_, checked) <- loadFact name
            unless (checked == expected)
                (Except.throwError ("recursion support theorem has an incompatible target: " <> name))
            pure actual
    relationLaws <- Relation.RelationLaws
        <$> law "logical_relation_on_membership" (Relation.relationMembership expectedRelations)
        <*> law "logical_relation_on_subseteq" (Relation.relationBound expectedRelations)
        <*> law "binary_relation_is_relation" (Relation.binaryRelation expectedRelations)
        <*> law "well_founded_on_from_induction" (Relation.inductionConverse expectedRelations)
    graphLaws <- Graph.GraphLaws
        <$> law "unbounded_recursive_relation_step_iff" (Graph.stepCharacterization expectedGraphs)
        <*> law "unbounded_relational_well_founded_recursion_function" (Graph.recursionFunction expectedGraphs)
        <*> law "unbounded_relational_well_founded_recursion_domain" (Graph.recursionDomain expectedGraphs)
        <*> law "unbounded_relational_well_founded_recursion_specification" (Graph.recursionSpecification expectedGraphs)
        <*> law "restrl_apply" (Graph.restrictionApply expectedGraphs)
        <*> law "downward_closure_iff" (Graph.predecessorMembership expectedGraphs)
        <*> law "function_apply_default" (Graph.graphDefault expectedGraphs)
    pure (RecursionLibrary operations relationLaws graphLaws)

loadFact :: Text -> Load ImportedLaw
loadFact name = do
    fingerprint <- Trans.lift (Declaration.resolveVisibleFactAliasLowering (semanticName name))
        >>= maybe (Except.throwError ("structural recursion requires recursion/well-founded-relation.tex; missing " <> name)) pure
    proposition <- Trans.lift (Declaration.resolveVisibleFactLowering fingerprint)
        >>= maybe (Except.throwError ("recursion support reference is unavailable: " <> name)) pure
    pure (fingerprint,checkedPropositionTerm proposition)

loadOperation :: GlobalTyping ObjectId -> Text -> CoreType -> Load ObjectId
loadOperation typing name expectedType = do
    (fingerprint,definition) <- loadFact name
    object <- maybe (Except.throwError ("recursion support definition has no ordinary head: " <> name)) pure
        (headObject (frozenCoreTerm definition))
    unless (lookupGlobalType typing object == Just expectedType)
        (Except.throwError ("recursion support operation has an incompatible type: " <> name))
    views <- Trans.lift (Declaration.resolveVisibleDefinitionViewsLowering object)
    unless (any ((== fingerprint) . Declaration.resolvedDefinitionViewFingerprint) views)
        (Except.throwError ("recursion support operation lacks checked definition ownership: " <> name))
    pure object
  where
    headObject (CForall _ body) = headObject body
    -- A named set construction publishes its membership characterization.
    -- The association check above, not this syntactic discovery, owns the view.
    headObject (CEq TyProp (CApp (CApp (CIntrinsic Member) _) set) _) = applicationHead set
    headObject (CEq _ left _) = applicationHead left
    headObject _ = Nothing
    applicationHead (CApp function _) = applicationHead function
    applicationHead (CGlobal object) = Just object
    applicationHead _ = Nothing
