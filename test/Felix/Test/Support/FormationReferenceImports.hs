{-# LANGUAGE NoImplicitPrelude #-}

-- Test-only bridge from declarations that passed the ordinary module checker.
-- No persisted join plan or production search index contributes to the oracle.
module Felix.Test.Support.FormationReferenceImports
    ( ImportedReferenceRule(..)
    , atomicConclusion
    , importedReferenceRules
    , referenceRulesFromBatches
    , prepareImportedReferenceRules
    , prepareProductionRuleDescriptions
    , importedReferenceTerm
    , equalReferenceCore
    , prepareImportedReferenceTerm
    , importedReferenceAtom
    ) where

import Base
import Data.List (filter)
import Control.Monad (foldM)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.Trans.Class (lift)
import Data.Functor.Identity (Identity(..))
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Record qualified as Record
import Felix.Checking.Notion (ConjunctionPath)
import Felix.Checking.Core qualified as Core
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Semantic
import Felix.Checking.Notion.Registration qualified as Registration
import Felix.Checking.Notion.Rule qualified as Rule
import Felix.Test.Support.FormationReference qualified as Reference
import Numeric.Natural (Natural)

-- The occurrence identifies the actual source; the ordinal identifies a
-- registration in this frozen test snapshot. Neither is proof authority.
data ImportedReferenceRule = ImportedReferenceRule
    { importedReferenceOccurrence :: !SemanticFactOccurrenceFingerprint
    , importedReferencePath :: !ConjunctionPath
    , importedReferenceRegistration :: !Reference.ReferenceRegistration
    , importedReferenceProposition :: !Identity.CheckedPropositionContent
    }

importedReferenceRules
    :: [Module.CompletedTypedModule] -> Either Text (Map Natural ImportedReferenceRule)
importedReferenceRules = referenceRulesFromBatches
    . concatMap (Commit.pendingModulePrefixBatches . Module.completedTypedModulePrefix)

referenceRulesFromBatches
    :: [Commit.CommittedDeclarationBatch] -> Either Text (Map Natural ImportedReferenceRule)
referenceRulesFromBatches batches = runIdentity (Except.runExceptT (referenceRulesFromBatchesWith (pure ()) batches))

prepareImportedReferenceRules
    :: [Module.CompletedTypedModule] -> Reference.Reference (Map Natural ImportedReferenceRule)
prepareImportedReferenceRules modules = do
    batches <- concat <$> for modules (\sealed -> Reference.chargeReferenceWork 1 >> pure
        (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)))
    either Reference.invalidReferenceInput pure =<< Except.runExceptT
        (referenceRulesFromBatchesWith (Reference.chargeReferenceWork 1) batches)

-- Compare the production compiler with the independent field-by-field oracle.
-- Resolve each occurrence from its own committed batch, including its actual
-- direct authorization, rather than inferring definition origin from syntax.
prepareProductionRuleDescriptions
    :: [Module.CompletedTypedModule]
    -> Reference.Reference (Map Natural (SemanticFactOccurrenceFingerprint, Reference.ReferenceRegistration))
prepareProductionRuleDescriptions modules = do
    let charge = Reference.chargeReferenceWork 1
        require message = maybe (Reference.invalidReferenceInput message) pure
    batches <- concat <$> for modules (\sealed -> charge >> pure
        (Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix sealed)))
    compiled <- fmap concat $ for batches \batch -> do
        charge
        let delta = Commit.committedBatchDelta batch
        facts <- referenceTable charge [(semanticFactFingerprint fact,fact) | fact <- declarationDeltaFacts delta]
        propositions <- referenceTable charge [(Identity.checkedPropositionId value,value) | value <- Commit.committedBatchPropositions batch]
        certificates <- referenceTable charge [(semanticFactFingerprint fact,certificate)
            | (fact,certificate) <- zip (declarationDeltaFacts delta) (Commit.committedBatchValidationCertificates batch)]
        let resolve occurrence = do
                charge
                fact <- require "production occurrence missing from its committed batch" (Map.lookup occurrence facts)
                proposition <- require "production proposition missing from its committed batch"
                    (Map.lookup (semanticFactProposition fact) propositions)
                certificate <- require "production source missing its certificate" (Map.lookup occurrence certificates)
                pure (proposition,Authority.validationDirectAuthorization certificate)
        entries <- Registration.compileRegistrationRules (Reference.chargeReferenceWork . fromIntegral) resolve
            (filter atomicConclusion (declarationDeltaRegistrations delta))
            >>= either (Reference.invalidReferenceInput . fromString . show) pure
        for entries \(occurrence,entry) -> do
            charge
            let (arity,premises,conclusion) = Rule.ruleDescription (Rule.registeredRule entry)
                atom = case conclusion of
                    AtomicLeaf value -> value
                    WholeLeaf{} -> error "atomic reference compiler received a whole conclusion"
                description = Reference.ReferenceRule arity premises atom Set.empty
                result = case entry of
                    Rule.RegisteredClassification{} -> Reference.ClassificationRule description
                    Rule.RegisteredDefinition{} -> Reference.DefinitionRule description
            pure (occurrence,result)
    pure (Map.fromList (zip [0..] compiled))

referenceRulesFromBatchesWith
    :: Monad m => m () -> [Commit.CommittedDeclarationBatch]
    -> Except.ExceptT Text m (Map Natural ImportedReferenceRule)
referenceRulesFromBatchesWith charge batches = Map.fromList . zip [0..] . concat <$> traverse fromBatch batches
  where
    fromBatch batch = do
        lift charge
        let delta = Commit.committedBatchDelta batch
        facts <- referenceTable (lift charge)
            [(semanticFactFingerprint fact, fact) | fact <- declarationDeltaFacts delta]
        propositions <- referenceTable (lift charge)
            [(Identity.checkedPropositionId proposition, proposition)
            | proposition <- Commit.committedBatchPropositions batch]
        certificates <- referenceTable (lift charge)
            [(semanticFactFingerprint fact, certificate)
            | (fact, certificate) <- zip (declarationDeltaFacts delta)
                (Commit.committedBatchValidationCertificates batch)]
        let source fingerprint = do
                fact <- require "registered occurrence missing from its own sealed declaration"
                    (Map.lookup fingerprint facts)
                proposition <- require "registered proposition missing from its sealed declaration"
                    (Map.lookup (semanticFactProposition fact) propositions)
                certificate <- require "registered source has no checked certificate"
                    (Map.lookup fingerprint certificates)
                pure (proposition, Authority.validationDirectAuthorization certificate)
            build definitional branch premises conclusion = do
                let fingerprint = semanticFactBranchFact branch
                (proposition, direct) <- source fingerprint
                lift charge
                arity <- telescope (Core.frozenCoreTerm (Identity.checkedPropositionTerm proposition))
                let rule = Reference.ReferenceRule arity premises conclusion Set.empty
                    registration = if definitional direct
                        then Reference.DefinitionRule rule else Reference.ClassificationRule rule
                pure (ImportedReferenceRule fingerprint (semanticFactBranchPath branch) registration proposition)
        for (filter atomicConclusion (declarationDeltaRegistrations delta)) \registration ->
          let branch = registrationBranch registration
          in case registrationBody registration of
            RegisterNotionView view -> case notionViewConclusion view of
                AtomicLeaf atom -> build definitionOrigin branch
                    [RulePremiseAtom (viewPremise (notionViewPremise view))] atom
                WholeLeaf{} -> error "atomic reference compiler received a whole view"
            RegisterNullaryProvider rule ->
                build (const False) branch []
                    (GlobalAtomTemplate (nullaryConclusion rule)
                        (Vector.singleton (TemplateProvider
                            (IntrinsicSourceProvider (nullaryProvider rule)) Vector.empty)))
            RegisterProviderResult rule -> do
                let provider = providerResultProvider rule
                    value = TemplateProvider (resultProviderTemplateHead provider) (resultProviderTemplateArguments provider)
                    result = fmap (\case ResultRuleTerm term -> term; ResultRuleProviderValue -> value)
                        (providerResultConclusion rule)
                    premises = case providerResultPremises rule of
                        ProviderResultUnconditional -> []
                        ProviderResultGuarded bundles -> forest bundles
                build (const False) branch premises result
            RegisterBackwardNotion rule ->
                build (const False) branch
                    (forest (backwardNotionPremises rule)) (backwardNotionConclusion rule)
            RegisterFiniteEvidence rule -> do
                let skeleton = finiteEvidenceSkeleton rule
                build (const False) branch
                    (checkedNotionRulePremises skeleton) (checkedNotionRuleConclusion skeleton)
            RegisterGraphDomain rule -> do
                let left = TemplateVariable (graphDomainLeft rule)
                    right = TemplateVariable (graphDomainRight rule)
                    graph = TemplateVariable (graphDomainGraph rule)
                build (const False) branch
                    [RulePremiseAtom (MembershipAtomTemplate (TemplateOrderedPair left right) graph)]
                    (MembershipAtomTemplate left (TemplateProvider (graphDomainProvider rule) (Vector.singleton graph)))
            RegisterWholeConclusion{} -> error "atomic reference compiler received a whole classification"

    -- This is read only after ordinary declaration authorization. Implication
    -- syntax and an ordinary no-ATP certificate cannot confer definition origin.
    definitionOrigin = \case
        Authority.CheckedKernelConstruction Authority.CheckedDefinitionProjection{} -> True
        Authority.CheckedKernelConstruction
            (Authority.CheckedStructureLaw Authority.StructurePredicateComponent) -> True
        _ -> False
    telescope term = do
        lift charge
        case term of
            Core.CForall Core.TySet body -> (1 +) <$> telescope body
            _ -> pure 0
    forest (RulePremiseBundles trees) = toList trees
    viewPremise = \case
        GlobalNotionViewPremise head' terms -> GlobalAtomTemplate head' terms
        StructureNotionViewPremise head' terms -> StructureAtomTemplate head' terms
        ExactProviderMembershipPremise element provider arguments ->
            MembershipAtomTemplate element (TemplateProvider provider arguments)
    require message = maybe (Except.throwE message) pure

-- Interpret only the owner-preserving provider syntax supplied by the admitted
-- registrations. The caller owns opaque leaves and their current lexical scope.
importedReferenceTerm
    :: Identity.CheckedObjectClosure
    -> [Module.CompletedTypedModule]
    -> (Reference.OpaqueSeed -> Core.CanonicalTerm Identity.ObjectId)
    -> Reference.GroundTerm
    -> Either Text (Core.CanonicalTerm Identity.ObjectId)
importedReferenceTerm closure modules seed term = runIdentity (Except.runExceptT
    (interpretReferenceTerm (pure ()) (\argument body -> pure (Core.instantiateCanonical argument body))
        closure (Map.fromList (referenceBindings modules)) (Map.fromList (referenceFields modules)) seed term))

referenceBindings :: [Module.CompletedTypedModule] -> [(GlobalBindingRef, SemanticGlobalBinding)]
referenceBindings = runIdentity . referenceBindingsWith (pure ())

referenceBindingsWith
    :: Monad m => m () -> [Module.CompletedTypedModule] -> m [(GlobalBindingRef, SemanticGlobalBinding)]
referenceBindingsWith charge modules = concat <$> for modules (\sealed -> do
    charge
    concat <$> for (semanticInterfaceDeclarations (Module.sealedTypedModuleSemantic (Module.completedTypedModuleSealed sealed))) (\delta -> do
        charge
        for (semanticEnvironmentBindings (declarationDeltaEnvironment delta)) (\binding -> do
            charge
            pure (globalBindingRef (declarationDeltaSlot delta) (semanticGlobalBindingKey binding), binding))))

referenceFields :: [Module.CompletedTypedModule] -> [(Identity.FieldId, Identity.ObjectId)]
referenceFields = runIdentity . referenceFieldsWith (pure ())

referenceFieldsWith
    :: Monad m => m () -> [Module.CompletedTypedModule] -> m [(Identity.FieldId, Identity.ObjectId)]
referenceFieldsWith charge modules = concat <$> for modules (\sealed -> do
    charge
    concat <$> for (Declaration.evidenceLocalStructureSchemas (Module.sealedTypedModuleEvidence (Module.completedTypedModuleSealed sealed))) (\schema -> do
        charge
        for (Map.elems (Schema.resolvedSchemaFields schema)) (\field -> do
            charge
            pure (Schema.resolvedFieldIdentity field, Schema.resolvedFieldProjection field))))

referenceTable :: (Monad m, Ord key) => m () -> [(key, value)] -> m (Map key value)
referenceTable charge = foldM (\entries (key, value) -> charge >> pure (Map.insert key value entries)) Map.empty

-- Prepare once, then interpret all requested terms within the same account.
prepareImportedReferenceTerm
    :: Identity.CheckedObjectClosure -> [Module.CompletedTypedModule]
    -> (variable -> Core.CanonicalTerm Identity.ObjectId)
    -> Reference.Reference (SetTermTemplate variable -> Reference.Reference (Core.CanonicalTerm Identity.ObjectId))
prepareImportedReferenceTerm closure modules seed = do
    bindings <- referenceBindingsWith (Reference.chargeReferenceWork 1) modules
        >>= referenceTable (Reference.chargeReferenceWork 1)
    fields <- referenceFieldsWith (Reference.chargeReferenceWork 1) modules
        >>= referenceTable (Reference.chargeReferenceWork 1)
    pure (\term -> either Reference.invalidReferenceInput pure =<< Except.runExceptT
        (interpretReferenceTerm (Reference.chargeReferenceWork 1) instantiate closure bindings fields seed term))
  where
    instantiate argument body = Reference.countedReferenceOperation \allowance ->
        let (result, after) = Core.countedInstantiateCanonical allowance argument body
        in (first coreWorkFailure result, after)

equalReferenceCore
    :: Core.CanonicalTerm Identity.ObjectId -> Core.CanonicalTerm Identity.ObjectId -> Reference.Reference Bool
equalReferenceCore left right = Reference.countedReferenceOperation \allowance ->
    let (result, after) = Core.countedCanonicalIdentity allowance left right
    in (first coreWorkFailure result, after)

coreWorkFailure :: Core.CountedCoreFailure Void -> Reference.ReferenceFailure
coreWorkFailure Core.CountedCoreStructuralWorkExhausted = Reference.ReferenceWorkExhausted

interpretReferenceTerm
    :: Monad m
    => m ()
    -> (Core.CanonicalTerm Identity.ObjectId -> Core.CanonicalTerm Identity.ObjectId -> m (Core.CanonicalTerm Identity.ObjectId))
    -> Identity.CheckedObjectClosure
    -> Map GlobalBindingRef SemanticGlobalBinding
    -> Map Identity.FieldId Identity.ObjectId
    -> (variable -> Core.CanonicalTerm Identity.ObjectId)
    -> SetTermTemplate variable -> Except.ExceptT Text m (Core.CanonicalTerm Identity.ObjectId)
interpretReferenceTerm charge instantiate closure bindings fields seed = go
  where
    go term = do
        lift charge
        case term of
            TemplateClosed value -> pure (closedSetValueTerm value)
            TemplateVariable variable -> pure (seed variable)
            TemplateOrderedPair left right -> Core.CApp
                <$> (Core.CApp (Core.CIntrinsic Core.OrderedPair) <$> go left) <*> go right
            TemplateProvider provider terms -> do
                arguments <- traverse go terms
                case provider of
                    GlobalSourceProvider reference -> do
                        binding <- maybe (Except.throwE "reference provider is outside the admitted module graph") pure
                            (Map.lookup reference bindings)
                        case semanticGlobalBindingTarget binding of
                            GlobalReference identity -> foldM applyGlobal (Core.CGlobal identity) arguments
                            TransparentExpansion identity -> case Identity.lookupCheckedObjectContent identity closure of
                                Just (Identity.TransparentObjectContent _ _ body) -> foldM apply body arguments
                                _ -> Except.throwE "reference provider has no transparent body"
                            ContextualTransparentExpansion{} -> Except.throwE "contextual providers cannot enter a registration"
                    StructureFieldSourceProvider field projection
                        | Map.lookup field fields == Just projection -> foldM applyGlobal (Core.CGlobal projection) arguments
                        | otherwise -> Except.throwE "reference field provider is outside the admitted module graph"
                    IntrinsicSourceProvider intrinsic -> maybe (Except.throwE "invalid intrinsic reference arity") pure
                        (intrinsicProviderApplication intrinsic arguments)
                    FiniteSetLiteralSourceProvider -> case toList arguments of
                        element : rest -> pure (finiteSetLiteralProviderApplication (element :| rest))
                        [] -> Except.throwE "empty finite literal in reference registration"
    apply (Core.CLam Core.TySet body) argument = lift charge >> lift (instantiate argument body)
    apply function argument = applyGlobal function argument
    applyGlobal function argument = lift charge >> pure (Core.CApp function argument)

-- Interpret atom labels independently of whichever proof the reference chose.
-- Notion occurrence order is not always the predicate's Core binding order.
importedReferenceAtom
    :: [Module.CompletedTypedModule]
    -> (Reference.GroundTerm -> Either Text (Core.CanonicalTerm Identity.ObjectId))
    -> Reference.GroundAtom -> Either Text (Core.CanonicalTerm Identity.ObjectId)
importedReferenceAtom modules term = go
  where
    bindings = Map.fromList
        [(globalBindingRef (declarationDeltaSlot delta) (semanticGlobalBindingKey binding), binding)
        | sealed <- modules
        , delta <- semanticInterfaceDeclarations (Module.sealedTypedModuleSemantic (Module.completedTypedModuleSealed sealed))
        , binding <- semanticEnvironmentBindings (declarationDeltaEnvironment delta)]
    structures = Map.fromList (concatMap
        (Declaration.evidenceLocalStructurePredicates . Module.sealedTypedModuleEvidence . Module.completedTypedModuleSealed) modules)
    go = \case
        NegativeAtomTemplate body -> Core.CNot <$> go body
        GlobalAtomTemplate head' terms -> do
            let reference = globalNotionHeadReference head'
                key = globalBindingRefKey reference
            binding <- maybe (Left "reference predicate is outside the admitted module graph") Right
                (Map.lookup reference bindings)
            if globalNotionHeadMatchesKey head' key then pure ()
                else Left "reference predicate has the wrong notion family"
            arguments <- maybe (Left "reference predicate arguments do not match its binding") Right
                (globalNotionBindingArguments key terms) >>= traverse term
            pure (foldl' Core.CApp (Core.CGlobal (semanticGlobalTargetObject
                (semanticGlobalBindingTarget binding))) arguments)
        StructureAtomTemplate head' terms -> do
            predicate <- maybe (Left "reference structure predicate is outside the admitted module graph") Right
                (Map.lookup (structureNotionHeadId head') structures)
            arguments <- traverse term terms
            pure (foldl' Core.CApp (Core.CGlobal predicate) arguments)
        ExactStructureAtomTemplate shape subject -> do
            let schemas = concatMap (Declaration.evidenceLocalStructureSchemas . Module.sealedTypedModuleEvidence . Module.completedTypedModuleSealed) modules
            if any ((== shape) . semanticRecordShapeKey) schemas then pure ()
                else Left "reference exact shape is outside the admitted module graph"
            Record.recordExactShape (Core.CGlobal <$> semanticRecordShapeSelectors shape) <$> term subject
        MembershipAtomTemplate element set -> Core.CApp
            <$> (Core.CApp (Core.CIntrinsic Core.Member) <$> term element) <*> term set

-- This oracle covers the atomic fragment. Whole conclusions have separate
-- consumer/replay cases and must not be silently represented as atomic rows.
atomicConclusion :: Registration fact -> Bool
atomicConclusion registration = case registrationBody registration of
    RegisterWholeConclusion{} -> False
    RegisterNotionView view -> case notionViewConclusion view of
        WholeLeaf{} -> False
        AtomicLeaf{} -> True
    _ -> True
