{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Recursion (unitTests) where

import Base hiding (Empty, empty)
import Felix.Checking.Authority qualified as Authority
import Felix.Test.Unit.RecursionIntegration qualified as Integration
import Felix.Checking.Planning
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Recursion.Construction qualified as Recursion
import Felix.Checking.Recursion.Relation qualified as Relation
import Felix.Checking.Recursion.Graph qualified as Graph
import Felix.Checking.Recursion.Proposition qualified as Proposition
import Felix.Checking.Recursion.Library qualified as Library
import Felix.Checking.Recursion.Prepared qualified as Prepared
import Felix.Checking.Recursion.Named qualified as Named
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Module qualified as Module
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Test.Unit.Module.Support (compileFixture)
import Felix.Module
import Felix.Source
import Felix.Math.Codec (hashBlake2b256)

import Control.Monad (foldM)
import Data.Vector qualified as Vector
import Data.Map.Strict qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Structural recursion construction"
    [ testCase "replays construction from checked datatype laws" recursionPrerequisites
    , testCase "replays truth-value encoding and the false default" truthValues
    , Integration.tests
    ]

right :: Show e => Either e a -> IO a
right = either (fail . show) pure

recursionPrerequisites :: Assertion
recursionPrerequisites = for_
    [ "test/phase5/datatype-formation.tex"
    , "test/phase5/datatype-family.tex"
    , "test/phase5/datatype-empty.tex"
    , "test/phase5/datatype-nullary.tex"
    , "test/phase5/datatype-premises.tex"
    , "test/phase5/datatype-recursive-witness.tex"
    ] \fixture -> do
        (foundation, _, _, modules) <- compileFixture fixture
        let batches = concatMap (Commit.pendingModulePrefixBatches . Module.completedTypedModulePrefix) modules
            objects = concatMap Commit.committedBatchObjects batches
            bindings = concatMap (Semantic.semanticEnvironmentBindings . Semantic.declarationDeltaEnvironment . Commit.committedBatchDelta) batches
            owners = Map.fromList [(Semantic.semanticGlobalBindingKey binding,Semantic.declarationDeltaSlot delta)
                | batch <- batches, let delta = Commit.committedBatchDelta batch
                , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)]
            byRef = Map.fromList [(Semantic.globalBindingRef owner key,binding) | binding <- bindings
                , let key = Semantic.semanticGlobalBindingKey binding, Just owner <- [Map.lookup key owners]]
            byKey = Map.fromList [(Semantic.semanticGlobalBindingKey binding, binding) | binding <- bindings]
            propositions = Map.fromList [(Identity.checkedPropositionId value, Identity.checkedPropositionTerm value)
                | batch <- batches, value <- Commit.committedBatchPropositions batch]
            facts = Map.fromList [(Semantic.semanticFactFingerprint fact, Semantic.semanticFactProposition fact)
                | batch <- batches, fact <- Semantic.declarationDeltaFacts (Commit.committedBatchDelta batch)]
            reference binding = case Semantic.semanticGlobalBindingTarget binding of
                Semantic.GlobalReference object -> pure object
                _ -> fail "a datatype is not a global reference"
            require key table = maybe (fail "checked datatype dependency is missing") pure (Map.lookup key table)
        (supportObjects, operations) <- libraryOperations (Identity.theoryId foundation)
        closure <- right (Identity.validateObjectClosure (Identity.theoryId foundation) (objects <> supportObjects))
        let typing = Identity.globalTypingFromClosure closure
            root = Proof.rootProofContext foundation typing
            relations = Graph.graphRelationOperations operations
        relationContracts <- traverse (right . checkCanonicalCore typing) (Relation.relationSupportTargets relations)
        graphContracts <- traverse (right . checkCanonicalCore typing) (Graph.graphSupportTargets operations)
        relative <- right (safeRelativePath "recursion-laws.tex")
        let supportOwner = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 "recursion-laws")) relative
            port target = (Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
                (Semantic.factSlot supportOwner (localFactOrdinal 0))
                (Authority.factAuthority (Identity.theoremRef (Identity.theoryId foundation)
                    (Identity.propositionIdOf (frozenCoreTerm target))) Authority.cleanAuthoritySafety),target)
            library = Library.RecursionLibrary operations (port <$> relationContracts) (port <$> graphContracts)
        for_ [(binding, descriptor) | binding <- bindings, Just descriptor <- [Semantic.semanticGlobalBindingDatatype binding]]
            \(binding, descriptor) -> do
                carrier <- reference binding
                checkedCarrier <- right (checkCanonicalCore typing (CGlobal carrier))
                let arity TySet = 0
                    arity (TyArrow TySet rest) = 1 + arity rest
                    arity _ = error "invalid checked datatype arity"
                    parameterCount = arity (frozenCoreType checkedCarrier)
                    descriptions = Semantic.datatypeDescriptorCases descriptor
                    caseIndices = Map.fromList (zip (Semantic.datatypeCaseConstructor <$> toList descriptions) [0 ..])
                    fingerprints = toList descriptor
                imports <- for fingerprints \fingerprint -> require fingerprint facts >>= \identity -> require identity propositions
                let indexed = Map.fromList (zip fingerprints (zip (importIx <$> [0 ..]) imports))
                cases <- require (Semantic.datatypeDescriptorCasesFact descriptor) indexed
                clauses <- for descriptions \description -> do
                    object <- require (Semantic.datatypeCaseConstructor description) byKey >>= reference
                    domains <- for (Semantic.datatypeCasePremises description) \case
                        Semantic.DatatypeRecursivePremise -> pure Datatype.Recursive
                        Semantic.DatatypeFixedPremise term -> Datatype.FixedDomain
                            <$> right (checkScopedCanonicalCore typing (replicate parameterCount TySet) term)
                    pure (Datatype.Clause object (Semantic.datatypeCaseFields description) domains)
                laws <- for descriptions \description -> Recursion.ConstructorLaws
                    <$> require (Semantic.datatypeCaseIntroductionFact description) indexed
                    <*> traverse (`require` indexed) (Semantic.datatypeCaseInjectivityFact description)
                    <*> traverse (\(key, fingerprint) -> (,) <$> require key caseIndices <*> require fingerprint indexed)
                        (Semantic.datatypeCaseDistinctnessFacts description)
                let imported fingerprint = (fingerprint,snd (indexed Map.! fingerprint))
                owner <- require (Semantic.semanticGlobalBindingKey binding) owners
                resolved <- right (Semantic.materializeResolvedGlobalBinding (`Map.lookup` byRef) (const Nothing) closure owner binding)
                let loaded = Library.LoadedDatatype resolved parameterCount carrier clauses
                        (imported (Semantic.datatypeDescriptorCasesFact descriptor))
                        (imported (Semantic.datatypeDescriptorPredicateInductionFact descriptor))
                        (fmap (\(index,target) -> (fromMaybe (impossible "test datatype import disappeared") (nth (importIxValue index) fingerprints),target)) <$> laws)
                    external = Map.fromList (toList (Library.libraryRelationLaws library)
                        <> toList (Library.libraryGraphLaws library) <> (imported <$> fingerprints))
                for_ [TySet,TyProp] \resultType -> do
                    prepared <- right (Prepared.prepareRecursor foundation closure resultType library loaded)
                    let fixedTypes = replicate (parameterCount + 1) TySet
                        instanceArguments = fromIntegral <$> reverse [1 .. parameterCount]
                    header <- right (checkScopedCanonicalCore typing fixedTypes (CEq TySet (CBound 0) (CIntrinsic Empty)))
                    fixedBranches <- for clauses \clause -> do
                        let recursive = length (Recursion.recursiveSlots clause)
                            binderTypes = replicate (length (Datatype.clauseArgumentSlots clause)) TySet
                                <> replicate recursive resultType
                            value = case resultType of
                                TyProp | recursive > 0 -> CNot (CBound 0)
                                TyProp -> CTruth
                                _ | recursive > 0 -> CApp (CApp (CIntrinsic PairSet) (CBound 0)) (CBound 0)
                                _ -> CIntrinsic Empty
                        right (checkScopedCanonicalCore typing fixedTypes (foldr CLam value binderTypes))
                    named <- right (Named.prepareNamedRecursor foundation closure library loaded
                        resultType (parameterCount + 1) instanceArguments [header] fixedBranches)
                    unguarded <- right (Named.prepareNamedRecursor foundation closure library loaded
                        resultType (parameterCount + 1) instanceArguments [] fixedBranches)
                    assertEqual "only predicate headers change the transparent body"
                        (resultType == TySet) (Named.namedRecursorObject named == Named.namedRecursorObject unguarded)
                    for_ [(Prepared.preparedRecursorObjects prepared,Prepared.preparedRecursorFacts prepared),
                          (Named.namedRecursorObjects named,Named.namedRecursorFacts named),
                          (Named.namedRecursorObjects unguarded,Named.namedRecursorFacts unguarded)] \(objectsToReplay,factsToReplay) -> do
                        preparedClosure <- right (Identity.extendObjectClosure closure objectsToReplay)
                        let preparedTyping = Identity.globalTypingFromClosure preparedClosure
                            targets = Prepared.recursorFactTarget <$> factsToReplay
                        for_ (zip [0 ..] factsToReplay) \(ordinal,fact) ->
                            case Prepared.recursorFactEvidence fact of
                                Prepared.RecursorDefinition object -> case Identity.lookupCheckedObjectContent object preparedClosure of
                                    Just (Identity.TransparentObjectContent _ ty body) ->
                                        assertEqual "definition recipe owns the exact transparent body"
                                            (canonicalDefinitionEquationTarget object ty body) (frozenCoreTerm (Prepared.recursorFactTarget fact))
                                    _ -> assertFailure "recursor definition object is missing"
                                Prepared.RecursorDerivation dependencies derivation -> do
                                    required <- for dependencies \case
                                        EnvironmentOccurrenceReference fingerprint -> require fingerprint external
                                        LocalCandidateReference (PlannedCandidatePosition stage index) -> do
                                            assertBool "recursor references only earlier singleton stages" (stage < ordinal && index == 0)
                                            maybe (fail "recursor stage is missing") pure (nth stage targets)
                                    assumptions <- traverse (right . derivationImportJudgement) required
                                    checked <- either (fail . ((fixture <> " prepared fact " <> show ordinal <> ": ") <>) . show) pure
                                        (replayKernelDerivation foundation defaultKernelReplayLimits preparedTyping (Vector.fromList assumptions)
                                            (Prepared.recursorFactTarget fact) derivation)
                                    assertEqual "prepared recursor target" (Prepared.recursorFactTarget fact) (replayedKernelTarget checked)
                let branchTypes = Recursion.branchType <$> toList clauses
                    types = replicate parameterCount TySet <> branchTypes
                    branchCount = length branchTypes
                    parameters = CBound . fromIntegral <$> reverse [branchCount .. length types - 1]
                    branches = CBound <$> (fromIntegral (branchCount - 1) :| (fromIntegral <$> reverse [0 .. branchCount - 2]))
                    d = foldl' CApp (CGlobal carrier) parameters
                expected <- right (Recursion.branchFunctionalityTarget (length types) d clauses branches)
                target <- right (checkCanonicalCore typing (foldr CForall expected types))
                proof <- right (Proof.introduceForalls root types \context ->
                    Recursion.proveBranchFunctionality context parameters d clauses branches cases laws)
                judgements <- traverse (right . derivationImportJudgement) imports
                result <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                    (Vector.fromList judgements) target (Proof.builtProofDerivation proof))
                assertEqual fixture target (replayedKernelTarget result)
                induction <- require (Semantic.datatypeDescriptorPredicateInductionFact descriptor) indexed
                inductionBody <- right (Recursion.subtermInductionTarget (length types) d clauses)
                inductionTarget <- right (checkCanonicalCore typing (foldr CForall inductionBody types))
                inductionProof <- right (Proof.introduceForalls root types \context ->
                    Recursion.proveSubtermInduction context parameters d clauses induction laws)
                inductionResult <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                    (Vector.fromList judgements) inductionTarget (Proof.builtProofDerivation inductionProof))
                assertEqual (fixture <> " subterm induction") inductionTarget (replayedKernelTarget inductionResult)
                -- A second logical function with the same guarded equations
                -- agrees on the carrier, for both Set and Prop results.
                for_ [TySet,TyProp] \resultType -> do
                    let branchTypes' = Recursion.branchTypeFor resultType <$> toList clauses
                        prefix = replicate parameterCount TySet <> branchTypes'
                        count = length prefix
                        contextTypes = prefix <> [TyArrow TySet resultType,TyArrow TySet resultType]
                        shift = shiftCanonical 2 0
                        d' = shift d
                        parameters' = shift <$> parameters
                        branches' = shift <$> branches
                        left = CBound 1
                        rightFunction = CBound 0
                    equations <- right (sequence
                        [Recursion.constructorEquationTarget resultType (count + 2) d' clause branch evaluator
                        | (clause,branch) <- zip (toList clauses) (toList branches')
                        , evaluator <- [left,rightFunction]])
                    let premises = foldr1 CAnd equations
                        conclusion = CForall TySet (CImp (member (CBound 0) (shiftCanonical 1 0 d'))
                            (CEq resultType (CApp (CBound 2) (CBound 0)) (CApp (CBound 1) (CBound 0))))
                    expectedUniqueness <- right (checkCanonicalCore typing (foldr CForall (CImp premises conclusion) contextTypes))
                    generated <- right (Proof.introduceForalls root contextTypes \context -> do
                        conditions <- Proof.scopedTerm context premises
                        Proof.implicationIntroductionProof context conditions \withEquations _ ->
                            Recursion.proveRecursorUniqueness resultType withEquations parameters' d' clauses branches' left rightFunction induction)
                    goal <- right (Proof.scopedTerm root (frozenCoreTerm expectedUniqueness))
                    converted <- right (Proof.conversionProof root generated goal)
                    checked <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                        (Vector.fromList judgements) expectedUniqueness (Proof.builtProofDerivation converted))
                    assertEqual (fixture <> " logical uniqueness") expectedUniqueness (replayedKernelTarget checked)
                -- Decode the Set equation for an arbitrary Prop branch.
                -- Arbitrary branch arguments include negative logical uses.
                for_ (zip (toList clauses) (toList branches)) \(clause,branch) -> do
                    let count = length (Datatype.clausePremises clause)
                        contextTypes = replicate parameterCount TySet
                            <> (Recursion.branchTypeFor TyProp <$> toList clauses)
                            <> [TyArrow TySet TySet] <> replicate count TySet
                        terms = CBound . fromIntegral <$> reverse [0 .. count - 1]
                        evaluate = CBound (fromIntegral count)
                        branch' = shiftCanonical (fromIntegral (count + 1)) 0 branch
                        encoded = Proposition.encodeBranch clause branch'
                        decoded = Proposition.decodedEvaluator evaluate
                    constructor <- right (Datatype.constructorTerm clause terms)
                    setValue <- right (Recursion.branchValue clause encoded evaluate terms)
                    propValue <- right (Recursion.branchValue clause branch' decoded terms)
                    let equation = CEq TySet (CApp evaluate constructor) setValue
                        conclusion = CEq TyProp (CApp decoded constructor) propValue
                    target' <- right (checkCanonicalCore typing (foldr CForall (CImp equation conclusion) contextTypes))
                    proof' <- right (Proof.introduceForalls root contextTypes \context -> do
                        condition <- Proof.scopedTerm context equation
                        Proof.implicationIntroductionProof context condition \withEquation setEquation ->
                            Proposition.proveDecodedEquation withEquation clause branch' evaluate terms setEquation)
                    result' <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing Vector.empty target'
                        (Proof.builtProofDerivation proof'))
                    assertEqual (fixture <> " proposition equation") target' (replayedKernelTarget result')
                -- The ports below are uninterpreted operations with the exact
                -- imported library contracts. Generated proofs are replayed
                -- without consulting operation bodies or an external prover.
                let allArguments = CBound . fromIntegral <$> reverse [0 .. length types - 1]
                    relationImports = toList relationContracts <> [inductionTarget]
                    relationLaws = Relation.RelationLaws
                        (importIx 0,Relation.relationMembership relationContracts)
                        (importIx 1,Relation.relationBound relationContracts)
                        (importIx 2,Relation.binaryRelation relationContracts)
                        (importIx 3,Relation.inductionConverse relationContracts)
                    replay label dependencies body action = do
                        expectedTarget <- right (checkCanonicalCore typing (foldr CForall body types))
                        generated <- either (fail . ((fixture <> " " <> label <> ": ") <>) . show) pure
                            (Proof.introduceForalls root types action)
                        goal <- right (Proof.scopedTerm root (frozenCoreTerm expectedTarget))
                        converted <- right (Proof.conversionProof root generated goal)
                        assumptions <- traverse (right . derivationImportJudgement) dependencies
                        replayed <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                            (Vector.fromList assumptions) expectedTarget (Proof.builtProofDerivation converted))
                        assertEqual (fixture <> " " <> label) expectedTarget (replayedKernelTarget replayed)
                        pure expectedTarget
                r <- right (Relation.subtermRelation (length types) relations d clauses)
                wf <- replay "well-founded subterms" relationImports
                    (CApp (CApp (CGlobal (Relation.wellFounded relations)) d) r)
                    (\context -> Relation.proveSubtermWellFounded context relations relationLaws d clauses
                        (importIx 4,inductionTarget) allArguments)
                let graphImports = toList graphContracts <> toList relationContracts <> [wf,target]
                    graphLaws = Graph.GraphLaws
                        (importIx 0,Graph.stepCharacterization graphContracts)
                        (importIx 1,Graph.recursionFunction graphContracts)
                        (importIx 2,Graph.recursionDomain graphContracts)
                        (importIx 3,Graph.recursionSpecification graphContracts)
                        (importIx 4,Graph.restrictionApply graphContracts)
                        (importIx 5,Graph.predecessorMembership graphContracts)
                        (importIx 6,Graph.graphDefault graphContracts)
                    graphRelationLaws = Relation.RelationLaws
                        (importIx 7,Relation.relationMembership relationContracts)
                        (importIx 8,Relation.relationBound relationContracts)
                        (importIx 9,Relation.binaryRelation relationContracts)
                        (importIx 10,Relation.inductionConverse relationContracts)
                    graphProperty fact context = Graph.proveGraphProperty context operations graphRelationLaws
                        d clauses branches (importIx 11,wf) allArguments fact
                stepRelation <- right (Graph.branchGraphRelation (length types) operations d clauses branches)
                graph <- right (Graph.recursionGraph (length types) operations d clauses branches)
                step <- replay "functional step" graphImports
                    (foldl' CApp (CGlobal (Graph.relationStep operations)) [d,r,stepRelation])
                    (\context -> Graph.proveRelationStep context operations graphLaws d clauses branches
                        (importIx 12,target) allArguments)
                _ <- replay "function graph" graphImports (CApp (CGlobal (Graph.graphFunction operations)) graph)
                    (graphProperty (Graph.recursionFunction graphLaws))
                domain <- replay "exact domain" graphImports (CEq TySet (CApp (CGlobal (Graph.domain operations)) graph) d)
                    (graphProperty (Graph.recursionDomain graphLaws))
                let shift = shiftCanonical 1 0
                    value = CApp (CApp (CGlobal (Graph.graphApply operations)) (shift graph)) (CBound 0)
                    restricted = CApp (CApp (CGlobal (Graph.restrict operations)) (shift graph))
                        (CApp (CApp (CGlobal (Graph.predecessors operations)) (shift r)) (CBound 0))
                    specificationBody = CForall TySet (CImp (member (CBound 0) (shift d))
                        (foldl' CApp (shift stepRelation) [CBound 0,restricted,value]))
                specification <- replay "branch specification" (graphImports <> [step]) specificationBody \context -> do
                    theorem <- graphProperty (Graph.recursionSpecification graphLaws) context
                    stepProof <- use context (importIx 13,step) allArguments
                    Proof.implicationEliminationProof context theorem stepProof
                let equationImports = graphImports <> [step,specification,domain] <> imports
                    evaluator = CLam TySet value
                    importOffset = fromIntegral (length graphImports + 3)
                    shiftedIntro law = (importIx (importOffset + importIxValue (fst law)),snd law)
                for_ (zip [0 ..] (toList clauses)) \(index,clause) -> do
                    branch <- maybe (fail "constructor branch missing") pure (nth index (toList branches))
                    intro <- maybe (fail "constructor law missing") (pure . shiftedIntro . Recursion.constructorIntroduction)
                        (nth index (toList laws))
                    equation <- right (Recursion.constructorEquationTarget TySet (length types) d clause branch evaluator)
                    void (replay "constructor equation" equationImports equation \context ->
                        Graph.proveConstructorEquation context operations graphRelationLaws graphLaws d clauses branches
                            index intro parameters (importIx 14,specification) (importIx 12,target) allArguments)
                void (replay "off-domain default" equationImports
                    (CForall TySet (CImp (CNot (member (CBound 0) (shift d))) (CEq TySet value (CIntrinsic Empty))))
                    (\context -> Graph.proveGraphDefault context operations graphLaws d graph (importIx 15,domain) allArguments))



-- Opaque operations keep this a test of derivations from the public contracts,
-- independent of the recursion library's implementation and its ATP proofs.
libraryOperations :: Identity.TheoryId -> IO ([Identity.AssertedObject],Graph.GraphOperations)
libraryOperations theory = do
    relative <- right (safeRelativePath "recursion-support.tex")
    let owner = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 "recursion-support")) relative
        sets n result = foldr (const (TyArrow TySet)) result [1 .. n :: Int]
        relationType = sets 2 TyProp
        stepType = sets 3 TyProp
        signatures =
            [("relationOn",TyArrow TySet (TyArrow relationType TySet))
            ,("subset",sets 2 TyProp),("product",sets 2 TySet),("relation",sets 1 TyProp),("wf",sets 2 TyProp)
            ,("recursion",sets 2 (TyArrow stepType TySet)),("step",sets 2 (TyArrow stepType TyProp))
            ,("history",sets 4 TyProp),("function",sets 1 TyProp),("apply",sets 2 TySet)
            ,("domain",sets 1 TySet),("restriction",sets 2 TySet),("predecessors",sets 2 TySet)]
        objects = [(name,Identity.opaqueObject theory
            (Identity.opaqueDeclarationSeed owner (localDeclarationOrdinal 0) SignatureDeclaration (generatedObjectSlot index)) ty)
            | (index,(name,ty)) <- zip [0 ..] signatures]
        ports = Map.fromList [(name,Identity.assertedObjectId object) | (name,object) <- objects]
        port name = maybe (fail "test support port is missing") pure (Map.lookup (name :: Text) ports)
    relations <- Relation.RelationOperations <$> port "relationOn" <*> port "subset" <*> port "product" <*> port "relation" <*> port "wf"
    operations <- Graph.GraphOperations relations <$> port "recursion" <*> port "step" <*> port "history" <*> port "function"
        <*> port "apply" <*> port "domain" <*> port "restriction" <*> port "predecessors"
    pure (snd <$> objects,operations)

member :: CanonicalTerm global -> CanonicalTerm global -> CanonicalTerm global
member a b = CApp (CApp (CIntrinsic Member) a) b

use :: Proof.ProofContext Identity.ObjectId -> Datatype.ProofImport -> [CanonicalTerm Identity.ObjectId]
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof Identity.ObjectId)
use context (index,target) arguments = do
    proof <- Proof.importedProof context index target
    foldM (\current argument -> Proof.scopedTerm context argument >>= Proof.forallEliminationProof context current) proof arguments

truthValues :: Assertion
truthValues = do
    foundation <- right Foundation.checkedFoundation
    closure <- right (Identity.validateObjectClosure (Identity.theoryId foundation) [])
    let typing = Identity.globalTypingFromClosure closure
        root = Proof.rootProofContext foundation typing
        run expected action = do
            target <- right (checkCanonicalCore typing expected)
            proof <- right action
            checked <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing Vector.empty target
                (Proof.builtProofDerivation proof))
            assertEqual "truth-value proof" target (replayedKernelTarget checked)
    run (CForall TyProp (CEq TyProp (Proposition.decode (Proposition.encode (CBound 0))) (CBound 0)))
        (Proof.forallIntroductionProof root TyProp \context _ -> Proposition.proveDecodeEncode context (CBound 0))
    run (CForall TySet (CImp (CEq TySet (CBound 0) (CIntrinsic Empty))
            (CEq TyProp (Proposition.decode (CBound 0)) CFalsum)))
        (Proof.forallIntroductionProof root TySet \context _ -> do
            hypothesis <- Proof.scopedTerm context (CEq TySet (CBound 0) (CIntrinsic Empty))
            Proof.implicationIntroductionProof context hypothesis \withDefault proof ->
                Proposition.proveDecodedDefault withDefault (CBound 0) proof)
