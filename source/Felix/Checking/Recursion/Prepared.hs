{-# LANGUAGE NoImplicitPrelude #-}

-- | Declaration-local recursor construction. The returned recipes have no
-- authority: the declaration owner must replay them before publication.
module Felix.Checking.Recursion.Prepared
    ( PreparedRecursor(..)
    , PreparedRecursorFact(..)
    , RecursorEvidence(..)
    , PreparedReference
    , prepareRecursor
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Foundation (CheckedFoundation)
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Planning
import Felix.Checking.Recursion.Construction qualified as Construction
import Felix.Checking.Recursion.Definition qualified as Definition
import Felix.Checking.Recursion.Graph qualified as Graph
import Felix.Checking.Recursion.Library
import Felix.Checking.Recursion.Proposition qualified as Proposition
import Felix.Checking.Recursion.Relation qualified as Relation

import Control.Monad (foldM, unless)
import Control.Monad.State.Strict qualified as State
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text

type Term = CanonicalTerm ObjectId
type PreparedReference = (PlannedFactReference, FrozenCheckedCore ObjectId)

data RecursorEvidence
    = RecursorDefinition !ObjectId
    | RecursorDerivation ![PlannedFactReference] !(Kernel.KernelDerivation ObjectId)

data PreparedRecursorFact = PreparedRecursorFact
    { recursorFactTarget :: !(FrozenCheckedCore ObjectId)
    , recursorFactEvidence :: !RecursorEvidence
    }

data PreparedRecursor = PreparedRecursor
    { preparedRecursorObjects :: ![AssertedObject]
    , preparedRecursorObject :: !ObjectId
    , preparedRecursorFacts :: ![PreparedRecursorFact]
    , preparedRecursorEquations :: !(NonEmpty PreparedReference)
    , preparedRecursorDefault :: !PreparedReference
    , preparedRecursorUniqueness :: !PreparedReference
    }

prepareRecursor
    :: CheckedFoundation -> CheckedObjectClosure -> CoreType -> RecursionLibrary -> LoadedDatatype
    -> Either Text PreparedRecursor
prepareRecursor foundation initial resultType library datatype = do
    unless (resultType == TySet || resultType == TyProp) (Left "recursion result must be Set or Prop")
    let clauses = loadedDatatypeClauses datatype
        parameterCount = loadedDatatypeParameterCount datatype
        familyTypes = replicate parameterCount TySet
        carrier = loadedDatatypeCarrier datatype
        setTypes = familyTypes <> (Construction.branchType <$> toList clauses)
        propTypes = familyTypes <> (Construction.branchTypeFor TyProp <$> toList clauses)
        arguments types = variables (length types)
        parameters types = take parameterCount (arguments types)
        branches types = NonEmpty.fromList (drop parameterCount (arguments types))
        carrierAt types = apply (CGlobal carrier) (parameters types)
        operations = libraryOperations library
        relationOps = Graph.graphRelationOperations operations
        environment (fingerprint,target) = (EnvironmentOccurrenceReference fingerprint,target)
        relationLaws = environment <$> libraryRelationLaws library
        graphLaws = environment <$> libraryGraphLaws library
        constructorLaws = fmap environment <$> loadedDatatypeConstructorLaws datatype
        casesLaw = environment (loadedDatatypeCases datatype)
        inductionLaw = environment (loadedDatatypeInduction datatype)
        datatypeLaws = casesLaw : inductionLaw : concatMap toList (toList constructorLaws)
        base = toList relationLaws <> toList graphLaws <> datatypeLaws
    graph <- build "recursion graph" (Graph.recursionGraph (length setTypes) operations (carrierAt setTypes) clauses (branches setTypes))
    let setEvaluator = CLam TySet (apply (CGlobal (Graph.graphApply operations)) [shift graph,CBound 0])
        setBody = foldr CLam setEvaluator setTypes
        setObject = transparentObject (checkedObjectClosureTheory initial) (foldr TyArrow (TyArrow TySet TySet) setTypes) setBody
        setName = assertedObjectId setObject
        encodedBranches = NonEmpty.zipWith Proposition.encodeBranch clauses (branches propTypes)
        setArguments = parameters propTypes <> toList encodedBranches
        setAtProp = apply (CGlobal setName) setArguments
        propEvaluator = Proposition.decodedEvaluator setAtProp
        propBody = foldr CLam propEvaluator propTypes
        propObject = transparentObject (checkedObjectClosureTheory initial) (foldr TyArrow (TyArrow TySet TyProp) propTypes) propBody
        -- Recursors are content-addressed and shared by subsequent named
        -- definitions. Keep all proof recipes, but publish only new objects.
        objects = [object | object <- setObject : [propObject | resultType == TyProp]
            , lookupCheckedObjectContent (assertedObjectId object) initial /= Just (assertedObjectContent object)]
    closure <- first (Text.pack . show) (extendObjectClosure initial objects)
    let typing = globalTypingFromClosure closure
        root = Proof.rootProofContext foundation typing
        checked = first (Text.pack . show) . checkCanonicalCore typing
        append target evidence = do
            facts <- State.get
            let position = PlannedCandidatePosition (fromIntegral (length facts)) 0
            State.put (facts <> [PreparedRecursorFact target evidence])
            pure (LocalCandidateReference position,target)
        definition object = case assertedObjectContent object of
            TransparentObjectContent _ ty body -> do
                target <- State.lift (checked (canonicalDefinitionEquationTarget (assertedObjectId object) ty body))
                append target (RecursorDefinition (assertedObjectId object))
            _ -> State.lift (Left "recursor object is not transparent")
        derived label types dependencies target action = do
            expectedBody <- State.lift (build label target)
            expected <- State.lift (checked (foldr CForall expectedBody types))
            let selected = Map.toAscList (Map.fromList dependencies)
                imports = Map.fromList [(reference,(Kernel.importIx index,proposition))
                    | (index,(reference,proposition)) <- zip [0 ..] selected]
                at (reference,_) = fromMaybe (impossible "recursion builder requested an unplanned import") (Map.lookup reference imports)
            proof <- State.lift (build label (Proof.introduceForalls root types (action at)))
            converted <- State.lift (build label (Proof.scopedTerm root (frozenCoreTerm expected) >>= Proof.conversionProof root proof))
            append expected (RecursorDerivation (fst <$> selected) (Proof.builtProofDerivation converted))
        plain label types dependencies target = derived label types dependencies (pure target)
        defaultTarget ty d evaluate = CForall TySet (CImp (CNot (member (CBound 0) (shift d)))
            (CEq ty (CApp (shift evaluate) (CBound 0)) (if ty == TySet then CIntrinsic Empty else CFalsum)))
        nameEquation ty types object definitionRef evaluate clause branch proof context at = do
            equality <- Definition.proveEvaluatorDefinition context object ty (at definitionRef) (arguments types) evaluate
            property <- Construction.constructorEquationTarget ty (length types + 1) (shift (carrierAt types)) clause (shift branch) (CBound 0)
            expected <- Construction.constructorEquationTarget ty (length types) (carrierAt types) clause branch (apply (CGlobal object) (arguments types))
            Definition.transportEvaluatorProperty context equality (CLam (TyArrow TySet ty) property) expected proof
    ((equations,defaultLaw,uniqueness),facts) <- State.runStateT (do
        setDefinition <- definition setObject
        propDefinition <- if resultType == TyProp then Just <$> definition propObject else pure Nothing
        subterm <- derived "subterm induction" familyTypes base
            (Construction.subtermInductionTarget parameterCount (carrierAt familyTypes) clauses)
            (\at context -> Construction.proveSubtermInduction context (parameters familyTypes) (carrierAt familyTypes) clauses
                (at inductionLaw) (fmap at <$> constructorLaws))
        r <- State.lift (build "subterm relation" (Relation.subtermRelation parameterCount relationOps (carrierAt familyTypes) clauses))
        wf <- plain "well-founded subterms" familyTypes (base <> [subterm])
            (apply (CGlobal (Relation.wellFounded relationOps)) [carrierAt familyTypes,r])
            (\at context -> Relation.proveSubtermWellFounded context relationOps (at <$> relationLaws) (carrierAt familyTypes) clauses
                (at subterm) (arguments familyTypes))
        functionality <- derived "branch functionality" setTypes base
            (Construction.branchFunctionalityTarget (length setTypes) (carrierAt setTypes) clauses (branches setTypes))
            (\at context -> Construction.proveBranchFunctionality context (parameters setTypes) (carrierAt setTypes) clauses (branches setTypes)
                (at casesLaw) (fmap at <$> constructorLaws))
        rSet <- State.lift (build "subterm relation" (Relation.subtermRelation (length setTypes) relationOps (carrierAt setTypes) clauses))
        stepRelation <- State.lift (build "branch relation" (Graph.branchGraphRelation (length setTypes) operations (carrierAt setTypes) clauses (branches setTypes)))
        step <- plain "functional relation step" setTypes (base <> [functionality])
            (apply (CGlobal (Graph.relationStep operations)) [carrierAt setTypes,rSet,stepRelation])
            (\at context -> Graph.proveRelationStep context operations (at <$> graphLaws) (carrierAt setTypes) clauses (branches setTypes)
                (at functionality) (arguments setTypes))
        let graphProperty law at context = Graph.proveGraphProperty context operations (at <$> relationLaws)
                (carrierAt setTypes) clauses (branches setTypes) (at wf) (parameters setTypes) (at law)
        _ <- plain "recursion function graph" setTypes (base <> [wf])
            (CApp (CGlobal (Graph.graphFunction operations)) graph) (graphProperty (Graph.recursionFunction graphLaws))
        domain <- plain "recursion exact domain" setTypes (base <> [wf])
            (CEq TySet (CApp (CGlobal (Graph.domain operations)) graph) (carrierAt setTypes))
            (graphProperty (Graph.recursionDomain graphLaws))
        let history = apply (CGlobal (Graph.restrict operations)) [shift graph,
                apply (CGlobal (Graph.predecessors operations)) [shift rSet,CBound 0]]
            value = apply (CGlobal (Graph.graphApply operations)) [shift graph,CBound 0]
            specificationTarget = CForall TySet (CImp (member (CBound 0) (shift (carrierAt setTypes)))
                (apply (shift stepRelation) [CBound 0,history,value]))
        specification <- plain "recursion specification" setTypes (base <> [wf,step]) specificationTarget \at context -> do
            theorem <- graphProperty (Graph.recursionSpecification graphLaws) at context
            functional <- use context (at step) (arguments setTypes)
            Proof.implicationEliminationProof context theorem functional
        setEquations <- for (NonEmpty.zip (0 :| [1 ..]) (NonEmpty.zip (NonEmpty.zip clauses (branches setTypes)) constructorLaws)) \(index,((clause,branch),laws)) -> do
            inline <- derived "constructed Set equation" setTypes (base <> [specification,functionality])
                (Construction.constructorEquationTarget TySet (length setTypes) (carrierAt setTypes) clause branch setEvaluator)
                (\at context -> Graph.proveConstructorEquation context operations (at <$> relationLaws) (at <$> graphLaws)
                    (carrierAt setTypes) clauses (branches setTypes) index
                    (at (Construction.constructorIntroduction laws)) (parameters setTypes)
                    (at specification) (at functionality) (arguments setTypes))
            derived "named Set equation" setTypes [setDefinition,inline]
                (Construction.constructorEquationTarget TySet (length setTypes) (carrierAt setTypes) clause branch (apply (CGlobal setName) (arguments setTypes)))
                (\at context -> do
                    proof <- use context (at inline) (arguments setTypes)
                    nameEquation TySet setTypes setName setDefinition setEvaluator clause branch proof context at)
        inlineDefault <- plain "constructed Set default" setTypes (base <> [domain])
            (defaultTarget TySet (carrierAt setTypes) setEvaluator)
            (\at context -> Graph.proveGraphDefault context operations (at <$> graphLaws) (carrierAt setTypes) graph (at domain) (arguments setTypes))
        setDefault <- plain "named Set default" setTypes [setDefinition,inlineDefault]
            (defaultTarget TySet (carrierAt setTypes) (apply (CGlobal setName) (arguments setTypes))) \at context -> do
                proof <- use context (at inlineDefault) (arguments setTypes)
                equality <- Definition.proveEvaluatorDefinition context setName TySet (at setDefinition) (arguments setTypes) setEvaluator
                let property = CLam (TyArrow TySet TySet) (defaultTarget TySet (shift (carrierAt setTypes)) (CBound 0))
                Definition.transportEvaluatorProperty context equality property
                    (defaultTarget TySet (carrierAt setTypes) (apply (CGlobal setName) (arguments setTypes))) proof
        (resultEquations,resultDefault) <- case propDefinition of
            Nothing -> pure (setEquations,setDefault)
            Just definitionRef -> do
                let propName = assertedObjectId propObject
                propEquations <- for (NonEmpty.zip (NonEmpty.zip clauses (branches propTypes)) setEquations) \((clause,branch),setEquation) ->
                    derived "named Prop equation" propTypes [definitionRef,setEquation]
                        (Construction.constructorEquationTarget TyProp (length propTypes) (carrierAt propTypes) clause branch (apply (CGlobal propName) (arguments propTypes)))
                        (\at context -> do
                            let count = length (Datatype.clausePremises clause)
                                liftTerm = shiftCanonical (fromIntegral count) 0
                                terms = variables count
                            proof <- Proof.introduceForalls context (replicate count TySet) \withFields -> do
                                let guards = Datatype.premiseTerms (length propTypes + count) (liftTerm (carrierAt propTypes)) clause terms
                                assumeGuards withFields guards \withGuards -> do
                                    equation <- use withGuards (at setEquation) ((liftTerm <$> setArguments) <> terms)
                                        >>= \instance' -> applyGuards withGuards instance' guards
                                    Proposition.proveDecodedEquation withGuards clause (liftTerm branch) (liftTerm setAtProp) terms equation
                            nameEquation TyProp propTypes propName definitionRef propEvaluator clause branch proof context at)
                propDefault <- plain "named Prop default" propTypes [definitionRef,setDefault]
                    (defaultTarget TyProp (carrierAt propTypes) (apply (CGlobal propName) (arguments propTypes))) \at context -> do
                        proof <- Proof.forallIntroductionProof context TySet \withElement _ -> do
                            condition <- Proof.scopedTerm withElement (CNot (member (CBound 0) (shift (carrierAt propTypes))))
                            Proof.implicationIntroductionProof withElement condition \withOutside outside -> do
                                equation <- use withOutside (at setDefault) ((shift <$> setArguments) <> [CBound 0])
                                    >>= \instance' -> Proof.implicationEliminationProof withOutside instance' outside
                                Proposition.proveDecodedDefault withOutside (CApp (shift setAtProp) (CBound 0)) equation
                        equality <- Definition.proveEvaluatorDefinition context propName TyProp (at definitionRef) (arguments propTypes) propEvaluator
                        let property = CLam (TyArrow TySet TyProp) (defaultTarget TyProp (shift (carrierAt propTypes)) (CBound 0))
                        Definition.transportEvaluatorProperty context equality property
                            (defaultTarget TyProp (carrierAt propTypes) (apply (CGlobal propName) (arguments propTypes))) proof
                pure (propEquations,propDefault)
        let types = if resultType == TySet then setTypes else propTypes
            functionType = TyArrow TySet resultType
            extra = shiftCanonical 2 0
            d = extra (carrierAt types)
            bs = extra <$> branches types
        eqs <- State.lift (build "uniqueness equations" (sequence
            [Construction.constructorEquationTarget resultType (length types + 2) d clause branch evaluator
            | (clause,branch) <- zip (toList clauses) (toList bs), evaluator <- [CBound 1,CBound 0]]))
        let conditions = conjunction eqs
            conclusion = CForall TySet (CImp (member (CBound 0) (shift d))
                (CEq resultType (CApp (CBound 2) (CBound 0)) (CApp (CBound 1) (CBound 0))))
        uniqueness <- plain "logical recursion uniqueness" (types <> [functionType,functionType]) [inductionLaw]
            (CImp conditions conclusion) \at context -> do
                condition <- Proof.scopedTerm context conditions
                Proof.implicationIntroductionProof context condition \withEquations _ ->
                    Construction.proveRecursorUniqueness resultType withEquations (extra <$> parameters types) d clauses bs
                        (CBound 1) (CBound 0) (at inductionLaw)
        pure (resultEquations,resultDefault,uniqueness)) []
    pure (PreparedRecursor objects (assertedObjectId (if resultType == TySet then setObject else propObject)) facts equations defaultLaw uniqueness)

build :: Show e => Text -> Either e a -> Either Text a
build label = first (\failure -> label <> ": " <> Text.pack (show failure))

variables :: Int -> [Term]
variables count = CBound . fromIntegral <$> reverse [0 .. count - 1]

apply :: Term -> [Term] -> Term
apply = foldl' CApp

shift :: Term -> Term
shift = shiftCanonical 1 0

member :: Term -> Term -> Term
member a b = apply (CIntrinsic Member) [a,b]

conjunction :: [Term] -> Term
conjunction [] = CTruth
conjunction (a:rest) = foldl' CAnd a rest

use :: Proof.ProofContext ObjectId -> Datatype.ProofImport -> [Term]
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
use context (index,target) arguments = do
    proof <- Proof.importedProof context index target
    foldM (\current argument -> Proof.scopedTerm context argument >>= Proof.forallEliminationProof context current) proof arguments

assumeGuards :: Proof.ProofContext ObjectId -> [Term]
    -> (Proof.ProofContext ObjectId -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId))
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
assumeGuards context [] body = body context
assumeGuards context guards body = do
    condition <- Proof.scopedTerm context (conjunction guards)
    Proof.implicationIntroductionProof context condition (\extended _ -> body extended)

applyGuards :: Proof.ProofContext ObjectId -> Proof.BuiltProof ObjectId -> [Term]
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
applyGuards _ proof [] = pure proof
applyGuards context proof guards = do
    premises <- for guards \condition -> do
        target <- Proof.scopedTerm context condition
        available <- traverse (Proof.hypothesisProof context) (Proof.proofContextHypotheses context)
        Proof.structuralLogicalProof context available target
            >>= maybe (Left (Proof.ProofStructuralCompositionMismatch "recursor equation lost a guard")) pure
    conjunctionProof <- Proof.buildLeftAssociatedConjunction context premises
    Proof.implicationEliminationProof context proof conjunctionProof
