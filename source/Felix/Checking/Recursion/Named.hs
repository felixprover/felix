{-# LANGUAGE NoImplicitPrelude #-}

-- | Specialize a checked recursor to fixed branch functions. Headers constrain
-- Set formation; for Prop they are also conjuncts of the transparent body.
-- These recipes acquire authority only when the declaration owner replays them.
module Felix.Checking.Recursion.Named
    ( NamedRecursor(..)
    , prepareNamedRecursor
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Foundation (CheckedFoundation, FoundationAxiomTag(..))
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Planning
import Felix.Checking.Recursion.Construction qualified as Construction
import Felix.Checking.Recursion.Definition qualified as Definition
import Felix.Checking.Recursion.Library
import Felix.Checking.Recursion.Prepared

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Numeric.Natural (Natural)

type Term = CanonicalTerm ObjectId

data NamedRecursor = NamedRecursor
    { namedRecursorObjects :: ![AssertedObject]
    , namedRecursorObject :: !ObjectId
    , namedRecursorFacts :: ![PreparedRecursorFact]
    , namedRecursorEquations :: !(NonEmpty PreparedReference)
    }

-- Datatype arguments are nearest-first indices into the fixed Set parameters.
-- Headers and branch lambdas live in exactly that parameter context. No clause
-- local or recursive-result variable can escape a checked branch lambda.
prepareNamedRecursor
    :: CheckedFoundation -> CheckedObjectClosure -> RecursionLibrary -> LoadedDatatype
    -> CoreType -> Int -> [Natural] -> [ScopedCheckedCore ObjectId]
    -> NonEmpty (ScopedCheckedCore ObjectId) -> Either Text NamedRecursor
prepareNamedRecursor foundation initial library datatype resultType parameterCount arguments headers branches = do
    unless (parameterCount >= 0 && length arguments == loadedDatatypeParameterCount datatype
        && all (< fromIntegral parameterCount) arguments)
        (Left "recursive definition has an invalid datatype instance")
    let types = replicate parameterCount TySet
        originalClauses = loadedDatatypeClauses datatype
    unless (NonEmpty.length branches == NonEmpty.length originalClauses)
        (Left "recursive definition requires exactly one branch per constructor")
    for_ headers (checkInput types TyProp)
    for_ (NonEmpty.zip originalClauses branches) \(clause,branch) ->
        checkInput types (Construction.branchTypeFor resultType clause) branch
    recursor <- prepareRecursor foundation initial resultType library datatype
    let typing = globalTypingFromClosure initial
        parameters = CBound <$> arguments
        substitute term = instantiateCanonicalPrefixWith (pure ()) (fromIntegral (length arguments))
            (\depth slot -> maybe (Left "datatype domain has an invalid parameter")
                (pure . shiftCanonical depth 0 . CBound) (nth slot (reverse arguments))) 0 term
    clauses <- for originalClauses \clause -> do
        premises <- for (Datatype.clausePremises clause) \case
            Datatype.Recursive -> pure Datatype.Recursive
            Datatype.FixedDomain domain -> do
                term <- substitute (scopedCoreTerm domain)
                Datatype.FixedDomain <$> first (Text.pack . show) (checkScopedCanonicalCore typing types term)
        pure clause {Datatype.clausePremises = premises}
    let branchTerms = scopedCoreTerm <$> branches
        conditions = scopedCoreTerm <$> headers
        carrier = apply (CGlobal (loadedDatatypeCarrier datatype)) parameters
        recursorArguments = parameters <> toList branchTerms
        evaluator = apply (CGlobal (preparedRecursorObject recursor)) recursorArguments
        guardedEvaluator = if resultType == TyProp && not (null conditions)
            then CLam TySet (CAnd (shift (conjunction conditions)) (CApp (shift evaluator) (CBound 0)))
            else evaluator
        object = transparentObject (checkedObjectClosureTheory initial)
            (foldr TyArrow (TyArrow TySet resultType) types) (foldr CLam guardedEvaluator types)
        identity = assertedObjectId object
        named = apply (CGlobal identity) (variables parameterCount)
        objects = preparedRecursorObjects recursor <>
            [object | lookupCheckedObjectContent identity initial /= Just (assertedObjectContent object)]
        priorFacts = preparedRecursorFacts recursor
        definitionPosition = PlannedCandidatePosition (fromIntegral (length priorFacts)) 0
    closure <- first (Text.pack . show) (extendObjectClosure initial objects)
    let checked = first (Text.pack . show) . checkCanonicalCore (globalTypingFromClosure closure)
        root = Proof.rootProofContext foundation (globalTypingFromClosure closure)
    definitionTarget <- checked (canonicalDefinitionEquationTarget identity
        (foldr TyArrow (TyArrow TySet resultType) types) (foldr CLam guardedEvaluator types))
    let definition = PreparedRecursorFact definitionTarget (RecursorDefinition identity)
    equations <- for (NonEmpty.zip (NonEmpty.zip clauses branchTerms) (preparedRecursorEquations recursor))
        \((clause,branch),(reference,law)) -> do
            let fieldCount = length (Datatype.clausePremises clause)
                liftTerm = shiftCanonical (fromIntegral fieldCount) 0
                fields = variables fieldCount
                guards = (liftTerm <$> conditions)
                    <> Datatype.premiseTerms (parameterCount + fieldCount) (liftTerm carrier) clause fields
                fieldTypes = replicate fieldCount TySet
            constructor <- build (Datatype.constructorTerm clause fields)
            value <- build (Construction.branchValue clause (liftTerm branch) (liftTerm named) fields)
            let equation = CEq resultType (CApp (liftTerm named) constructor) value
                body = if null guards then equation else CImp (conjunction guards) equation
            target <- checked (foldr CForall body (types <> fieldTypes))
            proof <- build (Proof.introduceForalls root (types <> fieldTypes) \context ->
                assume context guards \withGuards -> do
                    ordinary <- use withGuards (Kernel.importIx 0,law)
                        ((liftTerm <$> recursorArguments) <> fields)
                    applied <- case scopedCoreTerm (Proof.builtProofStatement ordinary) of
                        CImp guardTerm _ -> known withGuards guardTerm >>= Proof.implicationEliminationProof withGuards ordinary
                        _ -> pure ordinary
                    equality <- Definition.proveEvaluatorDefinition withGuards identity resultType
                        (Kernel.importIx 1,definitionTarget) (liftTerm <$> variables parameterCount) (liftTerm guardedEvaluator)
                    evaluatorEquality <- if resultType == TyProp && not (null conditions)
                        then do
                            unguarded <- removeHeader withGuards (liftTerm (conjunction conditions)) (liftTerm evaluator)
                            Proof.composeEqualityProof withGuards equality unguarded
                        else pure equality
                    -- Transport the evaluator as a whole, including every recursive
                    -- result occurrence in the branch (positive or negative).
                    result <- Construction.branchValue clause (shift (liftTerm branch)) (CBound 0) (shift <$> fields)
                    let property = CLam (TyArrow TySet resultType)
                            (CEq resultType (CApp (CBound 0) (shift constructor)) result)
                    Definition.transportEvaluatorProperty withGuards evaluatorEquality property equation applied)
            normalized <- build (Proof.scopedTerm root (frozenCoreTerm target) >>= Proof.conversionProof root proof)
            pure (PreparedRecursorFact target (RecursorDerivation
                [reference,LocalCandidateReference definitionPosition] (Proof.builtProofDerivation normalized)))
    let allFacts = priorFacts <> [definition] <> toList equations
        references = NonEmpty.zipWith (\ordinal fact ->
            (LocalCandidateReference (PlannedCandidatePosition ordinal 0),recursorFactTarget fact))
            (fromIntegral (length priorFacts + 1) :| [fromIntegral (length priorFacts + 2) ..]) equations
    pure (NamedRecursor objects identity allFacts references)
  where
    checkInput types expected input = do
        unless (scopedCoreContext input == types && scopedCoreType input == expected)
            (Left "recursive definition header or branch has an incompatible scope or type")
        void (first (Text.pack . show) (checkScopedCanonicalCore (globalTypingFromClosure initial) types (scopedCoreTerm input)))

removeHeader :: Proof.ProofContext ObjectId -> Term -> Term -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
removeHeader context header evaluator = do
    (extended,_) <- Proof.extendProofContextBinder context TySet
    let condition = shift header
        value = CApp (shift evaluator) (CBound 0)
        guarded = CAnd condition value
    forward <- Proof.scopedTerm extended guarded >>= \premise ->
        Proof.implicationIntroductionProof extended premise Proof.conjunctionRightProof
    backward <- Proof.scopedTerm extended value >>= \premise ->
        Proof.implicationIntroductionProof extended premise \withValue proof -> do
            conditionProof <- known withValue condition
            Proof.conjunctionIntroductionProof withValue conditionProof proof
    arguments <- traverse (Proof.scopedTerm extended) [guarded,value]
    extensionality <- Proof.foundationInstanceProof extended PropositionalExtensionality arguments
    equality <- Proof.implicationEliminationProof extended extensionality forward
        >>= \proof -> Proof.implicationEliminationProof extended proof backward
    function <- Proof.equalityCongruenceLambdaProof TySet equality
    Proof.scopedTerm context (CEq (TyArrow TySet TyProp)
        (CLam TySet guarded) evaluator) >>= Proof.conversionProof context function

build :: Either Proof.KernelProofBuildError a -> Either Text a
build = first (Text.pack . show)

use :: Proof.ProofContext ObjectId -> Datatype.ProofImport -> [Term]
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
use context (index,target) arguments = do
    proof <- Proof.importedProof context index target
    foldM (\current argument -> Proof.scopedTerm context argument >>= Proof.forallEliminationProof context current) proof arguments

known :: Proof.ProofContext ObjectId -> Term -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
known context target = do
    premises <- traverse (Proof.hypothesisProof context) (Proof.proofContextHypotheses context)
    checked <- Proof.scopedTerm context target
    Proof.structuralLogicalProof context premises checked
        >>= maybe (Left (Proof.ProofStructuralCompositionMismatch "named recursion lost a guard")) pure

assume :: Proof.ProofContext ObjectId -> [Term]
    -> (Proof.ProofContext ObjectId -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId))
    -> Either Proof.KernelProofBuildError (Proof.BuiltProof ObjectId)
assume context [] body = body context
assume context guards body = do
    premise <- Proof.scopedTerm context (conjunction guards)
    Proof.implicationIntroductionProof context premise (\extended _ -> body extended)

variables :: Int -> [Term]
variables count = CBound . fromIntegral <$> reverse [0 .. count - 1]

apply :: Term -> [Term] -> Term
apply = foldl' CApp

shift :: Term -> Term
shift = shiftCanonical 1 0

conjunction :: [Term] -> Term
conjunction [] = CTruth
conjunction (firstTerm:rest) = foldl' CAnd firstTerm rest
