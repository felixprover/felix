{-# LANGUAGE NoImplicitPrelude #-}

-- | Relate a named transparent recursor to its logical evaluator. Both the
-- ordinary pointwise definition form and exact higher-order definitions use
-- the same checked equality interface after this small adapter.
module Felix.Checking.Recursion.Definition
    ( proveEvaluatorDefinition
    , transportEvaluatorProperty
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction (ProofImport)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof

import Control.Monad (foldM)

type Term = CanonicalTerm ObjectId
type Context = ProofContext ObjectId
type Proof = BuiltProof ObjectId
type Build = Either KernelProofBuildError

proveEvaluatorDefinition
    :: Context -> ObjectId -> CoreType -> ProofImport -> [Term] -> Term -> Build Proof
proveEvaluatorDefinition context object resultType (index,target) arguments evaluator = do
    equality <- case frozenCoreTerm target of
        CEq{} -> do
            definition <- importedProof context index target
            foldM (\current argument -> do
                reflexive <- scopedTerm context argument >>= equalityReflexivityProof context
                equalityCongruenceApplicationProof context current reflexive) definition arguments
        CForall{} -> do
            (extended,_) <- extendProofContextBinder context TySet
            definition <- importedProof extended index target
            pointwise <- foldM (\current argument -> scopedTerm extended argument >>= forallEliminationProof extended current)
                definition ((shiftCanonical 1 0 <$> arguments) <> [CBound 0])
            equalityCongruenceLambdaProof TySet pointwise
        _ -> Left (ProofStructuralCompositionMismatch "recursor has no defining equation")
    let named = foldl' CApp (CGlobal object) arguments
    goal <- scopedTerm context (CEq (TyArrow TySet resultType) named evaluator)
    conversionProof context equality goal

-- Equality is named evaluator = constructed evaluator. A property proved of
-- the construction therefore transports in the reverse direction.
transportEvaluatorProperty :: Context -> Proof -> Term -> Term -> Proof -> Build Proof
transportEvaluatorProperty context equality property expected proof = do
    reversed <- equalityReverseProof context equality
    predicate <- scopedTerm context property
    transported <- equalityTransportProof context reversed predicate proof
    scopedTerm context expected >>= conversionProof context transported
