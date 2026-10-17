{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The set relation of immediate stored subterms. Library laws connect the
-- datatype's predicate induction to ordinary well-founded relation recursion.
module Felix.Checking.Recursion.Relation
    ( RelationOperations(..)
    , RelationLaws(..)
    , relationSupportTargets
    , subtermRelation
    , proveSubtermWellFounded
    ) where

import Base hiding (product)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof
import Felix.Checking.Recursion.Construction qualified as Recursion

import Control.Monad (foldM)

type Term = CanonicalTerm ObjectId
type Build = Either KernelProofBuildError

data RelationOperations = RelationOperations
    { relationOn :: !ObjectId
    , subset :: !ObjectId
    , product :: !ObjectId
    , relation :: !ObjectId
    , wellFounded :: !ObjectId
    }

data RelationLaws a = RelationLaws
    { relationMembership :: !a
    , relationBound :: !a
    , binaryRelation :: !a
    , inductionConverse :: !a
    } deriving stock (Functor, Foldable, Traversable)

-- Independently prepared contracts for the imported library facts. In
-- particular, a source marker supplies discovery, not proof authority.
relationSupportTargets :: RelationOperations -> RelationLaws Term
relationSupportTargets ops = RelationLaws
    (CForall TySet (CForall predicateType (CForall TySet (CForall TySet
        (CEq TyProp (edge (formed (CBound 3) (CBound 2)) (CBound 1) (CBound 0))
            (CAnd (CAnd (member (CBound 1) (CBound 3)) (member (CBound 0) (CBound 3)))
                (apply (CBound 2) [CBound 1, CBound 0])))))))
    (CForall TySet (CForall predicateType (bounded (formed (CBound 1) (CBound 0)) (CBound 1))))
    (CForall TySet (CForall TySet (CImp (bounded (CBound 1) (CBound 0)) (isRelation (CBound 1)))))
    (CForall TySet (CForall TySet (CImp (isRelation (CBound 1))
        (CImp (inductionPrinciple (CBound 0) (CBound 1))
            (apply (CGlobal (wellFounded ops)) [CBound 0, CBound 1])))))
  where
    predicateType = TyArrow TySet (TyArrow TySet TyProp)
    formed a p = apply (CGlobal (relationOn ops)) [a,p]
    bounded r a = apply (CGlobal (subset ops)) [r, apply (CGlobal (product ops)) [a,a]]
    isRelation r = CApp (CGlobal (relation ops)) r

inductionPrinciple :: Term -> Term -> Term
inductionPrinciple carrier r = CForall (TyArrow TySet TyProp)
    (CImp (progressive (shift carrier) (shift r) (CBound 0))
        (CForall TySet (CImp (member (CBound 0) (shift (shift carrier)))
            (CApp (CBound 1) (CBound 0)))))

progressive :: Term -> Term -> Term -> Term
progressive carrier r p = CForall TySet (CImp (member (CBound 0) (shift carrier))
    (CImp (CForall TySet (CImp
        (CAnd (member (CBound 0) (shift (shift carrier)))
            (edge (shift (shift r)) (CBound 0) (CBound 1)))
        (CApp (shift (shift p)) (CBound 0))))
        (CApp (shift p) (CBound 0))))

subtermRelation :: Int -> RelationOperations -> Term -> NonEmpty Datatype.Clause -> Build Term
subtermRelation width ops carrier clauses = do
    predicate <- subtermLambda width carrier clauses
    pure (apply (CGlobal (relationOn ops)) [carrier, predicate])

subtermLambda :: Int -> Term -> NonEmpty Datatype.Clause -> Build Term
subtermLambda width carrier clauses =
    CLam TySet . CLam TySet <$> Recursion.subtermPredicate (width + 2)
        (shift (shift carrier)) clauses (CBound 1) (CBound 0)

proveSubtermWellFounded
    :: ProofContext ObjectId -> RelationOperations -> RelationLaws Datatype.ProofImport
    -> Term -> NonEmpty Datatype.Clause -> Datatype.ProofImport -> [Term]
    -> Build (BuiltProof ObjectId)
proveSubtermWellFounded root ops laws carrier clauses subtermInduction arguments = do
    let width = length (proofContextTypes root)
    predicate <- subtermLambda width carrier clauses
    r <- subtermRelation width ops carrier clauses
    bounded <- use root (relationBound laws) [carrier, predicate]
    binary <- use root (binaryRelation laws) [r, carrier]
    isRelation <- implicationEliminationProof root binary bounded
    ordinaryInduction <- forallIntroductionProof root (TyArrow TySet TyProp) \withPredicate _ -> do
        let d = shift carrier
            p = CBound 0
        assume withPredicate (progressive d (shift r) p) \withProgress -> do
            -- Prove the induction step for the logical subterm predicate by
            -- transporting each graph predecessor through the membership law.
            steps <- forallIntroductionProof withProgress TySet \withParent _ -> do
                let d' = shift d
                    p' = shift p
                    parent = CBound 0
                assume withParent (member parent d') \withMember -> do
                    children <- Recursion.subtermPredicate (width + 3) (shift d') clauses (CBound 0) (shift parent)
                    let hypotheses = CForall TySet (CImp children (CApp (shift p') (CBound 0)))
                    assume withMember hypotheses \withChildren -> do
                        predecessors <- forallIntroductionProof withChildren TySet \withChild _ -> do
                            let child = CBound 0
                                parent' = shift parent
                                d'' = shift d'
                                r' = shift (shift (shift r))
                            assume withChild (CAnd (member child d'') (edge r' child parent')) \context -> do
                                membership <- use context (relationMembership laws)
                                    [d'', shift (shift (shift predicate)), child, parent']
                                graphEdge <- known context (edge r' child parent')
                                description <- equalityModusPonensProof context membership graphEdge
                                logicalEdge <- conjunctionRightProof context description
                                inductionHypothesis <- known context (shift hypotheses)
                                instance' <- scopedTerm context child >>= forallEliminationProof context inductionHypothesis
                                childDescription <- Recursion.subtermPredicate (width + 3) d'' clauses child parent'
                                converted <- scopedTerm context childDescription >>= conversionProof context logicalEdge
                                implicationEliminationProof context instance' converted
                        step <- known withChildren (shift (progressive d (shift r) p))
                        atParent <- scopedTerm withChildren parent >>= forallEliminationProof withChildren step
                        inCarrier <- known withChildren (member parent d')
                        applies <- implicationEliminationProof withChildren atParent inCarrier
                        implicationEliminationProof withChildren applies predecessors
            specialized <- use withProgress subtermInduction ((shift <$> arguments) <> [p])
            implicationEliminationProof withProgress specialized steps
    converse <- use root (inductionConverse laws) [r, carrier]
    needsInduction <- implicationEliminationProof root converse isRelation
    implicationEliminationProof root needsInduction ordinaryInduction

shift :: Term -> Term
shift = shiftCanonical 1 0

apply :: Term -> [Term] -> Term
apply = foldl' CApp

member :: Term -> Term -> Term
member a b = apply (CIntrinsic Member) [a,b]

edge :: Term -> Term -> Term -> Term
edge r a b = member (apply (CIntrinsic OrderedPair) [a,b]) r

assume :: ProofContext ObjectId -> Term -> (ProofContext ObjectId -> Build (BuiltProof ObjectId)) -> Build (BuiltProof ObjectId)
assume context proposition body = scopedTerm context proposition >>= \checked ->
    implicationIntroductionProof context checked (\extended _ -> body extended)

known :: ProofContext ObjectId -> Term -> Build (BuiltProof ObjectId)
known context target = do
    premises <- traverse (hypothesisProof context) (proofContextHypotheses context)
    goal <- scopedTerm context target
    structuralLogicalProof context premises goal >>= maybe (Left (ProofStructuralCompositionMismatch "subterm relation proof lost a premise")) pure

use :: ProofContext ObjectId -> Datatype.ProofImport -> [Term] -> Build (BuiltProof ObjectId)
use context (index, target) arguments = do
    proof <- importedProof context index target
    foldM (\current argument -> scopedTerm context argument >>= forallEliminationProof context current) proof arguments
