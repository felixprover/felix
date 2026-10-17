{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Adapt logical constructor branches to the library's codomain-free
-- well-founded recursion theorem. Graphs stay inside this construction.
module Felix.Checking.Recursion.Graph
    ( GraphOperations(..)
    , GraphLaws(..)
    , graphSupportTargets
    , branchGraphRelation
    , recursionGraph
    , proveRelationStep
    , proveGraphProperty
    , proveConstructorEquation
    , proveGraphDefault
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof
import Felix.Checking.Recursion.Construction qualified as Recursion
import Felix.Checking.Recursion.Relation qualified as Relation

import Control.Monad (foldM)
import Data.Bifunctor (first)
import Numeric.Natural (Natural)

type Term = CanonicalTerm ObjectId
type Context = ProofContext ObjectId
type Proof = BuiltProof ObjectId
type Build = Either KernelProofBuildError

data GraphOperations = GraphOperations
    { graphRelationOperations :: !Relation.RelationOperations
    , recursion :: !ObjectId
    , relationStep :: !ObjectId
    , history :: !ObjectId
    , graphFunction :: !ObjectId
    , graphApply :: !ObjectId
    , domain :: !ObjectId
    , restrict :: !ObjectId
    , predecessors :: !ObjectId
    }

data GraphLaws a = GraphLaws
    { stepCharacterization :: !a
    , recursionFunction :: !a
    , recursionDomain :: !a
    , recursionSpecification :: !a
    , restrictionApply :: !a
    , predecessorMembership :: !a
    , graphDefault :: !a
    } deriving stock (Functor, Foldable, Traversable)

graphSupportTargets :: GraphOperations -> GraphLaws Term
graphSupportTargets ops = GraphLaws
    { stepCharacterization = foralls [TySet, TySet, branchRelationType] $
        CEq TyProp (step (CBound 2) (CBound 1) (CBound 0)) $
            CForall TySet $ CImp (member (CBound 0) (CBound 3)) $
                CForall TySet $ CImp (invoke (history ops) [CBound 4,CBound 3,CBound 1,CBound 0]) $
                    uniqueResult (CBound 2) (CBound 1) (CBound 0)
    , recursionFunction = recursionGuard (invoke (graphFunction ops) [graph])
    , recursionDomain = recursionGuard (CEq TySet (invoke (domain ops) [graph]) (CBound 1))
    , recursionSpecification = recursionGuard $
        CImp (step (CBound 1) (CBound 2) (CBound 0)) $
            CForall TySet $ CImp (member (CBound 0) (CBound 2)) $
                apply (CBound 1) [CBound 0,
                    invoke (restrict ops) [shift graph, invoke (predecessors ops) [CBound 3,CBound 0]],
                    invoke (graphApply ops) [shift graph,CBound 0]]
    , restrictionApply = foralls [TySet,TySet,TySet] $
        CImp (member (CBound 2) (CBound 1)) $
            CEq TySet (invoke (graphApply ops) [invoke (restrict ops) [CBound 0,CBound 1],CBound 2])
                (invoke (graphApply ops) [CBound 0,CBound 2])
    , predecessorMembership = foralls [TySet,TySet,TySet] $
        CEq TyProp (member (CBound 2) (invoke (predecessors ops) [CBound 1,CBound 0]))
            (edge (CBound 1) (CBound 2) (CBound 0))
    , graphDefault = foralls [TySet,TySet] $
        CImp (CNot (member (CBound 1) (invoke (domain ops) [CBound 0]))) $
            CEq TySet (invoke (graphApply ops) [CBound 0,CBound 1]) (CIntrinsic Empty)
    }
  where
    relations = graphRelationOperations ops
    step a r s = invoke (relationStep ops) [a,r,s]
    graph = invoke (recursion ops) [CBound 1,CBound 2,CBound 0]
    recursionGuard conclusion = foralls [TySet,TySet]
        (CImp (invoke (Relation.subset relations) [CBound 1,invoke (Relation.product relations) [CBound 0,CBound 0]])
            (CImp (invoke (Relation.wellFounded relations) [CBound 0,CBound 1])
                (CForall branchRelationType conclusion)))

uniqueResult :: Term -> Term -> Term -> Term
uniqueResult predicate element h = CExists TySet $
    CAnd (apply (shift predicate) [shift element,shift h,CBound 0]) $
        CForall TySet $ CImp (apply (shift (shift predicate)) [shift (shift element),shift (shift h),CBound 0]) $
            CEq TySet (CBound 0) (CBound 1)

branchRelationType :: CoreType
branchRelationType = TyArrow TySet (TyArrow TySet (TyArrow TySet TyProp))

branchGraphRelation
    :: Int -> GraphOperations -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term -> Build Term
branchGraphRelation width ops carrier clauses branches = do
    let liftTerm = shiftCanonical 3 0
        evaluate = CLam TySet (invoke (graphApply ops) [CBound 2,CBound 0])
    body <- Recursion.branchRelation (width + 3) (liftTerm carrier) clauses (liftTerm <$> branches)
        evaluate (CBound 2) (CBound 0)
    pure (CLam TySet (CLam TySet (CLam TySet body)))

recursionGraph
    :: Int -> GraphOperations -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term -> Build Term
recursionGraph width ops carrier clauses branches = do
    r <- Relation.subtermRelation width (graphRelationOperations ops) carrier clauses
    step <- branchGraphRelation width ops carrier clauses branches
    pure (invoke (recursion ops) [carrier,r,step])

proveRelationStep
    :: Context -> GraphOperations -> GraphLaws Datatype.ProofImport
    -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Datatype.ProofImport -> [Term] -> Build Proof
proveRelationStep root ops laws carrier clauses branches functionality arguments = do
    let width = length (proofContextTypes root)
    r <- Relation.subtermRelation width (graphRelationOperations ops) carrier clauses
    s <- branchGraphRelation width ops carrier clauses branches
    characterization <- use root (stepCharacterization laws) [carrier,r,s]
    premise <- forallIntroductionProof root TySet \withElement _ -> do
        assume withElement (member (CBound 0) (shift carrier)) \withMember -> do
            forallIntroductionProof withMember TySet \withHistory _ -> do
                let element = CBound 1
                    h = CBound 0
                    evaluate = CLam TySet (invoke (graphApply ops) [CBound 1,CBound 0])
                assume withHistory (invoke (history ops) [shift (shift carrier),shift (shift r),element,h]) \context -> do
                    unique <- use context functionality ((shift . shift <$> arguments) <> [element,evaluate])
                    membership <- known context (member element (shift (shift carrier)))
                    implicationEliminationProof context unique membership
    case scopedCoreTerm (builtProofStatement characterization) of
        CEq TyProp _ right -> do
            converted <- scopedTerm root right >>= conversionProof root premise
            backwards <- equalityReverseProof root characterization
            equalityModusPonensProof root backwards converted
        _ -> Left (ProofStructuralCompositionMismatch "relation step law is not a proposition equality")

-- The function, domain and specification theorems share the same guarded
-- prefix. Their remaining conclusions retain the ordinary library authority.
proveGraphProperty
    :: Context -> GraphOperations -> Relation.RelationLaws Datatype.ProofImport
    -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Datatype.ProofImport -> [Term] -> Datatype.ProofImport -> Build Proof
proveGraphProperty context ops relationLaws carrier clauses branches wellFounded arguments law = do
    let width = length (proofContextTypes context)
        relations = graphRelationOperations ops
    r <- Relation.subtermRelation width relations carrier clauses
    predicate <- subtermLambda width carrier clauses
    s <- branchGraphRelation width ops carrier clauses branches
    bounded <- use context (Relation.relationBound relationLaws) [carrier,predicate]
    wf <- use context wellFounded arguments
    theorem <- use context law [r,carrier]
    instantiated <- implicationEliminationProof context theorem bounded
        >>= \proof -> implicationEliminationProof context proof wf
    scopedTerm context s >>= forallEliminationProof context instantiated

proveConstructorEquation
    :: Context -> GraphOperations -> Relation.RelationLaws Datatype.ProofImport
    -> GraphLaws Datatype.ProofImport -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Natural -> Datatype.ProofImport -> [Term]
    -> Datatype.ProofImport -> Datatype.ProofImport -> [Term] -> Build Proof
proveConstructorEquation root ops relationLaws laws carrier clauses branches index introduction parameters
        specification functionality arguments = do
    clause <- at "constructor" (toList clauses) index
    let count = length (Datatype.clausePremises clause)
        liftTerm = shiftCanonical (fromIntegral count) 0
    introduceForalls root (replicate count TySet) \withFields -> do
        let d = liftTerm carrier
            bs = liftTerm <$> branches
            terms = CBound . fromIntegral <$> reverse [0 .. count - 1]
            width = length (proofContextTypes withFields)
            guards = Datatype.premiseTerms width d clause terms
        assumeGuards withFields guards \context -> do
            branch <- at "branch" (toList bs) index
            constructor <- Datatype.constructorTerm clause terms
            intro <- use context introduction ((liftTerm <$> parameters) <> terms)
            inCarrier <- applyGuards context intro guards
            r <- Relation.subtermRelation width (graphRelationOperations ops) d clauses
            predicate <- subtermLambda width d clauses
            graph <- recursionGraph width ops d clauses bs
            let downward = invoke (predecessors ops) [r,constructor]
                restricted = invoke (restrict ops) [graph,downward]
                evaluate = CLam TySet (invoke (graphApply ops) [shift graph,CBound 0])
                evaluateHistory = CLam TySet (invoke (graphApply ops) [shift restricted,CBound 0])
                value = invoke (graphApply ops) [graph,constructor]
            step <- use context specification ((liftTerm <$> arguments) <> [constructor])
            describesValue <- implicationEliminationProof context step inCarrier
            describedBranch <- Recursion.proveConstructorBranch context d clauses bs evaluateHistory index terms
            historyValue <- Recursion.branchValue clause branch evaluateHistory terms
            unique <- use context functionality ((liftTerm <$> arguments) <> [constructor,evaluateHistory])
                >>= \proof -> implicationEliminationProof context proof inCarrier
            -- The library specification contains beta redexes from the branch
            -- relation lambda; align it with the independently prepared branch.
            description <- Recursion.branchRelation width d clauses bs evaluateHistory constructor value
            describesValue' <- scopedTerm context description >>= conversionProof context describesValue
            toHistory <- equalUniqueValues context unique (value,describesValue') (historyValue,describedBranch)
            children <- traverse (at "recursive field" terms) (Recursion.recursiveSlots clause)
            childEqualities <- for (zip [0 ..] children) \(childIndex, child) -> do
                logicalEdge <- Recursion.proveStoredChild context d clauses index terms childIndex
                membership <- use context (Relation.relationMembership relationLaws) [d,predicate,child,constructor]
                childMember <- known context (member child d)
                bounds <- conjunctionIntroductionProof context childMember inCarrier
                description' <- conjunctionIntroductionProof context bounds logicalEdge
                backwards <- equalityReverseProof context membership
                case scopedCoreTerm (builtProofStatement membership) of
                    CEq TyProp _ right -> do
                        converted <- scopedTerm context right >>= conversionProof context description'
                        graphEdge <- equalityModusPonensProof context backwards converted
                        downwardLaw <- use context (predecessorMembership laws) [child,r,constructor]
                            >>= equalityReverseProof context
                        predecessor <- equalityModusPonensProof context downwardLaw graphEdge
                        restriction <- use context (restrictionApply laws) [child,downward,graph]
                            >>= \proof -> implicationEliminationProof context proof predecessor
                        scopedTerm context (CEq TySet (CApp evaluateHistory child) (CApp evaluate child))
                            >>= conversionProof context restriction
                    _ -> Left (ProofStructuralCompositionMismatch "relation membership law is not a proposition equality")
            fields <- Datatype.argumentTerms clause terms
            fixed <- traverse (\term -> scopedTerm context term >>= equalityReflexivityProof context) fields
            branchEquality <- scopedTerm context branch >>= equalityReflexivityProof context
            historiesAgree <- foldM (equalityCongruenceApplicationProof context) branchEquality (fixed <> childEqualities)
            equation <- composeEqualityProof context toHistory historiesAgree
            result <- Recursion.branchValue clause branch evaluate terms
            scopedTerm context (CEq TySet (CApp evaluate constructor) result) >>= conversionProof context equation

proveGraphDefault
    :: Context -> GraphOperations -> GraphLaws Datatype.ProofImport
    -> Term -> Term -> Datatype.ProofImport -> [Term] -> Build Proof
proveGraphDefault root ops laws carrier graph domainLaw arguments =
    forallIntroductionProof root TySet \withElement _ -> do
        let x = CBound 0
            g = shift graph
        assume withElement (CNot (member x (shift carrier))) \context -> do
            domainEquality <- use context domainLaw (shift <$> arguments)
                >>= equalityReverseProof context
            notInCarrier <- known context (CNot (member x (shift carrier)))
            predicate <- scopedTerm context (CLam TySet (CNot (member (shift x) (CBound 0))))
            outside <- equalityTransportProof context domainEquality predicate notInCarrier
            law <- use context (graphDefault laws) [x,g]
            converted <- scopedTerm context (CNot (member x (invoke (domain ops) [g]))) >>= conversionProof context outside
            implicationEliminationProof context law converted

equalUniqueValues :: Context -> Proof -> (Term,Proof) -> (Term,Proof) -> Build Proof
equalUniqueValues root unique (left,leftProof) (right,rightProof) = do
    premises <- buildLeftAssociatedConjunction root [unique,leftProof,rightProof]
    let statement = scopedCoreTerm (builtProofStatement premises)
    implication <- scopedTerm root statement >>= \checked -> implicationIntroductionProof root checked \context _ -> do
        unique' <- known context (scopedCoreTerm (builtProofStatement unique))
        case scopedCoreTerm (builtProofStatement unique') of
            CExists ty body -> do
                body' <- first ProofTermIllTyped (checkScopedTermUnderBinder context ty body)
                goal <- scopedTerm context (CEq TySet left right)
                existentialEliminationProof context ty body' unique' goal \extended _ _ -> do
                    selected <- scopedTerm extended body >>= hypothesisProof extended
                    atMostOne <- conjunctionRightProof extended selected
                    leftValue <- scopedTerm extended (shift left) >>= forallEliminationProof extended atMostOne
                    rightValue <- scopedTerm extended (shift right) >>= forallEliminationProof extended atMostOne
                    leftHolds <- known extended (shift (scopedCoreTerm (builtProofStatement leftProof)))
                    rightHolds <- known extended (shift (scopedCoreTerm (builtProofStatement rightProof)))
                    leftEquality <- implicationEliminationProof extended leftValue leftHolds
                    rightEquality <- implicationEliminationProof extended rightValue rightHolds >>= equalityReverseProof extended
                    composeEqualityProof extended leftEquality rightEquality
            _ -> Left (ProofStructuralCompositionMismatch "branch uniqueness is not existential")
    implicationEliminationProof root implication premises

subtermLambda :: Int -> Term -> NonEmpty Datatype.Clause -> Build Term
subtermLambda width carrier clauses = CLam TySet . CLam TySet <$>
    Recursion.subtermPredicate (width + 2) (shift (shift carrier)) clauses (CBound 1) (CBound 0)

at :: Text -> [a] -> Natural -> Build a
at description values index = maybe (Left (ProofStructuralCompositionMismatch (description <> " is missing"))) pure (nth index values)

assumeGuards :: Context -> [Term] -> (Context -> Build Proof) -> Build Proof
assumeGuards context [] body = body context
assumeGuards context (firstGuard : rest) body = assume context (foldl' CAnd firstGuard rest) body

applyGuards :: Context -> Proof -> [Term] -> Build Proof
applyGuards _ proof [] = pure proof
applyGuards context proof guards = do
    premises <- traverse (known context) guards >>= buildLeftAssociatedConjunction context
    implicationEliminationProof context proof premises

foralls :: [CoreType] -> Term -> Term
foralls = flip (foldr CForall)

shift :: Term -> Term
shift = shiftCanonical 1 0

apply :: Term -> [Term] -> Term
apply = foldl' CApp

invoke :: ObjectId -> [Term] -> Term
invoke = apply . CGlobal

member :: Term -> Term -> Term
member a b = apply (CIntrinsic Member) [a,b]

edge :: Term -> Term -> Term -> Term
edge r a b = member (apply (CIntrinsic OrderedPair) [a,b]) r

assume :: Context -> Term -> (Context -> Build Proof) -> Build Proof
assume context proposition body = scopedTerm context proposition >>= \checked ->
    implicationIntroductionProof context checked (\extended _ -> body extended)

known :: Context -> Term -> Build Proof
known context target = do
    premises <- traverse (hypothesisProof context) (proofContextHypotheses context)
    goal <- scopedTerm context target
    structuralLogicalProof context premises goal >>= maybe (Left (ProofStructuralCompositionMismatch "recursion graph proof lost a premise")) pure

use :: Context -> Datatype.ProofImport -> [Term] -> Build Proof
use context (index, target) arguments = do
    proof <- importedProof context index target
    foldM (\current argument -> scopedTerm context argument >>= forallEliminationProof context current) proof arguments
