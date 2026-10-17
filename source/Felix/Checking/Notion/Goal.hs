{-# LANGUAGE NoImplicitPrelude #-}

-- | An admitted proposition and its structural proof operations. Exact truth
-- remains an alternative at every node. Atomic capabilities come exclusively
-- from source metadata; inspecting a connective never discovers a predicate.
module Felix.Checking.Notion.Goal
    ( GoalPlan(..), GoalOperation(..), compileGoal, goalChildren, goalNeedsGroundInputs, foldGoal
    ) where

import Base
import Felix.Checking.Core (CanonicalTerm(..), CoreType(..))
import Felix.Checking.Notion.SourceEvidence
import Numeric.Natural (Natural)

data GoalPlan global term atom = GoalPlan
    { goalFormula :: !(CanonicalTerm global)
    , goalEvidence :: !(SourceEvidence term atom)
    , goalOperation :: !(GoalOperation global term atom)
    -- Syntactic admission of finite witness search, not a claim about the
    -- transitive dependencies or termination of this node's producers.
    , goalPositive :: !Bool
    }

data GoalOperation global term atom
    = ExactGoal
    | AtomicGoal !atom
    | TruthGoal
    | EqualityGoal !(CanonicalTerm global) !(CanonicalTerm global)
    | ConjunctionGoal !(GoalPlan global term atom) !(GoalPlan global term atom)
    | DisjunctionGoal !(GoalPlan global term atom) !(GoalPlan global term atom)
    | ImplicationGoal !(GoalPlan global term atom) !(GoalPlan global term atom)
    | BiconditionalGoal !(GoalPlan global term atom) !(GoalPlan global term atom)
    | UniversalGoal !(GoalPlan global term atom)
    | ExistentialGoal !(GoalPlan global term atom)

-- Children share their written descriptions with the parent. No normalization
-- into alternatives or conjunctions occurs here. A complete opaque description
-- stays complete when a logical operation opens it: even an empty input list
-- must not silently restore operand discovery in a child scope.
compileGoal
    :: Monad m => m () -> CanonicalTerm global -> SourceEvidence term atom
    -> m (GoalPlan global term atom)
compileGoal charge = go
  where
    go formula evidence = do
        charge
        let described = body evidence
            opaque = case described of
                SourceInputs{} -> SourceInputs Nothing []
                _ -> SourceResidual Nothing
            binary constructor left right a b = constructor <$> go left a <*> go right b
            unary constructor nested description = constructor <$> go nested description
        operation <- case (described,formula) of
            (SourceAtom atom,_) -> pure (AtomicGoal atom)
            (_,CTruth) -> pure TruthGoal
            (_,CEq TySet left right) -> pure (EqualityGoal left right)
            (_,CAnd left right) -> let (a,b) = case described of
                                          SourceAnd x y -> (x,y)
                                          _ -> (opaque,opaque)
                in binary ConjunctionGoal left right a b
            (_,COr left right) -> let (a,b) = case described of
                                         SourceOr x y -> (x,y)
                                         _ -> (opaque,opaque)
                in binary DisjunctionGoal left right a b
            (_,CImp left right) -> let (a,b) = case described of
                                          SourceRequire x y -> (x,y)
                                          _ -> (opaque,opaque)
                in binary ImplicationGoal left right a b
            (_,CEq TyProp left right) -> let (a,b) = case described of
                                                SourceIff x y -> (x,y)
                                                _ -> (opaque,opaque)
                in binary BiconditionalGoal left right a b
            (_,CForall TySet nested) -> unary UniversalGoal nested
                (case described of SourceBind value -> value; _ -> opaque)
            (_,CExists TySet nested) -> unary ExistentialGoal nested
                (case described of SourceExists value -> value; _ -> opaque)
            _ -> pure ExactGoal
        pure (GoalPlan formula evidence operation (positive operation))
    body (SourceWithInputs _ nested) = body nested
    body expression = expression
    positive = \case
        AtomicGoal{} -> True
        TruthGoal -> True
        EqualityGoal{} -> True
        ConjunctionGoal a b -> goalPositive a && goalPositive b
        DisjunctionGoal a b -> goalPositive a && goalPositive b
        ExistentialGoal nested -> goalPositive nested
        ExactGoal -> False
        ImplicationGoal{} -> False
        BiconditionalGoal{} -> False
        UniversalGoal{} -> False

goalChildren :: GoalPlan global term atom -> [GoalPlan global term atom]
goalChildren goal = case goalOperation goal of
    ExactGoal -> []
    AtomicGoal{} -> []
    TruthGoal -> []
    EqualityGoal{} -> []
    ConjunctionGoal a b -> [a,b]
    DisjunctionGoal a b -> [a,b]
    ImplicationGoal a b -> [a,b]
    BiconditionalGoal a b -> [a,b]
    UniversalGoal body -> [body]
    ExistentialGoal body -> [body]

-- Relational introductions have their own clauses. Only these operations need
-- a concrete formula before the scope owner can construct their evidence.
goalNeedsGroundInputs :: GoalPlan global term atom -> Bool
goalNeedsGroundInputs goal = case goalOperation goal of
    TruthGoal -> True
    EqualityGoal{} -> True
    ImplicationGoal{} -> True
    BiconditionalGoal{} -> True
    UniversalGoal{} -> True
    _ -> False

-- Dependency selection precedes proof search. Children behind introductions
-- can request ordinary producers even when the exact parent has no producer.
-- Binder contexts belong to the formula node, not to a prospective witness.
foldGoal
    :: Monad m => (Natural -> CanonicalTerm global -> Maybe atom -> [value] -> m value)
    -> GoalPlan global term atom -> m value
foldGoal describe = go 0
  where
    go depth plan = do
        let nested = case goalOperation plan of UniversalGoal{} -> depth+1; ExistentialGoal{} -> depth+1; _ -> depth
        children <- traverse (go nested) (goalChildren plan)
        describe depth (goalFormula plan) (case goalOperation plan of AtomicGoal atom -> Just atom; _ -> Nothing) children
