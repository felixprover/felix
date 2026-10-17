{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | Ordered structural elimination of an already checked source proposition.
-- Binder and premise payloads identify holes in the consumer's environment;
-- these descriptions carry no proof authority or source-use permission.
module Felix.Checking.Elimination
    ( EliminationStep(..)
    , ConjunctionPath(..)
    , ConjunctionProjection(..)
    , rootConjunctionProjection
    , stepConjunctionProjection
    , definitionProjectionTarget
    , predicateProjectionTarget
    ) where

import Base
import Control.DeepSeq (NFData)
import Numeric.Natural (Natural)
import Felix.Checking.Core
    ( CoreType(..), CanonicalTerm(..)
    , firstOrderSymbolShape, canonicalDefinitionEquationTarget
    )

-- Prefixes may be shared between selected conjunction branches. Keep an
-- implication's entire antecedent as one payload: splitting its conjunction
-- for lookup does not change the proof which application must supply.
data EliminationStep binder premise
    = Instantiate !CoreType !binder
    | Apply !premise
    | ProjectLeft
    | ProjectRight

data ConjunctionPath
    = ConjunctionHere
    | ConjunctionLeft !ConjunctionPath
    | ConjunctionRight !ConjunctionPath
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- Prepared paths point towards their shared prefix. IDs belong to one path
-- table; a consumer must keep that table's paths with their original owner.
-- These are selectors, not proofs. Depth is cached for witness accounting.
data ConjunctionProjection
    = RootConjunctionProjection
    | ConjunctionProjection !Int !Natural !Bool !ConjunctionProjection

rootConjunctionProjection :: ConjunctionProjection
rootConjunctionProjection = RootConjunctionProjection

stepConjunctionProjection :: Int -> Bool -> ConjunctionProjection -> ConjunctionProjection
stepConjunctionProjection identifier right parent =
    ConjunctionProjection identifier (1 + case parent of
        RootConjunctionProjection -> 0
        ConjunctionProjection _ depth _ _ -> depth) right parent

-- Interpret a selected positive result of a canonical pointwise predicate
-- equation. Binder order and the original premise are retained exactly.
definitionProjectionTarget
    :: ConjunctionPath -> CanonicalTerm global -> Maybe (CanonicalTerm global)
definitionProjectionTarget path = go
  where
    go (CForall TySet body) = CForall TySet <$> go body
    go (CEq TyProp predicate body) = CImp predicate <$> selectConjunction path body
    go _ = Nothing

-- Generated predicates retain their lambda telescope. Opening it with the
-- canonical de Bruijn arguments is the identity substitution on its body, so
-- select first instead of copying the entire definition for every projection.
predicateProjectionTarget
    :: global -> CoreType -> CanonicalTerm global -> ConjunctionPath -> Maybe (CanonicalTerm global)
predicateProjectionTarget identity coreType body path = do
    (arity, TyProp) <- firstOrderSymbolShape coreType
    case open arity body of
        Just formula -> do
            selected <- selectConjunction path formula
            let arguments = CBound <$> reverse (take arity [0..])
                premise = foldl' CApp (CGlobal identity) arguments
            pure (foldr CForall (CImp premise selected) (replicate arity TySet))
        Nothing -> definitionProjectionTarget path (canonicalDefinitionEquationTarget identity coreType body)
  where
    open 0 term = Just term
    open count (CLam TySet term) = open (count - 1) term
    open _ _ = Nothing

selectConjunction :: ConjunctionPath -> CanonicalTerm global -> Maybe (CanonicalTerm global)
selectConjunction ConjunctionHere body = Just body
selectConjunction (ConjunctionLeft rest) (CAnd left _) = selectConjunction rest left
selectConjunction (ConjunctionRight rest) (CAnd _ right) = selectConjunction rest right
selectConjunction _ _ = Nothing
