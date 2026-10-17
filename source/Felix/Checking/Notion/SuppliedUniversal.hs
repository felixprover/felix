{-# LANGUAGE NoImplicitPrelude #-}

-- | Structural matching of one complete, supplied universal. The matcher
-- neither chooses outer parameters nor asks the notion evaluator for facts.
module Felix.Checking.Notion.SuppliedUniversal
    ( DescribedAtom
    , UniversalAdapter
    , adapterSource
    , adapterTarget
    , adapterEliminations
    , adapterResult
    , adapterCost
    , universalFormula
    , SuppliedIndex
    , emptySuppliedIndex
    , insertSuppliedSources
    , prepareSuppliedIndex
    , suppliedCandidates
    , sameUniversalAtom
    , matchUniversal
    ) where

import Base
import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Data.Ord (Down(..))
import Data.Set qualified as Set
import Felix.Checking.Notion.Rule (AtomSignature, atomSignature)
import Felix.Checking.Notion.TermIndex (indexWork)

import Felix.Checking.Core
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Semantic
import Numeric.Natural (Natural)

type DescribedAtom variable = (Maybe (AtomTemplate (SetTermTemplate (UniversalOperand variable))), CanonicalTerm ObjectId)

-- Guard references count the target's antecedent blocks in source order.
-- Binder arguments count its set binders in source order. Exact syntax stays
-- available for introduction; selectors reconstruct the source's guard trees.
data UniversalAdapter = UniversalAdapter
    { adapterSource :: !(UniversalBody (CanonicalTerm ObjectId))
    , adapterTarget :: !(UniversalBody (CanonicalTerm ObjectId))
    , adapterEliminations :: ![UniversalElimination Natural (AtomTree (Natural, ConjunctionPath))]
    , adapterResult :: !(AtomTree ConjunctionPath)
    , adapterUnitCost :: !(Natural, Natural)
    }

universalFormula :: UniversalBody (CanonicalTerm ObjectId) -> CanonicalTerm ObjectId
universalFormula = \case
    UniversalBind nested -> CForall TySet (universalFormula nested)
    UniversalRequire guard nested -> CImp (atoms guard) (universalFormula nested)
    UniversalReturn result -> atoms result
  where
    atoms (AtomLeaf atom) = atom
    atoms (AtomAnd left right) = CAnd (atoms left) (atoms right)

matchUniversal
    :: Monad m => (Natural -> m ())
    -> (AtomTemplate (SetTermTemplate (UniversalOperand variable)) -> AtomTemplate (SetTermTemplate (UniversalOperand variable)) -> m Bool)
    -> UniversalBody (DescribedAtom variable) -> UniversalBody (DescribedAtom variable)
    -> m (Maybe UniversalAdapter)
matchUniversal charge same supplied requested = do
    (sourceBinders, _sourceGuards, sourceResult, sourceSteps) <- flatten 0 0 supplied
    (targetBinders, targetGuards, targetResult, targetSteps) <- flatten 0 0 requested
    if sourceBinders /= targetBinders then pure Nothing else do
        eliminations <- traverse (elimination targetGuards) sourceSteps
        result <- traverse (findResult sourceResult . fst) targetResult
        charge (fromIntegral (length eliminations))
        case (sequence eliminations, sequence result) of
            (Just steps, Just projections) -> do
                sourceCost <- foldM eliminationCost (1,1) steps
                (nodes,depth) <- projectionCost sourceCost projections
                let introductions = fromIntegral (length targetSteps)
                charge introductions
                pure (Just (UniversalAdapter (snd <$> supplied) (snd <$> requested) steps projections
                    (nodes + introductions,depth + introductions)))
            _ -> pure Nothing
  where
    pathCost ConjunctionHere = charge 1 >> pure 0
    pathCost (ConjunctionLeft rest) = charge 1 >> ((1 +) <$> pathCost rest)
    pathCost (ConjunctionRight rest) = charge 1 >> ((1 +) <$> pathCost rest)
    guardCost (AtomLeaf (_,path)) = do
        size <- pathCost path
        pure (size + 1,size + 1)
    guardCost (AtomAnd left right) = do
        charge 1
        (n,d) <- guardCost left
        (m,e) <- guardCost right
        pure (n + m + 1,max d e + 1)
    eliminationCost (n,d) (EliminateBinder _) = charge 1 >> pure (n+1,d+1)
    eliminationCost (n,d) (EliminateGuard tree) = do
        charge 1
        (m,e) <- guardCost tree
        pure (n+m+1,max d e+1)
    projectionCost (n,d) (AtomLeaf path) = do
        size <- pathCost path
        pure (n+size,d+size)
    projectionCost cost (AtomAnd left right) = do
        charge 1
        (n,d) <- projectionCost cost left
        (m,e) <- projectionCost cost right
        pure (n+m+1,max d e+1)
    compareAtom (Just left) (Just right) = same left right
    compareAtom _ _ = charge 1 >> pure False
    flatten binder block = \case
        UniversalBind nested -> do
            charge 1
            (count, guards, result, steps) <- flatten (binder + 1) block nested
            pure (count, guards, result, EliminateBinder binder : steps)
        UniversalRequire guard nested -> do
            charge 1
            (count, guards, result, steps) <- flatten binder (block + 1) nested
            leaves <- traverse (\(path, atom) -> charge 1 >> pure (binder, block, path, fst atom)) (atomTreeLeaves guard)
            pure (count, leaves <> guards, result, EliminateGuard (binder, fst <$> guard) : steps)
        UniversalReturn result -> charge 1 >> pure (binder, [], result, [])
    findGuard [] _ _ = pure Nothing
    findGuard ((depth, block, path, atom):rest) requestedDepth wanted = do
        charge 1
        matched <- if depth == requestedDepth then compareAtom atom wanted else pure False
        if matched then pure (Just (block,path)) else findGuard rest requestedDepth wanted
    elimination _ (EliminateBinder binder) = charge 1 >> pure (Just (EliminateBinder binder))
    elimination guards (EliminateGuard (depth, atoms)) = do
        references <- traverse (findGuard guards depth) atoms
        pure (EliminateGuard <$> sequence references)
    findResult source wanted = go (atomTreeLeaves source)
      where
        go [] = pure Nothing
        go ((path,(atom,_)):rest) = do
            charge 1
            matches <- compareAtom atom wanted
            if matches then pure (Just path) else go rest

-- Compare rich source keys, including written provider arguments that may be
-- erased by transparent lowering. Core equality is used only for closed leaves.
sameUniversalAtom
    :: (Monad m, Eq variable) => (Natural -> m ())
    -> AtomTemplate (SetTermTemplate (UniversalOperand variable))
    -> AtomTemplate (SetTermTemplate (UniversalOperand variable)) -> m Bool
sameUniversalAtom charge left right = do
    charge 1
    case (left,right) of
        (NegativeAtomTemplate a,NegativeAtomTemplate b) -> sameUniversalAtom charge a b
        (GlobalAtomTemplate a xs,GlobalAtomTemplate b ys) | a == b -> terms (toList xs) (toList ys)
        (StructureAtomTemplate a xs,StructureAtomTemplate b ys) | a == b -> terms (toList xs) (toList ys)
        (ExactStructureAtomTemplate a x,ExactStructureAtomTemplate b y) | a == b -> term x y
        (MembershipAtomTemplate x a,MembershipAtomTemplate y b) -> terms [x,a] [y,b]
        _ -> pure False
  where
    terms [] [] = pure True
    terms (a:as) (b:bs) = term a b >>= \same -> if same then terms as bs else pure False
    terms _ _ = charge 1 >> pure False
    term a b = do
        charge 1
        case (a,b) of
            (TemplateClosed x,TemplateClosed y) -> (== EQ) <$> compareCanonicalWith (charge 1)
                (closedSetValueTerm x) (closedSetValueTerm y)
            (TemplateVariable x,TemplateVariable y) -> pure (x == y)
            (TemplateProvider x xs,TemplateProvider y ys) | x == y -> terms (toList xs) (toList ys)
            (TemplateOrderedPair x y,TemplateOrderedPair z w) -> terms [x,y] [z,w]
            _ -> pure False

-- Result postings admit stronger supplied conjunctions. Guard inclusion and
-- exact operand matching remain certificate checks after candidate selection.
data SuppliedIndex variable source = SuppliedIndex
    !Natural
    !(Map (Down Natural, Natural) (source, UniversalBody (DescribedAtom variable)))
    !(Map (Natural, AtomSignature) (Set (Down Natural, Natural)))

emptySuppliedIndex :: SuppliedIndex variable source
emptySuppliedIndex = SuppliedIndex 0 Map.empty Map.empty

prepareSuppliedIndex
    :: Monad m => (Natural -> m ()) -> [(source, UniversalBody (DescribedAtom variable))]
    -> m (SuppliedIndex variable source)
prepareSuppliedIndex charge sources = insertSuppliedSources charge sources emptySuppliedIndex

-- A source batch precedes older sources, while retaining its own view order.
-- Existing descriptions and postings are shared when the lexical scope grows.
insertSuppliedSources
    :: Monad m => (Natural -> m ()) -> [(source, UniversalBody (DescribedAtom variable))]
    -> SuppliedIndex variable source -> m (SuppliedIndex variable source)
insertSuppliedSources charge added (SuppliedIndex count sources postings) = do
    charge (fromIntegral (length added))
    let total = count + fromIntegral (length added)
    (nextSources, nextPostings) <- foldM (add total) (sources, postings) (zip [0..] added)
    pure (SuppliedIndex total nextSources nextPostings)
  where
    add total (knownSources, known) (offset, source@(_, body)) = do
        let ordinal = (Down total, offset)
        (binders, heads) <- resultHeads charge body
        indexed <- foldM (\entries head' -> do
            charge (indexWork (Map.size entries) 3)
            let bucket = Map.findWithDefault Set.empty (binders,head') entries
            charge (indexWork (Set.size bucket) 3)
            pure (Map.insert (binders,head') (Set.insert ordinal bucket) entries)) known (Set.toAscList heads)
        charge (indexWork (Map.size knownSources) 1)
        pure (Map.insert ordinal source knownSources, indexed)

suppliedCandidates
    :: Monad m => (Natural -> m ()) -> UniversalBody (DescribedAtom variable)
    -> SuppliedIndex variable source -> m [(source, UniversalBody (DescribedAtom variable))]
suppliedCandidates charge target (SuppliedIndex _ sources postings) = do
    (binders, heads) <- resultHeads charge target
    candidates <- foldM (\prior head' -> do
        charge (indexWork (Map.size postings) 1)
        let bucket = Map.findWithDefault Set.empty (binders,head') postings
        case prior of
            Nothing -> pure (Just bucket)
            Just known -> do
                charge (fromIntegral (Set.size known + Set.size bucket))
                pure (Just (Set.intersection known bucket))) Nothing (Set.toAscList heads)
    for (maybe [] Set.toAscList candidates) \ordinal -> do
        charge (indexWork (Map.size sources) 1)
        pure (sources Map.! ordinal)

resultHeads :: Monad m => (Natural -> m ()) -> UniversalBody (DescribedAtom variable)
    -> m (Natural, Set AtomSignature)
resultHeads charge = go 0
  where
    go binders body = charge 1 >> case body of
        UniversalBind nested -> go (binders + 1) nested
        UniversalRequire _ nested -> go binders nested
        UniversalReturn result -> (\heads -> (binders,heads)) <$> foldM (\known (key,_) -> do
            charge (indexWork (Set.size known) 3)
            pure (maybe known (\atom -> Set.insert (atomSignature atom) known) key)) Set.empty result

-- The adapter proves S -> T with a private unit-cost source hypothesis,
-- then applies the supplied source proof once in the root context.
adapterCost :: Natural -> Natural -> UniversalAdapter -> (Natural,Natural)
adapterCost sourceNodes sourceDepth adapter =
    let (nodes,depth) = adapterUnitCost adapter
    in (nodes + sourceNodes + 2, max (depth + 1) sourceDepth + 1)
