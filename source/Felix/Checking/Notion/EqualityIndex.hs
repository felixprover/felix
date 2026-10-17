{-# LANGUAGE NoImplicitPrelude #-}

-- | Persistent endpoint classes and ordered proof edges. Class identity is a
-- candidate index only; a consumer must replay the selected equality path.
module Felix.Checking.Notion.EqualityIndex
    ( EqualityIndex, emptyEqualityIndex
    , insertEquality, representative, classMembers, adjacent
    ) where

import Base
import Felix.Checking.Notion.TermIndex (indexWork)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)

data Component vertex = Root !(Set vertex) | Parent !vertex

data EqualityIndex vertex order edge = EqualityIndex
    !(Map vertex (Map order (vertex, edge)))
    !(Map vertex (Component vertex))

emptyEqualityIndex :: EqualityIndex vertex order edge
emptyEqualityIndex = EqualityIndex Map.empty Map.empty

-- Keys are interned scope identities. Union by size bounds parent depth;
-- persistent updates never walk or rewrite unrelated components.
insertEquality
    :: (Monad m, Ord vertex, Ord order) => (Natural -> m ())
    -> order -> vertex -> vertex -> edge -> edge -> EqualityIndex vertex order edge
    -> m (EqualityIndex vertex order edge)
insertEquality charge order left right forward backward (EqualityIndex edges components) = do
    first <- addEdge left right forward edges
    nextEdges <- if left == right then pure first else addEdge right left backward first
    (leftRoot, leftMembers) <- findComponent charge left components
    (rightRoot, rightMembers) <- findComponent charge right components
    nextComponents <- if leftRoot == rightRoot then pure components else do
        let (large, largeMembers, small, smallMembers) =
                if Set.size leftMembers >= Set.size rightMembers
                then (leftRoot, leftMembers, rightRoot, rightMembers)
                else (rightRoot, rightMembers, leftRoot, leftMembers)
        charge (2 * indexWork (Map.size components) 1
            + fromIntegral (Set.size smallMembers) * indexWork (Set.size largeMembers) 1)
        pure (Map.insert small (Parent large)
            (Map.insert large (Root (Set.union largeMembers smallMembers)) components))
    pure (EqualityIndex nextEdges nextComponents)
  where
    addEdge source target proof known = do
        charge (2 * indexWork (Map.size known) 1)
        let prior = Map.findWithDefault Map.empty source known
        charge (indexWork (Map.size prior) 1)
        pure (Map.insert source (Map.insert order (target, proof) prior) known)

findComponent
    :: (Monad m, Ord vertex) => (Natural -> m ()) -> vertex
    -> Map vertex (Component vertex) -> m (vertex, Set vertex)
findComponent charge vertex components = do
    charge (indexWork (Map.size components) 1)
    case Map.lookup vertex components of
        Nothing -> pure (vertex, Set.singleton vertex)
        Just (Root members) -> pure (vertex, members)
        Just (Parent parent) -> findComponent charge parent components

representative
    :: (Monad m, Ord vertex) => (Natural -> m ()) -> vertex
    -> EqualityIndex vertex order edge -> m vertex
representative charge vertex (EqualityIndex _ components) = fst <$> findComponent charge vertex components

classMembers
    :: (Monad m, Ord vertex) => (Natural -> m ()) -> vertex
    -> EqualityIndex vertex order edge -> m (Set vertex)
classMembers charge vertex (EqualityIndex _ components) = snd <$> findComponent charge vertex components

adjacent
    :: (Monad m, Ord vertex) => (Natural -> m ()) -> vertex
    -> EqualityIndex vertex order edge -> m [(vertex, edge)]
adjacent charge vertex (EqualityIndex edges _) = do
    charge (indexWork (Map.size edges) 1)
    let found = Map.findWithDefault Map.empty vertex edges
    charge (fromIntegral (Map.size found))
    pure (Map.elems found)
