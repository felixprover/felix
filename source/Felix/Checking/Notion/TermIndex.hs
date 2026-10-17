{-# LANGUAGE NoImplicitPrelude #-}

-- | Shared structural interning for formation support and request tables.
-- Node IDs are local to one append-only table and carry no proof authority.
module Felix.Checking.Notion.TermIndex
    ( Node(..)
    , Nodes
    , nodeValues
    , nodeSizes
    , nodeVisits
    , nodeCount
    , closedNodeValue
    , emptyNodes
    , children
    , indexWork
    , intern
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Core (canonicalClosedWith, compareCanonicalWith)
import Control.Monad (foldM)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Numeric.Natural (Natural)

-- Child IDs make equality independent of the expanded size of a shared term.
-- Leaves and provider identities are atomic keys, as in the formation calculus.
data Node variable
    = Leaf !variable
    | Closed !Int
    | Provider !SourceProviderHead ![Int]
    | Pair !Int !Int
    deriving (Eq, Ord)

data Nodes variable = Nodes
    { leafIds :: !(Map variable Int)
    , branchIds :: !(Map (Node variable) Int)
    , nodeValues :: !(IntMap.IntMap (Node variable))
    , nodeSizes :: !(IntMap.IntMap Natural)
    , nodeVisits :: !Natural
    , closedIndex :: !(Seq.Seq (ClosedSetValue, Int))
    , closedValues :: !(IntMap.IntMap ClosedSetValue)
    }

emptyNodes :: Nodes variable
emptyNodes = Nodes Map.empty Map.empty IntMap.empty IntMap.empty 0 Seq.empty IntMap.empty

-- These balanced maps cache their sizes; IntMap.size traverses its tree.
-- Diagnostics must not walk the shared node catalogue on each query.
nodeCount :: Nodes variable -> Int
nodeCount nodes = Map.size (leafIds nodes) + Map.size (branchIds nodes)

closedNodeValue :: Nodes variable -> Int -> ClosedSetValue
closedNodeValue nodes identifier = closedValues nodes IntMap.! identifier

children :: Node variable -> [Int]
children = \case
    Leaf{} -> []
    Closed{} -> []
    Provider _ arguments -> arguments
    Pair left right -> [left,right]

-- A conservative comparison allowance for the balanced map's shallow keys.
-- Each comparison visits at most one constructor plus the candidate's child
-- IDs. Unlike derived ordering on source terms, it cannot traverse subtrees.
indexWork :: Int -> Natural -> Natural
indexWork size width = width * (2 * bits (fromIntegral size + 1) + 1)
  where
    bits :: Natural -> Natural
    bits 0 = 0
    bits n = 1 + bits (n `div` 2)

intern
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> SetTermTemplate variable -> Nodes variable -> m (Int, Nodes variable)
intern charge term original = do
    charge 1
    let initial = original {nodeVisits = nodeVisits original + 1}
    (node, nodes) <- case term of
        TemplateVariable variable -> pure (Leaf variable, initial)
        TemplateClosed value -> do
            (identifier,next) <- internClosed charge value initial
            pure (Closed identifier,next)
        TemplateProvider provider arguments -> do
            (reversed, final) <- foldM (\(ids, current) argument -> do
                (identifier, next) <- intern charge argument current
                pure (identifier : ids, next)) ([], initial) arguments
            pure (Provider provider (reverse reversed), final)
        TemplateOrderedPair left right -> do
            (a, afterLeft) <- intern charge left initial
            (b, afterRight) <- intern charge right afterLeft
            pure (Pair a b, afterRight)
    -- Leaves have their own small index: repeated variables must not search
    -- through every provider and pair in the term universe.
    let identifier = nodeCount nodes
        retain previous = (previous, Just (fromMaybe identifier previous))
        (size, width, found, updated) = case node of
            Leaf variable ->
                let (previous, ids) = Map.alterF retain variable (leafIds nodes)
                in (Map.size (leafIds nodes), 1, previous, nodes {leafIds = ids})
            _ ->
                let (previous, ids) = Map.alterF retain node (branchIds nodes)
                in (Map.size (branchIds nodes), 1 + fromIntegral (length (children node)),
                    previous, nodes {branchIds = ids})
    -- Lookup and insertion share one balanced-tree traversal, including when
    -- the node was already interned by support or another request.
    charge (indexWork size width)
    case found of
        Just previous -> pure (previous, nodes)
        Nothing -> do
            let termSize = 1 + sum [nodeSizes nodes IntMap.! child | child <- children node]
            pure (identifier, updated
                { nodeValues = IntMap.insert identifier node (nodeValues nodes)
                , nodeSizes = IntMap.insert identifier termSize (nodeSizes nodes) })

-- Closed mathematical payloads have their own exact, charged comparison
-- index. Only its local integer IDs occur in ordinary node Ord keys; neither
-- their Core subterms nor their binders are exposed to formation support.
internClosed :: Monad m => (Natural -> m ()) -> ClosedSetValue -> Nodes variable -> m (Int, Nodes variable)
internClosed charge value initial = do
    closed <- canonicalClosedWith (charge 1) (closedSetValueTerm value)
    if not closed then error "an admitted closed value captured a binder" else search 0 (Seq.length sorted)
  where
    sorted = closedIndex initial
    navigation = indexWork (Seq.length sorted) 1
    search lower upper
        | lower == upper = do
            charge (2 * navigation)
            let identifier = Seq.length sorted
            pure (identifier,initial
                {closedIndex = Seq.insertAt lower (value,identifier) sorted,
                 closedValues = IntMap.insert identifier value (closedValues initial)})
        | otherwise = do
            charge navigation
            let middle = lower + (upper - lower) `div` 2
                (candidate,identifier) = Seq.index sorted middle
            ordering <- compareCanonicalWith (charge 1) (closedSetValueTerm value) (closedSetValueTerm candidate)
            case ordering of
                EQ -> pure (identifier,initial)
                LT -> search lower middle
                GT -> search (middle + 1) upper
