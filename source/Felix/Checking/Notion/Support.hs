{-# LANGUAGE NoImplicitPrelude #-}

-- | Fixed, one-layer formation support. Inputs have already been selected and
-- scoped by the request owner. This module grants no evidence or authority.
module Felix.Checking.Notion.Support
    ( PreparedTemplateSupport
    , emptyTemplateSupport
    , prepareTemplateSupport
    , extendTemplateSupport
    , extendOwnedTemplateSupport
    , SizeProfile
    , emptySizeProfile
    , unionSizeProfiles
    , sizeProfileGrowth
    , TemplateSupportView
    , selectTemplateSupport
    , freezeSelectedSupport
    , freezeSupport
    , freezeSupportWithCaptures
    , freezeSelectedSupportWithCaptures
    , FrozenSupport
    , SymbolicSupport
    , buildSymbolicSupport
    , symbolicSupportContains
    , symbolicSupportContainsWith
    , symbolicSupportMayContain
    , symbolicSupportMaximumTermSize
    , SupportCursor, supportCursor, nextSupportTerm, nextSupportTermWith, nextMatchingSupportTerm
    , OpaqueInterpreter(..), extendWholeSupport
    , templatePreparationCounts
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Core (CanonicalTerm(..), compareCanonicalWith, canonicalFreeIndicesWith)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.TermIndex
import Control.Monad (foldM, unless)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

data Head = ProviderHead !SourceProviderHead !Int | PairHead | ClosedHead | OpaqueHead
    deriving (Eq, Ord)

-- Source-independent descriptions. Written constructors have exact affine
-- size c + v*L, counting repeated variable occurrences. An open opaque recipe
-- has size one; L is a conservative upper bound which also excludes empty B.
-- Fixed nodes refer only to the owning frozen query's seed table. Declaration
-- preparation creates assignable slots; its immutable DAG never contains a
-- query-local node identifier.
data TemplateSlot = AssignableSlot !ViewVariableIx | FixedSeed !Int | OpaqueSlot !Int
    deriving (Eq, Ord)

-- These operations interpret one complete opaque value. Matches are private
-- membership constraints on B; they never become clause bindings or row views.
data OpaqueInterpreter m variable = OpaqueInterpreter
    { opaqueValue :: SetTermTemplate variable -> m variable
    , opaqueMatch :: Natural -> CanonicalTerm ObjectId -> variable -> m (Maybe (Map ViewVariableIx variable))
    , opaqueInstantiate :: Natural -> CanonicalTerm ObjectId
        -> Map ViewVariableIx (SetTermTemplate variable) -> m (SetTermTemplate variable)
    }

data OpaqueRecipe = OpaqueRecipe
    { recipeArity :: !Natural
    , recipeTerm :: !(CanonicalTerm ObjectId)
    , recipeParameters :: !(Set ViewVariableIx)
    , recipeCaptures :: !(Map ViewVariableIx Int)
    }

data PreparedTemplateSupport = PreparedTemplateSupport
    { templateNodes :: !(Nodes TemplateSlot)
    , templateHeads :: !(Map Head [Int])
    , templateSizes :: !(IntMap.IntMap (Natural, Natural))
    , templateOwners :: !(IntMap.IntMap (Set Int))
    , ownerTemplates :: !(IntMap.IntMap (Set Int))
    , templateProfile :: !SizeProfile
    , opaqueRecipes :: !(IntMap.IntMap OpaqueRecipe)
    , opaqueRecipeIndex :: !(Seq.Seq (OpaqueRecipe,Int))
    }

data SizeProfile = SizeProfile
    { closedMaximum :: !Natural
    , variableProfile :: !(Map Natural Natural)
    } deriving (Eq, Show)

emptySizeProfile :: SizeProfile
emptySizeProfile = SizeProfile 0 Map.empty

unionSizeProfiles :: Monad m => (Natural -> m ()) -> SizeProfile -> SizeProfile -> m SizeProfile
unionSizeProfiles charge left right = do
    profile <- foldM (\known (variables,fixed) -> do
        charge (indexWork (Map.size known) 1)
        pure (Map.insertWith max variables fixed known)) (variableProfile left)
        (Map.toAscList (variableProfile right))
    pure (SizeProfile (max (closedMaximum left) (closedMaximum right)) profile)

-- A root already contains every earlier local coefficient at a head it
-- reaches. Propagate only strict componentwise growth, once per admission;
-- repeated definition projections need not revisit dominated coefficients
-- at every ancestor. This does not remove templates or compare different v's.
sizeProfileGrowth :: Monad m => (Natural -> m ()) -> SizeProfile -> SizeProfile -> m SizeProfile
sizeProfileGrowth charge prior incoming = do
    growing <- foldM (\known (variables,fixed) -> do
        charge (indexWork (Map.size (variableProfile prior)) 1)
        case Map.lookup variables (variableProfile prior) of
            Just previous | fixed <= previous -> pure known
            _ -> do
                charge (indexWork (Map.size known) 1)
                pure (Map.insert variables fixed known)) Map.empty (Map.toAscList (variableProfile incoming))
    pure (SizeProfile (if closedMaximum incoming > closedMaximum prior then closedMaximum incoming else 0) growing)

-- A catalogue version and its complete reachable owner heads. Neither proof
-- candidate discrimination nor queries may narrow this template selection.
data TemplateSupportView = TemplateSupportView
    !PreparedTemplateSupport !(Maybe (Set Int)) !SizeProfile

selectTemplateSupport :: PreparedTemplateSupport -> Set Int -> SizeProfile -> TemplateSupportView
selectTemplateSupport prepared owners profile = TemplateSupportView prepared (Just owners) profile

data FrozenSupport variable = FrozenSupport
    { groundNodes :: !(Nodes variable)
    , seedIds :: !IntSet.IntSet
    , preparedTemplates :: !PreparedTemplateSupport
    , eligibleOwners :: !(Maybe (Set Int))
    , membershipMemo :: !(IntMap.IntMap Bool)
    , partialNodes :: !(Nodes (Maybe variable))
    , partialMemo :: !(IntMap.IntMap PartialMemo)
    , symbolicSupportMaximumTermSize :: !Natural
    , seedValues :: !(IntMap.IntMap variable)
    , valueSeeds :: !(Map variable IntSet.IntSet)
    }

-- Candidate IDs belong to the frozen ground/template tables, never to an
-- answer-derived support domain. Seeds denotes the original whole seed set.
data SupportCandidate = GroundCandidate !Int | TemplateCandidate !Int | Seeds
    deriving (Eq, Ord)

data PartialMemo = PartialMemo
    { seedPossibility :: !(Maybe Bool)
    , groundPossibilities :: !(IntMap.IntMap Bool)
    , templatePossibilities :: !(IntMap.IntMap Bool)
    }

emptyPartialMemo :: PartialMemo
emptyPartialMemo = PartialMemo Nothing IntMap.empty IntMap.empty

-- A cursor is opened only after B and T are frozen. Each step considers one
-- seed, template, or assignment. Skipped and duplicate candidates yield too,
-- allowing the evaluator to interleave enumeration with ordinary row joins.
data SupportCursor variable = SupportCursor
    !(FrozenSupport variable) !IntSet.IntSet !TemplateCursor
    -- The assignment stack chooses one seed per slot; the remaining slots
    -- have not been visited. Rejecting a partial assignment skips its entire
    -- subtree without changing the frozen domain or recovering any bindings.
    !(Maybe (Int, [(ViewVariableIx, IntSet.IntSet)], [ViewVariableIx]))
    !(Nodes variable) !IntSet.IntSet

data TemplateCursor
    = EveryTemplate !(IntMap.IntMap (Node TemplateSlot))
    | OwnedTemplates !(Set Int) !(Set Int) !(Set Int)

supportCursor :: FrozenSupport variable -> SupportCursor variable
supportCursor support = SupportCursor support (seedIds support)
    (case eligibleOwners support of
        Nothing -> EveryTemplate (nodeValues (templateNodes (preparedTemplates support)))
        Just owners -> OwnedTemplates owners Set.empty Set.empty) Nothing
    (groundNodes support) IntSet.empty

nextSupportTerm
    :: (Monad m, Ord variable) => (Natural -> m ()) -> SupportCursor variable
    -> m (Maybe (Maybe (SetTermTemplate variable), SupportCursor variable))
nextSupportTerm = nextSupportTermWith Nothing

nextSupportTermWith
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable)
    -> (Natural -> m ()) -> SupportCursor variable
    -> m (Maybe (Maybe (SetTermTemplate variable), SupportCursor variable))
nextSupportTermWith interpreter charge = nextMatchingSupportTerm interpreter charge Nothing

-- A necessary denotation condition may reject an entire template before its
-- assignments are visited. Unknown opaque recipes remain unknown here.
nextMatchingSupportTerm
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable)
    -> (Natural -> m ()) -> Maybe (SetTermTemplate (Maybe variable) -> m Bool)
    -> SupportCursor variable
    -> m (Maybe (Maybe (SetTermTemplate variable), SupportCursor variable))
nextMatchingSupportTerm interpreter charge compatible (SupportCursor support seeds pending active terms seen) = do
    charge 1
    case IntSet.minView seeds of
        Just (identifier,rest) -> do
            term <- ground identifier
            publish term rest pending active
        Nothing -> case active of
            Just (identifier,dimensions,remaining) -> do
                values <- foldM (\known (slot,choices) -> do
                    charge (indexWork (Map.size known) 1)
                    pure (Map.insert slot (IntSet.findMin choices) known)) Map.empty dimensions
                case remaining of
                    [] -> do
                        term <- instantiate values identifier
                        next <- advance dimensions []
                        publish term seeds pending ((\(chosen,rest) -> (identifier,chosen,rest)) <$> next)
                    slot:rest -> do
                        possible <- maybe (pure True) (\condition -> partial values identifier >>= condition) compatible
                        next <- if possible then pure (Just ((slot,seedIds support):dimensions,rest))
                            else advance dimensions remaining
                        pure (Just (Nothing,SupportCursor support seeds pending
                            ((\(chosen,rest') -> (identifier,chosen,rest')) <$> next) terms seen))
            Nothing -> nextTemplate pending >>= \case
                Nothing -> pure Nothing
                Just (Nothing,rest) -> pure (Just (Nothing,SupportCursor support seeds rest Nothing terms seen))
                Just (Just identifier,rest) -> do
                    charge (indexWork (nodeCount templates) 1)
                    let node = nodeValues templates IntMap.! identifier
                    possible <- maybe (pure True) (\condition -> partial Map.empty identifier >>= condition) compatible
                    variables <- if possible then slots Set.empty Set.empty [identifier] else pure Set.empty
                    let assignments = case Set.toAscList variables of
                            [] -> (identifier,[],[])
                            slot:rest -> (identifier,[(slot,seedIds support)],rest)
                        usable = possible && (Set.null variables || not (IntSet.null (seedIds support)))
                            && case node of Leaf OpaqueSlot{} -> True; Leaf{} -> False; _ -> True
                    charge (fromIntegral (Set.size variables))
                    pure (Just (Nothing,SupportCursor support seeds rest
                        (if usable then Just assignments else Nothing) terms seen))
  where
    prepared = preparedTemplates support
    templates = templateNodes prepared
    publish term rest templates' active' = do
        possible <- maybe (pure True) ($ (Just <$> term)) compatible
        if not possible then pure (Just (Nothing,SupportCursor support rest templates' active' terms seen)) else do
            (identifier,updated) <- intern charge term terms
            charge (indexWork (nodeCount updated) 1)
            let fresh = IntSet.notMember identifier seen
            pure (Just (if fresh then Just term else Nothing,
                SupportCursor support rest templates' active' updated (IntSet.insert identifier seen)))
    partial values identifier = charge 1 >> case nodeValues templates IntMap.! identifier of
        Leaf (FixedSeed seed) -> fmap Just <$> ground seed
        Leaf (AssignableSlot slot) -> do
            charge (indexWork (Map.size values) 1)
            maybe (pure (TemplateVariable Nothing)) (fmap (fmap Just) . ground) (Map.lookup slot values)
        Leaf{} -> pure (TemplateVariable Nothing)
        Closed value -> pure (TemplateClosed (closedNodeValue templates value))
        Provider provider arguments -> TemplateProvider provider . Vector.fromList <$> traverse (partial values) arguments
        Pair left right -> TemplateOrderedPair <$> partial values left <*> partial values right
    nextTemplate (EveryTemplate pending') = pure $ case IntMap.minViewWithKey pending' of
        Nothing -> Nothing
        Just ((identifier,_),rest) -> Just (Just identifier,EveryTemplate rest)
    nextTemplate (OwnedTemplates owners pending' visited) = do
        charge (indexWork (Set.size pending') 1)
        case Set.minView pending' of
            Just (identifier,rest) -> do
                charge (indexWork (Set.size visited) 1)
                let fresh = Set.notMember identifier visited
                pure (Just (if fresh then Just identifier else Nothing,
                    OwnedTemplates owners rest (Set.insert identifier visited)))
            Nothing -> do
                charge (indexWork (Set.size owners) 1)
                case Set.minView owners of
                    Nothing -> pure Nothing
                    Just (owner,rest) -> do
                        charge (indexWork (IntMap.size (ownerTemplates prepared)) 1)
                        pure (Just (Nothing,OwnedTemplates rest
                            (IntMap.findWithDefault Set.empty owner (ownerTemplates prepared)) visited))
    slots _ variables [] = pure variables
    slots visited variables (identifier:rest) = do
        charge (indexWork (Set.size visited) 1)
        if Set.member identifier visited then slots visited variables rest else do
            charge (indexWork (nodeCount templates) 1)
            let node = nodeValues templates IntMap.! identifier
                next = case node of
                    Leaf (AssignableSlot slot) -> Set.insert slot variables
                    Leaf (OpaqueSlot recipe) -> variables <> Set.difference
                        (recipeParameters (opaqueRecipes prepared IntMap.! recipe))
                        (Map.keysSet (recipeCaptures (opaqueRecipes prepared IntMap.! recipe)))
                    _ -> variables
            case node of
                Leaf (OpaqueSlot recipe) -> charge (fromIntegral
                    (Set.size (recipeParameters (opaqueRecipes prepared IntMap.! recipe))
                        + Map.size (recipeCaptures (opaqueRecipes prepared IntMap.! recipe)))
                    * indexWork (Set.size variables) 2)
                _ -> pure ()
            charge (fromIntegral (length (children node)))
            slots (Set.insert identifier visited) next (children node <> rest)
    ground identifier = do
        charge 1
        case nodeValues (groundNodes support) IntMap.! identifier of
            Leaf value -> pure (TemplateVariable value)
            Closed value -> pure (TemplateClosed (closedNodeValue (groundNodes support) value))
            Provider provider arguments -> TemplateProvider provider . Vector.fromList <$> traverse ground arguments
            Pair left right -> TemplateOrderedPair <$> ground left <*> ground right
    instantiate values identifier = do
        charge 1
        case nodeValues templates IntMap.! identifier of
            Leaf (AssignableSlot slot) -> ground (values Map.! slot)
            Leaf (FixedSeed seed) -> ground seed
            Leaf (OpaqueSlot recipeId) -> do
                let recipe = opaqueRecipes prepared IntMap.! recipeId
                actual <- traverse ground (recipeCaptures recipe <> values)
                opaqueInstantiate (requireInterpreter interpreter) (recipeArity recipe) (recipeTerm recipe) actual
            Closed value -> pure (TemplateClosed (closedNodeValue templates value))
            Provider provider arguments -> TemplateProvider provider . Vector.fromList <$> traverse (instantiate values) arguments
            Pair left right -> TemplateOrderedPair <$> instantiate values left <*> instantiate values right
    advance [] _ = pure Nothing
    advance ((slot,choices):rest) pendingSlots = do
        charge 1
        let remaining = IntSet.deleteMin choices
        if not (IntSet.null remaining) then pure (Just ((slot,remaining):rest,pendingSlots))
            else advance rest (slot:pendingSlots)

type SymbolicSupport = FrozenSupport

emptyTemplateSupport :: PreparedTemplateSupport
emptyTemplateSupport = PreparedTemplateSupport emptyNodes Map.empty IntMap.empty IntMap.empty IntMap.empty
    emptySizeProfile IntMap.empty Seq.empty

templatePreparationCounts :: PreparedTemplateSupport -> (Natural, Natural)
templatePreparationCounts prepared =
    (nodeVisits nodes, fromIntegral (nodeCount nodes))
  where
    nodes = templateNodes prepared

prepareTemplateSupport
    :: Monad m => (Natural -> m ()) -> [RuleTermTemplate] -> m PreparedTemplateSupport
prepareTemplateSupport charge templates = extendTemplateSupport charge templates emptyTemplateSupport

-- Append-only DAG preparation. Existing node descriptions and profiles are
-- reused; a failed charged operation returns no partially prepared value.
extendTemplateSupport
    :: Monad m => (Natural -> m ()) -> [RuleTermTemplate]
    -> PreparedTemplateSupport -> m PreparedTemplateSupport
extendTemplateSupport charge templates initial = snd <$> extendTemplates charge templates initial

extendTemplates
    :: Monad m => (Natural -> m ()) -> [RuleTermTemplate]
    -> PreparedTemplateSupport -> m ([Int], PreparedTemplateSupport)
extendTemplates charge templates =
    extendIndexedTemplates charge (const (error "a declaration template contains a scoped seed"))
        (fmap AssignableSlot <$> templates)

extendIndexedTemplates
    :: Monad m => (Natural -> m ()) -> (Int -> Natural) -> [SetTermTemplate TemplateSlot]
    -> PreparedTemplateSupport -> m ([Int], PreparedTemplateSupport)
extendIndexedTemplates charge fixedSize templates initial = do
    (roots,patterns) <- foldM (\(roots,nodes) term -> do
        (identifier,next) <- intern charge term nodes
        pure (identifier:roots,next)) ([],templateNodes initial) templates
    let firstNew = nodeCount (templateNodes initial)
        (_, added) = IntMap.split (firstNew - 1) (nodeValues patterns)
    charge (indexWork (nodeCount patterns) 1)
    prepared <- foldM admit (initial {templateNodes = patterns}) (IntMap.toAscList added)
    pure (roots,prepared)
  where
    admit current (identifier, node) = do
        charge (1 + fromIntegral (length (children node)))
        let (fixed, variables) = case node of
                Leaf AssignableSlot{} -> (0, 1)
                Leaf (FixedSeed identifier) -> (fixedSize identifier, 0)
                Leaf (OpaqueSlot recipeId) ->
                    let recipe = opaqueRecipes current IntMap.! recipeId
                    in if Set.null (Set.difference (recipeParameters recipe) (Map.keysSet (recipeCaptures recipe)))
                        then (1,0) else (0,1)
                _ -> foldl' (\(c,v) child -> let (a,b) = templateSizes current IntMap.! child
                            in (c+a,v+b)) (1,0) (children node)
        heads <- case templateHead node of
            Nothing -> pure (templateHeads current)
            Just head' -> do
                charge (indexWork (Map.size (templateHeads current)) 1)
                pure (Map.insertWith (<>) head' [identifier] (templateHeads current))
        profile <- addSize charge (fixed,variables) (templateProfile current)
        pure current
            { templateHeads = heads
            , templateSizes = IntMap.insert identifier (fixed,variables) (templateSizes current)
            , templateProfile = profile
            }

addSize :: Monad m => (Natural -> m ()) -> (Natural, Natural) -> SizeProfile -> m SizeProfile
addSize charge (fixed,variables) profile
    | variables == 0 = pure profile {closedMaximum = max fixed (closedMaximum profile)}
    | otherwise = do
        charge (indexWork (Map.size (variableProfile profile)) 1)
        pure profile {variableProfile = Map.insertWith max variables fixed (variableProfile profile)}

-- Associate every subtemplate, including shared and closed nodes, with the
-- result head of its checked registration. Syntax is interned once in the DAG;
-- ownership is an additional posting, not a new kind of term or evidence.
extendOwnedTemplateSupport
    :: Monad m => (Natural -> m ()) -> Int -> [RuleTermTemplate]
    -> PreparedTemplateSupport -> m (PreparedTemplateSupport, SizeProfile)
extendOwnedTemplateSupport charge owner templates =
    extendOwnedIndexedTemplates charge (const (error "a declaration template contains a scoped seed")) owner
        (fmap AssignableSlot <$> templates)

extendOwnedIndexedTemplates
    :: Monad m => (Natural -> m ()) -> (Int -> Natural) -> Int -> [SetTermTemplate TemplateSlot]
    -> PreparedTemplateSupport -> m (PreparedTemplateSupport, SizeProfile)
extendOwnedIndexedTemplates charge fixedSize owner templates initial = do
    (roots,prepared) <- extendIndexedTemplates charge fixedSize templates initial
    selected <- descend prepared Set.empty roots
    (owners,profile) <- foldM (\(known,profile) identifier -> do
        charge (indexWork (nodeCount (templateNodes prepared)) 1)
        let prior = IntMap.findWithDefault Set.empty identifier known
        charge (indexWork (Set.size prior) 1)
        next <- addSize charge (templateSizes prepared IntMap.! identifier) profile
        pure (IntMap.insert identifier (Set.insert owner prior) known,next))
        (templateOwners prepared,emptySizeProfile) (Set.toAscList selected)
    charge (indexWork (IntMap.size (ownerTemplates prepared)) 1)
    let prior = IntMap.findWithDefault Set.empty owner (ownerTemplates prepared)
    charge (fromIntegral (Set.size selected) * indexWork (Set.size prior) 1)
    pure (prepared {templateOwners = owners,
        ownerTemplates = IntMap.insert owner (Set.union prior selected) (ownerTemplates prepared)},profile)
  where
    descend _ seen [] = pure seen
    descend prepared seen (identifier:rest) = do
        charge (indexWork (Set.size seen) 1)
        if Set.member identifier seen then descend prepared seen rest else do
            let next = children (nodeValues (templateNodes prepared) IntMap.! identifier)
            charge (1 + fromIntegral (length next))
            descend prepared (Set.insert identifier seen) (next <> rest)

nodeHead :: Node variable -> Maybe Head
nodeHead = \case
    Leaf{} -> Nothing
    Closed{} -> Just ClosedHead
    Provider provider arguments -> Just (ProviderHead provider (length arguments))
    Pair{} -> Just PairHead

templateHead :: Node TemplateSlot -> Maybe Head
templateHead (Leaf OpaqueSlot{}) = Just OpaqueHead
templateHead node = nodeHead node

requireInterpreter :: Maybe (OpaqueInterpreter m variable) -> OpaqueInterpreter m variable
requireInterpreter = fromMaybe (error "opaque support requires its owning interpreter")

-- | Interning includes every subterm. The seed set is frozen here; later
-- queries can extend the intern table, but never the assignment domain.
-- Template variables range only over those seeds. A closed template requires
-- no seed, including when the entire seed domain is empty.
buildSymbolicSupport
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> [SetTermTemplate variable] -> [RuleTermTemplate] -> m (SymbolicSupport variable)
buildSymbolicSupport charge supplied templates = do
    prepared <- prepareTemplateSupport charge templates
    freezeSupport charge supplied prepared

-- B and T are already subterm closed. A subterm of t[sigma] is either inside
-- an assigned seed (hence in B) or is u[sigma] for a subtemplate u in T.
-- Consequently one layer is subterm closed without reseeding or composition.
-- Assigning every variable a largest seed attains c+v*L even with repeats.
freezeSupport
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> [SetTermTemplate variable] -> PreparedTemplateSupport -> m (FrozenSupport variable)
freezeSupport charge = freezeSupportWithCaptures charge []

freezeSupportWithCaptures
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> [([RuleTermTemplate], Map ViewVariableIx (SetTermTemplate variable))]
    -> [SetTermTemplate variable] -> PreparedTemplateSupport -> m (FrozenSupport variable)
freezeSupportWithCaptures charge captures supplied prepared =
    freezeSelectedSupportWithCaptures charge captures supplied
        (TemplateSupportView prepared Nothing (templateProfile prepared))

freezeSelectedSupport
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> [SetTermTemplate variable] -> TemplateSupportView -> m (FrozenSupport variable)
freezeSelectedSupport charge = freezeSelectedSupportWithCaptures charge []

freezeSelectedSupportWithCaptures
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> [([RuleTermTemplate], Map ViewVariableIx (SetTermTemplate variable))]
    -> [SetTermTemplate variable] -> TemplateSupportView -> m (FrozenSupport variable)
freezeSelectedSupportWithCaptures charge scoped supplied (TemplateSupportView prepared owners profile) = do
    charge 1
    let capturedTerms = concatMap (Map.elems . snd) scoped
    grounds <- foldM (\nodes term -> snd <$> intern charge term nodes) emptyNodes (supplied <> capturedTerms)
    (patterns, selectedProfile) <- foldM (specialize grounds) (prepared, profile) scoped
    let largestSeed = maximum (0 : IntMap.elems (nodeSizes grounds))
        seeds = IntMap.keysSet (nodeValues grounds)
        selectedOwners = if null scoped then owners else Set.insert scopedOwner <$> owners
    charge (fromIntegral (nodeCount grounds))
    largest <- if IntSet.null seeds then pure (closedMaximum selectedProfile) else
        foldM (\best (v,c) -> charge 1 >> pure (max best (c + v * largestSeed)))
            (max largestSeed (closedMaximum selectedProfile)) (Map.toAscList (variableProfile selectedProfile))
    pure (FrozenSupport grounds seeds patterns selectedOwners IntMap.empty emptyNodes IntMap.empty largest IntMap.empty Map.empty)
  where
    -- Catalogue owner IDs are nonnegative. This owner exists only in the
    -- private copy prepared after query-local captures have become seeds.
    scopedOwner = -1
    specialize grounds (patterns, priorProfile) (templates, captures) = do
        indexed <- traverse (\value -> fst <$> intern charge value grounds) captures
        rewritten <- traverse (rewrite indexed) templates
        (next, added) <- extendOwnedIndexedTemplates charge (\identifier -> nodeSizes grounds IntMap.! identifier)
            scopedOwner rewritten patterns
        combined <- unionSizeProfiles charge priorProfile added
        pure (next, combined)
    rewrite captures term = do
        charge 1
        case term of
            TemplateVariable slot -> do
                charge (indexWork (Map.size captures) 1)
                pure (TemplateVariable (maybe (AssignableSlot slot) FixedSeed (Map.lookup slot captures)))
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateProvider provider arguments -> TemplateProvider provider <$> traverse (rewrite captures) arguments
            TemplateOrderedPair left right -> TemplateOrderedPair <$> rewrite captures left <*> rewrite captures right

-- Add selected whole operands to the same template DAG before opening any
-- request. Parameter assignments still range over the original frozen B.
extendWholeSupport
    :: (Monad m, Ord variable) => (Natural -> m ()) -> OpaqueInterpreter m variable
    -> [(Natural, [SupportTermTemplate], Map ViewVariableIx (SetTermTemplate variable))]
    -> FrozenSupport variable -> m (FrozenSupport variable)
extendWholeSupport charge interpreter groups initial = do
    (prepared,profile) <- foldM add (preparedTemplates initial,emptySizeProfile) groups
    let grounds = groundNodes initial
        largestSeed = maximum (0 : [nodeSizes grounds IntMap.! identifier | identifier <- IntSet.toList (seedIds initial)])
    charge (fromIntegral (IntSet.size (seedIds initial)))
    largest <- if IntSet.null (seedIds initial) then pure (closedMaximum profile) else
        foldM (\best (v,c) -> charge 1 >> pure (max best (c+v*largestSeed)))
            (closedMaximum profile) (Map.toAscList (variableProfile profile))
    (meanings,index) <- if IntMap.null (opaqueRecipes prepared) then pure (IntMap.empty,Map.empty)
        else foldM (\(values,known) identifier -> do
            term <- groundTermWith charge grounds identifier
            value <- opaqueValue interpreter term
            charge (indexWork (Map.size known) 1)
            pure (IntMap.insert identifier value values,Map.insertWith IntSet.union value (IntSet.singleton identifier) known))
            (IntMap.empty,Map.empty) (IntSet.toAscList (seedIds initial))
    pure initial
        { preparedTemplates = prepared
        , eligibleOwners = Set.insert wholeOwner <$> eligibleOwners initial
        , symbolicSupportMaximumTermSize = max largest (symbolicSupportMaximumTermSize initial)
        , seedValues = meanings, valueSeeds = index
        }
  where
    wholeOwner = -2
    add (prepared,profile) (arity,terms,captures) = do
        captured <- traverse (\term -> do
            (identifier,_) <- intern charge term (groundNodes initial)
            unless (IntSet.member identifier (seedIds initial)) (error "a whole capture was not frozen in B")
            pure identifier) captures
        (indexed,withRecipes) <- State.runStateT (traverse (prepare arity captured) terms) prepared
        (next,added) <- extendOwnedIndexedTemplates charge
            (\identifier -> nodeSizes (groundNodes initial) IntMap.! identifier) wholeOwner indexed withRecipes
        combined <- unionSizeProfiles charge profile added
        pure (next,combined)
    prepare arity captures term = do
        lift (charge 1)
        case term of
            TemplateVariable (CBound index) | index < arity ->
                let slot = ViewVariableIx index
                in pure (TemplateVariable (maybe (AssignableSlot slot) FixedSeed (Map.lookup slot captures)))
            TemplateVariable value -> do
                free <- lift (canonicalFreeIndicesWith (charge 1) value)
                let parameters = Set.map ViewVariableIx (Set.filter (< arity) free)
                    recipe = OpaqueRecipe arity value parameters (Map.restrictKeys captures parameters)
                known <- State.get
                (identifier,next) <- lift (internRecipe charge recipe known)
                State.put next
                pure (TemplateVariable (OpaqueSlot identifier))
            TemplateClosed value -> pure (TemplateClosed value)
            TemplateProvider provider children -> TemplateProvider provider <$> traverse (prepare arity captures) children
            TemplateOrderedPair a b -> TemplateOrderedPair <$> prepare arity captures a <*> prepare arity captures b

-- Only shallow recipe IDs enter the structural DAG. Exact Core comparisons
-- and all navigation in this ordered payload index share the query allowance.
internRecipe :: Monad m => (Natural -> m ()) -> OpaqueRecipe -> PreparedTemplateSupport
    -> m (Int,PreparedTemplateSupport)
internRecipe charge recipe initial = search 0 (Seq.length sorted)
  where
    sorted = opaqueRecipeIndex initial
    navigation = indexWork (Seq.length sorted) 1
    search lower upper
        | lower == upper = do
            charge (2*navigation)
            let identifier = Seq.length sorted
            pure (identifier,initial
                { opaqueRecipes = IntMap.insert identifier recipe (opaqueRecipes initial)
                , opaqueRecipeIndex = Seq.insertAt lower (recipe,identifier) sorted })
        | otherwise = do
            charge navigation
            let middle = lower+(upper-lower) `div` 2
                (candidate,identifier) = Seq.index sorted middle
            termOrder <- compareCanonicalWith (charge 1) (recipeTerm recipe) (recipeTerm candidate)
            charge (fromIntegral (Map.size (recipeCaptures recipe)+Map.size (recipeCaptures candidate))+1)
            let ordering = compare (recipeArity recipe) (recipeArity candidate) <> termOrder
                    <> compare (recipeCaptures recipe) (recipeCaptures candidate)
            case ordering of
                EQ -> pure (identifier,initial)
                LT -> search lower middle
                GT -> search (middle+1) upper

groundTermWith :: Monad m => (Natural -> m ()) -> Nodes variable -> Int -> m (SetTermTemplate variable)
groundTermWith charge nodes = go
  where
    go identifier = charge 1 >> case nodeValues nodes IntMap.! identifier of
        Leaf value -> pure (TemplateVariable value)
        Closed value -> pure (TemplateClosed (closedNodeValue nodes value))
        Provider provider children -> TemplateProvider provider . Vector.fromList <$> traverse go children
        Pair a b -> TemplateOrderedPair <$> go a <*> go b

-- | Membership is matching, never Cartesian enumeration. The updated value
-- retains both node interning and answers for this exact frozen support.
-- The charge callback shares the owning request's account and must abort on
-- exhaustion; no partial answer or cache update is returned in that case.
symbolicSupportContains
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> SetTermTemplate variable -> SymbolicSupport variable -> m (Bool, SymbolicSupport variable)
symbolicSupportContains = symbolicSupportContainsWith Nothing

symbolicSupportContainsWith
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable) -> (Natural -> m ())
    -> SetTermTemplate variable -> SymbolicSupport variable -> m (Bool, SymbolicSupport variable)
symbolicSupportContainsWith interpreter charge term support = do
    (identifier, nodes) <- intern charge term (groundNodes support)
    charge 1
    let current = support {groundNodes = nodes}
    case IntMap.lookup identifier (membershipMemo support) of
        Just answer -> pure (answer, current)
        Nothing -> do
            answer <- if IntSet.member identifier (seedIds support)
                then pure True
                else do
                    let node = nodeValues nodes IntMap.! identifier
                        heads = templateHeads (preparedTemplates support)
                        ordinary = maybe [] (\head' -> Map.findWithDefault [] head' heads) (nodeHead node)
                        opaque = case node of Leaf{} -> True; Closed{} -> True; _ -> False
                    charge (indexWork (Map.size heads) 1)
                    anyMatch current identifier (ordinary <> if opaque then Map.findWithDefault [] OpaqueHead heads else [])
            pure (answer, current {membershipMemo = IntMap.insert identifier answer (membershipMemo support)})
  where
    anyMatch _ _ [] = pure False
    anyMatch current identifier (patternId : rest) = do
        eligible <- case eligibleOwners current of
            Nothing -> pure True
            Just heads -> do
                let postings = templateOwners (preparedTemplates current)
                charge (indexWork (nodeCount (templateNodes (preparedTemplates current))) 1)
                owned heads (Set.toAscList (IntMap.findWithDefault Set.empty patternId postings))
        found <- if eligible then match current (Map.empty,Map.empty) patternId identifier else pure Nothing
        case found of
            Just _ -> pure True
            Nothing -> anyMatch current identifier rest
    owned _ [] = pure False
    owned heads (owner:rest) = do
        charge (indexWork (Set.size heads) 1)
        if Set.member owner heads then pure True else owned heads rest
    match current bindings@(structural,meanings) patternId identifier = do
        let patternNode = nodeValues (templateNodes (preparedTemplates current)) IntMap.! patternId
            value = nodeValues (groundNodes current) IntMap.! identifier
        charge (1 + fromIntegral (length (children patternNode) + length (children value)))
        case patternNode of
            Closed patternValue -> case value of
                Closed groundValue -> do
                    same <- compareCanonicalWith (charge 1)
                        (closedSetValueTerm (closedNodeValue (templateNodes (preparedTemplates current)) patternValue))
                        (closedSetValueTerm (closedNodeValue (groundNodes current) groundValue))
                    pure (if same == EQ then Just bindings else Nothing)
                _ -> pure Nothing
            Leaf (FixedSeed selected) -> pure (if identifier == selected then Just bindings else Nothing)
            Leaf (OpaqueSlot recipeId) -> case value of
                Leaf{} -> opaque recipeId
                Closed{} -> opaque recipeId
                _ -> pure Nothing
            Leaf (AssignableSlot variable)
                | not (IntSet.member identifier (seedIds current)) -> pure Nothing
                | Just expected <- Map.lookup variable meanings
                , IntMap.lookup identifier (seedValues current) /= Just expected -> pure Nothing
                | otherwise -> case Map.lookup variable structural of
                    Nothing -> pure (Just (Map.insert variable identifier structural,meanings))
                    Just previous -> pure (if previous == identifier then Just bindings else Nothing)
            _ | nodeHead patternNode == nodeHead value ->
                    foldM (\pending (a,b) -> case pending of
                        Nothing -> pure Nothing
                        Just substitution -> match current substitution a b)
                        (Just bindings) (zip (children patternNode) (children value))
              | otherwise -> pure Nothing
      where
        opaque recipeId = do
            let recipe = opaqueRecipes (preparedTemplates current) IntMap.! recipeId
                operations = requireInterpreter interpreter
            target <- groundTermWith charge (groundNodes current) identifier >>= opaqueValue operations
            opaqueMatch operations (recipeArity recipe) (recipeTerm recipe) target >>= \case
                Nothing -> pure Nothing
                Just values -> do
                    charge (fromIntegral (Map.size values + Set.size (recipeParameters recipe)))
                    if Map.keysSet values /= recipeParameters recipe then pure Nothing else
                        foldM (constrain recipe) (Just bindings) (Map.toAscList values)
        constrain _ Nothing _ = pure Nothing
        constrain recipe (Just (bound,required)) (slot,value) = do
            charge (indexWork (Map.size (valueSeeds current)) 1
                + indexWork (Map.size bound + Map.size required + Map.size (recipeCaptures recipe)) 3)
            let fixed = Map.lookup slot (recipeCaptures recipe) <|> Map.lookup slot bound
                agrees = maybe True (== value) (Map.lookup slot required)
                seeded = case fixed of
                    Just seed -> IntMap.lookup seed (seedValues current) == Just value
                    Nothing -> Map.member value (valueSeeds current)
            pure (if agrees && seeded then Just (bound,Map.insert slot value required) else Nothing)

-- | Conservative existential admission for a partial source shape. Nothing is
-- a hole; Just is a rigid query leaf. Repeated holes/template slots may choose
-- independently here, so success is only a possibility, never an assignment.
-- Failure excludes every ground completion in the exact one-layer support.
-- This prevents impossible nested partial shapes from consuming the search
-- budget before their ground instances would finally be rejected.
symbolicSupportMayContain
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> SetTermTemplate (Maybe variable) -> SymbolicSupport variable -> m (Bool, SymbolicSupport variable)
symbolicSupportMayContain charge term original = do
    (identifier, nodes) <- intern charge term (partialNodes original)
    State.runStateT (admit identifier) original {partialNodes = nodes}
  where
    debit = lift . charge
    anyCandidate _ [] = pure False
    anyCandidate action (candidate:rest) = do
        debit 1
        found <- action candidate
        if found then pure True else anyCandidate action rest
    partial identifier = State.gets ((IntMap.! identifier) . nodeValues . partialNodes)
    admit identifier = do
        node <- partial identifier
        case node of
            Leaf Nothing -> State.gets ((> 0) . symbolicSupportMaximumTermSize)
            _ -> do
                seeded <- compatible identifier Seeds
                if seeded then pure True else do
                        prepared <- State.gets preparedTemplates
                        let heads = templateHeads prepared
                            ordinary = maybe [] (\head' -> Map.findWithDefault [] head' heads) (nodeHead node)
                            opaque = case node of Leaf{} -> True; Closed{} -> True; _ -> False
                        debit (indexWork (Map.size (templateHeads prepared)) 1)
                        anyCandidate (\candidate -> do
                            eligible <- eligibleTemplate candidate
                            if eligible then compatible identifier (TemplateCandidate candidate) else pure False)
                            (ordinary <> if opaque then Map.findWithDefault [] OpaqueHead heads else [])
    eligibleTemplate candidate = do
        support <- State.get
        case eligibleOwners support of
            Nothing -> pure True
            Just owners -> do
                let prepared = preparedTemplates support
                debit (indexWork (nodeCount (templateNodes prepared)) 1)
                anyCandidate (\owner -> debit (indexWork (Set.size owners) 1) >> pure (Set.member owner owners))
                    (Set.toAscList (IntMap.findWithDefault Set.empty candidate (templateOwners prepared)))
    compatible identifier candidate = do
        memo <- State.gets (IntMap.findWithDefault emptyPartialMemo identifier . partialMemo)
        debit 2
        let found = case candidate of
                Seeds -> seedPossibility memo
                GroundCandidate node -> IntMap.lookup node (groundPossibilities memo)
                TemplateCandidate node -> IntMap.lookup node (templatePossibilities memo)
        case found of
            Just answer -> pure answer
            Nothing -> do
                answer <- compareCandidate identifier candidate
                -- Recursive checks may have added entries at this query node.
                current <- State.gets (IntMap.findWithDefault emptyPartialMemo identifier . partialMemo)
                debit 2
                let next = case candidate of
                        Seeds -> current {seedPossibility = Just answer}
                        GroundCandidate node -> current {groundPossibilities = IntMap.insert node answer (groundPossibilities current)}
                        TemplateCandidate node -> current {templatePossibilities = IntMap.insert node answer (templatePossibilities current)}
                State.modify' (\support -> support {partialMemo = IntMap.insert identifier next (partialMemo support)})
                pure answer
    compareCandidate identifier candidate = do
        debit 1
        node <- partial identifier
        support <- State.get
        case candidate of
            Seeds -> case node of
                Leaf Nothing -> pure (not (IntSet.null (seedIds support)))
                _ -> anyCandidate (\ground -> do
                    let other = nodeValues (groundNodes support) IntMap.! ground
                    debit 1
                    if nodeHead node == nodeHead other then compatible identifier (GroundCandidate ground) else pure False)
                    (IntSet.toAscList (seedIds support))
            GroundCandidate ground -> case node of
                Leaf Nothing -> pure True
                _ -> case nodeValues (groundNodes support) IntMap.! ground of
                    Leaf value -> pure (node == Leaf (Just value))
                    other -> compareNode node (closedNodeValue (groundNodes support)) GroundCandidate (branch other)
            TemplateCandidate template -> case node of
                Leaf Nothing -> do
                    let prepared = preparedTemplates support
                        (_,variables) = templateSizes prepared IntMap.! template
                    debit (indexWork (nodeCount (templateNodes prepared)) 1)
                    pure (variables == 0 || not (IntSet.null (seedIds support)))
                _ -> case nodeValues (templateNodes (preparedTemplates support)) IntMap.! template of
                    Leaf AssignableSlot{} -> compatible identifier Seeds
                    Leaf (FixedSeed ground) -> compatible identifier (GroundCandidate ground)
                    Leaf OpaqueSlot{} -> pure $ case node of
                        Leaf{} -> True
                        Closed{} -> True
                        _ -> False
                    patternNode -> compareNode node (closedNodeValue (templateNodes (preparedTemplates support)))
                        TemplateCandidate (branch patternNode)
    branch = \case
        Leaf _ -> Leaf ()
        Closed value -> Closed value
        Provider provider arguments -> Provider provider arguments
        Pair left right -> Pair left right
    compareNode node closedValue wrap candidate = do
        debit (1 + fromIntegral (length (children node) + length (children candidate)))
        case (node,candidate) of
            (Closed value,Closed other) -> do
                current <- State.gets partialNodes
                (== EQ) <$> lift (compareCanonicalWith (charge 1)
                    (closedSetValueTerm (closedNodeValue current value)) (closedSetValueTerm (closedValue other)))
            _ | nodeHead node == nodeHead candidate && isJust (nodeHead node) ->
                allChildren (zip (children node) (children candidate))
              | otherwise -> pure False
      where
        allChildren [] = pure True
        allChildren ((left,right):rest) = do
            found <- compatible left (wrap right)
            if found then allChildren rest else pure False
