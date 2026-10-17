{-# LANGUAGE NoImplicitPrelude #-}

-- | Immutable, declaration-owned rule descriptions. Keys identify sources;
-- neither checked evidence nor query support belongs in this index.
module Felix.Checking.Notion.Catalog
    ( Catalog, emptyCatalog, catalogSize, catalogAcyclic
    , insertRule, insertRules, matchingRules, registeredRules, sourceDescriptions, lookupSource, lookupRule
    , matchingWholeRules, atomicWholeTruthPossible, possibleSource
    , providerStructureResults
    , providerFocusedSources
    , LocalProducerIx(..)
    , selectSnapshot, selectWholeSnapshot, selectSnapshotHeads
    , templatePreparationCounts
    , CandidateRules, candidateRulesFromMap, candidateRuleCount, nextCandidateRule, matchingPatternRules
    , matchingActivatedPatternRules, matchingPossiblePatternRules
    ) where

import Base
import Felix.Checking.Core (canonicalFreeIndicesWith)
import Felix.Checking.Semantic
import Felix.Checking.Notion.FormulaIndex (ResidualShape, residualShapeHash)
import Felix.Checking.Notion.Rule
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.Support qualified as Support
import Felix.Checking.Notion.Pattern (PatternVariable(..))
import Control.Monad (foldM, when)
import Control.Monad.State.Strict qualified as State
import Data.List (inits)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Merge
import Data.Ord (Down(..))
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

data Constructor = Provider !SourceProviderHead !Int | Pair | Closed
    deriving (Eq, Ord)

-- Stable within the owning lexical scope, independently of catalogue slots.
newtype LocalProducerIx = LocalProducerIx Int
    deriving (Show, Eq, Ord)

type Discriminator = ([Int], Constructor)

-- Head sets use cached cardinalities: costing a sparse update must not first
-- traverse an IntSet merely to discover the size of its unchanged population.
data HeadSummary = HeadSummary
    { reachableHeads :: !(Set Int)
    , wholeProducers :: !(Map Natural RegisteredRule)
    , reachableSignatures :: !(Set AtomSignature)
    , reachableRules :: !(Map Natural RegisteredRule)
    , initialRules :: !(Map Natural RegisteredRule)
    , sizeProfile :: !Support.SizeProfile
    , counts :: !SnapshotCounts
    , selectedForwardSources :: !(Map AtomSignature (Map Natural ForwardRule))
    }

emptySummary :: HeadSummary
emptySummary = HeadSummary Set.empty Map.empty Set.empty Map.empty Map.empty Support.emptySizeProfile (SnapshotCounts 0 0 0) Map.empty

-- Each alternative is one clause's conjunction, expressed in catalogue head
-- IDs. An empty conjunction is a possible starting point, not proof evidence.
data HeadSources = HeadSources !RuleHead !(Set (Set Int))

data Catalog source = Catalog
    { entries :: !(Map Natural (source, RegisteredRule))
    , fixed :: !(Map AtomSignature (Map Discriminator (Map Natural RegisteredRule)))
    , belowOutput :: !(Map AtomSignature (Map [Int] (Map Natural RegisteredRule)))
    , determined :: !(Map AtomSignature (Map Natural RegisteredRule))
    , flexible :: !(Map AtomSignature (Map Natural RegisteredRule))
    , scopedProducers :: !(Map AtomSignature (Map Natural RegisteredRule))
    , anchored :: !(Map (NotionLeaf AtomSignature Int) (Map AtomSignature (Map CandidatePriority (Map Natural RegisteredRule))))
    , definitionEdges :: !(Map AtomSignature (Set AtomSignature))
    , incomingHeads :: !(Set AtomSignature)
    , catalogAcyclic :: !Bool
    , structureResults :: !(Map SourceProviderHead (Map Natural source))
    , focusedSources :: !(Map SourceProviderHead (Map Natural source))
    -- Shape descriptions are interned at this boundary. Reachability and
    -- support subsequently use only these catalogue-local numeric head IDs.
    , nextHeadId :: !Int
    , headIds :: !(Map (NotionLeaf AtomSignature Int) [(RuleHead,Int)])
    , localSummaries :: !(IntMap.IntMap HeadSummary)
    , dependencyEdges :: !(IntMap.IntMap (Set Int))
    , formulaAtoms :: !(IntMap.IntMap (Set AtomSignature))
    , atomFormulas :: !(Map AtomSignature (IntMap.IntMap ResidualShape))
    , sourceClauses :: !(IntMap.IntMap HeadSources)
    , templates :: !Support.PreparedTemplateSupport
    , producers :: !(Map AtomSignature (Map Natural RegisteredRule))
    , sourceRanks :: !(Map AtomSignature Int)
    , invalidViewHeads :: !(Set AtomSignature)
    , viewPredecessors :: !(Map AtomSignature (Set AtomSignature))
    }

emptyCatalog :: Catalog source
emptyCatalog = Catalog Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Set.empty True Map.empty Map.empty
    0 Map.empty IntMap.empty IntMap.empty IntMap.empty Map.empty IntMap.empty Support.emptyTemplateSupport
    Map.empty Map.empty Set.empty Map.empty

catalogSize :: Catalog source -> Int
catalogSize = Map.size . entries

-- The head count bounds every head/component-indexed map. Use its cached
-- cardinality instead of traversing an IntMap just to cost an index lookup.
catalogHeadCount :: Catalog source -> Int
catalogHeadCount = nextHeadId

headLookupKey :: RuleHead -> NotionLeaf AtomSignature Int
headLookupKey = fmap residualShapeHash

lookupHead :: Monad m => (Natural -> m ()) -> RuleHead -> Catalog source -> m (Maybe Int)
lookupHead charge head' catalog = do
    charge (indexWork (Map.size (headIds catalog)) 3)
    findHead (Map.findWithDefault [] (headLookupKey head') (headIds catalog))
  where
    findHead [] = pure Nothing
    findHead ((candidate,identifier):rest) = case head' of
        AtomicLeaf{} -> pure (Just identifier)
        WholeLeaf{} -> do
            charge (max (ruleHeadWork head') (ruleHeadWork candidate))
            if head' == candidate then pure (Just identifier) else findHead rest

ensureHead :: Monad m => (Natural -> m ()) -> Catalog source -> RuleHead -> m (Int,Catalog source)
ensureHead charge catalog head' = lookupHead charge head' catalog >>= \case
    Just identifier -> pure (identifier,catalog)
    Nothing -> do
        let identifier = nextHeadId catalog
            key = headLookupKey head'
            local = emptySummary {reachableHeads = Set.singleton identifier,
                reachableSignatures = case head' of AtomicLeaf atom -> Set.singleton atom; WholeLeaf{} -> Set.empty}
        charge (indexWork (Map.size (headIds catalog)) 3 + 2 * indexWork (catalogHeadCount catalog) 1)
        pure (identifier,catalog
            { nextHeadId = identifier + 1
            , headIds = Map.insertWith (<>) key [(head',identifier)] (headIds catalog)
            , localSummaries = IntMap.insert identifier local (localSummaries catalog)
            , sourceClauses = IntMap.insert identifier (HeadSources head' Set.empty) (sourceClauses catalog) })

templatePreparationCounts :: Catalog source -> (Natural, Natural)
templatePreparationCounts = Support.templatePreparationCounts . templates

lookupSource :: Natural -> Catalog source -> Maybe source
lookupSource ordinal = fmap fst . Map.lookup ordinal . entries

lookupRule :: Natural -> Catalog source -> Maybe RegisteredRule
lookupRule ordinal = fmap snd . Map.lookup ordinal . entries

-- Schema discovery has no requested notion head yet. Index the written
-- provider at the subject of a structure result, rather than scanning schemas
-- or the full rule catalogue at every reconstruction occurrence.
providerStructureResults
    :: Monad m => (Natural -> m ()) -> SourceProviderHead -> Catalog source
    -> m [source]
providerStructureResults charge provider catalog = do
    charge (indexWork (Map.size (structureResults catalog)) 3)
    let found = Map.findWithDefault Map.empty provider (structureResults catalog)
    charge (fromIntegral (Map.size found))
    pure (Map.elems found)

-- Diagnostics can inspect one written provider and actual requesting ordinals
-- without enumerating the whole registration population. This description
-- index grants no evidence, and callers retain the registration-family check.
providerFocusedSources
    :: Monad m => (Natural -> m ()) -> SourceProviderHead -> Catalog source -> m [(Natural,source)]
providerFocusedSources charge provider catalog = do
    charge (indexWork (Map.size (focusedSources catalog)) 3)
    let found = Map.findWithDefault Map.empty provider (focusedSources catalog)
    charge (fromIntegral (Map.size found))
    pure (Map.toAscList found)

registeredRules :: Monad m => (Natural -> m ()) -> Catalog source -> m (Map Natural RegisteredRule)
registeredRules charge catalog = do
    charge (fromIntegral (catalogSize catalog))
    pure (snd <$> entries catalog)

sourceDescriptions :: Monad m => (Natural -> m ()) -> Catalog source -> m [(Natural, source)]
sourceDescriptions charge catalog = do
    charge (fromIntegral (catalogSize catalog))
    pure [(ordinal,source) | (ordinal,(source,_)) <- Map.toAscList (entries catalog)]

-- One rigid constructor suffices to exclude incompatible producers. Choosing
-- an inner constructor also distinguishes carriers of different structures.
-- Variables have a separate wildcard bucket; final matching is always checked.
insertRule
    :: Monad m => (Natural -> m ()) -> source -> RegisteredRule -> Catalog source
    -> m (Catalog source)
insertRule charge source entry catalog = do
    (ordinal,indexed) <- indexEntry charge source entry catalog
    prepareEntries charge [(ordinal,entry)] indexed

-- A declaration may project several results at the same head. Preserve all
-- original ordinals, but propagate their combined description once. Indexed
-- intermediate states remain private; only the fully prepared batch returns.
insertRules :: Monad m => (Natural -> m ()) -> [(source,RegisteredRule)] -> Catalog source -> m (Catalog source)
insertRules charge supplied initial = do
    (indexed,_,groups) <- foldM (\(catalog,heads,groups) (source,entry) -> do
        (ordinal,next) <- indexEntry charge source entry catalog
        (identifier,prepared) <- ensureHead charge next (ruleSignature (registeredRule entry))
        charge (2 * indexWork (Map.size heads) 1 + indexWork (Map.size groups) 1)
        let first = Map.findWithDefault ordinal identifier heads
        pure (prepared,Map.insert identifier first heads,Map.insertWith (<>) first [(ordinal,entry)] groups))
        (initial,Map.empty,Map.empty) supplied
    foldM (\catalog group -> prepareEntries charge (reverse group) catalog) indexed (Map.elems groups)

indexEntry
    :: Monad m => (Natural -> m ()) -> source -> RegisteredRule -> Catalog source
    -> m (Natural,Catalog source)
indexEntry charge source entry catalog = do
    let ordinal = fromIntegral (catalogSize catalog)
        rule = registeredRule entry
        (arity, premises, conclusion) = ruleDescription rule
        head' = ruleSignature rule
    partial <- case conclusion of
        AtomicLeaf atom -> indexAtomic ordinal arity premises atom (atomSignature atom)
        WholeLeaf residual -> do
            indices <- canonicalFreeIndicesWith (charge 1) (residualTemplateFormula residual)
            sourceHead <- bindingHead arity (Set.mapMonotonic ViewVariableIx (fst (Set.split arity indices)) <> ruleCapturedSlots rule) premises
            case sourceHead of
                Nothing -> pure catalog
                Just sourceHead' -> indexPreferred ordinal entry (headLookupKey head') sourceHead' (AnchoredCandidate (Down 0)) catalog
    withEdges <- case entry of
        RegisteredClassification{} -> pure partial
        RegisteredDefinition view -> case head' of
            AtomicLeaf target -> addEdge charge (forwardSourceSignature view) target partial
            WholeLeaf{} -> pure partial
    results <- case conclusion of
        AtomicLeaf (StructureAtomTemplate _ arguments')
            | Just (TemplateProvider provider _, _) <- Vector.uncons arguments' -> do
                charge (2 * indexWork (Map.size (structureResults catalog)) 3)
                let bucket = Map.findWithDefault Map.empty provider (structureResults catalog)
                charge (indexWork (Map.size bucket) 1)
                pure (Map.insert provider (Map.insert ordinal source bucket) (structureResults catalog))
        _ -> pure (structureResults catalog)
    focused <- case concatMap arguments (case conclusion of AtomicLeaf atom -> [atom]; WholeLeaf{} -> []) of
        TemplateProvider provider _ : _ -> do
            charge (2 * indexWork (Map.size (focusedSources catalog)) 3)
            let bucket = Map.findWithDefault Map.empty provider (focusedSources catalog)
            charge (indexWork (Map.size bucket) 1)
            pure (Map.insert provider (Map.insert ordinal source bucket) (focusedSources catalog))
        _ -> pure (focusedSources catalog)
    charge (indexWork (catalogSize catalog) 1)
    pure (ordinal,withEdges
        { entries = Map.insert ordinal (source,entry) (entries catalog)
        , structureResults = results
        , focusedSources = focused
        })
  where
    indexAtomic ordinal arity premises conclusion head' = do
        selected <- chooseArguments (zip [0..] (arguments conclusion))
        indexed <- case selected of
            Nothing -> do
                -- No constructor was found, so these are all variable leaves.
                -- A conclusion containing every binder needs no new parameters
                -- when requested ground. Prepare that distinction once; do not
                -- traverse every candidate's premise forest at each query.
                let terms = arguments conclusion
                charge (fromIntegral (length terms) * indexWork (length terms) 1)
                let complete = fromIntegral (Set.size (Set.fromList (concatMap toList terms) <> ruleCapturedSlots (registeredRule entry))) == arity
                    postings = if complete then determined catalog else flexible catalog
                charge (2 * indexWork (Map.size postings) 3)
                let bucket = Map.findWithDefault Map.empty head' postings
                charge (indexWork (Map.size bucket) 1)
                let updated = Map.insert head' (Map.insert ordinal entry bucket) postings
                pure $ if complete then catalog {determined = updated} else catalog {flexible = updated}
            Just (path, constructor) -> do
                charge (2 * indexWork (Map.size (fixed catalog)) 3)
                let headBucket = Map.findWithDefault Map.empty head' (fixed catalog)
                    key = (path,constructor)
                charge (2 * indexWork (Map.size headBucket) (1 + fromIntegral (length path)))
                let bucket = Map.findWithDefault Map.empty key headBucket
                charge (indexWork (Map.size bucket) 1)
                pure catalog {fixed = Map.insert head'
                    (Map.insert key (Map.insert ordinal entry bucket) headBucket) (fixed catalog)}
        patterned <- case selected of
            Nothing -> pure indexed
            Just (path,_) -> do
                charge (indexWork (Map.size (belowOutput indexed)) 3)
                let prior = Map.findWithDefault Map.empty head' (belowOutput indexed)
                updated <- foldM (\known prefix -> do
                    charge (indexWork (Map.size known) (1 + fromIntegral (length prefix)))
                    let bucket = Map.findWithDefault Map.empty prefix known
                    charge (indexWork (Map.size bucket) 1)
                    pure (Map.insert prefix (Map.insert ordinal entry bucket) known)) prior (drop 1 (inits path))
                pure indexed {belowOutput = Map.insert head' updated (belowOutput indexed)}
        headVariables <- foldM collectVariables (ruleCapturedSlots (registeredRule entry)) (toList conclusion)
        preferred <- bindingHead arity headVariables premises >>= \case
            Nothing -> pure patterned
            Just sourceHead -> indexPreferred ordinal entry (AtomicLeaf head') sourceHead
                (AnchoredCandidate (Down (maybe 0 (length . fst) selected))) patterned
        if not (ruleIsScoped (registeredRule entry)) then pure preferred else do
            charge (2 * indexWork (Map.size (scopedProducers preferred)) 3)
            let bucket = Map.findWithDefault Map.empty head' (scopedProducers preferred)
            charge (indexWork (Map.size bucket) 1)
            pure preferred {scopedProducers = Map.insert head' (Map.insert ordinal entry bucket) (scopedProducers preferred)}
    indexPreferred ordinal entry head' sourceHead priority patterned = do
        charge (2 * indexWork (Map.size (anchored patterned)) 3)
        let heads = Map.findWithDefault Map.empty head' (anchored patterned)
        charge (2 * indexWork (Map.size heads) 3)
        let priorities = Map.findWithDefault Map.empty sourceHead heads
        charge (2 * indexWork (Map.size priorities) 2)
        let bucket = Map.findWithDefault Map.empty priority priorities
        charge (indexWork (Map.size bucket) 1)
        pure patterned {anchored = Map.insert head'
            (Map.insert sourceHead (Map.insert priority (Map.insert ordinal entry bucket) priorities) heads) (anchored patterned)}
    -- A source row together with the requested head can determine the clause.
    -- Prefer an observed source, with more specific constructors first;
    -- matching and every remaining premise are still required.
    bindingHead _ _ [] = pure Nothing
    bindingHead arity headVariables (premise:rest) = inspect premise >>= \case
        Nothing -> bindingHead arity headVariables rest
        found -> pure found
      where
        inspect tree = do
            charge 1
            case tree of
                RulePremiseAnd left right -> inspect left >>= \case
                    Nothing -> inspect right
                    found -> pure found
                RulePremiseUniversal _ -> pure Nothing
                RulePremiseResidual _ -> pure Nothing
                RulePremiseAtom atom -> do
                    variables <- foldM collectVariables headVariables (toList atom)
                    pure (if fromIntegral (Set.size variables) == arity then Just (atomSignature atom) else Nothing)
    collectVariables known term = do
        charge 1
        case term of
            TemplateVariable variable -> do
                charge (indexWork (Set.size known) 1)
                pure (Set.insert variable known)
            TemplateClosed{} -> pure known
            TemplateProvider _ children -> foldM collectVariables known children
            TemplateOrderedPair left right -> collectVariables known left >>= (`collectVariables` right)
    -- Inspect the complete result once at admission. Selecting the first
    -- constructor would overlook more specific information in later operands.
    chooseArguments arguments' = do
        selected <- foldM (\known (position,term) -> choose 1 [position] known term) Nothing arguments'
        for selected \(depth,path,constructor) -> charge depth >> pure (reverse path,constructor)
    choose depth path known term = do
        charge 1
        let retain constructor = case known of
                Just (best,_,_) | best >= depth -> known
                _ -> Just (depth,path,constructor)
            descend constructor children = foldM (\best (position,child) ->
                choose (depth+1) (position:path) best child) (retain constructor) (zip [0..] children)
        case term of
            TemplateClosed{} -> pure (retain Closed)
            TemplateVariable{} -> pure known
            TemplateProvider provider children -> descend (Provider provider (Vector.length children)) (toList children)
            TemplateOrderedPair left right -> descend Pair [left,right]

-- Store each head's own descriptions and direct dependencies. Selection walks
-- the demanded graph once; declaration extension never copies ancestor closures.
prepareEntries :: Monad m => (Natural -> m ()) -> [(Natural,RegisteredRule)] -> Catalog source -> m (Catalog source)
prepareEntries _ [] initial = pure initial
prepareEntries charge entries@((_,first):_) initial = do
    let rules = registeredRule . snd <$> entries
        result = ruleSignature (registeredRule first)
        premises = rulePremiseSignatures <$> rules
    charge (fromIntegral (length entries + sum (length <$> premises)))
    compatible <- foldM connect initial (concatMap ruleFormulaHeads rules)
    (owner,withOwner) <- ensureHead charge compatible result
    (premiseGroups,withPremises) <- State.runStateT
        (traverse (traverse (\head' -> State.StateT (\catalog -> ensureHead charge catalog head'))) premises) withOwner
    withClauses <- foldM (\catalog group -> do
        dependencies <- foldM (\known identifier -> do
            charge (indexWork (Set.size known) 1)
            pure (Set.insert identifier known)) Set.empty group
        addSourceClause charge owner dependencies catalog) withPremises premiseGroups
    primitive <- concat <$> traverse (rulePrimitiveHeads charge) rules
    admitted <- foldM (\catalog shape -> do
        (identifier,next) <- ensureHead charge catalog (WholeLeaf shape)
        addSourceClause charge identifier Set.empty next) withClauses primitive
    let premiseIds = concat premiseGroups
    (prepared,profile) <- Support.extendOwnedTemplateSupport charge owner
        (concat [ruleTermTemplates rule | rule <- rules, not (ruleIsScoped rule)]) (templates admitted)
    charge (2 * indexWork (catalogHeadCount admitted) 1)
    let priorLocal = localSummaries admitted IntMap.! owner
    combinedProfile <- Support.unionSizeProfiles charge (sizeProfile priorLocal) profile
    direct <- foldM (\known identifier -> do
        charge (indexWork (Set.size known) 1)
        pure (Set.insert identifier known))
        (IntMap.findWithDefault Set.empty owner (dependencyEdges admitted)) premiseIds
    local <- foldM (\known (ordinal,entry) -> do
        let rule = registeredRule entry
            single = emptySummary
                { reachableRules = Map.singleton ordinal entry
                , wholeProducers = wholeProducerEntries ordinal entry
                , initialRules = if ruleIsInitial rule then Map.singleton ordinal entry else Map.empty
                , counts = SnapshotCounts 1 (fromIntegral (rulePremiseCount rule))
                    (case entry of RegisteredDefinition{} -> 1; _ -> 0)
                , selectedForwardSources = case entry of
                    RegisteredClassification{} -> Map.empty
                    RegisteredDefinition view -> Map.singleton (forwardSourceSignature view) (Map.singleton ordinal view) }
        mergeSummary charge known single) priorLocal entries
    let updated = admitted
            { templates = prepared
            , dependencyEdges = IntMap.insert owner direct (dependencyEdges admitted)
            , localSummaries = IntMap.insert owner local {sizeProfile = combinedProfile} (localSummaries admitted) }
    case result of
        WholeLeaf{} -> pure updated
        AtomicLeaf atom -> do
            charge (indexWork (Map.size (producers updated)) 3)
            let bucket = Map.findWithDefault Map.empty atom (producers updated)
            combined <- mergePostings charge bucket (Map.fromList entries)
            pure updated {producers = Map.insert atom combined (producers updated)}
  where
    connect catalog (atom,shape) = do
        (atomic,withAtom) <- ensureHead charge catalog (AtomicLeaf atom)
        (whole,withWhole) <- ensureHead charge withAtom (WholeLeaf shape)
        charge (indexWork (Map.size (atomFormulas withWhole)) 3
            + indexWork (catalogHeadCount withWhole) 1)
        let shapes = Map.findWithDefault IntMap.empty atom (atomFormulas withWhole)
        -- Every clause at this atom shares the same formula connection. Once
        -- present, its two edges and reverse posting need no further updates.
        if IntMap.member whole shapes then pure withWhole else do
            edges <- foldM (\known (from,to) -> do
                charge (indexWork (catalogHeadCount withWhole) 1)
                let prior = IntMap.findWithDefault Set.empty from known
                charge (indexWork (Set.size prior) 1)
                pure (IntMap.insert from (Set.insert to prior) known))
                (dependencyEdges withWhole) [(atomic,whole),(whole,atomic)]
            charge (2 * indexWork (catalogHeadCount withWhole) 1)
            let signatures = IntMap.findWithDefault Set.empty whole (formulaAtoms withWhole)
            charge (indexWork (Set.size signatures) 3)
            charge (indexWork (Map.size (atomFormulas withWhole)) 3
                + indexWork (catalogHeadCount withWhole) 1)
            withSources <- addSourceClause charge atomic (Set.singleton whole) withWhole
                >>= addSourceClause charge whole (Set.singleton atomic)
            pure withSources {dependencyEdges = edges,
                formulaAtoms = IntMap.insert whole (Set.insert atom signatures) (formulaAtoms withWhole),
                atomFormulas = Map.insert atom (IntMap.insert whole shape shapes) (atomFormulas withWhole)}

mergePostings :: Monad m => (Natural -> m ()) -> Map Natural value -> Map Natural value -> m (Map Natural value)
mergePostings charge left right
    | Map.null left = charge 1 >> pure right
    | Map.null right = charge 1 >> pure left
    | bulk < sparse = charge bulk >> pure (Map.union right left)
    | otherwise = foldM (\known (key,value) -> do
        charge (indexWork (Map.size known) 1)
        pure (Map.insert key value known)) left (Map.toAscList right)
  where
    bulk = 2 * fromIntegral (Map.size left + Map.size right)
    sparse = fromIntegral (Map.size right) * indexWork (Map.size left + Map.size right) 1

unionIds :: Monad m => (Natural -> m ()) -> Set Int -> Set Int -> m (Set Int)
unionIds charge left right
    | Set.null left = charge 1 >> pure right
    | Set.null right = charge 1 >> pure left
    | bulk < sparse = charge bulk >> pure (Set.union left right)
    | otherwise = foldM (\known identifier -> do
        charge (indexWork (Set.size known) 1)
        pure (Set.insert identifier known)) left (Set.toAscList right)
  where
    bulk = 2 * fromIntegral (Set.size left + Set.size right)
    sparse = fromIntegral (Set.size right) * indexWork (Set.size left + Set.size right) 1

mergeSummary :: Monad m => (Natural -> m ()) -> HeadSummary -> HeadSummary -> m HeadSummary
mergeSummary charge left right = do
    heads <- unionIds charge (reachableHeads left) (reachableHeads right)
    wholes <- mergePostings charge (wholeProducers left) (wholeProducers right)
    signatures <- unionSignatures charge (reachableSignatures left) (reachableSignatures right)
    rules <- mergePostings charge (reachableRules left) (reachableRules right)
    closed <- mergePostings charge (initialRules left) (initialRules right)
    profile <- Support.unionSizeProfiles charge (sizeProfile left) (sizeProfile right)
    sources <- mergeHeadPostings charge (selectedForwardSources left) (selectedForwardSources right)
    let SnapshotCounts a b c = counts left
        SnapshotCounts x y z = counts right
    pure left {reachableHeads = heads,wholeProducers = wholes,reachableSignatures = signatures,
        reachableRules = rules,initialRules = closed,sizeProfile = profile,
        counts = SnapshotCounts (a+x) (b+y) (c+z),
        selectedForwardSources = sources}

unionSignatures :: Monad m => (Natural -> m ()) -> Set AtomSignature -> Set AtomSignature -> m (Set AtomSignature)
unionSignatures charge left right
    | Set.null left = charge 1 >> pure right
    | Set.null right = charge 1 >> pure left
    | bulk < sparse = charge bulk >> pure (Set.union left right)
    | otherwise = foldM (\known signature -> do
        charge (indexWork (Set.size known) 3)
        pure (Set.insert signature known)) left (Set.toAscList right)
  where
    bulk = 6 * fromIntegral (Set.size left + Set.size right)
    sparse = fromIntegral (Set.size right) * indexWork (Set.size left + Set.size right) 3

mergeHeadPostings :: Monad m => (Natural -> m ()) -> Map AtomSignature (Map Natural value)
    -> Map AtomSignature (Map Natural value) -> m (Map AtomSignature (Map Natural value))
mergeHeadPostings charge left right
    | Map.null left = charge 1 >> pure right
    | Map.null right = charge 1 >> pure left
    | bulk < sparse = do
        charge bulk
        Merge.mergeA Merge.preserveMissing Merge.preserveMissing
            (Merge.zipWithAMatched (\_ -> mergePostings charge)) left right
    | otherwise = foldM (\known (head',views) -> do
        charge (indexWork (Map.size known) 3)
        let prior = Map.findWithDefault Map.empty head' known
        combined <- mergePostings charge prior views
        pure (Map.insert head' combined known)) left (Map.toAscList right)
  where
    bulk = 6 * fromIntegral (Map.size left + Map.size right)
    sparse = fromIntegral (Map.size right) * indexWork (Map.size left + Map.size right) 3

-- Selection is local to one immutable catalogue. Visit each reached head once,
-- including whole premises; argument filtering never narrows this domain graph.
selectSnapshot
    :: Monad m => (Natural -> m ()) -> AtomSignature -> Catalog source
    -> m (Either RuleSnapshotFailure RuleSnapshot)
selectSnapshot charge head' = selectSnapshotHeads charge [AtomicLeaf head']

selectWholeSnapshot
    :: Monad m => (Natural -> m ()) -> ResidualShape -> Catalog source
    -> m (Either RuleSnapshotFailure RuleSnapshot)
selectWholeSnapshot charge shape = selectSnapshotHeads charge [WholeLeaf shape]

selectSnapshotHeads
    :: Monad m => (Natural -> m ()) -> [RuleHead] -> Catalog source
    -> m (Either RuleSnapshotFailure RuleSnapshot)
selectSnapshotHeads charge roots catalog = do
    selected <- traverse (\head' -> lookupHead charge head' catalog) roots
    summary <- visit Set.empty emptySummary [identifier | Just identifier <- selected]
    let signatures = reachableSignatures summary <> Set.fromList [atom | AtomicLeaf atom <- roots]
    charge (fromIntegral (Set.size signatures))
    let invalid = Set.lookupMin (Set.intersection signatures (invalidViewHeads catalog))
    pure $ case invalid of
        Just head'' -> Left (CyclicDefinitionDependency head'')
        Nothing -> Right (preparedRuleSnapshot (reachableRules summary) signatures
            (producers catalog) (selectedForwardSources summary) (viewPredecessors catalog)
            (sourceRanks catalog) (initialRules summary)
            (wholeProducers summary)
            (Support.selectTemplateSupport (templates catalog) (reachableHeads summary) (sizeProfile summary)) (counts summary))
  where
    visit _ accumulated [] = pure accumulated
    visit seen accumulated (identifier:rest) = do
        charge (indexWork (Set.size seen) 1)
        if Set.member identifier seen then visit seen accumulated rest else do
            charge (3 * indexWork (catalogHeadCount catalog) 1)
            let local = localSummaries catalog IntMap.! identifier
                dependencies = IntMap.findWithDefault Set.empty identifier (dependencyEdges catalog)
            summary <- mergeSummary charge accumulated local
            charge (fromIntegral (Set.size dependencies))
            visit (Set.insert identifier seen) summary (Set.toAscList dependencies <> rest)

-- A whole demand selects producers of its rigid logical shape. Dependency
-- selection still prepares the complete finite domain independently of this
-- candidate filter.
matchingWholeRules
    :: Monad m => (Natural -> m ()) -> Set AtomSignature -> ResidualShape -> Catalog source
    -> m (CandidateRules, Map Natural RegisteredRule)
matchingWholeRules charge active shape catalog = lookupHead charge (WholeLeaf shape) catalog >>= \case
    Nothing -> (\rules -> (rules,Map.empty)) <$> candidateRulesFromMap charge Map.empty
    Just identifier -> do
        charge (2 * indexWork (catalogHeadCount catalog) 1)
        let signatures = IntMap.findWithDefault Set.empty identifier (formulaAtoms catalog)
        atomic <- foldM (\known signature -> do
            charge (indexWork (Map.size (producers catalog)) 3)
            mergePostings charge known (Map.findWithDefault Map.empty signature (producers catalog)))
            Map.empty (Set.toAscList signatures)
        let ordinary = wholeProducers (localSummaries catalog IntMap.! identifier)
        preferred <- preferredCandidates charge active (headLookupKey (WholeLeaf shape)) catalog
        CandidateRules count candidates _ _ <- candidatesFromBuckets charge [(DiscoveringCandidate,ordinary)]
        pure (CandidateRules count (Map.union preferred candidates) Set.empty (Just [ordinary]),atomic)

-- Only exact truth of a compatible shape can compensate for a missing row
-- view. Unrelated whole producers must not start finite parameter enumeration.
-- Descriptions are optional: an undescribed signature retains the fallback.
atomicWholeTruthPossible
    :: Monad m => (Natural -> m ()) -> (ResidualShape -> m Bool)
    -> AtomSignature -> Catalog source -> m Bool
atomicWholeTruthPossible = atomicTruthPossible True

atomicTruthPossible
    :: Monad m => Bool -> (Natural -> m ()) -> (ResidualShape -> m Bool)
    -> AtomSignature -> Catalog source -> m Bool
atomicTruthPossible includeAliases charge supplied signature catalog = do
    charge (indexWork (Map.size (atomFormulas catalog)) 3)
    case Map.lookup signature (atomFormulas catalog) of
        Nothing -> pure True
        Just shapes -> possible (IntMap.toAscList shapes)
  where
    possible [] = pure False
    possible ((identifier,shape):rest) = do
        charge (1 + indexWork (catalogHeadCount catalog) 1)
        let whole = wholeProducers (localSummaries catalog IntMap.! identifier)
            aliases = Set.delete signature (IntMap.findWithDefault Set.empty identifier (formulaAtoms catalog))
        alternate <- if not includeAliases then pure False else foldM (\found head' -> if found then pure True else do
            charge (indexWork (Map.size (producers catalog)) 1)
            pure (not (Map.null (Map.findWithDefault Map.empty head' (producers catalog)))))
            False (Set.toAscList aliases)
        if alternate || not (Map.null whole) then pure True else supplied shape >>= \case
            True -> pure True
            False -> possible rest

-- Source clauses are separate from support reachability: flattening their
-- alternatives would turn an AND/OR condition into mere graph reachability.
addSourceClause :: Monad m => (Natural -> m ()) -> Int -> Set Int -> Catalog source -> m (Catalog source)
addSourceClause charge identifier dependencies catalog = do
    charge (2 * indexWork (catalogHeadCount catalog) 1)
    let HeadSources head' prior = sourceClauses catalog IntMap.! identifier
    charge (indexWork (Set.size prior) (1 + fromIntegral (Set.size dependencies)))
    pure catalog {sourceClauses = IntMap.insert identifier
        (HeadSources head' (Set.insert dependencies prior)) (sourceClauses catalog)}

-- Necessary availability over the immutable catalogue. Forget arguments, but
-- retain every guard. Cycles acquire a starting point only from a supplied
-- source, a primitive goal operation, or a clause whose premises are possible.
-- Cache negatives only after saturating the entire reached component.
-- These work tables use Map's cached size for charging and clause identifiers.
possibleSource
    :: Monad m => (Natural -> m ()) -> (RuleHead -> m Bool) -> RuleHead
    -> Catalog source -> Map Int Bool -> m (Bool,Map Int Bool)
possibleSource charge supplied requested catalog known = lookupHead charge requested catalog >>= \case
    Nothing -> pure (True,known) -- An undescribed head retains conservative discovery.
    Just root -> do
        charge (indexWork (Map.size known) 1)
        case Map.lookup root known of
            Just available -> pure (available,known)
            Nothing -> do
                (seen,waiting,clauses,seeds) <- collect Set.empty Map.empty Map.empty [] [root]
                reached <- propagate waiting clauses Set.empty seeds
                updated <- foldM (\cache head' -> do
                    charge (indexWork (Map.size cache) 1 + indexWork (Set.size reached) 1)
                    pure (Map.insert head' (Set.member head' reached) cache)) known (Set.toAscList seen)
                pure (Set.member root reached,updated)
  where
    collect seen waiting clauses seeds [] = pure (seen,waiting,clauses,seeds)
    collect seen waiting clauses seeds (head':rest) = do
        charge (indexWork (Set.size seen) 1)
        if Set.member head' seen then collect seen waiting clauses seeds rest else do
            charge (indexWork (Set.size seen) 1 + indexWork (Map.size known) 1
                + indexWork (catalogHeadCount catalog) 1)
            let HeadSources description choices = sourceClauses catalog IntMap.! head'
            direct <- case Map.lookup head' known of
                Just result -> pure result
                Nothing -> do
                    undescribed <- case description of
                        AtomicLeaf signature -> do
                            charge (indexWork (Map.size (atomFormulas catalog)) 3)
                            pure (Map.notMember signature (atomFormulas catalog))
                        WholeLeaf{} -> pure False
                    if undescribed then pure True else supplied description
            let visited = Set.insert head' seen
            if direct then charge 1 >> collect visited waiting clauses (head':seeds) rest
              else if Map.lookup head' known == Just False then collect visited waiting clauses seeds rest
              else do
                (waiting',clauses',seeds',pending) <- foldM (addClause head')
                    (waiting,clauses,seeds,rest) (Set.toAscList choices)
                collect visited waiting' clauses' seeds' pending
    addClause head' (waiting,clauses,seeds,pending) dependencies
        | Set.null dependencies = charge 1 >> pure (waiting,clauses,head':seeds,pending)
        | otherwise = do
            let identifier = Map.size clauses
            charge (indexWork identifier 1 + fromIntegral (Set.size dependencies))
            waiting' <- foldM (\table dependency -> do
                charge (indexWork (Map.size table) 1)
                pure (Map.insertWith (<>) dependency [identifier] table)) waiting (Set.toAscList dependencies)
            pure (waiting',Map.insert identifier (head',Set.size dependencies) clauses,seeds,
                Set.toAscList dependencies <> pending)
    propagate _ _ reached [] = pure reached
    propagate waiting clauses reached (head':rest) = do
        charge (indexWork (Set.size reached) 1)
        if Set.member head' reached then propagate waiting clauses reached rest else do
            charge (indexWork (Set.size reached) 1 + indexWork (Map.size waiting) 1)
            (next,pending) <- foldM (\(table,pending) identifier -> do
                charge (2 * indexWork (Map.size table) 1)
                let (target,remaining) = table Map.! identifier
                when (remaining == 1) (charge 1)
                pure (Map.insert identifier (target,remaining-1) table,
                    if remaining == 1 then target:pending else pending))
                (clauses,rest) (Map.findWithDefault [] head' waiting)
            propagate waiting next (Set.insert head' reached) pending

-- Record rather than reject cycles: only a selected definition cycle is an
-- invalid general snapshot. Initial completion uses the selected root's
-- acyclic ranks, not the global flag. Usually a new source has no incoming edges,
-- so inserting its projections needs no graph traversal.
addEdge
    :: Monad m => (Natural -> m ()) -> AtomSignature -> AtomSignature
    -> Catalog source -> m (Catalog source)
addEdge charge source target catalog = do
    charge (2 * indexWork (Map.size (definitionEdges catalog)) 3)
    let outgoing = Map.findWithDefault Set.empty source (definitionEdges catalog)
    charge (2 * indexWork (Set.size outgoing) 3)
    if Set.member target outgoing then pure catalog else do
        charge (2 * indexWork (Set.size (incomingHeads catalog)) 3)
        charge (2 * indexWork (Map.size (viewPredecessors catalog)) 3)
        let predecessors = Map.findWithDefault Set.empty target (viewPredecessors catalog)
        charge (indexWork (Set.size predecessors) 3)
        cyclic <- if source == target then pure True
            else if Set.notMember source (incomingHeads catalog) then pure False
            else reaches Set.empty [target]
        let updated = catalog
                { definitionEdges = Map.insert source (Set.insert target outgoing) (definitionEdges catalog)
                , viewPredecessors = Map.insert target (Set.insert source predecessors) (viewPredecessors catalog)
                , incomingHeads = Set.insert target (incomingHeads catalog)
                , catalogAcyclic = catalogAcyclic catalog && not cyclic }
        charge (indexWork (Set.size (invalidViewHeads catalog)) 3)
        if cyclic || Set.member source (invalidViewHeads catalog) then do
            invalid <- markInvalid (definitionEdges updated) (invalidViewHeads catalog) [target]
            pure updated {invalidViewHeads = invalid}
        else do
            charge (indexWork (Map.size (sourceRanks catalog)) 3)
            ranks <- raiseRanks (definitionEdges updated) (sourceRanks catalog)
                [(target,1 + Map.findWithDefault 0 source (sourceRanks catalog))]
            pure updated {sourceRanks = ranks}
  where
    markInvalid _ invalid [] = pure invalid
    markInvalid edges invalid (head':rest) = do
        charge (indexWork (Set.size invalid) 3)
        if Set.member head' invalid then markInvalid edges invalid rest else do
            charge (indexWork (Map.size edges) 3)
            let next = Set.toAscList (Map.findWithDefault Set.empty head' edges)
            charge (1 + fromIntegral (length next))
            markInvalid edges (Set.insert head' invalid) (next <> rest)
    raiseRanks _ ranks [] = pure ranks
    raiseRanks edges ranks ((head',rank):rest) = do
        charge (indexWork (Map.size ranks) 3 + indexWork (Set.size (invalidViewHeads catalog)) 3)
        if Set.member head' (invalidViewHeads catalog) || rank <= Map.findWithDefault 0 head' ranks
            then raiseRanks edges ranks rest else do
                charge (indexWork (Map.size edges) 3)
                let next = Set.toAscList (Map.findWithDefault Set.empty head' edges)
                charge (1 + fromIntegral (length next))
                raiseRanks edges (Map.insert head' rank ranks) ([(child,rank+1) | child <- next] <> rest)
    reaches _ [] = pure False
    reaches seen (head':rest) = do
        charge (1 + indexWork (Set.size seen) 3)
        if head' == source then pure True
        else if Set.member head' seen then reaches seen rest else do
            charge (indexWork (Set.size seen) 3 + indexWork (Map.size (definitionEdges catalog)) 3)
            let next = Map.findWithDefault Set.empty head' (definitionEdges catalog)
            charge (2 * fromIntegral (Set.size next))
            reaches (Set.insert head' seen) (Set.toAscList next <> rest)

matchingRules
    :: Monad m => (Natural -> m ()) -> AtomTemplate (SetTermTemplate variable)
    -> Catalog source -> m [(Natural, RegisteredRule)]
matchingRules charge goal catalog = do
    selected <- selectCandidates charge Set.empty (const (pure False)) goal catalog
    collect selected []
  where
    collect selected reversed = nextCandidateRule charge selected >>= \case
        Nothing -> pure (reverse reversed)
        Just (entry,rest) -> collect rest (entry:reversed)

-- A finite ordered merge of immutable postings. Constructing a cursor visits
-- query shapes and bucket minima, not every selected producer. Each rule has
-- one discriminator; matching rigid nodes and unresolved-output subtrees have
-- disjoint ordinals. Preferred source-head postings may repeat a flexible
-- candidate: the cursor suppresses those repeats lazily, under the account.
-- This is an index cursor, not uncharged suspended population traversal.
data CandidatePriority = ScopedCandidate | AnchoredCandidate !(Down Int) | RigidCandidate !(Down Int) | DeterminedCandidate | DiscoveringCandidate | AlternativeViewCandidate
    deriving (Eq, Ord)

data CandidateRules = CandidateRules !Natural !(Map (CandidatePriority,Natural) (RegisteredRule,Map Natural RegisteredRule)) !(Set Natural) !(Maybe [Map Natural RegisteredRule])

candidateRuleCount :: CandidateRules -> Natural
candidateRuleCount (CandidateRules count _ _ _) = count

candidateRulesFromMap :: Monad m => (Natural -> m ()) -> Map Natural RegisteredRule -> m CandidateRules
candidateRulesFromMap charge rules = candidatesFromBuckets charge [(RigidCandidate (Down 0),rules)]

candidatesFromBuckets :: Monad m => (Natural -> m ()) -> [(CandidatePriority,Map Natural RegisteredRule)] -> m CandidateRules
candidatesFromBuckets charge = foldM (\(CandidateRules count known seen eligible) (priority,bucket) -> do
    charge (indexWork (Map.size bucket) 1)
    case Map.minViewWithKey bucket of
        Nothing -> pure (CandidateRules count known seen eligible)
        Just ((ordinal,entry),rest) -> do
            charge (indexWork (Map.size known) 1)
            pure (CandidateRules (count + fromIntegral (Map.size bucket)) (Map.insert (priority,ordinal) (entry,rest) known) seen eligible))
    (CandidateRules 0 Map.empty Set.empty Nothing)

nextCandidateRule
    :: Monad m => (Natural -> m ()) -> CandidateRules
    -> m (Maybe ((Natural,RegisteredRule),CandidateRules))
nextCandidateRule charge (CandidateRules count known seen eligible) = do
    charge (indexWork (Map.size known) 1)
    case Map.minViewWithKey known of
        Nothing -> pure Nothing
        Just (((priority,ordinal),(entry,bucket)),rest) -> do
            charge (indexWork (Map.size bucket) 1)
            next <- case Map.minViewWithKey bucket of
                Nothing -> pure rest
                Just ((key,value),tail') -> do
                    charge (indexWork (Map.size rest) 1)
                    pure (Map.insert (priority,key) (value,tail') rest)
            charge (indexWork (Set.size seen) 1)
            compatible <- case (priority,eligible) of
                (ScopedCandidate,_) -> pure True
                (RigidCandidate _,_) -> pure True
                (_,Nothing) -> pure True
                (DeterminedCandidate,_) -> pure True
                (DiscoveringCandidate,_) -> pure True
                (AlternativeViewCandidate,_) -> pure True
                (_,Just postings) -> present ordinal postings
            if not compatible || Set.member ordinal seen then nextCandidateRule charge (CandidateRules count next seen eligible) else do
                charge (indexWork (Set.size seen) 1)
                pure (Just ((ordinal,entry),CandidateRules count next (Set.insert ordinal seen) eligible))
  where
    present _ [] = pure False
    present ordinal (bucket:rest) = do
        charge (indexWork (Map.size bucket) 1)
        if Map.member ordinal bucket then pure True else present ordinal rest

matchingPatternRules
    :: Monad m => (Natural -> m ()) -> AtomTemplate (SetTermTemplate (PatternVariable variable))
    -> Catalog source -> m CandidateRules
matchingPatternRules charge = matchingActivatedPatternRules charge Set.empty

matchingActivatedPatternRules
    :: Monad m => (Natural -> m ()) -> Set AtomSignature
    -> AtomTemplate (SetTermTemplate (PatternVariable variable)) -> Catalog source -> m CandidateRules
matchingActivatedPatternRules charge active = selectCandidates charge active (pure . \case Output{} -> True; Pinned{} -> False)

-- Opaque values may conceal an admitted constructor. This callback certifies
-- only that a rigid leaf cannot; it never extracts an argument or grants a view.
matchingPossiblePatternRules
    :: Monad m => (Natural -> m ()) -> Set AtomSignature -> (SetTermTemplate variable -> m Bool)
    -> AtomTemplate (SetTermTemplate (PatternVariable variable)) -> Catalog source -> m CandidateRules
matchingPossiblePatternRules charge active rigid goal catalog = do
    prepared <- traverse (describeTerm) goal
    CandidateRules _ selected seen eligible <- selectCandidates charge active possible prepared catalog
    -- Written constructors are useful priorities, but different admitted views
    -- can denote the same value. Keep an indexed, lazy fallback at this head.
    charge (indexWork (Map.size (producers catalog)) 3)
    let allProducers = Map.findWithDefault Map.empty (atomSignature goal) (producers catalog)
    CandidateRules _ alternatives _ _ <- candidatesFromBuckets charge [(AlternativeViewCandidate,allProducers)]
    pure (CandidateRules (fromIntegral (Map.size allProducers)) (Map.union selected alternatives) seen eligible)
  where
    possible Nothing = pure True
    possible (Just value) = not <$> rigid value
    describeTerm term = charge 1 >> case term of
        TemplateVariable Output{} -> pure (TemplateVariable Nothing)
        TemplateVariable (Pinned value) -> pure (TemplateVariable (Just (TemplateVariable value)))
        TemplateClosed closed -> rigid (TemplateClosed closed) >>= \known ->
            pure (if known then TemplateClosed closed else TemplateVariable Nothing)
        TemplateProvider provider children -> TemplateProvider provider <$> traverse describeTerm children
        TemplateOrderedPair a b -> TemplateOrderedPair <$> describeTerm a <*> describeTerm b

selectCandidates
    :: Monad m => (Natural -> m ()) -> Set AtomSignature -> (variable -> m Bool)
    -> AtomTemplate (SetTermTemplate variable) -> Catalog source -> m CandidateRules
selectCandidates charge active unresolved goal catalog = do
    charge (indexWork (Map.size (scopedProducers catalog)) 3)
    let local = Map.findWithDefault Map.empty (atomSignature goal) (scopedProducers catalog)
    charge (indexWork (Map.size (flexible catalog)) 3)
    let initial = Map.findWithDefault Map.empty (atomSignature goal) (flexible catalog)
    charge (indexWork (Map.size (determined catalog)) 3)
    let complete = Map.findWithDefault Map.empty (atomSignature goal) (determined catalog)
    charge (indexWork (Map.size (fixed catalog)) 3)
    charge (indexWork (Map.size (belowOutput catalog)) 3)
    let partial = Map.findWithDefault Map.empty (atomSignature goal) (belowOutput catalog)
    selected <- case Map.lookup (atomSignature goal) (fixed catalog) of
        Nothing -> pure []
        Just rigid -> foldM (\known (position,term) -> visit rigid partial [position] known term)
            [] (zip [0..] (arguments goal))
    -- An existing source row can determine all remaining parameters. Prefer
    -- those producers before constructor matches requiring unrelated search.
    -- A constructor match then takes precedence over undetermined projections.
    -- Among variable-headed results prefer the rules whose conclusion fixes
    -- all theorem parameters to those needing parameter discovery. This is
    -- only a priority (also for partial requests), not a completeness filter.
    -- All strata remain in this cursor, with ordinal order within each one.
    -- Lexical clauses fix their captures. Supplied source projections are a
    -- common direct path, before opening general producer families.
    -- Every capture and guard is still checked by the ordinary clause path.
    let ordinaryBuckets = (ScopedCandidate,local) : selected <> [(DeterminedCandidate,complete),(DiscoveringCandidate,initial)]
    CandidateRules count ordinary _ _ <- candidatesFromBuckets charge ordinaryBuckets
    preferred <- preferredCandidates charge active (AtomicLeaf (atomSignature goal)) catalog
    charge (fromIntegral (Map.size preferred + Map.size ordinary))
    -- Preferred postings overlap the ordinary cursor. Count the full original
    -- selection once and suppress duplicate ordinals only as they are visited.
    -- Active heads describe existing source rows, never additional evidence or
    -- support seeds. No population-sized intersection is built at query time.
    pure (CandidateRules count (Map.union preferred ordinary) Set.empty (Just (snd <$> ordinaryBuckets)))
  where
    visit rigid partial path known term = do
        charge 1
        case term of
            TemplateClosed{} -> descend rigid partial path known Closed []
            TemplateVariable variable -> unresolved variable >>= \possible ->
                if not possible then pure known else do
                    let depth = length path
                    charge (fromIntegral depth + indexWork (Map.size partial) (1 + fromIntegral depth))
                    -- A missing view is as inconclusive as an output hole.
                    pure ((RigidCandidate (Down (depth-1)),Map.findWithDefault Map.empty (reverse path) partial) : known)
            TemplateProvider provider children -> descend rigid partial path known
                (Provider provider (Vector.length children)) (toList children)
            TemplateOrderedPair left right -> descend rigid partial path known Pair [left,right]
    descend rigid partial path known constructor children = do
        let depth = length path
        charge (fromIntegral depth + indexWork (Map.size rigid) (1 + fromIntegral depth))
        let bucket = Map.findWithDefault Map.empty (reverse path,constructor) rigid
        -- A deeper matched discriminator is more specific than an outer
        -- wrapper with variable operands (for example carrier(F(x)) versus
        -- carrier(y)). Keep both, but try the constrained result first.
        foldM (\current (position,term) -> visit rigid partial (position:path) current term)
            ((RigidCandidate (Down depth),bucket) : known) (zip [0..] children)

arguments :: AtomTemplate term -> [term]
arguments = toList

-- Source presence determines a scheduling preference only. The original
-- producer cursor and its compatibility filter remain authoritative.
preferredCandidates
    :: Monad m => (Natural -> m ()) -> Set AtomSignature -> NotionLeaf AtomSignature Int -> Catalog source
    -> m (Map (CandidatePriority,Natural) (RegisteredRule,Map Natural RegisteredRule))
preferredCandidates charge active head' catalog = do
    charge (indexWork (Map.size (anchored catalog)) 3)
    let sources = Map.findWithDefault Map.empty head' (anchored catalog)
    buckets <- for (Set.toAscList active) \source -> do
        charge (1 + indexWork (Map.size sources) 3)
        let priorities = Map.findWithDefault Map.empty source sources
        charge (fromIntegral (Map.size priorities))
        pure (Map.toAscList priorities)
    CandidateRules _ preferred _ _ <- candidatesFromBuckets charge (concat buckets)
    pure preferred
