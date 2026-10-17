{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingStrategies #-}

-- | Search-selected premises, imports and the recipe indexed into them.
module Felix.Checking.Notion.Formation
    ( MaterializedNotionHypothesis(..)
    , ConjunctionPath(..)
    , ConjunctionProjection
    , rootConjunctionProjection
    , ConjunctionProjections
    , emptyConjunctionProjections
    , extendConjunctionProjection
    , prepareConjunctionProjection
    , conjunctionProjectionDepth
    , conjunctionProjectionPath
    , FormationEqualityDirection(..)
    , FormationTransportEdge(..)
    , FormationDerivationRecipe(..)
    , FormationRecipeId(..)
    , FormationRecipeNode(..)
    , FormationRecipeBuilder
    , emptyFormationRecipeBuilder
    , insertFormationRecipeM
    , selectFormationRecipe
    , formationRecipeChildren, traverseFormationRecipeChildren
    , MaterializedFormationEvidence(..)
    , FormationArena
    , emptyFormationArena
    , arenaHypothesis
    , arenaImport
    , arenaInsert
    , arenaSelect
    , arenaProject, arenaGraft
    ) where

import Base
import Felix.Checking.Core
    ( CanonicalTerm, ScopedCheckedCore, CoreType(..)
    , scopedCoreContext, scopedCoreType, scopedCoreTerm, compareCanonicalWith )
import Felix.Checking.Elimination
    (ConjunctionPath(..), ConjunctionProjection(..), rootConjunctionProjection, stepConjunctionProjection)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Derivation (HypothesisIx, ImportIx, hypothesisIx, importIx, hypothesisIxValue, importIxValue)
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.SuppliedUniversal (UniversalAdapter)
import Felix.Checking.Semantic (SemanticFactOccurrenceFingerprint)

import Numeric.Natural (Natural)
import Control.Monad (foldM)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Control.Monad.State.Strict (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State.Strict qualified as State


-- Stable deduplication uses both fields: equal propositions from distinct
-- locals stay distinct, while projected leaves share their original source.
data MaterializedNotionHypothesis origin = MaterializedNotionHypothesis
    !(ScopedCheckedCore ObjectId)
    !origin

newtype FormationRecipeId = FormationRecipeId Int
    deriving stock (Eq, Ord)

-- A lexical scope shares selectors independently of any query's proof arena.
-- Legacy forward paths are admitted here once. A spine walk can extend its
-- current prefix directly, without first constructing each complete path.
newtype ConjunctionProjections = ConjunctionProjections
    (Map (Int, Bool) ConjunctionProjection)

emptyConjunctionProjections :: ConjunctionProjections
emptyConjunctionProjections = ConjunctionProjections Map.empty

conjunctionProjectionId :: ConjunctionProjection -> Int
conjunctionProjectionId RootConjunctionProjection = 0
conjunctionProjectionId (ConjunctionProjection identifier _ _ _) = identifier

conjunctionProjectionDepth :: ConjunctionProjection -> Natural
conjunctionProjectionDepth RootConjunctionProjection = 0
conjunctionProjectionDepth (ConjunctionProjection _ depth _ _) = depth

conjunctionProjectionPath :: ConjunctionProjection -> ConjunctionPath
conjunctionProjectionPath = go ConjunctionHere
  where
    go rest RootConjunctionProjection = rest
    go rest (ConjunctionProjection _ _ right parent) =
        go ((if right then ConjunctionRight else ConjunctionLeft) rest) parent

extendConjunctionProjection
    :: Monad m => (Natural -> m ()) -> Bool -> ConjunctionProjection
    -> StateT ConjunctionProjections m ConjunctionProjection
extendConjunctionProjection charge right parent = do
    ConjunctionProjections paths <- State.get
    lift (charge (indexWork (Map.size paths) 2))
    let key = (conjunctionProjectionId parent, right)
    case Map.lookup key paths of
        Just path -> pure path
        Nothing -> do
            lift (charge (1 + indexWork (Map.size paths) 2))
            let path = stepConjunctionProjection (Map.size paths + 1) right parent
            State.put (ConjunctionProjections (Map.insert key path paths))
            pure path

prepareConjunctionProjection
    :: Monad m => (Natural -> m ()) -> ConjunctionPath
    -> StateT ConjunctionProjections m ConjunctionProjection
prepareConjunctionProjection charge = go rootConjunctionProjection
  where
    go parent ConjunctionHere = pure parent
    go parent (ConjunctionLeft rest) = extendConjunctionProjection charge False parent >>= (`go` rest)
    go parent (ConjunctionRight rest) = extendConjunctionProjection charge True parent >>= (`go` rest)

-- Children precede their parents. Only source slots and projections are
-- interned here; search owns the identity of composite evidence.
data FormationDerivationRecipe = FormationDerivationRecipe
    !(Vector FormationRecipeNode) !FormationRecipeId

data FormationRecipeNode
    = FormationTruthIntroduction
    -- Bound references have no ambient source slot. An implication node owns
    -- their binding; replay rejects any use outside that introduction.
    | FormationBoundHypothesis
    | FormationForallIntroduction !CoreType !FormationRecipeId
    | FormationImplicationIntroduction
        !(ScopedCheckedCore ObjectId) !FormationRecipeId !FormationRecipeId
    | FormationUseHypothesis !HypothesisIx
    | FormationUseImport !ImportIx
    | FormationSuppliedUniversal !FormationRecipeId !UniversalAdapter
    | FormationConjunctionLeftElimination !FormationRecipeId
    | FormationConjunctionRightElimination !FormationRecipeId
    | FormationConjunctionIntroduction
        !FormationRecipeId
        !FormationRecipeId
    | FormationDisjunctionIntroduction !Bool !(ScopedCheckedCore ObjectId) !FormationRecipeId
    | FormationBiconditionalIntroduction !(ScopedCheckedCore ObjectId) !FormationRecipeId !FormationRecipeId
    | FormationBiconditionalElimination !Bool !FormationRecipeId !FormationRecipeId
    | FormationExistentialIntroduction !(ScopedCheckedCore ObjectId) !(CanonicalTerm ObjectId) !FormationRecipeId
    | FormationEqualityReflexivity !(CanonicalTerm ObjectId)
    | FormationForallElimination
        !FormationRecipeId
        !(CanonicalTerm ObjectId)
    | FormationImplicationElimination
        !FormationRecipeId
        !FormationRecipeId
    -- An exact denotation answer retains its original evidence and explicitly
    -- names the requested statement. The consumer checks conversion and scope.
    | FormationConversion
        !FormationRecipeId
        !(ScopedCheckedCore ObjectId)
    | FormationTransport
        !FormationRecipeId
        !(ScopedCheckedCore ObjectId)
        !(ScopedCheckedCore ObjectId)
        !(NonEmpty (ScopedCheckedCore ObjectId, FormationTransportEdge))

-- These ordinary path/direction values carry no checking or proof authority.
data FormationEqualityDirection
    = FormationEqualityLeftToRight
    | FormationEqualityRightToLeft
    deriving stock (Show, Eq, Ord)

data FormationTransportEdge = FormationTransportEdge
    !FormationRecipeId
    !FormationEqualityDirection

data FormationRecipeBuilder = FormationRecipeBuilder
    !(Seq FormationRecipeNode)
    !(Map (Either HypothesisIx ImportIx) FormationRecipeId)
    !(Map (FormationRecipeId, Bool) FormationRecipeId)

emptyFormationRecipeBuilder :: FormationRecipeBuilder
emptyFormationRecipeBuilder = FormationRecipeBuilder Seq.empty Map.empty Map.empty

insertFormationRecipeM
    :: Monad m => (Natural -> m ()) -> (Bool -> m ()) -> FormationRecipeNode
    -> StateT FormationRecipeBuilder m FormationRecipeId
insertFormationRecipeM charge observe node = do
    lift (charge 1)
    FormationRecipeBuilder nodes sources projections <- State.get
    let source = case node of
            FormationUseHypothesis index -> Just (Left index)
            FormationUseImport index -> Just (Right index)
            _ -> Nothing
        projection = case node of
            FormationConjunctionLeftElimination parent -> Just (parent, False)
            FormationConjunctionRightElimination parent -> Just (parent, True)
            _ -> Nothing
        existing = case (source, projection) of
            (Just key, _) -> Map.lookup key sources
            (_, Just key) -> Map.lookup key projections
            _ -> Nothing
    lift (charge (case (source, projection) of
        (Just _, _) -> indexWork (Map.size sources) 1
        (_, Just _) -> indexWork (Map.size projections) 2
        _ -> 0))
    case existing of
        Just reference -> pure reference
        Nothing -> do
            let reference = FormationRecipeId (Seq.length nodes)
            State.put (FormationRecipeBuilder (nodes Seq.|> node)
                (maybe sources (\key -> Map.insert key reference sources) source)
                (maybe projections (\key -> Map.insert key reference projections) projection))
            lift (observe (isJust projection))
            pure reference

-- Only the selected graph escapes a requirement. This walk also compacts
-- source slots, so the result retains neither unused sources nor the arena.
-- Explicit enter/leave work avoids using the Haskell stack as a proof-depth
-- allowance. Construction already guarantees that children precede parents.
data RecipeSelection = RecipeSelection
    { selectedNodes :: !(Seq FormationRecipeNode)
    , selectedReferences :: !(Map FormationRecipeId FormationRecipeId)
    , selectedHypotheses :: !(Map HypothesisIx HypothesisIx)
    , selectedHypothesisOrder :: !(Seq HypothesisIx)
    , selectedImports :: !(Map ImportIx ImportIx)
    , selectedImportOrder :: !(Seq ImportIx)
    }

selectFormationRecipe
    :: Monad m => (Natural -> m ()) -> FormationRecipeId -> FormationRecipeBuilder
    -> m (Vector HypothesisIx, Vector ImportIx, FormationDerivationRecipe)
selectFormationRecipe charge root (FormationRecipeBuilder nodes _ _) = do
    selected <- State.execStateT (visit [Left root])
        (RecipeSelection Seq.empty Map.empty Map.empty Seq.empty Map.empty Seq.empty)
    charge (fromIntegral (Seq.length (selectedNodes selected)
        + Seq.length (selectedHypothesisOrder selected) + Seq.length (selectedImportOrder selected)))
    pure ( Vector.fromList (toList (selectedHypothesisOrder selected))
         , Vector.fromList (toList (selectedImportOrder selected))
         , FormationDerivationRecipe (Vector.fromList (toList (selectedNodes selected)))
            (selectedReferences selected Map.! root) )
  where
    debit = lift . charge
    visit [] = pure ()
    visit (Left original@(FormationRecipeId ordinal):rest) = do
        known <- State.gets selectedReferences
        debit (indexWork (Map.size known) 1)
        if Map.member original known then visit rest else do
            debit (indexWork (Seq.length nodes) 1)
            let node = Seq.index nodes ordinal
                children = formationRecipeChildren node
            debit (fromIntegral (length children))
            visit (fmap Left children <> (Right (original,node) : rest))
    visit (Right (original,node):rest) = do
        prepared <- mapNode node
        selected <- State.get
        debit (indexWork (Map.size (selectedReferences selected)) 1)
        let identifier = FormationRecipeId (Seq.length (selectedNodes selected))
        State.put selected
            { selectedNodes = selectedNodes selected Seq.|> prepared
            , selectedReferences = Map.insert original identifier (selectedReferences selected) }
        visit rest
    reference original = do
        known <- State.gets selectedReferences
        debit (indexWork (Map.size known) 1)
        pure (known Map.! original)
    hypothesis original = do
        selected <- State.get
        debit (2 * indexWork (Map.size (selectedHypotheses selected)) 1)
        case Map.lookup original (selectedHypotheses selected) of
            Just identifier -> pure identifier
            Nothing -> do
                let identifier = hypothesisIx (fromIntegral (Seq.length (selectedHypothesisOrder selected)))
                State.put selected
                    { selectedHypotheses = Map.insert original identifier (selectedHypotheses selected)
                    , selectedHypothesisOrder = selectedHypothesisOrder selected Seq.|> original }
                pure identifier
    imported original = do
        selected <- State.get
        debit (2 * indexWork (Map.size (selectedImports selected)) 1)
        case Map.lookup original (selectedImports selected) of
            Just identifier -> pure identifier
            Nothing -> do
                let identifier = importIx (fromIntegral (Seq.length (selectedImportOrder selected)))
                State.put selected
                    { selectedImports = Map.insert original identifier (selectedImports selected)
                    , selectedImportOrder = selectedImportOrder selected Seq.|> original }
                pure identifier
    mapNode = \case
        FormationUseHypothesis slot -> FormationUseHypothesis <$> hypothesis slot
        FormationUseImport slot -> FormationUseImport <$> imported slot
        node -> traverseFormationRecipeChildren reference node

traverseFormationRecipeChildren
    :: Applicative m => (FormationRecipeId -> m FormationRecipeId)
    -> FormationRecipeNode -> m FormationRecipeNode
traverseFormationRecipeChildren reference = \case
    FormationTruthIntroduction -> pure FormationTruthIntroduction
    FormationBoundHypothesis -> pure FormationBoundHypothesis
    FormationForallIntroduction coreType body -> FormationForallIntroduction coreType <$> reference body
    FormationImplicationIntroduction premise binding body ->
        FormationImplicationIntroduction premise <$> reference binding <*> reference body
    FormationUseHypothesis slot -> pure (FormationUseHypothesis slot)
    FormationUseImport slot -> pure (FormationUseImport slot)
    FormationSuppliedUniversal parent adapter -> (\value -> FormationSuppliedUniversal value adapter) <$> reference parent
    FormationConjunctionLeftElimination parent -> FormationConjunctionLeftElimination <$> reference parent
    FormationConjunctionRightElimination parent -> FormationConjunctionRightElimination <$> reference parent
    FormationConjunctionIntroduction left right -> FormationConjunctionIntroduction <$> reference left <*> reference right
    FormationDisjunctionIntroduction right target parent -> FormationDisjunctionIntroduction right target <$> reference parent
    FormationBiconditionalIntroduction target left right -> FormationBiconditionalIntroduction target <$> reference left <*> reference right
    FormationBiconditionalElimination right parent premise -> FormationBiconditionalElimination right <$> reference parent <*> reference premise
    FormationExistentialIntroduction target witness parent -> FormationExistentialIntroduction target witness <$> reference parent
    FormationEqualityReflexivity operand -> pure (FormationEqualityReflexivity operand)
    FormationForallElimination parent argument -> (\value -> FormationForallElimination value argument) <$> reference parent
    FormationImplicationElimination parent premise -> FormationImplicationElimination <$> reference parent <*> reference premise
    FormationConversion parent target -> (\value -> FormationConversion value target) <$> reference parent
    FormationTransport parent premise target edges -> FormationTransport <$> reference parent <*> pure premise <*> pure target
        <*> traverse (\(predicate, FormationTransportEdge edge direction) ->
            (\value -> (predicate, FormationTransportEdge value direction)) <$> reference edge) edges

formationRecipeChildren :: FormationRecipeNode -> [FormationRecipeId]
formationRecipeChildren = \case
    FormationTruthIntroduction -> []
    FormationBoundHypothesis -> []
    FormationForallIntroduction _ body -> [body]
    FormationImplicationIntroduction _ binding body -> [binding,body]
    FormationUseHypothesis{} -> []
    FormationUseImport{} -> []
    FormationSuppliedUniversal parent _ -> [parent]
    FormationConjunctionLeftElimination parent -> [parent]
    FormationConjunctionRightElimination parent -> [parent]
    FormationConjunctionIntroduction left right -> [left, right]
    FormationDisjunctionIntroduction _ _ parent -> [parent]
    FormationBiconditionalIntroduction _ left right -> [left,right]
    FormationBiconditionalElimination _ parent premise -> [parent,premise]
    FormationExistentialIntroduction _ _ parent -> [parent]
    FormationEqualityReflexivity{} -> []
    FormationForallElimination parent _ -> [parent]
    FormationImplicationElimination parent premise -> [parent, premise]
    FormationConversion parent _ -> [parent]
    FormationTransport parent _ _ edges -> parent :
        [reference | (_, FormationTransportEdge reference _) <- toList edges]

-- The package is constructed with its recipe, so leaf indices refer to these
-- exact ordered sequences. Raw imported arguments are checked by the consumer;
-- checked transport fields enter that consumer through destination admission.
data MaterializedFormationEvidence origin = MaterializedFormationEvidence
    !(Vector (MaterializedNotionHypothesis origin))
    !(Vector SemanticFactOccurrenceFingerprint)
    !FormationDerivationRecipe
    !(Natural, Natural)

-- The query owns this arena. Prepared source handles may retain a root recipe
-- reference, so its conjunction views need no repeated hypothesis admission.
-- Arena sources are exact checked propositions with their original authority
-- origins; equal formulas from different locals remain different hypotheses.
data FormationArena origin = FormationArena
    { arenaRecipes :: !FormationRecipeBuilder
    , arenaHypotheses :: !(Seq (MaterializedNotionHypothesis origin))
    , arenaHypothesisIds :: !(Map origin (Seq (ScopedCheckedCore ObjectId, HypothesisIx)))
    , arenaImports :: !(Seq SemanticFactOccurrenceFingerprint)
    , arenaImportIds :: !(Map SemanticFactOccurrenceFingerprint ImportIx)
    , arenaPreparedProjections :: !(Map (FormationRecipeId, Int) FormationRecipeId)
    }

emptyFormationArena :: FormationArena origin
emptyFormationArena = FormationArena emptyFormationRecipeBuilder Seq.empty Map.empty Seq.empty Map.empty Map.empty

-- A requirement group uses one immutable scope's path table. Keep memoized
-- prefixes with the arena, so later leaves reuse them even when they start a
-- separate search problem. Sibling scopes never share a requirement arena.
arenaProject
    :: Monad m => (Natural -> m ()) -> (Bool -> m ()) -> FormationRecipeId -> ConjunctionProjection
    -> StateT (FormationArena origin) m FormationRecipeId
arenaProject _ _ root RootConjunctionProjection = pure root
arenaProject charge observe root (ConjunctionProjection identifier _ right parent) = do
    known <- State.gets arenaPreparedProjections
    lift (charge (indexWork (Map.size known) 2))
    case Map.lookup (root, identifier) known of
        Just reference -> pure reference
        Nothing -> do
            prefix <- arenaProject charge observe root parent
            reference <- arenaInsert charge observe
                (if right then FormationConjunctionRightElimination prefix
                    else FormationConjunctionLeftElimination prefix)
            current <- State.gets arenaPreparedProjections
            lift (charge (indexWork (Map.size current) 2))
            State.modify' (\arena -> arena
                {arenaPreparedProjections = Map.insert (root, identifier) reference current})
            pure reference

arenaInsert :: Monad m => (Natural -> m ()) -> (Bool -> m ()) -> FormationRecipeNode -> StateT (FormationArena origin) m FormationRecipeId
arenaInsert charge observe node = do
    builder <- State.gets arenaRecipes
    (reference, updated) <- lift (State.runStateT (insertFormationRecipeM charge observe node) builder)
    State.modify' (\arena -> arena {arenaRecipes = updated})
    pure reference

arenaImport
    :: Monad m => (Natural -> m ()) -> (Bool -> m ()) -> SemanticFactOccurrenceFingerprint
    -> StateT (FormationArena origin) m FormationRecipeId
arenaImport charge observe fingerprint = do
    arena <- State.get
    lift (charge (2 * indexWork (Map.size (arenaImportIds arena)) 1))
    slot <- case Map.lookup fingerprint (arenaImportIds arena) of
        Just known -> pure known
        Nothing -> do
            let next = importIx (fromIntegral (Seq.length (arenaImports arena)))
            State.put arena
                { arenaImports = arenaImports arena Seq.|> fingerprint
                , arenaImportIds = Map.insert fingerprint next (arenaImportIds arena) }
            pure next
    arenaInsert charge observe (FormationUseImport slot)

arenaHypothesis
    :: (Monad m, Ord origin) => (Natural -> m ()) -> (Bool -> m ()) -> MaterializedNotionHypothesis origin
    -> StateT (FormationArena origin) m FormationRecipeId
arenaHypothesis charge observe hypothesis@(MaterializedNotionHypothesis proposition origin) = do
    arena <- State.get
    lift (charge (2 * indexWork (Map.size (arenaHypothesisIds arena)) 1))
    let known = Map.findWithDefault Seq.empty origin (arenaHypothesisIds arena)
        search lower upper
            | lower == upper = do
                lift (charge (2 * indexWork (Seq.length known) 1))
                let slot = hypothesisIx (fromIntegral (Seq.length (arenaHypotheses arena)))
                State.put arena
                    { arenaHypotheses = arenaHypotheses arena Seq.|> hypothesis
                    , arenaHypothesisIds = Map.insert origin (Seq.insertAt lower (proposition,slot) known)
                        (arenaHypothesisIds arena) }
                pure slot
            | otherwise = do
                lift (charge (indexWork (Seq.length known) 1))
                let middle = lower + (upper-lower) `div` 2
                    (candidate,slot) = Seq.index known middle
                ordering <- compareChecked proposition candidate
                case ordering of
                    EQ -> pure slot
                    LT -> search lower middle
                    GT -> search (middle+1) upper
    search 0 (Seq.length known) >>= arenaInsert charge observe . FormationUseHypothesis
  where
    compareChecked left right = do
        typeWork (scopedCoreType left)
        typeWork (scopedCoreType right)
        traverse_ typeWork (scopedCoreContext left)
        traverse_ typeWork (scopedCoreContext right)
        let contexts = compare (scopedCoreContext left, scopedCoreType left)
                (scopedCoreContext right, scopedCoreType right)
        if contexts == EQ then lift (compareCanonicalWith (charge 1) (scopedCoreTerm left) (scopedCoreTerm right))
            else pure contexts
    typeWork coreType = do
        lift (charge 1)
        case coreType of
            TySet -> pure ()
            TyProp -> pure ()
            TyArrow argument result -> typeWork argument >> typeWork result

arenaSelect
    :: Monad m => (Natural -> m ()) -> (Natural, Natural) -> FormationRecipeId
    -> StateT (FormationArena origin) m (MaterializedFormationEvidence origin)
arenaSelect charge limits root = do
    arena <- State.get
    (hypotheses, imports, graph) <- lift (selectFormationRecipe charge root (arenaRecipes arena))
    retainedHypotheses <- traverse (\slot -> do
        lift (charge (indexWork (Seq.length (arenaHypotheses arena)) 1))
        let value = Seq.index (arenaHypotheses arena) (fromIntegral (hypothesisIxValue slot))
        value `seq` pure value) hypotheses
    retainedImports <- traverse (\slot -> do
        lift (charge (indexWork (Seq.length (arenaImports arena)) 1))
        let value = Seq.index (arenaImports arena) (fromIntegral (importIxValue slot))
        value `seq` pure value) imports
    pure (MaterializedFormationEvidence retainedHypotheses retainedImports graph limits)

-- Adopt a completed child graph after the owner has discharged or weakened
-- its source slots. Local bindings are copied with their introducing nodes;
-- the child table and unselected proof alternatives do not escape.
arenaGraft
    :: Monad m => (Natural -> m ()) -> (Bool -> m ()) -> Vector FormationRecipeId
    -> Vector SemanticFactOccurrenceFingerprint -> FormationDerivationRecipe
    -> StateT (FormationArena origin) m FormationRecipeId
arenaGraft charge observe hypotheses fingerprints (FormationDerivationRecipe nodes root) = do
    imports <- traverse (arenaImport charge observe) fingerprints
    references <- foldM (copy imports) Seq.empty nodes
    lift (charge (indexWork (Seq.length references) 1))
    let FormationRecipeId ordinal = root
    pure (Seq.index references ordinal)
  where
    copy imports references node = do
        lift (charge 1)
        current <- case node of
            FormationUseHypothesis index -> pure (hypotheses Vector.! fromIntegral (hypothesisIxValue index))
            FormationUseImport index -> pure (imports Vector.! fromIntegral (importIxValue index))
            _ -> do
                prepared <- traverseFormationRecipeChildren (\(FormationRecipeId index) -> do
                    lift (charge (indexWork (Seq.length references) 1))
                    pure (Seq.index references index)) node
                arenaInsert charge observe prepared
        pure (references Seq.|> current)
