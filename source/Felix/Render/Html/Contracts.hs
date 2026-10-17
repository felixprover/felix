{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Run-local frontend associations. These never enter semantic interface IDs.
module Felix.Render.Html.Contracts
    ( Notation
    , operatorNotation
    , relationNotation
    , fieldNotation
    , phraseNotation
    , predicateNotation
    , notationCategory
    , notationMarker
    , notationForKey
    , NotationBindings
    , withFieldBindings
    , withStructurePhraseBindings
    , checkedNotationBindings
    , NotationContracts
    , resolveNotationContracts
    , notationContractMarker
    , hasNotationContract
    , applyNotationContract
    ) where

import Base
import Control.Monad (foldM)
import Felix.Checking.Identity (FieldId, ObjectId, StructureId)
import Felix.Checking.Structure.Schema qualified as Schema
import Data.Set qualified as Set
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Elaboration.Vocabulary (FixedSemanticMeaning, fixedSemanticMeaning)
import Felix.Syntax.Interface (CanonicalLexicalEntry(..), fixedBaseSyntaxEntries)
import Felix.Syntax.Phrase
import Felix.Render.Html.Hints
import Felix.Syntax.Abstract qualified as Raw
import Data.List (nub)
import Data.Maybe (mapMaybe)
import Data.Map.Strict qualified as Map

-- A relation template renders its parameterized symbol; the two operands are
-- rendered by the surrounding chain. Prefix predicates render every argument.
data Notation
    = OperatorNotation !Raw.Pattern !Raw.Marker
    | RelationNotation !Raw.Token !Raw.ParameterArity !Raw.Marker
    | PredicateNotation !Text !Integer !Raw.Marker
    | FieldNotation !Raw.StructSymbol !ReceiverForm
    | PhraseNotation !NativePhraseBinding
    deriving stock (Show, Eq, Ord)

data ReceiverForm = OmittedReceiver | ExplicitReceiver
    deriving stock (Show, Eq, Ord)

fieldNotation :: Raw.StructSymbol -> Maybe receiver -> Notation
fieldNotation symbol receiver = FieldNotation symbol
    (if isJust receiver then ExplicitReceiver else OmittedReceiver)

phraseNotation :: NativePhraseBinding -> Notation
phraseNotation = PhraseNotation

operatorNotation :: Raw.MixfixItem -> Notation
operatorNotation item = OperatorNotation (Raw.mixfixPattern item) (Raw.mixfixMarker item)

relationNotation :: Raw.RelationSymbol -> Notation
relationNotation symbol = RelationNotation (Raw.relationSymbolToken symbol)
    (Raw.relationSymbolParameterArity symbol) (Raw.relationSymbolMarker symbol)

predicateNotation :: Raw.PrefixPredicate -> Raw.Marker -> Notation
predicateNotation (Raw.PrefixPredicate command arity) = PredicateNotation command (toInteger arity)

notationCategory :: Notation -> HintCategory
notationCategory = \case
    OperatorNotation{} -> OperatorHint
    RelationNotation{} -> RelationHint
    PredicateNotation{} -> PredicateHint
    FieldNotation{} -> StructOpHint
    PhraseNotation{} -> PhraseHint

notationMarker :: Notation -> Raw.Marker
notationMarker = \case
    OperatorNotation _ marker -> marker
    RelationNotation _ _ marker -> marker
    PredicateNotation _ _ marker -> marker
    FieldNotation (Raw.StructSymbol name) _ -> Raw.Marker name
    PhraseNotation binding -> fromMaybe
        (case nativePhraseCommands binding of
            name : _ -> Raw.Marker name
            [] -> impossible "a symbolic phrase lost its command")
        (nativePhraseMarker binding)

notationArity :: Notation -> Integer
notationArity = \case
    OperatorNotation pattern' _ -> arity pattern'
    RelationNotation _ parameters _ -> toInteger (Raw.parameterArityValue parameters)
    PredicateNotation _ count _ -> count
    FieldNotation _ OmittedReceiver -> 0
    FieldNotation _ ExplicitReceiver -> 1
    PhraseNotation{} -> 0
  where
    arity = \case
        Raw.End -> 0
        Raw.TokenCons _ rest -> arity rest
        Raw.HoleCons rest -> 1 + arity rest

notationForKey :: Semantic.SemanticGlobalKey -> Raw.Marker -> Maybe Notation
notationForKey key marker = case key of
    Semantic.SemanticTypedConstant token _ -> Just (OperatorNotation (Raw.TokenCons token Raw.End) marker)
    Semantic.SemanticExpressionFunction pattern' -> Just (OperatorNotation pattern' marker)
    Semantic.SemanticRelation token arity -> Just (RelationNotation token arity marker)
    Semantic.SemanticPrefixPredicate command arity -> Just (PredicateNotation command (toInteger arity) marker)
    Semantic.SemanticNoun singular plural -> phrase (CanonicalNoun singular plural marker)
    Semantic.SemanticFunctionPhrase singular plural -> phrase (CanonicalFunctionPhrase singular plural marker)
    Semantic.SemanticVerb surfaces -> phrase (CanonicalVerb surfaces marker)
    Semantic.SemanticLeftAdjective Semantic.OrdinaryAdjectiveReading pattern' ->
        phrase (CanonicalUserAdjective Raw.LeftAdjectiveSide (Raw.AdjectiveSurfaceKey pattern'))
    Semantic.SemanticRightAdjective Semantic.OrdinaryAdjectiveReading pattern' ->
        phrase (CanonicalUserAdjective Raw.RightAdjectiveSide (Raw.AdjectiveSurfaceKey pattern'))
    _ -> Nothing
  where
    phrase = fmap PhraseNotation . nativePhraseBinding

data FieldBinding = FieldBinding !StructureId !FieldId !ObjectId
    deriving stock (Show, Eq, Ord)

data NotationBinding
    = DeclaredNotation !Semantic.GlobalBindingRef !Raw.Marker
    | FixedNotation !FixedSemanticMeaning
    | FieldBindings !(Set FieldBinding)
    | StructurePhraseBinding !StructureId
    deriving stock (Show, Eq)

newtype NotationBindings = NotationBindings (Map Notation NotationBinding)
    deriving stock (Show, Eq)

-- A structop template is explicitly uniform over checked fields with that
-- spelling. Retain every owner; do not pick one or infer an omitted receiver.
-- Each member has the language's unary projection/receiver convention.
withFieldBindings :: [Schema.ResolvedStructureSchema] -> NotationBindings -> NotationBindings
withFieldBindings schemas (NotationBindings bindings) = NotationBindings
    (Map.unionWith merge fields bindings)
  where
    merge (FieldBindings left) (FieldBindings right) = FieldBindings (Set.union left right)
    merge _ _ = impossible "a hosted field key has a non-field binding"
    bySymbol = Map.fromListWith Set.union
        [(Schema.resolvedFieldSymbol field, Set.singleton
            (FieldBinding (Schema.resolvedFieldOwner field) (Schema.resolvedFieldIdentity field)
                (Schema.resolvedFieldProjection field)))
        | schema <- schemas, field <- Map.elems (Schema.resolvedSchemaFields schema)]
    fields = Map.fromList
        [(FieldNotation symbol form, FieldBindings owners)
        | (symbol, owners) <- Map.toAscList bySymbol, form <- [OmittedReceiver, ExplicitReceiver]]

-- A structure phrase has one checked schema owner. Unlike an explicitly
-- uniform field template, its display marker cannot merge distinct schemas.
withStructurePhraseBindings
    :: [Schema.ResolvedStructureSchema] -> NotationBindings -> Either Text NotationBindings
withStructurePhraseBindings schemas (NotationBindings bindings) =
    NotationBindings <$> foldM insert bindings entries
  where
    entries =
        [(PhraseNotation binding, StructurePhraseBinding (Schema.resolvedSchemaId schema))
        | schema <- schemas
        , let phrase = Schema.resolvedSchemaPhrase schema
        , Just binding <- [nativePhraseBinding (CanonicalStructureNoun
            (Schema.structurePhraseSingular phrase) (Schema.structurePhrasePlural phrase)
            (Schema.structurePhraseMarker phrase))]]
    insert table (notation, owner) = case Map.lookup notation table of
        Just previous | previous /= owner -> Left
            ("ambiguous structure phrase presentation binding: " <> fromString (show notation))
        _ -> Right (Map.insert notation owner table)

-- Checked deltas supply the owner and operand binding. A display marker is not
-- authority to associate two different declarations.
checkedNotationBindings :: [Semantic.DeclarationInterfaceDelta] -> Either Text NotationBindings
checkedNotationBindings deltas = do
    declared <- foldM insert Map.empty [(notation, reference) | (_, notation, reference) <- declarations]
    NotationBindings <$> foldM addFixedSurface declared fixedSurfaces
  where
    declarations =
        [(key, notation, DeclaredNotation (Semantic.globalBindingRef (Semantic.declarationDeltaSlot delta) key)
            (Raw.Marker (Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding))))
        | delta <- deltas
        , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)
        , let key = Semantic.semanticGlobalBindingKey binding
        , Just notation <- [notationForKey key
            (Raw.Marker (Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding)))]]
    insert bindings (notation, reference) = case Map.lookup notation bindings of
        Just previous | previous /= reference -> Left
            ("ambiguous notation presentation binding: " <> fromString (show notation))
        _ -> Right (Map.insert notation reference bindings)
    fixedSurfaces = mapMaybe surface fixedBaseSyntaxEntries
    surface = \case
        CanonicalExpressionFunction pattern' marker _ ->
            Just (Semantic.SemanticExpressionFunction pattern', OperatorNotation pattern' marker)
        CanonicalRelation token arity marker ->
            Just (Semantic.SemanticRelation token arity, RelationNotation token arity marker)
        CanonicalPrefixPredicate command arity marker ->
            Just (Semantic.SemanticPrefixPredicate command arity, PredicateNotation command (toInteger arity) marker)
        entry -> do
            binding <- nativePhraseBinding entry
            key <- Semantic.semanticGlobalKeyFromLexicalEntry entry
            pure (key, PhraseNotation binding)
    -- Fixed parser markers can differ from the prelude declaration label.
    -- Resolve the exact semantic key, using the elaborator's intrinsic table.
    addFixedSurface bindings (key, notation) =
        case fixedSemanticMeaning key of
            Just meaning -> insert bindings (notation, FixedNotation meaning)
            Nothing -> case nub [reference | (candidate, _, reference) <- declarations, candidate == key] of
                [] -> Right bindings
                [reference] -> insert bindings (notation, reference)
                _ -> Left ("ambiguous fixed notation surface: " <> fromString (show notation))

data NotationContract = NotationContract !NotationBinding !Raw.Marker !Int !(Maybe RenderHint)
    deriving stock (Show, Eq)

newtype NotationContracts = NotationContracts (Map Notation NotationContract)
    deriving stock (Show, Eq)

resolveNotationContracts :: RenderHints -> NotationBindings -> NotationContracts
resolveNotationContracts hints (NotationBindings bindings) = NotationContracts
    (Map.mapMaybeWithKey resolve bindings)
  where
    resolve notation reference = do
        let count = notationArity notation
        guard (count >= 0 && count <= toInteger (maxBound :: Int))
        let arity = fromInteger count
        let marker = case (notation, reference) of
                (PhraseNotation binding, DeclaredNotation _ label) -> fromMaybe label (nativePhraseMarker binding)
                _ -> notationMarker notation
        pure (NotationContract reference marker arity (resolveRenderHint (notationCategory notation) marker arity hints))

notationContractMarker :: NotationContracts -> Notation -> Raw.Marker
notationContractMarker (NotationContracts contracts) notation = case Map.lookup notation contracts of
    Just (NotationContract _ marker _ _) -> marker
    Nothing -> notationMarker notation

hasNotationContract :: NotationContracts -> Notation -> Int -> Bool
hasNotationContract contracts notation count = isJust (lookupContract contracts notation count)

lookupContract :: NotationContracts -> Notation -> Int -> Maybe RenderHint
lookupContract (NotationContracts contracts) notation count = do
    NotationContract _reference _marker expected hint <- Map.lookup notation contracts
    guard (count == expected)
    hint

applyNotationContract :: NotationContracts -> Notation -> [value] -> Maybe [Either Text value]
applyNotationContract contracts notation values = do
    hint <- lookupContract contracts notation (length values)
    applyResolvedRenderHint hint values
