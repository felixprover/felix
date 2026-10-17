{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Validated notation used by the HTML renderer.
module Felix.Render.Html.Hints
    ( HintCategory(..)
    , hintCategoryLabel
    , RenderHints
    , RenderHintError(..)
    , renderRenderHintError
    , parseRenderHints
    , hasRenderHint
    , RenderHint
    , resolveRenderHint
    , applyResolvedRenderHint
    , applyRenderHint
    ) where

import Base
import Control.Monad (unless)
import Felix.Syntax.Abstract (Marker(..))
import Felix.Text.BoundedInteger (readBoundedIntegral)
import Felix.Text.Identifier

import Data.Char (isDigit, isSpace)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text


data HintCategory
    = OperatorHint
    | RelationHint
    | PredicateHint
    | PhraseHint
    | StructOpHint
    deriving stock (Show, Eq, Ord, Enum, Bounded)

hintCategoryLabel :: HintCategory -> Text
hintCategoryLabel = \case
    OperatorHint -> "operator"
    RelationHint -> "relation"
    PredicateHint -> "predicate"
    PhraseHint -> "phrase"
    StructOpHint -> "structop"

data TemplatePiece
    = Literal !Text
    | Slot !Int
    deriving stock (Show, Eq, Ord)

data RenderHint = RenderHint !Int ![TemplatePiece]
    deriving stock (Show, Eq, Ord)

newtype RenderHints = RenderHints
    (Map (HintCategory, Marker, Int) RenderHint)
    deriving stock (Show, Eq)

data RenderHintError
    = RenderHintWrongColumnCount !Int !Int
    | RenderHintUnknownCategory !Int !Text
    | RenderHintInvalidMarker !Int !Text
    | RenderHintInvalidArity !Int !Text
    | RenderHintCategoryArity !Int !HintCategory !Int
    | RenderHintInvalidSlot !Int !Text
    | RenderHintSlotOutOfBounds !Int !Int !Int
    | RenderHintDuplicateKey
        !Int
        !Int
        !HintCategory
        !Marker
        !Int
    deriving stock (Show, Eq, Ord)

renderRenderHintError :: RenderHintError -> Text
renderRenderHintError = \case
    RenderHintWrongColumnCount line actual ->
        atLine line
            <> "expected exactly 4 tab-separated columns, found "
            <> Text.pack (show actual)
    RenderHintUnknownCategory line category ->
        atLine line <> "unknown category " <> quote category
    RenderHintInvalidMarker line marker ->
        atLine line <> "invalid marker " <> quote marker
    RenderHintInvalidArity line arity ->
        atLine line <> "invalid nonnegative arity " <> quote arity
    RenderHintCategoryArity line category arity ->
        atLine line <> "invalid " <> hintCategoryLabel category <> " arity " <> Text.pack (show arity)
            <> case category of
                PhraseHint -> "; symbolic phrases take no operands (arity 0)"
                StructOpHint -> "; hosted fields take only an optional receiver (arity 0 or 1)"
                _ -> ""
    RenderHintInvalidSlot line slot ->
        atLine line <> "invalid template slot " <> quote slot
    RenderHintSlotOutOfBounds line slot arity ->
        atLine line <> "template slot " <> Text.pack (show slot)
            <> " exceeds arity " <> Text.pack (show arity)
    RenderHintDuplicateKey line original category (Marker marker) arity ->
        atLine line <> "duplicate " <> hintCategoryLabel category
            <> " hint for " <> quote marker <> " with arity "
            <> Text.pack (show arity) <> "; first declared at line "
            <> Text.pack (show original)
  where
    atLine line = "line " <> Text.pack (show line) <> ": "
    quote value = "\"" <> value <> "\""

parseRenderHints :: Text -> Either (NonEmpty RenderHintError) RenderHints
parseRenderHints source =
    case reverse errors of
        [] -> Right (RenderHints (snd entries))
        failure : failures -> Left (failure :| failures)
  where
    relevantLines =
        [ (lineNumber, line)
        | (lineNumber, line) <- zip [1 :: Int ..] (Text.lines source)
        , not (Text.all isSpace line)
        ]
    (errors, entries) = foldl' addLine ([], (Map.empty, Map.empty)) relevantLines

    addLine
        :: ([RenderHintError], (Map (HintCategory, Marker, Int) Int, Map (HintCategory, Marker, Int) RenderHint))
        -> (Int, Text)
        -> ([RenderHintError], (Map (HintCategory, Marker, Int) Int, Map (HintCategory, Marker, Int) RenderHint))
    addLine (failures, tables@(origins, hints)) numberedLine@(line, _text) =
        case parseLine numberedLine of
            Left failure -> (failure : failures, tables)
            Right (key@(category, marker, arity), hint) ->
                case Map.lookup key origins of
                    Just original ->
                        ( RenderHintDuplicateKey
                            line original category marker arity
                            : failures
                        , tables
                        )
                    Nothing ->
                        ( failures
                        , (Map.insert key line origins, Map.insert key hint hints)
                        )

parseLine
    :: (Int, Text)
    -> Either RenderHintError ((HintCategory, Marker, Int), RenderHint)
parseLine (line, source) =
    case Text.splitOn "\t" source of
        [categorySource, markerSource, aritySource, templateSource] -> do
            category <- parseCategory line categorySource
            marker <- parseMarker line markerSource
            arity <- parseArity line aritySource
            let permitted = case category of
                    PhraseHint -> arity == 0
                    StructOpHint -> arity <= 1
                    _ -> True
            unless permitted (Left (RenderHintCategoryArity line category arity))
            template <- parseTemplate line arity templateSource
            Right ((category, marker, arity), RenderHint arity template)
        columns ->
            Left (RenderHintWrongColumnCount line (length columns))

parseCategory :: Int -> Text -> Either RenderHintError HintCategory
parseCategory line = \case
    "operator" -> Right OperatorHint
    "relation" -> Right RelationHint
    "predicate" -> Right PredicateHint
    "phrase" -> Right PhraseHint
    "structop" -> Right StructOpHint
    other -> Left (RenderHintUnknownCategory line other)

parseMarker :: Int -> Text -> Either RenderHintError Marker
parseMarker line source =
    case Text.uncons source of
        Just (initial, rest)
            | isPortableIdentifierInitial initial
            , Text.all isPortableIdentifierSubsequent rest ->
                Right (Marker source)
        _ -> Left (RenderHintInvalidMarker line source)

parseArity :: Int -> Text -> Either RenderHintError Int
parseArity line source =
    case readBoundedIntegral (Text.unpack source) of
        Just arity | arity >= 0 -> Right arity
        _ -> Left (RenderHintInvalidArity line source)

parseTemplate
    :: Int
    -> Int
    -> Text
    -> Either RenderHintError [TemplatePiece]
parseTemplate line arity = go []
  where
    go pieces source =
        case Text.breakOn "<x" source of
            (literal, rest)
                | Text.null rest ->
                    Right (reverse (addLiteral literal pieces))
                | otherwise -> do
                    let afterPrefix = Text.drop 2 rest
                        (digits, suffix) = Text.span isDigit afterPrefix
                        spelling = "<x" <> digits <> Text.take 2 suffix
                    slot <- case readBoundedIntegral (Text.unpack digits) of
                        Just value
                            | not (Text.null digits)
                            , Text.isPrefixOf "/>" suffix
                            , value > 0 -> Right value
                        _ -> Left (RenderHintInvalidSlot line spelling)
                    if slot <= arity
                        then go
                            (Slot slot : addLiteral literal pieces)
                            (Text.drop 2 suffix)
                        else Left
                            (RenderHintSlotOutOfBounds line slot arity)

    addLiteral literal pieces
        | Text.null literal = pieces
        | otherwise = Literal literal : pieces

resolveRenderHint :: HintCategory -> Marker -> Int -> RenderHints -> Maybe RenderHint
resolveRenderHint category marker arity (RenderHints hints) =
    Map.lookup (category, marker, arity) hints

hasRenderHint :: HintCategory -> Marker -> Int -> RenderHints -> Bool
hasRenderHint category marker arity (RenderHints hints) =
    Map.member (category, marker, arity) hints

-- | Apply a validated hint. Slot lookup is total because parsing has already
-- checked every slot against the key's arity.
applyRenderHint
    :: HintCategory
    -> Marker
    -> [value]
    -> RenderHints
    -> Maybe [Either Text value]
applyRenderHint category marker values hints = do
    hint <- resolveRenderHint category marker (length values) hints
    applyResolvedRenderHint hint values

applyResolvedRenderHint :: RenderHint -> [value] -> Maybe [Either Text value]
applyResolvedRenderHint (RenderHint arity pieces) values = do
    guard (length values == arity)
    traverse applyPiece pieces
  where
    applyPiece = \case
        Literal literal -> Just (Left literal)
        Slot slot ->
            Right <$> (oneBasedIndex slot >>= (`nth` values))
