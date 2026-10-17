{-# LANGUAGE DeriveFoldable #-}

-- | Commentary syntax and the balanced lexical boundaries shared with prose.
module Felix.Render.Html.Markup
    ( SourceSlice(..)
    , PhraseUse(..)
    , phraseMarker
    , phraseName
    , CommandInvocation(..)
    , takeCommandInvocation
    , isBareInvocation
    , takeBalancedGroup
    , MarkupParser
    , prepareMarkupParser
    , lookupMarkupPhrase
    , CommentaryMath(..)
    , Scripts(..)
    , Fence(..)
    , OperatorRole(..)
    , NamedOperatorStyle(..)
    , MarkupMathFailure(..)
    , parseCommentaryMath
    , EnvelopeKind(..)
    , MathEnvelope(..)
    , NarrativePiece(..)
    , takeMathEnvelope
    , splitDisplayEnvelopes
    , stripDisplayPunctuation
    ) where

import Felix.Syntax.Phrase
import Base
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Data.Char (isAlphaNum, isDigit, isLetter, isSpace)
import Data.List (lookup)
import Data.Text qualified as Text
import Felix.Report.Location (Location)
import Felix.Source.Scan qualified as SourceScan
import Felix.Syntax.Abstract (Marker(..))
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Lexicon (Lexicon)
import Felix.Syntax.Token (canonicalVariableControlWord, displayVariable, variableBaseText)
import Text.Megaparsec
    ( ParsecT, chunk, eof, errorBundlePretty, getInput, runParserT, satisfy
    , takeWhileP
    )
import Text.Megaparsec.Char (char)

data SourceSlice = SourceSlice !Location !Text
    deriving (Show, Eq)

data PhraseUse
    = ScopedPhrase !NativePhraseBinding !Text
    | DisplayPhrase !Text
    deriving (Show, Eq)

phraseMarker :: PhraseUse -> Marker
phraseMarker = \case
    ScopedPhrase binding name -> fromMaybe (Marker name) (nativePhraseMarker binding)
    DisplayPhrase name -> Marker name

phraseName :: PhraseUse -> Text
phraseName = \case
    ScopedPhrase _ name -> name
    DisplayPhrase name -> name

data Scripts a
    = Subscript !a
    | Superscript !a
    | SubSuperscript !a !a
    deriving (Show, Eq, Foldable)

data Fence = RoundFence | SquareFence | CurlyFence
    deriving (Show, Eq)

data OperatorRole = PrefixOperator | InfixOperator | SeparatorOperator
    deriving (Show, Eq)

data NamedOperatorStyle = UprightOperator | SansSerifOperator
    deriving (Show, Eq)

data CommentaryMath
    = NativeMath !Concrete.NativeMath
    | MathIdentifier !Text
    | MathNumber !Text
    | MathOperator !OperatorRole !Text
    | MathRow !(NonEmpty CommentaryMath)
    | MathFenced !Fence !CommentaryMath
    | MathScript !CommentaryMath !(Scripts CommentaryMath)
    | MathNamedOperator !NamedOperatorStyle !Text
    | MathPhrase !PhraseUse
    deriving (Show, Eq)

data MarkupMathFailure
    = MarkupUnsupported !Text
    | MarkupNativeAmbiguity !Int
    | MarkupPhraseAmbiguity !(NonEmpty NativePhraseBinding)
    | MarkupScannerInvariant !SourceScan.SourceScanInvariantError
    deriving (Show, Eq)

newtype MarkupParser = MarkupParser Concrete.NativeMathParser

prepareMarkupParser :: Lexicon -> MarkupParser
prepareMarkupParser = MarkupParser . Concrete.prepareNativeMathParser

lookupMarkupPhrase :: MarkupParser -> Text -> Concrete.NativePhraseResolution
lookupMarkupPhrase (MarkupParser native) = Concrete.lookupNativePhrase native

-- Native ambiguity remains decisive. Layout owns overlaps, while native-only
-- syntax retains its selected interpretation without consulting renderer data.
parseCommentaryMath :: MarkupParser -> Text -> Either MarkupMathFailure CommentaryMath
parseCommentaryMath (MarkupParser native) source = do
    selected <- case Concrete.parseNativeMath native source of
        Right value -> Right (Just value)
        Left (Concrete.NativeMathRejected (Concrete.NativeMathAmbiguous count)) ->
            Left (MarkupNativeAmbiguity count)
        Left (Concrete.NativeMathScannerInvariant invariant) ->
            Left (MarkupScannerInvariant invariant)
        Left Concrete.NativeMathRejected{} -> Right Nothing
    case parseLayout native (isNothing selected) source of
        Right value -> Right value
        Left failure@MarkupUnsupported{} ->
            maybe (Left failure) (Right . NativeMath) selected
        Left failure -> Left failure

type LayoutParser = ParsecT Void Text (Either MarkupMathFailure)

parseLayout
    :: Concrete.NativeMathParser -> Bool -> Text
    -> Either MarkupMathFailure CommentaryMath
parseLayout native allowDisplayNames source = do
    parsed <- runParserT (space *> row <* eof) "<commentary>" source
    case parsed of
        Left failure -> Left (MarkupUnsupported (Text.pack (errorBundlePretty failure)))
        Right value -> Right value
  where
    space :: LayoutParser ()
    space = void (takeWhileP Nothing isSpace)
    lexeme parser = parser <* space

    row = do
        firstValue <- chain
        remaining <- many do
            _ <- lexeme (char ',')
            value <- chain
            pure [MathOperator SeparatorOperator ",", value]
        pure (compactRow (firstValue :| concat remaining))

    chain = do
        firstValue <- signedProduct
        remaining <- many do
            operator <- infixOperator
            value <- signedProduct
            pure [MathOperator InfixOperator operator, value]
        pure (compactRow (firstValue :| concat remaining))

    signedProduct = do
        signs <- many (MathOperator PrefixOperator <$> sign)
        firstValue <- scriptedPrimary
        remaining <- many scriptedPrimary
        pure (compactRow (case signs of
            [] -> firstValue :| remaining
            firstSign : rest -> firstSign :| (rest <> (firstValue : remaining))))

    sign = lexeme do
        character <- satisfy (\c -> c == '+' || c == '-' || c == '−')
        pure (if character == '+' then "+" else "−")

    infixOperator = lexeme do
        input <- getInput
        case operatorPrefix input of
            Just (spelling, glyph) -> glyph <$ chunk spelling
            Nothing -> empty

    scriptedPrimary = do
        base <- primary False
        scripts base Nothing Nothing

    scripts base sub sup = do
        input <- getInput
        case Text.uncons input of
            Just ('_', _) -> do
                _ <- lexeme (char '_')
                when (isJust sub) (fail "duplicate subscript")
                argument <- scriptArgument
                scripts base (Just argument) sup
            Just ('^', _) -> do
                _ <- lexeme (char '^')
                when (isJust sup) (fail "duplicate superscript")
                argument <- scriptArgument
                scripts base sub (Just argument)
            _ -> pure case (sub, sup) of
                (Nothing, Nothing) -> base
                (Just value, Nothing) -> MathScript base (Subscript value)
                (Nothing, Just value) -> MathScript base (Superscript value)
                (Just lower, Just upper) -> MathScript base (SubSuperscript lower upper)

    scriptArgument = do
        input <- getInput
        case Text.uncons input of
            Just ('{', _) -> lexeme (char '{') *> row <* lexeme (char '}')
            _ -> primary True

    primary singleDigit = lexeme do
        input <- getInput
        case Text.uncons input of
            Just (c, _) | isDigit c -> do
                firstDigit <- satisfy isDigit
                remaining <- if singleDigit then pure "" else takeWhileP Nothing isDigit
                pure (MathNumber (Text.cons firstDigit remaining))
            Just (c, _) | isLetter c -> MathIdentifier . Text.singleton <$> satisfy isLetter
            Just ('(', _) -> fenced RoundFence "(" ")"
            Just ('[', _) -> fenced SquareFence "[" "]"
            Just ('{', _)
                | "{-}" `Text.isPrefixOf` input ->
                    MathOperator PrefixOperator "−" <$ chunk "{-}"
                | otherwise -> do
                    _ <- lexeme (char '{')
                    value <- row <* lexeme (char '}')
                    pure (MathRow (value :| []))
            Just ('\\', _)
                | "\\{" `Text.isPrefixOf` input -> fenced CurlyFence "\\{" "\\}"
                | isJust (operatorPrefix input) -> empty
                | otherwise -> commandPrimary input
            _ -> empty

    fenced fence opening closing =
        MathFenced fence <$> (lexeme (chunk opening) *> row <* lexeme (chunk closing))

    commandPrimary input =
        case takeCommandInvocation input of
            Nothing -> empty
            Just (invocation, _) -> do
                let name = invocationName invocation
                    spelling = invocationSource invocation
                case name of
                    "operatorname" -> do
                        _ <- chunk spelling
                        case operatorName invocation of
                            Just (style, text) -> pure (MathNamedOperator style text)
                            Nothing -> fail "malformed named operator"
                    "ON" -> bareIdentifier invocation (MathNamedOperator UprightOperator "ON")
                    "varphi" -> bareIdentifier invocation (MathIdentifier "φ")
                    _ | Just canonical <- canonicalVariableControlWord name ->
                            bareIdentifier invocation
                                (MathIdentifier (variableBaseText (displayVariable canonical)))
                      | otherwise -> do
                            _ <- chunk spelling
                            nativeCommand invocation

    bareIdentifier invocation value = do
        _ <- chunk (invocationSource invocation)
        unless (null (invocationGroups invocation) && invocationComplete invocation)
            (fail "identifier command does not take arguments")
        pure value

    nativeCommand invocation =
        case Concrete.parseNativeMath native (invocationSource invocation) of
            Right value -> pure (NativeMath value)
            Left (Concrete.NativeMathScannerInvariant invariant) ->
                lift (Left (MarkupScannerInvariant invariant))
            Left (Concrete.NativeMathRejected (Concrete.NativeMathAmbiguous count)) ->
                lift (Left (MarkupNativeAmbiguity count))
            Left Concrete.NativeMathRejected{} -> do
                unless (isBareInvocation invocation) (fail "unsupported complete command application")
                let name = invocationName invocation
                case Concrete.lookupNativePhrase native name of
                    Concrete.UniqueNativePhrase binding -> pure (MathPhrase (ScopedPhrase binding name))
                    Concrete.AmbiguousNativePhrase bindings ->
                        lift (Left (MarkupPhraseAmbiguity bindings))
                    Concrete.NoNativePhrase
                        | allowDisplayNames -> pure (MathPhrase (DisplayPhrase name))
                        | otherwise -> fail "command belongs to native-only syntax"

compactRow :: NonEmpty CommentaryMath -> CommentaryMath
compactRow (value :| []) = value
compactRow values = MathRow values

operatorName :: CommandInvocation -> Maybe (NamedOperatorStyle, Text)
operatorName invocation = do
    guard (invocationComplete invocation)
    raw <- case invocationGroups invocation of
        [('{', value)] -> Just (Text.strip value)
        _ -> Nothing
    let styled = do
            (nested, rest) <- takeCommandInvocation raw
            guard (invocationName nested == "textsf" && Text.null rest)
            case invocationGroups nested of
                [('{', value)] | invocationComplete nested -> Just (SansSerifOperator, Text.strip value)
                _ -> Nothing
        (style, name) = fromMaybe (UprightOperator, raw) styled
    (firstLetter, rest) <- Text.uncons name
    guard (isLetter firstLetter && Text.all isAlphaNum rest)
    pure (style, name)

operatorPrefix :: Text -> Maybe (Text, Text)
operatorPrefix source = case Text.uncons source of
    Just (character, _) -> case character of
        '+' -> Just ("+", "+")
        '-' -> Just ("-", "−")
        '−' -> Just ("−", "−")
        '/' -> Just ("/", "/")
        '=' -> Just ("=", "=")
        '<' -> Just ("<", "<")
        '>' -> Just (">", ">")
        '\\' -> do
            let name = Text.takeWhile isLetter (Text.drop 1 source)
            glyph <- lookup name
                [ ("cdot", "·"), ("times", "×"), ("circ", "∘")
                , ("mapsto", "↦"), ("to", "→"), ("longrightarrow", "→")
                , ("in", "∈"), ("notin", "∉"), ("subseteq", "⊆"), ("neq", "≠")
                ]
            pure ("\\" <> name, glyph)
        _ -> Nothing
    Nothing -> Nothing

data EnvelopeKind = InlineEnvelope | DisplayEnvelope | UnsupportedDollarEnvelope
    deriving (Show, Eq)

data MathEnvelope = MathEnvelope
    { envelopeKind :: !EnvelopeKind
    , envelopeSource :: !Text
    , envelopeBody :: !(Maybe Text)
    } deriving (Show, Eq)

data NarrativePiece = NarrativeProse !Text | NarrativeDisplay !MathEnvelope
    deriving (Show, Eq)

takeMathEnvelope :: Text -> Maybe (MathEnvelope, Text)
takeMathEnvelope source = do
    (kind, opening, closing) <- find (\(_, prefix, _) -> prefix `Text.isPrefixOf` source)
        [ (UnsupportedDollarEnvelope, "$$", "$$")
        , (InlineEnvelope, "$", "$")
        , (InlineEnvelope, "\\(", "\\)")
        , (DisplayEnvelope, "\\[", "\\]")
        ]
    let body = Text.drop (Text.length opening) source
    pure case closingAt closing 0 body of
        Nothing -> (MathEnvelope kind (Text.copy source) Nothing, "")
        Just (bodySize, rest) ->
            let completeSize = Text.length opening + bodySize + Text.length closing
            in (MathEnvelope kind (Text.copy (Text.take completeSize source))
                    (Just (Text.copy (Text.take bodySize body))), rest)
  where
    closingAt closing consumed remaining
        | Just rest <- Text.stripPrefix closing remaining = Just (consumed, rest)
        | otherwise = do
            (character, rest) <- Text.uncons remaining
            if character == '\\'
                then Text.uncons rest >>= closingAt closing (consumed + 2) . snd
                else closingAt closing (consumed + 1) rest

-- Displays are split before paragraphs, but commands and inline envelopes keep
-- ownership of their complete contents (including displays nested in emphasis).
splitDisplayEnvelopes :: Text -> [NarrativePiece]
splitDisplayEnvelopes source = scan source 0 source
  where
    scan original consumed remaining
        | Text.null remaining = prose (Text.take consumed original)
        | Just (envelope, rest) <- takeMathEnvelope remaining =
            case envelopeKind envelope of
                InlineEnvelope ->
                    scan original (consumed + Text.length (envelopeSource envelope)) rest
                _ -> prose (Text.take consumed original)
                    <> (NarrativeDisplay envelope : scan rest 0 rest)
        | Just (invocation, rest) <- takeCommandInvocation remaining =
            scan original (consumed + Text.length (invocationSource invocation)) rest
        | Just ('\\', rest) <- Text.uncons remaining
        , Just (_, afterEscape) <- Text.uncons rest =
            scan original (consumed + 2) afterEscape
        | Just (_, rest) <- Text.uncons remaining = scan original (consumed + 1) rest
        | otherwise = []
    prose text = [NarrativeProse (Text.copy text) | not (Text.null text)]

stripDisplayPunctuation :: Text -> Maybe (Text, Text)
stripDisplayPunctuation source = do
    (body, punctuation) <- Text.unsnoc (Text.stripEnd source)
    guard (punctuation == '.' || punctuation == ',')
    guard (balanced [] body)
    pure (Text.stripEnd body, Text.singleton punctuation)
  where
    balanced stack remaining = case Text.uncons remaining of
        Nothing -> null stack
        Just ('\\', rest) -> case Text.uncons rest of
            Just (_, afterEscape) -> balanced stack afterEscape
            Nothing -> False
        Just (character, rest) -> case character of
            '(' -> balanced (')' : stack) rest
            '[' -> balanced (']' : stack) rest
            '{' -> balanced ('}' : stack) rest
            ')' -> close ')' stack rest
            ']' -> close ']' stack rest
            '}' -> close '}' stack rest
            _ -> balanced stack rest
    close closing (expected : rest) sourceRest =
        closing == expected && balanced rest sourceRest
    close _ [] _ = False

data CommandInvocation = CommandInvocation
    { invocationName :: !Text
    , invocationSource :: !Text
    , invocationGroups :: ![(Char, Text)]
    , invocationComplete :: !Bool
    } deriving (Show, Eq)

isBareInvocation :: CommandInvocation -> Bool
isBareInvocation invocation =
    invocationComplete invocation && case invocationGroups invocation of
        [] -> True
        [('{', contents)] -> Text.null contents
        _ -> False

-- | Consume maximal associated groups; an unclosed group retains the remainder.
takeCommandInvocation :: Text -> Maybe (CommandInvocation, Text)
takeCommandInvocation source = do
    afterSlash <- Text.stripPrefix "\\" source
    let (name, afterName) = Text.span isLetter afterSlash
    guard (not (Text.null name))
    let (consumed, groups, complete, remaining) =
            arguments (1 + Text.length name) [] afterName
        spelling = Text.copy (Text.take consumed source)
    pure (CommandInvocation name spelling groups complete, remaining)
  where
    arguments consumed reversed remaining =
        let spaces = Text.takeWhile (\c -> c == ' ' || c == '\t') remaining
            afterSpace = Text.drop (Text.length spaces) remaining
        in case Text.uncons afterSpace of
            Just (opening, _) | opening == '{' || opening == '[' ->
                case scanBalancedGroup afterSpace of
                    Nothing -> (consumed + Text.length remaining, reverse reversed, False, "")
                    Just (groupSize, rest) ->
                        let contents = Text.copy (Text.take (groupSize - 2) (Text.drop 1 afterSpace))
                        in arguments (consumed + Text.length spaces + groupSize)
                            ((opening, contents) : reversed) rest
            _ -> (consumed, reverse reversed, True, remaining)

-- | Match braces/brackets, ignoring escaped delimiters. The body excludes fences.
takeBalancedGroup :: Text -> Maybe (Text, Text)
takeBalancedGroup source = do
    (consumed, remaining) <- scanBalancedGroup source
    pure (Text.copy (Text.take (consumed - 2) (Text.drop 1 source)), remaining)

-- Carry a consumed count rather than repeatedly measuring the unconsumed suffix.
scanBalancedGroup :: Text -> Maybe (Int, Text)
scanBalancedGroup source = do
    (opening, rest) <- Text.uncons source
    closing <- case opening of
        '{' -> Just '}'
        '[' -> Just ']'
        _ -> Nothing
    scan 1 [closing] rest
  where
    scan consumed closings remaining = do
        (character, rest) <- Text.uncons remaining
        case (character, closings) of
            ('\\', _) -> Text.uncons rest >>= scan (consumed + 2) closings . snd
            ('{', _) -> scan (consumed + 1) ('}' : closings) rest
            ('[', _) -> scan (consumed + 1) (']' : closings) rest
            (_, expected : pending)
                | character == expected ->
                    if null pending then Just (consumed + 1, rest)
                    else scan (consumed + 1) pending rest
            ('}', _) -> Nothing
            (']', _) -> Nothing
            _ -> scan (consumed + 1) closings rest
