{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Surface tokens and their parser-facing stream representation. Source
-- recognition and token construction are owned by "Felix.Source.Scan".
module Felix.Syntax.Token
    ( Token(..)
    , VariableDisplay(..)
    , VariableSuffix(..)
    , displayVariable
    , canonicalVariableControlWord
    , renderVariableText
    , tokToString
    , tokToText
    , TokStream(..)
    , Located(..)
    , Whitespace(..)
    ) where


import Base

import Felix.Report.Location

import Control.DeepSeq (NFData)
import Data.Text qualified as Text
import Prettyprinter (Pretty(..))


-- |
-- A token stream as input stream for a parser. Contains the raw input
-- before tokenization as 'Text' for showing error messages.
--
data TokStream = TokStream
    { rawInput :: !Text
    , unTokStream :: ![[Located Token]]
    } deriving (Show, Eq)

instance Semigroup TokStream where
    TokStream raw1 toks1 <> TokStream raw2 toks2 = TokStream (raw1 <> raw2) (toks1 <> toks2)

instance Monoid TokStream where
    mempty = TokStream mempty mempty

-- | A LaTeX token.
-- Invisible delimiters 'InvisibleBraceL' and 'InvisibleBraceR' are
-- unescaped braces used for grouping in TEX (@{@),
-- visibles braces are escaped braces (@\\{@).
data Token
    = Word !Text
    | Variable !Text
    | Symbol !Text
    | Integer !Integer
    | Command !Text
    | NamedItem !Text -- ^ An item heading, retaining its written spelling.
    | CaseHeading !Text
    -- ^ A caseOf command with a possible plain heading. Its argument tokens
    -- still follow, so ordinary logical cases keep their existing grammar.
    | CommandReference !Text !(NonEmpty Text)
    -- ^ A proof-method command with a nonempty marker argument. The scanner
    -- currently emits this only for @\auto{...}@ and @\obv{...}@.
    | Label Text -- ^ A /@\\label{...}@/ command (case-sensitive).
    | Ref (NonEmpty Text) -- ^ A /@\\ref{...}@/ command (case-sensitive).
    | BeginEnv !Text
    | EndEnv !Text
    | ParenL | ParenR
    | BracketL | BracketR
    | VisibleBraceL | VisibleBraceR
    | InvisibleBraceL | InvisibleBraceR
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)

instance IsString Token where
    fromString w = Word (Text.pack w)

data VariableDisplay = VariableDisplay
    { variableBaseText :: !Text
    , variableSuffix :: !(Maybe VariableSuffix)
    } deriving (Show, Eq, Ord)

data VariableSuffix
    = VariableSubscript !Text
    | VariableTicks !Int
    deriving (Show, Eq, Ord)

displayVariable :: Text -> VariableDisplay
displayVariable rawName =
    case splitVariableBase rawName of
        Nothing ->
            VariableDisplay rawName Nothing
        Just (baseText, suffixText) ->
            VariableDisplay baseText (displayVariableSuffix suffixText)

renderVariableText :: Text -> Text
renderVariableText rawName =
    case displayVariable rawName of
        VariableDisplay baseText Nothing ->
            baseText
        VariableDisplay baseText (Just (VariableTicks n)) ->
            baseText <> Text.replicate n "'"
        VariableDisplay baseText (Just (VariableSubscript subscriptText)) ->
            baseText <> renderSubscriptText subscriptText

splitVariableBase :: Text -> Maybe (Text, Text)
splitVariableBase rawName =
    matchBlackboardBase rawName <|> matchGreekBase rawName <|> matchSingleLetterBase rawName

matchBlackboardBase :: Text -> Maybe (Text, Text)
matchBlackboardBase rawName = do
    suffixText <- Text.stripPrefix "bb" rawName
    case Text.uncons suffixText of
        Just (upper, rest)
            | 'A' <= upper && upper <= 'Z' ->
                Just ("bb" <> Text.singleton upper, rest)
        _ ->
            Nothing

matchGreekBase :: Text -> Maybe (Text, Text)
matchGreekBase rawName =
    asum
        [ (\suffixText -> (rendered, suffixText)) <$> Text.stripPrefix prefix rawName
        | (prefix, rendered) <- greekVariables
        ]

matchSingleLetterBase :: Text -> Maybe (Text, Text)
matchSingleLetterBase rawName = do
    (baseChar, suffixText) <- Text.uncons rawName
    pure (Text.singleton baseChar, suffixText)

displayVariableSuffix :: Text -> Maybe VariableSuffix
displayVariableSuffix suffixText
    | Text.null suffixText =
        Nothing
    | Text.all (== '_') suffixText =
        Just (VariableTicks (Text.length suffixText))
    | otherwise =
        Just (VariableSubscript (Text.replace "_" "'" suffixText))

renderSubscriptText :: Text -> Text
renderSubscriptText subscriptText
    | Text.length subscriptText == 1 =
        "_" <> subscriptText
    | otherwise =
        "_{" <> subscriptText <> "}"

greekVariables :: [(Text, Text)]
greekVariables =
    [ ("alpha", "α"), ("beta", "β"), ("gamma", "γ"), ("delta", "δ")
    , ("epsilon", "ε"), ("zeta", "ζ"), ("eta", "η"), ("theta", "θ")
    , ("iota", "ι"), ("kappa", "κ"), ("lambda", "λ"), ("mu", "μ")
    , ("nu", "ν"), ("xi", "ξ"), ("pi", "π"), ("rho", "ρ"), ("sigma", "σ")
    , ("tau", "τ"), ("upsilon", "υ"), ("phi", "φ"), ("chi", "χ")
    , ("psi", "ψ"), ("omega", "ω")
    , ("Gamma", "Γ"), ("Delta", "Δ"), ("Theta", "Θ"), ("Lambda", "Λ")
    , ("Xi", "Ξ"), ("Pi", "Π"), ("Sigma", "Σ"), ("Upsilon", "Υ")
    , ("Phi", "Φ"), ("Psi", "Ψ"), ("Omega", "Ω")
    ]

-- | Recognize a TeX control word whose canonical token spelling denotes a
-- Greek variable.
canonicalVariableControlWord :: Text -> Maybe Text
canonicalVariableControlWord spelling =
    fst <$> find ((== spelling) . fst) greekVariables

tokToText :: Token -> Text
tokToText = \case
    Word w -> w
    Variable v -> renderVariableText v
    Symbol s -> s
    Integer n -> Text.pack (show n)
    Command cmd -> Text.cons '\\' cmd
    NamedItem name -> "\\item[" <> name <> "]"
    CaseHeading _ -> "\\caseOf"
    CommandReference cmd markers ->
        "\\" <> cmd <> "{"
            <> Text.intercalate ", " (toList markers)
            <> "}"
    Label m -> "\\label{" <> m <> "}"
    Ref ms -> "\\ref{" <> Text.intercalate ", " (toList ms) <> "}"
    BeginEnv "math" -> "$"
    EndEnv "math" -> "$"
    BeginEnv env -> "\\begin{" <> env <> "}"
    EndEnv env -> "\\end{" <> env <> "}"
    ParenL -> "("
    ParenR -> ")"
    BracketL -> "["
    BracketR -> "]"
    VisibleBraceL -> "\\{"
    VisibleBraceR -> "\\}"
    InvisibleBraceL -> "{"
    InvisibleBraceR -> "}"

tokToString :: Token -> String
tokToString = Text.unpack . tokToText

instance Pretty Token where
    pretty = \case
        Word w -> pretty w
        Variable v -> pretty (renderVariableText v)
        Symbol s -> pretty s
        Integer n -> pretty n
        Command cmd -> "\\" <> pretty cmd
        NamedItem name -> "\\item[" <> pretty name <> "]"
        CaseHeading _ -> "\\caseOf"
        CommandReference cmd markers ->
            "\\" <> pretty cmd <> "{"
                <> pretty (Text.intercalate ", " (toList markers))
                <> "}"
        Label m -> "\\label{" <> pretty m <> "}"
        Ref m -> "\\ref{" <> pretty m <> "}"
        BeginEnv env -> "\\begin{" <> pretty env <> "}"
        EndEnv env -> "\\end{" <> pretty env <> "}"
        ParenL -> "("
        ParenR -> ")"
        BracketL -> "["
        BracketR -> "]"
        VisibleBraceL -> "\\{"
        VisibleBraceR -> "\\}"
        InvisibleBraceL -> "{"
        InvisibleBraceR -> "}"


data Located a = Located
    { startPos :: !Location
    , unLocated :: !a
    , postWhitespace :: Whitespace
    } deriving (Show, Functor)

data Whitespace = NoSpace | Space deriving (Show, Eq)

instance Eq a  => Eq  (Located a) where (==) = (==) `on` unLocated
instance Ord a => Ord (Located a) where compare = compare `on` unLocated
