{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Syntax.LexicalPhrase where


import Base
import Felix.Syntax.Token (Token(..))

import Control.Applicative qualified as Applicative
import Control.DeepSeq (NFData)
import Data.Char (isAlpha)
import Data.List qualified as List
import Data.Text qualified as Text
import Text.Earley.Mixfix (Holey)
import Text.Earley (Grammar, Prod, (<?>), fullParses, parser, rule, token, satisfy)



-- | 'LexicalPhrase's should be nonempty lists with at least one proper word token.
-- Hyphens and quotes in words are treated as letters.
-- Thus /@manifold-with-boundary@/ is a singleton lexical phrase (one word).
--
type LexicalPhrase = Holey Token

-- MAYBE Add this instance by making LexicalPhrase a proper Type?
-- Until then we can use the default instance for lists of prettyprintable things.
--
-- instance Pretty LexicalPhrase where
--    pretty components = hsep (prettyComponent <$> components)
--       where
--          prettyComponent = \case
--             Nothing -> "_"
--             Just tok -> pretty tok



-- | Split data by grammatical number (singular/plural).
-- The 'Eq' and 'Ord' instances only consider the singular
-- form so that we can prefer known irregular plurals over
-- guessed irregular plurals when inserting items into
-- the 'Lexicon'.
data SgPl a
    = SgPl {sg :: a, pl :: a}
    deriving (Show, Functor, Generic, Hashable, NFData)

instance Eq a => Eq (SgPl a) where (==) = (==) `on` sg
instance Ord a => Ord (SgPl a) where compare = compare `on` sg


data LexicalPhraseSpecError
    = InvalidLexicalPhraseSpec !String
    | AmbiguousLexicalPhraseSpec !String
    deriving (Show, Eq)

lexicalPhrase :: NonEmpty (Maybe Text) -> LexicalPhrase
lexicalPhrase = fmap (fmap Word) . toList

lexicalPhraseSgPl
    :: NonEmpty (Maybe Text, Maybe Text)
    -> SgPl LexicalPhrase
lexicalPhraseSgPl components =
    SgPl
        (fmap (fmap Word) singular)
        (fmap (fmap Word) plural)
  where
    (singular, plural) = unzip (toList components)

readLexicalPhrase :: String -> Either LexicalPhraseSpecError LexicalPhrase
readLexicalPhrase source =
    selectUnique source (List.filter hasWord parses)
  where
    parses = fst (fullParses (parser lexicalPhraseSpec) source)

readLexicalPhraseSgPl
    :: String
    -> Either LexicalPhraseSpecError (SgPl LexicalPhrase)
readLexicalPhraseSgPl source =
    selectUnique source
        [ phrase
        | phrase <- fst (fullParses (parser lexicalPhraseSpecSgPl) source)
        , hasWord (sg phrase)
        , hasWord (pl phrase)
        ]

selectUnique
    :: String
    -> [value]
    -> Either LexicalPhraseSpecError value
selectUnique source = \case
    [value] -> Right value
    [] -> Left (InvalidLexicalPhraseSpec source)
    _ -> Left (AmbiguousLexicalPhraseSpec source)

hasWord :: LexicalPhrase -> Bool
hasWord = any isJust


lexicalPhraseSpec :: Grammar r (Prod r String Char LexicalPhrase)
lexicalPhraseSpec = do
    hole     <- rule $ Nothing <$ token '?' <?> "hole"
    word     <- rule $ Just <$> Applicative.some (satisfy (\c -> isAlpha c || c == '-'))
    space    <- rule $ Just . (:[]) <$> token ' '
    segment  <- rule $ hole <|> word
    rule $ (\s ss -> makePhrase (s:ss)) <$> segment <*> many (space *> segment)
    where
        makePhrase :: [Maybe String] -> LexicalPhrase
        makePhrase pat = fmap makeWord pat


lexicalPhraseSpecSgPl :: Grammar r (Prod r String Char (SgPl LexicalPhrase))
lexicalPhraseSpecSgPl = do
    space <- rule $ Just . (:[]) <$> token ' '
    hole  <- rule $ (Nothing, Nothing) <$ token '?'<?> "hole"

    word <- rule (Applicative.some (satisfy isAlpha) <?> "word")
    inflection <- rule (many (satisfy isAlpha) <?> "inflection")
    wordSgPl <- rule $ (,) <$> (token '[' *> inflection) <* token '/' <*> inflection <* token ']'
    complexWord <- rule $ (\(a,b) -> (Just a, Just b)) . fuse <$>
        Applicative.some ((<>) <$> (dup <$> word) <*> wordSgPl) <?> "word"
    segment  <- rule (hole <|> (dup . Just <$> word) <|> complexWord )
    rule $ (\s ss -> makePhrase (s:ss)) <$> segment <*> many (space *> segment)
    where
        dup x = (x,x)
        fuse =
            List.foldl'
                (\(leftSg, leftPl) (rightSg, rightPl) ->
                    (leftSg <> rightSg, leftPl <> rightPl))
                (mempty, mempty)

        makePhrase :: [(Maybe String, Maybe String)] -> SgPl LexicalPhrase
        makePhrase = (\(patSg, patPl) -> SgPl (fmap makeWord patSg) (fmap makeWord patPl)) . unzip

makeWord :: Maybe String -> Maybe Token
makeWord = fmap (Word . Text.pack)
