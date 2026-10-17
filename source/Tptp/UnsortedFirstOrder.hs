{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked lexical building blocks shared by the TPTP renderers.
module Tptp.UnsortedFirstOrder
    ( AtomicWord
    , atomicWord
    , atomicWordText
    , isProperAtomicWord
    , Variable
    , variable
    , variableText
    , isProperVariable
    , buildTuple
    , buildAtomicWord
    , buildVariable
    ) where

import Base
import Felix.Text.Identifier (isPortableIdentifierSubsequent)

import Data.Char (isAsciiLower, isAsciiUpper)
import Data.Text qualified as Text
import TextBuilder


-- | A TPTP atomic word starting with a lowercase ASCII letter.
newtype AtomicWord = AtomicWord Text deriving (Show, Eq, Ord)

atomicWord :: Text -> Maybe AtomicWord
atomicWord word
    | isProperAtomicWord word =
        Just (AtomicWord word)
    | otherwise =
        Nothing

atomicWordText :: AtomicWord -> Text
atomicWordText (AtomicWord word) = word

isProperAtomicWord :: Text -> Bool
isProperAtomicWord w = case Text.uncons w of
    Nothing -> False
    Just (head, tail) ->
        isAsciiLower head
            && Text.all isPortableIdentifierSubsequent tail

-- | A TPTP variable, written as a word starting with an uppercase letter.
newtype Variable = Variable Text deriving (Show, Eq, Ord)

variable :: Text -> Maybe Variable
variable name
    | isProperVariable name =
        Just (Variable name)
    | otherwise =
        Nothing

variableText :: Variable -> Text
variableText (Variable name) = name

isProperVariable :: Text -> Bool
isProperVariable name = case Text.uncons name of
    Nothing -> False
    Just (head, tail) ->
        isAsciiUpper head && Text.all isPortableIdentifierSubsequent tail

buildTuple :: [TextBuilder] -> TextBuilder
buildTuple bs = char '(' <> intercalate (char ',') bs <> char ')'

buildAtomicWord :: AtomicWord -> TextBuilder
buildAtomicWord = text . atomicWordText

buildVariable :: Variable -> TextBuilder
buildVariable = text . variableText
