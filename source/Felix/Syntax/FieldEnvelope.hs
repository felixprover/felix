{-# LANGUAGE NoImplicitPrelude #-}

-- | The lexicon-independent boundary of a structure-field declaration. Both
-- lexical extraction and the concrete grammar use this recognizer. Expressions
-- in the retained slices are interpreted only after the lexicon is complete.
module Felix.Syntax.FieldEnvelope
    ( FieldEnvelope(..)
    , FieldEnvelopeError(..)
    , recognizeFieldEnvelope
    , structureFieldEnvelopes
    , fieldItemToken
    ) where

import Base
import Felix.Report.Location
import Felix.Syntax.Token

import Control.Monad (unless)
import Data.List qualified as List
import Data.Text qualified as Text


data FieldEnvelope = FieldEnvelope
    { fieldEnvelopeCommand :: !(Located Text)
    , fieldEnvelopeLabel :: !(Maybe Text)
    , fieldEnvelopeDescription :: ![Token]
    , fieldEnvelopeOwner :: !(Maybe [Located Token])
    , fieldEnvelopeSpecification :: ![Located Token]
    , fieldEnvelopeTerminator :: !(Located Token)
    } deriving (Show, Eq, Ord)

data FieldEnvelopeError = FieldEnvelopeError !Location !Text
    deriving (Eq, Ord)

instance Show FieldEnvelopeError where
    show (FieldEnvelopeError location message) =
        "invalid structure field at " <> prettyLocation location <> ": " <> Text.unpack message

-- An item cannot extend into the next field or the end of the field list.
fieldItemToken :: Located Token -> Bool
fieldItemToken located = case unLocated located of
    Command "item" -> False
    EndEnv "enumerate" -> False
    _ -> True

recognizeFieldEnvelope
    :: Location
    -> [Located Token]
    -> Either FieldEnvelopeError FieldEnvelope
recognizeFieldEnvelope fallbackLocation tokens = do
    let (marker, afterLabel) = case tokens of
            Located{unLocated = Label value} : rest -> (Just value, rest)
            _ -> (Nothing, tokens)
        (description, afterDescription) = span isWord afterLabel
    afterBegin <- case afterDescription of
        Located{unLocated = BeginEnv "math"} : rest -> Right rest
        _ -> invalid "expected a field command in math after the description"
    (command, afterCommand) <- case afterBegin of
        token@Located{unLocated = Command name} : rest -> Right (name <$ token, rest)
        _ -> invalid "expected the declared field command first in math"
    (owner, afterOwner) <- case afterCommand of
        Located{unLocated = BracketL} : rest -> do
            (body, remaining) <- delimited BracketR rest
            if null body then invalid "the field owner must not be empty"
                else Right (Just body, remaining)
        _ -> Right (Nothing, afterCommand)
    (specification, afterMath) <- delimited (EndEnv "math") afterOwner
    unless (null specification || isJust owner) $
        invalid "a specified field must have an explicit owner"
    terminator <- case afterMath of
        [token@Located{unLocated = Symbol ";"}] -> Right token
        _ -> invalid "expected exactly one semicolon after field math"
    pure FieldEnvelope
        { fieldEnvelopeCommand = command
        , fieldEnvelopeLabel = marker
        , fieldEnvelopeDescription = unLocated <$> description
        , fieldEnvelopeOwner = owner
        , fieldEnvelopeSpecification = specification
        , fieldEnvelopeTerminator = terminator
        }
  where
    location = maybe fallbackLocation startPos (listToMaybe tokens)
    invalid :: Text -> Either FieldEnvelopeError a
    invalid message = Left (FieldEnvelopeError location message)
    isWord token = case unLocated token of
        Word{} -> True
        _ -> False

    -- Balance nested expression delimiters without knowing their bindings.
    -- In particular, math nested inside textual set comprehension is not the
    -- end of the declaration's outer math region.
    delimited closing = go [] []
      where
        go _ _ [] = invalid "unclosed field owner or math delimiter"
        go stack acc (token : rest)
            | unLocated token == closing, null stack = Right (reverse acc, rest)
            | Just end <- matchingClose (unLocated token) =
                go (end : stack) (token : acc) rest
            | isClosing (unLocated token) = case stack of
                end : ends | unLocated token == end -> go ends (token : acc) rest
                _ -> invalid "mismatched delimiter in field owner or specification"
            | otherwise = go stack (token : acc) rest

matchingClose :: Token -> Maybe Token
matchingClose = \case
    ParenL -> Just ParenR
    BracketL -> Just BracketR
    VisibleBraceL -> Just VisibleBraceR
    InvisibleBraceL -> Just InvisibleBraceR
    BeginEnv name -> Just (EndEnv name)
    _ -> Nothing

isClosing :: Token -> Bool
isClosing = \case
    ParenR -> True
    BracketR -> True
    VisibleBraceR -> True
    InvisibleBraceR -> True
    EndEnv{} -> True
    _ -> False

-- | Locate only the equipped-with list, not the subsequent structure laws.
-- The outer structure grammar remains responsible for the declaration header.
structureFieldEnvelopes
    :: [Located Token]
    -> Either FieldEnvelopeError [FieldEnvelope]
structureFieldEnvelopes = findFields
  where
    findFields = \case
        token : Located{unLocated = Word "with"}
                : Located{unLocated = BeginEnv "enumerate"} : rest
            | unLocated token `elem` [Word "equipped", Word "together"] -> fields rest
        _ : rest -> findFields rest
        [] -> Right []

    fields = \case
        Located{unLocated = EndEnv "enumerate"} : _ -> Right []
        item@Located{unLocated = Command "item"} : rest -> do
            let (body, remaining) = List.span fieldItemToken rest
            field <- recognizeFieldEnvelope (startPos item) body
            (field :) <$> fields remaining
        token : _ -> Left (FieldEnvelopeError (startPos token) "expected a field item")
        [] -> Right [] -- the outer grammar rejects an unclosed enumeration
