{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Complete lexical identities for symbolic phrases in presentation prose.
module Felix.Syntax.Phrase
    ( NativePhraseBinding
    , nativePhraseBinding
    , nativePhraseEntry
    , nativePhraseMarker
    , nativePhraseCommands
    , adjectivePhraseEntry
    , numberedPhraseEntry
    ) where

import Base
import Felix.Syntax.Abstract
import Felix.Syntax.Interface (CanonicalLexicalEntry(..))
import Data.Maybe (mapMaybe)

newtype NativePhraseBinding = NativePhraseBinding CanonicalLexicalEntry
    deriving stock (Show, Eq, Ord)

nativePhraseBinding :: CanonicalLexicalEntry -> Maybe NativePhraseBinding
nativePhraseBinding entry = do
    (_, patterns) <- phraseDetails entry
    guard (any (isJust . command) patterns)
    pure (NativePhraseBinding entry)

nativePhraseEntry :: NativePhraseBinding -> CanonicalLexicalEntry
nativePhraseEntry (NativePhraseBinding entry) = entry

nativePhraseMarker :: NativePhraseBinding -> Maybe Marker
nativePhraseMarker (NativePhraseBinding entry) =
    maybe (impossible "a native phrase lost its lexical identity") fst (phraseDetails entry)

nativePhraseCommands :: NativePhraseBinding -> [Text]
nativePhraseCommands (NativePhraseBinding entry) =
    maybe (impossible "a native phrase lost its lexical identity")
        (mapMaybe command . snd) (phraseDetails entry)

phraseDetails :: CanonicalLexicalEntry -> Maybe (Maybe Marker, [Pattern])
phraseDetails = \case
    CanonicalUserAdjective _ (AdjectiveSurfaceKey pattern') -> Just (Nothing, [pattern'])
    CanonicalIntrinsicAdjective _ pattern' marker -> Just (Just marker, [pattern'])
    CanonicalNoun singular plural marker -> Just (Just marker, [singular, plural])
    CanonicalStructureNoun singular plural marker -> Just (Just marker, [singular, plural])
    CanonicalFunctionPhrase singular plural marker -> Just (Just marker, [singular, plural])
    CanonicalVerb surfaces marker -> Just (Just marker,
        patternFromHoley <$> [verbSurfaceSingular surfaces, verbSurfaceBase surfaces])
    _ -> Nothing

command :: Pattern -> Maybe Text
command = \case
    TokenCons (Command name) End -> Just name
    _ -> Nothing

-- Keep the grammatical role at callers where a shared numbered lexical item
-- alone cannot distinguish a noun, function phrase, or structure phrase.
numberedPhraseEntry
    :: (Pattern -> Pattern -> Marker -> CanonicalLexicalEntry)
    -> LexicalItemSgPl -> CanonicalLexicalEntry
numberedPhraseEntry constructor item =
    let forms = lexicalItemSgPlPattern item
    in constructor (sg forms) (pl forms) (lexicalItemSgPlMarker item)

adjectivePhraseEntry :: AdjectiveLexicalItem -> CanonicalLexicalEntry
adjectivePhraseEntry item = case adjectiveLexicalIdentity item of
    UserAdjectiveIdentity surface -> CanonicalUserAdjective (adjectiveLexicalSide item) surface
    IntrinsicAdjectiveIdentity pattern' marker ->
        CanonicalIntrinsicAdjective (adjectiveLexicalSide item) pattern' marker
