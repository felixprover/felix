{-# LANGUAGE NoImplicitPrelude #-}

-- | The two controlled-language surfaces of a finite verb.
--
-- The constructor is deliberately private.  A value records that both
-- surfaces begin with a nonempty word and differ, if at all, only in that
-- leading word.
module Felix.Syntax.VerbSurface
    ( VerbSurfaces
    , verbSurfaceSingular
    , verbSurfaceBase
    , VerbSurfaceRole(..)
    , VerbSurfaceError(..)
    , deriveVerbSurfaces
    , checkVerbSurfaces
    ) where

import Base
import Felix.Syntax.LexicalPhrase (LexicalPhrase)
import Felix.Syntax.Token (Token(..))

import Control.DeepSeq (NFData(..))
import Data.Text qualified as Text


data VerbSurfaces = VerbSurfaces !LexicalPhrase !LexicalPhrase

instance Show VerbSurfaces where
    showsPrec precedence (VerbSurfaces singular base) =
        showParen (precedence > 10)
            ( showString "VerbSurfaces "
                . showsPrec 11 singular
                . showChar ' '
                . showsPrec 11 base
            )

instance Eq VerbSurfaces where
    VerbSurfaces singular base == VerbSurfaces singular' base' =
        singular == singular' && base == base'

instance Ord VerbSurfaces where
    compare (VerbSurfaces singular base) (VerbSurfaces singular' base') =
        compare (singular, base) (singular', base')

instance Hashable VerbSurfaces where
    hashWithSalt salt (VerbSurfaces singular base) =
        hashWithSalt salt (singular, base)

instance NFData VerbSurfaces where
    rnf (VerbSurfaces singular base) = rnf singular `seq` rnf base

verbSurfaceSingular :: VerbSurfaces -> LexicalPhrase
verbSurfaceSingular (VerbSurfaces singular _base) = singular

verbSurfaceBase :: VerbSurfaces -> LexicalPhrase
verbSurfaceBase (VerbSurfaces _singular base) = base

data VerbSurfaceRole
    = SingularVerbSurface
    | BaseVerbSurface
    deriving (Show, Eq)

data VerbSurfaceError
    = EmptyVerbSurface !VerbSurfaceRole
    | LeadingVerbSurfaceHole !VerbSurfaceRole
    | LeadingVerbSurfaceTokenNotWord !VerbSurfaceRole !Token
    | EmptyLeadingVerbSurfaceWord !VerbSurfaceRole
    | VerbSurfaceTailMismatch
    deriving (Show, Eq)

deriveVerbSurfaces
    :: Maybe Text
    -> LexicalPhrase
    -> Either VerbSurfaceError VerbSurfaces
deriveVerbSurfaces explicitBase singular = do
    singularWord <- leadingWord SingularVerbSurface singular
    let baseWord = fromMaybe (inferBaseWord singularWord) explicitBase
        base = Just (Word baseWord) : drop 1 singular
    checkVerbSurfaces singular base

checkVerbSurfaces
    :: LexicalPhrase
    -> LexicalPhrase
    -> Either VerbSurfaceError VerbSurfaces
checkVerbSurfaces singular base = do
    _ <- leadingWord SingularVerbSurface singular
    _ <- leadingWord BaseVerbSurface base
    if drop 1 singular == drop 1 base
        then Right (VerbSurfaces singular base)
        else Left VerbSurfaceTailMismatch

leadingWord
    :: VerbSurfaceRole
    -> LexicalPhrase
    -> Either VerbSurfaceError Text
leadingWord role = \case
    [] ->
        Left (EmptyVerbSurface role)
    Nothing : _ ->
        Left (LeadingVerbSurfaceHole role)
    Just (Word word) : _
        | Text.null word ->
            Left (EmptyLeadingVerbSurfaceWord role)
        | otherwise ->
            Right word
    Just token : _ ->
        Left (LeadingVerbSurfaceTokenNotWord role token)

inferBaseWord :: Text -> Text
inferBaseWord "has" = "have"
inferBaseWord word
    | Just stem <- Text.stripSuffix "ies" word
    , Just (_prefix, character) <- Text.unsnoc stem
    , character `elem` asciiConsonants =
        stem <> "y"
    | any (`Text.isSuffixOf` word) esSuffixes =
        Text.dropEnd 2 word
    | Text.isSuffixOf "s" word =
        Text.dropEnd 1 word
    | otherwise =
        word

asciiConsonants :: String
asciiConsonants = "bcdfghjklmnpqrstvwxyz"

esSuffixes :: [Text]
esSuffixes = ["sses", "shes", "ches", "xes", "zes", "oes"]
