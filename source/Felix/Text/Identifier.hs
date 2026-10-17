{-# LANGUAGE NoImplicitPrelude #-}

-- | The portable identifier alphabet shared by Felix source markers and
-- unquoted TPTP names.
module Felix.Text.Identifier
    ( isPortableIdentifierInitial
    , isPortableIdentifierSubsequent
    ) where

import Base

import Data.Char (isAsciiLower, isAsciiUpper, isDigit)


-- Felix markers deliberately use the common denominator accepted by both
-- LaTeX-facing source notation and unquoted TPTP identifiers. Keeping this
-- policy shared makes the source-marker-to-TPTP-name mapping transparent when
-- debugging exported proof tasks. TPTP-specific initial-case rules remain in
-- the TPTP renderer.
isPortableIdentifierInitial :: Char -> Bool
isPortableIdentifierInitial character =
    isAsciiLower character || isAsciiUpper character

isPortableIdentifierSubsequent :: Char -> Bool
isPortableIdentifierSubsequent character =
    isPortableIdentifierInitial character
        || isDigit character
        || character == '_'
