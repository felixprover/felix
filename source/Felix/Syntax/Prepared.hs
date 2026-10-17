{-# LANGUAGE DeriveAnyClass #-}

-- | Finite parsing data shared by one module or native-math parser lifetime.
-- Canonical syntax validation and persistent identities remain upstream.
module Felix.Syntax.Prepared
    ( PreparedLexicon
    , prepareLexicon
    , forcePreparedLexicon
    , preparedInventory
    , preparedConstants
    , TokenIndex
    , singletonTokens
    , repeatedTokens
    ) where

import Base
import Control.DeepSeq (NFData, rnf)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Felix.Syntax.Abstract
import Felix.Syntax.Lexicon

-- The ordered inventory still supplies observable token expectations and all
-- unconverted grammar categories. Index payloads share its immutable entries.
-- Keeping the constructor private prevents mismatched inventories and indexes.
data PreparedLexicon = PreparedLexicon
    { preparedInventory :: !Lexicon
    , preparedConstants :: !(TokenIndex ConcreteType)
    }

data TokenIndex a = TokenIndex
    { singletonTokens :: !(Map Token a)
    , repeatedTokens :: ![(Token, a)]
    } deriving (Generic, NFData)

prepareLexicon :: Lexicon -> PreparedLexicon
prepareLexicon original =
    PreparedLexicon inventory
        (indexTokens (lexiconTypedConstants inventory))
  where
    -- Reserved numeric syntax cannot be shadowed by a typed constant. The
    -- same visible inventory drives recognition, diagnostics and exclusion
    -- from the variable category.
    inventory = original
        { lexiconTypedConstants = List.filter
            ((/= Command "opaqueInteger") . fst)
            (lexiconTypedConstants original) }

-- Classification does not deduplicate entries. Equal repeated values still
-- generate separate alternatives in the concrete API.
indexTokens :: [(Token, a)] -> TokenIndex a
indexTokens entries = TokenIndex
    (Map.fromList (List.filter (unique . fst) entries))
    (List.filter (not . unique . fst) entries)
  where
    uniqueness = Map.fromListWith (\_ _ -> False) [(token, True) | (token, _) <- entries]
    unique token = Map.lookup token uniqueness == Just True

-- Force every selected index and its payloads, including repeated-key lists.
-- Unconverted inventories retain their existing demand; preparing an exact
-- token category must not eagerly traverse unrelated phrases or mixfix data.
-- No grammar, mutable Earley state, cache key or encoding lives here.
forcePreparedLexicon :: PreparedLexicon -> ()
forcePreparedLexicon = rnf . preparedConstants
