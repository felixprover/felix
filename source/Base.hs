{-# LANGUAGE NoImplicitPrelude #-}

-- | A basic prelude intended to reduce the amount of repetitive imports.
-- Mainly consists of re-exports from @base@ modules.
-- Intended to be imported explicitly (but with @NoImplicitPrelude@ enabled)
-- so that it is obvious that this module is used. Commonly used data types
-- or helper functions from outside of @base@ are also included.
--
module Base (module Base, module Export, guard) where

-- Some definitions from @base@ need to be hidden to avoid clashes.
--
import Prelude as Export hiding
    ( Word
    , head, last, init, tail, lines, lookup
    , filter -- Replaced by generalized form from "Data.Filtrable".
    , words, pi, all
    )

import Control.Applicative as Export hiding (some)
import Control.Applicative qualified as Applicative
import Control.Exception as Export (bracketOnError)
import Control.Monad
import Control.Monad.IO.Class as Export
import Data.Containers.ListUtils as Export (nubOrd) -- Faster than `nub`.
import Data.Foldable as Export
import Data.Function as Export (on)
import Data.Functor as Export (void)
import Data.Hashable as Export (Hashable(..))
import Data.HashMap.Strict as Export (HashMap)
import Data.IntMap.Strict as Export (IntMap)
import Data.List.NonEmpty as Export (NonEmpty(..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map as Export (Map)
import Data.Maybe as Export hiding (mapMaybe, catMaybes)  -- Replaced by generalized form from "Data.Filtrable".
import Data.Sequence as Export (Seq(..))
import Data.Set as Export (Set)
import Data.Set qualified as Set
import Data.String as Export (IsString(..))
import Data.Text as Export (Text)
import Data.Traversable as Export
import Data.Void as Export
import Data.Word as Export (Word64)
import GHC.Clock as Export (getMonotonicTimeNSec)
import GHC.Generics as Export (Generic(..), Generic1(..))
import Numeric.Natural qualified as Natural
import Prettyprinter as Export (pretty)
import System.IO as Export
    ( Handle
    , hClose
    , hFlush
    , openBinaryTempFileWithDefaultPermissions
    , openTempFile
    , utf8
    )
import System.IO.Error as Export (isDoesNotExistError, tryIOError)
import UnliftIO as Export (throwIO)

-- | Signal to the developer that a branch is unreachable or represent
-- an impossible state. Using @impossible@ instead of @error@ allows
-- for easily finding leftover @error@s while ignoring impossible branches.
impossible :: String -> a
impossible msg = error ("IMPOSSIBLE: " <> msg)

-- | Convert a ternary curried function to an uncurried function.
uncurry3 :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f ~(a, b, c) = f a b c

-- | Safe list lookup. Replaces @(!!)@. The index type excludes negative
-- values, which previously made this supposedly safe helper diverge.
nth :: Natural.Natural -> [a] -> Maybe a
nth _ [] = Nothing
nth 0 (a : _) = Just a
nth n (_ : as) = nth (n - 1) as

zeroBasedIndex :: Int -> Maybe Natural.Natural
zeroBasedIndex index
    | index < 0 = Nothing
    | otherwise = Just (fromIntegral index)

oneBasedIndex :: Int -> Maybe Natural.Natural
oneBasedIndex ordinal
    | ordinal <= 0 = Nothing
    | otherwise = Just (fromIntegral (ordinal - 1))

-- | The first value whose occurrence is not the first in the list.
firstDuplicate :: Ord value => [value] -> Maybe value
firstDuplicate =
    go Set.empty
  where
    go _seen [] = Nothing
    go seen (value : remaining)
        | value `Set.member` seen = Just value
        | otherwise = go (Set.insert value seen) remaining

-- | Do nothing and return @()@.
skip :: Applicative f => f ()
skip = pure ()

-- | One or more. Equivalent to @some@ from @Control.Applicative@, but
-- keeps the information that the result is @NonEmpty@.
many1 :: Alternative f => f a -> f (NonEmpty a)
many1 parser =
    (:|) <$> parser <*> many parser

-- | Same as 'many1', but discards the type information that the result is @NonEmpty@.
many1_ :: Alternative f => f a -> f [a]
many1_ = Applicative.some

-- | Parse the requested number of occurrences, with one as the minimum.
count1 :: Applicative f => Int -> f a -> f (NonEmpty a)
count1 n fa
    | n <= 1    = (:| []) <$> fa
    | otherwise = NonEmpty.fromList <$> replicateM n fa
