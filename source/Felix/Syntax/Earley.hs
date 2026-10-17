{-# LANGUAGE RankNTypes #-}

-- | One private Earley grammar lifetime across independent token chunks.
--
-- This adapter relies on the exposed internals of pinned Earley 0.13.0.1.
-- Grammar productions and token-independent nullable caches survive inputs;
-- charts and initial continuations are fresh. Earley resets rule continuations
-- and argument references at Parsed/Ended and position boundaries. Drain all
-- result actions and continuations before the consumer runs or the next input
-- begins. The consumer must force its selected payload before returning Right.
-- See benchmark/parser/phase2.md for the lifecycle and retention audit.
module Felix.Syntax.Earley (foldParses) where

import Base
import Control.Monad.ST (ST, runST)
import Text.Earley.Grammar (Grammar, Prod(..), runGrammar)
import Text.Earley.Parser.Internal qualified as Earley

-- | The consumer owns selection, validation and errors. A Left stops before
-- the next chunk. No mutable parser or delayed ST action escapes this fold.
foldParses
    :: (forall r. Grammar r (Prod r e t value))
    -> (input -> [t])
    -> (accumulator -> input -> ([value], Earley.Report e [t]) -> Either failure accumulator)
    -> accumulator
    -> [input]
    -> Either failure accumulator
foldParses _ _ _ initial [] = Right initial
foldParses grammar tokens consume initial inputs = runST do
    production <- runGrammar
        (fmap (\r -> NonTerminal r (pure id)) . Earley.mkRule) grammar
    let go accumulator [] = pure (Right accumulator)
        go accumulator (input : rest) = do
            state <- Earley.initialState production
            result <- Earley.parse [state] (Earley.emptyParseEnv (tokens input)) >>= complete
            case consume accumulator input result of
                Left failure -> pure (Left failure)
                Right next -> next `seq` go next rest
    go initial inputs

-- List-specific fullParses traversal in upstream order. Result values may be
-- lazy, but every ST action that produced them has finished before returning.
complete :: Earley.Result s e [t] value -> ST s ([value], Earley.Report e [t])
complete (Earley.Ended report) = pure ([], report)
complete (Earley.Parsed action _ remaining continuation) = do
    values <- if null remaining then action else pure []
    (later, report) <- continuation >>= complete
    pure (values <> later, report)
