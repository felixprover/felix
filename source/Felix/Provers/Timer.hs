-- The threaded RTS already owns a timer manager. Register just a completion
-- cell there; cancelling a deadline must not require scheduling another
-- Haskell thread after the prover has finished.
module Felix.Provers.Timer (Timer, startTimer, awaitTimer, stopTimer) where

import Prelude

import Control.Concurrent.STM
    ( STM, TVar, atomically, check, newTVarIO, readTVar, writeTVar )
import Control.Exception qualified as Exception
import Control.Monad (when)
import GHC.Event qualified as Event

data TimerState = Pending | Expired | Stopped
    deriving (Eq)

data Timer = Timer !(TVar TimerState) !Event.TimerManager !Event.TimeoutKey

-- Call only under the threaded RTS, from a masked acquisition. The caller
-- owns stopTimer on every exit path.
startTimer :: Int -> IO Timer
startTimer microseconds = Exception.mask_ do
    state <- newTVarIO Pending
    manager <- Event.getSystemTimerManager
    key <- Event.registerTimeout manager microseconds $ atomically do
        current <- readTVar state
        when (current == Pending) (writeTVar state Expired)
    pure (Timer state manager key)

awaitTimer :: Timer -> STM ()
awaitTimer (Timer state _ _) = readTVar state >>= check . (== Expired)

stopTimer :: Timer -> IO ()
stopTimer (Timer state manager key) = Exception.mask_ do
    -- The manager may already have dequeued the callback. Disarm its cell
    -- before deregistering; that callback owns no request or process state
    -- and cannot publish expiry after this transition.
    atomically (writeTVar state Stopped)
    Event.unregisterTimeout manager key
