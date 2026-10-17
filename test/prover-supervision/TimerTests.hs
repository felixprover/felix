module TimerTests (timerTests) where

import Prelude

import Control.Concurrent.STM (atomically, orElse)
import Control.Exception (bracket)
import Felix.Provers.Timer qualified as Timer
import System.Timeout qualified as Timeout
import Test.Tasty
import Test.Tasty.HUnit

timerTests :: TestTree
timerTests = testGroup "owned timer registrations"
    [ testCase "publishes expiry" $
        withTimer 1000 \timer ->
            Timeout.timeout 1000000 (atomically (Timer.awaitTimer timer))
                >>= (@?= Just ())
    , testCase "stops a long deadline synchronously and idempotently" $
        withTimer 60000000 \timer -> do
            Timeout.timeout 1000000 (Timer.stopTimer timer) >>= (@?= Just ())
            Timer.stopTimer timer
            hasExpired timer >>= (@?= False)
    , testCase "disarms an already expired timer" $
        withTimer 0 \timer -> do
            hasExpired timer >>= (@?= True)
            Timer.stopTimer timer
            hasExpired timer >>= (@?= False)
    , testCase "cancelled timers cannot publish later expiry" $
        withTimer 1000 \timer -> do
            Timer.stopTimer timer
            -- Await a later real timer, so checking the cancelled cell does
            -- not depend on whether its old callback was merely delayed.
            withTimer 20000 \later ->
                Timeout.timeout 1000000 (atomically (Timer.awaitTimer later))
                    >>= (@?= Just ())
            hasExpired timer >>= (@?= False)
    ]
  where
    withTimer microseconds = bracket (Timer.startTimer microseconds) Timer.stopTimer
    hasExpired timer = atomically $
        (Timer.awaitTimer timer >> pure True) `orElse` pure False
