module Main where

import Base
import Felix.Test.Unit.Provers (unitTests, runClosedDescriptorsHelper)
import System.Environment (lookupEnv)
import Test.Tasty (defaultMain, testGroup)
import TimerTests (timerTests)

main :: IO ()
main = do
    helper <- lookupEnv "FELIX_TEST_CLOSED_PROVER_PIPES"
    case helper of
        Just path -> runClosedDescriptorsHelper path
        Nothing -> defaultMain (testGroup "prover supervision" [unitTests, timerTests])
