module Main where

import Base
import qualified Felix.Store as Store
import qualified System.IO as IO
import qualified System.Environment as Environment
import Felix.Test.All
import Felix.Test.Unit.Provers (runClosedDescriptorsHelper)

main :: IO ()
main = do
    proverHelper <- Environment.lookupEnv "FELIX_TEST_CLOSED_PROVER_PIPES"
    case proverHelper of
        Just path -> runClosedDescriptorsHelper path
        Nothing -> runNormalTests

runNormalTests :: IO ()
runNormalTests = do
    helperPath <- Environment.lookupEnv "FELIX_TEST_STORE_LEASE_HELPER"
    case helperPath of
        Nothing ->
            runTests
        Just path ->
            runStoreLeaseHelper path

runStoreLeaseHelper :: FilePath -> IO ()
runStoreLeaseHelper path = do
    planned <- Store.planStore (Store.ExplicitStore path)
    plan <- either (fail . show) pure planned
    leased <- Store.withStoreLease plan \_lease -> do
        IO.putStrLn "ready"
        IO.hFlush IO.stdout
        _ <- IO.getLine
        pure ()
    either (fail . show) pure leased
