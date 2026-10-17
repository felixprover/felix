module Felix.Test.All where


import Base
import Felix.Test.Golden
import Felix.Test.Unit
import Test.Tasty


runTests :: IO ()
runTests = defaultMain =<< tests

tests :: IO TestTree
tests = do
    goldenTree <- goldenTests
    pure
        (testGroup "all tests"
            [ testGroup "fast" [goldenTree, fastTests]
            , testGroup "acceptance" [acceptanceTests]
            ])
