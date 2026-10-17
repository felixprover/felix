module Felix.Test.Unit.BoundedInteger (unitTests) where

import Base
import Felix.Text.BoundedInteger (readBoundedIntegral)
import Data.Int (Int8)
import Numeric (showHex, showOct)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Read (readMaybe)

unitTests :: TestTree
unitTests = testGroup "Bounded integer input"
    [ testCase "agrees with checked Integer Read across spelling and range boundaries" do
        for_ spellings \source ->
            assertEqual source (reference source)
                (readBoundedIntegral source :: Maybe Int8)
    , testCase "checks native widths before narrowing" do
        readBoundedIntegral (show (maxBound :: Int)) @?= Just (maxBound :: Int)
        readBoundedIntegral (show (minBound :: Int)) @?= Just (minBound :: Int)
        readBoundedIntegral (show (toInteger (maxBound :: Int) + 1)) @?= (Nothing :: Maybe Int)
        readBoundedIntegral (show (toInteger (minBound :: Int) - 1)) @?= (Nothing :: Maybe Int)
        readBoundedIntegral (show (maxBound :: Word64)) @?= Just (maxBound :: Word64)
        readBoundedIntegral "18446744073709551616" @?= (Nothing :: Maybe Word64)
        readBoundedIntegral "18446744073709551617" @?= (Nothing :: Maybe Int)
        readBoundedIntegral "18446744073709551617" @?= (Nothing :: Maybe Word64)
        readBoundedIntegral "-1" @?= (Nothing :: Maybe Word64)
        readBoundedIntegral "-0" @?= Just (0 :: Word64)
    , testCase "bounds arithmetic on long input without rejecting leading zeroes" do
        readBoundedIntegral (replicate 1000000 '9') @?= (Nothing :: Maybe Int)
        readBoundedIntegral (replicate 100000 '0' <> "1") @?= Just (1 :: Int)
    ]
  where
    reference source = do
        exact <- readMaybe source :: Maybe Integer
        guard (exact >= -128 && exact <= 127)
        pure (fromInteger exact :: Int8)
    numbers =
        [show number | number <- [-300 .. 300 :: Integer]]
        <> ["0x" <> showHex number "" | number <- [0 .. 300 :: Integer]]
        <> ["0o" <> showOct number "" | number <- [0 .. 300 :: Integer]]
        <> ["0", "00", "0x", "0o8", "0xg", "1.0", "1e0", "+1",
            "- 1", "- (1)", "--1", "1--x", "0b1", "１２"]
    spellings = concatMap
        (\source -> [source, "(" <> source <> ")", " ((" <> source <> ")) ",
            "\t" <> source <> "\n", source <> "x", "(" <> source, source <> ")"])
        numbers
