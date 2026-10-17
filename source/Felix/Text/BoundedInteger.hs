{-# LANGUAGE BangPatterns #-}

-- | Integral input with checked narrowing and bounded intermediate arithmetic.
module Felix.Text.BoundedInteger (readBoundedIntegral) where

import Base
import Data.Char (isSpace, ord)

-- | Preserve integral Read syntax (whitespace, parentheses, decimal, octal,
-- hexadecimal, and an optional minus sign). Accumulate exactly in Integer,
-- checking the magnitude before narrowing. After overflow, consume the remaining
-- digits without further arithmetic or constructing a gigantic Integer.
readBoundedIntegral
    :: forall value. (Integral value, Bounded value)
    => String
    -> Maybe value
readBoundedIntegral source = do
    let (depth, body) = opening 0 source
        (negative, number) = case body of
            '-' : rest -> (True, dropWhile isSpace rest)
            _ -> (False, body)
        lower = toInteger (minBound :: value)
        upper = toInteger (maxBound :: value)
        limit = if negative then negate lower else upper
        (radix, digits) = case number of
            '0' : 'x' : rest -> (16, rest)
            '0' : 'X' : rest -> (16, rest)
            '0' : 'o' : rest -> (8, rest)
            '0' : 'O' : rest -> (8, rest)
            _ -> (10, number)
    (magnitude, rest) <- scanDigits radix limit digits
    guard (closing depth rest)
    let exact = if negative then negate magnitude else magnitude
    guard (exact >= lower && exact <= upper)
    pure (fromInteger exact)
  where
    opening :: Int -> String -> (Int, String)
    opening !depth text = case dropWhile isSpace text of
        '(' : rest -> opening (depth + 1) rest
        rest -> (depth, rest)

    closing :: Int -> String -> Bool
    closing !depth text = case dropWhile isSpace text of
        [] -> depth == 0
        ')' : rest | depth > 0 -> closing (depth - 1) rest
        _ -> False

scanDigits :: Integer -> Integer -> String -> Maybe (Integer, String)
scanDigits radix limit source = do
    (digit, rest) <- nextDigit source
    go (bounded digit) rest
  where
    bounded value = if value <= limit then Just value else Nothing
    nextDigit (character : rest) = do
        digit <- digitValue character
        guard (digit < radix)
        pure (digit, rest)
    nextDigit [] = Nothing

    go !accumulated text = case nextDigit text of
        Nothing -> (\value -> (value, text)) <$> accumulated
        Just (digit, rest) ->
            go (accumulated >>= \value -> bounded (value * radix + digit)) rest

digitValue :: Char -> Maybe Integer
digitValue character
    | character >= '0' && character <= '9' = offset '0' 0
    | character >= 'a' && character <= 'f' = offset 'a' 10
    | character >= 'A' && character <= 'F' = offset 'A' 10
    | otherwise = Nothing
  where
    offset start base = Just (toInteger (ord character - ord start) + base)
