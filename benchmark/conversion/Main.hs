{-# LANGUAGE NoImplicitPrelude #-}

module Main (main) where

import Base
import Cases
import Runtime
import Scaling (runScaling)
import Workflows (runWorkflowScaling)

import Data.Text qualified as Text
import Data.Text.IO.Utf8 qualified as Text
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (stderr)
import Text.Read (readMaybe)


main :: IO ()
main = do
    arguments <- getArgs
    case arguments of
        ["scaling", family, rawSize, rawRepetitions]
            | Just size <- readMaybe rawSize
            , Just repetitions <- readMaybe rawRepetitions ->
                runScaling family size repetitions
        ["workflow", family, rawSize, rawRepetitions]
            | Just size <- readMaybe rawSize
            , Just repetitions <- readMaybe rawRepetitions ->
                runWorkflowScaling family size repetitions
        _ -> do
            suite <- either failText pure (validateFocusedSuite focusedSuite)
            runFocusedArguments suite arguments

runFocusedArguments :: ValidatedFocusedSuite -> [String] -> IO ()
runFocusedArguments suite arguments =
    case arguments of
        [] -> runFocused suite
        ["fixed"] -> runFocused suite
        ["self-check"] -> do
            either failText pure checkRejectedFocusedSuites
            either failText pure (selfCheckSuite suite)
            writeCommonHeader suite
            Text.putStrLn "self-check ok"
        _ -> do
            Text.hPutStrLn stderr
                "usage: conversion-focused [fixed | self-check | scaling FAMILY SIZE REPETITIONS | workflow FAMILY SIZE REPETITIONS]"
            exitFailure

runFocused :: ValidatedFocusedSuite -> IO ()
runFocused suite = do
    results <- either failText pure (runFocusedSuite suite)
    writeCommonHeader suite
    Text.putStrLn ("c5-limit " <> showText conversionWorkLimit)
    traverse_ Text.putStrLn results

writeCommonHeader :: ValidatedFocusedSuite -> IO ()
writeCommonHeader suite = do
    Text.putStrLn "conversion-focused-source-v2"
    Text.putStrLn ("suite " <> validatedFocusedSuiteName suite)
    Text.putStrLn ("namespace-digest " <> benchmarkNamespaceDigestText)
    Text.putStrLn
        ("case-count " <> showText (validatedFocusedSuiteCaseCount suite))

failText :: Text -> IO value
failText message = do
    Text.hPutStrLn stderr message
    exitFailure

showText :: Show value => value -> Text
showText = Text.pack . show
