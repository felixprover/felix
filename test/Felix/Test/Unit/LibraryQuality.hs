{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.LibraryQuality (unitTests) where

import Base
import Felix.Report.Location (anonymousSourceDescriptor)
import Felix.Source
    ( importPath
    , importRef
    , safeRelativePathFilePath
    )
import Felix.Syntax.Token (Located(..))
import Felix.Test.SourceScan.Adapter (scanTestImports)

import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.IO qualified as TextIO
import System.Directory qualified as Directory
import System.FilePath qualified as FilePath
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests =
    testGroup
        "Library quality"
        [ testCase
            "contains no source axioms or explicit proof gaps"
            libraryHasNoSourceEscapes
        , testCase
            "covers every maintained library source"
            aggregateCoversLibrary
        , testCase
            "uses unique labels across the library aggregate"
            aggregateLabelsAreUnique
        ]

libraryHasNoSourceEscapes :: Assertion
libraryHasNoSourceEscapes = do
    actual <- sourceEscapesBelow "library"
    assertEqual
        "Library sources must contain no non-comment \\begin{axiom} or Omitted. marker"
        []
        actual

aggregateCoversLibrary :: Assertion
aggregateCoversLibrary = do
    maintained <- effectiveLibraryClosure
    librarySources <-
        Set.fromList . map FilePath.normalise <$> texFilesBelow "library"
    assertEqual
        ("Every library TeX source must be the implicit prelude or "
            <> "reachable from library/everything.tex")
        librarySources
        maintained

everythingRoot :: FilePath
everythingRoot = "library" FilePath.</> "everything.tex"

preludeRoot :: FilePath
preludeRoot = "library" FilePath.</> "prelude.tex"

effectiveLibraryClosure :: IO (Set FilePath)
effectiveLibraryClosure =
    Set.insert preludeRoot <$> importClosure [everythingRoot]

importClosure :: [FilePath] -> IO (Set FilePath)
importClosure = go Set.empty
  where
    go seen [] = pure seen
    go seen (path : pending)
        | path `Set.member` seen = go seen pending
        | otherwise = do
            contents <- TextIO.readFile path
            imports <-
                case scanTestImports anonymousSourceDescriptor path contents of
                    Left err ->
                        assertFailure err >> pure []
                    Right located ->
                        case traverse (productionImportPath path) located of
                            Left message -> assertFailure message >> pure []
                            Right targets -> pure targets
            go (Set.insert path seen) (imports <> pending)

productionImportPath
    :: FilePath
    -> Located FilePath
    -> Either String FilePath
productionImportPath source located =
    case importRef (startPos located) (unLocated located) of
        Left reason ->
            Left
                ( "Invalid import in "
                    <> source
                    <> ": "
                    <> show reason
                )
        Right reference ->
            Right
                (FilePath.normalise
                    ("library" FilePath.</>
                        safeRelativePathFilePath (importPath reference)))

sourceEscapesBelow :: FilePath -> IO [String]
sourceEscapesBelow root = do
    files <- texFilesBelow root
    fmap concat $ for (List.sort files) \file -> do
        contents <- TextIO.readFile file
        pure (sourceEscapes file contents)

texFilesBelow :: FilePath -> IO [FilePath]
texFilesBelow directory = do
    entries <- List.sort <$> Directory.listDirectory directory
    fmap concat $ for entries \entry -> do
        let path = directory FilePath.</> entry
        isDirectory <- Directory.doesDirectoryExist path
        if isDirectory
            then texFilesBelow path
            else pure [path | FilePath.takeExtension path == ".tex"]

sourceEscapes :: FilePath -> Text -> [String]
sourceEscapes path contents =
    [ path <> ":" <> show lineNumber <> ": " <> description
    | (lineNumber, sourceLine) <- zip [1 :: Int ..] (Text.lines contents)
    , let code = fst (Text.breakOn "%" sourceLine)
    , (description, marker) <-
        [ ("source axiom", "\\begin{axiom}")
        , ("explicit proof gap", "Omitted.")
        ]
    , marker `Text.isInfixOf` code
    ]

labels :: Text -> [Text]
labels source =
    case Text.breakOn "\\label{" source of
        (_, suffix)
            | Text.null suffix -> []
            | otherwise ->
                let afterOpen = Text.drop (Text.length "\\label{") suffix
                    (label, afterLabel) = Text.breakOn "}" afterOpen
                 in if Text.null afterLabel
                        then []
                        else label : labels (Text.drop 1 afterLabel)

aggregateSources :: IO [FilePath]
aggregateSources = Set.toList <$> effectiveLibraryClosure

sourceLabels :: FilePath -> Text -> [(Text, String)]
sourceLabels path contents =
    [ (label, path <> ":" <> show lineNumber)
    | (lineNumber, sourceLine) <- zip [1 :: Int ..] (Text.lines contents)
    , label <- labels (fst (Text.breakOn "%" sourceLine))
    ]

aggregateLabelsAreUnique :: Assertion
aggregateLabelsAreUnique = do
    sources <- aggregateSources
    occurrences <- fmap concat $ for sources \path -> do
        contents <- TextIO.readFile path
        pure (sourceLabels path contents)
    let locations =
            Map.fromListWith
                (<>)
                [(label, [location]) | (label, location) <- occurrences]
        duplicates =
            [ Text.unpack label <> ": " <> List.intercalate ", " places
            | (label, places) <- Map.toAscList locations
            , length places > 1
            ]
    assertEqual
        "Maintained mathematical labels must be globally unique"
        []
        duplicates
