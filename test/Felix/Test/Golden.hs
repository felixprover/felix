{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}

module Felix.Test.Golden where


import Base
import Felix.Workspace qualified as Workspace

import Data.Text.Lazy.IO qualified as LazyTextIO
import System.Directory
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden (goldenVsFile, findByExtension)
import Text.Pretty.Simple (pShowNoColor)


goldenTests :: IO TestTree
goldenTests = do
    triples <- gatherTriples
    traverse_ createTripleDirectoryIfMissing triples
    pure $ testGroup "golden tests"
        [ testGroup "parsing"
            [ goldenVsFile
                (takeBaseName input)
                golden
                output
                (writeParsingOutput triple)
            | triple@Triple{..} <- triples
            ]
        ]


-- | A parsing input and its generated and expected output paths.
data Triple = Triple
    { input  :: FilePath
    , output :: FilePath
    , golden :: FilePath
    }
    deriving (Show, Eq)


-- | Gather every maintained example. Focused tokenizer and
-- lexicon-extraction tests own their lower-level contracts; these goldens
-- preserve the complete parse.
gatherTriples :: IO [Triple]
gatherTriples = do
    inputs <- findByExtension [".tex"] "test/examples"
    pure $
        [ Triple{..}
        | input <- inputs
        , let input' =
                "test" </> "golden" </> takeBaseName input </> "parsing"
        , let golden = input' <.> "golden"
        , let output = input' <.> "out"
        ]

createTripleDirectoryIfMissing :: Triple -> IO ()
createTripleDirectoryIfMissing Triple{..} =
    createDirectoryIfMissing True (takeDirectory output)

writeParsingOutput :: Triple -> IO ()
writeParsingOutput Triple{..} = do
    parseResult <- Workspace.parse input
    LazyTextIO.writeFile output (pShowNoColor parseResult)
