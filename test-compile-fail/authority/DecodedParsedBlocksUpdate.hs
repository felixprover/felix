module DecodedParsedBlocksUpdate where

import Felix.Parsed.Payload (DecodedParsedArtefact, decodedParsedBlocks)
import Felix.Syntax.Abstract qualified as Raw

replace :: [Raw.Block] -> DecodedParsedArtefact -> DecodedParsedArtefact
replace supplied original = original { decodedParsedBlocks = supplied }
