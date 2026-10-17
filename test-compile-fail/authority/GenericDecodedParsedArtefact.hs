module GenericDecodedParsedArtefact where

import Felix.Parsed.Payload (DecodedParsedArtefact)
import GHC.Generics (Generic(..))

reconstruct :: Rep DecodedParsedArtefact () -> DecodedParsedArtefact
reconstruct = to
