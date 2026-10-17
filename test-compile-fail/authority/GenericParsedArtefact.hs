module GenericParsedArtefact where

import Felix.Parsed.Payload (ParsedArtefact)
import GHC.Generics (Generic(..))

reconstruct :: Rep ParsedArtefact () -> ParsedArtefact
reconstruct = to
