module GenericIdentifiedParsedModule where

import Felix.Parsed.Module (IdentifiedParsedModule)
import GHC.Generics (Generic(..))

reconstruct :: Rep IdentifiedParsedModule () -> IdentifiedParsedModule
reconstruct = to
