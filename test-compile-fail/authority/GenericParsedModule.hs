module GenericParsedModule where

import Felix.Parsed.Module (ParsedModule)
import GHC.Generics (Generic(..))

reconstruct :: Rep ParsedModule () -> ParsedModule
reconstruct = to
