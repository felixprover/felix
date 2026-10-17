module GenericStructureApplicationKey where

import Felix.Checking.Structure.Schema (StructureApplicationKey)
import GHC.Generics (Generic(..))

reconstruct :: Rep (StructureApplicationKey) () -> StructureApplicationKey
reconstruct = to
