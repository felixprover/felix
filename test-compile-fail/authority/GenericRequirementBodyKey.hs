module GenericRequirementBodyKey where

import Felix.Checking.Structure.Schema (RequirementBodyKey)
import GHC.Generics (Generic(..))

reconstruct :: Rep (RequirementBodyKey) () -> RequirementBodyKey
reconstruct = to
