module GenericCanonicalPath where

import Felix.Source (CanonicalPath)
import GHC.Generics (Generic(..))

reconstruct :: Rep CanonicalPath () -> CanonicalPath
reconstruct = to
