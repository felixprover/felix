module GenericIdentifiedLoadedSource where

import Felix.Source.Content (IdentifiedLoadedSource)
import GHC.Generics (Generic(..))

reconstruct :: Rep IdentifiedLoadedSource () -> IdentifiedLoadedSource
reconstruct = to
