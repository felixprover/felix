module GenericLoadedSource where

import Felix.Source (LoadedSource)
import GHC.Generics (Generic(..))

reconstruct :: Rep LoadedSource () -> LoadedSource
reconstruct = to
