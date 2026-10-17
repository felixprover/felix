module GenericResolvedSource where

import Felix.Source (ResolvedSource)
import GHC.Generics (Generic(..))

reconstruct :: Rep ResolvedSource () -> ResolvedSource
reconstruct = to
