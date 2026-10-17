module GenericResolvedSourceAddress where

import Felix.Source (ResolvedSourceAddress)
import GHC.Generics (Generic(..))

reconstruct :: Rep ResolvedSourceAddress () -> ResolvedSourceAddress
reconstruct = to
