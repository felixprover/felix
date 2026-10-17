module GenericFrozenCore where

import Felix.Checking.Core (FrozenCheckedCore)
import GHC.Generics (Generic(..))

reconstruct :: Rep (FrozenCheckedCore ()) () -> FrozenCheckedCore ()
reconstruct = to
