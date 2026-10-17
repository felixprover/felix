module GenericScopedCore where

import Felix.Checking.Core (ScopedCheckedCore)
import GHC.Generics (Generic(..))

reconstruct :: Rep (ScopedCheckedCore ()) () -> ScopedCheckedCore ()
reconstruct = to
