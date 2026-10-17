module GenericPreparedSpine where

import Felix.Checking.Kernel.Conversion (PreparedSpine)
import GHC.Generics (Generic(..))

reconstruct :: Rep (PreparedSpine ()) () -> PreparedSpine ()
reconstruct = to
