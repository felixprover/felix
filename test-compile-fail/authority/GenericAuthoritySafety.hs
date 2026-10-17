module GenericAuthoritySafety where

import Felix.Checking.Authority (AuthoritySafety)
import GHC.Generics (Generic(..))

reconstruct :: Rep (AuthoritySafety) () -> AuthoritySafety
reconstruct = to
