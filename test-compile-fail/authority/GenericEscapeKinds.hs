module GenericEscapeKinds where

import Felix.Checking.Authority (EscapeKinds)
import GHC.Generics (Generic(..))

reconstruct :: Rep (EscapeKinds) () -> EscapeKinds
reconstruct = to
