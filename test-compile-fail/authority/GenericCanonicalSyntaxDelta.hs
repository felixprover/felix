module GenericCanonicalSyntaxDelta where

import Felix.Syntax.Interface (CanonicalSyntaxDelta)
import GHC.Generics (Generic(..))

reconstruct :: Rep CanonicalSyntaxDelta () -> CanonicalSyntaxDelta
reconstruct = to
