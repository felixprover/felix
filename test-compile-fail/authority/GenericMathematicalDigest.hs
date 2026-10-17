module GenericMathematicalDigest where

import Felix.Math.Codec (MathematicalDigest)
import GHC.Generics (Generic(..))

reconstruct :: Rep (MathematicalDigest) () -> MathematicalDigest
reconstruct = to
