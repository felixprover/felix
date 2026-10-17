module GenericMixfixLevel where

import Felix.Syntax.Interface (MixfixLevel)
import GHC.Generics (Generic(..))

reconstruct :: Rep MixfixLevel () -> MixfixLevel
reconstruct = to
