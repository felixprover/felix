module GenericSourceMixfixLevel where

import Felix.Syntax.Pragma (SourceMixfixLevel)
import GHC.Generics (Generic(..))

reconstruct :: Rep SourceMixfixLevel () -> SourceMixfixLevel
reconstruct = to
