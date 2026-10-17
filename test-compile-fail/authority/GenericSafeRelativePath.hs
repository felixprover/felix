module GenericSafeRelativePath where

import Felix.Source (SafeRelativePath)
import GHC.Generics (Generic(..))

reconstruct :: Rep SafeRelativePath () -> SafeRelativePath
reconstruct = to
