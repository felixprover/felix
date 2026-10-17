module GenericModuleSyntaxInterface where

import Felix.Syntax.Interface (ModuleSyntaxInterface)
import GHC.Generics (Generic(..))

reconstruct :: Rep ModuleSyntaxInterface () -> ModuleSyntaxInterface
reconstruct = to
