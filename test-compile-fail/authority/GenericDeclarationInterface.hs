module GenericDeclarationInterface where

import Felix.Checking.Semantic (DeclarationInterfaceDelta)
import GHC.Generics (Generic(..))

reconstruct :: Rep (DeclarationInterfaceDelta) () -> DeclarationInterfaceDelta
reconstruct = to
