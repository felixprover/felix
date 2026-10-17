module GenericSemanticEnvironment where

import Felix.Checking.Semantic (SemanticEnvironmentDelta)
import GHC.Generics (Generic(..))

reconstruct :: Rep (SemanticEnvironmentDelta) () -> SemanticEnvironmentDelta
reconstruct = to
