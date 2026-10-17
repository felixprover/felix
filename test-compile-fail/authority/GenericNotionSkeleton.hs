module GenericNotionSkeleton where

import Felix.Checking.Semantic (CheckedNotionRuleSkeleton)
import GHC.Generics (Generic(..))

reconstruct :: Rep (CheckedNotionRuleSkeleton) () -> CheckedNotionRuleSkeleton
reconstruct = to
