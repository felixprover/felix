module GenericGuardedRuleSet where

import Felix.Checking.Authority (GuardedRuleSet)
import GHC.Generics (Generic(..))

reconstruct :: Rep (GuardedRuleSet) () -> GuardedRuleSet
reconstruct = to
