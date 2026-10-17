module CarrierAndCoreCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core (FrozenCheckedCore, ScopedCheckedCore)
import Felix.Checking.GlobalTyping (GlobalTyping)

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badCarrier :: GlobalTyping UniverseA -> GlobalTyping UniverseB
badCarrier = coerce

badFrozen :: FrozenCheckedCore UniverseA -> FrozenCheckedCore UniverseB
badFrozen = coerce

badScoped :: ScopedCheckedCore UniverseA -> ScopedCheckedCore UniverseB
badScoped = coerce
