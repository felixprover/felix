module ScopedInstantiationResultCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Core (ScopedInstantiationResult)

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badInstantiation
    :: ScopedInstantiationResult UniverseA
    -> ScopedInstantiationResult UniverseB
badInstantiation = coerce
