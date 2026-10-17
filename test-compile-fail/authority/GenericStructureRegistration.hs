module GenericStructureRegistration where

import Felix.Checking.Structure.Predicate (PendingStructureRegistration)
import GHC.Generics (Generic(to), Rep)

forge :: Rep PendingStructureRegistration () -> PendingStructureRegistration
forge = to
