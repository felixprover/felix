module GenericLocation where

import Felix.Report.Location (Location)
import GHC.Generics (Generic(..))

reconstruct :: Rep (Location) () -> Location
reconstruct = to
