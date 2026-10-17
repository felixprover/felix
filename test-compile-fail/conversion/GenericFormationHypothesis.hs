module GenericFormationHypothesis where

import Felix.Checking.Notion (MaterializedNotionHypothesis)
import GHC.Generics (Generic(..))

reconstruct :: Rep (MaterializedNotionHypothesis ()) () -> MaterializedNotionHypothesis ()
reconstruct = to
