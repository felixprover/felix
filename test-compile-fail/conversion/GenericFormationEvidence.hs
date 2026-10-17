module GenericFormationEvidence where

import Felix.Checking.Notion (MaterializedFormationEvidence)
import GHC.Generics (Generic(..))

reconstruct :: Rep (MaterializedFormationEvidence ()) () -> MaterializedFormationEvidence ()
reconstruct = to
