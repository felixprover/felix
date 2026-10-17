module CheckedEvidenceProducers where

import Data.Void (Void)
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (emptyGlobalTyping)

checkedTruth :: Either CoreCheckError (FrozenCheckedCore Void)
checkedTruth = checkCanonicalCore emptyGlobalTyping CTruth
