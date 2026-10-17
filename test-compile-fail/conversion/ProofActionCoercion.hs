module ProofActionCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Kernel.Proof (CountedProof)

newtype First = First Int
newtype Second = Second Int

changeOwner :: CountedProof First () -> CountedProof Second ()
changeOwner = coerce
