module ProofActionState where

import qualified Control.Monad.State.Strict as State
import Felix.Checking.Kernel.Proof (CountedProof)

resetCredit :: CountedProof global ()
resetCredit = State.get >>= State.put
