module ProofActionConstructor where

import Felix.Checking.Kernel.Proof (CountedProof(..))

forge :: CountedProof global ()
forge = CountedProof (pure ())
