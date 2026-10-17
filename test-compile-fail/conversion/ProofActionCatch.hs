{-# LANGUAGE ScopedTypeVariables #-}

module ProofActionCatch where

import qualified Control.Monad.Except as Except
import Felix.Checking.Core (CountedCoreFailure)
import Felix.Checking.Kernel.Proof (CountedProof, KernelProofBuildError)

recover :: CountedProof global () -> CountedProof global ()
recover action = Except.catchError action
    (\(_ :: CountedCoreFailure KernelProofBuildError) -> pure ())
