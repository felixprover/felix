module ProofCoercion where

import Data.Coerce (coerce)
import Felix.Checking.Kernel.Derivation
    ( DerivationImportJudgement
    , KernelDerivation
    , ReplayedKernelDerivation
    , ReplayedScopedKernelDerivation
    )
import Felix.Checking.Kernel.Proof (BuiltProof, ProofContext)

newtype UniverseA = UniverseA Int
newtype UniverseB = UniverseB Int

badContext :: ProofContext UniverseA -> ProofContext UniverseB
badContext = coerce

badProof :: BuiltProof UniverseA -> BuiltProof UniverseB
badProof = coerce

badImport
    :: DerivationImportJudgement UniverseA
    -> DerivationImportJudgement UniverseB
badImport = coerce

badDerivation :: KernelDerivation UniverseA -> KernelDerivation UniverseB
badDerivation = coerce

badReplay
    :: ReplayedKernelDerivation UniverseA
    -> ReplayedKernelDerivation UniverseB
badReplay = coerce

badScopedReplay
    :: ReplayedScopedKernelDerivation UniverseA
    -> ReplayedScopedKernelDerivation UniverseB
badScopedReplay = coerce
