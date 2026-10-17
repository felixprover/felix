module GenericStoredProposition where

import Felix.Checking.Identity (StoredPropositionCandidate)
import GHC.Generics (Generic(..))

reconstruct :: Rep (StoredPropositionCandidate) () -> StoredPropositionCandidate
reconstruct = to
