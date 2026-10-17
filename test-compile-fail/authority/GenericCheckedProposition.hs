module GenericCheckedProposition where

import Felix.Checking.Identity (CheckedPropositionContent)
import GHC.Generics (Generic(..))

reconstruct :: Rep (CheckedPropositionContent) () -> CheckedPropositionContent
reconstruct = to
