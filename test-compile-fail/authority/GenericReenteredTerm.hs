module GenericReenteredTerm where

import Felix.Checking.Identity (ReenteredCanonicalTerm)
import GHC.Generics (Generic(..))

reconstruct :: Rep (ReenteredCanonicalTerm) () -> ReenteredCanonicalTerm
reconstruct = to
