module GenericCanonicalParsedPayload where

import Felix.Parsed.Payload (CanonicalParsedPayload)
import GHC.Generics (Generic(..))

reconstruct :: Rep CanonicalParsedPayload () -> CanonicalParsedPayload
reconstruct = to
