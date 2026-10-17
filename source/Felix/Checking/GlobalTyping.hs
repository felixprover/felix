{-# LANGUAGE NoImplicitPrelude #-}

-- | Immutable owner-created views of global types.
module Felix.Checking.GlobalTyping
    ( GlobalTyping
    , lookupGlobalType
    , emptyGlobalTyping
    ) where

import Base
import Felix.Checking.GlobalTyping.Internal
    ( GlobalTyping(..)
    , lookupGlobalType
    )


-- | The unique global typing snapshot for a universe with no inhabitants.
emptyGlobalTyping :: GlobalTyping Void
emptyGlobalTyping =
    GlobalTyping absurd
