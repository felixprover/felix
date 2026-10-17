{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of immutable global typing snapshots.  The public
-- module exposes point lookup and the unique empty-universe value;
-- 'Felix.Checking.Identity' is the sole inhabited production constructor
-- owner, and builds snapshots from validated object closures.  Keeping the
-- representation as a function makes that projection O(1) and retains the
-- closure map only for the snapshot's ordinary lexical lifetime.
module Felix.Checking.GlobalTyping.Internal
    ( GlobalTyping(..)
    , lookupGlobalType
    ) where

import Base
import Felix.Checking.Core.Representation.Internal (CoreType)


type role GlobalTyping nominal
newtype GlobalTyping global = GlobalTyping
    (global -> Maybe CoreType)

lookupGlobalType
    :: GlobalTyping global
    -> global
    -> Maybe CoreType
lookupGlobalType (GlobalTyping lookupType) =
    lookupType
