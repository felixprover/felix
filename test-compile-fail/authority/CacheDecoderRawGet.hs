module CacheDecoderRawGet where

import Data.Binary.Get qualified as Binary
import Data.ByteString.Lazy (ByteString)
import Data.Word (Word8)
import Felix.Cache.Codec (getCacheTag)

-- The public parser cannot be run without choosing an admission policy.
unbounded :: ByteString -> Word8
unbounded = Binary.runGet getCacheTag
