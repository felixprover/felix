module GenericCacheDigest where

import Felix.Cache.Codec (CacheDigest)
import GHC.Generics (Generic(..))

reconstruct :: Rep (CacheDigest) () -> CacheDigest
reconstruct = to
