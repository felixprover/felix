{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact validated source-byte identity within the current cache epoch.
module Felix.Source.Content
    ( SourceContentId
    , sourceContentId
    , sourceContentIdBytes
    , sourceContentIdDigest
    , IdentifiedLoadedSource
    , identifyLoadedSource
    , identifiedSourceLoaded
    , identifiedSourceDescriptor
    , identifiedSourceContentId
    , putSourceContentIdCache
    , getSourceContentIdCache
    ) where

import Base

import Felix.Cache.Codec
import Felix.Report.Location
    ( SourceDescriptor
    , sourceDescriptor
    )
import Felix.Source

import Control.DeepSeq (NFData(..), force)
import Control.Exception (evaluate)
import Data.ByteString (ByteString)

newtype SourceContentId =
    SourceContentId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

sourceContentId :: LoadedSource -> SourceContentId
sourceContentId =
    sourceContentIdBytes . loadedBytes

sourceContentIdBytes :: ByteString -> SourceContentId
sourceContentIdBytes bytes =
    SourceContentId
        (hashCacheFields
            "felix-source-content-v1"
            [bytes])

sourceContentIdDigest :: SourceContentId -> CacheDigest
sourceContentIdDigest (SourceContentId digest) =
    digest


-- | One physical source bound to its immutable location attribution and
-- exact-byte cache identity. The constructor is private so callers cannot pair
-- evidence obtained from different sources.
data IdentifiedLoadedSource = IdentifiedLoadedSource
    !LoadedSource
    !SourceDescriptor
    !SourceContentId
    deriving stock (Show, Eq)

instance NFData IdentifiedLoadedSource where
    rnf (IdentifiedLoadedSource loaded descriptor content) =
        rnf loaded `seq` rnf descriptor `seq` rnf content

identifyLoadedSource :: LoadedSource -> IO IdentifiedLoadedSource
identifyLoadedSource loaded = do
    let source = loadedSource loaded
        descriptor = sourceDescriptor
            (canonicalPathFilePath (resolvedSourceCanonicalPath source))
            (resolvedSourceLocationPath source)
    content <- evaluate (force (sourceContentId loaded))
    pure (IdentifiedLoadedSource loaded descriptor content)

identifiedSourceLoaded :: IdentifiedLoadedSource -> LoadedSource
identifiedSourceLoaded
        (IdentifiedLoadedSource loaded _descriptor _content) =
    loaded

identifiedSourceDescriptor :: IdentifiedLoadedSource -> SourceDescriptor
identifiedSourceDescriptor
        (IdentifiedLoadedSource _loaded descriptor _content) =
    descriptor

identifiedSourceContentId
    :: IdentifiedLoadedSource
    -> SourceContentId
identifiedSourceContentId
        (IdentifiedLoadedSource _loaded _descriptor content) =
    content

putSourceContentIdCache :: SourceContentId -> CachePut
putSourceContentIdCache
        (SourceContentId digest) =
    putCacheDigest digest

getSourceContentIdCache :: CacheGet SourceContentId
getSourceContentIdCache =
    SourceContentId <$> getCacheDigest
