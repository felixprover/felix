{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Owner-independent parsed artefact identities.
module Felix.Parsed.Identity
    ( ParsedModuleKey
    , parsedModuleKey
    , parsedModuleKeyFromSyntax
    , ParsedModuleKeyError(..)
    , parsedModuleKeyDigest
    , ParsedModuleId
    , parsedModuleId
    , parsedModuleIdDigest
    , putParsedModuleKeyCache
    , getParsedModuleKeyCache
    , putParsedModuleIdCache
    , getParsedModuleIdCache
    ) where

import Base
import Felix.Cache.Codec
import Felix.Source.Content
import Felix.Syntax.Interface

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)


newtype ParsedModuleKey =
    ParsedModuleKey CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

data ParsedModuleKeyError
    = DuplicateParsedDirectSyntaxInput !SyntaxInterfaceId
    deriving stock (Show, Eq)

parsedModuleKey
    :: SourceContentId
    -> BaseSyntaxInterfaceId
    -> [SyntaxInterfaceId]
    -> Either ParsedModuleKeyError ParsedModuleKey
parsedModuleKey sourceContent base direct = do
    case firstDuplicate direct of
        Just duplicate ->
            Left (DuplicateParsedDirectSyntaxInput duplicate)
        Nothing ->
            pure ()
    pure (computeParsedModuleKey sourceContent base direct)

-- | The syntax interface already establishes the ordered, distinct inputs.
parsedModuleKeyFromSyntax
    :: SourceContentId -> ModuleSyntaxInterface -> ParsedModuleKey
parsedModuleKeyFromSyntax content syntax =
    computeParsedModuleKey content
        (moduleSyntaxBase syntax) (moduleSyntaxDirectInputs syntax)

computeParsedModuleKey
    :: SourceContentId -> BaseSyntaxInterfaceId -> [SyntaxInterfaceId]
    -> ParsedModuleKey
computeParsedModuleKey sourceContent base direct =
    ParsedModuleKey
        (hashCacheFields
            "felix-parsed-module-key-v2"
            [ encodeCache
                (putSourceContentIdCache sourceContent)
            , encodeCache
                (putBaseSyntaxInterfaceIdCache base)
            , encodeCache
                (putCacheList
                    putSyntaxInterfaceIdCache
                    direct)
            ])

parsedModuleKeyDigest :: ParsedModuleKey -> CacheDigest
parsedModuleKeyDigest (ParsedModuleKey digest) =
    digest

newtype ParsedModuleId =
    ParsedModuleId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

-- | The payload is the complete canonical owner-independent parsed value.
parsedModuleId :: ParsedModuleKey -> ByteString -> ParsedModuleId
parsedModuleId key payload =
    ParsedModuleId
        (hashCacheFields
            "felix-parsed-module-v1"
            [ encodeCache (putParsedModuleKeyCache key)
            , payload
            ])

parsedModuleIdDigest :: ParsedModuleId -> CacheDigest
parsedModuleIdDigest (ParsedModuleId digest) =
    digest

putParsedModuleKeyCache :: ParsedModuleKey -> CachePut
putParsedModuleKeyCache (ParsedModuleKey digest) =
    putCacheDigest digest

getParsedModuleKeyCache :: CacheGet ParsedModuleKey
getParsedModuleKeyCache =
    ParsedModuleKey <$> getCacheDigest

putParsedModuleIdCache :: ParsedModuleId -> CachePut
putParsedModuleIdCache (ParsedModuleId digest) =
    putCacheDigest digest

getParsedModuleIdCache :: CacheGet ParsedModuleId
getParsedModuleIdCache =
    ParsedModuleId <$> getCacheDigest
