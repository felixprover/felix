{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Syntax.Interface
    ( MixfixLevel
    , mixfixLevel
    , mixfixLevelValue
    , MixfixLevelError(..)
    , Fixity(..)
    , sourcePragmaFixity
    , CanonicalLexicalEntry(..)
    , canonicalLexicalSurfacePatterns
    , eligibleExpressionPattern
    , CanonicalSyntaxDelta
    , canonicalSyntaxDelta
    , canonicalSyntaxDeltaEntries
    , canonicalSyntaxDeltaSize
    , CanonicalSyntaxCollision
    , canonicalCollisionPattern
    , canonicalCollisionEntries
    , CanonicalSyntaxDeltaId
    , canonicalSyntaxDeltaId
    , canonicalSyntaxDeltaIdDigest
    , BaseSyntaxInterfaceId
    , baseSyntaxInterfaceId
    , baseSyntaxInterfaceIdDigest
    , baseSyntaxManifest
    , fixedBaseSyntaxEntries
    , SyntaxInterfaceId
    , syntaxInterfaceIdDigest
    , ModuleSyntaxInterface
    , moduleSyntaxInterface
    , moduleSyntaxBase
    , moduleSyntaxDirectInputs
    , moduleSyntaxLocalDelta
    , moduleSyntaxAssertedId
    , SyntaxInterfaceError(..)
    , validateModuleSyntaxInterface
    , putCanonicalLexicalEntryCache
    , getCanonicalLexicalEntryCache
    , putPatternCache
    , getPatternCache
    , putTokenCache
    , getTokenCache
    , putCanonicalSyntaxDeltaCache
    , getCanonicalSyntaxDeltaCache
    , putModuleSyntaxInterfaceCache
    , getModuleSyntaxInterfaceCache
    , putBaseSyntaxInterfaceIdCache
    , getBaseSyntaxInterfaceIdCache
    , putSyntaxInterfaceIdCache
    , getSyntaxInterfaceIdCache
    ) where

import Base

import Felix.Cache.Codec
import Felix.Syntax.Abstract
import Felix.Syntax.Lexicon
import Felix.Syntax.Pragma

import Control.DeepSeq (NFData(..))
import Control.Monad (unless)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Word (Word8)
import Numeric.Natural (Natural)


newtype MixfixLevel = MixfixLevel Word8
    deriving stock (Show, Eq, Ord)
    deriving newtype (Hashable, NFData)

data MixfixLevelError
    = MixfixLevelOutOfRange !Word8
    deriving stock (Show, Eq)

mixfixLevel :: Word8 -> Either MixfixLevelError MixfixLevel
mixfixLevel supplied
    | supplied <= 9 =
        Right (MixfixLevel supplied)
    | otherwise =
        Left (MixfixLevelOutOfRange supplied)

mixfixLevelValue :: MixfixLevel -> Word8
mixfixLevelValue (MixfixLevel level) =
    level

data Fixity = Fixity
    { fixityAssociativity :: !Associativity
    , fixityLevel :: !MixfixLevel
    } deriving stock (Show, Eq, Ord, Generic)
      deriving anyclass (NFData)

sourcePragmaFixity :: SyntaxPragma -> Fixity
sourcePragmaFixity pragma =
    Fixity
        (syntaxPragmaAssociativity pragma)
        (MixfixLevel
            (sourceMixfixLevelValue
                (syntaxPragmaLevel pragma)))

-- | Complete origin-free lexical semantics produced by scanning.
data CanonicalLexicalEntry
    = CanonicalUserAdjective !AdjectiveSide !AdjectiveSurfaceKey
    | CanonicalIntrinsicAdjective !AdjectiveSide !Pattern !Marker
    | CanonicalFunctionPhrase !Pattern !Pattern !Marker
    | CanonicalNoun !Pattern !Pattern !Marker
    | CanonicalStructureNoun !Pattern !Pattern !Marker
    | CanonicalVerb !VerbSurfaces !Marker
    | CanonicalRelation !Token !ParameterArity !Marker
    | CanonicalExpressionFunction !Pattern !Marker !Fixity
    | CanonicalTypedConstant !Token !ConcreteType !Marker
    | CanonicalPrefixPredicate !Text !Natural !Marker
    | CanonicalStructureOperation !Text
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

-- | Every surface pattern through which the concrete parser can select an
-- entry. Equal singular and plural surfaces are returned only once.
canonicalLexicalSurfacePatterns
    :: CanonicalLexicalEntry
    -> NonEmpty Pattern
canonicalLexicalSurfacePatterns =
    deduplicatePatterns . \case
    CanonicalUserAdjective _side (AdjectiveSurfaceKey pat) ->
        [pat]
    CanonicalIntrinsicAdjective _side pat _marker ->
        [pat]
    CanonicalFunctionPhrase singular _plural _marker ->
        [singular]
    CanonicalNoun singular plural _marker ->
        [singular, plural]
    CanonicalStructureNoun singular plural _marker ->
        [singular, plural]
    CanonicalVerb surfaces _marker ->
        [ patternFromHoley (verbSurfaceSingular surfaces)
        , patternFromHoley (verbSurfaceBase surfaces)
        ]
    CanonicalRelation token arity marker ->
        [ relationSymbolPattern
            (RelationSymbol token arity marker)
        ]
    CanonicalExpressionFunction pat _marker _fixity ->
        [pat]
    CanonicalTypedConstant token _coreType _marker ->
        [TokenCons token End]
    CanonicalPrefixPredicate command _arity _marker ->
        [ prefixPredicatePattern
            (PrefixPredicate command 0)
        ]
    CanonicalStructureOperation command ->
        [structSymbolPattern (StructSymbol command)]
  where
    deduplicatePatterns patterns =
        case NonEmpty.nonEmpty
                (Set.toList (Set.fromList patterns)) of
            Just nonempty ->
                nonempty
            Nothing ->
                impossible
                    "canonical lexical entry has no parser surface"

eligibleExpressionPattern :: Pattern -> Bool
eligibleExpressionPattern pat =
    case patternToHoley pat of
        Nothing : rest ->
            case reverse rest of
                Nothing : middleReversed ->
                    let middle =
                            reverse middleReversed
                    in
                        any isJust middle
                            && internallyDelimited middle
                _ ->
                    False
        _ ->
            False
  where
    -- An infix operator may carry parameters, as in @x\\star_{A}y@.
    -- Requiring explicit delimiters keeps the parameter distinct from the
    -- two associative operand holes while allowing the ordinary mixfix
    -- engine to assign fixity to the complete indexed operator.
    internallyDelimited = \case
        [] ->
            True
        Just InvisibleBraceL : Nothing : Just InvisibleBraceR : rest ->
            internallyDelimited rest
        Just BracketL : Nothing : Just BracketR : rest ->
            internallyDelimited rest
        Just ParenL : Nothing : Just ParenR : rest ->
            internallyDelimited rest
        Nothing : _ ->
            False
        Just _token : rest ->
            internallyDelimited rest

newtype CanonicalSyntaxDelta =
    CanonicalSyntaxDelta
        [CanonicalLexicalEntry]
    deriving stock (Show, Eq)
    deriving newtype (NFData)

data CanonicalSyntaxCollision = CanonicalSyntaxCollision
    { canonicalCollisionPattern :: !Pattern
    , canonicalCollisionEntries
        :: !(NonEmpty CanonicalLexicalEntry)
    } deriving stock (Show, Eq)

canonicalSyntaxDelta
    :: [CanonicalLexicalEntry]
    -> Either CanonicalSyntaxCollision CanonicalSyntaxDelta
canonicalSyntaxDelta supplied =
    case orderedCollisions of
        [] ->
            Right (CanonicalSyntaxDelta orderedEntries)
        (_encodedPattern, pat, entries) : _ ->
            Left
                (CanonicalSyntaxCollision
                    pat
                    (case NonEmpty.nonEmpty
                        (canonicalEntryOrder
                            (Set.toList entries)) of
                        Just collisionEntries ->
                            collisionEntries
                        Nothing ->
                            impossible
                                "canonical syntax collision has no entries"))
  where
    orderedEntries =
        canonicalEntryOrder
            (Set.toList (Set.fromList supplied))

    grouped =
        foldl'
            (\entries entry ->
                foldl'
                    (\indexed pat ->
                        Map.insertWith
                            Set.union
                            pat
                            (Set.singleton entry)
                            indexed)
                    entries
                    (canonicalLexicalSurfacePatterns entry))
            mempty
            orderedEntries

    orderedCollisions =
        List.sortOn
            (\(encodedPattern, _pattern, _entries) ->
                encodedPattern)
            [ ( encodeCache (putPatternCache pat)
              , pat
              , entries
              )
            | (pat, entries) <- Map.toList grouped
            , Set.size entries > 1
            ]

canonicalSyntaxDeltaEntries
    :: CanonicalSyntaxDelta
    -> [CanonicalLexicalEntry]
canonicalSyntaxDeltaEntries
        (CanonicalSyntaxDelta entries) =
    entries

canonicalSyntaxDeltaSize :: CanonicalSyntaxDelta -> Int
canonicalSyntaxDeltaSize
        (CanonicalSyntaxDelta entries) =
    length entries

canonicalEntryOrder
    :: [CanonicalLexicalEntry]
    -> [CanonicalLexicalEntry]
canonicalEntryOrder =
    List.sortOn
        (encodeCache . putCanonicalLexicalEntryCache)

newtype CanonicalSyntaxDeltaId =
    CanonicalSyntaxDeltaId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

canonicalSyntaxDeltaId
    :: CanonicalSyntaxDelta
    -> CanonicalSyntaxDeltaId
canonicalSyntaxDeltaId delta =
    CanonicalSyntaxDeltaId
        (hashCacheFields
            "felix-syntax-delta-v1"
            [encodeCache
                (putCanonicalSyntaxDeltaCache delta)])

canonicalSyntaxDeltaIdDigest
    :: CanonicalSyntaxDeltaId
    -> CacheDigest
canonicalSyntaxDeltaIdDigest
        (CanonicalSyntaxDeltaId digest) =
    digest

newtype BaseSyntaxInterfaceId =
    BaseSyntaxInterfaceId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

baseSyntaxInterfaceId :: BaseSyntaxInterfaceId
baseSyntaxInterfaceId =
    BaseSyntaxInterfaceId
        (hashCacheFields
            "felix-base-syntax-interface-v2-bounded-nouns"
            [encodeCache
                (putCacheList
                    putManifestRow
                    baseSyntaxManifest)])
  where
    putManifestRow =
        putCacheList putCanonicalLexicalEntryCache
            . canonicalEntryOrder

baseSyntaxInterfaceIdDigest
    :: BaseSyntaxInterfaceId
    -> CacheDigest
baseSyntaxInterfaceIdDigest
        (BaseSyntaxInterfaceId digest) =
    digest

baseSyntaxManifest :: [[CanonicalLexicalEntry]]
baseSyntaxManifest =
    case traverse makeRow
            (zip [0 :: Word8 ..] builtinMixfixLevels) of
        Right rows
            | length rows == 10 ->
                rows
        _ ->
            impossible
                "the fixed mixfix manifest does not have ten valid rows"
  where
    makeRow (row, entries) = do
        level <- mixfixLevel row
        pure
            [ CanonicalExpressionFunction
                pat
                marker
                (Fixity associativity level)
            | MixfixItem pat marker associativity <-
                entries
            ]

-- | Every fixed lexical entry consulted by the concrete parser. The base
-- syntax identity above commits to the ten expression rows; the remaining
-- fixed categories are compiler input covered by the cache epoch.
fixedBaseSyntaxEntries :: [CanonicalLexicalEntry]
fixedBaseSyntaxEntries =
    case canonicalSyntaxDelta rawEntries of
        Right delta ->
            canonicalSyntaxDeltaEntries delta
        Left collision ->
            impossible
                ("fixed base syntax contains a collision: "
                    <> show collision)
  where
    rawEntries =
        concat baseSyntaxManifest
            <> (canonicalAdjective <$> lexiconAdjLs builtins)
            <> (canonicalAdjective <$> lexiconAdjRs builtins)
            <> (canonicalSgPl CanonicalFunctionPhrase
                    <$> lexiconFuns builtins)
            <> (canonicalSgPl CanonicalNoun
                    <$> lexiconNouns builtins)
            <> (canonicalSgPl CanonicalStructureNoun
                    <$> lexiconStructNouns builtins)
            <> (canonicalVerb <$> lexiconVerbs builtins)
            <> (canonicalRelation
                    <$> lexiconRelationSymbols builtins)
            <> (canonicalPrefix
                    <$> lexiconPrefixPredicates builtins)
            <> (canonicalStructure
                    <$> lexiconStructFun builtins)

    canonicalAdjective item =
        case adjectiveLexicalIdentity item of
            UserAdjectiveIdentity surface ->
                CanonicalUserAdjective
                    (adjectiveLexicalSide item)
                    surface
            IntrinsicAdjectiveIdentity pat marker ->
                CanonicalIntrinsicAdjective
                    (adjectiveLexicalSide item)
                    pat
                    marker

    canonicalSgPl constructor item =
        let patterns =
                lexicalItemSgPlPattern item
        in
            constructor
                (sg patterns)
                (pl patterns)
                (lexicalItemSgPlMarker item)

    canonicalVerb item =
        CanonicalVerb
            (verbLexicalSurfaces item)
            (verbLexicalMarker item)

    canonicalRelation relation =
        CanonicalRelation
            (relationSymbolToken relation)
            (relationSymbolParameterArity relation)
            (relationSymbolMarker relation)

    canonicalPrefix
            (PrefixPredicate command arity, marker) =
        CanonicalPrefixPredicate
            command
            (fromIntegral arity)
            marker

    canonicalStructure (StructSymbol command) =
        CanonicalStructureOperation command

newtype SyntaxInterfaceId =
    SyntaxInterfaceId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

syntaxInterfaceIdDigest :: SyntaxInterfaceId -> CacheDigest
syntaxInterfaceIdDigest (SyntaxInterfaceId digest) =
    digest

data ModuleSyntaxInterface = ModuleSyntaxInterface
    !BaseSyntaxInterfaceId
    ![SyntaxInterfaceId]
    !CanonicalSyntaxDelta
    !SyntaxInterfaceId
    deriving stock (Show, Eq)

instance NFData ModuleSyntaxInterface where
    rnf (ModuleSyntaxInterface base direct delta asserted) =
        rnf base `seq` rnf direct `seq` rnf delta `seq` rnf asserted

moduleSyntaxBase
    :: ModuleSyntaxInterface
    -> BaseSyntaxInterfaceId
moduleSyntaxBase
        (ModuleSyntaxInterface base _direct _delta _asserted) =
    base

moduleSyntaxDirectInputs
    :: ModuleSyntaxInterface
    -> [SyntaxInterfaceId]
moduleSyntaxDirectInputs
        (ModuleSyntaxInterface _base direct _delta _asserted) =
    direct

moduleSyntaxLocalDelta
    :: ModuleSyntaxInterface
    -> CanonicalSyntaxDelta
moduleSyntaxLocalDelta
        (ModuleSyntaxInterface _base _direct delta _asserted) =
    delta

moduleSyntaxAssertedId
    :: ModuleSyntaxInterface
    -> SyntaxInterfaceId
moduleSyntaxAssertedId
        (ModuleSyntaxInterface _base _direct _delta asserted) =
    asserted

data SyntaxInterfaceError
    = DuplicateDirectSyntaxInterface !SyntaxInterfaceId
    | UnexpectedBaseSyntaxInterface
        !BaseSyntaxInterfaceId
        !BaseSyntaxInterfaceId
    | SyntaxInterfaceIdMismatch
        !SyntaxInterfaceId
        !SyntaxInterfaceId
    deriving stock (Show, Eq)

moduleSyntaxInterface
    :: [SyntaxInterfaceId]
    -> CanonicalSyntaxDelta
    -> Either SyntaxInterfaceError ModuleSyntaxInterface
moduleSyntaxInterface direct delta = do
    case firstDuplicate direct of
        Just duplicate -> Left (DuplicateDirectSyntaxInterface duplicate)
        Nothing -> pure ()
    let computed = computeSyntaxInterfaceId baseSyntaxInterfaceId direct delta
    pure (ModuleSyntaxInterface baseSyntaxInterfaceId direct delta computed)

validateModuleSyntaxInterface
    :: BaseSyntaxInterfaceId
    -> [SyntaxInterfaceId]
    -> CanonicalSyntaxDelta
    -> SyntaxInterfaceId
    -> Either SyntaxInterfaceError ModuleSyntaxInterface
validateModuleSyntaxInterface base direct delta asserted = do
    unless
        (base == baseSyntaxInterfaceId)
        (Left
            (UnexpectedBaseSyntaxInterface
                base
                baseSyntaxInterfaceId))
    interface <- moduleSyntaxInterface direct delta
    let computed = moduleSyntaxAssertedId interface
    unless
        (asserted == computed)
        (Left
            (SyntaxInterfaceIdMismatch
                asserted
                computed))
    pure interface

computeSyntaxInterfaceId
    :: BaseSyntaxInterfaceId
    -> [SyntaxInterfaceId]
    -> CanonicalSyntaxDelta
    -> SyntaxInterfaceId
computeSyntaxInterfaceId base direct delta =
    SyntaxInterfaceId
        (hashCacheFields
            "felix-syntax-interface-v1"
            [ cacheDigestBytes
                (baseSyntaxInterfaceIdDigest base)
            , encodeCache
                (putCacheList
                    putSyntaxInterfaceIdCache
                    direct)
            , cacheDigestBytes
                (canonicalSyntaxDeltaIdDigest
                    (canonicalSyntaxDeltaId delta))
            ])

putCanonicalLexicalEntryCache
    :: CanonicalLexicalEntry
    -> CachePut
putCanonicalLexicalEntryCache = \case
    CanonicalUserAdjective side (AdjectiveSurfaceKey pat) -> do
        putCacheTag 0x00
        putAdjectiveSideCache side
        putPatternCache pat
    CanonicalIntrinsicAdjective side pat marker -> do
        putCacheTag 0x01
        putAdjectiveSideCache side
        putPatternCache pat
        putMarkerCache marker
    CanonicalFunctionPhrase singular plural marker -> do
        putCacheTag 0x02
        putPatternCache singular
        putPatternCache plural
        putMarkerCache marker
    CanonicalNoun singular plural marker -> do
        putCacheTag 0x03
        putPatternCache singular
        putPatternCache plural
        putMarkerCache marker
    CanonicalStructureNoun singular plural marker -> do
        putCacheTag 0x04
        putPatternCache singular
        putPatternCache plural
        putMarkerCache marker
    CanonicalVerb surfaces marker -> do
        putCacheTag 0x05
        putVerbSurfacesCache surfaces
        putMarkerCache marker
    CanonicalRelation token arity marker -> do
        putCacheTag 0x06
        putTokenCache token
        putCacheNatural (parameterArityValue arity)
        putMarkerCache marker
    CanonicalExpressionFunction pat marker fixity -> do
        putCacheTag 0x07
        putPatternCache pat
        putMarkerCache marker
        putFixityCache fixity
    CanonicalTypedConstant token coreType marker -> do
        putCacheTag 0x0a
        putTokenCache token
        putConcreteTypeCache coreType
        putMarkerCache marker
    CanonicalPrefixPredicate command arity marker -> do
        putCacheTag 0x08
        putCacheText command
        putCacheNatural arity
        putMarkerCache marker
    CanonicalStructureOperation command -> do
        putCacheTag 0x09
        putCacheText command

getCanonicalLexicalEntryCache
    :: CacheGet CanonicalLexicalEntry
getCanonicalLexicalEntryCache =
    getCacheTag >>= \case
        0x00 ->
            CanonicalUserAdjective
                <$> getAdjectiveSideCache
                <*> (AdjectiveSurfaceKey <$> getPatternCache)
        0x01 ->
            CanonicalIntrinsicAdjective
                <$> getAdjectiveSideCache
                <*> getPatternCache
                <*> getMarkerCache
        0x02 ->
            CanonicalFunctionPhrase
                <$> getPatternCache
                <*> getPatternCache
                <*> getMarkerCache
        0x03 ->
            CanonicalNoun
                <$> getPatternCache
                <*> getPatternCache
                <*> getMarkerCache
        0x04 ->
            CanonicalStructureNoun
                <$> getPatternCache
                <*> getPatternCache
                <*> getMarkerCache
        0x05 ->
            CanonicalVerb
                <$> getVerbSurfacesCache
                <*> getMarkerCache
        0x06 ->
            CanonicalRelation
                <$> getTokenCache
                <*> (ParameterArity <$> getCacheNatural)
                <*> getMarkerCache
        0x07 ->
            CanonicalExpressionFunction
                <$> getPatternCache
                <*> getMarkerCache
                <*> getFixityCache
        0x0a ->
            CanonicalTypedConstant
                <$> getTokenCache
                <*> getConcreteTypeCache
                <*> getMarkerCache
        0x08 ->
            CanonicalPrefixPredicate
                <$> getCacheText
                <*> getCacheNatural
                <*> getMarkerCache
        0x09 ->
            CanonicalStructureOperation
                <$> getCacheText
        tag ->
            fail
                ("unknown canonical lexical entry tag "
                    <> show tag)

putVerbSurfacesCache :: VerbSurfaces -> CachePut
putVerbSurfacesCache surfaces = do
    putPatternCache
        (patternFromHoley (verbSurfaceSingular surfaces))
    putPatternCache
        (patternFromHoley (verbSurfaceBase surfaces))

getVerbSurfacesCache :: CacheGet VerbSurfaces
getVerbSurfacesCache = do
    singular <- patternToHoley <$> getPatternCache
    base <- patternToHoley <$> getPatternCache
    either (fail . show) pure (checkVerbSurfaces singular base)

putAdjectiveSideCache :: AdjectiveSide -> CachePut
putAdjectiveSideCache = \case
    LeftAdjectiveSide -> putCacheTag 0x00
    RightAdjectiveSide -> putCacheTag 0x01

getAdjectiveSideCache :: CacheGet AdjectiveSide
getAdjectiveSideCache =
    getCacheTag >>= \case
        0x00 -> pure LeftAdjectiveSide
        0x01 -> pure RightAdjectiveSide
        tag -> fail ("unknown adjective side tag " <> show tag)

putConcreteTypeCache :: ConcreteType -> CachePut
putConcreteTypeCache = \case
    ConcreteProp ->
        putCacheTag 0x00
    ConcreteSet ->
        putCacheTag 0x01
    ConcreteArrow domain codomain -> do
        putCacheTag 0x02
        putConcreteTypeCache domain
        putConcreteTypeCache codomain

getConcreteTypeCache :: CacheGet ConcreteType
getConcreteTypeCache = getCacheNode $
    getCacheTag >>= \case
        0x00 -> pure ConcreteProp
        0x01 -> pure ConcreteSet
        0x02 ->
            ConcreteArrow
                <$> getConcreteTypeCache
                <*> getConcreteTypeCache
        tag ->
            fail ("unknown concrete type tag " <> show tag)

putCanonicalSyntaxDeltaCache
    :: CanonicalSyntaxDelta
    -> CachePut
putCanonicalSyntaxDeltaCache
        (CanonicalSyntaxDelta entries) =
    putCacheList putCanonicalLexicalEntryCache entries

getCanonicalSyntaxDeltaCache
    :: CacheGet CanonicalSyntaxDelta
getCanonicalSyntaxDeltaCache = do
    supplied <- getCacheList getCanonicalLexicalEntryCache
    case canonicalSyntaxDelta supplied of
        Left collision ->
            fail
                ("colliding cached canonical syntax entries: "
                    <> show collision)
        Right delta
            | canonicalSyntaxDeltaEntries delta == supplied ->
                pure delta
            | otherwise ->
                fail
                    "cached canonical syntax entries are not in canonical order"

putModuleSyntaxInterfaceCache
    :: ModuleSyntaxInterface
    -> CachePut
putModuleSyntaxInterfaceCache
        (ModuleSyntaxInterface base direct delta asserted) = do
    putBaseSyntaxInterfaceIdCache base
    putCacheList putSyntaxInterfaceIdCache direct
    putCanonicalSyntaxDeltaCache delta
    putSyntaxInterfaceIdCache asserted

getModuleSyntaxInterfaceCache
    :: CacheGet ModuleSyntaxInterface
getModuleSyntaxInterfaceCache = do
    base <- getBaseSyntaxInterfaceIdCache
    direct <- getCacheList getSyntaxInterfaceIdCache
    delta <- getCanonicalSyntaxDeltaCache
    asserted <- getSyntaxInterfaceIdCache
    case
        validateModuleSyntaxInterface
            base
            direct
            delta
            asserted of
        Left err ->
            fail
                ("invalid module syntax interface: "
                    <> show err)
        Right interface ->
            pure interface

putBaseSyntaxInterfaceIdCache
    :: BaseSyntaxInterfaceId
    -> CachePut
putBaseSyntaxInterfaceIdCache
        (BaseSyntaxInterfaceId digest) =
    putCacheDigest digest

getBaseSyntaxInterfaceIdCache
    :: CacheGet BaseSyntaxInterfaceId
getBaseSyntaxInterfaceIdCache =
    BaseSyntaxInterfaceId <$> getCacheDigest

putSyntaxInterfaceIdCache
    :: SyntaxInterfaceId
    -> CachePut
putSyntaxInterfaceIdCache
        (SyntaxInterfaceId digest) =
    putCacheDigest digest

getSyntaxInterfaceIdCache
    :: CacheGet SyntaxInterfaceId
getSyntaxInterfaceIdCache =
    SyntaxInterfaceId <$> getCacheDigest

putFixityCache :: Fixity -> CachePut
putFixityCache (Fixity associativity level) = do
    putAssociativityCache associativity
    putCacheTag (mixfixLevelValue level)

getFixityCache :: CacheGet Fixity
getFixityCache = do
    associativity <- getAssociativityCache
    suppliedLevel <- getCacheTag
    case mixfixLevel suppliedLevel of
        Left err ->
            fail ("invalid cached mixfix level: " <> show err)
        Right level ->
            pure (Fixity associativity level)

putAssociativityCache :: Associativity -> CachePut
putAssociativityCache =
    putCacheTag . \case
        LeftAssoc ->
            0x00
        RightAssoc ->
            0x01
        NonAssoc ->
            0x02

getAssociativityCache :: CacheGet Associativity
getAssociativityCache =
    getCacheTag >>= \case
        0x00 ->
            pure LeftAssoc
        0x01 ->
            pure RightAssoc
        0x02 ->
            pure NonAssoc
        tag ->
            fail
                ("unknown associativity tag " <> show tag)

putMarkerCache :: Marker -> CachePut
putMarkerCache (Marker marker) =
    putCacheText marker

getMarkerCache :: CacheGet Marker
getMarkerCache =
    Marker <$> getCacheText

putPatternCache :: Pattern -> CachePut
putPatternCache = \case
    End ->
        putCacheTag 0x00
    HoleCons rest -> do
        putCacheTag 0x01
        putPatternCache rest
    TokenCons token rest -> do
        putCacheTag 0x02
        putTokenCache token
        putPatternCache rest

getPatternCache :: CacheGet Pattern
getPatternCache = getCacheNode $
    getCacheTag >>= \case
        0x00 ->
            pure End
        0x01 ->
            HoleCons <$> getPatternCache
        0x02 ->
            TokenCons
                <$> getTokenCache
                <*> getPatternCache
        tag ->
            fail
                ("unknown lexical pattern tag " <> show tag)

putTokenCache :: Token -> CachePut
putTokenCache = \case
    Word text -> do
        putCacheTag 0x00
        putCacheText text
    Variable text -> do
        putCacheTag 0x01
        putCacheText text
    Symbol text -> do
        putCacheTag 0x02
        putCacheText text
    Integer integer -> do
        putCacheTag 0x03
        putCacheInteger integer
    Command text -> do
        putCacheTag 0x04
        putCacheText text
    NamedItem text -> putCacheTag 0x12 >> putCacheText text
    CaseHeading text -> putCacheTag 0x13 >> putCacheText text
    CommandReference command references -> do
        putCacheTag 0x11
        putCacheText command
        putCacheList putCacheText (toList references)
    Label text -> do
        putCacheTag 0x05
        putCacheText text
    Ref references -> do
        putCacheTag 0x06
        putCacheList putCacheText (toList references)
    BeginEnv text -> do
        putCacheTag 0x07
        putCacheText text
    EndEnv text -> do
        putCacheTag 0x08
        putCacheText text
    ParenL ->
        putCacheTag 0x09
    ParenR ->
        putCacheTag 0x0a
    BracketL ->
        putCacheTag 0x0b
    BracketR ->
        putCacheTag 0x0c
    VisibleBraceL ->
        putCacheTag 0x0d
    VisibleBraceR ->
        putCacheTag 0x0e
    InvisibleBraceL ->
        putCacheTag 0x0f
    InvisibleBraceR ->
        putCacheTag 0x10

getTokenCache :: CacheGet Token
getTokenCache =
    getCacheTag >>= \case
        0x00 ->
            Word <$> getCacheText
        0x01 ->
            Variable <$> getCacheText
        0x02 ->
            Symbol <$> getCacheText
        0x03 ->
            Integer <$> getCacheInteger
        0x04 ->
            Command <$> getCacheText
        0x12 -> NamedItem <$> getCacheText
        0x13 -> CaseHeading <$> getCacheText
        0x05 ->
            Label <$> getCacheText
        0x06 -> do
            references <- getCacheList getCacheText
            case NonEmpty.nonEmpty references of
                Nothing ->
                    fail "cached reference token has no marker"
                Just nonempty ->
                    pure (Ref nonempty)
        0x07 ->
            BeginEnv <$> getCacheText
        0x08 ->
            EndEnv <$> getCacheText
        0x09 ->
            pure ParenL
        0x0a ->
            pure ParenR
        0x0b ->
            pure BracketL
        0x0c ->
            pure BracketR
        0x0d ->
            pure VisibleBraceL
        0x0e ->
            pure VisibleBraceR
        0x0f ->
            pure InvisibleBraceL
        0x10 ->
            pure InvisibleBraceR
        0x11 -> do
            command <- getCacheText
            references <- getCacheList getCacheText
            case NonEmpty.nonEmpty references of
                Nothing ->
                    fail "cached command reference has no marker"
                Just nonempty ->
                    pure (CommandReference command nonempty)
        tag ->
            fail ("unknown lexical token tag " <> show tag)
