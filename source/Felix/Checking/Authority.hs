{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Compact public fact authority and exact contextual authorization.
module Felix.Checking.Authority
    ( EscapeKind(..)
    , EscapeKinds
    , emptyEscapeKinds
    , singletonEscapeKind
    , escapeKinds
    , escapeKindsToList
    , unionEscapeKinds
    , AuthoritySafety
    , cleanAuthoritySafety
    , authoritySafety
    , authoritySafetyEscapeKinds
    , unionAuthoritySafety
    , FactAuthority
    , factAuthority
    , factAuthorityTheorem
    , factAuthoritySafety
    , PreparedRequestDialect(..)
    , PreparedRequestMode(..)
    , PreparedRequestId
    , preparedRequestId
    , GuardedRuleSet
    , guardedRuleSet
    , guardedRuleTags
    , StructureLawFamily(..)
    , KernelConstructionDescriptor(..)
    , ExternalProofUse(..)
    , externalProofUseRequests
    , DirectAuthorization(..)
    , ValidationCertificate
    , validationCertificate
    , validationTarget
    , validationDirectAuthorization
    , ValidationCertificateError(..)
    , CandidateSafety
    , initialCandidateSafety
    , candidateSafetyAuthority
    , candidateFactAuthority
    , accumulateFactSafety
    , addCandidateEscape
    , FactSafetyError(..)
    , putEscapeKindsCache
    , getEscapeKindsCache
    , putAuthoritySafetyCache
    , getAuthoritySafetyCache
    , putFactAuthorityCache
    , getFactAuthorityCache
    , putPreparedRequestIdCache
    , getPreparedRequestIdCache
    , putDirectAuthorizationCache
    , getDirectAuthorizationCache
    , putValidationCertificateCache
    , getValidationCertificateCache
    ) where

import Base
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Cache.Codec

import Control.DeepSeq (NFData(..))
import Control.Monad (unless, when)
import Data.Bits ((.&.), (.|.), bit, complement)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.List (filter)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Word (Word8)


data EscapeKind
    = SourceAxiom
    | Omitted
    deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
    deriving anyclass (NFData)

-- | Canonical bounded set. The bit positions are stable cache tags.
newtype EscapeKinds =
    EscapeKinds Word8
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

emptyEscapeKinds :: EscapeKinds
emptyEscapeKinds =
    EscapeKinds 0

singletonEscapeKind :: EscapeKind -> EscapeKinds
singletonEscapeKind =
    EscapeKinds . escapeKindBit

escapeKinds :: Foldable collection => collection EscapeKind -> EscapeKinds
escapeKinds =
    foldl'
        (\acc kind ->
            unionEscapeKinds acc (singletonEscapeKind kind))
        emptyEscapeKinds

escapeKindsToList :: EscapeKinds -> [EscapeKind]
escapeKindsToList kinds =
    filter
        (\kind ->
            let EscapeKinds bits = kinds
            in bits .&. escapeKindBit kind /= 0)
        [SourceAxiom, Omitted]

unionEscapeKinds :: EscapeKinds -> EscapeKinds -> EscapeKinds
unionEscapeKinds (EscapeKinds left) (EscapeKinds right) =
    EscapeKinds (left .|. right)

escapeKindBit :: EscapeKind -> Word8
escapeKindBit = \case
    SourceAxiom -> bit 0
    Omitted -> bit 1

allEscapeBits :: Word8
allEscapeBits =
    escapeKindBit SourceAxiom .|. escapeKindBit Omitted


data AuthoritySafety
    = Clean
    | EscapeHatchBacked !EscapeKinds
    deriving stock (Show, Eq, Ord)

instance NFData AuthoritySafety where
    rnf Clean = ()
    rnf (EscapeHatchBacked kinds) = rnf kinds

cleanAuthoritySafety :: AuthoritySafety
cleanAuthoritySafety =
    Clean

authoritySafety :: EscapeKinds -> AuthoritySafety
authoritySafety kinds
    | kinds == emptyEscapeKinds = Clean
    | otherwise = EscapeHatchBacked kinds

authoritySafetyEscapeKinds :: AuthoritySafety -> EscapeKinds
authoritySafetyEscapeKinds = \case
    Clean -> emptyEscapeKinds
    EscapeHatchBacked kinds -> kinds

unionAuthoritySafety
    :: AuthoritySafety
    -> AuthoritySafety
    -> AuthoritySafety
unionAuthoritySafety left right =
    authoritySafety
        (unionEscapeKinds
            (authoritySafetyEscapeKinds left)
            (authoritySafetyEscapeKinds right))


-- | Public fact-authority content, not an authorization capability.  A value
-- becomes usable only when Declaration authenticates it against an opaque
-- builder or pending-fact capability and admits the matching proposition into
-- the current checked-object closure.
data FactAuthority = FactAuthority
    !TheoremRef
    !AuthoritySafety
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

factAuthority :: TheoremRef -> AuthoritySafety -> FactAuthority
factAuthority =
    FactAuthority

factAuthorityTheorem :: FactAuthority -> TheoremRef
factAuthorityTheorem (FactAuthority reference _) =
    reference

factAuthoritySafety :: FactAuthority -> AuthoritySafety
factAuthoritySafety (FactAuthority _ safety) =
    safety


data PreparedRequestDialect
    = PreparedRequestFof
    | PreparedRequestTh0
    deriving stock (Show, Eq, Ord, Generic)

data PreparedRequestMode
    = PreparedRequestDirect
    | PreparedRequestIndirect
    deriving stock (Show, Eq, Ord, Generic)

newtype PreparedRequestId =
    PreparedRequestId CacheDigest
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

preparedRequestId
    :: PreparedRequestDialect
    -> PreparedRequestMode
    -> ByteString
    -> PreparedRequestId
preparedRequestId dialect mode bytes =
    PreparedRequestId
        (hashCacheFields
            "felix-prepared-request-v2"
            [ ByteString.singleton (preparedRequestDialectTag dialect)
            , ByteString.singleton (preparedRequestModeTag mode)
            , bytes
            ])

preparedRequestDialectTag :: PreparedRequestDialect -> Word8
preparedRequestDialectTag = \case
    PreparedRequestFof -> 0x00
    PreparedRequestTh0 -> 0x01

preparedRequestModeTag :: PreparedRequestMode -> Word8
preparedRequestModeTag = \case
    PreparedRequestDirect -> 0x00
    PreparedRequestIndirect -> 0x01


-- | A nonempty canonical set of guarded kernel rules.
newtype GuardedRuleSet =
    GuardedRuleSet (Set KernelRuleTag)
    deriving stock (Show, Eq, Ord)

guardedRuleSet :: NonEmpty KernelRuleTag -> GuardedRuleSet
guardedRuleSet =
    GuardedRuleSet . Set.fromList . NonEmpty.toList

guardedRuleTags :: GuardedRuleSet -> Set KernelRuleTag
guardedRuleTags (GuardedRuleSet rules) =
    rules

data KernelConstructionDescriptor
    = FoundationLeaf !FoundationAxiomTag
    | GuardedFoundationRules !GuardedRuleSet
    | CheckedDefinitionEquation !ObjectId
    | CheckedDefinitionProjection !ObjectId !ConjunctionPath
    | CheckedSetConstructionExtensionality !ObjectId !CacheDigest
    | CheckedStructureLaw !StructureLawFamily
    | CheckedImplementationDefinition !ObjectId
    | CheckedDerivedConstruction
    deriving stock (Show, Eq, Ord, Generic)

-- | Persistent authority vocabulary for compiler-generated structure laws.
-- The theorem reference records the exact proposition; this tag records only
-- the independently checked proof recipe and foundation footprint.
data StructureLawFamily
    = StructurePredicateComponent
    | StructureExactGraph
    | StructureReductMembership
    | StructureReductExact
    | StructureProjectionEntry
    | StructureProjectionAgreement
    | StructureProjectionEntryAgreement
    | StructureProjectionGraphAgreement
    | StructureProjectionExtensionality
    | StructureReductIdentity
    | StructureReductProjection
    | StructureSelectorPairDistinct
    | StructureSelectorDistinct
    | StructureAggregatePairCoded
    | StructureAggregateValueUnique
    | StructureAggregateEntry
    | StructureAggregateSelectorClosed
    | StructureAggregateProjectionApplication
    | StructureAggregateFunctional
    | StructureAggregateExact
    | StructureAggregateProjection
    deriving stock (Show, Eq, Ord, Generic)

data ExternalProofUse request
    = NoExternalProofUse
    | UsesExternalProof !(NonEmpty request)
    deriving stock (Show, Eq, Ord, Functor, Generic)

externalProofUseRequests :: ExternalProofUse request -> [request]
externalProofUseRequests = \case
    NoExternalProofUse -> []
    UsesExternalProof requests -> toList requests

data DirectAuthorization
    = CheckedKernelConstruction !KernelConstructionDescriptor
    | CheckedSourceProof !(ExternalProofUse PreparedRequestId)
    | SourceAxiomAuthorization
    | OmittedAuthorization
    deriving stock (Show, Eq, Ord, Generic)


-- | Inert validation content.  The smart constructor checks the direct
-- authorization's safety shape, but possession of this value alone grants no
-- fact use; the declaration owner must match it to its retained capability.
data ValidationCertificate = ValidationCertificate
    !FactAuthority
    !DirectAuthorization
    deriving stock (Show, Eq, Ord, Generic)

data ValidationCertificateError
    = SourceAxiomSafetyMismatch !AuthoritySafety
    | OmittedSafetyMissing !AuthoritySafety
    deriving stock (Show, Eq)

validationCertificate
    :: FactAuthority
    -> DirectAuthorization
    -> Either ValidationCertificateError ValidationCertificate
validationCertificate target direct = do
    case direct of
        SourceAxiomAuthorization ->
            unless
                (factAuthoritySafety target
                    == authoritySafety
                        (singletonEscapeKind SourceAxiom))
                (Left
                    (SourceAxiomSafetyMismatch
                        (factAuthoritySafety target)))
        OmittedAuthorization ->
            unless
                (Omitted
                    `elem` escapeKindsToList
                        (authoritySafetyEscapeKinds
                            (factAuthoritySafety target)))
                (Left
                    (OmittedSafetyMissing
                        (factAuthoritySafety target)))
        CheckedKernelConstruction{} -> pure ()
        CheckedSourceProof{} -> pure ()
    pure (ValidationCertificate target direct)

validationTarget :: ValidationCertificate -> FactAuthority
validationTarget (ValidationCertificate target _) =
    target

validationDirectAuthorization
    :: ValidationCertificate
    -> DirectAuthorization
validationDirectAuthorization (ValidationCertificate _ direct) =
    direct


newtype CandidateSafety =
    CandidateSafety AuthoritySafety
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (NFData)

initialCandidateSafety :: CandidateSafety
initialCandidateSafety =
    CandidateSafety Clean

candidateSafetyAuthority :: CandidateSafety -> AuthoritySafety
candidateSafetyAuthority (CandidateSafety safety) =
    safety

-- | Freeze the final safety of one completed candidate into public authority.
--
-- The trusted completion boundary uses this projection for both the inert
-- validation certificate and its runtime pending authorization.
candidateFactAuthority
    :: TheoremRef
    -> CandidateSafety
    -> FactAuthority
candidateFactAuthority reference (CandidateSafety safety) =
    FactAuthority reference safety

data FactSafetyError
    = FactSafetyTheoremMismatch !TheoremRef !TheoremRef
    deriving stock (Show, Eq)

-- | Check theorem agreement and accumulate already-authorized public safety.
--
-- This operation does not authorize a freely constructed 'FactAuthority'.
-- Callers may use it only after checking opaque global, imported, or staged
-- builder authorization at the boundary that owns that authority.
accumulateFactSafety
    :: TheoremRef
    -> FactAuthority
    -> CandidateSafety
    -> Either FactSafetyError CandidateSafety
accumulateFactSafety expected supplied (CandidateSafety current) = do
    unless
        (factAuthorityTheorem supplied == expected)
        (Left
            (FactSafetyTheoremMismatch
                expected
                (factAuthorityTheorem supplied)))
    pure
        (CandidateSafety
            (unionAuthoritySafety
                current
                (factAuthoritySafety supplied)))

addCandidateEscape
    :: EscapeKind
    -> CandidateSafety
    -> CandidateSafety
addCandidateEscape kind (CandidateSafety current) =
    CandidateSafety
        (unionAuthoritySafety
            current
            (authoritySafety (singletonEscapeKind kind)))


putEscapeKindsCache :: EscapeKinds -> CachePut
putEscapeKindsCache (EscapeKinds bits) =
    putCacheTag bits

getEscapeKindsCache :: CacheGet EscapeKinds
getEscapeKindsCache = do
    bits <- getCacheTag
    unless
        (bits .&. complement allEscapeBits == 0)
        (fail "unknown cache escape-kind bit")
    pure (EscapeKinds bits)

putAuthoritySafetyCache :: AuthoritySafety -> CachePut
putAuthoritySafetyCache = \case
    Clean ->
        putCacheTag 0x00
    EscapeHatchBacked kinds -> do
        putCacheTag 0x01
        putEscapeKindsCache kinds

getAuthoritySafetyCache :: CacheGet AuthoritySafety
getAuthoritySafetyCache =
    getCacheTag >>= \case
        0x00 ->
            pure Clean
        0x01 -> do
            kinds <- getEscapeKindsCache
            when
                (kinds == emptyEscapeKinds)
                (fail "empty escape-hatch-backed safety")
            pure (EscapeHatchBacked kinds)
        tag ->
            fail ("unknown cache authority-safety tag " <> show tag)

putFactAuthorityCache :: FactAuthority -> CachePut
putFactAuthorityCache (FactAuthority reference safety) = do
    putTheoremRefCache reference
    putAuthoritySafetyCache safety

getFactAuthorityCache :: CacheGet FactAuthority
getFactAuthorityCache =
    FactAuthority
        <$> getTheoremRefCache
        <*> getAuthoritySafetyCache

putPreparedRequestIdCache :: PreparedRequestId -> CachePut
putPreparedRequestIdCache (PreparedRequestId digest) =
    putCacheDigest digest

getPreparedRequestIdCache :: CacheGet PreparedRequestId
getPreparedRequestIdCache =
    PreparedRequestId <$> getCacheDigest

putDirectAuthorizationCache :: DirectAuthorization -> CachePut
putDirectAuthorizationCache = \case
    CheckedKernelConstruction descriptor -> do
        putCacheTag 0x00
        putKernelDescriptor descriptor
    CheckedSourceProof requests -> do
        putCacheTag 0x01
        case requests of
            NoExternalProofUse ->
                putCacheTag 0x00
            UsesExternalProof nonempty -> do
                putCacheTag 0x01
                putCacheList putPreparedRequestIdCache (toList nonempty)
    SourceAxiomAuthorization ->
        putCacheTag 0x03
    OmittedAuthorization ->
        putCacheTag 0x04

getDirectAuthorizationCache :: CacheGet DirectAuthorization
getDirectAuthorizationCache =
    getCacheTag >>= \case
        0x00 ->
            CheckedKernelConstruction <$> getKernelDescriptor
        0x01 ->
            CheckedSourceProof <$> getExternalProofUse
        0x03 ->
            pure SourceAxiomAuthorization
        0x04 ->
            pure OmittedAuthorization
        tag ->
            fail ("unknown cache direct-authorization tag " <> show tag)
  where
    getExternalProofUse =
        getCacheTag >>= \case
            0x00 -> pure NoExternalProofUse
            0x01 -> do
                requests <- getCacheList getPreparedRequestIdCache
                maybe
                    (fail "external proof use has no requests")
                    (pure . UsesExternalProof)
                    (NonEmpty.nonEmpty requests)
            tag ->
                fail ("unknown cache external-proof-use tag " <> show tag)

putValidationCertificateCache :: ValidationCertificate -> CachePut
putValidationCertificateCache
        (ValidationCertificate target direct) = do
    putFactAuthorityCache target
    putDirectAuthorizationCache direct

getValidationCertificateCache :: CacheGet ValidationCertificate
getValidationCertificateCache = do
    target <- getFactAuthorityCache
    direct <- getDirectAuthorizationCache
    case validationCertificate target direct of
        Left err ->
            fail ("invalid cache validation certificate: " <> show err)
        Right certificate ->
            pure certificate


putKernelDescriptor :: KernelConstructionDescriptor -> CachePut
putKernelDescriptor = \case
    FoundationLeaf tag -> do
        putCacheTag 0x00
        putFoundationAxiomTagCache tag
    GuardedFoundationRules rules -> do
        putCacheTag 0x01
        putCacheList putKernelRuleTagCache
            (Set.toAscList (guardedRuleTags rules))
    CheckedDefinitionEquation identity -> do
        putCacheTag 0x02
        putObjectIdCache identity
    CheckedSetConstructionExtensionality identity construction -> do
        putCacheTag 0x03
        putObjectIdCache identity
        putCacheDigest construction
    CheckedStructureLaw family -> do
        putCacheTag 0x04
        putStructureLawFamily family
    CheckedDefinitionProjection identity path -> do
        putCacheTag 0x05
        putObjectIdCache identity
        putProjectionPath path
    CheckedImplementationDefinition identity -> do
        putCacheTag 0x06
        putObjectIdCache identity
    CheckedDerivedConstruction -> putCacheTag 0x07
  where
    putProjectionPath = \case
        ConjunctionHere -> putCacheTag 0x00
        ConjunctionLeft rest -> putCacheTag 0x01 >> putProjectionPath rest
        ConjunctionRight rest -> putCacheTag 0x02 >> putProjectionPath rest

getKernelDescriptor :: CacheGet KernelConstructionDescriptor
getKernelDescriptor =
    getCacheTag >>= \case
        0x00 -> FoundationLeaf <$> getFoundationAxiomTagCache
        0x01 -> do
            tags <- getCacheList getKernelRuleTagCache
            rules <-
                maybe
                    (fail "cache guarded-rule set is empty")
                    pure
                    (NonEmpty.nonEmpty tags)
            unless (strictlyIncreasing tags)
                (fail "cache guarded-rule tags are not in canonical order")
            pure (GuardedFoundationRules (guardedRuleSet rules))
        0x02 -> CheckedDefinitionEquation <$> getObjectIdCache
        0x03 ->
            CheckedSetConstructionExtensionality
                <$> getObjectIdCache
                <*> getCacheDigest
        0x04 -> CheckedStructureLaw <$> getStructureLawFamily
        0x05 -> CheckedDefinitionProjection <$> getObjectIdCache <*> getProjectionPath
        0x06 -> CheckedImplementationDefinition <$> getObjectIdCache
        0x07 -> pure CheckedDerivedConstruction
        tag ->
            fail ("unknown cache kernel-construction tag " <> show tag)
  where
    getProjectionPath = getCacheNode $ getCacheTag >>= \case
        0x00 -> pure ConjunctionHere
        0x01 -> ConjunctionLeft <$> getProjectionPath
        0x02 -> ConjunctionRight <$> getProjectionPath
        tag -> fail ("unknown definition-projection path tag " <> show tag)

putStructureLawFamily :: StructureLawFamily -> CachePut
putStructureLawFamily = putCacheTag . \case
    StructurePredicateComponent -> 0x00
    StructureExactGraph -> 0x01
    StructureReductMembership -> 0x02
    StructureReductExact -> 0x03
    StructureProjectionEntry -> 0x04
    StructureProjectionAgreement -> 0x05
    StructureProjectionEntryAgreement -> 0x06
    StructureProjectionGraphAgreement -> 0x07
    StructureProjectionExtensionality -> 0x08
    StructureReductIdentity -> 0x09
    StructureReductProjection -> 0x0a
    StructureSelectorPairDistinct -> 0x0b
    StructureSelectorDistinct -> 0x0c
    StructureAggregatePairCoded -> 0x0d
    StructureAggregateValueUnique -> 0x0e
    StructureAggregateEntry -> 0x0f
    StructureAggregateSelectorClosed -> 0x10
    StructureAggregateProjectionApplication -> 0x11
    StructureAggregateFunctional -> 0x12
    StructureAggregateExact -> 0x13
    StructureAggregateProjection -> 0x14

getStructureLawFamily :: CacheGet StructureLawFamily
getStructureLawFamily =
    getCacheTag >>= \case
        0x00 -> pure StructurePredicateComponent
        0x01 -> pure StructureExactGraph
        0x02 -> pure StructureReductMembership
        0x03 -> pure StructureReductExact
        0x04 -> pure StructureProjectionEntry
        0x05 -> pure StructureProjectionAgreement
        0x06 -> pure StructureProjectionEntryAgreement
        0x07 -> pure StructureProjectionGraphAgreement
        0x08 -> pure StructureProjectionExtensionality
        0x09 -> pure StructureReductIdentity
        0x0a -> pure StructureReductProjection
        0x0b -> pure StructureSelectorPairDistinct
        0x0c -> pure StructureSelectorDistinct
        0x0d -> pure StructureAggregatePairCoded
        0x0e -> pure StructureAggregateValueUnique
        0x0f -> pure StructureAggregateEntry
        0x10 -> pure StructureAggregateSelectorClosed
        0x11 -> pure StructureAggregateProjectionApplication
        0x12 -> pure StructureAggregateFunctional
        0x13 -> pure StructureAggregateExact
        0x14 -> pure StructureAggregateProjection
        tag -> fail ("unknown cache structure-law-family tag " <> show tag)

strictlyIncreasing :: Ord value => [value] -> Bool
strictlyIncreasing values =
    and (zipWith (<) values (drop 1 values))
