{-# LANGUAGE NoImplicitPrelude #-}

-- | Immutable products of successful declaration admission.
module Felix.Checking.Commit
    ( CommittedDeclarationBatch
    , committedDeclarationBatch
    , committedBatchOwner
    , committedBatchSlot
    , committedBatchPreviousPrefix
    , committedBatchNextPrefix
    , committedBatchDelta
    , committedBatchObjects
    , committedBatchPropositions
    , committedBatchProofValidations
    , committedBatchDeclarationValidation
    , committedBatchValidationCertificates
    , PendingModulePrefix
    , emptyPendingModulePrefix
    , appendPendingBatch
    , pendingModulePrefixBatches
    , pendingModulePrefixCurrent
    ) where

import Base
import Felix.Cache.Codec (encodeCache)
import Felix.Checking.Authority
    ( ValidationCertificate
    , putValidationCertificateCache
    )
import Felix.Checking.Identity
import Felix.Checking.Semantic
import Felix.Module (ModuleName)

import Control.DeepSeq (deepseq)
import Data.ByteString qualified as ByteString


data CommittedDeclarationBatch = CommittedDeclarationBatch
    !ModuleName
    !DeclarationSlot
    !PrefixContextId
    !PrefixContextId
    !DeclarationInterfaceDelta
    ![AssertedObject]
    ![CheckedPropositionContent]
    ![ProofValidationRecord]
    !(Maybe DeclarationValidationRecord)

committedDeclarationBatch
    :: ModuleName
    -> DeclarationSlot
    -> PrefixContextId
    -> PrefixContextId
    -> DeclarationInterfaceDelta
    -> [AssertedObject]
    -> [CheckedPropositionContent]
    -> [ProofValidationRecord]
    -> Maybe DeclarationValidationRecord
    -> CommittedDeclarationBatch
committedDeclarationBatch = CommittedDeclarationBatch

committedBatchOwner :: CommittedDeclarationBatch -> ModuleName
committedBatchOwner
        (CommittedDeclarationBatch owner _ _ _ _ _ _ _ _) =
    owner

committedBatchSlot
    :: CommittedDeclarationBatch
    -> DeclarationSlot
committedBatchSlot
        (CommittedDeclarationBatch _ slot _ _ _ _ _ _ _) =
    slot

committedBatchPreviousPrefix
    :: CommittedDeclarationBatch
    -> PrefixContextId
committedBatchPreviousPrefix
        (CommittedDeclarationBatch _ _ previous _ _ _ _ _ _) =
    previous

committedBatchNextPrefix
    :: CommittedDeclarationBatch
    -> PrefixContextId
committedBatchNextPrefix
        (CommittedDeclarationBatch _ _ _ next _ _ _ _ _) =
    next

committedBatchDelta
    :: CommittedDeclarationBatch
    -> DeclarationInterfaceDelta
committedBatchDelta
        (CommittedDeclarationBatch _ _ _ _ delta _ _ _ _) =
    delta

committedBatchObjects
    :: CommittedDeclarationBatch
    -> [AssertedObject]
committedBatchObjects
        (CommittedDeclarationBatch _ _ _ _ _ objects _ _ _) =
    objects

committedBatchPropositions
    :: CommittedDeclarationBatch
    -> [CheckedPropositionContent]
committedBatchPropositions
        (CommittedDeclarationBatch _ _ _ _ _ _ propositions _ _) =
    propositions

committedBatchProofValidations
    :: CommittedDeclarationBatch
    -> [ProofValidationRecord]
committedBatchProofValidations
        (CommittedDeclarationBatch _ _ _ _ _ _ _ validations _) =
    validations

committedBatchDeclarationValidation
    :: CommittedDeclarationBatch
    -> Maybe DeclarationValidationRecord
committedBatchDeclarationValidation
        (CommittedDeclarationBatch _ _ _ _ _ _ _ _ validation) =
    validation

committedBatchValidationCertificates
    :: CommittedDeclarationBatch
    -> [ValidationCertificate]
committedBatchValidationCertificates batch =
    ( proofValidationRecordCertificate
        <$> committedBatchProofValidations batch
    )
    <> maybe
        []
        declarationValidationRecordCertificates
        (committedBatchDeclarationValidation batch)


data PendingModulePrefix = PendingModulePrefix
    !PrefixContextId
    ![CommittedDeclarationBatch]

emptyPendingModulePrefix
    :: PrefixContextId
    -> PendingModulePrefix
emptyPendingModulePrefix prefix =
    PendingModulePrefix prefix []

instance Show PendingModulePrefix where
    show prefix =
        "PendingModulePrefix {pendingModulePrefixCurrent = "
            <> show (pendingModulePrefixCurrent prefix)
            <> ", pendingModulePrefixBatchCount = "
            <> show (length (pendingModulePrefixBatches prefix))
            <> "}"

pendingModulePrefixBatches
    :: PendingModulePrefix
    -> [CommittedDeclarationBatch]
pendingModulePrefixBatches
        (PendingModulePrefix _ batchesReversed) =
    reverse batchesReversed

pendingModulePrefixCurrent
    :: PendingModulePrefix
    -> PrefixContextId
pendingModulePrefixCurrent
        (PendingModulePrefix prefix _batches) =
    prefix

appendPendingBatch
    :: CommittedDeclarationBatch
    -> PendingModulePrefix
    -> PendingModulePrefix
appendPendingBatch batch (PendingModulePrefix _ batches) =
    forceCommittedBatch batch `seq`
        PendingModulePrefix
            (committedBatchNextPrefix batch)
            (batch : batches)

-- Force the canonical payload at the append boundary so a published prefix
-- cannot retain deferred declaration checking or serialization work.
forceCommittedBatch :: CommittedDeclarationBatch -> ()
forceCommittedBatch
        (CommittedDeclarationBatch
            owner slot previous next delta objects propositions
            proofValidations declarationValidation) =
    owner `seq`
    slot `seq`
    previous `seq`
    next `seq`
    ByteString.length
        (encodeCache (putDeclarationInterfaceDeltaCache delta)) `seq`
    objects `deepseq`
    propositions `deepseq`
    forceProofValidations proofValidations `seq`
    forceDeclarationValidation declarationValidation
  where
    forceProofValidations =
        foldl'
            (\() record ->
                proofValidationRecordKey record `seq`
                ByteString.length
                    (encodeCache
                        (putValidationCertificateCache
                            (proofValidationRecordCertificate
                                record))) `seq` ())
            ()

    forceDeclarationValidation = \case
        Nothing -> ()
        Just record ->
            declarationValidationRecordKey record `seq`
            foldl'
                (\() certificate ->
                    ByteString.length
                        (encodeCache
                            (putValidationCertificateCache
                                certificate)) `seq` ())
                ()
                (declarationValidationRecordCertificates record)
