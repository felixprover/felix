{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Pure applicability checks for later trusted materialization.
--
-- Successful checks are inert. Fresh completion and validated loading or
-- sealing own the runtime authority that may publish a fact.
module Felix.Checking.Materialization
    ( CandidateValidation
    , candidateProofValidation
    , candidateDeclarationValidation
    , checkDeclarationValidationRecord
    , checkCandidateValidation
    , checkImportedMembership
    , checkImportedOccurrence
    , MaterializationError(..)
    ) where

import Base
import Felix.Checking.Authority
import Felix.Checking.Identity
import Felix.Checking.Semantic

import Control.Monad (unless)
import Numeric.Natural (Natural)


data CandidateValidation
    = CandidateProofValidation
        !ProofValidationRecord
        !ProofSyntaxId
    | CandidateDeclarationValidation
        !DeclarationValidationRecord
        !DeclarationSyntaxId
        ![ObjectId]
        ![TheoremId]
        !Natural
    deriving stock (Show, Eq)

candidateProofValidation
    :: ProofValidationRecord
    -> ProofSyntaxId
    -> CandidateValidation
candidateProofValidation =
    CandidateProofValidation

candidateDeclarationValidation
    :: DeclarationValidationRecord
    -> DeclarationSyntaxId
    -> [ObjectId]
    -> [TheoremId]
    -> Natural
    -> CandidateValidation
candidateDeclarationValidation =
    CandidateDeclarationValidation

checkDeclarationValidationRecord
    :: PrefixContextId
    -> DeclarationSyntaxId
    -> [ObjectId]
    -> [TheoremId]
    -> DeclarationValidationRecord
    -> Either MaterializationError ()
checkDeclarationValidationRecord prefix syntax objects theorems record = do
    let suppliedKey =
            declarationValidationRecordKey record
        certificates =
            declarationValidationRecordCertificates record
        expectedKey =
            declarationValidationKey
                syntax prefix objects theorems
    unless
        (suppliedKey == expectedKey)
        (Left
            (DeclarationValidationKeyMismatch
                suppliedKey expectedKey))
    let certificateTheorems =
            theoremId
                . factAuthorityTheorem
                . validationTarget
                <$> certificates
    unless
        (certificateTheorems == theorems)
        (Left
            (DeclarationCertificateTargetsMismatch
                theorems certificateTheorems))

data MaterializationError
    = CandidateValidationIndexMissing !Natural
    | ProofValidationKeyMismatch
        !ProofValidationKey
        !ProofValidationKey
    | DeclarationValidationKeyMismatch
        !DeclarationValidationKey
        !DeclarationValidationKey
    | DeclarationCertificateTargetsMismatch
        ![TheoremId]
        ![TheoremId]
    | CandidateCertificateTargetMismatch
        !FactAuthority
        !FactAuthority
    | CandidateDirectAuthorizationMismatch
        !DirectAuthorization
        !DirectAuthorization
    | CandidateTheoryMismatch !TheoryId !TheoryId
    | CandidatePropositionMismatch
        !PropositionId
        !PropositionId
    | ImportedOccurrenceMissing
        !SemanticFactOccurrenceFingerprint
    | ImportedAuthorityMismatch
        !FactAuthority
        !FactAuthority
    | ImportedTheoryMismatch !TheoryId !TheoryId
    | ImportedPropositionMismatch
        !PropositionId
        !PropositionId
    deriving stock (Show, Eq)


-- | Check whether inert validation data applies to one exact candidate.
--
-- Success deliberately returns no builder authorization. A fresh trusted
-- completion or compatible validated-store hit must perform this check before
-- its owner mints runtime authority.
checkCandidateValidation
    :: TheoryId
    -> PrefixContextId
    -> CheckedPropositionContent
    -> FactAuthority
    -> DirectAuthorization
    -> CandidateValidation
    -> Either MaterializationError ()
checkCandidateValidation
        theory prefix proposition expectedAuthority
        expectedDirect validation = do
    certificate <-
        candidateCertificate
            prefix expectedAuthority validation
    validateCertificateTarget
        theory proposition expectedAuthority expectedDirect certificate

candidateCertificate
    :: PrefixContextId
    -> FactAuthority
    -> CandidateValidation
    -> Either MaterializationError ValidationCertificate
candidateCertificate prefix authority = \case
    CandidateProofValidation record syntax -> do
        let suppliedKey =
                proofValidationRecordKey record
            certificate =
                proofValidationRecordCertificate record
            expectedKey =
                proofValidationKey
                    (theoremId
                        (factAuthorityTheorem authority))
                    syntax
                    prefix
        unless
            (suppliedKey == expectedKey)
            (Left
                (ProofValidationKeyMismatch
                    suppliedKey expectedKey))
        pure certificate
    CandidateDeclarationValidation
            record syntax objects theorems ordinal -> do
        checkDeclarationValidationRecord
            prefix syntax objects theorems record
        maybe
            (Left (CandidateValidationIndexMissing ordinal))
            Right
            (nth ordinal
                (declarationValidationRecordCertificates record))

validateCertificateTarget
    :: TheoryId
    -> CheckedPropositionContent
    -> FactAuthority
    -> DirectAuthorization
    -> ValidationCertificate
    -> Either MaterializationError ()
validateCertificateTarget
        theory proposition expectedAuthority expectedDirect certificate = do
    let actualAuthority =
            validationTarget certificate
        actualDirect =
            validationDirectAuthorization certificate
        reference =
            factAuthorityTheorem actualAuthority
    unless
        (actualAuthority == expectedAuthority)
        (Left
            (CandidateCertificateTargetMismatch
                expectedAuthority actualAuthority))
    unless
        (actualDirect == expectedDirect)
        (Left
            (CandidateDirectAuthorizationMismatch
                expectedDirect actualDirect))
    unless
        (theoremRefTheory reference == theory)
        (Left
            (CandidateTheoryMismatch
                theory
                (theoremRefTheory reference)))
    unless
        ( theoremRefProposition reference
            == checkedPropositionId proposition
        )
        (Left
            (CandidatePropositionMismatch
                (checkedPropositionId proposition)
                (theoremRefProposition reference)))


-- | Validate exact membership in inert canonical interface data.
--
-- Logical sealing or atomic cached installation must additionally supply the
-- opaque runtime evidence before an importer receives builder authority.
checkImportedMembership
    :: TheoryId
    -> SemanticInterface
    -> SemanticFactOccurrenceFingerprint
    -> CheckedPropositionContent
    -> FactAuthority
    -> Either MaterializationError SemanticFactOccurrence
checkImportedMembership
        theory interface fingerprint proposition expectedAuthority = do
    occurrence <-
        maybe
            (Left (ImportedOccurrenceMissing fingerprint))
            Right
            (find
                ((== fingerprint) . semanticFactFingerprint)
                (concatMap
                    declarationDeltaFacts
                    (semanticInterfaceDeclarations interface)))
    checkImportedOccurrence
        theory fingerprint occurrence proposition expectedAuthority

checkImportedOccurrence
    :: TheoryId
    -> SemanticFactOccurrenceFingerprint
    -> SemanticFactOccurrence
    -> CheckedPropositionContent
    -> FactAuthority
    -> Either MaterializationError SemanticFactOccurrence
checkImportedOccurrence
        theory fingerprint occurrence proposition expectedAuthority = do
    unless
        (semanticFactFingerprint occurrence == fingerprint)
        (Left (ImportedOccurrenceMissing fingerprint))
    let actualAuthority =
            semanticFactAuthority occurrence
        reference =
            factAuthorityTheorem actualAuthority
    unless
        (actualAuthority == expectedAuthority)
        (Left
            (ImportedAuthorityMismatch
                expectedAuthority actualAuthority))
    unless
        (theoremRefTheory reference == theory)
        (Left
            (ImportedTheoryMismatch
                theory
                (theoremRefTheory reference)))
    unless
        (theoremRefProposition reference
            == checkedPropositionId proposition)
        (Left
            (ImportedPropositionMismatch
                (checkedPropositionId proposition)
                (theoremRefProposition reference)))
    pure occurrence
