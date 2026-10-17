{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Materialization (unitTests) where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Materialization qualified as Materialization
import Felix.Checking.Semantic qualified as Semantic
import Felix.Math.Codec
import Felix.Module
import Felix.Source

import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Validation applicability"
        [ testCase "keeps serializable candidate validation inert"
            keepsCandidateValidationInert
        , testCase "rejects inexact candidate validation"
            rejectsInexactCandidateValidation
        , testCase "rejects mismatched candidate fields"
            rejectsMismatchedCandidateFields
        , testCase "selects ordered declaration certificates"
            selectsDeclarationCertificate
        , testCase "keeps raw interface membership inert"
            keepsImportedMembershipInert
        ]

keepsCandidateValidationInert :: Assertion
keepsCandidateValidationInert = do
    fixture <- makeFixture
    let check =
            Materialization.checkCandidateValidation
                (fixtureTheory fixture)
                (fixturePrefix fixture)
                (fixtureProposition fixture)
                (fixtureAuthority fixture)
                (fixtureDirect fixture)
                (fixtureProofValidation fixture)
    assertEqual
        "freely constructed records yield only inert applicability"
        (Right ())
        check
    assertEqual
        "inert applicability data is reusable"
        (Right ())
        check

rejectsInexactCandidateValidation :: Assertion
rejectsInexactCandidateValidation = do
    fixture <- makeFixture
    let wrongKey =
            Semantic.proofValidationKey
                (Identity.theoremId
                    (fixtureReference fixture))
                (Semantic.proofSyntaxId "other-proof")
                (fixturePrefix fixture)
        wrongValidation =
            Materialization.candidateProofValidation
                (Semantic.proofValidationRecord
                    wrongKey
                    (fixtureCertificate fixture))
                (Semantic.proofSyntaxId "proof")
    case Materialization.checkCandidateValidation
            (fixtureTheory fixture)
            (fixturePrefix fixture)
            (fixtureProposition fixture)
            (fixtureAuthority fixture)
            (fixtureDirect fixture)
            wrongValidation of
        Left Materialization.ProofValidationKeyMismatch{} ->
            pure ()
        Left other ->
            assertFailure
                ("unexpected validation-key error: " <> show other)
        Right _ ->
            assertFailure "inexact proof validation key succeeded"

rejectsMismatchedCandidateFields :: Assertion
rejectsMismatchedCandidateFields = do
    fixture <- makeFixture
    let sourceAuthority =
            Authority.factAuthority
                (fixtureReference fixture)
                (Authority.authoritySafety
                    (Authority.singletonEscapeKind
                        Authority.SourceAxiom))
    sourceCertificate <- expectRight
        (Authority.validationCertificate
            sourceAuthority
            Authority.SourceAxiomAuthorization)
    let key =
            Semantic.proofValidationKey
                (Identity.theoremId (fixtureReference fixture))
                (Semantic.proofSyntaxId "proof")
                (fixturePrefix fixture)
        sourceValidation =
            Materialization.candidateProofValidation
                (Semantic.proofValidationRecord
                    key
                    sourceCertificate)
                (Semantic.proofSyntaxId "proof")
    case Materialization.checkCandidateValidation
            (fixtureTheory fixture)
            (fixturePrefix fixture)
            (fixtureProposition fixture)
            (fixtureAuthority fixture)
            (fixtureDirect fixture)
            sourceValidation of
        Left Materialization.CandidateCertificateTargetMismatch{} ->
            pure ()
        Left other ->
            assertFailure
                ("unexpected target mismatch: " <> show other)
        Right _ ->
            assertFailure "mismatched safety was accepted"
    differentDirect <- expectRight
        (Authority.validationCertificate
            (fixtureAuthority fixture)
            (Authority.CheckedSourceProof
                (Authority.UsesExternalProof
                    (Authority.preparedRequestId
                        Authority.PreparedRequestFof
                        Authority.PreparedRequestDirect
                        "different-request" :| []))))
    let directValidation =
            Materialization.candidateProofValidation
                (Semantic.proofValidationRecord
                    key
                    differentDirect)
                (Semantic.proofSyntaxId "proof")
    case Materialization.checkCandidateValidation
            (fixtureTheory fixture)
            (fixturePrefix fixture)
            (fixtureProposition fixture)
            (fixtureAuthority fixture)
            (fixtureDirect fixture)
            directValidation of
        Left Materialization.CandidateDirectAuthorizationMismatch{} ->
            pure ()
        Left other ->
            assertFailure
                ("unexpected direct-authorization mismatch: "
                    <> show other)
        Right _ ->
            assertFailure "mismatched request list was accepted"
    closure <- expectRight
        (Identity.validateObjectClosure
            (fixtureTheory fixture)
            [])
    otherProposition <- expectRight
        (Identity.validatePropositionContent
            closure
            (Core.CImp Core.CFalsum Core.CFalsum))
    case Materialization.checkCandidateValidation
            (fixtureTheory fixture)
            (fixturePrefix fixture)
            otherProposition
            (fixtureAuthority fixture)
            (fixtureDirect fixture)
            (fixtureProofValidation fixture) of
        Left Materialization.CandidatePropositionMismatch{} ->
            pure ()
        Left other ->
            assertFailure
                ("unexpected proposition mismatch: " <> show other)
        Right _ ->
            assertFailure "mismatched proposition content was accepted"

selectsDeclarationCertificate :: Assertion
selectsDeclarationCertificate = do
    fixture <- makeFixture
    let sourceAuthority =
            Authority.factAuthority
                (fixtureReference fixture)
                (Authority.authoritySafety
                    (Authority.singletonEscapeKind
                        Authority.SourceAxiom))
    sourceCertificate <- expectRight
        (Authority.validationCertificate
            sourceAuthority
            Authority.SourceAxiomAuthorization)
    let syntax =
            Semantic.declarationSyntaxId "declaration"
        producedTheorems =
            [ Identity.theoremId
                (fixtureReference fixture)
            , Identity.theoremId
                (fixtureReference fixture)
            ]
        key =
            Semantic.declarationValidationKey
                syntax
                (fixturePrefix fixture)
                []
                producedTheorems
        validation =
            Materialization.candidateDeclarationValidation
                (Semantic.declarationValidationRecord
                    key
                    [sourceCertificate, fixtureCertificate fixture])
                syntax []
                producedTheorems
                1
    assertEqual
        "candidate ordinal selects the second certificate"
        (Right ())
        (Materialization.checkCandidateValidation
            (fixtureTheory fixture)
            (fixturePrefix fixture)
            (fixtureProposition fixture)
            (fixtureAuthority fixture)
            (fixtureDirect fixture)
            validation)

keepsImportedMembershipInert :: Assertion
keepsImportedMembershipInert = do
    fixture <- makeFixture
    occurrence <- expectRight
        (Materialization.checkImportedMembership
            (fixtureTheory fixture)
            (fixtureInterface fixture)
            (fixtureFingerprint fixture)
            (fixtureProposition fixture)
            (fixtureAuthority fixture))
    assertEqual
        "raw interface yields only its inert occurrence"
        (fixtureAuthority fixture)
        (Semantic.semanticFactAuthority occurrence)
    let wrongAuthority =
            Authority.factAuthority
                (fixtureReference fixture)
                (Authority.authoritySafety
                    (Authority.singletonEscapeKind
                        Authority.Omitted))
    case Materialization.checkImportedMembership
            (fixtureTheory fixture)
            (fixtureInterface fixture)
            (fixtureFingerprint fixture)
            (fixtureProposition fixture)
            wrongAuthority of
        Left Materialization.ImportedAuthorityMismatch{} ->
            pure ()
        Left other ->
            assertFailure
                ("unexpected imported-authority error: " <> show other)
        Right _ ->
            assertFailure "imported authority mismatch succeeded"


data Fixture = Fixture
    { fixtureTheory :: !Identity.TheoryId
    , fixtureReference :: !Identity.TheoremRef
    , fixtureProposition :: !Identity.CheckedPropositionContent
    , fixtureAuthority :: !Authority.FactAuthority
    , fixtureDirect :: !Authority.DirectAuthorization
    , fixtureCertificate :: !Authority.ValidationCertificate
    , fixtureFingerprint
        :: !Semantic.SemanticFactOccurrenceFingerprint
    , fixtureInterface :: !Semantic.SemanticInterface
    , fixturePrefix :: !Semantic.PrefixContextId
    , fixtureProofValidation
        :: !Materialization.CandidateValidation
    }

makeFixture :: IO Fixture
makeFixture = do
    foundation <- expectRight Foundation.checkedFoundation
    let namespaceDigest =
            hashBlake2b256 "materialization-test-namespace\NULroot"
    relative <- expectRight (safeRelativePath "producer.tex")
    let theory =
            Identity.theoryId foundation
        owner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest namespaceDigest)
                relative
    closure <- expectRight
        (Identity.validateObjectClosure theory [])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure Core.CFalsum)
    let reference =
            Identity.theoremRef
                theory
                (Identity.checkedPropositionId proposition)
        authority =
            Authority.factAuthority
                reference
                Authority.cleanAuthoritySafety
        direct =
            Authority.CheckedSourceProof Authority.NoExternalProofUse
        slot =
            Semantic.factSlot owner (localFactOrdinal 0)
        fingerprint =
            Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
                slot authority
        occurrence =
            Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
                slot
                authority
                Semantic.SearchEligible
        declaration =
            Semantic.declarationSlot
                owner
                (localDeclarationOrdinal 0)
    certificate <- expectRight
        (Authority.validationCertificate authority direct)
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            declaration
            [occurrence]
            []
            []
            [Identity.checkedPropositionId proposition]
            []
            []
            Semantic.emptySemanticEnvironmentDelta)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    prefix <- expectRight
        (Semantic.initialPrefixContextId theory owner [])
    let syntax =
            Semantic.proofSyntaxId "proof"
        key =
            Semantic.proofValidationKey
                (Identity.theoremId reference)
                syntax prefix
    pure
        Fixture
            { fixtureTheory = theory
            , fixtureReference = reference
            , fixtureProposition = proposition
            , fixtureAuthority = authority
            , fixtureDirect = direct
            , fixtureCertificate = certificate
            , fixtureFingerprint = fingerprint
            , fixtureInterface = interface
            , fixturePrefix = prefix
            , fixtureProofValidation =
                Materialization.candidateProofValidation
                    (Semantic.proofValidationRecord
                        key certificate)
                    syntax
            }

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err ->
        assertFailure (show err) >> fail "unreachable"
    Right value ->
        pure value
