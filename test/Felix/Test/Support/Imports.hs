{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Support.Imports
    ( prepareTestImports
    , admitTestModule
    ) where

import Base
import Felix.Checking.Authority (ValidationCertificate)
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Core qualified as Core
import Felix.Math.Codec (encodeCanonicalTerm)
import Test.Tasty.HUnit (assertFailure, assertEqual)

prepareTestImports
    :: Identity.TheoryId
    -> [Declaration.ImportedModuleEvidence]
    -> IO Declaration.PreparedImports
prepareTestImports theory parents = do
    foundation <- either (fail . show) pure Foundation.checkedFoundation
    assertEqual "fixture theory matches the checked foundation" theory (Identity.theoryId foundation)
    check <- Declaration.newImportCheck foundation
    Declaration.prepareImports check parents >>= either
        (\failure -> assertFailure (show failure) >> fail "import fixture preparation failed")
        pure

-- Malformed-metadata fixtures retain genuine row-identity evidence and enter
-- through the same local admission boundary as decoded store candidates.
admitTestModule
    :: Identity.TheoryId
    -> [Declaration.ImportedModuleEvidence]
    -> Semantic.SemanticInterface
    -> [Identity.AssertedObject]
    -> [Identity.CheckedPropositionContent]
    -> [ValidationCertificate]
    -> IO (Either Declaration.DeclarationError Declaration.ImportedModuleEvidence)
admitTestModule theory parents interface objects propositions certificates = do
    foundation <- either (fail . show) pure Foundation.checkedFoundation
    assertEqual "fixture theory matches the checked foundation" theory (Identity.theoryId foundation)
    check <- Declaration.newImportCheck foundation
    prepared <- Declaration.prepareImports check parents
    case prepared of
        Left failure -> pure (Left failure)
        Right imports -> do
            candidates <- for propositions \proposition -> do
                reentered <- either
                    (\failure -> assertFailure (show failure) >> fail "invalid term fixture")
                    pure
                    (Identity.identifyAndReenterCanonicalTerm
                        (encodeCanonicalTerm Identity.objectIdBuilder
                            (Core.frozenCoreTerm (Identity.checkedPropositionTerm proposition))))
                case Identity.storedPropositionCandidate
                        (Identity.checkedPropositionId proposition)
                        reentered of
                    Left failure -> assertFailure (show failure) >> fail "invalid proposition fixture"
                    Right candidate -> pure candidate
            Declaration.admitCachedModuleEvidence imports interface objects candidates certificates
