{-# LANGUAGE NoImplicitPrelude #-}

-- Fixtures declare their complete semantic inputs before executing proofs.
module Felix.Test.Support.Declarations (admitProof, admitCompiled) where

import Base
import Felix.Checking.Commit (CommittedDeclarationBatch)
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Identity (AssertedObject)
import Felix.Checking.Semantic (DeclarationSyntaxId, ProofSyntaxId, SemanticGlobalBinding)

admitProof
    :: ProofSyntaxId -> [AssertedObject] -> Declaration.CheckedCandidate
    -> (Declaration.ReservedCandidate -> Declaration.Declaration value)
    -> Declaration.ModuleDriver failure (value, CommittedDeclarationBatch)
admitProof syntax objects candidate authorize =
    Declaration.admitCheckedDeclaration
        (Declaration.checkedProofDeclaration syntax objects [] [] Nothing [candidate :| []] ())
        (\() -> \case
            [reserved :| []] -> authorize reserved
            _ -> impossible "a single-candidate proof fixture changed shape")

admitCompiled
    :: DeclarationSyntaxId -> [AssertedObject] -> [SemanticGlobalBinding]
    -> [NonEmpty Declaration.CheckedCandidate]
    -> ([NonEmpty Declaration.ReservedCandidate] -> Declaration.Declaration value)
    -> Declaration.ModuleDriver failure (value, CommittedDeclarationBatch)
admitCompiled syntax objects globals candidates authorize =
    Declaration.admitCheckedDeclaration
        (Declaration.checkedCompiledDeclaration syntax objects [] globals Nothing candidates ())
        (\() -> authorize)
