{-# LANGUAGE NoImplicitPrelude #-}

-- | Preparation, lowering, and authorization of explicit source axioms.
module Felix.Checking.SourceAxiom
    ( PreparedSourceAxiom
    , prepareSourceAxiom
    , lowerPreparedSourceAxiom
    , authorizeCheckedSourceAxiom
    ) where

import Base
import Felix.Cache.Codec
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Identity
import Felix.Checking.Semantic
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw

import Control.Monad (unless)
import Data.ByteString (ByteString)


data PreparedSourceAxiom = PreparedSourceAxiom
    !Location
    !SemanticName
    !(ScopedCheckedCore ObjectId)
    !DeclarationSyntaxId

prepareSourceAxiom
    :: Raw.Block
    -> Declaration.LoweringDriver
        (Either Elaboration.ElaborationError PreparedSourceAxiom)
prepareSourceAxiom = \case
    Raw.BlockAxiom
            location _title (Raw.Marker marker)
            (Raw.Axiom assumptions statement) -> do
            prepared <- Elaboration.elaborateClaimEnvelope assumptions statement
            pure do
                envelope <- prepared
                let core = Elaboration.elaboratedClaimTarget envelope
                    alias = semanticName marker
                unless (null (scopedCoreContext core))
                    (Left (Elaboration.ElaborationUnsupportedDeclarationBody location))
                pure
                    (PreparedSourceAxiom
                        location
                        alias
                        core
                        (declarationSyntaxId
                            (encodePreparedSourceAxiom core alias)))
    block ->
        pure
            (Left
                (Elaboration.ElaborationUnsupportedDeclaration (locate block)))

lowerPreparedSourceAxiom
    :: PreparedSourceAxiom
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration ()))
lowerPreparedSourceAxiom
        (PreparedSourceAxiom _location alias target syntax) =
    fmap
        (\spec ->
            Declaration.checkedCompiledDeclaration
                syntax [] [] [] Nothing
                [ Declaration.checkedCandidate
                    spec
                    Declaration.checkedSourceAxiomPlanning
                    :| []
                ]
                ())
        <$> Declaration.prepareCandidateSpecLowering
            [] target SearchEligible [alias]

authorizeCheckedSourceAxiom
    :: ()
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedSourceAxiom () = \case
    [candidate :| []] ->
        Declaration.authorizeSourceAxiomCandidate candidate
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                1 (length stages))

encodePreparedSourceAxiom
    :: ScopedCheckedCore ObjectId
    -> SemanticName
    -> ByteString
encodePreparedSourceAxiom core alias =
    encodeCache do
        putCacheTag 0x03
        putCanonicalTermCache putObjectIdCache (scopedCoreTerm core)
        putCacheText (semanticNameText alias)
