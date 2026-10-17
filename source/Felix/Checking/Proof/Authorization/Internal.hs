{-# LANGUAGE RoleAnnotations #-}

-- | Package-private capability for structural source-proof authorization.
--
-- Only the checked proof owner may construct this capability.  Declaration
-- consumes it so that an arbitrary 'CandidateProof ()' cannot be promoted to
-- clean source-proof authority.
module Felix.Checking.Proof.Authorization.Internal
    ( StructuralProofAuthorization
    , structuralProofAuthorization
    , structuralProofAction
    ) where


type role StructuralProofAuthorization nominal
data StructuralProofAuthorization action =
    StructuralProofAuthorization action

structuralProofAuthorization
    :: action
    -> StructuralProofAuthorization action
structuralProofAuthorization =
    StructuralProofAuthorization

structuralProofAction
    :: StructuralProofAuthorization action
    -> action
structuralProofAction (StructuralProofAuthorization action) =
    action
