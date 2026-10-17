module InternalStructuralProofAuthorizationImport where

import Felix.Checking.Proof.Authorization.Internal
    ( StructuralProofAuthorization(..)
    )


unavailableAuthorization :: StructuralProofAuthorization ()
unavailableAuthorization = StructuralProofAuthorization ()
