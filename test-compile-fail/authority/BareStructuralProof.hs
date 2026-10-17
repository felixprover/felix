module BareStructuralProof where

import Felix.Checking.Declaration qualified as Declaration


authorizeWithoutOwner
    :: Declaration.ReservedCandidate
    -> Declaration.CandidateProof ()
    -> Declaration.Declaration ()
authorizeWithoutOwner candidate proof =
    Declaration.authorizeStructuralSourceProofCandidate
        candidate
        proof
