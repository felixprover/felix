{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact validation reuse selected by the checker invocation boundary.
module Felix.Checking.ValidationCache
    ( ValidationCache
    , lookupProofValidation
    , lookupDeclarationValidation
    , runValidationCacheWith
    , runValidationCacheAlwaysMiss
    ) where

import Base
import Felix.Checking.Semantic

import Effectful
    ( Dispatch(Dynamic)
    , DispatchOf
    , Eff
    , Effect
    , (:>)
    )
import Effectful.Dispatch.Dynamic (interpret, send)


data ValidationCache :: Effect where
    LookupProofValidation
        :: !ProofValidationKey
        -> ValidationCache m (Maybe ProofValidationRecord)
    LookupDeclarationValidation
        :: !DeclarationValidationKey
        -> ValidationCache m (Maybe DeclarationValidationRecord)

type instance DispatchOf ValidationCache = Dynamic

lookupProofValidation
    :: ValidationCache :> es
    => ProofValidationKey
    -> Eff es (Maybe ProofValidationRecord)
lookupProofValidation key =
    send (LookupProofValidation key)

lookupDeclarationValidation
    :: ValidationCache :> es
    => DeclarationValidationKey
    -> Eff es (Maybe DeclarationValidationRecord)
lookupDeclarationValidation key =
    send (LookupDeclarationValidation key)

runValidationCacheWith
    :: (ProofValidationKey
            -> Eff es (Maybe ProofValidationRecord))
    -> (DeclarationValidationKey
            -> Eff es (Maybe DeclarationValidationRecord))
    -> Eff (ValidationCache : es) value
    -> Eff es value
runValidationCacheWith lookupProof lookupDeclaration =
    interpret \_environment -> \case
        LookupProofValidation key -> lookupProof key
        LookupDeclarationValidation key -> lookupDeclaration key

runValidationCacheAlwaysMiss
    :: Eff (ValidationCache : es) value
    -> Eff es value
runValidationCacheAlwaysMiss =
    runValidationCacheWith (const (pure Nothing)) (const (pure Nothing))
