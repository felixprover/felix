{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Package-internal representation of canonical definition associations.
--
-- The public semantic API deliberately exposes this type only abstractly.
-- Declaration sealing and semantic cache decoding are the two construction
-- boundaries; imported associations remain inert until Declaration validates
-- their declaration provenance and direct-authorization certificate.
module Felix.Checking.DefinitionView
    ( DefinitionViewKind(..)
    , DefinitionView
    , definitionView
    , definitionViewObject
    , definitionViewKind
    , definitionViewTarget
    ) where

import Base

import Control.DeepSeq (NFData)


data DefinitionViewKind
    = DefinitionPointwiseView
    | DefinitionExactView
    | DefinitionMembershipView
    deriving stock (Show, Eq, Ord, Enum, Bounded, Generic)
    deriving anyclass (NFData)

data DefinitionView object target = DefinitionView
    !object
    !DefinitionViewKind
    !target
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

definitionView
    :: object
    -> DefinitionViewKind
    -> target
    -> DefinitionView object target
definitionView =
    DefinitionView

definitionViewObject :: DefinitionView object target -> object
definitionViewObject (DefinitionView object _kind _target) =
    object

definitionViewKind
    :: DefinitionView object target
    -> DefinitionViewKind
definitionViewKind (DefinitionView _object kind _target) =
    kind

definitionViewTarget :: DefinitionView object target -> target
definitionViewTarget (DefinitionView _object _kind target) =
    target
