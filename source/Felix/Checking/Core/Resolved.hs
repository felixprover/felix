{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}

-- | Safe, pure stable-local construction of checked Core terms.
module Felix.Checking.Core.Resolved
    ( CoreBuilder
    , CoreBuilderError(..)
    , LocalRef
    , localRefType
    , CheckedExpr
    , checkedExprType
    , runClosedBuilder
    , runClosedBuilderVoid
    , useLocal
    , useGlobal
    , embedClosed
    , intrinsic
    , apply
    , lambda
    , falsum
    , negation
    , conjunction
    , disjunction
    , forAll
    , exists
    , imply
    , equality
    ) where

import Base
import Felix.Checking.Core (FrozenCheckedCore)
import Felix.Checking.Core.Resolved.Internal
    ( CheckedExpr
    , CoreBuilder
    , CoreBuilderError(..)
    , LocalRef
    , checkedExprType
    , localRefType
    , runClosedBuilder
    , useLocal
    , useGlobal
    , embedClosed
    , intrinsic
    , apply
    , lambda
    , falsum
    , negation
    , conjunction
    , disjunction
    , forAll
    , exists
    , imply
    , equality
    )
import Felix.Checking.GlobalTyping (emptyGlobalTyping)

runClosedBuilderVoid
    :: (forall region.
            CoreBuilder region Void
                (CheckedExpr region Void))
    -> Either
        (CoreBuilderError Void)
        (FrozenCheckedCore Void)
runClosedBuilderVoid =
    runClosedBuilder emptyGlobalTyping
