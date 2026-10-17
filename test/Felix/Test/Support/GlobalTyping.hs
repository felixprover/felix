{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Production-owned global-typing fixtures for checked-ingress tests.
module Felix.Test.Support.GlobalTyping
    ( GlobalTypingFixture
    , globalTypingFixture
    , fixtureGlobalTyping
    , fixtureObjectIds
    , fixtureObjectClosure
    ) where

import Base
import Felix.Checking.Core (CoreType)
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity qualified as Identity
import Felix.Math.Codec (hashBlake2b256)
import Felix.Module
import Felix.Source (safeRelativePath)


data GlobalTypingFixture = GlobalTypingFixture
    { fixtureGlobalTyping :: !(GlobalTyping Identity.ObjectId)
    , fixtureObjectIds :: ![Identity.ObjectId]
    , fixtureObjectClosure :: !Identity.CheckedObjectClosure
    }

-- | Build opaque test globals through the same validated closure owner used in
-- production.  The list order is preserved in 'fixtureObjectIds'.
globalTypingFixture :: [CoreType] -> GlobalTypingFixture
globalTypingFixture coreTypes =
    GlobalTypingFixture
        { fixtureGlobalTyping =
            Identity.globalTypingFromClosure closure
        , fixtureObjectIds = Identity.assertedObjectId <$> objects
        , fixtureObjectClosure = closure
        }
  where
    foundation = expectRight Foundation.checkedFoundation
    theory = Identity.theoryId foundation
    owner =
        moduleNameFromParts
            (sourceNamespaceIdFromDigest
                (hashBlake2b256 "global-typing-test-fixture"))
            (expectRight (safeRelativePath "global-typing-fixture.tex"))
    objects =
        [ Identity.opaqueObject
            theory
            (Identity.opaqueDeclarationSeed
                owner
                (localDeclarationOrdinal ordinal)
                SignatureDeclaration
                (generatedObjectSlot 0))
            coreType
        | (ordinal, coreType) <- zip [0 ..] coreTypes
        ]
    closure =
        expectRight
            (Identity.validateObjectClosure theory objects)

    expectRight :: Show error => Either error value -> value
    expectRight = either (error . show) id
