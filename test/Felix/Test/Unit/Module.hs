{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Module (fastTests, acceptanceTests) where

import Base
import Felix.Test.Unit.Module.Cache qualified as Cache
import Felix.Test.Unit.Module.Checking qualified as Checking
import Felix.Test.Unit.Module.Notion qualified as Notion
import Felix.Test.Unit.Module.Reconstruction qualified as Reconstruction
import Felix.Test.Unit.Module.RecordPresentation qualified as RecordPresentation
import Felix.Test.Unit.Module.Scheduling qualified as Scheduling

import Test.Tasty


fastTests :: TestTree
fastTests =
    testGroup
        "Typed module inputs"
        ( Checking.fastTests
            <> Notion.fastTests
            <> Reconstruction.tests
            <> RecordPresentation.tests
            <> Scheduling.tests
            <> Cache.tests
        )

acceptanceTests :: TestTree
acceptanceTests =
    testGroup
        "Typed module acceptance"
        (Checking.acceptanceTests <> Notion.acceptanceTests)
