{-# LANGUAGE NoImplicitPrelude #-}
module Felix.Test.Unit.Location (unitTests) where

import Base
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.List qualified as List
import Data.Maybe (catMaybes)
import Felix.Report.Location
import System.Mem (performGC)
import System.Mem.Weak (Weak, deRefWeak, mkWeakPtr)
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Source locations"
    [ testCase "checks coordinate bounds without a reserved packed sentinel" checkedCoordinates
    , testCase "orders physical sources independently of construction timing" stableSourceOrder
    , testCase "releases descriptors across more than 65535 sessions" descriptorLifetime
    ]

checkedCoordinates :: Assertion
checkedCoordinates = do
    let source = sourceDescriptorForPath "coordinates.tex"
    for_ [source, anonymousSourceDescriptor] \descriptor -> do
        for_ [(0, 0), (1, 1), (0xffffff, 0xffffff)] \(line, column) -> do
            location <- either (assertFailure . show) pure (mkLocationChecked descriptor line column)
            locSourceDescriptor location @?= Just descriptor
            locLine location @?= line
            locColumn location @?= column
            assertBool "a valid location is not Nowhere" (location /= Nowhere)
        for_ [(-1, 0), (0, -1), (0x1000000, 1), (1, 0x1000000), (maxBound, 1)] \(line, column) ->
            mkLocationChecked descriptor line column
                @?= Left (LocationCoordinateOutOfRange line column)
    locSourceDescriptor Nowhere @?= Nothing
    locLine Nowhere @?= -1
    locColumn Nowhere @?= -1
    sourceDescriptor "<anonymous>" "<anonymous>" @?= anonymousSourceDescriptor
    sourceDescriptorIdentityPath anonymousSourceDescriptor @?= Nothing
    locFile (mkLocation anonymousSourceDescriptor 1 1) @?= "<anonymous>"

stableSourceOrder :: Assertion
stableSourceOrder = do
    let z = sourceDescriptor "/physical/z" "same.tex"
        a = sourceDescriptor "/physical/a" "same.tex"
        renamedA = sourceDescriptor "/physical/a" "other.tex"
        expected = [mkLocation anonymousSourceDescriptor 1 1,
            mkLocation renamedA 2 3, mkLocation a 1 1, mkLocation a 1 2,
            mkLocation z 1 1, Nowhere]
    for_ (List.permutations expected) \order -> List.sort order @?= expected
    for_ expected \left -> for_ expected \right ->
        (compare left right == EQ) @?= (left == right)
    let aAgain = sourceDescriptor "/physical/a" "same.tex"
    aAgain @?= a
    hash (mkLocation aAgain 1 1) @?= hash (mkLocation a 1 1)
    assertBool "same display does not merge physical sources" (a /= z)
    assertBool "same physical source retains independent presentation" (a /= renamedA)

unusedDescriptor :: Int -> IO (Weak SourceDescriptor)
unusedDescriptor index = do
    descriptor <- evaluate (force (sourceDescriptor
        ("/virtual/session/" <> show index) "session.tex"))
    mkWeakPtr descriptor Nothing
{-# NOINLINE unusedDescriptor #-}

retainedDiagnostic :: IO (Weak SourceDescriptor, Location)
retainedDiagnostic = do
    descriptor <- evaluate (force (sourceDescriptor "/virtual/retained" "retained.tex"))
    weak <- mkWeakPtr descriptor Nothing
    pure (weak, mkLocation descriptor 7 9)
{-# NOINLINE retainedDiagnostic #-}

descriptorLifetime :: Assertion
descriptorLifetime = do
    (retained, diagnostic) <- retainedDiagnostic
    unused <- traverse unusedDescriptor [1 .. 70000]
    performGC
    remaining <- catMaybes <$> traverse deRefWeak unused
    length remaining @?= 0
    retainedSource <- deRefWeak retained
    retainedSource @?= locSourceDescriptor diagnostic
    assertBool "the diagnostic keeps its own descriptor alive" (isJust retainedSource)
    locFile diagnostic @?= "retained.tex"
    (locLine diagnostic, locColumn diagnostic) @?= (7, 9)
    -- Anonymous construction does not allocate from or consult session history.
    mkLocation anonymousSourceDescriptor 3 4
        @?= either (error . show) id (mkLocationChecked anonymousSourceDescriptor 3 4)
