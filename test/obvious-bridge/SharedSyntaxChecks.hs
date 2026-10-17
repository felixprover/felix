module SharedSyntaxChecks (tests) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Obvious.LogicalView qualified as Logical
import Felix.Checking.Obvious.Driver qualified as Driver
import Felix.Checking.Obvious.Refutation qualified as Ground
import Felix.Checking.Obvious.Template qualified as Template

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Shared directional syntax"
    [ testCase "keeps parent syntax exact and reuses real goal and hypothesis operands" directionalViews
    , testCase "first directional startup reuses paid seed, body, and indexed hypothesis views" firstDirectionalStartup
    ]

require :: Show failure => Either failure value -> IO value
require = either (\failure -> assertFailure (show failure) >> fail "unreachable") pure

firstDirectionalStartup :: Assertion
firstDirectionalStartup = do
    foundation <- require Foundation.checkedFoundation
    let types = [TyProp, TyProp]
        checked = require . checkScopedCanonicalCore emptyGlobalTyping types
        beta term = CApp (CLam TyProp (CBound 0)) term
    for_ [(0 :: Int, 0), (40, 926)] \(depth, expectedCost) -> do
        left <- checked (foldr (const beta) (CBound 0) [1 .. depth])
        right <- checked (foldr (const beta) (CBound 1) [1 .. depth])
        context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [right])
        let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
                (Driver.GroundAllowance 2000000 1000 100 100 Driver.UniversalsDisabled) context Map.empty \scope ->
                    Driver.scopeDirectionalGroundProof scope left right
        (proof, cost) <- require result
        -- Count after the entry has paid for its pair. The old first-start
        -- handoff repeats head preparation and consumes 4,544 at depth 40.
        assertEqual "query work retains the paid preparation" expectedCost cost
        replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
            Vector.empty (Vector.fromList [left, right]) right (Proof.builtProofDerivation proof))
        assertEqual "real body target" right (replayedScopedKernelTarget replayed)
        assertEqual "the retained operand uses its actual hypothesis index" (Set.singleton (hypothesisIx 1))
            (replayedScopedKernelExternalHypothesisUses replayed)

limits :: Ground.RefutationLimits
limits = Ground.RefutationLimits 2000000 (Conversion.conversionPool 2000000) 10000 256 1000 True True Ground.UniversalsDisabled

freeze
    :: Ground.RefutationLimits -> Ground.RefutationSession Void -> IO (Ground.FrozenDomain Void)
freeze = go (0 :: Int)
  where
    go turns available session = do
        assertBool "preparation terminates" (turns < 2000)
        case Ground.refutationSessionDomain session of
            Just domain -> pure domain
            Nothing -> case Ground.advanceRefutation available session of
                (remaining, Ground.RefutationPending next) -> go (turns + 1) remaining next
                _ -> assertFailure "a domain was not frozen" >> fail "unreachable"

finish
    :: Ground.RefutationLimits -> Ground.RefutationSession Void
    -> IO (Ground.RefutationLimits, Either Ground.RefutationFailure (Ground.RefutationCandidate Void))
finish = go (0 :: Int)
  where
    go turns available session = do
        assertBool "query terminates" (turns < 2000)
        case Ground.advanceRefutation available session of
            (remaining, Ground.RefutationPending next) -> go (turns + 1) remaining next
            (remaining, Ground.RefutationBlocked _ failure _) -> pure (remaining, Left failure)
            (remaining, Ground.RefutationFinished _ result) -> pure (remaining, result)

directionalViews :: Assertion
directionalViews = do
    foundation <- require Foundation.checkedFoundation
    let types = [TySet, TyArrow TySet TyProp, TyArrow TySet TySet]
        checked = require . checkScopedCanonicalCore emptyGlobalTyping types
        reduced = CApp (CBound 1) (CApp (CBound 2) (CBound 0))
        beta term = CApp (CLam TyProp (CBound 0)) term
        original = foldr (const beta) reduced [1 .. 40 :: Int]
    left <- checked original
    right <- checked reduced
    forward <- checked (CImp original reduced)
    backward <- checked (CImp reduced original)
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [])
    let (afterLeft, preparedLeft) = Ground.prepareGroundSyntax limits emptyGlobalTyping context left
    leftView <- require preparedLeft
    let (afterRight, preparedRight) = Ground.prepareGroundSyntax afterLeft emptyGlobalTyping context right
    rightView <- require preparedRight
    let (afterForward, preparedForward) = Ground.assembleGroundImplication afterRight emptyGlobalTyping context forward leftView rightView
    forwardView <- require preparedForward
    let (afterBackward, preparedBackward) = Ground.assembleGroundImplication afterForward emptyGlobalTyping context backward rightView leftView
    backwardView <- require preparedBackward
    assertEqual "the parent's original is the exact written implication" forward
        (Template.compiledTemplateTerm (Logical.logicalViewOriginalTemplate forwardView))
    assertEqual "the parent's residual is not assembled from child residuals" forward
        (Template.compiledTemplateTerm (Logical.logicalViewResidualTemplate forwardView))
    assertBool "there is no invented parent head conversion" (isNothing (Logical.logicalViewHeadResidualization forwardView))
    assertBool "the child's real conversion is retained" (isJust (Logical.logicalViewHeadResidualization leftView))
    assertBool "reversed operands cannot be attached to the same written implication"
        (isLeft (snd (Ground.assembleGroundImplication afterRight emptyGlobalTyping context forward rightView leftView)))
    let views = [leftView, rightView, forwardView, backwardView]
    domain <- freeze afterBackward (Ground.startRefutationFromSeedWithViews afterBackward emptyGlobalTyping context views
        (forward :| [backward]) [] left)
    assertEqual "prepared directions fit the selected frozen domain" (Right True)
        (snd (Ground.groundSyntaxFits limits emptyGlobalTyping context domain [forwardView, backwardView]))
    for_ [(left, right), (right, left)] \(hypothesis, target) -> do
        owner <- require (Proof.scopedProofContext foundation emptyGlobalTyping types [hypothesis])
        let inputs = [Ground.RefutationHypothesis 0 hypothesis]
        (paid, result) <- finish limits (Ground.startRefutationInDomainWithViews limits emptyGlobalTyping owner views domain inputs target)
        proof <- Ground.refutationCandidateProof <$> require result
        (unshared, ordinary) <- finish limits (Ground.startRefutationInDomain limits emptyGlobalTyping owner domain inputs target)
        _ <- require ordinary
        assertBool "actual goal/hypothesis preparation reuses the operand, not only unused seed roots"
            (Conversion.conversionPoolAmount (Ground.refutationConversionPool paid)
                > Conversion.conversionPoolAmount (Ground.refutationConversionPool unshared))
        replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits emptyGlobalTyping
            Vector.empty (Vector.singleton hypothesis) target (Proof.builtProofDerivation proof))
        assertEqual "the exact query target is independently replayed" target (replayedScopedKernelTarget replayed)
        assertEqual "the actual hypothesis index is consumed" (Set.singleton (hypothesisIx 0))
            (replayedScopedKernelExternalHypothesisUses replayed)
    (_, withoutEvidence) <- finish limits
        (Ground.startRefutationInDomainWithViews limits emptyGlobalTyping context views domain [] left)
    assertBool "prepared seeds do not assert either direction or operand" (isLeft withoutEvidence)
