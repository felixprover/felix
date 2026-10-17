module MatcherChecks (tests) where

import Base
import Felix.Checking.Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Obvious.Driver qualified as Driver
import Felix.Checking.Obvious.Template qualified as Template

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Focused beta-eta matcher"
    [ testCase "binds bare and eta slots before entering target lambdas" slotAssignments
    , testCase "compares mixed lambdas in their own checked contexts" mixedLambdas
    , testCase "rejects a target whose enclosing local would escape" localEscape
    , testCase "retains a failed lambda-spine scan across yields" failedSpine
    , testCase "reconstructs an eta-slot theorem at the exact beta-wrapped target" theoremInstance
    ]

function :: CoreType
function = TyArrow TySet TySet

eta :: Natural -> CanonicalTerm global
eta index = CLam TySet (CApp (CBound index) (CBound 0))

constant :: CanonicalTerm global
constant = CLam TySet (COpaqueInteger 5)

-- This calls the matcher directly, so a separate conversion or ground proof
-- route cannot hide a slot-assignment or cursor regression.
match
    :: [CoreType] -> [CoreType] -> CanonicalTerm Void -> CanonicalTerm Void
    -> IO (Driver.TemplateMatchResult Void, Natural)
match ambient slots patternTerm goalTerm = do
    foundation <- require Foundation.checkedFoundation
    context <- require (Proof.scopedProofContext foundation emptyGlobalTyping ambient [])
    let binders = foldl' (flip Template.extendBinderEnvironment)
            (Template.emptyBinderEnvironment ambient) slots
    template <- require (fst (Template.compileTemplate emptyGlobalTyping 2000000 binders patternTerm))
    target <- require (checkScopedCanonicalCore emptyGlobalTyping ambient goalTerm)
    let (result, _, _) = Driver.runScoped 2000000 (Conversion.conversionPool 2000000)
            (Driver.GroundAllowance 0 0 0 0 Driver.UniversalsDisabled) context Map.empty \scope ->
                Driver.scopeMatchTemplate scope template target
    require result

require :: Show failure => Either failure value -> IO value
require = either (\failure -> assertFailure (show failure) >> fail "unreachable") pure

slotAssignments :: Assertion
slotAssignments = for_ cases \(scenario, ambient, slotType, patternTerm, target, expected) -> do
    (result, _) <- match ambient [slotType] patternTerm target
    case result of
        Driver.TemplateMatched substitutions _ -> assertEqual scenario (Just expected)
            (scopedCoreTerm <$> Template.lookupTemplateSubstitution (Template.MatcherSlot 0) substitutions)
        _ -> assertFailure (scenario <> ": matcher did not produce the assignment")
  where
    curried = TyArrow TySet function
    curriedEta = CLam TySet (CLam TySet (CApp (CApp (CBound 2) (CBound 1)) (CBound 0)))
    curriedTarget = CLam TySet (CLam TySet (CBound 1))
    betaTarget = CApp (CLam function (CBound 0)) constant
    cases =
        [ ("bare slot", [], function, CBound 0, constant, constant)
        , ("eta slot", [], function, eta 1, constant, constant)
        , ("curried eta slot", [], curried, curriedEta, curriedTarget, curriedTarget)
        , ("intact beta target", [], function, eta 1, betaTarget, betaTarget)
        , ("beta-hidden pattern head", [], function,
            CApp (CLam function (eta 1)) (CBound 0), constant, constant)
        , ("valid inner suffix", [], function,
            CLam TyProp (eta 2), CLam TyProp constant, constant)
        , ("repeated beta-eta assignment", [function], function,
            CEq function (eta 1) (CBound 0), CEq function (eta 1) (CBound 0), eta 1)
        ]

mixedLambdas :: Assertion
mixedLambdas = for_ [(CBound 0, eta 1), (eta 1, CBound 0)] \(left, right) -> do
    (result, _) <- match [function] [] left right
    case result of
        Driver.TemplateMatched{} -> pure ()
        _ -> assertFailure "mixed lambda/neutral matching failed"

localEscape :: Assertion
localEscape = do
    (result, _) <- match [] [function]
        (CLam TySet (eta 2)) (CLam TySet (CLam TySet (CBound 1)))
    case result of
        Driver.TemplateHigherOrderUnsupported{} -> pure ()
        _ -> assertFailure "an eta-slot assignment captured an enclosing local"

failedSpine :: Assertion
failedSpine = do
    observations <- forM [160, 320, 640 :: Int] \size -> do
        let term = foldr (const (CLam TySet)) (COpaqueInteger 0) [1 .. size]
        (result, turns) <- match [] [function] term term
        case result of
            Driver.TemplateMatched _ progress -> pure (progress, turns)
            _ -> assertFailure "failed eta recognition prevented ordinary matching" >> fail "unreachable"
    case observations of
        [(small, _), (medium, _), (large, turns)] -> do
            assertBool "doubling the failed chain does not quadruple matcher work"
                (medium < 3 * small && large < 3 * medium)
            assertBool "the long scan actually crosses scheduler yields" (turns > 1)
        _ -> assertFailure "matcher scaling fixture changed arity"

theoremInstance :: Assertion
theoremInstance = do
    foundation <- require Foundation.checkedFoundation
    let types = [TyArrow function TyProp]
        source = CForall function (CApp (CBound 1) (eta 1)) :: CanonicalTerm Void
        written = CApp (CLam TyProp (CBound 0)) (CApp (CBound 0) constant)
    hypothesis <- require (checkScopedCanonicalCore emptyGlobalTyping types source)
    target <- require (checkScopedCanonicalCore emptyGlobalTyping types written)
    let report = Driver.obviousProofReport
            Driver.defaultObviousBudget {Driver.obviousRefutationWorkLimit = 0}
            Driver.AnyObviousProof foundation emptyGlobalTyping [hypothesis] [] [] target
    proof <- require (Driver.obviousRunResult report)
    replayed <- require (replayScopedKernelDerivation foundation defaultKernelReplayLimits
        emptyGlobalTyping Vector.empty (Vector.singleton hypothesis) target
        (Proof.builtProofDerivation (Driver.obviousBuiltProof proof)))
    assertEqual "the caller's exact beta-wrapped target is restored" target (replayedScopedKernelTarget replayed)
    assertEqual "the theorem instance actually consumes its supplied source"
        (Set.singleton (hypothesisIx 0)) (replayedScopedKernelExternalHypothesisUses replayed)
    assertEqual "no ground proof masks the matcher route" 0
        (Driver.obviousRefutationWorkConsumed (Driver.obviousRunStatistics report))
