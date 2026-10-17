{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Support.KernelSemanticsVectors (ruleVectors) where

import Base hiding (Empty)
import Felix.Checking.Kernel.Semantics (KernelSemanticsError(..))
import Test.Tasty.HUnit
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (emptyGlobalTyping)
import Felix.Checking.Kernel.Semantics qualified as S
import Data.Word (Word)

checked :: [CoreType] -> CanonicalTerm Void -> ScopedCheckedCore Void
checked context = either (error . show) id . checkScopedCanonicalCore emptyGlobalTyping context
-- Frozen before rule unification; neither runner supplies the expected answer.
ruleVectors :: Assertion
ruleVectors = do
    observations <- for cases \(name, ordinary, counted) -> do
        let (result, remaining) = counted 10000
            used = 10000 - remaining
        assertBool (name <> ": a rule spends structural work") (used > 0)
        assertEqual (name <> ": exact allowance") (result, 0) (counted used)
        assertEqual (name <> ": retained surplus") (result, 3) (counted (used + 3))
        for_ [0 .. used - 1] \work ->
            assertEqual (name <> ": every partial expenditure")
                (Left CountedCoreStructuralWorkExhausted, 0) (counted work)
        pure (name, view <$> ordinary, view <$> result, used)
    assertEqual "logical results, contexts, error precedence and charged work" expected observations
  where
    view value = (scopedCoreContext value, scopedCoreType value, scopedCoreTerm value)
    expected =
        [ ("truth",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),1)
        , ("negation intro",Right ([],TyProp,CNot CTruth),Right ([],TyProp,CNot CTruth),5)
        , ("negation intro failure",Left KernelExpectedFalsum,Left (CountedCoreOperationFailed KernelExpectedFalsum),2)
        , ("negation elim",Right ([],TyProp,CFalsum),Right ([],TyProp,CFalsum),4)
        , ("negation mismatch",Left KernelNegationPremiseMismatch,Left (CountedCoreOperationFailed KernelNegationPremiseMismatch),3)
        , ("negation shape",Left KernelExpectedNegation,Left (CountedCoreOperationFailed KernelExpectedNegation),2)
        , ("conjunction intro",Right ([],TyProp,CAnd CTruth CFalsum),Right ([],TyProp,CAnd CTruth CFalsum),3)
        , ("conjunction type",Left (KernelExpectedProposition TySet),Left (CountedCoreOperationFailed (KernelExpectedProposition TySet)),2)
        , ("conjunction context",Left (KernelContextMismatch [] [TySet]),Left (CountedCoreOperationFailed (KernelContextMismatch [] [TySet])),1)
        , ("conjunction left",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),2)
        , ("conjunction right",Right ([],TyProp,CFalsum),Right ([],TyProp,CFalsum),2)
        , ("conjunction shape",Left KernelExpectedConjunction,Left (CountedCoreOperationFailed KernelExpectedConjunction),1)
        , ("disjunction left",Right ([],TyProp,COr CTruth CFalsum),Right ([],TyProp,COr CTruth CFalsum),7)
        , ("disjunction right",Right ([],TyProp,COr CTruth CFalsum),Right ([],TyProp,COr CTruth CFalsum),7)
        , ("disjunction elim",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),5)
        , ("disjunction mismatch",Left KernelDisjunctionBranchMismatch,Left (CountedCoreOperationFailed KernelDisjunctionBranchMismatch),4)
        , ("disjunction shape",Left KernelExpectedDisjunction,Left (CountedCoreOperationFailed KernelExpectedDisjunction),3)
        , ("implication intro",Right ([],TyProp,CImp CTruth CFalsum),Right ([],TyProp,CImp CTruth CFalsum),7)
        , ("implication elim",Right ([],TyProp,CFalsum),Right ([],TyProp,CFalsum),3)
        , ("implication mismatch",Left KernelImplicationPremiseMismatch,Left (CountedCoreOperationFailed KernelImplicationPremiseMismatch),3)
        , ("implication shape",Left KernelExpectedImplication,Left (CountedCoreOperationFailed KernelExpectedImplication),2)
        , ("forall intro",Right ([],TyProp,CForall TySet CTruth),Right ([],TyProp,CForall TySet CTruth),5)
        , ("forall empty context",Left (KernelBinderContextMismatch TySet []),Left (CountedCoreOperationFailed (KernelBinderContextMismatch TySet [])),1)
        , ("forall wrong binder",Left (KernelBinderContextMismatch TyProp [TySet]),Left (CountedCoreOperationFailed (KernelBinderContextMismatch TyProp [TySet])),2)
        , ("forall elim",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),5)
        , ("forall wrong argument",Left (KernelForallArgumentTypeMismatch TySet TyProp),Left (CountedCoreOperationFailed (KernelForallArgumentTypeMismatch TySet TyProp)),2)
        , ("forall shape",Left KernelExpectedForall,Left (CountedCoreOperationFailed KernelExpectedForall),1)
        , ("exists intro",Right ([],TyProp,CExists TySet CTruth),Right ([],TyProp,CExists TySet CTruth),10)
        , ("exists empty context",Left (KernelBinderContextMismatch TySet []),Left (CountedCoreOperationFailed (KernelBinderContextMismatch TySet [])),2)
        , ("exists wrong witness",Left (KernelExistentialWitnessTypeMismatch TySet TyProp),Left (CountedCoreOperationFailed (KernelExistentialWitnessTypeMismatch TySet TyProp)),3)
        , ("exists wrong premise",Left KernelExistentialPremiseMismatch,Left (CountedCoreOperationFailed KernelExistentialPremiseMismatch),7)
        , ("exists elim",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),8)
        , ("exists result mismatch",Left KernelExistentialResultMismatch,Left (CountedCoreOperationFailed KernelExistentialResultMismatch),7)
        , ("exists context mismatch",Left (KernelContextMismatch [TySet] []),Left (CountedCoreOperationFailed (KernelContextMismatch [TySet] [])),3)
        , ("exists shape",Left KernelExpectedExists,Left (CountedCoreOperationFailed KernelExpectedExists),3)
        , ("falsum elim",Right ([],TyProp,CTruth),Right ([],TyProp,CTruth),2)
        , ("falsum shape",Left KernelExpectedFalsum,Left (CountedCoreOperationFailed KernelExpectedFalsum),2)
        , ("equality reflexivity",Right ([],TyProp,CEq TySet (COpaqueInteger 0) (COpaqueInteger 0)),Right ([],TyProp,CEq TySet (COpaqueInteger 0) (COpaqueInteger 0)),5)
        , ("application congruence",Right ([],TyProp,CEq TySet (CApp (CLam TySet (CBound 0)) (COpaqueInteger 0)) (CApp (CLam TySet (CBound 0)) (COpaqueInteger 0))),Right ([],TyProp,CEq TySet (CApp (CLam TySet (CBound 0)) (COpaqueInteger 0)) (CApp (CLam TySet (CBound 0)) (COpaqueInteger 0))),18)
        , ("application nonfunction",Left (KernelExpectedFunctionEquality TySet),Left (CountedCoreOperationFailed (KernelExpectedFunctionEquality TySet)),2)
        , ("application argument mismatch",Left (KernelEqualityOperandTypeMismatch TySet TyProp),Left (CountedCoreOperationFailed (KernelEqualityOperandTypeMismatch TySet TyProp)),3)
        , ("lambda congruence",Right ([],TyProp,CEq (TyArrow TySet TySet) (CLam TySet (CBound 0)) (CLam TySet (CBound 0))),Right ([],TyProp,CEq (TyArrow TySet TySet) (CLam TySet (CBound 0)) (CLam TySet (CBound 0))),9)
        , ("lambda binder mismatch",Left (KernelBinderContextMismatch TyProp [TySet]),Left (CountedCoreOperationFailed (KernelBinderContextMismatch TyProp [TySet])),3)
        , ("lambda shape",Left KernelExpectedEquality,Left (CountedCoreOperationFailed KernelExpectedEquality),1)
        , ("equality MP",Right ([],TyProp,CFalsum),Right ([],TyProp,CFalsum),5)
        , ("equality MP mismatch",Left KernelEqualityPremiseMismatch,Left (CountedCoreOperationFailed KernelEqualityPremiseMismatch),4)
        , ("equality MP type",Left (KernelEqualityOperandTypeMismatch TyProp TySet),Left (CountedCoreOperationFailed (KernelEqualityOperandTypeMismatch TyProp TySet)),3)
        , ("equality MP shape",Left KernelExpectedEquality,Left (CountedCoreOperationFailed KernelExpectedEquality),2)
        ]

cases :: [(String,Either S.KernelSemanticsError (ScopedCheckedCore Void),Word -> (Either (CountedCoreFailure S.KernelSemanticsError) (ScopedCheckedCore Void),Word))]
cases =
 [ ("truth",S.truthIntroduction typing [],\w -> S.countedTruthIntroduction typing w [])
 , ("negation intro",S.negationIntroduction typing truth falsum,\w -> S.countedNegationIntroduction typing w truth falsum)
 , ("negation intro failure",S.negationIntroduction typing truth truth,\w -> S.countedNegationIntroduction typing w truth truth)
 , ("negation elim",S.negationElimination typing truth negated,\w -> S.countedNegationElimination typing w truth negated)
 , ("negation mismatch",S.negationElimination typing falsum negated,\w -> S.countedNegationElimination typing w falsum negated)
 , ("negation shape",S.negationElimination typing truth truth,\w -> S.countedNegationElimination typing w truth truth)
 , ("conjunction intro",S.conjunctionIntroduction truth falsum,\w -> S.countedConjunctionIntroduction w truth falsum)
 , ("conjunction type",S.conjunctionIntroduction set truth,\w -> S.countedConjunctionIntroduction w set truth)
 , ("conjunction context",S.conjunctionIntroduction truth openTruth,\w -> S.countedConjunctionIntroduction w truth openTruth)
 , ("conjunction left",S.conjunctionLeftElimination conjunction,\w -> S.countedConjunctionLeftElimination typing w conjunction)
 , ("conjunction right",S.conjunctionRightElimination conjunction,\w -> S.countedConjunctionRightElimination typing w conjunction)
 , ("conjunction shape",S.conjunctionLeftElimination truth,\w -> S.countedConjunctionLeftElimination typing w truth)
 , ("disjunction left",S.disjunctionLeftIntroduction typing truth falsum,\w -> S.countedDisjunctionLeftIntroduction typing w truth falsum)
 , ("disjunction right",S.disjunctionRightIntroduction typing truth falsum,\w -> S.countedDisjunctionRightIntroduction typing w truth falsum)
 , ("disjunction elim",S.disjunctionElimination typing disjunction truth truth,\w -> S.countedDisjunctionElimination typing w disjunction truth truth)
 , ("disjunction mismatch",S.disjunctionElimination typing disjunction truth falsum,\w -> S.countedDisjunctionElimination typing w disjunction truth falsum)
 , ("disjunction shape",S.disjunctionElimination typing truth truth truth,\w -> S.countedDisjunctionElimination typing w truth truth truth)
 , ("implication intro",S.implicationIntroduction truth falsum,\w -> S.countedImplicationIntroduction typing w truth falsum)
 , ("implication elim",S.implicationElimination implication truth,\w -> S.countedImplicationElimination w implication truth)
 , ("implication mismatch",S.implicationElimination implication falsum,\w -> S.countedImplicationElimination w implication falsum)
 , ("implication shape",S.implicationElimination truth truth,\w -> S.countedImplicationElimination w truth truth)
 , ("forall intro",S.forallIntroduction typing TySet openTruth,\w -> S.countedForallIntroduction typing w TySet openTruth)
 , ("forall empty context",S.forallIntroduction typing TySet truth,\w -> S.countedForallIntroduction typing w TySet truth)
 , ("forall wrong binder",S.forallIntroduction typing TyProp openTruth,\w -> S.countedForallIntroduction typing w TyProp openTruth)
 , ("forall elim",S.forallElimination quantified set,\w -> S.countedForallElimination w quantified set)
 , ("forall wrong argument",S.forallElimination quantified truth,\w -> S.countedForallElimination w quantified truth)
 , ("forall shape",S.forallElimination truth set,\w -> S.countedForallElimination w truth set)
 , ("exists intro",S.existentialIntroduction typing openTruth set truth,\w -> S.countedExistentialIntroduction typing w openTruth set truth)
 , ("exists empty context",S.existentialIntroduction typing truth set truth,\w -> S.countedExistentialIntroduction typing w truth set truth)
 , ("exists wrong witness",S.existentialIntroduction typing openTruth truth truth,\w -> S.countedExistentialIntroduction typing w openTruth truth truth)
 , ("exists wrong premise",S.existentialIntroduction typing openTruth set falsum,\w -> S.countedExistentialIntroduction typing w openTruth set falsum)
 , ("exists elim",S.existentialElimination typing existential truth openTruth,\w -> S.countedExistentialElimination typing w existential truth openTruth)
 , ("exists result mismatch",S.existentialElimination typing existential truth openFalsum,\w -> S.countedExistentialElimination typing w existential truth openFalsum)
 , ("exists context mismatch",S.existentialElimination typing existential truth truth,\w -> S.countedExistentialElimination typing w existential truth truth)
 , ("exists shape",S.existentialElimination typing truth truth openTruth,\w -> S.countedExistentialElimination typing w truth truth openTruth)
 , ("falsum elim",S.falsumElimination typing falsum truth,\w -> S.countedFalsumElimination typing w falsum truth)
 , ("falsum shape",S.falsumElimination typing truth truth,\w -> S.countedFalsumElimination typing w truth truth)
 , ("equality reflexivity",S.equalityReflexivity set,\w -> S.countedEqualityReflexivity typing w set)
 , ("application congruence",S.equalityCongruenceApplication functionEquality setEquality,\w -> S.countedEqualityCongruenceApplication typing w functionEquality setEquality)
 , ("application nonfunction",S.equalityCongruenceApplication setEquality setEquality,\w -> S.countedEqualityCongruenceApplication typing w setEquality setEquality)
 , ("application argument mismatch",S.equalityCongruenceApplication functionEquality propositionEquality,\w -> S.countedEqualityCongruenceApplication typing w functionEquality propositionEquality)
 , ("lambda congruence",S.equalityCongruenceLambda TySet openEquality,\w -> S.countedEqualityCongruenceLambda w TySet openEquality)
 , ("lambda binder mismatch",S.equalityCongruenceLambda TyProp openEquality,\w -> S.countedEqualityCongruenceLambda w TyProp openEquality)
 , ("lambda shape",S.equalityCongruenceLambda TySet openTruth,\w -> S.countedEqualityCongruenceLambda w TySet openTruth)
 , ("equality MP",S.equalityModusPonens propositionEquality truth,\w -> S.countedEqualityModusPonens typing w propositionEquality truth)
 , ("equality MP mismatch",S.equalityModusPonens propositionEquality falsum,\w -> S.countedEqualityModusPonens typing w propositionEquality falsum)
 , ("equality MP type",S.equalityModusPonens setEquality truth,\w -> S.countedEqualityModusPonens typing w setEquality truth)
 , ("equality MP shape",S.equalityModusPonens truth truth,\w -> S.countedEqualityModusPonens typing w truth truth)
 ]
 where
  typing=emptyGlobalTyping
  truth=checked [] CTruth
  falsum=checked [] CFalsum
  set=checked [] (COpaqueInteger 0)
  negated=checked [] (CNot CTruth)
  conjunction=checked [] (CAnd CTruth CFalsum)
  disjunction=checked [] (COr CTruth CFalsum)
  implication=checked [] (CImp CTruth CFalsum)
  openTruth=checked [TySet] CTruth
  openFalsum=checked [TySet] CFalsum
  quantified=checked [] (CForall TySet CTruth)
  existential=checked [] (CExists TySet CTruth)
  propositionEquality=checked [] (CEq TyProp CTruth CFalsum)
  setEquality=checked [] (CEq TySet (COpaqueInteger 0) (COpaqueInteger 0))
  functionEquality=checked [] (CEq (TyArrow TySet TySet) (CLam TySet (CBound 0)) (CLam TySet (CBound 0)))
  openEquality=checked [TySet] (CEq TySet (CBound 0) (CBound 0))
