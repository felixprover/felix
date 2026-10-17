{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Abstract (unitTests) where

import Base
import Felix.Report.Location
import Felix.Syntax.Abstract

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog (testPropertyNamed)

unitTests :: TestTree
unitTests =
    testGroup "Abstract syntax"
        [ testPropertyNamed
            "noun phrase ordering obeys the Ord laws"
            "prop_nounPhraseOrd"
            prop_nounPhraseOrd
        , testCase
            "noun phrase fields survive ordered deduplication"
            nounPhraseFieldsRemainDistinct
        ]

prop_nounPhraseOrd :: Property
prop_nounPhraseOrd = withTests 100 . property $ do
    x <- forAll nounPhrase
    y <- forAll nounPhrase
    z <- forAll nounPhrase

    (compare x y == EQ) === (x == y)
    compare x y === oppositeOrdering (compare y x)
    assert (not (x <= y && y <= z) || x <= z)

nounPhraseFieldsRemainDistinct :: Assertion
nounPhraseFieldsRemainDistinct =
    assertEqual
        "one value per base and changed field"
        6
        (length
            (nubOrd
                [ sampleNounPhrase False False False False False
                , sampleNounPhrase True False False False False
                , sampleNounPhrase False True False False False
                , sampleNounPhrase False False True False False
                , sampleNounPhrase False False False True False
                , sampleNounPhrase False False False False True
                ]))

nounPhrase :: Gen (NounPhraseOf Maybe Int)
nounPhrase = do
    NounPhrase left core names right residual <- unboundedPhrase
    bound <- Gen.element
        [ Unbounded
        , Bounded Nowhere Positive (Relation Nowhere ElementSymbol []) (ExprVar "F")
        , Bounded Nowhere Negative (Relation Nowhere ElementSymbol []) (ExprVar "F")
        , Bounded Nowhere Positive (Relation Nowhere ElementSymbol []) (ExprVar "G")
        ]
    pure (NounPhrase left core (names { nounBinderBound = bound }) right residual)
  where
    unboundedPhrase = sampleNounPhrase
            <$> Gen.bool
            <*> Gen.bool
            <*> Gen.bool
            <*> Gen.bool
            <*> Gen.bool

sampleNounPhrase
    :: Bool
    -> Bool
    -> Bool
    -> Bool
    -> Bool
    -> NounPhraseOf Maybe Int
sampleNounPhrase hasLeft otherNoun hasName hasRight hasSuchThat =
    NounPhrase
        [AdjL Nowhere leftAdjective [1] | hasLeft]
        (Noun
            Nowhere
            (if otherNoun then secondNoun else firstNoun)
            [2])
        (unboundedNounBinder (NamedVar "x" <$ guardMaybe hasName))
        [AdjR Nowhere rightAdjective [3] | hasRight]
        (truthStatement <$ guardMaybe hasSuchThat)
  where
    guardMaybe condition =
        if condition then Just () else Nothing

leftAdjective :: AdjectiveLexicalItem
leftAdjective =
    userAdjectiveLexicalItem
        LeftAdjectiveSide
        (patternFromHoley [Just (Word "left")])

rightAdjective :: AdjectiveLexicalItem
rightAdjective =
    userAdjectiveLexicalItem
        RightAdjectiveSide
        (patternFromHoley [Just (Word "right")])

firstNoun :: LexicalItemSgPl
firstNoun =
    mkLexicalItemSgPl
        (SgPl
            [Just (Word "first")]
            [Just (Word "firsts")])
        "first"

secondNoun :: LexicalItemSgPl
secondNoun =
    mkLexicalItemSgPl
        (SgPl
            [Just (Word "second")]
            [Just (Word "seconds")])
        "second"

truthStatement :: Stmt
truthStatement =
    StmtFormula (PropositionalConstant Nowhere IsTop)

oppositeOrdering :: Ordering -> Ordering
oppositeOrdering = \case
    LT -> GT
    EQ -> EQ
    GT -> LT
