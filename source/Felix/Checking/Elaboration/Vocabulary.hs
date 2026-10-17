{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Fixed semantic vocabulary used by ordinary source elaboration.
module Felix.Checking.Elaboration.Vocabulary
    ( FixedSemanticMeaning(..)
    , fixedSemanticMeaning
    , isSetNounPhrase
    , lowerFixedEqualityPredicate
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Semantic
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Lexicon qualified as Lexicon

import Data.Map.Strict qualified as Map


data FixedSemanticMeaning
    = FixedEquality
    | FixedDisequality
    | FixedIntrinsic !CoreIntrinsicTag
    | FixedNegatedIntrinsic !CoreIntrinsicTag
    deriving stock (Show, Eq)

fixedSemanticMeaning
    :: SemanticGlobalKey
    -> Maybe FixedSemanticMeaning
fixedSemanticMeaning key =
    Map.lookup key fixedSemanticVocabulary

isSetNounPhrase :: Raw.NounPhrase Maybe -> Bool
isSetNounPhrase = \case
    Raw.NounPhrase
            []
            (Raw.Noun _ item [])
            (Raw.NounBinder Nothing Raw.Unbounded)
            []
            Nothing ->
        Lexicon.isBuiltinSetNoun item
    _ -> False

-- This inventory owns every source form that bypasses global lookup.
fixedSemanticVocabulary
    :: Map.Map SemanticGlobalKey FixedSemanticMeaning
fixedSemanticVocabulary =
    Map.fromList
    [ ( relationKey Raw.EqSymbol
      , FixedEquality
      )
    , ( semanticAdjectiveKey
            OrdinaryAdjectiveReading
            (Raw.adjectiveLexicalSide
                Lexicon.builtinEqualityRightAdjective)
            (Raw.adjectiveLexicalPattern
                Lexicon.builtinEqualityRightAdjective)
      , FixedEquality
      )
    , ( verbKey Lexicon.builtinEqualityVerb
      , FixedEquality
      )
    , ( relationKey Raw.ElementSymbol
      , FixedIntrinsic Member
      )
    , ( relationKey Raw.NotElementSymbol
      , FixedNegatedIntrinsic Member
      )
    , ( relationKey Raw.NeqSymbol
      , FixedDisequality
      )
    , ( nounKey Lexicon.builtinElementNoun
      , FixedIntrinsic Member
      )
    , ( expressionKey
            (Raw.TokenCons (Raw.Command "emptyset") Raw.End)
      , FixedIntrinsic Empty
      )
    , ( expressionKey (Raw.mixfixPattern Raw.UnionsSymbol)
      , FixedIntrinsic FamilyUnion
      )
    , ( expressionKey (unaryCommandPattern "choice")
      , FixedIntrinsic GlobalChoice
      )
    , ( expressionKey (unaryCommandPattern "pow")
      , FixedIntrinsic PowerSet
      )
    , ( expressionKey (unaryCommandPattern "cumul")
      , FixedIntrinsic UnivOf
      )
    , ( expressionKey (binaryCommandPattern "repl")
      , FixedIntrinsic Repl
      )
    , ( expressionKey (binaryCommandPattern "sep")
      , FixedIntrinsic Sep
      )
    , ( expressionKey (binaryCommandPattern "lfp")
      , FixedIntrinsic ISetLfp
      )
    , ( expressionKey (Raw.mixfixPattern Raw.UpairSymbol)
      , FixedIntrinsic PairSet
      )
    , ( expressionKey (Raw.mixfixPattern Raw.PairSymbol)
      , FixedIntrinsic OrderedPair
      )
    , ( expressionKey (unaryCommandPattern "fst")
      , FixedIntrinsic FirstProjection
      )
    , ( expressionKey (unaryCommandPattern "snd")
      , FixedIntrinsic SecondProjection
      )
    ]
  where
    relationKey relation =
        SemanticRelation
            (Raw.relationSymbolToken relation)
            (Raw.relationSymbolParameterArity relation)
    nounKey item =
        let patterns = Raw.lexicalItemSgPlPattern item
        in SemanticNoun (Raw.sg patterns) (Raw.pl patterns)
    verbKey item =
        SemanticVerb (Raw.verbLexicalSurfaces item)
    expressionKey = SemanticExpressionFunction

-- | Lower fixed equality-like proposition meanings. Membership deliberately
-- retains its carrier-aware source lowering and is not handled here.
lowerFixedEqualityPredicate
    :: FixedSemanticMeaning
    -> [CanonicalTerm global]
    -> Maybe (CanonicalTerm global)
lowerFixedEqualityPredicate meaning arguments =
    case (meaning, arguments) of
        (FixedEquality, [left, right]) ->
            Just (CEq TySet left right)
        (FixedDisequality, [left, right]) ->
            Just (CNot (CEq TySet left right))
        _ ->
            Nothing

unaryCommandPattern :: Text -> Raw.Pattern
unaryCommandPattern command =
    Raw.TokenCons (Raw.Command command)
        (Raw.TokenCons Raw.InvisibleBraceL
            (Raw.HoleCons
                (Raw.TokenCons Raw.InvisibleBraceR Raw.End)))

binaryCommandPattern :: Text -> Raw.Pattern
binaryCommandPattern command =
    Raw.TokenCons (Raw.Command command)
        (Raw.TokenCons Raw.InvisibleBraceL
            (Raw.HoleCons
                (Raw.TokenCons Raw.InvisibleBraceR
                    (Raw.TokenCons Raw.InvisibleBraceL
                        (Raw.HoleCons
                            (Raw.TokenCons Raw.InvisibleBraceR Raw.End))))))
