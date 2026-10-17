{-# LANGUAGE RecordWildCards #-}

-- Deterministic, bounded inputs. Direct lexicons intentionally bypass source
-- declaration validation; the corpus command exercises that separate boundary.
module Fixtures where

import Base
import Control.DeepSeq (rnf)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Lexicon
import Felix.Syntax.Token
import Felix.Syntax.VerbSurface (checkVerbSurfaces)

data Fixture = Fixture
    { fixtureName :: String
    , fixtureLexicon :: Lexicon
    , fixtureSource :: Text
    }

proposition :: Text -> Text
proposition body = "\\begin{proposition}\\label{benchmark}\n" <> body <> "\n\\end{proposition}\n"

fixtures :: [Fixture]
fixtures =
    [ Fixture "short" builtins (proposition "$x=x$.")
    , Fixture "many-small" builtins (Text.concat
        [Text.replace "{benchmark}" ("{" <> nameAt i <> "}") (proposition "$x=x$.") | i <- [1..32]])
    , Fixture "few-large" builtins (Text.concat
        [Text.replace "{benchmark}" ("{" <> nameAt i <> "}")
            (proposition ("$" <> Text.intercalate "\\land " (replicate 23 "x=x") <> "$.")) | i <- [1..4]])
    , Fixture "empty" builtins ""
    , Fixture "partial" builtins (proposition "$x=$.")
    , Fixture "malformed" builtins (proposition "$x \\unknown y$.")
    , Fixture "empty-categories" builtins
        { lexiconRelationSymbols = [], lexiconTypedConstants = []
        , lexiconPrefixPredicates = [], lexiconNouns = [], lexiconAdjRs = []
        , lexiconVerbs = [], lexiconStructNouns = [] }
        (proposition "$x \\unknown y$.")
    , Fixture "duplicate-relation" builtins
        { lexiconRelationSymbols = replicate 2 (relation "bench" "same") }
        (proposition "$x \\bench y$.")
    , Fixture "ambiguous-relation" builtins
        { lexiconRelationSymbols = [relation "bench" "first", relation "bench" "second"] }
        (proposition "$x \\bench y$.")
    , Fixture "native-ambiguous" builtins
        { lexiconTypedConstants = [(Command "Set", Raw.ConcreteSet), (Command "Set", Raw.ConcreteProp)] }
        (proposition "$x=x$.")
    ] <> [scaling category shared n arities | (category, shared, n, arities) <- scalingCases]

data Category = Relations | Constants | Predicates | Nouns | Adjectives | Verbs | Functions | Mixfix
    deriving (Eq)

categoryName :: Category -> String
categoryName = \case
    Relations -> "relation"
    Constants -> "constant"
    Predicates -> "prefix"
    Nouns -> "noun"
    Adjectives -> "adjective"
    Verbs -> "verb"
    Functions -> "function"
    Mixfix -> "mixfix"

scalingCases :: [(Category, Bool, Int, Int)]
scalingCases =
    [ (category, shared, n, arities)
    | category <- [Relations, Constants, Predicates, Nouns, Adjectives, Verbs, Functions, Mixfix]
    , shared <- if category `elem` [Nouns, Adjectives, Verbs, Functions] then [False, True] else [False]
    , n <- [0, 32, 128]
    , arities <- if category == Predicates then [1, 8] else [1]
    ]

relation :: Text -> Raw.Marker -> Raw.RelationSymbol
relation name = Raw.RelationSymbol (Command name) Raw.zeroParameterArity

-- Alphabetic names have identical tokenization at every size.
nameAt :: Int -> Text
nameAt n = "bench" <> Text.pack [toEnum (97 + n `div` 26), toEnum (97 + n `mod` 26)]

scaling :: Category -> Bool -> Int -> Int -> Fixture
scaling category shared size arities = Fixture name inventory source
  where
    name = intercalate "-" [categoryName category, if shared then "shared" else "disjoint", show size, show arities]
    entries = [1 .. size]
    surface i = (if shared then [Just (Word "common")] else []) <> [Just (Word (nameAt i))]
    phrase i = Raw.mkLexicalItemSgPl (Raw.SgPl (surface i) (surface i)) (Raw.Marker (nameAt i))
    verb i = Raw.VerbLexicalItem
        (either (error . show) id (checkVerbSurfaces (surface i) (surface i)))
        (Raw.Marker (nameAt i))
    inventory = case category of
        Relations -> builtins
            { lexiconRelationSymbols = lexiconRelationSymbols builtins <>
                [relation (nameAt i) (Raw.Marker (nameAt i)) | i <- entries] }
        Constants -> builtins
            { lexiconTypedConstants = [(Command (nameAt i), Raw.ConcreteSet) | i <- entries] }
        Predicates -> builtins
            { lexiconPrefixPredicates = lexiconPrefixPredicates builtins <>
                [(Raw.PrefixPredicate (nameAt i) (1 + (i - 1) `mod` arities), Raw.Marker (nameAt i)) | i <- entries] }
        Nouns -> builtins { lexiconNouns = lexiconNouns builtins <> map phrase entries }
        Adjectives -> builtins
            { lexiconAdjRs = lexiconAdjRs builtins <>
                [Raw.intrinsicAdjectiveLexicalItem Raw.RightAdjectiveSide
                    (Raw.patternFromHoley (surface i)) (Raw.Marker (nameAt i)) | i <- entries] }
        Verbs -> builtins { lexiconVerbs = lexiconVerbs builtins <> map verb entries }
        Functions -> builtins { lexiconFuns = map phrase entries }
        Mixfix -> builtins
            { lexiconMixfixTable = Seq.adjust'
                (\level -> foldl' addMixfix level entries) 9 (lexiconMixfixTable builtins) }
    addMixfix table i =
        let item = Raw.mkMixfixItem [Just (Command (nameAt i)), Nothing] (Raw.Marker (nameAt i)) Raw.NonAssoc
        in Map.insert (Raw.mixfixPattern item) item table
    -- A fixed built-in target measures collateral setup/fan-out. Matching and
    -- malformed variants below retain exactly the same target at every size.
    source = proposition "$x=x$."

scalingVariants :: [Fixture]
scalingVariants = concat
    [ variants category shared (scaling category shared size arities)
    | (category, shared, size, arities) <- scalingCases ]
  where
    variants category shared f =
        [ f { fixtureName = fixtureName f <> "-match", fixtureSource = proposition (target category shared) }
        , f { fixtureName = fixtureName f <> "-failure", fixtureSource = proposition "$x \\unknown y$." }
        ]
    target category shared =
        let phrase = (if shared then "common " else "") <> "benchab"
        in case category of
            Relations -> "$x \\benchab y$."
            Constants -> "$\\benchab=x$."
            Predicates -> "$\\benchab{x}$."
            Nouns -> "$x$ is a " <> phrase <> "."
            Adjectives -> "$x$ is " <> phrase <> "."
            Verbs -> "$x$ " <> phrase <> "."
            Functions -> "The " <> phrase <> " is a set."
            Mixfix -> "$\\benchab x=x$."

allFixtures :: [Fixture]
allFixtures = fixtures <> scalingVariants <> focusedFixtures <>
    [ Fixture ("derivations-" <> show n <> if distinct then "-distinct" else "-equal")
        builtins { lexiconRelationSymbols =
            [relation "bench" (Raw.Marker (if distinct then nameAt i else "same")) | i <- [1..n]] }
        (proposition "$x \\bench y$.")
    | n <- [8, 32, 128], distinct <- [False, True] ]

focusedFixtures :: [Fixture]
focusedFixtures =
    [ Fixture "owned-field-failure" widgetLexicon (structure "Y")
    , Fixture "owned-field-success" widgetLexicon (structure "X")
    , Fixture "typed-variable-exclusion" builtins
        { lexiconTypedConstants = [(Variable "x", Raw.ConcreteSet)] }
        (proposition "$x=x$.")
    , Fixture "native-expression-priority" builtins
        { lexiconTypedConstants = [(Command "Set", Raw.ConcreteSet)] }
        (proposition "$x=x$.")
    , Fixture "reserved-constant" builtins
        { lexiconTypedConstants = [(Command "opaqueInteger", Raw.ConcreteSet)]
        , lexiconStructFun = Raw.StructSymbol "opaqueInteger" : lexiconStructFun builtins
        , lexiconPrefixPredicates = (Raw.PrefixPredicate "opaqueInteger" 1, "reserved") : lexiconPrefixPredicates builtins }
        (proposition "$\\opaqueInteger{-3}=0$.")
    ] <>
    [ Fixture ("prefix-boundary-" <> show arity) builtins
        { lexiconPrefixPredicates = [(Raw.PrefixPredicate "bench" arity, "boundary")] }
        (proposition "$\\bench{x}$.")
    | arity <- [-1, 0, 1, 2] ] <>
    [ Fixture ("prefix-definition-" <> show arity) builtins
        { lexiconPrefixPredicates = [(Raw.PrefixPredicate "bench" arity, "boundary")] }
        "\\begin{definition}\\label{boundary} We write $\\bench{x}$ if $x=x$. \\end{definition}"
    | arity <- [0, 1, 2] ] <>
    [ Fixture "prefix-repeated-across-arities" builtins
        { lexiconPrefixPredicates = [(Raw.PrefixPredicate "bench" arity, Raw.Marker (nameAt arity)) | arity <- [0,1,2]] }
        (proposition "$\\bench{x}$.")
    , Fixture "structure-annotation" structureLexicon
        (proposition "$\\structure[left module over \\carrier[X]]{A,a,z,n,s}=M$.")
    , Fixture "structure-annotation-spacing" structureLexicon
        (proposition "$\\structure[leftmodule over R]{A,a}=M$.")
    , Fixture "structure-plural-slot" structureLexicon
        (proposition "Let $M,N$ be left modules over $R$. Then $M=M$.")
    , Fixture "structure-nullable-slot" structureLexicon
        (proposition "$M$ is a left module over $R$.")
    , Fixture "let-relation" builtins
        { lexiconRelationSymbols = relation "bench" "bench" : lexiconRelationSymbols builtins }
        (proposition "Let $x \\bench y$. Then $x=x$.")
    , Fixture "let-equality" builtins (proposition "Let $x=y$. Then $x=x$.")
    , Fixture "let-membership" builtins (proposition "Let $x\\in A$. Then $x=x$.")
    ]
  where
    widget = Raw.mkLexicalItemSgPl
        (Raw.SgPl [Just (Word "widget")] [Just (Word "widgets")]) "widget"
    widgetLexicon = builtins
        { lexiconStructNouns = widget : lexiconStructNouns builtins
        , lexiconStructFun = Raw.StructSymbol "widgetValue" : lexiconStructFun builtins }
    structureLexicon = builtins
        { lexiconStructNouns = Raw.mkLexicalItemSgPl
            (Raw.SgPl [Just (Word "left"), Just (Word "module"), Just (Word "over"), Nothing]
                [Just (Word "left"), Just (Word "modules"), Just (Word "over"), Nothing]) "left_module"
            : lexiconStructNouns builtins }
    structure receiver = Text.unlines
        [ "\\begin{struct}\\label{widget}"
        , "A widget $X$ is a onesorted structure equipped with"
        , "\\begin{enumerate}"
        , "\\item a set $\\widgetValue[" <> receiver <> "]$;"
        , "\\end{enumerate}."
        , "\\end{struct}" ]

nativeSnippets :: [Text]
nativeSnippets =
    [ "x", "x,y", "\\Set", "\\Set \\to \\Prop", "x=x"
    , "\\opaqueInteger{-3}", "0", "-3", "\\unknown", "x="
    ]

markupSnippets :: [Text]
markupSnippets = nativeSnippets <>
    [ "x_i^2", "\\frac{a}{b}", "\\left(x+y\\right)", "\\operatorname{sin}(x)" ]

-- No Show-based forcing, grammar traversal, or oracle construction in setup.
forceLexicon :: Lexicon -> ()
forceLexicon Lexicon{..} =
    rnf lexiconMixfixTable `seq` rnf lexiconTypedConstants `seq`
    foldr (\level rest -> foldr (\c next -> forceConnective c `seq` next) rest level) () lexiconConnectives `seq`
    rnf lexiconPrefixPredicates `seq` rnf lexiconStructFun `seq`
    rnf lexiconRelationSymbols `seq` rnf lexiconVerbs `seq`
    rnf lexiconAdjLs `seq` rnf lexiconAdjRs `seq` rnf lexiconNouns `seq`
    rnf lexiconStructNouns `seq` rnf lexiconFuns
  where
    forceConnective (PrefixNegationSyntax token) = rnf token
    forceConnective (InfixConnectiveSyntax token associativity connective) =
        rnf token `seq` rnf associativity `seq` rnf connective

lexiconCounts :: Lexicon -> [(String, Int)]
lexiconCounts Lexicon{..} =
    [ ("mixfix", sum (Map.size <$> lexiconMixfixTable))
    , ("connective", sum (length <$> lexiconConnectives))
    , ("constant", length lexiconTypedConstants)
    , ("prefix", length lexiconPrefixPredicates)
    , ("prefix-arities", length (nubOrd [arity | (Raw.PrefixPredicate _ arity, _) <- lexiconPrefixPredicates]))
    , ("relation", length lexiconRelationSymbols)
    , ("verb", length lexiconVerbs), ("adjective-left", length lexiconAdjLs)
    , ("adjective-right", length lexiconAdjRs), ("noun", length lexiconNouns)
    , ("structure-noun", length lexiconStructNouns), ("function", length lexiconFuns)
    , ("structure-operation", length lexiconStructFun)
    ]
