{-# LANGUAGE NoImplicitPrelude #-}

-- | The 'Lexicon' describes the part of the grammar that extensible/dynamic.
--
-- The items of the 'Lexicon' are organized by their meaning and their
-- syntactic behaviour. They are typically represented as some kind of
-- pattern data which is then used to generate various production rules
-- for the concrete grammar. This representation makes inspection and
-- extension easier.
--

module Felix.Syntax.Lexicon
    ( module Felix.Syntax.Lexicon
    , pattern ConsSymbol
    , pattern PairSymbol
    , pattern UpairSymbol
    , pattern UnionsSymbol
    , pattern CarrierSymbol
    , pattern ApplySymbol
    , pattern DomSymbol
    ) where


import Base
import Felix.Syntax.Abstract

import Data.List qualified as List
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text


data SignatureHeadForm
    = AdjectiveSignatureHead
    | SymbolicSignatureHead
    deriving (Show, Eq, Ord)

-- Adjective heads must precede symbolic heads because both start with a math
-- variable.
concreteSignatureHeadForms :: [SignatureHeadForm]
concreteSignatureHeadForms =
    [ AdjectiveSignatureHead
    , SymbolicSignatureHead
    ]

data Lexicon = Lexicon
    { lexiconMixfixTable        :: Seq (Map Pattern MixfixItem)
    , lexiconTypedConstants     :: [(Token, ConcreteType)]
    , lexiconConnectives        :: [[ConnectiveSyntax]]
    , lexiconPrefixPredicates   :: [(PrefixPredicate, Marker)]
    , lexiconStructFun          :: [StructSymbol]
    , lexiconRelationSymbols    :: [RelationSymbol]
    , lexiconVerbs              :: [VerbLexicalItem]
    , lexiconAdjLs              :: [AdjectiveLexicalItem]
    , lexiconAdjRs              :: [AdjectiveLexicalItem]
    , lexiconNouns              :: [LexicalItemSgPl]
    , lexiconStructNouns        :: [LexicalItemSgPl]
    , lexiconFuns               :: [LexicalItemSgPl]
    } deriving (Show, Eq)

data ConnectiveSyntax
    = PrefixNegationSyntax !Token
    | InfixConnectiveSyntax !Token !Associativity !Connective
    deriving (Show, Eq)

-- Projection returning the union of both left and right attributes.
--
lexiconAdjs :: Lexicon -> [AdjectiveLexicalItem]
lexiconAdjs lexicon = lexiconAdjLs lexicon <> lexiconAdjRs lexicon


builtins :: Lexicon
builtins =
    Lexicon
        { lexiconMixfixTable        = builtinMixfixTable
        , lexiconTypedConstants     = []
        , lexiconPrefixPredicates   = builtinPrefixPredicates
        , lexiconStructFun          = builtinStructOps
        , lexiconConnectives        = builtinConnectives
        , lexiconRelationSymbols    = builtinRelationSymbols
        , lexiconAdjLs              = []
        , lexiconAdjRs              = builtinAdjRs
        , lexiconVerbs              = builtinVerbs
        , lexiconNouns              = builtinNouns
        , lexiconStructNouns        = builtinStructNouns
        , lexiconFuns               = []
        }

prefixPredicatePattern :: PrefixPredicate -> Pattern
prefixPredicatePattern (PrefixPredicate command _arity) =
    TokenCons (Command command) End

builtinMixfixTable :: Seq (Map Pattern MixfixItem)
builtinMixfixTable = Seq.fromList $ Map.fromList . fmap toEntry <$> builtinMixfixLevels
    where
        toEntry item@(MixfixItem pat _ _) = (pat, item)

-- INVARIANT: 10 precedence levels for now.
builtinMixfixLevels :: [[MixfixItem]]
builtinMixfixLevels =
    [ []
    , [binOp (Symbol "+") LeftAssoc "add", binOp (Command "union") LeftAssoc "union", binOp (Symbol "-") LeftAssoc "minus", binOp (Command "rminus") LeftAssoc "rminus", binOp (Command "monus") LeftAssoc "monus"]
    , [binOp (Command "relcomp") LeftAssoc "relcomp"]
    , [binOp (Command "circ") LeftAssoc "circ"]
    , [binOp (Command "mul") LeftAssoc "mul", binOp (Command "inter") LeftAssoc "inter", binOp (Command "rmul") LeftAssoc "rmul"]
    , [binOp (Command "setminus") LeftAssoc "setminus"]
    , [binOp (Command "times") RightAssoc "times"]
    , []
    , prefixOps
    , builtinIdentifiers
    ]
    where
        builtinIdentifiers :: [MixfixItem]
        builtinIdentifiers = identifier <$>
            [ "emptyset"
            , "naturals"
            , "naturalsPlus"
            , "integers"
            , "rationals"
            , "reals"
            , "unit"
            , "zero"
            ]


prefixOps :: [MixfixItem]
prefixOps =
    [ mkMixfixItem [Just (Command "rfrac"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "rfrac" NonAssoc
    , mkMixfixItem [Just (Command "exp"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "exp" NonAssoc
    , mkMixfixItem [Just (Command "repl"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "repl" NonAssoc
    , mkMixfixItem [Just (Command "sep"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "sep" NonAssoc
    , mkMixfixItem [Just (Command "lfp"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR, Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "lfp" NonAssoc
    , UnionsSymbol
    , mkMixfixItem [Just (Command "choice"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "choice" NonAssoc
    , mkMixfixItem [Just (Command "cumul"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "cumul" NonAssoc
    , mkMixfixItem [Just (Command "fst"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "fst" NonAssoc
    , mkMixfixItem [Just (Command "snd"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "snd" NonAssoc
    , mkMixfixItem [Just (Command "pow"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "pow" NonAssoc
    , mkMixfixItem [Just (Command "neg"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "neg" NonAssoc
    , mkMixfixItem [Just (Command "inv"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "inv" NonAssoc
    , mkMixfixItem [Just (Command "abs"), Just InvisibleBraceL, Nothing, Just InvisibleBraceR] "abs" NonAssoc
    , ConsSymbol
    , PairSymbol
    , UpairSymbol
    -- NOTE Is now defined and hence no longer necessary , ApplySymbol
    ]


builtinStructOps :: [StructSymbol]
builtinStructOps =
    [ CarrierSymbol
    ]

identifier :: Text -> MixfixItem
identifier cmd = mkMixfixItem [Just (Command cmd)] (Marker cmd) NonAssoc


builtinRelationSymbols :: [RelationSymbol]
builtinRelationSymbols =
    [ RelationSymbol (Symbol "=") zeroParameterArity "eq"
    , RelationSymbol (Command "rless") zeroParameterArity "rless"
    , RelationSymbol (Command "neq") zeroParameterArity "neq"
    , ElementSymbol
    , NotElementSymbol -- Alternative to @\not\in@.
    ]

builtinPrefixPredicates :: [(PrefixPredicate, Marker)]
builtinPrefixPredicates =
    [ (PrefixPredicate "Cong" 4, "cong")
    , (PrefixPredicate "Betw" 3, "betw")
    ]


builtinConnectives :: [[ConnectiveSyntax]]
builtinConnectives =
    [ [InfixConnectiveSyntax (Command "iff") NonAssoc Equivalence]
    , [InfixConnectiveSyntax (Command "implies") RightAssoc Implication]
    , [InfixConnectiveSyntax (Command "lor") LeftAssoc Disjunction]
    , [InfixConnectiveSyntax (Command "land") LeftAssoc Conjunction]
    , [PrefixNegationSyntax (Command "lnot")]
    ]


binOp :: Token -> Associativity -> Marker -> MixfixItem
binOp tok assoc m = mkMixfixItem [Nothing, Just tok, Nothing] m assoc

builtinAdjRs :: [AdjectiveLexicalItem]
builtinAdjRs =
    [ builtinEqualityRightAdjective
    ]

builtinEqualityRightAdjective :: AdjectiveLexicalItem
builtinEqualityRightAdjective =
    intrinsicAdjectiveLexicalItem
        RightAdjectiveSide
        (patternFromHoley
            (lexicalPhrase
                (Just "equal" :| [Just "to", Nothing])))
        "eq"

builtinVerbs :: [VerbLexicalItem]
builtinVerbs =
    [ builtinEqualityVerb
    ]

builtinEqualityVerb :: VerbLexicalItem
builtinEqualityVerb =
    VerbLexicalItem
        surfaces
        "eq"
  where
    surfaces =
        case checkVerbSurfaces
                (lexicalPhrase
                    (Just "equals" :| [Nothing]))
                (lexicalPhrase
                    (Just "equal" :| [Nothing])) of
            Right checked -> checked
            Left failure ->
                impossible
                    ("invalid fixed verb surfaces: " <> show failure)


-- Some of these do/should correspond to mathlib structures,
-- e.g.: lattice, complete lattice, ring, etc.
--
builtinNouns :: [LexicalItemSgPl]
builtinNouns =
    [ builtinSetNoun
    , mkLexicalItemSgPl
        (lexicalPhraseSgPl
            ((Just "point", Just "points") :| []))
        "point"
    , builtinElementNoun
    ]

builtinSetNoun :: LexicalItemSgPl
builtinSetNoun =
    mkLexicalItemSgPl
        (lexicalPhraseSgPl
            ((Just "set", Just "sets") :| []))
        "set"

builtinElementNoun :: LexicalItemSgPl
builtinElementNoun =
    mkLexicalItemSgPl
        (lexicalPhraseSgPl
            ( (Just "element", Just "elements")
                :| [ (Just "of", Just "of")
                   , (Nothing, Nothing)
                   ]
            ))
        "elem"

-- | Match the complete fixed-base identity, including the plural surface and
-- authoritative marker. The ordinary 'Eq' instance intentionally compares
-- only singular patterns.
isBuiltinSetNoun :: LexicalItemSgPl -> Bool
isBuiltinSetNoun item =
    let actual = lexicalItemSgPlPattern item
        expected = lexicalItemSgPlPattern builtinSetNoun
    in sg actual == sg expected
        && pl actual == pl expected
        && lexicalItemSgPlMarker item
            == lexicalItemSgPlMarker builtinSetNoun

_Record :: LexicalItemSgPl
_Record = mkLexicalItemSgPl
    (lexicalPhraseSgPl ((Just "record", Just "records") :| [])) "record"

_Onesorted :: LexicalItemSgPl
_Onesorted =
    mkLexicalItemSgPl
        (lexicalPhraseSgPl
            ( (Just "onesorted", Just "onesorted")
                :| [(Just "structure", Just "structures")]
            ))
        "onesorted_structure"

builtinStructNouns :: [LexicalItemSgPl]
builtinStructNouns = [_Record, _Onesorted]


-- | Naïve splitting of lexical phrases to insert a variable slot for names in noun phrases,
-- as in /@there exists a linear form $h$ on $E$@/, where the underlying pattern is
-- /@linear form on ?@/. In this case we would get:
--
-- For example, the singular pattern represented by
-- @"linear form[/s] on ?"@ splits into @"linear form"@ and @"on ?"@.
--
splitOnVariableSlot :: LexicalPhrase -> (LexicalPhrase, LexicalPhrase)
splitOnVariableSlot pat = case prepositionIndices <> nonhyphenatedSlotIndices of
    [] -> (pat, []) -- Place variable slot at the end.
    is -> List.splitAt (minimum is) pat
    where
        prepositionIndices, slotIndices, nonhyphenatedSlotIndices :: [Int] -- Ascending.
        prepositionIndices = List.findIndices isPreposition pat
        slotIndices = List.findIndices isNothing pat
        nonhyphenatedSlotIndices =
            [ i
            | i <- slotIndices
            , noHyphen (zeroBasedIndex (i + 1) >>= (`nth` pat))
            ]

        isPreposition :: Maybe Token -> Bool
        isPreposition = \case
            Just (Word w) -> w `Set.member` prepositions
            _ -> False

        noHyphen :: Maybe (Maybe Token) -> Bool
        noHyphen = \case
            Just (Just (Word w)) ->
                not (Text.singleton '-' `Text.isPrefixOf` w)
            -- If we arrive here, either the pattern is over (`Nothing`) or the next
            -- part of the pattern is not a word that starts with a hyphen.
            _ -> True


-- Preposition are a closed class, but this list is not yet exhaustive.
-- It can and should be extended when needed. The following list is a
-- selection of the prepositions found at
-- https://en.wikipedia.org/wiki/List_of_English_prepositions.
--
prepositions :: Set Text
prepositions = Set.fromList
    [ "about"
    , "above"
    , "across"
    , "after"
    , "against"
    , "along", "alongside"
    , "amid", "amidst"
    , "among"
    , "around"
    , "as"
    , "at"
    , "atop"
    , "before"
    , "behind"
    , "below"
    , "beneath"
    , "beside", "besides"
    , "between"
    , "beyond"
    , "but"
    , "by"
    , "except"
    , "for"
    , "from"
    , "in", "inside", "into"
    , "like"
    , "modulo", "mod"
    , "near"
    , "next"
    , "of"
    , "off"
    , "on"
    , "onto"
    , "opposite"
    , "out"
    , "over"
    , "past"
    , "per"
    , "sans"
    , "till"
    , "to"
    , "under"
    , "underneath"
    , "unlike"
    , "unto"
    , "up", "upon"
    , "versus"
    , "via"
    , "with"
    , "within"
    , "without"
    ]
