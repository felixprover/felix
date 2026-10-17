{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}

-- | Data types for the abstract syntax tree and helper functions
-- for constructing the lexicon.
--
module Felix.Syntax.Abstract
    ( module Felix.Syntax.Abstract
    , module Felix.Syntax.LexicalPhrase
    , module Felix.Syntax.Token
    , module Felix.Syntax.VerbSurface
    ) where


import Base
import Felix.Syntax.LexicalPhrase
    ( LexicalPhrase
    , LexicalPhraseSpecError(..)
    , SgPl(..)
    , lexicalPhrase
    , lexicalPhraseSgPl
    , readLexicalPhrase
    , readLexicalPhraseSgPl
    )
import Felix.Syntax.Token (Token(..), Located(..))
import Felix.Syntax.VerbSurface
import Felix.Report.Location

import Control.DeepSeq (NFData)
import Data.Set qualified as Set
import Text.Earley.Mixfix (Holey)
import Data.Text qualified as Text
import Numeric.Natural (Natural)

-- | Local "variable-like" symbols that can be captured by binders.
data VarSymbol
    = NamedVarAt Location Text -- ^ A named variable.
    | FreshVarAt Location Int -- ^ A nameless (implicit) variable. Should only come from desugaring.
    deriving (Generic, NFData)

pattern NamedVar :: Text -> VarSymbol
pattern NamedVar x <- NamedVarAt _ x where
    NamedVar x = NamedVarAt Nowhere x

pattern FreshVar :: Int -> VarSymbol
pattern FreshVar n <- FreshVarAt _ n where
    FreshVar n = FreshVarAt Nowhere n

{-# COMPLETE NamedVarAt, FreshVarAt #-}
{-# COMPLETE NamedVar, FreshVar #-}

instance Show VarSymbol where
    showsPrec d = \case
        NamedVarAt _ x ->
            showParen (d > 10) (showString "NamedVar " . showsPrec 11 x)
        FreshVarAt _ n ->
            showParen (d > 10) (showString "FreshVar " . showsPrec 11 n)

instance Eq VarSymbol where
    NamedVarAt _ x == NamedVarAt _ y = x == y
    FreshVarAt _ n == FreshVarAt _ m = n == m
    _ == _ = False

instance Ord VarSymbol where
    compare (NamedVarAt _ x) (NamedVarAt _ y) = compare x y
    compare NamedVarAt{} FreshVarAt{} = LT
    compare FreshVarAt{} NamedVarAt{} = GT
    compare (FreshVarAt _ n) (FreshVarAt _ m) = compare n m

instance Hashable VarSymbol where
    hashWithSalt s = \case
        NamedVarAt _ x -> hashWithSalt s (0 :: Int, x)
        FreshVarAt _ n -> hashWithSalt s (1 :: Int, n)

instance IsString VarSymbol where
    fromString v = NamedVar $ Text.pack v

instance Locatable VarSymbol where
    locate = \case
        NamedVarAt l _ -> l
        FreshVarAt l _ -> l

-- | Choose the first unused named variable, trying the base spelling before
-- appending the suffixes @1@, @2@, and so on.
freshNamedVar :: Set VarSymbol -> Text -> VarSymbol
freshNamedVar used base =
    go (NamedVar base) 1
  where
    go :: VarSymbol -> Natural -> VarSymbol
    go candidate nextSuffix
        | candidate `Set.notMember` used =
            candidate
        | otherwise =
            go
                (NamedVar (base <> Text.pack (show nextSuffix)))
                (nextSuffix + 1)

data Expr
    = ExprVar VarSymbol
    | ExprNaturalNumeral Location Natural
    | ExprOpaqueInteger Location Integer
    | ExprTypedConstant Location Token ConcreteType
    -- ^ An atomic monomorphic logical constant.
    | ExprHigherApply Location TypedExpression TypedExpression
    -- ^ Logical application, distinct from set-coded 'ExprApp'.
    | ExprLambda Location (NonEmpty VarSymbol) ConcreteType TypedExpression
    -- ^ One or more same-typed binders; multiple binders elaborate by currying.
    | ExprSelect Location (Maybe ConcreteType) TypedExpression
    -- ^ Logical selection, optionally checked against an explicit type.
    | ExprOp Location MixfixItem [Expr]
    | ExprStructOp Location StructSymbol (Maybe Expr)
    | ExprFiniteSet Location (NonEmpty Expr)
    | ExprSep Location VarSymbol Expr Stmt
    -- ^ Of the form /@{x ∈ X | P(x)}@/.
    | ExprReplace Location Expr (NonEmpty (VarSymbol,Expr)) (Maybe Stmt)
    -- ^ E.g.: /@{ f(x, y) | x ∈ X, y ∈ Y | P(x, y) }@/.
    | ExprReplacePred Location VarSymbol VarSymbol Expr Stmt
    -- ^ E.g.: /@{ y | \\exists x\\in X. P(x, y) }@/.
    | ExprStructAggregate
        Location
        (Maybe (StructApplication Expr))
        [StructAggregateEntry]
    -- ^ A concrete extensional structure record.  The optional schema is an
    -- elaboration annotation, not a component of the denoted set.
    | ExprStructReduct
        Location
        (StructApplication Expr)
        Expr
    -- ^ Checked restriction of a record to the selectors of one mandatory
    -- schema application.
    | ExprStructReconstruction
        Location
        (StructApplication Expr)
        Expr
        [StructAggregateEntry]
    -- ^ A schema-directed copy with simultaneous named replacements. The
    -- base supplies only fields selected by the target, never its extra data.
    --
    -- New expression forms are deliberately appended: the generic parsed
    -- payload codec assigns constructor tags in declaration order, so this
    -- preserves every older parsed expression encoding.
    deriving (Show, Eq, Ord, Generic, NFData)

data StructAggregateEntry
    = StructAggregatePositional Expr
    | StructAggregateNamed Location StructSymbol Expr
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable StructAggregateEntry where
    locate = \case
        StructAggregatePositional expression -> locate expression
        StructAggregateNamed location _symbol _expression -> location

structAggregateEntryExpression :: StructAggregateEntry -> Expr
structAggregateEntryExpression = \case
    StructAggregatePositional expression -> expression
    StructAggregateNamed _location _symbol expression -> expression

mapStructAggregateEntry
    :: (Expr -> Expr)
    -> StructAggregateEntry
    -> StructAggregateEntry
mapStructAggregateEntry transform = \case
    StructAggregatePositional expression ->
        StructAggregatePositional (transform expression)
    StructAggregateNamed location symbol expression ->
        StructAggregateNamed location symbol (transform expression)

-- | Concrete simple types accepted only in dedicated type positions.
--
-- The surface arrow is right-associative.  The AST itself is fully
-- parenthesized, so rendering and cache round trips do not depend on parser
-- precedence.
data ConcreteType
    = ConcreteProp
    | ConcreteSet
    | ConcreteArrow !ConcreteType !ConcreteType
    deriving (Show, Eq, Ord, Generic, NFData)

-- | A checked symbolic value can be term-valued or proposition-valued.
-- Formula-valued bodies are kept explicitly until elaboration; a
-- standalone symbolic expression is normalized to 'TypedExpressionExpr' by
-- the concrete parser.
data TypedExpression
    = TypedExpressionExpr !Expr
    | TypedExpressionFormula !Formula
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable TypedExpression where
    locate = \case
        TypedExpressionExpr expression -> locate expression
        TypedExpressionFormula proposition -> locate proposition

instance Locatable Expr where
    locate = \case
        ExprVar x -> locate x
        ExprNaturalNumeral l _ -> l
        ExprOpaqueInteger l _ -> l
        ExprTypedConstant l _ _ -> l
        ExprHigherApply l _ _ -> l
        ExprLambda l _ _ _ -> l
        ExprSelect l _ _ -> l
        ExprOp l _ _ -> l
        ExprStructOp l _ _ -> l
        ExprFiniteSet l _ -> l
        ExprSep l _ _ _ -> l
        ExprReplace l _ _ _ -> l
        ExprReplacePred l _ _ _ _ -> l
        ExprStructAggregate l _ _ -> l
        ExprStructReduct l _ _ -> l
        ExprStructReconstruction l _ _ _ -> l


data LexicalItem = LexicalItem Pattern Marker deriving (Show, Generic, NFData)

instance Eq LexicalItem where
    LexicalItem p _ == LexicalItem p' _ = p == p'

instance Ord LexicalItem where
    compare (LexicalItem p _) (LexicalItem p' _) = compare p p'

instance Hashable LexicalItem where
    hashWithSalt s (LexicalItem p _) = hashWithSalt s p

-- | The syntactic side on which an adjective was declared.  Predicative
-- occurrences retain this distinction so semantic elaboration never has to
-- guess it from proof context or try both parser readings.
data AdjectiveSide
    = LeftAdjectiveSide
    | RightAdjectiveSide
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)

-- | The marker-free parser identity shared by declarations and occurrences of
-- a user-defined adjective.
newtype AdjectiveSurfaceKey = AdjectiveSurfaceKey Pattern
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

-- | User adjectives deliberately lose their declaration marker after source
-- occurrence association.  Intrinsic adjective syntax, currently @equal to@,
-- retains its fixed identity and bypasses user-defined reading selection.
data AdjectiveLexicalIdentity
    = UserAdjectiveIdentity !AdjectiveSurfaceKey
    | IntrinsicAdjectiveIdentity !Pattern !Marker
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)

data AdjectiveLexicalItem = AdjectiveLexicalItem
    { adjectiveLexicalSide :: !AdjectiveSide
    , adjectiveLexicalIdentity :: !AdjectiveLexicalIdentity
    } deriving (Show, Eq, Ord, Generic, Hashable, NFData)

data LexicalItemSgPl = LexicalItemSgPl (SgPl Pattern) Marker deriving (Show, Generic, NFData)

instance Eq LexicalItemSgPl where
    LexicalItemSgPl p _ == LexicalItemSgPl p' _ = sg p == sg p'

instance Ord LexicalItemSgPl where
    compare (LexicalItemSgPl p _) (LexicalItemSgPl p' _) = compare (sg p) (sg p')

instance Hashable LexicalItemSgPl where
    hashWithSalt s (LexicalItemSgPl p _) = hashWithSalt s (sg p)

data VerbLexicalItem = VerbLexicalItem !VerbSurfaces !Marker
    deriving (Show, Generic, NFData)

instance Eq VerbLexicalItem where
    VerbLexicalItem surfaces _ == VerbLexicalItem surfaces' _ =
        surfaces == surfaces'

instance Ord VerbLexicalItem where
    compare
            (VerbLexicalItem surfaces _)
            (VerbLexicalItem surfaces' _) =
        compare surfaces surfaces'

instance Hashable VerbLexicalItem where
    hashWithSalt salt (VerbLexicalItem surfaces _marker) =
        hashWithSalt salt surfaces

data Associativity
  = LeftAssoc
  | NonAssoc
  | RightAssoc
  deriving (Eq, Show, Ord, Generic, Hashable, NFData)

data MixfixItem = MixfixItem Pattern Marker Associativity deriving (Eq, Show, Ord, Generic, Hashable, NFData)

data Pattern = End | HoleCons Pattern | TokenCons Token Pattern deriving (Eq, Show, Ord, Generic, Hashable, NFData)

type FunctionSymbol = MixfixItem

newtype ParameterArity = ParameterArity Natural
    deriving stock (Show, Eq, Ord, Generic)
    deriving newtype (Hashable, NFData)

zeroParameterArity :: ParameterArity
zeroParameterArity = ParameterArity 0

parameterArityOf :: Foldable f => f a -> ParameterArity
parameterArityOf = ParameterArity . fromIntegral . length

parameterArityValue :: ParameterArity -> Natural
parameterArityValue (ParameterArity arity) = arity

data RelationSymbol
    = RelationSymbol Token ParameterArity Marker
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)

newtype StructSymbol = StructSymbol { unStructSymbol :: Text }
    deriving newtype (Show, Eq, Ord, Hashable, NFData)

pattern ElementSymbol, NotElementSymbol :: RelationSymbol
pattern ElementSymbol =
    RelationSymbol (Command "in") (ParameterArity 0) "elem"
pattern NotElementSymbol =
    RelationSymbol (Command "notin") (ParameterArity 0) "notelem"

pattern EqSymbol, NeqSymbol, SubseteqSymbol :: RelationSymbol
pattern EqSymbol =
    RelationSymbol (Symbol "=") (ParameterArity 0) "eq"
pattern NeqSymbol =
    RelationSymbol (Command "neq") (ParameterArity 0) "neq"
pattern SubseteqSymbol =
    RelationSymbol (Command "subseteq") (ParameterArity 0) "subseteq"

-- | The ordinary source-level @cons@ function symbol.
--
-- Finite-set notation is intrinsic and does not desugar through this symbol.
pattern ConsSymbol :: FunctionSymbol
pattern ConsSymbol =
    MixfixItem
        (TokenCons (Command "cons")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR
                        (TokenCons InvisibleBraceL
                            (HoleCons
                                (TokenCons InvisibleBraceR End)))))))
        "cons"
        NonAssoc

-- | The predefined @pair@ function symbol used for desugaring tuple notation..
pattern PairSymbol :: FunctionSymbol
pattern PairSymbol =
    MixfixItem
        (TokenCons (Command "pair")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR
                        (TokenCons InvisibleBraceL
                            (HoleCons
                                (TokenCons InvisibleBraceR End)))))))
        "pair"
        NonAssoc

-- | The concrete binary-tuple surface recognized by the dedicated tuple
-- grammar. It lowers to 'PairSymbol'.
tupleSurfacePattern :: Pattern
tupleSurfacePattern =
    TokenCons ParenL
        (HoleCons
            (TokenCons (Symbol ",")
                (HoleCons
                    (TokenCons ParenR End))))

-- | The predefined unordered-pair function symbol.
pattern UpairSymbol :: FunctionSymbol
pattern UpairSymbol =
    MixfixItem
        (TokenCons (Command "upair")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR
                        (TokenCons InvisibleBraceL
                            (HoleCons
                                (TokenCons InvisibleBraceR End)))))))
        "upair"
        NonAssoc

-- | The fixed family-union function symbol.
pattern UnionsSymbol :: FunctionSymbol
pattern UnionsSymbol =
    MixfixItem
        (TokenCons (Command "unions")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR End))))
        "unions"
        NonAssoc

-- | Function application /@f(x)@/ desugars to /@\apply{f}{x}@/.
pattern ApplySymbol :: FunctionSymbol
pattern ApplySymbol =
    MixfixItem
        (TokenCons (Command "apply")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR
                        (TokenCons InvisibleBraceL
                            (HoleCons
                                (TokenCons InvisibleBraceR End)))))))
        "apply"
        NonAssoc

pattern DomSymbol :: FunctionSymbol
pattern DomSymbol =
    MixfixItem
        (TokenCons (Command "dom")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR End))))
        "dom"
        NonAssoc

-- | The standard-library function-set constructor used by the dedicated
-- set-coded map assertion /@$f:A\to B$@/.
--
-- The surface assertion retains its own formula node for rendering, but its
-- checked meaning is ordinary membership in this source-owned function set.
pattern FunsSymbol :: FunctionSymbol
pattern FunsSymbol =
    MixfixItem
        (TokenCons (Command "funs")
            (TokenCons InvisibleBraceL
                (HoleCons
                    (TokenCons InvisibleBraceR
                        (TokenCons InvisibleBraceL
                            (HoleCons
                                (TokenCons InvisibleBraceR End)))))))
        "funs"
        NonAssoc

pattern CarrierSymbol :: StructSymbol
pattern CarrierSymbol = StructSymbol "carrier"

patternFromHoley :: Holey Token -> Pattern
patternFromHoley = foldr step End
    where
        step = \case
            Nothing -> HoleCons
            Just tok -> TokenCons tok

patternToHoley :: Pattern -> Holey Token
patternToHoley = \case
    End -> []
    HoleCons pat -> Nothing : patternToHoley pat
    TokenCons tok pat -> Just tok : patternToHoley pat

mixfixPattern :: MixfixItem -> Pattern
mixfixPattern (MixfixItem pat _ _) = pat

mixfixMarker :: MixfixItem -> Marker
mixfixMarker (MixfixItem _ m _) = m

mixfixAssoc :: MixfixItem -> Associativity
mixfixAssoc (MixfixItem _ _ assoc) = assoc

mkMixfixItem :: Holey Token -> Marker -> Associativity -> MixfixItem
mkMixfixItem pat m assoc = MixfixItem (patternFromHoley pat) m assoc

lexicalItemPattern :: LexicalItem -> Pattern
lexicalItemPattern (LexicalItem pat _) = pat

lexicalItemMarker :: LexicalItem -> Marker
lexicalItemMarker (LexicalItem _ m) = m

lexicalItemPhrase :: LexicalItem -> LexicalPhrase
lexicalItemPhrase = patternToHoley . lexicalItemPattern

adjectiveLexicalPattern :: AdjectiveLexicalItem -> Pattern
adjectiveLexicalPattern item =
    case adjectiveLexicalIdentity item of
        UserAdjectiveIdentity (AdjectiveSurfaceKey pat) -> pat
        IntrinsicAdjectiveIdentity pat _marker -> pat

adjectiveLexicalMarker :: AdjectiveLexicalItem -> Maybe Marker
adjectiveLexicalMarker item =
    case adjectiveLexicalIdentity item of
        UserAdjectiveIdentity{} -> Nothing
        IntrinsicAdjectiveIdentity _pat marker -> Just marker

adjectiveLexicalPhrase :: AdjectiveLexicalItem -> LexicalPhrase
adjectiveLexicalPhrase = patternToHoley . adjectiveLexicalPattern

userAdjectiveLexicalItem
    :: AdjectiveSide
    -> Pattern
    -> AdjectiveLexicalItem
userAdjectiveLexicalItem side pat =
    AdjectiveLexicalItem side
        (UserAdjectiveIdentity (AdjectiveSurfaceKey pat))

intrinsicAdjectiveLexicalItem
    :: AdjectiveSide
    -> Pattern
    -> Marker
    -> AdjectiveLexicalItem
intrinsicAdjectiveLexicalItem side pat marker =
    AdjectiveLexicalItem side
        (IntrinsicAdjectiveIdentity pat marker)

lexicalItemSgPlPattern :: LexicalItemSgPl -> SgPl Pattern
lexicalItemSgPlPattern (LexicalItemSgPl pat _) = pat

lexicalItemSgPlMarker :: LexicalItemSgPl -> Marker
lexicalItemSgPlMarker (LexicalItemSgPl _ m) = m

lexicalItemSgPlPhrase :: LexicalItemSgPl -> SgPl LexicalPhrase
lexicalItemSgPlPhrase = fmap patternToHoley . lexicalItemSgPlPattern

mkLexicalItem :: LexicalPhrase -> Marker -> LexicalItem
mkLexicalItem pat m = LexicalItem (patternFromHoley pat) m

mkLexicalItemSgPl :: SgPl LexicalPhrase -> Marker -> LexicalItemSgPl
mkLexicalItemSgPl pat m = LexicalItemSgPl (patternFromHoley <$> pat) m

verbLexicalSurfaces :: VerbLexicalItem -> VerbSurfaces
verbLexicalSurfaces (VerbLexicalItem surfaces _marker) = surfaces

verbLexicalMarker :: VerbLexicalItem -> Marker
verbLexicalMarker (VerbLexicalItem _surfaces marker) = marker

relationSymbolToken :: RelationSymbol -> Token
relationSymbolToken (RelationSymbol tok _ _) = tok

relationSymbolParameterArity :: RelationSymbol -> ParameterArity
relationSymbolParameterArity (RelationSymbol _ arity _) = arity

relationSymbolMarker :: RelationSymbol -> Marker
relationSymbolMarker (RelationSymbol _ _ m) = m

relationSymbolPattern :: RelationSymbol -> Pattern
relationSymbolPattern rel =
    HoleCons (TokenCons (relationSymbolToken rel) (HoleCons End))

structSymbolPattern :: StructSymbol -> Pattern
structSymbolPattern (StructSymbol c) = TokenCons (Command c) End

patternToken :: Pattern -> Maybe Token
patternToken = \case
    TokenCons tok End -> Just tok
    _ -> Nothing

tokenMarker :: Token -> Maybe Marker
tokenMarker = \case
    Word word -> Just (Marker word)
    Symbol symbol -> Just (Marker symbol)
    Command command -> Just (Marker command)
    Integer integer -> Just (Marker (Text.pack (show integer)))
    Variable{} -> Nothing
    CommandReference{} -> Nothing
    NamedItem{} -> Nothing
    CaseHeading{} -> Just (Marker "caseOf")
    Label{} -> Nothing
    Ref{} -> Nothing
    BeginEnv{} -> Nothing
    EndEnv{} -> Nothing
    ParenL -> Nothing
    ParenR -> Nothing
    BracketL -> Nothing
    BracketR -> Nothing
    VisibleBraceL -> Nothing
    VisibleBraceR -> Nothing
    InvisibleBraceL -> Nothing
    InvisibleBraceR -> Nothing

pattern ExprApp :: Location -> Expr -> Expr -> Expr
pattern ExprApp loc e1 e2 = ExprOp loc ApplySymbol [e1, e2]

pattern ExprPair :: Location -> Expr -> Expr -> Expr
pattern ExprPair loc e1 e2 = ExprOp loc PairSymbol [e1, e2]

-- | Tuples are interpreted as nested pairs:
-- the triple /@(a, b, c)@/ is interpreted as
-- /@(a, (b, c))@/.
-- This means that the product operation should also
-- be right associative, so that /@(a, b, c)@/ can
-- form elements of /@A\times B\times C@/.
makeTuple :: Location -> NonEmpty Expr -> Expr
makeTuple l = \case
    e :| [] -> e
    e :| (e' : es) -> ExprPair l e (makeTuple l (e' :| es))


data Chain
    = ChainBase (NonEmpty Expr) Sign Relation (NonEmpty Expr) -- left arguments, possibly empty list of parameters, right arguments
    | ChainCons (NonEmpty Expr) Sign Relation Chain
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Chain where
    locate (ChainBase lhs _ _ _) = locate lhs
    locate (ChainCons lhs _ _ _) = locate lhs

data Relation
    = Relation Location RelationSymbol [Expr] -- ^  E.g.: /@x \in X@/, potentially with parameters in braces
    | RelationExpr Location Expr   -- ^  E.g.: /@x \mathrel{R} y@/
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Relation where
    locate = \case
        Relation l _ _ -> l
        RelationExpr l _ -> l

data Sign = Positive | Negative deriving (Show, Eq, Ord, Generic, NFData)

data Formula
    = FormulaChain Chain
    | FormulaSetMap Location Expr Expr Expr
    -- ^ A set-coded map assertion /@$f:A\to B$@/. It lowers to
    -- /@$f\in\funs{A}{B}$@/, not to a logical concrete type.
    | FormulaExpression Expr
    -- ^ A symbolic expression used as a statement; checked elaboration
    -- requires it to have type Prop.
    | FormulaPredicate Location PrefixPredicate Marker (NonEmpty Expr)
    | Connected Location Connective Formula Formula
    | FormulaNeg Location Formula
    | FormulaQuantified Location Quantifier (NonEmpty VarSymbol) Bound Formula
    | FormulaTypedQuantified
        Location Quantifier (NonEmpty VarSymbol) ConcreteType Formula
    | PropositionalConstant Location PropositionalConstant
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Formula where
    locate = \case
        FormulaChain chain -> locate chain
        FormulaSetMap location _function _domain _codomain -> location
        FormulaExpression expression -> locate expression
        FormulaPredicate l _ _ _ -> l
        Connected l _ _ _ -> l
        FormulaNeg l _ -> l
        FormulaQuantified l _ _ _ _ -> l
        FormulaTypedQuantified l _ _ _ _ -> l
        PropositionalConstant l _ -> l


-- | Expanded raw meaning of a set-coded map assertion.
setMapFormulaChain :: Location -> Expr -> Expr -> Expr -> Chain
setMapFormulaChain location function domain codomain =
    ChainBase
        (function :| [])
        Positive
        (Relation location ElementSymbol [])
        (ExprOp location FunsSymbol [domain, codomain] :| [])

data PropositionalConstant = IsBottom | IsTop
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)

data PrefixPredicate
    = PrefixPredicate Text Int
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)


data Connective
    = Conjunction
    | Disjunction
    | Implication
    | Equivalence
    | ExclusiveOr
    | NegatedDisjunction
    deriving (Show, Eq, Ord, Generic, Hashable, NFData)



mixfixLoc :: Locatable a => Holey (Located Token) -> [a] -> Location
mixfixLoc parts args0 = go parts args0
    where
        go [] _ = Nowhere
        go (Just ltok : _parts') _args' = startPos ltok
        go (Nothing : parts') (a : args')
            | locate a == Nowhere = go parts' args'
            | otherwise = locate a
        go (Nothing : parts') [] = go parts' []

type StructPhrase = LexicalItemSgPl

data StructApplication a = StructApplication
    { structApplicationPhrase :: StructPhrase
    , structApplicationArguments :: [a]
    }
    deriving (Show, Eq, Ord, Generic, NFData)

mapStructApplication
    :: (a -> b)
    -> StructApplication a
    -> StructApplication b
mapStructApplication transform (StructApplication structurePhrase arguments) =
    StructApplication structurePhrase (transform <$> arguments)

data StructNounPhraseOf a = StructNounPhrase
    { structPhraseLeftModifiers :: [AdjLOf a]
    , structPhraseCore :: StructApplication a
    , structPhraseRightModifiers :: [AdjROf a]
    , structPhraseResidual :: Maybe Stmt
    }
    deriving (Show, Eq, Ord, Generic, NFData)

-- | For example 'an integer' would be
-- > Noun (lexicalPhrase (Just "integer" :| [])) []
type Noun = NounOf Term
data NounOf a
    = Noun Location LexicalItemSgPl [a]
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (NounOf a) where
    locate (Noun l _ _) = l




type NounPhrase t = NounPhraseOf t Term

-- A name slot owns one shared bound. The container retains the existing
-- nameless, optional-single-name, and grouped-name distinctions. A real bound
-- requires a nonempty name slot and is admitted only by binding hosts.
data NounBinder names = NounBinder
    { nounBinderNames :: names
    , nounBinderBound :: Bound
    }
    deriving (Show, Eq, Ord, Generic, NFData)

unboundedNounBinder :: names -> NounBinder names
unboundedNounBinder names = NounBinder names Unbounded

-- NOTE: 'NounPhraseOf' is only used with arguments of type 'Term',
-- but keeping the argument parameter @a@ allows the 'Show' and 'Eq'
-- instances to remain decidable.
data NounPhraseOf t a
    = NounPhrase [AdjLOf a] (NounOf a) (NounBinder (t VarSymbol)) [AdjROf a] (Maybe Stmt)
    deriving (Generic)

instance (Show a, Show (t VarSymbol)) => Show (NounPhraseOf t a) where
    show (NounPhrase ls n vs rs ms) =
        "NounPhrase ("
            <> show ls <> ") ("
            <> show n <> ") ("
            <> showNames vs <> ") ("
            <> show rs <> ") ("
            <> show ms <> ")"
      where
        showNames (NounBinder names Unbounded) = show names
        showNames binder = show binder

instance (Eq a, Eq (t VarSymbol)) => Eq (NounPhraseOf t a) where
    NounPhrase ls n vs rs ms == NounPhrase ls' n' vs' rs' ms' =
        ls == ls' && n == n' && vs == vs' && rs == rs' && ms == ms'

-- Raw syntax uses this lexicographic order for deterministic deduplication.
instance (Ord a, Ord (t VarSymbol)) => Ord (NounPhraseOf t a) where
    NounPhrase ls n vs rs ms `compare` NounPhrase ls' n' vs' rs' ms' =
        compare
            (ls, n, vs, rs, ms)
            (ls', n', vs', rs', ms')

instance
    (NFData a, NFData (t VarSymbol))
    => NFData (NounPhraseOf t a)

-- | @Nameless a@ is quivalent to @Const () a@ (from "Data.Functor.Const").
-- It describes a container that is unwilling to actually contain something.
-- @Nameless@ lets us treat nouns with no names, one name, or many names uniformly.
-- Thus @NounPhraseOf Nameless a@ is a noun phrase without a name and with arguments
-- of type @a@.
data Nameless a = Nameless deriving (Show, Eq, Ord, Generic, NFData)


-- | Left adjectives modify nouns from the left side,
-- e.g. /@even@/, /@continuous@/, and /@σ-finite@/.
type AdjL = AdjLOf Term
data AdjLOf a
    = AdjL Location AdjectiveLexicalItem [a]
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (AdjLOf a) where
    locate (AdjL l _ _) = l


-- | Right attributes consist of basic right adjectives, e.g.
-- /@divisible by ?@/, or /@of finite type@/ and verb phrases
-- marked with /@that@/, such as /@integer that divides n@/.
-- In some cases these right attributes may be followed
-- by an additional such-that phrase.
type AdjR = AdjROf Term
data AdjROf a
    = AdjR Location AdjectiveLexicalItem [a]
    | AttrRThat VerbPhrase
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (AdjROf a) where
    locate (AdjR l _ _) = l
    locate (AttrRThat vp) = locate vp

-- | Predicative adjectives, such as /@n is even@/.  The source side remains
-- part of the lexical item so this syntax has one parser result and later
-- semantic reading selection is static.
type Adj = AdjOf Term
data AdjOf a
    = Adj Location AdjectiveLexicalItem [a]
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (AdjOf a) where
    locate (Adj l _ _) = l


type Verb = VerbOf Term
data VerbOf a
    = Verb Location VerbLexicalItem [a]
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (VerbOf a) where
    locate (Verb l _ _) = l


type Fun = FunOf Term
data FunOf a
    = Fun {loc :: Location, phrase :: LexicalItemSgPl, funArgs :: [a]}
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (FunOf a) where
    locate = (.loc)


type VerbPhrase = VerbPhraseOf Term
data VerbPhraseOf a
    = VPVerb (VerbOf a)
    | VPAdj (NonEmpty (AdjOf a)) -- ^ @x is foo@ / @x is foo and bar@
    | VPVerbNot (VerbOf a)
    | VPAdjNot (NonEmpty (AdjOf a)) -- ^ @x is not foo@ / @x is neither foo nor bar@
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable (VerbPhraseOf a) where
    locate = \case
        VPVerb v -> locate v
        VPAdj adjs -> locate adjs
        VPVerbNot v -> locate v
        VPAdjNot adjs -> locate adjs


data Quantifier
    = Universally
    | Existentially
    | Nonexistentially
    deriving (Show, Eq, Ord, Generic, NFData)

data QuantPhrase = QuantPhrase Quantifier (NounPhrase []) deriving (Show, Eq, Ord, Generic, NFData)


data Term
    = TermExpr Expr
    -- ^ A symbolic expression.
    | TermFun Fun
    -- ^ Definite noun phrase, e.g. /@the derivative of $f$@/.
    | TermIota Location VarSymbol Stmt
    -- ^ Definite descriptor, e.g. /@an $x$ such that ...@//
    | TermQuantified Quantifier Location (NounPhrase Maybe)
    -- ^ Indefinite quantified notion, e.g. /@every even integer that divides $k$ ...@/.
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Term where
    locate :: Term -> Location
    locate (TermExpr e) = locate e
    locate (TermFun f) = f.loc
    locate (TermIota l _ _) = l
    locate (TermQuantified _ l _) = l


data Stmt
    = StmtFormula {formula :: Formula} -- ^ E.g.: /@We have \<Formula\>@/.
    | StmtVerbPhrase {args :: NonEmpty Term, verb :: VerbPhrase} -- ^ E.g.: /@\<Term\> and \<Term\> \<verb\>@/.
    | StmtNoun {polarity :: Sign, args :: NonEmpty Term, noun :: (NounPhrase Maybe)}
    -- ^ Noun predication: /@\<Term\> is [not] a(n) \<NP\>@/.
    -- Polarity applies to each subject's complete noun predicate, inside
    -- subject quantifiers. Sentence negation is represented by 'StmtNeg'.
    | StmtStruct Term (StructNounPhraseOf Term)
    | StmtNeg {loc :: Location, stmt :: Stmt} -- ^ E.g.: /@It is not the case that \<Stmt\>@/.
    | StmtExists {loc :: Location, np :: NounPhrase []} -- ^ E.g.: /@There exists a(n) \<NP\>@/.
    | StmtConnected {conn :: Connective, mloc :: Maybe Location, stmt1 :: Stmt, stmt2 :: Stmt}
    | StmtQuantPhrase {loc :: Location, qp :: QuantPhrase, stmt :: Stmt}
    | SymbolicQuantified {loc :: Location, quant :: Quantifier, vars :: NonEmpty VarSymbol, b :: Bound, suchThat :: Maybe Stmt, stmt :: Stmt}
    | StmtExactStruct Term (StructApplication Term)
    -- ^ The full structure predicate together with exact record shape.
    -- Appended to preserve generic parsed-payload constructor tags.
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Stmt where
    locate :: Stmt -> Location
    locate StmtFormula{formula = phi} = locate phi
    locate StmtConnected{mloc = Just p} = p
    locate StmtConnected{mloc = Nothing, stmt1 = s} = locate s
    locate StmtVerbPhrase{args = a :| _} = locate a
    locate StmtNoun{args = a :| _} = locate a
    locate (StmtStruct a _structure) = locate a
    locate StmtNeg{loc = p} = p
    locate StmtExists{loc = p} = p
    locate StmtQuantPhrase{loc = p} = p
    locate SymbolicQuantified{loc = p} = p
    locate (StmtExactStruct a _structure) = locate a

data Bound = Unbounded | Bounded Location Sign Relation Expr deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Bound where
    locate = \case
        Unbounded -> Nowhere
        Bounded l _ _ _ -> l

pattern SymbolicForall :: Location -> NonEmpty VarSymbol -> Bound -> Maybe Stmt -> Stmt -> Stmt
pattern SymbolicForall loc vs bound suchThat have = SymbolicQuantified loc Universally vs bound suchThat have

pattern SymbolicExists :: Location -> NonEmpty VarSymbol -> Bound -> Stmt -> Stmt
pattern SymbolicExists loc vs bound suchThat = SymbolicQuantified loc Existentially vs bound Nothing suchThat

makeSymbolicNotExists :: Location -> NonEmpty VarSymbol -> Bound -> Stmt -> Stmt
makeSymbolicNotExists p vs bound st = StmtNeg p (SymbolicExists p vs bound st)

data Asm
    = AsmSuppose Stmt
    | AsmLetNoun (NonEmpty VarSymbol) (NounPhrase Maybe) -- ^ E.g.: /@let k be an integer@/
    | AsmLetIn (NonEmpty VarSymbol) Expr -- ^ E.g.: /@let $k\in\integers$@/
    | AsmLetThe VarSymbol Fun -- ^ E.g.: /@let $g$ be the derivative of $f$@/
    | AsmLetEq VarSymbol Expr -- ^ E.g.: /@let $m = n + k$@/
    | AsmLetStruct (NonEmpty VarSymbol) (StructNounPhraseOf Term)
    -- ^ E.g.: /@let $M,N$ be left modules over $R$@/.
    | AsmLetRelation (NonEmpty VarSymbol) Relation Expr
    -- ^ E.g.: /@let $A,B \subseteq C$@/.
    deriving (Show, Eq, Ord, Generic, NFData)

data Axiom = Axiom [Asm] Stmt
    deriving (Show, Eq, Ord, Generic, NFData)

data Claim = Claim [Asm] Stmt
    deriving (Show, Eq, Ord, Generic, NFData)

-- | The head of the definition describes the part before the /@iff@/,
-- i.e. the definiendum. An optional noun-phrase corresponds to an optional
-- type annotation for the 'Term' of the head. The last part of the head
-- is the lexical phrase that is defined.
--
-- > "A natural number   $n$        divides $m$   iff   ..."
-- >  ^^^^^^^^^^^^^^^^   ^^^        ^^^^^^^^^^^         ^^^
-- >  type annotation    variable   verb                definiens
-- >  (a noun phrase)               (all args are vars) (a statement)
--
data DefnHead
    = DefnAdj VarSymbol (AdjOf VarSymbol)
    | DefnVerb VarSymbol (VerbOf VarSymbol)
    | DefnNoun VarSymbol (NounOf VarSymbol)
    | DefnSymbolicPredicate PrefixPredicate Marker (NonEmpty VarSymbol)
    | DefnRel VarSymbol RelationSymbol [VarSymbol] VarSymbol
    -- ^ E.g.: /@$x \subseteq y$ iff [...@/
    deriving (Show, Eq, Ord, Generic, NFData)

data Defn
    = Defn [Asm] DefnHead Stmt
    | DefnFun
        [Asm]
        (FunOf VarSymbol)
        (Maybe Term)
        Term
        (Maybe DefinitionResultPhrase)
    -- ^ A 'DefnFun' consists of the functional noun (which must start with /@the@/)
    -- and an optional specification of a symbolic equivalent. The symbolic equivalent
    -- does not need to have the same variables as the full functional noun pattern.
    --
    -- > "The tensor product of $U$ and $V$ over $K$, $U\tensor V$, is ..."
    -- >  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^     ^^^
    -- >  definiendum                                 symbolic eqv.    definiens
    -- >  (a functional noun)                         (an exression)   (a term)
    --
    | DefnOp [Asm] SymbolPattern Expr (Maybe DefinitionResultPhrase)
    | DefnTypedConstant
        Location Token ConcreteType TypedExpression
    deriving (Show, Eq, Ord, Generic, NFData)

-- | The deliberately narrow source attachment used by result-annotated
-- set-valued definitions. Elaboration, rather than the raw syntax type,
-- checks that the phrase denotes one supported atomic notion.
type DefinitionResultPhrase = NounPhrase Nameless

data CalcQuantifier
    = CalcQuantifier (NonEmpty VarSymbol) Bound (Maybe Stmt)
    deriving (Show, Eq, Ord, Generic, NFData)

data HaveIntro
    = HaveNoIntro
    | HaveWeHave
    | HaveThus
    | HaveHence
    | HaveThen
    | HaveNext
    | HaveNow
    | HaveFirst
    | HaveFinally
    | HaveSubsequently
    | HaveUltimately
    | HaveTherefore
    | HaveParticularly
    | HaveInParticular
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data AssumeIntro
    = AssumeIntroAssume
    | AssumeIntroSuppose
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data FixBinder
    = FixBinderSymbolic (NonEmpty VarSymbol) Bound
    | FixBinderTyped (NonEmpty VarSymbol) ConcreteType
    deriving (Show, Eq, Ord, Generic, NFData)

data Proof
    = Omitted Location
    | Qed (Maybe Location) Justification
    -- ^ Ends of a proof, leaving automation to discharge the current goal using the given justification.
    | Contradiction Location Justification
    -- ^ Ends a proof by deriving absurdity using the given justification.
    | ByCase Location [Case]
    | ByContradiction Location Proof
    | BySetInduction Location (Maybe Term) Proof
    -- ^ ∈-induction.
    | ByOrdInduction Location Proof
    -- ^ Transfinite induction for ordinals.
    | ByStructuralInduction Location VarSymbol (NonEmpty NamedCase)
    | Assume Location AssumeIntro Stmt Proof
    | Fix Location (NonEmpty FixBinder) (Maybe Stmt) Proof
    | Calc Location (Maybe CalcQuantifier) Calc Proof
    -- ^ Simplify goals that are implications or disjunctions.
    | TakeVar Location (NonEmpty VarSymbol) Bound Stmt Justification Proof
    | TakeTyped
        Location (NonEmpty VarSymbol) ConcreteType Stmt Justification Proof
    | TakeNoun Location (NounPhrase []) Justification Proof
    | Have Location HaveIntro Stmt Justification Proof
    | Since
        Location Stmt Justification
        Location Stmt Justification
        Proof
    -- ^ /@Since P [by ...], we have Q [by ...].@/  The first claim is
    -- available only while proving the second; only the second persists.
    | Suffices Location Stmt Justification Proof
    -- ^ /@It suffices to show that [...]. [...]@/
    | Subclaim Location Stmt Proof Proof
    -- ^ A claim is a sublemma with its own proof:
    --  /@Show \<goal stmt\>. \<steps\>. \<continue other proof\>.@/
    | Define Location VarSymbol Expr Proof
    -- ^ Local definition.
    --
    | DefineTyped
        Location VarSymbol ConcreteType TypedExpression Proof
    -- ^ Typed local logical definition.
    --
    | DefineFunction Location VarSymbol VarSymbol Expr VarSymbol Expr Proof
    -- ^ Local function definition, e.g. /@Let $f(x) = e$ for $x\\in d$@/.
    -- The first 'VarSymbol' is the newly defined symbol, the second one is the argument.
    -- The first 'Expr' is the value, the final variable and expr specify a bound (the domain of the function).




    | DefineFunctionLocal Location VarSymbol VarSymbol Expr VarSymbol VarSymbol (NonEmpty (Expr, Formula)) Proof
    -- ^ Local function definition, but in this case we give the domain and target an the rules for $xs$ in some sub domains.
    --
    deriving (Show, Eq, Ord, Generic, NFData)

-- | An inline justification.
data Justification
    = JustificationAuto (Maybe (NonEmpty Marker))
    -- ^ Explicit ATP: no citations selects complete locals; citations select
    -- exactly the named global facts and their supported local context.
    | JustificationObviousReferences (NonEmpty Marker)
    | JustificationSetExt
    | JustificationStructureExt
    | JustificationExtensionality
    | JustificationImplicit
    | JustificationAssumption
    | JustificationDefinition
    | JustificationNotion
    deriving (Show, Eq, Ord, Generic, NFData)


-- | A case of a case split.
data Case = Case
    { caseOf :: Stmt
    , caseProof :: Proof
    } deriving (Show, Eq, Ord, Generic, NFData)

data Calc
    = RelationCalculation Expr (NonEmpty CalcRelationLink)
    | Biconditionals Formula (NonEmpty (Formula, Justification))
    deriving (Show, Eq, Ord, Generic, NFData)

data NamedCase = NamedCase
    { namedCaseLocation :: Location
    , namedCaseName :: Text
    , namedCaseProof :: Proof
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data CalcRelationLink = CalcRelationLink
    !Sign
    !Relation
    !Expr
    !Justification
    deriving (Show, Eq, Ord, Generic, NFData)


data Abbreviation
    = AbbreviationAdj VarSymbol (AdjOf VarSymbol) Stmt
    | AbbreviationVerb VarSymbol (VerbOf VarSymbol) Stmt
    | AbbreviationNoun VarSymbol (NounOf VarSymbol) Stmt
    | AbbreviationRel VarSymbol RelationSymbol [VarSymbol] VarSymbol Stmt
    | AbbreviationFun (FunOf VarSymbol) Term
    | AbbreviationEq SymbolPattern Expr
    deriving (Show, Eq, Ord, Generic, NFData)

data Datatype
    = Datatype
        { datatypeHeadExpr :: Expr
        , datatypeClauses :: NonEmpty DatatypeClause
        }
    deriving (Show, Eq, Ord, Generic, NFData)

data DatatypeClause = DatatypeClause
    { datatypeClauseName :: Maybe Text
    , datatypeClauseConstructorExpr :: Expr
    , datatypeClauseTargetExpr :: Expr
    , datatypeClausePremises :: [(VarSymbol, Expr)]
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data RecursiveDefinition = RecursiveDefinition
    { recursiveAssumptions :: [Asm]
    , recursiveHead :: Either SymbolPattern DefnHead
    , recursiveVariable :: VarSymbol
    , recursiveDomain :: Expr
    , recursiveClauses :: NonEmpty RecursiveClause
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data RecursiveClause = RecursiveClause
    { recursiveClauseName :: Maybe Text
    , recursiveClauseEquation :: Either (Expr, Expr) (Formula, Stmt)
    }
    deriving (Show, Eq, Ord, Generic, NFData)

-- Names are prose headings; keys also serve as generated theorem suffixes.
datatypeCaseKey :: Text -> Maybe Text
datatypeCaseKey spelling = do
    let name = Text.strip spelling
        letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
        space c = c `elem` [' ', '\t', '\n', '\r', '\f', '\v']
    (first, _) <- Text.uncons name
    guard (letter first && Text.all (\c -> letter c || ('0' <= c && c <= '9') || c == '_' || space c) spelling)
    pure (Text.intercalate "_" (Text.words (Text.toLower name)))

data Inductive = Inductive
    { inductiveSymbolPattern :: SymbolPattern
    , inductiveDomain :: Expr
    , inductiveIntros :: NonEmpty IntroRule
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data IntroRule = IntroRule
    { introConditions :: [Formula] -- The inductively defined set may only appear as an argument of monotone operations on the rhs.
    , introResult :: Formula -- TODO Refine.
    }
    deriving (Show, Eq, Ord, Generic, NFData)


data SymbolPattern = SymbolPattern FunctionSymbol [VarSymbol]
    deriving (Show, Eq, Ord, Generic, NFData)

data Signature
    = SignatureAdj  VarSymbol (AdjOf  VarSymbol)
    -- The verb and noun forms are available to programmatic AST consumers but
    -- have no concrete source syntax.
    | SignatureVerb VarSymbol (VerbOf VarSymbol)
    | SignatureNoun VarSymbol (NounOf VarSymbol)
    | SignatureSymbolic SymbolPattern (NounPhrase Maybe)
    -- ^ /@$\<symbol\>(\<vars\>)$ is a \<noun\>@/
    | SignatureTypedConstant Location Token ConcreteType
    -- ^ An atomic logical constant, e.g. /@$\Phi : \Set\to\Prop$@/.
    deriving (Show, Eq, Ord, Generic, NFData)


data StructDefn = StructDefn
    { structPreamble :: [Asm]
    -- ^ Explicit parameter declarations and their premises.
    , structPhrase :: StructPhrase
    -- ^ E.g.: @partial order@ or @abelian group@.\
    , structParameters :: [VarSymbol]
    -- ^ Parameters occurring in the declared structure phrase, in source
    -- order. They must be introduced by 'structPreamble'.
    , structParents :: [StructParent]
    -- ^ Structural parents with explicit parameter applications.
    , structLabel :: VarSymbol
    , structFields :: [StructField]
    -- ^ Locally declared fields, distinct from inherited fields and from the
    -- later list of mathematical laws.
    , structAssumes :: [(Marker, Stmt)]
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data StructParent = StructParent
    { structParentApplication :: !(StructApplication Term)
    , structParentLabel :: !(Maybe Marker)
    }
    deriving (Show, Eq, Ord, Generic, NFData)

data StructField = StructField
    { structFieldLocation :: !Location
    , structFieldDescription :: ![Token]
    -- ^ Presentation-only prose such as “a multiplication”.
    , structFieldMarker :: !(Maybe Marker)
    -- ^ Optional source name for the generated specification fact.
    , structFieldSymbol :: !StructSymbol
    , structFieldSpecification :: !(Maybe Stmt)
    -- ^ The source specification, checked during schema elaboration.
    -- 'Nothing' denotes an unconstrained set-valued field.
    }
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable StructField where
    locate = structFieldLocation

-- | A closed named realization of one structure schema.  The name is an
-- atomic set-valued logical constant; elaboration requires the value to be a
-- structure aggregate.  The schema application remains
-- separate from the aggregate annotation so an unannotated aggregate can use
-- the instance head as its immediate, unambiguous context.
data Instance = Instance
    { instanceApplication :: !(StructApplication Term)
    , instanceNameLocation :: !Location
    , instanceNameToken :: !Token
    , instanceValue :: !Expr
    }
    deriving (Show, Eq, Ord, Generic, NFData)

-- | A set-valued provider whose structure result is established by the
-- immediately following proof. Parameters belong to its symbolic head;
-- hypotheses qualify its public consequences, not its total definition.
data Construction = Construction
    { constructionAssumptions :: ![Asm]
    , constructionApplication :: !(StructApplication Term)
    , constructionHead :: !SymbolPattern
    , constructionValue :: !Expr
    }
    deriving (Show, Eq, Ord, Generic, NFData)

newtype Marker = Marker Text
    deriving stock (Show, Eq, Ord, Generic)

deriving newtype instance Hashable Marker
deriving newtype instance NFData Marker

instance IsString Marker where
    fromString str = Marker (Text.pack str)

type BlockTitle = [Token]

data ClaimKind
    = Proposition
    | Theorem
    | Lemma
    | Corollary
    | Composition
    | PlainClaim
    | Classification
    deriving (Show, Eq, Ord, Generic, NFData)

data Block
    = BlockAxiom Location (Maybe BlockTitle) Marker Axiom
    | BlockClaim ClaimKind Location (Maybe BlockTitle) Marker Claim
    | BlockProof Location Proof Location -- ^ Proof start and ending location.
    | BlockDefn Location (Maybe BlockTitle) Marker Defn
    | BlockAbbr Location (Maybe BlockTitle) Marker Abbreviation
    | BlockData Location (Maybe BlockTitle) Marker Datatype
    | BlockInductive Location (Maybe BlockTitle) Marker Inductive
    | BlockSig Location (Maybe BlockTitle) Marker [Asm] Signature
    | BlockStruct Location (Maybe BlockTitle) Marker StructDefn
    -- Parsed payloads follow the generic sum layout; adding a block requires
    -- advancing the cache epoch even when the new constructor is appended.
    | BlockInstance Location (Maybe BlockTitle) Marker Instance
    | BlockConstruction Location (Maybe BlockTitle) Marker Construction
    | BlockRecursive Location (Maybe BlockTitle) Marker RecursiveDefinition
    deriving (Show, Eq, Ord, Generic, NFData)

instance Locatable Block where
    locate = \case
        BlockAxiom location _title _marker _axiom -> location
        BlockClaim _kind location _title _marker _claim -> location
        BlockProof location _proof _end -> location
        BlockDefn location _title _marker _definition -> location
        BlockAbbr location _title _marker _abbreviation -> location
        BlockData location _title _marker _datatype -> location
        BlockInductive location _title _marker _inductive -> location
        BlockSig location _title _marker _assumptions _signature -> location
        BlockStruct location _title _marker _structure -> location
        BlockInstance location _title _marker _instance -> location
        BlockConstruction location _title _marker _construction -> location
        BlockRecursive location _title _marker _definition -> location
