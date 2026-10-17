{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

-- | Concrete syntax of the surface language.
module Felix.Syntax.Concrete
    ( grammar
    , grammarPrepared
    , ConcreteSyntaxError(..)
    , NativeMathParser
    , NativeMath(..)
    , NativePhraseResolution(..)
    , prepareNativeMathParser
    , parseNativeMath
    , lookupNativePhrase
    , NativeMathParseError(..)
    , NativeMathFailure(..)
    ) where

import Base
import Felix.Syntax.Abstract
import Felix.Syntax.Concrete.Keywords
import Felix.Syntax.Interface (CanonicalLexicalEntry(..))
import Felix.Syntax.Phrase
import Felix.Syntax.FieldEnvelope
import Felix.Source.Scan qualified as SourceScan
import Felix.Syntax.Lexicon
    ( ConnectiveSyntax(..)
    , Lexicon(..)
    , SignatureHeadForm(..)
    , concreteSignatureHeadForms
    , lexiconAdjs
    , splitOnVariableSlot
    )
import Felix.Syntax.Token
import Felix.Syntax.Prepared qualified as Prepared
import Felix.Report.Location

import Data.Bifunctor qualified as Bifunctor
import Data.List.NonEmpty qualified as NonEmpty
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Text.Earley
    ( Grammar
    , Parser
    , Prod
    , Report(..)
    , (<?>)
    , fullParses
    , parser
    , rule
    , satisfy
    , terminal
    )
import Felix.Syntax.Mixfix


grammar
    :: Lexicon
    -> Grammar r
        (Prod r Text (Located Token) (Either ConcreteSyntaxError Block))
-- | Convenience entry point for direct lexicons. Module and native-parser
-- owners prepare once explicitly; do not call this wrapper in chunk loops.
grammar lexicon =
    let prepared = Prepared.prepareLexicon lexicon
    in Prepared.forcePreparedLexicon prepared `seq` grammarPrepared prepared

grammarPrepared
    :: Prepared.PreparedLexicon
    -> Grammar r
        (Prod r Text (Located Token) (Either ConcreteSyntaxError Block))
grammarPrepared prepared = concreteGrammarBlock <$> concreteGrammar prepared

data ConcreteSyntaxError
    = InvalidFieldEnvelope !FieldEnvelopeError
    | InvalidFieldContents !Location !Text
    | OwnedStructureFieldReceiverMismatch
        !Location
        !VarSymbol
        !Expr
    deriving (Eq, Ord)

instance Show ConcreteSyntaxError where
    show (InvalidFieldEnvelope failure) = show failure
    show (InvalidFieldContents location message) =
        "invalid structure field at " <> prettyLocation location <> ": " <> Text.unpack message
    show (OwnedStructureFieldReceiverMismatch location receiver owner) =
        "owned structure field at "
            <> prettyLocation location
            <> " must use the declared receiver "
            <> show receiver
            <> "; found "
            <> show owner

data NativeMath
    = NativeTypedExpression !TypedExpression
    | NativeConcreteType !ConcreteType
    | NativeVariableList !(NonEmpty Text)
    deriving (Show, Eq, Ord)

data NativeMathParseError
    = NativeMathTokenError !Text
    | NativeMathUnconsumed ![Text] !(NonEmpty Token)
    | NativeMathEmptyParse
    | NativeMathAmbiguous !Int
    deriving (Show, Eq)

data NativeMathFailure
    = NativeMathRejected !NativeMathParseError
    | NativeMathScannerInvariant
        !SourceScan.SourceScanInvariantError
    deriving (Show, Eq)

data NativeMathParser = NativeMathParser
    !(Parser Text [Located Token] NativeMath)
    !(Map Text (Set NativePhraseBinding))

data NativePhraseResolution
    = NoNativePhrase
    | UniqueNativePhrase !NativePhraseBinding
    | AmbiguousNativePhrase !(NonEmpty NativePhraseBinding)
    deriving (Show, Eq)

prepareNativeMathParser :: Lexicon -> NativeMathParser
prepareNativeMathParser lexicon =
    Prepared.forcePreparedLexicon prepared `seq`
    NativeMathParser
        (parser do
            ConcreteGrammar{..} <- concreteGrammar prepared
            pure
                ((NativeTypedExpression <$> concreteGrammarTypedExpression)
                    <|> (NativeConcreteType <$> concreteGrammarType)))
        (nativePhraseBindings (Prepared.preparedInventory prepared))
  where
    prepared = Prepared.prepareLexicon lexicon

lookupNativePhrase :: NativeMathParser -> Text -> NativePhraseResolution
lookupNativePhrase (NativeMathParser _ phraseBindings) commandText =
    case Set.toList (Map.findWithDefault Set.empty commandText phraseBindings) of
        [] -> NoNativePhrase
        [binding] -> UniqueNativePhrase binding
        firstBinding : remaining ->
            AmbiguousNativePhrase (firstBinding :| remaining)

parseNativeMath :: NativeMathParser -> Text -> Either NativeMathFailure NativeMath
parseNativeMath nativeParser source = do
    tokens <- scanNativeMathTokens source
    parseNativeMathTokens nativeParser source tokens

scanNativeMathTokens :: Text -> Either NativeMathFailure [Located Token]
scanNativeMathTokens source =
    case SourceScan.scanMathSnippet source of
        Left (SourceScan.SourceInputFailure failure) ->
            Left (NativeMathRejected
                (NativeMathTokenError (SourceScan.renderSourceFragmentError failure)))
        Left (SourceScan.SourceScannerInvariantFailure failure) ->
            Left (NativeMathScannerInvariant failure)
        Right tokens -> Right tokens

parseNativeMathTokens
    :: NativeMathParser
    -> Text
    -> [Located Token]
    -> Either NativeMathFailure NativeMath
parseNativeMathTokens (NativeMathParser prepared _) source tokens =
    case selectNativeParse (fullParses prepared tokens) of
        Left NativeMathEmptyParse -> variableListOr NativeMathEmptyParse
        Left unconsumed@NativeMathUnconsumed{} -> variableListOr unconsumed
        Left failure -> Left (NativeMathRejected failure)
        Right value -> Right value
  where
    variableListOr failure =
        case SourceScan.parsePresentationVariableFragment source of
            Left invariant -> Left (NativeMathScannerInvariant invariant)
            Right (Just variables) -> Right (NativeVariableList variables)
            Right Nothing -> Left (NativeMathRejected failure)

selectNativeParse
    :: ([NativeMath], Report Text [Located Token])
    -> Either NativeMathParseError NativeMath
selectNativeParse = \case
    (_, Report _ expectations (located : remaining)) ->
        Left
            (NativeMathUnconsumed
                expectations
                (unLocated located :| (unLocated <$> remaining)))
    (parsed, _) ->
        case nubOrd
                [ value
                | value@NativeTypedExpression{} <- parsed
                ] of
            [value] ->
                Right value
            _first : _second : rest ->
                Left (NativeMathAmbiguous (2 + length rest))
            [] ->
                case nubOrd
                        [ value
                        | value@NativeConcreteType{} <- parsed
                        ] of
                    [value] ->
                        Right value
                    _first : _second : rest ->
                        Left
                            (NativeMathAmbiguous
                                (2 + length rest))
                    [] ->
                        Left NativeMathEmptyParse

nativePhraseBindings :: Lexicon -> Map Text (Set NativePhraseBinding)
nativePhraseBindings Lexicon{..} =
    Map.fromListWith Set.union
        [(name, Set.singleton binding)
        | entry <- entries
        , Just binding <- [nativePhraseBinding entry]
        , name <- nativePhraseCommands binding]
  where
    entries =
        (adjectivePhraseEntry <$> (lexiconAdjLs <> lexiconAdjRs))
        <> (numberedPhraseEntry CanonicalNoun <$> lexiconNouns)
        <> (numberedPhraseEntry CanonicalStructureNoun <$> lexiconStructNouns)
        <> (numberedPhraseEntry CanonicalFunctionPhrase <$> lexiconFuns)
        <> [CanonicalVerb (verbLexicalSurfaces item) (verbLexicalMarker item) | item <- lexiconVerbs]

data ConcreteGrammar r = ConcreteGrammar
    { concreteGrammarBlock
        :: !(Prod r Text (Located Token) (Either ConcreteSyntaxError Block))
    , concreteGrammarTypedExpression
        :: !(Prod r Text (Located Token) TypedExpression)
    , concreteGrammarType
        :: !(Prod r Text (Located Token) ConcreteType)
    , concreteGrammarExpression
        :: !(Prod r Text (Located Token) Expr)
    , concreteGrammarFieldSpecification
        :: !(Prod r Text (Located Token) (Expr -> Stmt))
    }

-- | Split only the outer textual conjunctions produced by statement
-- coordination.  Symbolic conjunctions remain inside 'StmtFormula' and are
-- therefore deliberately left intact.
splitOuterTextualConjunction :: Stmt -> NonEmpty Stmt
splitOuterTextualConjunction = \case
    StmtConnected Conjunction _ left right ->
        splitOuterTextualConjunction left
            <> splitOuterTextualConjunction right
    statement -> statement :| []

introducedStatementLocations
    :: Location
    -> NonEmpty Stmt
    -> NonEmpty (Location, Stmt)
introducedStatementLocations introductionLocation
        (statement :| statements) =
    (introductionLocation, statement)
        :| [ (locate statement', statement')
           | statement' <- statements
           ]

data ProofDefinitionClause
    = ProofDefinitionUntyped Location VarSymbol Expr
    | ProofDefinitionTyped
        Location
        VarSymbol
        ConcreteType
        TypedExpression

data ParsedStructField = ParsedStructField
    !StructField
    !(Maybe Expr)

structFieldFor
    :: VarSymbol
    -> ParsedStructField
    -> Either ConcreteSyntaxError StructField
structFieldFor receiver (ParsedStructField field maybeOwner) =
    case maybeOwner of
        Nothing -> Right field
        Just owner@(ExprVar parsedReceiver)
            | parsedReceiver == receiver -> Right field
            | otherwise -> mismatch owner
        Just owner -> mismatch owner
  where
    mismatch owner =
        Left
            (OwnedStructureFieldReceiverMismatch
                (locate field)
                receiver
                owner)

-- The envelope owns declaration boundaries. These two parsers interpret only
-- its expression slices; neither can select a different field or punctuation.
parseFieldEnvelope
    :: Prepared.PreparedLexicon
    -> Location
    -> [Located Token]
    -> Either ConcreteSyntaxError ParsedStructField
parseFieldEnvelope prepared = parseField
  where
    ownerParser :: Parser Text [Located Token] Expr
    ownerParser = parser (concreteGrammarExpression <$> concreteGrammar prepared)
    specificationParser :: Parser Text [Located Token] (Expr -> Stmt)
    specificationParser = parser
        (concreteGrammarFieldSpecification <$> concreteGrammar prepared)

    parseField itemLocation tokens = do
        envelope <- Bifunctor.first InvalidFieldEnvelope
            (recognizeFieldEnvelope itemLocation tokens)
        let commandToken = fieldEnvelopeCommand envelope
            location = startPos commandToken
            fieldSymbol = StructSymbol (unLocated commandToken)
        owner <- traverse (parsePart ownerParser location "owner")
            (fieldEnvelopeOwner envelope)
        let fieldExpression = ExprStructOp location fieldSymbol owner
        specification <- case fieldEnvelopeSpecification envelope of
            [] -> Right Nothing
            body -> Just . ($ fieldExpression) <$>
                parsePart specificationParser location "specification" body
        pure (ParsedStructField
            (StructField location (fieldEnvelopeDescription envelope)
                (Marker <$> fieldEnvelopeLabel envelope) fieldSymbol specification)
            owner)

    parsePart :: Parser Text [Located Token] a -> Location -> Text
        -> [Located Token] -> Either ConcreteSyntaxError a
    parsePart compiled location part tokens =
        case fullParses compiled tokens of
            ([value], Report _ _ []) -> Right value
            ([], _) -> Left (InvalidFieldContents location ("could not parse field " <> part))
            _ -> Left (InvalidFieldContents location ("ambiguous field " <> part))

concreteGrammar :: Prepared.PreparedLexicon -> Grammar r (ConcreteGrammar r)
concreteGrammar prepared = mdo
    let patternToProd :: Pattern -> Holey (Prod r Text (Located Token) (Located Token))
        patternToProd pat = map (fmap tokenLocated) (patternToHoley pat)
        makeMixfixOp item = (patternToProd (mixfixPattern item), mixfixAssoc item, \parts args -> ExprOp (mixfixLoc parts args) item args)
        mixfixItems =
            map
                (List.filter (not . startsWithReservedExpressionToken)
                    . Map.elems)
                (toList lexiconMixfixTable)
        mixfixOps = map (map makeMixfixOp) mixfixItems
        makeConn = \case
            PrefixNegationSyntax connectiveToken ->
                ( map (fmap tokenLocated) [Just connectiveToken, Nothing]
                , NonAssoc
                , \parts -> \case
                    [formula'] ->
                        FormulaNeg (mixfixLoc parts [formula']) formula'
                    _ -> impossible
                        "prefix connective received a non-unary operand list"
                )
            InfixConnectiveSyntax connectiveToken assoc connective ->
                ( map
                    (fmap tokenLocated)
                    [Nothing, Just connectiveToken, Nothing]
                , assoc
                , \parts -> \case
                    [left, right] ->
                        Connected
                            (mixfixLoc parts [left, right])
                            connective
                            left
                            right
                    _ -> impossible
                        "infix connective received a non-binary operand list"
                )
        conns = map (map makeConn) lexiconConnectives
        visibleStructureFunctions =
            List.filter
                (not . isReservedOpaqueIntegerStructSymbol)
                lexiconStructFun
        visiblePrefixPredicates =
            List.filter
                (not . isReservedOpaqueIntegerPredicate . fst)
                lexiconPrefixPredicates
        typedConstantTokens =
            Set.fromList (fst <$> lexiconTypedConstants)
        structureNounTrie =
            nounTrieOf sg lexiconStructNouns

        startsWithReservedExpressionToken item =
            case mixfixPattern item of
                TokenCons (Command "opaqueInteger") _remaining -> True
                TokenCons (Integer _) End -> True
                TokenCons (Symbol "-") (HoleCons End) -> True
                TokenCons (Symbol "-") (TokenCons (Integer _) End) -> True
                _ -> False

        isReservedOpaqueIntegerStructSymbol (StructSymbol commandName) =
            commandName == "opaqueInteger"

        isReservedOpaqueIntegerPredicate
                (PrefixPredicate commandName _arity) =
            commandName == "opaqueInteger"

    nonnegativeIntegerWithLoc <-
        rule
            (terminal maybeNonnegativeIntegerTokenWithLoc
                <?> "nonnegative integer")
    relatorWithLoc <- rule $ asum
        [ (,) <$> tokenPos (relationSymbolToken item) <*> pure item
        | item <- lexiconRelationSymbols
        ] <?> "relator"
    letRelatorWithLoc <- rule $ asum
        [ (,) <$> tokenPos (relationSymbolToken item) <*> pure item
        | item <- lexiconRelationSymbols
        , relationSymbolToken item /= Command "in"
        , relationSymbolToken item /= Symbol "="
        ] <?> "relation in a Let header"
    relator <- rule (snd <$> relatorWithLoc)
    varSymbol  <- rule
        (terminal
            (\located -> do
                guard
                    (unLocated located
                        `Set.notMember` typedConstantTokens)
                maybeVarToken located)
            <?> "variable")
    varSymbols <- rule (commaList varSymbol)
    cmdWithLoc <- rule
        (terminal maybeCmdTokenWithLoc <?> "TEX command")
    typedConstantWithLoc <- rule
        (exactTokens (fst <$> lexiconTypedConstants)
            (Prepared.preparedConstants prepared)
            <?> "typed logical constant")

    concreteTypeAtom <- rule $ asum
        [ ConcreteSet <$ command "Set"
        , ConcreteProp <$ command "Prop"
        , paren concreteType
        ]
    concreteType <- rule $
        ConcreteArrow
            <$> concreteTypeAtom
            <* _to
            <*> concreteType
        <|> concreteTypeAtom
--
-- Formulas have three levels:
--
-- + Expressions: atoms or operators applied to atoms.
-- + Chains:      comma-lists of expressions, separated by relators.
-- + Formulas:    chains or connectives applied to chains.
--
-- For example, the formula @x, y < z \implies x, y < z + 1@ consist of the
-- connective @\implies@ applied to two chains @x, y < z@ and @x, y < z + 1@.
-- In turn, the chain @x, y < z + 1@ consist of three expressions,
-- @x@, @y@, and @z + 1@. Finally, @z + 1@ consist the operator @+@
-- applied to two atoms, the variable @z@ and the number literal @1@.
--
-- This split is due to the different behaviour of relators compared to
-- operators and connectives. Relators can chain (@x < y < z@) and allow
-- lists as arguments, as in the above example. Operators and connectives
-- instead have precedence and fixity. The only syntactic difference between
-- an operator and a connective is the relative precedence compared to relators.
--
    replaceBound  <- rule $ (,) <$> varSymbol <* _in <*> expr
    replaceBounds <- rule $ commaList replaceBound
    comprStmt <- rule $ (StmtFormula <$> formula) <|> text stmt

    let replaceFun = (\e bounds mstmt loc -> ExprReplace loc e bounds mstmt) <$> expr <* _pipe <*> replaceBounds <*> optional (_pipe *> comprStmt)
        replacePredSymbolic = (\y x xBound st loc -> ExprReplacePred loc y x xBound st) <$> varSymbol <* _pipe <*> (command "exists" *> varSymbol) <* _in <*> expr <* _dot <*> (StmtFormula <$> formula)
        replacePredText = (\y x xBound st loc -> ExprReplacePred loc y x xBound st) <$> varSymbol <* _pipe <*> (begin "text" *> _exists *> beginMath *> varSymbol <* _in) <*> expr <* endMath <* _suchThat <*> stmt <* end "text"
        replacePred = replacePredSymbolic <|> replacePredText

    let exprStructOpOf ann = foldr alg empty visibleStructureFunctions
            where
                alg s prod = prod <|> (uncurry ExprStructOp <$> structSymbolPos s <*> ann)

    exprStructOp <- rule (exprStructOpOf (optional (bracket expr)))

    let bracedArgs1 ar arg = count1 ar $ group arg
    let prefixPredicateOf f arg symb@(PrefixPredicate c ar) = f <$> pure symb <* command c <*> bracedArgs1 ar arg


    exprParen <- rule $ paren expr
    exprNaturalNumeral <- rule $
        (\(location, magnitude) ->
            ExprNaturalNumeral location (fromInteger magnitude))
            <$> nonnegativeIntegerWithLoc
    opaqueIntegerPayload <- rule $
        (negate
            <$> ( token (Symbol "-")
                  *> (snd <$> nonnegativeIntegerWithLoc)
                ))
        <|> (snd <$> nonnegativeIntegerWithLoc)
    exprOpaqueInteger <- rule $
        ExprOpaqueInteger
            <$> command "opaqueInteger"
            <*> group opaqueIntegerPayload
    exprVar <- rule $ ExprVar <$> varSymbol
    exprTypedConstant <- rule $
        (\(location, constantToken, registeredType) ->
            ExprTypedConstant location constantToken registeredType)
            <$> typedConstantWithLoc
    exprHigherApply <- rule $
        lowerHigherApplication
            <$> command "Apply"
            <*> group typedExpression
            <*> group (commaList higherApplicationArgument)
    exprLambda <- rule $
        (\location (variables, binderType) body ->
            ExprLambda location variables binderType body)
            <$> command "fun"
            <*> group
                ((,)
                    <$> varSymbols
                    <* _colon
                    <*> concreteType)
            <*> group typedExpression
    exprSelect <- rule $
        ExprSelect
            <$> command "Select"
            <*> optional (bracket concreteType)
            <*> group typedExpression
    structAggregateSchema <- rule $
        structApplicationOfTrie structureNounTrie expr
    structAggregateNamedEntry <- rule $
        (\(location, name) value ->
            StructAggregateNamed location (StructSymbol name) value)
            <$> cmdWithLoc
            <* _eq
            <*> expr
    structAggregateEntry <- rule $
        structAggregateNamedEntry
            <|> (StructAggregatePositional <$> expr)
    structAggregateEntries <- rule $
        pure [] <|> commaList_ structAggregateEntry
    exprStructAggregate <- rule $
        ExprStructAggregate
            <$> command "structure"
            <*> optional (bracket structAggregateSchema)
            <*> group structAggregateEntries
    exprStructReduct <- rule $
        ExprStructReduct
            <$> command "reduct"
            <*> bracket structAggregateSchema
            <*> group expr
    exprTuple <- rule do
        loc <- tokenPos ParenL
        es <- commaList2 expr <* token ParenR
        pure (makeTuple loc es)
    exprSep <- rule do
        loc <- tokenPos VisibleBraceL
        x <- varSymbol <* _in
        bound <- expr <* _pipe
        phi <- comprStmt <* token VisibleBraceR
        pure (ExprSep loc x bound phi)
    exprReplace <- rule do
        (\loc mk -> mk loc) <$> tokenPos VisibleBraceL <*> (replaceFun <|> replacePred) <* token VisibleBraceR
    exprFinSet <- rule do
        loc <- tokenPos VisibleBraceL
        es <- exprs <* token VisibleBraceR
        pure (ExprFiniteSet loc es)
    exprBase    <- rule $ asum
        [ exprVar
        , exprNaturalNumeral
        , exprOpaqueInteger
        , exprTypedConstant
        , exprHigherApply
        , exprLambda
        , exprSelect
        , exprStructAggregate
        , exprStructReduct
        , exprStructOp
        , exprParen
        , exprTuple
        , exprSep
        , exprReplace
        , exprFinSet
        ]
    exprApp <- rule $ (\e1 e2 -> ExprApp (locate e1) e1 e2) <$> exprBase <*> (paren expr <|> exprTuple)
    ordinaryExpr <- mixfixExpressionSeparate mixfixOps (exprBase <|> exprApp)
    -- A nested reconstruction must have an explicit delimiter (parentheses
    -- or a command argument). Field names never decide which "and" owns it.
    reconstructionEntry <- rule $
        (\(location, name) value ->
            StructAggregateNamed location (StructSymbol name) value)
            <$> cmdWithLoc <* _eq <*> ordinaryExpr
    exprStructReconstruction <- rule $ do
        schema <- structAggregateSchema
        location <- annotationTokenPos True (Word "based")
            <* annotationTokenPos True (Word "on")
        base <- ordinaryExpr
        replacements <- optional
            (annotationTokenPos True (Word "with") *>
                ((:) <$> reconstructionEntry <*>
                    many (annotationTokenPos True (Word "and") *> reconstructionEntry)))
        pure (ExprStructReconstruction location schema base
            (fromMaybe [] replacements))
    expr <- rule $ exprStructReconstruction <|> ordinaryExpr
    exprs       <- rule $ commaList expr

    relationSign   <- rule $ pure Positive <|> (Negative <$ command "not")
    relationExpr <- rule $ RelationExpr <$> command "mathrel" <*> group expr
    namedRelation <- rule $
        uncurry Relation <$> relatorWithLoc <*> many (group expr)
    letNamedRelation <- rule $
        uncurry Relation <$> letRelatorWithLoc <*> many (group expr)
    relation <- rule $ namedRelation <|> relationExpr
    chainBase <- rule $ (\es sign rel es' -> ChainBase es sign rel es') <$> exprs <*> relationSign <*> relation <*> exprs
    chainCons <- rule $ (\es sign rel ch -> ChainCons es sign rel ch) <$> exprs <*> relationSign <*> relation <*> chain
    chain          <- rule $ chainCons <|> chainBase

    formulaPredicate <- rule $ asum
        [ (\loc es -> FormulaPredicate loc symb marker es) <$> command c <*> bracedArgs1 ar expr
        | (symb@(PrefixPredicate c ar), marker) <- visiblePrefixPredicates
        ]
    formulaSetMap <- rule do
        function <- expr
        location <- _colon
        domain <- expr <* _to
        codomain <- expr
        pure (FormulaSetMap location function domain codomain)
    formulaChain <- rule $ FormulaChain <$> chain
    formulaExpression <- rule $ FormulaExpression <$> expr
    formulaBottom <- rule $ PropositionalConstant <$> command "bot" <*> pure IsBottom <?> "\"\\bot\""
    formulaTop <- rule $ PropositionalConstant <$> command "top" <*> pure IsTop <?> "\"\\top\""
    formulaExists <- rule $ FormulaQuantified <$> command "exists" <*> pure Existentially <*> varSymbols <*> maybeBounded <* _dot <*> formula
    formulaAll <- rule $ FormulaQuantified <$> command "forall" <*> pure Universally <*> varSymbols <*> maybeBounded <* _dot <*> formula
    formulaTypedExists <- rule $
        FormulaTypedQuantified
            <$> command "exists"
            <*> pure Existentially
            <*> varSymbols
            <* _colon
            <*> concreteType
            <* _dot
            <*> formula
    formulaTypedAll <- rule $
        FormulaTypedQuantified
            <$> command "forall"
            <*> pure Universally
            <*> varSymbols
            <* _colon
            <*> concreteType
            <* _dot
            <*> formula
    formulaQuantified <- rule $
        formulaTypedExists
        <|> formulaTypedAll
        <|> formulaExists
        <|> formulaAll
    formulaNonExpressionBase <- rule $ asum
        [ formulaSetMap
        , formulaChain
        , formulaPredicate
        , formulaBottom
        , formulaTop
        , paren formula
        ]
    formulaBase <- rule $
        formulaExpression <|> formulaNonExpressionBase
    (formulaConn, formulaConnected) <-
        mixfixExpressionSeparateWithOperator conns formulaBase
    formula           <- rule $ formulaQuantified <|> formulaConn
    formulaStatement <- rule $
        formulaQuantified
            <|> formulaConnected
            <|> formulaNonExpressionBase
    let typedExpressionOfFormula = \case
            FormulaExpression expression ->
                TypedExpressionExpr expression
            proposition ->
                TypedExpressionFormula proposition
    typedExpression <- rule $ typedExpressionOfFormula <$> formula

    -- Commas at the application level always separate applications.  Keep
    -- the unparenthesized formula language available for arguments, but use
    -- a comma-free chain there; a formula containing a comma chain must be
    -- parenthesized.
    applicationChainBase <- rule $
        (\expression sign relation' expression' ->
            ChainBase
                (expression :| [])
                sign
                relation'
                (expression' :| []))
            <$> expr
            <*> relationSign
            <*> relation
            <*> expr
    applicationChainCons <- rule $
        (\expression sign relation' rest ->
            ChainCons
                (expression :| [])
                sign
                relation'
                rest)
            <$> expr
            <*> relationSign
            <*> relation
            <*> applicationChain
    applicationChain <- rule $
        applicationChainCons <|> applicationChainBase
    applicationFormulaQuantified <- rule $
        (FormulaQuantified
            <$> command "exists"
            <*> pure Existentially
            <*> varSymbols
            <*> maybeBounded
            <* _dot
            <*> applicationFormula)
        <|> (FormulaQuantified
            <$> command "forall"
            <*> pure Universally
            <*> varSymbols
            <*> maybeBounded
            <* _dot
            <*> applicationFormula)
        <|> (FormulaTypedQuantified
            <$> command "exists"
            <*> pure Existentially
            <*> varSymbols
            <* _colon
            <*> concreteType
            <* _dot
            <*> applicationFormula)
        <|> (FormulaTypedQuantified
            <$> command "forall"
            <*> pure Universally
            <*> varSymbols
            <* _colon
            <*> concreteType
            <* _dot
            <*> applicationFormula)
    applicationFormulaBase <- rule $ asum
        [ formulaSetMap
        , FormulaChain <$> applicationChain
        , formulaExpression
        , formulaPredicate
        , formulaBottom
        , formulaTop
        , paren formula
        ]
    (applicationFormulaConn, _) <-
        mixfixExpressionSeparateWithOperator
            conns
            applicationFormulaBase
    applicationFormula <- rule $
        applicationFormulaQuantified <|> applicationFormulaConn
    higherApplicationArgument <- rule $
        typedExpressionOfFormula <$> applicationFormula

-- These are asymmetric formulas (only variables are allowed on one side).
-- They express judgements.
--
    assignment  <- rule $ (,) <$> varSymbol <* (_eq <|> _defeq) <*> expr
    typing      <- rule $ (,) <$> varSymbols <* (_in <|> _colon) <*> expr

    adjL     <- rule $ adjLOf lexicon term
    adjR     <- rule $ adjROf lexicon term
    adj      <- rule $ adjOf lexicon term
    adjVar   <- rule $ adjOf lexicon var

    var  <- rule $ math varSymbol
    vars <- rule $ math varSymbols

    verb     <- rule $ verbOf lexicon verbSurfaceSingular term
    verbPl   <- rule $ verbOf lexicon verbSurfaceBase term
    verbVar  <- rule $ verbOf lexicon verbSurfaceSingular var

    let nounTrieSg = nounTrieOf sg lexiconNouns
        nounTriePl = nounTrieOf pl lexiconNouns
        structNounTrieSg = nounTrieOf sg lexiconStructNouns
        structNounTriePl = nounTrieOf pl lexiconStructNouns

    noun      <- rule $ nounOfTrie nounTrieSg term (unboundedNounBinder <$> nounName)
    nounList  <- rule $ nounOfTrie nounTrieSg term nounNames -- Noun with a list of names.
    nounVar   <- rule $ fst <$> nounOfTrie nounTrieSg var (pure Nameless) -- No names in defined nouns.
    nounNameless <- rule $ nounOfTrie nounTrieSg term (pure (unboundedNounBinder Nameless))
    nounPl    <- rule $ nounOfTrie nounTriePl term nounNames
    nounPlMay <- rule $ nounOfTrie nounTriePl term (unboundedNounBinder <$> nounName)
    nounSingleBinder <- rule $ nounOfTrie nounTrieSg term
        (math (NounBinder <$> (Just <$> varSymbol) <*> maybeBounded)
            <|> pure (unboundedNounBinder Nothing))


    structNoun <- rule $ structNounOfTrie structNounTrieSg var var
    structNounNameless <- rule $
        (\(phrase, arguments, _nameless) ->
            StructApplication phrase arguments)
            <$> structNounOfTrie structNounTrieSg term (pure Nameless)
    structNounNamelessPl <- rule $
        (\(phrase, arguments, _nameless) ->
            StructApplication phrase arguments)
            <$> structNounOfTrie structNounTriePl term (pure Nameless)
    structNounPhraseNameless <- rule $
        StructNounPhrase
            <$> many adjL
            <*> structNounNameless
            <*> attrRightSg
            <*> optional suchStmt
    structNounPhraseNamelessPl <- rule $
        StructNounPhrase
            <$> many adjL
            <*> structNounNamelessPl
            <*> attrRightPl
            <*> optional suchStmt


    fun      <- rule $ funOf lexicon sg term
    funVar   <- rule $ funOf lexicon sg var

    verbPhraseVerbSg    <- rule $ VPVerb <$> verb
    verbPhraseVerbNotSg <- rule $ VPVerbNot <$> (_does *> _not *> verbPl)
    verbPhraseAdjSg     <- rule $ VPAdj . (:|[]) <$> (_is *> adj)
    verbPhraseAdjAndSg  <- rule do
        _is
        a1 <- adj
        _and
        a2 <- adj
        pure (VPAdj (a1 :| [a2]))
    verbPhraseAdjNotSg  <- rule $ VPAdjNot . (:|[]) <$> (_is *> _not *> adj)
    verbPhraseNotSg     <- rule $ verbPhraseVerbNotSg <|> verbPhraseAdjNotSg
    verbPhraseSg        <- rule $ verbPhraseVerbSg <|> verbPhraseAdjSg <|> verbPhraseAdjAndSg <|> verbPhraseNotSg

    verbPhraseVerbPl    <- rule $ VPVerb <$> verbPl
    verbPhraseVerbNotPl <- rule $ VPVerbNot <$> (_do *> _not *> verbPl)
    verbPhraseAdjPl     <- rule $ VPAdj . (:|[]) <$> (_are *> adj)
    verbPhraseAdjAndPl  <- rule do
        _are
        a1 <- adj
        _and
        a2 <- adj
        pure (VPAdj (a1 :| [a2]))
    verbPhraseAdjNotPl  <- rule $ VPAdjNot . (:|[]) <$> (_are *> _not *> adj)
    verbPhraseNotPl     <- rule $ verbPhraseVerbNotPl <|> verbPhraseAdjNotPl
    verbPhrasePl        <- rule $
        verbPhraseVerbPl
            <|> verbPhraseAdjPl
            <|> verbPhraseAdjAndPl
            <|> verbPhraseNotPl

    attrRThatSg  <- rule $ AttrRThat <$> (_that *> verbPhraseSg)
    attrRThatPl  <- rule $ AttrRThat <$> (_that *> verbPhrasePl)
    attrRThatsSg <- rule $
        ((:[]) <$> attrRThatSg)
            <|> ((\a a' -> [a,a'])
                    <$> attrRThatSg <* _and <*> attrRThatSg)
            <|> pure []
    attrRThatsPl <- rule $
        ((:[]) <$> attrRThatPl)
            <|> ((\a a' -> [a,a'])
                    <$> attrRThatPl <* _and <*> attrRThatPl)
            <|> pure []
    attrRs       <- rule $
        ((:[]) <$> adjR)
            <|> ((\a a' -> [a,a']) <$> adjR <* _and <*> adjR)
            <|> pure []
    attrRightSg  <- rule $ (<>) <$> attrRs <*> attrRThatsSg
    attrRightPl  <- rule $ (<>) <$> attrRs <*> attrRThatsPl

    nounName        <- rule $ optional (math varSymbol)
    nounNames       <- rule $
        math (NounBinder <$> commaList_ varSymbol <*> maybeBounded)
            <|> pure (unboundedNounBinder [])
    nounPhrase      <- rule $
        makeNounPhrase
            <$> many adjL <*> noun <*> attrRightSg <*> optional suchStmt
    nounPhrase'     <- rule $
        makeNounPhrase
            <$> many adjL <*> nounList <*> attrRightSg <*> optional suchStmt
    nounPhrasePl    <- rule $
        makeNounPhrase
            <$> many adjL <*> nounPl <*> attrRightPl <*> optional suchStmt
    nounPhrasePlMay <- rule $
        makeNounPhrase
            <$> many adjL <*> nounPlMay <*> attrRightPl <*> optional suchStmt
    nounPhraseMay   <- rule $
        makeNounPhrase
            <$> many adjL <*> nounSingleBinder <*> attrRightSg <*> optional suchStmt
    nounPhraseNameless <- rule $
        makeNounPhrase
            <$> many adjL
            <*> nounNameless
            <*> attrRightSg
            <*> optional suchStmt

    -- Quantification phrases for quantification and indfinite terms.
    quantAll   <- rule $ QuantPhrase Universally <$> (_forEvery *> nounPhrase' <|> _forAll *> nounPhrasePl)
    quantSome  <- rule $ QuantPhrase Existentially <$> (_some *> (nounPhrase' <|> nounPhrasePl))
    quantNone  <- rule $ QuantPhrase Nonexistentially <$> (_no *> (nounPhrase' <|> nounPhrasePl))
    quant      <- rule $ quantAll <|> quantSome <|> quantNone -- <|> quantUniq


    termExpr <- rule $ math do
        e <- expr
        pure (TermExpr e)
    termFun        <- rule $ TermFun <$> (optional _the *> fun)
    termIota       <- rule $ TermIota <$> _the <*> var <* _suchThat <*> stmt
    termAll        <- rule $ TermQuantified Universally <$> _every <*> nounPhraseMay
    termSome       <- rule $ TermQuantified Existentially <$> _some <*> nounPhraseMay
    termNo         <- rule $ TermQuantified Nonexistentially <$> _no <*> nounPhraseMay
    termQuantified <- rule $ termAll <|> termSome <|> termNo
    term           <- rule $ termExpr <|> termFun <|> termQuantified <|> termIota

-- Basic statements @stmt'@ are statements without any conjunctions or quantifiers.
--
    let singletonTerm = (:| []) <$> term
        pluralTerms = andList2 term
    stmtVerbSg    <- rule $ StmtVerbPhrase <$> singletonTerm <*> verbPhraseSg
    stmtVerbPl    <- rule $ StmtVerbPhrase <$> pluralTerms <*> verbPhrasePl
    stmtVerb      <- rule $ stmtVerbSg <|> stmtVerbPl
    stmtNounIs    <- rule do
        ts <- singletonTerm
        np <- _is *> _an *> nounPhrase
        pure (StmtNoun Positive ts np)
    stmtNounAre   <- rule do
        ts <- pluralTerms <* _are
        np <- nounPhrasePlMay
        pure (StmtNoun Positive ts np)
    stmtNounIsNot <- rule do
        ts <- singletonTerm
        np <- _is *> _not *> _an *> nounPhrase
        pure (StmtNoun Negative ts np)
    stmtNounAreNot <- rule do
        ts <- pluralTerms
        np <- _are *> _not *> nounPhrasePlMay
        pure (StmtNoun Negative ts np)
    stmtNoun      <- rule $ stmtNounIs <|> stmtNounIsNot <|> stmtNounAre <|> stmtNounAreNot
    stmtStruct    <- rule do
        t <- term
        s <- _is *> _an *> structNounPhraseNameless
        pure (StmtStruct t s)
    stmtExactStruct <- rule do
        t <- term
        s <- _is *> _an *> word "exact" *> structNounNameless
        pure (StmtExactStruct t s)
    stmtExists    <- rule $ StmtExists <$> _exists <*> (_an *> nounPhrase')
    stmtExist     <- rule $ StmtExists <$> _exist <*> nounPhrasePl
    stmtExistsNot <- rule do
        p <- _exists *> _no
        np <- nounPhrase'
        pure (StmtNeg p (StmtExists p np))
    stmtFormula <- rule $ math do
        phi <- formulaStatement
        pure (StmtFormula phi)
    -- A lone proposition-valued expression is a complete statement, but it
    -- is not an operand of controlled-English textual coordination.  This
    -- keeps `$A$ and $B$ are sets` in the established plural-noun grammar;
    -- higher-order users can coordinate proposition variables symbolically
    -- in one math segment or parenthesize the statement explicitly.
    stmtFormulaExpression <- rule $ math do
        expression <- expr
        pure (StmtFormula (FormulaExpression expression))
    stmtFormualNeg <- rule do
        loc <- _not
        phi <- math formula
        pure (StmtNeg loc (StmtFormula phi))
    stmtAtom <- rule $
        stmtVerb
            <|> stmtNoun
            <|> stmtExactStruct
            <|> stmtStruct
            <|> stmtFormula
            <|> stmtFormualNeg
            <|> symbolicExistsBare
            <|> paren stmt

    -- Textual connectives use the same precedence and associativity as
    -- symbolic connectives. A prefix form that takes a statement body is a
    -- terminal operand: its body consumes every following connective unless
    -- an explicit delimiter (such as a parenthesis or "then") ends it. The
    -- plain/scoped split at each precedence level prevents an enclosing level
    -- from resuming after such an operand.
    let connect conn lhs rhs =
            StmtConnected conn Nothing lhs rhs
        connectMany conn lhs rhs =
            foldl' (connect conn) lhs rhs
    stmtAndPlain <- rule do
        lhs <- stmtAtom
        rhs <- many (_and *> stmtAtom)
        pure (connectMany Conjunction lhs rhs)
    stmtAndScoped <- rule $
        connect Conjunction <$> stmtAndPlain <* _and <*> stmtScoped
    stmtAnd <- rule $ stmtAndScoped <|> stmtAndPlain
    stmtXorPlain <- rule $
        StmtConnected ExclusiveOr
            <$> (Just <$> _either)
            <*> stmtAnd
            <* _or
            <*> stmtAndPlain
    stmtXorScoped <- rule $
        StmtConnected ExclusiveOr
            <$> (Just <$> _either)
            <*> stmtAnd
            <* _or
            <*> stmtAndScoped
    stmtNorPlain <- rule $
        StmtConnected NegatedDisjunction
            <$> (Just <$> _neither)
            <*> stmtAnd
            <* _nor
            <*> stmtAndPlain
    stmtNorScoped <- rule $
        StmtConnected NegatedDisjunction
            <$> (Just <$> _neither)
            <*> stmtAnd
            <* _nor
            <*> stmtAndScoped
    stmtOrBasePlain <- rule $ stmtXorPlain <|> stmtNorPlain <|> stmtAndPlain
    stmtOrBaseScoped <- rule $ stmtXorScoped <|> stmtNorScoped <|> stmtAndScoped
    stmtOrPlain <- rule do
        lhs <- stmtOrBasePlain
        rhs <- many (_or *> stmtOrBasePlain)
        pure (connectMany Disjunction lhs rhs)
    stmtOrScoped <- rule $
        stmtOrBaseScoped
            <|> (connect Disjunction
                    <$> stmtOrPlain
                    <* _or
                    <*> (stmtOrBaseScoped <|> stmtScoped))
    stmtOr <- rule $ stmtOrScoped <|> stmtOrPlain
    stmtIfPlain <- rule $
        StmtConnected Implication
            <$> (Just <$> _if)
            <*> stmtIfAntecedent
            <* optional _comma
            <* _then
            <*> stmtImpPlain
    stmtIfScoped <- rule $
        StmtConnected Implication
            <$> (Just <$> _if)
            <*> stmtIfAntecedent
            <* optional _comma
            <* _then
            <*> (stmtScoped <|> stmtImpScoped)
    stmtImpPlain <- rule $ stmtIfPlain <|> stmtOrPlain
    stmtImpScoped <- rule $ stmtIfScoped <|> stmtOrScoped
    stmtIffPlain <- rule do
        lhs <- stmtImpPlain
        rhs <- optional (_iff *> stmtImpPlain)
        pure case rhs of
            Nothing -> lhs
            Just rhs' -> connect Equivalence lhs rhs'
    stmtIffScoped <- rule $
        stmtImpScoped
            <|> (connect Equivalence
                    <$> stmtImpPlain
                    <* _iff
                    <*> (stmtScoped <|> stmtImpScoped))
    stmtNeg <- rule $ StmtNeg <$> _itIsWrong <*> stmt

    stmtQuantPhrase <- rule $ StmtQuantPhrase <$> _for <*> quant <* optional _comma <* optional _have <*> stmt

    suchStmt <- rule $ _suchThat *> stmt <* optional _comma

   -- Symbolic quantifications with or without generalized bounds.
    symbolicForall <- rule do
        p <- _forAll <|> _forEvery
        xs <- beginMath *> varSymbols
        b <- maybeBounded <* endMath
        ms <- optional suchStmt
        s <- optional _have *> stmt
        pure (SymbolicForall p xs b ms s)
    symbolicExistsHead <- rule do
        loc1 <- _exists <|> _exist
        xs <- beginMath *> varSymbols
        b <- maybeBounded
        loc2 <- endMath
        pure (loc1, xs, b, loc2)
    symbolicExistsBare <- rule $
        (\(loc1, xs, b, loc2) ->
            SymbolicExists loc1 xs b (StmtFormula (PropositionalConstant loc2 IsTop)))
            <$> symbolicExistsHead
    symbolicExistsScoped <- rule $
        (\(loc1, xs, b, _loc2) -> SymbolicExists loc1 xs b)
            <$> symbolicExistsHead
            <*> (_suchThat *> stmt)
    symbolicNotExists <- rule do
        p <- _exists *> _no
        xs <- beginMath *> varSymbols
        b <- maybeBounded <* endMath
        s <- _suchThat *> stmt
        pure (makeSymbolicNotExists p xs b s)
    symbolicBound <- rule $ (\sign rel e -> Bounded (locate rel) sign rel e) <$> relationSign <*> relation <*> expr
    maybeBounded <- rule (pure Unbounded <|> symbolicBound)

    stmtScoped <- rule $
        asum
            [ stmtNeg
            , stmtExists
            , stmtExist
            , stmtExistsNot
            , stmtQuantPhrase
            , symbolicForall
            , symbolicExistsScoped
            , symbolicNotExists
            ]
    stmtIfAntecedent <- rule $ stmtScoped <|> stmtOr
    stmt :: Prod r Text (Located Token) Stmt <- rule $
        ( stmtScoped
            <|> stmtIffScoped
            <|> stmtIffPlain
            <|> stmtFormulaExpression
        ) <?> "a statement"


    asmLetInClause     <- rule $ uncurry AsmLetIn <$> math typing
    asmLetNounClause   <- rule $ AsmLetNoun <$> fmap pure var <* (_be <|> _denote) <* _an <*> nounPhrase
    asmLetNounsClause  <- rule $ AsmLetNoun <$> vars <* (_be <|> _denote) <*> nounPhrasePlMay
    asmLetEqClause     <- rule $ uncurry AsmLetEq <$> math assignment
    asmLetRelationClause <- rule $ math $
        (AsmLetRelation <$> varSymbols <*> letNamedRelation <*> expr)
        <|> (AsmLetRelation
            <$> commaList2 varSymbol
            <*> ((\location -> Relation location EqSymbol [])
                <$> tokenPos (Symbol "="))
            <*> expr)
    asmLetTheClause    <- rule $ AsmLetThe <$> var <* _be <* _the <*> fun
    asmLetStructClause <- rule $
        AsmLetStruct <$> fmap pure var <* _be <* _an <*> structNounPhraseNameless
    asmLetStructsClause <- rule $
        AsmLetStruct
            <$> math (commaList2 varSymbol)
            <* _be
            <*> structNounPhraseNamelessPl
    asmLetOrdinaryClause <- rule
        $ asmLetNounClause
        <|> asmLetNounsClause
        <|> asmLetInClause
        <|> asmLetEqClause
        <|> asmLetTheClause
        <|> asmLetStructClause
        <|> asmLetStructsClause
    asmLetGroup <- rule $
        _let *>
            ((pure <$> asmLetRelationClause)
                <|> (NonEmpty.toList <$> andList1 asmLetOrdinaryClause))
    asmSupposeGroup <- rule $ do
        statements <- splitOuterTextualConjunction <$> (_suppose *> stmt)
        pure (AsmSuppose <$> NonEmpty.toList statements)
    asm             <- rule $ (asmLetGroup <|> asmSupposeGroup) <* _dot
    asms            <- rule $ concat <$> many asm

    axiom <- rule $ Axiom <$> asms <* optional _then <*> stmt <* _dot

    claim <- rule $ (,) <$> asms <* optional _then <*> stmt <* _dot

    defnAdj <- rule $ DefnAdj <$> var <* _is <*> adjVar
    defnVerb <- rule $ DefnVerb <$> var <*> verbVar
    defnNoun <- rule $ DefnNoun <$> var <* _is <* _an <*> nounVar
    defnRel <- rule $ DefnRel <$> (beginMath *> varSymbol) <*> relator <*> many (group varSymbol) <*> varSymbol <* endMath
    defnSymbolicPredicate <- rule $ math $ asum $ do
        (predi, marker) <- visiblePrefixPredicates
        pure (prefixPredicateOf (\predi' args -> DefnSymbolicPredicate predi' marker args) varSymbol predi)
    defnHead <- rule $ optional _write *> asum [defnAdj, defnVerb, defnNoun, defnRel, defnSymbolicPredicate]

    defnIf <- rule $ Defn <$> asms <*> defnHead <* (_iff <|> _if) <*> stmt <* _dot
    defnFunSymb <- rule $ _comma *> termExpr <* _comma --  Optional symbolic equivalent.
    definitionResultPhrase <- rule $
        _comma *> word "which" *> _is *> _an *> nounPhraseNameless
    defnFun <- rule $
        DefnFun
            <$> asms
            <*> (optional _the *> funVar)
            <*> optional defnFunSymb
            <* _is
            <*> term
            <*> optional definitionResultPhrase
            <* _dot

    symbolicPatternEqExpression <- rule do
        pat <- beginMath *> symbolicPattern <* _eq
        e <- expr <* endMath
        pure (pat, e)
    symbolicPatternEqTerm <- rule $
        symbolicPatternEqExpression <* _dot
    defnOp <- rule $
        (\asms' (pat, expr') result -> DefnOp asms' pat expr' result)
            <$> asms
            <*> symbolicPatternEqExpression
            <*> optional definitionResultPhrase
            <* _dot

    defnTyped <- rule $
        (\(location, constantToken, _registeredType) coreType body ->
            DefnTypedConstant location constantToken coreType body)
            <$> (beginMath *> typedConstantWithLoc)
            <* _colon
            <*> concreteType
            <* _eq
            <*> typedExpression
            <* endMath
            <* _dot

    defn <- rule $ defnTyped <|> defnIf <|> defnFun <|> defnOp

    abbreviationVerb  <- rule $ AbbreviationVerb <$> var <*> verbVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationAdj   <- rule $ AbbreviationAdj <$> var <* _is <*> adjVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationNoun  <- rule $ AbbreviationNoun <$>  var <* _is <* _an <*> nounVar <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationRel   <- rule $ AbbreviationRel <$> (beginMath *> varSymbol) <*> relator <*> many (group varSymbol) <*> varSymbol <* endMath <* (_iff <|> _if) <*> stmt <* _dot
    abbreviationFun   <- rule $ AbbreviationFun <$> (_the *> funVar) <* (_is <|> _denotes) <*> term <* _dot
    abbreviationEq    <- rule $ uncurry AbbreviationEq <$> symbolicPatternEqTerm
    abbreviation      <- rule $ (abbreviationVerb <|> abbreviationAdj <|> abbreviationNoun <|> abbreviationRel <|> abbreviationFun <|> abbreviationEq)

    datatypePremise <- rule $ math $ (,) <$> varSymbol <* _in <*> expr
    datatypeItem <- rule $ terminal \located -> case unLocated located of
        Command "item" -> Just Nothing
        NamedItem name -> Just (Just name)
        _ -> Nothing
    datatypeClause <- rule $
        (\name (constructorExpr, targetExpr) premises -> DatatypeClause
            { datatypeClauseName = name
            , datatypeClauseConstructorExpr = constructorExpr
            , datatypeClauseTargetExpr = targetExpr
            , datatypeClausePremises = fromMaybe [] premises
            }) <$> datatypeItem <*> math ((,) <$> expr <* _in <*> expr)
               <*> optional (_for *> andList1_ datatypePremise)
               <* _dot
    datatypeHead <- rule $ _define *> math expr <* optional _inductively <* optional _asFollows <* _dot
    datatype     <- rule $ Datatype <$> datatypeHead <*> (begin "enumerate" *> many1 datatypeClause <* end "enumerate")

    recursiveClause <- rule $ RecursiveClause <$> datatypeItem <*>
        ((Left <$> math ((,) <$> expr <* _eq <*> expr))
            <|> (Right <$> ((,) <$> math formula <* _iff <*> stmt))) <* _dot
    recursiveDefinition <- rule $ RecursiveDefinition <$> asms
        <* _define <*> ((Left <$> math symbolicPattern) <|> (Right <$> defnSymbolicPredicate))
        <* word "recursively" <* _for
        <*> (beginMath *> varSymbol <* _in) <*> (expr <* endMath)
        <* _asFollows <* _dot
        <*> (begin "enumerate" *> many1 recursiveClause <* end "enumerate")

    unconditionalIntro <- rule $ IntroRule [] <$> math formula
    conditionalIntro   <- rule $ IntroRule <$> (_if *> andList1_ (math formula)) <* _comma <* _then <*> math formula
    inductiveIntro     <- rule $ (unconditionalIntro <|> conditionalIntro) <* _dot
    inductiveDomain    <- rule $ math $ (,) <$> symbolicPattern <* _subseteq <*> expr
    inductiveHead      <- rule $ _define *> inductiveDomain <* optional _inductively <* optional _asFollows <* _dot
    inductive          <- rule $ uncurry Inductive <$> inductiveHead <*> enumerated1 inductiveIntro

    signatureAdj      <- rule $ SignatureAdj <$> var <* _can <* _be <*> adjOf lexicon var
    symbolicPattern   <- symbolicPatternOf mixfixItems varSymbol
    signatureSymbolic <- rule $ SignatureSymbolic <$> math symbolicPattern <* _is <* _an <*> nounPhrase
    signatureTyped <- rule $
        (\(location, constantToken, _registeredType) coreType ->
            SignatureTypedConstant location constantToken coreType)
            <$> (beginMath *> typedConstantWithLoc)
            <* _colon
            <*> concreteType
            <* endMath
    signatureHead <- rule $
        signatureTyped
        <|> asum
        [ case form of
            AdjectiveSignatureHead -> signatureAdj
            SymbolicSignatureHead -> signatureSymbolic
        | form <- concreteSignatureHeadForms
        ]
    signature <- rule $
        (,) <$> asms <* optional _then <*> signatureHead <* _dot

    fieldSpecification <- rule $
        (\location domain codomain fieldExpression ->
            StmtFormula (FormulaSetMap location fieldExpression domain codomain))
            <$> _colon <*> expr <* _to <*> expr
        <|> (\sign fieldRelation right fieldExpression ->
            StmtFormula (FormulaChain
                (ChainBase (fieldExpression :| []) sign fieldRelation right)))
            <$> relationSign <*> relation <*> exprs
    structField <- rule $
        parseFieldEnvelope prepared
            <$> command "item" <*> many (satisfy fieldItemToken)
    structFieldList <- rule $
        begin "enumerate" *> many1_ structField <* end "enumerate"
    let makeStructDefn
                structPreamble
                (structPhrase, structParameters, structLabel)
                structParents
                maybeFields
                structAssumes = do
            structFields <-
                traverse (>>= structFieldFor structLabel)
                    (fromMaybe [] maybeFields)
            pure StructDefn{..}
    structDefn <- rule $
        makeStructDefn
            <$> asms
            <* _an
            <*> structNoun
            <* _extends
            <*> andList1_ (StructParent <$> (_an *> structNounNameless) <*> optional label)
            <*> optional (_equipped *> structFieldList)
            <*> ((_suchThat *> enumeratedMarked (stmt <* _dot))
                <|> ([] <$ _dot))

    constructionDefn <- rule $ do
        assumptions <- asms
        ~(phrase, arguments, (head', value)) <-
            _the *> structNounOfTrie structNounTrieSg term
                symbolicPatternEqExpression
        _dot
        pure (Construction assumptions (StructApplication phrase arguments) head' value)

    instanceName <- rule $ do
        ~(location, constantToken, _registeredType) <-
            beginMath *> typedConstantWithLoc <* endMath
        pure (location, constantToken)
    instanceEquation <- rule $ do
        ~(structurePhrase, structureArguments,
            (nameLocation, nameToken, value)) <-
                _the *>
                    structNounOfTrie
                        structNounTrieSg
                        term
                        (do
                            ~(location, constantToken, _registeredType) <-
                                beginMath *> typedConstantWithLoc
                            value <- _eq *> expr <* endMath
                            pure (location, constantToken, value))
        _dot
        pure Instance
            { instanceApplication =
                StructApplication structurePhrase structureArguments
            , instanceNameLocation = nameLocation
            , instanceNameToken = nameToken
            , instanceValue = value
            }
    instanceNatural <- rule $ do
        ~(structurePhrase, structureArguments,
            (nameLocation, nameToken)) <-
                _the *>
                    structNounOfTrie
                        structNounTrieSg
                        term
                        instanceName
        value <- _is *> math expr <* _dot
        pure Instance
            { instanceApplication =
                StructApplication structurePhrase structureArguments
            , instanceNameLocation = nameLocation
            , instanceNameToken = nameToken
            , instanceValue = value
            }
    instanceDefn <- rule (instanceEquation <|> instanceNatural)

    justificationSet <- rule $ JustificationSetExt <$ _bySetExt
    justificationStructure <- rule $
        JustificationStructureExt <$ _byStructureExt
    justificationExtensionality <- rule $
        JustificationExtensionality <$ _byExt
    justificationAuto <- rule $
        _by *> ( JustificationAuto . Just <$> commandReference "auto"
            <|> JustificationAuto Nothing <$ _auto
        )
    justificationObvious <- rule $
        _by *> (JustificationObviousReferences <$> commandReference "obv")
    justificationAssumption <- rule $
        JustificationAssumption <$ (_by *> _assumption)
    justificationDefinition <- rule $
        JustificationDefinition <$ (_by *> _definition)
    justificationNotion <- rule $
        JustificationNotion <$ (_by *> word "notion")
    justification <- rule
        ( justificationSet
            <|> justificationStructure
            <|> justificationExtensionality
            <|> justificationAuto
            <|> justificationObvious
            <|> justificationAssumption
            <|> justificationDefinition
            <|> justificationNotion
            <|> pure JustificationImplicit
        )

    omitted          <- rule $ Omitted <$> _omitted <* _dot
    qedJustified     <- rule $ Qed . Just <$> _follows <*> (justification <* _dot)
    qed              <- rule $ qedJustified <|> omitted <|> pure (Qed Nothing JustificationImplicit)
    contradiction    <- rule $ Contradiction <$> _contradiction <*> justification <* _dot

    let alignedEq = symbol "&=" <?> "\"&=\""
    explanation <- rule $ (text justification) <|> pure JustificationImplicit
    relationCalculationItem <- rule $
        ( (\location destination stepJustification ->
                CalcRelationLink
                    Positive
                    (Relation location EqSymbol [])
                    destination
                    stepJustification)
            <$> alignedEq
            <*> expr
            <*> explanation
        )
        <|>
        ( CalcRelationLink
            <$> (symbol "&" *> relationSign)
            <*> relation
            <*> expr
            <*> explanation
        )
    relationCalculations <-
        rule $ RelationCalculation <$> expr <*> many1 relationCalculationItem

    let alignedIff = symbol "&" *> command "iff" <?> "\"&\\iff\""
    biconditionalItem <- rule $ (,) <$> (alignedIff *> formula) <*> explanation
    biconditionals <- rule $ Biconditionals <$> formula <*> (many1 biconditionalItem) <* optional _dot


    calcQuantifier <- rule do
        loc <- _forAll <|> _forEvery
        xs <- beginMath *> varSymbols
        mb <- maybeBounded <* endMath
        st <- optional suchStmt
        optional _have
        pure (loc, CalcQuantifier xs mb st)

    calc <- rule do
        mquant <- optional calcQuantifier
        psteps <- align (relationCalculations <|> biconditionals)
        pf <- proof
        pure let (loc2, steps) = psteps in case mquant of
            Nothing -> Calc loc2 Nothing steps pf
            Just (loc, q) -> Calc loc (Just q) steps pf

    caseOf           <- rule $ command "caseOf" *> token InvisibleBraceL *> stmt <* _dot <* token InvisibleBraceR
    byCases          <- rule $ uncurry ByCase <$> envPos_ "byCase" (many1_ (Case <$> caseOf <*> proof))
    byContradiction  <- rule $ ByContradiction <$> _suppose <* _not <* _dot <*> proof
    bySetInduction   <- rule $ uncurry BySetInduction <$> proofBy (_in *> word "-induction" *> optional (word "on" *> term)) <*> proof
    byOrdInduction   <- rule $ ByOrdInduction . fst <$> proofBy (word "transfinite" *> word "induction") <*> proof
    namedCaseHeading <- rule $ terminal \located -> case unLocated located of
        CaseHeading name -> Just (startPos located, name)
        _ -> Nothing
    caseNamePart <- rule $ terminal \located -> case unLocated located of
        Word{} -> Just ()
        Integer{} -> Just ()
        Symbol "_" -> Just ()
        _ -> Nothing
    namedCase <- rule $ (\(location, name) child -> NamedCase location name child)
        <$> (namedCaseHeading <* token InvisibleBraceL <* many1 caseNamePart <* _dot <* token InvisibleBraceR)
        <*> proof
    byStructuralInduction <- rule $ (\(location, focus) cases -> ByStructuralInduction location focus cases)
        <$> proofBy (word "structural" *> word "induction" *> word "on" *> math varSymbol)
        <*> (begin "byCase" *> many1 namedCase <* end "byCase")
    assumeIntro      <- rule do
        parsed <- asum
            [ (,) <$> word "assume" <*> pure AssumeIntroAssume
            , (,) <$> word "suppose" <*> pure AssumeIntroSuppose
            ]
        optional (word "that")
        pure parsed
    assume           <- rule $
        (\(location, intro) statement continuation ->
            foldr
                (\(statementLocation, statement') continuation' ->
                    Assume
                        statementLocation
                        intro
                        statement'
                        continuation')
                continuation
                (introducedStatementLocations
                    location
                    (splitOuterTextualConjunction statement)))
            <$> assumeIntro
            <*> (stmt <* _dot)
            <*> proof

    fixBinderTyped   <- rule $ FixBinderTyped <$> (beginMath *> varSymbols) <* _colon <*> concreteType <* endMath
    fixBinderSymbolic <- rule $ FixBinderSymbolic <$> (beginMath *> varSymbols) <*> maybeBounded <* endMath
    fixBinder         <- rule $ fixBinderTyped <|> fixBinderSymbolic
    fix              <- rule do
        location <- _fix
        binders <- andList1 fixBinder
        condition <- optional (_suchThat *> stmt)
        _dot
        continuation <- proof
        pure (Fix location binders condition continuation)

    takeTyped        <- rule $ TakeTyped <$> _take <*> (beginMath *> varSymbols) <* _colon <*> concreteType <* endMath <* _suchThat <*> stmt <*> justification <* _dot <*> proof
    takeVar          <- rule $ TakeVar <$> _take <*> (beginMath *> varSymbols) <*> maybeBounded <* endMath <* _suchThat <*> stmt <*> justification <* _dot <*> proof
    takeNoun         <- rule $ TakeNoun <$> _take <*> (_an *> (nounPhrase' <|> nounPhrasePl)) <*> justification <* _dot <*> proof
    take             <- rule $ takeTyped <|> takeVar <|> takeNoun
    suffices         <- rule $ Suffices <$> _sufficesThat <*> stmt <*> (justification <* _dot) <*> proof
    subclaim         <- rule $ Subclaim <$> _show <*> (stmt <* _dot) <*> env_ "subproof" proof <*> proof
    have             <- rule do
        mIntro <- optional haveIntro
        s <- stmt
        j <- justification <* _dot
        pf <- proof
        pure $ case mIntro of
            Nothing -> Have (locate s) HaveNoIntro s j pf
            Just (introLocation, parsedIntro) ->
                Have introLocation parsedIntro s j pf
    since            <- rule do
        premiseLocation <- _since
        premise <- stmt
        premiseJustification <- justification
        claimLocation <- _comma *> _have
        sinceClaim <- stmt
        claimJustification <- justification <* _dot
        continuation <- proof
        pure
            (Since
                premiseLocation premise premiseJustification
                claimLocation sinceClaim claimJustification
                continuation)


    defineTypedClause <- rule do
        variable <- beginMath *> varSymbol <* _colon
        variableType <- concreteType <* _eq
        expression <- typedExpression <* endMath
        pure
            (ProofDefinitionTyped
                (locate variable)
                variable
                variableType
                expression)
    defineClause <- rule
        ( defineTypedClause
        <|> do
            variable <- beginMath *> varSymbol <* _eq
            expression <- expr <* endMath
            pure
                (ProofDefinitionUntyped
                    (locate variable)
                    variable
                    expression)
        )
    defineGroup <- rule do
        _let
        clauses <- andList1 defineClause
        _dot
        continuation <- proof
        pure
            (foldr
                (\clause continuation' ->
                    case clause of
                        ProofDefinitionTyped
                                clauseLocation variable variableType expression ->
                            DefineTyped
                                clauseLocation
                                variable
                                variableType
                                expression
                                continuation'
                        ProofDefinitionUntyped clauseLocation variable expression ->
                            Define clauseLocation variable expression continuation')
                continuation
                (NonEmpty.toList clauses))
    defineFunction   <- rule $ DefineFunction <$> _let <*> (beginMath *> varSymbol) <*> paren varSymbol <* _eq <*>  expr <* endMath <* _for <* beginMath <*> varSymbol <* _in <*> expr <* endMath <* _dot <*> proof

    proof            <- rule $ asum [byContradiction, byCases, bySetInduction, byOrdInduction, byStructuralInduction, calc, subclaim, assume, fix, take, since, have, suffices, defineGroup, defineFunction, contradiction, qed]


    blockAxiom  <- rule $ Right . (\(p, title, m, a) -> BlockAxiom p title m a) <$> envPos  "axiom" axiom
    blockClaim  <- rule $ Right <$> claimEnv claim
    blockProof  <- rule $ Right . uncurry3 BlockProof <$> envStartEndLocation "proof" proof
    blockDefn   <- rule $ Right . (\(p, title, m, d) -> BlockDefn p title m d) <$> envPos "definition" defn
    blockAbbr   <- rule $ Right . (\(p, title, m, a) -> BlockAbbr p title m a) <$> envPos "abbreviation" abbreviation
    blockData   <- rule $ Right . (\(p, title, m, d) -> BlockData p title m d) <$> envPos "datatype" datatype
    blockRecursive <- rule $ Right . (\(p, title, m, d) -> BlockRecursive p title m d) <$> envPos "recursive-definition" recursiveDefinition
    blockInd    <- rule $ Right . (\(p, title, m, i) -> BlockInductive p title m i) <$> envPos "inductive" inductive
    blockSig    <- rule $ Right . (\(p, title, m, (a, s)) -> BlockSig p title m a s) <$> envPos "signature" signature
    blockStruct <- rule $
        (\(p, title, m, result) ->
            BlockStruct p title m <$> result)
            <$> envPos "struct" structDefn
    blockInstance <- rule $ Right . (\(p, title, m, i) -> BlockInstance p title m i) <$> envPos "instance" instanceDefn
    blockConstruction <- rule $ Right . (\(p, title, m, c) -> BlockConstruction p title m c) <$> envPos "construction" constructionDefn
    block       <- rule $ asum [blockAxiom, blockClaim, blockDefn, blockAbbr, blockData, blockRecursive, blockInd, blockSig, blockStruct, blockInstance, blockConstruction, blockProof]

    pure
        ConcreteGrammar
            { concreteGrammarBlock = block
            , concreteGrammarTypedExpression = typedExpression
            , concreteGrammarType = concreteType
            , concreteGrammarExpression = expr
            , concreteGrammarFieldSpecification = fieldSpecification
            }
  where
    lexicon@Lexicon{..} = Prepared.preparedInventory prepared

haveIntro :: Prod r Text (Located Token) (Location, HaveIntro)
haveIntro =
    introWord "thus" HaveThus
        <|> introWord "hence" HaveHence
        <|> introWord "then" HaveThen
        <|> introWord "next" HaveNext
        <|> introWord "now" HaveNow
        <|> introWord "first" HaveFirst
        <|> introWord "finally" HaveFinally
        <|> introWord "subsequently" HaveSubsequently
        <|> introWord "ultimately" HaveUltimately
        <|> introWord "therefore" HaveTherefore
        <|> particularlyIntro
        <|> inParticularIntro
        <|> ((\location -> (location, HaveWeHave)) <$> _have)
  where
    introWord spelling intro =
        ((\location -> (location, intro)) <$> word spelling)
            <?> ("\"" <> spelling <> "\"")

    particularlyIntro =
        ((\location -> (location, HaveParticularly))
            <$> (word "particularly" <* _comma))
            <?> "\"particularly\""

    inParticularIntro =
        ((\location -> (location, HaveInParticular))
            <$> (word "in" *> word "particular" <* _comma))
            <?> "\"in particular\""


proofBy :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (Location, a)
proofBy method = bracket do
    pos <- word "proof" *> word "by"
    a <- method
    pure (pos, a)

claimEnv :: Prod r Text (Located Token) (([Asm], Stmt)) -> Prod r Text (Located Token) Block
claimEnv content = asum
    [ make Theorem <$> envPos "theorem" content
    , make Lemma <$> envPos "lemma" content
    , make Corollary <$> envPos "corollary" content
    , make Composition <$> envPos "composition" content
    , make PlainClaim <$> envPos "claim" content
    , make Proposition <$> envPos "proposition" content
    , make Classification <$> envPos "classification" content
    ]
    where
        make kind =
            (\(loc, title, marker, (asms, stmt)) ->
                BlockClaim kind loc title marker
                    (Claim asms stmt))

-- | Nonempty textual lists of the form "a, b, c, and d".
-- The final comma is mandatory, 'and' is not.
-- Also allows "a and b". Should therefore be avoided in contexts where
-- a logical conjunction would also be possible.
-- Currently also allows additional 'and's after each comma...
--
andList1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
andList1 item = ((:|) <$> item <*> many (_commaAnd *> item))
    <|> ((\i j -> i:|[j]) <$> item <* _and <*> item)

-- | A textual conjunction containing at least two items.
andList2 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
andList2 item =
        ((\i j js -> i :| (j : js))
            <$> item
            <*> (_commaAnd *> item)
            <*> many (_commaAnd *> item))
    <|> ((\i j -> i :| [j]) <$> item <* _and <*> item)

-- | Like 'andList1', but drops the information about nonemptiness.
andList1_ :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [a]
andList1_ item = NonEmpty.toList <$> andList1 item


commaList :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
commaList item = (:|) <$> item <*> many (_comma *> item)

-- | Like 'commaList', but drops the information about nonemptiness.
commaList_ :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [a]
commaList_ item = NonEmpty.toList <$> commaList item

-- | Like 'commaList', but requires at least two items (and hence at least one comma).
commaList2 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
commaList2 item = (:|) <$> item <* _comma <*> commaList_ item


lowerHigherApplication
    :: Location
    -> TypedExpression
    -> NonEmpty TypedExpression
    -> Expr
lowerHigherApplication location function arguments =
    let firstArgument = NonEmpty.head arguments
        remainingArguments = NonEmpty.tail arguments
    in List.foldl'
        (\current argument ->
            ExprHigherApply
                location
                (TypedExpressionExpr current)
                argument)
        (ExprHigherApply location function firstArgument)
        remainingArguments


enumerated1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty a)
enumerated1 p = begin "enumerate" *> many1 (command "item" *> p) <* end "enumerate" <?> "\"\\begin{enumerate} ...\""


enumeratedMarked :: Prod r Text (Located Token) a -> Prod r Text (Located Token) [(Marker, a)]
enumeratedMarked p = NonEmpty.toList <$> enumeratedMarked1 p

enumeratedMarked1 :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (NonEmpty (Marker, a))
enumeratedMarked1 p = begin "enumerate" *> many1 ((,) <$> (command "item" *> label) <*> p) <* end "enumerate" <?> "\"\\begin{enumerate}\\item\\label{...}...\""



-- This function could be rewritten, so that it can be used directly in the grammar,
-- instead of with specialized variants.
--
phraseOf
    :: forall pat a b r. Locatable a
    => (Location -> pat -> [a] -> b)
    -> Lexicon
    -> (Lexicon -> [pat])
    -> (pat -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) b
phraseOf constr lexicon selector proj arg =
    uncurry3 constr <$> buildPhraseTrie arg trie
    where
        pats :: [pat]
        pats = selector lexicon

        trie :: Trie PhraseStep pat
        trie = trieFromList
            [ (phraseSteps (proj pat), pat)
            | pat <- pats
            ]

adjLOf :: Locatable arg => Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjLOf arg)
adjLOf lexicon arg = phraseOf AdjL lexicon lexiconAdjLs adjectiveLexicalPhrase arg <?> "a left adjective"

adjROf :: Locatable arg =>Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjROf arg)
adjROf lexicon arg = phraseOf AdjR lexicon lexiconAdjRs adjectiveLexicalPhrase arg <?> "a right adjective"

adjOf :: Locatable arg =>Lexicon -> Prod r Text (Located Token) arg -> Prod r Text (Located Token) (AdjOf arg)
adjOf lexicon arg = phraseOf Adj lexicon lexiconAdjs adjectiveLexicalPhrase arg <?> "an adjective"

verbOf
    :: Locatable a => Lexicon
    -> (VerbSurfaces -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) (VerbOf a)
verbOf lexicon proj arg =
    phraseOf Verb lexicon lexiconVerbs (proj . verbLexicalSurfaces) arg

funOf
    :: Locatable a => Lexicon
    -> (SgPl LexicalPhrase -> LexicalPhrase)
    -> Prod r Text (Located Token) a
    -> Prod r Text (Located Token) (FunOf a)
funOf lexicon proj arg = phraseOf Fun lexicon lexiconFuns (proj . lexicalItemSgPlPhrase) arg <?> "functional phrase"


nounOfTrie
    :: Locatable arg => Trie NounStep LexicalItemSgPl
    -> Prod r Text (Located Token) arg
    -> Prod r Text (Located Token) names
    -> Prod r Text (Located Token) (NounOf arg, names)
nounOfTrie trie arg vars =
    (\(loc, pat, args, xs) -> (Noun loc pat args, xs))
        <$> buildNounTrie arg vars trie
        <?> "a noun"

nounTrieOf
    :: (SgPl LexicalPhrase -> LexicalPhrase)
    -> [LexicalItemSgPl]
    -> Trie NounStep LexicalItemSgPl
nounTrieOf proj pats = trieFromList
    [ (nounStepsWithSlot (proj (lexicalItemSgPlPhrase pat)), pat)
    | pat <- pats
    ]

structNounOfTrie
    :: Locatable arg => Trie NounStep LexicalItemSgPl
    -> Prod r Text (Located Token) arg
    -> Prod r Text (Located Token) name
    -> Prod r Text (Located Token) (StructPhrase, [arg], name)
structNounOfTrie trie arg name =
    (\(_loc, pat, args, xs) -> (pat, args, xs))
        <$> buildNounTrie arg name trie
        <?> "a structure noun"

-- | Parse a structure application without the subject slot used by ordinary
-- controlled-English structure nouns.  For example, the declaration phrase
-- @left module M over R@ has the annotation surface @left module over R@
-- inside @\\structure[...]@.
structApplicationOfTrie
    :: Locatable arg => Trie NounStep LexicalItemSgPl
    -> Prod r Text (Located Token) arg
    -> Prod r Text (Located Token) (StructApplication arg)
structApplicationOfTrie trie arg =
    (\(_loc, phrase, arguments) ->
        StructApplication phrase arguments)
        <$> buildStructApplicationTrie arg trie
        <?> "a structure annotation"

-- Naming traverses the original inventory order even though singleton token
-- recognition is indexed. Earley floats these names around alternatives; a
-- category-only lookup would change both raw reports and the CLI's first eight
-- expectations. Repeated keys remain explicit, ordered semantic alternatives.
exactTokens
    :: [Token]
    -> Prepared.TokenIndex a
    -> Prod r Text (Located Token) (Location, Token, a)
exactTokens expectations index =
    foldr (\tok production -> production <?> tokToText tok) alternatives expectations
  where
    alternatives
        | Map.null (Prepared.singletonTokens index) = repeated
        | otherwise = terminal singleton <|> repeated
    repeated = asum
        [ terminal (\located -> do
            guard (unLocated located == tok)
            pure (startPos located, unLocated located, value))
        | (tok, value) <- Prepared.repeatedTokens index
        ]
    singleton located = do
        let tok = unLocated located
        value <- Map.lookup tok (Prepared.singletonTokens index)
        pure (startPos located, tok, value)

-- Trie helpers for lexically-defined phrases.

data PhraseStep
    = PhraseTok Token
    | PhraseHole
    deriving (Eq, Ord)

data NounStep
    = NounTok Token
    | NounHole
    | NounVar
    deriving (Eq, Ord)

data Trie k v = Trie
    { trieValues :: [v]
    , trieEdges  :: [(k, Trie k v)]
    }

emptyTrie :: Trie k v
emptyTrie = Trie [] []

insertTrie :: Eq k => [k] -> v -> Trie k v -> Trie k v
insertTrie [] v Trie{trieValues = vs, trieEdges = es} =
    Trie (vs <> [v]) es
insertTrie (k:ks) v Trie{trieValues = vs, trieEdges = es} =
    Trie vs (go es)
    where
        go = \case
            [] -> [(k, insertTrie ks v emptyTrie)]
            (k', child) : rest
                | k == k'   -> (k', insertTrie ks v child) : rest
                | otherwise -> (k', child) : go rest

trieFromList :: Eq k => [([k], v)] -> Trie k v
trieFromList = foldl' (\tr (k, v) -> insertTrie k v tr) emptyTrie

phraseSteps :: LexicalPhrase -> [PhraseStep]
phraseSteps = map \case
    Just tok -> PhraseTok tok
    Nothing  -> PhraseHole

nounSteps :: LexicalPhrase -> [NounStep]
nounSteps = map \case
    Just tok -> NounTok tok
    Nothing  -> NounHole

nounStepsWithSlot :: LexicalPhrase -> [NounStep]
nounStepsWithSlot pat =
    let (pat1, pat2) = splitOnVariableSlot pat
    in nounSteps pat1 <> [NounVar] <> nounSteps pat2

data PhraseAcc a = PhraseAcc
    { phraseLoc  :: Maybe Location
    , phraseArgs :: [a] -> [a]
    }

emptyPhraseAcc :: PhraseAcc a
emptyPhraseAcc = PhraseAcc Nothing id

setPhraseLoc :: Location -> PhraseAcc a -> PhraseAcc a
setPhraseLoc Nowhere acc = acc
setPhraseLoc _loc acc@PhraseAcc{phraseLoc = Just _} = acc
setPhraseLoc loc PhraseAcc{phraseLoc = Nothing, phraseArgs = args} =
    PhraseAcc (Just loc) args

addPhraseArg :: Locatable a => a -> PhraseAcc a -> PhraseAcc a
addPhraseArg a acc@PhraseAcc{phraseLoc = loc, phraseArgs = args}
    | locate a == Nowhere = acc{phraseArgs = args . (a :)}
    | otherwise = PhraseAcc (loc <|> Just (locate a)) (args . (a :))

finalizePhraseAcc :: PhraseAcc a -> (Location, [a])
finalizePhraseAcc PhraseAcc{phraseLoc = Just loc, phraseArgs = args} =
    (loc, args [])
finalizePhraseAcc PhraseAcc{phraseLoc = Nothing} =
    impossible "phraseOf: empty phrase"

data NounAcc a name = NounAcc
    { nounLoc :: Maybe Location
    , nounArgs :: [a] -> [a]
    , nounName :: Maybe name
    }

emptyNounAcc :: NounAcc a name
emptyNounAcc = NounAcc Nothing id Nothing

setNounLoc :: Location -> NounAcc a name -> NounAcc a name
setNounLoc Nowhere acc = acc
setNounLoc _loc acc@NounAcc{nounLoc = Just _} = acc
setNounLoc loc NounAcc{nounLoc = Nothing, nounArgs = args, nounName = name} =
    NounAcc (Just loc) args name

addNounArg :: Locatable a => a -> NounAcc a name -> NounAcc a name
addNounArg a acc@NounAcc{nounLoc = loc, nounArgs = args, nounName = name}
    | locate a == Nowhere = acc{nounArgs = args . (a :)}
    | otherwise = NounAcc (loc <|> Just (locate a)) (args . (a :)) name

setNounName :: name -> NounAcc a name -> NounAcc a name
setNounName name NounAcc{nounLoc = loc, nounArgs = args, nounName = Nothing} =
    NounAcc loc args (Just name)
setNounName _ acc@NounAcc{nounName = Just _} = acc

finalizeNounAcc :: NounAcc a name -> (Location, [a], name)
finalizeNounAcc NounAcc{nounLoc = Just loc, nounArgs = args, nounName = Just name} =
    (loc, args [], name)
finalizeNounAcc NounAcc{nounName = Nothing} =
    impossible "nounOf: missing variable slot"
finalizeNounAcc NounAcc{nounLoc = Nothing} =
    impossible "nounOf: empty noun phrase"

buildPhraseTrie
    :: Locatable a
    => Prod r Text (Located Token) a
    -> Trie PhraseStep pat
    -> Prod r Text (Located Token) (Location, pat, [a])
buildPhraseTrie arg trie =
    let stepParser = \case
            PhraseTok tok -> setPhraseLoc <$> tokenPos tok
            PhraseHole    -> addPhraseArg <$> arg
        finish f =
            let (acc, pat) = f emptyPhraseAcc
                (loc, args) = finalizePhraseAcc acc
            in (loc, pat, args)
    in finish <$> buildTrieProd stepParser trie

buildTrieProd
    :: (step -> Prod r Text (Located Token) (acc -> acc))
    -> Trie step pat
    -> Prod r Text (Located Token) (acc -> (acc, pat))
buildTrieProd stepParser = go
    where
        go Trie{trieValues = pats, trieEdges = edges} =
            let leafs = asum [pure (\acc -> (acc, pat)) | pat <- pats]
                edgesProds = asum
                    [ liftA2 (\f g -> g . f) (stepParser step) (go sub)
                    | (step, sub) <- edges
                    ]
            in leafs <|> edgesProds

buildNounTrie
    :: Locatable a
    => Prod r Text (Located Token) a
    -> Prod r Text (Located Token) name
    -> Trie NounStep pat
    -> Prod r Text (Located Token) (Location, pat, [a], name)
buildNounTrie arg vars trie =
    let stepParser = \case
            NounTok tok -> setNounLoc <$> tokenPos tok
            NounHole    -> addNounArg <$> arg
            NounVar     -> setNounName <$> vars
        finish f =
            let (acc, pat) = f emptyNounAcc
                (loc, args, name) = finalizeNounAcc acc
            in (loc, pat, args, name)
    in finish <$> buildTrieProd stepParser trie

buildStructApplicationTrie
    :: Locatable a
    => Prod r Text (Located Token) a
    -> Trie NounStep pat
    -> Prod r Text (Located Token) (Location, pat, [a])
buildStructApplicationTrie arg trie =
    let stepParser step child = case step of
            NounTok tok ->
                setPhraseLoc
                    <$> annotationTokenPos
                        (not (canFinishWithoutToken child))
                        tok
            NounHole -> addPhraseArg <$> arg
            -- The structure object occupies this slot in an ordinary noun
            -- phrase.  An aggregate annotation names only the schema.
            NounVar -> pure id
        go Trie{trieValues = values, trieEdges = edges} =
            let leaves =
                    asum
                        [ pure (\acc -> (acc, value))
                        | value <- values
                        ]
                branches =
                    asum
                        [ liftA2
                            (\first rest -> rest . first)
                            (stepParser step child)
                            (go child)
                        | (step, child) <- edges
                        ]
            in leaves <|> branches
        canFinishWithoutToken Trie{trieValues = values, trieEdges = edges} =
            not (null values)
                || any
                    (\case
                        (NounVar, child) ->
                            canFinishWithoutToken child
                        _ -> False)
                    edges
        finish f =
            let (acc, pat) = f emptyPhraseAcc
                (loc, arguments) = finalizePhraseAcc acc
            in (loc, pat, arguments)
    in finish <$> go trie

-- Structure annotations deliberately live in a math argument while their
-- schema names use ordinary prose.  The lexer therefore emits the letters of
-- a schema word as math variables.  Reconstruct only a known literal word at
-- this grammar position; parameter holes still use the ordinary expression
-- grammar and no special lexer token or mode is introduced.
annotationTokenPos
    :: Bool
    -> Token
    -> Prod r Text (Located Token) Location
annotationTokenPos requiresTrailingSpace token' =
    tokenPos token'
        <|> case token' of
            Word wordText ->
                annotationWordPos requiresTrailingSpace wordText
            _ -> empty

annotationWordPos
    :: Bool
    -> Text
    -> Prod r Text (Located Token) Location
annotationWordPos requiresTrailingSpace wordText =
    case Text.uncons wordText of
        Nothing -> impossible "an empty structure-annotation word"
        Just (firstCharacter, remainingText) -> do
            location <- annotationCharacter firstCharacter (Text.null remainingText)
            consume remainingText
            pure location
  where
    consume remaining =
        case Text.uncons remaining of
            Nothing -> pure ()
            Just (character, rest) ->
                annotationCharacter character (Text.null rest)
                    *> consume rest

    annotationCharacter character isLast =
        terminal \located -> do
            let expected = Text.toCaseFold (Text.singleton character)
                actual = case unLocated located of
                    Variable variable ->
                        Just (Text.toCaseFold variable)
                    Symbol symbolText
                        | character == '-' || character == '\'' ->
                            Just symbolText
                    _ -> Nothing
            guard (actual == Just expected)
            guard
                (if isLast
                    then not requiresTrailingSpace
                        || postWhitespace located == Space
                    else postWhitespace located == NoSpace)
            pure (startPos located)


symbolicPatternOf
    :: forall r. [[MixfixItem]]
    -> Prod r Text (Located Token) VarSymbol
    -> Grammar r (Prod r Text (Located Token) SymbolPattern)
symbolicPatternOf ops varSymbol = rule $
    (tuplePattern <|> asum
        [ go item
        | ops' <- ops
        , item <- ops'
        ]) <?> "a symbolic pattern"
    where
        tuplePattern = do
            token ParenL
            first <- varSymbol <* token (Symbol ",")
            second <- varSymbol <* token ParenR
            pure (SymbolPattern PairSymbol [first, second])

        go :: MixfixItem -> Prod r Text (Located Token) SymbolPattern
        go item = SymbolPattern item <$> parseVars (mixfixPattern item)

        parseVars :: Pattern -> Prod r Text (Located Token) [VarSymbol]
        parseVars = \case
            End -> pure []
            TokenCons tok pat -> token tok *> parseVars pat
            HoleCons pat -> (:) <$> varSymbol <*> parseVars pat


makeNounPhrase
    :: [AdjL]
    -> (Noun, NounBinder (t VarSymbol))
    -> [AdjR]
    -> Maybe Stmt
    -> NounPhrase t
makeNounPhrase ls (n, vs) rs ms = NounPhrase ls n vs rs ms




begin, end :: Text -> Prod r Text (Located Token) Location
begin kind = tokenPos (BeginEnv kind) <?> ("\"\\begin{" <> kind <> "}\"")
end kind   = tokenPos (EndEnv kind) <?> ("\"\\end{" <> kind <> "}\"")

-- | Surround a production rule @body@ with an environment of a certain @kind@ requiring a marker specified in a @\\label@.
envPos :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) (Location, Maybe [Token], Marker, a)
envPos kind body = do
    p <- begin kind <?> ("start of a \"" <> kind <> "\" environment")
    mt <- optional title
    m <- label
    a <- body <* end kind
    pure (p, mt, m, a)
    where
        title :: Prod r Text (Located Token) [Token]
        title = bracket (many (unLocated <$> satisfy (\ltok -> unLocated ltok /= BracketR)))

-- 'env_' is like 'env', but without allowing titles.
--
envPos_ :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) (Location, a)
envPos_ kind body = (,) <$> begin kind <*> (optional label *> body) <* end kind

envStartEndLocation :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) (Location, a, Location)
envStartEndLocation kind body = (,,) <$> begin kind <*> (optional label *> body) <*> end kind

env_ :: Text -> Prod r Text (Located Token) a -> Prod r Text (Located Token) a
env_ kind body = begin kind *> optional label *> body <* end kind

-- | A label specifying a marker for referencing via /@\\label{...}@/. Returns the marker text.
label :: Prod r Text (Located Token) Marker
label = label_ <?> "\"\\label{...}\""
    where
        label_ = terminal \ltok -> case unLocated ltok of
            Label m -> Just (Marker m)
            _tok -> Nothing

commandReference
    :: Text
    -> Prod r Text (Located Token) (NonEmpty Marker)
commandReference expected = terminal \ltok -> case unLocated ltok of
    CommandReference actual markers
        | actual == expected ->
            Just (Marker <$> markers)
    _tok -> Nothing

math :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
math body = beginMath *> body <* endMath

text :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
text body = begin "text" *> body <* end "text" <?> "\"\\text{...}\""

beginMath, endMath :: Prod r Text (Located Token) Location
beginMath = begin "math" <?> "start of a formula, e.g. \"$\""
endMath = end "math" <?> "end of a formula, e.g. \"$\""

paren :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
paren body = token ParenL *> body <* token ParenR <?> "\"(...)\""

bracket :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
bracket body = token BracketL *> body <* token BracketR <?> "\"[...]\""

group :: Prod r Text (Located Token) a -> Prod r Text (Located Token) a
group body = token InvisibleBraceL *> body <* token InvisibleBraceR <?> "\"{...}\""

align :: Prod r Text (Located Token) a -> Prod r Text (Located Token) (Location, a)
align body = (,) <$> begin "align*" <*> body <* end "align*"

maybeVarToken :: Located Token -> Maybe VarSymbol
maybeVarToken ltok = case unLocated ltok of
    Variable x -> Just (NamedVarAt (startPos ltok) x)
    _tok -> Nothing

maybeNonnegativeIntegerTokenWithLoc
    :: Located Token
    -> Maybe (Location, Integer)
maybeNonnegativeIntegerTokenWithLoc ltok = case unLocated ltok of
    Integer n | n >= 0 -> Just (startPos ltok, n)
    _tok -> Nothing

maybeCmdTokenWithLoc :: Located Token -> Maybe (Location, Text)
maybeCmdTokenWithLoc ltok = case unLocated ltok of
    Command n -> Just (startPos ltok, n)
    _tok -> Nothing

structSymbolPos :: StructSymbol -> Prod r Text (Located Token) (Location, StructSymbol)
structSymbolPos s@(StructSymbol c) = terminal \ltok -> case unLocated ltok of
    Command c' | c == c' -> Just (startPos ltok, s)
    _ -> Nothing

token :: Token -> Prod r Text (Located Token) Token
token tok = terminal maybeToken <?> tokToText tok
    where
        maybeToken ltok = case unLocated ltok of
            tok' | tok == tok' -> Just tok
            _ -> Nothing

tokenLocated :: Token -> Prod r Text (Located Token) (Located Token)
tokenLocated tok = terminal maybeToken <?> tokToText tok
    where
        maybeToken ltok = case unLocated ltok of
            tok' | tok == tok' -> Just ltok
            _ -> Nothing

tokenPos :: Token -> Prod r Text (Located Token) Location
tokenPos tok = terminal maybeToken <?> tokToText tok
    where
        maybeToken ltok = case unLocated ltok of
            tok' | tok == tok' -> Just (startPos ltok)
            _ -> Nothing
