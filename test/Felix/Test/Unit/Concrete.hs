{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Concrete (unitTests) where

import Base
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Adapt qualified as Adapt
import Felix.Syntax.FieldEnvelope
import Felix.Syntax.Concrete
    ( ConcreteSyntaxError(..)
    , NativeMathFailure(..)
    , NativeMathParseError(..)
    , NativeMath(..)
    , parseNativeMath
    , prepareNativeMathParser
    , NativeMathParser
    , grammar
    )
import Felix.Syntax.Lexicon (Lexicon(..), builtins)
import Felix.Syntax.Token (Token(..), Located(..))
import Felix.Test.SourceScan.Adapter (scanTestSource)

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Earley (fullParses, parser)

successfulParses :: ([Either error value], report) -> ([value], report)
successfulParses (results, report) =
    ([value | Right value <- results], report)

unitTests :: TestTree
unitTests =
    testGroup "Parser"
        [ testCase
            "textual connectives follow symbolic precedence"
            textualConnectivePrecedence
        , testCase
            "built-in symbolic connectives carry their meanings"
            builtinSymbolicConnectiveMeaning
        , testCase
            "transfinite induction precedes its continuation"
            transfiniteInductionContinuation
        , testCase
            "concrete type arrows associate to the right"
            concreteTypeAssociativity
        , testCase
            "set-map assertions are disjoint from concrete types"
            setMapAssertionSyntax
        , testCase
            "parses typed symbolic expressions without ambiguity"
            typedSymbolicExpressions
        , testCase
            "lowers compact logical application to the existing spine"
            compactLogicalApplication
        , testCase
            "parses grouped Fix binders without merging their scopes"
            groupedFixSyntax
        , testCase "bounded nouns keep one name slot and reject unsupported hosts" boundedNounSyntax
        , testCase "native display parsing preserves category selection" nativeMathematics
        , testCase
            "parses annotated and contextual structure aggregates"
            structureAggregateSyntax
        , testCase
            "parses checked structure reducts"
            structureReductSyntax
        , testCase
            "reconstructions retain their target, base, and grouped replacements"
            structureReconstructionSyntax
        , testCase
            "parses exact structure predicates"
            exactStructurePredicateSyntax
        , testCase
            "parses shared structure field envelopes"
            structureFieldSyntax
        , testCase
            "parses arbitrary-precision integer expressions"
            arbitraryPrecisionIntegerExpression
        , testCase
            "distinguishes natural numerals from opaque integers"
            naturalAndOpaqueIntegerSyntax
        , testCase
            "rejects noncanonical integer expression syntax"
            rejectsNoncanonicalIntegerSyntax
        , testCase
            "parses closed named structure instances"
            structureInstanceSyntax
        , testCase "extracts and parses parameterized construction heads" constructionSyntax
        , testCase
            "distinguishes explicit proof automation methods"
            explicitProofAutomationMethods
        , testCase
            "preserves Have introductions"
            haveIntroductions
        , testCase
            "preserves ordinary assumption introductions"
            assumptionIntroductions
        , testCase
            "splits grouped assumptions and definitions without splitting math"
            groupedIntroductionSyntax
        , testCase
            "parses grouped structure assumptions with exact number agreement"
            groupedStructureAssumptionSyntax
        , testCase
            "parses built-in records without ambiguity"
            recordPhraseSyntax
        , testCase
            "parses symbolic relation Let headers without stealing fixed forms"
            symbolicRelationLetSyntax
        , testCase
            "parses noun right attributes with exact number agreement"
            nounRightAttributeNumberSyntax
        , testCase
            "parses verb and copular agreement structurally"
            structuralPredicateAgreementSyntax
        , testCase
            "parses the algebra vocabulary with exact verb agreement"
            algebraVocabularySyntax
        , testCase
            "parses Since as two independently justified discharges"
            scopedSinceSyntax
        , testCase
            "parses classifications as a distinct claim kind"
            classificationClaimKind
        ]

nativeMathematics :: Assertion
nativeMathematics = do
    let prepared = prepareNativeMathParser builtins
    case parseNativeMath prepared "x=y" of
        Right (NativeTypedExpression (Raw.TypedExpressionFormula{})) ->
            pure ()
        parsed ->
            assertFailure
                ("unexpected presentation formula: " <> show parsed)
    assertEqual
        "type arrows retain ordinary right associativity"
        (Right
            (NativeConcreteType
                (Raw.ConcreteArrow
                    Raw.ConcreteSet
                    (Raw.ConcreteArrow
                        Raw.ConcreteSet
                        Raw.ConcreteSet))))
        (parseNativeMath prepared "\\Set\\to\\Set\\to\\Set")
    assertEqual
        "legacy comma lists remain a presentation form"
        (Right (NativeVariableList ("x" :| ["alpha"])))
        (parseNativeMath prepared "  x, \\alpha  ")
    case parseNativeMath prepared "x+" of
        Left NativeMathRejected{} -> pure ()
        result ->
            assertFailure
                ("ordinary malformed presentation syntax was not rejected: "
                    <> show result)
    let typed = builtins
            { lexiconTypedConstants = [(Command "Set", Raw.ConcreteSet)] }
    case parseNativeMath (prepareNativeMathParser typed) "\\Set" of
        Right NativeTypedExpression{} -> pure ()
        value -> assertFailure ("type displaced the expression parse: " <> show value)
    let ambiguous = typed
            { lexiconTypedConstants =
                [(Command "Set", Raw.ConcreteSet), (Command "Set", Raw.ConcreteProp)] }
    case parseNativeMath (prepareNativeMathParser ambiguous) "\\Set" of
        Left (NativeMathRejected (NativeMathAmbiguous 2)) -> pure ()
        value -> assertFailure ("native ambiguity was lost: " <> show value)
    case parseNativeMath prepared "g(u,y)" of
        Right (NativeTypedExpression (Raw.TypedExpressionExpr
                (Raw.ExprApp _ (Raw.ExprVar (Raw.NamedVar "g"))
                    (Raw.ExprPair _ (Raw.ExprVar (Raw.NamedVar "u"))
                        (Raw.ExprVar (Raw.NamedVar "y")))))) -> pure ()
        value -> assertFailure ("native application shape changed: " <> show value)
    for_ ["2^{-n}", "x=2^{-n}"] \source ->
        assertBool "native parsing does not normalize commentary"
            (isLeft (parseNativeMath prepared source))

arbitraryPrecisionIntegerExpression :: Assertion
arbitraryPrecisionIntegerExpression = do
    let prepared = prepareNativeMathParser builtins
        large = 18446744073709551616 :: Integer
    case parseNativeMath
            prepared
            "18446744073709551616=0" of
        Right
            (NativeTypedExpression
                (Raw.TypedExpressionFormula
                    (Raw.FormulaChain
                        (Raw.ChainBase
            (Raw.ExprNaturalNumeral _ left :| [])
                            _sign
                            _relation
                            (Raw.ExprNaturalNumeral _ right :| []))))) -> do
            assertEqual "left natural numeral" (fromInteger large) left
            assertEqual "right natural numeral" 0 right
        parsed ->
            assertFailure
                ("unexpected large integer expression: " <> show parsed)

naturalAndOpaqueIntegerSyntax :: Assertion
naturalAndOpaqueIntegerSyntax = do
    let prepared = prepareNativeMathParser builtins
        parse source =
            case parseNativeMath prepared source of
                Right
                    (NativeTypedExpression
                        (Raw.TypedExpressionExpr expression)) ->
                    Right expression
                other ->
                    Left (show other)
        assertNatural magnitude =
            case parse (Text.pack (show magnitude)) of
                Right (Raw.ExprNaturalNumeral _ actual) ->
                    assertEqual ("natural " <> show magnitude)
                        magnitude actual
                result ->
                    assertFailure
                        ("unexpected natural parse: " <> show result)
        assertOpaque source expected =
            case parse source of
                Right (Raw.ExprOpaqueInteger _ actual) ->
                    assertEqual (Text.unpack source) expected actual
                result ->
                    assertFailure
                        ("unexpected opaque parse: " <> show result)
    traverse_ assertNatural ([0, 1, 1024] :: [Natural])
    assertOpaque "\\opaqueInteger{0}" 0
    assertOpaque "\\opaqueInteger{37}" 37
    assertOpaque "\\opaqueInteger{-37}" (-37)
    let colliding =
            Raw.mkMixfixItem
                [ Just (Command "opaqueInteger")
                , Just InvisibleBraceL
                , Nothing
                , Just InvisibleBraceR
                ]
                (Raw.Marker "user-opaque-integer")
                Raw.NonAssoc
        collisionLexicon =
            builtins
                { lexiconMixfixTable =
                    Seq.adjust
                        (Map.insert (Raw.mixfixPattern colliding) colliding)
                        9
                        (lexiconMixfixTable builtins)
                }
        typedConstantCollision =
            builtins
                { lexiconTypedConstants =
                    (Command "opaqueInteger", Raw.ConcreteSet)
                        : lexiconTypedConstants builtins
                }
        structureCollision =
            builtins
                { lexiconStructFun =
                    Raw.StructSymbol "opaqueInteger"
                        : lexiconStructFun builtins
                }
        predicateCollision =
            builtins
                { lexiconPrefixPredicates =
                    ( Raw.PrefixPredicate "opaqueInteger" 1
                    , Raw.Marker "user-opaque-integer-predicate"
                    )
                        : lexiconPrefixPredicates builtins
                }
    for_
        [ ("mixfix", collisionLexicon)
        , ("typed constant", typedConstantCollision)
        , ("structure operation", structureCollision)
        , ("prefix predicate", predicateCollision)
        ]
        \(label, candidateLexicon) -> do
            case parseNativeMath
                    (prepareNativeMathParser candidateLexicon)
                    "\\opaqueInteger{5}" of
                Right
                    (NativeTypedExpression
                        (Raw.TypedExpressionExpr
                            (Raw.ExprOpaqueInteger _ 5))) -> pure ()
                result ->
                    assertFailure
                        (label <> " reinterpreted reserved opaque syntax: "
                            <> show result)
            assertBool
                (label <> " accepted the reserved command without a payload")
                (isLeft
                    (parseNativeMath
                        (prepareNativeMathParser candidateLexicon)
                        "\\opaqueInteger"))

rejectsNoncanonicalIntegerSyntax :: Assertion
rejectsNoncanonicalIntegerSyntax = do
    let prepared = prepareNativeMathParser builtins
    for_
        [ "-1"
        , "\\opaqueInteger{+1}"
        , "\\opaqueInteger{}"
        , "\\opaqueInteger{--1}"
        , "\\opaqueInteger{-1 2}"
        ]
        \source ->
            assertBool
                ("noncanonical integer parsed: " <> Text.unpack source)
                (isLeft (parseNativeMath prepared source))
    for_
        [ "$0=0$"
        , "$\\opaqueInteger{0}=0$"
        ]
        assertSyntheticNegativeRejected
    let prefixMinus =
            Raw.mkMixfixItem
                [Just (Symbol "-"), Nothing]
                (Raw.Marker "user-prefix-minus")
                Raw.NonAssoc
        collisionLexicon =
            builtins
                { lexiconMixfixTable =
                    Seq.adjust
                        (Map.insert (Raw.mixfixPattern prefixMinus) prefixMinus)
                        9
                        (lexiconMixfixTable builtins)
                }
    assertBool
        "a user prefix operator did not reinterpret a bare negative decimal"
        (isLeft
            (parseNativeMath
                (prepareNativeMathParser collisionLexicon)
                "-1"))
    let nullaryMinusOne =
            Raw.mkMixfixItem
                [Just (Symbol "-"), Just (Integer 1)]
                (Raw.Marker "user-nullary-minus-one")
                Raw.NonAssoc
        nullaryCollisionLexicon =
            builtins
                { lexiconMixfixTable =
                    Seq.adjust
                        (Map.insert
                            (Raw.mixfixPattern nullaryMinusOne)
                            nullaryMinusOne)
                        9
                        (lexiconMixfixTable builtins)
                }
    assertBool
        "a user nullary operator did not reinterpret a bare negative decimal"
        (isLeft
            (parseNativeMath
                (prepareNativeMathParser nullaryCollisionLexicon)
                "-1"))
    let nullaryOne =
            Raw.mkMixfixItem
                [Just (Integer 1)]
                (Raw.Marker "user-nullary-one")
                Raw.NonAssoc
        naturalCollisionLexicon =
            builtins
                { lexiconMixfixTable =
                    Seq.adjust
                        (Map.insert
                            (Raw.mixfixPattern nullaryOne)
                            nullaryOne)
                        9
                        (lexiconMixfixTable builtins)
                }
    case parseNativeMath
            (prepareNativeMathParser naturalCollisionLexicon)
            "1" of
        Right
            (NativeTypedExpression
                (Raw.TypedExpressionExpr
                    (Raw.ExprNaturalNumeral _ 1))) -> pure ()
        result ->
            assertFailure
                ("a user nullary operator reinterpreted a bare natural: "
                    <> show result)
  where
    assertSyntheticNegativeRejected statement = do
        chunks <- case scanTestSource
                anonymousSourceDescriptor
                "negative-integer-token.tex"
                (Text.unlines
                    [ "\\begin{axiom}\\label{negative_integer_token}"
                    , statement <> "."
                    , "\\end{axiom}"
                    ]) of
            Left failure ->
                assertFailure failure >> fail "unreachable"
            Right (_imports, parsedChunks) ->
                pure parsedChunks
        tokens <- case chunks of
            [single] -> pure single
            _ ->
                assertFailure "negative-token fixture did not produce one chunk"
                    >> fail "unreachable"
        let negativeTokens = replaceFirstMagnitude tokens
            (blocks, _report) = successfulParses
                (fullParses (parser (grammar builtins)) negativeTokens)
        assertEqual "synthetic negative magnitude is rejected" [] blocks

    replaceFirstMagnitude = \case
        [] -> []
        located : remaining ->
            case Raw.unLocated located of
                Integer _ -> (Integer (-1) <$ located) : remaining
                _ -> located : replaceFirstMagnitude remaining


setMapAssertionSyntax :: Assertion
setMapAssertionSyntax = do
    case parseStatement "$f:A\\to B$" of
        Right
            (Raw.StmtFormula
                (Raw.FormulaSetMap
                    _location
                    (Raw.ExprVar (Raw.NamedVar "f"))
                    (Raw.ExprVar (Raw.NamedVar "A"))
                    (Raw.ExprVar (Raw.NamedVar "B")))) ->
            pure ()
        parsed ->
            assertFailure
                ("unexpected set-map assertion: " <> show parsed)
    assertBool
        "a concrete logical type is not a set-map domain"
        (isLeft (parseStatement "$f:\\Set\\to B$"))
    assertBool
        "a set-map assertion has one set-valued codomain expression"
        (isLeft (parseStatement "$f:A\\to B\\to C$"))

compactLogicalApplication :: Assertion
compactLogicalApplication = do
    let prepared = prepareNativeMathParser builtins
        compact = parseLogicalApplication prepared "\\Apply{P}{a,b,d}"
        nested = parseLogicalApplication
            prepared
            "\\Apply{\\Apply{\\Apply{P}{a}}{b}}{d}"
        expected =
            ApplicationApply
                (ApplicationApply
                    (ApplicationApply
                        (ApplicationVariable "P")
                        (ApplicationVariable "a"))
                    (ApplicationVariable "b"))
                (ApplicationVariable "d")
        unary = parseLogicalApplication prepared "\\Apply{P}{a}"
    assertEqual
        "unary application remains valid"
        (Right
            (ApplicationApply
                (ApplicationVariable "P")
                (ApplicationVariable "a")))
        unary
    assertEqual
        "compact application has the existing left-associated shape"
        (Right expected)
        compact
    assertEqual
        "compact and nested spellings lower to the same raw shape"
        nested
        compact
    for_ [Text.empty, ",a", "a,", "a,,b"] \arguments ->
        assertBool
            ( "malformed compact application is rejected: "
                <> Text.unpack arguments)
            (isLeft
                (parseLogicalApplication
                    prepared
                    ("\\Apply{P}{" <> arguments <> "}")))
    case parseNativeMath prepared "\\Apply{R}{(a,b\\rless c),d}" of
        Right _ -> pure ()
        Left err ->
            assertFailure
                ( "parenthesized comma-bearing formula was rejected: "
                    <> show err)
    case parseNativeMath prepared "\\Apply{R}{a=b,d}" of
        Right
            (NativeTypedExpression
                (Raw.TypedExpressionExpr expression)) ->
            case applicationSpine expression of
                Just
                    [ _function
                    , Raw.TypedExpressionFormula
                        (Raw.FormulaChain
                            (Raw.ChainBase
                                (_left :| [])
                                _sign
                                _relation
                                (_right :| [])))
                    , _lastArgument
                    ] ->
                    pure ()
                spine ->
                    assertFailure
                        ( "unexpected comma-free formula argument spine: "
                            <> show spine)
        parsed ->
            assertFailure
                ( "unparenthesized comma-free formula argument was rejected: "
                    <> show parsed)
    assertEqual
        "application commas take precedence over relation-chain commas"
        (Just 4)
        (case parseNativeMath
                prepared
                "\\Apply{R}{a,b\\rless c,d}" of
            Right
                (NativeTypedExpression
                    (Raw.TypedExpressionExpr expression)) ->
                length <$> applicationSpine expression
            _ ->
                Nothing)

groupedFixSyntax :: Assertion
groupedFixSyntax = do
    proof <- parseProof
        (Text.unlines
            [ "Fix $A$ and $x\\in A$ such that $x\\neq\\emptyset$."
            , "Follows."
            ])
    case proof of
        Raw.Fix
                _location
                ( firstBinder
                    :| [secondBinder])
                (Just (Raw.StmtFormula{}))
                (Raw.Qed (Just _) Raw.JustificationImplicit) -> do
            assertEqual
                "unbounded binder remains its own group"
                (Raw.FixBinderSymbolic
                    (Raw.NamedVar "A" :| [])
                    Raw.Unbounded)
                firstBinder
            case secondBinder of
                Raw.FixBinderSymbolic
                        (Raw.NamedVar "x" :| [])
                        (Raw.Bounded _location _sign _relation
                            (Raw.ExprVar (Raw.NamedVar "A"))) ->
                    pure ()
                parsed ->
                    assertFailure
                        ("unexpected dependent binder: " <> show parsed)
        parsed ->
            assertFailure ("unexpected grouped Fix: " <> show parsed)
    let sourceText = Text.unlines
            [ "\\begin{proof}"
            , "Fix $A,x\\in A,f:\\Set\\to\\Set$."
            , "\\end{proof}"
            ]
    tokens <- case scanTestSource
        anonymousSourceDescriptor
        "grouped-fix-malformed.tex"
        sourceText of
        Left err ->
            assertFailure err >> fail "unreachable"
        Right (_imports, [tokens']) -> pure tokens'
        Right (_imports, chunks) ->
            assertFailure
                ("expected one malformed proof chunk, got "
                    <> show (length chunks))
                >> fail "unreachable"
    case successfulParses (fullParses (parser (grammar builtins)) tokens) of
        ([], _report) -> pure ()
        (blocks, report) ->
            assertFailure
                ("single-delimiter mixed Fix unexpectedly parsed as "
                    <> show blocks <> " with " <> show report)

data ApplicationShape
    = ApplicationVariable Text
    | ApplicationApply ApplicationShape ApplicationShape
    deriving (Eq, Show)

parseLogicalApplication
    :: NativeMathParser
    -> Text
    -> Either String ApplicationShape
parseLogicalApplication prepared source =
    case parseNativeMath prepared source of
        Right
            (NativeTypedExpression
                (Raw.TypedExpressionExpr expression)) ->
            maybe
                (Left ("unexpected expression: " <> show expression))
                Right
                (applicationShape expression)
        Right parsed ->
            Left ("unexpected presentation parse: " <> show parsed)
        Left err ->
            Left (show err)

applicationShape :: Raw.Expr -> Maybe ApplicationShape
applicationShape = \case
    Raw.ExprVar (Raw.NamedVar name) ->
        Just (ApplicationVariable name)
    Raw.ExprHigherApply
        _location
        (Raw.TypedExpressionExpr function)
        (Raw.TypedExpressionExpr argument) ->
        ApplicationApply
            <$> applicationShape function
            <*> applicationShape argument
    _ ->
        Nothing

applicationSpine :: Raw.Expr -> Maybe [Raw.TypedExpression]
applicationSpine = go []
  where
    go arguments (Raw.ExprHigherApply _ function argument) =
        case function of
            Raw.TypedExpressionExpr nested@(Raw.ExprHigherApply _ _ _) ->
                go (argument : arguments) nested
            _ ->
                Just (function : argument : arguments)
    go _ _ =
        Nothing

typedSymbolicExpressions :: Assertion
typedSymbolicExpressions = do
    chunks <- case scanTestSource
        anonymousSourceDescriptor
        "typed-symbolic.tex"
        sourceText of
        Left err -> assertFailure err >> fail "unreachable"
        Right (_imports, chunks') -> pure chunks'
    assertEqual "source chunk count" 20 (length chunks)
    for_ (zip [1 :: Int ..] chunks) \(index, tokens) ->
        case successfulParses
                (fullParses (parser (grammar typedLexicon)) tokens) of
            ([_block], _report) -> pure ()
            (blocks, report) ->
                assertFailure
                    ( "chunk " <> show index
                        <> " has " <> show (length blocks)
                        <> " parses: " <> show report
                    )
  where
    setToProp =
        Raw.ConcreteArrow Raw.ConcreteSet Raw.ConcreteProp
    setEndo =
        Raw.ConcreteArrow Raw.ConcreteSet Raw.ConcreteSet
    typedLexicon =
        builtins
            { lexiconTypedConstants =
                [ ( Raw.Variable "Phi"
                  , Raw.ConcreteArrow
                        Raw.ConcreteSet
                        setToProp
                  )
                , (Raw.Command "mathcalP", setToProp)
                , ( Raw.Command "mathcalH"
                  , Raw.ConcreteArrow setEndo Raw.ConcreteProp
                  )
                , (Raw.Command "mathcalI", setEndo)
                ]
            }
    sourceText = Text.unlines
        [ "\\begin{signature}\\label{typed_phi}"
        , "$\\Phi : \\Set\\to\\Set\\to\\Prop$."
        , "\\end{signature}"
        , "\\begin{signature}\\label{typed_predicate}"
        , "$\\mathcalP : \\Set\\to\\Prop$."
        , "\\end{signature}"
        , "\\begin{signature}\\label{typed_function_predicate}"
        , "$\\mathcalH : (\\Set\\to\\Set)\\to\\Prop$."
        , "\\end{signature}"
        , "\\begin{definition}\\label{typed_identity}"
        , "$\\mathcalI : \\Set\\to\\Set = \\fun{x:\\Set}{x}$."
        , "\\end{definition}"
        , "\\begin{axiom}\\label{typed_application}"
        , "$\\forall x:\\Set.\\ \\Apply{\\mathcalP}{x}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_lambda_application}"
        , "$\\Apply{\\mathcalH}{\\fun{x:\\Set}{x}}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_function_equality}"
        , "$\\fun{x:\\Set}{x} = \\fun{y:\\Set}{y}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_select_inferred}"
        , "$\\Apply{\\mathcalP}{\\Select{\\mathcalP}}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_select_explicit}"
        , "$\\Select[\\Set]{\\mathcalP} = \\Select{\\mathcalP}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_select_function}"
        , "$\\Apply{\\mathcalH}{\\Select[\\Set\\to\\Set]{\\mathcalH}}$."
        , "\\end{axiom}"
        , "\\begin{axiom}\\label{typed_proposition_quantifier}"
        , "$\\forall p:\\Prop.\\ p \\iff p$."
        , "\\end{axiom}"
        , "\\begin{proposition}\\label{typed_explicit_fix}"
        , "$\\forall p:\\Prop.\\ p \\implies p$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "Fix $p:\\Prop$."
        , "Assume $p$."
        , "Follows by assumption."
        , "\\end{proof}"
        , "\\begin{proposition}\\label{typed_inferred_fix}"
        , "$\\forall p:\\Prop.\\ p \\iff p$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "Fix $p$."
        , "Follows."
        , "\\end{proof}"
        , "\\begin{proposition}\\label{typed_local_definition}"
        , "$\\forall p:\\Prop.\\ p \\iff p$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "Fix $p:\\Prop$."
        , "Let $q:\\Prop = p$."
        , "Follows."
        , "\\end{proof}"
        , "\\begin{axiom}\\label{typed_prop_witness}"
        , "$\\exists p:\\Prop.\\ p \\iff p$."
        , "\\end{axiom}"
        , "\\begin{proposition}\\label{typed_take}"
        , "$\\exists p:\\Prop.\\ p \\iff p$."
        , "\\end{proposition}"
        , "\\begin{proof}"
        , "Take $p:\\Prop$ such that $p \\iff p$ by \\auto{typed_prop_witness}."
        , "Follows by assumption."
        , "\\end{proof}"
        ]

concreteTypeAssociativity :: Assertion
concreteTypeAssociativity = do
    assertEqual
        "unparenthesized arrow"
        (Right
            (Raw.ConcreteArrow
                Raw.ConcreteSet
                (Raw.ConcreteArrow Raw.ConcreteSet Raw.ConcreteProp)))
        (parseTypedSignatureType "\\Set\\to\\Set\\to\\Prop")
    assertEqual
        "parenthesized domain"
        (Right
            (Raw.ConcreteArrow
                (Raw.ConcreteArrow Raw.ConcreteSet Raw.ConcreteSet)
                Raw.ConcreteProp))
        (parseTypedSignatureType "(\\Set\\to\\Set)\\to\\Prop")
    assertBool
        "ordinary expressions are not concrete types"
        (case parseTypedSignatureType "A" of
            Left _ -> True
            Right _ -> False)

parseTypedSignatureType :: Text -> Either String Raw.ConcreteType
parseTypedSignatureType sourceType = do
    let registeredType = Raw.ConcreteSet
        typedLexicon =
            builtins
                { lexiconTypedConstants =
                    [(Raw.Variable "Phi", registeredType)]
                }
        sourceText =
            Text.unlines
                [ "\\begin{signature}\\label{typed_constant}"
                , "$\\Phi : " <> sourceType <> "$ ."
                , "\\end{signature}"
                ]
    chunks <- case scanTestSource
        anonymousSourceDescriptor
        "concrete-types.tex"
        sourceText of
        Left err ->
            Left err
        Right (_imports, chunks') ->
            Right chunks'
    tokens <- case chunks of
        [tokens'] -> Right tokens'
        _ -> Left ("expected one source chunk, got " <> show (length chunks))
    case successfulParses
            (fullParses (parser (grammar typedLexicon)) tokens) of
        ( [Raw.BlockSig
                _location
                _title
                _marker
                []
                (Raw.SignatureTypedConstant
                    _headLocation
                    (Raw.Variable "Phi")
                    coreType)]
          , _report
          ) ->
            Right coreType
        (blocks, report) ->
            Left
                ( "expected one typed signature, got "
                    <> show blocks
                    <> " with "
                    <> show report
                )

data StatementShape
    = Truth
    | Falsity
    | Connected Raw.Connective StatementShape StatementShape
    | Negated StatementShape
    | Scoped StatementShape
    deriving (Show, Eq)

builtinSymbolicConnectiveMeaning :: Assertion
builtinSymbolicConnectiveMeaning = do
    for_ cases \(label, statement, expected) ->
        assertEqual
            label
            (Right expected)
            (statementShape =<< parseStatement statement)
    assertBool
        "negation requires an operand"
        (isLeft (parseStatement "$\\lnot$"))
  where
    cases =
        [ ( "equivalence"
          , "$\\top \\iff \\bot$"
          , Connected Raw.Equivalence Truth Falsity
          )
        , ( "implication"
          , "$\\top \\implies \\bot$"
          , Connected Raw.Implication Truth Falsity
          )
        , ( "disjunction"
          , "$\\top \\lor \\bot$"
          , Connected Raw.Disjunction Truth Falsity
          )
        , ( "conjunction"
          , "$\\top \\land \\bot$"
          , Connected Raw.Conjunction Truth Falsity
          )
        , ( "negation"
          , "$\\lnot \\top$"
          , Negated Truth
          )
        ]

textualConnectivePrecedence :: Assertion
textualConnectivePrecedence = do
    for_ cases \(label, statement, expected) ->
        assertEqual label (Right expected) (statementShape =<< parseStatement statement)

    assertBool
        "chained iff is rejected"
        (case parseStatement "$\\top$ iff $\\bot$ iff $\\top$" of
            Left _ -> True
            Right _ -> False)

    assertEqual
        "textual and symbolic connective trees agree"
        (statementShape
            =<< parseStatement
                "$\\top \\land \\bot \\lor \\top$")
        (statementShape
            =<< parseStatement
                "$\\top$ and $\\bot$ or $\\top$")
  where
    cases =
        [ ( "and binds tighter than following or"
          , "$\\top$ and $\\bot$ or $\\top$"
          , Connected Raw.Disjunction
                (Connected Raw.Conjunction Truth Falsity)
                Truth
          )
        , ( "and binds tighter than preceding or"
          , "$\\top$ or $\\bot$ and $\\top$"
          , Connected Raw.Disjunction
                Truth
                (Connected Raw.Conjunction Falsity Truth)
          )
        , ( "and associates left"
          , "$\\top$ and $\\bot$ and $\\top$"
          , Connected Raw.Conjunction
                (Connected Raw.Conjunction Truth Falsity)
                Truth
          )
        , ( "or associates left"
          , "$\\top$ or $\\bot$ or $\\top$"
          , Connected Raw.Disjunction
                (Connected Raw.Disjunction Truth Falsity)
                Truth
          )
        , ( "either is accepted after ordinary or"
          , "$\\top$ or either $\\bot$ or $\\top$"
          , Connected Raw.Disjunction
                Truth
                (Connected Raw.ExclusiveOr Falsity Truth)
          )
        , ( "implication associates right"
          , "if $\\top$ then if $\\bot$ then $\\top$"
          , Connected Raw.Implication
                Truth
                (Connected Raw.Implication Falsity Truth)
          )
        , ( "a quantified implication antecedent ends at then"
          , "if for all $x$ we have $\\top$ then $\\bot$"
          , Connected Raw.Implication
                (Scoped Truth)
                Falsity
          )
        , ( "parentheses override precedence"
          , "($\\top$ or $\\bot$) and $\\top$"
          , Connected Raw.Conjunction
                (Connected Raw.Disjunction Truth Falsity)
                Truth
          )
        , ( "a quantified right operand scopes over its continuation"
          , "$\\top$ iff there exists $x$ such that $\\bot$ and $\\top$"
          , Connected Raw.Equivalence
                Truth
                (Scoped
                    (Connected Raw.Conjunction Falsity Truth))
          )
        , ( "a quantified conjunction operand scopes over following disjunctions"
          , "$\\top$ and for all $x$ such that $\\top$ we have $\\bot$ or $\\top$ or $\\bot$"
          , Connected Raw.Conjunction
                Truth
                (Scoped
                    (Connected Raw.Disjunction
                        (Connected Raw.Disjunction Falsity Truth)
                        Falsity))
          )
        , ( "a quantified conjunction operand scopes over following equivalence"
          , "$\\top$ and for all $x$ we have $\\bot$ iff $\\top$"
          , Connected Raw.Conjunction
                Truth
                (Scoped
                    (Connected Raw.Equivalence Falsity Truth))
          )
        , ( "a bare existential remains an ordinary connective operand"
          , "$\\top$ and there exists $x$ or $\\bot$"
          , Connected Raw.Disjunction
                (Connected Raw.Conjunction Truth (Scoped Truth))
                Falsity
          )
        ]

parseStatement :: Text -> Either String Raw.Stmt
parseStatement = parseStatementWith builtins

parseStatementWith :: Lexicon -> Text -> Either String Raw.Stmt
parseStatementWith sourceLexicon statement = do
    chunks <- case scanTestSource
        anonymousSourceDescriptor
        "textual-connectives.tex"
        (Text.unlines
            [ "\\begin{axiom}\\label{textual_connectives}"
            , statement <> "."
            , "\\end{axiom}"
            ]) of
        Left err ->
            Left err
        Right (_imports, chunks') ->
            Right chunks'
    tokens <- case chunks of
        [tokens'] ->
            Right tokens'
        _ ->
            Left ("expected one source chunk, got " <> show (length chunks))
    case successfulParses
            (fullParses (parser (grammar sourceLexicon)) tokens) of
        ( [Raw.BlockAxiom
                _location
                _title
                _marker
                (Raw.Axiom [] statement')]
            , _report
            ) ->
                Right statement'
        (blocks, report) ->
            Left
                ( "expected one axiom, got "
                    <> show blocks
                    <> " with "
                    <> show report
                )

topologicalSpacePhrase :: Raw.SgPl Raw.LexicalPhrase
topologicalSpacePhrase =
    Raw.lexicalPhraseSgPl
        ( (Just "topological", Just "topological")
            :| [(Just "space", Just "spaces")]
        )

structureAggregateSyntax :: Assertion
structureAggregateSyntax = do
    contextual <- parseAggregate
        "$\\structure{X,O}$ is a topological space"
    case contextual of
        Raw.ExprStructAggregate _location Nothing
            [ Raw.StructAggregatePositional
                (Raw.ExprVar (Raw.NamedVar "X"))
            , Raw.StructAggregatePositional
                (Raw.ExprVar (Raw.NamedVar "O"))
            ] -> pure ()
        expression ->
            assertFailure
                ("unexpected contextual aggregate: " <> show expression)

    annotated <- parseAggregate
        "$\\structure[topological space]{\\opens=O,\\carrier=X}=T$"
    case annotated of
        Raw.ExprStructAggregate _location
            (Just (Raw.StructApplication phrase []))
            [ Raw.StructAggregateNamed _ (Raw.StructSymbol "opens")
                (Raw.ExprVar (Raw.NamedVar "O"))
            , Raw.StructAggregateNamed _ Raw.CarrierSymbol
                (Raw.ExprVar (Raw.NamedVar "X"))
            ] ->
                assertEqual
                    "annotated schema phrase"
                    topologicalSpace
                    phrase
        expression ->
            assertFailure
                ("unexpected named aggregate: " <> show expression)

    parameterized <- parseAggregate
        "$\\structure[left module over \\carrier[X]]{A,a,z,n,s}=M$"
    case parameterized of
        Raw.ExprStructAggregate _location
            (Just
                (Raw.StructApplication phrase
                    [ Raw.ExprStructOp _ Raw.CarrierSymbol
                        (Just (Raw.ExprVar (Raw.NamedVar "X")))
                    ]))
            entries -> do
                assertEqual
                    "parameterized schema phrase"
                    leftModule
                    phrase
                assertEqual "parameterized field count" 5 (length entries)
        expression ->
            assertFailure
                ("unexpected parameterized aggregate: " <> show expression)

    mixed <- parseAggregate
        "$\\structure[topological space]{X,\\opens=O}=T$"
    case mixed of
        Raw.ExprStructAggregate _ _
            [Raw.StructAggregatePositional{}, Raw.StructAggregateNamed{}] ->
                pure ()
        expression ->
            assertFailure
                ("mixed aggregate was not preserved for diagnostics: "
                    <> show expression)
    assertBool
        "schema words retain their textbook spacing"
        (isLeft
            (parseStatementWith
                aggregateLexicon
                "$\\structure[topologicalspace]{X,O}=T$"))
  where
    topologicalSpace =
        Raw.mkLexicalItemSgPl
            topologicalSpacePhrase
            "aggregate_topological_space"
    leftModule =
        Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl
                ( (Just "left", Just "left")
                    :| [ (Just "module", Just "modules")
                       , (Just "over", Just "over")
                       , (Nothing, Nothing)
                       ]
                ))
            "aggregate_left_module"
    aggregateLexicon =
        builtins
            { lexiconStructNouns =
                [topologicalSpace, leftModule]
                    <> lexiconStructNouns builtins
            , lexiconStructFun =
                Raw.StructSymbol "opens"
                    : lexiconStructFun builtins
            }
    parseAggregate source = do
        statement <-
            either assertFailure pure
                (parseStatementWith aggregateLexicon source)
        case statement of
            Raw.StmtStruct
                    (Raw.TermExpr aggregate@Raw.ExprStructAggregate{})
                    _structure ->
                pure aggregate
            Raw.StmtFormula
                    (Raw.FormulaChain
                        (Raw.ChainBase
                            (aggregate@Raw.ExprStructAggregate{} :| [])
                            Raw.Positive
                            (Raw.Relation _ Raw.EqSymbol [])
                            (_right :| []))) ->
                pure aggregate
            _ ->
                assertFailure
                    ("unexpected aggregate statement: " <> show statement)
                    >> fail "unreachable"

structureReductSyntax :: Assertion
structureReductSyntax = do
    statement <- either assertFailure pure
        (parseStatementWith reductLexicon
            "$\\reduct[topological space]{T}=R$")
    case statement of
        Raw.StmtFormula
                (Raw.FormulaChain
                    (Raw.ChainBase
                        (Raw.ExprStructReduct
                            _location
                            (Raw.StructApplication phrase [])
                            (Raw.ExprVar (Raw.NamedVar "T"))
                            :| [])
                        Raw.Positive
                        (Raw.Relation _ Raw.EqSymbol [])
                        (Raw.ExprVar (Raw.NamedVar "R") :| []))) ->
            assertEqual "reduct schema phrase" topologicalSpace phrase
        _ ->
            assertFailure ("unexpected reduct statement: " <> show statement)
  where
    topologicalSpace =
        Raw.mkLexicalItemSgPl
            topologicalSpacePhrase
            "reduct_topological_space"
    reductLexicon =
        builtins
            { lexiconStructNouns =
                topologicalSpace : lexiconStructNouns builtins
            }

structureReconstructionSyntax :: Assertion
structureReconstructionSyntax = do
    let space = Raw.mkLexicalItemSgPl topologicalSpacePhrase "reconstruction_space"
        lexicon = builtins
            { lexiconStructNouns = space : lexiconStructNouns builtins
            , lexiconStructFun = Raw.StructSymbol "opens" : lexiconStructFun builtins
            }
        prepared = prepareNativeMathParser lexicon
        parse source = case parseNativeMath prepared source of
            Right (NativeTypedExpression (Raw.TypedExpressionExpr expression)) -> pure expression
            other -> assertFailure ("unexpected reconstruction parse: " <> show other) >> fail "unreachable"
    bare <- parse "topological space based on T"
    case bare of
        Raw.ExprStructReconstruction _ (Raw.StructApplication actual [])
                (Raw.ExprVar (Raw.NamedVar "T")) [] -> actual @?= space
        other -> assertFailure (show other)
    nested <- parse "topological space based on T with \\opens = (topological space based on R with \\opens = O) and \\carrier = X"
    case nested of
        Raw.ExprStructReconstruction _ _ _
                [ Raw.StructAggregateNamed _ (Raw.StructSymbol "opens")
                    (Raw.ExprStructReconstruction _ _ _ [_])
                , Raw.StructAggregateNamed _ Raw.CarrierSymbol (Raw.ExprVar (Raw.NamedVar "X"))
                ] -> pure ()
        other -> assertFailure (show other)
    assertBool "unparenthesized nested clauses do not acquire an owner by field lookup"
        (isLeft (parseNativeMath prepared
            "topological space based on T with \\opens = topological space based on R with \\opens = O and \\carrier = X"))
    for_ ["(topological space based on T with \\opens=O)=R",
            "\\opens[(topological space based on T with \\opens=O)]=O"] \source ->
        case parseNativeMath prepared source of
            Right (NativeTypedExpression (Raw.TypedExpressionFormula{})) -> pure ()
            other -> assertFailure ("grouping lost in formula: " <> show other)

exactStructurePredicateSyntax :: Assertion
exactStructurePredicateSyntax = do
    named <- either assertFailure pure
        (parseStatementWith exactLexicon
            "$T$ is an exact topological space")
    contextual <- either assertFailure pure
        (parseStatementWith exactLexicon
            "$\\structure{X,O}$ is an exact topological space")
    case named of
        Raw.StmtExactStruct
                (Raw.TermExpr (Raw.ExprVar (Raw.NamedVar "T")))
                (Raw.StructApplication phrase []) ->
            assertEqual "exact predicate phrase" topologicalSpace phrase
        _ ->
            assertFailure
                ("unexpected named exact predicate: " <> show named)
    case contextual of
        Raw.StmtExactStruct
                (Raw.TermExpr Raw.ExprStructAggregate{})
                (Raw.StructApplication phrase []) ->
            assertEqual
                "contextual exact aggregate phrase"
                topologicalSpace
                phrase
        _ ->
            assertFailure
                ("unexpected contextual exact predicate: "
                    <> show contextual)
  where
    topologicalSpace =
        Raw.mkLexicalItemSgPl
            topologicalSpacePhrase
            "exact_topological_space"
    exactLexicon =
        builtins
            { lexiconStructNouns =
                topologicalSpace : lexiconStructNouns builtins
            }

structureFieldSyntax :: Assertion
structureFieldSyntax = do
    canonical <- parseStructure
        (structureSource
            "\\item\\label{widget_value_field} a set $\\widgetValue[X]$;")
    case Raw.structFields canonical of
        [Raw.StructField
            _location
            [Raw.Word "a", Raw.Word "set"]
            (Just "widget_value_field")
            (Raw.StructSymbol "widgetValue")
            Nothing] -> pure ()
        fields ->
            assertFailure
                ("unexpected canonical owned field: " <> show fields)

    bare <- parseStructure
        (structureSource "\\item $\\widgetValue$;")
    case Raw.structFields bare of
        [Raw.StructField
            _location
            []
            Nothing
            (Raw.StructSymbol "widgetValue")
            Nothing] -> pure ()
        fields ->
            assertFailure
                ("unexpected bare field: " <> show fields)

    bounded <- parseStructure
        (structureSource
            "\\item a map $\\widgetValue[X]:\\carrier[X]\\to\\carrier[X]$;")
    case Raw.structFields bounded of
        [Raw.StructField
            _location
            [Raw.Word "a", Raw.Word "map"]
            Nothing
            (Raw.StructSymbol "widgetValue")
            (Just Raw.StmtFormula{})] -> pure ()
        fields ->
            assertFailure
                ("unexpected bounded field: " <> show fields)

    relation <- parseStructure
        (structureSource "\\item a family of sets $\\widgetValue[X]\\subseteq A$;")
    case Raw.structFields relation of
        [Raw.StructField _ _ _ _ (Just (Raw.StmtFormula (Raw.FormulaChain _)))] -> pure ()
        fields -> assertFailure ("unexpected relational field: " <> show fields)

    assertWrongReceiver
        (structureSource "\\item a set $\\widgetValue[Y]$;")
    unowned <- parseStructure
        (structureSource "\\item a set $\\widgetValue$;")
    assertEqual "unowned set field retains its description" [Raw.Word "a", Raw.Word "set"]
        (concatMap Raw.structFieldDescription (Raw.structFields unowned))
    assertWrongReceiver
        (structureSource "\\item a map $\\widgetValue[Y]:A\\to B$;")
    for_ [ "\\item"
         , "\\item $\\widgetValue$"
         , "\\item $\\widgetValue$;;"
         , "\\item a set $\\widgetValue[]$;"
         , "\\item a set $\\widgetValue[X)$;"
         , "\\item a set $\\widgetValue[X]$; extra"
         , "\\item a set $\\widgetValue \\in A$;"
         ] (assertStructureRejected . structureSource)
  where
    structureSource field =
        Text.unlines
            [ "\\begin{struct}\\label{widget}"
            , "A widget $X$ is a onesorted structure equipped with"
            , "\\begin{enumerate}"
            , field
            , "\\end{enumerate}."
            , "\\end{struct}"
            ]

    widgetPhrase =
        Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl
                ((Just "widget", Just "widgets") :| []))
            "widget"

    structureLexicon =
        builtins
            { lexiconRelationSymbols = Raw.SubseteqSymbol : lexiconRelationSymbols builtins
            , lexiconStructNouns =
                widgetPhrase : lexiconStructNouns builtins
            , lexiconStructFun =
                Raw.StructSymbol "widgetValue"
                    : lexiconStructFun builtins
            }

    parseStructure sourceText = do
        tokens <- scanStructure sourceText
        envelopes <- either (fail . show) pure (structureFieldEnvelopes tokens)
        extracted <- either (fail . show) pure (Adapt.prepareLexicalChunk tokens)
        assertEqual "extraction uses the envelope's command and source location"
            [ (startPos (fieldEnvelopeCommand envelope),
                Adapt.ExtractedStructureOperation (unLocated (fieldEnvelopeCommand envelope)))
            | envelope <- envelopes
            ]
            [ (startPos item, unLocated item)
            | item <- Adapt.preparedLexicalItems extracted
            , Adapt.ExtractedStructureOperation{} <- [unLocated item]
            ]
        for_ envelopes \envelope -> do
            assertEqual "one semicolon" (Symbol ";")
                (unLocated (fieldEnvelopeTerminator envelope))
            for_ (fieldEnvelopeOwner envelope) \owner ->
                assertEqual "owner expression slice" [Variable "X"] (unLocated <$> owner)
        case successfulParses
                (fullParses (parser (grammar structureLexicon)) tokens) of
            ([Raw.BlockStruct _location _title _marker structure], _report) -> do
                assertEqual "the parsed fields consume exactly the recognized envelopes"
                    [ ( startPos (fieldEnvelopeCommand envelope)
                      , fieldEnvelopeDescription envelope
                      , Raw.Marker <$> fieldEnvelopeLabel envelope
                      , Raw.StructSymbol (unLocated (fieldEnvelopeCommand envelope))
                      , not (null (fieldEnvelopeSpecification envelope))
                      )
                    | envelope <- envelopes
                    ]
                    [ (Raw.structFieldLocation field, Raw.structFieldDescription field,
                        Raw.structFieldMarker field, Raw.structFieldSymbol field,
                        isJust (Raw.structFieldSpecification field))
                    | field <- Raw.structFields structure
                    ]
                pure structure
            (blocks, report) ->
                assertFailure
                    ( "expected one structure, got "
                        <> show blocks
                        <> " with "
                        <> show report
                    )
                    >> fail "unreachable"

    assertStructureRejected sourceText = do
        tokens <- scanStructure sourceText
        extractionFailure <- case Adapt.prepareLexicalChunk tokens of
            Left (Adapt.InvalidStructureFieldEnvelope failure) -> pure failure
            _ -> assertFailure "expected envelope rejection"
                >> fail "unreachable"
        case nubOrd (fst (fullParses (parser (grammar structureLexicon)) tokens)) of
            [Left (InvalidFieldEnvelope failure)] ->
                assertEqual "extraction and parsing report the same envelope error"
                    extractionFailure failure
            results -> assertFailure ("unexpected invalid-field result: " <> show results)

    assertWrongReceiver sourceText = do
        tokens <- scanStructure sourceText
        case nubOrd
                (fst (fullParses
                    (parser (grammar structureLexicon))
                    tokens)) of
            [Left
                (OwnedStructureFieldReceiverMismatch
                    _location
                    (Raw.NamedVar "X")
                    (Raw.ExprVar (Raw.NamedVar "Y")))] -> pure ()
            results ->
                assertFailure
                    ("unexpected wrong-receiver result: " <> show results)

    scanStructure sourceText =
        case scanTestSource
                anonymousSourceDescriptor
                "structure-field.tex"
                sourceText of
            Left err ->
                assertFailure err >> fail "unreachable"
            Right (_imports, [tokens]) -> pure tokens
            Right (_imports, chunks) ->
                assertFailure
                    ("expected one structure chunk, got " <> show (length chunks))
                    >> fail "unreachable"

constructionSyntax :: Assertion
constructionSyntax = do
    let source = Text.unlines
            [ "\\begin{construction}\\label{construction_parser}"
            , "Let $X$ be a topological space."
            , "The topological space $\\CopyTopology{X}=topological space based on X$."
            , "\\end{construction}"
            ]
        space = Raw.mkLexicalItemSgPl topologicalSpacePhrase "construction_space"
    tokens <- case scanTestSource anonymousSourceDescriptor "construction.tex" source of
        Right (_, [chunk]) -> pure chunk
        other -> assertFailure (show other) >> fail "unreachable"
    extracted <- either (fail . show) pure (Adapt.prepareLexicalChunk tokens)
    (pattern', marker) <- case unLocated <$> Adapt.preparedLexicalItems extracted of
        [Adapt.ExtractedFunctionSymbol pattern' marker] -> pure (pattern', marker)
        other -> assertFailure (show other) >> fail "unreachable"
    let lexicon = builtins
            { lexiconStructNouns = space : lexiconStructNouns builtins
            , lexiconMixfixTable = Seq.adjust
                (Map.insert pattern' (Raw.MixfixItem pattern' marker Raw.NonAssoc)) 0
                (lexiconMixfixTable builtins)
            }
    case successfulParses (fullParses (parser (grammar lexicon)) tokens) of
        ([Raw.BlockConstruction _ _ actual construction], _) -> do
            actual @?= marker
            length (Raw.constructionAssumptions construction) @?= 1
            case Raw.constructionHead construction of
                Raw.SymbolPattern _ parameters -> parameters @?= ["X"]
            case Raw.constructionValue construction of
                Raw.ExprStructReconstruction _ _ (Raw.ExprVar "X") [] -> pure ()
                other -> assertFailure (show other)
        other -> assertFailure (show other)

structureInstanceSyntax :: Assertion
structureInstanceSyntax = do
    equation <- parseInstance
        "\\begin{instance}\\label{instance_equation}"
        "The topological space $\\InstanceEquation=\\structure{X,O}$."
        "\\end{instance}"
    natural <- parseInstance
        "\\begin{instance}\\label{instance_natural}"
        "The topological space $\\InstanceNatural$ is $\\structure{X,O}$."
        "\\end{instance}"
    checkInstance (Raw.Command "InstanceEquation") equation
    checkInstance (Raw.Command "InstanceNatural") natural
    rejectFamilyInstance
  where
    topologicalSpace =
        Raw.mkLexicalItemSgPl
            topologicalSpacePhrase
            "instance_topological_space"
    instanceLexicon token =
        builtins
            { lexiconStructNouns =
                topologicalSpace : lexiconStructNouns builtins
            , lexiconTypedConstants =
                (token, Raw.ConcreteSet)
                    : lexiconTypedConstants builtins
            }
    parseInstance beginLine bodyLine endLine = do
        let token =
                if "Natural" `Text.isInfixOf` bodyLine
                    then Raw.Command "InstanceNatural"
                    else Raw.Command "InstanceEquation"
        chunks <- case scanTestSource
            anonymousSourceDescriptor
            "structure-instance.tex"
            (Text.unlines [beginLine, bodyLine, endLine]) of
            Left err ->
                assertFailure err >> fail "unreachable"
            Right (_imports, chunks') -> pure chunks'
        tokens <- case chunks of
            [tokens'] -> pure tokens'
            _ ->
                assertFailure
                    ("expected one instance chunk, got " <> show (length chunks))
                    >> fail "unreachable"
        case successfulParses
                (fullParses
                    (parser (grammar (instanceLexicon token)))
                    tokens) of
            ([Raw.BlockInstance _location _title _marker instanceDefn], _report) ->
                pure instanceDefn
            (blocks, report) ->
                assertFailure
                    ("unexpected instance parse: " <> show blocks
                        <> " with " <> show report)
                    >> fail "unreachable"
    checkInstance expectedToken instanceDefn = do
        assertEqual "atomic instance name"
            expectedToken
            (Raw.instanceNameToken instanceDefn)
        case Raw.instanceValue instanceDefn of
            Raw.ExprStructAggregate _ Nothing
                    [ Raw.StructAggregatePositional{}
                    , Raw.StructAggregatePositional{}
                    ] -> pure ()
            value ->
                assertFailure ("unexpected instance value: " <> show value)

    rejectFamilyInstance = do
        let source = Text.unlines
                [ "\\begin{instance}\\label{instance_family}"
                , "The topological space $\\InstanceFamily{A}=\\structure{A,O}$."
                , "\\end{instance}"
                ]
            token = Raw.Command "InstanceFamily"
        chunks <- case scanTestSource
            anonymousSourceDescriptor "structure-instance-family.tex" source of
            Left err ->
                assertFailure err >> fail "unreachable"
            Right (_imports, chunks') -> pure chunks'
        tokens <- case chunks of
            [tokens'] -> pure tokens'
            _ ->
                assertFailure
                    ("expected one family-instance chunk, got "
                        <> show (length chunks))
                    >> fail "unreachable"
        let (blocks, _report) = successfulParses
                (fullParses
                    (parser (grammar (instanceLexicon token)))
                    tokens)
        assertBool
            "an instance head cannot bind a parameterized construction family"
            (null blocks)

statementShape :: Raw.Stmt -> Either String StatementShape
statementShape = \case
    Raw.StmtConnected conn _ left right ->
        Connected conn
            <$> statementShape left
            <*> statementShape right
    Raw.StmtFormula formula ->
        formulaShape formula
    Raw.SymbolicQuantified _ _ _ _ _ statement ->
        Scoped <$> statementShape statement
    statement ->
        Left ("unsupported statement in precedence test: " <> show statement)

formulaShape :: Raw.Formula -> Either String StatementShape
formulaShape = \case
    Raw.PropositionalConstant _ Raw.IsTop ->
        Right Truth
    Raw.PropositionalConstant _ Raw.IsBottom ->
        Right Falsity
    Raw.Connected _ conn left right ->
        Connected conn
            <$> formulaShape left
            <*> formulaShape right
    Raw.FormulaNeg _ formula ->
        Negated <$> formulaShape formula
    formula ->
        Left ("unsupported formula in precedence test: " <> show formula)

transfiniteInductionContinuation :: Assertion
transfiniteInductionContinuation =
    case scanTestSource
        anonymousSourceDescriptor
        "transfinite-induction.tex"
        sourceText of
        Left err ->
            assertFailure err
        Right (_imports, [tokens]) ->
            case successfulParses
                    (fullParses (parser (grammar builtins)) tokens) of
                ( [ Raw.BlockProof
                        _start
                        (Raw.ByOrdInduction methodLocation
                            (Raw.Qed
                                (Just continuationLocation)
                                Raw.JustificationImplicit))
                        _end
                  ]
                    , _report
                    ) -> do
                        assertEqual
                            "method header line"
                            2
                            (locLine methodLocation)
                        assertEqual
                            "continuation line"
                            3
                            (locLine continuationLocation)
                (blocks, report) ->
                    assertFailure
                        ( "expected one transfinite-induction proof, got "
                            <> show blocks
                            <> " with "
                            <> show report
                        )
        Right (_imports, chunks) ->
            assertFailure
                ("expected one proof chunk, got " <> show (length chunks))
  where
    sourceText =
        Text.unlines
            [ "\\begin{proof}"
            , "[proof by transfinite induction]"
            , "Follows."
            , "\\end{proof}"
            ]

explicitProofAutomationMethods :: Assertion
explicitProofAutomationMethods = do
    parsed <-
        traverse
            (\source -> parseProof source >>= proofJustification)
            [ "Follows by \\auto."
            , "Follows by \\auto{first,second}."
            , "Follows by \\obv{first,second}."
            , "Follows by assumption."
            , "Follows by definition."
            , "Follows by notion."
            ]
    assertEqual
        "raw proof methods retain their distinct policies"
        [ Raw.JustificationAuto Nothing
        , Raw.JustificationAuto
            (Just (Raw.Marker "first" :| [Raw.Marker "second"]))
        , Raw.JustificationObviousReferences
            (Raw.Marker "first" :| [Raw.Marker "second"])
        , Raw.JustificationAssumption
        , Raw.JustificationDefinition
        , Raw.JustificationNotion
        ]
        parsed
    for_ ["\\obv", "\\auto[local]"] assertMethodRejected
  where
    proofJustification = \case
        Raw.Qed (Just _location) justification -> pure justification
        proof ->
            assertFailure ("unexpected proof shape: " <> show proof)
                >> fail "unreachable"

    assertMethodRejected method = do
        let sourceText =
                Text.unlines
                    [ "\\begin{proof}"
                    , "Follows by " <> method <> "."
                    , "\\end{proof}"
                    ]
        tokens <- case scanTestSource
            anonymousSourceDescriptor
            "bare-obvious.tex"
            sourceText of
            Left err ->
                assertFailure err >> fail "unreachable"
            Right (_imports, [tokens']) -> pure tokens'
            Right (_imports, chunks) ->
                assertFailure
                    ("expected one proof chunk, got " <> show (length chunks))
                    >> fail "unreachable"
        case successfulParses
                (fullParses (parser (grammar builtins)) tokens) of
            ([], _report) -> pure ()
            (blocks, _report) ->
                assertFailure
                    (show method <> " unexpectedly parsed as " <> show blocks)

scopedSinceSyntax :: Assertion
scopedSinceSyntax = do
    proof <-
        parseProof
            (Text.unlines
                [ "Since $x=x$ by assumption, we have $x=x$ by \\obv{seed}."
                , "Follows."
                ])
    case proof of
        Raw.Since
                premiseLocation _premise Raw.JustificationAssumption
                claimLocation _claim
                (Raw.JustificationObviousReferences
                    (Raw.Marker "seed" :| []))
                (Raw.Qed (Just _continuationLocation)
                    Raw.JustificationImplicit) -> do
            assertEqual "premise location line" 2 (locLine premiseLocation)
            assertEqual "claim location line" 2 (locLine claimLocation)
            assertBool
                "claim discharge has its own later source location"
                (locColumn premiseLocation < locColumn claimLocation)
        parsed ->
            assertFailure ("unexpected Since proof shape: " <> show parsed)

haveIntroductions :: Assertion
haveIntroductions =
    for_ introductions \(prefix, expectedIntro, expectedColumn) -> do
        let conclusion =
                (if Text.null prefix then "" else prefix <> " ")
                    <> "$x=x$ by assumption."
        proof <- parseProof (Text.unlines [conclusion, "Follows."])
        case proof of
            Raw.Have
                    location actualIntro _statement
                    Raw.JustificationAssumption
                    (Raw.Qed (Just _continuationLocation)
                        Raw.JustificationImplicit) -> do
                assertEqual
                    ("introduction for " <> show prefix)
                    expectedIntro
                    actualIntro
                assertEqual
                    ("introduction line for " <> show prefix)
                    2
                    (locLine location)
                assertEqual
                    ("introduction column for " <> show prefix)
                    expectedColumn
                    (locColumn location)
            parsed ->
                assertFailure
                    ("unexpected Have proof for "
                        <> show prefix
                        <> ": "
                        <> show parsed)
  where
    introductions =
        [ ("", Raw.HaveNoIntro, 2)
        , ("we have", Raw.HaveWeHave, 1)
        , ("we have that", Raw.HaveWeHave, 1)
        , ("thus", Raw.HaveThus, 1)
        , ("hence", Raw.HaveHence, 1)
        , ("then", Raw.HaveThen, 1)
        , ("next", Raw.HaveNext, 1)
        , ("now", Raw.HaveNow, 1)
        , ("first", Raw.HaveFirst, 1)
        , ("finally", Raw.HaveFinally, 1)
        , ("subsequently", Raw.HaveSubsequently, 1)
        , ("ultimately", Raw.HaveUltimately, 1)
        , ("therefore", Raw.HaveTherefore, 1)
        , ("particularly,", Raw.HaveParticularly, 1)
        , ("in particular,", Raw.HaveInParticular, 4)
        ]

assumptionIntroductions :: Assertion
assumptionIntroductions =
    for_ introductions \(keyword, expectedIntro) -> do
        proof <- parseProof (keyword <> " $x=x$.")
        case proof of
            Raw.Assume location actualIntro _statement
                    (Raw.Qed Nothing
                        Raw.JustificationImplicit) -> do
                assertEqual
                    ("introduction for " <> show keyword)
                    expectedIntro
                    actualIntro
                assertEqual
                    ("introduction line for " <> show keyword)
                    2
                    (locLine location)
                assertEqual
                    ("introduction column for " <> show keyword)
                    1
                    (locColumn location)
            parsed ->
                assertFailure
                    ("unexpected Assume proof for "
                        <> show keyword
                        <> ": "
                        <> show parsed)
  where
    introductions =
        [ ("Assume", Raw.AssumeIntroAssume)
        , ("Suppose", Raw.AssumeIntroSuppose)
        , ("Suppose that", Raw.AssumeIntroSuppose)
        ]

groupedIntroductionSyntax :: Assertion
groupedIntroductionSyntax = do
    grouped <-
        parseProof
            (Text.unlines
                [ "Assume that $x\\in A$ and $y\\in B$."
                , "Follows."
                ])
    case grouped of
        Raw.Assume
                firstLocation Raw.AssumeIntroAssume _
                (Raw.Assume
                    secondLocation Raw.AssumeIntroAssume _
                    (Raw.Qed _ Raw.JustificationImplicit)) -> do
            assertEqual "grouped assumption introduction column" 1
                (locColumn firstLocation)
            assertEqual "grouped assumption location line" 2
                (locLine secondLocation)
            assertBool
                "later grouped assumptions use their statement locations"
                (locColumn firstLocation < locColumn secondLocation)
        parsed ->
            assertFailure
                ("unexpected grouped assumption structure: " <> show parsed)

    repeated <-
        parseProof
            (Text.unlines
                [ "Assume $x\\in A$."
                , "Assume $y\\in B$."
                , "Follows."
                ])
    case repeated of
        Raw.Assume
                _ Raw.AssumeIntroAssume _
                (Raw.Assume
                    _ Raw.AssumeIntroAssume _
                    (Raw.Qed _ Raw.JustificationImplicit)) ->
            pure ()
        parsed ->
            assertFailure
                ("unexpected repeated assumption structure: " <> show parsed)

    compound <- parseProof "Assume $(x\\in A)\\land(y\\in B)$."
    case compound of
        Raw.Assume
                _ Raw.AssumeIntroAssume
                (Raw.StmtFormula{})
                (Raw.Qed _ Raw.JustificationImplicit) ->
            pure ()
        parsed ->
            assertFailure
                ("explicit conjunction was split: " <> show parsed)

    definitions <-
        parseProof
            (Text.unlines
                [ "Let $A=1$ and $B=A$."
                , "Follows."
                ])
    case definitions of
        Raw.Define firstLocation (Raw.NamedVar "A") _
                (Raw.Define secondLocation (Raw.NamedVar "B") _
                    (Raw.Qed _ Raw.JustificationImplicit)) -> do
            assertEqual "grouped definition location line" 2
                (locLine secondLocation)
            assertBool
                "grouped definitions use their clause locations"
                (locColumn firstLocation < locColumn secondLocation)
        parsed ->
            assertFailure
                ("unexpected grouped definition structure: " <> show parsed)

    Raw.Claim _asms _statement <- parseClaim
        (Text.unlines
            [ "Suppose $x\\in A$ and $y\\in B$."
            , "Then $x\\in A$."
            ])
    assertEqual "grouped declaration assumptions are separate" 2 (length _asms)

    Raw.Claim repeatedAsms _statement <- parseClaim
        (Text.unlines
            [ "Suppose $x\\in A$."
            , "Suppose $y\\in B$."
            , "Then $x\\in A$."
            ])
    assertEqual "repeated declaration assumptions remain separate" 2
        (length repeatedAsms)

    Raw.Claim letAsms _statement <- parseClaim
        (Text.unlines
            [ "Let $A$ be a set, $x\\in A$, and $B=\\pow{A}$."
            , "Then $x\\in A$."
            ])
    case letAsms of
        [ Raw.AsmLetNoun _ _
            , Raw.AsmLetIn _ _
            , Raw.AsmLetEq _ _
            ] -> pure ()
        parsed ->
            assertFailure
                ("unexpected grouped declaration Lets: " <> show parsed)

    Raw.Claim repeatedLetAsms _statement <- parseClaim
        (Text.unlines
            [ "Let $A$ be a set."
            , "Let $x\\in A$."
            , "Then $x\\in A$."
            ])
    case repeatedLetAsms of
        [ Raw.AsmLetNoun _ _
            , Raw.AsmLetIn _ _
            ] -> pure ()
        parsed ->
            assertFailure
                ("unexpected repeated declaration Lets: " <> show parsed)

    assertProofRejected "Assume $x\\in A$ and that $y\\in B$."
    assertProofRejected "Assume that $x\\in A$ and that $y\\in B$."

recordPhraseSyntax :: Assertion
recordPhraseSyntax = do
    traverse_
        (\source -> do
            claim <- either assertFailure pure (parseClaimWith recordLexicon source)
            case claim of
                Raw.Claim [Raw.AsmLetStruct _variables
                        (Raw.StructNounPhrase [] (Raw.StructApplication phrase []) [] Nothing)] _ ->
                    assertEqual "record phrase identity" recordPhrase phrase
                other -> assertFailure ("unexpected record introduction: " <> show other))
        [ "Let $R$ be a record. Then $R=R$."
        , "Let $R,S$ be records. Then $R=R$."
        ]
    traverse_
        (\source -> assertBool "record number disagreement is rejected"
            (isLeft (parseClaimWith recordLexicon source)))
        [ "Let $R$ be records. Then $R=R$."
        , "Let $R,S$ be a record. Then $R=R$."
        ]
  where
    recordPhrase = Raw.mkLexicalItemSgPl
        (Raw.lexicalPhraseSgPl ((Just "record", Just "records") :| []))
        "record"
    recordLexicon = builtins

groupedStructureAssumptionSyntax :: Assertion
groupedStructureAssumptionSyntax = do
    singular <- parseWith "Let $G$ be a group. Then $G=G$."
    case singular of
        Raw.Claim
            [ Raw.AsmLetStruct
                (Raw.NamedVar "G" :| [])
                (Raw.StructNounPhrase []
                    (Raw.StructApplication phrase []) [] Nothing)
            ]
            _conclusion ->
                assertEqual "singular structure phrase" groupPhrase phrase
        claim ->
            assertFailure
                ("unexpected singular structure claim: " <> show claim)

    plural <- parseWith "Let $G,H$ be groups. Then $G=G$."
    case plural of
        Raw.Claim
            [ Raw.AsmLetStruct
                (Raw.NamedVar "G" :| [Raw.NamedVar "H"])
                (Raw.StructNounPhrase []
                    (Raw.StructApplication phrase []) [] Nothing)
            ]
            _conclusion ->
                assertEqual "plural structure phrase" groupPhrase phrase
        claim ->
            assertFailure
                ("unexpected plural structure claim: " <> show claim)

    parameterized <-
        parseWith
            "Let $M,N$ be left modules over $R$. Then $M=M$."
    case parameterized of
        Raw.Claim
            [ Raw.AsmLetStruct
                (Raw.NamedVar "M" :| [Raw.NamedVar "N"])
                (Raw.StructNounPhrase []
                    (Raw.StructApplication phrase
                        [Raw.TermExpr
                            (Raw.ExprVar (Raw.NamedVar "R"))])
                    []
                    Nothing)
            ]
            _conclusion ->
                assertEqual
                    "plural parameterized structure phrase"
                    leftModulePhrase
                    phrase
        claim ->
            assertFailure
                ("unexpected parameterized structure claim: " <> show claim)

    singularRich <- parseWith
        "Let $G$ be a group that is equal to $H$ such that $G=H$. Then $G=G$."
    assertRichStructurePhrase "singular rich" 1 singularRich

    pluralRich <- parseWith
        "Let $G,H$ be groups that are equal to $A$ and equal to $A$ such that $G=H$. Then $G=G$."
    assertRichStructurePhrase "coordinated plural rich" 2 pluralRich

    traverse_
        (\source ->
            assertBool
                ("number disagreement parsed: " <> Text.unpack source)
                (isLeft (parseClaimWith structureLexicon source)))
        [ "Let $G$ be groups. Then $G=G$."
        , "Let $G,H$ be a group. Then $G=G$."
        , "Let $G$ be a group that are equal to $A$. Then $G=G$."
        , "Let $G,H$ be groups that is equal to $A$. Then $G=G$."
        ]
  where
    parseWith = either assertFailure pure . parseClaimWith structureLexicon

    assertRichStructurePhrase label expected = \case
        Raw.Claim
            [ Raw.AsmLetStruct _variables
                (Raw.StructNounPhrase _left _core
                    [Raw.AttrRThat (Raw.VPAdj adjectives)]
                    (Just _residual))
            ]
            _conclusion ->
                assertEqual (label <> " adjective count")
                    expected (length adjectives)
        claim ->
            assertFailure
                ("unexpected " <> label <> " structure phrase: "
                    <> show claim)

    groupPhrase =
        Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl
                ((Just "group", Just "groups") :| []))
            "group"

    leftModulePhrase =
        Raw.mkLexicalItemSgPl
            (Raw.lexicalPhraseSgPl
                ( (Just "left", Just "left") :|
                    [ (Just "module", Just "modules")
                    , (Just "over", Just "over")
                    , (Nothing, Nothing)
                    ]
                ))
            "left_module"

    structureLexicon =
        builtins
            { lexiconStructNouns =
                [groupPhrase, leftModulePhrase]
                    <> lexiconStructNouns builtins
            }

symbolicRelationLetSyntax :: Assertion
symbolicRelationLetSyntax = do
    grouped <- parseWith
        "Let $A,B\\precedes C$. Then $A\\precedes C$."
    case grouped of
        Raw.Claim
            [ Raw.AsmLetRelation
                (Raw.NamedVar "A" :| [Raw.NamedVar "B"])
                (Raw.Relation _ symbol [])
                (Raw.ExprVar (Raw.NamedVar "C"))
            ]
            _conclusion ->
                assertEqual "grouped relation symbol" precedes symbol
        claim ->
            assertFailure
                ("unexpected grouped relation Let: " <> show claim)

    parameterized <- parseWith
        "Let $x\\indexed{P}y$. Then $x\\indexed{P}y$."
    case parameterized of
        Raw.Claim
            [ Raw.AsmLetRelation _variables
                (Raw.Relation _ symbol
                    [Raw.ExprVar (Raw.NamedVar "P")])
                (Raw.ExprVar (Raw.NamedVar "y"))
            ]
            _conclusion ->
                assertEqual "parameterized relation symbol" indexed symbol
        claim ->
            assertFailure
                ("unexpected parameterized relation Let: " <> show claim)

    Raw.Claim [Raw.AsmLetIn{}] _ <- parseWith
        "Let $x\\in X$. Then $x\\in X$."
    Raw.Claim [Raw.AsmLetIn{}] _ <- parseWith
        "Let $x:X$. Then $x\\in X$."
    Raw.Claim [Raw.AsmLetEq{}] _ <- parseWith
        "Let $x=y$. Then $x=y$."
    Raw.Claim
        [Raw.AsmLetRelation _ (Raw.Relation _ Raw.EqSymbol []) _] _ <-
            parseWith "Let $x,y=z$. Then $x=x$."

    residual <- parseWith
        "Let $A$ be a set such that $A=A$ and $A\\precedes B$. Then $A=A$."
    case residual of
        Raw.Claim
            [ Raw.AsmLetNoun _variables
                (Raw.NounPhrase _left _noun _named _right
                    (Just (Raw.StmtConnected Raw.Conjunction _ _ _)))
            ]
            _conclusion -> pure ()
        claim -> assertFailure
            ("a noun residual was split into a relation Let: " <> show claim)

    traverse_
        (\source ->
            assertBool
                ("unsupported relation Let parsed: " <> Text.unpack source)
                (isLeft (parseClaimWith relationLexicon source)))
        [ "Let $x\\not\\precedes y$. Then $x=x$."
        , "Let $x\\mathrel{R}y$. Then $x=x$."
        , "Let $x\\precedes y\\precedes z$. Then $x=x$."
        ]
  where
    precedes = Raw.RelationSymbol
        (Raw.Command "precedes") (Raw.ParameterArity 0) "precedes"
    indexed = Raw.RelationSymbol
        (Raw.Command "indexed") (Raw.ParameterArity 1) "indexed"
    relationLexicon =
        builtins
            { lexiconRelationSymbols =
                [precedes, indexed] <> lexiconRelationSymbols builtins
            }
    parseWith = either assertFailure pure . parseClaimWith relationLexicon

nounRightAttributeNumberSyntax :: Assertion
nounRightAttributeNumberSyntax = do
    singular <- parseClaim
        "Let $X$ be a set that is equal to $A$. Then $X=X$."
    assertAttributeCount "singular" 1 singular

    plural <- parseClaim
        "Let $X,Y$ be sets that are equal to $A$ and equal to $A$. Then $X=X$."
    assertAttributeCount "coordinated plural" 2 plural

    negative <- parseClaim
        "Let $X,Y$ be sets that are not equal to $A$. Then $X=X$."
    case negative of
        Raw.Claim
            [Raw.AsmLetNoun _variables
                (Raw.NounPhrase _left _noun _named
                    [Raw.AttrRThat Raw.VPAdjNot{}] _residual)]
            _conclusion -> pure ()
        claim ->
            assertFailure
                ("unexpected negative plural attribute: " <> show claim)

    traverse_
        (\source ->
            assertBool
                ("noun attribute number disagreement parsed: "
                    <> Text.unpack source)
                (isLeft (parseClaimWith builtins source)))
        [ "Let $X$ be a set that are equal to $A$. Then $X=X$."
        , "Let $X,Y$ be sets that is equal to $A$. Then $X=X$."
        ]
  where
    assertAttributeCount label expected = \case
        Raw.Claim
            [Raw.AsmLetNoun _variables
                (Raw.NounPhrase _left _noun _named
                    [Raw.AttrRThat (Raw.VPAdj adjectives)] _residual)]
            _conclusion ->
                assertEqual (label <> " adjective count")
                    expected (length adjectives)
        claim ->
            assertFailure
                ("unexpected " <> label <> " attribute: " <> show claim)

structuralPredicateAgreementSyntax :: Assertion
structuralPredicateAgreementSyntax = do
    singular <- parseWith "Then $X$ has a clopen basis."
    assertVerbSubjects "singular article-bearing verb" 1 singular
    plural <- parseWith "Then $X$, $Y$ have a clopen basis."
    assertVerbSubjects "plural article-bearing verb" 2 plural
    grouped <- parseWith "Then $X$ and $Y$ have a clopen basis."
    assertVerbSubjects "and-grouped verb" 2 grouped

    traverse_ parseWith
        [ "Then $X$ does not have a clopen basis."
        , "Then $X$, $Y$ do not have a clopen basis."
        , "Then $X$ lies over $Y$."
        , "Then $X$, $Y$ lie over $Z$."
        , "Then $X$ is a set."
        , "Then $X$, $Y$ are sets."
        , "Then $X$ is not a set."
        , "Then $X$, $Y$ are not sets."
        , "Then $X$ is equal to $A$."
        , "Then $X$, $Y$ are equal to $A$."
        , "Then $X$ is not equal to $A$."
        , "Then $X$, $Y$ are not equal to $A$."
        , "Then $X$ equals $Y$."
        , "Then $X$, $Y$ equal $Z$."
        , "Then $X$ does not equal $Y$."
        , "Then $X$, $Y$ do not equal $Z$."
        , "Then $X$ has a clopen basis and $Y$ has a clopen basis."
        , "Let $X$ be a set that has a clopen basis. Then $X=X$."
        , "Let $X,Y$ be sets that have a clopen basis. Then $X=X$."
        ]

    traverse_
        (\source ->
            assertBool
                ("malformed agreement parsed: " <> Text.unpack source)
                (isLeft (parseClaimWith predicateLexicon source)))
        [ "Then $X$ have a clopen basis."
        , "Then $X$, $Y$ has a clopen basis."
        , "Then $X$ do not have a clopen basis."
        , "Then $X$, $Y$ does not have a clopen basis."
        , "Then $X$ are sets."
        , "Then $X$ are not sets."
        , "Then $X$ are equal to $A$."
        , "Then $X$ are not equal to $A$."
        , "Then $X$, $Y$ is equal to $A$."
        , "Then $X$, $Y$ is not equal to $A$."
        ]
  where
    parseWith = either assertFailure pure . parseClaimWith predicateLexicon

    assertVerbSubjects label expected = \case
        Raw.Claim [] (Raw.StmtVerbPhrase subjects _phrase) ->
            assertEqual label expected (length subjects)
        claim ->
            assertFailure ("unexpected " <> label <> " claim: " <> show claim)

    predicateLexicon =
        builtins
            { lexiconVerbs =
                [ verbItem
                    "has_clopen_basis"
                    [ Just (Raw.Word "has")
                    , Just (Raw.Word "a")
                    , Just (Raw.Word "clopen")
                    , Just (Raw.Word "basis")
                    ]
                    [ Just (Raw.Word "have")
                    , Just (Raw.Word "a")
                    , Just (Raw.Word "clopen")
                    , Just (Raw.Word "basis")
                    ]
                , verbItem
                    "lies_over"
                    [Just (Raw.Word "lies"), Just (Raw.Word "over"), Nothing]
                    [Just (Raw.Word "lie"), Just (Raw.Word "over"), Nothing]
                ] <> lexiconVerbs builtins
            }

    verbItem marker singular base =
        Raw.VerbLexicalItem
            (case Raw.checkVerbSurfaces singular base of
                Right surfaces -> surfaces
                Left failure ->
                    impossible
                        ("invalid agreement-test verb: " <> show failure))
            marker

algebraVocabularySyntax :: Assertion
algebraVocabularySyntax = do
    singularDivide <- parseWith
        "Then $m$ divides $n$ as natural numbers."
    assertVerb "singular divides" 1 "natural_divisibility" singularDivide
    pluralDivide <- parseWith
        "Then $m$, $n$ divide $p$ as natural numbers."
    assertVerb "plural divide" 2 "natural_divisibility" pluralDivide
    singularSpan <- parseWith
        "Then $v$ spans $M$ over $R$ indexed by $I$."
    assertVerb "singular spans" 1 "indexed_module_spanning" singularSpan
    pluralSpan <- parseWith
        "Then $v$, $w$ span $M$ over $R$ indexed by $I$."
    assertVerb "plural span" 2 "indexed_module_spanning" pluralSpan
    singularForm <- parseWith
        "Then $v$ forms a basis of $M$ over $R$ indexed by $I$."
    assertVerb "singular forms" 1 "indexed_module_basis" singularForm
    pluralForm <- parseWith
        "Then $v$, $w$ form a basis of $M$ over $R$ indexed by $I$."
    assertVerb "plural form" 2 "indexed_module_basis" pluralForm

    traverse_ parseWith
        [ "Then $f$ is a magma homomorphism from $A$ to $B$."
        , "Then $f$ is a magma embedding from $A$ to $B$."
        , "Then $f$ is a magma surjection from $A$ to $B$."
        , "Then $f$ is a magma isomorphism from $A$ to $B$."
        , "Then $f$ is a monoid homomorphism from $M$ to $N$."
        , "Then $f$ is a monoid embedding from $M$ to $N$."
        , "Then $f$ is a monoid surjection from $M$ to $N$."
        , "Then $f$ is a monoid isomorphism from $M$ to $N$."
        , "Then $u$ is a unit of $M$."
        , "Then $C$ is a closure system on $X$."
        , "Then $m$ is coprime to $n$ as natural numbers."
        , "Then $p$ is a prime natural number."
        , "Then $f$ is a ring homomorphism from $R$ to $S$."
        , "Then $f$ is a ring embedding from $R$ to $S$."
        , "Then $f$ is a ring surjection from $R$ to $S$."
        , "Then $f$ is a ring isomorphism from $R$ to $S$."
        , "Then $A$ is a subring of $R$."
        , "Then $f$ is a module embedding from $M$ to $N$ over $R$."
        , "Then $f$ is a module surjection from $M$ to $N$ over $R$."
        , "Then $f$ is a module isomorphism from $M$ to $N$ over $R$."
        , "Then $M$ is a right module over $R$."
        , "Then $I$ is a left ideal of $R$."
        , "Then $I$ is a right ideal of $R$."
        , "Then $I$ is a two-sided ideal of $R$."
        , "Then $I$ is an ideal of $R$."
        , "Then $v$ is linearly independent in $M$ over $R$ indexed by $I$."
        , "Then $m$ does not divide $n$ as natural numbers."
        , "Then $v$ does not span $M$ over $R$ indexed by $I$."
        , "Then $v$ does not form a basis of $M$ over $R$ indexed by $I$."
        , "Let $m$ be a set that divides $n$ as natural numbers. Then $m=m$."
        , "Let $v$ be a set that spans $M$ over $R$ indexed by $I$. Then $v=v$."
        , "Let $v$ be a set that forms a basis of $M$ over $R$ indexed by $I$. Then $v=v$."
        ]

    traverse_
        (\source ->
            assertBool
                ("dangerous shortened algebra phrase parsed: "
                    <> Text.unpack source)
                (isLeft (parseClaimWith algebraLexicon source)))
        [ "Then $u$ is a unit."
        , "Then $v$ is a basis."
        , "Then $v$ is a basiss."
        , "Then $f$ is a homomorphism."
        , "Then $f$ is a homomorphism from $A$ to $B$."
        , "Then $m$ divide $n$ as natural numbers."
        , "Then $v$, $w$ spans $M$ over $R$ indexed by $I$."
        , "Then $v$ form a basis of $M$ over $R$ indexed by $I$."
        ]
  where
    parseWith = either assertFailure pure . parseClaimWith algebraLexicon

    assertVerb label expectedSubjects expectedMarker = \case
        Raw.Claim []
            (Raw.StmtVerbPhrase subjects
                (Raw.VPVerb (Raw.Verb _ item _arguments))) -> do
                    assertEqual (label <> " subject count")
                        expectedSubjects (length subjects)
                    assertEqual (label <> " selected owner")
                        expectedMarker (Raw.verbLexicalMarker item)
        claim ->
            assertFailure ("unexpected " <> label <> " claim: " <> show claim)

    algebraLexicon =
        builtins
            { lexiconVerbs = algebraVerbs <> lexiconVerbs builtins
            , lexiconNouns = algebraNouns <> lexiconNouns builtins
            , lexiconAdjRs = algebraAdjectives <> lexiconAdjRs builtins
            }

    algebraVerbs =
        [ verbItem
            "natural_divisibility"
            [ Just (Raw.Word "divides")
            , Nothing
            , Just (Raw.Word "as")
            , Just (Raw.Word "natural")
            , Just (Raw.Word "numbers")
            ]
            [ Just (Raw.Word "divide")
            , Nothing
            , Just (Raw.Word "as")
            , Just (Raw.Word "natural")
            , Just (Raw.Word "numbers")
            ]
        , verbItem
            "indexed_module_spanning"
            [ Just (Raw.Word "spans")
            , Nothing
            , Just (Raw.Word "over")
            , Nothing
            , Just (Raw.Word "indexed")
            , Just (Raw.Word "by")
            , Nothing
            ]
            [ Just (Raw.Word "span")
            , Nothing
            , Just (Raw.Word "over")
            , Nothing
            , Just (Raw.Word "indexed")
            , Just (Raw.Word "by")
            , Nothing
            ]
        , verbItem
            "indexed_module_basis"
            [ Just (Raw.Word "forms")
            , Just (Raw.Word "a")
            , Just (Raw.Word "basis")
            , Just (Raw.Word "of")
            , Nothing
            , Just (Raw.Word "over")
            , Nothing
            , Just (Raw.Word "indexed")
            , Just (Raw.Word "by")
            , Nothing
            ]
            [ Just (Raw.Word "form")
            , Just (Raw.Word "a")
            , Just (Raw.Word "basis")
            , Just (Raw.Word "of")
            , Nothing
            , Just (Raw.Word "over")
            , Nothing
            , Just (Raw.Word "indexed")
            , Just (Raw.Word "by")
            , Nothing
            ]
        ]

    verbItem marker singular base =
        Raw.VerbLexicalItem
            (case Raw.checkVerbSurfaces singular base of
                Right surfaces -> surfaces
                Left failure ->
                    impossible
                        ("invalid algebra-test verb: " <> show failure))
            marker

    algebraNouns =
        [ noun "magma_hom" "magma homomorphism from ? to ?"
            "magma homomorphisms from ? to ?"
        , noun "magma_embedding" "magma embedding from ? to ?"
            "magma embeddings from ? to ?"
        , noun "magma_surjection" "magma surjection from ? to ?"
            "magma surjections from ? to ?"
        , noun "magma_isomorphism" "magma isomorphism from ? to ?"
            "magma isomorphisms from ? to ?"
        , noun "monoid_hom" "monoid homomorphism from ? to ?"
            "monoid homomorphisms from ? to ?"
        , noun "monoid_embedding" "monoid embedding from ? to ?"
            "monoid embeddings from ? to ?"
        , noun "monoid_surjection" "monoid surjection from ? to ?"
            "monoid surjections from ? to ?"
        , noun "monoid_isomorphism" "monoid isomorphism from ? to ?"
            "monoid isomorphisms from ? to ?"
        , noun "monoid_unit" "unit of ?" "units of ?"
        , noun "closure_system" "closure system on ?" "closure systems on ?"
        , noun "prime_natural" "prime natural number" "prime natural numbers"
        , noun "ring_hom" "ring homomorphism from ? to ?"
            "ring homomorphisms from ? to ?"
        , noun "ring_embedding" "ring embedding from ? to ?"
            "ring embeddings from ? to ?"
        , noun "ring_surjection" "ring surjection from ? to ?"
            "ring surjections from ? to ?"
        , noun "ring_isomorphism" "ring isomorphism from ? to ?"
            "ring isomorphisms from ? to ?"
        , noun "subring" "subring of ?" "subrings of ?"
        , noun "module_embedding" "module embedding from ? to ? over ?"
            "module embeddings from ? to ? over ?"
        , noun "module_surjection" "module surjection from ? to ? over ?"
            "module surjections from ? to ? over ?"
        , noun "module_isomorphism" "module isomorphism from ? to ? over ?"
            "module isomorphisms from ? to ? over ?"
        , noun "right_module" "right module over ?" "right modules over ?"
        , noun "left_ideal" "left ideal of ?" "left ideals of ?"
        , noun "right_ideal" "right ideal of ?" "right ideals of ?"
        , noun "two_sided_ideal" "two-sided ideal of ?"
            "two-sided ideals of ?"
        , noun "ideal" "ideal of ?" "ideals of ?"
        ]

    noun marker singular plural =
        Raw.mkLexicalItemSgPl
            (case Raw.SgPl
                    <$> Raw.readLexicalPhrase singular
                    <*> Raw.readLexicalPhrase plural of
                Right phrase -> phrase
                Left failure ->
                    impossible
                        ("invalid algebra-test noun: " <> show failure))
            marker

    algebraAdjectives =
        [ adjective
            ( Just "coprime" :|
                [ Just "to"
                , Nothing
                , Just "as"
                , Just "natural"
                , Just "numbers"
                ])
        , adjective
            ( Just "linearly" :|
                [ Just "independent"
                , Just "in"
                , Nothing
                , Just "over"
                , Nothing
                , Just "indexed"
                , Just "by"
                , Nothing
                ])
        ]

    adjective components =
        Raw.userAdjectiveLexicalItem
            Raw.RightAdjectiveSide
            (Raw.patternFromHoley (Raw.lexicalPhrase components))

parseProof :: Text -> IO Raw.Proof
parseProof conclusion = do
    let sourceText =
            Text.unlines
                [ "\\begin{proof}"
                , conclusion
                , "\\end{proof}"
                ]
    tokens <- case scanTestSource
        anonymousSourceDescriptor
        "proof-alias.tex"
        sourceText of
        Left err ->
            assertFailure err >> fail "unreachable"
        Right (_imports, [tokens']) ->
            pure tokens'
        Right (_imports, chunks) ->
            assertFailure
                ("expected one proof chunk, got " <> show (length chunks))
                >> fail "unreachable"
    case successfulParses
            (fullParses (parser (grammar builtins)) tokens) of
        ([Raw.BlockProof _start proof _end], _report) ->
            pure proof
        (blocks, report) ->
            assertFailure
                ( "expected one proof, got "
                    <> show blocks
                    <> " with "
                    <> show report
                )
                >> fail "unreachable"

parseClaim :: Text -> IO Raw.Claim
parseClaim content =
    either assertFailure pure (parseClaimWith builtins content)

parseClaimWith :: Lexicon -> Text -> Either String Raw.Claim
parseClaimWith sourceLexicon content = do
    let sourceText =
            Text.unlines
                ( [ "\\begin{proposition}\\label{claim_introductions}" ]
                    <> Text.lines content
                    <> ["\\end{proposition}"]
                )
    tokens <- case scanTestSource
        anonymousSourceDescriptor
        "claim-introductions.tex"
        sourceText of
        Left err ->
            Left err
        Right (_imports, [tokens']) ->
            Right tokens'
        Right (_imports, chunks) ->
            Left
                ("expected one claim chunk, got " <> show (length chunks))
    case successfulParses
            (fullParses (parser (grammar sourceLexicon)) tokens) of
        ( [Raw.BlockClaim _kind _location _title _marker claim], _report) ->
            Right claim
        (blocks, report) ->
            Left
                ( "expected one claim, got "
                    <> show blocks
                    <> " with "
                    <> show report
                )

classificationClaimKind :: Assertion
classificationClaimKind = do
    let sourceText = Text.unlines
            [ "\\begin{classification}\\label{notion_view}"
            , "Suppose $x=x$."
            , "Then $x=x$."
            , "\\end{classification}"
            ]
    tokens <- case scanTestSource anonymousSourceDescriptor "notion-view.tex" sourceText of
        Left err ->
            assertFailure err >> fail "unreachable"
        Right (_imports, [tokens']) -> pure tokens'
        Right (_imports, chunks) ->
            assertFailure
                ("expected one notion-view chunk, got " <> show (length chunks))
                >> fail "unreachable"
    case successfulParses
            (fullParses (parser (grammar builtins)) tokens) of
        ( [ Raw.BlockClaim kind _location _title _marker
                (Raw.Claim _assumptions _statement) ]
          , _report
          ) -> assertEqual "classification kind" Raw.Classification kind
        (blocks, report) ->
            assertFailure
                ( "expected one classification, got "
                    <> show blocks
                    <> " with "
                    <> show report
                )

assertProofRejected :: Text -> Assertion
assertProofRejected conclusion = do
    let sourceText =
            Text.unlines
                [ "\\begin{proof}"
                , conclusion
                , "\\end{proof}"
                ]
    case scanTestSource anonymousSourceDescriptor "rejected-proof.tex" sourceText of
        Left _err -> pure ()
        Right (_imports, [tokens]) ->
            case successfulParses
                    (fullParses (parser (grammar builtins)) tokens) of
                ([], _report) -> pure ()
                (blocks, report) ->
                    assertFailure
                        ( "unsupported inner that parsed as "
                            <> show blocks
                            <> " with "
                            <> show report
                        )
        Right (_imports, chunks) ->
            assertFailure
                ("expected one rejected proof chunk, got " <> show (length chunks))

boundedNounSyntax :: Assertion
boundedNounSyntax = do
    for_ [ "For every element $x\\in F$ of $A$ we have $x=x$"
         , "For all elements $x,y\\in F$ of $A$ we have $x=y$"
         , "There exists an element $x\\notin F$ of $A$"
         , "There exist elements $x,y\\in F$ of $A$ such that $x=y$"
         , "There exists no element $x\\in F$ of $A$"
         , "Every element $x\\in F$ of $A$ is equal to $x$"
         , "$z$ is equal to some element $x\\in F$ of $A$"
         , "$z$ is equal to no element $x\\in F$ of $A$"
         , "For every set $x\\neq y$ we have $x=x$"
         ] \source -> either assertFailure (const (pure ())) (parseStatement source)
    statement <- either assertFailure pure
        (parseStatement "For all elements $x,y\\in F$ of $A$ we have $x=y$")
    case statement of
        Raw.StmtQuantPhrase _ (Raw.QuantPhrase Raw.Universally
                (Raw.NounPhrase _ (Raw.Noun _ _ [Raw.TermExpr (Raw.ExprVar a)])
                    (Raw.NounBinder names (Raw.Bounded location Raw.Positive
                        (Raw.Relation _ Raw.ElementSymbol []) (Raw.ExprVar f))) _ _)) _ -> do
            assertEqual "names stay in written order" ["x", "y"] names
            assertEqual "trailing noun parameter" "A" a
            assertEqual "shared endpoint" "F" f
            assertBool "bound retains its source location" (location /= Nowhere)
            assertBool "names retain their source locations" (all ((/= Nowhere) . locate) names)
        other -> assertFailure ("lost bounded noun shape: " <> show other)
    _ <- parseProof "Take an element $x\\in F$ of $A$ such that $x=x$. Follows."
    for_ [ "For every element $\\in F$ of $A$ we have $A=A$"
         , "For every element $g(x)\\in F$ of $A$ we have $A=A$"
         , "For all elements $x\\in F,y\\in G$ of $A$ we have $A=A$"
         , "For all elements $x$ and $y\\in F$ of $A$ we have $A=A$"
         , "For every element $x$ of $A\\in F$ we have $A=A$"
         , "$z$ is an element $x\\in F$ of $A$"
         , "Let $x\\in F$ be an element of $A$. Then $x=x$"
         , "Let $x$ be an element $y\\in F$ of $A$. Then $x=x$"
         , "For every record $X\\in F$ we have $X=X$"
         ] \source -> assertBool (Text.unpack source <> " must be rejected")
            (isLeft (parseClaimWith builtins (source <> ".")))
