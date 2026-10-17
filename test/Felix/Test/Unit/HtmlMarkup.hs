module Felix.Test.Unit.HtmlMarkup (unitTests) where

import Base
import Data.Either (isLeft)
import Data.Text qualified as Text
import Felix.Syntax.Phrase qualified as Phrase
import Felix.Syntax.Interface qualified as Syntax
import Felix.Render.Html.Markup
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Lexicon (Lexicon(..), builtins)
import Felix.Syntax.Token (Token(..))
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "HTML markup"
    [ testCase "layout owns conventional native overlaps" layoutOverlaps
    , testCase "scripts preserve lexical attachment and explicit grouping" scriptAttachment
    , testCase "closed layout covers textbook notation" textbookNotation
    , testCase "rejects incomplete and unsupported layout" malformedNotation
    , testCase "native leaves consume the complete application" nativeLeaves
    , testCase "native ambiguity remains decisive" nativeAmbiguity
    , testCase "envelopes respect escapes, commands, and segment boundaries" envelopes
    ]

parse :: Text -> Either MarkupMathFailure CommentaryMath
parse = parseCommentaryMath (prepareMarkupParser builtins)

identifier :: Text -> CommentaryMath
identifier = MathIdentifier

layoutOverlaps :: Assertion
layoutOverlaps = do
    parse "aH" @?= Right (MathRow (identifier "a" :| [identifier "H"]))
    parse "g(u,y)" @?= Right (MathRow
        (identifier "g" :| [MathFenced RoundFence
            (MathRow (identifier "u" :| [MathOperator SeparatorOperator ",", identifier "y"]))]))
    parse "x=y" @?= Right (MathRow
        (identifier "x" :| [MathOperator InfixOperator "=", identifier "y"]))
    case parse "x\\rless y" of
        Right NativeMath{} -> pure ()
        value -> assertFailure ("native-only relation lost its interpretation: " <> show value)

scriptAttachment :: Assertion
scriptAttachment = do
    parse "x^12" @?= Right (MathRow
        (MathScript (identifier "x") (Superscript (MathNumber "1")) :| [MathNumber "2"]))
    parse "x^{12}" @?= Right (MathScript (identifier "x") (Superscript (MathNumber "12")))
    let combined = MathScript (identifier "x")
            (SubSuperscript (identifier "i") (MathNumber "2"))
    parse "x_i^2" @?= Right combined
    parse "x^2_i" @?= Right combined
    parse "x^y_z" @?= Right (MathScript (identifier "x")
        (SubSuperscript (identifier "z") (identifier "y")))
    parse "x^{y_z}" @?= Right (MathScript (identifier "x")
        (Superscript (MathScript (identifier "y") (Subscript (identifier "z")))))
    parse "1_R" @?= Right (MathScript (MathNumber "1") (Subscript (identifier "R")))
    for_ ["(fg)^2", "{fg}^2"] \source -> case parse source of
        Right (MathScript base (Superscript (MathNumber "2"))) ->
            case base of
                MathRow{} -> pure ()
                MathFenced{} -> pure ()
                _ -> assertFailure "script did not keep its grouped base"
        value -> assertFailure ("unexpected grouped script: " <> show value)

textbookNotation :: Assertion
textbookNotation =
    for_
        [ "n\\cdot 1_R", "x\\mapsto axa^{-1}", "(\\varphi\\psi)(x)=\\varphi(\\psi(x))"
        , "[x,y]=x^{-1}y^{-1}xy", "(fg)(x)=f(g(x))", "-x+y", "R/I"
        , "(f\\circ g)(x)=f(g(x))", "2^n", "2^{-n-1}", "\\ON\\times A"
        , "\\operatorname{cons}", "\\operatorname{\\textsf{cons}}", "({-},{-})"
        , "A\\longrightarrow B\\longrightarrow C", "\\{x,y\\}", "-1"
        ] \source -> case parse source of
            Right _ -> pure ()
            Left failure -> assertFailure (Text.unpack source <> ": " <> show failure)

malformedNotation :: Assertion
malformedNotation =
    for_
        [ "", "g()", "x+", "A\\longrightarrow", "x^", "x^-1", "x_i_j", "x^i^j"
        , "x^{-}", "({-},)", "(x]", "\\operatorname{}", "\\operatorname{a b}"
        , "\\operatorname{\\textsf{}}", "\\unknown{X}{Y}", "\\pow{A}+"
        ] \source -> assertBool ("accepted " <> Text.unpack source) (isLeft (parse source))

nativeLeaves :: Assertion
nativeLeaves = do
    for_ ["x\\mapsto\\pow{A}", "x\\mapsto\\carrier[Y]",
            "A\\times\\pow{A\\times B}\\longrightarrow B"] \source ->
        case parse source of
            Right _ -> pure ()
            value -> assertFailure ("native leaf failed: " <> show value)
    for_ ["\\pow{A}{B}", "x\\mapsto\\pow{A^{-1}}", "\\sibling{A}"] \source ->
        assertBool ("accepted incomplete native invocation " <> Text.unpack source)
            (isLeft (parse source))
    case parse "\\exp{2}{\\neg{n}}" of
        Right NativeMath{} -> pure ()
        value -> assertFailure ("explicit native commands lost native rendering: " <> show value)

nativeAmbiguity :: Assertion
nativeAmbiguity = do
    let ambiguous = builtins { lexiconTypedConstants =
            [(Command "Set", Raw.ConcreteSet), (Command "Set", Raw.ConcreteProp)] }
    parseCommentaryMath (prepareMarkupParser ambiguous) "\\Set"
        @?= Left (MarkupNativeAmbiguity 2)
    let phrase marker = Raw.intrinsicAdjectiveLexicalItem Raw.LeftAdjectiveSide
            (Raw.TokenCons (Command "scoped") Raw.End) marker
        scoped markers = prepareMarkupParser builtins { lexiconAdjLs = phrase <$> markers }
    case parseCommentaryMath (scoped ["different-marker"]) "\\scoped" of
        Right (MathPhrase (ScopedPhrase binding "scoped")) ->
            Phrase.nativePhraseEntry binding @?= Syntax.CanonicalIntrinsicAdjective Raw.LeftAdjectiveSide
                (Raw.TokenCons (Command "scoped") Raw.End) "different-marker"
        value -> assertFailure ("native phrase lost its complete binding: " <> show value)
    parseCommentaryMath (scoped ["same", "same"]) "\\scoped"
        @?= parseCommentaryMath (scoped ["same"]) "\\scoped"
    let userPattern = Raw.TokenCons (Command "scoped") Raw.End
        userParser = prepareMarkupParser builtins
            { lexiconAdjLs = [Raw.userAdjectiveLexicalItem Raw.LeftAdjectiveSide userPattern] }
    case parseCommentaryMath userParser "\\scoped" of
        Right (MathPhrase (ScopedPhrase binding "scoped")) -> do
            Phrase.nativePhraseEntry binding @?= Syntax.CanonicalUserAdjective Raw.LeftAdjectiveSide
                (Raw.AdjectiveSurfaceKey userPattern)
            Phrase.nativePhraseMarker binding @?= Nothing
        value -> assertFailure ("user phrase was treated as unbound display syntax: " <> show value)
    let sharedMarker = prepareMarkupParser builtins
            { lexiconAdjLs = [phrase "same"]
            , lexiconAdjRs = [Raw.intrinsicAdjectiveLexicalItem Raw.RightAdjectiveSide
                (Raw.TokenCons (Command "scoped") Raw.End) "same"] }
    assertPhraseAmbiguity (parseCommentaryMath sharedMarker "\\scoped")
    for_ ["\\scoped", "x+\\scoped"] \source ->
        assertPhraseAmbiguity (parseCommentaryMath (scoped ["first", "second"]) source)
    case Concrete.parseNativeMath (Concrete.prepareNativeMathParser builtins) "-1" of
        Left Concrete.NativeMathRejected{} -> pure ()
        value -> assertFailure ("layout acceptance leaked into native syntax: " <> show value)

assertPhraseAmbiguity :: Either MarkupMathFailure CommentaryMath -> Assertion
assertPhraseAmbiguity = \case
    Left (MarkupPhraseAmbiguity bindings) -> length bindings @?= 2
    value -> assertFailure ("expected distinct native phrase bindings: " <> show value)

envelopes :: Assertion
envelopes = do
    takeMathEnvelope "$x\\$y$ tail" @?=
        Just (MathEnvelope InlineEnvelope "$x\\$y$" (Just "x\\$y"), " tail")
    takeMathEnvelope "\\\\[x\\]" @?= Nothing
    takeMathEnvelope "$$x$$rest" @?=
        Just (MathEnvelope UnsupportedDollarEnvelope "$$x$$" (Just "x"), "rest")
    takeMathEnvelope "\\[x" @?= Just (MathEnvelope DisplayEnvelope "\\[x" Nothing, "")
    splitDisplayEnvelopes "a\\emph{\\[x\\]}b\\[x\n\n+y\\]c" @?=
        [ NarrativeProse "a\\emph{\\[x\\]}b"
        , NarrativeDisplay (MathEnvelope DisplayEnvelope "\\[x\n\n+y\\]" (Just "x\n\n+y"))
        , NarrativeProse "c"
        ]
    stripDisplayPunctuation "x+y. " @?= Just ("x+y", ".")
    stripDisplayPunctuation "(x." @?= Nothing
