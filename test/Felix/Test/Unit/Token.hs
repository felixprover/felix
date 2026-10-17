{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.Token (unitTests) where

import Base
import Felix.Cache.Codec qualified as Cache
import Felix.Report.Location
import Felix.Source.Scan qualified as SourceScan
import Felix.Syntax.Adapt
import Felix.Syntax.Abstract
    ( Associativity(..)
    , Marker(..)
    , tokenMarker
    )
import Felix.Syntax.Interface
import Felix.Syntax.Pragma
import Felix.Syntax.Token
import Felix.Test.SourceScan.Adapter
    ( scanTestImports
    , scanTestPresentation
    , scanTestSource
    , scanTestVerification
    )

import Data.List qualified as List
import Data.Text qualified as Text
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Lexer"
    [ testCase "nested math inside text returns to text" nestedMathInsideText
    , testCase "nested text and math returns to the enclosing frame" deeperAlternation
    , testCase "braces inside text do not close the text frame" textBraceNesting
    , testCase "rejects malformed formal boundaries"
        rejectsMalformedFormalBoundaries
    , testCase "delimiter prefixes do not capture longer commands"
        delimiterPrefixesDoNotCaptureCommands
    , testCase "operator subscripts remain ordinary symbolic tokens"
        operatorSubscriptsAreSymbolic
    , testCase "formal-space escapes are exact and raw tabs remain invalid"
        formalSpaceEscapesAreExact
    , testCase "cases is tokenized as an environment only inside math" casesOnlyInsideMath
    , testCase "preserves arbitrary-precision decimal literals"
        arbitraryPrecisionDecimalLiterals
    , testCase "keeps opaque-integer sign and magnitude separate"
        opaqueIntegerSignTokenization
    , testCase "round-trips arbitrary-precision integer tokens"
        arbitraryPrecisionIntegerTokenCache
    , testCase "classifies marker-bearing tokens totally"
        classifiesMarkerBearingTokens
    , testCase "datatype item headings retain their spelling"
        namedDatatypeItems
    , testCase "imports retain source locations and POSIX spellings" locatedImports
    , testCase "heading command text does not affect imports"
        headingCommandTextDoesNotAffectImports
    , testCase "imports accept comments, whitespace, and adjacency"
        importsAcceptCommentsWhitespaceAndAdjacency
    , testCase "late imports are rejected by complete parsing"
        rejectsLateImports
    , testCase "header import paths use the shared grammar"
        rejectsMalformedHeaderImports
    , testCase "commented environment starts are ignored"
        ignoresCommentedEnvironmentStart
    , testCase "document segmentation shares formal boundaries with the lexer"
        segmentsDocumentStructure
    , testCase "incomplete headings remain document prose"
        incompleteHeadingsRemainProse
    , testCase "multibyte prose advances by Unicode scalar columns"
        multibyteProseUsesScalarColumns
    , testCase "presentation math accepts only complete variable lists"
        parsesPresentationVariables
    , testCase "presentation references reuse strict source markers"
        parsesPresentationReferences
    , testCase "scans complete presentation math fragments"
        scansPresentationMathFragments
    , testCase "empty inputs construct empty lexical syntax"
        constructsEmptyLexicalSyntax
    , testCase "extracts exact source fixity pragmas"
        extractsSourceFixityPragmas
    , testCase "literal advancement preserves physical-line pragma observation"
        literalAdvancementPreservesPragmaObservation
    , testCase "rejects malformed reserved pragma lines"
        rejectsMalformedPragmas
    ]

classifiesMarkerBearingTokens :: Assertion
classifiesMarkerBearingTokens = do
    for_ accepted \(token, marker) ->
        assertEqual (show token) (Just marker) (tokenMarker token)
    for_ rejected \token ->
        assertEqual (show token) Nothing (tokenMarker token)
  where
    accepted =
        [ (Word "word", Marker "word")
        , (Symbol "+", Marker "+")
        , (Command "command", Marker "command")
        , (CaseHeading "Falsity", Marker "caseOf")
        , (Integer (-12), Marker "-12")
        ]
    rejected =
        [ Variable "x"
        , NamedItem "Falsity"
        , CommandReference "auto" ("fact" :| [])
        , Label "label"
        , Ref ("reference" :| [])
        , BeginEnv "math"
        , EndEnv "math"
        , ParenL
        , ParenR
        , BracketL
        , BracketR
        , VisibleBraceL
        , VisibleBraceR
        , InvisibleBraceL
        , InvisibleBraceR
        ]

namedDatatypeItems :: Assertion
namedDatatypeItems = do
    let heading = NamedItem "  DNE_2 Case  "
        body = "\\begin{enumerate}\\item[  DNE_2 Case  ] $x$.\\item $y$.\\end{enumerate}"
    actual <- tokensInProof body
    assertBool "heading preserves display case, digits and spacing" (heading `elem` actual)
    assertEqual "unnamed item remains unchanged" 1 (length (List.filter (== Command "item") actual))
    assertEqual "heading token round trip" (Right heading)
        (Cache.decodeCache getTokenCache (Cache.encodeCache (putTokenCache heading)))
    case scanTestPresentation anonymousSourceDescriptor "named-items"
            ("\\begin{proof}" <> body <> "\\end{proof}") of
        Right [_] -> pure ()
        result -> assertFailure ("discard-token scan disagreed with named-item scanning: " <> show result)
    let caseToken = CaseHeading " DNE_2 Case "
    cases <- tokensInProof "\\caseOf{ DNE_2 Case .} Follows. \\caseOf{$x=x$.} Follows."
    assertBool "plain case headings preserve their written name" (caseToken `elem` cases)
    assertBool "mathematical cases retain the ordinary command" (Command "caseOf" `elem` cases)
    assertEqual "case heading token round trip" (Right caseToken)
        (Cache.decodeCache getTokenCache (Cache.encodeCache (putTokenCache caseToken)))

delimiterPrefixesDoNotCaptureCommands :: Assertion
delimiterPrefixesDoNotCaptureCommands = do
    mathTokens <- tokensInProof
        "$\\leftCoset\\rightCoset\\left(x\\right)\\left\\{x\\right\\}$"
    mathTokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , Command "leftCoset"
        , Command "rightCoset"
        , ParenL
        , Variable "x"
        , ParenR
        , VisibleBraceL
        , Variable "x"
        , VisibleBraceR
        , EndEnv "math"
        , EndEnv "proof"
        ]
    textTokens <- tokensInProof
        "$\\text{\\leftWord \\rightWord \\left(foo\\right)}$"
    textTokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , BeginEnv "text"
        , Command "leftWord"
        , Command "rightWord"
        , ParenL
        , Word "foo"
        , ParenR
        , EndEnv "text"
        , EndEnv "math"
        , EndEnv "proof"
        ]

nestedMathInsideText :: Assertion
nestedMathInsideText = do
    tokens <- tokensInProof "$\\text{if $x \\in A$ then}$"
    tokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , BeginEnv "text"
        , Word "if"
        , BeginEnv "math"
        , Variable "x"
        , Command "in"
        , Variable "A"
        , EndEnv "math"
        , Word "then"
        , EndEnv "text"
        , EndEnv "math"
        , EndEnv "proof"
        ]

deeperAlternation :: Assertion
deeperAlternation = do
    tokens <- tokensInProof "$\\text{a $ \\text{b $c$ d} e$ f}$"
    tokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , BeginEnv "text"
        , Word "a"
        , BeginEnv "math"
        , BeginEnv "text"
        , Word "b"
        , BeginEnv "math"
        , Variable "c"
        , EndEnv "math"
        , Word "d"
        , EndEnv "text"
        , Variable "e"
        , EndEnv "math"
        , Word "f"
        , EndEnv "text"
        , EndEnv "math"
        , EndEnv "proof"
        ]

textBraceNesting :: Assertion
textBraceNesting = do
    tokens <- tokensInProof "$\\text{a {b}}$"
    tokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , BeginEnv "text"
        , Word "a"
        , InvisibleBraceL
        , Word "b"
        , InvisibleBraceR
        , EndEnv "text"
        , EndEnv "math"
        , EndEnv "proof"
        ]

rejectsMalformedFormalBoundaries :: Assertion
rejectsMalformedFormalBoundaries =
    for_ cases
        \(description, source, expectedLine, expectedColumn, fragments) ->
            case SourceScan.scanCompleteVerificationText
                    anonymousSourceDescriptor
                    "formal-boundary.tex"
                    source of
                Left
                    (SourceScan.SourceInputFailure
                        (SourceScan.VerificationBodyFailure
                            (SourceScan.SourceScanExplicitFailure
                                location
                                message))) -> do
                    assertEqual
                        (description <> " line")
                        expectedLine
                        (locLine location)
                    assertEqual
                        (description <> " column")
                        expectedColumn
                        (locColumn location)
                    for_ fragments \fragment ->
                        assertBool
                            (description
                                <> " should contain "
                                <> show fragment
                                <> ", got "
                                <> show message)
                            (fragment `Text.isInfixOf` message)
                result ->
                    assertFailure
                        ("expected structured boundary rejection for "
                            <> description
                            <> ", got "
                            <> show result)
  where
    cases :: [(String, Text, Int, Int, [Text])]
    cases =
        [ ( "unclosed math at matching end"
          , Text.unlines
                [ "\\begin{definition}"
                , "  $x = y"
                , "\\end{definition}"
                ]
          , 3
          , 1
          , [ "inline math opened at 2:3 is not closed before \\end{definition}"
            , "expected '$'"
            ]
          )
        , ( "nested top-level begin"
          , Text.unlines
                [ "\\begin{theorem}"
                , "  A."
                , "\\begin{proof}"
                ]
          , 3
          , 1
          , [ "cannot begin top-level proof inside theorem"
            , "expected \\end{theorem} first"
            ]
          )
        , ( "mismatched top-level end"
          , Text.unlines
                [ "\\begin{theorem}"
                , "  A."
                , "\\end{proof}"
                ]
          , 3
          , 1
          , [ "unexpected \\end{proof} while scanning theorem"
            , "expected \\end{theorem}"
            ]
          )
        , ( "unclosed outer environment at EOF"
          , Text.unlines
                [ "\\begin{proof}"
                , "  Indeed."
                ]
          , 3
          , 1
          , [ "unexpected end of input while scanning proof"
            , "expected \\end{proof}"
            ]
          )
        , ( "unclosed inner frame at EOF"
          , Text.unlines
                [ "\\begin{definition}"
                , "  $x"
                ]
          , 3
          , 1
          , [ "inline math opened at 2:3 is not closed before end of input"
            , "expected '$'"
            , "outer definition is also not closed; expected \\end{definition}"
            ]
          )
        ]

operatorSubscriptsAreSymbolic :: Assertion
operatorSubscriptsAreSymbolic = do
    tokens <- tokensInProof "$x\\star_A y+_R z$"
    tokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , Variable "x"
        , Command "star"
        , Symbol "_"
        , Variable "A"
        , Variable "y"
        , Symbol "+_"
        , Variable "R"
        , Variable "z"
        , EndEnv "math"
        , EndEnv "proof"
        ]

formalSpaceEscapesAreExact :: Assertion
formalSpaceEscapesAreExact = do
    for_ ["\\ ", "\\\\", "\\!", "\\,", "\\:", "\\;"] \escape -> do
        located <- locatedTokensInProof ("$x" <> escape <> "y$")
        case List.find ((== Variable "x") . unLocated) located of
            Nothing ->
                assertFailure ("missing first variable for " <> show escape)
            Just variable ->
                assertEqual
                    ("formal-space escape " <> show escape)
                    Space
                    (postWhitespace variable)
    case scanTestSource anonymousSourceDescriptor "raw-tab" rawTabSource of
        Left _failure -> pure ()
        Right result ->
            assertFailure
                ("raw tab unexpectedly scanned as formal whitespace: "
                    <> show result)
  where
    rawTabSource = Text.unlines
        [ "\\begin{proof}"
        , "$x\ty$"
        , "\\end{proof}"
        ]

casesOnlyInsideMath :: Assertion
casesOnlyInsideMath = do
    tokensInsideMath <- tokensInProof "$\\begin{cases}x\\end{cases}$"
    tokensInsideMath `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , BeginEnv "cases"
        , Variable "x"
        , EndEnv "cases"
        , EndEnv "math"
        , EndEnv "proof"
        ]

    tokensOutsideMath <- tokensInProof "\\begin{cases}x\\end{cases}"
    assertBool
        "cases should not be tokenized as an environment outside math"
        (BeginEnv "cases" `notElem` tokensOutsideMath && EndEnv "cases" `notElem` tokensOutsideMath)

arbitraryPrecisionDecimalLiterals :: Assertion
arbitraryPrecisionDecimalLiterals = do
    for_ values \value -> do
        tokens <- tokensInProof
            ("$" <> Text.pack (show value) <> "$")
        assertEqual
            ("lexed literal " <> show value)
            [ BeginEnv "proof"
            , BeginEnv "math"
            , Integer value
            , EndEnv "math"
            , EndEnv "proof"
            ]
            tokens
  where
    values =
        [ 9223372036854775807
        , 9223372036854775808
        , 18446744073709551616
        , 12345678901234567890123456789012345678901234567890
        ] :: [Integer]

arbitraryPrecisionIntegerTokenCache :: Assertion
arbitraryPrecisionIntegerTokenCache = do
    let token = Integer 18446744073709551616
        encoded =
            Cache.encodeCache
                (putTokenCache token)
    assertEqual
        "arbitrary-precision token cache round trip"
        (Right token)
        (Cache.decodeCache getTokenCache encoded)

opaqueIntegerSignTokenization :: Assertion
opaqueIntegerSignTokenization = do
    tokens <- tokensInProof "$\\opaqueInteger{-1}$."
    tokens `shouldBe`
        [ BeginEnv "proof"
        , BeginEnv "math"
        , Command "opaqueInteger"
        , InvisibleBraceL
        , Symbol "-"
        , Integer 1
        , InvisibleBraceR
        , EndEnv "math"
        , Symbol "."
        , EndEnv "proof"
        ]

locatedImports :: Assertion
locatedImports = do
    let raw = Text.unlines
            [ "% heading"
            , "\\import{set/base.tex}"
            , "\\import{set\\special.tex}"
            , "\\begin{axiom}"
            , "  $x = x$."
            , "\\end{axiom}"
            ]
    case scanTestImports anonymousSourceDescriptor "import-unit" raw of
        Left err ->
            assertFailure err
        Right imports@[firstImport, secondImport] -> do
            assertEqual
                "import paths"
                ["set/base.tex", "set\\special.tex"]
                (unLocated <$> imports)
            assertEqual "first import line" 2 (locLine (startPos firstImport))
            assertEqual "second import line" 3 (locLine (startPos secondImport))
        Right imports ->
            assertFailure ("expected two imports, got " <> show imports)

headingCommandTextDoesNotAffectImports :: Assertion
headingCommandTextDoesNotAffectImports = do
    let raw = Text.unlines
            [ "\\section{Literal \\import{ghost.tex} and \\begin{theorem}}"
            , ""
            , "\\import{real.tex}"
            , "\\begin{proposition}"
            , "  $x=x$."
            , "\\end{proposition}"
            ]
    imports <-
        either
            assertFailure
            pure
            (scanTestImports anonymousSourceDescriptor "heading-import" raw)
    assertEqual "heading imports" ["real.tex"] (unLocated <$> imports)
    segments <-
        either
            assertFailure
            pure
            (scanTestPresentation anonymousSourceDescriptor "heading-import" raw)
    case segments of
        SourceScan.DecodedPresentationHeading _ _ title _ : _ ->
            assertBool
                "heading retains literal import text"
                ("\\import{ghost.tex}" `Text.isInfixOf` title)
        _ ->
            assertFailure ("expected heading segment, got " <> show segments)

importsAcceptCommentsWhitespaceAndAdjacency :: Assertion
importsAcceptCommentsWhitespaceAndAdjacency = do
    let raw = Text.unlines
            [ "\\import{one.tex}\\import{two.tex}"
            , " \t  "
            , "% separated by a comment"
            , "\\import{three.tex}"
            , "\\begin{axiom}"
            , "  $x=x$."
            , "\\end{axiom}"
            ]
    imports <-
        either
            assertFailure
            pure
            (scanTestImports anonymousSourceDescriptor "import-trivia" raw)
    assertEqual
        "import paths"
        ["one.tex", "two.tex", "three.tex"]
        (unLocated <$> imports)
    assertEqual
        "import lines"
        [1, 1, 4]
        (locLine . startPos <$> imports)
    (lexedImports, _chunks) <-
        either
            assertFailure
            pure
            (scanTestSource anonymousSourceDescriptor "import-trivia" raw)
    assertEqual
        "complete-parser import paths"
        ["one.tex", "two.tex", "three.tex"]
        lexedImports

rejectsLateImports :: Assertion
rejectsLateImports = do
    let raw = Text.unlines
            [ "\\import{first.tex}"
            , ""
            , "\\section{Body}"
            , ""
            , "\\import{second.tex}"
            ]
        expected = "imports must form one contiguous top-level block"
    case scanTestSource anonymousSourceDescriptor "late-import" raw of
        Left err ->
            assertBool
                "scanner reports late import"
                (expected `List.isInfixOf` err)
        Right result ->
            assertFailure ("late import was accepted: " <> show result)

rejectsMalformedHeaderImports :: Assertion
rejectsMalformedHeaderImports = do
    let raw = Text.unlines
            [ "\\import{}"
            , "\\begin{axiom}"
            , "  $x=x$."
            , "\\end{axiom}"
            ]
    case scanTestSource anonymousSourceDescriptor "malformed-header-import" raw of
        Left _ -> pure ()
        Right result ->
            assertFailure ("malformed header import was accepted: " <> show result)

ignoresCommentedEnvironmentStart :: Assertion
ignoresCommentedEnvironmentStart = do
    let raw = Text.unlines
            [ "% \\begin{signature}"
            , "ordinary text"
            , "\\begin{struct}"
            , "  an ordered set $X$ is a onesorted structure."
            , "\\end{struct}"
            ]
    (_, chunks) <-
        either
            assertFailure
            pure
            (scanTestSource anonymousSourceDescriptor "commented-environment" raw)
    case chunks of
        [Located{unLocated = BeginEnv "struct"} : _] -> pure ()
        _ -> assertFailure ("expected the real structure environment, got " <> show chunks)

segmentsDocumentStructure :: Assertion
segmentsDocumentStructure = do
    let raw = Text.unlines
            [ "\\import{base.tex}"
            , "% invisible commentary"
            , "\\section{Readable}\\label{readable}"
            , "Text before."
            , ""
            , "Text after."
            , "\\begin{proposition}\\label{reflexive}"
            , "  $x=x$."
            , "\\end{proposition}"
            ]
    segments <-
        either
            assertFailure
            pure
            (scanTestPresentation anonymousSourceDescriptor "segments" raw)
    case segments of
        [ SourceScan.DecodedPresentationHeading
                SourceScan.DocumentSection headingLocation
                "Readable" (Just "readable")
          , SourceScan.DecodedPresentationProse proseLocation prose
          , SourceScan.DecodedPresentationFormal formalLocation environment
          ] -> do
                assertEqual "heading line" 3 (locLine headingLocation)
                assertEqual "prose line" 3 (locLine proseLocation)
                assertBool "first prose paragraph retained"
                    ("Text before." `Text.isInfixOf` prose)
                assertBool "second prose paragraph retained"
                    ("Text after." `Text.isInfixOf` prose)
                assertEqual "formal line" 7 (locLine formalLocation)
                assertEqual "formal environment" "proposition" environment
        other ->
            assertFailure
                ("unexpected document segmentation: " <> show other)

incompleteHeadingsRemainProse :: Assertion
incompleteHeadingsRemainProse = do
    segments <-
        either
            assertFailure
            pure
            (scanTestPresentation
                anonymousSourceDescriptor
                "incomplete-heading"
                "\\section{unfinished")
    case segments of
        [SourceScan.DecodedPresentationProse location prose] -> do
            assertEqual "prose location" (1, 1)
                (locLine location, locColumn location)
            assertEqual "prose source" "\\section{unfinished" prose
        other ->
            assertFailure
                ("incomplete heading did not remain prose: " <> show other)

multibyteProseUsesScalarColumns :: Assertion
multibyteProseUsesScalarColumns = do
    segments <-
        either
            assertFailure
            pure
            (scanTestPresentation
                anonymousSourceDescriptor
                "multibyte-prose"
                "αβ\\begin{axiom}\\end{axiom}")
    case segments of
        [ SourceScan.DecodedPresentationProse proseLocation "αβ"
          , SourceScan.DecodedPresentationFormal formalLocation "axiom"
          ] -> do
                assertEqual "prose column" 1 (locColumn proseLocation)
                assertEqual "formal column" 3 (locColumn formalLocation)
        other ->
            assertFailure
                ("unexpected multibyte segmentation: " <> show other)

parsesPresentationVariables :: Assertion
parsesPresentationVariables = do
    SourceScan.parsePresentationVariableFragment "\n  x, \\alpha, A_2\n"
        `shouldBe` Right (Just ("x" :| ["alpha", "A2"]))
    for_ (["x+y", "x,", "\\emptyset", "f(x)"] :: [Text]) \source ->
        assertEqual (Text.unpack source) (Right Nothing)
            (SourceScan.parsePresentationVariableFragment source)

parsesPresentationReferences :: Assertion
parsesPresentationReferences = do
    SourceScan.parsePresentationReferenceFragment "\\ref{one}"
        `shouldBe` Right (Just ("one" :| []))
    SourceScan.parsePresentationReferenceFragment "\\cref{one,two_2}"
        `shouldBe` Right (Just ("one" :| ["two_2"]))
    SourceScan.parsePresentationReferenceFragment "\\cref{one,\n    two_2}"
        `shouldBe` Right (Just ("one" :| ["two_2"]))
    SourceScan.parsePresentationReferenceFragment "\\obv{one_two,\n    second}"
        `shouldBe` Right (Just ("one_two" :| ["second"]))
    for_ (["\\cref{one,}", "\\ref{2bad}", "\\hyperref[one]{One}",
            "\\obv{}", "\\obv{one,}", "\\obv{one}{two}", "\\auto{one}"] :: [Text])
        \source ->
            assertEqual (Text.unpack source) (Right Nothing)
                (SourceScan.parsePresentationReferenceFragment source)

scansPresentationMathFragments :: Assertion
scansPresentationMathFragments = do
    case SourceScan.scanMathSnippet "  x=\\alpha\n" of
        Right tokens ->
            assertEqual
                "math tokens"
                [Variable "x", Symbol "=", Variable "alpha"]
                (unLocated <$> tokens)
        Left failure ->
            assertFailure ("valid math fragment failed: " <> show failure)
    for_ (["x\ty", "\\", "\\mathbb{a}", "\\text{unterminated"] :: [Text])
        \source ->
            case SourceScan.scanMathSnippet source of
                Left (SourceScan.SourceInputFailure _) -> pure ()
                result ->
                    assertFailure
                        ("malformed math fragment was not rejected: "
                            <> show result)

constructsEmptyLexicalSyntax :: Assertion
constructsEmptyLexicalSyntax =
    forM_
        [ ("empty", "")
        , ("comment-only", "% heading\n% body")
        ]
        \(description, raw) -> do
            let input = Text.pack raw
            imports <-
                either
                    assertFailure
                    pure
                    (scanTestImports
                        anonymousSourceDescriptor
                        description
                        input)
            assertEqual (description <> " imports") [] imports
            (lexedImports, chunks) <-
                either
                    assertFailure
                    pure
                    (scanTestSource
                        anonymousSourceDescriptor
                        description
                        input)
            assertEqual (description <> " lexer imports") [] lexedImports
            assertEqual (description <> " chunks") [] chunks
            extracted <-
                either
                    (assertFailure . show)
                    pure
                    (concatMap preparedLexicalItems
                        <$> traverse prepareLexicalChunk chunks)
            assertEqual
                (description <> " extracted declarations")
                []
                extracted
            delta <-
                either
                    (assertFailure . show)
                    pure
                    (canonicalSyntaxDelta [])
            assertBool
                (description <> " syntax declarations")
                (null (canonicalSyntaxDeltaEntries delta))

extractsSourceFixityPragmas :: Assertion
extractsSourceFixityPragmas = do
    let input =
            "  %! infixl 0\n"
                <> "\t%! infixr 07\r\n"
                <> "%! infix 3"
        ordinaryComments =
            Text.unlines
                [ "% ! infixl 1"
                , "text %! infixr 2"
                , "% ordinary"
                ]
    verification <-
        either assertFailure pure
            (scanTestVerification anonymousSourceDescriptor "pragma-unit" input)
    let pragmas = SourceScan.verificationPragmas verification
    assertEqual
        "normalized pragmas"
        [ (LeftAssoc, 0, 1, 3)
        , (RightAssoc, 7, 2, 2)
        , (NonAssoc, 3, 3, 1)
        ]
        [ ( syntaxPragmaAssociativity pragma
          , sourceMixfixLevelValue (syntaxPragmaLevel pragma)
          , locLine (syntaxPragmaLocation pragma)
          , locColumn (syntaxPragmaLocation pragma)
          )
        | pragma <- pragmas
        ]
    ordinaryVerification <-
        either
            assertFailure
            pure
            (scanTestVerification
                anonymousSourceDescriptor "pragma-unit" ordinaryComments)
    assertEqual
        "ordinary comments"
        []
        (SourceScan.verificationPragmas ordinaryVerification)

literalAdvancementPreservesPragmaObservation :: Assertion
literalAdvancementPreservesPragmaObservation = do
    verification <-
        either
            assertFailure
            pure
            (scanTestVerification
                anonymousSourceDescriptor
                "literal-pragma-observation"
                (Text.unlines
                    [ "\\import{base.tex}%! infixl 1"
                    , "%! infixr 2"
                    ]))
    assertEqual
        "only a line-leading pragma is observed"
        [(RightAssoc, 2, 2, 1)]
        [ ( syntaxPragmaAssociativity pragma
          , sourceMixfixLevelValue (syntaxPragmaLevel pragma)
          , locLine (syntaxPragmaLocation pragma)
          , locColumn (syntaxPragmaLocation pragma)
          )
        | pragma <- SourceScan.verificationPragmas verification
        ]

rejectsMalformedPragmas :: Assertion
rejectsMalformedPragmas =
    forM_
        [ ("%!infixl 1\n", SyntaxPragmaMissingSpaceAfterPrefix)
        , ("%!\n", SyntaxPragmaMissingKeyword)
        , ("%! Infixl 1\n", SyntaxPragmaUnknownKeyword "Infixl")
        , ("%! infixl\n", SyntaxPragmaMissingLevel)
        , ("%! infixl -1\n", SyntaxPragmaInvalidLevel)
        , ("%! infixl ١\n", SyntaxPragmaInvalidLevel)
        , ("%! infixl 8\n", SyntaxPragmaLevelOutOfRange)
        , ("%! infixl 1 extra\n", SyntaxPragmaTrailingContent)
        , ("%! infixl 1\r", SyntaxPragmaLoneCarriageReturn)
        ]
        \(input, expectedProblem) ->
            case SourceScan.scanCompleteVerificationText
                    anonymousSourceDescriptor "pragma-unit" input of
                Left
                    (SourceScan.SourceInputFailure
                        (SourceScan.VerificationPragmaFailure
                            (InvalidSyntaxPragma location actualProblem))) -> do
                    assertEqual
                        ("problem for " <> show input)
                        expectedProblem
                        actualProblem
                    assertEqual "error line" 1 (locLine location)
                    assertEqual "error column" 1 (locColumn location)
                Left err ->
                    assertFailure
                        ("unexpected pragma error: "
                            <> show err)
                Right verification ->
                    assertFailure
                        ("expected malformed pragma rejection, got "
                            <> show (SourceScan.verificationPragmas verification))

tokensInProof :: Text -> IO [Token]
tokensInProof raw =
    case scanTestSource anonymousSourceDescriptor "lexer-unit" wrapped of
        Left err ->
            assertFailure err
        Right (_imports, chunks) ->
            pure (concatMap (map unLocated) chunks)
    where
        wrapped = Text.unlines
            [ "\\begin{proof}"
            , raw
            , "\\end{proof}"
            ]

locatedTokensInProof :: Text -> IO [Located Token]
locatedTokensInProof raw =
    case scanTestSource anonymousSourceDescriptor "lexer-unit" wrapped of
        Left err ->
            assertFailure err
        Right (_imports, chunks) ->
            pure (concat chunks)
  where
    wrapped = Text.unlines
        [ "\\begin{proof}"
        , raw
        , "\\end{proof}"
        ]

shouldBe :: (Eq a, Show a, HasCallStack) => a -> a -> Assertion
shouldBe = flip (assertEqual "")
