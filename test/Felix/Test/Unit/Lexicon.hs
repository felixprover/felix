{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Lexicon (unitTests) where

import Base
import Felix.Cache.Codec
import Felix.Syntax.Abstract
import Felix.Syntax.Adapt
import Felix.Syntax.Interface
import Felix.Syntax.Lexicon

import Data.Either (isLeft)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit



unitTests :: TestTree
unitTests =
    testGroup "Lexicon"
        [ testCase "retains the literal ten-row base mixfix grouping"
            retainsBaseMixfixGrouping
        , testCase "checks literal mixfix levels"
            checksMixfixLevels
        , testCase "admits explicitly delimited infix parameters"
            admitsDelimitedInfixParameters
        , testCase "coalesces equal canonical syntax entries"
            coalescesCanonicalEntries
        , testCase "keeps adjective side and intrinsic identity unambiguous"
            rejectsAmbiguousAdjectiveSurfaces
        , testCase "rejects shared plural parser surfaces"
            rejectsSharedPluralSurfaces
        , testCase "pluralizes structure nominal heads independently of length"
            pluralizesStructureNominalHeads
        , testCase "parses only nonempty word-bearing phrase specifications"
            parsesPhraseSpecificationsTotally
        , testCase "derives bounded canonical verb paradigms"
            derivesCanonicalVerbSurfaces
        , testCase "rejects malformed verb-surface pairs deterministically"
            rejectsMalformedVerbSurfaces
        , testCase "round-trips complete canonical lexical entries"
            roundTripsCanonicalEntries
        , testCase "rejects malformed cached canonical verb surfaces"
            rejectsMalformedCanonicalVerbCache
        , testCase "round-trips asserted module syntax interfaces"
            roundTripsSyntaxInterfaces
        ]

parsesPhraseSpecificationsTotally :: Assertion
parsesPhraseSpecificationsTotally = do
    assertEqual
        "ordinary phrase"
        (Right
            (lexicalPhrase
                (Just "equal" :| [Just "to", Nothing])))
        (readLexicalPhrase "equal to ?")
    assertEqual
        "singular and plural phrase"
        (Right
            (lexicalPhraseSgPl
                ( (Just "element", Just "elements")
                    :| [ (Just "of", Just "of")
                       , (Nothing, Nothing)
                       ]
                )))
        (readLexicalPhraseSgPl "element[/s] of ?")
    assertEqual
        "built-in equality surfaces"
        (lexicalPhraseSgPl
            ((Just "equals", Just "equal") :| [(Nothing, Nothing)]))
        (let surfaces = verbLexicalSurfaces builtinEqualityVerb
         in SgPl
            (verbSurfaceSingular surfaces)
            (verbSurfaceBase surfaces))
    traverse_
        (\source ->
            assertBool
                ("invalid ordinary phrase was accepted: " <> show source)
                (isLeft (readLexicalPhrase source)))
        ["", " ", "?", "? ?"]
    traverse_
        (\source ->
            assertBool
                ("invalid singular/plural phrase was accepted: " <> show source)
                (isLeft (readLexicalPhraseSgPl source)))
        ["", " ", "?", "? ?", "[/]"]

derivesCanonicalVerbSurfaces :: Assertion
derivesCanonicalVerbSurfaces = do
    traverse_
        (\(singularWord, baseWord) -> do
            surfaces <- expectRight
                (deriveVerbSurfaces Nothing
                    (verbPhrase singularWord))
            assertEqual
                ("inferred base of " <> show singularWord)
                (verbPhrase baseWord)
                (verbSurfaceBase surfaces))
        [ ("has", "have")
        , ("accompanies", "accompany")
        , ("passes", "pass")
        , ("wishes", "wish")
        , ("catches", "catch")
        , ("fixes", "fix")
        , ("buzzes", "buzz")
        , ("goes", "go")
        , ("covers", "cover")
        , ("cut", "cut")
        ]
    explicit <- expectRight
        (deriveVerbSurfaces (Just "lie") (verbPhrase "lies"))
    assertEqual "explicit base wins"
        (verbPhrase "lie")
        (verbSurfaceBase explicit)
    assertEqual "singular tail is exact"
        (verbPhrase "lies")
        (verbSurfaceSingular explicit)
    invariant <- expectRight
        (deriveVerbSurfaces (Just "has") (verbPhrase "has"))
    assertEqual "an explicit invariant surface is accepted"
        (verbPhrase "has")
        (verbSurfaceBase invariant)
  where
    verbPhrase word =
        lexicalPhrase
            (Just word :| [Just "a", Just "property", Nothing])

rejectsMalformedVerbSurfaces :: Assertion
rejectsMalformedVerbSurfaces = do
    let word text = Just (Word text)
        valid = [word "covers", Nothing]
        validBase = [word "cover", Nothing]
    assertEqual "singular emptiness is checked first"
        (Left (EmptyVerbSurface SingularVerbSurface))
        (checkVerbSurfaces [] [])
    assertEqual "singular leading holes are rejected"
        (Left (LeadingVerbSurfaceHole SingularVerbSurface))
        (checkVerbSurfaces [Nothing] validBase)
    assertEqual "singular leading nonwords are rejected"
        (Left
            (LeadingVerbSurfaceTokenNotWord
                SingularVerbSurface
                (Command "predicate")))
        (checkVerbSurfaces [Just (Command "predicate")] validBase)
    assertEqual "singular empty words are rejected"
        (Left (EmptyLeadingVerbSurfaceWord SingularVerbSurface))
        (checkVerbSurfaces [word ""] validBase)
    assertEqual "base emptiness follows a valid singular"
        (Left (EmptyVerbSurface BaseVerbSurface))
        (checkVerbSurfaces valid [])
    assertEqual "base leading holes are rejected"
        (Left (LeadingVerbSurfaceHole BaseVerbSurface))
        (checkVerbSurfaces valid [Nothing])
    assertEqual "tail mismatches are rejected last"
        (Left VerbSurfaceTailMismatch)
        (checkVerbSurfaces valid [word "cover", word "something"])
    assertEqual "empty inferred bases use the shared pair error"
        (Left (EmptyLeadingVerbSurfaceWord BaseVerbSurface))
        (deriveVerbSurfaces Nothing [word "s", Nothing])

retainsBaseMixfixGrouping :: Assertion
retainsBaseMixfixGrouping =
    do
        assertEqual
            "least-to-most-tight marker and associativity rows"
            expectedBaseRows
            (fmap (fmap entryShape) builtinMixfixLevels)
        assertEqual
            "canonical base manifest"
            expectedBaseRows
            (fmap (fmap canonicalEntryShape) baseSyntaxManifest)
        assertEqual
            "cache-epoch base syntax identity"
            "2d3d71dbcfaf8cf9d1d45a27ddd785938f7b3b96ca499e86b7d646f2fb28b1b0"
            (cacheDigestHex
                (baseSyntaxInterfaceIdDigest
                    baseSyntaxInterfaceId))
  where
    entryShape (MixfixItem _pattern marker associativity) =
        (marker, associativity)

    canonicalEntryShape = \case
        CanonicalExpressionFunction
                _pattern
                marker
                (Fixity associativity _level) ->
            (marker, associativity)
        entry ->
            impossible
                ("non-expression entry in base manifest: "
                    <> show entry)

checksMixfixLevels :: Assertion
checksMixfixLevels = do
    assertEqual
        "lowest level"
        (Right 0)
        (mixfixLevelValue <$> mixfixLevel 0)
    assertEqual
        "highest internal level"
        (Right 9)
        (mixfixLevelValue <$> mixfixLevel 9)
    assertEqual
        "out-of-range level"
        (Left (MixfixLevelOutOfRange 10))
        (mixfixLevel 10)

admitsDelimitedInfixParameters :: Assertion
admitsDelimitedInfixParameters = do
    assertBool
        "ordinary binary operator"
        (eligibleExpressionPattern
            (patternFromHoley
                [ Nothing
                , Just (Command "star")
                , Nothing
                ]))
    assertBool
        "braced index between operands"
        (eligibleExpressionPattern
            (patternFromHoley
                [ Nothing
                , Just (Command "star")
                , Just (Symbol "_")
                , Just InvisibleBraceL
                , Nothing
                , Just InvisibleBraceR
                , Nothing
                ]))
    assertBool
        "an unbraced internal hole is not a fixity target"
        (not
            (eligibleExpressionPattern
                (patternFromHoley
                    [ Nothing
                    , Just (Command "star")
                    , Just (Symbol "_")
                    , Nothing
                    , Nothing
                    ])))

coalescesCanonicalEntries :: Assertion
coalescesCanonicalEntries = do
    level <- expectRight (mixfixLevel 3)
    let pat =
            patternFromHoley
                [ Nothing
                , Just (Command "star")
                , Nothing
                ]
        first =
            CanonicalExpressionFunction
                pat
                "star"
                (Fixity LeftAssoc level)
        conflicting =
            CanonicalExpressionFunction
                pat
                "other_star"
                (Fixity LeftAssoc level)
    delta <- expectRight
        (canonicalSyntaxDelta [first, first])
    assertEqual
        "equal entries coalesce"
        1
        (canonicalSyntaxDeltaSize delta)
    assertEqual
        "coalesced entry"
        [first]
        (canonicalSyntaxDeltaEntries delta)
    assertEqual
        "collision is independent of occurrence order"
        (canonicalSyntaxDelta [first, conflicting])
        (canonicalSyntaxDelta [conflicting, first])

rejectsAmbiguousAdjectiveSurfaces :: Assertion
rejectsAmbiguousAdjectiveSurfaces = do
    let pat = patternFromHoley [Just (Word "finite")]
        left =
            CanonicalUserAdjective
                LeftAdjectiveSide
                (AdjectiveSurfaceKey pat)
        right =
            CanonicalUserAdjective
                RightAdjectiveSide
                (AdjectiveSurfaceKey pat)
        intrinsic =
            CanonicalIntrinsicAdjective
                RightAdjectiveSide
                pat
                "finite_intrinsic"
    assertCollision left right
    assertCollision right intrinsic
    delta <- expectRight (canonicalSyntaxDelta [left, left])
    assertEqual
        "one neutral parser entry represents repeated providers"
        [left]
        (canonicalSyntaxDeltaEntries delta)
  where
    assertCollision first second =
        case canonicalSyntaxDelta [first, second] of
            Left collision ->
                assertEqual
                    "collision is reported at the common adjective surface"
                    (NonEmpty.head (canonicalLexicalSurfacePatterns first))
                    (canonicalCollisionPattern collision)
            Right _ ->
                assertFailure
                    "accepted two adjective identities for one parser surface"

rejectsSharedPluralSurfaces :: Assertion
rejectsSharedPluralSurfaces = do
    let nounEntry =
            CanonicalNoun
                (wordPattern "member")
                (wordPattern "objects")
                "member"
        otherNoun =
            CanonicalNoun
                (wordPattern "element")
                (wordPattern "objects")
                "element"
        verbEntry =
            CanonicalVerb
                (checkedVerbSurfaces
                    (wordPattern "belongs")
                    (wordPattern "objects"))
                "belongs"
        structureEntry =
            CanonicalStructureNoun
                (wordPattern "structure")
                (wordPattern "objects")
                "structure"
    assertPluralCollision nounEntry otherNoun
    assertPluralCollision nounEntry verbEntry
    assertPluralCollision nounEntry structureEntry
    case decodeCache
            getCanonicalSyntaxDeltaCache
            (encodeCache
                (putCacheList
                    putCanonicalLexicalEntryCache
                    [nounEntry, otherNoun])) of
        Left _ ->
            pure ()
        Right _ ->
            assertFailure
                "decoded a delta with a shared plural collision"
  where
    wordPattern word =
        TokenCons (Word word) End

    assertPluralCollision first second =
        case canonicalSyntaxDelta [first, second] of
            Left collision -> do
                assertEqual
                    "shared plural pattern"
                    (wordPattern "objects")
                    (canonicalCollisionPattern collision)
                assertEqual
                    "both complete entries"
                    (Set.fromList [first, second])
                    (Set.fromList
                        (toList
                            (canonicalCollisionEntries collision)))
            Right _ ->
                assertFailure
                    "accepted two entries with one parser-active plural"

pluralizesStructureNominalHeads :: Assertion
pluralizesStructureNominalHeads = do
    level <- expectRight (mixfixLevel 0)
    let fixity = Fixity NonAssoc level
        completeOrderedField =
            lexicalPhrase
                (Just "complete" :|
                    [ Just "Archimedean"
                    , Just "ordered"
                    , Just "field"
                    ])
        towerSegmentDatum =
            lexicalPhrase
                (Just "tower" :|
                    [ Just "segment"
                    , Just "datum"
                    ])
        leftModuleOver =
            lexicalPhrase
                (Just "left" :|
                    [ Just "module"
                    , Just "over"
                    , Nothing
                    ])
    assertPlural
        fixity
        completeOrderedField
        (lexicalPhrase
            (Just "complete" :|
                [ Just "Archimedean"
                , Just "ordered"
                , Just "fields"
                ]))
    assertPlural
        fixity
        towerSegmentDatum
        (lexicalPhrase
            (Just "tower" :|
                [ Just "segment"
                , Just "data"
                ]))
    assertPlural
        fixity
        leftModuleOver
        (lexicalPhrase
            (Just "left" :|
                [ Just "modules"
                , Just "over"
                , Nothing
                ]))
  where
    assertPlural fixity singular expected =
        case canonicalExtractedItem fixity
                (ExtractedStructureNoun singular "plural_test") of
            CanonicalStructureNoun actualSingular actualPlural _marker -> do
                assertEqual "singular structure surface"
                    (patternFromHoley singular) actualSingular
                assertEqual "plural structure surface"
                    (patternFromHoley expected) actualPlural
            entry ->
                assertFailure
                    ("unexpected extracted structure entry: " <> show entry)

roundTripsCanonicalEntries :: Assertion
roundTripsCanonicalEntries = do
    level <- expectRight (mixfixLevel 4)
    let unary =
            patternFromHoley
                [ Just (Word "red")
                , Nothing
                ]
        singular =
            patternFromHoley
                [ Just (Word "member")
                , Just (Word "of")
                , Nothing
                ]
        plural =
            patternFromHoley
                [ Just (Word "members")
                , Just (Word "of")
                , Nothing
                ]
        binary =
            patternFromHoley
                [ Nothing
                , Just (Command "star")
                , Nothing
                ]
        entries =
            [ CanonicalUserAdjective
                LeftAdjectiveSide (AdjectiveSurfaceKey unary)
            , CanonicalIntrinsicAdjective
                RightAdjectiveSide unary "red_right"
            , CanonicalFunctionPhrase singular plural "member_fun"
            , CanonicalNoun singular plural "member"
            , CanonicalStructureNoun singular plural "member_struct"
            , CanonicalVerb
                (checkedVerbSurfaces singular plural)
                "member_verb"
            , CanonicalRelation (Command "rel") (ParameterArity 2) "rel"
            , CanonicalExpressionFunction
                binary
                "star"
                (Fixity LeftAssoc level)
            , CanonicalTypedConstant
                (Variable "Phi")
                (ConcreteArrow
                    ConcreteSet
                    (ConcreteArrow ConcreteSet ConcreteProp))
                "typed_phi"
            , CanonicalPrefixPredicate "Pred" 3 "pred"
            , CanonicalStructureOperation "operation"
            ]
    traverse_
        (\entry ->
            assertEqual
                ("cache round trip for " <> show entry)
                (Right entry)
                (decodeCache
                    getCanonicalLexicalEntryCache
                    (encodeCache
                        (putCanonicalLexicalEntryCache entry))))
            entries

checkedVerbSurfaces :: Pattern -> Pattern -> VerbSurfaces
checkedVerbSurfaces singular base =
    case checkVerbSurfaces
            (patternToHoley singular)
            (patternToHoley base) of
        Right surfaces -> surfaces
        Left failure ->
            impossible ("invalid verb test fixture: " <> show failure)

rejectsMalformedCanonicalVerbCache :: Assertion
rejectsMalformedCanonicalVerbCache = do
    let singular = patternFromHoley
            [Just (Word "covers"), Nothing]
        mismatchedBase = patternFromHoley
            [Just (Word "cover"), Just (Word "everything")]
        bytes = encodeCache do
            putCacheTag 0x05
            putPatternCache singular
            putPatternCache mismatchedBase
            putCacheText "malformed_verb"
    case decodeCache getCanonicalLexicalEntryCache bytes of
        Left{} -> pure ()
        Right entry ->
            assertFailure
                ("accepted malformed canonical verb cache entry: "
                    <> show entry)

roundTripsSyntaxInterfaces :: Assertion
roundTripsSyntaxInterfaces = do
    level <- expectRight (mixfixLevel 7)
    changedLevel <- expectRight (mixfixLevel 6)
    let entry =
            CanonicalExpressionFunction
                (patternFromHoley
                    [ Nothing
                    , Just (Command "diamond")
                    , Nothing
                    ])
                "diamond"
                (Fixity NonAssoc level)
        changedEntry =
            CanonicalExpressionFunction
                (patternFromHoley
                    [ Nothing
                    , Just (Command "diamond")
                    , Nothing
                    ])
                "diamond"
                (Fixity RightAssoc changedLevel)
    delta <- expectRight (canonicalSyntaxDelta [entry])
    changedDelta <- expectRight
        (canonicalSyntaxDelta [changedEntry])
    interface <- expectRight
        (moduleSyntaxInterface [] delta)
    changedInterface <- expectRight
        (moduleSyntaxInterface [] changedDelta)
    assertEqual
        "current fixed base"
        baseSyntaxInterfaceId
        (moduleSyntaxBase interface)
    assertEqual
        "module syntax cache round trip"
        (Right interface)
        (decodeCache
            getModuleSyntaxInterfaceCache
            (encodeCache
                (putModuleSyntaxInterfaceCache interface)))
    assertEqual
        "asserted ID is deterministic"
        (Right (moduleSyntaxAssertedId interface))
        (moduleSyntaxAssertedId
            <$> moduleSyntaxInterface [] delta)
    assertBool
        "normalized fixity changes syntax identity"
        (moduleSyntaxAssertedId interface
            /= moduleSyntaxAssertedId changedInterface)
    case moduleSyntaxInterface
            [ moduleSyntaxAssertedId interface
            , moduleSyntaxAssertedId interface
            ]
            delta of
        Left (DuplicateDirectSyntaxInterface duplicate) ->
            assertEqual
                "duplicate direct interface"
                (moduleSyntaxAssertedId interface)
                duplicate
        Left err ->
            assertFailure
                ("expected duplicate direct syntax input, got "
                    <> show err)
        Right _ ->
            assertFailure
                "accepted a duplicate direct syntax input"

expectRight :: Show err => Either err value -> IO value
expectRight = \case
    Left err ->
        assertFailure (show err)
            >> fail "unreachable"
    Right value ->
        pure value

expectedBaseRows :: [[(Marker, Associativity)]]
expectedBaseRows =
    [ []
    , [ ("add", LeftAssoc)
      , ("union", LeftAssoc)
      , ("minus", LeftAssoc)
      , ("rminus", LeftAssoc)
      , ("monus", LeftAssoc)
      ]
    , [("relcomp", LeftAssoc)]
    , [("circ", LeftAssoc)]
    , [ ("mul", LeftAssoc)
      , ("inter", LeftAssoc)
      , ("rmul", LeftAssoc)
      ]
    , [("setminus", LeftAssoc)]
    , [("times", RightAssoc)]
    , []
    , [ ("rfrac", NonAssoc)
      , ("exp", NonAssoc)
      , ("repl", NonAssoc)
      , ("sep", NonAssoc)
      , ("lfp", NonAssoc)
      , ("unions", NonAssoc)
      , ("choice", NonAssoc)
      , ("cumul", NonAssoc)
      , ("fst", NonAssoc)
      , ("snd", NonAssoc)
      , ("pow", NonAssoc)
      , ("neg", NonAssoc)
      , ("inv", NonAssoc)
      , ("abs", NonAssoc)
      , ("cons", NonAssoc)
      , ("pair", NonAssoc)
      , ("upair", NonAssoc)
      ]
    , [ ("emptyset", NonAssoc)
      , ("naturals", NonAssoc)
      , ("naturalsPlus", NonAssoc)
      , ("integers", NonAssoc)
      , ("rationals", NonAssoc)
      , ("reals", NonAssoc)
      , ("unit", NonAssoc)
      , ("zero", NonAssoc)
      ]
    ]
