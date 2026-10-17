module Felix.Test.Unit.ParsedPayload (unitTests) where

import Base
import Felix.Cache.Codec qualified as Cache
import Felix.Parsed.Identity qualified as Identity
import Felix.Parsed.Payload qualified as Parsed
import Felix.Report.Location
import Felix.Source.Content qualified as Content
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface qualified as Syntax
import Felix.Syntax.Lexicon qualified as Lexicon

import Data.Binary.Put qualified as Put
import Data.ByteString qualified as ByteString
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests = testGroup "Parsed payload"
    [ testCase "retains complete labeled structure parents" retainsParentLabels
    , testCase "recursive definition payloads retain both result kinds" recursivePayloads
    , testCase "rejects noncanonical fields during decoding" rejectsNoncanonicalFields
    , testCase "accepted byte mutations re-encode identically" checksAcceptedMutations
    , testCase "located coordinate endpoints stay distinct from Nowhere"
        retainsLocatedEndpoints
    , testCase "retains noun polarity separately from sentence negation"
        retainsNounPolarity
    ]

payloadKey :: IO Identity.ParsedModuleKey
payloadKey = expectRight
    (Identity.parsedModuleKey
        (Content.sourceContentIdBytes "parsed-codec-test")
        Syntax.baseSyntaxInterfaceId [])

expectRight :: Show failure => Either failure value -> IO value
expectRight = either (assertFailure . show) pure

-- Small wire fixtures keep each malformed field independent of the generic
-- constructor layout. Occurrence association belongs to module installation.
occurrencePayload :: Cache.CachePut -> Cache.CachePut -> Cache.CachePut -> ByteString.ByteString
occurrencePayload index location entry = Cache.encodeCache do
    Cache.putCacheTag 0x01
    Put.putWord64be 0 -- imports
    Put.putWord64be 0 -- blocks
    Put.putWord64be 1 -- occurrences
    index
    location
    Cache.putCacheText "marker"
    entry
    Put.putByteString (ByteString.replicate 32 0) -- opaque syntax identity

operationEntry :: Cache.CachePut
operationEntry = Cache.putCacheTag 0x09 >> Cache.putCacheText "operation"

located :: Cache.CachePut -> Cache.CachePut
located line = Cache.putCacheTag 0x01 >> line >> Cache.putCacheNatural 4

rejectsNoncanonicalFields :: Assertion
rejectsNoncanonicalFields = do
    key <- payloadKey
    let index = Cache.putCacheInteger 0
        nowhere = Cache.putCacheTag 0x00
        valid = occurrencePayload index nowhere operationEntry
        singular = Raw.patternFromHoley [Just (Raw.Word "covers"), Nothing]
        mismatchedBase = Raw.patternFromHoley [Just (Raw.Word "cover")]
        invalidVerb = do
            Cache.putCacheTag 0x05
            Syntax.putPatternCache singular
            Syntax.putPatternCache mismatchedBase
            Cache.putCacheText "verb"
        invalidFixity = do
            Cache.putCacheTag 0x07
            Syntax.putPatternCache Raw.End
            Cache.putCacheText "function"
            Cache.putCacheTag 0x00 -- left associative
            Cache.putCacheTag 0xff -- unsupported level
        invalidUtf8 = Cache.putCacheTag 0x09 >> Cache.putCacheBytes "\xc0\x80"
        badFields =
            [ ("negative zero", occurrencePayload
                (Cache.putCacheTag 0x01 >> Cache.putCacheNatural 0) nowhere operationEntry)
            , ("non-minimal magnitude", occurrencePayload
                (Cache.putCacheTag 0x00 >> Cache.putCacheBytes "\0\1") nowhere operationEntry)
            , ("unknown integer sign", occurrencePayload
                (Cache.putCacheTag 0x02 >> Cache.putCacheNatural 1) nowhere operationEntry)
            , ("Int overflow", occurrencePayload
                (Cache.putCacheInteger (toInteger (maxBound :: Int) + 1)) nowhere operationEntry)
            , ("non-minimal line", occurrencePayload index
                (located (Cache.putCacheBytes "\0")) operationEntry)
            , ("coordinate overflow", occurrencePayload index
                (located (Cache.putCacheNatural 0x1000000)) operationEntry)
            , ("unknown location tag", occurrencePayload index (Cache.putCacheTag 0x02) operationEntry)
            , ("unknown lexical tag", occurrencePayload index nowhere (Cache.putCacheTag 0xff))
            , ("invalid UTF-8", occurrencePayload index nowhere invalidUtf8)
            , ("mismatched verb surfaces", occurrencePayload index nowhere invalidVerb)
            , ("invalid fixity", occurrencePayload index nowhere invalidFixity)
            , ("excessive list length", Cache.encodeCache do
                Cache.putCacheTag 0x01
                Put.putWord64be (Cache.maximumCacheListElements + 1))
            , ("unsafe import path", Cache.encodeCache do
                Cache.putCacheTag 0x01
                Put.putWord64be 1
                Cache.putCacheText "../escape.tex"
                nowhere
                Put.putWord64be 0
                Put.putWord64be 0
                Put.putByteString (ByteString.replicate 32 0))
            , ("trailing bytes", valid <> "\0")
            ]
    _ <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key valid)
    for_ badFields $ \(label, bytes) -> do
        case Parsed.canonicalParsedPayloadFromBytes bytes of
            Left{} -> pure ()
            Right _ -> assertFailure (label <> " accepted by byte-only reader")
        case Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key bytes of
            Left{} -> pure ()
            Right _ -> assertFailure (label <> " accepted by decoded-artifact reader")

recursivePayloads :: Assertion
recursivePayloads = do
    key <- payloadKey
    delta <- expectRight (Syntax.canonicalSyntaxDelta [])
    syntax <- expectRight (Syntax.moduleSyntaxInterface [] delta)
    let symbol = Raw.mkMixfixItem [Just (Raw.Command "copy"),Nothing] "copy" Raw.NonAssoc
        term = Raw.ExprVar "p"
        predicate = Raw.PrefixPredicate "sat" 1
        truth = Raw.StmtFormula (Raw.PropositionalConstant Nowhere Raw.IsTop)
        blocks =
            [ Raw.BlockRecursive Nowhere Nothing "copy" (Raw.RecursiveDefinition []
                (Left (Raw.SymbolPattern symbol ["p"])) "p" (Raw.ExprVar "D")
                (Raw.RecursiveClause (Just "Base") (Left (Raw.ExprOp Nowhere symbol [term],term)) :| []))
            , Raw.BlockRecursive Nowhere Nothing "sat" (Raw.RecursiveDefinition []
                (Right (Raw.DefnSymbolicPredicate predicate "sat" ("p" :| []))) "p" (Raw.ExprVar "D")
                (Raw.RecursiveClause Nothing (Right (Raw.FormulaPredicate Nowhere predicate "sat" (term :| []),truth)) :| []))
            ]
        payload = Parsed.canonicalParsedPayload [] blocks [] (Syntax.moduleSyntaxAssertedId syntax)
    decoded <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key
        (Parsed.canonicalParsedPayloadBytes payload))
    Parsed.decodedParsedBlocks decoded @?= blocks

checksAcceptedMutations :: Assertion
checksAcceptedMutations = do
    key <- payloadKey
    let location = mkLocation anonymousSourceDescriptor 3 7
        block = Raw.BlockAxiom location Nothing "nonempty"
            (Raw.Axiom [] (Raw.StmtFormula
                (Raw.FormulaSetMap location
                    (Raw.ExprVar (Raw.FreshVar (-2)))
                    (Raw.ExprVar "A") (Raw.ExprVar "B"))))
        emptyBytes = occurrencePayload (Cache.putCacheInteger 0)
            (located (Cache.putCacheNatural 7)) operationEntry
    decoded <- expectRight
        (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key emptyBytes)
    let bytes = Parsed.canonicalParsedPayloadBytes
            (Parsed.canonicalParsedPayload [] [block] []
                (Parsed.decodedParsedSyntaxInterface decoded))
        mutations input = input
            : [ ByteString.take position input <> ByteString.singleton byte
                    <> ByteString.drop (position + 1) input
              | position <- [0 .. ByteString.length input - 1]
              , byte <- [0x00, 0x01, 0x02, 0x7f, 0xff]
              ]
            <> [ByteString.take n input | n <- [0 .. ByteString.length input - 1]]
    for_ (mutations bytes <> mutations emptyBytes) $ \candidate ->
        case Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key candidate of
            Left{} -> pure ()
            Right actual -> do
                let reencoded = Parsed.canonicalParsedPayload
                        (Parsed.decodedParsedImports actual)
                        (Parsed.decodedParsedBlocks actual)
                        (Parsed.decodedParsedOccurrences actual)
                        (Parsed.decodedParsedSyntaxInterface actual)
                assertEqual "successful reader preserves every byte" candidate
                    (Parsed.canonicalParsedPayloadBytes reencoded)

retainsLocatedEndpoints :: Assertion
retainsLocatedEndpoints = do
    key <- payloadKey
    for_ [anonymousSourceDescriptor, sourceDescriptorForPath "endpoints.tex"] $ \descriptor ->
        for_ [0, 0xffffff] $ \coordinate -> do
            let bytes = occurrencePayload (Cache.putCacheInteger 0)
                    (Cache.putCacheTag 0x01
                        >> Cache.putCacheNatural coordinate
                        >> Cache.putCacheNatural coordinate)
                    operationEntry
            decoded <- expectRight
                (Parsed.decodedParsedArtefactFromBytes descriptor key bytes)
            let locations = Parsed.parsedSyntaxOccurrenceLocation
                    <$> Parsed.decodedParsedOccurrences decoded
            locations @?= [mkLocation descriptor (fromIntegral coordinate) (fromIntegral coordinate)]
            assertBool "located endpoint is not Nowhere" (all (/= Nowhere) locations)
            let reencoded = Parsed.canonicalParsedPayload
                    (Parsed.decodedParsedImports decoded)
                    (Parsed.decodedParsedBlocks decoded)
                    (Parsed.decodedParsedOccurrences decoded)
                    (Parsed.decodedParsedSyntaxInterface decoded)
            Parsed.canonicalParsedPayloadBytes reencoded @?= bytes

retainsNounPolarity :: Assertion
retainsNounPolarity = do
    key <- payloadKey
    seed <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key
        (occurrencePayload (Cache.putCacheInteger 0) (Cache.putCacheTag 0x00) operationEntry))
    let noun sign = Raw.StmtNoun sign (Raw.TermExpr (Raw.ExprVar "x") :| [])
            (Raw.NounPhrase [] (Raw.Noun Nowhere Lexicon.builtinSetNoun [])
                (Raw.unboundedNounBinder Nothing) [] Nothing)
        statements = [noun Raw.Positive, noun Raw.Negative, Raw.StmtNeg Nowhere (noun Raw.Positive)]
        blocks = [Raw.BlockAxiom Nowhere Nothing "polarity" (Raw.Axiom [] statement)
            | statement <- statements]
        bytes = Parsed.canonicalParsedPayloadBytes
            (Parsed.canonicalParsedPayload [] blocks [] (Parsed.decodedParsedSyntaxInterface seed))
    decoded <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key bytes)
    assertEqual "predicate and sentence polarity survive storage" blocks
        (Parsed.decodedParsedBlocks decoded)

retainsParentLabels :: Assertion
retainsParentLabels = do
    key <- payloadKey
    seed <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key
        (occurrencePayload (Cache.putCacheInteger 0) (Cache.putCacheTag 0x00) operationEntry))
    let phrase = Raw.LexicalItemSgPl
            (Raw.SgPl (Raw.TokenCons (Raw.Word "action") Raw.End)
                (Raw.TokenCons (Raw.Word "actions") Raw.End)) "action"
        parent argument name = Raw.StructParent
            (Raw.StructApplication phrase [Raw.TermExpr (Raw.ExprVar argument)]) (Just name)
        block = Raw.BlockStruct Nowhere Nothing "child"
            (Raw.StructDefn [] phrase ["R", "S"]
                [parent "R" "left", parent "S" "right"] "M" [] [])
        bytes = Parsed.canonicalParsedPayloadBytes
            (Parsed.canonicalParsedPayload [] [block] [] (Parsed.decodedParsedSyntaxInterface seed))
    decoded <- expectRight (Parsed.decodedParsedArtefactFromBytes anonymousSourceDescriptor key bytes)
    assertEqual "labels stay attached to their complete applications" [block]
        (Parsed.decodedParsedBlocks decoded)
