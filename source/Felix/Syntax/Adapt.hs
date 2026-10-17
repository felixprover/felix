{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

module Felix.Syntax.Adapt
    ( FunctionPatternError(..)
    , VerbMetadataError(..)
    , LexiconExtractionError(..)
    , PreparedLexicalChunk
    , preparedLexicalTokens
    , preparedLexicalItems
    , prepareLexicalChunk
    , ExtractedLexiconItem(..)
    , extractedItemMarker
    , canonicalExtractedItem
    , SyntaxMaterializationError(..)
    , materializeSyntaxDelta
    , EffectiveSyntaxError(..)
    , renderEffectiveSyntaxError
    , effectiveSyntaxDelta
    , materializeEffectiveSyntax
    ) where

import Base
import Felix.Syntax.Abstract
import Felix.Syntax.FieldEnvelope
import Felix.Syntax.Interface
import Felix.Syntax.Lexicon
import Felix.Report.Location

import Control.Monad (foldM, unless)
import Data.Bifunctor qualified as Bifunctor
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Numeric.Natural (Natural)
import Text.Regex.Applicative qualified as RE
import Text.Regex.Applicative (RE)

data FunctionPatternError
    = FunctionPatternEmpty
    | FunctionPatternBareVariable
    | FunctionPatternReservedApplication
    deriving (Show, Eq)

data VerbMetadataError
    = DuplicateVerbBase
    | IllegalVerbBasePlacement
    | MalformedVerbBasePayload
    deriving (Show, Eq)

data LexiconExtractionError
    = InvalidStructureFieldEnvelope !FieldEnvelopeError
    | MalformedLexicalEnvironment !Location !Text
    | InvalidFunctionPattern !Location !FunctionPatternError
    | MalformedDatatype !Location !Text
    | MalformedRecursion !Location !Text
    | InvalidVerbMetadata !Location !VerbMetadataError
    | VerbBaseOnNonverbHead !Location
    | InvalidVerbSurfaces !Location !VerbSurfaceError
    deriving (Eq)

instance Show LexiconExtractionError where
    show = \case
        InvalidStructureFieldEnvelope failure -> show failure
        MalformedLexicalEnvironment location environment ->
            "could not find a lexical pattern in "
                <> Text.unpack environment
                <> " at "
                <> prettyLocation location
        InvalidFunctionPattern location problem ->
            functionPatternErrorMessage problem
                <> " at "
                <> prettyLocation location
        MalformedRecursion location problem ->
            "malformed recursive definition at " <> prettyLocation location <> ": " <> Text.unpack problem
        MalformedDatatype location problem ->
            "malformed datatype declaration at "
                <> prettyLocation location
                <> ": "
                <> Text.unpack problem
        InvalidVerbMetadata location problem ->
            "invalid verb-base metadata ("
                <> show problem
                <> ") at "
                <> prettyLocation location
        VerbBaseOnNonverbHead location ->
            "verb-base metadata belongs to a nonverb declaration at "
                <> prettyLocation location
        InvalidVerbSurfaces location problem ->
            "invalid verb surfaces ("
                <> show problem
                <> ") at "
                <> prettyLocation location

data PreparedLexicalChunk = PreparedLexicalChunk
    { preparedLexicalTokens :: [Located Token]
    , preparedLexicalItems :: [Located ExtractedLexiconItem]
    }

prepareLexicalChunk
    :: [Located Token]
    -> Either LexiconExtractionError PreparedLexicalChunk
prepareLexicalChunk ltoks = do
    (tokens, explicitBase, metadataLocation) <- prepareVerbMetadata ltoks
    items <- extractLexiconItemsFromPreparedChunk explicitBase tokens
    case (metadataLocation, items) of
        (Just _location, [Located{unLocated = ExtractedVerb{}}]) ->
            pure ()
        (Just location, _items) ->
            Left (VerbBaseOnNonverbHead location)
        (Nothing, _items) ->
            pure ()
    pure (PreparedLexicalChunk tokens items)

prepareVerbMetadata
    :: [Located Token]
    -> Either
        LexiconExtractionError
        ([Located Token], Maybe Text, Maybe Location)
prepareVerbMetadata ltoks =
    case verbBaseCommands of
        _first : second : _ ->
            Left
                (InvalidVerbMetadata
                    (startPos (snd second))
                    DuplicateVerbBase)
        [] ->
            Right (ltoks, Nothing, Nothing)
        [(commandIndex, commandToken)] -> do
            unless (legalPlacement commandIndex) $
                Left
                    (InvalidVerbMetadata
                        (startPos commandToken)
                        IllegalVerbBasePlacement)
            base <- metadataPayload commandIndex commandToken
            pure
                ( take commandIndex ltoks <> drop (commandIndex + 4) ltoks
                , Just base
                , Just (startPos commandToken)
                )
  where
    verbBaseCommands =
        [ (index, token)
        | (index, token) <- zip [0 :: Int ..] ltoks
        , unLocated token == Command "verbbase"
        ]

    legalPlacement commandIndex =
        case ltoks of
            Located{unLocated = BeginEnv environment} : _
                | environment == "definition"
                    || environment == "abbreviation" ->
                    case List.findIndex (isLabel . unLocated) ltoks of
                        Just labelIndex -> commandIndex == labelIndex + 1
                        Nothing -> False
            _ -> False

    metadataPayload commandIndex commandToken =
        case drop (commandIndex + 1) ltoks of
            Located{unLocated = InvisibleBraceL}
                : Located{unLocated = Word base}
                : Located{unLocated = InvisibleBraceR}
                : _ ->
                    Right base
            Located{unLocated = InvisibleBraceL}
                : Located{unLocated = Word _base}
                : badRight
                : _ ->
                    malformedAt badRight
            [ Located{unLocated = InvisibleBraceL}
              , Located{unLocated = Word _base}
              ] ->
                    malformedAt commandToken
            [Located{unLocated = InvisibleBraceL}] ->
                malformedAt commandToken
            Located{unLocated = InvisibleBraceL}
                : badWord
                : _ ->
                    malformedAt badWord
            badLeft : _ ->
                malformedAt badLeft
            [] ->
                malformedAt commandToken

    malformedAt token =
        Left
            (InvalidVerbMetadata
                (startPos token)
                MalformedVerbBasePayload)

extractLexiconItemsFromPreparedChunk
    :: Maybe Text
    -> [Located Token]
    -> Either LexiconExtractionError [Located ExtractedLexiconItem]
extractLexiconItemsFromPreparedChunk explicitBase ltoks =
    case ltoks of
        first@Located{startPos = pos, unLocated = BeginEnv "definition"} : _ ->
            locateAt first
                <$> (matchOrErr (definition pos explicitBase ltoks) "definition" pos >>= id)
        first@Located{startPos = pos, unLocated = BeginEnv "signature"} : _ ->
            locateAt first
                <$> (matchOrErr (signatureExtension pos) "signature" pos >>= id)
        first@Located{startPos = pos, unLocated = BeginEnv "abbreviation"} : _ ->
            locateAt first
                <$> (matchOrErr (abbreviation pos explicitBase ltoks) "abbreviation" pos >>= id)
        first@Located{startPos = pos, unLocated = BeginEnv "struct"} : _ ->
            do
                noun <- matchOrErr structRE "struct definition" pos
                fields <- Bifunctor.first InvalidStructureFieldEnvelope (structureFieldEnvelopes ltoks)
                pure ((noun <$ first) : map extractField fields)
        first@Located{startPos = pos, unLocated = BeginEnv "instance"} : _ ->
            locateAt first
                <$> (matchOrErr instanceRE "instance" pos >>= id)
        first@Located{startPos = pos, unLocated = BeginEnv "construction"} : _ ->
            locateAt first
                <$> (matchOrErr (constructionRE pos) "construction" pos >>= id)
        first@Located{startPos = pos, unLocated = BeginEnv "inductive"} : _ ->
            locateAt first
                <$> (matchOrErr (inductive pos) "inductive definition" pos >>= id)
        Located{startPos = pos, unLocated = BeginEnv "datatype"} : _ ->
            extractDatatypeLexiconItemsFromChunk pos ltoks
        Located{startPos = pos, unLocated = BeginEnv "recursive-definition"} : _ ->
            extractRecursionLexiconItem pos ltoks
        _ ->
            Right []
  where
    toks = unLocated <$> ltoks
    matchOrErr
        :: RE Token a
        -> Text
        -> Location
        -> Either LexiconExtractionError a
    matchOrErr re environment location =
        case RE.match re toks of
            Nothing ->
                Left
                    (MalformedLexicalEnvironment
                        location
                        environment)
            Just result ->
                Right result

    locateAt first items =
        [item <$ first | item <- items]

data ExtractedLexiconItem
    = ExtractedAdjective LexicalPhrase Marker
    | ExtractedFunctionPhrase LexicalPhrase Marker
    | ExtractedNoun LexicalPhrase Marker
    | ExtractedStructureNoun LexicalPhrase Marker
    | ExtractedVerb VerbSurfaces Marker
    | ExtractedRelationSymbol Token ParameterArity Marker
    | ExtractedFunctionSymbol Pattern Marker
    | ExtractedTypedConstant Token ConcreteType Marker
    | ExtractedPrefixPredicate PrefixPredicate Marker
    | ExtractedStructureOperation Text -- we an use the command text as export name.
    deriving (Show, Eq, Ord)

extractedItemMarker :: ExtractedLexiconItem -> Marker
extractedItemMarker = \case
    ExtractedAdjective _item marker ->
        marker
    ExtractedFunctionPhrase _item marker ->
        marker
    ExtractedNoun _item marker ->
        marker
    ExtractedStructureNoun _item marker ->
        marker
    ExtractedVerb _item marker ->
        marker
    ExtractedRelationSymbol _token _arity marker ->
        marker
    ExtractedFunctionSymbol _pattern marker ->
        marker
    ExtractedTypedConstant _token _coreType marker ->
        marker
    ExtractedPrefixPredicate _predicate marker ->
        marker
    ExtractedStructureOperation commandText ->
        Marker commandText

canonicalExtractedItem
    :: Fixity
    -> ExtractedLexiconItem
    -> CanonicalLexicalEntry
canonicalExtractedItem fixity = \case
    ExtractedAdjective phrase marker ->
        let side =
                if isAdjR phrase
                    then RightAdjectiveSide
                    else LeftAdjectiveSide
            pat = patternFromHoley phrase
            matchesIntrinsic item =
                adjectiveLexicalSide item == side
                    && adjectiveLexicalPattern item == pat
                    && adjectiveLexicalMarker item == Just marker
        in
            case List.filter matchesIntrinsic
                    (lexiconAdjLs builtins <> lexiconAdjRs builtins) of
                [_intrinsic] ->
                    CanonicalIntrinsicAdjective side pat marker
                [] ->
                    CanonicalUserAdjective
                        side
                        (AdjectiveSurfaceKey pat)
                _ ->
                    impossible
                        "fixed adjectives duplicate one intrinsic identity"
    ExtractedFunctionPhrase phrase marker ->
        canonicalSgPl
            CanonicalFunctionPhrase
            (guessNounPlural phrase)
            marker
    ExtractedNoun phrase marker ->
        canonicalSgPl
            CanonicalNoun
            (guessNounPlural phrase)
            marker
    ExtractedStructureNoun phrase marker ->
        canonicalSgPl
            CanonicalStructureNoun
            (guessNounPlural phrase)
            marker
    ExtractedVerb surfaces marker ->
        CanonicalVerb surfaces marker
    ExtractedRelationSymbol token arity marker ->
        CanonicalRelation token arity marker
    ExtractedFunctionSymbol pat marker ->
        CanonicalExpressionFunction
            (if pat == tupleSurfacePattern
                then mixfixPattern PairSymbol
                else pat)
            marker
            fixity
    ExtractedTypedConstant token coreType marker ->
        CanonicalTypedConstant token coreType marker
    ExtractedPrefixPredicate
            (PrefixPredicate commandText arity)
            marker ->
        CanonicalPrefixPredicate
            commandText
            (fromIntegral arity)
            marker
    ExtractedStructureOperation commandText ->
        CanonicalStructureOperation commandText
  where
    canonicalSgPl constructor phrases marker =
        constructor
            (patternFromHoley (sg phrases))
            (patternFromHoley (pl phrases))
            marker

data SyntaxMaterializationError
    = MaterializedSyntaxCollision !CanonicalSyntaxCollision
    | PrefixPredicateArityOutOfRange !Natural
    deriving (Show, Eq)

materializeSyntaxDelta
    :: CanonicalSyntaxDelta
    -> Either SyntaxMaterializationError Lexicon
materializeSyntaxDelta delta = do
    combined <-
        Bifunctor.first MaterializedSyntaxCollision
            (canonicalSyntaxDelta
                (fixedBaseSyntaxEntries
                    <> canonicalSyntaxDeltaEntries delta))
    foldM
        insertCanonicalEntry
        builtins
        [ entry
        | entry <- canonicalSyntaxDeltaEntries combined
        , entry `Set.notMember` fixedEntries
        ]
  where
    fixedEntries =
        Set.fromList fixedBaseSyntaxEntries

data EffectiveSyntaxError
    = EffectiveSyntaxInputMissing !SyntaxInterfaceId
    | EffectiveSyntaxCollision !CanonicalSyntaxCollision
    | EffectiveSyntaxMaterialization !SyntaxMaterializationError
    deriving (Show, Eq)

renderEffectiveSyntaxError :: EffectiveSyntaxError -> Text
renderEffectiveSyntaxError = \case
    EffectiveSyntaxInputMissing identity ->
        "effective syntax is missing input " <> Text.pack (show identity)
    EffectiveSyntaxCollision collision ->
        "effective syntax has conflicting entries for pattern "
            <> Text.pack (show (canonicalCollisionPattern collision))
    EffectiveSyntaxMaterialization failure ->
        "effective syntax could not be materialized: "
            <> Text.pack (show failure)

-- | Reconstruct the complete syntax visible through a module interface. The
-- caller supplies interfaces by their asserted identities; diamond imports
-- are folded once and no filesystem state is consulted.
effectiveSyntaxDelta
    :: Map SyntaxInterfaceId ModuleSyntaxInterface
    -> ModuleSyntaxInterface
    -> Either EffectiveSyntaxError CanonicalSyntaxDelta
effectiveSyntaxDelta supplied root = do
    (_visited, entries) <- collect Set.empty root
    Bifunctor.first EffectiveSyntaxCollision
        (canonicalSyntaxDelta entries)
  where
    collect visited interface
        | identity `Set.member` visited =
            Right (visited, [])
        | otherwise = do
            (withInputs, importedEntries) <-
                foldM collectInput
                    (Set.insert identity visited, [])
                    (moduleSyntaxDirectInputs interface)
            pure
                ( withInputs
                , importedEntries
                    <> canonicalSyntaxDeltaEntries
                        (moduleSyntaxLocalDelta interface)
                )
      where
        identity = moduleSyntaxAssertedId interface

    collectInput (visited, entries) identity =
        case Map.lookup identity supplied of
            Nothing ->
                Left (EffectiveSyntaxInputMissing identity)
            Just interface -> do
                (withInput, inputEntries) <- collect visited interface
                pure (withInput, entries <> inputEntries)

materializeEffectiveSyntax
    :: Map SyntaxInterfaceId ModuleSyntaxInterface
    -> ModuleSyntaxInterface
    -> Either EffectiveSyntaxError Lexicon
materializeEffectiveSyntax supplied root = do
    delta <- effectiveSyntaxDelta supplied root
    Bifunctor.first EffectiveSyntaxMaterialization
        (materializeSyntaxDelta delta)

insertCanonicalEntry
    :: Lexicon
    -> CanonicalLexicalEntry
    -> Either SyntaxMaterializationError Lexicon
insertCanonicalEntry lexicon@Lexicon{..} entry = do
    extended <- case entry of
        CanonicalUserAdjective side (AdjectiveSurfaceKey pat) ->
            case side of
                LeftAdjectiveSide ->
                    pure
                        lexicon
                            { lexiconAdjLs =
                                userAdjectiveLexicalItem side pat
                                    : lexiconAdjLs
                            }
                RightAdjectiveSide ->
                    pure
                        lexicon
                            { lexiconAdjRs =
                                userAdjectiveLexicalItem side pat
                                    : lexiconAdjRs
                            }
        CanonicalIntrinsicAdjective side pat marker ->
            case side of
                LeftAdjectiveSide ->
                    pure
                        lexicon
                            { lexiconAdjLs =
                                intrinsicAdjectiveLexicalItem side pat marker
                                    : lexiconAdjLs
                            }
                RightAdjectiveSide ->
                    pure
                        lexicon
                            { lexiconAdjRs =
                                intrinsicAdjectiveLexicalItem side pat marker
                                    : lexiconAdjRs
                            }
        CanonicalFunctionPhrase singular plural marker ->
            pure
                lexicon
                    { lexiconFuns =
                        lexicalItemSgPl singular plural marker
                            : lexiconFuns
                    }
        CanonicalNoun singular plural marker ->
            pure
                lexicon
                    { lexiconNouns =
                        lexicalItemSgPl singular plural marker
                            : lexiconNouns
                    }
        CanonicalStructureNoun singular plural marker ->
            pure
                lexicon
                    { lexiconStructNouns =
                        lexicalItemSgPl singular plural marker
                            : lexiconStructNouns
                    }
        CanonicalVerb surfaces marker ->
            pure
                lexicon
                    { lexiconVerbs =
                        VerbLexicalItem surfaces marker
                            : lexiconVerbs
                    }
        CanonicalRelation token arity marker ->
            pure
                lexicon
                    { lexiconRelationSymbols =
                        RelationSymbol token arity marker
                            : lexiconRelationSymbols
                    }
        CanonicalExpressionFunction
                pat
                marker
                (Fixity associativity level) ->
            pure
                lexicon
                    { lexiconMixfixTable =
                        Seq.adjust
                            (Map.insert
                                pat
                                (MixfixItem
                                    pat
                                    marker
                                    associativity))
                            (fromIntegral
                                (mixfixLevelValue level))
                            lexiconMixfixTable
                        }
        CanonicalTypedConstant token coreType _marker ->
            pure
                lexicon
                    { lexiconTypedConstants =
                        (token, coreType) : lexiconTypedConstants
                    }
        CanonicalPrefixPredicate commandText arity marker -> do
            runtimeArity <-
                if arity <= fromIntegral (maxBound :: Int)
                    then pure (fromIntegral arity)
                    else
                        Left
                            (PrefixPredicateArityOutOfRange arity)
            pure
                lexicon
                    { lexiconPrefixPredicates =
                        (PrefixPredicate commandText runtimeArity, marker)
                            : lexiconPrefixPredicates
                    }
        CanonicalStructureOperation commandText ->
            pure
                lexicon
                    { lexiconStructFun =
                        StructSymbol commandText : lexiconStructFun
                    }
    pure extended
  where
    lexicalItemSgPl singular plural marker =
        mkLexicalItemSgPl
            (SgPl
                (patternToHoley singular)
                (patternToHoley plural))
            marker

skipUntilNextLexicalEnv :: RE Token [Token]
skipUntilNextLexicalEnv = many (RE.psym otherToken)
    where
        otherToken tok = tok /= BeginEnv "definition" && tok /= BeginEnv "struct" && tok /= BeginEnv "abbreviation"

notEndOfLexicalEnvToken :: RE Token Token
notEndOfLexicalEnvToken = RE.psym innerToken
    where
        innerToken tok = tok /= EndEnv "definition" && tok /= EndEnv "struct" && tok /= EndEnv "abbreviation"

notEndOfSignatureSentenceToken :: RE Token Token
notEndOfSignatureSentenceToken = RE.psym \case
    Symbol "." -> False
    EndEnv "signature" -> False
    _ -> True

definition
    :: Location
    -> Maybe Text
    -> [Located Token]
    -> RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
definition location explicitBase locatedTokens = do
    RE.sym (BeginEnv "definition")
    RE.few notEndOfLexicalEnvToken
    m <- labelRE
    RE.few RE.anySym
    lexicalItem <- headRE location explicitBase locatedTokens
    RE.few RE.anySym
    RE.sym (EndEnv "definition")
    skipUntilNextLexicalEnv
    pure ((: []) <$> lexicalItem m)

abbreviation
    :: Location
    -> Maybe Text
    -> [Located Token]
    -> RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
abbreviation location explicitBase locatedTokens = do
    RE.sym (BeginEnv "abbreviation")
    RE.few RE.anySym
    m <- labelRE
    RE.few RE.anySym
    lexicalItem <- headRE location explicitBase locatedTokens
    RE.few RE.anySym
    RE.sym (EndEnv "abbreviation")
    skipUntilNextLexicalEnv
    pure ((: []) <$> lexicalItem m)

signatureExtension
    :: Location
    -> RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
signatureExtension location = do
    RE.sym (BeginEnv "signature")
    RE.few notEndOfLexicalEnvToken
    m <- labelRE
    RE.few RE.anySym
    lexicalItem <- sigHeadRE location
    RE.few notEndOfSignatureSentenceToken
    RE.sym (Symbol ".")
    RE.sym (EndEnv "signature")
    skipUntilNextLexicalEnv
    pure ((: []) <$> lexicalItem m)

-- Structure declaration phrases place their object slot before every
-- parameter hole.  Consequently the first math atom after "the" is the
-- atomic instance name in both supported surfaces:
--
--   The topological space $T = \structure{...}$.
--   The left module $M$ over $R$ is $\structure{...}$.
--
-- Register it as a concrete Set constant.  This avoids treating a bare
-- variable-shaped name as a recursive mixfix function pattern.
instanceRE
    :: RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
instanceRE = do
    RE.sym (BeginEnv "instance")
    RE.few RE.anySym
    marker <- labelRE
    RE.few RE.anySym
    the
    RE.few (RE.psym (/= BeginEnv "math"))
    beginMath
    constantToken <- typedConstantTokenRE
    RE.few RE.anySym
    RE.sym (EndEnv "instance")
    skipUntilNextLexicalEnv
    pure (Right [ExtractedTypedConstant constantToken ConcreteSet marker])

constructionRE :: Location -> RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
constructionRE location = do
    RE.sym (BeginEnv "construction")
    RE.few RE.anySym
    marker <- labelRE
    RE.few RE.anySym
    the
    RE.few (RE.psym (/= BeginEnv "math"))
    patternResult <- functionSymbolRE location
    RE.few RE.anySym
    RE.sym (EndEnv "construction")
    skipUntilNextLexicalEnv
    pure ((\pattern' -> [ExtractedFunctionSymbol pattern' marker]) <$> patternResult)

labelRE :: RE Token Marker
labelRE = RE.msym \case
    Label m -> Just (Marker m)
    _ -> Nothing

-- | 'RE' that matches the head of a definition.
headRE
    :: Location
    -> Maybe Text
    -> [Located Token]
    -> RE Token (Marker -> Either LexiconExtractionError ExtractedLexiconItem)
-- Note that @<|>@ is left biased for 'RE', so we can just
-- place 'adj' before 'verb' and do not have to worry about
-- overlapping patterns.
headRE location explicitBase locatedTokens =
        extractTypedConstant <$> typedConstantDefinitionRE
    <|> makeExtractedItem ExtractedNoun <$> nounRE
    <|> makeExtractedItem ExtractedAdjective <$> adjRE
    <|> extractVerb <$> verbRE
    <|> makeExtractedItem ExtractedFunctionPhrase <$> funRE
    <|> extractRelationSymbol <$> relationSymbolRE
    <|> extractFunctionSymbol <$> functionSymbolRE location
    <|> makeExtractedItem ExtractedPrefixPredicate <$> prefixPredicate
  where
    extractTypedConstant (token, typeTokens) marker = do
        coreType <- parseConcreteTypeTokens location typeTokens
        Right (ExtractedTypedConstant token coreType marker)

    makeExtractedItem constructor value marker =
        Right (constructor value marker)

    extractVerb phrase marker =
        Bifunctor.first
            (InvalidVerbSurfaces
                (verbSurfaceLocation location phrase locatedTokens))
            (ExtractedVerb
                <$> deriveVerbSurfaces explicitBase phrase
                <*> pure marker)

    extractRelationSymbol (token, arity) marker =
        Right (ExtractedRelationSymbol token arity marker)

    extractFunctionSymbol patternResult marker =
        (`ExtractedFunctionSymbol` marker) <$> patternResult

verbSurfaceLocation
    :: Location
    -> LexicalPhrase
    -> [Located Token]
    -> Location
verbSurfaceLocation fallback phrase tokens =
    case phrase of
        Just leading : _ ->
            maybe fallback startPos
                (List.find ((== leading) . unLocated) tokens)
        _ -> fallback

sigHeadRE
    :: Location
    -> RE Token (Marker -> Either LexiconExtractionError ExtractedLexiconItem)
sigHeadRE location =
    extractTypedConstant <$> typedConstantSignatureRE
    <|> asum
        [ signatureHeadRE form
        | form <- concreteSignatureHeadForms
        ]
  where
    extractTypedConstant (token, typeTokens) marker = do
        coreType <- parseConcreteTypeTokens location typeTokens
        Right (ExtractedTypedConstant token coreType marker)

    signatureHeadRE = \case
        AdjectiveSignatureHead ->
            makeExtractedItem ExtractedAdjective <$> sigAdjectiveRE
        SymbolicSignatureHead ->
            extractFunctionSymbol <$> sigFunctionSymbolRE location

    makeExtractedItem constructor value marker =
        Right (constructor value marker)

    extractFunctionSymbol patternResult marker =
        (`ExtractedFunctionSymbol` marker) <$> patternResult

typedConstantSignatureRE :: RE Token (Token, [Token])
typedConstantSignatureRE = math do
    token <- typedConstantTokenRE
    RE.sym (Symbol ":")
    typeTokens <- RE.some concreteTypeSurfaceRE
    pure (token, typeTokens)

typedConstantDefinitionRE :: RE Token (Token, [Token])
typedConstantDefinitionRE = do
    RE.sym (BeginEnv "math")
    token <- typedConstantTokenRE
    RE.sym (Symbol ":")
    typeTokens <- RE.some concreteTypeSurfaceRE
    RE.sym (Symbol "=")
    pure (token, typeTokens)

typedConstantTokenRE :: RE Token Token
typedConstantTokenRE = RE.psym \case
    Variable{} -> True
    Command{} -> True
    _ -> False

-- Lexicon extraction is based on regular expressions.  Concrete types are
-- recursive (parentheses may nest), so recognizing them recursively as an
-- 'RE' makes automaton construction diverge.  Capture their finite token
-- alphabet here and parse it deterministically below instead.
concreteTypeSurfaceRE :: RE Token Token
concreteTypeSurfaceRE = RE.psym isConcreteTypeSurfaceToken

isConcreteTypeSurfaceToken :: Token -> Bool
isConcreteTypeSurfaceToken = \case
    Command "Set" -> True
    Command "Prop" -> True
    Command "to" -> True
    ParenL -> True
    ParenR -> True
    _ -> False

parseConcreteTypeTokens
    :: Location
    -> [Token]
    -> Either LexiconExtractionError ConcreteType
parseConcreteTypeTokens location tokens =
    case parseArrow tokens of
        Just (coreType, []) -> Right coreType
        _ -> Left (MalformedLexicalEnvironment location "concrete type")
  where
    parseArrow input = do
        (domain, rest) <- parseAtom input
        case rest of
            Command "to" : codomainTokens -> do
                (codomain, trailing) <- parseArrow codomainTokens
                pure (ConcreteArrow domain codomain, trailing)
            _ -> pure (domain, rest)

    parseAtom = \case
        Command "Set" : rest -> Just (ConcreteSet, rest)
        Command "Prop" : rest -> Just (ConcreteProp, rest)
        ParenL : rest -> do
            (coreType, afterType) <- parseArrow rest
            case afterType of
                ParenR : trailing -> Just (coreType, trailing)
                _ -> Nothing
        _ -> Nothing

sigAdjectiveRE :: RE Token LexicalPhrase
sigAdjectiveRE =
    toLexicalPhrase
        <$> ( math var
                *> RE.sym (Word "can")
                *> RE.sym (Word "be")
                *> RE.some
                    (RE.psym isLexicalPhraseToken <|> math var)
            )

sigFunctionSymbolRE :: Location -> RE Token (Either LexiconExtractionError Pattern)
sigFunctionSymbolRE location = do
    RE.sym (BeginEnv "math")
    toks <- RE.few nonDefinitionKeyword
    RE.sym (EndEnv "math")
    pure (makeFunctionSymbol location toks)

inductive
    :: Location
    -> RE Token (Either LexiconExtractionError [ExtractedLexiconItem])
inductive location = do
    RE.sym (BeginEnv "inductive")
    RE.few notEndOfLexicalEnvToken
    m <- labelRE
    RE.few RE.anySym
    lexicalItem <- functionSymbolInductive location
    RE.few RE.anySym
    RE.sym (EndEnv "inductive")
    skipUntilNextLexicalEnv
    pure (((: []) . (`ExtractedFunctionSymbol` m)) <$> lexicalItem)

-- The head fixes the notation; the first equation determines its result kind.
-- Later clauses are parsed with that same notation and checked as one family.
extractRecursionLexiconItem
    :: Location -> [Located Token]
    -> Either LexiconExtractionError [Located ExtractedLexiconItem]
extractRecursionLexiconItem location tokens = do
    marker <- require "missing declaration label" (findDatatypeLabel tokens)
    headTokens <- require "missing symbolic head after Define" (findDatatypeHead tokens)
    clauses <- require "missing clause enumeration" (findDatatypeConstructors tokens)
    (_, firstClause) <- require "missing clause" (listToMaybe clauses)
    mathStart <- require "missing clause equation" (tailMay =<< dropUntil ((== BeginEnv "math") . unLocated) firstClause)
    mathBody <- require "unclosed clause equation" (takeUntilToken (EndEnv "math") mathStart)
    item <- if Symbol "=" `elem` (unLocated <$> mathBody)
        then (`ExtractedFunctionSymbol` marker) <$> makeFunctionSymbol location (unLocated <$> headTokens)
        else do
            predicate <- require "a predicate head must be a prefix command with variable arguments"
                (RE.match prefixPredicate ([BeginEnv "math"] <> (unLocated <$> headTokens) <> [EndEnv "math", Word "iff"]))
            pure (ExtractedPrefixPredicate predicate marker)
    pure [item <$ locationTemplate location tokens]
  where
    require :: Text -> Maybe a -> Either LexiconExtractionError a
    require message = maybe (Left (MalformedRecursion location message)) Right

extractDatatypeLexiconItemsFromChunk
    :: Location
    -> [Located Token]
    -> Either LexiconExtractionError [Located ExtractedLexiconItem]
extractDatatypeLexiconItemsFromChunk = extractDatatypeLexiconItems

extractDatatypeLexiconItems
    :: Location
    -> [Located Token]
    -> Either LexiconExtractionError [Located ExtractedLexiconItem]
extractDatatypeLexiconItems environmentLocation toks = do
    marker <- requireDatatype
        environmentLocation
        "missing declaration label"
        (findDatatypeLabel toks)
    datatypeHeadToks <- requireDatatype
        environmentLocation
        "missing datatype head"
        (findDatatypeHead toks)
    constructorToks <- requireDatatype
        environmentLocation
        "missing constructor enumeration"
        (findDatatypeConstructors toks)
    let datatypeLocation =
            maybe environmentLocation startPos (listToMaybe datatypeHeadToks)
    datatypePattern <- makeFunctionSymbol
        datatypeLocation
        (unLocated <$> datatypeHeadToks)
    constructorItems <- traverse makeConstructor constructorToks
    pure
        ((ExtractedFunctionSymbol datatypePattern marker
            <$ locationTemplate datatypeLocation toks)
            : constructorItems)
  where
    makeConstructor (itemLocation, raw) = do
        constructorToks <- requireDatatype
            itemLocation
            "constructor item has no symbolic declaration"
            (itemConstructorToks raw)
        let stripped = stripOuterParens constructorToks
        (markerToken, marker) <- constructorMarker itemLocation stripped
        constructorPattern <- makeFunctionSymbol
            (startPos markerToken)
            (unLocated <$> stripped)
        pure
            (ExtractedFunctionSymbol
                constructorPattern
                marker
                <$ markerToken)

requireDatatype
    :: Location
    -> Text
    -> Maybe a
    -> Either LexiconExtractionError a
requireDatatype location problem =
    maybe (Left (MalformedDatatype location problem)) Right

locationTemplate :: Location -> [Located Token] -> Located Token
locationTemplate location = \case
    token : _ ->
        token{startPos = location}
    [] ->
        impossible "datatype lexicon extractor has no environment token"

findDatatypeLabel :: [Located Token] -> Maybe Marker
findDatatypeLabel = \case
    [] -> Nothing
    Located{unLocated = Label m} : _ -> Just (Marker m)
    _ : toks -> findDatatypeLabel toks

findDatatypeHead :: [Located Token] -> Maybe [Located Token]
findDatatypeHead toks = do
    afterLabel <- tailMay =<< dropUntil (isLabel . unLocated) toks
    defineToks <- dropUntil ((== Word "define") . unLocated) afterLabel
    case defineToks of
        _define : Located{unLocated = BeginEnv "math"} : rest ->
            takeUntilToken (EndEnv "math") rest
        _ -> Nothing

findDatatypeConstructors
    :: [Located Token]
    -> Maybe [(Location, [Located Token])]
findDatatypeConstructors toks = do
    afterEnumerate <- tailMay
        =<< dropUntil ((== BeginEnv "enumerate") . unLocated) toks
    enumerateBody <- takeUntilToken (EndEnv "enumerate") afterEnumerate
    let items = splitDatatypeItems enumerateBody
    guard (not (null items))
    pure items

splitDatatypeItems
    :: [Located Token]
    -> [(Location, [Located Token])]
splitDatatypeItems = \case
    [] ->
        []
    Located{startPos = itemLocation, unLocated = itemToken} : rest | isItem itemToken ->
        let (item, remaining) =
                break (isItem . unLocated) rest
        in (itemLocation, item) : splitDatatypeItems remaining
    _ : rest ->
        splitDatatypeItems rest
  where
    isItem (Command "item") = True
    isItem NamedItem{} = True
    isItem _ = False

itemConstructorToks :: [Located Token] -> Maybe [Located Token]
itemConstructorToks toks = do
    afterMath <- tailMay =<< dropUntil ((== BeginEnv "math") . unLocated) toks
    mathBody <- takeUntilToken (EndEnv "math") afterMath
    takeUntilToken (Command "in") mathBody

constructorMarker
    :: Location
    -> [Located Token]
    -> Either LexiconExtractionError (Located Token, Marker)
constructorMarker fallback tokens =
    maybe
        (Left
            (MalformedDatatype
                fallback
                "constructor has no marker-bearing head token"))
        Right
        (firstMarker tokens)
  where
    firstMarker = \case
        [] -> Nothing
        token : remaining ->
            case tokenMarker (unLocated token) of
                Just marker -> Just (token, marker)
                Nothing -> firstMarker remaining

stripOuterParens :: [Located Token] -> [Located Token]
stripOuterParens toks
    | hasOuterParens toks = case toks of
        Located{unLocated = ParenL} : rest -> case reverse rest of
            Located{unLocated = ParenR} : innerRev -> reverse innerRev
            _ -> toks
        _ -> toks
    | otherwise = toks

hasOuterParens :: [Located Token] -> Bool
hasOuterParens = \case
    Located{unLocated = ParenL} : rest -> go (1 :: Int) rest
    _ -> False
    where
        go _ [] = False
        go depth [Located{unLocated = ParenR}] = depth == 1
        go depth (Located{unLocated = ParenL} : rest) =
            go (depth + 1) rest
        go depth (Located{unLocated = ParenR} : rest)
            | depth <= 0 = False
            | otherwise = go (depth - 1) rest
        go depth (_ : rest) = go depth rest

isLabel :: Token -> Bool
isLabel = \case
    Label _ -> True
    _ -> False

dropUntil :: (a -> Bool) -> [a] -> Maybe [a]
dropUntil predicate = \case
    [] -> Nothing
    xs@(x : rest)
        | predicate x -> Just xs
        | otherwise -> dropUntil predicate rest

takeUntilToken :: Token -> [Located Token] -> Maybe [Located Token]
takeUntilToken stop = \case
    [] -> Nothing
    x : xs
        | unLocated x == stop -> Just []
        | otherwise -> (x :) <$> takeUntilToken stop xs

tailMay :: [a] -> Maybe [a]
tailMay = \case
    [] -> Nothing
    _ : xs -> Just xs

extractField :: FieldEnvelope -> Located ExtractedLexiconItem
extractField envelope =
    let token = fieldEnvelopeCommand envelope
    in ExtractedStructureOperation <$> token

structRE :: RE Token ExtractedLexiconItem
structRE = do
    RE.sym (BeginEnv "struct")
    RE.few RE.anySym
    m <- labelRE
    RE.few RE.anySym
    lexicalItem <- do
        prefix <- an *> structPat
        math var
        suffix <- patRE
        pure (ExtractedStructureNoun (toLexicalPhrase (prefix <> suffix)))
    RE.few RE.anySym
    RE.sym (EndEnv "struct")
    skipUntilNextLexicalEnv
    pure (lexicalItem m)

nounRE :: RE Token LexicalPhrase
nounRE = toLexicalPhrase <$> (math var *> is *> an *> patRE <* iff)

adjRE :: RE Token LexicalPhrase
adjRE = toLexicalPhrase <$> (math var *> is *> patRE <* iff)

verbRE :: RE Token LexicalPhrase
verbRE = toLexicalPhrase <$> (math var *> verbPatRE <* iff)

funRE :: RE Token LexicalPhrase
funRE = toLexicalPhrase <$> (the *> patRE <* (is <|> comma))

relationSymbolRE :: RE Token (Token, ParameterArity)
relationSymbolRE = do
    beginMath
    var
    rel <- symbol
    k <- params
    var
    endMath
    iff
    pure (rel, k)
        where
        params :: RE Token ParameterArity
        params = do
            vars <- many (RE.sym InvisibleBraceL *> var <* RE.sym InvisibleBraceR)
            pure (parameterArityOf vars)

functionSymbolRE
    :: Location
    -> RE Token (Either LexiconExtractionError Pattern)
functionSymbolRE location = do
    RE.sym (BeginEnv "math")
    toks <- RE.few nonDefinitionKeyword
    RE.sym (Symbol "=")
    pure (makeFunctionSymbol location toks)

makeFunctionSymbol
    :: Location
    -> [Token]
    -> Either LexiconExtractionError Pattern
makeFunctionSymbol location = \case
    [] ->
        Left (InvalidFunctionPattern location FunctionPatternEmpty)
    [Variable _] ->
        Left (InvalidFunctionPattern location FunctionPatternBareVariable)
    [Variable _, ParenL, Variable _, ParenR] ->
        Left
            (InvalidFunctionPattern
                location
                FunctionPatternReservedApplication)
    toks ->
        Right (patternFromHoley (fromToken <$> toks))
    where
        fromToken = \case
            Variable _ -> Nothing -- Variables become slots.
            tok -> Just tok -- Everything else is part of the pattern.

functionPatternErrorMessage :: FunctionPatternError -> String
functionPatternErrorMessage = \case
    FunctionPatternEmpty ->
        "malformed function pattern: no pattern"
    FunctionPatternBareVariable ->
        "malformed function pattern: a bare variable would cause infinite left recursion"
    FunctionPatternReservedApplication ->
        "malformed function pattern: _(_) is reserved for set-theoretic function application"

functionSymbolInductive
    :: Location
    -> RE Token (Either LexiconExtractionError Pattern)
functionSymbolInductive location = do
    RE.sym (BeginEnv "math")
    toks <- RE.few nonDefinitionKeyword
    RE.sym (Command "subseteq")
    pure (makeFunctionSymbol location toks)

prefixPredicate :: RE Token PrefixPredicate
prefixPredicate = math prfx <* iff
    where
        prfx = do
            r <- command
            args <- many (RE.sym InvisibleBraceL *> var <* RE.sym InvisibleBraceR)
            pure (PrefixPredicate r (length args))


command :: RE Token Text
command = RE.msym \case
    Command cmd -> Just cmd
    _ -> Nothing

var :: RE Token Token
var = RE.psym isVar


nonDefinitionKeyword :: RE Token Token
nonDefinitionKeyword = RE.psym (`notElem` keywords)
    where
        keywords =
            [ Word "if"
            , Word "iff"
            , Symbol "="
            , Command "iff"
            , BeginEnv "math"
            , EndEnv "math"
            ]


patRE :: RE Token [Token]
patRE = many (RE.psym isLexicalPhraseToken <|> math var)

verbPatRE :: RE Token [Token]
verbPatRE = many (RE.psym isVerbLexicalPhraseToken <|> math var)

structPat :: RE Token [Token]
structPat = many (RE.psym isLexicalPhraseToken)

beginMath, endMath :: RE Token ()
beginMath = void (RE.sym (BeginEnv "math"))
endMath = void (RE.sym (EndEnv "math"))

math :: RE Token a -> RE Token a
math re = beginMath *> re <* endMath

-- | We allow /conditional perfection/: the first /@if@/ in a definition is interpreted as /@iff@/.
iff :: RE Token ()
iff = void (RE.sym (Word "if")) -- Using @void@ is faster (only requires recognition).
    <|> void (RE.sym (Word "iff"))
    <|> void (RE.string [Word "if", Word "and", Word "only", Word "if"])
    <|> void (RE.sym (Word "denote"))
    <|> void (RE.sym (Word "stand") *> RE.sym (Word "for"))
{-# INLINE iff #-}

an :: RE Token ()
an = void (RE.sym (Word "a"))
    <|> void (RE.sym (Word "an"))
{-# INLINE an #-}

is :: RE Token ()
is = void (RE.sym (Word "is") <|> RE.sym (Word "denotes"))
{-# INLINE is #-}

the :: RE Token ()
the = void (RE.sym (Word "the"))
{-# INLINE the #-}

comma :: RE Token ()
comma = void (RE.sym (Symbol ","))
{-# INLINE comma #-}


isVar :: Token -> Bool
isVar = \case
    Variable _ -> True
    _token -> False

isLexicalPhraseToken :: Token -> Bool
isLexicalPhraseToken = \case
    Word w -> w `Set.notMember` keywords
    --
    -- Simple commands (outside of math-mode) are allowed. This is useful
    -- for defining lexical phrases containing symbolic expressions such as
    -- `X is \Ttwo{}`, where `\Ttwo` is a macro that expands to `T_2`.
    -- We also allow these macros to take arguments, hence the need to
    -- allow grouping delimiters. They can also be used to escape the end
    -- of the command for correct spacing, as in the above example.
    --
    Command _cmd -> True
    InvisibleBraceL -> True
    InvisibleBraceR -> True
    --
    -- No other tokens may occur in lexical phrases. In particular, no `_dot`
    -- token may occur, limiting the lexical phrase to a single sentence.
    -- Commas occurring in variable lists should be placed
    -- within the math environment. Thus `$a,b$ are coprime iff`,
    -- not `$a$,`$b$` are coprime iff`.
    --
    _token -> False
    where
        keywords = Set.fromList ["a", "an", "is", "are", "if", "iff", "denote", "stand", "let"]

isVerbLexicalPhraseToken :: Token -> Bool
isVerbLexicalPhraseToken = \case
    Word "a" -> True
    Word "an" -> True
    token -> isLexicalPhraseToken token


toLexicalPhrase :: [Token] -> LexicalPhrase
toLexicalPhrase toks = component <$> toks
    where
        component = \case
            Variable _ -> Nothing
            tok        -> Just tok


symbol :: RE Token Token
symbol = RE.msym $ \tok -> case tok of
    Command _ -> Just tok
    Symbol _ -> Just tok
    _tok -> Nothing


-- | Basic paradigms for pluralizations of nominals.
guessNounPlural :: LexicalPhrase -> SgPl LexicalPhrase
guessNounPlural item = SgPl item (pluralize item)
    where
        pluralize :: LexicalPhrase -> LexicalPhrase
        pluralize phrase =
            case nominalHeadIndex phrase of
                Nothing -> phrase
                Just headIndex ->
                    [ if index == headIndex
                        then pluralizeComponent component
                        else component
                    | (index, component) <- zip [0 :: Int ..] phrase
                    ]

        nominalHeadIndex :: LexicalPhrase -> Maybe Int
        nominalHeadIndex phrase =
            fst <$> List.find (isWord . snd)
                (reverse (zip [0 :: Int ..] beforePreposition))
            where
                beforePreposition =
                    takeWhile
                        (not . maybe False isPreposition)
                        phrase

        isWord :: Maybe Token -> Bool
        isWord = \case
            Just Word{} -> True
            _ -> False

        pluralizeComponent :: Maybe Token -> Maybe Token
        pluralizeComponent = \case
            Just (Word word) -> Just (Word (pluralizeWord word))
            component -> component

        pluralizeWord :: Text -> Text
        pluralizeWord "datum" = "data"
        pluralizeWord word = Text.snoc word 's'

isAdjR :: LexicalPhrase -> Bool
isAdjR item = containsPreposition item || containsSlot item
    where
        containsPreposition, containsSlot :: LexicalPhrase -> Bool
        containsPreposition = any isPreposition . catMaybes
        containsSlot = (Nothing `elem`)

isPreposition :: Token -> Bool
isPreposition w = Set.member w (Set.map Word prepositions)
