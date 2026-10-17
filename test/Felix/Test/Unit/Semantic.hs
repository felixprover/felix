{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Semantic (unitTests) where

import Data.Either (isLeft)
import Data.Functor.Identity (runIdentity)
import Base
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.SourceTemplate qualified as SourceTemplate
import Felix.Report.Location (pattern Nowhere)
import Felix.Checking.Structure.Predicate qualified as Predicate
import Felix.Checking.Structure.Builtin qualified as Builtin
import Felix.Cache.Codec
import Felix.Math.Codec
import Felix.Module
import Felix.Parsed.Identity
import Felix.Source
import Felix.Source.Content
import Felix.Syntax.Interface qualified as Syntax
import Felix.Syntax.Abstract qualified as Raw

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.ByteString (ByteString)
import Data.ByteString qualified as Bytes
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "Semantic interfaces"
        [ testCase "separates syntax and semantic Merkle identities"
            separatesSyntaxAndSemantics
        , testCase "round-trips closed semantic declaration state"
            roundTripsSemanticState
        , testCase "includes structural purpose in exact occurrence identity"
            distinguishesStructurePurposes
        , testCase "round-trips exact semantic global keys"
            roundTripsSemanticGlobalKeys
        , testCase "owns relation notion identity and argument layout"
            ownsRelationNotionLayout
        , testCase "owns verb notion identity and argument layout"
            ownsVerbNotionLayout
        , testCase "owns prefix-predicate notion identity and role"
            ownsPrefixPredicateNotionRole
        , testCase "keys exact proof and module inputs"
            keysExactInputs
        , testCase "materializes formation contracts at their environment boundary"
            materializesFormationContracts
        , testCase "materializes abbreviation expansions at their binding"
            materializesAbbreviationExpansions
        , testCase "source templates keep typed endpoint slots separate from equal captures"
            instantiatesTypedSourceTemplates
        , testCase "classifies exact owner-bearing source providers"
            classifiesSourceProviders
        , testCase "round-trips the closed intrinsic provider identities"
            roundTripsIntrinsicProviderIdentities
        , testCase "round-trips the finite-set source provider identity"
            roundTripsFiniteSetProviderIdentity
        , testCase "round-trips persisted finite-evidence rules"
            roundTripsFiniteEvidenceRules
        , testCase "round-trips provider-result premise modes"
            roundTripsProviderResultPremiseModes
        , testCase "checks closed-value cache payloads at decoding and visible admission"
            checksClosedValuePayloads
        , testCase "normalizes registration families without changing within-family order"
            normalizesRegistrationOrder
        , testCase "bounds and rejects malformed fact-branch selectors"
            rejectsMalformedFactBranches
        , testCase "preserves template bytes and decoder work"
            preservesTemplateEncoding
        ]

preservesTemplateEncoding :: Assertion
preservesTemplateEncoding = do
    fixture <- makeFixture
    let slot = Semantic.declarationSlot (fixtureOwner fixture) (localDeclarationOrdinal 0)
        key = Semantic.SemanticPrefixPredicate "codec" 1
        head' = Semantic.PrefixPredicateNotionHead (Semantic.globalBindingRef slot key)
        structure = Identity.structureId
            (Identity.StructureOrigin (fixtureOwner fixture) (localDeclarationOrdinal 0) (structureSlot 0))
        -- Independent primitive-tag recipes, captured before codec consolidation.
        variable = putCacheTag 0 >> putCacheNatural 0
        nested = do
            putCacheTag 2
            putCacheTag 1
            putCacheTag 3
            putCacheList (const variable) [()]
            putCacheTag 3
            putCanonicalTermCache Identity.putObjectIdCache (Core.COpaqueInteger 7)
        atoms term =
            [ putCacheTag 0 >> Semantic.putGlobalNotionHeadCache head'
                >> putCacheList (const term) [()]
            , putCacheTag 1 >> Identity.putStructureIdCache structure
                >> putCacheList (const term) [()]
            , putCacheTag 2 >> term >> term
            , putCacheTag 3 >> putCacheList (const (pure ())) [] >> term
            ]
        premises atomWires = encodeCache do
            putCacheTag 1
            putCacheList (\wire -> putCacheTag 0 >> wire) atomWires
        environment = encodeCache do
            putCacheList (\() -> do
                Semantic.putSemanticGlobalKeyCache key
                putCacheText "codec"
                putCacheTag 0
                Identity.putObjectIdCache (Identity.intrinsicObjectId (fixtureTheory fixture) Core.Empty)
                putCacheTag 1
                putCacheTag 2
                putCacheList (\atom -> putCacheTag 0 >> atom) (atoms nested)
                putCacheTag 0 -- no abbreviation expansion
                putCacheTag 0) [()] -- no datatype description
            putCacheList (const (pure ())) []
        ruleBytes = premises (atoms nested)
    (rules, ruleUsage) <- expectRight
        (decodeCacheWithLimits standardDecoderLimits Semantic.getProviderResultPremisesCache ruleBytes)
    (bindings, formationUsage) <- expectRight
        (decodeCacheWithLimits standardDecoderLimits Semantic.getSemanticEnvironmentDeltaCache environment)
    encodeCache (Semantic.putProviderResultPremisesCache rules) @?= ruleBytes
    encodeCache (Semantic.putSemanticEnvironmentDeltaCache bindings) @?= environment
    let deltaBytes = encodeCache (Semantic.putDeclarationInterfaceDeltaCache (fixtureDelta fixture))
    (_, deltaUsage) <- expectRight
        (decodeCacheWithLimits standardDecoderLimits Semantic.getDeclarationInterfaceDeltaCache deltaBytes)
    -- The result wrapper has its own tags, in addition to the atom tags.
    case rules of
        Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles trees) ->
            for_ (zip (toList trees) (atoms (putCacheTag 0 >> nested))) \case
                (Semantic.RulePremiseAtom atom, wire) ->
                    encodeCache (Semantic.putResultNotionRuleTemplateCache
                        (fmap Semantic.ResultRuleTerm atom)) @?= encodeCache wire
                _ -> assertFailure "template fixture lost an atomic premise"
        _ -> assertFailure "template fixture lost its guarded forest"
    encodeCache (Semantic.putResultNotionRuleTemplateCache
        (Semantic.MembershipAtomTemplate Semantic.ResultRuleProviderValue
            Semantic.ResultRuleProviderValue)) @?= Bytes.pack [2,1,1]
    assertEqual "baseline template decoder usage"
        [ DecoderUsage 95 26 7 315 1 10 4
        , DecoderUsage 107 37 9 404 1 10 4
        , DecoderUsage 157 179 5 1110 0 13 2
        ]
        [ruleUsage, formationUsage, deltaUsage]
    let checkBoundary resource limits =
            case decodeCacheWithLimits limits Semantic.getProviderResultPremisesCache ruleBytes of
                Left (CacheResourceLimitExceeded failure) -> decoderLimitedResource failure @?= resource
                result -> assertFailure ("expected isolated decoder limit: " <> show result)
        nodes = decoderUsedNodes ruleUsage
        depth = decoderPeakDepth ruleUsage
    decodeCacheWithLimits (standardDecoderLimits {maximumDecoderNodes = nodes})
        Semantic.getProviderResultPremisesCache ruleBytes @?= Right (rules, ruleUsage)
    checkBoundary DecoderNodes (standardDecoderLimits {maximumDecoderNodes = nodes - 1})
    decodeCacheWithLimits (standardDecoderLimits {maximumDecoderDepth = depth})
        Semantic.getProviderResultPremisesCache ruleBytes @?= Right (rules, ruleUsage)
    checkBoundary DecoderDepth (standardDecoderLimits {maximumDecoderDepth = depth - 1})
    for_ [(putCacheTag 255, "rule-atom template"),
            (putCacheTag 2 >> putCacheTag 255, "rule-term template")] \(wire, label) ->
        case decodeCache Semantic.getProviderResultPremisesCache (premises [wire]) of
            Left (CacheBinaryDecodeError message) ->
                assertBool "unknown template tags retain their family label" (label `List.isInfixOf` message)
            result -> assertFailure ("expected unknown template tag: " <> show result)

distinguishesStructurePurposes :: Assertion
distinguishesStructurePurposes = do
    fixture <- makeFixture
    proposition <- expectRight
        (Identity.validatePropositionContent (fixtureClosure fixture)
            (Record.recordSchemaExactGraphLaw []))
    let owner = fixtureOwner fixture
        identity = Identity.structureId
            (Identity.StructureOrigin owner (localDeclarationOrdinal 0) (structureSlot 0))
        authority = Authority.factAuthority
            (Identity.theoremRef (fixtureTheory fixture) (Identity.checkedPropositionId proposition))
            Authority.cleanAuthoritySafety
        slot = Semantic.factSlot owner (localFactOrdinal 0)
        exactPurpose = Semantic.structureLawPurpose
            (Schema.StructureLawId identity (Schema.RecordSchemaLaw Record.RecordExactGraphLaw))
        projectionPurpose = Semantic.structureLawPurpose
            (Schema.StructureLawId identity (Schema.RecordSchemaLaw Record.RecordProjectionExtensionalityLaw))
        occurrence purpose = Semantic.semanticFactOccurrence purpose slot authority Semantic.SearchIneligible
    assertEqual "the empty laws share mathematical content"
        (Record.recordSchemaExactGraphLaw [] :: Core.CanonicalTerm Identity.ObjectId)
        (Record.recordSchemaProjectionExtensionalityLaw [])
    assertBool "distinct structural law keys remain distinct occurrences"
        (Semantic.semanticFactFingerprint (occurrence exactPurpose)
            /= Semantic.semanticFactFingerprint (occurrence projectionPurpose))
    assertBool "an ordinary theorem does not acquire structural purpose"
        (Semantic.semanticFactFingerprint (occurrence Semantic.GeneralFactPurpose)
            /= Semantic.semanticFactFingerprint (occurrence projectionPurpose))
    assertEqual "the actual purpose is retained" projectionPurpose
        (Semantic.semanticFactPurpose (occurrence projectionPurpose))

checksClosedValuePayloads :: Assertion
checksClosedValuePayloads = do
    fixture <- makeFixture
    let closure = fixtureClosure fixture
        typing = Identity.globalTypingFromClosure closure
        comprehension = Core.CApp (Core.CApp (Core.CIntrinsic Core.Sep) (Core.CIntrinsic Core.Empty))
            (Core.CLam Core.TySet (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)))
        -- An intentionally untrusted wire payload: no checked value constructor
        -- is used to manufacture these invalid semantic descriptions.
        encoded term = encodeCache do
            putCacheTag 1
            putCacheList (\() -> do
                putCacheTag 0
                putCacheTag 2
                putCacheTag 3
                putCanonicalTermCache Identity.putObjectIdCache term
                putCacheTag 0
                putCacheNatural 0) [()]
        decoded = decodeCache Semantic.getProviderResultPremisesCache . encoded
        extract term = do
            result <- expectRight (decoded term)
            case result of
                Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom (Semantic.MembershipAtomTemplate (Semantic.TemplateClosed value) _) :| [])) -> pure value
                _ -> fail "a rigid closed cache value lost its term tag"
    for_ [Core.COpaqueInteger 0,Core.COpaqueInteger 2,comprehension] \term -> do
        value <- extract term
        Semantic.materializeClosedSetValue closure value @?= Right term
        checked <- expectRight (Core.checkScopedCanonicalCore typing [Core.TySet] term)
        Semantic.closedSetValue checked @?= Just value
        let premises = Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles
                (Semantic.RulePremiseAtom (Semantic.MembershipAtomTemplate (Semantic.TemplateClosed value)
                    (Semantic.TemplateVariable (Semantic.ViewVariableIx 0))) :| []))
        decodeCache Semantic.getProviderResultPremisesCache
            (encodeCache (Semantic.putProviderResultPremisesCache premises)) @?= Right premises
    for_ [Core.CBound 0,Core.CApp (Core.CLam Core.TySet (Core.CBound 1)) (Core.CIntrinsic Core.Empty)] \term ->
        case decoded term of
            Left _ -> pure ()
            Right _ -> assertFailure "a captured closed cache value was admitted"
    let unknown = Identity.intrinsicObjectId (fixtureTheory fixture) Core.Empty
    for_ [Core.CTruth,Core.CLam Core.TySet (Core.CBound 0),Core.CGlobal unknown] \term -> do
        value <- extract term
        case Semantic.materializeClosedSetValue closure value of
            Left _ -> pure ()
            Right _ -> assertFailure "a non-set or unavailable closed value crossed visible admission"

roundTripsProviderResultPremiseModes :: Assertion
roundTripsProviderResultPremiseModes = do
    let variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        guarded = Semantic.ProviderResultGuarded
            (Semantic.RulePremiseBundles
                (Semantic.RulePremiseAtom
                    (Semantic.MembershipAtomTemplate variable variable) :| []))
        roundTrip premises =
            decodeCache
                Semantic.getProviderResultPremisesCache
                (encodeCache
                    (Semantic.putProviderResultPremisesCache premises))
    assertEqual "the premise-free mode round-trips"
        (Right Semantic.ProviderResultUnconditional)
        (roundTrip Semantic.ProviderResultUnconditional)
    assertEqual "the guarded mode retains its nonempty forest"
        (Right guarded)
        (roundTrip guarded)
    case decodeCache
            Semantic.getProviderResultPremisesCache
            (encodeCache (putCacheTag 0xff)) of
        Left (CacheBinaryDecodeError message) ->
            assertBool "an unknown premise-mode tag is rejected at its boundary"
                ("provider-result premise-mode tag" `Text.isInfixOf`
                    Text.pack message)
        Left failure ->
            assertFailure
                ("an unknown provider-result premise-mode tag failed by another route: "
                    <> show failure)
        Right{} ->
            assertFailure "an unknown provider-result premise-mode tag was accepted"

ownsRelationNotionLayout :: Assertion
ownsRelationNotionLayout = do
    fixture <- makeFixture
    let slot = Semantic.declarationSlot
            (fixtureOwner fixture) (localDeclarationOrdinal 9)
        zeroKey = Semantic.SemanticRelation
            (Raw.Command "related") (Raw.ParameterArity 0)
        parameterizedKey = Semantic.SemanticRelation
            (Raw.Command "between") (Raw.ParameterArity 2)
        reference = Semantic.globalBindingRef slot parameterizedKey
        head' = Semantic.RelationNotionHead reference
    assertEqual "relation head retains its exact binding"
        reference
        (Semantic.globalNotionHeadReference head')
    assertBool "relation head accepts a relation key"
        (Semantic.globalNotionHeadMatchesKey head' parameterizedKey)
    assertBool "relation head rejects a noun key"
        (not
            (Semantic.globalNotionHeadMatchesKey head'
                (Semantic.SemanticNoun Raw.End Raw.End)))
    assertEqual "zero-parameter relation order is unchanged"
        (Just (Vector.fromList [0 :: Int, 1]))
        (Semantic.globalNotionBindingArguments
            zeroKey
            (Vector.fromList [0, 1]))
    assertEqual "parameterized relations rotate focus behind parameters"
        (Just (Vector.fromList [20 :: Int, 30, 10, 40]))
        (Semantic.globalNotionBindingArguments
            parameterizedKey
            (Vector.fromList [10, 20, 30, 40]))
    assertEqual "checked relation applications recover their focus-first occurrence order"
        (Just (Vector.fromList [10 :: Int, 20, 30, 40]))
        (Semantic.globalNotionOccurrenceArguments
            parameterizedKey (Vector.fromList [20, 30, 10, 40]))
    assertEqual "malformed relation arguments are rejected"
        (Nothing :: Maybe (Vector.Vector Int))
        (Semantic.globalNotionBindingArguments
            parameterizedKey
            (Vector.fromList [10, 20, 30]))
    assertEqual "relation normalization focus follows binding order"
        (Just (Semantic.OccurrenceArgumentIx 2))
        (Semantic.globalNotionHostFocus parameterizedKey)
    assertEqual "relation notion head codec round trip"
        (Right head')
        (decodeCache
            Semantic.getGlobalNotionHeadCache
            (encodeCache (Semantic.putGlobalNotionHeadCache head')))
    case decodeCache Semantic.getGlobalNotionHeadCache
            (encodeCache (putCacheTag 0xff)) of
        Left{} -> pure ()
        Right{} -> assertFailure "an unknown global-notion head tag was accepted"

ownsVerbNotionLayout :: Assertion
ownsVerbNotionLayout = do
    fixture <- makeFixture
    let slot = Semantic.declarationSlot
            (fixtureOwner fixture) (localDeclarationOrdinal 10)
        withoutHoles = verbKey
            (Raw.TokenCons (Raw.Word "holds") Raw.End)
            (Raw.TokenCons (Raw.Word "hold") Raw.End)
        withOneHole = verbKey
            (Raw.TokenCons (Raw.Word "follows") (Raw.HoleCons Raw.End))
            (Raw.TokenCons (Raw.Word "follow") (Raw.HoleCons Raw.End))
        withTwoHoles = verbKey
            (Raw.TokenCons (Raw.Word "sends")
                (Raw.HoleCons
                    (Raw.TokenCons (Raw.Word "to") (Raw.HoleCons Raw.End))))
            (Raw.TokenCons (Raw.Word "send")
                (Raw.HoleCons
                    (Raw.TokenCons (Raw.Word "to") (Raw.HoleCons Raw.End))))
        reference = Semantic.globalBindingRef slot withTwoHoles
        head' = Semantic.VerbNotionHead reference
    assertEqual "verb head retains its exact binding"
        reference
        (Semantic.globalNotionHeadReference head')
    assertBool "verb head accepts a verb key"
        (Semantic.globalNotionHeadMatchesKey head' withTwoHoles)
    assertBool "verb head rejects a noun key"
        (not
            (Semantic.globalNotionHeadMatchesKey head'
                (Semantic.SemanticNoun Raw.End Raw.End)))
    for_ [withoutHoles, withOneHole, withTwoHoles] \key ->
        assertEqual "verb normalization focus is the subject"
            (Just (Semantic.OccurrenceArgumentIx 0))
            (Semantic.globalNotionHostFocus key)
    for_
        [ (withoutHoles, Vector.fromList [10 :: Int])
        , (withOneHole, Vector.fromList [10, 20])
        , (withTwoHoles, Vector.fromList [10, 20, 30])
        ] \(key, arguments) ->
            assertEqual "verb binding order preserves subject then holes"
                (Just arguments)
                (Semantic.globalNotionBindingArguments key arguments)
    assertEqual "verb notion head codec round trip"
        (Right head')
        (decodeCache
            Semantic.getGlobalNotionHeadCache
            (encodeCache (Semantic.putGlobalNotionHeadCache head')))
  where
    verbKey singular base =
        Semantic.SemanticVerb (checkedVerbSurfaces singular base)

ownsPrefixPredicateNotionRole :: Assertion
ownsPrefixPredicateNotionRole = do
    fixture <- makeFixture
    let slot = Semantic.declarationSlot
            (fixtureOwner fixture) (localDeclarationOrdinal 11)
        key = Semantic.SemanticPrefixPredicate "prefixGuard" 2
        nullaryKey = Semantic.SemanticPrefixPredicate "closedGuard" 0
        reference = Semantic.globalBindingRef slot key
        head' = Semantic.PrefixPredicateNotionHead reference
        arguments = Vector.fromList [10 :: Int, 20]
    assertEqual "prefix head retains its exact binding"
        reference
        (Semantic.globalNotionHeadReference head')
    assertEqual "prefix heads have no distinguished host"
        Semantic.UnhostedGlobalPredicate
        (Semantic.globalNotionHeadRole head')
    assertEqual "hosted heads retain their role"
        Semantic.HostedGlobalNotion
        (Semantic.globalNotionHeadRole
            (Semantic.NounNotionHead
                (Semantic.globalBindingRef slot
                    (Semantic.SemanticNoun Raw.End Raw.End))))
    assertBool "prefix head accepts its semantic key"
        (Semantic.globalNotionHeadMatchesKey head' key)
    assertBool "prefix head rejects a hosted key"
        (not
            (Semantic.globalNotionHeadMatchesKey head'
                (Semantic.SemanticNoun Raw.End Raw.End)))
    assertEqual "prefix arguments remain in binding order"
        (Just arguments)
        (Semantic.globalNotionBindingArguments key arguments)
    assertEqual "malformed prefix arity is rejected"
        (Nothing :: Maybe (Vector.Vector Int))
        (Semantic.globalNotionBindingArguments key (Vector.singleton 10))
    assertEqual "prefix predicates have no host focus"
        Nothing
        (Semantic.globalNotionHostFocus key)
    assertEqual "a synthetic nullary prefix preserves its empty vector"
        (Just (Vector.empty :: Vector.Vector Int))
        (Semantic.globalNotionBindingArguments nullaryKey Vector.empty)
    assertEqual "a synthetic nullary prefix remains hostless"
        Nothing
        (Semantic.globalNotionHostFocus nullaryKey)
    assertEqual "prefix notion head codec round trip"
        (Right head')
        (decodeCache
            Semantic.getGlobalNotionHeadCache
            (encodeCache (Semantic.putGlobalNotionHeadCache head')))

roundTripsFiniteEvidenceRules :: Assertion
roundTripsFiniteEvidenceRules = do
    fixture <- makeFixture
    let owner = fixtureOwner fixture
        slot = Semantic.declarationSlot owner (localDeclarationOrdinal 1)
        fact = Semantic.factSlot owner (localFactOrdinal 1)
        variable = Semantic.TemplateVariable (Semantic.ViewVariableIx 0)
        atomTemplate = Semantic.MembershipAtomTemplate variable variable
        premiseBundles = Semantic.RulePremiseBundles
            (Semantic.RulePremiseAtom atomTemplate :| [])
        member = Core.CApp
            (Core.CApp (Core.CIntrinsic Core.Member) (Core.CBound 0))
            (Core.CBound 0)
        theorem = Core.CForall Core.TySet (Core.CImp member member)
    proposition <- expectRight
        (Identity.validatePropositionContent
            (fixtureClosure fixture)
            theorem)
    let authority = Authority.factAuthority
            (Identity.theoremRef
                (fixtureTheory fixture)
                (Identity.checkedPropositionId proposition))
            Authority.cleanAuthoritySafety
        occurrence = Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
            fact authority Semantic.SearchEligible
        fingerprint =
            Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose fact authority
    skeleton <- evaluate . force =<< expectRight
        (Semantic.checkedNotionRuleSkeleton
            1 (let Semantic.RulePremiseBundles bundles = premiseBundles in toList bundles) atomTemplate)
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            slot
            [occurrence]
            []
            []
            [Identity.checkedPropositionId proposition]
            []
            [Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterFiniteEvidence (Semantic.FiniteEvidenceRule skeleton))]
            Semantic.emptySemanticEnvironmentDelta)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    assertEqual "finite-evidence interface codec round trip"
        (Right interface)
        (decodeCache
            Semantic.getSemanticInterfaceCache
            (encodeCache (Semantic.putSemanticInterfaceCache interface)))

normalizesRegistrationOrder :: Assertion
normalizesRegistrationOrder = do
    fixture <- makeFixture
    let original = fixtureDelta fixture
        rebuild registrations = expectRight (Semantic.declarationInterfaceDelta
            (Semantic.declarationDeltaSlot original)
            (Semantic.declarationDeltaFacts original)
            (Semantic.declarationDeltaAliases original)
            (Semantic.declarationDeltaObjects original)
            (Semantic.declarationDeltaPropositions original)
            (Semantic.declarationDeltaDefinitionViews original)
            registrations
            (Semantic.declarationDeltaEnvironment original))
        bytes = encodeCache . Semantic.putDeclarationInterfaceDeltaCache
    case Semantic.declarationDeltaRegistrations original of
        [nullary, guarded, unconditional] -> do
            for_ [[nullary, guarded, unconditional], [guarded, nullary, unconditional],
                    [guarded, unconditional, nullary]] \interleaving -> do
                actual <- rebuild interleaving
                actual @?= original
                bytes actual @?= bytes original
            reversed <- rebuild [nullary, unconditional, guarded]
            Semantic.declarationDeltaRegistrations reversed @?= [nullary, unconditional, guarded]
            assertBool "within-family order remains part of the canonical bytes"
                (bytes reversed /= bytes original)
            -- The old product compared the nullary segment before the provider
            -- segment, including when one earlier segment was exhausted.
            let segments = [([], []), ([nullary], []), ([], [guarded]),
                    ([nullary], [guarded]), ([], [guarded, unconditional]),
                    ([nullary], [unconditional, guarded])]
            values <- traverse (rebuild . uncurry (<>)) segments
            for_ (zip segments values) \(left, leftDelta) ->
                for_ (zip segments values) \(right, rightDelta) ->
                    compare leftDelta rightDelta @?= compare left right
        _ -> assertFailure "the registration-order fixture changed its three-family-segment entries"

rejectsMalformedFactBranches :: Assertion
rejectsMalformedFactBranches = do
    fixture <- makeFixture
    let delta = fixtureDelta fixture
        encoded = encodeCache (Semantic.putDeclarationInterfaceDeltaCache delta)
    rule <- case reverse (Semantic.declarationDeltaRegistrations delta) of
        value : _ -> pure value
        [] -> fail "fact-branch fixture has no provider registration"
    let fingerprint = encodeCache (Semantic.putSemanticFactOccurrenceFingerprintCache
            (Semantic.registrationSource rule))
        occurrences offset bytes = case Bytes.breakSubstring fingerprint bytes of
            (_, rest) | Bytes.null rest -> []
            (before, rest) ->
                let position = offset + Bytes.length before + Bytes.length fingerprint
                in position : occurrences position (Bytes.drop (Bytes.length fingerprint) rest)
    selectorOffset <- case reverse (occurrences 0 encoded) of
        value : _ -> pure value
        [] -> fail "encoded fixture lost its registration source"
    let replaceSelector bytes = Bytes.take selectorOffset encoded <> bytes <> Bytes.drop (selectorOffset + 1) encoded
    assertEqual "ordinary source branches use the identity projection" 0 (Bytes.index encoded selectorOffset)
    case decodeCache Semantic.getDeclarationInterfaceDeltaCache (replaceSelector (Bytes.singleton 255)) of
        Left failure -> assertBool "invalid selectors fail at their own codec boundary"
            ("fact-branch path tag" `List.isInfixOf` show failure)
        Right _ -> assertFailure "unknown branch-selector tag was accepted"
    let deep = Bytes.replicate (fromIntegral (maximumDecoderDepth standardDecoderLimits) + 1) 1 <> Bytes.singleton 0
    case decodeCache Semantic.getDeclarationInterfaceDeltaCache (replaceSelector deep) of
        Left failure -> assertBool "selector recursion consumes decoder depth"
            ("DecoderDepth" `List.isInfixOf` show failure)
        Right _ -> assertFailure "unbounded branch-selector nesting was accepted"

roundTripsFiniteSetProviderIdentity :: Assertion
roundTripsFiniteSetProviderIdentity = do
    let head' = Semantic.FiniteSetLiteralSourceProvider
    assertEqual "finite-set provider codec round trip"
        (Right head')
        (decodeCache
            Semantic.getSourceProviderHeadCache
            (encodeCache (Semantic.putSourceProviderHeadCache head')))
    let first :: Core.CanonicalTerm ()
        first = Core.COpaqueInteger 1
        second = Core.COpaqueInteger 2
    assertEqual "finite-set provider preserves source order"
        (Core.canonicalSetInsert first
            (Core.canonicalSetInsert second (Core.CIntrinsic Core.Empty)))
        (Semantic.finiteSetLiteralProviderApplication (first :| [second]))

roundTripsIntrinsicProviderIdentities :: Assertion
roundTripsIntrinsicProviderIdentities = do
    forM_
        [ Semantic.PowerSetProvider
        , Semantic.GlobalChoiceProvider
        , Semantic.EmptySetProvider
        , Semantic.FirstProjectionProvider
        , Semantic.SecondProjectionProvider
        ] \provider -> do
            let head' = Semantic.IntrinsicSourceProvider provider
            assertEqual "intrinsic provider codec round trip"
                (Right head')
                (decodeCache
                    Semantic.getSourceProviderHeadCache
                    (encodeCache
                        (Semantic.putSourceProviderHeadCache head')))
    case decodeCache
            Semantic.getSourceProviderHeadCache
            (encodeCache do
                putCacheTag 0x02
                putCacheTag 0xff) of
        Left{} -> pure ()
        Right{} ->
            assertFailure "an unknown intrinsic-provider id tag was accepted"

classifiesSourceProviders :: Assertion
classifiesSourceProviders = do
    fixture <- makeFixture
    let slot = Semantic.declarationSlot
            (fixtureOwner fixture) (localDeclarationOrdinal 7)
        object = Identity.intrinsicObjectId
            (fixtureTheory fixture) Core.Empty
        unary word = Raw.HoleCons (Raw.TokenCons (Raw.Word word) Raw.End)
        functionKey = Semantic.SemanticFunctionPhrase
            (unary "provider") (unary "providers")
        constantKey ty = Semantic.SemanticTypedConstant (Raw.Word "closed-provider") ty
        resolve key target = expectRight
            (Semantic.materializeResolvedGlobalBinding
                (const Nothing)
                (const Nothing)
                (fixtureClosure fixture)
                slot
                (Semantic.semanticGlobalBinding
                    key
                    (Semantic.semanticBindingLabel "provider")
                    target))
        expected key = Just
            (Semantic.GlobalSourceProvider
                (Semantic.globalBindingRef slot key))
    function <- resolve functionKey (Semantic.GlobalReference object)
    constant <- resolve (constantKey Core.TySet) (Semantic.GlobalReference object)
    higher <- resolve (constantKey (Core.TyArrow Core.TySet Core.TySet))
        (Semantic.GlobalReference object)
    proposition <- resolve (constantKey Core.TyProp) (Semantic.GlobalReference object)
    assertEqual "function-phrase owner"
        (expected functionKey)
        (Semantic.resolvedBindingSourceProviderHead function)
    assertEqual "a typed set constant retains its exact owner"
        (expected (constantKey Core.TySet))
        (Semantic.resolvedBindingSourceProviderHead constant)
    assertEqual "a typed function is not a source provider"
        Nothing (Semantic.resolvedBindingSourceProviderHead higher)
    assertEqual "a typed proposition is not a source provider"
        Nothing (Semantic.resolvedBindingSourceProviderHead proposition)

instantiatesTypedSourceTemplates :: Assertion
instantiatesTypedSourceTemplates = do
    fixture <- makeFixture
    let context = SourceTerm.SourceTermCheckingContext (Identity.globalTypingFromClosure (fixtureClosure fixture)) [Core.TySet]
        source ty value = SourceTerm.sourceTermOccurrence value ty ()
        original = source Core.TySet (Core.CBound 0)
        replacement = source Core.TySet (Core.CIntrinsic Core.Empty)
        layout = Vector.fromList [1,0]
        formula = Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 2)
        captured = Semantic.ExpansionOpaque (Core.CBound 2)
        expansion = Semantic.PropositionExpansion
            (SourceEvidence.SourceInputs Nothing
                [SourceEvidence.SourceInput [] (Semantic.ExpansionFormal 0), SourceEvidence.SourceInput [] captured])
            [Semantic.ExpansionEquality (Semantic.ExpansionFormal 0) captured Notion.ConjunctionHere]
        origin path = SourceEvidence.WrittenOrigin Nowhere Nothing path
        run allowance arguments body template = runIdentity (Semantic.runExpansionWork allowance
            (SourceTemplate.instantiateSourceTemplate context Map.empty Nowhere () origin layout arguments body template))
        observe = \case
            SourceTemplate.InstantiatedProposition core evidence equalities -> do
                assertEqual "equality sidecar denotes the instantiated proposition" [core]
                    (Notion.sourceEqualityFormula <$> equalities)
                pure (core, SourceEvidence.sourceInputsAtDepth (const []) evidence)
            _ -> assertFailure "proposition template returned a term" >> fail "unreachable"
        originalArguments = Vector.fromList [original,original]
        replacements = Vector.fromList [replacement,original]
    (before,_) <- expectRight (fst (run 10000 originalArguments formula expansion)) >>= observe
    assertEqual "the endpoint and capture initially coincide"
        (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)) before
    let (result,remaining) = run 10000 replacements formula expansion
    (changed,inputs) <- expectRight result >>= observe
    assertEqual "replacement changes only the distinguished endpoint"
        (Core.CEq Core.TySet (Core.CIntrinsic Core.Empty) (Core.CBound 0)) changed
    assertEqual "captured source inputs stay fixed"
        [SourceEvidence.SourceInput [] (Semantic.TemplateVariable (Core.CIntrinsic Core.Empty)),
            SourceEvidence.SourceInput [] (Semantic.TemplateVariable (Core.CBound 0))] inputs
    let used = 10000 - remaining
    void (expectRight (fst (run used replacements formula expansion)))
    case fst (run (used-1) replacements formula expansion) of
        Left Semantic.ExpansionWorkExhausted{} -> pure ()
        _ -> assertFailure "source substitution must not replenish its work allowance"
    let functionType = Core.TyArrow Core.TySet Core.TySet
        identity = source functionType (Core.CLam Core.TySet (Core.CBound 0))
        typed = Vector.fromList [source Core.TyProp Core.CTruth,identity]
    typedResult <- expectRight (fst (run 10000 typed (Core.CBound 0) (Semantic.TermExpansion (Semantic.ExpansionFormal 1))))
    case typedResult of
        SourceTemplate.InstantiatedTerm term -> do
            SourceTerm.sourceTermOccurrenceType term @?= functionType
            SourceTerm.sourceTermOccurrenceCore term @?= Core.CLam Core.TySet (Core.CBound 0)
        _ -> assertFailure "typed formal changed expansion kind"
    let membership x y = Core.CApp (Core.CApp (Core.CIntrinsic Core.Member) x) y
        truth = SourceEvidence.SourceInputs Nothing []
        positive = Semantic.PropositionExpansion (SourceEvidence.SourceExists
            (SourceEvidence.SourceOr
                (SourceEvidence.SourceAtom (Semantic.MembershipAtomTemplate
                    (Semantic.ExpansionLocal 0) (Semantic.ExpansionFormal 0)))
                (SourceEvidence.SourceIff truth truth))) []
        positiveCore set = Core.CExists Core.TySet (Core.COr
            (membership (Core.CBound 0) set) (Core.CEq Core.TyProp Core.CTruth Core.CTruth))
    decodeCache Semantic.getAbbreviationExpansionCache
        (encodeCache (Semantic.putAbbreviationExpansionCache positive)) @?= Right positive
    instantiated <- expectRight (fst (run 10000 replacements (positiveCore (Core.CBound 2)) positive))
    case instantiated of
        SourceTemplate.InstantiatedProposition core
                (SourceEvidence.SourceExists (SourceEvidence.SourceOr (SourceEvidence.SourceAtom assertion)
                    SourceEvidence.SourceIff{})) equalities -> do
            core @?= positiveCore (Core.CIntrinsic Core.Empty)
            (SourceTerm.sourceTermOccurrenceCore <$> Notion.sourceAssertionAtom assertion)
                @?= Semantic.MembershipAtomTemplate (Core.CBound 0) (Core.CIntrinsic Core.Empty)
            assertBool "compound metadata supplies no equality assumption" (null equalities)
        _ -> assertFailure "positive source structure or lexical binding was lost"

materializesAbbreviationExpansions :: Assertion
materializesAbbreviationExpansions = do
    fixture <- makeFixture
    let theory = fixtureTheory fixture
        owner = fixtureOwner fixture
        requiredSlot = Semantic.declarationSlot
            owner (localDeclarationOrdinal 20)
        hostSlot = Semantic.declarationSlot
            owner (localDeclarationOrdinal 21)
        prefixSlot = Semantic.declarationSlot
            owner (localDeclarationOrdinal 22)
        wordPattern word = Raw.TokenCons (Raw.Word word) Raw.End
        requiredKey = Semantic.SemanticNoun
            (wordPattern "canonical") (wordPattern "canonicals")
        hostKey = Semantic.SemanticNoun
            (wordPattern "alias") (wordPattern "aliases")
        prefixKey = Semantic.SemanticPrefixPredicate "prefixGuard" 1
        requiredReference = Semantic.globalBindingRef requiredSlot requiredKey
        prefixReference = Semantic.globalBindingRef prefixSlot prefixKey
        requiredHead = Semantic.NounNotionHead requiredReference
        predicateType = Core.TyArrow Core.TySet Core.TyProp
        requiredObject = Identity.transparentObject
            theory predicateType (Core.CLam Core.TySet Core.CFalsum)
        requiredIdentity = Identity.assertedObjectId requiredObject
        hostBody = Core.CLam Core.TySet
            (Core.CApp (Core.CGlobal requiredIdentity) (Core.CBound 0))
        hostObject = Identity.transparentObject theory predicateType hostBody
        hostIdentity = Identity.assertedObjectId hostObject
        requiredBinding = Semantic.semanticGlobalBinding
            requiredKey
            (Semantic.semanticBindingLabel "canonical")
            (Semantic.GlobalReference requiredIdentity)
        prefixBinding = Semantic.semanticGlobalBinding
            prefixKey
            (Semantic.semanticBindingLabel "prefix guard")
            (Semantic.GlobalReference requiredIdentity)
        variable = Semantic.ExpansionFormal 0
        validTemplate = Semantic.GlobalAtomTemplate
            requiredHead (Vector.singleton variable)
        hostBinding = hostEvidence . SourceEvidence.SourceAtom
        hostEvidence evidence = Semantic.semanticGlobalBindingWithMetadata
            hostKey
            (Semantic.semanticBindingLabel "alias")
            (Semantic.TransparentExpansion hostIdentity)
            Nothing
            (Just (Semantic.PropositionExpansion evidence []))
        lookupBinding reference
            | reference == requiredReference = Just requiredBinding
            | reference == prefixReference = Just prefixBinding
            | otherwise = Nothing
        materialize closure binding =
            Semantic.materializeResolvedGlobalBinding
                lookupBinding (const Nothing) closure hostSlot binding
    closure <- expectRight
        (Identity.validateObjectClosure theory [requiredObject, hostObject])
    resolved <- expectRight (materialize closure (hostBinding validTemplate))
    assertEqual "the validated terminal template is retained only at runtime"
        (Just (Semantic.PropositionExpansion (SourceEvidence.SourceAtom validTemplate) []))
        (Semantic.resolvedBindingExpansion resolved)
    environment <- expectRight
        (Semantic.semanticEnvironmentDelta [hostBinding validTemplate])
    assertEqual "normalization metadata participates in interface encoding"
        (Right environment)
        (decodeCache
            Semantic.getSemanticEnvironmentDeltaCache
            (encodeCache
                (Semantic.putSemanticEnvironmentDeltaCache environment)))

    let annotation = SourceEvidence.SourceInput [] variable
        annotated = SourceEvidence.withSourceInputs [annotation] (SourceEvidence.SourceAtom validTemplate)
    for_ [SourceEvidence.SourceInputs Nothing [], annotated,
            SourceEvidence.SourceWithInputs [] (SourceEvidence.SourceInputs Nothing [])] \evidence -> do
        void (expectRight (materialize closure (hostEvidence evidence)))
        encoded <- expectRight (Semantic.semanticEnvironmentDelta [hostEvidence evidence])
        assertEqual "complete and additive expansion inputs round-trip distinctly" (Right encoded)
            (decodeCache Semantic.getSemanticEnvironmentDeltaCache
                (encodeCache (Semantic.putSemanticEnvironmentDeltaCache encoded)))
        let residual = Semantic.describedResidualTemplate (Core.CApp (Core.CGlobal requiredIdentity) (Core.CBound 0))
                (SourceEvidence.SourceWithInputs [SourceEvidence.SourceInput [] (Semantic.TemplateVariable (Core.CBound 0))]
                    (SourceEvidence.SourceInputs Nothing []))
            contract = Semantic.formationContract (Semantic.WholeLeaf (Semantic.WholeResidual residual) :| [])
        contractEnvironment <- expectRight (Semantic.semanticEnvironmentDelta
            [Semantic.semanticGlobalBindingWithMetadata hostKey (Semantic.semanticBindingLabel "alias")
                (Semantic.GlobalReference requiredIdentity) (Just contract) Nothing])
        assertEqual "residual annotations survive the formation-contract codec" (Right contractEnvironment)
            (decodeCache Semantic.getSemanticEnvironmentDeltaCache
                (encodeCache (Semantic.putSemanticEnvironmentDeltaCache contractEnvironment)))
    for_ [Semantic.ExpansionFormal 9, Semantic.ExpansionOpaque (Core.CIntrinsic Core.Empty)] \operand ->
        case materialize closure (hostEvidence (SourceEvidence.withSourceInputs
                [SourceEvidence.SourceInput [] operand] (SourceEvidence.SourceAtom validTemplate))) of
            Left Semantic.AbbreviationExpansionInvalid{} -> pure ()
            other -> assertFailure ("invalid additive input was admitted: " <> show other)

    let missing = Semantic.semanticGlobalBinding hostKey (Semantic.semanticBindingLabel "alias")
            (Semantic.TransparentExpansion hostIdentity)
    case materialize closure missing of
        Left Semantic.AbbreviationExpansionInvalid{} -> pure ()
        other -> assertFailure ("a missing expansion payload was accepted: " <> show other)

    let malformedProvider = Semantic.MembershipAtomTemplate
            variable
            (Semantic.ExpansionProvider
                (Semantic.IntrinsicSourceProvider Semantic.PowerSetProvider)
                Vector.empty)
    case materialize closure (hostBinding malformedProvider) of
        Left (Semantic.AbbreviationExpansionInvalid _detail) -> pure ()
        result -> assertFailure
            ("malformed normalization escaped its own error boundary: "
                <> show result)

    let mismatchedTemplate = Semantic.MembershipAtomTemplate variable variable
    case materialize closure (hostBinding mismatchedTemplate) of
        Left (Semantic.AbbreviationExpansionInvalid _detail) -> pure ()
        result -> assertFailure
            ("normalization/body disagreement was accepted: " <> show result)

    let measured template = do
            environment' <- Semantic.semanticEnvironmentDelta [hostBinding template]
            pure (Semantic.materializeSemanticEnvironmentDeltaMeasured lookupBinding (const Nothing)
                (const Nothing) Set.empty closure hostSlot environment')
    (accepted, admittedWork) <- expectRight (measured validTemplate)
    void (expectRight accepted)
    assertBool "fresh and cached expansion admission retain their work" (admittedWork > 0)
    (rejected, rejectedWork) <- expectRight (measured mismatchedTemplate)
    assertBool "failed admission retains accepted debits" (isLeft rejected && rejectedWork > 0)

    let sourceTerminalTemplate = Semantic.GlobalAtomTemplate
            (Semantic.PrefixPredicateNotionHead prefixReference)
            (Vector.singleton variable)
    void (expectRight (materialize closure (hostBinding sourceTerminalTemplate)))

    -- Two admitted fields can have equal projections. Their identities still
    -- distinguish contextual receiver eligibility and the rich construction.
    let field = Identity.fieldId owner (localDeclarationOrdinal 0) (structureFieldSlot 0)
        otherField = Identity.fieldId owner (localDeclarationOrdinal 0) (structureFieldSlot 1)
        projectionObject = Identity.transparentObject theory (Core.TyArrow Core.TySet Core.TySet)
            (Core.CLam Core.TySet (Core.CBound 0))
        projection = Identity.assertedObjectId projectionObject
        contextualObject = Identity.transparentObject theory (Core.TyArrow Core.TySet predicateType)
            (Core.CLam Core.TySet (Core.CLam Core.TySet
                (Core.CApp (Core.CGlobal requiredIdentity) (Core.CApp (Core.CGlobal projection) (Core.CBound 1)))))
        contextual required = Semantic.semanticGlobalBindingWithMetadata hostKey
            (Semantic.semanticBindingLabel "contextual alias")
            (Semantic.ContextualTransparentExpansion (Identity.assertedObjectId contextualObject)
                (Map.singleton Raw.CarrierSymbol (required, projection))) Nothing
            (Just (Semantic.PropositionExpansion (SourceEvidence.SourceAtom (Semantic.GlobalAtomTemplate requiredHead
                (Vector.singleton (Semantic.ExpansionProvider (Semantic.StructureFieldSourceProvider field projection)
                    (Vector.singleton (Semantic.ExpansionFormal 1)))))) []))
        fieldLookup identity
            | identity == field || identity == otherField = Just projection
            | otherwise = Nothing
    contextualClosure <- expectRight (Identity.validateObjectClosure theory
        [requiredObject, projectionObject, contextualObject])
    let resolveContextual = Semantic.materializeResolvedGlobalBindingWithFields
            lookupBinding (const Nothing) fieldLookup Set.empty contextualClosure hostSlot
    void (expectRight (resolveContextual (contextual field)))
    case resolveContextual (contextual otherField) of
        Left Semantic.AbbreviationExpansionInvalid{} -> pure ()
        result -> assertFailure ("a different field identity with equal Core was accepted: " <> show result)

materializesFormationContracts :: Assertion
materializesFormationContracts = do
    fixture <- makeFixture
    let owner = fixtureOwner fixture
        otherOwner = moduleNameFromParts
            (sourceNamespaceIdFromDigest
                (hashBlake2b256 "other-semantic-test-namespace\NULroot"))
            (expectPureRight (safeRelativePath "other.tex"))
        slot = Semantic.declarationSlot owner (localDeclarationOrdinal 0)
        otherSlot =
            Semantic.declarationSlot otherOwner (localDeclarationOrdinal 0)
        predicate = Identity.intrinsicObjectId
            (fixtureTheory fixture) Core.Empty
        wordPattern word = Raw.TokenCons (Raw.Word word) Raw.End
        hostKey = Semantic.SemanticNoun
            (wordPattern "host") (wordPattern "hosts")
        requiredKey = Semantic.SemanticNoun
            (wordPattern "required") (wordPattern "requirements")
        adjectiveKey = Semantic.SemanticLeftAdjective
            Semantic.OrdinaryAdjectiveReading
            (wordPattern "required")
        hostReference = Semantic.globalBindingRef slot hostKey
        requiredReference = Semantic.globalBindingRef slot requiredKey
        requiredBinding = Semantic.semanticGlobalBinding
            requiredKey
            (Semantic.semanticBindingLabel "required")
            (Semantic.GlobalReference predicate)
        requiredHead = Semantic.NounNotionHead requiredReference
        requirement index = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx index)))
        contract templates =
            Semantic.formationContract
                (Semantic.AtomicLeaf <$> case templates of
                    first : rest -> first :| rest
                    [] -> error "formation-contract test requires a template")
        hostBinding templates = Semantic.semanticGlobalBindingWithContract
            hostKey
            (Semantic.semanticBindingLabel "host")
            (Semantic.GlobalReference predicate)
            (Just (contract templates))
        directBindings reference =
            if reference == requiredReference
            then Just requiredBinding
            else Nothing
        noStructures _phrase = Nothing
        materializeWith bindings structures binding =
            Semantic.materializeResolvedGlobalBinding
                bindings structures (fixtureClosure fixture) slot binding
    resolved <- expectRight
        (materializeWith directBindings noStructures
            (hostBinding [requirement 0]))
    assertBool "valid contract is retained only as checked runtime data"
        (isJust (Semantic.resolvedBindingContract resolved))
    let wholeBinding whole = Semantic.semanticGlobalBindingWithContract hostKey
            (Semantic.semanticBindingLabel "whole-host") (Semantic.GlobalReference predicate)
            (Just (Semantic.formationContract (Semantic.WholeLeaf whole :| [])))
        residual formula = Semantic.WholeResidual (Semantic.ResidualTemplate formula)
        universal index = Semantic.WholeUniversal $ SourceEvidence.UniversalBind $
            SourceEvidence.UniversalReturn $ SourceEvidence.AtomLeaf $ Semantic.MembershipAtomTemplate
                (Semantic.TemplateVariable (SourceEvidence.UniversalBound index))
                (Semantic.TemplateVariable (SourceEvidence.UniversalOuter
                    (Semantic.TemplateVariable (Semantic.OccurrenceArgumentIx 0))))
    for_ [residual (Core.CEq Core.TySet (Core.CBound 0) (Core.CBound 0)), universal 0] \whole ->
        void (expectRight (materializeWith directBindings noStructures (wholeBinding whole)))
    for_ [residual (Core.CBound 0), residual (Core.CEq Core.TySet (Core.CBound 1) (Core.CBound 0)), universal 1] \whole ->
        case materializeWith directBindings noStructures (wholeBinding whole) of
            Left Semantic.FormationContractWholeRequirementInvalid{} -> pure ()
            result -> assertFailure ("malformed whole requirement escaped admission: " <> show result)
    assertEqual "out-of-range host occurrence index"
        (Left
            (Semantic.FormationContractArgumentOutOfRange
                (Semantic.OccurrenceArgumentIx 1) 1))
        (fmap (const ())
            (materializeWith directBindings noStructures
                (hostBinding [requirement 1])))
    assertEqual "exact duplicate requirement"
        (Left
            (Semantic.FormationContractDuplicateRequirement
                (Semantic.AtomicLeaf (requirement 0))))
        (fmap (const ())
            (materializeWith directBindings noStructures
                (hostBinding [requirement 0, requirement 0])))
    let wrongOwnerHead = Semantic.NounNotionHead
            (Semantic.globalBindingRef otherSlot requiredKey)
        wrongOwnerRequirement = Semantic.GlobalAtomTemplate
            wrongOwnerHead
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
    assertEqual "wrong global owner"
        (Left
            (Semantic.FormationContractGlobalBindingMissing
                (Semantic.globalBindingRef otherSlot requiredKey)))
        (fmap (const ())
            (materializeWith directBindings noStructures
                (hostBinding [wrongOwnerRequirement])))
    let adjectiveReference = Semantic.globalBindingRef slot adjectiveKey
        wrongFamily = Semantic.GlobalAtomTemplate
            (Semantic.NounNotionHead adjectiveReference)
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
    assertEqual "global notion family"
        (Left
            (Semantic.FormationContractGlobalFamilyMismatch
                (Semantic.NounNotionHead adjectiveReference)
                adjectiveKey))
        (fmap (const ())
            (materializeWith (const Nothing) noStructures
                (hostBinding [wrongFamily])))
    let contextualBinding = Semantic.semanticGlobalBinding
            requiredKey
            (Semantic.semanticBindingLabel "contextual requirement")
            (Semantic.ContextualTransparentExpansion
                predicate
                (Map.singleton (Raw.StructSymbol "carrier") (Identity.fieldId owner (localDeclarationOrdinal 0) (structureFieldSlot 0), predicate)))
        contextualLookup reference
            | reference == requiredReference = Just contextualBinding
            | otherwise = Nothing
    assertEqual "contextual requirement head"
        (Left
            (Semantic.FormationContractGlobalNotDirect
                requiredReference
                (Semantic.semanticGlobalBindingTarget contextualBinding)))
        (fmap (const ())
            (materializeWith contextualLookup noStructures
                (hostBinding [requirement 0])))
    let assertUnsupportedHost label unsupportedKey unsupportedType = do
            let unsupportedHost =
                    Semantic.semanticGlobalBindingWithContract
                        unsupportedKey
                        (Semantic.semanticBindingLabel label)
                        (Semantic.GlobalReference predicate)
                        (Just (contract [requirement 0]))
            assertEqual (Text.unpack label)
                (Left
                    (Semantic.FormationContractHostSignatureUnsupported
                        unsupportedKey (Just unsupportedType)))
                (fmap (const ())
                    (Semantic.materializeResolvedGlobalBinding
                        directBindings noStructures (fixtureClosure fixture)
                        slot unsupportedHost))
        setHostType = Core.TyArrow Core.TySet Core.TySet
        setHostKey = Semantic.SemanticTypedConstant
            (Raw.Variable "set-valued-host") setHostType
        higherOrderHostType =
            Core.TyArrow
                (Core.TyArrow Core.TySet Core.TySet)
                Core.TyProp
        higherOrderHostKey = Semantic.SemanticTypedConstant
            (Raw.Variable "higher-order-host") higherOrderHostType
        nonFirstOrderResultType =
            Core.TyArrow Core.TySet
                (Core.TyArrow Core.TyProp Core.TyProp)
        nonFirstOrderResultKey = Semantic.SemanticTypedConstant
            (Raw.Variable "non-first-order-result") nonFirstOrderResultType
    assertUnsupportedHost
        "set-valued first-order host" setHostKey setHostType
    assertUnsupportedHost
        "higher-order argument host" higherOrderHostKey higherOrderHostType
    assertUnsupportedHost
        "non-first-order result host"
        nonFirstOrderResultKey nonFirstOrderResultType
    let expressionSetHostKey = Semantic.SemanticExpressionFunction
            (Raw.TokenCons
                (Raw.Command "setTermHost")
                (Raw.HoleCons Raw.End))
        expressionSetHostType = fromMaybe
            (error "expression set host lacks a semantic type")
            (Semantic.semanticGlobalKeyType expressionSetHostKey)
        expressionSetHostObject = Identity.transparentObjectId
            (fixtureTheory fixture)
            expressionSetHostType
            (Core.CLam Core.TySet (Core.CBound 0))
        expressionSetHost = Semantic.semanticGlobalBindingWithContract
            expressionSetHostKey
            (Semantic.semanticBindingLabel "transparent expression set host")
            (Semantic.GlobalReference expressionSetHostObject)
            (Just (contract [requirement 0]))
    expressionResolved <- expectRight
        (Semantic.materializeResolvedGlobalBinding
            directBindings noStructures (fixtureClosure fixture)
            slot expressionSetHost)
    assertBool "transparent expression set host retains its contract"
        (isJust (Semantic.resolvedBindingContract expressionResolved))
    let providerReference = Semantic.globalBindingRef slot expressionSetHostKey
        providerHead = Semantic.GlobalSourceProvider providerReference
        providerTerm = Semantic.TemplateProvider
            providerHead
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        providerRequirement = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton providerTerm)
        providerLookup reference
            | reference == requiredReference = Just requiredBinding
            | reference == providerReference =
                Just
                    (Semantic.semanticGlobalBinding
                        expressionSetHostKey
                        (Semantic.semanticBindingLabel "provider")
                        (Semantic.GlobalReference expressionSetHostObject))
            | otherwise = Nothing
    providerResolved <- expectRight
        (materializeWith providerLookup noStructures
            (hostBinding [providerRequirement]))
    assertBool "an exact uncontracted provider is retained in a contract"
        (isJust (Semantic.resolvedBindingContract providerResolved))
    let fieldIdentity = Identity.fieldId
            owner (localDeclarationOrdinal 0) (structureFieldSlot 0)
        fieldProjection = Identity.intrinsicObjectId
            (fixtureTheory fixture) Core.Empty
        fieldProvider = Semantic.StructureFieldSourceProvider
            fieldIdentity fieldProjection
        fieldTerm = Semantic.TemplateProvider
            fieldProvider
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        fieldRequirement = Semantic.GlobalAtomTemplate
            requiredHead (Vector.singleton fieldTerm)
        materializeField lookupField fieldRequirement' =
            Semantic.materializeResolvedGlobalBindingWithFields
                directBindings noStructures lookupField Set.empty (fixtureClosure fixture)
                slot
                (hostBinding [fieldRequirement'])
    fieldResolved <- expectRight
        (materializeField
            (\identity ->
                if identity == fieldIdentity
                then Just fieldProjection
                else Nothing)
            fieldRequirement)
    assertBool "an exact visible structure-field provider is retained"
        (isJust (Semantic.resolvedBindingContract fieldResolved))
    assertEqual "a structure-field provider must be visible"
        (Left
            (Semantic.FormationContractStructureFieldProviderMissing
                fieldIdentity))
        (fmap (const ())
            (materializeField (const Nothing) fieldRequirement))
    let staleProjection = Identity.intrinsicObjectId
            (fixtureTheory fixture) Core.Member
    assertEqual "a structure-field provider retains its exact projection"
        (Left
            (Semantic.FormationContractStructureFieldProviderMismatch
                fieldIdentity staleProjection fieldProjection))
        (fmap (const ())
            (Semantic.materializeResolvedGlobalBindingWithFields
                directBindings noStructures (const (Just staleProjection))
                Set.empty (fixtureClosure fixture) slot
                (hostBinding [fieldRequirement])))
    let nullaryFieldRequirement = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton
                (Semantic.TemplateProvider fieldProvider Vector.empty))
    assertEqual "structure-field providers are unary"
        (Left
            (Semantic.FormationContractStructureFieldProviderArityMismatch
                fieldIdentity 0))
        (fmap (const ())
            (materializeField (const (Just fieldProjection))
                nullaryFieldRequirement))
    let intrinsicProvider = Semantic.IntrinsicSourceProvider
            Semantic.PowerSetProvider
        intrinsicTerm = Semantic.TemplateProvider
            intrinsicProvider
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        intrinsicRequirement = Semantic.GlobalAtomTemplate
            requiredHead (Vector.singleton intrinsicTerm)
    intrinsicResolved <- expectRight
        (materializeWith directBindings noStructures
            (hostBinding [intrinsicRequirement]))
    assertBool "an admitted intrinsic provider is retained in a contract"
        (isJust (Semantic.resolvedBindingContract intrinsicResolved))
    let nullaryIntrinsicRequirement = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton
                (Semantic.TemplateProvider intrinsicProvider Vector.empty))
    assertEqual "intrinsic providers derive their unary arity from Core"
        (Left
            (Semantic.FormationContractIntrinsicProviderArityMismatch
                Semantic.PowerSetProvider 1 0))
        (fmap (const ())
            (materializeWith directBindings noStructures
                (hostBinding [nullaryIntrinsicRequirement])))
    let finiteLiteralTerm = Semantic.TemplateProvider
            Semantic.FiniteSetLiteralSourceProvider
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        finiteLiteralRequirement = Semantic.GlobalAtomTemplate
            requiredHead (Vector.singleton finiteLiteralTerm)
    finiteLiteralResolved <- expectRight
        (materializeWith directBindings noStructures
            (hostBinding [finiteLiteralRequirement]))
    assertBool "a nonempty finite literal is retained in a contract"
        (isJust
            (Semantic.resolvedBindingContract finiteLiteralResolved))
    let emptyFiniteLiteralRequirement = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton
                (Semantic.TemplateProvider
                    Semantic.FiniteSetLiteralSourceProvider
                    Vector.empty))
    emptyFiniteLiteralEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta
            [hostBinding [emptyFiniteLiteralRequirement]])
    decodedEmptyFiniteLiteralEnvironment <- expectRight
        (decodeCache
            Semantic.getSemanticEnvironmentDeltaCache
            (encodeCache
                (Semantic.putSemanticEnvironmentDeltaCache
                    emptyFiniteLiteralEnvironment)))
    decodedEmptyFiniteLiteralHost <- case
            Semantic.semanticEnvironmentBindings
                decodedEmptyFiniteLiteralEnvironment of
        [binding] -> pure binding
        _ -> assertFailure "decoded finite-literal contract changed its bindings"
            >> fail "unreachable"
    assertEqual "a decoded finite literal cannot have an empty spine"
        (Left Semantic.FormationContractFiniteSetLiteralProviderEmpty)
        (fmap (const ())
            (materializeWith directBindings noStructures
                decodedEmptyFiniteLiteralHost))
    providerEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta
            [hostBinding [providerRequirement]])
    assertEqual "provider-valued formation contract cache round trip"
        (Right providerEnvironment)
        (decodeCache
            Semantic.getSemanticEnvironmentDeltaCache
            (encodeCache
                (Semantic.putSemanticEnvironmentDeltaCache
                    providerEnvironment)))
    let contractedProviderLookup reference
            | reference == requiredReference = Just requiredBinding
            | reference == providerReference =
                Just
                    (Semantic.semanticGlobalBindingWithContract
                        expressionSetHostKey
                        (Semantic.semanticBindingLabel "contracted provider")
                        (Semantic.GlobalReference expressionSetHostObject)
                        (Just (contract [requirement 0])))
            | otherwise = Nothing
    assertEqual "a contract provider cannot recursively carry a contract"
        (Left
            (Semantic.FormationContractProviderContracted providerReference))
        (fmap (const ())
            (materializeWith contractedProviderLookup noStructures
                (hostBinding [providerRequirement])))
    let pairRequirement = Semantic.GlobalAtomTemplate
            requiredHead
            (Vector.singleton
                (Semantic.TemplateOrderedPair
                    (Semantic.TemplateVariable
                        (Semantic.OccurrenceArgumentIx 0))
                    (Semantic.TemplateVariable
                        (Semantic.OccurrenceArgumentIx 0))))
    assertEqual "ordered pairs remain outside formation-contract mode"
        (Left Semantic.FormationContractOrderedPairUnsupported)
        (fmap (const ())
            (materializeWith directBindings noStructures
                (hostBinding [pairRequirement])))
    let opaqueExpressionSetHost = Semantic.semanticGlobalBindingWithContract
            expressionSetHostKey
            (Semantic.semanticBindingLabel "opaque expression set host")
            (Semantic.GlobalReference predicate)
            (Just (contract [requirement 0]))
    assertEqual "opaque expression set host"
        (Left
            (Semantic.FormationContractHostSignatureUnsupported
                expressionSetHostKey
                (Semantic.semanticGlobalKeyType expressionSetHostKey)))
        (fmap (const ())
            (Semantic.materializeResolvedGlobalBinding
                directBindings noStructures (fixtureClosure fixture)
                slot opaqueExpressionSetHost))
    for_
        [ ( "transparent abbreviation set host"
          , Semantic.TransparentExpansion expressionSetHostObject
          )
        , ( "contextual abbreviation set host"
          , Semantic.ContextualTransparentExpansion
                expressionSetHostObject
                (Map.singleton Raw.CarrierSymbol (Identity.fieldId owner (localDeclarationOrdinal 0) (structureFieldSlot 0), predicate))
          )
        ]
        \(label, target) -> do
            let unsupportedBinding =
                    Semantic.semanticGlobalBindingWithContract
                        expressionSetHostKey
                        (Semantic.semanticBindingLabel label)
                        target
                        (Just (contract [requirement 0]))
            assertEqual (Text.unpack label)
                (Left
                    (Semantic.FormationContractHostSignatureUnsupported
                        expressionSetHostKey
                        (Semantic.semanticGlobalKeyType expressionSetHostKey)))
                (fmap (const ())
                    (Semantic.materializeResolvedGlobalBinding
                        directBindings noStructures (fixtureClosure fixture)
                        slot unsupportedBinding))
    let manifest = Builtin.builtinStructureManifest (localDeclarationOrdinal 0)
        field = Builtin.builtinCarrierFieldId manifest
        theory = fixtureTheory fixture
    fieldClosure <- expectRight (Identity.extendObjectClosure (fixtureClosure fixture)
        [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field])
    inputs <- expectRight (Builtin.builtinStructureInputs fieldClosure manifest)
    root :| [onesorted] <- expectRight (Schema.resolveStructureBatch (const Nothing) inputs)
    let rootObject = Identity.transparentObject theory (Predicate.structurePredicateType root) (Predicate.structurePredicateBody root)
    rootClosure <- expectRight (Identity.extendObjectClosure fieldClosure [rootObject])
    registration <- expectRight (Predicate.checkPendingStructureRegistration rootClosure root (Identity.assertedObjectId rootObject))
    let structureHead = Semantic.pendingStructureNotionHead registration
        structureRequirement = Semantic.StructureAtomTemplate structureHead
            (Vector.singleton (Semantic.TemplateVariable (Semantic.OccurrenceArgumentIx 0)))
    assertEqual "identity-only structure heads require the exact visible interface"
        (Left (Semantic.FormationContractStructureMissing (Schema.resolvedSchemaId root)))
        (fmap (const ()) (materializeWith directBindings (const Nothing) (hostBinding [structureRequirement])))
    _ <- expectRight (Semantic.materializeResolvedGlobalBinding directBindings
        (\identity -> if identity == Schema.resolvedSchemaId root then Just registration else Nothing)
        rootClosure slot (hostBinding [structureRequirement]))
    let shape = Semantic.semanticRecordShapeKey onesorted
        exact = Semantic.ExactStructureAtomTemplate shape (Semantic.TemplateVariable (Semantic.OccurrenceArgumentIx 0))
        materializeExact visible atom = Semantic.materializeResolvedGlobalBindingWithFields
            directBindings noStructures (const Nothing) visible rootClosure slot (hostBinding [atom])
        shapeEncoding encodedFields = encodeCache do
            putCacheTag 1
            putCacheList (\() -> do
                putCacheTag 0
                putCacheTag 3
                putCacheList (\(identity, selector, projection) ->
                    Identity.putFieldIdCache identity >> Identity.putObjectIdCache selector >> Identity.putObjectIdCache projection) encodedFields
                putCacheTag 0
                putCacheNatural 0) [()]
        fields = [(Schema.resolvedFieldIdentity value, Schema.resolvedFieldSelector value, Schema.resolvedFieldProjection value)
            | value <- Map.elems (Schema.resolvedSchemaFields onesorted)]
        premise key = Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles
            (Semantic.RulePremiseAtom (Semantic.ExactStructureAtomTemplate key
                (Semantic.TemplateVariable (Semantic.ViewVariableIx 0))) :| []))
    for_ [premise shape, premise (Semantic.semanticRecordShapeKey root)] \value ->
        assertEqual "empty and nonempty exact shapes have canonical bounded round trips" (Right value)
            (decodeCache Semantic.getProviderResultPremisesCache
                (encodeCache (Semantic.putProviderResultPremisesCache value)))
    void (expectRight (materializeExact (Set.singleton shape) exact))
    assertEqual "a decoded shape needs a matching visible catalogue entry"
        (Left (Semantic.FormationContractRecordShapeMissing shape))
        (const () <$> materializeExact Set.empty exact)
    case decodeCache Semantic.getProviderResultPremisesCache (shapeEncoding (fields <> fields)) of
        Left _ -> pure ()
        Right _ -> assertFailure "duplicate shape fields were accepted"
    Semantic.ProviderResultGuarded (Semantic.RulePremiseBundles (Semantic.RulePremiseAtom mismatching :| [])) <-
        expectRight (decodeCache Semantic.getProviderResultPremisesCache
        (shapeEncoding [(identity, projection, selector) | (identity, selector, projection) <- fields]))
    case materializeExact (Set.singleton shape) (fmap (const (Semantic.TemplateVariable (Semantic.OccurrenceArgumentIx 0))) mismatching) of
        Left Semantic.FormationContractRecordShapeMissing{} -> pure ()
        _ -> assertFailure "a decoded shape with mismatching object associations was materialized"
    assertEqual "resolved host reference"
        hostReference
        (Semantic.resolvedBindingRef resolved)

    let laterSlot =
            Semantic.declarationSlot owner (localDeclarationOrdinal 1)
        laterReference = Semantic.globalBindingRef laterSlot requiredKey
        laterRequirement = Semantic.GlobalAtomTemplate
            (Semantic.NounNotionHead laterReference)
            (Vector.singleton
                (Semantic.TemplateVariable
                    (Semantic.OccurrenceArgumentIx 0)))
        forwardHost = hostBinding [laterRequirement]
    forwardEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta [forwardHost])
    assertEqual "later declaration is not visible during materialization"
        (Left
            (Semantic.SemanticEnvironmentBindingMaterializationFailed
                hostReference
                (Semantic.FormationContractGlobalBindingMissing
                    laterReference)))
        (fmap (const ())
            (Semantic.materializeSemanticEnvironmentDelta
                (const Nothing) (const Nothing) (const Nothing) Set.empty (fixtureClosure fixture)
                slot forwardEnvironment))

    sameDeltaEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta
            (List.sortOn Semantic.semanticGlobalBindingKey
                [hostBinding [requirement 0], requiredBinding]))
    sameDelta <- expectRight
        (Semantic.materializeSemanticEnvironmentDelta
            (const Nothing) (const Nothing) (const Nothing) Set.empty (fixtureClosure fixture)
            slot sameDeltaEnvironment)
    assertEqual "same-declaration bindings are staged together"
        2 (length sameDelta)

    structureEnvironment <- expectRight
        (Semantic.semanticEnvironmentDelta [hostBinding [structureRequirement]])
    structuresMaterialized <- expectRight
        (Semantic.materializeSemanticEnvironmentDelta (const Nothing)
            (\identity -> if identity == Schema.resolvedSchemaId root then Just registration else Nothing)
            (const Nothing) (Set.singleton (Semantic.semanticRecordShapeKey root)) rootClosure slot structureEnvironment)
    assertEqual "binding contracts consume the completed checked structure environment"
        1 (length structuresMaterialized)

separatesSyntaxAndSemantics :: Assertion
separatesSyntaxAndSemantics = do
    fixture <- makeFixture
    firstSyntax <- makeSyntax "first"
    secondSyntax <- makeSyntax "second"
    assertBool
        "notation changes syntax identity"
        ( Syntax.moduleSyntaxAssertedId firstSyntax
            /= Syntax.moduleSyntaxAssertedId secondSyntax
        )
    assertEqual
        "notation does not enter semantic prefix identity"
        (fixtureNextPrefix fixture)
        (Semantic.nextPrefixContextId
            (fixtureInitialPrefix fixture)
            (fixtureDelta fixture))

roundTripsSemanticState :: Assertion
roundTripsSemanticState = do
    fixture <- makeFixture
    assertEqual
        "semantic interface cache round trip"
        (Right (fixtureInterface fixture))
        (decodeCache
            Semantic.getSemanticInterfaceCache
            (encodeCache
                (Semantic.putSemanticInterfaceCache
                    (fixtureInterface fixture))))
    assertEqual
        "walking-subset environment delta round trip"
        (Right Semantic.emptySemanticEnvironmentDelta)
        (decodeCache
            Semantic.getSemanticEnvironmentDeltaCache
            (encodeCache
                (Semantic.putSemanticEnvironmentDeltaCache
                    Semantic.emptySemanticEnvironmentDelta)))

roundTripsSemanticGlobalKeys :: Assertion
roundTripsSemanticGlobalKeys = do
    fixture <- makeFixture
    let unary = Raw.HoleCons (Raw.TokenCons (Raw.Command "f") Raw.End)
        plural = Raw.HoleCons (Raw.TokenCons (Raw.Word "things") Raw.End)
        verbSurfaces =
            checkedVerbSurfaces
                (Raw.TokenCons (Raw.Word "follows") unary)
                (Raw.TokenCons (Raw.Word "follow") unary)
        keys =
            [ Semantic.SemanticLeftAdjective
                Semantic.OrdinaryAdjectiveReading unary
            , Semantic.SemanticRightAdjective
                Semantic.StructureAdjectiveReading unary
            , Semantic.SemanticFunctionPhrase unary plural
            , Semantic.SemanticNoun unary plural
            , Semantic.SemanticVerb verbSurfaces
            , Semantic.SemanticRelation
                (Raw.Command "rel")
                (Raw.ParameterArity 2)
            , Semantic.SemanticExpressionFunction unary
            , Semantic.SemanticTypedConstant
                (Raw.Variable "Phi")
                (Core.TyArrow Core.TySet Core.TyProp)
            , Semantic.SemanticPrefixPredicate "Pred" 3
            ]
        target =
            Identity.intrinsicObjectId
                (fixtureTheory fixture)
                Core.Empty
        bindings =
            List.sortOn Semantic.semanticGlobalBindingKey
                ( case keys of
                    [] -> []
                    first : rest ->
                        Semantic.semanticGlobalBinding
                            first
                            (Semantic.semanticBindingLabel "fixture-first")
                            (Semantic.ContextualTransparentExpansion
                                target
                                (Map.singleton
                                    (Raw.StructSymbol "operation")
                                    (Identity.fieldId (fixtureOwner fixture) (localDeclarationOrdinal 0) (structureFieldSlot 0), target)))
                            : [ Semantic.semanticGlobalBinding
                                    key
                                    (Semantic.semanticBindingLabel "fixture")
                                    (Semantic.GlobalReference target)
                              | key <- rest
                              ]
                )
    delta <- evaluate . force =<< expectRight (Semantic.semanticEnvironmentDelta bindings)
    assertEqual "binding cache round trip"
        (Right delta)
        (decodeCache
            Semantic.getSemanticEnvironmentDeltaCache
            (encodeCache
                (Semantic.putSemanticEnvironmentDeltaCache delta)))
    let malformedVerbBytes = encodeCache do
            putCacheTag 0x04
            Syntax.putPatternCache
                (Raw.patternFromHoley
                    [Just (Raw.Word "covers"), Nothing])
            Syntax.putPatternCache
                (Raw.patternFromHoley
                    [Just (Raw.Word "cover"), Just (Raw.Word "everything")])
    case decodeCache Semantic.getSemanticGlobalKeyCache malformedVerbBytes of
        Left{} -> pure ()
        Right key ->
            assertFailure
                ("accepted malformed semantic verb surfaces: " <> show key)
    case bindings of
        first : second : _ -> do
            assertEqual "rejects noncanonical order"
                (Left Semantic.NonCanonicalSemanticGlobalBindingOrder)
                (Semantic.semanticEnvironmentDelta
                    (second : first : drop 2 bindings))
            assertEqual "rejects duplicate key"
                (Left
                    (Semantic.DuplicateSemanticGlobalKey
                        (Semantic.semanticGlobalBindingKey first)))
                (Semantic.semanticEnvironmentDelta [first, first])
        _ -> assertFailure "semantic key fixture is unexpectedly empty"

checkedVerbSurfaces :: Raw.Pattern -> Raw.Pattern -> Raw.VerbSurfaces
checkedVerbSurfaces singular base =
    case Raw.checkVerbSurfaces
            (Raw.patternToHoley singular)
            (Raw.patternToHoley base) of
        Right surfaces -> surfaces
        Left failure ->
            impossible ("invalid semantic verb fixture: " <> show failure)

keysExactInputs :: Assertion
keysExactInputs = do
    fixture <- makeFixture
    let authority =
            Authority.factAuthority
                (fixtureTheorem fixture)
                Authority.cleanAuthoritySafety
    certificate <- expectRight
        (Authority.validationCertificate
            authority
            (Authority.CheckedSourceProof Authority.NoExternalProofUse))
    let theorem =
            Identity.theoremId
                (fixtureTheorem fixture)
        firstProof =
            Semantic.proofValidationKey
                theorem
                (Semantic.proofSyntaxId "proof-a")
                (fixtureInitialPrefix fixture)
        secondProof =
            Semantic.proofValidationKey
                theorem
                (Semantic.proofSyntaxId "proof-b")
                (fixtureInitialPrefix fixture)
        laterContext =
            Semantic.proofValidationKey
                theorem
                (Semantic.proofSyntaxId "proof-a")
                (fixtureNextPrefix fixture)
    assertBool
        "proof syntax is an exact validation input"
        (firstProof /= secondProof)
    assertBool
        "semantic predecessor is an exact validation input"
        (firstProof /= laterContext)
    let proofRecord =
            Semantic.proofValidationRecord
                firstProof certificate
        declarationKey =
            Semantic.declarationValidationKey
                (Semantic.declarationSyntaxId "declaration")
                (fixtureInitialPrefix fixture)
                []
                [theorem, theorem]
        declarationRecord =
            Semantic.declarationValidationRecord
                declarationKey
                [certificate, certificate]
    assertEqual
        "proof validation record cache round trip"
        (Right proofRecord)
        (decodeCache
            Semantic.getProofValidationRecordCache
            (encodeCache
                (Semantic.putProofValidationRecordCache
                    proofRecord)))
    assertEqual
        "ordered declaration certificates retain repetitions"
        (Right declarationRecord)
        (decodeCache
            Semantic.getDeclarationValidationRecordCache
            (encodeCache
                (Semantic.putDeclarationValidationRecordCache
                    declarationRecord)))
    firstParsedKey <- expectRight
        (parsedModuleKey
                (fixtureSourceContentId "source-a")
                Syntax.baseSyntaxInterfaceId
                [])
    secondParsedKey <- expectRight
        (parsedModuleKey
                (fixtureSourceContentId "source-b")
                Syntax.baseSyntaxInterfaceId
                [])
    directSyntax <- makeSyntax "direct"
    let directSyntaxId =
            Syntax.moduleSyntaxAssertedId directSyntax
    assertEqual
        "parsed identity rejects duplicate direct syntax"
        (Left
            (DuplicateParsedDirectSyntaxInput
                directSyntaxId))
        (parsedModuleKey
            (fixtureSourceContentId "source-a")
            Syntax.baseSyntaxInterfaceId
            [directSyntaxId, directSyntaxId])
    let
        firstParsed =
            parsedModuleId firstParsedKey "parsed"
        secondParsed =
            parsedModuleId secondParsedKey "parsed"
    firstArtefactKey <- expectRight
        (Semantic.moduleArtefactKey
            (fixtureOwner fixture)
            firstParsed
            []
            (fixtureTheory fixture))
    secondArtefactKey <- expectRight
        (Semantic.moduleArtefactKey
            (fixtureOwner fixture)
            secondParsed
            []
            (fixtureTheory fixture))
    let firstArtefact =
            Semantic.moduleArtefactId firstArtefactKey
        secondArtefact =
            Semantic.moduleArtefactId secondArtefactKey
    assertBool
        "module artefact binds parsed source identity"
        (firstArtefact /= secondArtefact)
    let semanticId =
            Semantic.semanticInterfaceAssertedId
                (fixtureInterface fixture)
    assertEqual
        "prefix identity rejects duplicate direct semantics"
        (Left
            (Semantic.DuplicateInitialPrefixSemanticInput
                semanticId))
        (Semantic.initialPrefixContextId
            (fixtureTheory fixture)
            (fixtureOwner fixture)
            [semanticId, semanticId])
    assertEqual
        "module artefact key cache round trip"
        (Right firstArtefactKey)
        (decodeCache
            Semantic.getModuleArtefactKeyCache
            (encodeCache
                (Semantic.putModuleArtefactKeyCache
                    firstArtefactKey)))
    syntax <- makeSyntax "artefact"
    let artefactResult =
            Semantic.moduleArtefactResult
                firstArtefactKey
                (Syntax.moduleSyntaxAssertedId syntax)
                (Semantic.semanticInterfaceAssertedId
                    (fixtureInterface fixture))
                []
    assertEqual
        "module artefact root round trip"
        (Right artefactResult)
        (decodeCache
            (Semantic.getModuleArtefactResultCache
                firstArtefact)
            (encodeCache
                (Semantic.putModuleArtefactResultCache
                    artefactResult)))


data Fixture = Fixture
    { fixtureTheory :: !Identity.TheoryId
    , fixtureClosure :: !Identity.CheckedObjectClosure
    , fixtureOwner :: !ModuleName
    , fixtureTheorem :: !Identity.TheoremRef
    , fixtureDelta :: !Semantic.DeclarationInterfaceDelta
    , fixtureInterface :: !Semantic.SemanticInterface
    , fixtureInitialPrefix :: !Semantic.PrefixContextId
    , fixtureNextPrefix :: !Semantic.PrefixContextId
    }

makeFixture :: IO Fixture
makeFixture = do
    foundation <- expectRight Foundation.checkedFoundation
    let namespaceDigest =
            hashBlake2b256 "semantic-test-namespace\NULroot"
    relative <- expectRight (safeRelativePath "module.tex")
    closure <- expectRight
        (Identity.validateObjectClosure
            (Identity.theoryId foundation)
            [])
    proposition <- expectRight
        (Identity.validatePropositionContent
            closure
            Core.CFalsum)
    let theory =
            Identity.theoryId foundation
        owner =
            moduleNameFromParts
                (sourceNamespaceIdFromDigest namespaceDigest)
                relative
        reference =
            Identity.theoremRef
                theory
                (Identity.checkedPropositionId proposition)
        authority =
            Authority.factAuthority
                reference
                Authority.cleanAuthoritySafety
        occurrence =
            Semantic.semanticFactOccurrence Semantic.GeneralFactPurpose
                (Semantic.factSlot owner (localFactOrdinal 0))
                authority
                Semantic.SearchEligible
        slot =
            Semantic.declarationSlot
                owner
                (localDeclarationOrdinal 0)
        fingerprint =
            Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
                (Semantic.factSlot owner (localFactOrdinal 0))
                authority
        providerPattern =
            Raw.HoleCons (Raw.TokenCons (Raw.Word "provider") Raw.End)
        providerReference = Semantic.globalBindingRef
            slot
            (Semantic.SemanticExpressionFunction providerPattern)
        resultHead = Semantic.NounNotionHead
            (Semantic.globalBindingRef
                slot
                (Semantic.SemanticNoun
                    (Raw.TokenCons (Raw.Word "result") Raw.End)
                    (Raw.TokenCons (Raw.Word "results") Raw.End)))
        unconditionalResultHead = Semantic.NounNotionHead
            (Semantic.globalBindingRef
                slot
                (Semantic.SemanticNoun
                    (Raw.TokenCons (Raw.Word "total-result") Raw.End)
                    (Raw.TokenCons (Raw.Word "total-results") Raw.End)))
        variable = Semantic.ViewVariableIx 0
        variableTerm = Semantic.TemplateVariable variable
        providerRule = Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterProviderResult (Semantic.ProviderResultRule (Semantic.resultProviderTemplate
                (Semantic.GlobalSourceProvider providerReference)
                (Vector.singleton variableTerm)) (Semantic.ProviderResultGuarded
                (Semantic.RulePremiseBundles
                    (Semantic.RulePremiseAtom
                        (Semantic.GlobalAtomTemplate
                            resultHead (Vector.singleton variableTerm)) :| []))) (Semantic.GlobalAtomTemplate
                resultHead
                (Vector.singleton Semantic.ResultRuleProviderValue))))
        unconditionalProviderRule = Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterProviderResult (Semantic.ProviderResultRule (Semantic.resultProviderTemplate
                (Semantic.GlobalSourceProvider providerReference)
                (Vector.singleton variableTerm)) Semantic.ProviderResultUnconditional (Semantic.GlobalAtomTemplate
                unconditionalResultHead
                (Vector.singleton Semantic.ResultRuleProviderValue))))
        nullaryClassification =
            Semantic.Registration fingerprint Notion.ConjunctionHere (Semantic.RegisterNullaryProvider (Semantic.NullaryProviderRule Semantic.EmptySetProvider resultHead))
    delta <- expectRight
        (Semantic.declarationInterfaceDelta
            slot
            [occurrence]
            [ Semantic.semanticAlias
                (Semantic.semanticName "theorem")
                (Semantic.semanticFactOccurrenceFingerprint Semantic.GeneralFactPurpose
                    (Semantic.factSlot owner (localFactOrdinal 0))
                    authority)
            ]
            []
            [Identity.checkedPropositionId proposition]
            []
            ([nullaryClassification] <> [providerRule, unconditionalProviderRule])
            Semantic.emptySemanticEnvironmentDelta)
    interface <- expectRight
        (Semantic.semanticInterface owner [] [delta])
    initial <- expectRight
        (Semantic.initialPrefixContextId theory owner [])
    pure
        Fixture
            { fixtureTheory = theory
            , fixtureClosure = closure
            , fixtureOwner = owner
            , fixtureTheorem = reference
            , fixtureDelta = delta
            , fixtureInterface = interface
            , fixtureInitialPrefix = initial
            , fixtureNextPrefix =
                Semantic.nextPrefixContextId initial delta
            }

makeSyntax :: Text -> IO Syntax.ModuleSyntaxInterface
makeSyntax command = do
    delta <- expectRight
        (Syntax.canonicalSyntaxDelta
            [Syntax.CanonicalStructureOperation command])
    expectRight (Syntax.moduleSyntaxInterface [] delta)

fixtureSourceContentId :: ByteString -> SourceContentId
fixtureSourceContentId bytes =
    either
        (impossible . show)
        id
        (decodeCache
            getSourceContentIdCache
            (encodeCache
                (putCacheDigest
                    (hashCacheFields
                        "semantic-test-source"
                        [bytes]))))

expectPureRight :: Show error => Either error value -> value
expectPureRight = \case
    Left failure -> error ("unexpected fixture failure: " <> show failure)
    Right value -> value

expectRight :: Show error => Either error value -> IO value
expectRight = \case
    Left err ->
        assertFailure (show err) >> fail "unreachable"
    Right value ->
        pure value
