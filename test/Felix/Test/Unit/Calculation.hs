{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Calculation (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Calculation
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Notion.SourceEvidence qualified as SourceEvidence
import Felix.Cache.Codec (encodeCache, decodeCache)
import Felix.Module qualified as Module
import Felix.Math.Codec (hashBlake2b256)
import Felix.Source (safeRelativePath)
import Data.Word (Word)
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Felix.Test.Support.GlobalTyping
import Data.Functor.Identity (Identity, runIdentity)
import Data.Map.Strict qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "calculation patterns"
    [ testCase "shares parameter bindings across both inputs" sharedBindings
    , testCase "retains ambient captures but rejects endpoint and internal binder captures" scopedBindings
    , testCase "uses beta normalization without eta expansion" normalization
    , testCase "rejects applied parameters, including below other constructors" appliedParameters
    , testCase "unifies both inputs with an occurs check" overlap
    , testCase "work exhaustion is distinct from a failed match" budget
    , testCase "admits the actual telescope and rejects invalid endpoint roles" schemaAdmission
    , testCase "rejects overlap and deduplicates an identical occurrence" registryCoherence
    , testCase "finishes a registry scan after finding a match" completeRegistryScan
    , testCase "round trips composition sources and fingerprints semantic metadata" compositionCodec
    , testCase "supports heterogeneous relators and equality of logical functions" concreteEndpointTypes
    ]

typing :: GlobalTyping ObjectId
typing = fixtureGlobalTyping (globalTypingFixture [])
checked :: [CoreType] -> CanonicalTerm ObjectId -> ScopedCheckedCore ObjectId
checked context term = either (error . show) id (checkScopedCanonicalCore typing context term)
run :: CalculationWork Identity a -> Either CalculationError a
run action = fst (runIdentity (runCalculationWork defaultCalculationWork action))
expect :: Show e => Either e a -> a
expect = either (error . show) id
rel :: [CoreType] -> CanonicalTerm ObjectId -> CalculationWork Identity Relator
rel context body = prepareRelator typing (checked context (CLam TySet (CLam TySet body)))
pair, member :: CanonicalTerm ObjectId -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
pair a b = CApp (CApp (CIntrinsic OrderedPair) a) b
member a b = CApp (CApp (CIntrinsic Member) a) b
relation, wrapped :: CanonicalTerm ObjectId -> CanonicalTerm ObjectId
relation r = member (pair (CBound 1) (CBound 0)) r
emptySet :: CanonicalTerm ObjectId
emptySet = CIntrinsic Empty
wrapped r = pair r emptySet
parameterPattern :: CalculationWork Identity CompositionPattern
parameterPattern = do
    r <- rel [TySet] (relation (CBound 2))
    prepareCompositionPattern (Map.singleton 0 TySet) r r
matches :: CompositionPattern -> Relator -> Relator -> CalculationWork Identity Bool
matches pattern' a b = isJust <$> matchCompositionPattern pattern' a b

sharedBindings :: Assertion
sharedBindings = do
    let result = run do
            pattern' <- parameterPattern
            a <- rel [] (relation emptySet)
            b <- rel [] (relation (wrapped emptySet))
            (,) <$> matches pattern' a a <*> matches pattern' a b
    result @?= Right (True,False)

scopedBindings :: Assertion
scopedBindings = do
    let result = run do
            pattern' <- parameterPattern
            ambient <- rel [TySet] (relation (CBound 2))
            endpoint <- rel [TySet] (relation (CBound 0))
            scoped <- matchCompositionPattern pattern' ambient ambient
            escapes <- matches pattern' endpoint endpoint
            law <- rel [TySet] (CForall TySet (member (pair (CBound 2) (CBound 1)) (CBound 3)))
            internalPattern <- prepareCompositionPattern (Map.singleton 0 TySet) law law
            bad <- rel [] (CForall TySet (member (pair (CBound 2) (CBound 1)) (CBound 0)))
            internal <- matches internalPattern bad bad
            pure (scopedCoreTerm <$> (scoped >>= Map.lookup 0),escapes,internal)
    result @?= Right (Just (CBound 0),False,False)

normalization :: Assertion
normalization = do
    let result = run do
            pattern' <- parameterPattern
            a <- rel [] (relation (CApp (CLam TySet (CBound 0)) emptySet))
            b <- rel [] (relation emptySet)
            normalized <- matches pattern' a b
            let function = TyArrow TySet TySet
                identity = CLam TySet (CBound 0)
            law <- rel [function] (CEq function (CBound 2) identity)
            functionPattern <- prepareCompositionPattern (Map.singleton 0 function) law law
            direct <- rel [function] (CEq function (CBound 2) identity)
            eta <- rel [function] (CEq function (CLam TySet (CApp (CBound 3) (CBound 0))) identity)
            unchanged <- matches functionPattern direct eta
            equality <- rel [] (CEq TySet (CBound 1) (CBound 0))
            negative <- rel [] (CNot (CEq TySet (CBound 1) (CBound 0)))
            pure (normalized,unchanged,relatorIsEquality equality,relatorIsEquality negative)
    result @?= Right (True,False,True,False)

appliedParameters :: Assertion
appliedParameters = case run (do
    r <- rel [TyArrow TySet TySet] (CNot (CEq TySet (CApp (CBound 2) (CBound 1)) (CBound 0)))
    prepareCompositionPattern (Map.singleton 0 (TyArrow TySet TySet)) r r) of
        Left CalculationInvalid{} -> pure ()
        _ -> assertFailure "an applied function parameter was accepted"

overlap :: Assertion
overlap = do
    let result = run do
            generic <- parameterPattern
            a <- rel [] (relation emptySet)
            b <- rel [] (relation (wrapped emptySet))
            ground <- prepareCompositionPattern Map.empty a a
            incompatible <- prepareCompositionPattern Map.empty a b
            first <- rel [TySet] (relation (CBound 2))
            second <- rel [TySet] (relation (wrapped (CBound 2)))
            p <- prepareCompositionPattern (Map.singleton 0 TySet) first second
            q <- prepareCompositionPattern (Map.singleton 0 TySet) second first
            (,,) <$> compositionPatternsOverlap generic ground
                <*> compositionPatternsOverlap generic incompatible
                <*> compositionPatternsOverlap p q
    result @?= Right (True,False,False)

budget :: Assertion
budget = do
    let (pattern',a) = expect (run ((,) <$> parameterPattern <*> rel [] (relation emptySet)))
        action = matches pattern' a a
        (answer,remaining) = runIdentity (runCalculationWork defaultCalculationWork action)
        used = defaultCalculationWork - remaining
    answer @?= Right True
    runIdentity (runCalculationWork used action) @?= (Right True,0)
    fst (runIdentity (runCalculationWork (used-1) action)) @?= Left CalculationWorkExhausted

-- These tests exercise logical admission directly; declaration integration
-- separately authenticates source templates and provider ownership.
sourceDescription :: Semantic.AbbreviationExpansion
sourceDescription = Semantic.PropositionExpansion (SourceEvidence.SourceResidual Nothing) []

lawMetadata :: Semantic.SemanticRelationComposition
lawMetadata = Semantic.SemanticRelationComposition (0,2,3)
    (Vector.singleton sourceDescription) relationSource relationSource relationSource
  where relationSource = Semantic.SemanticRelationSource sourceDescription Vector.empty

lawTheorem :: Bool -> CanonicalTerm ObjectId
lawTheorem negative = foldr CForall body (replicate 4 TySet)
  where
    related a b = (if negative then CNot else id) (member (pair a b) (CBound 2))
    body = CImp CTruth (CImp (CAnd (related (CBound 3) (CBound 1)) (related (CBound 1) (CBound 0)))
        (related (CBound 3) (CBound 0)))

lawOwner :: Module.ModuleName
lawOwner = Module.moduleNameFromParts
    (Module.sourceNamespaceIdFromDigest (hashBlake2b256 "calculation-laws"))
    (expect (safeRelativePath "calculation-laws.tex"))

lawSlot :: Word -> Semantic.FactSlot
lawSlot ordinal = Semantic.factSlot lawOwner (Module.localFactOrdinal (fromIntegral ordinal))

logicalLaw :: Word -> Bool -> CalculationWork Identity CheckedCompositionLaw
logicalLaw ordinal negative = prepareCompositionLaw typing (\_ _ _ _ -> pure ())
    (lawSlot ordinal) (checked [] (lawTheorem negative)) lawMetadata

lawOccurrence :: Word -> Bool -> Semantic.SemanticRelationComposition -> Semantic.SemanticFactOccurrence
lawOccurrence ordinal negative metadata = Semantic.semanticFactOccurrenceWithRelationComposition
    Semantic.GeneralFactPurpose (lawSlot ordinal) authority Semantic.SearchEligible metadata
  where
    closure = fixtureObjectClosure (globalTypingFixture [])
    proposition = expect (Identity.validatePropositionContent closure (lawTheorem negative))
    authority = Authority.factAuthority
        (Identity.theoremRef (Identity.checkedObjectClosureTheory closure) (Identity.checkedPropositionId proposition))
        Authority.cleanAuthoritySafety

lawFingerprint :: Word -> Bool -> Semantic.SemanticFactOccurrenceFingerprint
lawFingerprint ordinal negative = Semantic.semanticFactFingerprint (lawOccurrence ordinal negative lawMetadata)

schemaAdmission :: Assertion
schemaAdmission = do
    let accepted = expect (run (logicalLaw 0 False))
    Semantic.compositionEndpointPositions (compositionLawMetadata accepted) @?= (0,2,3)
    Vector.length (compositionLawConditions accepted) @?= 1
    let invalidMetadata = lawMetadata{Semantic.compositionEndpointPositions = (0,0,3)}
        invalidSource = lawMetadata{Semantic.compositionLeftSource = Semantic.SemanticRelationSource
            (Semantic.PropositionExpansion
                (SourceEvidence.SourceInputs Nothing [SourceEvidence.SourceInput [] (Semantic.ExpansionFormal 2)]) []) Vector.empty}
        erasedCapture = lawMetadata{Semantic.compositionLeftSource = Semantic.SemanticRelationSource
            sourceDescription (Vector.singleton (Semantic.ExpansionFormal 2))}
        check metadata = run (prepareCompositionLaw typing (\_ _ _ _ -> pure ()) (lawSlot 0)
            (checked [] (lawTheorem False)) metadata)
    for_ [invalidMetadata,invalidSource,erasedCapture] \metadata -> case check metadata of
        Left CalculationInvalid{} -> pure ()
        _ -> assertFailure "invalid endpoint roles were accepted"
    let unused = CForall TySet (lawTheorem False)
        unusedMetadata = lawMetadata{Semantic.compositionEndpointPositions = (1,3,4)}
    case run (prepareCompositionLaw typing (\_ _ _ _ -> pure ()) (lawSlot 0) (checked [] unused) unusedMetadata) of
        Left CalculationInvalid{} -> pure ()
        _ -> assertFailure "an undetermined parameter was accepted"

registryCoherence :: Assertion
registryCoherence = do
    let firstLaw = expect (run (logicalLaw 0 False))
        secondLaw = expect (run (logicalLaw 1 False))
        firstFingerprint = lawFingerprint 0 False
        secondFingerprint = lawFingerprint 1 False
        singleton = expect (run (insertCompositionLaw firstFingerprint firstLaw emptyCompositionRegistry))
    length (compositionRegistryEntries (expect (run (insertCompositionLaw firstFingerprint firstLaw singleton)))) @?= 1
    case run (insertCompositionLaw secondFingerprint secondLaw singleton) of
        Left (CalculationInvalid reason) -> assertBool "overlap identifies declarations" ("overlapping composition" `Text.isInfixOf` reason)
        _ -> assertFailure "overlapping laws were registered"
    let negative = expect (run (logicalLaw 2 True))
        both = expect (run (insertCompositionLaw (lawFingerprint 2 True) negative singleton))
    length (compositionRegistryEntries both) @?= 2

completeRegistryScan :: Assertion
completeRegistryScan = do
    let positive = expect (run (logicalLaw 0 False))
        negative = expect (run (logicalLaw 1 True))
        both = expect (run (insertCompositionLaw (lawFingerprint 0 False) positive emptyCompositionRegistry
            >>= insertCompositionLaw (lawFingerprint 1 True) negative))
        (fingerprint,firstLaw) = case compositionRegistryEntries both of
            entry:_ -> entry
            [] -> error "two inserted laws disappeared"
        singleton = expect (run (insertCompositionLaw fingerprint firstLaw emptyCompositionRegistry))
        select registry = selectCompositionLaws registry (compositionLawLeft firstLaw) (compositionLawRight firstLaw)
        (_,afterFirst) = runIdentity (runCalculationWork defaultCalculationWork (select singleton))
        firstCost = defaultCalculationWork - afterFirst
        (result,afterAll) = runIdentity (runCalculationWork defaultCalculationWork (select both))
    length (expect result) @?= 1
    assertBool "the second registry entry is visited" (afterAll < afterFirst)
    case fst (runIdentity (runCalculationWork firstCost (select both))) of
        Left CalculationWorkExhausted -> pure ()
        _ -> assertFailure "an earlier match escaped an exhausted full scan"

compositionCodec :: Assertion
compositionCodec = do
    let occurrence = lawOccurrence 0 False lawMetadata
        reordered = lawOccurrence 0 False lawMetadata{Semantic.compositionEndpointPositions = (2,0,3)}
    assertBool "semantic metadata affects occurrence identity"
        (Semantic.semanticFactFingerprint occurrence /= Semantic.semanticFactFingerprint reordered)
    decodeCache Semantic.getSemanticFactOccurrenceCache (encodeCache (Semantic.putSemanticFactOccurrenceCache occurrence)) @?= Right occurrence

concreteEndpointTypes :: Assertion
concreteEndpointTypes = do
    let action = do
            mixed <- prepareRelator typing (checked []
                (CLam TySet (CLam TyProp (CAnd (CEq TySet (CBound 1) (CBound 1)) (CBound 0)))))
            predicate <- applyRelator typing mixed (checked [] emptySet) (checked [] CTruth)
            let function = TyArrow TySet TySet
                identity = checked [] (CLam TySet (CBound 0))
            equality <- prepareRelator typing (checked [] (CLam function (CLam function (CEq function (CBound 1) (CBound 0)))))
            applied <- applyRelator typing equality identity identity
            pure (relatorEndpointTypes mixed,scopedCoreTerm predicate,relatorIsEquality equality,scopedCoreType applied)
    run action @?= Right ((TySet,TyProp),CAnd (CEq TySet emptySet emptySet) CTruth,True,TyProp)
