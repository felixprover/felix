{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Record (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Backend.Problem qualified as Backend
import Felix.Checking.Core qualified as Core
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.GlobalTyping qualified as GlobalTyping
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Record qualified as Record
import Felix.Checking.Record.Proof qualified as RecordProof
import Felix.Checking.SetConstruction qualified as SetConstruction
import Felix.Module
import Felix.Math.Codec (mathematicalDigestHex)
import Felix.Provers qualified as Provers
import Felix.Test.Support.GlobalTyping

import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit



unitTests :: TestTree
unitTests =
    testGroup "Extensional records"
        [ testCase "checks balanced transparent field selectors"
            checksBalancedFieldSelectors
        , testCase "bundles paired field objects without changing them"
            bundlesPairedFieldObjects
        , testCase "keeps transparent projection definitions at the TH0 boundary"
            keepsTransparentProjectionDefinitionsAtTh0Boundary
        , testCase "checks open, exact, aggregate, lookup, and reduct terms"
            checksRecordCalculusTerms
        , testCase "strictly recognizes generated exact global shapes"
            recognizesExactGlobalShapes
        , testCase "classifies record calculus laws at the backend boundary"
            provesRecordCalculusLaws
        , testCase "classifies flattened projection consequences in FOF"
            provesFlattenedProjectionConsequences
        , testCase "classifies transparent aggregate interfaces in FOF"
            provesTransparentAggregateInterfaces
        , testCase "keeps selector identities stable and distinct"
            keepsSelectorIdentitiesStableAndDistinct
        , testCase "prepares selector distinction as compact FOF"
            preparesSelectorDistinctionAsCompactFof
        , testCase "checks canonical record-proof schemas and law identities"
            checksCanonicalRecordProofSchemas
        , testCase "builds and replays deterministic record-proof slices"
            buildsAndReplaysRecordProofSlices
        , testCase "replays every empty-schema law without synthetic fields"
            replaysEmptyRecordSchema
        , testCase "weakens checked finite open shapes by field inclusion"
            weakensFiniteRecordShapes
        ]

replaysEmptyRecordSchema :: Assertion
replaysEmptyRecordSchema = do
    fixture <- makeRecordProofFixture []
    let schema = fixturePreparedSchema fixture
        laws = RecordProof.recordLawInventory schema
        expectedLaws =
            [ Record.RecordExactGraphLaw
            , Record.RecordReductExactLaw
            , Record.RecordReductMembershipLaw
            , Record.RecordProjectionEntryAgreementLaw
            , Record.RecordProjectionGraphAgreementLaw
            , Record.RecordProjectionExtensionalityLaw
            , Record.RecordReductIdentityLaw
            , Record.RecordSelectorDistinctLaw
            , Record.RecordAggregatePairCodedLaw
            , Record.RecordAggregateSelectorClosedLaw
            , Record.RecordAggregateFunctionalLaw
            , Record.RecordAggregateExactLaw
            ]
        globalTyping = Identity.globalTypingFromClosure (fixtureClosure fixture)
        record = Core.CBound 0 :: Core.CanonicalTerm Identity.ObjectId
        exact = Record.recordExactShape [] record
        emptySet = Core.CIntrinsic Core.Empty
        equalityTarget = Core.CForall Core.TySet
            (Core.CForall Core.TySet
                (Core.CImp (Record.recordExactShape [] (Core.CBound 1))
                    (Core.CImp exact
                        (Core.CImp Core.CTruth
                            (Core.CEq Core.TySet (Core.CBound 1) record)))))
    assertEqual "all twelve law occurrences remain distinct" expectedLaws laws
    assertEqual "equal targets share exactly one proposition identity" 11
        (Set.size (Set.fromList
            [ Identity.propositionIdOf (Core.frozenCoreTerm (knownRecordLawTarget schema law))
            | law <- laws
            ]))
    assertEqual "empty open shape is functionality"
        (Record.recordFunctional record) (Record.recordOpenShape [] record)
    assertEqual "empty aggregate is the empty set" emptySet
        (Record.recordAggregate [] :: Core.CanonicalTerm Identity.ObjectId)
    assertEqual "empty exact shape excludes every entry"
        (Core.CAnd (Record.recordFunctional record)
            (Core.CForall Core.TySet
                (Core.CImp
                    (Core.CApp (Core.CApp (Core.CIntrinsic Core.Member)
                        (Core.CBound 0)) (Core.CBound 1))
                    Core.CFalsum)))
        exact
    assertEqual "empty reduct separates with the false predicate"
        (Core.CApp (Core.CApp (Core.CIntrinsic Core.Sep) record)
            (Core.CLam Core.TySet Core.CFalsum))
        (Record.recordReduct [] record)
    checkedShape <- expectRight
        (Core.checkScopedCanonicalCore globalTyping [Core.TySet] exact)
    assertEqual "empty shape lookup retains its subject" (Just (record, []))
        (Record.recognizeRecordExactGlobalShape checkedShape)
    assertEqual "zero-field projection agreement is truth" equalityTarget
        (Core.frozenCoreTerm
            (knownRecordLawTarget schema Record.RecordProjectionExtensionalityLaw))
    assertEqual "exact graph and projection extensionality share a target"
        (knownRecordLawTarget schema Record.RecordExactGraphLaw)
        (knownRecordLawTarget schema Record.RecordProjectionExtensionalityLaw)
    for_ laws \law -> do
        (_proof, replayed, imports) <- buildAndReplayRecordLaw fixture law
        assertEqual ("no guarded-rule authority for " <> show law) Set.empty
            (Kernel.replayedKernelRuleUses replayed)
        assertEqual ("exact imports for " <> show law)
            (Set.fromList [Kernel.importIx i | (i, _) <- zip [0 ..] imports])
            (Kernel.replayedKernelImportUses replayed)

weakensFiniteRecordShapes :: Assertion
weakensFiniteRecordShapes = do
    let field0 = sampleFieldId 3 0
        field1 = sampleFieldId 3 1
        field2 = sampleFieldId 3 2
    for_ [([], []), ([field0], []), ([field0], [field0]),
            ([field0, field1, field2], [field2, field0])] \(childIds, parentIds) -> do
        child <- makeRecordProofFixture childIds
        parent <- makeRecordProofFixture parentIds
        proof <- expectRight
            (RecordProof.buildRecordOpenShapeWeakeningProof
                (fixtureFoundation child)
                (fixtureCheckedSchema child) (fixtureCheckedSchema parent))
        let theory = Identity.theoryId (fixtureFoundation child)
            selectors identities =
                Core.CGlobal . Record.fieldSelectorObjectId theory <$> identities
            targetTerm = Core.CForall Core.TySet
                (Core.CImp
                    (Record.recordOpenShape (selectors childIds) (Core.CBound 0))
                    (Record.recordOpenShape (selectors parentIds) (Core.CBound 0)))
            globalTyping = Identity.globalTypingFromClosure (fixtureClosure child)
        target <- expectRight (Core.checkCanonicalCore globalTyping targetTerm)
        assertEqual "weakening target" (Core.embedClosedCore [] target)
            (KernelProof.builtProofStatement proof)
        replayed <- expectRight
            (Kernel.replayKernelDerivation (fixtureFoundation child)
                Kernel.defaultKernelReplayLimits globalTyping Vector.empty target
                (KernelProof.builtProofDerivation proof))
        assertEqual "weakening uses no global imports" Set.empty
            (Kernel.replayedKernelImportUses replayed)
        assertEqual "weakening uses no foundation axioms" Set.empty
            (Kernel.replayedKernelFoundationUses replayed)
        assertEqual "weakening uses no guarded rules" Set.empty
            (Kernel.replayedKernelRuleUses replayed)
    child <- makeRecordProofFixture [field0]
    parent <- makeRecordProofFixture [field1]
    case RecordProof.buildRecordOpenShapeWeakeningProof
            (fixtureFoundation child)
            (fixtureCheckedSchema child) (fixtureCheckedSchema parent) of
        Left (RecordProof.RecordWeakeningFieldMissing actual) ->
            assertEqual "inclusion reports the missing parent field" field1 actual
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "weakening accepted unrelated field families"
    emptyClosure <- expectRight
        (Identity.validateObjectClosure
            (Identity.theoryId (fixtureFoundation child)) [])
    case RecordProof.checkRecordSchema emptyClosure (fixturePreparedSchema child) of
        Left (RecordProof.RecordSchemaObjectMissing _) -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "an unavailable field resource was checked"
    let theory = Identity.theoryId (fixtureFoundation child)
    selectorOnly <- expectRight
        (Identity.validateObjectClosure theory [Record.fieldSelectorObject theory field0])
    case RecordProof.checkRecordSchema selectorOnly (fixturePreparedSchema child) of
        Left (RecordProof.RecordSchemaObjectMissing actual) ->
            assertEqual "unused projections still require checked resources"
                (Record.fieldProjectionObjectId theory field0) actual
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "an unavailable projection was checked"

knownRecordLawTarget
    :: RecordProof.PreparedRecordSchema
    -> Record.RecordSchemaLaw
    -> Core.FrozenCheckedCore Identity.ObjectId
knownRecordLawTarget schema law =
    either
        (impossible . ("canonical record-law target is unavailable: " <>) . show)
        id
        (RecordProof.recordLawTarget schema law)

knownRecordLawDependencies
    :: RecordProof.PreparedRecordSchema
    -> Record.RecordSchemaLaw
    -> [RecordProof.RecordLawDependency]
knownRecordLawDependencies schema law =
    either
        (impossible . ("canonical record-law dependencies are unavailable: " <>)
            . show)
        id
        (RecordProof.recordLawDependencies schema law)

bundlesPairedFieldObjects :: Assertion
bundlesPairedFieldObjects = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identity = sampleFieldId 0 0
        objects = Record.fieldObjects theory identity
        selector = Record.fieldObjectsSelector objects
        projection = Record.fieldObjectsProjection objects
    assertEqual "selector object"
        (Record.fieldSelectorObject theory identity)
        selector
    assertEqual "selector identity"
        (Record.fieldSelectorObjectId theory identity)
        (Identity.assertedObjectId selector)
    assertEqual "projection object"
        (Record.fieldProjectionObject theory identity)
        projection
    assertEqual "projection identity"
        (Record.fieldProjectionObjectId theory identity)
        (Identity.assertedObjectId projection)

data RecordProofFixture = RecordProofFixture
    { fixtureFoundation
        :: !Foundation.CheckedFoundation
    , fixtureClosure
        :: !Identity.CheckedObjectClosure
    , fixturePreparedSchema
        :: !RecordProof.PreparedRecordSchema
    , fixtureCheckedSchema
        :: !RecordProof.CheckedRecordSchema
    }

makeRecordProofFixture
    :: [Identity.FieldId]
    -> IO RecordProofFixture
makeRecordProofFixture identities = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
    let fields = preparedField theory <$> identities
    closure <- expectRight
        (Identity.validateObjectClosure theory
            (concatMap (preparedFieldObjects theory) identities))
    schema <- expectRight
        (RecordProof.prepareRecordSchema
            theory
            (Identity.globalTypingFromClosure closure)
            fields)
    checkedSchema <- expectRight
        (RecordProof.checkRecordSchema closure schema)
    pure
        (RecordProofFixture
            foundation closure schema checkedSchema)
  where
    preparedField theory identity =
        RecordProof.PreparedRecordField
            identity
            (Record.fieldSelectorObjectId theory identity)
            (Record.fieldProjectionObjectId theory identity)

    preparedFieldObjects theory identity =
        [ Record.fieldSelectorObject theory identity
        , Record.fieldProjectionObject theory identity
        ]

checkedRecordLaw
    :: RecordProofFixture
    -> Record.RecordSchemaLaw
    -> IO RecordProof.CheckedRecordSchemaLaw
checkedRecordLaw fixture =
    expectRight
        . RecordProof.checkRecordSchemaLaw
            (fixtureCheckedSchema fixture)

checkedImportsFor
    :: RecordProofFixture
    -> Record.RecordSchemaLaw
    -> IO [RecordProof.CheckedRecordImport]
checkedImportsFor fixture law =
    traverse checkedImport
        (knownRecordLawDependencies
            (fixturePreparedSchema fixture)
            law)
  where
    theory = Identity.theoryId (fixtureFoundation fixture)
    closure = fixtureClosure fixture
    schema = fixturePreparedSchema fixture

    checkedImport dependency = do
        proposition <- case dependency of
            RecordProof.RecordGeneratedDependency generated ->
                pure (knownRecordLawTarget schema generated)
            RecordProof.RecordSelectorDefinition identity ->
                checkTarget
                    (Core.canonicalDefinitionEquationTarget
                        (Record.fieldSelectorObjectId theory identity)
                        Core.TySet
                        (Record.fieldSelectorBody identity))
            RecordProof.RecordProjectionMembership identity ->
                checkTarget
                    (Record.recordProjectionMembershipLaw
                        (Core.CGlobal
                            (Record.fieldSelectorObjectId theory identity))
                        (Core.CGlobal
                            (Record.fieldProjectionObjectId theory identity)))
        pure (RecordProof.CheckedRecordImport dependency proposition)

    checkTarget =
        expectRight
            . Core.checkCanonicalCore
                (Identity.globalTypingFromClosure closure)

buildAndReplayRecordLaw
    :: RecordProofFixture
    -> Record.RecordSchemaLaw
    -> IO
        ( KernelProof.BuiltProof Identity.ObjectId
        , Kernel.ReplayedKernelDerivation Identity.ObjectId
        , [RecordProof.CheckedRecordImport]
        )
buildAndReplayRecordLaw fixture law = do
    checkedLaw <- checkedRecordLaw fixture law
    imports <- checkedImportsFor fixture law
    proof <- expectRight
        (RecordProof.buildRecordLawProof
            (fixtureFoundation fixture)
            checkedLaw
            imports)
    let target =
            knownRecordLawTarget (fixturePreparedSchema fixture) law
    assertEqual ("record proof target for " <> show law)
        (Core.embedClosedCore [] target)
        (KernelProof.builtProofStatement proof)
    judgements <- Vector.fromList <$> traverse
        (expectRight
            . Kernel.derivationImportJudgement
            . RecordProof.checkedRecordImportProposition)
        imports
    replayed <- expectRight
        (Kernel.replayKernelDerivation
            (fixtureFoundation fixture)
            Kernel.defaultKernelReplayLimits
            (Identity.globalTypingFromClosure (fixtureClosure fixture))
            judgements
            target
            (KernelProof.builtProofDerivation proof))
    pure (proof, replayed, imports)

assertRecordLawAuthority
    :: RecordProofFixture
    -> Record.RecordSchemaLaw
    -> Set Foundation.FoundationAxiomTag
    -> Assertion
assertRecordLawAuthority fixture law expectedFoundation = do
    (_proof, replayed, imports) <-
        buildAndReplayRecordLaw fixture law
    assertEqual ("foundation footprint for " <> show law)
        expectedFoundation
        (Kernel.replayedKernelFoundationUses replayed)
    assertEqual ("import footprint for " <> show law)
        (Set.fromList
            [ Kernel.importIx index
            | (index, _checkedImport) <- zip [0 ..] imports
            ])
        (Kernel.replayedKernelImportUses replayed)
    assertEqual ("guarded-rule footprint for " <> show law)
        Set.empty
        (Kernel.replayedKernelRuleUses replayed)

buildsAndReplaysRecordProofSlices :: Assertion
buildsAndReplaysRecordProofSlices = do
    let identities =
            [sampleFieldId 2 0, sampleFieldId 2 1, sampleFieldId 2 2]
        firstIdentity = sampleFieldId 2 0
        middleIdentity = sampleFieldId 2 1
        finalIdentity = sampleFieldId 2 2
    fixture <- makeRecordProofFixture identities
    assertCanonicalTargets fixture identities
    rejectsWrongDependencyProposition fixture

    traverse_
        (\(law, footprint) ->
            assertRecordLawAuthority fixture law footprint)
        [ ( Record.RecordReductMembershipLaw
          , Set.singleton Foundation.SeparationCharacteristic
          )
        , ( Record.RecordReductIdentityLaw
          , Set.singleton Foundation.SetExtensionality
          )
        , ( Record.RecordReductExactLaw
          , Set.singleton Foundation.OrderedPairFirst
          )
        , ( Record.RecordExactGraphLaw
          , Set.singleton Foundation.SetExtensionality
          )
        , ( Record.RecordAggregatePairCodedLaw
          , Set.fromList
                [ Foundation.EmptyCharacteristic
                , Foundation.PairSetCharacteristic
                , Foundation.FamilyUnionCharacteristic
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
          )
        , ( Record.RecordAggregateSelectorClosedLaw
          , Set.fromList
                [ Foundation.EmptyCharacteristic
                , Foundation.PairSetCharacteristic
                , Foundation.FamilyUnionCharacteristic
                , Foundation.OrderedPairFirst
                ]
          )
        , (Record.RecordAggregateFunctionalLaw, Set.empty)
        , (Record.RecordSelectorDistinctLaw, Set.empty)
        , (Record.RecordProjectionEntryAgreementLaw, Set.empty)
        , (Record.RecordProjectionGraphAgreementLaw, Set.empty)
        , (Record.RecordProjectionExtensionalityLaw, Set.empty)
        , (Record.RecordAggregateExactLaw, Set.empty)
        ]

    let selectorPairFootprint =
            Set.fromList
                [ Foundation.EmptyCharacteristic
                , Foundation.PairSetCharacteristic
                , Foundation.OrderedPairInjective
                ]
    assertRecordLawAuthority fixture
        (Record.RecordSelectorPairDistinctLaw
            firstIdentity middleIdentity)
        selectorPairFootprint

    let projectionEntryFootprint =
            Set.fromList
                [ Foundation.SetExtensionality
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
    traverse_
        (\identity ->
            assertRecordLawAuthority fixture
                (Record.RecordProjectionEntryLaw identity)
                projectionEntryFootprint)
        identities

    traverse_
        (\identity -> do
            assertRecordLawAuthority fixture
                (Record.RecordProjectionAgreementLaw identity)
                Set.empty
            assertRecordLawAuthority fixture
                (Record.RecordReductProjectionLaw identity)
                (Set.singleton Foundation.SetExtensionality)
            assertRecordLawAuthority fixture
                (Record.RecordAggregateProjectionApplicationLaw identity)
                Set.empty
            assertRecordLawAuthority fixture
                (Record.RecordAggregateProjectionLaw identity)
                Set.empty)
        identities

    let aggregateEntryFootprint =
            Set.fromList
                [ Foundation.PairSetCharacteristic
                , Foundation.FamilyUnionCharacteristic
                ]
    assertRecordLawAuthority fixture
        (Record.RecordAggregateEntryLaw firstIdentity)
        aggregateEntryFootprint
    assertRecordLawAuthority fixture
        (Record.RecordAggregateEntryLaw middleIdentity)
        aggregateEntryFootprint
    assertRecordLawAuthority fixture
        (Record.RecordAggregateEntryLaw finalIdentity)
        aggregateEntryFootprint

    let aggregateUniqueFootprint =
            Set.fromList
                [ Foundation.EmptyCharacteristic
                , Foundation.PairSetCharacteristic
                , Foundation.FamilyUnionCharacteristic
                , Foundation.OrderedPairInjective
                ]
    assertRecordLawAuthority fixture
        (Record.RecordAggregateValueUniqueLaw firstIdentity)
        aggregateUniqueFootprint
    assertRecordLawAuthority fixture
        (Record.RecordAggregateValueUniqueLaw middleIdentity)
        aggregateUniqueFootprint
    assertRecordLawAuthority fixture
        (Record.RecordAggregateValueUniqueLaw finalIdentity)
        aggregateUniqueFootprint
  where
    assertCanonicalTargets fixture identities = do
        let theory = Identity.theoryId (fixtureFoundation fixture)
            selectors =
                [ Core.CGlobal (Record.fieldSelectorObjectId theory identity)
                | identity <- identities
                ]
        assertCanonicalTarget fixture
            Record.RecordExactGraphLaw
            (Record.recordSchemaExactGraphLaw selectors)
        assertCanonicalTarget fixture
            Record.RecordReductMembershipLaw
            (Record.recordSchemaReductMembershipLaw selectors)
        assertCanonicalTarget fixture
            Record.RecordReductExactLaw
            (Record.recordSchemaReductExactLaw selectors)
        assertCanonicalTarget fixture
            Record.RecordReductIdentityLaw
            (Record.recordSchemaReductIdentityLaw selectors)

    assertCanonicalTarget fixture law term = do
        expected <- expectRight
            (Core.checkCanonicalCore
                (Identity.globalTypingFromClosure (fixtureClosure fixture))
                term)
        assertEqual ("canonical catalogue target for " <> show law)
            expected
            (knownRecordLawTarget (fixturePreparedSchema fixture) law)

    rejectsWrongDependencyProposition fixture = do
        let law = Record.RecordReductIdentityLaw
        checkedLaw <- checkedRecordLaw fixture law
        dependencies <- case
            knownRecordLawDependencies (fixturePreparedSchema fixture) law of
                [dependency] -> pure dependency
                actual -> assertFailure
                    ("expected one reduct-identity dependency, got "
                        <> show actual)
                    >> fail "unreachable"
        truth <- expectRight
            (Core.checkCanonicalCore
                (Identity.globalTypingFromClosure (fixtureClosure fixture))
                Core.CTruth)
        case RecordProof.buildRecordLawProof
                (fixtureFoundation fixture)
                checkedLaw
                [RecordProof.CheckedRecordImport dependencies truth] of
            Left RecordProof.RecordProofDependencyPropositionMismatch{} ->
                pure ()
            Left other -> assertFailure
                ("expected a dependency-proposition mismatch, got "
                    <> show other)
            Right _ -> assertFailure
                "a record proof accepted the wrong dependency proposition"
checksCanonicalRecordProofSchemas :: Assertion
checksCanonicalRecordProofSchemas = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identity0 = sampleFieldId 0 0
        identity1 = sampleFieldId 0 1
        identity2 = sampleFieldId 0 2
        identities = [identity0, identity1, identity2]
        fields = preparedField theory <$> identities
    closure <- expectRight
        (Identity.validateObjectClosure theory
            (concatMap (preparedFieldObjects theory) identities))
    let globalTyping = Identity.globalTypingFromClosure closure
    schema <- expectRight
        (RecordProof.prepareRecordSchema theory globalTyping fields)
    let laws = RecordProof.recordLawInventory schema
        identitiesInOrder = laws
        expectedOrder =
            [ Record.RecordExactGraphLaw
            , Record.RecordReductExactLaw
            , Record.RecordReductMembershipLaw
            ]
                <> (Record.RecordProjectionAgreementLaw <$> identities)
                <> [ Record.RecordProjectionEntryAgreementLaw
                   , Record.RecordProjectionGraphAgreementLaw
                   , Record.RecordProjectionExtensionalityLaw
                   , Record.RecordReductIdentityLaw
                   ]
                <> (Record.RecordReductProjectionLaw <$> identities)
                <> [ Record.RecordSelectorPairDistinctLaw left right
                   | (index, left) <- zip [0 :: Int ..] identities
                   , right <- drop (index + 1) identities
                   ]
                <> [Record.RecordSelectorDistinctLaw]
                <> (Record.RecordProjectionEntryLaw <$> identities)
                <> [Record.RecordAggregatePairCodedLaw]
                <> (Record.RecordAggregateValueUniqueLaw <$> identities)
                <> (Record.RecordAggregateEntryLaw <$> identities)
                <> [Record.RecordAggregateSelectorClosedLaw]
                <> ( Record.RecordAggregateProjectionApplicationLaw
                        <$> identities
                   )
                <> [ Record.RecordAggregateFunctionalLaw
                   , Record.RecordAggregateExactLaw
                   ]
                <> (Record.RecordAggregateProjectionLaw <$> identities)
    assertEqual "record-law inventory preserves publication order"
        expectedOrder
        identitiesInOrder
    assertEqual "three fields generate the complete quadratic inventory"
        36
        (length laws)
    assertBool "every record-law target is a checked proposition"
        (all
            ((== Core.TyProp)
                . Core.frozenCoreType
                . knownRecordLawTarget schema)
            laws)

    checkedSchema <- expectRight
        (RecordProof.checkRecordSchema closure schema)
    traverse_
        (expectRight . RecordProof.checkRecordSchemaLaw checkedSchema)
        laws

    let otherIdentity = sampleFieldId 1 0
        unavailableLaws =
            [ Record.RecordProjectionEntryLaw otherIdentity
            , Record.RecordSelectorPairDistinctLaw identity0 identity0
            , Record.RecordSelectorPairDistinctLaw identity1 identity0
            , Record.RecordSelectorPairDistinctLaw identity0 otherIdentity
            ]
    traverse_
        (\unavailableLaw ->
            case RecordProof.checkRecordSchemaLaw
                    checkedSchema unavailableLaw of
                Left (RecordProof.RecordSchemaLawUnavailable actual) ->
                    assertEqual "the unavailable law is reported"
                        unavailableLaw actual
                Left other ->
                    assertFailure
                        ("expected an unavailable record law, got "
                            <> show other)
                Right _ ->
                    assertFailure
                        ("an unavailable record law passed the schema boundary: "
                            <> show unavailableLaw))
        unavailableLaws

    narrowClosure <- expectRight
        (Identity.validateObjectClosure theory
            (preparedFieldObjects theory identity0))
    case RecordProof.checkRecordSchema narrowClosure schema of
        Left (RecordProof.RecordSchemaObjectMissing object) ->
            assertEqual "the first absent canonical resource is reported"
                (Record.fieldSelectorObjectId theory identity1)
                object
        other ->
            assertFailure
                ("expected a missing canonical schema object, got "
                    <> either show (const "unexpected success") other)

    let firstIdentity = identity0
        wrongSelector = Record.fieldSelectorObjectId theory identity1
        mismatched = RecordProof.PreparedRecordField
            firstIdentity
            wrongSelector
            (Record.fieldProjectionObjectId theory firstIdentity)
    case RecordProof.prepareRecordSchema
            theory globalTyping [mismatched] of
        Left RecordProof.NoncanonicalRecordSelector{} -> pure ()
        other ->
            assertFailure
                ("expected a noncanonical selector rejection, got "
                    <> either show (const "unexpected success") other)

    functional <- soleRecordLaw
        Record.RecordAggregateFunctionalLaw
        laws
    assertEqual "aggregate functionality dependency order"
        ( [Record.RecordAggregatePairCodedLaw]
            <> (Record.RecordAggregateValueUniqueLaw <$> identities)
            <> [Record.RecordAggregateSelectorClosedLaw]
        )
        (generatedDependencyIdentities
            (knownRecordLawDependencies schema functional))
  where
    preparedField theory identity =
        RecordProof.PreparedRecordField
            identity
            (Record.fieldSelectorObjectId theory identity)
            (Record.fieldProjectionObjectId theory identity)

    preparedFieldObjects theory identity =
        [ Record.fieldSelectorObject theory identity
        , Record.fieldProjectionObject theory identity
        ]

    soleRecordLaw identity laws =
        case
            [ law
            | law <- laws
            , law == identity
            ] of
            [law] -> pure law
            matches ->
                assertFailure
                    ("expected one record law, got " <> show (length matches))
                    >> fail "unreachable"

    generatedDependencyIdentities dependencies =
        [ dependency
        | RecordProof.RecordGeneratedDependency dependency <- dependencies
        ]

checksBalancedFieldSelectors :: Assertion
checksBalancedFieldSelectors = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identity = sampleFieldId 0 0
        body :: Core.CanonicalTerm Identity.ObjectId
        body = Record.fieldSelectorBody identity
        object = Record.fieldSelectorObject theory identity
    closure <- expectRight
        (Identity.validateObjectClosure theory [object])
    checked <- expectRight
        (Core.checkCanonicalCore
            (Identity.globalTypingFromClosure closure)
            body)
    assertEqual "selector body is a set"
        Core.TySet
        (Core.frozenCoreType checked)
    assertEqual "selector tree has one level per digest bit exponent"
        (Just 8)
        (orderedPairTreeDepth body)
    assertBool "selector tree stays within its fixed representation envelope"
        (canonicalNodeCount body <= 2045)
    let selector = Record.fieldSelectorObjectId theory identity
    assertEqual "selector object is transparent"
        Identity.TransparentObject
        (Identity.objectIdFamily selector)
    assertEqual "selector object validates with its transparent body"
        (Just
            (Identity.TransparentObjectContent theory Core.TySet body))
        (Identity.lookupCheckedObjectContent selector closure)

keepsTransparentProjectionDefinitionsAtTh0Boundary :: Assertion
keepsTransparentProjectionDefinitionsAtTh0Boundary = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identity = sampleFieldId 0 0
        selector = Record.fieldSelectorObjectId theory identity
        projection = Record.fieldProjectionObjectId theory identity
        projectionBody = Record.fieldProjectionBody selector
        objects =
            [ Record.fieldSelectorObject theory identity
            , Record.fieldProjectionObject theory identity
            ]
    closure <- expectRight
        (Identity.validateObjectClosure theory objects)
    checkedBody <- expectRight
        (Core.checkCanonicalCore
            (Identity.globalTypingFromClosure closure)
            projectionBody)
    assertEqual "field projection has unary set type"
        (Core.TyArrow Core.TySet Core.TySet)
        (Core.frozenCoreType checkedBody)
    assertEqual "projection object validates with its transparent body"
        (Just
            (Identity.TransparentObjectContent
                theory
                (Core.TyArrow Core.TySet Core.TySet)
                projectionBody))
        (Identity.lookupCheckedObjectContent projection closure)

    construction <- maybe
        (assertFailure "field projection construction did not check"
            >> fail "unreachable")
        pure
        (Record.fieldProjectionConstruction
            (Identity.globalTypingFromClosure closure)
            selector)
    assertEqual "projection construction retains the exact transparent body"
        projectionBody
        (Core.frozenCoreTerm
            (SetConstruction.namedSetConstructionClosedBody construction))
    derived <- maybe
        (assertFailure "projection membership view was not derived"
            >> fail "unreachable")
        pure
        (SetConstruction.namedSetConstructionObjectFact
            (SetConstruction.checkedFoundationSetConstruction foundation)
            closure
            projection
            construction)
    let wrongProjectionObject =
            Identity.transparentObject
                theory
                (Core.TyArrow Core.TySet Core.TySet)
                (Core.CLam Core.TySet (Core.CIntrinsic Core.Empty))
        wrongProjection = Identity.assertedObjectId wrongProjectionObject
    wrongClosure <- expectRight
        (Identity.extendObjectClosure closure [wrongProjectionObject])
    assertBool
        "a different transparent object cannot acquire the construction view"
        (isNothing
            (SetConstruction.namedSetConstructionObjectFact
                (SetConstruction.checkedFoundationSetConstruction foundation)
                wrongClosure
                wrongProjection
                construction))
    assertEqual "projection has a flattened membership interface"
        (Record.recordProjectionMembershipLaw
            (Core.CGlobal selector)
            (Core.CGlobal projection))
        (Core.frozenCoreTerm
            (SetConstruction.namedSetConstructionFactProposition derived))
    assertEqual "flattened projection membership remains first-order"
        Foundation.FoundationFofProjectable
        (Foundation.classifyFrozenCore
            (SetConstruction.namedSetConstructionFactProposition derived))

    let pointwiseDefinition =
            Core.CForall Core.TySet
                (Core.CEq Core.TySet
                    (Core.CApp
                        (Core.CGlobal projection)
                        (Core.CBound 0))
                    (Core.instantiateCanonical
                        (Core.CBound 0)
                        (case projectionBody of
                            Core.CLam Core.TySet body -> body
                            _ -> impossible
                                "a field projection body is not a set lambda")))
        firstOrderUse =
            Core.CForall Core.TySet
                (Core.CEq Core.TySet
                    (Core.CApp
                        (Core.CGlobal projection)
                        (Core.CBound 0))
                    (Core.CApp
                        (Core.CGlobal projection)
                        (Core.CBound 0)))
    definitionCapability <- classifyObjectProposition closure pointwiseDefinition
    useCapability <- classifyObjectProposition closure firstOrderUse
    case definitionCapability of
        Backend.RequiresTh0{} -> pure ()
        Backend.FofProjectable{} ->
            assertFailure "generic projection definition unexpectedly routed to FOF"
    case useCapability of
        Backend.FofProjectable{} -> pure ()
        Backend.RequiresTh0 exclusions ->
            assertFailure
                ("first-order projection use unexpectedly requires TH0: "
                    <> show exclusions)

checksRecordCalculusTerms :: Assertion
checksRecordCalculusTerms = do
    let selectors =
            [ Core.CGlobal firstSelector
            , Core.CGlobal secondSelector
            ]
        aggregate =
            Record.recordAggregate
                [ (Core.CGlobal firstSelector, Core.CIntrinsic Core.Empty)
                , (Core.CGlobal secondSelector, Core.CIntrinsic Core.Empty)
                ]
        propositions =
            [ Record.recordFunctional aggregate
            , Record.recordOpenShape selectors aggregate
            , Record.recordExactShape selectors aggregate
            , Record.recordExactGraphExtensionality
                selectors aggregate aggregate
            , Record.recordReductExact selectors aggregate
            , Record.recordReductMembership
                selectors
                (Core.CApp
                    (Core.CApp (Core.CIntrinsic Core.OrderedPair)
                        (Core.CGlobal firstSelector))
                    (Core.CIntrinsic Core.Empty))
                aggregate
            , Record.recordSchemaExactGraphLaw selectors
            , Record.recordSchemaProjectionEntryAgreementLaw
                [ ( Core.CGlobal firstSelector
                  , Core.CGlobal firstProjection
                  )
                ]
            , Record.recordSchemaProjectionGraphAgreementLaw
                [ ( Core.CGlobal firstSelector
                  , Core.CGlobal firstProjection
                  )
                ]
            , Record.recordSchemaReductExactLaw selectors
            , Record.recordSchemaReductMembershipLaw selectors
            , Record.recordSchemaReductIdentityLaw selectors
            , Record.recordSchemaReductCoreLaws selectors
            ]
                <> Record.recordSchemaReductProjectionLaws
                    [ ( Core.CGlobal firstSelector
                      , Core.CGlobal firstProjection
                      )
                    ]
        setTerms =
            [ aggregate
            , Record.recordLookup
                (Core.CGlobal firstSelector) aggregate
            , Record.recordReduct
                [Core.CGlobal firstSelector] aggregate
            ]
    traverse_
        (\term -> do
            checked <- expectRight
                (Core.checkCanonicalCore selectorGlobalTyping term)
            assertEqual "record proposition has Prop type"
                Core.TyProp
                (Core.frozenCoreType checked))
        propositions
    traverse_
        (\term -> do
            checked <- expectRight
                (Core.checkCanonicalCore selectorGlobalTyping term)
            assertEqual "record construction has Set type"
                Core.TySet
                (Core.frozenCoreType checked))
        setTerms
    openCapability <- selectorCapability
        (Record.recordOpenShape selectors aggregate)
    reductCapability <- selectorCapability
        (Core.CEq Core.TySet
            (Record.recordReduct
                [Core.CGlobal firstSelector] aggregate)
            (Record.recordReduct
                [Core.CGlobal firstSelector] aggregate))
    case openCapability of
        Backend.FofProjectable{} -> pure ()
        Backend.RequiresTh0 exclusions ->
            assertFailure
                ("open record shape unexpectedly requires TH0: "
                    <> show exclusions)
    case reductCapability of
        Backend.RequiresTh0{} -> pure ()
        Backend.FofProjectable{} ->
            assertFailure "transparent reduct unexpectedly routed to FOF"

recognizesExactGlobalShapes :: Assertion
recognizesExactGlobalShapes = do
    let subject = Core.CBound 0
        selectors =
            [ Core.CGlobal firstSelector
            , Core.CGlobal secondSelector
            ]
        exact = Record.recordExactShape selectors subject
    checked <- expectRight
        (Core.checkScopedCanonicalCore
            selectorGlobalTyping
            [Core.TySet]
            exact)
    assertEqual "exact shape inverse"
        (Just (subject, [firstSelector, secondSelector]))
        (Record.recognizeRecordExactGlobalShape checked)

    open <- expectRight
        (Core.checkScopedCanonicalCore
            selectorGlobalTyping
            [Core.TySet]
            (Record.recordOpenShape selectors subject))
    assertEqual "open shape is not exact" Nothing
        (Record.recognizeRecordExactGlobalShape open)

    lookalike <- expectRight
        (Core.checkScopedCanonicalCore
            selectorGlobalTyping
            [Core.TySet]
            (Core.CAnd
                (Record.recordOpenShape selectors subject)
                Core.CTruth))
    assertEqual "partial lookalike does not reconstruct" Nothing
        (Record.recognizeRecordExactGlobalShape lookalike)

    nonglobal <- expectRight
        (Core.checkScopedCanonicalCore
            selectorGlobalTyping
            [Core.TySet]
            (Record.recordExactShape [Core.CBound 0] subject))
    assertEqual "non-global selector is rejected" Nothing
        (Record.recognizeRecordExactGlobalShape nonglobal)

provesRecordCalculusLaws :: Assertion
provesRecordCalculusLaws = do
    foundation <- expectRight Foundation.checkedFoundation
    let emptySet = Core.CIntrinsic Core.Empty
        laws =
            [ ( "schema graph extensionality"
              , True
              , [ Foundation.SetExtensionality
                , Foundation.OrderedPairInjective
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
              , Record.recordSchemaExactGraphLaw [emptySet]
              )
            , ( "schema reduct exactness"
              , False
              , [ Foundation.SeparationCharacteristic
                , Foundation.SetExtensionality
                , Foundation.OrderedPairInjective
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
              , Record.recordSchemaReductExactLaw [emptySet]
              )
            , ( "schema reduct membership"
              , False
              , [ Foundation.SeparationCharacteristic
                , Foundation.SetExtensionality
                , Foundation.OrderedPairInjective
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
              , Record.recordSchemaReductMembershipLaw [emptySet]
              )
            , ( "exact schema reduct identity"
              , False
              , [ Foundation.SeparationCharacteristic
                , Foundation.SetExtensionality
                , Foundation.OrderedPairInjective
                , Foundation.OrderedPairFirst
                , Foundation.OrderedPairSecond
                ]
              , Record.recordSchemaReductIdentityLaw [emptySet]
              )
            ]
    traverse_
        (\(label, expectFof, auxiliaries, term) ->
            proveRecordLaw foundation label expectFof auxiliaries term)
        laws

proveRecordLaw
    :: Foundation.CheckedFoundation
    -> String
    -> Bool
    -> [Foundation.FoundationAxiomTag]
    -> Core.CanonicalTerm Void
    -> Assertion
proveRecordLaw foundation label expectFof auxiliaryTags term = do
    checked <- expectRight
        (Core.checkScopedCanonicalCore
            GlobalTyping.emptyGlobalTyping
            []
            term)
    claim <- expectRight
        (Backend.supportedProposition Vector.empty checked)
    let auxiliaries =
            Backend.typedFoundationAuxiliaryInput foundation
                <$> auxiliaryTags
        planned
            :: Either
                (Backend.TypedProblemError Void Void)
                (Backend.TypedProblem Void Void Void Void)
        planned =
            Backend.planTypedProblem
                GlobalTyping.emptyGlobalTyping
                Vector.empty
                claim
                []
                auxiliaries
                Backend.FirstOrderLocals
    problem <- expectRight planned
    assertEqual (label <> " uses the intended backend boundary")
        (if expectFof then Backend.RouteFof else Backend.RouteTh0)
        (Backend.typedProblemRoute problem)

provesFlattenedProjectionConsequences :: Assertion
provesFlattenedProjectionConsequences = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identity = sampleFieldId 0 0
        selector = Record.fieldSelectorObjectId theory identity
        projection = Record.fieldProjectionObjectId theory identity
        objects =
            [ Record.fieldSelectorObject theory identity
            , Record.fieldProjectionObject theory identity
            ]
        selectorTerm = Core.CGlobal selector
        projectionTerm = Core.CGlobal projection
        membership =
            Record.recordProjectionMembershipLaw
                selectorTerm projectionTerm
        projectionAgreement =
            Record.recordSchemaProjectionAgreementLaw
                (selectorTerm, projectionTerm)
        projectionEntryAgreement =
            Record.recordSchemaProjectionEntryAgreementLaw
                [(selectorTerm, projectionTerm)]
        projectionGraphAgreement =
            Record.recordSchemaProjectionGraphAgreementLaw
                [(selectorTerm, projectionTerm)]
        targets =
            [ ( "projection of a present entry"
              , [membership]
              , Record.recordProjectionEntryLaw
                    selectorTerm projectionTerm
              )
            , ( "projection agreement determines entry agreement"
              , [Record.recordProjectionEntryLaw
                    selectorTerm projectionTerm]
              , projectionAgreement
              )
            , ( "projection agreements determine schema-entry agreement"
              , [projectionAgreement]
              , projectionEntryAgreement
              )
            , ( "schema entries determine graph agreement"
              , [projectionEntryAgreement]
              , projectionGraphAgreement
              )
            , ( "projection of a missing entry"
              , [membership]
              , Record.recordProjectionMissingLaw
                    selectorTerm projectionTerm
              )
            , ( "exact projection extensionality"
              , [projectionGraphAgreement]
              , Record.recordSchemaProjectionExtensionalityLaw
                    [(selectorTerm, projectionTerm)]
              )
            ]
        auxiliaryTags =
            [ Foundation.EmptyCharacteristic
            , Foundation.SetExtensionality
            , Foundation.OrderedPairInjective
            , Foundation.OrderedPairFirst
            , Foundation.OrderedPairSecond
            ]
    closure <- expectRight
        (Identity.validateObjectClosure theory objects)
    let globalType = Identity.globalTypingFromClosure closure
        support = Vector.empty :: Vector.Vector (Void, Core.CoreType)
    traverse_
        (\(label, premises, target) -> do
            localPremises <-
                traverse
                    (\(index, premise) -> do
                        checkedPremise <- expectRight
                            (Core.checkScopedCanonicalCore
                                globalType [] premise)
                        supportedPremise <- expectRight
                            (Backend.supportedProposition
                                support checkedPremise)
                        expectRight
                            (Backend.typedLocalPremise
                                globalType
                                (Backend.localPremiseOrdinal index)
                                ()
                                supportedPremise))
                    (zip [0 :: Natural ..] premises)
            checkedTarget <- expectRight
                (Core.checkScopedCanonicalCore globalType [] target)
            supportedTarget <- expectRight
                (Backend.supportedProposition support checkedTarget)
            let auxiliaries =
                    Backend.typedFoundationAuxiliaryInput foundation
                        <$> auxiliaryTags
                planned =
                    Backend.planTypedProblem
                        globalType
                        Vector.empty
                        supportedTarget
                        localPremises
                        auxiliaries
                        Backend.CompleteLocals
            problem <- expectRight planned
            assertEqual (label <> " stays first-order")
                Backend.RouteFof
                (Backend.typedProblemRoute problem)
            pure ())
        targets

provesTransparentAggregateInterfaces :: Assertion
provesTransparentAggregateInterfaces = do
    foundation <- expectRight Foundation.checkedFoundation
    let firstSelectorTerm = Core.CGlobal firstSelector
        secondSelectorTerm = Core.CGlobal secondSelector
        thirdSelectorTerm = Core.CGlobal thirdSelector
        fourthSelectorTerm = Core.CGlobal fourthSelector
        firstProjectionTerm = Core.CGlobal firstProjection
        secondProjectionTerm = Core.CGlobal secondProjection
        thirdProjectionTerm = Core.CGlobal thirdProjection
        fourthProjectionTerm = Core.CGlobal fourthProjection
        fields =
            [ (firstSelectorTerm, firstProjectionTerm)
            , (secondSelectorTerm, secondProjectionTerm)
            , (thirdSelectorTerm, thirdProjectionTerm)
            , (fourthSelectorTerm, fourthProjectionTerm)
            ]
        selectors = fst <$> fields
        distinct = Record.recordSelectorDistinctLaw selectors
        pairCoded = Record.recordSchemaAggregatePairCodedLaw selectors
        valueUnique =
            Record.recordSchemaAggregateValueUniqueLaws selectors
        aggregateEntries =
            Record.recordSchemaAggregateEntryLaws selectors
        selectorClosed =
            Record.recordSchemaAggregateSelectorClosedLaw selectors
        functional =
            Record.recordSchemaAggregateFunctionalLaw selectors
        components = functional : aggregateEntries <> [selectorClosed]
        exact =
            Record.recordSchemaAggregateExactLaw selectors
        projectionEntryLaws =
            [ Record.recordProjectionEntryLaw
                selector projection
            | (selector, projection) <- fields
            ]
        projectionApplicationLaws =
            Record.recordSchemaAggregateProjectionApplicationLaws fields
        targets =
            [ ( "aggregate primitive " <> show index
              , [distinct]
              , primitive
              )
            | (index, primitive) <- zip [0 :: Int ..]
                (pairCoded : valueUnique <> aggregateEntries <> [selectorClosed])
            ]
                <> [ ( "aggregate functionality"
                     , pairCoded : valueUnique <> [selectorClosed]
                     , functional
                     )
                   ]
                <> [ ("aggregate exactness", components, exact) ]
                <> [ ( "aggregate projection application " <> show index
                     , [entryLaw]
                     , applicationLaw
                     )
                   | (index, entryLaw, applicationLaw) <-
                        zip3
                            [0 :: Int ..]
                            projectionEntryLaws
                            projectionApplicationLaws
                   ]
                <> [ ( "aggregate projection " <> show index
                    , [ components !! 0
                      , components !! (index + 1)
                      , applicationLaw
                      ]
                    , target
                    )
                  | (index, applicationLaw, target) <-
                        zip3
                            [0 :: Int ..]
                            projectionApplicationLaws
                            (Record.recordSchemaAggregateProjectionLaws fields)
                  ]
        auxiliaryTags =
            [ Foundation.EmptyCharacteristic
            , Foundation.PairSetCharacteristic
            , Foundation.FamilyUnionCharacteristic
            , Foundation.SetExtensionality
            , Foundation.OrderedPairInjective
            , Foundation.OrderedPairFirst
            , Foundation.OrderedPairSecond
            ]
    traverse_
        (\(label, premises, target) -> do
            checkedPremises <- traverse selectorProposition premises
            locals <- traverse
                (\(index, premise) ->
                    expectRight
                        (Backend.typedLocalPremise
                            selectorGlobalTyping
                            (Backend.localPremiseOrdinal index)
                            ()
                            premise))
                (zip [0 :: Natural ..] checkedPremises)
            claim <- selectorProposition target
            let auxiliaries =
                    Backend.typedFoundationAuxiliaryInput foundation
                        <$> auxiliaryTags
                planned
                    :: Either
                        (Backend.TypedProblemError Void Identity.ObjectId)
                        (Backend.TypedProblem Void Void () Identity.ObjectId)
                planned =
                    Backend.planTypedProblem
                        selectorGlobalTyping
                        Vector.empty
                        claim
                        locals
                        auxiliaries
                        Backend.CompleteLocals
            problem <- expectRight planned
            assertEqual (label <> " stays first-order")
                Backend.RouteFof
                (Backend.typedProblemRoute problem)
            pure ())
        targets

keepsSelectorIdentitiesStableAndDistinct :: Assertion
keepsSelectorIdentitiesStableAndDistinct = do
    foundation <- expectRight Foundation.checkedFoundation
    let theory = Identity.theoryId foundation
        identities =
            [ sampleFieldId declaration field
            | declaration <- [0 .. 15]
            , field <- [0 .. 15]
            ]
        selectorBody fieldIdentity =
            Record.fieldSelectorBody fieldIdentity
                :: Core.CanonicalTerm Identity.ObjectId
        bodies = selectorBody <$> identities
        objects = Record.fieldSelectorObjectId theory <$> identities
        identity = sampleFieldId 3 5
        downstreamVectors =
            [ ( "selector object"
              , "69eea9f35906a0e9ae185dd4f16b658263d06fad5a77470b373ea7c33fb5b27b"
              , mathematicalDigestHex
                    (Identity.objectIdDigest
                        (Record.fieldSelectorObjectId theory identity))
              )
            , ( "projection object"
              , "1eb5dbcf04f0cb8dc936c17b2b7f8e0c3ce8a6f7c44571ba8c9cf89dfed9ae19"
              , mathematicalDigestHex
                    (Identity.objectIdDigest
                        (Record.fieldProjectionObjectId theory identity))
              )
            ] :: [(String, Text, Text)]
    assertEqual "same FieldId has one selector body"
        (selectorBody identity)
        (selectorBody identity)
    assertEqual "same FieldId has one selector object"
        (Record.fieldSelectorObjectId theory identity)
        (Record.fieldSelectorObjectId theory identity)
    assertEqual "sample FieldIds are distinct"
        (length identities)
        (Set.size (Set.fromList identities))
    assertEqual "selector bodies preserve FieldId distinctions"
        (length identities)
        (Set.size (Set.fromList bodies))
    assertEqual "transparent selector objects preserve FieldId distinctions"
        (length identities)
        (Set.size (Set.fromList objects))
    assertEqual "FieldId downstream identity vectors"
        [ (description, expected)
        | (description, expected, _actual) <- downstreamVectors
        ]
        [ (description, actual)
        | (description, _expected, actual) <- downstreamVectors
        ]

selectorFixture :: GlobalTypingFixture
selectorFixture =
    globalTypingFixture
        ( replicate 4 Core.TySet
            <> replicate 4 (Core.TyArrow Core.TySet Core.TySet)
        )

selectorGlobalTyping :: GlobalTyping.GlobalTyping Identity.ObjectId
selectorGlobalTyping = fixtureGlobalTyping selectorFixture

firstSelector, secondSelector, thirdSelector, fourthSelector,
    firstProjection, secondProjection, thirdProjection, fourthProjection
        :: Identity.ObjectId
( firstSelector
    , secondSelector
    , thirdSelector
    , fourthSelector
    , firstProjection
    , secondProjection
    , thirdProjection
    , fourthProjection
    ) =
        case fixtureObjectIds selectorFixture of
            [ firstSelectorObject
                , secondSelectorObject
                , thirdSelectorObject
                , fourthSelectorObject
                , firstProjectionObject
                , secondProjectionObject
                , thirdProjectionObject
                , fourthProjectionObject
                ] ->
                    ( firstSelectorObject
                    , secondSelectorObject
                    , thirdSelectorObject
                    , fourthSelectorObject
                    , firstProjectionObject
                    , secondProjectionObject
                    , thirdProjectionObject
                    , fourthProjectionObject
                    )
            _ -> error "the record selector fixture changed arity"

preparesSelectorDistinctionAsCompactFof :: Assertion
preparesSelectorDistinctionAsCompactFof = do
    foundation <- expectRight Foundation.checkedFoundation
    let firstBody =
            Record.fieldSelectorBody (sampleFieldId 0 0)
                :: Core.CanonicalTerm Identity.ObjectId
        secondBody =
            Record.fieldSelectorBody (sampleFieldId 0 1)
                :: Core.CanonicalTerm Identity.ObjectId
    firstDefinition <- selectorBackendFact 0
        (Core.CEq Core.TySet
            (Core.CGlobal firstSelector)
            firstBody)
    secondDefinition <- selectorBackendFact 1
        (Core.CEq Core.TySet
            (Core.CGlobal secondSelector)
            secondBody)
    claim <- selectorProposition
        (Core.CImp
            (Core.CEq Core.TySet
                (Core.CGlobal firstSelector)
                (Core.CGlobal secondSelector))
            Core.CFalsum)
    let planned
            :: Either
                (Backend.TypedProblemError Void Identity.ObjectId)
                (Backend.TypedProblem Int Void Void Identity.ObjectId)
        planned =
            Backend.planTypedProblem
                selectorGlobalTyping
                (Vector.fromList
                    [firstDefinition, secondDefinition])
                claim
                []
                [ Backend.typedFoundationAuxiliaryInput foundation
                    Foundation.EmptyCharacteristic
                , Backend.typedFoundationAuxiliaryInput foundation
                    Foundation.PairSetCharacteristic
                , Backend.typedFoundationAuxiliaryInput foundation
                    Foundation.OrderedPairInjective
                ]
                Backend.FirstOrderLocals
    problem <- expectRight planned
    task <- expectRight
        (Provers.prepareTypedProverTask Provers.DirectTask problem)
    assertEqual "selector distinction stays first-order"
        Backend.RouteFof
        (Backend.typedProblemRoute problem)
    assertBool "selector distinction stays below its prepared-size envelope"
        ( Provers.preparedVerificationByteCount
            (Provers.preparedTypedProverRequest task)
            <= 12000
        )

selectorProposition
    :: Core.CanonicalTerm Identity.ObjectId
    -> IO (Backend.SupportedProposition Void Identity.ObjectId)
selectorProposition term = do
    checked <- expectRight
        (Core.checkScopedCanonicalCore selectorGlobalTyping [] term)
    expectRight
        (Backend.supportedProposition Vector.empty checked)

selectorCapability
    :: Core.CanonicalTerm Identity.ObjectId
    -> IO
        (Backend.FofCapability
            (Backend.CheckedFofProjection Void Identity.ObjectId))
selectorCapability term = do
    proposition <- selectorProposition term
    expectRight
        (Backend.classifySupportedProposition
            selectorGlobalTyping proposition)

selectorBackendFact
    :: Int
    -> Core.CanonicalTerm Identity.ObjectId
    -> IO (Backend.TypedBackendFact Int Identity.ObjectId)
selectorBackendFact reference term = do
    proposition <- selectorProposition term
    capability <- expectRight
        (Backend.classifySupportedProposition
            selectorGlobalTyping proposition)
    pure
        (Backend.typedBackendFact
            reference proposition capability)

classifyObjectProposition
    :: Identity.CheckedObjectClosure
    -> Core.CanonicalTerm Identity.ObjectId
    -> IO
        (Backend.FofCapability
            (Backend.CheckedFofProjection Void Identity.ObjectId))
classifyObjectProposition closure term = do
    checked <- expectRight
        (Core.checkScopedCanonicalCore
            (Identity.globalTypingFromClosure closure)
            []
            term)
    proposition <- expectRight
        (Backend.supportedProposition Vector.empty checked)
    expectRight
        (Backend.classifySupportedProposition
            (Identity.globalTypingFromClosure closure)
            proposition)

sampleFieldId :: Natural -> Natural -> Identity.FieldId
sampleFieldId declaration field =
    Identity.fieldId
        preludeModuleName
        (localDeclarationOrdinal declaration)
        (structureFieldSlot field)

orderedPairTreeDepth :: Core.CanonicalTerm global -> Maybe Int
orderedPairTreeDepth term =
    case orderedPairChildren term of
        Just (left, right) -> do
            leftDepth <- orderedPairTreeDepth left
            rightDepth <- orderedPairTreeDepth right
            if leftDepth == rightDepth then
                Just (leftDepth + 1)
            else
                Nothing
        Nothing
            | isBitCode term -> Just 0
            | otherwise -> Nothing

orderedPairChildren
    :: Core.CanonicalTerm global
    -> Maybe (Core.CanonicalTerm global, Core.CanonicalTerm global)
orderedPairChildren = \case
    Core.CApp
        (Core.CApp (Core.CIntrinsic Core.OrderedPair) left)
        right ->
            Just (left, right)
    _ -> Nothing

isBitCode :: Core.CanonicalTerm global -> Bool
isBitCode = \case
    Core.CIntrinsic Core.Empty -> True
    Core.CApp
        (Core.CApp (Core.CIntrinsic Core.PairSet)
            (Core.CIntrinsic Core.Empty))
        (Core.CIntrinsic Core.Empty) -> True
    _ -> False

canonicalNodeCount :: Core.CanonicalTerm global -> Int
canonicalNodeCount = \case
    Core.CBound{} -> 1
    Core.CGlobal{} -> 1
    Core.CIntrinsic{} -> 1
    Core.CLogicalSelect{} -> 1
    Core.COpaqueInteger{} -> 1
    Core.CApp function argument ->
        1 + canonicalNodeCount function + canonicalNodeCount argument
    Core.CLam _binderType body -> 1 + canonicalNodeCount body
    Core.CFalsum -> 1
    Core.CTruth -> 1
    Core.CNot proposition -> 1 + canonicalNodeCount proposition
    Core.CAnd left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    Core.COr left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    Core.CImp premise conclusion ->
        1 + canonicalNodeCount premise + canonicalNodeCount conclusion
    Core.CEq _operandType left right ->
        1 + canonicalNodeCount left + canonicalNodeCount right
    Core.CForall _binderType body -> 1 + canonicalNodeCount body
    Core.CExists _binderType body -> 1 + canonicalNodeCount body

expectRight :: Show failure => Either failure value -> IO value
expectRight = \case
    Right value -> pure value
    Left failure ->
        assertFailure (show failure) >> fail "unreachable"
