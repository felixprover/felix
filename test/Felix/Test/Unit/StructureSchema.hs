{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.StructureSchema (unitTests) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Foundation
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as KernelProof
import Felix.Checking.Structure.Laws qualified as Laws
import Felix.Checking.Structure.Batch qualified as Batch
import Felix.Checking.Structure.Interface qualified as Interface
import Felix.Checking.Planning
import Felix.Checking.Semantic (ViewVariableIx(..))
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Predicate qualified as Predicate
import Felix.Checking.Structure.Schema
import Felix.Cache.Codec
import Felix.Math.Codec qualified as Math
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Control.Monad (foldM)
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Normalized structure schemas"
    [ testCase "preserves canonical structure-key orders and bytes" preservesKeyOrders
    , testCase "demands sort encodings only after earlier key components" keepsKeyEncodingLazy
    , testCase "normalizes diamonds independently of written parent order" normalizesDiamond
    , testCase "bounds repeated diamond predicates by unique requirements" boundsDiamondPredicates
    , testCase "retains distinct applications of one parent" retainsApplications
    , testCase "names complete parent applications independently of order" namesParentApplications
    , testCase "pulls back preamble requirements along subject arguments" specializesPreamble
    , testCase "checks preamble terms in their actual prefix" checksPrefix
    , testCase "rejects exact duplicate edges and cycles by identity" rejectsCycles
    , testCase "reuses an active predicate object" checksRegistration
    , testCase "specializes retained normalized registrations without reducing source laws" specializesRegistration
    , testCase "requires unused canonical field resources and reserves carrier" checksResources
    , testCase "replays the normalized law catalogue with exact resources" replaysCatalogue
    , testCase "derives inherited predicates directly from normalized inclusion" replaysInheritance
    , testCase "shares equal predicate resources without duplicating proof imports" sharesDefinitions
    , testCase "keeps compound inheritance laws outside generated notion views" checksViewEligibility
    , testCase "names inherited selector and projection resources exactly" checksInheritedResources
    , testCase "resolves batches with declaration-wide field slots" checksBatchSlots
    , testCase "checks complete batch inventories and dependency stages" checksPendingBatch
    , testCase "keeps public field-law roles stable after re-elaboration" stableFieldLawNames
    , testCase "checks actual structural purposes, targets, and authority" checksInterfaces
    , testCase "round-trips local structural interface claims" roundTripsStructureWire
    , testCase "rejects unavailable predicate laws and changed batch mathematics" rejectsUnavailableLaws
    ]

preservesKeyOrders :: Assertion
preservesKeyOrders = do
    let fields = [fieldId preludeModuleName (localDeclarationOrdinal n) (structureFieldSlot n)
            | n <- [0 .. 31]]
        resources = PredicateDefinitionResource
            : concat [[SelectorDefinitionResource field, ProjectionMembershipResource field]
                | field <- fields]
        terms = [CBound n | n <- [0, 1, 127, 128, 255, 256, 16383, 16384]]
            <> [COpaqueInteger n | n <- [-129, -128, -1, 0, 1, 127, 128, 255, 256]]
            <> [CNot (CAnd CTruth CFalsum), CLam TySet (CBound 0)]
            <> [foldr (const CNot) (CBound n) (replicate 100 ()) | n <- [0, 1]]
        bodies = requirementBodyKey <$> terms
        identities = [structureId (origin n n) | n <- [0, 1, 255]]
        applications = [structureApplicationKey identity arguments
            | identity <- identities, arguments <- [] : concat [[[term], [term, CTruth]] | term <- terms]]
        bytes = LazyByteString.toStrict . Builder.toLazyByteString
        oldResource = compare `on` (bytes . resourceKeyBuilder)
        termBytes = Math.encodeCanonicalTerm objectIdBuilder
        oldBody = compare `on` (termBytes . requirementBodyTerm)
        oldApplication left right = compare (parts left) (parts right)
        parts applicationKey = (structureApplicationId applicationKey,
            length (structureApplicationArguments applicationKey),
            termBytes <$> structureApplicationArguments applicationKey)
    keyOrderLaws resources oldResource
    keyOrderLaws bodies oldBody
    keyOrderLaws applications oldApplication
    -- Lexicographic ULEB order deliberately disagrees with numeric order here.
    compare (requirementBodyKey (CBound 255)) (requirementBodyKey (CBound 256)) @?= GT
    for_ applications \key -> do
        let identity = structureApplicationId key
            arguments = structureApplicationArguments key
        bytes (applicationKeyBuilder key) @?=
            bytes (Builder.byteString (Math.mathematicalDigestBytes (structureIdDigest identity))
                <> Math.compactSequenceBuilder (Math.canonicalTermBuilder objectIdBuilder) arguments)
        show key @?= "StructureApplicationKey " <> showsPrec 11 identity " " <> showsPrec 11 arguments ""
    for_ bodies \key ->
        show key @?= "RequirementBodyKey " <> showsPrec 11 (requirementBodyTerm key) ""

keyOrderLaws :: (Show key, Ord key) => [key] -> (key -> key -> Ordering) -> Assertion
keyOrderLaws keys reference = do
    for_ keys \left -> for_ keys \right -> do
        compare left right @?= reference left right
        (compare left right == EQ) @?= (left == right)
        compare left right @?= invert (compare right left)
    List.sort keys @?= List.sortBy reference keys
    for_ (take 12 keys) \a -> for_ (take 12 keys) \b -> for_ (take 12 keys) \c ->
        assertBool "transitivity" (not (a <= b && b <= c) || a <= c)
  where
    invert LT = GT
    invert EQ = EQ
    invert GT = LT

keepsKeyEncodingLazy :: Assertion
keepsKeyEncodingLazy = do
    let firstId = structureId (origin 1 0)
        secondId = structureId (origin 2 0)
        unused = error "comparison demanded an unused argument"
        unfinished = CTruth : error "comparison demanded argument count before ID"
    assertBool "test IDs differ" (firstId /= secondId)
    compare (structureApplicationKey firstId unfinished)
        (structureApplicationKey secondId unfinished) @?= compare firstId secondId
    compare (structureApplicationKey firstId [unused])
        (structureApplicationKey firstId [unused, unused]) @?= LT
    compare (structureApplicationKey firstId [CBound 0, unused])
        (structureApplicationKey firstId [CBound 1, unused]) @?= LT

origin :: Natural -> Natural -> StructureOrigin
origin declaration slot = StructureOrigin preludeModuleName
    (localDeclarationOrdinal declaration) (structureSlot slot)

wire :: Natural -> Natural -> [StructureApplicationKey] -> LocalStructureSchemaWire
wire slot parameters parents = LocalStructureSchemaWire
    (structureSlot slot) [LocalParameterOrdinal i | i <- take (fromIntegral parameters) [0 ..]]
    [] parents [] []

presentation :: Text -> LocalStructureSchemaWire -> StructurePresentation
presentation name input = StructurePresentation
    (structurePhrase (Raw.mkLexicalItemSgPl
        (Raw.lexicalPhraseSgPl ((Just name, Just (name <> "s")) :|
            replicate (length (localWireParameters input)) (Nothing, Nothing))) (Raw.Marker name)))
    Nowhere
    [fromString ("p" <> show i) | i <- [0 :: Int .. length (localWireParameters input) - 1]]
    [(if length [() | other <- localWireParents input,
            structureApplicationId other == structureApplicationId parent] > 1
        then Just (Raw.Marker (name <> "_parent_" <> fromString (show index))) else Nothing, Nowhere)
    | (index, parent) <- zip [0 :: Int ..] (localWireParents input)]
    (Map.fromList [(key, Nowhere) | LocalPreambleWire key _ _ <- localWirePreamble input])
    (Map.fromList [(slot, (Nothing, Nowhere)) | LocalStructureFieldWire slot _ _ <- localWireFields input])
    (Map.fromList [(ordinal, (Raw.Marker name, Nowhere)) | (ordinal, _) <- localWireLaws input])

fixture :: IO (CheckedObjectClosure, ResolvedStructureSchema)
fixture = do
    foundation <- expectRight checkedFoundation
    closure <- expectRight (validateObjectClosure (theoryId foundation) [])
    let input = wire 0 0 []
    local <- expectRight (checkManifestLocalStructureSchema closure (origin 100 0)
        GeneralRecordRoot input (presentation "record" input))
    root :| _ <- expectRight (resolveStructureBatch (const Nothing) (local :| []))
    pure (closure, root)

checkLocal
    :: CheckedObjectClosure -> Natural -> Text -> LocalStructureSchemaWire
    -> IO LocalStructureSchema
checkLocal closure declaration name input = expectRight
    (checkLocalStructureSchema closure (origin declaration (structureSlotValue (localWireSlot input)))
        input (presentation name input))

resolveOne :: [ResolvedStructureSchema] -> LocalStructureSchema -> IO ResolvedStructureSchema
resolveOne visible local = do
    schema :| rest <- expectRight (resolveStructureBatch (lookupSchema visible) (local :| []))
    assertEqual "one local input resolves once" 0 (length rest)
    pure schema

lookupSchema :: [ResolvedStructureSchema] -> StructureId -> Maybe ResolvedStructureSchema
lookupSchema visible identity = Map.lookup identity
    (Map.fromList [(resolvedSchemaId schema, schema) | schema <- visible])

application :: ResolvedStructureSchema -> [CanonicalTerm ObjectId] -> StructureApplicationKey
application schema = structureApplicationKey (resolvedSchemaId schema)

parameterParent :: CheckedObjectClosure -> ResolvedStructureSchema -> IO ResolvedStructureSchema
parameterParent closure root = do
    let input = (wire 0 1 [application root []])
            { localWireLaws = [(LocalLawOrdinal 0, CEq TySet (CBound 0) (CBound 1))] }
    checkLocal closure 101 "parameter-parent" input >>= resolveOne [root]

boundsDiamondPredicates :: Assertion
boundsDiamondPredicates = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    let grow 0 known previous = pure (known, previous)
        grow remaining known previous = do
            let ordinal = 200 + 3 * remaining
                edge schema = application schema [CBound 0]
            left <- checkLocal closure ordinal ("left" <> fromString (show remaining)) (wire 0 1 [edge previous])
                >>= resolveOne known
            right <- checkLocal closure (ordinal + 1) ("right" <> fromString (show remaining)) (wire 0 1 [edge previous])
                >>= resolveOne known
            child <- checkLocal closure (ordinal + 2) ("join" <> fromString (show remaining)) (wire 0 1 [edge left, edge right])
                >>= resolveOne (left : right : known)
            assertEqual "duplicate paths do not enlarge the predicate"
                (Predicate.structurePredicateBody parent) (Predicate.structurePredicateBody child)
            assertEqual "duplicate paths do not enlarge provenance" [1]
                (Map.size . resolvedRequirementOccurrences <$> Map.elems (resolvedSchemaRequirements child))
            grow (remaining - 1) (child : left : right : known) child
    (_, final) <- grow 12 [root, parent] parent
    assertEqual "ancestor applications grow with distinct declarations, not paths"
        37 (Set.size (resolvedSchemaAncestors final))
    assertEqual "generated notion edges remain direct" 2 (Set.size (resolvedSchemaDirectParents final))

normalizesDiamond :: Assertion
normalizesDiamond = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    left <- checkLocal closure 102 "left" (wire 0 1 [application parent [CBound 0]])
        >>= resolveOne [root, parent]
    right <- checkLocal closure 103 "right" (wire 0 1 [application parent [CBound 0]])
        >>= resolveOne [root, parent]
    let parents = [application left [CBound 0], application right [CBound 0]]
    child <- checkLocal closure 104 "diamond" (wire 0 1 parents)
        >>= resolveOne [root, parent, left, right]
    reordered <- checkLocal closure 104 "diamond" (wire 0 1 (reverse parents))
        >>= resolveOne [root, parent, left, right]
    assertEqual "one shared requirement" 1 (Map.size (resolvedSchemaRequirements child))
    assertEqual "one provenance through both paths" [1]
        (Map.size . resolvedRequirementOccurrences <$> Map.elems (resolvedSchemaRequirements child))
    assertEqual "normalized requirements ignore parent presentation"
        (resolvedSchemaRequirements child) (resolvedSchemaRequirements reordered)
    assertEqual "schema content ignores parent presentation"
        (resolvedSchemaContentDigest child) (resolvedSchemaContentDigest reordered)
    assertEqual "canonical predicate ignores parent presentation"
        (Predicate.structurePredicateBody child) (Predicate.structurePredicateBody reordered)
    assertEqual "the common ancestor application occurs once" 1
        (length [key | key <- resolvedSchemaSemanticAncestorOrder child,
            structureApplicationId key == resolvedSchemaId parent])
    assertEqual "written parent order is retained" (reverse parents)
        (resolvedPresentationParentOrder (resolvedSchemaPresentation reordered))
    assertEqual "inheritance is named by its resolved parent"
        (Semantic.SearchEligible, [Semantic.semanticName "diamondinherit_left"])
        (Laws.structureLawPresentation child (ParentInheritanceLaw (application left [CBound 0])))
    assertEqual "reordering parents preserves the named law"
        (Semantic.SearchEligible, [Semantic.semanticName "diamondinherit_left"])
        (Laws.structureLawPresentation reordered (ParentInheritanceLaw (application left [CBound 0])))

namesParentApplications :: Assertion
namesParentApplications = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    let left = application parent [CBound 0]
        right = application parent [CBound 1]
        input = wire 0 2 [left, right]
        make source names = expectRight (checkLocalStructureSchema closure (origin 102 0) source
                (presentation "named_child" source)
                    {structurePresentationParents = [(name, Nowhere) | name <- names]})
                >>= resolveOne [root, parent]
    original <- make input [Just (Raw.Marker "left_instance"), Just (Raw.Marker "right_instance")]
    reordered <- make (wire 0 2 [right, left]) [Just (Raw.Marker "right_instance"), Just (Raw.Marker "left_instance")]
    assertEqual "labeled parent order does not affect mathematics"
        (resolvedSchemaContentDigest original) (resolvedSchemaContentDigest reordered)
    for_ [original, reordered] \schema ->
        for_ [(left, "left_instance"), (right, "right_instance")] \(target, name) ->
            assertEqual "each label names its complete checked application"
                (Just [Raw.Marker name])
                (Map.lookup target (resolvedPresentationParentAliases (resolvedSchemaPresentation schema)))
    leftChild <- checkLocal closure 103 "left_child" (wire 0 1 [application parent [CBound 0]])
        >>= resolveOne [root, parent]
    rightChild <- checkLocal closure 104 "right_child" (wire 0 1 [application parent [CBound 0]])
        >>= resolveOne [root, parent]
    grandchild <- checkLocal closure 105 "grandchild"
        (wire 0 2 [application leftChild [CBound 0], application rightChild [CBound 1]])
        >>= resolveOne [root, parent, leftChild, rightChild]
    for_ [left, right] \target -> do
        assertBool "ambiguous transitive application retains its internal inheritance law"
            (target `Set.member` resolvedSchemaAncestors grandchild)
        assertEqual "ambiguous transitive helper has no public alias" (Semantic.SearchEligible, [])
            (Laws.structureLawPresentation grandchild (ParentInheritanceLaw target))
    unlabeled <- expectRight (checkLocalStructureSchema closure (origin 102 0) input
        (presentation "named_child" input) {structurePresentationParents = [(Nothing, Nowhere), (Nothing, Nowhere)]})
    case resolveStructureBatch (lookupSchema [root, parent]) (unlabeled :| []) of
        Left StructureParentLabelRequired{} -> pure ()
        other -> assertFailure ("an ambiguous parent acquired an implicit name: " <> show other)
    conflicting <- expectRight (checkLocalStructureSchema closure (origin 102 0) input
        (presentation "named_child" input)
            {structurePresentationParents = [(Just (Raw.Marker "same"), Nowhere), (Just (Raw.Marker "same"), Nowhere)]})
    case resolveStructureBatch (lookupSchema [root, parent]) (conflicting :| []) of
        Left StructureParentAliasConflict{} -> pure ()
        other -> assertFailure ("one label selected two parent applications: " <> show other)

retainsApplications :: Assertion
retainsApplications = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    child <- checkLocal closure 102 "two-applications"
        (wire 0 1 [application parent [CBound 0], application parent [CBound 1]])
        >>= resolveOne [root, parent]
    assertEqual "both applications are direct parents" 2 (Set.size (resolvedSchemaDirectParents child))
    assertEqual "both specialized requirements survive" 2 (Map.size (resolvedSchemaRequirements child))
    assertEqual "the subject follows the declared parameter vector"
        [CBound 2, CBound 1, CBound 0] (schemaParameterArguments 3)
    let binderArgument = CApp (CApp (CIntrinsic Sep) (CBound 0))
            (CLam TySet (CEq TySet (CBound 0) (CBound 1)))
    assertEqual "substitution protects binders in compound parent arguments"
        (CEq TySet binderArgument (CBound 0))
        (specializeStructureBody 0 [binderArgument] (CEq TySet (CBound 0) (CBound 1)))

specializesPreamble :: Assertion
specializesPreamble = do
    (closure, root) <- fixture
    let input = (wire 0 1 [application root []])
            { localWirePreamble = [LocalPreambleWire (LocalPreambleClauseKey 0 0) 1
                (CEq TySet (CBound 0) (CIntrinsic Empty))] }
    parent <- checkLocal closure 101 "preamble-parent" input >>= resolveOne [root]
    child <- checkLocal closure 102 "subject-child" (wire 0 0 [application parent [CBound 0]])
        >>= resolveOne [root, parent]
    assertEqual "subject-dependent pullback retains admissibility placement"
        [ CEq TySet (CBound 0) (CIntrinsic Empty)
        , Record.recordOpenShape [] (CBound 0)
        ] (Predicate.structurePredicateComponents child)

checksPrefix :: Assertion
checksPrefix = do
    (closure, root) <- fixture
    let input = (wire 0 2 [application root []])
            { localWirePreamble = [LocalPreambleWire (LocalPreambleClauseKey 0 0) 1
                (CEq TySet (CBound 1) (CIntrinsic Empty))] }
    case checkLocalStructureSchema closure (origin 101 0) input (presentation "bad-prefix" input) of
        Left LocalStructureTermInvalid{} -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "a later parameter entered an earlier preamble row"

rejectsCycles :: Assertion
rejectsCycles = do
    (closure, root) <- fixture
    local <- checkLocal closure 101 "duplicate" (wire 0 0 [application root [], application root []])
    case resolveStructureBatch (lookupSchema [root]) (local :| []) of
        Left StructureDuplicateParent{} -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "duplicate direct edges were accepted"
    left <- checkLocal closure 102 "cycle-left" (wire 0 0 [structureApplicationKey (structureId (origin 102 1)) []])
    right <- checkLocal closure 102 "cycle-right" (wire 1 0 [structureApplicationKey (structureId (origin 102 0)) []])
    case resolveStructureBatch (lookupSchema [root]) (right :| [left]) of
        Left (StructureCycle identities) -> assertEqual "both cycle identities" 2 (length identities)
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "a cycle was accepted"

checksRegistration :: Assertion
checksRegistration = do
    (closure, root) <- fixture
    let predicateObject = transparentObject (resolvedSchemaTheory root)
            (Predicate.structurePredicateType root) (Predicate.structurePredicateBody root)
    active <- expectRight (extendObjectClosure closure [predicateObject])
    firstRegistration <- expectRight (Predicate.checkPendingStructureRegistration active root (assertedObjectId predicateObject))
    secondRegistration <- expectRight (Predicate.checkPendingStructureRegistration active root (assertedObjectId predicateObject))
    assertEqual "an already active predicate is reusable" firstRegistration secondRegistration
    case Predicate.checkPendingStructureRegistration closure root (assertedObjectId predicateObject) of
        Left Predicate.StructurePredicateObjectInvalid{} -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "an unavailable predicate was registered"
    let wrongObjects =
            [transparentObject (resolvedSchemaTheory root) (TyArrow TySet TyProp) (CLam TySet CTruth),
             transparentObject (resolvedSchemaTheory root) TyProp CTruth]
    malformed <- expectRight (extendObjectClosure active wrongObjects)
    for_ wrongObjects \object -> assertLeft "body and type must both match the normalized schema"
        (Predicate.checkPendingStructureRegistration malformed root (assertedObjectId object))

specializesRegistration :: Assertion
specializesRegistration = do
    (closure, root) <- fixture
    let law = CApp (CLam TyProp (CBound 0)) (CEq TySet (CBound 0) (CBound 1))
        input = (wire 0 1 [application root []])
            { localWirePreamble = [LocalPreambleWire (LocalPreambleClauseKey 0 0) 1
                (CEq TySet (CBound 0) (CIntrinsic Empty))]
            , localWireLaws = [(LocalLawOrdinal 0, law)] }
    schema <- checkLocal closure 101 "retained-registration" input >>= resolveOne [root]
    (active, registrations) <- registerSchemas closure [root, schema]
    let registration = fromMaybe (impossible "fixture lost its registration")
            (Map.lookup (resolvedSchemaId schema) registrations)
        subject = CIntrinsic Empty
        parameter = CApp (CIntrinsic PowerSet) subject
    applied <- maybe (assertFailure "valid application rejected" >> fail "unreachable") pure
        (Predicate.applyStructurePredicate registration subject [parameter])
    assertEqual "specialization retains the exact checked registration" registration
        (Predicate.appliedStructureRegistration applied)
    assertEqual "subject precedes the parameter in the application"
        (CApp (CApp (CGlobal (Predicate.pendingStructurePredicate registration)) subject) parameter)
        (Predicate.appliedStructureTerm applied)
    assertEqual "preamble and law binders specialize without normalizing the law"
        [CEq TySet parameter subject, Record.recordOpenShape [] subject,
         CApp (CLam TyProp (CBound 0)) (CEq TySet parameter subject)]
        (Predicate.appliedStructureComponents applied)
    let occurrences = Predicate.appliedStructureRequirementOccurrences applied
    assertEqual "plain requirements project the same specialization"
        (Predicate.appliedStructureRequirements applied) (fst <$> occurrences)
    assertEqual "every specialized requirement retains its complete provenance"
        (Set.fromList (concatMap (Map.keys . resolvedRequirementOccurrences)
            (Map.elems (resolvedSchemaRequirements schema))))
        (Set.fromList (concatMap (Map.keys . snd) occurrences))
    assertBool "wrong parameter count is rejected"
        (isNothing (Predicate.applyStructurePredicate registration subject []))
    -- Registration now requires the exact schema compiler body. A convertible
    -- wrapper accepted by the retired descriptor checker is deliberately invalid.
    let body = Predicate.structurePredicateBody schema
        wrapped = transparentObject (resolvedSchemaTheory schema)
            (Predicate.structurePredicateType schema)
            (CApp (CLam (Predicate.structurePredicateType schema) (CBound 0)) body)
    extended <- expectRight (extendObjectClosure active [wrapped])
    assertLeft "convertibility does not replace the normalized registration contract"
        (Predicate.checkPendingStructureRegistration extended schema (assertedObjectId wrapped))

checksResources :: Assertion
checksResources = do
    (closure, root) <- fixture
    let field = fieldId preludeModuleName (localDeclarationOrdinal 101) (structureFieldSlot 0)
        theory = resolvedSchemaTheory root
        input = (wire 0 0 [application root []])
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot 0) (Raw.StructSymbol "datum") Nothing] }
    selectorOnly <- expectRight (extendObjectClosure closure [Record.fieldSelectorObject theory field])
    case checkLocalStructureSchema selectorOnly (origin 101 0) input (presentation "datum-record" input) of
        Left (LocalStructureResourceMissing actual) ->
            assertEqual "the unused projection must still be present"
                (Record.fieldProjectionObjectId theory field) actual
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "a missing projection was accepted"
    complete <- expectRight (extendObjectClosure selectorOnly [Record.fieldProjectionObject theory field])
    local <- checkLocal complete 101 "datum-record" input
    schema <- resolveOne [root] local
    assertEqual "the canonical field identity survives resolution" [field]
        (resolvedSchemaSemanticFieldOrder schema)
    case checkLocalSchemaVisibility selectorOnly local of
        Left (LocalStructureResourceMissing _) -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "earlier typing evidence made a hidden projection visible"
    let carrierInput = input
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot 0) Raw.CarrierSymbol Nothing] }
    case checkLocalStructureSchema complete (origin 101 0) carrierInput (presentation "forged-carrier" carrierInput) of
        Left LocalStructureReservedCarrier{} -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "an ordinary declaration introduced the reserved carrier role"

registerSchemas
    :: CheckedObjectClosure -> [ResolvedStructureSchema]
    -> IO (CheckedObjectClosure, Map StructureId Predicate.PendingStructureRegistration)
registerSchemas closure = foldM register (closure, Map.empty)
  where
    register (active, registrations) schema = do
        let object = transparentObject (resolvedSchemaTheory schema)
                (Predicate.structurePredicateType schema) (Predicate.structurePredicateBody schema)
        extended <- if checkedObjectMember (assertedObjectId object) active
            then pure active else expectRight (extendObjectClosure active [object])
        registration <- expectRight (Predicate.checkPendingStructureRegistration extended schema (assertedObjectId object))
        pure (extended, Map.insert (resolvedSchemaId schema) registration registrations)

replayCatalogue
    :: CheckedObjectClosure -> Laws.CheckedStructureCatalogue -> Assertion
replayCatalogue closure catalogue = do
    foundation <- expectRight checkedFoundation
    for_ (Map.toAscList (Laws.structureCatalogueLaws catalogue)) \(key, spec) -> do
        imports <- for (Laws.generatedLawDependencies spec) \dependency ->
            Laws.CheckedGeneratedImport dependency <$> expectRight (Laws.structureDependencyTarget catalogue dependency)
        proof <- expectRight (Laws.buildStructureLawProof foundation catalogue key imports)
        judgements <- traverse (\(Laws.CheckedGeneratedImport _ target) ->
            expectRight (Kernel.derivationImportJudgement target)) imports
        replayed <- expectRight (Kernel.replayKernelDerivation foundation Kernel.defaultKernelReplayLimits
            (globalTypingFromClosure closure) (Vector.fromList judgements) (Laws.generatedLawTarget spec)
            (KernelProof.builtProofDerivation proof))
        assertEqual ("exact dependency use for " <> show key)
            (Set.fromList [Kernel.importIx index | (index, _) <- zip [0 ..] imports])
            (Kernel.replayedKernelImportUses replayed)
        assertEqual ("exact foundation footprint for " <> show key)
            (Laws.structureLawFoundationTags (Predicate.pendingStructureSchema (Laws.structureCatalogueRegistration catalogue)) key)
            (Kernel.replayedKernelFoundationUses replayed)
        assertEqual "no guarded-rule authority" Set.empty (Kernel.replayedKernelRuleUses replayed)

replaysCatalogue :: Assertion
replaysCatalogue = do
    (closure, root) <- fixture
    (active, registrations) <- registerSchemas closure [root]
    rootRegistration <- maybe (assertFailure "root registration missing" >> fail "unreachable") pure
        (Map.lookup (resolvedSchemaId root) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Map.keysSet registrations)
        (`Map.lookup` registrations) rootRegistration)
    assertEqual "one shape component plus twelve record laws" 13
        (Map.size (Laws.structureCatalogueLaws catalogue))
    replayCatalogue active catalogue

replaysInheritance :: Assertion
replaysInheritance = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    child <- checkLocal closure 102 "inheriting-child" (wire 0 1 [application parent [CBound 1]])
        >>= resolveOne [root, parent]
    (active, registrations) <- registerSchemas closure [root, parent, child]
    childRegistration <- maybe (assertFailure "child registration missing" >> fail "unreachable") pure
        (Map.lookup (resolvedSchemaId child) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Set.singleton (resolvedSchemaId child))
        (`Map.lookup` registrations) childRegistration)
    assertEqual "all ancestor applications receive inheritance laws" 2
        (length [() | ParentInheritanceLaw _ <- Map.keys (Laws.structureCatalogueLaws catalogue)])
    replayCatalogue active catalogue

sharesDefinitions :: Assertion
sharesDefinitions = do
    (closure, root) <- fixture
    child <- checkLocal closure 101 "empty-refinement" (wire 0 0 [application root []])
        >>= resolveOne [root]
    (active, registrations) <- registerSchemas closure [root, child]
    let childRegistration = fromMaybe (impossible "fixture lost its child registration")
            (Map.lookup (resolvedSchemaId child) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Set.singleton (resolvedSchemaId child))
        (`Map.lookup` registrations) childRegistration)
    let inherited = fromMaybe (impossible "fixture lost its inheritance law")
            (Map.lookup (ParentInheritanceLaw (application root [])) (Laws.structureCatalogueLaws catalogue))
    assertEqual "identical predicates need one definition import" 1
        (length (Laws.generatedLawDependencies inherited))
    replayCatalogue active catalogue

checksViewEligibility :: Assertion
checksViewEligibility = do
    (closure, root) <- fixture
    parent <- parameterParent closure root
    let compound = CApp (CApp (CIntrinsic Sep) (CBound 0))
            (CLam TySet (CEq TySet (CBound 0) (CBound 1)))
        variableKey = application parent [CBound 1]
        compoundKey = application parent [compound]
    child <- checkLocal closure 102 "mixed-applications" (wire 0 1 [variableKey, compoundKey])
        >>= resolveOne [root, parent]
    assertEqual "the shared subject retains its de Bruijn index"
        (Right (Just (Vector.singleton (ViewVariableIx 1))))
        (Laws.inheritanceViewVariables child variableKey)
    assertEqual "compound arguments have no generated view" (Right Nothing)
        (Laws.inheritanceViewVariables child compoundKey)
    case Laws.inheritanceViewVariables child (application root []) of
        Left Laws.StructureViewNotDirect{} -> pure ()
        other -> assertFailure ("transitive generated view was accepted: " <> show other)
    (active, registrations) <- registerSchemas closure [root, parent, child]
    let childRegistration = fromMaybe (impossible "fixture lost its child registration")
            (Map.lookup (resolvedSchemaId child) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Set.singleton (resolvedSchemaId child))
        (`Map.lookup` registrations) childRegistration)
    assertBool "the compound inheritance theorem remains in the checked catalogue"
        (Map.member (ParentInheritanceLaw compoundKey) (Laws.structureCatalogueLaws catalogue))
    replayCatalogue active catalogue

checksInheritedResources :: Assertion
checksInheritedResources = do
    (closure, root) <- fixture
    foundation <- expectRight checkedFoundation
    let theory = resolvedSchemaTheory root
        fields = [fieldId preludeModuleName (localDeclarationOrdinal 101) (structureFieldSlot i) | i <- [0, 1]]
        input = (wire 0 0 [application root []])
            { localWireFields =
                [LocalStructureFieldWire (structureFieldSlot i) (Raw.StructSymbol name) Nothing
                | (i, name) <- [(0, "datum0"), (1, "datum1")]] }
    withFields <- expectRight (extendObjectClosure closure
        (concatMap (\field -> [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field]) fields))
    parent <- checkLocal withFields 101 "field-parent" input >>= resolveOne [root]
    child <- checkLocal withFields 102 "field-child" (wire 0 0 [application parent []])
        >>= resolveOne [root, parent]
    (active, registrations) <- registerSchemas withFields [root, parent, child]
    let childRegistration = fromMaybe (impossible "fixture lost its child registration")
            (Map.lookup (resolvedSchemaId child) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Set.singleton (resolvedSchemaId child))
        (`Map.lookup` registrations) childRegistration)
    replayCatalogue active catalogue
    let dependencies = concatMap Laws.generatedLawDependencies (Map.elems (Laws.structureCatalogueLaws catalogue))
    for_ fields \field -> for_ [SelectorDefinitionResource field, ProjectionMembershipResource field] \resource ->
        assertBool "inherited resources name the defining structure"
            (Laws.EnvironmentDependency (resolvedSchemaId parent) (StructureResourceFact resource) `elem` dependencies)
    case fields of
        [firstField, secondField] -> do
            let key = RecordSchemaLaw (Record.RecordProjectionEntryLaw firstField)
                spec = fromMaybe (impossible "fixture lost its projection law")
                    (Map.lookup key (Laws.structureCatalogueLaws catalogue))
                wrongTarget = checkedPropositionTerm (fromMaybe (impossible "fixture lost its other projection resource")
                    (Map.lookup (ProjectionMembershipResource secondField) (Laws.structureCatalogueResources catalogue)))
            case Laws.buildStructureLawProof foundation catalogue key
                    [Laws.CheckedGeneratedImport dependency wrongTarget | dependency <- Laws.generatedLawDependencies spec] of
                Left Laws.StructureLawDependencyTargetMismatch{} -> pure ()
                Left other -> assertFailure (show other)
                Right _ -> assertFailure "a swapped projection resource was accepted"
        _ -> impossible "fixture field family changed"

stableFieldLawNames :: Assertion
stableFieldLawNames = do
    (closure, root) <- fixture
    let theory = resolvedSchemaTheory root
        fields = [fieldId preludeModuleName (localDeclarationOrdinal 101) (structureFieldSlot i) | i <- [0, 1]]
        input names = (wire 0 0 [application root []])
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot i) (Raw.StructSymbol name) Nothing
                | (i, name) <- zip [0..] names] }
    active <- expectRight (extendObjectClosure closure
        (concatMap (\field -> [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field]) fields))
    original <- checkLocal active 101 "stable" (input ["leftValue", "rightValue"]) >>= resolveOne [root]
    reordered <- checkLocal active 101 "stable" (input ["rightValue", "leftValue"]) >>= resolveOne [root]
    let fieldFor schema role = fromMaybe (impossible "the reordered schema lost a field role")
            (Map.lookup (Raw.StructSymbol role) (resolvedSchemaFieldRoles schema))
    assertBool "re-elaboration may assign a different generative coordinate"
        (fieldFor original "leftValue" /= fieldFor reordered "leftValue")
    for_ [original, reordered] \schema -> for_ ["leftValue", "rightValue"] \role -> do
        let field = fieldFor schema role
        assertEqual "the named projection selects its role, not its written position"
            (Semantic.SearchEligible, [Semantic.semanticName ("stableaggregateprojection_" <> role)])
            (Laws.structureLawPresentation schema (RecordSchemaLaw (Record.RecordAggregateProjectionLaw field)))
        assertEqual "the named reduct projection selects the same role"
            (Semantic.SearchIneligible, [Semantic.semanticName ("stablereductprojection_" <> role)])
            (Laws.structureLawPresentation schema (RecordSchemaLaw (Record.RecordReductProjectionLaw field)))

checksBatchSlots :: Assertion
checksBatchSlots = do
    (closure, root) <- fixture
    let theory = resolvedSchemaTheory root
        firstIdentity = fieldId preludeModuleName (localDeclarationOrdinal 101) (structureFieldSlot 0)
        secondIdentity = fieldId preludeModuleName (localDeclarationOrdinal 101) (structureFieldSlot 1)
        firstInput = (wire 0 0 [application root []])
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot 0) (Raw.StructSymbol "first-datum") Nothing] }
        secondInput = (wire 1 0 [structureApplicationKey (structureId (origin 101 0)) []])
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot 1) (Raw.StructSymbol "second-datum") Nothing] }
    active <- expectRight (extendObjectClosure closure
        (concatMap (\field -> [Record.fieldSelectorObject theory field, Record.fieldProjectionObject theory field])
            [firstIdentity, secondIdentity]))
    firstLocal <- checkLocal active 101 "batch-parent" firstInput
    secondLocal <- checkLocal active 101 "batch-child" secondInput
    forward <- expectRight (resolveStructureBatch (lookupSchema [root]) (firstLocal :| [secondLocal]))
    backward <- expectRight (resolveStructureBatch (lookupSchema [root]) (secondLocal :| [firstLocal]))
    assertEqual "batch list order does not affect canonical resolution" forward backward
    let child = fromMaybe (impossible "batch fixture lost its child")
            (find ((== localSchemaId secondLocal) . resolvedSchemaId) forward)
    assertEqual "both independently allocated fields survive inheritance"
        (Set.fromList [firstIdentity, secondIdentity]) (Map.keysSet (resolvedSchemaFields child))
    assertEqual "presentation keeps the parent before the local field"
        [firstIdentity, secondIdentity] (resolvedPresentationFieldOrder (resolvedSchemaPresentation child))
    let restartedInput = secondInput
            { localWireFields = [LocalStructureFieldWire (structureFieldSlot 0) (Raw.StructSymbol "second-datum") Nothing] }
    restarted <- checkLocal active 101 "batch-child" restartedInput
    case resolveStructureBatch (lookupSchema [root]) (restarted :| [firstLocal]) of
        Left StructureBatchFieldSlotsInvalid{} -> pure ()
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "per-schema field-slot allocation was accepted"

rootCatalogueFixture
    :: IO (CheckedObjectClosure, LocalStructureSchema, Predicate.PendingStructureRegistration,
        Laws.CheckedStructureCatalogue)
rootCatalogueFixture = do
    (closure, root) <- fixture
    let input = wire 0 0 []
    local <- expectRight (checkManifestLocalStructureSchema closure (origin 100 0)
        GeneralRecordRoot input (presentation "record" input))
    (active, registrations) <- registerSchemas closure [root]
    let registration = fromMaybe (impossible "fixture lost its root")
            (Map.lookup (resolvedSchemaId root) registrations)
    catalogue <- expectRight (Laws.checkStructureCatalogue active (Map.keysSet registrations)
        (`Map.lookup` registrations) registration)
    pure (active, local, registration, catalogue)

checksPendingBatch :: Assertion
checksPendingBatch = do
    (closure, local, registration, catalogue) <- rootCatalogueFixture
    let owner = localSchemaId local
        positions = Map.fromList
            [(Laws.generatedLawId law, PlannedCandidatePosition stage 0)
            | (stage, law) <- zip [1 ..] (Map.elems (Laws.structureCatalogueLaws catalogue))]
        resources = Map.singleton owner
            (Map.singleton PredicateDefinitionResource (LocalCandidateReference (PlannedCandidatePosition 0 0)))
        check laws refs = Batch.checkPendingStructureBatch closure (const Nothing)
            (local :| []) (registration :| []) laws refs
    batch <- expectRight (check positions resources)
    assertEqual "the checked batch retains exact resource references" resources
        (Batch.pendingBatchResourceReferences batch)
    assertLeft "a missing structural law is rejected"
        (check (Map.delete (StructureLawId owner (RecordSchemaLaw Record.RecordExactGraphLaw)) positions) resources)
    assertLeft "equal-target laws cannot share a candidate position"
        (check (Map.map (const (PlannedCandidatePosition 1 0)) positions) resources)
    assertLeft "a missing resource is rejected" (check positions (Map.singleton owner Map.empty))
    let component = StructureLawId owner (PredicateComponentLaw PredicateShapeComponent)
    assertLeft "a definition in the same stage cannot support a law"
        (check (Map.insert component (PlannedCandidatePosition 0 1) positions) resources)
    assertLeft "resources cannot reuse law positions"
        (check positions (Map.singleton owner (Map.singleton PredicateDefinitionResource
            (LocalCandidateReference (PlannedCandidatePosition 1 0)))))

checksInterfaces :: Assertion
checksInterfaces = do
    foundation <- expectRight checkedFoundation
    (closure, local, registration, catalogue) <- rootCatalogueFixture
    let owner = localSchemaId local
        theory = checkedObjectClosureTheory closure
        lawRows = [(StructureLawFact law, Laws.generatedLawProposition spec,
                Semantic.structureLawPurpose (Laws.generatedLawId spec),
                Authority.CheckedKernelConstruction (Authority.CheckedStructureLaw (Laws.structureLawFamily law)))
            | (law, spec) <- Map.toAscList (Laws.structureCatalogueLaws catalogue)]
        resourceRows = [(StructureResourceFact PredicateDefinitionResource,
            Predicate.structurePredicateDefinitionProposition registration, Semantic.GeneralFactPurpose,
            Authority.CheckedKernelConstruction (Authority.CheckedDefinitionEquation (Predicate.pendingStructurePredicate registration)))]
        rows = Map.fromList [(key, Interface.StructureOccurrence proposition
                (Semantic.semanticFactOccurrence purpose (Semantic.factSlot preludeModuleName (localFactOrdinal index))
                    (Authority.factAuthority (theoremRef theory (checkedPropositionId proposition)) Authority.cleanAuthoritySafety)
                    (case key of
                        StructureLawFact law -> fst (Laws.structureLawPresentation (Predicate.pendingStructureSchema registration) law)
                        StructureResourceFact _ -> Semantic.SearchIneligible)) direct)
            | (index, (key, proposition, purpose, direct)) <- zip [0 ..] (lawRows <> resourceRows)]
        check supplied = Interface.checkStructureInterfaces foundation closure Just (const Nothing)
            (local :| []) (registration :| []) (Map.singleton owner supplied)
        key = StructureLawFact (RecordSchemaLaw Record.RecordProjectionExtensionalityLaw)
        alter change = Map.adjust change key rows
        replacePurpose purpose (Interface.StructureOccurrence proposition metadata direct) =
            Interface.StructureOccurrence proposition (Semantic.semanticFactOccurrence purpose
                (Semantic.semanticFactSlot metadata) (Semantic.semanticFactAuthority metadata) Semantic.SearchIneligible) direct
    interface :| _ <- expectRight (check rows)
    assertEqual "all thirteen law occurrences survive content sharing" 13
        (Map.size (Interface.structureInterfaceLawIndex interface))
    assertLeft "the actual purpose must match the indexed law"
        (check (alter (replacePurpose Semantic.GeneralFactPurpose)))
    assertLeft "another structural purpose cannot stand in for an equal-target law"
        (check (alter (replacePurpose (Semantic.structureLawPurpose
            (StructureLawId owner (RecordSchemaLaw Record.RecordExactGraphLaw))))))
    assertLeft "an incomplete interface cannot be assembled" (check (Map.delete key rows))
    assertLeft "a source proof cannot grant generated structural authority"
        (check (alter (\(Interface.StructureOccurrence proposition metadata _) ->
            Interface.StructureOccurrence proposition metadata (Authority.CheckedSourceProof Authority.NoExternalProofUse))))
    let replaceSafety (Interface.StructureOccurrence proposition metadata direct) =
            Interface.StructureOccurrence proposition
                (Semantic.semanticFactOccurrence (Semantic.semanticFactPurpose metadata)
                    (Semantic.semanticFactSlot metadata)
                    (Authority.factAuthority (Authority.factAuthorityTheorem (Semantic.semanticFactAuthority metadata))
                        (Authority.authoritySafety (Authority.singletonEscapeKind Authority.Omitted)))
                    Semantic.SearchIneligible) direct
    assertLeft "an escaped proof cannot grant clean structural authority" (check (alter replaceSafety))
    certificates <- traverse (\(Interface.StructureOccurrence proposition metadata direct) -> do
        certificate <- expectRight (Authority.validationCertificate (Semantic.semanticFactAuthority metadata) direct)
        pure (Interface.StructureOccurrence proposition metadata certificate))
        (Interface.structureInterfaceOccurrences interface)
    rebound <- expectRight (Interface.rebindStructureInterfaceEvidence Just
        (Just . Authority.validationDirectAuthorization) certificates interface)
    assertBool "phase conversion preserves the complete mathematical interface"
        (Interface.sameStructureInterface interface rebound)
    assertLeft "phase conversion cannot invent missing registry evidence"
        (Interface.rebindStructureInterfaceEvidence Just
            (Just . Authority.validationDirectAuthorization) Map.empty interface)

assertLeft :: Show result => String -> Either failure result -> Assertion
assertLeft message = \case
    Left _ -> pure ()
    Right result -> assertFailure (message <> ": " <> show result)

expectRight :: Show failure => Either failure result -> IO result
expectRight = either (\failure -> assertFailure (show failure) >> fail "unreachable") pure

roundTripsStructureWire :: Assertion
roundTripsStructureWire = do
    (closure, local, registration, catalogue) <- rootCatalogueFixture
    let theory = checkedObjectClosureTheory closure
        rows = [(StructureLawFact law, Laws.generatedLawProposition spec, Semantic.structureLawPurpose (Laws.generatedLawId spec))
                | (law, spec) <- Map.toAscList (Laws.structureCatalogueLaws catalogue)]
            <> [(StructureResourceFact key, proposition, Semantic.GeneralFactPurpose)
                | (key, proposition) <- Map.toAscList (Laws.structureCatalogueResources catalogue)]
        references = Map.fromList [(key, Semantic.semanticFactOccurrenceFingerprint purpose
                (Semantic.factSlot preludeModuleName (localFactOrdinal ordinal))
                (Authority.factAuthority (theoremRef theory (checkedPropositionId proposition)) Authority.cleanAuthoritySafety))
            | (ordinal, (key, proposition, purpose)) <- zip [0 ..] rows]
    wire' <- expectRight (Semantic.structureInterfaceWire local registration
        (Map.fromList [(law, fingerprint) | (StructureLawFact law, fingerprint) <- Map.toAscList references])
        (Map.fromList [(resource, fingerprint) | (StructureResourceFact resource, fingerprint) <- Map.toAscList references]))
    decoded <- expectRight (decodeCache Semantic.getStructureInterfaceWireCache
        (encodeCache (Semantic.putStructureInterfaceWireCache wire')))
    assertEqual "wire claims survive disposable cache encoding" wire' decoded
    assertEqual "local inputs survive encoding" (Right (localSchemaWire local)) (Semantic.structureWireLocalInput decoded)
    assertEqual "source presentation is reconstructed independently" (Right (localPresentation local))
        (Semantic.materializeStructureWirePresentation decoded)
    assertBool "normalized presentation is exact" (Semantic.structureWirePresentationMatches decoded (Predicate.pendingStructureSchema registration))

rejectsUnavailableLaws :: Assertion
rejectsUnavailableLaws = do
    foundation <- expectRight checkedFoundation
    (closure, _local, registration, catalogue) <- rootCatalogueFixture
    let schema = Predicate.pendingStructureSchema registration
        absent = PredicateComponentLaw (PredicateRequirementComponent
            (RequirementProvenanceKey (LawOrigin (resolvedSchemaId schema) (LocalLawOrdinal 0)) (application schema [])))
    case Laws.buildStructureLawProof foundation catalogue absent [] of
        Left (Laws.StructureLawUnavailable actual) -> assertEqual "missing exact law" absent actual
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "an unregistered predicate law was built"
    let input = (wire 0 0 [application schema []]) { localWireLaws = [(LocalLawOrdinal 0, CTruth)] }
    local <- checkLocal closure 102 "changed-batch" input
    resolved <- resolveOne [schema] local
    (active, registrations) <- registerSchemas closure [schema, resolved]
    let lookupRegistration identity = Map.lookup identity registrations
        original = fromMaybe (impossible "fixture lost its registration") (lookupRegistration (resolvedSchemaId resolved))
    changed <- checkLocal active 102 "changed-batch"
        input { localWireLaws = [(LocalLawOrdinal 0, CFalsum)] }
    case Batch.checkStructureBatchRegistrations active (\identity -> if identity == resolvedSchemaId schema then lookupRegistration identity else Nothing) (changed :| []) (original :| []) of
        Left (Batch.StructureBatchRegistrationMismatch actual) -> assertEqual "changed registration owner" (localSchemaId changed) actual
        Left other -> assertFailure (show other)
        Right _ -> assertFailure "a checked registration was paired with changed local laws"
