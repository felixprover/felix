{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Request-wide shallow identities and the frozen typed term catalogue used
-- by bounded refutation. Core owns checked occurrence analysis; this module
-- owns the two fixed catalogue policies which consume that evidence.
module Felix.Checking.Obvious.Search
    ( TermId(..)
    , FormulaId(..)
    , TypeId(..)
    , Catalogue
    , CatalogueTerm
    , catalogueTermValue
    , catalogueTermTypeId
    , catalogueTermApplication
    , catalogueTermCount
    , catalogueTerm
    , cataloguePropositionTypeId
    , findCatalogueTypeCounted
    , findCatalogueTermCounted
    , CatalogueTypeTerms
    , catalogueTypeTermsCounted
    , nextCatalogueTypeTermCounted
    , HeadRefs(..)
    , CataloguedRootRefs
    , cataloguedRootTermId
    , cataloguedRootHeadRefs
    , CataloguedNodeRefs
    , CataloguedLogicalView
    , CataloguedFormulaView
    , cataloguedFormulaView
    , cataloguedFormulaLogicalView
    , cataloguedFormulaRootReferences
    , InitialCatalogueResult
    , initialCatalogue
    , initialRootViews
    , collectInitialCatalogue
    , InitialCatalogueCursor
    , InitialCatalogueStep(..)
    , startInitialCatalogue
    , advanceInitialCatalogue
    , ResolvedTermRef
    , resolvedTermExistingId
    , ResolvedTermView
    , resolvedTermViewValue
    , resolvedTermViewApplication
    , resolvedTermView
    , ResolvedDerivedProposition
    , resolvedDerivedValue
    , resolvedDerivedRootRef
    , resolvedDerivedHeadRefs
    , prepareResolvedDerivedPropositionCounted
    , StagedTermAdmission
    , stagedCatalogue
    , stagedLogicalView
    , finishDerivedPropositionCounted
    , CatalogueError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Obvious.LogicalView qualified as LogicalView
import Felix.Checking.Obvious.Template qualified as Template

import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Word (Word)


newtype TermId = TermId Int
    deriving stock (Show, Eq, Ord)

-- | Refutation is the sole allocator. The newtype lives here because the
-- equality engine and coordinator both use it.
newtype FormulaId = FormulaId Int
    deriving stock (Show, Eq, Ord)

newtype TypeId = TypeId Int
    deriving stock (Show, Eq, Ord)

data CatalogueTerm global = CatalogueTerm
    !(ScopedCheckedCore global)
    !TypeId
    !(Maybe (TermId, TermId))

catalogueTermValue :: CatalogueTerm global -> ScopedCheckedCore global
catalogueTermValue (CatalogueTerm value _typeId _application) = value

catalogueTermTypeId :: CatalogueTerm global -> TypeId
catalogueTermTypeId (CatalogueTerm _value typeId _application) = typeId

catalogueTermApplication
    :: CatalogueTerm global
    -> Maybe (TermId, TermId)
catalogueTermApplication (CatalogueTerm _value _typeId application) = application

-- Equal terms have equal heads. Globals deliberately share a discriminator:
-- this catalogue requires only Eq global, and the index grants no authority.
data TermHead
    = BoundHead | GlobalHead | IntrinsicHead !CoreIntrinsicTag | SelectionHead
    | IntegerHead | ApplicationHead | LambdaHead | FalsumHead | TruthHead
    | NegationHead | ConjunctionHead | DisjunctionHead | ImplicationHead
    | EqualityHead | UniversalHead | ExistentialHead
    deriving stock (Eq, Ord)

termHead :: CanonicalTerm global -> TermHead
termHead = \case
    CBound{} -> BoundHead
    CGlobal{} -> GlobalHead
    CIntrinsic tag -> IntrinsicHead tag
    CLogicalSelect{} -> SelectionHead
    COpaqueInteger{} -> IntegerHead
    CApp{} -> ApplicationHead
    CLam{} -> LambdaHead
    CFalsum -> FalsumHead
    CTruth -> TruthHead
    CNot{} -> NegationHead
    CAnd{} -> ConjunctionHead
    COr{} -> DisjunctionHead
    CImp{} -> ImplicationHead
    CEq{} -> EqualityHead
    CForall{} -> UniversalHead
    CExists{} -> ExistentialHead

type TermBucket = Map TermHead (Seq TermId)

-- | The term table and each type/head bucket retain admission order. The
-- proposition type is cached and cannot be absent after initial collection.
data Catalogue global = Catalogue
    !(Seq CoreType)
    !(Seq (CatalogueTerm global))
    !(Seq TermBucket)
    !TypeId

catalogueTermCount :: Catalogue global -> Word
catalogueTermCount (Catalogue _types terms _buckets _propositionType) =
    fromIntegral (Seq.length terms)

catalogueTerm
    :: Catalogue global
    -> TermId
    -> Maybe (CatalogueTerm global)
catalogueTerm (Catalogue _types terms _buckets _propositionType)
        (TermId position) =
    Seq.lookup position terms

cataloguePropositionTypeId :: Catalogue global -> TypeId
cataloguePropositionTypeId
        (Catalogue _types _terms _buckets propositionType) =
    propositionType

data CatalogueBuilder global = CatalogueBuilder
    !(Seq CoreType)
    !(Seq (CatalogueTerm global))
    !(Seq TermBucket)
    !(Maybe TypeId)

emptyCatalogueBuilder :: CatalogueBuilder global
emptyCatalogueBuilder =
    CatalogueBuilder Seq.empty Seq.empty Seq.empty Nothing

data CatalogueError
    = CatalogueWorkExhausted
    | CatalogueGroundTermLimitExhausted
    | CatalogueOutsideFrozenUniverse
    | CatalogueIntegrityFailure !Text
    deriving stock (Show, Eq)

data CatalogueWork = CatalogueWork
    { remainingStructuralWork :: !Word
    , rowsAdmitted :: !Word
    }

type Counted value = ExceptT CatalogueError (State CatalogueWork) value

runCounted :: Word -> Counted value -> (Either CatalogueError value, Word)
runCounted available operation =
    let (result, remaining, _admissions) = runAdmissionCounted available operation
    in (result, remaining)

runAdmissionCounted :: Word -> Counted value -> (Either CatalogueError value, Word, Word)
runAdmissionCounted available operation =
    let (result, final) = State.runState (Except.runExceptT operation) (CatalogueWork available 0)
    in (result, remainingStructuralWork final, rowsAdmitted final)

charge :: Counted ()
charge = do
    remaining <- State.gets remainingStructuralWork
    if remaining == 0
        then Except.throwE CatalogueWorkExhausted
        else State.modify' (\state -> state {remainingStructuralWork = remaining - 1})

recordAdmission :: Counted ()
recordAdmission = do
    admitted <- State.gets rowsAdmitted
    when (admitted == maxBound)
        (Except.throwE (CatalogueIntegrityFailure "catalogue admission counter overflow"))
    State.modify' (\state -> state {rowsAdmitted = admitted + 1})

runStructural
    :: (Word -> (Either (CountedCoreFailure error) value, Word))
    -> (error -> CatalogueError)
    -> Counted value
runStructural operation domainFailure = do
    available <- State.gets remainingStructuralWork
    let (result, remaining) = operation available
    State.modify' (\state -> state {remainingStructuralWork = remaining})
    case result of
        Left CountedCoreStructuralWorkExhausted ->
            Except.throwE CatalogueWorkExhausted
        Left (CountedCoreOperationFailed failure) ->
            Except.throwE (domainFailure failure)
        Right value -> pure value

integrity :: Show error => Text -> error -> CatalogueError
integrity label failure =
    CatalogueIntegrityFailure
        (label <> ": " <> fromString (show failure))

rebaseGround
    :: CheckedOccurrence global
    -> Counted (Maybe (ScopedCheckedCore global))
rebaseGround row =
    runStructural
        (\work -> countedRebaseCheckedOccurrence work row)
        (integrity "catalogue occurrence rebase failed")

findTypeIn
    :: Seq CoreType
    -> CoreType
    -> Counted (Maybe TypeId)
findTypeIn types candidate = scan 0 (Seq.viewl types)
  where
    scan _position Seq.EmptyL = pure Nothing
    scan position (existing Seq.:< rest) = do
        charge
        equal <-
            runStructural
                (\work -> countedCoreTypeIdentity work existing candidate)
                absurd
        if equal
            then pure (Just (TypeId position))
            else scan (position + 1) (Seq.viewl rest)

findCatalogueTypeC
    :: Catalogue global
    -> CoreType
    -> Counted (Maybe TypeId)
findCatalogueTypeC (Catalogue types _terms _buckets _propositionType) =
    findTypeIn types

findCatalogueTypeCounted
    :: Word
    -> Catalogue global
    -> CoreType
    -> (Either CatalogueError (Maybe TypeId), Word)
findCatalogueTypeCounted available catalogue candidate =
    runCounted available (findCatalogueTypeC catalogue candidate)

-- | An immutable exact-type inventory in original TermId order. Each head
-- bucket already has that order, so a bounded-head merge can produce a small
-- prefix without scanning unrelated types or sorting the complete population.
-- The owner retains this cursor with the catalogue snapshot that produced it.
newtype CatalogueTypeTerms = CatalogueTypeTerms (Map TermId (Seq TermId))

catalogueTypeTermsCounted
    :: Word
    -> Catalogue global
    -> TypeId
    -> (Either CatalogueError CatalogueTypeTerms, Word)
catalogueTypeTermsCounted available (Catalogue _types _terms buckets _propositionType) typeId =
    runCounted available do
        charge
        bucket <- maybe
            (Except.throwE (CatalogueIntegrityFailure "term inventory received an unknown TypeId"))
            pure (bucketAt buckets typeId)
        CatalogueTypeTerms <$> foldM addHead Map.empty (Map.elems bucket)
  where
    addHead queue terms = do
        charge
        pure (case Seq.viewl terms of
            Seq.EmptyL -> queue
            first Seq.:< rest -> Map.insert first rest queue)

nextCatalogueTypeTermCounted
    :: Word
    -> CatalogueTypeTerms
    -> (Either CatalogueError (Maybe (TermId, CatalogueTypeTerms)), Word)
nextCatalogueTypeTermCounted available (CatalogueTypeTerms queue) =
    runCounted available do
        charge -- one row and a queue bounded by the fixed TermHead population
        pure (case Map.minViewWithKey queue of
            Nothing -> Nothing
            Just ((termId, tailBucket), rest) ->
                let following = case Seq.viewl tailBucket of
                        Seq.EmptyL -> rest
                        first Seq.:< remaining -> Map.insert first remaining rest
                in Just (termId, CatalogueTypeTerms following))

bucketAt
    :: Seq TermBucket
    -> TypeId
    -> Maybe TermBucket
bucketAt buckets (TypeId position) = Seq.lookup position buckets

selectHead :: TermBucket -> CanonicalTerm global -> Counted (Seq TermId)
selectHead bucket candidate = do
    charge -- shallow discriminator and bounded constructor-map selection
    pure (Map.findWithDefault Seq.empty (termHead candidate) bucket)

appendHead :: TermBucket -> CanonicalTerm global -> TermId -> Counted TermBucket
appendHead bucket candidate termId = do
    charge -- discriminator and index maintenance, in addition to row admission
    pure (Map.alter (Just . (Seq.|> termId) . fromMaybe Seq.empty)
        (termHead candidate) bucket)

findTermIn
    :: Eq global
    => Seq (CatalogueTerm global)
    -> TermBucket
    -> CanonicalTerm global
    -> Maybe (TermId, TermId)
    -> Counted (Maybe TermId)
findTermIn terms bucket candidate application =
    selectHead bucket candidate >>= scan . Seq.viewl
  where
    scan Seq.EmptyL = pure Nothing
    scan (termId@(TermId position) Seq.:< rest) = do
        charge
        existing <-
            maybe
                (Except.throwE
                    (CatalogueIntegrityFailure
                        "typed catalogue bucket contains an unknown TermId"))
                pure
                (Seq.lookup position terms)
        -- Builder children already have identities in this same catalogue.
        -- Unequal child pairs can reject a candidate, but equal pairs still
        -- require counted exact checking. Missing child metadata cannot reject.
        compatible <- case (application, catalogueTermApplication existing) of
            (Just expected, Just actual) -> charge >> pure (expected == actual)
            _ -> pure True
        equal <- if compatible
            then runStructural
                (\work ->
                    countedCanonicalIdentity work
                        (scopedCoreTerm (catalogueTermValue existing)) candidate)
                absurd
            else pure False
        if equal then pure (Just termId) else scan (Seq.viewl rest)

findCatalogueTermC
    :: Eq global
    => Catalogue global
    -> TypeId
    -> CanonicalTerm global
    -> Counted (Maybe TermId)
findCatalogueTermC
        (Catalogue _types terms buckets _propositionType) typeId candidate =
    case bucketAt buckets typeId of
        Nothing ->
            Except.throwE
                (CatalogueIntegrityFailure
                    "catalogue lookup received an unknown TypeId")
        Just bucket -> findTermIn terms bucket candidate Nothing

findCatalogueTermCounted
    :: Eq global
    => Word
    -> Catalogue global
    -> TypeId
    -> CanonicalTerm global
    -> (Either CatalogueError (Maybe TermId), Word)
findCatalogueTermCounted available catalogue typeId candidate =
    runCounted available (findCatalogueTermC catalogue typeId candidate)

internBuilderType
    :: CatalogueBuilder global
    -> CoreType
    -> Counted (CatalogueBuilder global, TypeId)
internBuilderType builder@(CatalogueBuilder types terms buckets propositionType)
        candidate =
    findTypeIn types candidate >>= \case
        Just typeId -> pure (builder, typeId)
        Nothing -> do
            charge
            let typeId = TypeId (Seq.length types)
                cached =
                    case candidate of
                        TyProp -> Just typeId
                        _ -> propositionType
            pure
                ( CatalogueBuilder
                    (types Seq.|> candidate)
                    terms
                    (buckets Seq.|> Map.empty)
                    cached
                , typeId
                )

findBuilderTerm
    :: Eq global
    => CatalogueBuilder global
    -> TypeId
    -> CanonicalTerm global
    -> Maybe (TermId, TermId)
    -> Counted (Maybe TermId)
findBuilderTerm (CatalogueBuilder _types terms buckets _propositionType)
        typeId candidate application =
    case bucketAt buckets typeId of
        Nothing ->
            Except.throwE
                (CatalogueIntegrityFailure
                    "builder lookup received an unknown TypeId")
        Just bucket -> findTermIn terms bucket candidate application

appendBuilderTerm
    :: Word
    -> CatalogueBuilder global
    -> TypeId
    -> ScopedCheckedCore global
    -> Maybe (TermId, TermId)
    -> Counted (CatalogueBuilder global, TermId)
appendBuilderTerm termLimit
        (CatalogueBuilder types terms buckets propositionType)
        typeId value application = do
    when (fromIntegral (Seq.length terms) >= termLimit)
        (Except.throwE CatalogueGroundTermLimitExhausted)
    charge
    let termId = TermId (Seq.length terms)
        row = CatalogueTerm value typeId application
    bucket <-
        maybe
            (Except.throwE
                (CatalogueIntegrityFailure
                    "builder append received an unknown TypeId"))
            pure
            (bucketAt buckets typeId)
    updatedBucket <- appendHead bucket (scopedCoreTerm value) termId
    let TypeId bucketPosition = typeId
        updatedBuckets =
            Seq.update bucketPosition updatedBucket buckets
    recordAdmission
    pure
        ( CatalogueBuilder types (terms Seq.|> row) updatedBuckets
            propositionType
        , termId
        )

internBuilderTerm
    :: Eq global
    => Word
    -> CatalogueBuilder global
    -> TypeId
    -> ScopedCheckedCore global
    -> Maybe (TermId, TermId)
    -> Counted (CatalogueBuilder global, TermId)
internBuilderTerm termLimit builder typeId value application =
    findBuilderTerm builder typeId (scopedCoreTerm value) application >>= \case
        Just termId -> pure (builder, termId)
        Nothing -> appendBuilderTerm termLimit builder typeId value application

explicitTypePayload :: CheckedOccurrenceView global -> Maybe CoreType
explicitTypePayload = \case
    OccurrenceLogicalSelect coreType -> Just coreType
    OccurrenceLambda coreType _body -> Just coreType
    OccurrenceEquality coreType _left _right -> Just coreType
    OccurrenceUniversal coreType _body -> Just coreType
    OccurrenceExistential coreType _body -> Just coreType
    _ -> Nothing

occurrenceViewChildren
    :: CheckedOccurrenceView global
    -> [CheckedOccurrence global]
occurrenceViewChildren = \case
    OccurrenceBound{} -> []
    OccurrenceGlobal{} -> []
    OccurrenceIntrinsic{} -> []
    OccurrenceLogicalSelect{} -> []
    OccurrenceOpaqueInteger{} -> []
    OccurrenceApplication function argument -> [function, argument]
    OccurrenceLambda _binderType body -> [body]
    OccurrenceFalsum -> []
    OccurrenceTruth -> []
    OccurrenceNegation proposition -> [proposition]
    OccurrenceConjunction left right -> [left, right]
    OccurrenceDisjunction left right -> [left, right]
    OccurrenceImplication premise conclusion -> [premise, conclusion]
    OccurrenceEquality _operandType left right -> [left, right]
    OccurrenceUniversal _binderType body -> [body]
    OccurrenceExistential _binderType body -> [body]

data HeadRefs term
    = NonEqualityRefs
    | EqualityRefs !TypeId !term !term
    deriving stock (Show, Eq)

data CollectedOccurrence = CollectedOccurrence
    !(Maybe TermId)
    !(HeadRefs TermId)

collectedTermId :: CollectedOccurrence -> Maybe TermId
collectedTermId (CollectedOccurrence termId _headRefs) = termId

collectedHeadRefs :: CollectedOccurrence -> HeadRefs TermId
collectedHeadRefs (CollectedOccurrence _termId headRefs) = headRefs

data CollectedHeadEvidence
    = CollectedNoHeadEvidence
    | CollectedEqualityEvidence
        !TypeId
        !CollectedOccurrence
        !CollectedOccurrence

collectInitialOccurrence
    :: Eq global
    => Word
    -> CatalogueBuilder global
    -> CheckedOccurrence global
    -> Counted (CatalogueBuilder global, CollectedOccurrence)
collectInitialOccurrence termLimit initialBuilder row = do
    let view = checkedOccurrenceView row
    withExplicitType <-
        case view of
            OccurrenceEquality{} -> pure initialBuilder
            _ ->
                case explicitTypePayload view of
                    Nothing -> pure initialBuilder
                    Just coreType ->
                        fst <$> internBuilderType initialBuilder coreType
    (withChildren, applicationChildren, headEvidence) <-
        case view of
            OccurrenceApplication function argument -> do
                (withFunction, collectedFunction) <-
                    collectInitialOccurrence termLimit withExplicitType function
                (finished, collectedArgument) <-
                    collectInitialOccurrence termLimit withFunction argument
                pure
                    ( finished
                    , Just (collectedFunction, collectedArgument)
                    , CollectedNoHeadEvidence
                    )
            OccurrenceEquality operandType left right -> do
                (withEqualityType, equalityTypeId) <-
                    internBuilderType withExplicitType operandType
                (withLeft, collectedLeft) <-
                    collectInitialOccurrence termLimit withEqualityType left
                (finished, collectedRight) <-
                    collectInitialOccurrence termLimit withLeft right
                pure
                    ( finished
                    , Nothing
                    , CollectedEqualityEvidence
                        equalityTypeId collectedLeft collectedRight
                    )
            _ -> do
                finished <-
                    collectChildren withExplicitType
                        (occurrenceViewChildren view)
                pure (finished, Nothing, CollectedNoHeadEvidence)
    if checkedOccurrenceDependsOnBinderPrefix row
        then pure
            (withChildren, CollectedOccurrence Nothing NonEqualityRefs)
        else do
            rebased <- rebaseGround row >>= \case
                Nothing ->
                    Except.throwE
                        (CatalogueIntegrityFailure
                            "ground initial occurrence did not rebase")
                Just value -> pure value
            (withType, typeId) <-
                internBuilderType withChildren (checkedOccurrenceType row)
            application <-
                case applicationChildren of
                    Just (function, argument) ->
                        case (collectedTermId function, collectedTermId argument) of
                            (Just functionId, Just argumentId) ->
                                pure (Just (functionId, argumentId))
                            _ ->
                                Except.throwE
                                    (CatalogueIntegrityFailure
                                        "closed application has an open child")
                    Nothing -> pure Nothing
            (finished, termId) <-
                internBuilderTerm termLimit withType typeId rebased application
            headRefs <-
                case headEvidence of
                    CollectedNoHeadEvidence -> pure NonEqualityRefs
                    CollectedEqualityEvidence equalityType left right ->
                        case (collectedTermId left, collectedTermId right) of
                            (Just leftId, Just rightId) ->
                                pure
                                    (EqualityRefs
                                        equalityType leftId rightId)
                            _ ->
                                Except.throwE
                                    (CatalogueIntegrityFailure
                                        "initial equality has an open endpoint")
            pure
                ( finished
                , CollectedOccurrence (Just termId) headRefs
                )
  where
    -- Core constructor arity is fixed, but preserving source order directly
    -- also keeps this walker free of a second semantic-row traversal.
    collectChildren builder [] = pure builder
    collectChildren builder (child : rest) = do
        (updated, _collected) <-
            collectInitialOccurrence termLimit builder child
        collectChildren updated rest

data CataloguedRootRefs = CataloguedRootRefs
    !TermId
    !(HeadRefs TermId)
    deriving stock (Show, Eq)

cataloguedRootTermId :: CataloguedRootRefs -> TermId
cataloguedRootTermId (CataloguedRootRefs termId _headRefs) = termId

cataloguedRootHeadRefs :: CataloguedRootRefs -> HeadRefs TermId
cataloguedRootHeadRefs (CataloguedRootRefs _termId headRefs) = headRefs

rootReferences :: CollectedOccurrence -> Counted CataloguedRootRefs
rootReferences collected = do
    rootId <-
        maybe
            (Except.throwE
                (CatalogueIntegrityFailure
                    "initial proposition root was not closed"))
            pure
            (collectedTermId collected)
    pure (CataloguedRootRefs rootId (collectedHeadRefs collected))

freezeBuilder
    :: CatalogueBuilder global
    -> Counted (Catalogue global)
freezeBuilder
        (CatalogueBuilder types terms buckets propositionType) =
    case propositionType of
        Nothing ->
            Except.throwE
                (CatalogueIntegrityFailure
                    "initial catalogue did not establish TyProp")
        Just typeId -> pure (Catalogue types terms buckets typeId)

data CataloguedNodeRefs = CataloguedNodeRefs
    !(Maybe TermId)
    !(HeadRefs TermId)

type CataloguedLogicalView global =
    LogicalView.LogicalView global CataloguedNodeRefs

cataloguedLogicalRootReferences
    :: CataloguedLogicalView global
    -> Maybe CataloguedRootRefs
cataloguedLogicalRootReferences view =
    case LogicalView.logicalViewPayload view of
        CataloguedNodeRefs Nothing _headRefs -> Nothing
        CataloguedNodeRefs (Just termId) headRefs ->
            Just (CataloguedRootRefs termId headRefs)

-- | A catalogued logical view whose root is known to be a closed retained
-- proposition.  Refutation constructs formula rows only through this seam, so
-- later access to the root evidence is total and needs no parallel cache.
data CataloguedFormulaView global = CataloguedFormulaView
    !(CataloguedLogicalView global)
    !CataloguedRootRefs

cataloguedFormulaView
    :: CataloguedLogicalView global
    -> Maybe (CataloguedFormulaView global)
cataloguedFormulaView view =
    CataloguedFormulaView view <$> cataloguedLogicalRootReferences view

cataloguedFormulaLogicalView
    :: CataloguedFormulaView global
    -> CataloguedLogicalView global
cataloguedFormulaLogicalView (CataloguedFormulaView view _references) = view

cataloguedFormulaRootReferences
    :: CataloguedFormulaView global
    -> CataloguedRootRefs
cataloguedFormulaRootReferences
        (CataloguedFormulaView _view references) = references

data InitialCatalogueResult global root = InitialCatalogueResult
    !(Catalogue global)
    -- Each opaque root owner stays attached to its source-aligned semantic
    -- tree throughout collection.  Callers therefore need no post-publication
    -- cardinality pairing pass.
    !(NonEmpty (root, CataloguedLogicalView global))

initialCatalogue :: InitialCatalogueResult global root -> Catalogue global
initialCatalogue (InitialCatalogueResult catalogue _roots) = catalogue

initialRootViews
    :: InitialCatalogueResult global root
    -> NonEmpty (root, CataloguedLogicalView global)
initialRootViews (InitialCatalogueResult _catalogue roots) = roots

-- The builder and completed views stay private until all initial roots have
-- been collected. One advance admits one source-aligned logical view; freezing
-- never publishes a partial catalogue to logical search.
data InitialCatalogueCursor global root = InitialCatalogueCursor
    !(CatalogueBuilder global)
    ![(root, LogicalView.LogicalView global ())]
    !(Seq (root, CataloguedLogicalView global))

data InitialCatalogueStep global root
    = InitialCatalogueMore !(InitialCatalogueCursor global root)
    | InitialCatalogueDone !(InitialCatalogueResult global root)

startInitialCatalogue
    :: NonEmpty (root, LogicalView.LogicalView global ())
    -> InitialCatalogueCursor global root
startInitialCatalogue roots = InitialCatalogueCursor emptyCatalogueBuilder (toList roots) Seq.empty

advanceInitialCatalogue
    :: Eq global
    => GlobalTyping global
    -> Word
    -> Word
    -> [CoreType]
    -> InitialCatalogueCursor global root
    -> (Either CatalogueError (InitialCatalogueStep global root), Word, Word)
advanceInitialCatalogue globalType available termLimit ambient cursor =
    runAdmissionCounted available (advanceInitialCatalogueM globalType termLimit ambient cursor)

collectInitialCatalogue
    :: Eq global
    => GlobalTyping global
    -> Word
    -> Word
    -> [CoreType]
    -> NonEmpty (root, LogicalView.LogicalView global ())
    -> (Either CatalogueError (InitialCatalogueResult global root), Word, Word)
collectInitialCatalogue globalType available termLimit ambient roots =
    runAdmissionCounted available (drain (startInitialCatalogue roots))
  where
    drain cursor = advanceInitialCatalogueM globalType termLimit ambient cursor >>= \case
        InitialCatalogueMore next -> drain next
        InitialCatalogueDone result -> pure result

advanceInitialCatalogueM
    :: Eq global
    => GlobalTyping global
    -> Word
    -> [CoreType]
    -> InitialCatalogueCursor global root
    -> Counted (InitialCatalogueStep global root)
advanceInitialCatalogueM globalType termLimit ambient
        (InitialCatalogueCursor retained pending completed) = case pending of
    [] -> do
        catalogue <- freezeBuilder retained
        case Seq.viewl completed of
            Seq.EmptyL -> Except.throwE (CatalogueIntegrityFailure "initial catalogue has no roots")
            first Seq.:< rest -> pure (InitialCatalogueDone
                (InitialCatalogueResult catalogue (first :| toList rest)))
    root : rest -> do
        (view, updated) <- State.runStateT (collectRoot root) retained
        pure (InitialCatalogueMore (InitialCatalogueCursor updated rest (completed Seq.|> view)))
  where
    collectRoot (root, view) = do
        lift (ensureViewAmbient ambient view)
        catalogued <- LogicalView.traverseLogicalViewPayloadM before after view
        pure (root, catalogued)

    before view = do
        lift charge
        case LogicalView.logicalViewNode view of
            LogicalView.LogicalUniversal binderType _child -> internBinder binderType
            LogicalView.LogicalExistential binderType _child -> internBinder binderType
            _ -> pure ()
        pure view

    internBinder binderType = do
        builder <- State.get
        (updated, _typeId) <- lift (internBuilderType builder binderType)
        State.put $! updated

    after view = do
        builder <- State.get
        (updated, payload) <- lift
            if isLogicalLeaf (LogicalView.logicalViewNode view)
                then do
                    row <- analyseView globalType view
                    (collectedBuilder, collected) <-
                        collectInitialOccurrence termLimit builder row
                    payload <- initialLeafPayload collected
                    pure (collectedBuilder, payload)
                else do
                    (collectedBuilder, rootId) <-
                        collectInitialLogicalRoot globalType termLimit builder view
                    pure (collectedBuilder, CataloguedNodeRefs rootId NonEqualityRefs)
        State.put $! updated
        pure payload

isLogicalLeaf :: LogicalView.LogicalNode global payload -> Bool
isLogicalLeaf = \case
    LogicalView.LogicalTruth -> True
    LogicalView.LogicalFalsum -> True
    LogicalView.LogicalEquality{} -> True
    LogicalView.LogicalNeutral -> True
    LogicalView.LogicalNegation{} -> False
    LogicalView.LogicalConjunction{} -> False
    LogicalView.LogicalDisjunction{} -> False
    LogicalView.LogicalImplication{} -> False
    LogicalView.LogicalUniversal{} -> False
    LogicalView.LogicalExistential{} -> False

ensureViewAmbient
    :: [CoreType]
    -> LogicalView.LogicalView global payload
    -> Counted ()
ensureViewAmbient expected view = do
    equal <-
        runStructural
            (\work ->
                countedCoreTypeListIdentity work expected
                    (Template.binderEnvironmentAmbientContext
                        (Template.compiledTemplateBinderEnvironment
                            (LogicalView.logicalViewResidualTemplate view))))
            absurd
    unless equal
        (Except.throwE
            (CatalogueIntegrityFailure
                "logical view has a different fixed ambient context"))

analyseView
    :: GlobalTyping global
    -> LogicalView.LogicalView global payload
    -> Counted (CheckedOccurrence global)
analyseView globalType view =
    runStructural
        (\work ->
            countedAnalyseScopedOccurrencesUnderBinders
                globalType work
                (LogicalView.logicalViewBinderDepth view)
                (Template.compiledTemplateTerm
                    (LogicalView.logicalViewResidualTemplate view)))
        (integrity "logical-view occurrence analysis failed")

initialLeafPayload
    :: CollectedOccurrence
    -> Counted CataloguedNodeRefs
initialLeafPayload collected =
    case collectedTermId collected of
        Nothing -> pure (CataloguedNodeRefs Nothing NonEqualityRefs)
        Just rootId -> do
            references <- rootReferences collected
            pure
                (CataloguedNodeRefs
                    (Just rootId)
                    (cataloguedRootHeadRefs references))

collectInitialLogicalRoot
    :: Eq global
    => GlobalTyping global
    -> Word
    -> CatalogueBuilder global
    -> LogicalView.LogicalView global payload
    -> Counted (CatalogueBuilder global, Maybe TermId)
collectInitialLogicalRoot globalType termLimit builder view = do
    let checked =
            Template.compiledTemplateTerm
                (LogicalView.logicalViewResidualTemplate view)
    maybeValue <-
        if LogicalView.logicalViewBinderDepth view == 0
            then pure (Just checked)
            else do
                row <- analyseView globalType view
                if checkedOccurrenceDependsOnBinderPrefix row
                    then pure Nothing
                    else rebaseGround row >>= \case
                        Nothing ->
                            Except.throwE
                                (CatalogueIntegrityFailure
                                    "ground logical-view root did not rebase")
                        Just value -> pure (Just value)
    case maybeValue of
        Nothing -> pure (builder, Nothing)
        Just value -> do
            (withType, typeId) <- internBuilderType builder TyProp
            (finished, termId) <-
                internBuilderTerm termLimit withType typeId value Nothing
            pure (finished, Just termId)

newtype RequiredNodeIx = RequiredNodeIx Int
    deriving stock (Show, Eq, Ord)

newtype PendingNodeIx = PendingNodeIx Int
    deriving stock (Show, Eq, Ord)

data TermRef pending
    = ExistingTerm !TermId
    | DeferredTerm !pending
    deriving stock (Show, Eq)

newtype ResolvedTermRef = ResolvedTermRef (TermRef PendingNodeIx)
    deriving stock (Show, Eq)

resolvedTermExistingId :: ResolvedTermRef -> Maybe TermId
resolvedTermExistingId (ResolvedTermRef reference) =
    case reference of
        ExistingTerm termId -> Just termId
        DeferredTerm _pending -> Nothing

data RequiredTerm global = RequiredTerm
    !(ScopedCheckedCore global)
    !(Maybe (TermRef RequiredNodeIx, TermRef RequiredNodeIx))

data PendingTerm global = PendingTerm
    !(ScopedCheckedCore global)
    !(Maybe (TermRef PendingNodeIx, TermRef PendingNodeIx))

data RequiredNodeRefs = RequiredNodeRefs
    !(Maybe (TermRef RequiredNodeIx))
    !(HeadRefs (TermRef RequiredNodeIx))

data DerivedCensus global = DerivedCensus
    !(Seq (RequiredTerm global))
    !(LogicalView.LogicalView global RequiredNodeRefs)

newtype DerivedState global = DerivedState
    (Seq (RequiredTerm global))

type Derive global value =
    State.StateT
        (DerivedState global)
        (ExceptT CatalogueError (State CatalogueWork))
        value

liftCounted :: Counted value -> Derive global value
liftCounted = lift

lookupFrozenType
    :: Catalogue global
    -> CoreType
    -> Derive global TypeId
lookupFrozenType catalogue coreType =
    liftCounted (findCatalogueTypeC catalogue coreType) >>= \case
        -- Substitution can close an initially open partial application whose
        -- result type has no catalogue row. Its absence is a domain boundary,
        -- just like an absent term in an existing typed bucket.
        Nothing ->
            liftCounted (Except.throwE CatalogueOutsideFrozenUniverse)
        Just typeId -> pure typeId

appendRequired
    :: ScopedCheckedCore global
    -> Maybe (TermRef RequiredNodeIx, TermRef RequiredNodeIx)
    -> Derive global (TermRef RequiredNodeIx)
appendRequired value application = do
    DerivedState rows <- State.get
    let index = RequiredNodeIx (Seq.length rows)
    State.put (DerivedState (rows Seq.|> RequiredTerm value application))
    pure (DeferredTerm index)

newtype DerivedCollected = DerivedCollected
    (Maybe (TermRef RequiredNodeIx))

derivedReference :: DerivedCollected -> Maybe (TermRef RequiredNodeIx)
derivedReference (DerivedCollected reference) = reference

censusDerivedOccurrence
    :: Eq global
    => Catalogue global
    -> Bool
    -> CheckedOccurrence global
    -> Derive global DerivedCollected
censusDerivedOccurrence catalogue required row = do
    let view = checkedOccurrenceView row
    _explicitType <-
        traverse (lookupFrozenType catalogue)
            (explicitTypePayload view)
    applicationChildren <-
        case view of
            OccurrenceApplication function argument -> do
                collectedFunction <-
                    censusDerivedOccurrence catalogue required function
                collectedArgument <-
                    censusDerivedOccurrence catalogue required argument
                pure (Just (collectedFunction, collectedArgument))
            _ -> do
                traverse_
                    (censusDerivedOccurrence catalogue False)
                    (occurrenceViewChildren view)
                pure Nothing
    if checkedOccurrenceDependsOnBinderPrefix row
        then do
            when required
                (liftCounted
                    (Except.throwE
                        (CatalogueIntegrityFailure
                            "required derived catalogue occurrence is open")))
            pure (DerivedCollected Nothing)
        else do
            value <-
                liftCounted (rebaseGround row) >>= \case
                    Nothing ->
                        liftCounted
                            (Except.throwE
                                (CatalogueIntegrityFailure
                                    "ground derived occurrence did not rebase"))
                    Just rebased -> pure rebased
            case checkedOccurrenceType row of
                TyProp
                    | required -> do
                        application <-
                            case applicationChildren of
                                Just (function, argument) ->
                                    case (derivedReference function,
                                            derivedReference argument) of
                                        (Just functionRef, Just argumentRef) ->
                                            pure (Just (functionRef, argumentRef))
                                        _ ->
                                            liftCounted
                                                (Except.throwE
                                                (CatalogueIntegrityFailure
                                                    "required proposition application lost a child reference"))
                                Nothing -> pure Nothing
                        reference <- appendRequired value application
                        pure
                            (DerivedCollected (Just reference))
                    | otherwise ->
                        pure (DerivedCollected Nothing)
                nonPropositionType -> do
                    typeId <- lookupFrozenType catalogue nonPropositionType
                    found <-
                        liftCounted
                            (findCatalogueTermC catalogue typeId
                                (scopedCoreTerm value))
                    termId <-
                        maybe
                            (liftCounted
                                (Except.throwE CatalogueOutsideFrozenUniverse))
                            pure
                            found
                    pure
                        (DerivedCollected
                            (if required
                                then Just (ExistingTerm termId)
                                else Nothing))

-- Equality endpoints are part of the derived catalogue dependency closure
-- even though equality is not an application constructor.
censusDerivedEquality
    :: Eq global
    => Catalogue global
    -> CoreType
    -> CheckedOccurrence global
    -> CheckedOccurrence global
    -> CheckedOccurrence global
    -> Derive global (DerivedCollected, HeadRefs (TermRef RequiredNodeIx))
censusDerivedEquality catalogue operandType left right root = do
    typeId <- lookupFrozenType catalogue operandType
    leftCollected <- censusDerivedOccurrence catalogue True left
    rightCollected <- censusDerivedOccurrence catalogue True right
    value <-
        liftCounted (rebaseGround root) >>= \case
            Just rebased -> pure rebased
            Nothing ->
                liftCounted
                    (Except.throwE
                        (CatalogueIntegrityFailure
                            "derived equality root is open"))
    leftReference <- requireReference "left" leftCollected
    rightReference <- requireReference "right" rightCollected
    rootReference <- appendRequired value Nothing
    pure
        ( DerivedCollected (Just rootReference)
        , EqualityRefs typeId leftReference rightReference
        )
  where
    requireReference side collected =
        case derivedReference collected of
            Just reference -> pure reference
            Nothing ->
                liftCounted
                    (Except.throwE
                        (CatalogueIntegrityFailure
                            ("derived equality lost its " <> side
                                <> " endpoint reference")))

derivedLeafPayload
    :: Eq global
    => Catalogue global
    -> CheckedOccurrence global
    -> Derive global RequiredNodeRefs
derivedLeafPayload catalogue root = do
    (collected, headRefs) <-
        case ( checkedOccurrenceDependsOnBinderPrefix root
             , checkedOccurrenceView root
             ) of
            (True, _) ->
                do
                    collected <-
                        censusDerivedOccurrence catalogue False root
                    pure (collected, NonEqualityRefs)
            (False, OccurrenceEquality operandType left right) ->
                censusDerivedEquality catalogue operandType left right root
            (False, _) ->
                do
                    collected <-
                        censusDerivedOccurrence catalogue True root
                    pure (collected, NonEqualityRefs)
    pure (RequiredNodeRefs (derivedReference collected) headRefs)

censusDerivedView
    :: Eq global
    => GlobalTyping global
    -> Catalogue global
    -> LogicalView.LogicalView global ()
    -> Derive global (LogicalView.LogicalView global RequiredNodeRefs)
censusDerivedView globalType catalogue =
    LogicalView.traverseLogicalViewPayloadM before after
  where
    before view = do
        liftCounted charge
        case LogicalView.logicalViewNode view of
            LogicalView.LogicalUniversal binderType _child -> internBinder binderType
            LogicalView.LogicalExistential binderType _child -> internBinder binderType
            _ -> pure ()
        pure view

    internBinder binderType = void (lookupFrozenType catalogue binderType)

    after view
        | isLogicalLeaf (LogicalView.logicalViewNode view) = do
            root <- liftCounted (analyseView globalType view)
            derivedLeafPayload catalogue root
        | otherwise = do
            rootRef <- derivedLogicalRoot globalType catalogue view
            pure (RequiredNodeRefs rootRef NonEqualityRefs)

derivedLogicalRoot
    :: GlobalTyping global
    -> Catalogue global
    -> LogicalView.LogicalView global payload
    -> Derive global (Maybe (TermRef RequiredNodeIx))
derivedLogicalRoot globalType _catalogue view = do
    let checked =
            Template.compiledTemplateTerm
                (LogicalView.logicalViewResidualTemplate view)
    maybeValue <-
        if LogicalView.logicalViewBinderDepth view == 0
            then pure (Just checked)
            else do
                row <- liftCounted (analyseView globalType view)
                if checkedOccurrenceDependsOnBinderPrefix row
                    then pure Nothing
                    else liftCounted (rebaseGround row) >>= \case
                        Nothing ->
                            liftCounted
                                (Except.throwE
                                    (CatalogueIntegrityFailure
                                        "ground derived logical root did not rebase"))
                        Just value -> pure (Just value)
    traverse (`appendRequired` Nothing) maybeValue

derivedCensus
    :: Eq global
    => GlobalTyping global
    -> [CoreType]
    -> Catalogue global
    -> LogicalView.LogicalView global ()
    -> Counted (DerivedCensus global)
derivedCensus globalType ambient catalogue view = do
    ensureViewAmbient ambient view
    (prepared, DerivedState rows) <-
        State.runStateT
            (censusDerivedView globalType catalogue view)
            (DerivedState Seq.empty)
    case LogicalView.logicalViewPayload prepared of
        RequiredNodeRefs Nothing _headRefs ->
            Except.throwE
                (CatalogueIntegrityFailure
                    "derived proposition census lost its closed root")
        RequiredNodeRefs (Just _root) _headRefs ->
            pure (DerivedCensus rows prepared)

data ResolvedNodeRefs = ResolvedNodeRefs
    !(Maybe ResolvedTermRef)
    !(HeadRefs ResolvedTermRef)

data ResolvedDerivedProposition global = ResolvedDerivedProposition
    !Word
    !(Seq (PendingTerm global))
    !(LogicalView.LogicalView global ResolvedNodeRefs)

resolvedDerivedValue
    :: ResolvedDerivedProposition global
    -> ScopedCheckedCore global
resolvedDerivedValue (ResolvedDerivedProposition _base _pending view) =
    Template.compiledTemplateTerm
        (LogicalView.logicalViewResidualTemplate view)

resolvedDerivedRootRef
    :: ResolvedDerivedProposition global
    -> Maybe ResolvedTermRef
resolvedDerivedRootRef (ResolvedDerivedProposition _base _pending view) =
    case LogicalView.logicalViewPayload view of
        ResolvedNodeRefs root _headRefs -> root

resolvedDerivedHeadRefs
    :: ResolvedDerivedProposition global
    -> HeadRefs ResolvedTermRef
resolvedDerivedHeadRefs (ResolvedDerivedProposition _base _pending view) =
    case LogicalView.logicalViewPayload view of
        ResolvedNodeRefs _root headRefs -> headRefs

resolveRequiredRef
    :: Seq (TermRef PendingNodeIx)
    -> TermRef RequiredNodeIx
    -> Counted (TermRef PendingNodeIx)
resolveRequiredRef _resolved (ExistingTerm termId) = pure (ExistingTerm termId)
resolveRequiredRef resolved (DeferredTerm (RequiredNodeIx position)) =
    maybe
        (Except.throwE
            (CatalogueIntegrityFailure
                "required proposition row references a non-older row"))
        pure
        (Seq.lookup position resolved)

findPending
    :: Eq global
    => CanonicalTerm global
    -> Seq (PendingTerm global)
    -> Counted (Maybe PendingNodeIx)
findPending candidate = scan 0 . Seq.viewl
  where
    scan _position Seq.EmptyL = pure Nothing
    scan position (PendingTerm existing _application Seq.:< rest) = do
        charge
        equal <-
            runStructural
                (\work ->
                    countedCanonicalIdentity work
                        (scopedCoreTerm existing) candidate)
                absurd
        if equal
            then pure (Just (PendingNodeIx position))
            else scan (position + 1) (Seq.viewl rest)

resolveCensus
    :: Eq global
    => Catalogue global
    -> DerivedCensus global
    -> Counted
        ( Seq (PendingTerm global)
        , LogicalView.LogicalView global ResolvedNodeRefs
        )
resolveCensus catalogue (DerivedCensus required view) = do
    (resolved, pending) <-
        foldM resolveRow (Seq.empty, Seq.empty) required
    resolvedView <- resolveView resolved view
    pure (pending, resolvedView)
  where
    propositionType = cataloguePropositionTypeId catalogue

    resolveRow (resolved, pending) (RequiredTerm value application) = do
        charge
        resolvedApplication <-
            traverse
                (\(function, argument) ->
                    (,) <$> resolveRequiredRef resolved function
                        <*> resolveRequiredRef resolved argument)
                application
        existing <-
            findCatalogueTermC catalogue propositionType (scopedCoreTerm value)
        case existing of
            Just termId ->
                pure (resolved Seq.|> ExistingTerm termId, pending)
            Nothing ->
                findPending (scopedCoreTerm value) pending >>= \case
                    Just pendingIx ->
                        pure (resolved Seq.|> DeferredTerm pendingIx, pending)
                    Nothing -> do
                        let pendingIx = PendingNodeIx (Seq.length pending)
                        pure
                            ( resolved Seq.|> DeferredTerm pendingIx
                            , pending Seq.|> PendingTerm value resolvedApplication
                            )

    resolveView resolved =
        LogicalView.traverseLogicalViewPayloadM resolvePayload pure
      where
        resolvePayload viewRow = do
            charge
            let RequiredNodeRefs root headRefs = LogicalView.logicalViewPayload viewRow
            resolvedRoot <-
                traverse (fmap ResolvedTermRef . resolveRequiredRef resolved) root
            resolvedHead <-
                fmapHeadRefs ResolvedTermRef
                    <$> traverseHeadRefs (resolveRequiredRef resolved) headRefs
            pure (ResolvedNodeRefs resolvedRoot resolvedHead)

traverseHeadRefs
    :: Applicative f
    => (left -> f right)
    -> HeadRefs left
    -> f (HeadRefs right)
traverseHeadRefs operation = \case
    NonEqualityRefs -> pure NonEqualityRefs
    EqualityRefs typeId left right ->
        EqualityRefs typeId <$> operation left <*> operation right

fmapHeadRefs :: (left -> right) -> HeadRefs left -> HeadRefs right
fmapHeadRefs operation = \case
    NonEqualityRefs -> NonEqualityRefs
    EqualityRefs typeId left right ->
        EqualityRefs typeId (operation left) (operation right)

prepareResolvedDerivedPropositionCounted
    :: Eq global
    => GlobalTyping global
    -> Word
    -> [CoreType]
    -> Catalogue global
    -> LogicalView.LogicalView global ()
    -> (Either CatalogueError (ResolvedDerivedProposition global), Word)
prepareResolvedDerivedPropositionCounted
        globalType available ambient catalogue view =
    runCounted available do
        census <- derivedCensus globalType ambient catalogue view
        (pending, resolvedView) <- resolveCensus catalogue census
        pure
            (ResolvedDerivedProposition
                (catalogueTermCount catalogue) pending resolvedView)

data ResolvedTermView global = ResolvedTermView
    !(ScopedCheckedCore global)
    !(Maybe (ResolvedTermRef, ResolvedTermRef))

resolvedTermViewValue
    :: ResolvedTermView global
    -> ScopedCheckedCore global
resolvedTermViewValue (ResolvedTermView value _application) = value

resolvedTermViewApplication
    :: ResolvedTermView global
    -> Maybe (ResolvedTermRef, ResolvedTermRef)
resolvedTermViewApplication (ResolvedTermView _value application) = application

resolvedTermView
    :: Catalogue global
    -> ResolvedDerivedProposition global
    -> ResolvedTermRef
    -> Maybe (ResolvedTermView global)
resolvedTermView catalogue
        (ResolvedDerivedProposition _base pending _view)
        (ResolvedTermRef reference) =
    case reference of
        ExistingTerm termId -> do
            row <- catalogueTerm catalogue termId
            pure
                (ResolvedTermView
                    (catalogueTermValue row)
                    (fmap
                        (\(function, argument) ->
                            ( ResolvedTermRef (ExistingTerm function)
                            , ResolvedTermRef (ExistingTerm argument)
                            ))
                        (catalogueTermApplication row)))
        DeferredTerm (PendingNodeIx position) -> do
            PendingTerm value application <- Seq.lookup position pending
            pure
                (ResolvedTermView value
                    (fmap
                        (\(function, argument) ->
                            (ResolvedTermRef function, ResolvedTermRef argument))
                        application))

data StagedTermAdmission global = StagedTermAdmission
    !(Catalogue global)
    !(CataloguedLogicalView global)

stagedCatalogue :: StagedTermAdmission global -> Catalogue global
stagedCatalogue (StagedTermAdmission catalogue _view) = catalogue

stagedLogicalView
    :: StagedTermAdmission global
    -> CataloguedLogicalView global
stagedLogicalView (StagedTermAdmission _catalogue view) = view

resolvePendingId
    :: Word
    -> TermRef PendingNodeIx
    -> TermId
resolvePendingId _base (ExistingTerm termId) = termId
resolvePendingId base (DeferredTerm (PendingNodeIx position)) =
    TermId (fromIntegral base + position)

finishDerivedPropositionCounted
    :: Word
    -> Word
    -> Catalogue global
    -> ResolvedDerivedProposition global
    -> (Either CatalogueError (StagedTermAdmission global), Word, Word)
finishDerivedPropositionCounted available termLimit catalogue
        (ResolvedDerivedProposition base pending view) =
    runAdmissionCounted available do
        charge
        unless (catalogueTermCount catalogue == base)
            (Except.throwE
                (CatalogueIntegrityFailure
                    "derived proposition was resolved against a stale catalogue"))
        let delta = fromIntegral (Seq.length pending)
        when (base > termLimit || delta > termLimit - base)
            (Except.throwE CatalogueGroundTermLimitExhausted)
        updated <- foldM appendPending catalogue pending
        finalView <- finalizeView view
        pure
            (StagedTermAdmission updated finalView)
  where
    propositionType = cataloguePropositionTypeId catalogue

    resolveResolved (ResolvedTermRef reference) = resolvePendingId base reference

    finalizeView =
        LogicalView.traverseLogicalViewPayloadM finalizePayload pure
      where
        finalizePayload viewRow = do
            charge
            let ResolvedNodeRefs root headRefs = LogicalView.logicalViewPayload viewRow
            pure
                (CataloguedNodeRefs
                    (resolveResolved <$> root)
                    (fmapHeadRefs resolveResolved headRefs))

    appendPending
            (Catalogue types terms buckets propositionTypeId)
            (PendingTerm value application) = do
        charge
        let termId = TermId (Seq.length terms)
            concreteApplication =
                fmap
                    (\(function, argument) ->
                        ( resolvePendingId base function
                        , resolvePendingId base argument
                        ))
                    application
            row = CatalogueTerm value propositionType concreteApplication
            TypeId position = propositionType
        bucket <-
            maybe
                (Except.throwE
                    (CatalogueIntegrityFailure
                        "cached proposition bucket disappeared"))
                pure
                (Seq.lookup position buckets)
        updatedBucket <- appendHead bucket (scopedCoreTerm value) termId
        recordAdmission
        pure
            (Catalogue types (terms Seq.|> row)
                (Seq.update position updatedBucket buckets)
                propositionTypeId)
