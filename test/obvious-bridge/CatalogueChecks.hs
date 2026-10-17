module CatalogueChecks (tests) where

import Base hiding (Empty)
import Data.List (permutations)
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping, emptyGlobalTyping)
import Felix.Checking.Obvious.LogicalView qualified as Logical
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template
import Felix.Test.Support.GlobalTyping
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "Catalogue discrimination"
    [ testCase "preserves first exact matches across admission orders and collisions" admissionOrders
    , testCase "streams exact-type inventories in original admission order under counted work" typeInventories
    , testCase "keeps globals and same-head syntax subject to exact comparison" collisions
    , testCase "publishes derived rows and their index together" stagedAdmission
    ]

right :: Show failure => Either failure value -> IO value
right = either (fail . show) pure

prepare :: Eq global => GlobalTyping global -> CanonicalTerm global -> IO (Logical.LogicalView global ())
prepare typing term = do
    checked <- right (checkScopedCanonicalCore typing [] term)
    template <- right (Template.retainCheckedPropositionTemplate checked)
    right =<< Logical.prepareCompiledLogicalViewCounted (const (pure Nothing)) (pure ()) template

makeCatalogue :: Eq global => GlobalTyping global -> [CanonicalTerm global] -> IO (Search.Catalogue global)
makeCatalogue typing terms = do
    roots <- forM terms \term -> do
        checked <- right (checkScopedCanonicalCore typing [] term)
        view <- prepare typing (CEq (scopedCoreType checked) term term)
        pure ((), view)
    nonempty <- case roots of
        first : rest -> pure (first :| rest)
        [] -> fail "empty fixture"
    let (result, _, _) = Search.collectInitialCatalogue typing maxBound maxBound [] nonempty
    Search.initialCatalogue <$> right result

-- The reference scans the authoritative admission-order rows, independently of
-- their index. Every query is also checked at its exact and one-short budget.
checkLookup :: Eq global => Search.Catalogue global -> Search.TypeId -> CanonicalTerm global -> Assertion
checkLookup catalogue typeId candidate = do
    let rows = [(Search.TermId position, row)
            | position <- [0 .. fromIntegral (Search.catalogueTermCount catalogue) - 1]
            , Just row <- [Search.catalogueTerm catalogue (Search.TermId position)]]
        expected = fst <$> find (\(_, row) -> Search.catalogueTermTypeId row == typeId
            && scopedCoreTerm (Search.catalogueTermValue row) == candidate) rows
        query budget = Search.findCatalogueTermCounted budget catalogue typeId candidate
        (actual, remaining) = query maxBound
        consumed = maxBound - remaining
    assertEqual "first admitted exact match" (Right expected) actual
    assertEqual "exact budget" (Right expected, 0) (query consumed)
    assertBool "head lookup consumes work even for an empty bucket" (consumed > 0)
    assertEqual "one-short is exhaustion, not absence"
        (Left Search.CatalogueWorkExhausted, 0) (query (consumed - 1))

checkRows :: Eq global => Search.Catalogue global -> Assertion
checkRows catalogue = forM_ [0 .. fromIntegral (Search.catalogueTermCount catalogue) - 1] \position -> do
    row <- maybe (fail "missing row") pure (Search.catalogueTerm catalogue (Search.TermId position))
    checkLookup catalogue (Search.catalogueTermTypeId row) (scopedCoreTerm (Search.catalogueTermValue row))

admissionOrders :: Assertion
admissionOrders = forM_ (permutations terms) \ordered -> do
    catalogue <- makeCatalogue emptyGlobalTyping (ordered <> reverse ordered)
    checkRows catalogue
    typeId <- right (fst (Search.findCatalogueTypeCounted maxBound catalogue TySet))
        >>= maybe (fail "missing Set") pure
    forM_ [COpaqueInteger 99, CApp (CIntrinsic PowerSet) (COpaqueInteger 99), CFalsum] $
        checkLookup catalogue typeId
  where
    terms :: [CanonicalTerm Void]
    terms = [COpaqueInteger 1, COpaqueInteger 2,
        CApp (CIntrinsic PowerSet) (COpaqueInteger 1), CIntrinsic Empty]

typeInventories :: Assertion
typeInventories = do
    forM_ (permutations terms) \ordered -> do
        catalogue <- makeCatalogue emptyGlobalTyping (ordered <> reverse ordered)
        forM_ [TySet, TyProp, TyArrow TySet TySet] \coreType -> do
            typeId <- right (fst (Search.findCatalogueTypeCounted maxBound catalogue coreType))
                >>= maybe (fail "missing inventory type") pure
            let expected = [Search.TermId position
                    | position <- [0 .. fromIntegral (Search.catalogueTermCount catalogue) - 1]
                    , Just row <- [Search.catalogueTerm catalogue (Search.TermId position)]
                    , Search.catalogueTermTypeId row == typeId]
                start work = Search.catalogueTypeTermsCounted work catalogue typeId
                (started, remaining) = start maxBound
                used = maxBound - remaining
            cursor <- right started
            assertBool "inventory initialization charges its bounded-head scan" (used > 0)
            assertEqual "one-short initialization is exhaustion"
                (Left Search.CatalogueWorkExhausted, 0)
                (let (result, left) = start (used - 1) in (() <$ result, left))
            let (exact, exactRemaining) = start used
            assertEqual "exact initialization work" 0 exactRemaining
            exactCursor <- right exact
            assertEqual "merged heads retain complete admission order" expected =<< drainInventory cursor
            assertEqual "exact initialization retains the same inventory" expected =<< drainInventory exactCursor
        case fst (Search.catalogueTypeTermsCounted maxBound catalogue (Search.TypeId maxBound)) of
            Left Search.CatalogueIntegrityFailure{} -> pure ()
            _ -> assertFailure "unknown inventory type lost integrity failure"
  where
    terms :: [CanonicalTerm Void]
    terms = [CApp (CIntrinsic PowerSet) (COpaqueInteger 2), CIntrinsic Empty,
        COpaqueInteger 1, CApp (CIntrinsic PowerSet) (CIntrinsic Empty)]

drainInventory :: Search.CatalogueTypeTerms -> IO [Search.TermId]
drainInventory cursor = do
    let step work = Search.nextCatalogueTypeTermCounted work cursor
        (advanced, remaining) = step maxBound
        used = maxBound - remaining
        observe (result, left) = (fmap (fmap fst) result, left)
    assertBool "each inventory observation consumes work, including end-of-stream" (used > 0)
    assertEqual "exact inventory step" (fmap (fmap fst) advanced, 0) (observe (step used))
    assertEqual "one-short inventory step is exhaustion, not end-of-stream"
        (Left Search.CatalogueWorkExhausted, 0) (observe (step (used - 1)))
    right advanced >>= \case
        Nothing -> pure []
        Just (termId, next) -> (termId :) <$> drainInventory next

collisions :: Assertion
collisions = do
    let fixture = globalTypingFixture (replicate 3 TySet)
        typing = fixtureGlobalTyping fixture
        globals = fixtureObjectIds fixture
        terms = fmap CGlobal (take 2 globals) <>
            [CFalsum, CTruth, CNot CTruth, CAnd CTruth CFalsum, COr CTruth CFalsum,
             CImp CTruth CFalsum, CForall TySet CTruth, CExists TySet CFalsum,
             CLam TySet (CBound 0), CIntrinsic PowerSet,
             CApp (CIntrinsic PowerSet) (CIntrinsic Empty)]
    catalogue <- makeCatalogue typing (terms <> reverse terms)
    checkRows catalogue
    typeId <- right (fst (Search.findCatalogueTypeCounted maxBound catalogue TySet))
        >>= maybe (fail "missing Set") pure
    forM_ (drop 2 globals) (checkLookup catalogue typeId . CGlobal)
    case fst (Search.findCatalogueTermCounted maxBound catalogue (Search.TypeId maxBound) CTruth) of
        Left Search.CatalogueIntegrityFailure{} -> pure ()
        other -> assertFailure ("unknown type lost integrity failure: " <> show other)

stagedAdmission :: Assertion
stagedAdmission = do
    catalogue <- makeCatalogue emptyGlobalTyping [CTruth, CFalsum :: CanonicalTerm Void]
    let term = CAnd CTruth CFalsum
        typeId = Search.cataloguePropositionTypeId catalogue
    originalInventory <- right (fst (Search.catalogueTypeTermsCounted maxBound catalogue typeId))
    view <- prepare emptyGlobalTyping term
    resolved <- right (fst (Search.prepareResolvedDerivedPropositionCounted emptyGlobalTyping maxBound [] catalogue view))
    let (result, _, admitted) = Search.finishDerivedPropositionCounted maxBound maxBound catalogue resolved
    staged <- right result
    let updated = Search.stagedCatalogue staged
    assertEqual "one derived row" 1 admitted
    assertEqual "original remains frozen" (Right Nothing)
        (fst (Search.findCatalogueTermCounted maxBound catalogue typeId term))
    assertEqual "published row" (Right (Just (Search.TermId (fromIntegral (Search.catalogueTermCount catalogue)))))
        (fst (Search.findCatalogueTermCounted maxBound updated typeId term))
    originalTerms <- drainInventory originalInventory
    updatedInventory <- right (fst (Search.catalogueTypeTermsCounted maxBound updated typeId))
    assertEqual "late proposition publication does not extend the captured inventory"
        (originalTerms <> [Search.TermId (fromIntegral (Search.catalogueTermCount catalogue))])
        =<< drainInventory updatedInventory
    checkRows updated
    let (limited, _, limitedAdmissions) = Search.finishDerivedPropositionCounted maxBound
            (Search.catalogueTermCount catalogue) catalogue resolved
    case limited of
        Left Search.CatalogueGroundTermLimitExhausted -> pure ()
        _ -> assertFailure "term cap did not reject staged publication"
    assertEqual "rejected publication admits nothing" 0 limitedAdmissions
