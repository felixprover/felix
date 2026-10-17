{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Admission and structural identities for one formation request domain.
module Felix.Checking.Notion.Request
    ( RequestId
    , RequestTable
    , emptyRequestTable
    , internRequest, internConstrainedRequest, requestConstraints
    , WholeRequest(WholeRequest), wholeRequestFormula, wholeRequestUniversal, wholeRequestAtomicOrigin
    , atomicTruthRequest
    , evidenceOnlyRequest, wholeRequestIntroducible
    , internWholeRequest
    , lookupRequest
    , requestSupportsTerm
    , requestSupportsTermWith, internConstrainedRequestWith
    ) where

import Base
import Felix.Checking.Semantic
import Felix.Checking.Notion.Pattern
import Felix.Checking.Notion.Rule (AtomSignature)
import Felix.Checking.Notion.Support
import Felix.Checking.Notion.TermIndex qualified as Terms
import Felix.Checking.Notion.FormulaIndex (FormulaId)
import Felix.Checking.Notion.SuppliedUniversal (DescribedAtom)
import Felix.Checking.Notion.SourceEvidence (UniversalBody(..), UniversalOperand, AtomTree(..))
import Control.Monad.State.Strict qualified as State
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)

newtype RequestId = RequestId Int
    deriving (Show, Eq, Ord)

-- Formula identity is shared by exact and supplied-universal requests. The
-- matching description is nevertheless part of request identity: a previous
-- exact miss must not suppress a different supplied adapter attempt.
data WholeRequest variable = DescribedWholeRequest
    { wholeRequestFormula :: !FormulaId
    , wholeRequestUniversal :: !(Maybe (UniversalBody (DescribedAtom variable)))
    , wholeRequestAtomicOrigin :: !(Maybe AtomSignature)
    , wholeRequestIntroducible :: !Bool
    }

pattern WholeRequest :: FormulaId -> Maybe (UniversalBody (DescribedAtom variable)) -> WholeRequest variable
pattern WholeRequest formula body <- DescribedWholeRequest formula body _ _ where
    WholeRequest formula body = DescribedWholeRequest formula body Nothing True
{-# COMPLETE WholeRequest #-}

-- The originating demand opens its own head. Other heads with the same checked
-- formula remain eligible; a source spelling cannot restrict exact truth.
atomicTruthRequest :: AtomSignature -> FormulaId -> WholeRequest variable
atomicTruthRequest signature formula = DescribedWholeRequest formula Nothing (Just signature) True

-- A generated projection consumes an established G. It may discover ordinary
-- clause producers, but does not launch an introduction merely to eliminate it
-- again. Independently requested introductions publish to the same truth key.
evidenceOnlyRequest :: WholeRequest variable -> WholeRequest variable
evidenceOnlyRequest request = request {wholeRequestIntroducible = False}

-- The support domain and all IDs belong to this table's request-local lifetime.
-- Retaining canonical syntax supports expansion/replay without decoding the
-- intern key; scheduler comparisons see only RequestId.
data RequestTable variable = RequestTable
    { requestSupport :: !(SymbolicSupport variable)
    , requestTerms :: !(Terms.Nodes (PatternVariable variable))
    , requestIds :: !(Map (AtomTemplate Int, [(Int,variable)]) RequestId)
    , wholeRequestTerms :: !(Terms.Nodes (UniversalOperand variable))
    , wholeRequestIds :: !(Map (FormulaId, Maybe (UniversalBody (Maybe (AtomTemplate Int))), Maybe AtomSignature, Bool) RequestId)
    , exactConstraints :: !(Map RequestId (Map Int variable))
    , requestPatterns :: !(IntMap.IntMap (NotionLeaf (CanonicalPattern variable) (WholeRequest variable)))
    }

emptyRequestTable :: SymbolicSupport variable -> RequestTable variable
emptyRequestTable support = RequestTable support Terms.emptyNodes Map.empty Terms.emptyNodes Map.empty Map.empty IntMap.empty

requestSupportsTerm
    :: (Monad m, Ord variable) => (Natural -> m ()) -> SetTermTemplate variable
    -> RequestTable variable -> m (Bool,RequestTable variable)
requestSupportsTerm = requestSupportsTermWith Nothing

requestSupportsTermWith
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable)
    -> (Natural -> m ()) -> SetTermTemplate variable -> RequestTable variable -> m (Bool,RequestTable variable)
requestSupportsTermWith interpreter charge value table = do
    (admitted,support) <- symbolicSupportContainsWith interpreter charge value (requestSupport table)
    pure (admitted,table {requestSupport = support})

lookupRequest :: RequestId -> RequestTable variable -> Maybe (NotionLeaf (CanonicalPattern variable) (WholeRequest variable))
lookupRequest (RequestId identifier) table = IntMap.lookup identifier (requestPatterns table)

-- | Normalize against this table's own frozen support before allocating a key.
-- Ground pins, constructor heads, arities, and repeated output constraints all
-- remain in the shallow key. Alpha-equivalent requests share an ID. Neither a
-- support rejection nor budget exhaustion returns a partially updated table.
internRequest
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> AtomTemplate (SetTermTemplate (PatternVariable variable)) -> RequestTable variable
    -> m (Either PatternRejection (RequestId, RequestTable variable))
internRequest charge requested = internConstrainedRequest charge requested Map.empty

requestConstraints :: Monad m => (Natural -> m ()) -> RequestId -> RequestTable variable -> m (Map Int variable)
requestConstraints charge identifier table = do
    charge (Terms.indexWork (Map.size (exactConstraints table)) 1)
    pure (Map.findWithDefault Map.empty identifier (exactConstraints table))

internConstrainedRequest
    :: (Monad m, Ord variable) => (Natural -> m ())
    -> AtomTemplate (SetTermTemplate (PatternVariable variable)) -> Map Int variable -> RequestTable variable
    -> m (Either PatternRejection (RequestId, RequestTable variable))
internConstrainedRequest = internConstrainedRequestWith Nothing

internConstrainedRequestWith
    :: (Monad m, Ord variable) => Maybe (OpaqueInterpreter m variable) -> (Natural -> m ())
    -> AtomTemplate (SetTermTemplate (PatternVariable variable)) -> Map Int variable -> RequestTable variable
    -> m (Either PatternRejection (RequestId, RequestTable variable))
internConstrainedRequestWith interpreter charge requested constraints table = do
    admitted <- normalizeFormationPatternWith interpreter charge (requestSupport table) requested
    case admitted of
        Left failure -> pure (Left failure)
        Right (canonical, support) -> do
            (shapeKey, terms) <- State.runStateT
                (traverseAtomTemplateArguments (\term -> State.StateT (Terms.intern charge term))
                    (canonicalPatternAtom canonical)) (requestTerms table)
            let key = (shapeKey,Map.toAscList constraints)
                arity = atomArity shapeKey
            charge (2 * Terms.indexWork (Map.size (requestIds table)) (1 + fromIntegral arity + 2 * fromIntegral (Map.size constraints)))
            let updated = table {requestSupport = support, requestTerms = terms}
            case Map.lookup key (requestIds table) of
                Just identifier -> pure (Right (identifier, updated))
                Nothing -> do
                    let ordinal = IntMap.size (requestPatterns table)
                        identifier = RequestId ordinal
                    pure (Right (identifier, updated
                        { requestIds = Map.insert key identifier (requestIds table)
                        , exactConstraints = if Map.null constraints then exactConstraints table else Map.insert identifier constraints (exactConstraints table)
                        , requestPatterns = IntMap.insert ordinal (AtomicLeaf canonical) (requestPatterns table) }))

internWholeRequest
    :: (Monad m, Ord variable) => (Natural -> m ()) -> WholeRequest variable
    -> RequestTable variable -> m (RequestId, RequestTable variable)
internWholeRequest charge requested table = do
    (mode, terms) <- State.runStateT (traverse body
        (wholeRequestUniversal requested)) (wholeRequestTerms table)
    let key = (wholeRequestFormula requested, mode, wholeRequestAtomicOrigin requested, wholeRequestIntroducible requested)
        known = wholeRequestIds table
        updated = table {wholeRequestTerms = terms}
    charge (2 * Terms.indexWork (Map.size known) (2 + maybe 0 bodyWidth mode))
    case Map.lookup key known of
        Just identifier -> pure (identifier, updated)
        Nothing -> do
            let ordinal = IntMap.size (requestPatterns table)
                identifier = RequestId ordinal
            pure (identifier, updated
                { wholeRequestIds = Map.insert key identifier known
                , requestPatterns = IntMap.insert ordinal (WholeLeaf requested) (requestPatterns table) })
  where
    body expression = State.lift (charge 1) >> case expression of
        UniversalBind nested -> UniversalBind <$> body nested
        UniversalRequire guard nested -> UniversalRequire <$> atoms guard <*> body nested
        UniversalReturn result -> UniversalReturn <$> atoms result
    atoms expression = State.lift (charge 1) >> case expression of
        AtomLeaf (template, _) -> AtomLeaf <$> traverse (traverse (\term -> State.StateT (Terms.intern charge term))) template
        AtomAnd left right -> AtomAnd <$> atoms left <*> atoms right
    bodyWidth = \case
        UniversalBind nested -> 1 + bodyWidth nested
        UniversalRequire guard nested -> 1 + atomsWidth guard + bodyWidth nested
        UniversalReturn result -> 1 + atomsWidth result
    atomsWidth = \case
        AtomLeaf template -> 1 + maybe 0 (fromIntegral . length . toList) template
        AtomAnd left right -> 1 + atomsWidth left + atomsWidth right
