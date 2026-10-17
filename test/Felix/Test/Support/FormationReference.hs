{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Explicit, small-input reference semantics for formation. This module owns
-- no checked evidence or registration authority. Its caller supplies templates
-- from validated associations and opaque leaves from one admitted scope.
module Felix.Test.Support.FormationReference
    ( Reference
    , runReference
    , countedReferenceOperation
    , chargeReferenceWork
    , invalidReferenceInput
    , evaluateFormationReference
    , evaluateFormationReferenceBy
    , OpaqueSeed(..)
    , GroundTerm
    , ReferenceSupport(..)
    , ReferenceFailure(..)
    , enumerateSupport
    , referenceTermSet
    , determinedVariables
    , ruleTemplates
    , PatternVariable(..)
    , PatternAtom
    , GroundAtom
    , WitnessSummary(..)
    , ReferenceRule(..)
    , referenceRuleFromSkeleton
    , referenceRuleTemplates
    , ReferenceFact(..)
    , WitnessId(..)
    , PremiseWitness(..)
    , WitnessRecipe(..)
    , ReferenceWitness(..)
    , ReferenceRejection(..)
    , ReferenceEvaluation(..)
    , evaluateRequests
    , groundPattern
    , normalizeRequest
    , unifyAtoms
    , applyAtom
    , ReferenceAtomHead(..)
    , ReferenceRegistration(..)
    , registrationRule
    , ReferenceSnapshot(..)
    , prepareReferenceSnapshot
    , evaluateFormation
    , evaluateFormationWithDenotation
    , ReferenceWholeRule(..), GroundLeaf
    , evaluateFiniteHorn
    , FiniteFormula(..), FiniteClause(..), evaluateFiniteQueries
    ) where

import Base
import Felix.Checking.Semantic hiding (atomArity)
import Felix.Checking.Core qualified as Core
import Felix.Checking.Identity (ObjectId)
import Control.Monad (foldM, unless)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Data.Word (Word)
import Numeric.Natural (Natural)

-- Opaque means that the reference cannot extract additional mathematical
-- subterms from this leaf. The caller must not encode an out-of-scope variable.
newtype OpaqueSeed = OpaqueSeed Natural
    deriving stock (Show, Eq, Ord)

type GroundTerm = SetTermTemplate OpaqueSeed

data ReferenceSupport = ReferenceSupport
    { referenceSeeds :: !(Set GroundTerm)
    , referenceUniverse :: !(Set GroundTerm)
    , referenceMaximumTermSize :: !Natural
    }
    deriving stock (Show, Eq)

data ReferenceFailure = ReferenceWorkExhausted | ReferenceInvalidInput Text
    deriving stock (Show, Eq)

type Reference value = Except.ExceptT ReferenceFailure (State.State Word) value

-- One account can span adapters, interpreters, support construction and search.
-- Exhaustion never debits beyond the allowance or resets earlier work.
chargeReferenceWork :: Word -> Reference ()
chargeReferenceWork count = do
    remaining <- State.get
    if count > remaining then Except.throwE ReferenceWorkExhausted
        else State.put (remaining - count)

invalidReferenceInput :: Text -> Reference value
invalidReferenceInput = Except.throwE . ReferenceInvalidInput

charge :: Reference ()
charge = chargeReferenceWork 1

-- | Enumerate exactly one template layer over the original seeds. Neither
-- generated instances nor their subterms become assignment candidates. This
-- intentionally uses Cartesian products; production must implement equivalent
-- membership symbolically rather than call this evaluator.
enumerateSupport
    :: Word
    -> Set GroundTerm
    -> Set RuleTermTemplate
    -> (Either ReferenceFailure ReferenceSupport, Word)
enumerateSupport allowance supplied templates = runReference allowance (constructSupport supplied templates)

runReference :: Word -> Reference value -> (Either ReferenceFailure value, Word)
runReference allowance operation =
    let (result, remaining) = State.runState (Except.runExceptT operation) allowance
    in (result, allowance - remaining)

-- Adapt a counted operation which returns its remaining allowance, including
-- on failure (the convention used by counted Core operations).
countedReferenceOperation
    :: (Word -> (Either ReferenceFailure value, Word)) -> Reference value
countedReferenceOperation operation = do
    remaining <- State.get
    let (result, after) = operation remaining
    if after > remaining then invalidReferenceInput "counted operation exceeded its supplied allowance"
        else do
            State.put after
            either Except.throwE pure result

-- Ordered-list operations make deep term comparisons explicit in this small
-- oracle. Rebuild with fromDistinctAscList, which does not compare the terms.
referenceTermSet :: Ord variable => [SetTermTemplate variable] -> Reference (Set (SetTermTemplate variable))
referenceTermSet = foldM (flip insertTerm) Set.empty

compareTerms :: Ord variable => SetTermTemplate variable -> SetTermTemplate variable -> Reference Ordering
compareTerms left right = do
    charge
    case (left, right) of
        (TemplateClosed a,TemplateClosed b) -> compareClosed a b
        (TemplateVariable a, TemplateVariable b) -> pure (compare a b)
        (TemplateProvider a xs, TemplateProvider b ys) -> case compare a b of
            EQ -> compareListsBy compareTerms (toList xs) (toList ys)
            ordering -> pure ordering
        (TemplateOrderedPair a b, TemplateOrderedPair c d) -> compareTerms a c >>= \case
            EQ -> compareTerms b d
            ordering -> pure ordering
        _ -> pure (compare (tag left) (tag right))
  where
    tag :: SetTermTemplate variable -> Int
    tag = \case
        TemplateVariable{} -> 0
        TemplateClosed{} -> 1
        TemplateProvider{} -> 2
        TemplateOrderedPair{} -> 3

-- The independent oracle pays for both descriptions before using their
-- ordinary structural order. It neither calls the production interner nor
-- exposes Core subterms as members of formation support.
compareClosed :: ClosedSetValue -> ClosedSetValue -> Reference Ordering
compareClosed left right = do
    visit (closedSetValueTerm left)
    visit (closedSetValueTerm right)
    pure (compare left right)
  where
    visit value = do
        charge
        case value of
            Core.CApp a b -> visit a >> visit b
            Core.CLam ty body -> coreType ty >> visit body
            Core.CNot body -> visit body
            Core.CAnd a b -> visit a >> visit b
            Core.COr a b -> visit a >> visit b
            Core.CImp a b -> visit a >> visit b
            Core.CEq ty a b -> coreType ty >> visit a >> visit b
            Core.CForall ty body -> coreType ty >> visit body
            Core.CExists ty body -> coreType ty >> visit body
            Core.CLogicalSelect ty -> coreType ty
            _ -> pure ()
    coreType ty = charge >> case ty of
        Core.TyArrow left right -> coreType left >> coreType right
        _ -> pure ()
insertOrderedBy :: (value -> value -> Reference Ordering) -> value -> [value] -> Reference [value]
insertOrderedBy compareValue value entries = do
    charge
    case entries of
        [] -> pure [value]
        existing : rest -> compareValue value existing >>= \case
            LT -> pure (value : entries)
            EQ -> pure (value : rest)
            GT -> (existing :) <$> insertOrderedBy compareValue value rest

insertSetBy :: (value -> value -> Reference Ordering) -> value -> Set value -> Reference (Set value)
insertSetBy compareValue value entries = Set.fromDistinctAscList
    <$> insertOrderedBy compareValue value (Set.toAscList entries)

insertTerm :: Ord variable => SetTermTemplate variable -> Set (SetTermTemplate variable) -> Reference (Set (SetTermTemplate variable))
insertTerm = insertSetBy compareTerms

compareListsBy :: (value -> value -> Reference Ordering) -> [value] -> [value] -> Reference Ordering
compareListsBy compareValue left right = do
    charge
    case (left, right) of
        ([], []) -> pure EQ
        ([], _ : _) -> pure LT
        (_ : _, []) -> pure GT
        (a : rest, b : rest') -> compareValue a b >>= \case
            EQ -> compareListsBy compareValue rest rest'
            ordering -> pure ordering

compareAtoms :: Ord variable => AtomTemplate (SetTermTemplate variable) -> AtomTemplate (SetTermTemplate variable) -> Reference Ordering
compareAtoms left right = do
    charge
    case compare (atomHead left) (atomHead right) of
        EQ -> compareListsBy compareTerms (atomTerms left) (atomTerms right)
        ordering -> pure ordering

compareSummaries :: Ord origin => WitnessSummary origin -> WitnessSummary origin -> Reference Ordering
compareSummaries (WitnessSummary a b c) (WitnessSummary d e f) = do
    charge
    origins <- compareListsBy (\x y -> pure (compare x y)) (Set.toAscList a) (Set.toAscList d)
    case origins of
        EQ -> do
            occurrences <- compareListsBy (\x y -> pure (compare x y)) (Set.toAscList b) (Set.toAscList e)
            case occurrences of
                EQ -> compareListsBy (\x y -> pure (compare x y)) (Set.toAscList c) (Set.toAscList f)
                ordering -> pure ordering
        ordering -> pure ordering

compareAnswerKeys :: Ord origin => (GroundAtom, WitnessSummary origin) -> (GroundAtom, WitnessSummary origin) -> Reference Ordering
compareAnswerKeys (atom, summary) (other, otherSummary) = compareAtoms atom other >>= \case
    EQ -> compareSummaries summary otherSummary
    ordering -> pure ordering

compareRejections :: ReferenceRejection -> ReferenceRejection -> Reference Ordering
compareRejections left right = do
    charge
    case (left, right) of
        (UnanchoredPremise a b term, UnanchoredPremise c d other) -> case compare (a,b) (c,d) of
            EQ -> compareAtoms term other
            ordering -> pure ordering
        (OutsideSupport a term, OutsideSupport b other) -> case compare a b of
            EQ -> compareAtoms term other
            ordering -> pure ordering
        (UndeterminedBinder a b, UndeterminedBinder c d) -> pure (compare (a,b) (c,d))
        _ -> pure (compare (tag left) (tag right))
  where
    tag :: ReferenceRejection -> Int
    tag = \case
        UnanchoredPremise{} -> 0
        OutsideSupport{} -> 1
        UndeterminedBinder{} -> 2

reject :: ReferenceRejection -> ReferenceEvaluation origin -> Reference (ReferenceEvaluation origin)
reject reason state = do
    reasons <- insertSetBy compareRejections reason (referenceRejections state)
    pure state {referenceRejections = reasons}

unionTerms :: Ord variable => [Set (SetTermTemplate variable)] -> Reference (Set (SetTermTemplate variable))
unionTerms = foldM (\known terms -> foldM (flip insertTerm) known (Set.toAscList terms)) Set.empty

memberTerm :: Ord variable => SetTermTemplate variable -> Set (SetTermTemplate variable) -> Reference Bool
memberTerm value = member . Set.toAscList
  where
    member entries = do
        charge
        case entries of
            [] -> pure False
            first : rest -> compareTerms value first >>= \case
                LT -> pure False
                EQ -> pure True
                GT -> member rest

intersectsTerms :: Ord variable => Set (SetTermTemplate variable) -> Set (SetTermTemplate variable) -> Reference Bool
intersectsTerms left right = go (Set.toAscList left)
  where
    go [] = pure False
    go (term : rest) = memberTerm term right >>= \present -> if present then pure True else go rest

subsetTerms :: Ord variable => Set (SetTermTemplate variable) -> Set (SetTermTemplate variable) -> Reference Bool
subsetTerms left right = go (Set.toAscList left)
  where
    go [] = pure True
    go (term : rest) = memberTerm term right >>= \present -> if present then go rest else pure False

constructSupport :: Set GroundTerm -> Set RuleTermTemplate -> Reference ReferenceSupport
constructSupport supplied templates = do
    seeds <- subtermClosure supplied
    approved <- subtermClosure templates
    instances <- foldM (instantiateOver seeds) seeds (Set.toAscList approved)
    universe <- subtermClosure instances
    sizes <- traverse termSize (Set.toAscList universe)
    pure (ReferenceSupport seeds universe (maximum (0 : sizes)))
  where
    instantiateOver seeds accumulated template = do
        variables <- termVariables template
        assignments <- assign (Set.toAscList variables)
        foldM (\terms substitution -> do
            value <- instantiate substitution template
            insertTerm value terms) accumulated assignments
      where
        assign [] = charge >> pure [Map.empty]
        assign (variable : rest) = do
            tails <- assign rest
            concat <$> traverse (\tail' -> traverse (\seed -> do
                charge
                pure (Map.insert variable seed tail')) (Set.toAscList seeds)) tails

    instantiate substitution = \case
        TemplateClosed value -> charge >> pure (TemplateClosed value)
        TemplateVariable variable -> do
            charge
            -- The assignment enumerator binds precisely this template's vars.
            pure (substitution Map.! variable)
        TemplateProvider provider arguments -> do
            charge
            TemplateProvider provider <$> traverse (instantiate substitution) arguments
        TemplateOrderedPair left right -> do
            charge
            TemplateOrderedPair <$> instantiate substitution left <*> instantiate substitution right

subtermClosure :: Ord variable => Set (SetTermTemplate variable) -> Reference (Set (SetTermTemplate variable))
subtermClosure terms = traverse visit (Set.toAscList terms) >>= unionTerms
  where
    visit term = do
        charge
        descendants <- traverse visit (children term)
        unionTerms descendants >>= insertTerm term

children :: SetTermTemplate variable -> [SetTermTemplate variable]
children = \case
    TemplateClosed{} -> []
    TemplateVariable{} -> []
    TemplateProvider _provider arguments -> toList arguments
    TemplateOrderedPair left right -> [left, right]

termVariables :: Ord variable => SetTermTemplate variable -> Reference (Set variable)
termVariables term = do
    charge
    case term of
        TemplateVariable variable -> pure (Set.singleton variable)
        _ -> Set.unions <$> traverse termVariables (children term)

termSize :: SetTermTemplate variable -> Reference Natural
termSize term = do
    charge
    sizes <- traverse termSize (children term)
    pure (1 + sum sizes)

atomTerms :: AtomTemplate term -> [term]
atomTerms = toList

premiseAtoms :: [RulePremiseTree term] -> [AtomTemplate term]
premiseAtoms = concatMap leaves
  where
    leaves (RulePremiseAtom atom) = [atom]
    leaves (RulePremiseUniversal _) = error "atomic reference received a whole premise"
    leaves (RulePremiseResidual _) = error "atomic reference received a whole premise"
    leaves (RulePremiseAnd left right) = leaves left <> leaves right

ruleTemplates :: CheckedNotionRuleSkeleton -> Set RuleTermTemplate
ruleTemplates rule = Set.fromList (concatMap atomTerms
    (checkedNotionRuleConclusion rule : premiseAtoms (checkedNotionRulePremises rule)))

-- | Declarative determination, independent of a physical lookup schedule.
-- A complete anchored row makes all its variables available. Ground paths must
-- connect to a result/earlier-row occurrence; merely sharing a predicate head
-- or a constant elsewhere in the environment does not establish an anchor.
-- Fully determined guards need no literal-row-locality restriction: support
-- admission and their actual proofs are separate obligations for evaluation.
determinedVariables
    :: Word
    -> CheckedNotionRuleSkeleton
    -> (Either ReferenceFailure (Set ViewVariableIx), Word)
determinedVariables allowance rule =
    let (result, remaining) = State.runState (Except.runExceptT construct) allowance
    in (result, allowance - remaining)
  where
    leaves = premiseAtoms (checkedNotionRulePremises rule)
    construct = do
        conclusionTerms <- referenceTermSet (atomTerms (checkedNotionRuleConclusion rule))
        occurrences <- subtermClosure conclusionTerms
        known <- Set.unions <$> traverse termVariables (Set.toAscList conclusionTerms)
        rounds known occurrences
    rounds known occurrences = do
        charge
        additions <- traverse (available known occurrences) leaves
        let (variables, terms) = unzip additions
            nextKnown = known <> Set.unions variables
        nextOccurrences <- unionTerms (occurrences : terms)
        -- The union retains all old occurrences, so equal size proves stability.
        if nextKnown == known && Set.size nextOccurrences == Set.size occurrences
            then pure known
            else rounds nextKnown nextOccurrences
    available known occurrences atom = do
        terms <- referenceTermSet (atomTerms atom) >>= subtermClosure
        anchors <- traverse (\term -> do
            variables <- termVariables term
            present <- memberTerm term occurrences
            pure (present && variables `Set.isSubsetOf` known))
            (Set.toAscList terms)
        variables <- Set.unions <$> traverse termVariables (atomTerms atom)
        if variables `Set.isSubsetOf` known || or anchors
            then pure (variables, terms)
            else pure (Set.empty, Set.empty)

-- The opaque leaves are already admitted in one scope. Holes denote outputs,
-- not candidates to enumerate from the universe. Constructor nodes retain the
-- same first-order meaning and size in ground terms and partial patterns.
data PatternVariable = Pin !OpaqueSeed | Hole !Natural
    deriving stock (Show, Eq, Ord)

type PatternTerm = SetTermTemplate PatternVariable
type PatternAtom = AtomTemplate PatternTerm
type GroundAtom = AtomTemplate GroundTerm
type Substitution = Map Natural PatternTerm

-- Small admitted clauses for the finite Horn oracle. Whole interiors remain
-- opaque; only the surrounding parameter substitution is performed.
data ReferenceWholeRule = ReferenceWholeRule !Natural ![RuleConclusion] !RuleConclusion
    deriving stock (Show, Eq)

type GroundLeaf = NotionLeaf GroundAtom (Core.CanonicalTerm ObjectId)

-- A separate, deliberately exhaustive specification of compositional queries.
-- Maybe introduces a lexical slot: Nothing is the nearest binder, Just keeps
-- an outer value. These descriptions are supplied by the fixture, not obtained
-- by running the production compiler or selector.
data FiniteFormula variable
    = FiniteAtom !(AtomTemplate (SetTermTemplate variable))
    | FiniteTruth
    | FiniteEquality !(SetTermTemplate variable) !(SetTermTemplate variable)
    | FiniteAnd !(FiniteFormula variable) !(FiniteFormula variable)
    | FiniteOr !(FiniteFormula variable) !(FiniteFormula variable)
    | FiniteImplies !(FiniteFormula variable) !(FiniteFormula variable)
    | FiniteIff !(FiniteFormula variable) !(FiniteFormula variable)
    | FiniteExists !(FiniteFormula (Maybe variable))
    | FiniteForall !(FiniteFormula (Maybe variable))
    | FiniteOpaque !Int ![SetTermTemplate variable]
    deriving stock (Show, Eq, Ord, Functor)

data FiniteClause = FiniteClause !Natural ![FiniteFormula ViewVariableIx] !(FiniteFormula ViewVariableIx)

substituteFinite
    :: (variable -> Reference (SetTermTemplate other))
    -> FiniteFormula variable -> Reference (FiniteFormula other)
substituteFinite value formula = charge >> case formula of
    FiniteAtom atom -> FiniteAtom <$> traverse term atom
    FiniteTruth -> pure FiniteTruth
    FiniteEquality a b -> FiniteEquality <$> term a <*> term b
    FiniteAnd a b -> binary FiniteAnd a b
    FiniteOr a b -> binary FiniteOr a b
    FiniteImplies a b -> binary FiniteImplies a b
    FiniteIff a b -> binary FiniteIff a b
    FiniteExists body -> FiniteExists <$> substituteFinite under body
    FiniteForall body -> FiniteForall <$> substituteFinite under body
    FiniteOpaque tag terms -> FiniteOpaque tag <$> traverse term terms
  where
    binary constructor a b = constructor <$> substituteFinite value a <*> substituteFinite value b
    under Nothing = pure (TemplateVariable Nothing)
    under (Just outer) = fmap Just <$> value outer
    term expression = charge >> case expression of
        TemplateVariable slot -> value slot
        TemplateClosed closed -> pure (TemplateClosed closed)
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse term arguments
        TemplateOrderedPair a b -> TemplateOrderedPair <$> term a <*> term b

-- The fixed equality graph compares complete operands only. It never changes
-- an assignment or adds an equation derived by a clause. Truth lookup precedes
-- introduction at every node, including nested and unsupported existentials.
evaluateFiniteQueries
    :: [GroundTerm] -> [(GroundTerm,GroundTerm)] -> [FiniteClause]
    -> [FiniteFormula OpaqueSeed] -> [FiniteFormula OpaqueSeed]
    -> Reference [Bool]
evaluateFiniteQueries domain equalities clauses supplied goals = do
    instances <- concat <$> traverse instantiate clauses
    closure <- saturate instances (Set.fromList supplied)
    traverse (holds closure) goals
  where
    instantiate (FiniteClause arity premises conclusion) = do
        assignments <- assign [ViewVariableIx index | index <- binderIndices arity]
        for assignments \values -> do
            let value slot = charge >> maybe (invalidReferenceInput "a finite clause has an unbound parameter") pure (Map.lookup slot values)
            (,) <$> traverse (substituteFinite value) premises <*> substituteFinite value conclusion
    assign [] = pure [Map.empty]
    assign (slot:rest) = do
        assignments <- assign rest
        for [(value,tail') | value <- domain, tail' <- assignments] \(value,tail') ->
            charge >> pure (Map.insert slot value tail')
    instantiateBinder witness = substituteFinite (\case
        Nothing -> pure witness
        Just outer -> pure (TemplateVariable outer))
    related start target = walk Set.empty [start]
      where
        walk _ [] = pure False
        walk visited (value:rest) = do
            charge
            if value == target then pure True else if Set.member value visited then walk visited rest else do
                neighbors <- concat <$> for equalities (\(a,b) -> charge >> pure
                    ([b | a == value] <> [a | b == value]))
                walk (Set.insert value visited) (neighbors <> rest)
    positive :: FiniteFormula variable -> Bool
    positive = \case
        FiniteAtom{} -> True
        FiniteTruth -> True
        FiniteEquality{} -> True
        FiniteAnd a b -> positive a && positive b
        FiniteOr a b -> positive a && positive b
        FiniteExists body -> positive body
        FiniteImplies{} -> False
        FiniteIff{} -> False
        FiniteForall{} -> False
        FiniteOpaque{} -> False
    holds known formula = do
        charge
        if Set.member formula known then pure True else case formula of
            FiniteTruth -> pure True
            FiniteEquality a b -> related a b
            FiniteAtom atom -> do
                admissible <- and <$> traverse (\value -> charge >> pure (value `elem` domain)) atom
                if not admissible then pure False else anyM (\candidate -> case candidate of
                    FiniteAtom row | fmap (const ()) atom == fmap (const ()) row ->
                        and <$> sequence (zipWith related (toList atom) (toList row))
                    _ -> pure False) (Set.toList known)
            FiniteAnd a b -> (&&) <$> holds known a <*> holds known b
            FiniteOr a b -> holds known a >>= \found -> if found then pure True else holds known b
            FiniteExists body | positive body -> anyM
                (\witness -> instantiateBinder witness body >>= holds known) domain
            FiniteIff a b -> (&&) <$> holds known (FiniteImplies a b) <*> holds known (FiniteImplies b a)
            _ -> pure False
    anyM _ [] = pure False
    anyM predicate (value:rest) = predicate value >>= \found -> if found then pure True else anyM predicate rest
    saturate instances known = do
        projected <- foldM (\current formula -> do
            results <- case formula of
                FiniteAnd a b -> pure [a,b]
                FiniteImplies a b -> holds known a >>= \ready -> pure [b | ready]
                FiniteIff a b -> do
                    left <- holds known a
                    right <- holds known b
                    pure ([b | left] <> [a | right])
                FiniteForall body -> traverse (`instantiateBinder` body) domain
                _ -> pure []
            pure (foldr Set.insert current results)) known (Set.toList known)
        next <- foldM (\current (premises,conclusion) -> do
            ready <- and <$> traverse (holds known) premises
            admissible <- case conclusion of
                FiniteAtom atom -> pure (all (`elem` domain) atom)
                _ -> pure True
            pure (if ready && admissible then Set.insert conclusion current else current)) projected instances
        if next == known then pure next else saturate instances next

-- | The finite Horn semantics, independent of demand scheduling and source
-- matching. Parameters range over the fixed universe; relational operands
-- must also belong to it. Premises ask for exact truth, regardless of whether
-- the evidence carries a usable source view. Returned views retain their
-- structural descriptions even when several descriptions denote one formula.
-- The caller admits clauses and computes B and T before calling this oracle.
evaluateFiniteHorn
    :: [GroundTerm]
    -> (GroundTerm -> Core.CanonicalTerm ObjectId)
    -> (GroundAtom -> Core.CanonicalTerm ObjectId)
    -> [ReferenceWholeRule] -> [(GroundLeaf, Bool)]
    -> Reference (Set (GroundLeaf, Bool))
evaluateFiniteHorn domain denote atomFormula rules supplied = do
    instances <- concat <$> traverse instantiate rules
    rounds instances (Set.fromList supplied)
  where
    formula (AtomicLeaf atom) = atomFormula atom
    formula (WholeLeaf whole) = whole
    instantiate (ReferenceWholeRule arity premises result) = do
        assignments <- assign (binderIndices arity)
        fmap catMaybes $ for assignments \values -> do
            let substitution = Map.fromList [(i, fmap Pin term) | (i, term) <- Map.toList values]
                groundLeaf = \case
                    AtomicLeaf atom -> do
                        grounded <- applyAtom substitution (rulePattern atom) >>= traverseAtomTemplateArguments groundTerm
                        maybe (invalidReferenceInput "finite Horn oracle retained a hole") (pure . AtomicLeaf) (sequenceAtom grounded)
                    WholeLeaf (ResidualTemplate body) -> WholeLeaf <$>
                        Core.instantiateCanonicalPrefixWith charge arity
                            (\depth index -> pure (Core.shiftCanonical depth 0 (denote (values Map.! index)))) 0 body
            body <- traverse groundLeaf premises
            head' <- groundLeaf result
            admitted <- and <$> traverse inDomain (head' : body)
            pure (if admitted then Just (body, head') else Nothing)
    inDomain WholeLeaf{} = pure True
    inDomain (AtomicLeaf atom) = and <$> traverse (\term -> do
        charge
        pure (term `elem` domain)) (atomTerms atom)
    assign [] = charge >> pure [Map.empty]
    assign (index:rest) = do
        tails <- assign rest
        for [(term, tail') | term <- domain, tail' <- tails] \(term, tail') ->
            charge >> pure (Map.insert index term tail')
    rounds instances snapshot = do
        truth <- foldM (\known (leaf,_) -> charge >> pure (Set.insert (formula leaf) known)) Set.empty
            (Set.toList snapshot)
        next <- foldM (\known (premises,result) -> do
            ready <- and <$> traverse (\premise -> charge >> pure (Set.member (formula premise) truth)) premises
            charge
            let capable = case result of AtomicLeaf{} -> True; WholeLeaf{} -> False
            pure (if ready then Set.insert (result,capable) known else known)) snapshot instances
        if next == snapshot then pure next else rounds instances next

-- Origins use the same caller-owned type as production formation. Occurrence
-- ordinals identify exact entries of the immutable request snapshot, including
-- distinct entries for repeated citations. Support is recorded independently:
-- an ordinary witness must not hide one that consumed a required view/equality.
data WitnessSummary origin = WitnessSummary
    { witnessOrigins :: !(Set origin)
    , witnessOccurrences :: !(Set Natural)
    , witnessSupport :: !(Set Natural)
    }
    deriving stock (Show, Eq, Ord)

data ReferenceRule = ReferenceRule
    { referenceRuleArity :: !Natural
    , referenceRulePremises :: ![RulePremiseTree RuleTermTemplate]
    , referenceRuleConclusion :: !(AtomTemplate RuleTermTemplate)
    , referenceRuleSupport :: !(Set Natural)
    }
    deriving stock (Show, Eq)

referenceRuleFromSkeleton :: CheckedNotionRuleSkeleton -> ReferenceRule
referenceRuleFromSkeleton rule = ReferenceRule
    (checkedNotionRuleBinderArity rule)
    (checkedNotionRulePremises rule)
    (checkedNotionRuleConclusion rule) Set.empty

referenceRuleTemplates :: ReferenceRule -> Set RuleTermTemplate
referenceRuleTemplates rule = Set.fromList (concatMap atomTerms
    (referenceRuleConclusion rule : concatMap treeAtoms (referenceRulePremises rule)))

data ReferenceFact origin = ReferenceFact !GroundAtom !(WitnessSummary origin)
    deriving stock (Show, Eq)

newtype WitnessId = WitnessId Natural
    deriving stock (Show, Eq, Ord)

data PremiseWitness
    = PremiseLeaf !WitnessId
    | PremiseConjunction !PremiseWitness !PremiseWitness
    deriving stock (Show, Eq)

data WitnessRecipe
    = ObservedRow !Natural
    | AppliedRule !Natural !(Map ViewVariableIx GroundTerm) ![PremiseWitness]
    | SameDenotation !WitnessId
    deriving stock (Show, Eq)

data ReferenceWitness origin = ReferenceWitness
    { referenceWitnessAtom :: !GroundAtom
    , referenceWitnessSummary :: !(WitnessSummary origin)
    , referenceWitnessRecipe :: !WitnessRecipe
    }
    deriving stock (Show, Eq)

data ReferenceRejection
    = UnanchoredPremise !Natural !Natural !PatternAtom
    | OutsideSupport !(Maybe Natural) !PatternAtom
    | UndeterminedBinder !Natural !Natural
    deriving stock (Show, Eq, Ord)

data ReferenceEvaluation origin = ReferenceEvaluation
    { referenceRequests :: !(Set PatternAtom)
    , referenceAnswers :: !(Map (GroundAtom, WitnessSummary origin) WitnessId)
    , referenceWitnesses :: !(Map WitnessId (ReferenceWitness origin))
    , referenceRejections :: !(Set ReferenceRejection)
    }
    deriving stock (Show, Eq)

groundPattern :: GroundAtom -> PatternAtom
groundPattern = fmap (fmap Pin)

-- | Full-round semantics over a previously frozen support/E0 snapshot. This
-- reference intentionally recomputes joins and scans complete answer rows.
-- Production will subscribe to deltas; it must not define a different answer
-- relation. Definition-head closure and scope admission belong to the snapshot
-- adapter, not this round engine. No reference value is a checked proof.
evaluateRequests
    :: Ord origin
    => Word
    -> ReferenceSupport
    -> Map Natural ReferenceRule
    -> [ReferenceFact origin]
    -> GroundAtom
    -> (Either ReferenceFailure (ReferenceEvaluation origin), Word)
evaluateRequests allowance support rules facts target = runReference allowance do
    seeded <- foldM (\state (ordinal, ReferenceFact atom summary) -> do
        supported <- supportedAtom support atom
        unless supported (Except.throwE (ReferenceInvalidInput "E0 contains an unsupported atom"))
        insertWitness atom summary (ObservedRow ordinal) state) emptyEvaluation (zip [0..] facts)
    evaluateFrom pure (\left right -> pure (left == right)) support rules [] seeded target

emptyEvaluation :: ReferenceEvaluation origin
emptyEvaluation = ReferenceEvaluation Set.empty Map.empty Map.empty Set.empty

evaluateFrom
    :: Ord origin => (GroundTerm -> Reference denotation)
    -> (denotation -> denotation -> Reference Bool)
    -> ReferenceSupport -> Map Natural ReferenceRule
    -> [(Natural, ReferenceRule, AtomTemplate RuleTermTemplate)]
    -> ReferenceEvaluation origin -> GroundAtom -> Reference (ReferenceEvaluation origin)
evaluateFrom denote equal support rules views initialEvidence target = do
    root <- normalizeRequest support (groundPattern target)
    initial <- case root of
        Nothing -> pure initialEvidence {referenceRejections = Set.singleton (OutsideSupport Nothing (groundPattern target))}
        Just query -> pure initialEvidence {referenceRequests = Set.singleton query}
    rounds initial
  where
    rounds snapshot = do
        charge
        searched <- foldM (expandRequest snapshot) snapshot (Set.toAscList (referenceRequests snapshot))
        next <- expandViewRound (WithinSupport support) views snapshot searched
        -- Requests only grow; retained witness IDs also include answer promotions.
        if Map.size (referenceWitnesses next) == Map.size (referenceWitnesses snapshot)
            && Set.size (referenceRequests next) == Set.size (referenceRequests snapshot)
            then pure next
            else rounds next

    expandRequest snapshot accumulated query = do
        exact <- exactAnswers snapshot accumulated query
        foldM (expandRule snapshot query) exact (Map.toAscList rules)

    -- Equality answers only an already-ground request. Its requested source
    -- presentation cannot subsequently supply unknown provider/pair operands.
    exactAnswers snapshot accumulated query = do
        grounded <- traverseAtomTemplateArguments groundTerm query
        case sequenceAtom grounded of
            Nothing -> pure accumulated
            Just targetRow -> foldM (compareRow targetRow) accumulated (Map.toAscList (referenceAnswers snapshot))
      where
        compareRow targetRow state ((row, summary), witness) = do
            charge
            ordering <- compareAtoms row targetRow
            if ordering == EQ || atomHead row /= atomHead targetRow || atomArity row /= atomArity targetRow
                || not (hasSourceShape snapshot witness)
                then pure state
                else do
                    targetMeaning <- traverse meaning (atomTerms targetRow)
                    rowMeaning <- traverse meaning (atomTerms row)
                    same <- equalMeanings targetMeaning rowMeaning
                    if same
                        then insertWitness targetRow summary (SameDenotation witness) state
                        else pure state
        meaning value = charge >> denote value
        equalMeanings [] [] = pure True
        equalMeanings (left : rest) (right : remaining) = do
            same <- equal left right
            if same then equalMeanings rest remaining else pure False
        equalMeanings _ _ = pure False

    expandRule snapshot query accumulated (ordinal, rule) = do
        charge
        -- Fresh query holes cannot alias this rule's de Bruijn variables.
        let query' = fmap (fmap (\case Pin seed -> Pin seed; Hole n -> Hole (n + referenceRuleArity rule))) query
            conclusion = rulePattern (referenceRuleConclusion rule)
        unifyAtoms Map.empty conclusion query' >>= \case
            Nothing -> pure accumulated
            Just substitution -> do
                instantiated <- applyAtom substitution conclusion
                anchors <- atomGroundFragments instantiated
                joinRows snapshot ordinal rule substitution anchors Map.empty
                    (zip [0..] (concatMap treeAtoms (referenceRulePremises rule))) accumulated

    joinRows snapshot ordinal rule substitution anchors witnesses pending accumulated = case pending of
        [] -> completeRule snapshot ordinal rule substitution witnesses accumulated
        _ -> foldM tryRow accumulated pending
      where
        tryRow current (position, premise) = do
            charge
            requested <- applyAtom substitution (rulePattern premise)
            fragments <- atomGroundFragments requested
            ground <- traverseAtomTemplateArguments groundTerm requested
            anchored <- if isJust (sequenceAtom ground) then pure True else intersectsTerms anchors fragments
            if not anchored
                then reject (UnanchoredPremise ordinal position requested) current
                else normalizeRequest support requested >>= \case
                    Nothing -> reject (OutsideSupport (Just ordinal) requested) current
                    Just query -> do
                        charge
                        requests <- insertSetBy compareAtoms query (referenceRequests current)
                        let enrolled = current {referenceRequests = requests}
                        foldM (consumeRow requested) enrolled (Map.toAscList (referenceAnswers snapshot))
          where
            consumeRow requested state ((answer, _summary), witness) = do
                charge
                grounded <- traverseAtomTemplateArguments groundTerm requested
                if isNothing (sequenceAtom grounded) && not (hasSourceShape snapshot witness)
                    then pure state
                    else unifyAtoms substitution requested (groundPattern answer) >>= \case
                        Nothing -> pure state
                        Just extended -> do
                            supplied <- atomGroundFragments (groundPattern answer)
                            combined <- unionTerms [anchors, supplied]
                            joinRows snapshot ordinal rule extended combined
                                (Map.insert position witness witnesses)
                                (List.filter ((/= position) . fst) pending) state

    completeRule snapshot ordinal rule substitution witnesses accumulated = do
        bindings <- traverse (\index -> do
            term <- applyTerm substitution (TemplateVariable (Hole index))
            value <- groundTerm term
            pure (index, value)) (binderIndices (referenceRuleArity rule))
        case [index | (index, Nothing) <- bindings] of
            missing : _ -> reject (UndeterminedBinder ordinal missing) accumulated
            [] -> do
                result <- applyAtom substitution (rulePattern (referenceRuleConclusion rule))
                    >>= traverseAtomTemplateArguments groundTerm
                case sequenceAtom result of
                    Nothing -> Except.throwE (ReferenceInvalidInput "a determined rule retained an output hole")
                    Just atom -> do
                        supported <- supportedAtom support atom
                        if not supported then reject (OutsideSupport (Just ordinal) (groundPattern atom)) accumulated
                        else do
                            let associated = Map.fromList [(ViewVariableIx i, term) | (i, Just term) <- bindings]
                            forest <- rebuildPremises witnesses (referenceRulePremises rule)
                            summary <- foldM (\known witness -> do
                                charge
                                case Map.lookup witness (referenceWitnesses snapshot) of
                                    Nothing -> Except.throwE (ReferenceInvalidInput "a witness prerequisite is not from an earlier round")
                                    Just prior -> combineSummary known (referenceWitnessSummary prior))
                                (WitnessSummary Set.empty (Set.singleton ordinal) (referenceRuleSupport rule))
                                (Map.elems witnesses)
                            insertWitness atom summary (AppliedRule ordinal associated forest) accumulated

data ReferenceAtomHead
    = ReferenceGlobalHead !GlobalNotionHead
    | ReferenceStructureHead !SemanticStructureNotionHead
    | ReferenceMembershipHead
    | ReferenceExactShapeHead !SemanticRecordShapeKey
    | ReferenceNegativeGlobalHead !GlobalNotionHead
    | ReferenceNegativeStructureHead !SemanticStructureNotionHead
    | ReferenceNegativeMembershipHead
    | ReferenceNegativeExactShapeHead !SemanticRecordShapeKey
    deriving stock (Show, Eq, Ord)

atomArity :: AtomTemplate term -> Int
atomArity = length . toList

atomHead :: AtomTemplate term -> ReferenceAtomHead
atomHead = \case
    GlobalAtomTemplate head' _ -> ReferenceGlobalHead head'
    StructureAtomTemplate head' _ -> ReferenceStructureHead head'
    MembershipAtomTemplate{} -> ReferenceMembershipHead
    ExactStructureAtomTemplate shape _ -> ReferenceExactShapeHead shape
    NegativeGlobalAtomTemplate head' _ -> ReferenceNegativeGlobalHead head'
    NegativeStructureAtomTemplate head' _ -> ReferenceNegativeStructureHead head'
    NegativeMembershipAtomTemplate{} -> ReferenceNegativeMembershipHead
    NegativeExactStructureAtomTemplate shape _ -> ReferenceNegativeExactShapeHead shape

-- This distinction comes from the admitted association, not from inspecting
-- a theorem's syntax. Only forward definition views may expand E0. A declared
-- classification with the same implication shape waits for ordinary search.
data ReferenceRegistration
    = ClassificationRule !ReferenceRule
    | DefinitionRule !ReferenceRule
    deriving stock (Show, Eq)

registrationRule :: ReferenceRegistration -> ReferenceRule
registrationRule (ClassificationRule rule) = rule
registrationRule (DefinitionRule rule) = rule

data ReferenceSnapshot origin = ReferenceSnapshot
    { referenceSnapshotHeads :: !(Set ReferenceAtomHead)
    , referenceSnapshotRules :: !(Map Natural ReferenceRule)
    , referenceSnapshotViews :: ![(Natural, ReferenceRule, AtomTemplate RuleTermTemplate)]
    , referenceSnapshotSupport :: !ReferenceSupport
    , referenceSnapshotInitial :: !(ReferenceEvaluation origin)
    }
    deriving stock (Show, Eq)

prepareReferenceSnapshot
    :: Ord origin => Word -> Map Natural ReferenceRegistration
    -> [ReferenceFact origin] -> Set GroundTerm -> GroundAtom
    -> (Either ReferenceFailure (ReferenceSnapshot origin), Word)
prepareReferenceSnapshot allowance registrations facts aliases target =
    runReference allowance (prepareSnapshot registrations facts aliases target)

-- Scope, provider validity, and consumer permission have already been checked
-- by the caller. These operations spend one budget from closure through search;
-- entering a stage does not reset the account or enlarge an existing support.
evaluateFormation
    :: Ord origin => Word -> Map Natural ReferenceRegistration
    -> [ReferenceFact origin] -> Set GroundTerm -> GroundAtom
    -> (Either ReferenceFailure (ReferenceSnapshot origin, ReferenceEvaluation origin), Word)
evaluateFormation = evaluateFormationWithDenotation Right

-- The free-constructor model uses syntax as its denotation; a scoped caller
-- supplies checked Core denotations. This grants exact equality, never an
-- inverse provider match or an equality-based source occurrence.
evaluateFormationWithDenotation
    :: (Ord origin, Eq denotation) => (GroundTerm -> Either Text denotation)
    -> Word -> Map Natural ReferenceRegistration
    -> [ReferenceFact origin] -> Set GroundTerm -> GroundAtom
    -> (Either ReferenceFailure (ReferenceSnapshot origin, ReferenceEvaluation origin), Word)
evaluateFormationWithDenotation denote allowance registrations facts aliases target =
    runReference allowance (evaluateFormationReference (either invalidReferenceInput pure . denote)
        registrations facts aliases target)

-- The interpreter runs in the caller's existing work account. The pure
-- denotation wrapper above is suitable only when its internal work is external
-- to the measurement; scoped qualification should use this operation.
evaluateFormationReference
    :: (Ord origin, Eq denotation) => (GroundTerm -> Reference denotation)
    -> Map Natural ReferenceRegistration
    -> [ReferenceFact origin] -> Set GroundTerm -> GroundAtom
    -> Reference (ReferenceSnapshot origin, ReferenceEvaluation origin)
evaluateFormationReference denote = evaluateFormationReferenceBy denote (\left right -> pure (left == right))

evaluateFormationReferenceBy
    :: Ord origin => (GroundTerm -> Reference denotation)
    -> (denotation -> denotation -> Reference Bool)
    -> Map Natural ReferenceRegistration
    -> [ReferenceFact origin] -> Set GroundTerm -> GroundAtom
    -> Reference (ReferenceSnapshot origin, ReferenceEvaluation origin)
evaluateFormationReferenceBy denote equal registrations facts aliases target = do
    snapshot <- prepareSnapshot registrations facts aliases target
    result <- evaluateFrom denote equal (referenceSnapshotSupport snapshot) (referenceSnapshotRules snapshot)
        (referenceSnapshotViews snapshot) (referenceSnapshotInitial snapshot) target
    pure (snapshot,result)

prepareSnapshot
    :: Ord origin => Map Natural ReferenceRegistration -> [ReferenceFact origin]
    -> Set GroundTerm -> GroundAtom -> Reference (ReferenceSnapshot origin)
prepareSnapshot registrations facts aliases target = do
    heads <- headClosure (Set.singleton (atomHead target))
    selected <- fmap Map.fromList $ fmap catMaybes $ forM (Map.toAscList registrations) \(ordinal, registration) -> do
        charge
        pure (if Set.member (atomHead (referenceRuleConclusion (registrationRule registration))) heads
            then Just (ordinal,registration) else Nothing)
    views <- validateDefinitionViews selected
    direct <- foldM (\state (ordinal, ReferenceFact atom summary) -> do
        charge
        if Set.member (atomHead atom) heads
            then insertWitness atom summary (ObservedRow ordinal) state else pure state)
        emptyEvaluation (zip [0..] facts)
    closed <- foldM (\state (ordinal, registration) -> do
        charge
        let rule = registrationRule registration
        if referenceRuleArity rule == 0 && null (referenceRulePremises rule)
            then publishViewResult InitialSeed ordinal rule Map.empty [] [] state else pure state)
        direct (Map.toAscList selected)
    initial <- expandInitial views closed
    seedSets <- forM (Map.keys (referenceAnswers initial)) \(atom,_summary) -> do
        charge
        referenceTermSet (atomTerms atom)
    templates <- forM (Map.elems selected) \registration -> do
        charge
        let rule = registrationRule registration
        referenceTermSet (concatMap atomTerms (referenceRuleConclusion rule : concatMap treeAtoms (referenceRulePremises rule)))
    targetTerms <- referenceTermSet (atomTerms target)
    supplied <- unionTerms (targetTerms : aliases : seedSets)
    approved <- unionTerms templates
    support <- constructSupport supplied approved
    pure (ReferenceSnapshot heads (registrationRule <$> selected) views support initial)
  where
    headClosure heads = do
        charge
        reached <- foldM (\known registration -> do
            charge
            let rule = registrationRule registration
            if Set.member (atomHead (referenceRuleConclusion rule)) heads
                then foldM (\more premise -> charge >> pure (Set.insert (atomHead premise) more))
                    known (concatMap treeAtoms (referenceRulePremises rule))
                else pure known) heads (Map.elems registrations)
        if reached == heads then pure heads else headClosure reached

-- Every definition view is a single-source forward elimination. Its source
-- determines all binders, and its result cannot introduce a free variable.
-- A head cycle is invalid definition data, unlike a pending classification
-- cycle, which the ordinary request fixed point is allowed to retain.
validateDefinitionViews
    :: Map Natural ReferenceRegistration
    -> Reference [(Natural, ReferenceRule, AtomTemplate RuleTermTemplate)]
validateDefinitionViews registrations = do
    views <- fmap catMaybes $ forM (Map.toAscList registrations) \(ordinal, registration) -> case registration of
        ClassificationRule{} -> charge >> pure Nothing
        DefinitionRule rule -> do
            charge
            source <- case referenceRulePremises rule of
                [RulePremiseAtom source] -> pure source
                _ -> invalid ordinal "a forward definition view must have one atomic source"
            case source of
                MembershipAtomTemplate{} -> invalid ordinal
                    "a forward definition view requires a named predicate or structure source"
                _ -> pure ()
            supplied <- Set.unions <$> traverse termVariables (atomTerms source)
            required <- Set.unions <$> traverse termVariables (atomTerms (referenceRuleConclusion rule))
            complete <- coversBinders (referenceRuleArity rule) supplied
            unless (complete && required `Set.isSubsetOf` supplied)
                (invalid ordinal "a forward definition view has an undetermined binder")
            pure (Just (ordinal,rule,source))
    let edges = Map.fromListWith Set.union
            [(atomHead source, Set.singleton (atomHead (referenceRuleConclusion rule))) | (_ordinal,rule,source) <- views]
        visit active finished head' = do
            charge
            if Set.member head' active then Except.throwE (ReferenceInvalidInput "cyclic forward definition dependencies")
            else if Set.member head' finished then pure finished
            else do
                visited <- foldM (visit (Set.insert head' active)) finished
                    (Set.toAscList (Map.findWithDefault Set.empty head' edges))
                pure (Set.insert head' visited)
    _finished <- foldM (visit Set.empty) Set.empty (Map.keys edges)
    pure views
  where
    invalid ordinal message = Except.throwE (ReferenceInvalidInput
        ("registration " <> fromString (show ordinal) <> ": " <> message))

expandInitial
    :: Ord origin => [(Natural, ReferenceRule, AtomTemplate RuleTermTemplate)]
    -> ReferenceEvaluation origin -> Reference (ReferenceEvaluation origin)
expandInitial views snapshot = do
    charge
    next <- expandViewRound InitialSeed views snapshot snapshot
    if Map.size (referenceAnswers next) == Map.size (referenceAnswers snapshot)
        then pure next else expandInitial views next

data ViewAdmission = InitialSeed | WithinSupport !ReferenceSupport

expandViewRound
    :: Ord origin => ViewAdmission -> [(Natural, ReferenceRule, AtomTemplate RuleTermTemplate)]
    -> ReferenceEvaluation origin -> ReferenceEvaluation origin -> Reference (ReferenceEvaluation origin)
expandViewRound admission views snapshot initial = foldM expandView initial views
  where
    expandView accumulated (ordinal, rule, source) =
        foldM (\state ((atom,summary), witness) -> do
            charge
            if not (hasSourceShape snapshot witness) then pure state else
                unifyAtoms Map.empty (rulePattern source) (groundPattern atom) >>= \case
                    Nothing -> pure state
                    Just substitution -> publishViewResult admission ordinal rule substitution
                        [PremiseLeaf witness] [summary] state)
            accumulated (Map.toAscList (referenceAnswers snapshot))

-- E0 is constructed before U is frozen. Acyclic view dependencies bound its
-- term growth; applying U here would circularly define which seeds enter U.
-- Keep the exact closed/view witness rather than laundering it into a direct
-- input row when the ordinary request engine starts.
publishViewResult
    :: Ord origin => ViewAdmission -> Natural -> ReferenceRule -> Substitution
    -> [PremiseWitness] -> [WitnessSummary origin] -> ReferenceEvaluation origin
    -> Reference (ReferenceEvaluation origin)
publishViewResult admission ordinal rule substitution forest prerequisites state = do
    bindings <- forM (binderIndices (referenceRuleArity rule)) \index -> do
        term <- applyTerm substitution (TemplateVariable (Hole index)) >>= groundTerm
        value <- maybe (Except.throwE (ReferenceInvalidInput "an initial view lost its determined binder")) pure term
        pure (ViewVariableIx index,value)
    conclusion <- applyAtom substitution (rulePattern (referenceRuleConclusion rule))
        >>= traverseAtomTemplateArguments groundTerm
    atom <- maybe (Except.throwE (ReferenceInvalidInput "an initial result retained a free variable")) pure (sequenceAtom conclusion)
    supported <- case admission of
        InitialSeed -> pure True
        WithinSupport support -> supportedAtom support atom
    if not supported then reject (OutsideSupport (Just ordinal) (groundPattern atom)) state
    else do
        summary <- foldM (\known prior -> charge >> combineSummary known prior)
            (WitnessSummary Set.empty (Set.singleton ordinal) (referenceRuleSupport rule)) prerequisites
        insertWitness atom summary (AppliedRule ordinal (Map.fromList bindings) forest) state

-- Inspect the observed variables, never allocate a range from a declared
-- arity. A corrupt large arity must not bypass the reference work limit.
coversBinders :: Natural -> Set ViewVariableIx -> Reference Bool
coversBinders arity variables = do
    charge
    if arity /= fromIntegral (Set.size variables) then pure False
        else consecutive 0 (Set.toAscList variables)
  where
    consecutive _ [] = pure True
    consecutive expected (ViewVariableIx actual : rest) = do
        charge
        if actual == expected then consecutive (expected + 1) rest else pure False

binderIndices :: Natural -> [Natural]
binderIndices 0 = []
binderIndices count = [0 .. count - 1]

combineSummary :: Ord origin => WitnessSummary origin -> WitnessSummary origin -> Reference (WitnessSummary origin)
combineSummary (WitnessSummary origins occurrences support) (WitnessSummary origins' occurrences' support') =
    WitnessSummary <$> combineSet origins origins' <*> combineSet occurrences occurrences' <*> combineSet support support'
  where
    combineSet :: Ord value => Set value -> Set value -> Reference (Set value)
    combineSet known supplied = foldM (\entries value -> charge >> pure (Set.insert value entries)) known (Set.toAscList supplied)

insertWitness
    :: Ord origin => GroundAtom -> WitnessSummary origin -> WitnessRecipe
    -> ReferenceEvaluation origin -> Reference (ReferenceEvaluation origin)
insertWitness atom summary recipe state = do
    charge
    let key = (atom, summary)
        lookupAnswer [] = charge >> pure Nothing
        lookupAnswer ((other, witness) : rest) = do
            charge
            compareAnswerKeys key other >>= \case
                LT -> pure Nothing
                EQ -> pure (Just witness)
                GT -> lookupAnswer rest
    prior <- lookupAnswer (Map.toAscList (referenceAnswers state))
    let retained = maybe False (\witness -> hasSourceShape state witness || not (recipeHasSourceShape recipe)) prior
    if retained then pure state else do
        charge
        let identifier = WitnessId (fromIntegral (Map.size (referenceWitnesses state)))
        answers <- Map.fromDistinctAscList <$> insertOrderedBy
            (\(left, _) (right, _) -> compareAnswerKeys left right)
            (key, identifier) (Map.toAscList (referenceAnswers state))
        pure state
            { referenceAnswers = answers
            , referenceWitnesses = Map.insert identifier (ReferenceWitness atom summary recipe) (referenceWitnesses state)
            }

-- A stronger source-capable answer may replace an exact-only answer with the
-- same logical support. Earlier witness IDs remain valid prerequisites. Each
-- key has at most one such promotion, keeping the fixed point finite.
hasSourceShape :: ReferenceEvaluation origin -> WitnessId -> Bool
hasSourceShape state witness = case Map.lookup witness (referenceWitnesses state) of
    Just proof -> recipeHasSourceShape (referenceWitnessRecipe proof)
    Nothing -> error "reference answer lost its witness"

recipeHasSourceShape :: WitnessRecipe -> Bool
recipeHasSourceShape SameDenotation{} = False
recipeHasSourceShape ObservedRow{} = True
recipeHasSourceShape AppliedRule{} = True

treeAtoms :: RulePremiseTree term -> [AtomTemplate term]
treeAtoms (RulePremiseAtom atom) = [atom]
treeAtoms (RulePremiseUniversal _) = error "atomic reference received a whole premise"
treeAtoms (RulePremiseResidual _) = error "atomic reference received a whole premise"
treeAtoms (RulePremiseAnd left right) = treeAtoms left <> treeAtoms right

rebuildPremises :: Map Natural WitnessId -> [RulePremiseTree term] -> Reference [PremiseWitness]
rebuildPremises witnesses trees = State.evalStateT (traverse rebuild trees) 0
  where
    rebuild tree = do
        State.lift charge
        case tree of
            RulePremiseUniversal _ -> State.lift (invalidReferenceInput "atomic reference received a whole premise")
            RulePremiseResidual _ -> State.lift (invalidReferenceInput "atomic reference received a whole premise")
            RulePremiseAnd left right -> PremiseConjunction <$> rebuild left <*> rebuild right
            RulePremiseAtom _ -> do
                index <- State.get
                State.put (index + 1)
                case Map.lookup index witnesses of
                    Nothing -> State.lift (Except.throwE (ReferenceInvalidInput "an applied rule lost a premise witness"))
                    Just witness -> pure (PremiseLeaf witness)

rulePattern :: AtomTemplate RuleTermTemplate -> PatternAtom
rulePattern = fmap (fmap (\(ViewVariableIx index) -> Hole index))

sequenceAtom :: AtomTemplate (Maybe term) -> Maybe (AtomTemplate term)
sequenceAtom = traverseAtomTemplateArguments id

groundTerm :: PatternTerm -> Reference (Maybe GroundTerm)
groundTerm term = do
    charge
    case term of
        TemplateClosed value -> pure (Just (TemplateClosed value))
        TemplateVariable (Pin seed) -> pure (Just (TemplateVariable seed))
        TemplateVariable Hole{} -> pure Nothing
        TemplateProvider provider arguments ->
            fmap (TemplateProvider provider) . sequence <$> traverse groundTerm arguments
        TemplateOrderedPair left right -> liftA2 TemplateOrderedPair <$> groundTerm left <*> groundTerm right

atomGroundFragments :: PatternAtom -> Reference (Set GroundTerm)
atomGroundFragments atom = traverse fragments (atomTerms atom) >>= unionTerms
  where
    fragments term = do
        value <- groundTerm term
        case value of
            Just ground -> subtermClosure (Set.singleton ground)
            Nothing -> traverse fragments (children term) >>= unionTerms

supportedAtom :: ReferenceSupport -> GroundAtom -> Reference Bool
supportedAtom support atom = and <$> traverse (\term -> memberTerm term (referenceUniverse support)) (atomTerms atom)

-- Every hole needs at least one ground node. With fixed heads, arities, pins,
-- and this support-derived size bound, alpha-normalization makes the possible
-- request vocabulary finite. No depth knob or growing filter history is used.
normalizeRequest :: ReferenceSupport -> PatternAtom -> Reference (Maybe PatternAtom)
normalizeRequest support atom = do
    sizes <- traverse termSize (atomTerms atom)
    fragments <- atomGroundFragments atom
    if any (> referenceMaximumTermSize support) sizes then pure Nothing else do
        admitted <- subsetTerms fragments (referenceUniverse support)
        if not admitted then pure Nothing
            else Just <$> State.evalStateT
                (traverseAtomTemplateArguments (traverseSetTermTemplateVariables rename) atom) (Map.empty, 0)
  where
    rename (Pin seed) = State.lift charge >> pure (Pin seed)
    rename (Hole index) = do
        State.lift charge
        (known, next) <- State.get
        case Map.lookup index known of
            Just canonical -> pure (Hole canonical)
            Nothing -> do
                State.put (Map.insert index next known, next + 1)
                pure (Hole next)

applyAtom :: Substitution -> PatternAtom -> Reference PatternAtom
applyAtom substitution = traverseAtomTemplateArguments (applyTerm substitution)

applyTerm :: Substitution -> PatternTerm -> Reference PatternTerm
applyTerm substitution term = do
    charge
    case term of
        TemplateClosed{} -> pure term
        TemplateVariable (Hole index) -> case Map.lookup index substitution of
            Nothing -> pure term
            Just value -> applyTerm substitution value
        TemplateVariable Pin{} -> pure term
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse (applyTerm substitution) arguments
        TemplateOrderedPair left right -> TemplateOrderedPair <$> applyTerm substitution left <*> applyTerm substitution right

-- Ordinary first-order unification propagates query constraints into producer
-- premises. An occurs check rejects recursive unknown expressions; complete
-- answer rows are the only operation that turns an unknown into evidence.
unifyAtoms :: Substitution -> PatternAtom -> PatternAtom -> Reference (Maybe Substitution)
unifyAtoms substitution left right = do
    charge
    case (left, right) of
        (NegativeAtomTemplate a, NegativeAtomTemplate b) -> unifyAtoms substitution a b
        (GlobalAtomTemplate head' arguments, GlobalAtomTemplate other actual)
            | head' == other -> argumentsMatch arguments actual
        (StructureAtomTemplate head' arguments, StructureAtomTemplate other actual)
            | head' == other -> argumentsMatch arguments actual
        (MembershipAtomTemplate element set, MembershipAtomTemplate other domain) ->
            unifyTerms substitution [(element, other), (set, domain)]
        _ -> pure Nothing
  where
    argumentsMatch arguments actual
        | Vector.length arguments == Vector.length actual = unifyTerms substitution (toList (Vector.zip arguments actual))
        | otherwise = pure Nothing

unifyTerms :: Substitution -> [(PatternTerm, PatternTerm)] -> Reference (Maybe Substitution)
unifyTerms substitution [] = pure (Just substitution)
unifyTerms substitution ((left, right) : rest) = do
    charge
    a <- applyTerm substitution left
    b <- applyTerm substitution right
    case (a, b) of
        (TemplateVariable (Hole index), _) -> bind index b
        (_, TemplateVariable (Hole index)) -> bind index a
        (TemplateVariable (Pin seed), TemplateVariable (Pin other))
            | seed == other -> continue []
        (TemplateProvider provider arguments, TemplateProvider other actual)
            | provider == other, Vector.length arguments == Vector.length actual -> continue (toList (Vector.zip arguments actual))
        (TemplateOrderedPair first second, TemplateOrderedPair otherFirst otherSecond) -> continue [(first, otherFirst), (second, otherSecond)]
        (TemplateClosed left,TemplateClosed right) -> compareClosed left right >>= \same ->
            if same == EQ then continue [] else pure Nothing
        _ -> pure Nothing
  where
    continue added = unifyTerms substitution (added <> rest)
    bind index term
        | term == TemplateVariable (Hole index) = continue []
        | otherwise = do
            variables <- termVariables term
            if Set.member (Hole index) variables then pure Nothing
                else unifyTerms (Map.insert index term substitution) rest
