{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Structural recursion through the public laws of a datatype. These builders
-- retain ordinary kernel derivations; they do not authorize their conclusions.
module Felix.Checking.Recursion.Construction
    ( branchType
    , branchTypeFor
    , branchValue
    , recursiveSlots
    , proveStoredChild
    , branchRelation
    , branchFunctionalityTarget
    , ConstructorLaws(..)
    , proveBranchFunctionality
    , proveConstructorBranch
    , constructorEquationTarget
    , proveRecursorUniqueness
    , subtermPredicate
    , subtermInductionTarget
    , proveSubtermInduction
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof

import Control.Monad (foldM, unless)
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Numeric.Natural (Natural)

type Term = CanonicalTerm ObjectId
type Context = ProofContext ObjectId
type Proof = BuiltProof ObjectId
type Build = Either KernelProofBuildError

-- Distinctness references name the later constructor by its clause index.
data ConstructorLaws a = ConstructorLaws
    { constructorIntroduction :: !a
    , constructorInjectivity :: !(Maybe a)
    , constructorDistinctness :: ![(Natural, a)]
    } deriving stock (Functor, Foldable, Traversable)

branchType :: Datatype.Clause -> CoreType
branchType = branchTypeFor TySet

branchTypeFor :: CoreType -> Datatype.Clause -> CoreType
branchTypeFor result clause = foldr TyArrow result
    (replicate (length (Datatype.clauseArgumentSlots clause)) TySet
        <> replicate (length (recursiveSlots clause)) result)

recursiveSlots :: Datatype.Clause -> [Natural]
recursiveSlots clause =
    [slot | slot <- Datatype.clauseArgumentSlots clause
    , Just Datatype.Recursive <- [nth slot (Datatype.clausePremises clause)]]

branchValue :: Datatype.Clause -> Term -> Term -> [Term] -> Build Term
branchValue clause branch evaluate terms = do
    fields <- Datatype.argumentTerms clause terms
    children <- traverse (at "recursive field" terms) (recursiveSlots clause)
    pure (foldl' CApp branch (fields <> (CApp evaluate <$> children)))

-- Each branch describes a value using only stored fields and their recursive
-- values. Existential premise witnesses may establish a guard but cannot
-- influence that value.
branchDescriptions
    :: Int -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Term -> Term -> Term -> Build [Term]
branchDescriptions width carrier clauses branches evaluate element value = do
    unless (NonEmpty.length clauses == NonEmpty.length branches)
        (failure "branch count does not match the datatype")
    for (zip (toList clauses) (toList branches)) \(clause, branch) -> do
        let count = length (Datatype.clausePremises clause)
            liftTerm = shiftCanonical (fromIntegral count) 0
            terms = variables count
        constructor <- Datatype.constructorTerm clause terms
        result <- branchValue clause (liftTerm branch) (liftTerm evaluate) terms
        let conditions = Datatype.premiseTerms (width + count) (liftTerm carrier) clause terms
                <> [CEq TySet (liftTerm element) constructor, CEq TySet (liftTerm value) result]
        pure (foldr (const (CExists TySet)) (conjunction conditions) terms)

branchRelation
    :: Int -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Term -> Term -> Term -> Build Term
branchRelation width carrier clauses branches evaluate element value =
    disjunction <$> branchDescriptions width carrier clauses branches evaluate element value

-- The evaluator may return arbitrary sets. Functionality needs no hypothesis
-- about a history graph; the recursion adapter can instantiate it with graph
-- application once it has constructed the immediate-subterm relation.
branchFunctionalityTarget
    :: Int -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term -> Build Term
branchFunctionalityTarget width carrier clauses branches = do
    let liftTerm = shiftCanonical 2 0
    result <- uniqueValue (width + 2) (liftTerm carrier) clauses (liftTerm <$> branches) (CBound 0) (CBound 1)
    pure (CForall TySet (CForall (TyArrow TySet TySet)
        (CImp (member (CBound 1) (liftTerm carrier)) result)))

uniqueValue :: Int -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term -> Term -> Term -> Build Term
uniqueValue width carrier clauses branches evaluate element = do
    let shift = shiftCanonical 1 0
    holds <- branchRelation (width + 1) (shift carrier) clauses (shift <$> branches) (shift evaluate) (shift element) (CBound 0)
    other <- branchRelation (width + 2) (shift (shift carrier)) clauses (shift . shift <$> branches)
        (shift (shift evaluate)) (shift (shift element)) (CBound 0)
    pure (CExists TySet (CAnd holds (CForall TySet (CImp other (CEq TySet (CBound 0) (CBound 1))))))

proveBranchFunctionality
    :: Context -> [Term] -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Datatype.ProofImport -> NonEmpty (ConstructorLaws Datatype.ProofImport) -> Build Proof
proveBranchFunctionality root parameters carrier clauses branches casesLaw laws = do
    unless (NonEmpty.length clauses == NonEmpty.length branches && NonEmpty.length clauses == NonEmpty.length laws)
        (failure "branch laws do not match the datatype")
    introduceForalls root [TySet, TyArrow TySet TySet] \context -> do
        let element = CBound 1
            evaluate = CBound 0
            d = weaken root context carrier
            bs = weaken root context <$> branches
        assume context (member element d) \withMember -> do
            cases <- use withMember casesLaw ((weaken root withMember <$> parameters) <> [element])
            premise <- known withMember (member element d)
            alternatives <- traverse (Datatype.clauseFormula (contextWidth withMember) d element) (toList clauses)
            proof <- implicationEliminationProof withMember cases premise
            target <- uniqueValue (contextWidth withMember) d clauses bs evaluate element >>= scopedTerm withMember
            eliminateLeftAssociatedDisjunction withMember alternatives proof target \caseContext index alternative -> do
                clause <- at "constructor" (toList clauses) index
                witnesses caseContext (length (Datatype.clausePremises clause)) alternative
                    (scopedCoreTerm target) \chosen -> do
                        let terms = variables (length (Datatype.clausePremises clause))
                            current term = weaken context chosen term
                            d' = current d
                            bs' = current <$> bs
                            evaluate' = current evaluate
                            element' = current element
                        branch <- at "branch" (toList bs') index
                        value <- branchValue clause branch evaluate' terms
                        descriptions <- branchDescriptions (contextWidth chosen) d' clauses bs' evaluate' element' value
                        selected <- at "branch description" descriptions index
                        constructor <- Datatype.constructorTerm clause terms
                        guards <- traverse (known chosen) (Datatype.premiseTerms (contextWidth chosen) d' clause terms
                            <> [CEq TySet element' constructor])
                        reflexive <- scopedTerm chosen value >>= equalityReflexivityProof chosen
                        body <- buildLeftAssociatedConjunction chosen (guards <> [reflexive])
                        exists <- existsMany chosen selected terms body
                        holds <- introduceLeftAssociatedDisjunct chosen index descriptions exists
                        unique <- forallIntroductionProof chosen TySet \withOther _ -> do
                            let liftTerm = weaken chosen withOther
                                other = CBound 0
                                original = liftTerm value

                            descriptions' <- branchDescriptions (contextWidth withOther) (liftTerm d') clauses
                                (liftTerm <$> bs') (liftTerm evaluate') (liftTerm element') other
                            assume withOther (disjunction descriptions') \withRelation -> do
                                related <- known withRelation (disjunction descriptions')
                                equality <- scopedTerm withRelation (CEq TySet other original)
                                eliminateLeftAssociatedDisjunction withRelation descriptions' related equality
                                    \otherCase otherIndex otherDescription -> do
                                        otherClause <- at "constructor" (toList clauses) otherIndex
                                        witnesses otherCase (length (Datatype.clausePremises otherClause)) otherDescription
                                            (scopedCoreTerm equality) \comparison -> do
                                                let fromChosen = weaken chosen comparison
                                                    fromOther = weaken withOther comparison
                                                    leftTerms = fromChosen <$> terms
                                                    rightTerms = variables (length (Datatype.clausePremises otherClause))
                                                    x = fromChosen element'
                                                left <- Datatype.constructorTerm clause leftTerms
                                                right <- Datatype.constructorTerm otherClause rightTerms
                                                toLeft <- known comparison (CEq TySet x left) >>= equalityReverseProof comparison
                                                toRight <- known comparison (CEq TySet x right)
                                                same <- composeEqualityProof comparison toLeft toRight
                                                if index == otherIndex then do
                                                    selectedLaws <- at "constructor laws" (toList laws) index
                                                    equalities <- fieldEqualities comparison clause selectedLaws leftTerms rightTerms same
                                                    valueEquality <- branchCongruence comparison clause (fromChosen branch)
                                                        (fromChosen evaluate') equalities
                                                    otherValue <- branchValue otherClause (fromChosen branch) (fromChosen evaluate') rightTerms
                                                    output <- known comparison (CEq TySet (fromOther other) otherValue)
                                                    reversed <- equalityReverseProof comparison valueEquality
                                                    composeEqualityProof comparison output reversed
                                                else do
                                                    contradiction <- constructorClash comparison clauses laws
                                                        (index, leftTerms) (otherIndex, rightTerms) same
                                                    goal <- scopedTerm comparison (CEq TySet (fromOther other) (fromOther original))
                                                    falsumEliminationProof comparison contradiction goal
                        both <- conjunctionIntroductionProof chosen holds unique
                        goal <- uniqueValue (contextWidth chosen) d' clauses bs' evaluate' element'
                        existsOne chosen goal value both

-- A constructor with its premise guards realizes the corresponding branch.
proveConstructorBranch
    :: Context -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Term -> Natural -> [Term] -> Build Proof
proveConstructorBranch context carrier clauses branches evaluate index terms = do
    clause <- at "constructor" (toList clauses) index
    branch <- at "branch" (toList branches) index
    constructor <- Datatype.constructorTerm clause terms
    value <- branchValue clause branch evaluate terms
    descriptions <- branchDescriptions (contextWidth context) carrier clauses branches evaluate constructor value
    selected <- at "branch description" descriptions index
    guards <- traverse (known context) (Datatype.premiseTerms (contextWidth context) carrier clause terms)
    constructorEquality <- scopedTerm context constructor >>= equalityReflexivityProof context
    valueEquality <- scopedTerm context value >>= equalityReflexivityProof context
    body <- buildLeftAssociatedConjunction context (guards <> [constructorEquality, valueEquality])
    exists <- existsMany context selected terms body
    introduceLeftAssociatedDisjunct context index descriptions exists

constructorEquationTarget :: CoreType -> Int -> Term -> Datatype.Clause -> Term -> Term -> Build Term
constructorEquationTarget resultType width carrier clause branch evaluate = do
    let count = length (Datatype.clausePremises clause)
        shift = shiftCanonical (fromIntegral count) 0
        terms = variables count
    constructor <- Datatype.constructorTerm clause terms
    value <- branchValue clause (shift branch) (shift evaluate) terms
    let guards = Datatype.premiseTerms (width + count) (shift carrier) clause terms
        equation = CEq resultType (CApp (shift evaluate) constructor) value
        guarded = if null guards then equation else CImp (conjunction guards) equation
    pure (foldr (const (CForall TySet)) guarded terms)

-- Constructor equations characterize a logical function on the carrier.
-- There is deliberately no constraint on its off-carrier values here.
proveRecursorUniqueness
    :: CoreType -> Context -> [Term] -> Term -> NonEmpty Datatype.Clause -> NonEmpty Term
    -> Term -> Term -> Datatype.ProofImport -> Build Proof
proveRecursorUniqueness resultType root parameters carrier clauses branches left right inductionLaw = do
    let predicate = CLam TySet (CEq resultType (CApp (shiftCanonical 1 0 left) (CBound 0))
            (CApp (shiftCanonical 1 0 right) (CBound 0)))
    cases <- for (NonEmpty.zip clauses branches) \(clause, branch) ->
        introduceForalls root (replicate (length (Datatype.clausePremises clause)) TySet) \withFields -> do
            let current = weaken root withFields
                terms = variables (length (Datatype.clausePremises clause))
                guards = Datatype.premiseTerms (contextWidth withFields) (current carrier) clause terms
                hypotheses = [CApp (current predicate) term
                    | (Datatype.Recursive, term) <- zip (Datatype.clausePremises clause) terms]
            assumeConditions withFields (guards <> hypotheses) \context -> do
                constructor <- Datatype.constructorTerm clause terms
                leftEquation <- constructorEquationTarget resultType (contextWidth root) carrier clause branch left
                rightEquation <- constructorEquationTarget resultType (contextWidth root) carrier clause branch right
                -- Equations are active hypotheses in the outer context;
                -- retrieve their shifted forms to preserve binder indices.
                leftLaw <- known context (current leftEquation)
                rightLaw <- known context (current rightEquation)
                leftAtConstructor <- foldM (\proof term -> scopedTerm context term >>= forallEliminationProof context proof) leftLaw terms
                    >>= \proof -> applyConditions context proof guards
                rightAtConstructor <- foldM (\proof term -> scopedTerm context term >>= forallEliminationProof context proof) rightLaw terms
                    >>= \proof -> applyConditions context proof guards
                fields <- Datatype.argumentTerms clause terms
                fixed <- traverse (\term -> scopedTerm context term >>= equalityReflexivityProof context) fields
                children <- traverse (at "recursive field" terms) (recursiveSlots clause)
                results <- for children \child -> do
                    hypothesis <- known context (CApp (current predicate) child)
                    scopedTerm context (CEq resultType (CApp (current left) child) (CApp (current right) child))
                        >>= conversionProof context hypothesis
                branchEquality <- scopedTerm context (current branch) >>= equalityReflexivityProof context
                equalValues <- foldM (equalityCongruenceApplicationProof context) branchEquality (fixed <> results)
                reversed <- equalityReverseProof context rightAtConstructor
                equation <- composeEqualityProof context leftAtConstructor equalValues
                    >>= \proof -> composeEqualityProof context proof reversed
                scopedTerm context (CApp (current predicate) constructor) >>= conversionProof context equation
    induction <- use root inductionLaw (parameters <> [predicate])
    allCases <- buildLeftAssociatedConjunction root (toList cases)
    implicationEliminationProof root induction allCases

-- Only stored recursive fields give edges of the subterm relation.
proveStoredChild
    :: Context -> Term -> NonEmpty Datatype.Clause -> Natural -> [Term] -> Natural -> Build Proof
proveStoredChild context carrier clauses index terms childIndex = do
    clause <- at "constructor" (toList clauses) index
    constructor <- Datatype.constructorTerm clause terms
    children <- traverse (at "recursive field" terms) (recursiveSlots clause)
    child <- at "recursive child" children childIndex
    descriptions <- subtermDescriptions (contextWidth context) carrier clauses child constructor
    selected <- at "subterm description" descriptions index
    guards <- traverse (known context) (Datatype.premiseTerms (contextWidth context) carrier clause terms)
    parentEquality <- scopedTerm context constructor >>= equalityReflexivityProof context
    childEquality <- scopedTerm context child >>= equalityReflexivityProof context
    choice <- introduceLeftAssociatedDisjunct context childIndex (CEq TySet child <$> children) childEquality
    body <- buildLeftAssociatedConjunction context (guards <> [parentEquality,choice])
    exists <- existsMany context selected terms body
    introduceLeftAssociatedDisjunct context index descriptions exists

-- Different constructors cannot describe the same scrutinee. Reorient the
-- equation to the declaration order used by the public distinctness law.
constructorClash
    :: Context -> NonEmpty Datatype.Clause -> NonEmpty (ConstructorLaws Datatype.ProofImport)
    -> (Natural, [Term]) -> (Natural, [Term]) -> Proof -> Build Proof
constructorClash context clauses laws (leftIndex, leftTerms) (rightIndex, rightTerms) same = do
    left <- at "constructor" (toList clauses) leftIndex
    right <- at "constructor" (toList clauses) rightIndex
    leftFields <- Datatype.argumentTerms left leftTerms
    rightFields <- Datatype.argumentTerms right rightTerms
    let (earlier, later) = if leftIndex < rightIndex then (leftIndex, rightIndex) else (rightIndex, leftIndex)
    earlierLaws <- at "constructor laws" (toList laws) earlier
    distinct <- maybe (failure "constructor distinctness law is missing") pure
        (List.lookup later (constructorDistinctness earlierLaws))
    (arguments, equation) <- if leftIndex < rightIndex
        then pure (leftFields <> rightFields, same)
        else do
            reversed <- equalityReverseProof context same
            pure (rightFields <> leftFields, reversed)
    unequal <- use context distinct arguments
    negationEliminationProof context equation unequal

fieldEqualities :: Context -> Datatype.Clause -> ConstructorLaws Datatype.ProofImport -> [Term] -> [Term] -> Proof -> Build [Proof]
fieldEqualities context clause laws left right same = do
    leftFields <- Datatype.argumentTerms clause left
    rightFields <- Datatype.argumentTerms clause right
    case leftFields of
        [] -> pure []
        _ -> do
            law <- maybe (failure "constructor injectivity law is missing") pure (constructorInjectivity laws)
            injective <- use context law (leftFields <> rightFields)
            equalities <- implicationEliminationProof context injective same
            projectLeftAssociatedConjuncts context (zipWith (CEq TySet) leftFields rightFields) equalities

branchCongruence :: Context -> Datatype.Clause -> Term -> Term -> [Proof] -> Build Proof
branchCongruence context clause branch evaluate equalities = do
    initial <- scopedTerm context branch >>= equalityReflexivityProof context
    evaluator <- scopedTerm context evaluate >>= equalityReflexivityProof context
    recursive <- sequence
        [equalityCongruenceApplicationProof context evaluator equality
        | (slot, equality) <- zip (Datatype.clauseArgumentSlots clause) equalities
        , slot `elem` recursiveSlots clause]
    foldM (equalityCongruenceApplicationProof context) initial (equalities <> recursive)

subtermDescriptions :: Int -> Term -> NonEmpty Datatype.Clause -> Term -> Term -> Build [Term]
subtermDescriptions width carrier clauses child parent = for (toList clauses) \clause -> do
    let count = length (Datatype.clausePremises clause)
        shift = shiftCanonical (fromIntegral count) 0
        terms = variables count
    constructor <- Datatype.constructorTerm clause terms
    children <- traverse (at "recursive field" terms) (recursiveSlots clause)
    let conditions = Datatype.premiseTerms (width + count) (shift carrier) clause terms
            <> [CEq TySet (shift parent) constructor, disjunction (CEq TySet (shift child) <$> children)]
    pure (foldr (const (CExists TySet)) (conjunction conditions) terms)

subtermPredicate :: Int -> Term -> NonEmpty Datatype.Clause -> Term -> Term -> Build Term
subtermPredicate width carrier clauses child parent =
    disjunction <$> subtermDescriptions width carrier clauses child parent

predecessorProperty :: Int -> Term -> NonEmpty Datatype.Clause -> Term -> Term -> Build Term
predecessorProperty width carrier clauses predicate parent = do
    let shift = shiftCanonical 1 0
    edge <- subtermPredicate (width + 1) (shift carrier) clauses (CBound 0) (shift parent)
    pure (CForall TySet (CImp edge (CApp (shift predicate) (CBound 0))))

progressiveProperty :: Int -> Term -> NonEmpty Datatype.Clause -> Term -> Build Term
progressiveProperty width carrier clauses predicate = do
    let shift = shiftCanonical 1 0
    predecessors <- predecessorProperty (width + 1) (shift carrier) clauses (shift predicate) (CBound 0)
    pure (CForall TySet (CImp (member (CBound 0) (shift carrier))
        (CImp predecessors (CApp (shift predicate) (CBound 0)))))

subtermInductionTarget :: Int -> Term -> NonEmpty Datatype.Clause -> Build Term
subtermInductionTarget width carrier clauses = do
    let shift = shiftCanonical 1 0
    progressive <- progressiveProperty (width + 1) (shift carrier) clauses (CBound 0)
    pure (CForall (TyArrow TySet TyProp) (CImp progressive
        (CForall TySet (CImp (member (CBound 0) (shift (shift carrier))) (CApp (CBound 1) (CBound 0))))))

-- Ordinary datatype induction implies induction along stored recursive fields.
-- The induction hypotheses for unstored recursive witnesses are harmless: the
-- predecessor proof below selects only fields occurring in the constructor.
proveSubtermInduction
    :: Context -> [Term] -> Term -> NonEmpty Datatype.Clause
    -> Datatype.ProofImport -> NonEmpty (ConstructorLaws Datatype.ProofImport) -> Build Proof
proveSubtermInduction root parameters carrier clauses inductionLaw laws =
    forallIntroductionProof root (TyArrow TySet TyProp) \withPredicate _ -> do
        let d = weaken root withPredicate carrier
            predicate = CBound 0
        progressive <- progressiveProperty (contextWidth withPredicate) d clauses predicate
        assume withPredicate progressive \context -> do
            cases <- for (NonEmpty.zip (0 :| [1 ..]) clauses) \(index, clause) ->
                introduceForalls context (replicate (length (Datatype.clausePremises clause)) TySet) \withFields -> do
                    let current = weaken context withFields
                        terms = variables (length (Datatype.clausePremises clause))
                        guards = Datatype.premiseTerms (contextWidth withFields) (current d) clause terms
                        hypotheses = [CApp (current predicate) term
                            | (Datatype.Recursive, term) <- zip (Datatype.clausePremises clause) terms]
                    assumeConditions withFields (guards <> hypotheses) \withPremises -> do
                        selected <- at "constructor laws" (toList laws) index
                        intro <- use withPremises (constructorIntroduction selected)
                            ((weaken root withPremises <$> parameters) <> terms)
                        inCarrier <- applyConditions withPremises intro guards
                        constructor <- Datatype.constructorTerm clause terms
                        step <- known withPremises (current progressive)
                        instance' <- scopedTerm withPremises constructor >>= forallEliminationProof withPremises step
                        atConstructor <- implicationEliminationProof withPremises instance' inCarrier
                        predecessors <- provePredecessorProperty withPremises (current d) clauses laws
                            (current predicate) index terms
                        implicationEliminationProof withPremises atConstructor predecessors
            induction <- use context inductionLaw ((weaken root context <$> parameters) <> [predicate])
            closed <- buildLeftAssociatedConjunction context (toList cases)
            implicationEliminationProof context induction closed

provePredecessorProperty
    :: Context -> Term -> NonEmpty Datatype.Clause -> NonEmpty (ConstructorLaws Datatype.ProofImport)
    -> Term -> Natural -> [Term] -> Build Proof
provePredecessorProperty root carrier clauses laws predicate index terms = do
    clause <- at "constructor" (toList clauses) index
    constructor <- Datatype.constructorTerm clause terms
    forallIntroductionProof root TySet \withChild _ -> do
        let current = weaken root withChild
            child = CBound 0
        descriptions <- subtermDescriptions (contextWidth withChild) (current carrier) clauses child (current constructor)
        assume withChild (disjunction descriptions) \context -> do
            relation <- known context (disjunction descriptions)
            goal <- scopedTerm context (CApp (current predicate) child)
            eliminateLeftAssociatedDisjunction context descriptions relation goal \otherCase otherIndex description -> do
                other <- at "constructor" (toList clauses) otherIndex
                witnesses otherCase (length (Datatype.clausePremises other)) description
                    (scopedCoreTerm goal) \comparison -> do
                        let fromRoot = weaken root comparison
                            fromChild = weaken withChild comparison
                            leftTerms = fromRoot <$> terms
                            rightTerms = variables (length (Datatype.clausePremises other))
                            y = fromChild child
                            p = fromRoot predicate
                        right <- Datatype.constructorTerm other rightTerms
                        same <- known comparison (CEq TySet (fromRoot constructor) right)
                        target <- scopedTerm comparison (CApp p y)
                        if index /= otherIndex then do
                            contradiction <- constructorClash comparison clauses laws
                                (index, leftTerms) (otherIndex, rightTerms) same
                            falsumEliminationProof comparison contradiction target
                        else do
                            selected <- at "constructor laws" (toList laws) index
                            equalities <- fieldEqualities comparison clause selected leftTerms rightTerms same
                            children <- traverse (at "recursive field" rightTerms) (recursiveSlots clause)
                            let alternatives = CEq TySet y <$> children
                            choice <- known comparison (disjunction alternatives)
                            eliminateLeftAssociatedDisjunction comparison alternatives choice target \chosen childIndex equality -> do
                                slot <- at "recursive slot" (recursiveSlots clause) childIndex
                                fieldEquality <- maybe (failure "recursive field equality is missing") pure
                                    (List.lookup slot (zip (Datatype.clauseArgumentSlots clause) equalities))
                                field <- at "recursive field" leftTerms slot
                                original <- known chosen (CApp p field)
                                let added = length (proofContextHypotheses chosen) - length (proofContextHypotheses comparison)
                                backwards <- equalityReverseProof chosen (weakenProofHypotheses (fromIntegral added) fieldEquality)
                                toField <- composeEqualityProof chosen equality backwards
                                toChild <- equalityReverseProof chosen toField
                                property <- scopedTerm chosen p
                                equalityTransportProof chosen toChild property original

assumeConditions :: Context -> [Term] -> (Context -> Build Proof) -> Build Proof
assumeConditions context [] body = body context
assumeConditions context conditions body = assume context (conjunction conditions) body

applyConditions :: Context -> Proof -> [Term] -> Build Proof
applyConditions _ proof [] = pure proof
applyConditions context proof conditions = do
    premises <- traverse (known context) conditions >>= buildLeftAssociatedConjunction context
    implicationEliminationProof context proof premises

contextWidth :: Context -> Int
contextWidth = length . proofContextTypes

weaken :: Context -> Context -> Term -> Term
weaken root context = shiftCanonical (fromIntegral (contextWidth context - contextWidth root)) 0

variables :: Int -> [Term]
variables count = CBound . fromIntegral <$> reverse [0 .. count - 1]

member :: Term -> Term -> Term
member a b = CApp (CApp (CIntrinsic Member) a) b

conjunction, disjunction :: [Term] -> Term
conjunction [] = CTruth
conjunction (x : xs) = foldl' CAnd x xs
disjunction [] = CFalsum
disjunction (x : xs) = foldl' COr x xs

failure :: Text -> Build a
failure = Left . ProofStructuralCompositionMismatch

at :: Text -> [a] -> Natural -> Build a
at description values index = maybe (failure (description <> " is missing")) pure (nth index values)

assume :: Context -> Term -> (Context -> Build Proof) -> Build Proof
assume context proposition body = scopedTerm context proposition >>= \checked ->
    implicationIntroductionProof context checked (\extended _ -> body extended)

known :: Context -> Term -> Build Proof
known context target = do
    premises <- traverse (hypothesisProof context) (proofContextHypotheses context)
    goal <- scopedTerm context target
    structuralLogicalProof context premises goal >>= maybe (failure "recursion proof lost a premise") pure

use :: Context -> Datatype.ProofImport -> [Term] -> Build Proof
use context (index, target) arguments = do
    proof <- importedProof context index target
    foldM (\current argument -> scopedTerm context argument >>= forallEliminationProof context current) proof arguments

existsOne :: Context -> Term -> Term -> Proof -> Build Proof
existsOne context target witness proof = case target of
    CExists ty body -> do
        checked <- first ProofTermIllTyped (checkScopedTermUnderBinder context ty body)
        term <- scopedTerm context witness
        existentialIntroductionProof context ty checked term proof
    _ -> failure "recursion witness target is not existential"

existsMany :: Context -> Term -> [Term] -> Proof -> Build Proof
existsMany context target [] proof = scopedTerm context target >>= conversionProof context proof
existsMany context target (witness : rest) proof = case target of
    CExists _ body -> do
        inner <- existsMany context (instantiateCanonical witness body) rest proof
        existsOne context target witness inner
    _ -> failure "recursion branch lost an existential binder"

witnesses :: Context -> Int -> Proof -> Term -> (Context -> Build Proof) -> Build Proof
witnesses context 0 proof _target body = do
    implication <- implicationIntroductionProof context (builtProofStatement proof) (\extended _ -> body extended)
    implicationEliminationProof context implication proof
witnesses context count proof target body = case scopedCoreTerm (builtProofStatement proof) of
    CExists ty inner -> do
        checked <- first ProofTermIllTyped (checkScopedTermUnderBinder context ty inner)
        goal <- scopedTerm context target
        existentialEliminationProof context ty checked proof goal \extended _ _ -> do
            premise <- scopedTerm extended inner >>= hypothesisProof extended
            witnesses extended (count - 1) premise (shiftCanonical 1 0 target) body
    _ -> failure "recursion branch has too few existential witnesses"
