{-# LANGUAGE NoImplicitPrelude #-}

-- | Set encodings and ordinary proof-producing mathematics for datatypes.
-- Nothing in this module grants authority: the declaration owner replays each
-- retained derivation against its independently prepared target and imports.
module Felix.Checking.Datatype.Construction
    ( kuratowskiBody
    , constructorBody
    , ProofImport
    , proveKuratowskiInjective
    , proveBitInequality
    , proveUniverseEmpty
    , proveUniversePair
    , proveUniverseKuratowski
    , Premise(..)
    , Clause(..)
    , argumentTerms
    , constructorTerm
    , premiseTerms
    , clauseFormula
    , carrierTerms
    , introductionTarget
    , distinctTarget
    , injectiveTarget
    , casesTarget
    , inductionTarget
    , predicateCaseTarget
    , predicateCaseBoundedTarget
    , provePredicateCaseFromBounded
    , predicateInductionTarget
    , guardTarget
    , subsetTerm
    , proveBoundedMono
    , proveCarrierBound
    , proveCarrierFixed
    , proveIntroduction
    , proveCases
    , proveInduction
    , provePredicateInduction
    , proveDomainBound
    , UniverseProofs(..)
    , proveGuard
    , proveInjective
    , proveDistinct
    , kuratowskiInjectiveTarget
    , bitInequalityTarget
    , universeEmptyTarget
    , universePairTarget
    , universeKuratowskiTarget
    , boundedMonoTarget
    ) where

import Base hiding (Empty, empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Derivation (ImportIx, HypothesisIx, hypothesisIx, hypothesisIxValue)
import Felix.Checking.Kernel.Proof
import Felix.Checking.Kernel.SetLfp qualified as SetLfp

import Control.Monad (foldM)
import Data.Bifunctor qualified as Bifunctor
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Numeric.Natural (Natural)

type Term = CanonicalTerm ObjectId
type Context = ProofContext ObjectId
type Proof = BuiltProof ObjectId
type Build = Either KernelProofBuildError
type ProofImport = (ImportIx, FrozenCheckedCore ObjectId)

empty :: Term
empty = CIntrinsic Empty

pair, member, equal :: Term -> Term -> Term
pair a b = CApp (CApp (CIntrinsic PairSet) a) b
member a b = CApp (CApp (CIntrinsic Member) a) b
equal = CEq TySet

singleton, universe, power :: Term -> Term
singleton a = pair a a
universe = CApp (CIntrinsic UnivOf)
power = CApp (CIntrinsic PowerSet)

kuratowski :: Term -> Term -> Term
kuratowski a b = pair (singleton a) (pair a b)

kuratowskiBody :: Term
kuratowskiBody = CLam TySet (CLam TySet (kuratowski (CBound 1) (CBound 0)))

tuple :: ObjectId -> [Term] -> Term
tuple k = foldr (\a b -> CApp (CApp (CGlobal k) a) b) empty

constructorBody :: ObjectId -> Natural -> Natural -> Int -> Term
constructorBody k count index arity =
    foldr (const (CLam TySet))
        (CApp (CApp (CGlobal k) tag) (tuple k (variables arity))) [1 .. arity]
  where
    tag = tuple k (tagDigits count index)

tagDigits :: Natural -> Natural -> [Term]
tagDigits count index = reverse (digits width index)
  where
    width = max 1 (bitLength (count - 1))
    bitLength :: Natural -> Natural
    bitLength 0 = 0
    bitLength n = 1 + bitLength (n `div` 2)
    digits 0 _ = []
    digits n i = (if odd i then singleton empty else empty) : digits (n - 1) (i `div` 2)

-- Premise order is also quantifier order. Argument slots index that order;
-- a premise need not occur among the constructor arguments.
data Premise = Recursive | FixedDomain !(ScopedCheckedCore ObjectId)

data Clause = Clause
    { clauseConstructor :: !ObjectId
    , clauseArgumentSlots :: ![Natural]
    , clausePremises :: ![Premise]
    }

argumentTerms :: Clause -> [Term] -> Build [Term]
argumentTerms clause terms = traverse
    (\slot -> maybe (Left (ProofStructuralCompositionMismatch "datatype argument has no premise slot")) pure
        (nth slot terms)) (clauseArgumentSlots clause)

constructorTerm :: Clause -> [Term] -> Build Term
constructorTerm clause terms = foldl' CApp (CGlobal (clauseConstructor clause)) <$> argumentTerms clause terms

-- Fixed domains are checked in the family-parameter context. Generated local
-- binders only extend that context; weaken domains at their point of use.
domainAt :: Int -> ScopedCheckedCore ObjectId -> Term
domainAt width domain
    | width >= length (scopedCoreContext domain) =
        shiftCanonical (fromIntegral (width - length (scopedCoreContext domain))) 0 (scopedCoreTerm domain)
    | otherwise = impossible "datatype domain escaped its parameter context"

contextWidth :: Context -> Int
contextWidth = length . proofContextTypes

parametersAt :: Int -> Context -> [Term]
parametersAt count context = CBound . fromIntegral <$> reverse [contextWidth context - count .. contextWidth context - 1]

premiseTerms :: Int -> Term -> Clause -> [Term] -> [Term]
premiseTerms width recursive clause = zipWith
    (\premise variable -> member variable (case premise of Recursive -> recursive; FixedDomain domain -> domainAt width domain))
    (clausePremises clause)

foralls :: Int -> Term -> Term
foralls count body = foldr (const (CForall TySet)) body [1 .. count]

implications :: [Term] -> Term -> Term
implications [] conclusion = conclusion
implications premises conclusion = CImp (conjunctions premises) conclusion

conjunctions, disjunctions :: [Term] -> Term
conjunctions [] = CTruth
conjunctions (first : rest) = foldl' CAnd first rest
disjunctions [] = CFalsum
disjunctions (first : rest) = foldl' COr first rest

subsetTerm :: Term -> Term -> Term
subsetTerm a b = CForall TySet (CImp (member (CBound 0) (shift a)) (member (CBound 0) (shift b)))

clauseFormula :: Int -> Term -> Term -> Clause -> Build Term
clauseFormula width recursive element clause = do
    let count = length (clausePremises clause)
        terms = variables count
    result <- constructorTerm clause terms
    let body = conjunctions (premiseTerms (width + count) (shiftCanonical (fromIntegral count) 0 recursive) clause terms
            <> [equal (shiftCanonical (fromIntegral count) 0 element) result])
    pure (foldr (const (CExists TySet)) body (clausePremises clause))

operatorPredicate :: Int -> NonEmpty Clause -> Term -> Build Term
operatorPredicate width clauses recursive = CLam TySet . disjunctions
    <$> traverse (clauseFormula (width + 1) (shift recursive) (CBound 0)) (toList clauses)

fixedDomains :: Int -> NonEmpty Clause -> [Term]
fixedDomains width clauses = [domainAt width domain | clause <- toList clauses, FixedDomain domain <- clausePremises clause]

seedTerm :: Int -> NonEmpty Clause -> Term
seedTerm width clauses = foldl' (flip canonicalSetInsert) empty (empty : fixedDomains width clauses)

carrierTerms :: Int -> NonEmpty Clause -> Build (Term, Term, Term)
carrierTerms width clauses = do
    predicate <- operatorPredicate (width + 1) clauses (CBound 0)
    let bound = universe (seedTerm width clauses)
        operator = CLam TySet (separate (shift bound) predicate)
        carrier = CApp (CApp (CIntrinsic ISetLfp) bound) operator
    pure (bound, operator, carrier)

introductionTarget :: Int -> Term -> Clause -> Build Term
introductionTarget width carrier clause = do
    let count = length (clausePremises clause)
        terms = variables count
        recursive = shiftCanonical (fromIntegral count) 0 carrier
    result <- constructorTerm clause terms
    pure (foralls count (implications (premiseTerms (width + count) recursive clause terms) (member result recursive)))

guardTarget :: Int -> Term -> Clause -> Build Term
guardTarget = introductionTarget

distinctTarget :: Clause -> Clause -> Term
distinctTarget left right =
    let leftCount = length (clauseArgumentSlots left)
        rightCount = length (clauseArgumentSlots right)
        terms = variables (leftCount + rightCount)
    in foralls (leftCount + rightCount) (CNot (equal
        (foldl' CApp (CGlobal (clauseConstructor left)) (take leftCount terms))
        (foldl' CApp (CGlobal (clauseConstructor right)) (drop leftCount terms))))

injectiveTarget :: Clause -> Term
injectiveTarget clause =
    let count = length (clauseArgumentSlots clause)
        terms = variables (2 * count)
        left = take count terms; right = drop count terms
        app = foldl' CApp (CGlobal (clauseConstructor clause))
    in foralls (2 * count) (CImp (equal (app left) (app right)) (conjunctions (zipWith equal left right)))

casesTarget :: Int -> Term -> NonEmpty Clause -> Build Term
casesTarget width carrier clauses = do
    alternatives <- traverse (clauseFormula (width + 1) (shift carrier) (CBound 0)) (toList clauses)
    pure (CForall TySet (CImp (member (CBound 0) (shift carrier)) (disjunctions alternatives)))

inductionTarget :: Int -> Term -> NonEmpty Clause -> Build Term
inductionTarget width carrier clauses = do
    closures <- traverse (introductionTarget (width + 1) (CBound 0)) (toList clauses)
    pure (CForall TySet (implications closures (subsetTerm (shift carrier) (CBound 0))))

predicateCaseTarget :: Int -> Term -> Term -> Clause -> Build Term
predicateCaseTarget width predicate carrier clause = do
    let count = length (clausePremises clause)
        terms = variables count
        weaken = shiftCanonical (fromIntegral count) 0
        property = weaken predicate
        guards = premiseTerms (width + count) (weaken carrier) clause terms
        hypotheses = [applyProperty property variable | (Recursive, variable) <- zip (clausePremises clause) terms]
    result <- constructorTerm clause terms
    pure (foralls count (implications (guards <> hypotheses) (applyProperty property result)))
  where
    -- Source induction supplies a literal motive. Reduce only the applications
    -- introduced here; the author's property need not be normalized.
    applyProperty (CLam TySet body) argument = instantiateCanonical argument body
    applyProperty property argument = CApp property argument

predicateInductionTarget :: Int -> Term -> NonEmpty Clause -> Build Term
predicateInductionTarget width carrier clauses = do
    cases' <- traverse (predicateCaseTarget (width + 1) (CBound 0) (shift carrier)) (toList clauses)
    pure (CForall (TyArrow TySet TyProp) (implications cases'
        (CForall TySet (CImp (member (CBound 0) (shift (shift carrier))) (CApp (CBound 1) (CBound 0))))))

-- The source-facing form puts each domain beside its binder, so ordinary
-- bounded Fix steps open it. The public law keeps its existing premise block.
predicateCaseBoundedTarget :: Int -> Term -> Term -> Clause -> Build Term
predicateCaseBoundedTarget width predicate carrier clause = do
    flat <- predicateCaseTarget width predicate carrier clause
    let count = length (clausePremises clause)
        terms = variables count
        guards = premiseTerms (width + count) (shiftCanonical (fromIntegral count) 0 carrier) clause terms
        open 0 body = body
        open n (CForall TySet body) = open (n - 1) body
        open _ _ = impossible "datatype case lost its quantified premises"
        tailGoal = case open count flat of
            CImp _ conclusion ->
                let property = shiftCanonical (fromIntegral count) 0 predicate
                    apply argument = case property of
                        CLam TySet body -> instantiateCanonical argument body
                        _ -> CApp property argument
                in implications [apply term | (Recursive, term) <- zip (clausePremises clause) terms] conclusion
            conclusion -> conclusion
        bind (index, domainGuard) body =
            -- This guard uses its own variable and family parameters only.
            -- Remove the later, vacuous clause binders.
            CForall TySet (CImp (iterate (instantiateCanonical empty) domainGuard !! (count - index - 1)) body)
    pure (if count == 0 then flat else foldr bind tailGoal (zip [0..] guards))

provePredicateCaseFromBounded
    :: Context -> Term -> Term -> Clause -> HypothesisIx -> Build Proof
provePredicateCaseFromBounded root predicate carrier clause index = do
    target <- predicateCaseTarget (contextWidth root) predicate carrier clause
    introduceForalls root (replicate count TySet) \context -> do
        let opened = strip count target
        if count == 0 then indexedHypothesisProof context index else
            case opened of
                CImp antecedent _ -> assume context antecedent apply
                _ -> impossible "datatype case lost its domain guards"
  where
    count = length (clausePremises clause)
    strip 0 body = body
    strip n (CForall TySet body) = strip (n - 1) body
    strip _ _ = impossible "datatype case lost its quantifiers"
    apply context = do
        bounded <- indexedHypothesisProof context (hypothesisIx (hypothesisIxValue index + 1))
        instantiated <- foldM (\proof term -> do
            universal <- specialize context proof [term]
            discharge context universal) bounded (variables count)
        if any isRecursive (clausePremises clause)
            then discharge context instantiated else pure instantiated
    isRecursive Recursive = True
    isRecursive FixedDomain{} = False
    discharge context proof = case scopedCoreTerm (builtProofStatement proof) of
        CImp premise _ -> known context premise >>= implicationEliminationProof context proof
        _ -> pure proof

kuratowskiInjectiveTarget :: ObjectId -> Term
kuratowskiInjectiveTarget k = foralls 4
    (CImp (equal (app (CBound 3) (CBound 2)) (app (CBound 1) (CBound 0)))
        (CAnd (equal (CBound 3) (CBound 1)) (equal (CBound 2) (CBound 0))))
  where
    app a b = CApp (CApp (CGlobal k) a) b

bitInequalityTarget, universeEmptyTarget, universePairTarget :: Term
bitInequalityTarget = CNot (equal empty (singleton empty))
universeEmptyTarget = CForall TySet (member empty (universe (CBound 0)))
universePairTarget = universeClosureTarget (pair (CBound 1) (CBound 0))

universeKuratowskiTarget :: ObjectId -> Term
universeKuratowskiTarget k = universeClosureTarget (CApp (CApp (CGlobal k) (CBound 1)) (CBound 0))

universeClosureTarget :: Term -> Term
universeClosureTarget value = foralls 3 (CImp (member (CBound 1) u) (CImp (member (CBound 0) u) (member value u)))
  where
    u = universe (CBound 2)

boundedMonoTarget :: Int -> NonEmpty Clause -> Build Term
boundedMonoTarget width clauses = do
    (bound, operator, _) <- carrierTerms width clauses
    let weaken = shiftCanonical 2 0
    pure (CAnd (subsetTerm (CApp operator bound) bound)
        (foralls 2 (CImp (CAnd (subsetTerm (CBound 1) (CBound 0)) (subsetTerm (CBound 0) (weaken bound)))
            (subsetTerm (CApp (weaken operator) (CBound 1)) (CApp (weaken operator) (CBound 0))))))

variables :: Int -> [Term]
variables count = CBound . fromIntegral <$> reverse [0 .. count - 1]

shift :: Term -> Term
shift = shiftCanonical 1 0

check :: Context -> Term -> Build (ScopedCheckedCore ObjectId)
check = scopedTerm

hyp :: Context -> Term -> Build Proof
hyp context proposition = check context proposition >>= hypothesisProof context

assume :: Context -> Term -> (Context -> Build Proof) -> Build Proof
assume context proposition body = do
    checked <- check context proposition
    implicationIntroductionProof context checked (\extended _ -> body extended)

assumePremises :: Context -> [Term] -> (Context -> Build Proof) -> Build Proof
assumePremises context [] body = body context
assumePremises context premises body = assume context (conjunctions premises) body

-- A cut shares a derived fact within one proof tree. The body uses its local
-- hypothesis, so repeated uses do not duplicate the derivation of the fact.
withProof :: Context -> Proof -> (Context -> Build Proof) -> Build Proof
withProof context proof body = do
    implication <- implicationIntroductionProof context (builtProofStatement proof)
        (\extended _ -> body extended)
    implicationEliminationProof context implication proof

axiom :: Context -> FoundationAxiomTag -> [Term] -> Build Proof
axiom context tag arguments = traverse (check context) arguments >>= foundationInstanceProof context tag

use :: Context -> ProofImport -> [Term] -> Build Proof
use context (index, target) arguments = do
    proof <- importedProof context index target
    specialize context proof arguments

specialize :: Context -> Proof -> [Term] -> Build Proof
specialize context = foldM (\current argument -> check context argument >>= forallEliminationProof context current)

reflexive :: Context -> Term -> Build Proof
reflexive context term = check context term >>= equalityReflexivityProof context

convert :: Context -> Term -> Proof -> Build Proof
convert context target proof = check context target >>= conversionProof context proof

rewrite :: Context -> Proof -> Term -> Proof -> Build Proof
rewrite context equality predicate proof = do
    checked <- check context predicate
    result <- equalityTransportProof context equality checked proof
    case scopedCoreTerm (builtProofStatement result) of
        CApp (CLam _ body) argument -> convert context (instantiateCanonical argument body) result
        _ -> pure result

rewriteSet :: Context -> Term -> Proof -> Proof -> Build Proof
rewriteSet context element equality proof =
    rewrite context equality (CLam TySet (member (shift element) (CBound 0))) proof

rewriteElement :: Context -> Term -> Proof -> Proof -> Build Proof
rewriteElement context set equality proof =
    rewrite context equality (CLam TySet (member (CBound 0) (shift set))) proof

characteristic :: Context -> FoundationAxiomTag -> [Term] -> Bool -> Proof -> Build Proof
characteristic context tag arguments reverseDirection proof = do
    equation <- axiom context tag arguments
    directed <- if reverseDirection then equalityReverseProof context equation else pure equation
    case scopedCoreTerm (builtProofStatement directed) of
        CEq TyProp left _ -> convert context left proof >>= equalityModusPonensProof context directed
        _ -> Left (ProofStructuralCompositionMismatch "datatype characteristic is not a proposition equality")

known :: Context -> Term -> Build Proof
known context target = do
    premises <- traverse (hypothesisProof context) (proofContextHypotheses context)
    goal <- check context target
    structuralLogicalProof context premises goal >>= maybe
        (Left (ProofStructuralCompositionMismatch "datatype proof lost a local premise")) pure

existsI :: Context -> Term -> Term -> Proof -> Build Proof
existsI context target witness proof = case target of
    CExists ty body -> do
        body' <- either (Left . ProofTermIllTyped) pure (checkScopedTermUnderBinder context ty body)
        witness' <- check context witness
        existentialIntroductionProof context ty body' witness' proof
    _ -> Left (ProofStructuralCompositionMismatch "datatype witness target is not existential")

existsE :: Context -> Proof -> Term -> (Context -> Build Proof) -> Build Proof
existsE context proof target branch = case scopedCoreTerm (builtProofStatement proof) of
    CExists ty body -> do
        body' <- either (Left . ProofTermIllTyped) pure (checkScopedTermUnderBinder context ty body)
        goal <- check context target
        existentialEliminationProof context ty body' proof goal (\extended _ _ -> branch extended)
    _ -> Left (ProofStructuralCompositionMismatch "datatype proof expected an existential")

byCases :: Context -> Term -> Term -> (Context -> Build Proof) -> (Context -> Build Proof) -> Build Proof
byCases context proposition target yes no = do
    let disjunction = COr proposition (CNot proposition)
    negated <- check context (CNot disjunction)
    doubleNegated <- negationIntroductionProof context negated \outer _ -> do
        p <- check outer proposition
        notP <- negationIntroductionProof outer p \inner _ -> do
            positive <- hyp inner proposition >>= disjunctionLeftProof inner (CNot proposition)
            negative <- hyp inner (CNot disjunction)
            negationEliminationProof inner positive negative
        positive <- disjunctionRightProof outer proposition notP
        negative <- hyp outer (CNot disjunction)
        negationEliminationProof outer positive negative
    goal <- check context disjunction
    excluded <- doubleNegationEliminationProof context goal doubleNegated
    cases context excluded target yes no

union, separation :: Term -> Term
union = CApp (CIntrinsic FamilyUnion)
separation = CApp (CIntrinsic Sep)

separate :: Term -> Term -> Term
separate set predicate = CApp (separation set) predicate

unionI :: Context -> Term -> Term -> Term -> Proof -> Proof -> Build Proof
unionI context family element witness inFamily inWitness = do
    both <- conjunctionIntroductionProof context inFamily inWitness
    let target = CExists TySet (CAnd (member (CBound 0) (shift family)) (member (shift element) (CBound 0)))
    existential <- existsI context target witness both
    characteristic context FamilyUnionCharacteristic [family,element] True existential

setEquality :: Context -> Term -> Term -> Proof -> Proof -> Build Proof
setEquality context a b forward backward = do
    extensionality <- axiom context SetExtensionality [a,b]
    implicationEliminationProof context extensionality forward
        >>= \next -> implicationEliminationProof context next backward

emptySubset :: Context -> Term -> Build Proof
emptySubset context set = forallIntroductionProof context TySet \withElement element ->
    assume withElement (member (scopedCoreTerm element) empty) \extended -> do
        membership <- hyp extended (member (scopedCoreTerm element) empty)
        contradiction <- characteristic extended EmptyCharacteristic [scopedCoreTerm element] False membership
        target <- check extended (member (scopedCoreTerm element) (shift set))
        falsumEliminationProof extended contradiction target

pairLeft, pairRight :: Context -> Term -> Term -> Build Proof
pairLeft context a b = do
    equation <- reflexive context a
    disjunction <- disjunctionLeftProof context (equal a b) equation
    characteristic context PairSetCharacteristic [a,b,a] True disjunction
pairRight context a b = do
    equation <- reflexive context b
    disjunction <- disjunctionRightProof context (equal b a) equation
    characteristic context PairSetCharacteristic [a,b,b] True disjunction

cases :: Context -> Proof -> Term -> (Context -> Build Proof) -> (Context -> Build Proof) -> Build Proof
cases context proof target left right = case scopedCoreTerm (builtProofStatement proof) of
    COr a b -> do
        result <- check context target
        disjunctionEliminationProof context a b proof result
            (\extended _ -> left extended) (\extended _ -> right extended)
    _ -> Left (ProofStructuralCompositionMismatch "datatype proof expected a disjunction")

singletonMember :: Context -> Term -> Term -> Proof -> Build Proof
singletonMember context element a proof = do
    alternatives <- characteristic context PairSetCharacteristic [a,a,element] False proof
    cases context alternatives (equal element a)
        (\branch -> hyp branch (equal element a)) (\branch -> hyp branch (equal element a))

-- The first coordinate follows from membership of {a} in the other pair.
firstCoordinate :: Context -> Term -> Term -> Term -> Term -> Proof -> Build Proof
firstCoordinate context a b c d equality = do
    membership <- pairLeft context (singleton a) (pair a b)
    transported <- rewriteSet context (singleton a) equality membership
    alternatives <- characteristic context PairSetCharacteristic [singleton c,pair c d,singleton a] False transported
    result <- cases context alternatives (equal c a)
        (inSingleton (singleton c) (\branch -> pairLeft branch c c))
        (inSingleton (pair c d) (\branch -> pairLeft branch c d))
    equalityReverseProof context result
  where
    inSingleton right build branch = do
        equation <- hyp branch (equal (singleton a) right) >>= equalityReverseProof branch
        membership <- build branch >>= rewriteSet branch c equation
        singletonMember branch c a membership

-- The second coordinate belongs to {c,d}. This avoids an auxiliary theory
-- of intersections or projections for the internal Kuratowski encoding.
secondAlternatives :: Context -> Term -> Term -> Term -> Term -> Proof -> Build Proof
secondAlternatives context a b c d equality = do
    membership <- pairRight context (singleton a) (pair a b)
    transported <- rewriteSet context (pair a b) equality membership
    alternatives <- characteristic context PairSetCharacteristic [singleton c,pair c d,pair a b] False transported
    cases context alternatives target
        (\branch -> do
            equation <- hyp branch (equal (pair a b) (singleton c))
            inRight <- pairRight branch a b >>= rewriteSet branch b equation
            bc <- singletonMember branch b c inRight
            disjunctionLeftProof branch (equal b d) bc)
        (\branch -> do
            equation <- hyp branch (equal (pair a b) (pair c d))
            inRight <- pairRight branch a b >>= rewriteSet branch b equation
            characteristic branch PairSetCharacteristic [c,d,b] False inRight)
  where
    target = COr (equal b c) (equal b d)

proveKuratowskiInjective :: Context -> ObjectId -> ProofImport -> Build Proof
proveKuratowskiInjective root k definition = introduceForalls root (replicate 4 TySet) \context -> do
    let a = CBound 3
        b = CBound 2
        c = CBound 1
        d = CBound 0
        app x y = CApp (CApp (CGlobal k) x) y
        expanded = equal (kuratowski a b) (kuratowski c d)
    assume context (equal (app a b) (app c d)) \withEquality -> do
        left <- use withEquality definition [a,b] >>= equalityReverseProof withEquality
        original <- hyp withEquality (equal (app a b) (app c d))
        right <- use withEquality definition [c,d]
        equality <- composeEqualityProof withEquality left original
            >>= \proof -> composeEqualityProof withEquality proof right
        withProof withEquality equality \withExpanded -> do
            first <- hyp withExpanded expanded >>= firstCoordinate withExpanded a b c d
            withProof withExpanded first \withFirst -> do
                let normalized = equal (kuratowski a b) (kuratowski a d)
                ca <- hyp withFirst (equal a c) >>= equalityReverseProof withFirst
                source <- hyp withFirst expanded
                normalizedProof <- rewrite withFirst ca
                    (CLam TySet (equal (kuratowski (shift a) (shift b)) (kuratowski (CBound 0) (shift d)))) source
                second <- withProof withFirst normalizedProof \withNormalized -> do
                    choices <- hyp withNormalized normalized >>= secondAlternatives withNormalized a b a d
                    cases withNormalized choices (equal b d)
                        (\withBA -> do
                            reverseEquality <- hyp withBA normalized >>= equalityReverseProof withBA
                            reverseChoices <- secondAlternatives withBA a d a b reverseEquality
                            cases withBA reverseChoices (equal b d)
                                (\branch -> do
                                    ba <- hyp branch (equal b a)
                                    ad <- hyp branch (equal d a) >>= equalityReverseProof branch
                                    composeEqualityProof branch ba ad)
                                (\branch -> hyp branch (equal d b) >>= equalityReverseProof branch))
                        (\branch -> hyp branch (equal b d))
                ac <- hyp withFirst (equal a c)
                conjunctionIntroductionProof withFirst ac second

proveBitInequality :: Context -> Build Proof
proveBitInequality context = do
    target <- check context (equal empty (singleton empty))
    negationIntroductionProof context target \extended _ -> do
        equality <- hyp extended (equal empty (singleton empty)) >>= equalityReverseProof extended
        membership <- pairLeft extended empty empty >>= rewriteSet extended empty equality
        characteristic extended EmptyCharacteristic [empty] False membership

proveUniverseEmpty :: Context -> Build Proof
proveUniverseEmpty root = forallIntroductionProof root TySet \context e -> do
    let seed = scopedCoreTerm e
        u = universe seed
    subsetOfSeed <- emptySubset context seed
    inPower <- characteristic context PowerSetCharacteristic [seed,empty] True subsetOfSeed
    contained <- axiom context UnivOfContains [seed]
    powerClosed <- axiom context UnivOfPowerSetClosed [seed,seed]
    powerMember <- implicationEliminationProof context powerClosed contained
    transitive <- axiom context UnivOfTransitive [seed,power seed]
    subset <- implicationEliminationProof context transitive powerMember
    implication <- specialize context subset [empty]
    result <- implicationEliminationProof context implication inPower
    convert context (member empty u) result

-- A total selection term built solely from union and separation. Sending
-- every nonzero argument to b avoids enumerating the two-element domain.
selectionPredicate :: Term -> Term -> Term -> Term
selectionPredicate a b t = CLam TySet (selectionCondition (shift a) (shift b) (shift t) (CBound 0))

selectionCondition :: Term -> Term -> Term -> Term -> Term
selectionCondition a b t x =
    COr (CAnd (equal t empty) (equal x a)) (CAnd (CNot (equal t empty)) (equal x b))

selection :: Term -> Term -> Term -> Term
selection a b t = union (separate (pair a b) (selectionPredicate a b t))

selectionEquation :: Context -> Term -> Term -> Term -> Bool -> Build Proof
selectionEquation context a b t takeLeft = do
    forward <- forallIntroductionProof context TySet \underElement _ -> do
        let element = CBound 0
            a' = shift a; b' = shift b; t' = shift t
            family = separate (pair a' b') (selectionPredicate a' b' t')
        assume underElement (member element (union family)) \withMember -> do
            membership <- hyp withMember (member element (union family))
            witness <- characteristic withMember FamilyUnionCharacteristic [family,element] False membership
            existsE withMember witness (member element (if takeLeft then a' else b')) \withWitness -> do
                let a'' = shift a'; b'' = shift b'; t'' = shift t'
                    x = CBound 0; z = CBound 1
                    predicate = selectionPredicate a'' b'' t''
                    selected = if takeLeft then a'' else b''
                    condition = equal t'' empty
                inFamily <- known withWitness (member x (separate (pair a'' b'') predicate))
                separated <- characteristic withWitness SeparationCharacteristic [pair a'' b'',predicate,x] False inFamily
                predicateProof <- conjunctionRightProof withWitness separated
                    >>= convert withWitness (selectionCondition a'' b'' t'' x)
                cases withWitness predicateProof (member z selected)
                    (finish takeLeft condition a'' x z selected)
                    (finish (not takeLeft) condition b'' x z selected)
    backward <- forallIntroductionProof context TySet \underElement _ -> do
        let z = CBound 0; a' = shift a; b' = shift b; t' = shift t
            chosen = if takeLeft then a' else b'
            predicate = selectionPredicate a' b' t'
            family = separate (pair a' b') predicate
        assume underElement (member z chosen) \withMember -> do
            inPair <- if takeLeft then pairLeft withMember a' b' else pairRight withMember a' b'
            condition <- hyp withMember (if takeLeft then equal t' empty else CNot (equal t' empty))
            self <- reflexive withMember chosen
            selected <- conjunctionIntroductionProof withMember condition self
            let left = CAnd (equal t' empty) (equal chosen a')
                right = CAnd (CNot (equal t' empty)) (equal chosen b')
            disjunction <- if takeLeft then disjunctionLeftProof withMember right selected
                else disjunctionRightProof withMember left selected
            conjunction <- conjunctionIntroductionProof withMember inPair disjunction
            inFamily <- characteristic withMember SeparationCharacteristic [pair a' b',predicate,chosen] True conjunction
            inChosen <- hyp withMember (member z chosen)
            unionI withMember family z chosen inFamily inChosen
    setEquality context (selection a b t) (if takeLeft then a else b) forward backward
  where
    finish matches condition selected x z goal branch
        | matches = do
            equality <- known branch (equal x selected)
            membership <- known branch (member z x)
            rewriteSet branch z equality membership
        | otherwise = do
            positive <- known branch condition
            negative <- known branch (CNot condition)
            contradiction <- negationEliminationProof branch positive negative
            check branch (member z goal) >>= falsumEliminationProof branch contradiction

proveUniversePair :: Context -> ProofImport -> ProofImport -> Build Proof
proveUniversePair root emptyLemma bitLemma = introduceForalls root (replicate 3 TySet) \context -> do
    let e = CBound 2; a = CBound 1; b = CBound 0
        u = universe e
        indexSet = power (power empty)
        function = CLam TySet (selection (shift a) (shift b) (CBound 0))
        image = CApp (CApp (CIntrinsic Repl) indexSet) function
    assume context (member a u) \withA -> assume withA (member b u) \withBoth -> do
        zero <- use withBoth emptyLemma [e]
        closed <- axiom withBoth UnivOfPowerSetClosed [e,empty]
        once <- implicationEliminationProof withBoth closed zero
        closedAgain <- axiom withBoth UnivOfPowerSetClosed [e,power empty]
        domain <- implicationEliminationProof withBoth closedAgain once
        range <- forallIntroductionProof withBoth TySet \withIndex _ ->
            assume withIndex (member (CBound 0) indexSet) \withMembership -> do
                let a' = shift a; b' = shift b; u' = shift u; t = CBound 0
                    target = member (selection a' b' t) u'
                    branch pick extended = do
                        equality <- selectionEquation extended a' b' t pick >>= equalityReverseProof extended
                        membership <- hyp extended (member (if pick then a' else b') u')
                        rewriteElement extended u' equality membership
                selected <- byCases withMembership (equal t empty) target (branch True) (branch False)
                convert withMembership (member (CApp (shift function) t) u') selected
        closure <- axiom withBoth UnivOfReplacementClosed [e,indexSet,function]
        bounded <- implicationEliminationProof withBoth closure domain
            >>= \next -> implicationEliminationProof withBoth next range
        equality <- replacementPair withBoth a b function image indexSet
        rewriteElement withBoth u equality bounded
  where
    replacementPair context a b function image domain = do
        forward <- forallIntroductionProof context TySet \underZ _ ->
            assume underZ (member (CBound 0) (shift image)) \withMember -> do
                let z = CBound 0; a' = shift a; b' = shift b; f' = shift function
                membership <- hyp withMember (member z (shift image))
                witness <- characteristic withMember ReplacementCharacteristic [domain,f',z] False membership
                existsE withMember witness (member z (pair a' b')) \withWitness -> do
                    let z' = CBound 1; t = CBound 0; a'' = shift a'; b'' = shift b'; f'' = shift f'
                        branch pick extended = do
                            value <- selectionEquation extended a'' b'' t pick
                                >>= convert extended (equal (CApp f'' t) (if pick then a'' else b''))
                            original <- known extended (equal z' (CApp f'' t))
                            result <- composeEqualityProof extended original value
                            alternatives <- if pick then disjunctionLeftProof extended (equal z' b'') result
                                else disjunctionRightProof extended (equal z' a'') result
                            characteristic extended PairSetCharacteristic [a'',b'',z'] True alternatives
                    byCases withWitness (equal t empty) (member z' (pair a'' b'')) (branch True) (branch False)
        backward <- forallIntroductionProof context TySet \underZ _ ->
            assume underZ (member (CBound 0) (pair (shift a) (shift b))) \withMember -> do
                let z = CBound 0; a' = shift a; b' = shift b; f' = shift function
                membership <- hyp withMember (member z (pair a' b'))
                alternatives <- characteristic withMember PairSetCharacteristic [a',b',z] False membership
                cases withMember alternatives (member z (shift image))
                    (witnessBranch a' b' f' z domain True)
                    (witnessBranch a' b' f' z domain False)
        setEquality context image (pair a b) forward backward

    witnessBranch a b function z domain pick context = do
        let witness = if pick then empty else singleton empty
        inside <- if pick
            then emptySubset context (power empty) >>= characteristic context PowerSetCharacteristic [power empty,empty] True
            else do
                subset <- forallIntroductionProof context TySet \underX _ ->
                    assume underX (member (CBound 0) (singleton empty)) \withMember -> do
                        membership <- hyp withMember (member (CBound 0) (singleton empty))
                        equality <- singletonMember withMember (CBound 0) empty membership >>= equalityReverseProof withMember
                        emptyInPower <- emptySubset withMember empty >>= characteristic withMember PowerSetCharacteristic [empty,empty] True
                        rewriteElement withMember (power empty) equality emptyInPower
                characteristic context PowerSetCharacteristic [power empty,singleton empty] True subset
        condition <- if pick then reflexive context empty else do
            goal <- check context (equal (singleton empty) empty)
            negationIntroductionProof context goal \extended _ -> do
                opposite <- hyp extended (equal (singleton empty) empty) >>= equalityReverseProof extended
                unequal <- use extended bitLemma []
                negationEliminationProof extended opposite unequal
        value <- withProof context condition \extended -> selectionEquation extended a b witness pick
        valueAtWitness <- convert context (equal (CApp function witness) (if pick then a else b)) value
            >>= equalityReverseProof context
        original <- hyp context (equal z (if pick then a else b))
        equality <- composeEqualityProof context original valueAtWitness
        body <- conjunctionIntroductionProof context inside equality
        let existential = CExists TySet (CAnd (member (CBound 0) (shift domain))
                (equal (shift z) (CApp (shift function) (CBound 0))))
        proof <- existsI context existential witness body
        characteristic context ReplacementCharacteristic [domain,function,z] True proof

proveUniverseKuratowski :: Context -> ProofImport -> ProofImport -> Build Proof
proveUniverseKuratowski root definition pairLemma = introduceForalls root (replicate 3 TySet) \context -> do
    let e = CBound 2; a = CBound 1; b = CBound 0; u = universe e
        closePair current x y px py = do
            closure <- use current pairLemma [e,x,y]
            implicationEliminationProof current closure px
                >>= \next -> implicationEliminationProof current next py
    assume context (member a u) \withA -> assume withA (member b u) \withBoth -> do
        pa <- hyp withBoth (member a u)
        pb <- hyp withBoth (member b u)
        single <- closePair withBoth a a pa pa
        paired <- closePair withBoth a b pa pb
        code <- closePair withBoth (singleton a) (pair a b) single paired
        equation <- use withBoth definition [a,b] >>= equalityReverseProof withBoth
        rewriteElement withBoth u equation code

applyPremises :: Context -> Proof -> [Proof] -> Build Proof
applyPremises context = foldM (implicationEliminationProof context)

applyConditions :: Context -> Proof -> [Proof] -> Build Proof
applyConditions _ proof [] = pure proof
applyConditions context proof premises = do
    conjunction <- buildLeftAssociatedConjunction context premises
    implicationEliminationProof context proof conjunction

existsMany :: Context -> Term -> [Term] -> Proof -> Build Proof
existsMany context target witnesses proof = case witnesses of
    [] -> convert context target proof
    witness : remaining -> case target of
        CExists _ body -> do
            inner <- existsMany context (instantiateCanonical witness body) remaining proof
            existsI context target witness inner
        _ -> Left (ProofStructuralCompositionMismatch "datatype clause lost an existential binder")

eliminateWitnesses :: Context -> Int -> Proof -> Term -> (Context -> Build Proof) -> Build Proof
eliminateWitnesses context count proof target build
    | count == 0 = withProof context proof build
    | otherwise = case scopedCoreTerm (builtProofStatement proof) of
        CExists _ body -> existsE context proof target \extended -> do
            premise <- hyp extended body
            eliminateWitnesses extended (count - 1) premise (shift target) build
        _ -> Left (ProofStructuralCompositionMismatch "datatype clause has too few witnesses")

operatorMemberI
    :: Context -> NonEmpty Clause -> Term -> Term -> Natural -> [Term]
    -> [Proof] -> Proof -> Proof -> Build Proof
operatorMemberI context clauses recursive element index witnesses premises equality bounded = do
    (bound, operator, _) <- carrierTerms (contextWidth context) clauses
    alternatives <- traverse (clauseFormula (contextWidth context) recursive element) (toList clauses)
    selected <- maybe (Left (ProofStructuralCompositionMismatch "datatype clause index is absent")) pure (nth index alternatives)
    body <- buildLeftAssociatedConjunction context (premises <> [equality])
    existential <- existsMany context selected witnesses body
    disjunction <- introduceLeftAssociatedDisjunct context index alternatives existential
    both <- conjunctionIntroductionProof context bounded disjunction
    predicate <- operatorPredicate (contextWidth context) clauses recursive
    result <- characteristic context SeparationCharacteristic [bound,predicate,element] True both
    convert context (member element (CApp operator recursive)) result

eliminateOperatorMember
    :: Context -> NonEmpty Clause -> Term -> Term -> Proof -> Term
    -> (Context -> Natural -> Clause -> Build Proof) -> Build Proof
eliminateOperatorMember context clauses recursive element proof target build = do
    (bound, _, _) <- carrierTerms (contextWidth context) clauses
    predicate <- operatorPredicate (contextWidth context) clauses recursive
    alternatives <- traverse (clauseFormula (contextWidth context) recursive element) (toList clauses)
    separated <- characteristic context SeparationCharacteristic [bound,predicate,element] False proof
        >>= convert context (CAnd (member element bound) (disjunctions alternatives))
    withProof context separated \withSeparation -> do
        disjunction <- known withSeparation (disjunctions alternatives)
        goal <- check withSeparation target
        eliminateLeftAssociatedDisjunction withSeparation alternatives disjunction goal \withClause index clauseProof -> do
            clause <- maybe (Left (ProofStructuralCompositionMismatch "datatype case index is absent")) pure
                (nth index (toList clauses))
            eliminateWitnesses withClause (length (clausePremises clause)) clauseProof target
                (\withWitnesses -> build withWitnesses index clause)

-- Generated family facts quantify exactly the parameter context of their
-- root. Constructor/encoding facts remain parameter-free and use 'use'.
useFamily :: Context -> Context -> ProofImport -> [Term] -> Build Proof
useFamily root context lemma arguments =
    use context lemma (parametersAt (contextWidth root) context <> arguments)

weakenFrom :: Context -> Context -> Term -> Term
weakenFrom root context = shiftCanonical (fromIntegral (contextWidth context - contextWidth root)) 0

proveBoundedMono :: Context -> NonEmpty Clause -> Build Proof
proveBoundedMono root clauses = do
    bounded <- forallIntroductionProof root TySet \context _ -> do
        (bound, operator, _) <- carrierTerms (contextWidth context) clauses
        assume context (member (CBound 0) (CApp operator bound)) \withMember -> do
            let z = CBound 0
            predicate <- operatorPredicate (contextWidth context) clauses bound
            membership <- hyp withMember (member z (CApp operator bound))
            separated <- characteristic withMember SeparationCharacteristic [bound,predicate,z] False membership
            conjunctionLeftProof withMember separated
    monotone <- introduceForalls root [TySet,TySet] \context -> do
        (bound, _, _) <- carrierTerms (contextWidth context) clauses
        assume context (CAnd (subsetTerm (CBound 1) (CBound 0)) (subsetTerm (CBound 0) bound)) \withSubsets ->
            forallIntroductionProof withSubsets TySet \withElement _ -> do
                let x = CBound 2; y = CBound 1; z = CBound 0
                (_, operator, _) <- carrierTerms (contextWidth withElement) clauses
                assume withElement (member z (CApp operator x)) \withMember -> do
                    membership <- hyp withMember (member z (CApp operator x))
                    eliminateOperatorMember withMember clauses x z membership (member z (CApp operator y))
                        \withWitnesses index clause -> do
                            let count = length (clausePremises clause)
                                weaken = shiftCanonical (fromIntegral count) 0
                                x' = weaken x; y' = weaken y; z' = weaken z
                                terms = variables count
                            premises <- sequence
                                [case premise of
                                    FixedDomain domain -> known withWitnesses (member variable (domainAt (contextWidth withWitnesses) domain))
                                    Recursive -> do
                                        source <- known withWitnesses (member variable x')
                                        subset <- known withWitnesses (subsetTerm x' y')
                                        implication <- specialize withWitnesses subset [variable]
                                        implicationEliminationProof withWitnesses implication source
                                | (premise,variable) <- zip (clausePremises clause) terms]
                            constructor <- constructorTerm clause terms
                            equality <- known withWitnesses (equal z' constructor)
                            (witnessBound, _, _) <- carrierTerms (contextWidth withWitnesses) clauses
                            inBound <- known withWitnesses (member z' witnessBound)
                            operatorMemberI withWitnesses clauses y' z' index terms premises equality inBound
    proof <- conjunctionIntroductionProof root bounded monotone
    (bound, operator, _) <- carrierTerms (contextWidth root) clauses
    domain <- check root bound
    operation <- check root operator
    target <- Bifunctor.first (ProofSetLfpRuleFailed . fromString . show)
        (SetLfp.boundedMonoProposition (proofContextGlobalTyping root) domain operation)
    conversionProof root proof target

proveCarrierBound :: Context -> Term -> NonEmpty Clause -> ProofImport -> Build Proof
proveCarrierBound context carrier clauses definition = do
    (bound, operator, _) <- carrierTerms (contextWidth context) clauses
    domain <- check context bound
    operation <- check context operator
    bounded <- setLfpBoundProof context domain operation
    equation <- useFamily context context definition [] >>= equalityReverseProof context
    result <- rewrite context equation (CLam TySet (subsetTerm (CBound 0) (shift bound))) bounded
    convert context (subsetTerm carrier bound) result

proveCarrierFixed :: Context -> Term -> NonEmpty Clause -> ProofImport -> ProofImport -> Build Proof
proveCarrierFixed context carrier clauses definition monotonicity = do
    (bound, operator, _) <- carrierTerms (contextWidth context) clauses
    domain <- check context bound
    operation <- check context operator
    monotone <- useFamily context context monotonicity []
    fixed <- setLfpFixedProof context domain operation monotone
    equation <- useFamily context context definition []
    initial <- composeEqualityProof context equation fixed
    reverseEquation <- equalityReverseProof context equation
    unchanged <- reflexive context operator
    images <- equalityCongruenceApplicationProof context unchanged reverseEquation
    result <- composeEqualityProof context initial images
    convert context (equal carrier (CApp operator carrier)) result

proveIntroduction
    :: Context -> Term -> NonEmpty Clause -> Natural
    -> ProofImport -> ProofImport -> ProofImport -> Build Proof
proveIntroduction root carrier clauses index boundLemma fixedLemma guardLemma = do
    clause <- maybe (Left (ProofStructuralCompositionMismatch "datatype introduction index is absent")) pure
        (nth index (toList clauses))
    let count = length (clausePremises clause)
        terms = variables count
    introduceForalls root (replicate count TySet) \context -> do
        let d = weakenFrom root context carrier
        (bound, _, _) <- carrierTerms (contextWidth context) clauses
        assumePremises context (premiseTerms (contextWidth context) d clause terms) \withPremises -> do
            premises <- traverse (known withPremises) (premiseTerms (contextWidth context) d clause terms)
            guardPremises <- sequence
                [case premise of
                    FixedDomain _ -> pure proof
                    Recursive -> do
                        implication <- useFamily root withPremises boundLemma [variable]
                        implicationEliminationProof withPremises implication proof
                | (premise, variable, proof) <- zip3 (clausePremises clause) terms premises]
            guardProof <- useFamily root withPremises guardLemma terms
            bounded <- applyConditions withPremises guardProof guardPremises
            result <- constructorTerm clause terms
            bounded' <- convert withPremises (member result bound) bounded
            equality <- reflexive withPremises result
            inOperator <- operatorMemberI withPremises clauses d result index terms premises equality bounded'
            fixed <- useFamily root withPremises fixedLemma [] >>= equalityReverseProof withPremises
            rewriteSet withPremises result fixed inOperator

proveCases :: Context -> Term -> NonEmpty Clause -> ProofImport -> Build Proof
proveCases root carrier clauses fixedLemma =
    forallIntroductionProof root TySet \context _ -> do
        let d = weakenFrom root context carrier
        (bound, _, _) <- carrierTerms (contextWidth context) clauses
        assume context (member (CBound 0) d) \withMember -> do
            original <- hyp withMember (member (CBound 0) d)
            fixed <- useFamily root withMember fixedLemma []
            unfolded <- rewriteSet withMember (CBound 0) fixed original
            predicate <- operatorPredicate (contextWidth context) clauses d
            separated <- characteristic withMember SeparationCharacteristic [bound,predicate,CBound 0] False unfolded
            disjunction <- conjunctionRightProof withMember separated
            target <- disjunctions <$> traverse (clauseFormula (contextWidth context) d (CBound 0)) (toList clauses)
            convert withMember target disjunction

proveInduction
    :: Context -> Term -> NonEmpty Clause -> ProofImport -> ProofImport -> Build Proof
proveInduction root carrier clauses definition monotonicity =
    forallIntroductionProof root TySet \withSubset _ -> do
        closures <- traverse (introductionTarget (contextWidth withSubset) (CBound 0)) (toList clauses)
        assumePremises withSubset closures \withClosures ->
            forallIntroductionProof withClosures TySet \withElement _ -> do
                let d = weakenFrom root withElement carrier
                assume withElement (member (CBound 0) d) \context -> do
                    (bound, operator, fixedPoint) <- carrierTerms (contextWidth context) clauses
                    let subset = CBound 1; element = CBound 0
                        predicate = CLam TySet (member (CBound 0) (shift subset))
                        restricted = separate fixedPoint predicate
                    closure <- forallIntroductionProof context TySet \withStepElement _ -> do
                        let stepElement = CBound 0; restricted' = shift restricted; subset' = shift subset
                            stepOperator = shift operator
                        assume withStepElement (member stepElement (CApp stepOperator restricted')) \withStep -> do
                            membership <- hyp withStep (member stepElement (CApp stepOperator restricted'))
                            eliminateOperatorMember withStep clauses restricted' stepElement membership (member stepElement subset')
                                \withWitnesses _ clause -> do
                                    let count = length (clausePremises clause)
                                        weaken = shiftCanonical (fromIntegral count) 0
                                        s = weaken subset'; z = weaken stepElement
                                        restriction = weaken restricted'
                                        condition = CLam TySet (member (CBound 0) (shift s))
                                        terms = variables count
                                    (_, _, witnessFixedPoint) <- carrierTerms (contextWidth withWitnesses) clauses
                                    premises <- sequence
                                        [case premise of
                                            FixedDomain domain -> known withWitnesses (member variable (domainAt (contextWidth withWitnesses) domain))
                                            Recursive -> do
                                                original <- known withWitnesses (member variable restriction)
                                                separated <- characteristic withWitnesses SeparationCharacteristic
                                                    [witnessFixedPoint,condition,variable] False original
                                                conjunctionRightProof withWitnesses separated
                                                    >>= convert withWitnesses (member variable s)
                                        | (premise,variable) <- zip (clausePremises clause) terms]
                                    closureTarget <- introductionTarget (contextWidth withWitnesses) s clause
                                    sourceClosure <- known withWitnesses closureTarget
                                    specialized <- specialize withWitnesses sourceClosure terms
                                    closed <- applyConditions withWitnesses specialized premises
                                    constructor <- constructorTerm clause terms
                                    equation <- known withWitnesses (equal z constructor) >>= equalityReverseProof withWitnesses
                                    rewriteElement withWitnesses s equation closed
                    domain <- check context bound
                    operation <- check context operator
                    checkedPredicate <- check context predicate
                    checkedElement <- check context element
                    closureTarget <- Bifunctor.first (ProofSetLfpRuleFailed . fromString . show)
                        (SetLfp.inductionClosureProposition (proofContextGlobalTyping context)
                            domain operation checkedPredicate)
                    checkedClosure <- conversionProof context closure closureTarget
                    monotone <- useFamily root context monotonicity []
                    equation <- useFamily root context definition []
                    original <- hyp context (member element d)
                    inFixedPoint <- rewriteSet context element equation original
                    result <- setLfpInductProof context domain operation checkedPredicate checkedElement monotone inFixedPoint checkedClosure
                    convert context (member element subset) result

-- Apply set induction to the separation of the carrier by the motive. Each
-- recursive membership supplies both its original domain and its hypothesis.
provePredicateInduction
    :: Context -> Term -> NonEmpty Clause -> ProofImport -> [ProofImport] -> Build Proof
provePredicateInduction root carrier clauses induction introductions =
    forallIntroductionProof root (TyArrow TySet TyProp) \withPredicate _ -> do
        let d = shift carrier
            predicate = CBound 0
            restricted = separate d predicate
        cases' <- traverse (predicateCaseTarget (contextWidth withPredicate) predicate d) (toList clauses)
        assumePremises withPredicate cases' \withCases -> do
            closures <- for (zip (toList clauses) introductions) \(clause, introduction) -> do
                let count = length (clausePremises clause)
                    terms = variables count
                introduceForalls withCases (replicate count TySet) \context -> do
                    let d' = weakenFrom withCases context d
                        predicate' = weakenFrom withCases context predicate
                        restricted' = separate d' predicate'
                    assumePremises context (premiseTerms (contextWidth context) restricted' clause terms) \withPremises -> do
                        premises <- for (zip (clausePremises clause) terms) \(premise, variable) ->
                            case premise of
                                FixedDomain domain -> do
                                    guardProof <- known withPremises (member variable (domainAt (contextWidth context) domain))
                                    pure (guardProof, Nothing)
                                Recursive -> do
                                    original <- known withPremises (member variable restricted')
                                    separated <- characteristic withPremises SeparationCharacteristic [d',predicate',variable] False original
                                    guardProof <- conjunctionLeftProof withPremises separated
                                    hypothesis <- conjunctionRightProof withPremises separated
                                    pure (guardProof, Just hypothesis)
                        let guards = fst <$> premises
                            hypotheses = [proof | (_, Just proof) <- premises]
                        intro <- useFamily root withPremises introduction terms
                        inCarrier <- applyConditions withPremises intro guards
                        caseTarget <- predicateCaseTarget (contextWidth context) predicate' d' clause
                        propertyCase <- known withPremises caseTarget >>= \proof -> specialize withPremises proof terms
                        property <- applyConditions withPremises propertyCase (guards <> hypotheses)
                        both <- conjunctionIntroductionProof withPremises inCarrier property
                        result <- constructorTerm clause terms
                        characteristic withPremises SeparationCharacteristic [d',predicate',result] True both
            setInduction <- useFamily root withCases induction [restricted]
            subset <- applyConditions withCases setInduction closures
            withProof withCases subset \withSubset ->
                forallIntroductionProof withSubset TySet \context _ -> do
                    let d' = shift d
                        predicate' = shift predicate
                        restricted' = shift restricted
                        element = CBound 0
                    assume context (member element d') \withMember -> do
                        original <- hyp withMember (member element d')
                        subset' <- known withMember (subsetTerm d' restricted')
                        implication <- specialize withMember subset' [element]
                        inSeparation <- implicationEliminationProof withMember implication original
                        separated <- characteristic withMember SeparationCharacteristic [d',predicate',element] False inSeparation
                        conjunctionRightProof withMember separated

proveDomainBound :: Context -> NonEmpty Clause -> Term -> Build Proof
proveDomainBound context clauses domain = do
    (_, membership) <- foldM insert (empty, Nothing) (empty : fixedDomains (contextWidth context) clauses)
    inSeed <- maybe (Left (ProofStructuralCompositionMismatch "datatype domain is absent from its universe seed")) pure membership
    let seed = seedTerm (contextWidth context) clauses
    seedInUniverse <- axiom context UnivOfContains [seed]
    transitive <- axiom context UnivOfTransitive [seed,seed]
    subset <- implicationEliminationProof context transitive seedInUniverse
    implication <- specialize context subset [domain]
    domainInUniverse <- implicationEliminationProof context implication inSeed
    domainTransitive <- axiom context UnivOfTransitive [seed,domain]
    implicationEliminationProof context domainTransitive domainInUniverse
  where
    insert (set, previous) element = do
        let family = pair (singleton element) set
            next = canonicalSetInsert element set
        membership <- if element == domain
            then do
                inFamily <- pairLeft context (singleton element) set
                inSingleton <- pairLeft context element element
                Just <$> unionI context family domain (singleton element) inFamily inSingleton
            else traverse (\inSet -> do
                inFamily <- pairRight context (singleton element) set
                unionI context family domain set inFamily inSet) previous
        pure (next, membership)

data UniverseProofs = UniverseProofs
    { universeEmptyProof :: !ProofImport
    , universePairProof :: !ProofImport
    , universeKuratowskiProof :: !ProofImport
    }

closeKuratowski :: Context -> ProofImport -> Term -> Term -> Term -> Proof -> Proof -> Build Proof
closeKuratowski context lemma seed a b pa pb = do
    closure <- use context lemma [seed,a,b]
    applyPremises context closure [pa,pb]

tupleClosed :: Context -> ObjectId -> Term -> UniverseProofs -> [(Term, Proof)] -> Build Proof
tupleClosed context k seed lemmas = \case
    [] -> use context (universeEmptyProof lemmas) [seed]
    (element, membership) : rest -> do
        remaining <- tupleClosed context k seed lemmas rest
        closeKuratowski context (universeKuratowskiProof lemmas) seed
            element (tuple k (fst <$> rest)) membership remaining

proveGuard
    :: Context -> ObjectId -> NonEmpty Clause -> Natural -> ProofImport
    -> UniverseProofs -> [(Term, ProofImport)] -> Build Proof
proveGuard root k clauses index definition lemmas domains = do
    clause <- maybe (Left (ProofStructuralCompositionMismatch "datatype guard index is absent")) pure
        (nth index (toList clauses))
    let count = length (clausePremises clause)
        terms = variables count
        digits = tagDigits (fromIntegral (NonEmpty.length clauses)) index
    introduceForalls root (replicate count TySet) \context -> do
        let seed = seedTerm (contextWidth context) clauses
            bound = universe seed
        assumePremises context (premiseTerms (contextWidth context) bound clause terms) \withPremises -> do
            memberships <- sequence
                [case premise of
                    Recursive -> known withPremises (member variable bound)
                    FixedDomain domain -> do
                        let set = domainAt (contextWidth context) domain
                        source <- known withPremises (member variable set)
                        imported <- maybe (Left (ProofStructuralCompositionMismatch "datatype guard lost its domain bound")) pure
                            (List.lookup (domainAt (contextWidth root) domain) domains)
                        implication <- useFamily root withPremises imported [variable]
                        implicationEliminationProof withPremises implication source
                | (premise,variable) <- zip (clausePremises clause) terms]
            arguments <- argumentTerms clause terms
            argumentProofs <- traverse
                (\slot -> maybe (Left (ProofStructuralCompositionMismatch "datatype argument lost its universe proof")) pure
                    (nth slot memberships)) (clauseArgumentSlots clause)
            payload <- tupleClosed withPremises k seed lemmas (zip arguments argumentProofs)
            bitProofs <- traverse (\digit -> if digit == empty
                then use withPremises (universeEmptyProof lemmas) [seed]
                else do
                    zero <- use withPremises (universeEmptyProof lemmas) [seed]
                    closed <- use withPremises (universePairProof lemmas) [seed,empty,empty]
                    applyPremises withPremises closed [zero,zero]) digits
            tag <- tupleClosed withPremises k seed lemmas (zip digits bitProofs)
            code <- closeKuratowski withPremises (universeKuratowskiProof lemmas) seed
                (tuple k digits) (tuple k arguments) tag payload
            equation <- use withPremises definition arguments >>= equalityReverseProof withPremises
            rewriteElement withPremises bound equation code

expandConstructorEquality :: Context -> ProofImport -> [Term] -> ProofImport -> [Term] -> Proof -> Build Proof
expandConstructorEquality context left arguments right otherArguments original = do
    leftEquation <- use context left arguments >>= equalityReverseProof context
    rightEquation <- use context right otherArguments
    composeEqualityProof context leftEquation original
        >>= \next -> composeEqualityProof context next rightEquation

injectKuratowski :: Context -> ProofImport -> Term -> Term -> Term -> Term -> Proof -> Build Proof
injectKuratowski context lemma a b c d equality = do
    injection <- use context lemma [a,b,c,d]
    implicationEliminationProof context injection equality

proveInjective
    :: Context -> ObjectId -> Natural -> Natural -> Clause -> ProofImport -> ProofImport -> Build Proof
proveInjective root k constructorCount index clause definition injection = do
    let arity = length (clauseArgumentSlots clause)
        terms = variables (2 * arity)
        left = take arity terms; right = drop arity terms
        app = foldl' CApp (CGlobal (clauseConstructor clause))
        tag = tuple k (tagDigits constructorCount index)
    introduceForalls root (replicate (2 * arity) TySet) \context ->
        assume context (equal (app left) (app right)) \withEquality -> do
            original <- hyp withEquality (equal (app left) (app right))
            expanded <- expandConstructorEquality withEquality definition left definition right original
            components <- injectKuratowski withEquality injection tag (tuple k left) tag (tuple k right) expanded
            payload <- conjunctionRightProof withEquality components
            collect withEquality [] left right payload
  where
    collect context obtained [] [] _ = known context (conjunctions obtained)
    collect context obtained (a : rest) (b : others) equality = do
        components <- injectKuratowski context injection a (tuple k rest) b (tuple k others) equality
        withProof context components \extended -> do
            remaining <- known extended (equal (tuple k rest) (tuple k others))
            collect extended (obtained <> [equal a b]) rest others remaining
    collect _ _ _ _ _ = Left (ProofStructuralCompositionMismatch "datatype injection changed tuple arity")

proveDistinct
    :: Context -> ObjectId -> Natural
    -> (Natural, Clause, ProofImport) -> (Natural, Clause, ProofImport)
    -> ProofImport -> ProofImport -> Build Proof
proveDistinct root k count (leftIndex,left,leftDefinition) (rightIndex,right,rightDefinition) injection inequality = do
    let leftArity = length (clauseArgumentSlots left)
        rightArity = length (clauseArgumentSlots right)
        terms = variables (leftArity + rightArity)
        leftArguments = take leftArity terms; rightArguments = drop leftArity terms
        leftValue = foldl' CApp (CGlobal (clauseConstructor left)) leftArguments
        rightValue = foldl' CApp (CGlobal (clauseConstructor right)) rightArguments
        leftDigits = tagDigits count leftIndex; rightDigits = tagDigits count rightIndex
    introduceForalls root (replicate (leftArity + rightArity) TySet) \context -> do
        target <- check context (equal leftValue rightValue)
        negationIntroductionProof context target \withEquality _ -> do
            original <- hyp withEquality (equal leftValue rightValue)
            expanded <- expandConstructorEquality withEquality leftDefinition leftArguments rightDefinition rightArguments original
            components <- injectKuratowski withEquality injection (tuple k leftDigits) (tuple k leftArguments)
                (tuple k rightDigits) (tuple k rightArguments) expanded
            tags <- conjunctionLeftProof withEquality components
            different withEquality leftDigits rightDigits tags
  where
    different context (a : rest) (b : others) equality = do
        components <- injectKuratowski context injection a (tuple k rest) b (tuple k others) equality
        if a == b
            then conjunctionRightProof context components >>= different context rest others
            else do
                bits <- conjunctionLeftProof context components
                directed <- if a == empty then pure bits else equalityReverseProof context bits
                unequal <- use context inequality []
                negationEliminationProof context directed unequal
    different _ _ _ _ = Left (ProofStructuralCompositionMismatch "datatype constructor tags are not distinct")
