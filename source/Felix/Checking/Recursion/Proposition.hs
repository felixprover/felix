{-# LANGUAGE NoImplicitPrelude #-}

-- | Prop recursion is Set recursion through a truth-value representation.
-- No positivity condition is needed: branches may use decoded values freely.
module Felix.Checking.Recursion.Proposition
    ( encode
    , decode
    , encodeBranch
    , decodedEvaluator
    , proveDecodeEncode
    , proveDecodedEquation
    , proveDecodedDefault
    ) where

import Base hiding (Empty, empty)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Foundation (FoundationAxiomTag(..))
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Kernel.Proof
import Felix.Checking.Recursion.Construction qualified as Recursion

type Term = CanonicalTerm ObjectId
type Context = ProofContext ObjectId
type Proof = BuiltProof ObjectId
type Build = Either KernelProofBuildError

encode :: Term -> Term
encode proposition = CApp (CApp (CIntrinsic Sep) singleton) (CLam TySet (shift proposition))
  where
    singleton = CApp (CApp (CIntrinsic PairSet) empty) empty

decode :: Term -> Term
decode = CApp (CApp (CIntrinsic Member) empty)

decodedEvaluator :: Term -> Term
decodedEvaluator evaluate = CLam TySet (decode (CApp (shift evaluate) (CBound 0)))

encodeBranch :: Datatype.Clause -> Term -> Term
encodeBranch clause branch = foldr (const (CLam TySet)) (encode result) [1 .. count]
  where
    fields = length (Datatype.clauseArgumentSlots clause)
    recursive = length (Recursion.recursiveSlots clause)
    count = fields + recursive
    arguments = (CBound . fromIntegral <$> reverse [recursive .. count - 1])
        <> (decode . CBound . fromIntegral <$> reverse [0 .. recursive - 1])
    result = foldl' CApp (shiftCanonical (fromIntegral count) 0 branch) arguments

proveDecodeEncode :: Context -> Term -> Build Proof
proveDecodeEncode context proposition = do
    let singleton = CApp (CApp (CIntrinsic PairSet) empty) empty
        inSingleton = CApp (CApp (CIntrinsic Member) empty) singleton
        predicate = CLam TySet (shift proposition)
    pair <- axiom context PairSetCharacteristic [empty,empty,empty]
    reflexive <- scopedTerm context empty >>= equalityReflexivityProof context
    alternative <- disjunctionLeftProof context (CEq TySet empty empty) reflexive
    membership <- equalityReverseProof context pair >>= \backwards -> equalityModusPonensProof context backwards alternative
    separation <- axiom context SeparationCharacteristic [singleton,predicate,empty]
    normalized <- scopedTerm context (CEq TyProp (decode (encode proposition)) (CAnd inSingleton proposition))
        >>= conversionProof context separation
    decoded <- scopedTerm context (decode (encode proposition))
    forward <- implicationIntroductionProof context decoded \withDecoded hypothesis -> do
        separated <- equalityModusPonensProof withDecoded (weakenProofHypotheses 1 normalized) hypothesis
        conjunctionRightProof withDecoded separated
    statement <- scopedTerm context proposition
    backward <- implicationIntroductionProof context statement \withProposition hypothesis -> do
        both <- conjunctionIntroductionProof withProposition (weakenProofHypotheses 1 membership) hypothesis
        reversed <- equalityReverseProof withProposition (weakenProofHypotheses 1 normalized)
        equalityModusPonensProof withProposition reversed both
    extensionality <- axiom context PropositionalExtensionality [decode (encode proposition),proposition]
    implicationEliminationProof context extensionality forward
        >>= \proof -> implicationEliminationProof context proof backward

-- The supplied Set equation is the one for the encoded branch. Congruence
-- transports it through decoding, and separation removes the representation.
proveDecodedEquation
    :: Context -> Datatype.Clause -> Term -> Term -> [Term] -> Proof -> Build Proof
proveDecodedEquation context clause branch setEvaluator terms setEquation = do
    constructor <- Datatype.constructorTerm clause terms
    let evaluate = decodedEvaluator setEvaluator
    result <- Recursion.branchValue clause branch evaluate terms
    decoder <- scopedTerm context (CLam TySet (decode (CBound 0))) >>= equalityReflexivityProof context
    congruence <- equalityCongruenceApplicationProof context decoder setEquation
    normalized <- scopedTerm context (CEq TyProp (CApp evaluate constructor) (decode (encode result)))
        >>= conversionProof context congruence
    decoded <- proveDecodeEncode context result
    composeEqualityProof context normalized decoded

proveDecodedDefault :: Context -> Term -> Proof -> Build Proof
proveDecodedDefault context value setDefault = do
    decoder <- scopedTerm context (CLam TySet (decode (CBound 0))) >>= equalityReflexivityProof context
    congruence <- equalityCongruenceApplicationProof context decoder setDefault
    normalized <- scopedTerm context (CEq TyProp (decode value) (decode empty)) >>= conversionProof context congruence
    emptyLaw <- axiom context EmptyCharacteristic [empty]
    composeEqualityProof context normalized emptyLaw

empty :: Term
empty = CIntrinsic Empty

shift :: Term -> Term
shift = shiftCanonical 1 0

axiom :: Context -> FoundationAxiomTag -> [Term] -> Build Proof
axiom context tag arguments = traverse (scopedTerm context) arguments >>= foundationInstanceProof context tag
