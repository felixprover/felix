{-# LANGUAGE NoImplicitPrelude #-}

-- | Specialize one owned constructor equation. Unstored fields are witnesses
-- of one joint guard; neither endpoint can depend on them.
module Felix.Checking.Recursion.Application
    ( RecursiveApplication
    , applicationBinding, applicationEquation, applicationGuard, applicationEquality
    , applicationArguments, applicationCase, applicationWitnessCount
    , applicationBranchArguments
    , matchRecursiveApplication
    , applyRecursiveEquation
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Identity
import Felix.Checking.Kernel.Derivation (ImportIx, hypothesisIx)
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Recursion.Interface
import Felix.Checking.Recursion.Construction qualified as Construction
import Felix.Checking.Semantic

import Control.Monad (foldM, unless)
import Control.Monad.Except qualified as Except
import Control.Monad.State.Strict qualified as State
import Data.List qualified as List
import Data.Word (Word)
import Numeric.Natural (Natural)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text

type Term = CanonicalTerm ObjectId

data RecursiveApplication = RecursiveApplication
    { applicationBinding :: !GlobalBindingRef
    , applicationEquation :: !(SemanticFactOccurrenceFingerprint, FrozenCheckedCore ObjectId)
    , applicationGuard :: !(ScopedCheckedCore ObjectId)
    , applicationEquality :: !(ScopedCheckedCore ObjectId)
    -- Universal arguments in source order, in the innermost witness scope.
    , applicationArguments :: ![Term]
    , applicationCase :: !Natural
    , applicationBranchArguments :: ![Term]
    , applicationWitnessResults :: ![ScopedCheckedCore ObjectId]
    , applicationHasGuard :: !Bool
    }

applicationWitnessCount :: RecursiveApplication -> Int
applicationWitnessCount = length . applicationWitnessResults

-- All structural work is charged, including failed matching and copying. The
-- host owns this account and the separate conversion pool used by replay.
matchRecursiveApplication
    :: Word -> Proof.ProofContext ObjectId -> CheckedRecursiveDefinition
    -> ScopedCheckedCore ObjectId
    -> (Either (CountedCoreFailure Text) (Maybe RecursiveApplication), Word)
matchRecursiveApplication available context definition call =
    State.runState (Except.runExceptT match) available
  where
    invalid = Except.throwError . CountedCoreOperationFailed
    charge = do
        remaining <- State.get
        if remaining == 0 then Except.throwError CountedCoreStructuralWorkExhausted
            else State.put (remaining - 1)
    core describe operation = do
        remaining <- State.get
        let (result,balance) = operation remaining
        State.put balance
        either (Except.throwError . fmap describe) pure result
    checked types term = core (Text.pack . show)
        (\work -> countedCheckScopedCanonicalCore (Proof.proofContextGlobalTyping context) work types term)
    spine = go []
      where
        go arguments term = charge >> case term of
            CApp function argument -> go (argument:arguments) function
            _ -> pure (term,arguments)
    match = do
        sameScope <- core absurd (\work -> countedCoreTypeListIdentity work
            (Proof.proofContextTypes context) (scopedCoreContext call))
        unless sameScope (invalid "a recursive application changed scope")
        (headTerm,arguments) <- spine (scopedCoreTerm call)
        let count = recursiveParameterCount definition
        if headTerm /= CGlobal (recursiveObject definition) || length arguments /= count + 1
            then pure Nothing else case splitAt count arguments of
                (parameters,[argument]) -> do
                    (constructor,fields) <- spine argument
                    select parameters constructor fields
                        (zip [0..] (List.zip3 (toList (recursiveClauses definition))
                            (toList (recursiveDefinitionEquations (recursiveDescriptor definition)))
                            (toList (recursiveEquationTargets definition))))
                _ -> invalid "a recursive call lost its structural argument"
    select _ _ _ [] = pure Nothing
    select parameters constructor fields ((caseIndex,(clause,(_,fingerprint),target)):rest) = do
        charge
        if constructor /= CGlobal (Datatype.clauseConstructor clause)
            then select parameters constructor fields rest
            else do
                unless (length fields == length (Datatype.clauseArgumentSlots clause))
                    (invalid "a checked constructor has the wrong arity")
                let fieldCount = length (Datatype.clausePremises clause)
                    known = Map.fromList (zip (Datatype.clauseArgumentSlots clause) fields)
                    unknown :: [Natural]
                    unknown = [fromIntegral index | index <- [0 .. fieldCount - 1], Map.notMember (fromIntegral index) known]
                    witnesses = fromIntegral (length unknown)
                    witnessMap = Map.fromList (zip unknown (CBound . fromIntegral <$> reverse [0 .. length unknown - 1]))
                shiftedParameters <- traverse (weaken witnesses) parameters
                shiftedFields <- for [0 .. fieldCount - 1] \index -> do
                    charge
                    case Map.lookup (fromIntegral index) known of
                        Just term -> weaken witnesses term
                        Nothing -> maybe (invalid "an unstored field lost its witness") pure
                            (Map.lookup (fromIntegral index) witnessMap)
                let actuals = shiftedParameters <> shiftedFields
                    prefix = Map.fromList (zip [0..] (reverse actuals))
                body <- stripForalls (length actuals) (frozenCoreTerm target)
                instantiated <- core (Text.pack . show) (\work -> countedInstantiateCanonicalSlots
                    work (fromIntegral (length actuals)) prefix body)
                let (hasGuard,condition,equality) = case instantiated of
                        CImp premise result -> (True,premise,result)
                        result -> (False,CTruth,result)
                endpoint <- core (Text.pack . show) (\work -> countedInstantiateCanonicalSlots work witnesses Map.empty equality)
                case endpoint of
                    CEq ty left _ | ty == recursiveResultType definition -> do
                        same <- core absurd (\work -> countedCanonicalIdentity work left (scopedCoreTerm call))
                        unless same (invalid "an owned equation matched a different call")
                    _ -> invalid "an owned equation has no applicable equality"
                let types = Proof.proofContextTypes context
                obligation <- checked types (foldr CExists condition (replicate (length unknown) TySet))
                result <- checked types endpoint
                recursive <- for (Construction.recursiveSlots clause) \slot -> do
                    child <- maybe (invalid "a recursive field is not stored by its constructor") pure (Map.lookup slot known)
                    -- Copying the fixed arguments belongs to this application,
                    -- even when several branch arguments denote the same call.
                    core absurd (\work -> countedShiftCanonical work 0 0
                        (foldl' CApp (CGlobal (recursiveObject definition)) (parameters <> [child])))
                nested <- for [1 .. length unknown] \depth -> do
                    term <- weaken (fromIntegral depth) endpoint
                    checked (replicate depth TySet <> types) term
                pure (Just (RecursiveApplication (recursiveBinding definition) (fingerprint,target)
                    obligation result actuals caseIndex (parameters <> fields <> recursive) nested hasGuard))
    weaken depth term = core absurd (\work -> countedShiftCanonical work depth 0 term)
    stripForalls 0 term = pure term
    stripForalls count term = charge >> case term of
        CForall TySet body -> stripForalls (count - 1) body
        _ -> invalid "an owned equation lost its universal prefix"

-- The guard is already proved by the host. Elimination opens each witness
-- locally and closes it before returning the equality in the original scope.
applyRecursiveEquation
    :: Proof.ProofContext ObjectId -> ImportIx -> RecursiveApplication
    -> Proof.BuiltProof ObjectId -> Proof.CountedProof ObjectId (Proof.BuiltProof ObjectId)
applyRecursiveEquation context index application guardProof =
    eliminate context guardProof (applicationEquality application) (applicationWitnessResults application)
  where
    eliminate current evidence result remaining = case remaining of
        [] -> do
            imported <- Proof.countedImportedProof current index (snd (applicationEquation application))
            law <- foldM (\proof term -> Proof.countedScopedTerm current term
                >>= Proof.countedForallEliminationProof current proof) imported (applicationArguments application)
            applied <- if applicationHasGuard application
                then Proof.countedImplicationEliminationProof current law evidence else pure law
            Proof.countedConversionProof current applied result
        nestedResult:rest -> case scopedCoreTerm (Proof.builtProofStatement evidence) of
            CExists TySet body -> do
                (nested,_) <- Proof.countedExtendProofContextBinder current TySet
                premise <- Proof.countedScopedTerm nested body
                withWitness <- Proof.countedExtendProofContextHypothesis nested premise
                assumption <- Proof.countedIndexedHypothesisProof withWitness (hypothesisIx 0)
                branch <- eliminate withWitness assumption nestedResult rest
                Proof.countedPreparedExistentialEliminationProof current TySet body evidence result branch
            _ -> impossible "a checked recursive guard lost its existential prefix"
