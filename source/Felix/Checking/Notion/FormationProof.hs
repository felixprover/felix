{-# LANGUAGE NoImplicitPrelude #-}

-- | Interpret one search-produced recipe under its consumer's proof context.
module Felix.Checking.Notion.FormationProof
    ( defaultFormationProofConversionPool
    , materializeFormationProof, materializeFormationProofWithDiagnostics
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Foundation (FoundationAxiomTag(..))
import Felix.Checking.Kernel.Conversion (ConversionPool, conversionPool, conversionPoolAmount)
import Felix.Checking.Kernel.Derivation
    ( DerivationImportJudgement
    , HypothesisIx
    , ImportIx
    , derivationImportStatement
    , hypothesisIx
    , hypothesisIxValue
    , importIxValue
    )
import Felix.Checking.Kernel.Proof
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.Diagnostics qualified as Diagnostics
import Felix.Checking.Notion.Formation
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Notion.SuppliedUniversal

import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Numeric.Natural (Natural)
import Data.Word (Word)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Set qualified as Set
import Data.Map.Strict qualified as Map
import Data.List qualified as List


-- Conversion calls share this pool across one proof interpretation, separately
-- from the per-call limit. Entry checks, proof construction and fresh replay
-- also contribute to total runtime; see benchmark/readme.md#work-budgets.
defaultFormationProofConversionPool :: ConversionPool
defaultFormationProofConversionPool = conversionPool 20000000

type FormationBuild value =
    Except.ExceptT Notion.FormationProofError (State FormationBuildState) value

-- Costs describe the emitted tree, including references to shared hypotheses
-- and the implication nodes which bind them. They never unfold a recipe DAG.
data EmittedProof = EmittedProof
    { emittedProof :: !(BuiltProof ObjectId)
    , emittedNodes :: !Natural
    , emittedDepth :: !Natural
    }

statement :: EmittedProof -> ScopedCheckedCore ObjectId
statement = builtProofStatement . emittedProof

-- Entry slots are local to this one context/fingerprint association. They only
-- avoid readmitting a selected source used along several conjunction paths.
data FormationBuildState = FormationBuildState
    { remainingPool :: !ConversionPool
    , admittedHypotheses :: !(Set HypothesisIx)
    , admittedImports :: !(Set ImportIx)
    , constructedNodes :: !Natural
    , constructionWork :: !Natural
    , preparedGraph :: !Bool
    , constructedDepth :: !Natural
    }

materializeFormationProof
    :: ConversionPool
    -> ProofContext ObjectId
    -> MaterializedFormationEvidence origin
    -> Vector (DerivationImportJudgement ObjectId)
    -> (Either Notion.FormationProofError (BuiltProof ObjectId), ConversionPool)
materializeFormationProof pool context evidence imports =
    let (result, remaining, _) = materializeFormationProofWithDiagnostics pool context evidence imports
    in (result, remaining)

materializeFormationProofWithDiagnostics
    :: ConversionPool -> ProofContext ObjectId -> MaterializedFormationEvidence origin
    -> Vector (DerivationImportJudgement ObjectId)
    -> (Either Notion.FormationProofError (BuiltProof ObjectId), ConversionPool, Diagnostics.Measurement)
materializeFormationProofWithDiagnostics pool rootContext
        (MaterializedFormationEvidence hypotheses fingerprints (FormationDerivationRecipe nodes root) (maximumNodes, maximumDepth)) imports =
    let (result, finalState) = State.runState (Except.runExceptT interpret)
            (FormationBuildState pool Set.empty Set.empty 0 0 False 0)
        selectedCount = if preparedGraph finalState then fromIntegral (Vector.length nodes) else 0
        selectedWork = if preparedGraph finalState then graphWork else 0
        measured = Diagnostics.emptyMeasurement
            { Diagnostics.measuredDiagnostics =
                Diagnostics.countOperation Diagnostics.SelectedProofNode selectedCount
                (Diagnostics.countOperation Diagnostics.EmittedNode (constructedNodes finalState)
                (Diagnostics.countCoreWork Diagnostics.Proof (constructionWork finalState)
                (Diagnostics.countPhaseWork Diagnostics.Proof
                    (constructedNodes finalState + selectedWork + constructionWork finalState) Diagnostics.emptyDiagnostics)))
            , Diagnostics.limitHighWater = Map.fromList
                [ ("emitted-nodes.used", max (constructedNodes finalState) (either (const 0) emittedNodes result))
                , ("emitted-nodes.cap", maximumNodes)
                , ("emitted-depth.used", constructedDepth finalState)
                , ("emitted-depth.cap", maximumDepth)
                , ("proof-conversion.used", fromIntegral (conversionPoolAmount pool - conversionPoolAmount (remainingPool finalState)))
                , ("proof-conversion.cap", fromIntegral (conversionPoolAmount pool)) ]
                <> case result of
                    Left (Notion.FormationProofDerivationLimitExceeded (Notion.FormationDerivationNodeLimitExceeded cap actual)) ->
                        Map.singleton "emitted-nodes.rejected" (actual - cap)
                    Left (Notion.FormationProofDerivationLimitExceeded (Notion.FormationDerivationDepthLimitExceeded cap actual)) ->
                        Map.singleton "emitted-depth.rejected" (actual - cap)
                    Left (Notion.FormationProofKernelError ProofConversionLimitExhausted{}) ->
                        Map.singleton "proof-conversion.rejected" 1
                    _ -> Map.empty }
    in (emittedProof <$> result, remainingPool finalState, measured)
  where
    expectedHypotheses = fromIntegral (Vector.length hypotheses)
    actualHypotheses = proofContextHypotheses rootContext

    interpret = do
        unless (expectedHypotheses == fromIntegral (length actualHypotheses))
            (Except.throwE
                (Notion.FormationProofHypothesisCountMismatch
                    expectedHypotheses (fromIntegral (length actualHypotheses))))
        for_ (zip3 [0..] (toList hypotheses) actualHypotheses)
            \(ordinal, MaterializedNotionHypothesis expected _origin, actual) -> do
                same <- core (\work -> countedScopedCoreIdentity work expected actual)
                unless same
                    (Except.throwE
                        (Notion.FormationProofHypothesisMismatch
                            (hypothesisIx ordinal)))
        unless (Vector.length fingerprints == Vector.length imports)
            (Except.throwE
                (Notion.FormationProofImportCountMismatch
                    (fromIntegral (Vector.length fingerprints))
                    (fromIntegral (Vector.length imports))))
        graphWork `seq` State.modify' (\state -> state {preparedGraph = True})
        buildScope rootContext 0 Map.empty root

    kernel :: CountedProof ObjectId value -> FormationBuild value
    kernel operation = do
        poolBefore <- State.gets remainingPool
        let (result, remaining, poolAfter) = runCountedProof maxBound poolBefore operation
            used = fromIntegral (maxBound - remaining)
                + fromIntegral (conversionPoolAmount poolBefore - conversionPoolAmount poolAfter)
        State.modify' (\state -> state
            {remainingPool = poolAfter, constructionWork = constructionWork state + used})
        case result of
            Right value -> pure value
            Left (CountedCoreOperationFailed problem) -> Except.throwE (Notion.FormationProofKernelError problem)
            Left CountedCoreStructuralWorkExhausted -> impossible "formation proof operation exceeded the measurement range"

    core :: (Word -> (Either (CountedCoreFailure Void) value, Word)) -> FormationBuild value
    core operation = do
        let (result, remaining) = operation maxBound
        State.modify' (\state -> state {constructionWork = constructionWork state + fromIntegral (maxBound - remaining)})
        case result of
            Right value -> pure value
            Left (CountedCoreOperationFailed problem) -> absurd problem
            Left CountedCoreStructuralWorkExhausted -> impossible "formation Core operation exceeded the measurement range"

    sameCore left right = core (\work -> countedScopedCoreIdentity work left right)

    emit children result = do
        constructed <- State.gets ((+ 1) . constructedNodes)
        let count = 1 + sum (emittedNodes <$> children)
            depth = case children of
                [] -> 0
                _ -> 1 + maximum (emittedDepth <$> children)
            exhausted = Except.throwE . Notion.FormationProofDerivationLimitExceeded
        when (max count constructed > maximumNodes)
            (exhausted (Notion.FormationDerivationNodeLimitExceeded maximumNodes (max count constructed)))
        when (depth > maximumDepth)
            (exhausted (Notion.FormationDerivationDepthLimitExceeded maximumDepth depth))
        State.modify' (\state -> state {constructedNodes = constructed,
            constructedDepth = max depth (constructedDepth state)})
        proof <- kernel result
        pure (EmittedProof proof count depth)

    -- Count edges in the graph, never paths through an unfolded proof. A
    -- multiply used non-leaf becomes (\h -> body) rhs in the kernel calculus.
    uses = Vector.foldl' (\counts node -> foldl'
        (\counts' child -> Map.insertWith (+) child (1 :: Int) counts')
        counts (formationRecipeChildren node)) Map.empty nodes
    graphWork = fromIntegral (Vector.length nodes) + fromIntegral (sum (Map.elems uses))
    -- Sharing cannot hoist a child proof past its binder or assumption.
    -- Walk only this scope's DAG; each introduction starts its own walk.
    scopeSharedNodes scopeRoot = visit Set.empty [] [scopeRoot]
      where
        visit _ shared [] = pure (List.sort shared)
        visit seen shared (reference@(FormationRecipeId ordinal):rest)
            | Set.member reference seen = visit seen shared rest
            | otherwise = do
                State.modify' (\state -> state {constructionWork = constructionWork state + 1})
                node <- maybe (Except.throwE Notion.FormationProofInvalidRecipe) pure (nodes Vector.!? ordinal)
                let children = case node of
                        FormationForallIntroduction{} -> []
                        FormationImplicationIntroduction{} -> []
                        _ -> formationRecipeChildren node
                    reusable = case node of
                        FormationUseHypothesis{} -> False
                        FormationUseImport{} -> False
                        FormationBoundHypothesis -> False
                        _ -> Map.findWithDefault 0 reference uses > 1
                visit (Set.insert reference seen) (if reusable then reference:shared else shared) (children <> rest)

    buildScope active depth bindings scopeRoot = do
        shared <- scopeSharedNodes scopeRoot
        buildShared active depth bindings scopeRoot shared
    buildShared active depth bindings scopeRoot = \case
        [] -> build active depth bindings scopeRoot
        reference : rest | Map.member reference bindings ->
            buildShared active depth bindings scopeRoot rest
        reference : rest -> do
            value <- build active depth bindings reference
            let premise = statement value
            extended <- kernel (countedExtendProofContextHypothesis active premise)
            body <- buildShared extended (depth + 1)
                (Map.insert reference depth bindings) scopeRoot rest
            abstraction <- emit [body] (countedComposeImplicationProof active premise (emittedProof body))
            emit [abstraction, value] (countedImplicationEliminationProof active (emittedProof abstraction) (emittedProof value))

    checkedTerm active = kernel . countedScopedTerm active

    build active depth bindings reference = case Map.lookup reference bindings of
        Just level -> emit [] (countedIndexedHypothesisProof active (hypothesisIx (depth - level - 1)))
        Nothing -> do
            let FormationRecipeId ordinal = reference
            node <- maybe (Except.throwE Notion.FormationProofInvalidRecipe) pure
                (nodes Vector.!? ordinal)
            buildNode active depth bindings node

    buildNode context depth bindings = \case
        FormationTruthIntroduction -> emit [] (countedTruthIntroductionProof context)
        FormationBoundHypothesis -> Except.throwE Notion.FormationProofInvalidRecipe
        FormationForallIntroduction coreType child -> do
            (extended, _) <- kernel (countedExtendProofContextBinder context coreType)
            body <- buildScope extended depth bindings child
            emit [body] (countedForallIntroductionProof context coreType (emittedProof body))
        FormationImplicationIntroduction premise binding@(FormationRecipeId boundOrdinal) child -> do
            case nodes Vector.!? boundOrdinal of
                Just FormationBoundHypothesis -> pure ()
                _ -> Except.throwE Notion.FormationProofInvalidRecipe
            premise' <- kernel (countedAdmitScopedTerm context premise)
            extended <- kernel (countedExtendProofContextHypothesis context premise')
            body <- buildScope extended (depth + 1) (Map.insert binding depth bindings) child
            emit [body] (countedComposeImplicationProof context premise' (emittedProof body))
        FormationUseHypothesis index -> do
            when (hypothesisIxValue index >= expectedHypotheses)
                (Except.throwE Notion.FormationProofInvalidRecipe)
            proof <- emit [] (countedIndexedHypothesisProof context (hypothesisIx (hypothesisIxValue index + depth)))
            entered <- State.gets (Set.member index . admittedHypotheses)
            unless entered do
                _admitted <- kernel (countedAdmitScopedTerm context (statement proof))
                State.modify' (\state -> state
                    {admittedHypotheses = Set.insert index (admittedHypotheses state)})
            pure proof
        FormationSuppliedUniversal parent adapter -> do
            original <- build context depth bindings parent
            adaptUniversal context original adapter
        FormationUseImport index -> do
            let ordinal = importIxValue index
            when (ordinal >= fromIntegral (Vector.length imports))
                (Except.throwE Notion.FormationProofInvalidRecipe)
            imported <- maybe
                (Except.throwE Notion.FormationProofInvalidRecipe)
                pure
                (imports Vector.!? fromIntegral ordinal)
            proof <- emit [] (countedImportedProof context index (derivationImportStatement imported))
            entered <- State.gets (Set.member index . admittedImports)
            unless entered do
                _admitted <- kernel (countedAdmitScopedTerm context (statement proof))
                State.modify' (\state -> state
                    {admittedImports = Set.insert index (admittedImports state)})
            pure proof
        FormationConjunctionLeftElimination child -> do
            conjunction <- build context depth bindings child
            emit [conjunction] (countedProjectConjunctionProof True context (emittedProof conjunction))
        FormationConjunctionRightElimination child -> do
            conjunction <- build context depth bindings child
            emit [conjunction] (countedProjectConjunctionProof False context (emittedProof conjunction))
        FormationConjunctionIntroduction left right -> do
            leftProof <- build context depth bindings left
            rightProof <- build context depth bindings right
            emit [leftProof, rightProof] (countedConjunctionIntroductionProof (emittedProof leftProof) (emittedProof rightProof))
        FormationDisjunctionIntroduction right target parent -> do
            target' <- kernel (countedAdmitScopedTerm context target)
            (a,b) <- checked (splitScopedDisjunction target')
            child <- build context depth bindings parent
            result <- if right
                then emit [child] (countedDisjunctionRightProof context (scopedCoreTerm a) (emittedProof child))
                else emit [child] (countedDisjunctionLeftProof context (scopedCoreTerm b) (emittedProof child))
            convert context result target'
        FormationBiconditionalIntroduction target forward backward -> do
            target' <- kernel (countedAdmitScopedTerm context target)
            (operand,a,b) <- checked (splitScopedEquality target')
            unless (operand == TyProp) (Except.throwE Notion.FormationProofInvalidRecipe)
            first <- build context depth bindings forward
            second <- build context depth bindings backward
            principle <- emit [] (countedFoundationProof context PropositionalExtensionality)
            atLeft <- emit [principle] (countedForallEliminationProof context (emittedProof principle) a)
            atRight <- emit [atLeft] (countedForallEliminationProof context (emittedProof atLeft) b)
            oneWay <- emit [atRight,first] (countedImplicationEliminationProof context (emittedProof atRight) (emittedProof first))
            result <- emit [oneWay,second] (countedImplicationEliminationProof context (emittedProof oneWay) (emittedProof second))
            convert context result target'
        FormationBiconditionalElimination right parent premise -> do
            original <- build context depth bindings parent
            (operand,_,_) <- checked (splitScopedEquality (statement original))
            unless (operand == TyProp) (Except.throwE Notion.FormationProofInvalidRecipe)
            equality <- if right then reverseEquality context original else pure original
            child <- build context depth bindings premise
            emit [equality,child] (countedComposeEqualityModusPonensProof context (emittedProof equality) (emittedProof child))
        FormationExistentialIntroduction target witness parent -> do
            target' <- kernel (countedAdmitScopedTerm context target)
            (binder,body) <- checked (openScopedExists target')
            unless (binder == TySet) (Except.throwE Notion.FormationProofInvalidRecipe)
            argument <- checkedTerm context witness
            child <- build context depth bindings parent
            emit [child] (countedExistentialIntroductionProof context binder body argument (emittedProof child))
        FormationEqualityReflexivity operand -> do
            argument <- checkedTerm context operand
            emit [] (countedComposeReflexivityProof context argument)
        FormationForallElimination quantified argument -> do
            quantifiedProof <- build context depth bindings quantified
            argument' <- checkedTerm context argument
            emit [quantifiedProof] (countedForallEliminationProof context (emittedProof quantifiedProof) argument')
        FormationImplicationElimination implication premise -> do
            implicationProof <- build context depth bindings implication
            premiseProof <- build context depth bindings premise
            emit [implicationProof, premiseProof] (countedImplicationEliminationProof context (emittedProof implicationProof) (emittedProof premiseProof))
        FormationConversion parent target -> do
            target' <- kernel (countedAdmitScopedTerm context target)
            source <- build context depth bindings parent
            convert context source target'
        FormationTransport parent premise target steps -> do
            premise' <- kernel (countedAdmitScopedTerm context premise)
            target' <- kernel (countedAdmitScopedTerm context target)
            source <- build context depth bindings parent
            initial <- convert context source premise'
            transported <- foldM (\current (predicate, edge) -> do
                predicate' <- kernel (countedAdmitScopedTerm context predicate)
                predicateEquality <- emit [] (countedComposeReflexivityProof context predicate')
                transport context depth bindings predicate' predicateEquality current edge) initial steps
            convert context transported target'

    -- Prove S -> T in a private context, then apply the actual root proof of S.
    -- The root source may use checked alias transport. No admission cache or
    -- root hypothesis index is reused under the adapter's introductions.
    adaptUniversal context original adapter = do
        source <- checkedTerm context (universalFormula (adapterSource adapter))
        sourceMatches <- sameCore (statement original) source
        unless sourceMatches
            (Except.throwE Notion.FormationProofInvalidRecipe)
        extended <- kernel (countedExtendProofContextHypothesis context source)
        adapted <- introduce extended 0 0 (adapterTarget adapter)
        implication <- emit [adapted] (countedComposeImplicationProof context source (emittedProof adapted))
        result <- emit [implication, original] (countedImplicationEliminationProof context (emittedProof implication) (emittedProof original))
        target <- checkedTerm context (universalFormula (adapterTarget adapter))
        targetMatches <- sameCore (statement result) target
        unless targetMatches
            (Except.throwE Notion.FormationProofInvalidRecipe)
        pure result
      where
        introduce active binders guards = \case
            UniversalBind nested -> do
                (extended, _) <- kernel (countedExtendProofContextBinder active TySet)
                child <- introduce extended (binders + 1) guards nested
                emit [child] (countedForallIntroductionProof active TySet (emittedProof child))
            UniversalRequire premise nested -> do
                premise' <- kernel (countedScopedTerm active (atomFormula premise))
                extended <- kernel (countedExtendProofContextHypothesis active premise')
                child <- introduce extended binders (guards + 1) nested
                emit [child] (countedComposeImplicationProof active premise' (emittedProof child))
            UniversalReturn _ -> do
                sourceProof <- local active (hypothesisIx guards)
                sourceResult <- foldM (eliminate active binders guards) sourceProof (adapterEliminations adapter)
                rebuild active (\selector -> projectIn active selector sourceResult) (adapterResult adapter)
        atomFormula (AtomLeaf atom) = atom
        atomFormula (AtomAnd left right) = CAnd (atomFormula left) (atomFormula right)
        local active index' = do
            value <- emit [] (countedIndexedHypothesisProof active index')
            _ <- kernel (countedAdmitScopedTerm active (statement value))
            pure value
        eliminate active binders guards parent = \case
            EliminateBinder ordinal -> do
                when (ordinal >= binders) (Except.throwE Notion.FormationProofInvalidRecipe)
                argument <- kernel (countedScopedTerm active (CBound (binders - ordinal - 1)))
                emit [parent] (countedForallEliminationProof active (emittedProof parent) argument)
            EliminateGuard references -> do
                premise <- rebuild active (\(ordinal, selector) -> do
                    when (ordinal >= guards) (Except.throwE Notion.FormationProofInvalidRecipe)
                    local active (hypothesisIx (guards - ordinal - 1)) >>= projectIn active selector) references
                emit [parent, premise] (countedImplicationEliminationProof active (emittedProof parent) (emittedProof premise))
        rebuild :: ProofContext ObjectId -> (value -> FormationBuild EmittedProof)
            -> AtomTree value -> FormationBuild EmittedProof
        rebuild active leaf = \case
            AtomLeaf value -> leaf value
            AtomAnd left right -> do
                a <- rebuild active leaf left
                b <- rebuild active leaf right
                emit [a, b] (countedConjunctionIntroductionProof (emittedProof a) (emittedProof b))
        projectIn _ ConjunctionHere value = pure value
        projectIn active (ConjunctionLeft rest) value =
            emit [value] (countedProjectConjunctionProof True active (emittedProof value)) >>= projectIn active rest
        projectIn active (ConjunctionRight rest) value =
            emit [value] (countedProjectConjunctionProof False active (emittedProof value)) >>= projectIn active rest

    transport context depth bindings predicate predicateEquality current
            (FormationTransportEdge reference direction) = do
        original <- build context depth bindings reference
        equality <- case direction of
            FormationEqualityLeftToRight -> pure original
            FormationEqualityRightToLeft -> reverseEquality context original
        (_operandType, left, _right) <-
            checked (splitScopedEquality (statement equality))
        application <- core (\work -> countedApplyScopedCore work predicate left) >>= checked
        functionEquality <- emit [predicateEquality, equality]
            (countedComposeApplicationEqualityProof context (emittedProof predicateEquality) (emittedProof equality))
        source <- convert context current application
        emit [functionEquality, source] (countedComposeEqualityModusPonensProof context (emittedProof functionEquality) (emittedProof source))

    reverseEquality context equality = do
        (operandType, left, right) <-
            checked (splitScopedEquality (statement equality))
        let ambient = proofContextTypes context
            bound = scopedBound ambient operandType
        shiftedLeft <- core (\work -> countedWeakenCheckedScopedCore work operandType left)
        predicateBody <- core (\work -> countedEqualScopedCore work bound shiftedLeft) >>= checked
        predicate <- core (\work -> countedAbstractScopedCore work operandType predicateBody) >>= checked
        predicateEquality <- emit [] (countedComposeReflexivityProof context predicate)
        applicationEquality <- emit [predicateEquality, equality]
            (countedComposeApplicationEqualityProof context (emittedProof predicateEquality) (emittedProof equality))
        reflexivity <- emit [] (countedComposeReflexivityProof context left)
        leftApplication <- core (\work -> countedApplyScopedCore work predicate left) >>= checked
        premise <- convert context reflexivity leftApplication
        reversed <- emit [applicationEquality, premise] (countedComposeEqualityModusPonensProof context (emittedProof applicationEquality) (emittedProof premise))
        target <- core (\work -> countedEqualScopedCore work right left) >>= checked
        convert context reversed target

    checked :: Maybe value -> FormationBuild value
    checked = maybe (Except.throwE Notion.FormationProofInvalidRecipe) pure

    convert context source target = do
        same <- sameCore (statement source) target
        if same then pure source else
            emit [source] (countedConversionProof context (emittedProof source) target)
