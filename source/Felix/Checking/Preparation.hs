{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Bounded, proof-producing refinement of an already checked obligation.
-- The host supplies eligible canonical definitions and owns ATP/selection
-- policy. Returned holes retain their exact lexical scope.
module Felix.Checking.Preparation
    ( PreparationSession
    , preparationSession
    , defaultPreparationWork
    , PreparationStatistics(..)
    , PreparationLimit(..)
    , preparationExhausted
    , preparationStatistics
    , renderPreparationExhaustion
    , PreparationPlan
    , PreparationView(..)
    , preparationView
    , preparationGoal
    , PreparationOutcome(..)
    , preparationOutcome
    , prepareLocalEvidence
    , prepareLocalEvidenceWithDefinitions
    , prepareStructureRequirements
    , preparePredicateEquality
    , prepareSelectedImport
    , prepareAliasEvidence
    , openPreparationGoal
    , runPreparationWork
    , runPreparationWorkM
    , runPreparationProof
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Elimination qualified as Elimination
import Felix.Checking.Obvious.Template qualified as Template
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Kernel.Derivation (ImportIx, hypothesisIx, importIx)
import Felix.Checking.Kernel.Proof qualified as Kernel
import Control.Monad (foldM, unless)
import Control.Monad.Except qualified as Except
import Control.Monad.State.Strict qualified as State
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Word (Word)
import Data.Functor.Identity (runIdentity)
import Data.Text qualified as Text
import Numeric.Natural (Natural)

-- Work covers candidate visits, structural identity, projection proof work,
-- logical introductions (including hypothesis weakening), exact local rule
-- application, and composition. Exhaustion only ends optional preparation;
-- it does not enlarge or disable the eventual ATP request.
defaultPreparationWork :: Word
defaultPreparationWork = 1000000

data PreparationSession = PreparationSession
    { sessionInitialWork :: !Word
    , sessionRemainingWork :: !Word
    , sessionStopped :: !(Maybe PreparationLimit)
    } deriving stock (Show, Eq)

preparationSession :: Word -> PreparationSession
preparationSession work = PreparationSession work work Nothing

-- Source-aware preparation uses the same account for its checked operations.
-- Failure retains expenditure; an exhausted session cannot start another job.
runPreparationWork
    :: (Word -> (Either (CountedCoreFailure failure) value, Word))
    -> PreparationSession
    -> (Either failure (Maybe value), PreparationSession)
runPreparationWork operation session =
    runIdentity (runPreparationWorkM (pure . operation) session)

runPreparationWorkM
    :: Monad m => (Word -> m (Either (CountedCoreFailure failure) value, Word))
    -> PreparationSession -> m (Either failure (Maybe value), PreparationSession)
runPreparationWorkM operation session
    | isJust (sessionStopped session) = pure (Right Nothing,session)
    | otherwise = do
        (result,remaining) <- operation (sessionRemainingWork session)
        let updated = session {sessionRemainingWork = remaining}
        pure $ case result of
            Left CountedCoreStructuralWorkExhausted ->
                (Right Nothing,updated {sessionStopped = Just PreparationWorkLimit})
            Left (CountedCoreOperationFailed failure) -> (Left failure,updated)
            Right value -> (Right (Just value),updated)

runPreparationProof
    :: Conversion.ConversionPool -> Kernel.CountedProof global value
    -> PreparationSession
    -> (Either Kernel.KernelProofBuildError (Maybe value), PreparationSession, Conversion.ConversionPool)
runPreparationProof pool operation session
    | isJust (sessionStopped session) = (Right Nothing,session,pool)
    | otherwise =
        let (result,remaining,balance) = Kernel.runCountedProof (sessionRemainingWork session) pool operation
            updated = session {sessionRemainingWork = remaining}
        in case result of
            Left CountedCoreStructuralWorkExhausted ->
                (Right Nothing,updated {sessionStopped = Just PreparationWorkLimit},balance)
            Left (CountedCoreOperationFailed (Kernel.ProofConversionLimitExhausted _ limit)) ->
                (Right Nothing,updated {sessionStopped = Just
                    (PreparationConversionLimit (Conversion.conversionLimitAmount limit))},balance)
            Left (CountedCoreOperationFailed failure) -> (Left failure,updated,balance)
            Right value -> (Right (Just value),updated,balance)

data PreparationLimit = PreparationWorkLimit | PreparationConversionLimit !Word
    deriving stock (Show, Eq)

data PreparationStatistics = PreparationStatistics
    { preparationUsedWork :: !Word
    , preparationWorkLimit :: !Word
    , preparationStoppedAt :: !(Maybe PreparationLimit)
    } deriving stock (Show, Eq)

preparationExhausted :: PreparationStatistics -> Bool
preparationExhausted = isJust . preparationStoppedAt

preparationStatistics :: PreparationSession -> PreparationStatistics
preparationStatistics session = PreparationStatistics
    (sessionInitialWork session - sessionRemainingWork session)
    (sessionInitialWork session)
    (sessionStopped session)

renderPreparationExhaustion :: PreparationStatistics -> Text
renderPreparationExhaustion statistics =
    "automatic local-evidence preparation exhausted "
        <> (case preparationStoppedAt statistics of
            Just (PreparationConversionLimit limit) ->
                "a conversion operation limit of " <> Text.pack (show limit) <> " units (shared work "
            _ -> "its work limit (")
        <> Text.pack (show (preparationUsedWork statistics)) <> "/"
        <> Text.pack (show (preparationWorkLimit statistics))
        <> "); completed components were retained and remaining obligations kept their ATP policy"

-- Constructors are private. Refinements retain the exact checked logical view
-- of their parent and each introduced scope. Solved leaves contain ordinary
-- independently replayable proofs.
data PreparationPlan global
    = Hole !(ScopedCheckedCore global)
    | Closed !(Kernel.BuiltProof global) !(Set ImportIx)
    | Conjunction !(ScopedCheckedCore global)
        !(PreparationPlan global) !(PreparationPlan global)
    | Universal !(ScopedCheckedCore global) !CoreType
        !(Kernel.ProofContext global) !(PreparationPlan global)
    | Implication !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(Kernel.ProofContext global) !(PreparationPlan global)
    | Rewrite !(ScopedCheckedCore global) !(Kernel.BuiltProof global) !(PreparationPlan global)
    | Evidence !(Kernel.BuiltProof global) !(Set ImportIx)
        !(Kernel.ProofContext global) !(PreparationPlan global)

data PreparationView global
    = PreparationHole !(ScopedCheckedCore global)
    | PreparationProof !(Kernel.BuiltProof global) !(Set ImportIx)
    | PreparationConjunction !(ScopedCheckedCore global)
        !(PreparationPlan global) !(PreparationPlan global)
    | PreparationUniversal !(ScopedCheckedCore global) !CoreType
        !(Kernel.ProofContext global) !(PreparationPlan global)
    | PreparationImplication !(ScopedCheckedCore global) !(ScopedCheckedCore global)
        !(Kernel.ProofContext global) !(PreparationPlan global)
    | PreparationRewrite !(ScopedCheckedCore global) !(Kernel.BuiltProof global) !(PreparationPlan global)
    | PreparationEvidence !(Kernel.BuiltProof global) !(Set ImportIx)
        !(Kernel.ProofContext global) !(PreparationPlan global)

preparationView :: PreparationPlan global -> PreparationView global
preparationView = \case
    Hole goal -> PreparationHole goal
    Closed proof used -> PreparationProof proof used
    Conjunction goal left right -> PreparationConjunction goal left right
    Universal goal binderType context child -> PreparationUniversal goal binderType context child
    Implication goal premise context child -> PreparationImplication goal premise context child
    Rewrite goal equation child -> PreparationRewrite goal equation child
    Evidence proof used context child -> PreparationEvidence proof used context child

preparationGoal :: PreparationPlan global -> ScopedCheckedCore global
preparationGoal = \case
    Hole goal -> goal
    Closed proof _used -> Kernel.builtProofStatement proof
    Conjunction goal _left _right -> goal
    Universal goal _type _context _child -> goal
    Implication goal _premise _context _child -> goal
    Rewrite goal _equation _child -> goal
    Evidence _proof _used _context child -> preparationGoal child

-- Retain one checked logical opening even when its children remain holes.
-- The source host extends its lexical evidence alongside the returned scope.
openPreparationGoal
    :: Eq global => PreparationSession -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global), PreparationSession)
openPreparationGoal session context target =
    let (result,remaining) = runPreparationWork
            (\work -> let (answer,balance,_) = Kernel.runCountedProof work (Conversion.conversionPool 0) open
                in (answer,balance)) session
    in (fromMaybe (Hole target) <$> result,remaining)
  where
    open
        | Just (left,right) <- splitScopedConjunction target = do
            void (Kernel.countedAdmitScopedTerm context target)
            pure (Conjunction target (Hole left) (Hole right))
        | Just (ty,body) <- openScopedForall target = do
            (nested,_) <- Kernel.countedExtendProofContextBinder context ty
            pure (Universal target ty nested (Hole body))
        | Just (premise,body) <- openScopedImplication target = do
            nested <- Kernel.countedExtendProofContextHypothesis context premise
            pure (Implication target premise nested (Hole body))
        | otherwise = pure (Hole target)

data PreparationOutcome
    = NoApplicableView
    | Solved
    | Residual
    | Exhausted
    deriving stock (Show, Eq)

preparationOutcome :: PreparationSession -> PreparationPlan global -> PreparationOutcome
preparationOutcome session plan
    | isJust (sessionStopped session) = Exhausted
    | otherwise = case plan of
        Hole{} -> NoApplicableView
        Closed{} -> Solved
        Conjunction{} -> Residual
        Universal{} -> Residual
        Implication{} -> Residual
        Evidence{} -> Residual
        Rewrite{} -> Residual

data PreparationFailure
    = WorkExhausted
    | IntegrityFailure !Kernel.KernelProofBuildError

data PreparationState global = PreparationState
    { currentSession :: !PreparationSession
    , definitionImports :: !(Map global ImportIx)
    }

type Preparation global = Except.ExceptT PreparationFailure (State.State (PreparationState global))

-- | Continue the same work account across nested goals. A failed attempt keeps
-- its actual debit. In particular, an exhausted right child cannot discard a
-- solved left child or restart search with a fresh budget.
prepareLocalEvidence
    :: Ord global
    => PreparationSession
    -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global), PreparationSession)
prepareLocalEvidence initial context goal =
    let (result, final) = prepareLocalEvidenceWithDefinitions (const Nothing) initial context goal
    in (fst <$> result, final)

-- | Look up only canonical pointwise equations owned by the head of an active
-- positive local fact. The host must retain this exact import association when
-- lowering solved leaves; unused attempted definitions carry no dependency.
prepareLocalEvidenceWithDefinitions
    :: Ord global
    => (global -> Maybe (FrozenCheckedCore global))
    -> PreparationSession
    -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global, [(ImportIx, global)]), PreparationSession)
prepareLocalEvidenceWithDefinitions = prepareEvidence OrdinaryRoot

-- | Refine the registered left-associated component spine. The count comes
-- from the admitted schema; conjunctions inside an individual requirement
-- retain ordinary local-preparation policy. There is no component-count cap.
prepareStructureRequirements
    :: Ord global
    => Natural
    -> (global -> Maybe (FrozenCheckedCore global))
    -> PreparationSession
    -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global, [(ImportIx, global)]), PreparationSession)
prepareStructureRequirements count = prepareEvidence (RequirementRoot count)

-- | View a residual through compiler-owned local alias equations, newest
-- definition first. Indices refer to the supplied context; the host owns their
-- eligibility. Arbitrary local equalities must not be passed as aliases.
prepareAliasEvidence
    :: Ord global
    => [Natural]
    -> (global -> Maybe (FrozenCheckedCore global))
    -> PreparationSession -> Kernel.ProofContext global -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global, [(ImportIx, global)]), PreparationSession)
prepareAliasEvidence indices = prepareEvidence (AliasRoot indices)

data PreparationRoot global = OrdinaryRoot | RequirementRoot !Natural
    | SelectedRoot !(FrozenCheckedCore global) | AliasRoot ![Natural]

-- Hypotheses are prepended as views are proved. A cursor records the generation
-- of its index instead of repeatedly weakening every pending proof recipe.
data PositiveSource global = PositiveSource
    { sourceGeneration :: !Natural
    , sourceHypothesis :: !Natural
    , sourceProjections :: ![Bool]
    , sourceActiveHeads :: !(Set global)
    , sourceProposition :: !(ScopedCheckedCore global)
    }

prepareEvidence
    :: Ord global
    => PreparationRoot global
    -> (global -> Maybe (FrozenCheckedCore global))
    -> PreparationSession
    -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> (Either Kernel.KernelProofBuildError (PreparationPlan global, [(ImportIx, global)]), PreparationSession)
prepareEvidence root lookupDefinition initial context goal =
    let (result, final) = State.runState (Except.runExceptT (case root of
            OrdinaryRoot -> refine context goal
            RequirementRoot count -> refineRequirements count context goal >>= retainResidualEvidence context
            SelectedRoot statement -> refineSelected statement
            AliasRoot aliases -> do
                candidate <- refineAliasGoal context goal aliases aliases False
                -- Alias normalization is an evidence lookup, not an ATP
                -- simplifier. Commit only actual goal progress; otherwise
                -- preserve the original abstraction and the attempt's debit.
                pure (if solvedComponent candidate then candidate else Hole goal)))
            (PreparationState initial Map.empty)
        imports = [(index, object) | (object, index) <- Map.toList (definitionImports final)]
    in (case result of
            Left (IntegrityFailure failure) -> Left failure
            Left WorkExhausted -> Right (Hole goal, imports)
            Right plan -> Right (plan, imports),
        currentSession final)
  where
    solvedComponent = \case
        Closed{} -> True
        Hole{} -> False
        Conjunction _ left right -> solvedComponent left || solvedComponent right
        Universal _ _ _ child -> solvedComponent child
        Implication _ _ _ child -> solvedComponent child
        Evidence _ _ _ child -> solvedComponent child
        Rewrite _ _ child -> solvedComponent child

    refineSelected statement = do
        result <- attemptWithinBudget do
            charge
            let proposition = embedClosedCore (scopedCoreContext goal) statement
                source = proofOperation (Kernel.countedImportedProof context (importIx 0) statement)
            exact <- exactOperation (\work -> countedScopedCoreIdentity work goal proposition)
            if exact then Just <$> source else do
                template <- either (integrity . Text.pack . show) pure
                    (Template.retainCheckedPropositionTemplate proposition)
                visitRule context goal source False [] template
        pure case result of
            Just (Just proof) -> Closed proof (Set.singleton (importIx 0))
            _ -> Hole goal

    -- Preserve solved components before spending work to enrich a residual.
    -- Each continuation keeps the lexical and hypothesis scope of that hole.
    retainResidualEvidence current plan = case plan of
        Hole target -> retainPositiveEvidence target 0 current
            [PositiveSource 0 index [] Set.empty proposition
            | (index, proposition) <- zip [0..] (Kernel.proofContextHypotheses current)]
        Closed{} -> pure plan
        Conjunction target left right ->
            Conjunction target <$> retainResidualEvidence current left <*> retainResidualEvidence current right
        Universal target binderType nested child ->
            Universal target binderType nested <$> retainResidualEvidence nested child
        Implication target premise nested child ->
            Implication target premise nested <$> retainResidualEvidence nested child
        Evidence{} -> pure plan
        Rewrite{} -> pure plan

    retainPositiveEvidence target generation current pending = case pending of
        [] -> refine current target
        source : rest -> do
            admitted <- attemptWithinBudget charge
            case admitted of
                Nothing -> pure (Hole target)
                Just () -> case splitScopedConjunction (sourceProposition source) of
                    Just (left, right) ->
                        retainPositiveEvidence target generation current
                            (source {sourceProposition = left, sourceProjections = False : sourceProjections source}
                            : source {sourceProposition = right, sourceProjections = True : sourceProjections source}
                            : rest)
                    Nothing -> do
                        opened <- attemptWithinBudget (openPositiveSource generation current source)
                        case opened of
                            Nothing -> pure (Hole target)
                            Just Nothing -> retainPositiveEvidence target generation current rest
                            Just (Just (object, proof, used, nested)) -> do
                                let body = Kernel.builtProofStatement proof
                                    nextGeneration = generation + 1
                                    next = PositiveSource nextGeneration 0 []
                                        (Set.insert object (sourceActiveHeads source)) body
                                child <- retainPositiveEvidence target nextGeneration nested (next : rest)
                                finishEvidence current proof used nested child

    finishEvidence current proof used nested child = case child of
        Closed childProof childUses -> do
            joined <- attemptWithinBudget (proofOperation do
                implication <- Kernel.countedImplicationIntroductionProof
                    current (Kernel.builtProofStatement proof) childProof
                Kernel.countedImplicationEliminationProof current implication proof)
            pure (maybe (Evidence proof used nested child)
                (\result -> Closed result (used <> childUses)) joined)
        _ -> pure (Evidence proof used nested child)

    openPositiveSource generation current source = do
        (headTerm, arguments) <- applicationSpine (scopedCoreTerm (sourceProposition source)) []
        case headTerm of
            CGlobal object | object `Set.notMember` sourceActiveHeads source
                , Just definition <- lookupDefinition object -> do
                    index <- definitionIndex object
                    (equation, body) <- specializePredicateEquation current (sourceProposition source)
                        arguments index definition
                    existing <- findHypothesis current body 0 (Kernel.proofContextHypotheses current)
                    case existing of
                        Just _ -> pure Nothing
                        Nothing -> do
                            initialProof <- proofOperation (Kernel.countedIndexedHypothesisProof current
                                    (hypothesisIx (generation - sourceGeneration source + sourceHypothesis source)))
                            premise <- foldM (project current) initialProof (reverse (sourceProjections source))
                            (expanded, nested) <- proofOperation do
                                expanded <- Kernel.countedEqualityModusPonensProof current equation premise
                                nested <- Kernel.countedExtendProofContextHypothesis current body
                                pure (expanded, nested)
                            charge -- Reserve publication of the complete evidence continuation.
                            pure (Just (object, expanded, Set.singleton index, nested))
            _ -> pure Nothing

    -- Normalize in declaration order once. The alias catalogue is acyclic;
    -- this phase never alternates orientations or recursively searches equations.
    refineAliasGoal current target allAliases remaining changed = case remaining of
        [] -> refineAliasFacts changed allAliases 0 current target
            (zip [0..] (Kernel.proofContextHypotheses current))
        index : rest -> do
            opened <- attemptWithinBudget do
                replacement <- aliasReplacement current index target
                case replacement of
                    Nothing -> pure Nothing
                    Just (equality, replaced) -> do
                        equation <- transportOperation (\work -> Kernel.congruenceEqualityWithinWork
                            work current equality (scopedCoreReplacementAbstraction replaced)
                            target (scopedCoreReplacementResult replaced))
                        charge
                        pure (Just (equation, scopedCoreReplacementResult replaced))
            case opened of
                Nothing -> pure (Hole target)
                Just Nothing -> refineAliasGoal current target allAliases rest changed
                Just (Just (equation, result)) -> do
                    child <- refineAliasGoal current result allAliases rest True
                    case child of
                        Closed proof used -> do
                            joined <- attemptWithinBudget do
                                identity <- proofOperation (Kernel.countedScopedTerm
                                    current (CLam TyProp (CBound 0)))
                                transportOperation (\work -> Kernel.transportEqualityWithinWork
                                    work current Kernel.EqualityRightToLeft equation identity proof target)
                            pure (maybe (Rewrite target equation child)
                                (\proved -> Closed proved used) joined)
                        _ -> pure (Rewrite target equation child)

    refineAliasFacts goalChanged aliases added current target sources = case sources of
        [] -> if goalChanged || added > 0 then refine current target else pure (Hole target)
        (index, proposition) : rest -> do
            admitted <- attemptWithinBudget charge
            case admitted of
                Nothing -> pure (Hole target)
                Just () | index `elem` aliases -> next
                Just () -> do
                    normalized <- attemptWithinBudget do
                        result <- normalizeAliasFact current (index + added) proposition
                            (fmap (+ added) aliases) Nothing
                        case result of
                            Nothing -> pure Nothing
                            Just proof -> do
                                existing <- findHypothesis current (Kernel.builtProofStatement proof)
                                    0 (Kernel.proofContextHypotheses current)
                                case existing of
                                    Just _ -> pure Nothing
                                    Nothing -> do
                                        nested <- proofOperation (Kernel.countedExtendProofContextHypothesis
                                            current (Kernel.builtProofStatement proof))
                                        charge
                                        pure (Just (proof, nested))
                    case normalized of
                        Nothing -> pure (Hole target)
                        Just Nothing -> next
                        Just (Just (proof, nested)) -> do
                            child <- refineAliasFacts goalChanged aliases (added + 1) nested target rest
                            finishEvidence current proof Set.empty nested child
          where
            next = refineAliasFacts goalChanged aliases added current target rest

    normalizeAliasFact current source proposition remaining evidence = case remaining of
        [] -> pure evidence
        index : rest -> do
            replaced <- aliasReplacement current index proposition
            case replaced of
                Nothing -> normalizeAliasFact current source proposition rest evidence
                Just (equality, replacement) -> do
                    premise <- maybe (proofOperation (Kernel.countedIndexedHypothesisProof current (hypothesisIx source))) pure evidence
                    let result = scopedCoreReplacementResult replacement
                    proof <- transportOperation (\work -> Kernel.transportEqualityWithinWork
                        work current Kernel.EqualityLeftToRight equality
                        (scopedCoreReplacementAbstraction replacement) premise result)
                    normalizeAliasFact current source result rest (Just proof)

    aliasReplacement current index target = do
        charge
        equality <- proofOperation (Kernel.countedIndexedHypothesisProof
            current (hypothesisIx index))
        case splitScopedEquality (Kernel.builtProofStatement equality) of
            Just (TySet, left, right) | CBound{} <- scopedCoreTerm left -> do
                replaced <- templateOperation (\work -> countedReplaceScopedCoreOccurrence work left right target)
                pure ((\replacement -> (equality, replacement)) <$> replaced)
            _ -> integrity "a compiler-owned alias lost its defining set equality"

    refineRequirements 0 _current _target = integrity "a structure has no shape component"
    refineRequirements 1 current target = refine current target
    refineRequirements count current target = do
        direct <- attemptWithinBudget do
            charge
            findHypothesis current target 0 (Kernel.proofContextHypotheses current)
        case direct of
            Nothing -> pure (Hole target)
            Just (Just proof) -> pure (Closed proof Set.empty)
            Just Nothing -> do
                admitted <- attemptWithinBudget charge
                case admitted of
                    Nothing -> pure (Hole target)
                    Just () -> case splitScopedConjunction target of
                        Nothing -> integrity "the registered structure lost its component spine"
                        Just (left, right) -> do
                            leftPlan <- refineRequirements (count - 1) current left
                            rightPlan <- refine current right
                            joinConjunction target leftPlan rightPlan

    joinConjunction target leftPlan rightPlan = case (leftPlan, rightPlan) of
        (Closed leftProof leftUses, Closed rightProof rightUses) -> do
            joined <- attemptWithinBudget (proofOperation (Kernel.countedConjunctionIntroductionProof leftProof rightProof))
            pure (maybe (Conjunction target leftPlan rightPlan)
                (\proof -> Closed proof (leftUses <> rightUses)) joined)
        _ -> pure (Conjunction target leftPlan rightPlan)

    refine current target = do
        attempt <- attemptWithinBudget do
            charge
            findHypothesis current target 0 (Kernel.proofContextHypotheses current)
        case attempt of
            Nothing -> pure (Hole target)
            Just (Just proof) -> pure (Closed proof Set.empty)
            Just Nothing -> do
                applied <- attemptWithinBudget
                    (findRule current target 0 (Kernel.proofContextHypotheses current))
                case applied of
                    Nothing -> pure (Hole target)
                    Just (Just proof) -> pure (Closed proof Set.empty)
                    Just Nothing -> do
                        transported <- attemptWithinBudget (findTransport current target)
                        case transported of
                            Nothing -> pure (Hole target)
                            Just (Just proof) -> pure (Closed proof Set.empty)
                            Just Nothing -> do
                                viewed <- attemptWithinBudget
                                    (findDefinition current target 0 (Kernel.proofContextHypotheses current))
                                case viewed of
                                    Nothing -> pure (Hole target)
                                    Just (Just (proof, used)) -> pure (Closed proof used)
                                    Just Nothing -> refineIntroduction current target

    refineIntroduction current target
        | Just (left, right) <- splitScopedConjunction target = do
            admitted <- attemptWithinBudget charge
            case admitted of
                Nothing -> pure (Hole target)
                Just () -> do
                    leftPlan <- refine current left
                    rightPlan <- refine current right
                    case (leftPlan, rightPlan) of
                        (Hole{}, Hole{}) -> pure (Hole target)
                        _ -> joinConjunction target leftPlan rightPlan
        | Just (binderType, body) <- openScopedForall target = do
            opened <- attemptWithinBudget (proofOperation (Kernel.countedExtendProofContextBinder current binderType))
            case opened of
                Nothing -> pure (Hole target)
                Just (nested, _variable) -> do
                    child <- refine nested body
                    finishIntroduction target (Universal target binderType nested child) child
                        (\proof -> Kernel.countedForallIntroductionProof
                            current binderType proof)
        | Just (premise, body) <- openScopedImplication target = do
            opened <- attemptWithinBudget (proofOperation (Kernel.countedExtendProofContextHypothesis current premise))
            case opened of
                Nothing -> pure (Hole target)
                Just nested -> do
                    child <- refine nested body
                    finishIntroduction target (Implication target premise nested child) child
                        (\proof -> Kernel.countedImplicationIntroductionProof
                            current premise proof)
        | otherwise = pure (Hole target)

    -- An opening is committed only when its child made progress. If closing a
    -- solved child exhausts the account, retain the introduction and that proof
    -- for the host's mandatory completion/replay phase; never reopen the child.
    finishIntroduction target retained child introduce = case child of
        Hole{} -> pure (Hole target)
        Closed proof used -> do
            joined <- attemptWithinBudget (proofOperation (introduce proof))
            pure (maybe retained (\result -> Closed result used) joined)
        _ -> pure retained

    findHypothesis _current _target _index [] = pure Nothing
    findHypothesis current target index (hypothesis : rest) = do
        matched <- findProjection target hypothesis []
        case matched of
            Nothing -> findHypothesis current target (index + 1) rest
            Just path -> do
                initialProof <- proofOperation (Kernel.countedIndexedHypothesisProof current (hypothesisIx index))
                Just <$> foldM (project current) initialProof (reverse path)

    findProjection target proposition path = do
        charge
        same <- exactOperation (\work -> countedScopedCoreIdentity work target proposition)
        if same
            then pure (Just path)
            else case splitScopedConjunction proposition of
                Nothing -> pure Nothing
                Just (left, right) -> do
                    first <- findProjection target left (False : path)
                    case first of
                        Just _ -> pure first
                        Nothing -> findProjection target right (True : path)

    -- Demand one transport from an actual active equality. Rewrite the goal
    -- only to look for exact supplied evidence, then transport that proof back.
    -- Failed orientations do not become new hypotheses or recursive requests.
    findTransport current target = sources 0 (Kernel.proofContextHypotheses current)
      where
        sources _ [] = pure Nothing
        sources index (proposition : rest) = do
            let source = proofOperation (Kernel.countedIndexedHypothesisProof current (hypothesisIx index))
            found <- visit source proposition
            maybe (sources (index + 1) rest) (pure . Just) found
        visit source proposition = do
            charge
            case splitScopedConjunction proposition of
                Just (left, right) -> do
                    first <- visit (source >>= \proof -> project current proof False) left
                    maybe (visit (source >>= \proof -> project current proof True) right) (pure . Just) first
                Nothing -> case splitScopedEquality proposition of
                    Just (_type, left, right) -> do
                        same <- exactOperation (\work -> countedScopedCoreIdentity work left right)
                        if same then pure Nothing else do
                            first <- orient source Kernel.EqualityRightToLeft left right
                            maybe (orient source Kernel.EqualityLeftToRight right left) (pure . Just) first
                    Nothing -> pure Nothing
        orient source direction endpoint replacementEndpoint = do
            replaced <- templateOperation (\work -> countedReplaceScopedCoreOccurrence work endpoint replacementEndpoint target)
            case replaced of
                Nothing -> pure Nothing
                Just replacement -> do
                    evidence <- findHypothesis current (scopedCoreReplacementResult replacement)
                        0 (Kernel.proofContextHypotheses current)
                    case evidence of
                        Nothing -> pure Nothing
                        Just premise -> do
                            equality <- source
                            Just <$> transportOperation (\work -> Kernel.transportEqualityWithinWork work
                                current direction equality (scopedCoreReplacementAbstraction replacement)
                                premise target)

    -- Apply at most one supplied clause. Its conclusion determines every
    -- instantiation; antecedents use exact local evidence/conjunctions only.
    -- In particular this never recursively chains rules or guesses witnesses.
    findRule _current _target _index [] = pure Nothing
    findRule current target index (hypothesis : rest) = do
        template <- either (integrity . Text.pack . show) pure
            (Template.retainCheckedPropositionTemplate hypothesis)
        let source = proofOperation (Kernel.countedIndexedHypothesisProof current (hypothesisIx index))
        found <- visitRule current target source False [] template
        maybe (findRule current target (index + 1) rest) (pure . Just) found

    visitRule current target source applied steps template = do
        charge
        direct <- if applied then do
                matched <- templateOperation (\work -> Template.matchTemplateExactly
                    (Kernel.proofContextGlobalTyping current) work template target)
                case matched of
                    Nothing -> pure Nothing
                    Just substitution -> do
                        missing <- exactOperation (\work -> Template.missingTemplateSlotsCounted work
                            (Template.compiledTemplateBinderEnvironment template) substitution)
                        if null missing then do
                            sourceProof <- source
                            materializeRule current substitution sourceProof (reverse steps)
                        else pure Nothing
            else pure Nothing
        case direct of
            Just proof -> do
                same <- exactOperation (\work -> countedScopedCoreIdentity work
                    (Kernel.builtProofStatement proof) target)
                unless same (integrity "exact local rule matching changed its target")
                pure direct
            Nothing
                | Just (binderType, body) <- Template.openCompiledForall template ->
                    let slot = Template.MatcherSlot (Template.binderEnvironmentCount
                            (Template.compiledTemplateBinderEnvironment template))
                    in visitRule current target source True
                        (Elimination.Instantiate binderType slot : steps) body
                | Just (_premise, body) <- Template.openCompiledImplication template ->
                    visitRule current target source True (Elimination.Apply () : steps) body
                | Just (left, right) <- Template.splitCompiledConjunction template -> do
                    first <- visitRule current target source applied (Elimination.ProjectLeft : steps) left
                    maybe (visitRule current target source applied (Elimination.ProjectRight : steps) right)
                        (pure . Just) first
                | otherwise -> pure Nothing

    findDefinition _current _target _index [] = pure Nothing
    findDefinition current target index (hypothesis : rest) = do
        let source = proofOperation (Kernel.countedIndexedHypothesisProof current (hypothesisIx index))
        found <- positiveView current target Set.empty Set.empty source hypothesis
        maybe (findDefinition current target (index + 1) rest) (pure . Just) found

    positiveView current target active used source proposition = do
        charge
        case splitScopedConjunction proposition of
            Just (left, right) -> do
                first <- positiveView current target active used
                    (source >>= \proof -> project current proof False) left
                maybe (positiveView current target active used
                    (source >>= \proof -> project current proof True) right) (pure . Just) first
            Nothing -> do
                (headTerm, arguments) <- applicationSpine (scopedCoreTerm proposition) []
                case headTerm of
                    CGlobal object | object `Set.notMember` active
                        , Just equation <- lookupDefinition object -> do
                            index <- definitionIndex object
                            (specialized, _body) <- specializePredicateEquation current proposition arguments index equation
                            premise <- source
                            expanded <- proofOperation (Kernel.countedEqualityModusPonensProof current specialized premise)
                            let expandedTarget = Kernel.builtProofStatement expanded
                                used' = Set.insert index used
                            path <- findProjection target expandedTarget []
                            direct <- case path of
                                Just projections -> Just <$> foldM (project current) expanded (reverse projections)
                                Nothing -> do
                                    template <- either (integrity . Text.pack . show) pure
                                        (Template.retainCheckedPropositionTemplate expandedTarget)
                                    visitRule current target (pure expanded) False [] template
                            case direct of
                                Just proof -> pure (Just (proof, used'))
                                Nothing -> positiveView current target (Set.insert object active)
                                    used' (pure expanded) expandedTarget
                    _ -> pure Nothing

    definitionIndex object = do
        charge
        indices <- State.gets definitionImports
        case Map.lookup object indices of
            Just index -> pure index
            Nothing -> do
                let index = importIx (fromIntegral (Map.size indices))
                State.modify' (\state -> state {definitionImports = Map.insert object index indices})
                pure index

    materializeRule _current _substitution proof [] = pure (Just proof)
    materializeRule current substitution proof (step : rest) = case step of
        Elimination.Instantiate _binderType slot -> do
            argument <- maybe (integrity "a complete local rule lost its instantiation") pure
                (Template.lookupTemplateSubstitution slot substitution)
            specialized <- proofOperation (Kernel.countedForallEliminationProof current proof argument)
            materializeRule current substitution specialized rest
        Elimination.Apply () -> case openScopedImplication (Kernel.builtProofStatement proof) of
            Nothing -> integrity "a local rule lost its implication antecedent"
            Just (premise, _body) -> do
                evidence <- provePremise current premise
                case evidence of
                    Nothing -> pure Nothing
                    Just premiseProof -> do
                        applied <- proofOperation (Kernel.countedImplicationEliminationProof current proof premiseProof)
                        materializeRule current substitution applied rest
        Elimination.ProjectLeft -> do
            projected <- project current proof False
            materializeRule current substitution projected rest
        Elimination.ProjectRight -> do
            projected <- project current proof True
            materializeRule current substitution projected rest

    provePremise current target = do
        direct <- findHypothesis current target 0 (Kernel.proofContextHypotheses current)
        case direct of
            Just _ -> pure direct
            Nothing -> case splitScopedConjunction target of
                Just (left, right) -> do
                    leftProof <- provePremise current left
                    case leftProof of
                        Nothing -> pure Nothing
                        Just l -> do
                            rightProof <- provePremise current right
                            traverse (\r -> proofOperation (Kernel.countedConjunctionIntroductionProof l r)) rightProof
                Nothing | scopedCoreTerm target == CTruth ->
                    Just <$> proofOperation (Kernel.countedTruthIntroductionProof current)
                Nothing -> pure Nothing

    project current proof rightward =
        case splitScopedConjunction (Kernel.builtProofStatement proof) of
            Nothing -> Except.throwError (IntegrityFailure
                (Kernel.ProofStructuralCompositionMismatch "preparation lost its exact projection path"))
            Just (left, right) -> proofOperation ((if rightward then Kernel.countedConjunctionRightProof
                    else Kernel.countedConjunctionLeftProof)
                    current (scopedCoreTerm left) (scopedCoreTerm right) proof)

attemptWithinBudget :: Preparation global value -> Preparation global (Maybe value)
attemptWithinBudget action = do
    stopped <- State.gets (sessionStopped . currentSession)
    if isJust stopped then pure Nothing
        else Except.catchError (Just <$> action) \case
            WorkExhausted -> pure Nothing
            failure@IntegrityFailure{} -> Except.throwError failure

charge :: Preparation global ()
charge = do
    remaining <- State.gets (sessionRemainingWork . currentSession)
    if remaining == 0 then exhaust
        else modifySession (\session -> session {sessionRemainingWork = remaining - 1})

exhaust :: Preparation global value
exhaust = stopPreparation PreparationWorkLimit

stopPreparation :: PreparationLimit -> Preparation global value
stopPreparation reason = do
    modifySession (\session -> session {sessionStopped = Just reason})
    Except.throwError WorkExhausted

transportOperation
    :: (Word -> (Either (CountedCoreFailure Kernel.KernelProofBuildError) value, Word))
    -> Preparation global value
transportOperation operation = do
    remaining <- State.gets (sessionRemainingWork . currentSession)
    let (result, after) = operation remaining
    modifySession (\session -> session {sessionRemainingWork = after})
    case result of
        Left CountedCoreStructuralWorkExhausted -> exhaust
        Left (CountedCoreOperationFailed (Kernel.ProofConversionLimitExhausted _ limit)) ->
            stopPreparation (PreparationConversionLimit (Conversion.conversionLimitAmount limit))
        Left (CountedCoreOperationFailed failure) -> Except.throwError (IntegrityFailure failure)
        Right value -> pure value

exactOperation
    :: (Word -> (Either (CountedCoreFailure Void) value, Word))
    -> Preparation global value
exactOperation operation = do
    remaining <- State.gets (sessionRemainingWork . currentSession)
    let (result, after) = operation remaining
    modifySession (\session -> session {sessionRemainingWork = after})
    case result of
        Left CountedCoreStructuralWorkExhausted -> exhaust
        Right value -> pure value

proofOperation
    :: Kernel.CountedProof global value
    -> Preparation global value
proofOperation operation = do
    remaining <- State.gets (sessionRemainingWork . currentSession)
    -- Exact logical operations require no beta conversion. Give them no
    -- conversion allowance, so this preparer cannot acquire a hidden search.
    let (result, after, _pool) = Kernel.runCountedProof remaining (Conversion.conversionPool 0) operation
    modifySession (\session -> session {sessionRemainingWork = after})
    case result of
        Left CountedCoreStructuralWorkExhausted -> exhaust
        Left (CountedCoreOperationFailed failure) -> Except.throwError (IntegrityFailure failure)
        Right value -> pure value

-- Checked template operations may exhaust the same account; any other failure
-- contradicts the preparer's checked source/target interfaces.
templateOperation
    :: Show failure
    => (Word -> (Either (CountedCoreFailure failure) value, Word))
    -> Preparation global value
templateOperation operation = do
    remaining <- State.gets (sessionRemainingWork . currentSession)
    let (result, after) = operation remaining
    modifySession (\session -> session {sessionRemainingWork = after})
    case result of
        Left CountedCoreStructuralWorkExhausted -> exhaust
        Left (CountedCoreOperationFailed failure) -> integrity (Text.pack (show failure))
        Right value -> pure value

integrity :: Text -> Preparation global value
integrity = Except.throwError . IntegrityFailure . Kernel.ProofStructuralCompositionMismatch

modifySession :: (PreparationSession -> PreparationSession) -> Preparation global ()
modifySession update = State.modify' (\state -> state {currentSession = update (currentSession state)})

-- | Construct the exact proposition equality for one admitted predicate
-- equation. Import slot zero belongs to that equation. Exhaustion produces
-- no opening; the host keeps the original goal until the complete equation
-- can be replayed and retained at residual boundaries.
preparePredicateEquality
    :: Eq global
    => PreparationSession
    -> Kernel.ProofContext global
    -> ScopedCheckedCore global
    -> FrozenCheckedCore global
    -> (Either Kernel.KernelProofBuildError
        (Maybe (Kernel.BuiltProof global, ScopedCheckedCore global)), PreparationSession)
preparePredicateEquality initial context target equation =
    let action = attemptWithinBudget do
            (_head, arguments) <- applicationSpine (scopedCoreTerm target) []
            (proof, body) <- specializePredicateEquation context target arguments (importIx 0) equation
            charge
            pure (proof, body)
        (result, final) = State.runState (Except.runExceptT action) (PreparationState initial Map.empty)
    in (case result of
            Left (IntegrityFailure failure) -> Left failure
            Left WorkExhausted -> Right Nothing
            Right opening -> Right opening,
        currentSession final)

-- | Apply one caller-selected theorem using exact matching and the same
-- ordered clause eliminations as local evidence. Import slot zero belongs to
-- that occurrence; unresolved parameters are never guessed.
prepareSelectedImport
    :: Ord global
    => PreparationSession -> Kernel.ProofContext global -> ScopedCheckedCore global
    -> FrozenCheckedCore global
    -> (Either Kernel.KernelProofBuildError (Maybe (Kernel.BuiltProof global)), PreparationSession)
prepareSelectedImport initial context target statement =
    let (result, final) = prepareEvidence (SelectedRoot statement) (const Nothing) initial context target
        selected (Closed proof _used, _imports) = Just proof
        selected (Hole{}, _imports) = Nothing
        selected _ = impossible "selected-clause preparation produced a residual scope"
    in (selected <$> result, final)

applicationSpine :: CanonicalTerm global -> [CanonicalTerm global]
    -> Preparation global (CanonicalTerm global, [CanonicalTerm global])
applicationSpine term arguments = do
    charge
    case term of
        CApp function argument -> applicationSpine function (argument : arguments)
        _ -> pure (term, arguments)

specializePredicateEquation
    :: Eq global
    => Kernel.ProofContext global -> ScopedCheckedCore global -> [CanonicalTerm global]
    -> ImportIx -> FrozenCheckedCore global
    -> Preparation global (Kernel.BuiltProof global, ScopedCheckedCore global)
specializePredicateEquation context target arguments index equation = do
    definition <- proofOperation (Kernel.countedImportedProof context index equation)
    specialized <- foldM specialize definition arguments
    case splitScopedEquality (Kernel.builtProofStatement specialized) of
        Just (TyProp, left, right) -> do
            same <- exactOperation (\work -> countedScopedCoreIdentity work left target)
            unless same (integrity "a canonical predicate equation changed its application")
            pure (specialized, right)
        _ -> integrity "a pointwise predicate equation did not specialize to a proposition equality"
  where
    specialize definition argument = proofOperation do
        checked <- Kernel.countedScopedTerm context argument
        Kernel.countedForallEliminationProof context definition checked
