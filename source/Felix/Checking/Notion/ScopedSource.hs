{-# LANGUAGE NoImplicitPrelude #-}

-- | Specialize checked local source views to their lexical captures, then use
-- the declaration projection compiler. Formula context is kept separately:
-- hidden lexical operands never become discoverable clause parameters.
module Felix.Checking.Notion.ScopedSource
    ( ScopedProjection(..), ScopedIntroduction(..), compileScopedSource, compileScopedEliminations, describeScopedGoal, scopedSourceInputs, sourceTemplateInputs
    ) where

import Base
import Control.Monad (unless)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Word (Word)
import Numeric.Natural (Natural)
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.LeafIndex qualified as Leaves
import Felix.Checking.Notion.Projection qualified as Projection
import Felix.Checking.Notion.Introduction qualified as Introduction
import Felix.Checking.Notion.Rule qualified as Rule
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Notion.SuppliedUniversal (DescribedAtom)
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as Source

-- | Domain inputs are independent of the optional universal matcher. Source
-- atoms retain their written views; residual syntax contributes complete opaque
-- set operands. Neither path opens an opaque operand to acquire its children.
scopedSourceInputs
    :: GlobalTyping ObjectId -> Word -> [CoreType] -> [CoreType]
    -> CanonicalTerm ObjectId -> SourceEvidence SupportTermTemplate (SourceAtom presentation termPresentation)
    -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Text) ([SetTermTemplate Leaves.OpaqueLeaf], Leaves.OpaqueLeaves), Word)
scopedSourceInputs typing allowance ambient original formula evidence initial =
    let portable = fmap (fmap (Source.sourceSupportTemplate scopedCoreTerm) . Notion.sourceAssertionAtom) evidence
        (prepared,remaining) = sourceTemplateInputs typing allowance original formula portable
    in case prepared of
        Left failure -> (Left failure,remaining)
        Right templates ->
            let (result,(after,leaves)) = State.runState (Except.runExceptT (traverse encode templates)) (remaining,initial)
            in (fmap (\values -> (values,leaves)) result,after)
  where
    charge = do
        (available,leaves) <- State.get
        if available == 0 then Except.throwE CountedCoreStructuralWorkExhausted
            else State.put (available-1,leaves)
    encode term = charge >> case term of
        TemplateVariable value -> opaque value
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateProvider provider children -> TemplateProvider provider <$> traverse encode children
        TemplateOrderedPair a b -> TemplateOrderedPair <$> encode a <*> encode b
    step operation = do
        (available,leaves) <- State.get
        let (result,remaining) = operation available
        State.put (remaining,leaves)
        either (Except.throwE . fmap (Text.pack . show)) pure result
    opaque term = do
        checked <- step (\work -> countedCheckScopedCanonicalCore typing work original term)
        aligned <- step (\work -> countedAlignScopedCore work ambient checked)
            >>= maybe (impossible "a whole input escaped its lexical scope") pure
        closedSetValueWith charge aligned >>= \case
            Just value -> pure (TemplateClosed value)
            Nothing -> do
                (available,leaves) <- State.get
                let (result,remaining) = Leaves.internOpaqueLeaf available aligned leaves
                State.put (remaining,leaves)
                case result of
                    Left Leaves.OpaqueLeafWorkExhausted -> Except.throwE CountedCoreStructuralWorkExhausted
                    Left _ -> impossible "a whole set input lost its checked type or scope"
                    Right (identifier,next) -> State.put (remaining,next) >> pure (TemplateVariable identifier)

-- Complete support operands, independently of any inverse matching filter.
-- Internal formula binders are removable only when the operand (or a written
-- rich child) is independent of them. Core interiors never become subterms.
sourceTemplateInputs
    :: GlobalTyping ObjectId -> Word -> [CoreType] -> CanonicalTerm ObjectId
    -> SourceEvidence SupportTermTemplate (AtomTemplate SupportTermTemplate)
    -> (Either (CountedCoreFailure Text) [SupportTermTemplate], Word)
sourceTemplateInputs typing allowance context formula evidence = State.runState (Except.runExceptT collect) allowance
  where
    charge = do
        available <- State.get
        if available == 0 then Except.throwE CountedCoreStructuralWorkExhausted
            else State.put (available-1)
    step operation = do
        available <- State.get
        let (result,remaining) = operation available
        State.put remaining
        either (Except.throwE . fmap (Text.pack . show)) pure result
    keep term = pure (Just term,[term])
    input binders term = do
        charge
        case term of
            TemplateClosed{} -> keep term
            TemplateVariable value -> do
                checked <- step (\work -> countedCheckScopedCanonicalCore typing work (binders <> context) value)
                unless (scopedCoreType checked == TySet)
                    (Except.throwE (CountedCoreOperationFailed "a whole support operand is not set-valued"))
                step (\work -> countedInstantiateScopedPrefix work (fromIntegral (length binders)) Map.empty checked) >>= \case
                    ScopedInstantiationOpen{} -> pure (Nothing,[])
                    ScopedInstantiationClosed scoped -> keep (TemplateVariable (scopedCoreTerm scoped))
            TemplateProvider provider children -> do
                parts <- traverse (input binders) children
                case traverse fst parts of
                    Just values -> keep (TemplateProvider provider values)
                    Nothing -> pure (Nothing,concatMap snd (toList parts))
            TemplateOrderedPair a b -> do
                left <- input binders a
                right <- input binders b
                case (left,right) of
                    ((Just x,_),(Just y,_)) -> keep (TemplateOrderedPair x y)
                    ((_,xs),(_,ys)) -> pure (Nothing,xs <> ys)
    inputs binders expression term = do
        charge
        case (expression,term) of
            (SourceWithInputs terms body,_) -> do
                nested <- inputs binders body term
                extras <- concat <$> traverse (\(SourceInput private value) -> snd <$> input (private <> binders) value) terms
                pure (nested <> extras)
            (SourceAtom atom,_) -> concat <$> traverse (fmap snd . input binders) (toList atom)
            (SourceAnd a b,CAnd left right) -> (<>) <$> inputs binders a left <*> inputs binders b right
            (SourceBind nested,CForall TySet body) -> inputs (TySet:binders) nested body
            (SourceExists nested,CExists TySet body) -> inputs (TySet:binders) nested body
            (SourceOr a b,COr left right) -> (<>) <$> inputs binders a left <*> inputs binders b right
            (SourceIff a b,CEq TyProp left right) -> (<>) <$> inputs binders a left <*> inputs binders b right
            (SourceRequire condition nested,CImp premise body) -> (<>) <$> inputs binders condition premise <*> inputs binders nested body
            (SourceResidual{},_) -> do
                checked <- step (\work -> countedAnalyseCanonicalOccurrences typing work (binders <> context) term)
                residual binders checked
            (SourceInputs _ terms,_) -> do
                concat <$> traverse (\(SourceInput private term) -> snd <$> input (private <> binders) term) terms
            _ -> impossible "an admitted whole input description lost its formula spine"
    residual binders occurrence = do
        charge
        if checkedOccurrenceType occurrence == TySet then
            step (\work -> countedRebaseCheckedOccurrence work occurrence)
                >>= maybe (pure []) (fmap snd . input binders . TemplateVariable . scopedCoreTerm)
        else case checkedOccurrenceView occurrence of
            OccurrenceApplication a b -> binary a b
            OccurrenceLambda _ body -> residual binders body
            OccurrenceNegation body -> residual binders body
            OccurrenceConjunction a b -> binary a b
            OccurrenceDisjunction a b -> binary a b
            OccurrenceImplication a b -> binary a b
            OccurrenceEquality _ a b -> binary a b
            OccurrenceUniversal _ body -> residual binders body
            OccurrenceExistential _ body -> residual binders body
            _ -> pure []
      where
        binary a b = (<>) <$> residual binders a <*> residual binders b
    -- Checked metadata already describes complete inputs. Analyse Core only
    -- at an undescribed residual, retaining its surrounding formula binders.
    collect = inputs [] evidence formula

data ScopedProjection = ScopedProjection
    { scopedProjectionRule :: !Rule.Rule
    , scopedProjectionCaptures :: !(Map ViewVariableIx (SetTermTemplate Leaves.OpaqueLeaf))
    , scopedProjectionPlan :: !Projection.ProjectionPlan
    }

data ScopedIntroduction = ScopedIntroduction
    { scopedIntroductionRule :: !Rule.Rule
    , scopedIntroductionCaptures :: !(Map ViewVariableIx (SetTermTemplate Leaves.OpaqueLeaf))
    , scopedIntroductionPlan :: !Introduction.Introduction
    }

type SourceAtom presentation termPresentation =
    Notion.SourceNotionOccurrence presentation
        (Source.SourceTermOccurrence termPresentation (ScopedCheckedCore ObjectId))
        (ScopedCheckedCore ObjectId)

type Compilation = Except.ExceptT (CountedCoreFailure Text)
    (State.State (Word, Leaves.OpaqueLeaves, Map Leaves.OpaqueLeaf ViewVariableIx))

data Purpose = CompileProducers | CompileEliminations | DescribeGoal

compileScopedSource
    :: Word -> [CoreType] -> [CoreType] -> CanonicalTerm ObjectId
    -> SourceEvidence SupportTermTemplate (SourceAtom presentation termPresentation) -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Text)
        ([ScopedProjection], [ScopedIntroduction], Maybe (UniversalBody (DescribedAtom Leaves.OpaqueLeaf)), Leaves.OpaqueLeaves), Word)
compileScopedSource = compileSource CompileProducers

compileScopedEliminations
    :: Word -> [CoreType] -> [CoreType] -> CanonicalTerm ObjectId
    -> SourceEvidence SupportTermTemplate (SourceAtom presentation termPresentation) -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Text) ([ScopedProjection], [ScopedIntroduction], Leaves.OpaqueLeaves), Word)
compileScopedEliminations allowance ambient original proposition evidence initial =
    let (result,remaining) = compileSource CompileEliminations allowance ambient original proposition evidence initial
    in (fmap (\(projections,introductions,_,leaves) -> (projections,introductions,leaves)) result,remaining)

describeScopedGoal
    :: Word -> [CoreType] -> [CoreType] -> CanonicalTerm ObjectId
    -> SourceEvidence SupportTermTemplate (SourceAtom presentation termPresentation) -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Text) (Maybe (UniversalBody (DescribedAtom Leaves.OpaqueLeaf)), Leaves.OpaqueLeaves), Word)
describeScopedGoal allowance ambient original proposition evidence initial =
    let (result,remaining) = compileSource DescribeGoal allowance ambient original proposition evidence initial
    in (fmap (\(_,_,described,leaves) -> (described,leaves)) result, remaining)

compileSource
    :: Purpose -> Word -> [CoreType] -> [CoreType] -> CanonicalTerm ObjectId
    -> SourceEvidence SupportTermTemplate (SourceAtom presentation termPresentation) -> Leaves.OpaqueLeaves
    -> (Either (CountedCoreFailure Text)
        ([ScopedProjection], [ScopedIntroduction], Maybe (UniversalBody (DescribedAtom Leaves.OpaqueLeaf)), Leaves.OpaqueLeaves), Word)
compileSource purpose allowance ambient original proposition evidence initial =
    let (result,(remaining,leaves,_)) = State.runState (Except.runExceptT compile) (allowance,initial,Map.empty)
    in (fmap (\(projections,introductions,described) -> (projections,introductions,described,leaves)) result,remaining)
  where
    step :: Show failure => (Word -> (Either (CountedCoreFailure failure) value, Word)) -> Compilation value
    step operation = do
        (available,leaves,captures) <- State.get
        let (result,remaining) = operation available
        State.put (remaining,leaves,captures)
        either (Except.throwE . fmap (Text.pack . show)) pure result
    charge :: Natural -> Compilation ()
    charge amount = do
        (available,leaves,captures) <- State.get
        if amount <= fromIntegral available
            then State.put (available-fromIntegral amount,leaves,captures)
            else State.put (0,leaves,captures) >> Except.throwE CountedCoreStructuralWorkExhausted
    invalid = Except.throwE . CountedCoreOperationFailed
    require message = maybe (invalid message) pure
    intern scoped = do
        (available,leaves,captures) <- State.get
        let (result,remaining) = Leaves.internOpaqueLeaf available scoped leaves
        State.put (remaining,leaves,captures)
        case result of
            Left Leaves.OpaqueLeafWorkExhausted -> Except.throwE CountedCoreStructuralWorkExhausted
            Left _ -> invalid "a local source capture lost its scope"
            Right (identifier,next) -> State.put (remaining,next,captures) >> pure identifier
    capture depth scoped = do
        value <- intern scoped
        (_,_,captures) <- State.get
        charge (indexWork (Map.size captures) 3)
        slot <- case Map.lookup value captures of
            Just slot -> pure slot
            Nothing -> do
                let slot = ViewVariableIx (fromIntegral (Map.size captures))
                State.modify' (\(remaining,leaves,_) -> (remaining,leaves,Map.insert value slot captures))
                pure slot
        let ViewVariableIx index = slot
        pure (TemplateVariable (ViewVariableIx (depth+index)))
    term depth occurrence = do
        charge 1
        let scoped = Source.sourceTermOccurrenceCore occurrence
        same <- step (\work -> countedCoreTypeListIdentity work
            (replicate (fromIntegral depth) TySet <> original) (scopedCoreContext scoped))
        unless (same && scopedCoreType scoped == TySet)
            (invalid "a local source term disagrees with its binder telescope")
        case (Source.sourceTermOccurrenceProvider occurrence,Source.sourceTermOccurrenceOrderedPair occurrence) of
            (Just provider,_) -> fmap (TemplateProvider (Source.sourceTermProviderHead provider)) . sequence
                <$> traverse (term depth) (Source.sourceTermProviderArguments provider)
            (_,Just (left,right)) -> liftA2 TemplateOrderedPair <$> term depth left <*> term depth right
            _ -> case scopedCoreTerm scoped of
                CBound index | index < depth -> pure (Just (TemplateVariable (ViewVariableIx index)))
                _ -> step (\work -> countedInstantiateScopedPrefix work depth Map.empty scoped) >>= \case
                    ScopedInstantiationOpen{} -> pure Nothing
                    ScopedInstantiationClosed captured -> do
                        aligned <- step (\work -> countedAlignScopedCore work ambient captured)
                            >>= require "a local source capture is outside the active scope"
                        closedSetValueWith (charge 1) aligned >>= \case
                            Just value -> pure (Just (TemplateClosed value))
                            Nothing -> Just <$> capture depth aligned
    atom depth expected occurrence = do
        charge 1
        let formula = Notion.sourceAssertionFormula occurrence
        sameContext <- step (\work -> countedCoreTypeListIdentity work
            (replicate (fromIntegral depth) TySet <> original) (scopedCoreContext formula))
        sameFormula <- step (\work -> countedCanonicalIdentity work expected (scopedCoreTerm formula))
        unless (sameContext && sameFormula && Notion.sourceAssertionPath occurrence == Notion.ConjunctionHere)
            (invalid "a local notion occurrence does not select its source")
        described <- sequence <$> traverse (term depth) (Notion.sourceAssertionAtom occurrence)
        aligned <- shiftCanonicalWith (charge 1) (fromIntegral (length ambient-length original)) depth expected
        pure (described,aligned)
    encode depth expected expression = do
        charge 1
        case (expression,expected) of
            (SourceResidual _,_) -> pure (SourceResidual Nothing)
            (SourceInputs _ terms,_) -> pure (SourceInputs Nothing terms)
            (SourceWithInputs terms body,_) -> withSourceInputs terms <$> encode depth expected body
            (SourceAtom occurrence,_) -> do
                described@(view,_) <- atom depth expected occurrence
                pure $ case view of
                    Nothing -> SourceInputs Nothing
                        (SourceInput [] . Source.sourceSupportTemplate scopedCoreTerm <$> toList (Notion.sourceAssertionAtom occurrence))
                    Just{} -> SourceAtom described
            (SourceAnd a b,CAnd left right) -> SourceAnd <$> encode depth left a <*> encode depth right b
            (SourceBind nested,CForall TySet body) -> SourceBind <$> encode (depth+1) body nested
            (SourceExists nested,CExists TySet body) -> SourceExists <$> encode (depth+1) body nested
            (SourceOr a b,COr left right) -> SourceOr <$> encode depth left a <*> encode depth right b
            (SourceIff a b,CEq TyProp left right) -> SourceIff <$> encode depth left a <*> encode depth right b
            (SourceRequire condition nested,CImp premise body) -> SourceRequire <$> encode depth premise condition <*> encode depth body nested
            _ -> invalid "a local source description disagrees with its checked formula"
    compile = do
        unless (length ambient >= length original) (invalid "a local source escaped its scope")
        encoded <- encode 0 proposition evidence
        (_,_,captures) <- State.get
        charge (fromIntegral (Map.size captures))
        let inputs = Map.fromList [(slot,TemplateVariable value) | (value,slot) <- Map.toAscList captures]
            arity = fromIntegral (Map.size inputs)
            key depth (ViewVariableIx index)
                | index < depth = UniversalBound (depth-index-1)
                | Just (TemplateVariable value) <- Map.lookup (ViewVariableIx (index-depth)) inputs = UniversalOuter value
                | otherwise = impossible "a local source lost its captured operand"
        keyed <- traverseAtDepth (\depth (view,formula) -> pure (fmap (fmap (key depth)) <$> view,formula)) encoded
        described <- universalBodyWith (charge 1) keyed
        (projections,introductions) <- case purpose of
            DescribeGoal -> pure ([],[])
            _ -> do
                formula <- shiftCanonicalWith (charge 1)
                    (arity + fromIntegral (length ambient-length original)) 0 proposition
                unshifted <- atomicMetadata encoded
                metadata <- traverseSourceAtDepth
                    (\depth -> traverse (shiftCanonicalWith (charge 1)
                        (arity + fromIntegral (length ambient-length original)) depth)) (const pure) unshifted
                base <- Rule.compileRuleFromPrefix charge (Just (Map.keysSet inputs)) arity
                    (Rule.scopedRulePrefix ambient) (WholeLeaf (describedResidualTemplate formula metadata))
                    >>= either (invalid . Text.pack . show) pure
                compiled <- case purpose of
                    CompileEliminations -> fmap (\(_,plan,rule) -> (plan,rule)) <$>
                        (Projection.compileWholeEliminations charge base >>= either (invalid . Text.pack . show) pure)
                    _ -> Projection.compileProjections charge base >>= either (invalid . Text.pack . show) pure
                introduced <- Introduction.compileIntroductions charge base >>= either (invalid . Text.pack . show) pure
                introductions <- for introduced \entry -> do
                    introducedCaptures <- for (Introduction.introductionCaptureSlots entry) \slot -> do
                        charge (indexWork (Map.size inputs) 1)
                        pure (inputs Map.! slot)
                    pure (ScopedIntroduction (Introduction.introductionRule entry) introducedCaptures (Introduction.introductionOperation entry))
                pure ([ScopedProjection rule inputs plan | (plan,rule) <- compiled],introductions)
        pure (projections,introductions,described)
    atomicMetadata expression = charge 1 >> case expression of
        SourceInputs _ inputs -> pure (SourceInputs Nothing inputs)
        SourceWithInputs inputs body -> withSourceInputs inputs <$> atomicMetadata body
        SourceResidual _ -> pure (SourceResidual Nothing)
        SourceAtom (Nothing,_) -> pure (SourceResidual Nothing)
        SourceAtom (Just view,_) -> pure (SourceAtom view)
        SourceAnd left right -> SourceAnd <$> atomicMetadata left <*> atomicMetadata right
        SourceBind body -> SourceBind <$> atomicMetadata body
        SourceExists body -> SourceExists <$> atomicMetadata body
        SourceOr a b -> SourceOr <$> atomicMetadata a <*> atomicMetadata b
        SourceIff a b -> SourceIff <$> atomicMetadata a <*> atomicMetadata b
        SourceRequire condition body -> SourceRequire <$> atomicMetadata condition <*> atomicMetadata body
