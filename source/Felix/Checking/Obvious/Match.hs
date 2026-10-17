{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact first-order rule recognition for bounded obvious refutation.
-- Recursive checked syntax remains payload behind the compiled rule; the
-- coordinator gives retained rules and substitutions shallow request IDs.
module Felix.Checking.Obvious.Match
    ( MatchFailure(..)
    , RuleRecognition(..)
    , RuleProjectionCursor
    , RuleProjectionProgress(..)
    , RuleCoverage(..)
    , advanceRuleProjections
    , CompiledRule
    , compiledRuleBinderEnvironment
    , compiledRuleDemandPattern
    , CompiledPremise
    , compiledRulePremises
    , PremiseRecipe(..)
    , compiledRuleEliminations
    , compiledRuleContinuation
    , compiledRuleResultTemplate
    , compiledPremiseTemplate
    , compiledPremisePattern
    , PremisePattern(..)
    , TermPattern
    , termPatternTemplate
    , termPatternSlots
    , termPatternNode
    , TermPatternNode(..)
    , RigidHead(..)
    , recognizeRule
    , UniversalHint(..)
    , UniversalHintCursor
    , UniversalHintStep(..)
    , startUniversalHints
    , advanceUniversalHints
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Elimination qualified as Elimination
import Felix.Checking.GlobalTyping (GlobalTyping, lookupGlobalType)
import Felix.Checking.Obvious.LogicalView qualified as LogicalView
import Felix.Checking.Obvious.Search qualified as Search
import Felix.Checking.Obvious.Template qualified as Template

import Control.Monad.State.Strict (State)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Word (Word)
import Numeric.Natural (Natural)


data MatchFailure
    = MatchWorkExhausted
    | MatchIntegrityFailure !Text
    deriving stock (Show, Eq)

data RuleRecognition global
    = NotARule
    | RecognizedRule !(CompiledRule global)
    | ProjectedRules !(RuleProjectionCursor global)

-- Coverage describes the supported source syntax, not the substitutions found.
data RuleCoverage = FullRuleCoverage | PartialRuleCoverage
    deriving stock (Show, Eq)

data RuleProjectionCursor global = RuleProjectionCursor
    !RuleCoverage ![RuleContinuation global]

type RuleEliminations global =
    Seq (Elimination.EliminationStep Template.MatcherSlot (PremiseRecipe global))

-- The prefix and compiled leaves are shared by sibling result branches.
data RuleContinuation global
    = ContinueRule
        !(RuleEliminations global)
        !(Seq (CompiledPremise global))
        !(Search.CataloguedLogicalView global)

data RuleProjectionProgress global
    = RuleProjectionPending !(RuleProjectionCursor global)
    | RuleProjectionFound !(CompiledRule global) !(RuleProjectionCursor global)
    | RuleProjectionFinished !RuleCoverage

-- A leaf's polarity directs a search for complementary signed evidence. The
-- resulting substitution is only an ordering suggestion, never a premise.
data UniversalHint global = UniversalHint
    { universalHintPositive :: !Bool
    , universalHintPattern :: !(PremisePattern global)
    }

data UniversalHintCursor global = UniversalHintCursor
    ![(Bool, Search.CataloguedLogicalView global)]

data UniversalHintStep global
    = UniversalHintsFinished
    | UniversalHintsPending !(UniversalHintCursor global)
    | UniversalHintFound !(UniversalHint global) !(UniversalHintCursor global)

data CompiledRule global = CompiledRule
    !(CompiledTheoremBody global)
    !(RuleEliminations global)
    !(Template.CompiledTemplate global)
    !(Maybe (RuleProjectionCursor global))

data CompiledTheoremBody global
    = UniversalDemand !(PremisePattern global)
    | ImplicationChain
        !(CompiledPremise global)
        !(Seq (CompiledPremise global))

data CompiledPremise global = CompiledPremise
    !(Template.CompiledTemplate global)
    !(PremisePattern global)

-- Leaves are matched in source order. The tree retains each original
-- implication antecedent for reconstruction, including premises with no leaves.
data PremiseRecipe global
    = PremiseTruth
    | PremiseLeaf !(CompiledPremise global)
    | PremiseConjunction !(PremiseRecipe global) !(PremiseRecipe global)

compiledRuleBinderEnvironment
    :: CompiledRule global -> Template.BinderEnvironment
compiledRuleBinderEnvironment =
    Template.compiledTemplateBinderEnvironment . compiledRuleResultTemplate

compiledRulePremises :: CompiledRule global -> Seq (CompiledPremise global)
compiledRulePremises (CompiledRule body _steps _result _continuation) =
    case body of
        UniversalDemand{} -> Seq.empty
        ImplicationChain first rest -> first Seq.<| rest

compiledRuleDemandPattern :: CompiledRule global -> Maybe (PremisePattern global)
compiledRuleDemandPattern (CompiledRule body _steps _result _continuation) =
    case body of
        UniversalDemand pattern' -> Just pattern'
        ImplicationChain{} -> Nothing

compiledRuleResultTemplate :: CompiledRule global -> Template.CompiledTemplate global
compiledRuleResultTemplate (CompiledRule _body _steps result _continuation) = result

compiledRuleEliminations :: CompiledRule global -> RuleEliminations global
compiledRuleEliminations (CompiledRule _body steps _result _continuation) = steps

-- Continue through a structured intermediate only when that whole result
-- cannot be admitted. Otherwise its admitted formula owns subsequent discovery.
compiledRuleContinuation :: CompiledRule global -> Maybe (RuleProjectionCursor global)
compiledRuleContinuation (CompiledRule _body _steps _result continuation) = continuation

compiledPremiseTemplate :: CompiledPremise global -> Template.CompiledTemplate global
compiledPremiseTemplate (CompiledPremise template _pattern) = template

compiledPremisePattern :: CompiledPremise global -> PremisePattern global
compiledPremisePattern (CompiledPremise _template pattern') = pattern'

data PremisePattern global
    = AtomicPremise
        !(RigidHead global)
        ![TermPattern global]
    | EqualityPremise
        !Search.TypeId
        !(TermPattern global)
        !(TermPattern global)

data TermPattern global = TermPattern
    !(Template.CompiledTemplate global)
    !(Set.Set Template.MatcherSlot)
    !(TermPatternNode global)

termPatternTemplate
    :: TermPattern global
    -> Template.CompiledTemplate global
termPatternTemplate (TermPattern template _slots _node) = template

termPatternSlots
    :: TermPattern global
    -> Set.Set Template.MatcherSlot
termPatternSlots (TermPattern _template slots _node) = slots

termPatternNode :: TermPattern global -> TermPatternNode global
termPatternNode (TermPattern _template _slots node) = node

data TermPatternNode global
    = PatternVariable !Template.MatcherSlot
    | PatternRigid !(RigidHead global) ![TermPattern global]
    | PatternOpaqueGround

data RigidHead global
    = RigidGlobal !global
    | RigidIntrinsic !CoreIntrinsicTag
    | RigidOpaqueInteger !Integer
    | RigidAmbient !Natural
    deriving stock (Show, Eq, Ord)

type Compile value = Except.ExceptT MatchFailure (State Word) value

runCompile :: Word -> Compile value -> (Either MatchFailure value, Word)
runCompile structural action = State.runState (Except.runExceptT action) structural

charge :: Compile ()
charge = do
    remaining <- State.get
    if remaining == 0
        then Except.throwE MatchWorkExhausted
        else State.put $! remaining - 1

applicationSpine
    :: CanonicalTerm global
    -> Compile (CanonicalTerm global, [CanonicalTerm global], Int)
applicationSpine = collect [] 0
  where
    collect arguments arity term = do
        charge
        case term of
            CApp function argument ->
                collect (argument : arguments) (arity + 1) function
            headTerm -> pure (headTerm, arguments, arity)

sequenceMaybe :: [Maybe value] -> Compile (Maybe [value])
sequenceMaybe [] = pure (Just [])
sequenceMaybe (candidate : rest) = do
    charge
    case candidate of
        Nothing -> pure Nothing
        Just value -> fmap (value :) <$> sequenceMaybe rest

combinePatternSlots
    :: [TermPattern global]
    -> Compile (Set.Set Template.MatcherSlot)
combinePatternSlots = go Set.empty
  where
    go slots [] = pure slots
    go slots (patternTerm : rest) = do
        charge
        updated <- insertSlots slots
            (Set.toAscList (termPatternSlots patternTerm))
        go updated rest

    insertSlots slots [] = pure slots
    insertSlots slots (slot : rest) = do
        charge
        insertSlots (Set.insert slot slots) rest

runTemplate
    :: (Word -> (Either
            (CountedCoreFailure Template.TemplateError)
            value, Word))
    -> Compile value
runTemplate operation = do
    available <- State.get
    let (result, remaining) = operation available
    State.put $! remaining
    case result of
        Left CountedCoreStructuralWorkExhausted ->
            Except.throwE MatchWorkExhausted
        Left (CountedCoreOperationFailed failure) ->
            Except.throwE
                (MatchIntegrityFailure
                    ("checked rule template failed to compile: "
                        <> fromString (show failure)))
        Right value -> pure value

runCatalogue
    :: (Word -> (Either Search.CatalogueError value, Word))
    -> Compile value
runCatalogue operation = do
    available <- State.get
    let (result, remaining) = operation available
    State.put $! remaining
    case result of
        Left Search.CatalogueWorkExhausted ->
            Except.throwE MatchWorkExhausted
        Left (Search.CatalogueIntegrityFailure message) ->
            Except.throwE (MatchIntegrityFailure message)
        Left Search.CatalogueGroundTermLimitExhausted ->
            Except.throwE
                (MatchIntegrityFailure
                    "read-only rule compilation crossed the term cap")
        Left Search.CatalogueOutsideFrozenUniverse ->
            Except.throwE
                (MatchIntegrityFailure
                    "rule compilation unexpectedly performed a term census")
        Right value -> pure value

recognizeRule
    :: Bool
    -> GlobalTyping global
    -> Word
    -> Search.Catalogue global
    -> Search.CataloguedLogicalView global
    -> (Either MatchFailure (RuleRecognition global), Word)
recognizeRule extended globalType structural catalogue sourceView =
    runCompile structural do
        charge
        compileRulePath extended globalType catalogue Seq.empty Seq.empty sourceView

-- Open only the leading set binder. Eligibility and the frozen candidate
-- inventory belong to the executor; this cursor only inspects checked syntax.
startUniversalHints :: Search.CataloguedLogicalView global -> Maybe (UniversalHintCursor global)
startUniversalHints view = case LogicalView.logicalViewNode view of
    LogicalView.LogicalUniversal TySet body
        | LogicalView.logicalViewBinderDepth view == 0 -> Just (UniversalHintCursor [(True, body)])
    _ -> Nothing

-- One turn visits a connective or compiles one leaf with the ordinary counted
-- first-order pattern compiler. Nested binders deliberately stop this path.
advanceUniversalHints
    :: GlobalTyping global -> Word -> Search.Catalogue global -> UniversalHintCursor global
    -> (Either MatchFailure (UniversalHintStep global), Word)
advanceUniversalHints globalType structural catalogue (UniversalHintCursor pending) =
    runCompile structural do
        charge
        case pending of
            [] -> pure UniversalHintsFinished
            (positive, current) : rest ->
                let following = UniversalHintCursor rest
                    continue children = pure (UniversalHintsPending (UniversalHintCursor (children <> rest)))
                    leaf = compilePremisePattern globalType catalogue current >>= \case
                        Nothing -> pure (UniversalHintsPending following)
                        Just pattern' -> bindsOuter pattern' >>= \binds -> pure
                            (if binds then UniversalHintFound (UniversalHint positive pattern') following
                                else UniversalHintsPending following)
                in case LogicalView.logicalViewNode current of
                    LogicalView.LogicalNegation body -> continue [(not positive, body)]
                    LogicalView.LogicalConjunction left right -> continue [(positive, left), (positive, right)]
                    LogicalView.LogicalDisjunction left right -> continue [(positive, left), (positive, right)]
                    LogicalView.LogicalImplication premise conclusion -> continue [(not positive, premise), (positive, conclusion)]
                    LogicalView.LogicalEquality{} -> leaf
                    LogicalView.LogicalNeutral -> leaf
                    _ -> pure (UniversalHintsPending following)
  where
    bindsOuter pattern' = anyOuter case pattern' of
        AtomicPremise _head patterns -> patterns
        EqualityPremise _type left right -> [left, right]
    anyOuter [] = pure False
    anyOuter (pattern' : rest) = do
        charge
        if Set.member (Template.MatcherSlot 0) (termPatternSlots pattern')
            then pure True
            else anyOuter rest

-- A turn exposes one conjunction node or compiles one leaf. Paths share their
-- parents, and discovered rules can run before the remaining source is examined.
advanceRuleProjections
    :: GlobalTyping global
    -> Word
    -> Search.Catalogue global
    -> RuleProjectionCursor global
    -> (Either MatchFailure (RuleProjectionProgress global), Word)
advanceRuleProjections globalType structural catalogue (RuleProjectionCursor coverage pending) =
    runCompile structural do
        charge
        case pending of
            [] -> pure (RuleProjectionFinished coverage)
            ContinueRule steps leaves current : rest ->
                compileRulePath True globalType catalogue steps leaves current >>= \case
                    NotARule -> pure (RuleProjectionPending (RuleProjectionCursor PartialRuleCoverage rest))
                    RecognizedRule rule -> pure (RuleProjectionFound rule (RuleProjectionCursor coverage rest))
                    ProjectedRules (RuleProjectionCursor _childrenCoverage children) ->
                        pure (RuleProjectionPending (RuleProjectionCursor coverage (children <> rest)))

-- Inspect the actual source order. A selected branch retains the preceding
-- instantiations and whole antecedents, even when more binders follow them.
compileRulePath
    :: Bool
    -> GlobalTyping global
    -> Search.Catalogue global
    -> RuleEliminations global
    -> Seq (CompiledPremise global)
    -> Search.CataloguedLogicalView global
    -> Compile (RuleRecognition global)
compileRulePath extended globalType catalogue = go
  where
    go steps leaves current = do
        charge
        case LogicalView.logicalViewNode current of
            LogicalView.LogicalUniversal TySet body ->
                let slot = Template.MatcherSlot (LogicalView.logicalViewBinderDepth current)
                    following = steps Seq.|> Elimination.Instantiate TySet slot
                in case Seq.viewl leaves of
                    Seq.EmptyL -> go following leaves body
                    first Seq.:< rest ->
                        pure (RecognizedRule (CompiledRule (ImplicationChain first rest) steps
                            (LogicalView.logicalViewResidualTemplate current)
                            (Just (RuleProjectionCursor FullRuleCoverage
                                [ContinueRule following leaves body]))))
            LogicalView.LogicalUniversal{}
                | not (Seq.null leaves) -> finishRule current leaves steps
                | otherwise -> pure NotARule
            LogicalView.LogicalImplication premise conclusion -> do
                premiseResult <- compilePremise premise leaves
                case premiseResult of
                    Nothing -> pure NotARule
                    Just (recipe, followingLeaves) ->
                        go (steps Seq.|> Elimination.Apply recipe) followingLeaves conclusion
            LogicalView.LogicalConjunction left right
                | extended, not (Seq.null steps) ->
                    let continuation = RuleProjectionCursor FullRuleCoverage
                            [ContinueRule (steps Seq.|> Elimination.ProjectLeft) leaves left,
                             ContinueRule (steps Seq.|> Elimination.ProjectRight) leaves right]
                    in case Seq.viewl leaves of
                        Seq.EmptyL -> pure (ProjectedRules continuation)
                        first Seq.:< rest -> pure (RecognizedRule
                            (CompiledRule (ImplicationChain first rest) steps
                                (LogicalView.logicalViewResidualTemplate current) (Just continuation)))
            _ -> finishRule current leaves steps

    compilePremise current leaves = case LogicalView.logicalViewNode current of
        LogicalView.LogicalTruth | extended -> do
            charge
            pure (Just (PremiseTruth, leaves))
        LogicalView.LogicalConjunction left right | extended -> do
            charge
            compilePremise left leaves >>= \case
                Nothing -> pure Nothing
                Just (leftRecipe, afterLeft) ->
                    compilePremise right afterLeft >>= \case
                        Nothing -> pure Nothing
                        Just (rightRecipe, afterRight) ->
                            pure (Just (PremiseConjunction leftRecipe rightRecipe, afterRight))
        _ -> do
            patternResult <- compilePremisePattern globalType catalogue current
            pure (case patternResult of
                Nothing -> Nothing
                Just premisePattern ->
                    let leaf = CompiledPremise
                            (LogicalView.logicalViewResidualTemplate current) premisePattern
                    in Just (PremiseLeaf leaf, leaves Seq.|> leaf))

    finishRule current leaves steps =
        let result = LogicalView.logicalViewResidualTemplate current
            binders = Template.compiledTemplateBinderEnvironment result
        in case Seq.viewl leaves of
            first Seq.:< rest ->
                pure (RecognizedRule (CompiledRule (ImplicationChain first rest) steps result Nothing))
            Seq.EmptyL
                | Template.binderEnvironmentCount binders == 0 -> pure NotARule
                | otherwise -> do
                    patternResult <- compilePremisePattern globalType catalogue current
                    pure
                        (case patternResult of
                            Nothing -> NotARule
                            Just demand ->
                                RecognizedRule (CompiledRule (UniversalDemand demand) steps result Nothing))

compileTerm
    :: GlobalTyping global
    -> Template.BinderEnvironment
    -> CanonicalTerm global
    -> Compile (Template.CompiledTemplate global)
compileTerm globalType binders term =
    runTemplate
        (\work ->
            Template.compileTemplate
                globalType work binders term)

compilePremisePattern
    :: GlobalTyping global
    -> Search.Catalogue global
    -> LogicalView.LogicalView global payload
    -> Compile (Maybe (PremisePattern global))
compilePremisePattern globalType catalogue view = do
    charge
    let template = LogicalView.logicalViewResidualTemplate view
        binders = Template.compiledTemplateBinderEnvironment template
        binderCount = Template.binderEnvironmentCount binders
        ambient = Template.binderEnvironmentAmbientContext binders
    case LogicalView.logicalViewNode view of
        LogicalView.LogicalEquality checkedLeft checkedRight -> do
            let operandType = scopedCoreType checkedLeft
                left = scopedCoreTerm checkedLeft
                right = scopedCoreTerm checkedRight
            operandTypeId <-
                runCatalogue
                    (\work ->
                        Search.findCatalogueTypeCounted
                            work catalogue operandType) >>= \case
                    Nothing ->
                        Except.throwE
                            (MatchIntegrityFailure
                                "equality premise type is absent from the frozen catalogue")
                    Just typeId -> pure typeId
            case operandType of
                TySet -> do
                    leftPattern <-
                        compileSetPattern
                            globalType binders left
                    rightPattern <-
                        compileSetPattern
                            globalType binders right
                    pure
                        (EqualityPremise operandTypeId
                            <$> leftPattern <*> rightPattern)
                _ -> do
                    leftPattern <-
                        compileOpaquePattern
                            globalType binders left
                    rightPattern <-
                        compileOpaquePattern
                            globalType binders right
                    pure
                        (EqualityPremise operandTypeId
                            <$> leftPattern <*> rightPattern)
        LogicalView.LogicalNeutral -> do
            let term = scopedCoreTerm (Template.compiledTemplateTerm template)
            (headTerm, arguments, arity) <- applicationSpine term
            rigid <-
                compileRigidHead
                    globalType ambient binderCount TyProp
                    headTerm arity
            case rigid of
                Nothing -> pure Nothing
                Just headPattern -> do
                    compiledArguments <-
                        traverse
                            (compileSetPattern
                                globalType binders)
                            arguments
                    patterns <- sequenceMaybe compiledArguments
                    pure
                        (AtomicPremise headPattern <$> patterns)
        _ -> pure Nothing

compileSetPattern
    :: GlobalTyping global
    -> Template.BinderEnvironment
    -> CanonicalTerm global
    -> Compile (Maybe (TermPattern global))
compileSetPattern globalType binders term = do
    charge
    template <- compileTerm globalType binders term
    let binderCount = Template.binderEnvironmentCount binders
        ambient = Template.binderEnvironmentAmbientContext binders
    if scopedCoreType (Template.compiledTemplateTerm template) /= TySet
        then pure Nothing
        else do
            (headTerm, arguments, arity) <- applicationSpine term
            case (headTerm, arguments) of
                (CBound index, [])
                    | index < binderCount ->
                        let slot =
                                Template.MatcherSlot
                                    (binderCount - index - 1)
                        in pure
                            (Just
                                (TermPattern template
                                    (Set.singleton slot)
                                    (PatternVariable slot)))
                _ -> do
                    rigid <-
                        compileRigidHead
                            globalType ambient binderCount TySet
                            headTerm arity
                    case rigid of
                        Nothing -> pure Nothing
                        Just headPattern -> do
                            compiledArguments <-
                                traverse
                                    (compileSetPattern
                                        globalType binders)
                                    arguments
                            patternsResult <-
                                sequenceMaybe compiledArguments
                            case patternsResult of
                                Nothing -> pure Nothing
                                Just patterns -> do
                                    slots <- combinePatternSlots patterns
                                    pure
                                        (Just
                                            (TermPattern template slots
                                                (PatternRigid headPattern
                                                    patterns)))

compileOpaquePattern
    :: GlobalTyping global
    -> Template.BinderEnvironment
    -> CanonicalTerm global
    -> Compile (Maybe (TermPattern global))
compileOpaquePattern globalType binders term = do
    let binderCount = Template.binderEnvironmentCount binders
    template <- compileTerm globalType binders term
    slots <- matcherSlots binderCount 0 term
    pure
        (if Set.null slots
            then
                Just
                    (TermPattern template Set.empty PatternOpaqueGround)
            else Nothing)

compileRigidHead
    :: GlobalTyping global
    -> [CoreType]
    -> Natural
    -> CoreType
    -> CanonicalTerm global
    -> Int
    -> Compile (Maybe (RigidHead global))
compileRigidHead globalType ambient binderCount expectedResult
        headTerm arity = do
    charge
    found <- case headTerm of
        CGlobal global ->
            pure
                ((\coreType -> (RigidGlobal global, coreType))
                    <$> lookupGlobalType globalType global)
        CIntrinsic intrinsic ->
            pure
                (Just
                    (RigidIntrinsic intrinsic, coreIntrinsicType intrinsic))
        COpaqueInteger integer ->
            pure (Just (RigidOpaqueInteger integer, TySet))
        CBound index
            | index >= binderCount -> do
                let ambientSlot = index - binderCount
                ambientType <- countedNth ambientSlot ambient
                pure
                    ((\coreType -> (RigidAmbient ambientSlot, coreType))
                        <$> ambientType)
        _ -> pure Nothing
    case found of
        Nothing -> pure Nothing
        Just (rigid, headType) -> do
            shape <- firstOrderShape 0 headType
            pure do
                (foundArity, resultType) <- shape
                guard
                    ( foundArity == arity
                        && sameFirstOrderResult resultType expectedResult
                    )
                pure rigid
  where
    sameFirstOrderResult TySet TySet = True
    sameFirstOrderResult TyProp TyProp = True
    sameFirstOrderResult _found _expected = False

    firstOrderShape foundArity coreType = do
        charge
        case coreType of
            TyArrow TySet result ->
                firstOrderShape (foundArity + 1) result
            result@TySet -> pure (Just (foundArity, result))
            result@TyProp -> pure (Just (foundArity, result))
            _ -> pure Nothing

    countedNth _position [] = pure Nothing
    countedNth position (value : rest) = do
        charge
        if position == 0
            then pure (Just value)
            else countedNth (position - 1) rest

matcherSlots
    :: Natural
    -> Natural
    -> CanonicalTerm global
    -> Compile (Set.Set Template.MatcherSlot)
matcherSlots binderCount innerDepth term = do
    charge
    case term of
        CBound index
            | index >= innerDepth
              && index < innerDepth + binderCount ->
                let reversePosition = index - innerDepth
                in pure
                    (Set.singleton
                        (Template.MatcherSlot
                            (binderCount - reversePosition - 1)))
            | otherwise -> pure Set.empty
        CApp function argument ->
            binary function argument
        CLam _ body -> matcherSlots binderCount (innerDepth + 1) body
        CNot proposition -> matcherSlots binderCount innerDepth proposition
        CAnd left right -> binary left right
        COr left right -> binary left right
        CImp premise conclusion -> binary premise conclusion
        CEq _ left right -> binary left right
        CForall _ body -> matcherSlots binderCount (innerDepth + 1) body
        CExists _ body -> matcherSlots binderCount (innerDepth + 1) body
        _ -> pure Set.empty
  where
    binary left right = do
        leftSlots <- matcherSlots binderCount innerDepth left
        rightSlots <- matcherSlots binderCount innerDepth right
        unionSlots leftSlots (Set.toAscList rightSlots)

    unionSlots slots [] = pure slots
    unionSlots slots (slot : rest) = do
        charge
        unionSlots (Set.insert slot slots) rest
