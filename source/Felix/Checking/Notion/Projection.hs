{-# LANGUAGE NoImplicitPrelude #-}

-- | Compile checked source eliminations to ordinary finite clauses. Prefixes
-- and reverse proof paths are persistent, so siblings share their guards.
module Felix.Checking.Notion.Projection
    ( ProjectionStep(..), ProjectionPlan(..), compileProjections, compileWholeEliminations
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Notion.Rule
import Felix.Checking.Notion.Join (JoinFailure(..))
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.FormulaIndex (residualShape)
import Felix.Checking.Notion.WholePattern (compileWholePattern)
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Semantic
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Numeric.Natural (Natural)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data ProjectionStep
    = ProjectionBinder !Natural
    | ProjectionGuard !Natural
    | ProjectionConjunct !Bool
    | ProjectionBiconditionalGuard !Bool !Natural
    deriving (Show,Eq,Ord)

data ProjectionPlan = ProjectionPlan
    { projectionSourceArity :: !Natural
    , projectionSourcePremises :: !Natural
    -- Nearest elimination first, sharing the complete source prefix.
    , projectionReverseSteps :: ![ProjectionStep]
    }
    deriving (Show,Eq,Ord)

compileProjections
    :: Monad m => (Natural -> m ()) -> Rule
    -> m (Either JoinFailure [(ProjectionPlan,Rule)])
compileProjections charge original = case ruleDescription original of
    (_,_,AtomicLeaf{}) -> pure (Right [])
    (arity,premises,WholeLeaf template) -> fmap (fmap (fmap (\(plan,rule) -> (plan,inheritRuleSupport original rule)))) $
        compileProjected charge (if ruleIsScoped original then Just (ruleCapturedSlots original) else Nothing)
            (ruleAmbientTypes original) Set.empty arity (fromIntegral (length premises)) (rulePrefix original) template

-- Exact G is an ordinary premise, regardless of how its witness was obtained.
-- Compile these clauses before domain selection; publishing an introduced G
-- never mutates the admitted program or turns it into a new hypothesis.
compileWholeEliminations
    :: Monad m => (Natural -> m ()) -> Rule
    -> m (Either JoinFailure [(ResidualTemplate,ProjectionPlan,Rule)])
compileWholeEliminations charge original = Except.runExceptT $ fmap concat $
    for (ruleWholeTemplates original) \template -> if not (eliminable (residualTemplateFormula template)) then pure [] else do
            let (originalArity,_,_) = ruleDescription original
                scoped = ruleIsScoped original
                captures = if scoped then Just (ruleCapturedSlots original) else Nothing
                ambient = ruleAmbientTypes original
            (arity,source) <- if scoped then pure (originalArity,template) else lift (thin template)
            let inputs = Set.fromList [ViewVariableIx index | index <- take (fromIntegral arity) [0..]]
            prefix <- Except.ExceptT (extendRulePrefix charge arity (scopedRulePrefix ambient)
                (RulePremiseResidual source) (Just (residualTemplateFormula source)))
            sourceHead <- lift (residualShape (charge 1) (replicate (fromIntegral arity) TySet <> ambient) (residualTemplateFormula source))
            pattern' <- lift (compileWholePattern charge arity (residualTemplateFormula source))
            results <- Except.ExceptT (compileProjected charge captures ambient inputs arity 1 prefix source)
            let elimination = WholeElimination sourceHead pattern'
            pure [(source,plan,asWholeElimination elimination (inheritRuleSupport original rule)) | (plan,rule) <- results]
  where
    eliminable = \case
        CAnd{} -> True
        CForall TySet _ -> True
        CImp{} -> True
        CEq TyProp _ _ -> True
        _ -> False
    -- Parameters erased from this whole source must not require an arbitrary
    -- inhabitant of U. Rich source views also count: their fixed associations
    -- may mention a parameter erased from the Core denotation.
    thin template = do
        slots <- canonicalFreeIndicesWith (charge 1) (residualTemplateFormula template)
        metadata <- maybe (pure (SourceResidual Nothing)) pure (residualTemplateEvidence template)
        referenced <- for (sourceInputsAtDepth
            (fmap (fmap (\(ViewVariableIx index) -> CBound index)) . toList) metadata)
            \(SourceInput binders term) -> do
                free <- traverse (canonicalFreeIndicesWith (charge 1)) term
                let depth = fromIntegral (length binders)
                pure (Set.fromList [index-depth | indices <- toList free, index <- Set.toList indices, index >= depth])
        let selected = Set.toAscList (slots <> Set.unions referenced)
            renaming = Map.fromList (zip selected [0..])
            arity = fromIntegral (length selected)
            rename depth index
                | index < depth = pure index
                | otherwise = do
                    charge (indexWork (Map.size renaming) 1)
                    pure (depth + renaming Map.! (index-depth))
        charge (fromIntegral (length selected))
        let (originalArity,_,_) = ruleDescription original
        formula <- instantiateCanonicalPrefixWith (charge 1) originalArity
            (\depth index -> CBound <$> rename depth (depth+index)) 0 (residualTemplateFormula template)
        evidence <- traverseSourceAtDepth
            (\depth -> traverse (instantiateCanonicalPrefixWith (charge 1) originalArity
                (\internal index -> CBound <$> rename internal (internal+index)) depth))
            (\depth -> traverse (traverse (\(ViewVariableIx index) -> ViewVariableIx <$> rename depth index))) metadata
        pure (arity,describedResidualTemplate formula evidence)

compileProjected
    :: Monad m => (Natural -> m ()) -> Maybe (Set ViewVariableIx) -> [CoreType]
    -> Set ViewVariableIx -> Natural -> Natural -> RulePrefix -> ResidualTemplate
    -> m (Either JoinFailure [(ProjectionPlan,Rule)])
compileProjected charge captures ambient inputs sourceArity sourcePremises sourcePrefix template = Except.runExceptT $
            walk sourceArity sourcePremises sourcePremises 0 sourcePrefix []
                (residualTemplateFormula template) (fromMaybe (SourceResidual Nothing) (residualTemplateEvidence template))
  where
    walk arity baseCount guardPosition depth prefix steps formula evidence = do
        lift (charge 1)
        case (evidence,formula) of
            (SourceWithInputs _ body,_) -> walk arity baseCount guardPosition depth prefix steps formula body
            (SourceResidual{},CAnd _ _) -> walk arity baseCount guardPosition depth prefix steps formula
                (SourceAnd (SourceResidual Nothing) (SourceResidual Nothing))
            (SourceResidual{},CForall TySet _) -> walk arity baseCount guardPosition depth prefix steps formula
                (SourceBind (SourceResidual Nothing))
            (SourceResidual{},CImp _ _) -> walk arity baseCount guardPosition depth prefix steps formula
                (SourceRequire (SourceResidual Nothing) (SourceResidual Nothing))
            (SourceResidual{},CEq TyProp _ _) -> walk arity baseCount guardPosition depth prefix steps formula
                (SourceIff (SourceResidual Nothing) (SourceResidual Nothing))
            (SourceAnd a b,CAnd left right) -> (<>)
                <$> walk arity baseCount guardPosition depth prefix (ProjectionConjunct False:steps) left a
                <*> walk arity baseCount guardPosition depth prefix (ProjectionConjunct True:steps) right b
            (SourceBind nested,CForall TySet body) -> do
                whole <- finish arity baseCount depth prefix steps formula evidence
                nestedRules <- walk arity baseCount guardPosition (depth+1) prefix (ProjectionBinder (arity+depth):steps) body nested
                pure (whole <> nestedRules)
            (SourceRequire condition nested,CImp guard body) -> do
                (premise,exact) <- preparePremise arity depth guard condition
                next <- Except.ExceptT (extendRulePrefix charge (arity+depth) prefix premise (Just exact))
                walk arity baseCount (guardPosition+1) depth next (ProjectionGuard guardPosition:steps) body nested
            (SourceIff a b,CEq TyProp left right) -> do
                let direction reverseDirection conditionFormula condition body nested = do
                        (premise,exact) <- preparePremise arity depth conditionFormula condition
                        next <- Except.ExceptT (extendRulePrefix charge (arity+depth) prefix premise (Just exact))
                        walk arity baseCount (guardPosition+1) depth next
                            (ProjectionBiconditionalGuard reverseDirection guardPosition:steps) body nested
                (<>) <$> direction False left a right b <*> direction True right b left a
            _ -> finish arity baseCount depth prefix steps formula evidence
    finish _ _ _ _ [] _ _ = pure []
    finish arity baseCount depth prefix steps formula evidence = do
        conclusion <- case evidence of
            SourceAtom atom -> AtomicLeaf <$> traverse (traverse (renameVariable arity depth 0)) atom
            _ -> WholeLeaf <$> renameResidual arity depth formula evidence
        -- A vacuous quantified binder still has an elimination argument. It
        -- ranges over U just like another generated schema input, even when
        -- neither a guard nor the selected conclusion mentions it.
        let introduced = Set.fromList [ViewVariableIx index | index <- take (fromIntegral depth) [arity..]]
        lift (charge depth)
        compiled <- lift (compileRuleFromPrefixWithInputs charge (inputs <> introduced) captures
            (arity+depth) prefix conclusion)
        case compiled of
            Left JoinWholeConclusionUndetermined -> pure []
            Left JoinUndeterminedVariable{} -> pure []
            Left failure -> Except.throwE failure
            Right rule -> do
                exact <- renameFormula arity depth formula
                described <- lift (describeRuleConclusion charge (replicate (fromIntegral (arity+depth)) TySet <> ambient,exact) rule)
                pure [(ProjectionPlan arity baseCount steps,described)]
    preparePremise arity depth formula evidence = do
        exact <- renameFormula arity depth formula
        premise <- tree formula evidence
        pure (premise,exact)
      where
        tree formula' = \case
            SourceWithInputs _ body -> tree formula' body
            SourceAtom atom -> RulePremiseAtom <$> traverse (traverse (renameVariable arity depth 0)) atom
            SourceAnd a b | CAnd left right <- formula' -> RulePremiseAnd <$> tree left a <*> tree right b
            expression -> RulePremiseResidual <$> renameResidual arity depth formula' expression
    renameVariable arity depth internal (ViewVariableIx index) = do
        lift (charge 1)
        pure (ViewVariableIx (if index < internal then index else internal + rename arity depth (index-internal)))
    rename arity depth index
        | index < depth = arity + depth - index - 1
        | otherwise = index-depth
    renameFormula arity depth = renameFormulaAt arity depth 0
    renameFormulaAt arity depth protected formula = do
        -- Clause parameters form a prefix. A local source's lexical context
        -- follows it and must survive this permutation unchanged.
        let width = arity+depth
        prepared <- if null ambient then pure formula else
            shiftCanonicalWith (lift (charge 1)) width (width+protected) formula
        instantiateCanonicalPrefixWith (lift (charge 1)) width
            (\internal index -> pure (CBound (internal + rename arity depth index))) protected prepared
    renameResidual arity depth formula evidence = do
        exact <- renameFormula arity depth formula
        described <- traverseSourceAtDepth
            (\internal -> traverse (renameFormulaAt arity depth internal))
            (\internal -> traverse (traverse (renameVariable arity depth internal))) evidence
        pure (describedResidualTemplate exact described)
