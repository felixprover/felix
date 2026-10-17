{-# LANGUAGE NoImplicitPrelude #-}

-- | Logical query alternatives lowered to the ordinary clause language.
-- Their conclusions retain exact formula identity; their local witness slots
-- are ordinary finite clause variables and survive only in the selected recipe.
module Felix.Checking.Notion.Introduction
    ( Introduction(..), IntroductionRule(..), compileIntroductions
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Notion.Goal
import Felix.Checking.Notion.Join (JoinFailure)
import Felix.Checking.Notion.Rule
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Semantic
import Control.Monad (foldM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)

data Introduction = IntroduceConjunction | IntroduceDisjunction !Bool | IntroduceExistential !ViewVariableIx
    deriving (Show,Eq,Ord)

data IntroductionRule = IntroductionRule
    { introductionRule :: !Rule
    , introductionOperation :: !Introduction
    -- New clause slot -> original source capture. Ordinary parameters and
    -- locally bound witnesses are deliberately absent from this mapping.
    , introductionCaptureSlots :: !(Map ViewVariableIx ViewVariableIx)
    }

compileIntroductions
    :: Monad m => (Natural -> m ()) -> Rule -> m (Either JoinFailure [IntroductionRule])
compileIntroductions charge original = Except.runExceptT $ concat <$> traverse compile (ruleWholeTemplates original)
  where
    (sourceArity,_,_) = ruleDescription original
    ambient = ruleAmbientTypes original
    compile template = do
        plan <- lift (compileGoal (charge 1) (residualTemplateFormula template)
            (fromMaybe (SourceResidual Nothing) (residualTemplateEvidence template)))
        walk 0 plan
    walk depth plan = do
        let arity = sourceArity+depth
        own <- case goalOperation plan of
            ConjunctionGoal left right -> generate depth arity IntroduceConjunction [] plan [left,right]
            DisjunctionGoal left right -> (<>)
                <$> generate depth arity (IntroduceDisjunction False) [] plan [left]
                <*> generate depth arity (IntroduceDisjunction True) [] plan [right]
            ExistentialGoal body | goalPositive body -> do
                -- Opening the nearest binder already gives its body the right
                -- nearest-first clause layout. Shift only the parent's free
                -- slots; its existential binder remains private in the target.
                formula <- lift (shiftCanonicalWith (charge 1) 1 0 (goalFormula plan))
                evidence <- lift (renameEvidence (\internal index -> pure
                    (if index < internal then index else index+1)) (goalEvidence plan))
                let target = describedResidualTemplate formula evidence
                generateTemplates (depth+1) (arity+1) (IntroduceExistential (ViewVariableIx 0))
                    [0] target [asTemplate body]
            _ -> pure []
        let nextDepth = case goalOperation plan of UniversalGoal{} -> depth+1; ExistentialGoal{} -> depth+1; _ -> depth
        nested <- concat <$> traverse (walk nextDepth) (goalChildren plan)
        pure (own <> nested)
    asTemplate plan = describedResidualTemplate (goalFormula plan) (goalEvidence plan)
    generate depth arity operation required target premises =
        generateTemplates depth arity operation required (asTemplate target) (asTemplate <$> premises)
    generateTemplates depth arity operation required target premises = do
        referenced <- lift (traverse (freeSlots arity) (target:premises))
        let selected = Set.toAscList (Set.fromList required <> Set.unions referenced)
            renaming = Map.fromList (zip selected [0..])
            width = fromIntegral (length selected)
            rename internal index
                | index < internal = pure index
                | index-internal >= arity = pure (index-arity+width)
                | otherwise = charge (indexWork (Map.size renaming) 1)
                    >> pure (internal + renaming Map.! (index-internal))
            remap (ViewVariableIx index) = ViewVariableIx (renaming Map.! index)
            captures = Map.fromList
                [(remap (ViewVariableIx index),ViewVariableIx (index-depth))
                | index <- selected, index >= depth,
                  Set.member (ViewVariableIx (index-depth)) (ruleCapturedSlots original)]
            external = case referenced of
                headSlots:bodySlots -> Set.map (remap . ViewVariableIx)
                    (headSlots <> (Set.fromList required `Set.difference` Set.unions bodySlots))
                [] -> Set.empty
        lift (charge (fromIntegral (length selected)))
        conclusion <- lift (renameTemplate rename target)
        conditions <- lift (traverse (renameTemplate rename) premises)
        prefix <- foldM (\prefix template -> Except.ExceptT (extendRulePrefix charge width prefix
            (premise template) (Just (residualTemplateFormula template)))) (scopedRulePrefix ambient) conditions
        compiled <- Except.ExceptT (compileRuleFromPrefixWithInputs charge
            external
            (if ruleIsScoped original then Just (Map.keysSet captures) else Nothing)
            width prefix (WholeLeaf conclusion))
        described <- lift (describeRuleConclusion charge (replicate (fromIntegral width) TySet <> ambient,
            residualTemplateFormula conclusion) compiled)
        let selectedOperation = case operation of
                IntroduceExistential slot -> IntroduceExistential (remap slot)
                other -> other
        pure [IntroductionRule (asIntroduction described) selectedOperation captures]
    -- Each generated operation depends on its immediate children. Flattening
    -- them here would duplicate every suffix of a skewed conjunction and lose
    -- the children's exact-evidence alternatives. Ordinary source clauses keep
    -- their existing flat atomic join path.
    premise template = tree (fromMaybe (SourceResidual Nothing) (residualTemplateEvidence template))
      where
        tree = \case
            SourceWithInputs _ body -> tree body
            SourceAtom atom -> RulePremiseAtom atom
            _ -> RulePremiseResidual template
    freeSlots arity template = do
        slots <- residualTemplateParametersWith (charge 1) template
        pure (Set.filter (< arity) (Set.map (\(ViewVariableIx index) -> index) slots))
    renameTemplate rename template = describedResidualTemplate
        <$> renameFormula rename 0 (residualTemplateFormula template)
        <*> renameEvidence rename (fromMaybe (SourceResidual Nothing) (residualTemplateEvidence template))
    renameFormula rename depth = traverseCanonicalBindings (charge 1)
        (\internal index -> CBound <$> rename internal index) depth
    renameEvidence rename = traverseSourceAtDepth
        (\depth -> traverse (renameFormula rename depth))
        (\depth -> traverse (traverse (\(ViewVariableIx index) -> ViewVariableIx <$> rename depth index)))
