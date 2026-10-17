{-# LANGUAGE NoImplicitPrelude #-}

-- | Shared structural facts and premise checks for notion-rule terms. Internal so
-- semantic templates remain transport values while their recursive invariants
-- have one implementation.
module Felix.Checking.Notion.RuleTerm
    ( recursiveRuleTermTemplates
    , ruleTermTemplateVariables
    , ruleTermTemplateDeterminedBy
    , ProviderResultPremiseScope
    , providerResultPremiseScope
    , providerResultDeterminingVariables
    , validateProviderResultPremises
    , compileSourceRuleTermTemplate
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.SourceEvidence (UniversalBody(..))
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

-- Written construction precedes its denotation. Named providers retain their
-- exact identity; transparent abbreviations have already expanded here.
compileSourceRuleTermTemplate
    :: Natural
    -> SourceTerm.SourceTermOccurrence presentation (ScopedCheckedCore ObjectId)
    -> Either Text RuleTermTemplate
compileSourceRuleTermTemplate arity occurrence
    | Just provider <- SourceTerm.sourceTermOccurrenceProvider occurrence =
        TemplateProvider (SourceTerm.sourceTermProviderHead provider)
            <$> traverse (compileSourceRuleTermTemplate arity)
                (SourceTerm.sourceTermProviderArguments provider)
    | Just (left, right) <- SourceTerm.sourceTermOccurrenceOrderedPair occurrence =
        TemplateOrderedPair
            <$> compileSourceRuleTermTemplate arity left
            <*> compileSourceRuleTermTemplate arity right
    | CBound index <- core, index < arity =
        Right (TemplateVariable (ViewVariableIx index))
    | Just value <- closedSetValue (SourceTerm.sourceTermOccurrenceCore occurrence) =
        Right (TemplateClosed value)
    | otherwise = Left
        ("rule terms must be theorem variables, approved rich source terms, or closed sets; found "
            <> Text.pack (show core))
  where
    core = scopedCoreTerm (SourceTerm.sourceTermOccurrenceCore occurrence)


recursiveRuleTermTemplates
    :: RuleTermTemplate
    -> NonEmpty RuleTermTemplate
recursiveRuleTermTemplates term =
    term :| case term of
        TemplateClosed{} -> []
        TemplateVariable{} -> []
        TemplateProvider _head arguments ->
            concatMap
                (NonEmpty.toList . recursiveRuleTermTemplates)
                (toList arguments)
        TemplateOrderedPair left right ->
            NonEmpty.toList (recursiveRuleTermTemplates left)
                <> NonEmpty.toList (recursiveRuleTermTemplates right)

ruleTermTemplateVariables
    :: RuleTermTemplate
    -> Set ViewVariableIx
ruleTermTemplateVariables = foldMap Set.singleton

ruleTermTemplateDeterminedBy
    :: Set ViewVariableIx
    -> RuleTermTemplate
    -> Bool
ruleTermTemplateDeterminedBy determining template =
    ruleTermTemplateVariables template `Set.isSubsetOf` determining

-- Premise-only sets stay lazy: binder checks and unconditional rules need only
-- the determining variables. This scope is shared within one admission call.
data ProviderResultPremiseScope = ProviderResultPremiseScope
    { providerResultDeterminingVariables :: Set ViewVariableIx
    , providerResultArgumentSubterms :: Set RuleTermTemplate
    , providerResultAvailableTerms :: Set RuleTermTemplate
    }

providerResultPremiseScope
    :: ResultProviderTemplate
    -> ResultNotionRuleTemplate
    -> ProviderResultPremiseScope
providerResultPremiseScope provider conclusion =
    ProviderResultPremiseScope determining providerSubterms available
  where
    providerTerms = toList (resultProviderTemplateArguments provider)
    conclusionTerms = [term | ResultRuleTerm term <- toList conclusion]
    determining = foldMap ruleTermTemplateVariables (providerTerms <> conclusionTerms)
    subterms = Set.fromList . concatMap (NonEmpty.toList . recursiveRuleTermTemplates)
    providerSubterms = subterms providerTerms
    available = providerSubterms <> subterms conclusionTerms

validateProviderResultPremises
    :: ProviderResultPremiseScope
    -> ProviderResultPremises RuleTermTemplate
    -> Either (Natural, Text) ()
validateProviderResultPremises scope = \case
    ProviderResultUnconditional -> pure ()
    ProviderResultGuarded (RulePremiseBundles bundles) ->
        for_ (zip [0..] (toList bundles)) \(ordinal, bundle) ->
            first (\reason -> (ordinal, reason)) (validateTree bundle)
  where
    validateTree = \case
        RulePremiseAtom atom -> validateAtom atom
        RulePremiseResidual template ->
            unless (residualTemplateVariables template `Set.isSubsetOf` providerResultDeterminingVariables scope)
                (Left "a whole premise is not determined by the provider and conclusion")
        RulePremiseUniversal body -> do
            case body of
                UniversalBind{} -> pure ()
                _ -> Left "a supplied premise must start with a set binder"
            unless
                (all (ruleTermTemplateDeterminedBy (providerResultDeterminingVariables scope))
                    (foldMap (foldMap (foldMap toList)) body))
                (Left "a supplied universal premise is not determined by the provider and conclusion")
        RulePremiseAnd left right -> validateTree left *> validateTree right

    validateAtom atom = case atom of
        NegativeAtomTemplate body -> validateAtom body
        GlobalAtomTemplate head' arguments -> case globalNotionHeadRole head' of
            HostedGlobalNotion -> validateFocused (fst <$> Vector.uncons arguments) atom
            UnhostedGlobalPredicate ->
                unless (all (ruleTermTemplateDeterminedBy
                    (providerResultDeterminingVariables scope)) arguments)
                    (Left "a source-terminal provider-result premise is not determined by its provider and conclusion")
        StructureAtomTemplate _head arguments ->
            validateFocused (fst <$> Vector.uncons arguments) atom
        MembershipAtomTemplate element _set -> validateFocused (Just element) atom
        ExactStructureAtomTemplate _shape subject -> validateFocused (Just subject) atom

    validateFocused focus atom = do
        unless (maybe False (`Set.member` providerResultArgumentSubterms scope) focus)
            (Left "every hosted provider-result premise must focus on a strict provider argument or subterm")
        unless (all (`Set.member` providerResultAvailableTerms scope) atom)
            (Left "a provider-result premise contains a fresh or growing term")
