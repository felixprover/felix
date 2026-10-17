{-# LANGUAGE NoImplicitPrelude #-}

-- | Translate admitted declaration interfaces to the common rule meaning.
-- The owner resolves each exact occurrence to its checked source and direct
-- authorization. These descriptions grant no permission to use that source.
module Felix.Checking.Notion.Registration
    ( compileRegistrationRules
    ) where

import Base
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Core qualified as Core
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Checking.Semantic
import Felix.Checking.Notion.Join (JoinFailure(..))
import Felix.Checking.Notion.Rule
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

compileRegistrationRules
    :: Monad m => (Natural -> m ())
    -> (SemanticFactOccurrenceFingerprint -> m (Identity.CheckedPropositionContent, Authority.DirectAuthorization))
    -> [Registration SemanticFactOccurrenceFingerprint]
    -> m (Either JoinFailure [(SemanticFactOccurrenceFingerprint, RegisteredRule)])
compileRegistrationRules charge resolve registrations = Except.runExceptT $
    for registrations \registration ->
      let branch = registrationBranch registration
      in case registrationBody registration of
        RegisterNotionView view -> do
            let source = viewPremise (notionViewPremise view)
            build (Just source) branch
                [RulePremiseAtom source] (notionViewConclusion view)
        RegisterNullaryProvider rule ->
            build Nothing branch []
                (AtomicLeaf (GlobalAtomTemplate (nullaryConclusion rule)
                    (Vector.singleton (TemplateProvider
                        (IntrinsicSourceProvider (nullaryProvider rule)) Vector.empty))))
        RegisterProviderResult rule -> do
            let provider = providerResultProvider rule
                value = TemplateProvider (resultProviderTemplateHead provider) (resultProviderTemplateArguments provider)
                result = fmap (\case ResultRuleTerm term -> term; ResultRuleProviderValue -> value)
                    (providerResultConclusion rule)
                premises = case providerResultPremises rule of
                    ProviderResultUnconditional -> []
                    ProviderResultGuarded bundles -> forest bundles
            build Nothing branch premises (AtomicLeaf result)
        RegisterBackwardNotion rule ->
            build Nothing branch
                (forest (backwardNotionPremises rule)) (AtomicLeaf (backwardNotionConclusion rule))
        RegisterFiniteEvidence rule -> do
            let skeleton = finiteEvidenceSkeleton rule
            buildWithArity (Just (checkedNotionRuleBinderArity skeleton)) Nothing branch
                (checkedNotionRulePremises skeleton) (AtomicLeaf (checkedNotionRuleConclusion skeleton))
        RegisterGraphDomain rule -> do
            let left = TemplateVariable (graphDomainLeft rule)
                right = TemplateVariable (graphDomainRight rule)
                graph = TemplateVariable (graphDomainGraph rule)
            build Nothing branch
                [RulePremiseAtom (MembershipAtomTemplate (TemplateOrderedPair left right) graph)]
                (AtomicLeaf (MembershipAtomTemplate left (TemplateProvider (graphDomainProvider rule) (Vector.singleton graph))))
        RegisterWholeConclusion rule ->
            buildWithArity (Just (wholeConclusionArity rule)) Nothing branch
                (wholeConclusionPremises rule) (WholeLeaf (wholeConclusionTemplate rule))
  where
    build = buildWithArity Nothing
    buildWithArity specifiedArity viewSource branch premises conclusion = do
        lift (charge 1)
        chargeSelector (semanticFactBranchPath branch)
        let occurrence = semanticFactBranchFact branch
        (proposition,authorization) <- lift (resolve occurrence)
        let term = Core.frozenCoreTerm (Identity.checkedPropositionTerm proposition)
        (arity,body) <- case specifiedArity of
            Nothing -> telescope term
            Just arity -> (\body -> (arity,body)) <$> open arity term
        (described,result) <- premiseFormulas premises body
        selected <- select (semanticFactBranchPath branch) result
        compiled <- case viewSource of
            Just source | definitionOrigin authorization ->
                RegisteredDefinition <$> Except.ExceptT (compileDescribedForwardRule charge arity source conclusion)
            _ -> RegisteredClassification <$> Except.ExceptT (compileDescribedRule charge arity described conclusion)
        let contextual formula = (replicate (fromIntegral arity) Core.TySet,formula)
        describedRule <- Except.ExceptT (describeRuleFormulas charge (contextual . snd <$> described) (contextual selected) compiled)
        pure (occurrence,describedRule)
    chargeSelector ConjunctionHere = pure ()
    chargeSelector (ConjunctionLeft rest) = lift (charge 1) >> chargeSelector rest
    chargeSelector (ConjunctionRight rest) = lift (charge 1) >> chargeSelector rest
    telescope term = do
        lift (charge 1)
        case term of
            Core.CForall Core.TySet body -> do
                (arity,inner) <- telescope body
                pure (arity+1,inner)
            _ -> pure (0,term)
    open 0 term = pure term
    open remaining (Core.CForall Core.TySet body) = lift (charge 1) >> open (remaining - 1) body
    open _ _ = Except.throwE JoinUnresolvedResult
    premiseFormulas [] result = pure ([],result)
    premiseFormulas (premise:rest) (Core.CImp formula body) = do
        lift (charge 1)
        (described,result) <- premiseFormulas rest body
        pure ((premise,formula):described,result)
    premiseFormulas _ _ = Except.throwE JoinUnresolvedResult
    select ConjunctionHere formula = pure formula
    select (ConjunctionLeft rest) (Core.CAnd left _) = lift (charge 1) >> select rest left
    select (ConjunctionRight rest) (Core.CAnd _ right) = lift (charge 1) >> select rest right
    select _ _ = Except.throwE JoinUnresolvedResult
    definitionOrigin = \case
        Authority.CheckedKernelConstruction Authority.CheckedDefinitionProjection{} -> True
        Authority.CheckedKernelConstruction (Authority.CheckedStructureLaw Authority.StructurePredicateComponent) -> True
        _ -> False
    forest (RulePremiseBundles trees) = toList trees
    viewPremise = \case
        GlobalNotionViewPremise head' terms -> GlobalAtomTemplate head' terms
        StructureNotionViewPremise head' terms -> StructureAtomTemplate head' terms
        ExactProviderMembershipPremise element provider arguments ->
            MembershipAtomTemplate element (TemplateProvider provider arguments)
