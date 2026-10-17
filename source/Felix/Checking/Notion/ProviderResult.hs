{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Pure source-shape validation for provider-result rules.  Written
-- classifications and generated definition-result facts pass through this
-- single seam before they can become operational notion registrations.
module Felix.Checking.Notion.ProviderResult
    ( ProviderResultSubject
    , writtenProviderResultSubject
    , definitionProviderResultSubject
    , prepareWrittenProviderResultRuleTemplates
    , prepareGuardedDefinitionResultRuleTemplates
    , ProviderResultError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion
import Felix.Checking.Notion.RuleTerm qualified as RuleTerm
import Felix.Checking.Notion.Premise qualified as Premise
import Felix.Checking.Notion.SourceEvidence (SourceEvidence)
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as SourceTerm

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


type ScopedSourceTerm presentation =
    SourceTerm.SourceTermOccurrence
        presentation
        (ScopedCheckedCore ObjectId)

type ScopedNotionOccurrence presentation =
    SourceNotionOccurrence
        presentation
        (ScopedSourceTerm presentation)
        (ScopedCheckedCore ObjectId)

-- Ordinals index the complete logical-premise telescope, not raw headers.
-- Neutral and grouped source headers need not correspond one-to-one to rows.
data ProviderResultError = ProviderResultError
    { providerResultErrorPremise :: !(Maybe Natural)
    , providerResultErrorReason :: !Text
    } deriving stock (Show, Eq)

data ProviderResultSubject presentation
    = WrittenProviderResultSubject
        !(SourceTerm.SourceTermProvider
            presentation
            (ScopedCheckedCore ObjectId))
    | DefinitionProviderResultSubject
        !ResultProviderTemplate
        !(ScopedSourceTerm presentation)

writtenProviderResultSubject
    :: SourceTerm.SourceTermProvider
        presentation
        (ScopedCheckedCore ObjectId)
    -> ProviderResultSubject presentation
writtenProviderResultSubject = WrittenProviderResultSubject

definitionProviderResultSubject
    :: ResultProviderTemplate
    -> ScopedSourceTerm presentation
    -> ProviderResultSubject presentation
definitionProviderResultSubject = DefinitionProviderResultSubject

-- | Prepare a written classification.  Absence of compiled logical headers is
-- the sole route to the premise-free mode; every nonempty header list must
-- compile as the existing guarded premise forest.
prepareWrittenProviderResultRuleTemplates
    :: Natural
    -> [( ScopedCheckedCore ObjectId
        , SourceEvidence SupportTermTemplate (ScopedNotionOccurrence presentation)
        )]
    -> ScopedNotionOccurrence presentation
    -> ProviderResultSubject presentation
    -> Either
        ProviderResultError
        ( ResultProviderTemplate
        , ProviderResultPremises RuleTermTemplate
        , ResultNotionRuleTemplate
        )
prepareWrittenProviderResultRuleTemplates binderArity premiseSources
        conclusionAssertion subject = do
    premises <- case NonEmpty.nonEmpty premiseSources of
        Nothing -> pure ProviderResultUnconditional
        Just presentSources ->
            ProviderResultGuarded
                <$> compileGuardedPremises binderArity presentSources
    (provider, conclusion) <- prepareProviderResultRuleTemplates
        binderArity premises conclusionAssertion subject
    pure (provider, premises, conclusion)

-- | Prepare a generated definition-result rule.  This entry point preserves
-- the definition feature's nonempty-header contract in its result type.
prepareGuardedDefinitionResultRuleTemplates
    :: Natural
    -> [( ScopedCheckedCore ObjectId
        , SourceEvidence SupportTermTemplate (ScopedNotionOccurrence presentation)
        )]
    -> ScopedNotionOccurrence presentation
    -> ProviderResultSubject presentation
    -> Either
        ProviderResultError
        ( ResultProviderTemplate
        , RulePremiseBundles RuleTermTemplate
        , ResultNotionRuleTemplate
        )
prepareGuardedDefinitionResultRuleTemplates binderArity premiseSources
        conclusionAssertion subject = do
    presentSources <- maybe
        (Left . ProviderResultError Nothing $
            "a provider-result rule needs one or more logical claim-header premises")
        Right
        (NonEmpty.nonEmpty premiseSources)
    premises <- compileGuardedPremises binderArity presentSources
    (provider, conclusion) <- prepareProviderResultRuleTemplates
        binderArity (ProviderResultGuarded premises)
        conclusionAssertion subject
    pure (provider, premises, conclusion)

compileGuardedPremises
    :: Natural
    -> NonEmpty
        ( ScopedCheckedCore ObjectId
        , SourceEvidence SupportTermTemplate (ScopedNotionOccurrence presentation)
        )
    -> Either ProviderResultError (RulePremiseBundles RuleTermTemplate)
compileGuardedPremises binderArity sources =
    RulePremiseBundles
        <$> traverse (\(ordinal, (proposition, assertions)) ->
            first (ProviderResultError (Just ordinal))
                (compilePremiseBundle binderArity proposition assertions))
            (NonEmpty.zip (0 :| [1..]) sources)

compilePremiseBundle
    :: Natural
    -> ScopedCheckedCore ObjectId
    -> SourceEvidence SupportTermTemplate (ScopedNotionOccurrence presentation)
    -> Either Text (RulePremiseTree RuleTermTemplate)
compilePremiseBundle = Premise.compilePremise

compileRuleTermTemplate
    :: Natural
    -> ScopedSourceTerm presentation
    -> Either Text RuleTermTemplate
compileRuleTermTemplate = RuleTerm.compileSourceRuleTermTemplate

-- | Validate the theorem-independent provider/result shape shared by both
-- source policies.  The theorem context is nearest-first de Bruijn order.
prepareProviderResultRuleTemplates
    :: Natural
    -> ProviderResultPremises RuleTermTemplate
    -> ScopedNotionOccurrence presentation
    -> ProviderResultSubject presentation
    -> Either ProviderResultError (ResultProviderTemplate, ResultNotionRuleTemplate)
prepareProviderResultRuleTemplates binderArity premises
        conclusionAssertion subject = do
    (providerTemplate, expectedFocus) <-
        first (ProviderResultError Nothing) (prepareSubject subject)
    conclusionTemplate <-
        first (ProviderResultError Nothing)
            (compileResultConclusionTemplate conclusionAssertion expectedFocus)
    let scope = RuleTerm.providerResultPremiseScope providerTemplate conclusionTemplate
        theoremVariables = RuleTerm.providerResultDeterminingVariables scope
        expectedVariables =
            if binderArity == 0
            then Set.empty
            else Set.fromList
                [ ViewVariableIx index
                | index <- [0 .. binderArity - 1]
                ]
    unless (theoremVariables == expectedVariables)
        (Left . ProviderResultError Nothing $
            "the provider occurrence and requested conclusion must determine every theorem variable")
    first (\(ordinal, reason) -> ProviderResultError (Just ordinal) reason)
        (RuleTerm.validateProviderResultPremises scope premises)
    pure (providerTemplate, conclusionTemplate)
  where
    prepareSubject = \case
        WrittenProviderResultSubject provider -> do
            arguments <- traverse (compileRuleTermTemplate binderArity)
                (SourceTerm.sourceTermProviderArguments provider)
            let template = resultProviderTemplate
                    (SourceTerm.sourceTermProviderHead provider) arguments
            pure (template, WrittenResultFocus template)
        DefinitionProviderResultSubject provider body ->
            pure (provider, DefinitionResultFocus body)

    compileResultConclusionTemplate assertion = compileResultAtom (sourceAssertionAtom assertion)
    compileResultAtom atom expectedFocus = case atom of
        NegativeAtomTemplate body -> withAtomPolarity NegativePolarity <$> compileResultAtom body expectedFocus
        GlobalAtomTemplate head' arguments -> do
            unless (globalNotionHeadRole head' == HostedGlobalNotion)
                (Left "a source-terminal global predicate cannot be a provider-result conclusion")
            GlobalAtomTemplate head' <$> compileFocusedArguments expectedFocus arguments
        StructureAtomTemplate head' arguments ->
            StructureAtomTemplate head' <$> compileFocusedArguments expectedFocus arguments
        MembershipAtomTemplate element set -> do
            requireFocus expectedFocus element
            setTerm <- compileRuleTermTemplate binderArity set
            pure (MembershipAtomTemplate ResultRuleProviderValue (ResultRuleTerm setTerm))
        ExactStructureAtomTemplate shape focus -> do
            requireFocus expectedFocus focus
            pure (ExactStructureAtomTemplate shape ResultRuleProviderValue)

    compileFocusedArguments expectedFocus arguments =
        case Vector.uncons arguments of
            Nothing -> Left "a result notion has no subject"
            Just (focus, remaining) -> do
                requireFocus expectedFocus focus
                tailTerms <- traverse
                    (compileRuleTermTemplate binderArity) remaining
                pure
                    (Vector.cons
                        ResultRuleProviderValue
                        (ResultRuleTerm <$> tailTerms))

    requireFocus expected actual = case expected of
        WrittenResultFocus provider -> do
            actualProvider <- maybe
                (Left
                    "a provider-result conclusion has no provider at notion focus")
                Right
                (SourceTerm.sourceTermOccurrenceProvider actual)
            actualArguments <- traverse (compileRuleTermTemplate binderArity)
                (SourceTerm.sourceTermProviderArguments actualProvider)
            unless
                ( SourceTerm.sourceTermProviderHead actualProvider
                    == resultProviderTemplateHead provider
                  && actualArguments == resultProviderTemplateArguments provider
                )
                (Left
                    "the provider-result focus differs from its selected provider occurrence")
        DefinitionResultFocus body ->
            unless
                ( SourceTerm.sourceTermOccurrenceCore actual
                    == SourceTerm.sourceTermOccurrenceCore body
                )
                (Left
                    "the definition result focus differs from its checked definiens")

data ResultFocus presentation
    = WrittenResultFocus !ResultProviderTemplate
    | DefinitionResultFocus !(ScopedSourceTerm presentation)
