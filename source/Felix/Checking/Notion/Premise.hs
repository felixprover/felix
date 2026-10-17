{-# LANGUAGE NoImplicitPrelude #-}

-- | Compile the exact header forest shared by written classifications
-- and generated result registrations. Source syntax and its checked proposition
-- are validated together; no theorem premise can disappear during registration.
module Felix.Checking.Notion.Premise
    ( compilePremise
    , compileAtom, describeResidual
    ) where

import Base
import Control.Monad (unless)
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.RuleTerm qualified as RuleTerm
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as Source
import Numeric.Natural (Natural)

type Occurrence presentation = Notion.SourceNotionOccurrence presentation
    (Source.SourceTermOccurrence presentation (ScopedCheckedCore ObjectId))
    (ScopedCheckedCore ObjectId)

compileAtom
    :: Natural -> Occurrence presentation -> Either Text (AtomTemplate RuleTermTemplate)
compileAtom arity = traverse (RuleTerm.compileSourceRuleTermTemplate arity) . Notion.sourceAssertionAtom

compilePremise
    :: Natural -> ScopedCheckedCore ObjectId -> SourceEvidence SupportTermTemplate (Occurrence presentation)
    -> Either Text (RulePremiseTree RuleTermTemplate)
compilePremise arity proposition = tree (scopedCoreTerm proposition)
  where
    invalid = Left "a marked premise must be an exact positive notion conjunction or supplied set universal"
    tree expected = \case
        SourceWithInputs _ body -> tree expected body
        SourceAtom occurrence -> RulePremiseAtom <$> atom 0 expected occurrence
        SourceAnd left right | CAnd a b <- expected ->
            RulePremiseAnd <$> tree a left <*> tree b right
        expression@SourceBind{} -> case universal 0 expected expression of
            Right body -> Right (RulePremiseUniversal body)
            Left _ -> residual expected expression
        SourceAnd{} -> invalid
        expression -> residual expected expression
    residual expected expression = do
        template <- describedResidualTemplate expected <$>
            describeEvidence arity (scopedCoreContext proposition) expected expression
        unless (all (\(ViewVariableIx index) -> index < arity) (residualTemplateVariables template))
            (Left "a whole premise escapes its theorem context")
        pure (RulePremiseResidual template)
    atom depth expected occurrence = do
        let formula = Notion.sourceAssertionFormula occurrence
        unless (scopedCoreContext formula == replicate (fromIntegral depth) TySet <> scopedCoreContext proposition
            && scopedCoreTerm formula == expected
            && Notion.sourceAssertionPath occurrence == Notion.ConjunctionHere)
            (Left "a rule premise occurrence disagrees with its checked source or scope")
        compileAtom (arity + depth) occurrence
    universalAtom depth expected occurrence = fmap (fmap (fmap variable)) (atom depth expected occurrence)
      where
        variable (ViewVariableIx index)
            | index < depth = UniversalBound (depth - index - 1)
            | otherwise = UniversalOuter (TemplateVariable (ViewVariableIx (index - depth)))
    atoms depth expected = \case
        SourceWithInputs _ body -> atoms depth expected body
        SourceAtom occurrence -> AtomLeaf <$> universalAtom depth expected occurrence
        SourceAnd left right | CAnd a b <- expected ->
            AtomAnd <$> atoms depth a left <*> atoms depth b right
        _ -> invalid
    universal depth expected = \case
        SourceWithInputs _ body -> universal depth expected body
        SourceBind nested | CForall TySet rest <- expected ->
            UniversalBind <$> universal (depth + 1) rest nested
        SourceRequire guard nested | CImp p rest <- expected ->
            UniversalRequire <$> atoms depth p guard <*> universal depth rest nested
        expression -> UniversalReturn <$> atoms depth expected expression

-- Retain admitted eliminations alongside exact whole truth. Unsupported atom
-- patterns become opaque leaves; their interiors never acquire argument views.
describeResidual
    :: Natural -> ScopedCheckedCore ObjectId -> SourceEvidence SupportTermTemplate (Occurrence presentation)
    -> Either Text ResidualTemplate
describeResidual arity proposition evidence =
    describedResidualTemplate (scopedCoreTerm proposition) <$>
        describeEvidence arity (scopedCoreContext proposition) (scopedCoreTerm proposition) evidence

describeEvidence
    :: Natural -> [CoreType] -> CanonicalTerm ObjectId -> SourceEvidence SupportTermTemplate (Occurrence presentation)
    -> Either Text (SourceEvidence SupportTermTemplate (AtomTemplate RuleTermTemplate))
describeEvidence arity context = describe 0
  where
    invalid = Left "a whole source description disagrees with its checked formula"
    describe depth expected = \case
        SourceResidual{} -> pure (SourceResidual Nothing)
        SourceInputs _ terms -> pure (SourceInputs Nothing terms)
        SourceWithInputs terms body -> withSourceInputs terms <$> describe depth expected body
        SourceAtom occurrence -> do
            let formula = Notion.sourceAssertionFormula occurrence
            unless (scopedCoreContext formula == replicate (fromIntegral depth) TySet <> context
                && scopedCoreTerm formula == expected
                && Notion.sourceAssertionPath occurrence == Notion.ConjunctionHere) invalid
            pure (either (const (SourceInputs Nothing
                (SourceInput [] . Source.sourceSupportTemplate scopedCoreTerm <$> toList (Notion.sourceAssertionAtom occurrence))))
                SourceAtom (compileAtom (arity+depth) occurrence))
        SourceAnd a b -> case expected of
            CAnd left right -> SourceAnd <$> describe depth left a <*> describe depth right b
            _ -> invalid
        SourceBind body -> case expected of
            CForall TySet nested -> SourceBind <$> describe (depth+1) nested body
            _ -> invalid
        SourceExists body -> case expected of
            CExists TySet nested -> SourceExists <$> describe (depth+1) nested body
            _ -> invalid
        SourceOr a b -> case expected of
            COr left right -> SourceOr <$> describe depth left a <*> describe depth right b
            _ -> invalid
        SourceIff a b -> case expected of
            CEq TyProp left right -> SourceIff <$> describe depth left a <*> describe depth right b
            _ -> invalid
        SourceRequire a b -> case expected of
            CImp left right -> SourceRequire <$> describe depth left a <*> describe depth right b
            _ -> invalid
