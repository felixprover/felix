{-# LANGUAGE NoImplicitPrelude #-}

-- | Operations on a universal's own telescope and its separate outer terms.
module Felix.Checking.Notion.UniversalTemplate
    ( traverseOuter
    , flattenOuter
    , lowerAtom
    , traverseBodyAtDepth
    ) where

import Base
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Semantic
import Numeric.Natural (Natural)

traverseOuter :: Applicative m => (a -> m b) -> UniversalTemplate a -> m (UniversalTemplate b)
traverseOuter = traverse . traverse . traverse . traverse

-- Convert to ordinary nearest-first theorem indices only at reconstruction.
-- Universal source-order slots are checked before subtraction.
lowerAtom
    :: Natural -> AtomTemplate (SetTermTemplate (UniversalOperand RuleTermTemplate))
    -> Either Text (AtomTemplate RuleTermTemplate)
lowerAtom depth = traverseAtomTemplateArguments term
  where
    term = \case
        TemplateClosed value -> pure (TemplateClosed value)
        TemplateVariable (UniversalBound index)
            | index < depth -> pure (TemplateVariable (ViewVariableIx (depth - index - 1)))
            | otherwise -> Left "a supplied-premise variable escaped its telescope"
        TemplateVariable (UniversalOuter outer) -> pure
            ((\(ViewVariableIx index) -> ViewVariableIx (index + depth)) <$> outer)
        TemplateProvider provider arguments -> TemplateProvider provider <$> traverse term arguments
        TemplateOrderedPair left right -> TemplateOrderedPair <$> term left <*> term right

traverseBodyAtDepth
    :: Applicative m => (Natural -> a -> m b) -> UniversalBody a -> m (UniversalBody b)
traverseBodyAtDepth visit = go 0
  where
    go depth = \case
        UniversalBind nested -> UniversalBind <$> go (depth + 1) nested
        UniversalRequire guard nested -> UniversalRequire <$> traverse (visit depth) guard <*> go depth nested
        UniversalReturn result -> UniversalReturn <$> traverse (visit depth) result

-- Flatten fixed outer source terms without exposing inner bound slots as
-- ordinary evaluator variables or discarding written provider applications.
flattenOuter :: UniversalTemplate (SetTermTemplate variable)
    -> UniversalBody (AtomTemplate (SetTermTemplate (UniversalOperand variable)))
flattenOuter = fmap (fmap term)
  where
    term = \case
        TemplateClosed value -> TemplateClosed value
        TemplateVariable (UniversalBound index) -> TemplateVariable (UniversalBound index)
        TemplateVariable (UniversalOuter value) -> UniversalOuter <$> value
        TemplateProvider provider arguments -> TemplateProvider provider (term <$> arguments)
        TemplateOrderedPair left right -> TemplateOrderedPair (term left) (term right)
