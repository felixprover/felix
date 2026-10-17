{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked original/residual roots and their logical decomposition. The node
-- owns its shape and children; clients may transform only the payload.
module Felix.Checking.Obvious.LogicalView
    ( LogicalView
    , LogicalNode(..)
    , HeadResidualization
    , headResidualizationOriginal
    , headResidualizationResidual
    , LogicalViewError(..)
    , logicalViewOriginalTemplate
    , logicalViewResidualTemplate
    , logicalViewHeadResidualization
    , logicalViewNode
    , logicalViewPayload
    , logicalViewBinderDepth
    , traverseLogicalViewPayloadM
    , prepareCompiledLogicalViewCounted
    , assembleImplicationViewCounted
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Obvious.Template qualified as Template

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Numeric.Natural (Natural)


data PreparedHeadExposure global
    = HeadAlreadyExposed !(Template.CompiledTemplate global)
    | HeadResidualized
        !(Template.CompiledTemplate global)
        !(Template.CompiledTemplate global)

data HeadResidualization global = HeadResidualization
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)

data LogicalView global payload = LogicalView
    !(PreparedHeadExposure global)
    !payload
    !(LogicalNode global payload)

data LogicalNode global payload
    = LogicalTruth
    | LogicalFalsum
    | LogicalEquality
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
    | LogicalNeutral
    | LogicalNegation !(LogicalView global payload)
    | LogicalConjunction
        !(LogicalView global payload)
        !(LogicalView global payload)
    | LogicalDisjunction
        !(LogicalView global payload)
        !(LogicalView global payload)
    | LogicalImplication
        !(LogicalView global payload)
        !(LogicalView global payload)
    | LogicalUniversal !CoreType !(LogicalView global payload)
    | LogicalExistential !CoreType !(LogicalView global payload)

data LogicalViewError
    = LogicalViewIntegrityFailure !Text
    deriving stock (Show, Eq)

headResidualizationOriginal
    :: HeadResidualization global -> ScopedCheckedCore global
headResidualizationOriginal (HeadResidualization original _residual) = original

headResidualizationResidual
    :: HeadResidualization global -> ScopedCheckedCore global
headResidualizationResidual (HeadResidualization _original residual) = residual

logicalViewOriginalTemplate
    :: LogicalView global payload -> Template.CompiledTemplate global
logicalViewOriginalTemplate (LogicalView exposure _payload _node) =
    case exposure of
        HeadAlreadyExposed original -> original
        HeadResidualized original _residual -> original

logicalViewResidualTemplate
    :: LogicalView global payload -> Template.CompiledTemplate global
logicalViewResidualTemplate (LogicalView exposure _payload _node) =
    residualTemplate exposure

logicalViewHeadResidualization
    :: LogicalView global payload -> Maybe (HeadResidualization global)
logicalViewHeadResidualization (LogicalView exposure _payload _node) =
    case exposure of
        HeadAlreadyExposed{} -> Nothing
        HeadResidualized original residual ->
            Just
                (HeadResidualization
                    (Template.compiledTemplateTerm original)
                    (Template.compiledTemplateTerm residual))

logicalViewNode :: LogicalView global payload -> LogicalNode global payload
logicalViewNode (LogicalView _exposure _payload node) = node

logicalViewPayload :: LogicalView global payload -> payload
logicalViewPayload (LogicalView _exposure payload _node) = payload

logicalViewBinderDepth :: LogicalView global payload -> Natural
logicalViewBinderDepth =
    Template.binderEnvironmentCount
        . Template.compiledTemplateBinderEnvironment
        . logicalViewResidualTemplate

-- | Share two already prepared root operands. The written implication is
-- already head-exposed: residuals belong to its children, not its parent.
-- The owning caller supplies charged exact identity and node operations.
assembleImplicationViewCounted
    :: Monad m
    => (ScopedCheckedCore global -> ScopedCheckedCore global -> m Bool)
    -> m () -> ScopedCheckedCore global
    -> LogicalView global () -> LogicalView global ()
    -> m (Either LogicalViewError (LogicalView global ()))
assembleImplicationViewCounted same charge written left right = Except.runExceptT do
    lift charge
    unless (logicalViewBinderDepth left == 0 && logicalViewBinderDepth right == 0)
        (Except.throwE (LogicalViewIntegrityFailure "an implication operand retains a removable binder"))
    (antecedent, consequent) <- maybe
        (Except.throwE (LogicalViewIntegrityFailure "prepared implication has a different checked head"))
        pure (openScopedImplication written)
    leftMatches <- lift (same antecedent (Template.compiledTemplateTerm (logicalViewOriginalTemplate left)))
    rightMatches <- lift (same consequent (Template.compiledTemplateTerm (logicalViewOriginalTemplate right)))
    unless (leftMatches && rightMatches)
        (Except.throwE (LogicalViewIntegrityFailure "prepared implication has different checked operands"))
    original <- either
        (const (Except.throwE (LogicalViewIntegrityFailure "prepared implication is not a proposition")))
        pure (Template.retainCheckedPropositionTemplate written)
    pure (LogicalView (HeadAlreadyExposed original) () (LogicalImplication left right))

-- | Run preorder and postorder payload effects without allowing a client to
-- replace a semantic child, binder type, equality operand or prepared root.
traverseLogicalViewPayloadM
    :: Monad m
    => (LogicalView global old -> m seed)
    -> (seed -> m new)
    -> LogicalView global old
    -> m (LogicalView global new)
traverseLogicalViewPayloadM before after = go
  where
    go view@(LogicalView exposure _payload node) = do
        seed <- before view
        node' <- case node of
            LogicalTruth -> pure LogicalTruth
            LogicalFalsum -> pure LogicalFalsum
            LogicalEquality left right -> pure (LogicalEquality left right)
            LogicalNeutral -> pure LogicalNeutral
            LogicalNegation child -> LogicalNegation <$> go child
            LogicalConjunction left right -> do
                left' <- go left
                right' <- go right
                pure (LogicalConjunction left' right')
            LogicalDisjunction left right -> do
                left' <- go left
                right' <- go right
                pure (LogicalDisjunction left' right')
            LogicalImplication left right -> do
                left' <- go left
                right' <- go right
                pure (LogicalImplication left' right')
            LogicalUniversal binderType child -> LogicalUniversal binderType <$> go child
            LogicalExistential binderType child -> LogicalExistential binderType <$> go child
        payload <- after seed
        pure (LogicalView exposure payload node')

-- | The Refutation owner supplies its charged optional head residual and node
-- charge. Nothing retains the original checked syntax. Their effects stay in its
-- existing state, including the post-debit pool when any later step fails.
-- The residualizer must run on the supplied checked root under the current
-- snapshot; only this immediate result may enter the unchecked retention seam.
prepareCompiledLogicalViewCounted
    :: Monad m
    => (ScopedCheckedCore global -> m (Maybe (ScopedCheckedCore global)))
    -> m ()
    -> Template.CompiledTemplate global
    -> m (Either LogicalViewError (LogicalView global ()))
prepareCompiledLogicalViewCounted residualize charge original =
    Except.runExceptT (prepare original)
  where
    prepare template = do
        let checked = Template.compiledTemplateTerm template
        residual <- lift (residualize checked)
        let exposure =
                case residual of
                    Nothing -> HeadAlreadyExposed template
                    Just recovered -> HeadResidualized template
                        (Template.unsafeRetainResidualizedPropositionTemplate
                            template recovered)
        lift charge
        node <- buildLogicalNode prepare (residualTemplate exposure)
        pure (LogicalView exposure () node)

residualTemplate :: PreparedHeadExposure global -> Template.CompiledTemplate global
residualTemplate = \case
    HeadAlreadyExposed template -> template
    HeadResidualized _original residual -> residual

-- Decompose the checked residual once. Recursive children retain the terms
-- projected from this parent as their originals, before their own observation.
buildLogicalNode
    :: Monad m
    => (Template.CompiledTemplate global
        -> Except.ExceptT LogicalViewError m (LogicalView global ()))
    -> Template.CompiledTemplate global
    -> Except.ExceptT LogicalViewError m (LogicalNode global ())
buildLogicalNode prepare template =
    case scopedCoreTerm checked of
        CTruth -> pure LogicalTruth
        CFalsum -> pure LogicalFalsum
        CEq{} -> do
            (_operandType, left, right) <- require "equality" (splitScopedEquality checked)
            pure (LogicalEquality left right)
        CNot{} -> do
            child <- require "negation" (Template.splitCompiledNegation template)
            LogicalNegation <$> prepare child
        CAnd{} -> do
            (left, right) <- require "conjunction" (Template.splitCompiledConjunction template)
            left' <- prepare left
            right' <- prepare right
            pure (LogicalConjunction left' right')
        COr{} -> do
            (left, right) <- require "disjunction" (Template.splitCompiledDisjunction template)
            left' <- prepare left
            right' <- prepare right
            pure (LogicalDisjunction left' right')
        CImp{} -> do
            (left, right) <- require "implication" (Template.openCompiledImplication template)
            left' <- prepare left
            right' <- prepare right
            pure (LogicalImplication left' right')
        CForall{} -> do
            (binderType, child) <- require "universal" (Template.openCompiledForall template)
            LogicalUniversal binderType <$> prepare child
        CExists{} -> do
            (binderType, child) <- require "existential" (Template.openCompiledExists template)
            LogicalExistential binderType <$> prepare child
        CBound{} -> pure LogicalNeutral
        CGlobal{} -> pure LogicalNeutral
        CIntrinsic{} -> pure LogicalNeutral
        CLogicalSelect{} -> pure LogicalNeutral
        COpaqueInteger{} -> pure LogicalNeutral
        CApp{} -> pure LogicalNeutral
        CLam{} -> pure LogicalNeutral
  where
    checked = Template.compiledTemplateTerm template
    require label = maybe
        (Except.throwE
            (LogicalViewIntegrityFailure
                ("checked " <> label <> " failed its opening operation")))
        pure
