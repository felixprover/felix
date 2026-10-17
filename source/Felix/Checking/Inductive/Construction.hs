{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Direct checked lowering of the current one-carrier set-valued inductive
-- declaration.
module Felix.Checking.Inductive.Construction
    ( InductiveVariable(..)
    , InductiveBinder
    , CheckedInductiveTerm
    , prepareCheckedInductiveTerm
    , CheckedInductiveFormula
    , prepareCheckedInductiveFormula
    , DirectInductive(..)
    , DirectInductiveClause(..)
    , DirectInductiveCondition(..)
    , RecursiveCarrierContext
    , prepareRecursiveCarrierContext
    , directRecursiveCarrierContext
    , PreparedTypedInductive
    , typedInductiveCarrierType
    , typedInductiveCarrierBody
    , typedInductiveGuardTargets
    , PreparedTypedInductiveMonotonicity
    , typedInductiveMonotonicities
    , typedInductiveMonotonicityLocation
    , typedInductiveMonotonicityTarget
    , typedInductiveContextInventory
    , PreparedTypedInductiveFact
    , typedInductiveFacts
    , typedInductiveFactMarker
    , typedInductiveFactTarget
    , typedInductiveFactRules
    , typedInductiveFactRequiresMonotonicities
    , typedInductiveFactDerivation
    , prepareTypedInductive
    , TypedInductiveError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof
import Felix.Report.Location (Location)

import Control.Monad ((<=<), foldM, unless)
import Data.Bifunctor (first)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)


newtype InductiveVariable = InductiveVariable Natural
    deriving stock (Show, Eq, Ord)

-- Binders are in source order; checked Core contexts are nearest-first.
type InductiveBinder = (InductiveVariable, CoreType)

data CheckedInductiveTerm global = CheckedInductiveTerm
    ![InductiveBinder]
    !(FrozenCheckedCore global)

data CheckedInductiveFormula global = CheckedInductiveFormula
    ![InductiveBinder]
    !(FrozenCheckedCore global)

prepareCheckedInductiveTerm
    :: GlobalTyping global
    -> [InductiveBinder]
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (CheckedInductiveTerm global)
prepareCheckedInductiveTerm globalType variables scoped = do
    frozen <- prepareCheckedTemplate globalType variables TySet scoped
    pure (CheckedInductiveTerm variables frozen)

prepareCheckedInductiveFormula
    :: GlobalTyping global
    -> [InductiveBinder]
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (CheckedInductiveFormula global)
prepareCheckedInductiveFormula globalType variables scoped = do
    frozen <- prepareCheckedTemplate globalType variables TyProp scoped
    pure (CheckedInductiveFormula variables frozen)

prepareCheckedTemplate
    :: GlobalTyping global
    -> [InductiveBinder]
    -> CoreType
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (FrozenCheckedCore global)
prepareCheckedTemplate globalType variables =
    prepareCheckedTemplateWithTypes globalType (snd <$> variables)

prepareCheckedTemplateWithTypes
    :: GlobalTyping global
    -> [CoreType]
    -> CoreType
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (FrozenCheckedCore global)
prepareCheckedTemplateWithTypes globalType types expected scoped
    | scopedCoreContext scoped /= reverse types =
        Left
            (TypedInductiveUnsupportedExpression
                "an inductive expression has the wrong checked binder context")
    | scopedCoreType scoped /= expected =
        Left
            (TypedInductiveUnsupportedExpression
                "an inductive expression has the wrong checked result type")
    | otherwise =
        first TypedInductiveCoreError
            (checkCanonicalCore globalType
                (closeLambdas types (scopedCoreTerm scoped)))

data DirectInductive global = DirectInductive
    { directInductiveParams :: ![InductiveBinder]
    , directInductiveDomain :: !(CheckedInductiveTerm global)
    , directInductiveClauses
        :: !(NonEmpty (DirectInductiveClause global))
    }

data DirectInductiveClause global = DirectInductiveClause
    { directClauseVariables :: ![InductiveBinder]
    , directClauseConditions
        :: ![DirectInductiveCondition global]
    , directClauseResult :: !(CheckedInductiveTerm global)
    }

data DirectInductiveCondition global
    = DirectSideCondition !(CheckedInductiveFormula global)
    | DirectRecursiveCondition
        !(CheckedInductiveTerm global)
        !(RecursiveCarrierContext global)

-- | A checked set-valued carrier context, closed over its typed variables
-- and one final Set-valued hole. The frontend owns its source restrictions.
data RecursiveCarrierContext global = RecursiveCarrierContext
    !Location
    !Bool
    ![InductiveBinder]
    !(FrozenCheckedCore global)

prepareRecursiveCarrierContext
    :: GlobalTyping global
    -> Location
    -> Bool
    -> [InductiveBinder]
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (RecursiveCarrierContext global)
prepareRecursiveCarrierContext
        globalType location direct variables scoped = do
    frozen <-
        prepareCheckedTemplateWithTypes
            globalType
            ((snd <$> variables) <> [TySet])
            TySet
            scoped
    pure (RecursiveCarrierContext location direct variables frozen)

directRecursiveCarrierContext
    :: GlobalTyping global
    -> Location
    -> [InductiveBinder]
    -> ScopedCheckedCore global
    -> Either TypedInductiveError (RecursiveCarrierContext global)
directRecursiveCarrierContext globalType location variables =
    prepareRecursiveCarrierContext
        globalType location True variables

data PreparedTypedInductive global = PreparedTypedInductive
    !CoreType
    !(FrozenCheckedCore global)
    !(Vector (FrozenCheckedCore global))
    !(Vector (PreparedTypedInductiveMonotonicity global))
    !(Vector (FrozenCheckedCore global))
    !(NonEmpty (PreparedTypedInductiveFact global))

data PreparedTypedInductiveMonotonicity global =
    PreparedTypedInductiveMonotonicity
        !Location
        !(FrozenCheckedCore global)

typedInductiveMonotonicities
    :: PreparedTypedInductive global
    -> Vector (PreparedTypedInductiveMonotonicity global)
typedInductiveMonotonicities
        (PreparedTypedInductive
            _carrierType
            _body
            _guards
            monotonicities
            _contexts
            _facts) =
    monotonicities

typedInductiveMonotonicityLocation
    :: PreparedTypedInductiveMonotonicity global
    -> Location
typedInductiveMonotonicityLocation
        (PreparedTypedInductiveMonotonicity location _target) =
    location

typedInductiveMonotonicityTarget
    :: PreparedTypedInductiveMonotonicity global
    -> FrozenCheckedCore global
typedInductiveMonotonicityTarget
        (PreparedTypedInductiveMonotonicity _location target) =
    target

typedInductiveContextInventory
    :: PreparedTypedInductive global
    -> Vector (FrozenCheckedCore global)
typedInductiveContextInventory
        (PreparedTypedInductive
            _carrierType _body _guards _monotonicities contexts _facts) =
    contexts

data CheckedRecursiveCarrierContext global =
    CheckedRecursiveCarrierContext
        ![InductiveBinder]
        !(FrozenCheckedCore global)

data PreparedInductiveSource global = PreparedInductiveSource
    { preparedInductiveGlobalTyping :: !(GlobalTyping global)
    , preparedInductiveParams :: ![InductiveBinder]
    , preparedInductiveDomain :: !(CheckedInductiveTerm global)
    , preparedInductiveClauses
        :: !(NonEmpty (PreparedInductiveClause global))
    }

data PreparedInductiveClause global = PreparedInductiveClause
    { preparedClauseVariables :: ![InductiveBinder]
    , preparedClauseConditions
        :: ![PreparedInductiveCondition global]
    , preparedClauseResult :: !(CheckedInductiveTerm global)
    }

data PreparedInductiveCondition global
    = PreparedSideCondition !(CheckedInductiveFormula global)
    | PreparedDirectRecursiveCondition
        !(CheckedInductiveTerm global)
        !(CheckedRecursiveCarrierContext global)
    | PreparedNestedRecursiveCondition
        !(CheckedInductiveTerm global)
        !(CheckedRecursiveCarrierContext global)
        !ImportIx
        !(FrozenCheckedCore global)

data PreparedInductiveGuard global
    = PreparedFoundationGuard !FoundationAxiomTag
    | PreparedImportedGuard
        !ImportIx
        !(FrozenCheckedCore global)

typedInductiveCarrierType
    :: PreparedTypedInductive global
    -> CoreType
typedInductiveCarrierType
        (PreparedTypedInductive
            carrierType
            _body
            _guards
            _monotonicities
            _contexts
            _facts) =
    carrierType

typedInductiveCarrierBody
    :: PreparedTypedInductive global
    -> FrozenCheckedCore global
typedInductiveCarrierBody
        (PreparedTypedInductive
            _carrierType
            body
            _guards
            _monotonicities
            _contexts
            _facts) =
    body

typedInductiveGuardTargets
    :: PreparedTypedInductive global
    -> Vector (FrozenCheckedCore global)
typedInductiveGuardTargets
        (PreparedTypedInductive
            _carrierType
            _body
            guards
            _monotonicities
            _contexts
            _facts) =
    guards

newtype PreparedTypedInductiveFact global =
    PreparedTypedInductiveFact
        ( Text
        , FrozenCheckedCore global
        , NonEmpty KernelRuleTag
        , Bool
        , KernelDerivation global
        )

typedInductiveFacts
    :: PreparedTypedInductive global
    -> NonEmpty (PreparedTypedInductiveFact global)
typedInductiveFacts
        (PreparedTypedInductive
            _carrierType
            _body
            _guards
            _monotonicities
            _contexts
            facts) =
    facts

typedInductiveFactMarker
    :: PreparedTypedInductiveFact global
    -> Text
typedInductiveFactMarker
        (PreparedTypedInductiveFact
            (marker, _target, _rule, _monotonicities, _derivation)) =
    marker

typedInductiveFactTarget
    :: PreparedTypedInductiveFact global
    -> FrozenCheckedCore global
typedInductiveFactTarget
        (PreparedTypedInductiveFact
            (_marker, target, _rule, _monotonicities, _derivation)) =
    target

typedInductiveFactRules
    :: PreparedTypedInductiveFact global
    -> NonEmpty KernelRuleTag
typedInductiveFactRules
        (PreparedTypedInductiveFact
            (_marker, _target, rules, _monotonicities, _derivation)) =
    rules

typedInductiveFactRequiresMonotonicities
    :: PreparedTypedInductiveFact global
    -> Bool
typedInductiveFactRequiresMonotonicities
        (PreparedTypedInductiveFact
            (_marker, _target, _rules, required, _derivation)) =
    required

typedInductiveFactDerivation
    :: PreparedTypedInductiveFact global
    -> KernelDerivation global
typedInductiveFactDerivation
        (PreparedTypedInductiveFact
            (_marker, _target, _rule, _monotonicities, derivation)) =
    derivation

data TypedInductiveError
    = TypedInductiveDuplicateBinder !InductiveVariable
    | TypedInductiveUnknownLocal !InductiveVariable
    | TypedInductiveBinderTypeMismatch !InductiveVariable !CoreType !CoreType
    | TypedInductiveUnsupportedExpression !Text
    | TypedInductiveCoreError !CoreCheckError
    | TypedInductiveProofError !KernelProofBuildError
    | TypedInductiveProofRemainedOpen
    | TypedInductiveFactPreparationFailed
        !Text
        !TypedInductiveError
    | TypedInductivePreparationContext
        !Text
        !TypedInductiveError
    deriving stock (Show, Eq)

data InductiveEnvironment = InductiveEnvironment
    !(Map InductiveVariable (Natural, CoreType))

emptyEnvironment :: InductiveEnvironment
emptyEnvironment =
    InductiveEnvironment Map.empty

extendEnvironment
    :: InductiveBinder
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        InductiveEnvironment
extendEnvironment (variable, binderType)
        (InductiveEnvironment variables)
    | Map.member variable variables =
        Left
            (TypedInductiveDuplicateBinder
                variable)
    | otherwise =
        Right
            (InductiveEnvironment
                (Map.insert variable (0, binderType)
                    (first succ <$> variables)))

lookupEnvironment
    :: InductiveBinder
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
lookupEnvironment (variable, expected) (InductiveEnvironment variables) =
    case Map.lookup variable variables of
        Nothing -> Left (TypedInductiveUnknownLocal variable)
        Just (index, actual)
            | actual == expected -> Right (CBound index)
            | otherwise -> Left (TypedInductiveBinderTypeMismatch variable expected actual)

prepareTypedInductive
    :: Eq global
    => GlobalTyping global
    -> CheckedFoundation
    -> Text
    -> DirectInductive global
    -> Either
        TypedInductiveError
        (PreparedTypedInductive global)
prepareTypedInductive
        globalTyping
        foundation
        marker
        inductive =
    prepareTypedInductiveInternal
        globalTyping
        foundation
        marker
        inductive

prepareTypedInductiveInternal
    :: Eq global
    => GlobalTyping global
    -> CheckedFoundation
    -> Text
    -> DirectInductive global
    -> Either
        TypedInductiveError
        (PreparedTypedInductive global)
prepareTypedInductiveInternal
        globalTyping
        foundation
        marker
        inductive = do
    for_ (directInductiveClauses inductive) \clause ->
        unless (all ((== TySet) . snd) (directClauseVariables clause))
            (Left (TypedInductiveUnsupportedExpression
                "inductive rule-local binders must be sets"))
    guards <-
        traverse
            (prepareDirectGuardTarget globalTyping inductive)
            (directInductiveClauses
                inductive)
    let preparedGuards =
            assignGuardSources foundation
                (NonEmpty.toList guards)
        nextImport =
            fromIntegral
                (length
                    [ ()
                    | PreparedImportedGuard{} <- preparedGuards
                    ])
    (preparedSource, monotonicities, contexts) <-
        prepareInductiveSource
            nextImport
            globalTyping
            inductive
    carrierBody <-
        prepareCarrierBody preparedSource
    facts <-
        prepareFacts
            foundation
            marker
            preparedSource
            (case preparedGuards of
                firstGuard : remainingGuards ->
                    firstGuard :| remainingGuards
                [] ->
                    impossible
                        "a nonempty inductive declaration produced no guards")
    pure
        (PreparedTypedInductive
            carrierType
            carrierBody
            (Vector.fromList
                [ target
                | PreparedImportedGuard
                    _index target <- preparedGuards
                ])
            (Vector.fromList monotonicities)
            (Vector.fromList contexts)
            facts)
  where
    carrierType =
        foldr
            TyArrow
            TySet
            (snd
                <$> directInductiveParams
                    inductive)

data MonotonicityInventory global = MonotonicityInventory
    ![(FrozenCheckedCore global, ImportIx)]
    !Natural
    ![PreparedTypedInductiveMonotonicity global]
    ![FrozenCheckedCore global]

prepareInductiveSource
    :: Eq global
    => Natural
    -> GlobalTyping global
    -> DirectInductive global
    -> Either
        TypedInductiveError
        ( PreparedInductiveSource global
        , [PreparedTypedInductiveMonotonicity global]
        , [FrozenCheckedCore global]
        )
prepareInductiveSource firstImport globalTyping inductive = do
    (final, clauses) <-
        prepareClauses
            (MonotonicityInventory [] firstImport [] [])
            (NonEmpty.toList (directInductiveClauses inductive))
    let MonotonicityInventory
            _targets _next monotonicities contexts = final
    pure
        ( PreparedInductiveSource
            globalTyping
            (directInductiveParams inductive)
            (directInductiveDomain inductive)
            (NonEmpty.fromList clauses)
        , reverse monotonicities
        , reverse contexts
        )
  where
    variablesFor clause =
        directInductiveParams inductive
            <> directClauseVariables clause

    prepareClauses inventory = \case
        [] -> pure (inventory, [])
        clause : remaining -> do
            (afterClause, preparedClause) <-
                prepareClause inventory clause
            (final, preparedRemaining) <-
                prepareClauses afterClause remaining
            pure (final, preparedClause : preparedRemaining)

    prepareClause inventory clause = do
        (next, conditions) <-
            prepareConditions inventory clause
                (directClauseConditions clause)
        pure
            ( next
            , PreparedInductiveClause
                (directClauseVariables clause)
                conditions
                (directClauseResult clause)
            )

    prepareConditions inventory _clause [] =
        pure (inventory, [])
    prepareConditions inventory clause (condition : remaining) = do
        (next, prepared) <-
            prepareCondition inventory clause condition
        (final, preparedRemaining) <-
            prepareConditions next clause remaining
        pure (final, prepared : preparedRemaining)

    prepareCondition inventory _clause (DirectSideCondition formula) =
        pure (inventory, PreparedSideCondition formula)
    prepareCondition
            (MonotonicityInventory targets next facts contexts)
            clause
            (DirectRecursiveCondition recursiveTerm sourceContext) = do
        checkedContext <-
            prepareRecursiveCarrierTemplate
                (variablesFor clause)
                sourceContext
        let template = checkedRecursiveCarrierTemplate checkedContext
            withContext currentFacts =
                MonotonicityInventory
                    targets next currentFacts (template : contexts)
        if recursiveCarrierContextIsDirect sourceContext
            then pure
                ( withContext facts
                , PreparedDirectRecursiveCondition
                    recursiveTerm checkedContext
                )
            else do
                target <-
                    prepareRecursiveCarrierMonotonicityTarget
                        globalTyping
                        checkedContext
                let RecursiveCarrierContext location _direct _variables _template =
                        sourceContext
                case List.lookup target targets of
                    Just index ->
                        pure
                            ( MonotonicityInventory
                                targets next facts (template : contexts)
                            , PreparedNestedRecursiveCondition
                                recursiveTerm checkedContext index target
                            )
                    Nothing ->
                        let index = importIx next
                        in pure
                            ( MonotonicityInventory
                                ((target, index) : targets)
                                (next + 1)
                                (PreparedTypedInductiveMonotonicity
                                    location target : facts)
                                (template : contexts)
                            , PreparedNestedRecursiveCondition
                                recursiveTerm checkedContext index target
                            )

checkedRecursiveCarrierTemplate
    :: CheckedRecursiveCarrierContext global
    -> FrozenCheckedCore global
checkedRecursiveCarrierTemplate
        (CheckedRecursiveCarrierContext _variables template) =
    template

recursiveCarrierContextIsDirect :: RecursiveCarrierContext global -> Bool
recursiveCarrierContextIsDirect
        (RecursiveCarrierContext _location direct _variables _template) =
    direct

prepareRecursiveCarrierTemplate
    :: [InductiveBinder]
    -> RecursiveCarrierContext global
    -> Either
        TypedInductiveError
        (CheckedRecursiveCarrierContext global)
prepareRecursiveCarrierTemplate variables
        (RecursiveCarrierContext _location _direct contextVariables template)
    | variables == contextVariables =
        pure (CheckedRecursiveCarrierContext variables template)
    | otherwise =
        Left
            (TypedInductiveUnsupportedExpression
                "a recursive carrier context has the wrong checked binder telescope")

prepareRecursiveCarrierMonotonicityTarget
    :: GlobalTyping global
    -> CheckedRecursiveCarrierContext global
    -> Either
        TypedInductiveError
        (FrozenCheckedCore global)
prepareRecursiveCarrierMonotonicityTarget
        globalTyping
        context@(CheckedRecursiveCarrierContext variables _template) = do
    target <-
        buildUnderVariables emptyEnvironment variables \environment -> do
            underSets <- shiftEnvironment =<< shiftEnvironment environment
            left <-
                instantiateRecursiveCarrier
                    underSets (CBound 1) context
            right <-
                instantiateRecursiveCarrier
                    underSets (CBound 0) context
            pure
                (CImp
                    (subsetTerm (CBound 1) (CBound 0))
                    (subsetTerm left right))
    freezeClosedTarget globalTyping
        (closeForalls ((snd <$> variables) <> [TySet, TySet]) target)

instantiateRecursiveCarrier
    :: InductiveEnvironment
    -> CanonicalTerm global
    -> CheckedRecursiveCarrierContext global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
instantiateRecursiveCarrier environment replacement
        context@(CheckedRecursiveCarrierContext variables _template) = do
    arguments <- traverse (`lookupEnvironment` environment) variables
    foldM instantiateLambda
        (frozenCoreTerm (checkedRecursiveCarrierTemplate context))
        (arguments <> [replacement])
  where
    instantiateLambda term argument =
        case term of
            CLam _binderType body ->
                pure (instantiateCanonical argument body)
            _ ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "a checked recursive carrier context lost its typed telescope")

prepareCarrierBody
    :: PreparedInductiveSource global
    -> Either
        TypedInductiveError
        (FrozenCheckedCore global)
prepareCarrierBody inductive = do
    body <-
        buildUnderVariables
            emptyEnvironment
            (preparedInductiveParams
                inductive)
            (fixedPointTerm inductive)
    let closed =
            closeLambdas (snd <$> preparedInductiveParams inductive) body
    checked <-
        first TypedInductiveCoreError
            (checkCanonicalCore
                (preparedInductiveGlobalTyping inductive)
                closed)
    pure checked

prepareDirectGuardTarget
    :: GlobalTyping global
    -> DirectInductive global
    -> DirectInductiveClause global
    -> Either
        TypedInductiveError
        (FrozenCheckedCore global)
prepareDirectGuardTarget
        globalTyping
        inductive
        clause = do
    target <-
        buildUnderVariables
            emptyEnvironment
            (directInductiveParams inductive
                <> directClauseVariables clause)
            (\environment -> do
                domain <-
                    lowerTerm
                        environment
                        (directInductiveDomain
                            inductive)
                conditions <-
                    traverse
                        (directConditionTerm
                            environment
                            domain)
                        (directClauseConditions
                            clause)
                result <-
                    lowerTerm
                        environment
                        (directClauseResult
                            clause)
                pure
                    (impliesIfNeeded
                        (conjunctionList
                            conditions)
                        (memberTerm
                            result
                            domain)))
    freezeClosedTarget globalTyping
        (closeForalls
            (snd <$> (directInductiveParams inductive
                <> directClauseVariables clause))
            target)

assignGuardSources
    :: Eq global
    => CheckedFoundation
    -> [FrozenCheckedCore global]
    -> [PreparedInductiveGuard global]
assignGuardSources foundation =
    snd . List.mapAccumL assign 0
  where
    assign nextImport target =
        case matchingFoundationAxiom target of
            Just tag ->
                (nextImport, PreparedFoundationGuard tag)
            Nothing ->
                ( nextImport + 1
                , PreparedImportedGuard
                    (importIx nextImport)
                    target
                )

    matchingFoundationAxiom target =
        List.find
            (\tag ->
                eliminateFrozenVoid
                    (foundationAxiomFrozen
                        foundation
                        tag)
                    == target)
            [minBound .. maxBound]

prepareFacts
    :: Eq global
    => CheckedFoundation
    -> Text
    -> PreparedInductiveSource global
    -> NonEmpty (PreparedInductiveGuard global)
    -> Either
        TypedInductiveError
        (NonEmpty (PreparedTypedInductiveFact global))
prepareFacts
        foundation
        marker
        inductive
        guards = do
    introductions <-
        sequence
            (NonEmpty.zipWith
                (\clauseIndex pair ->
                    first
                        (TypedInductiveFactPreparationFailed
                            (introMarker
                                marker
                                (clauseIndex + 1)))
                        (prepareIntroductionFact
                            foundation
                            marker
                            inductive
                            clauseIndex
                            pair))
                (0 :| [1 ..])
                (NonEmpty.zip
                    guards
                    (preparedInductiveClauses
                        inductive)))
    domainSubset <-
        first
            (TypedInductiveFactPreparationFailed
                (derivedMarker marker "dom_subset"))
            (prepareDomainSubsetFact
                foundation
                marker
                inductive)
    cases <-
        first
            (TypedInductiveFactPreparationFailed
                (derivedMarker marker "cases"))
            (prepareCasesFact
                foundation
                marker
                inductive)
    induction <-
        first
            (TypedInductiveFactPreparationFailed
                (derivedMarker marker "induct"))
            (prepareInductionFact
                foundation
                marker
                inductive)
    pure
        (introductions
            <> (domainSubset
                :| [cases, induction]))

prepareIntroductionFact
    :: Eq global
    => CheckedFoundation
    -> Text
    -> PreparedInductiveSource global
    -> Natural
    -> (PreparedInductiveGuard global, PreparedInductiveClause global)
    -> Either
        TypedInductiveError
        (PreparedTypedInductiveFact global)
prepareIntroductionFact
        foundation
        marker
        inductive
        clauseIndex
        (guardSource, clause) = do
    proof <-
        proveUnderVariables
            (rootProofContext
                foundation
                (preparedInductiveGlobalTyping inductive))
            emptyEnvironment
            (preparedInductiveParams inductive
                <> preparedClauseVariables clause)
            (\context environment -> do
                domain <-
                    checkedTerm context
                        =<< lowerTerm
                            environment
                            (preparedInductiveDomain
                                inductive)
                operator <-
                    checkedTerm context
                        =<< operatorTerm
                            inductive
                            environment
                fixedPoint <-
                    checkedTerm context
                        =<< fixedPointTerm
                            inductive
                            environment
                predicate <-
                    checkedTerm context
                        =<< operatorPredicateAt
                            inductive
                            environment
                            (scopedCoreTerm
                                fixedPoint)
                appliedOperatorSet <-
                    checkedTerm context
                        (CApp
                            (scopedCoreTerm operator)
                            (scopedCoreTerm
                                fixedPoint))
                conditions <-
                    traverse
                        (checkedTerm context <=<
                            conditionTerm
                                environment
                                (scopedCoreTerm
                                    fixedPoint))
                        (preparedClauseConditions
                            clause)
                result <-
                    checkedTerm context
                        =<< lowerTerm
                            environment
                            (preparedClauseResult
                                clause)
                let conditionTerms =
                        scopedCoreTerm <$> conditions
                first
                    (TypedInductivePreparationContext
                        "introduction premises")
                    (provePremises
                        context
                        conditionTerms
                        (\premiseProofs -> do
                        guardProof <-
                            preparedGuardProof
                                context
                                guardSource
                        specializedGuard <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction guard specialization")
                                (eliminateWrittenForalls
                                    context
                                    environment
                                    (preparedInductiveParams
                                        inductive
                                        <> preparedClauseVariables
                                            clause)
                                    guardProof)
                        guardPremiseProofs <-
                            sequence
                                [ case condition of
                                    PreparedSideCondition _formula ->
                                        pure premiseProof
                                    PreparedDirectRecursiveCondition
                                            recursiveTerm _context -> do
                                        bound <-
                                            first
                                                TypedInductiveProofError
                                                (setLfpBoundProof
                                                    context
                                                    domain
                                                    operator)
                                        recursiveElement <-
                                            checkedTerm context
                                                =<< lowerTerm
                                                    environment
                                                    recursiveTerm
                                        implication <-
                                            first
                                                TypedInductiveProofError
                                                (forallEliminationProof
                                                    context
                                                    bound
                                                    recursiveElement)
                                        first
                                            TypedInductiveProofError
                                            (implicationEliminationProof
                                                context
                                                implication
                                                premiseProof)
                                    nested@PreparedNestedRecursiveCondition{} -> do
                                        bound <-
                                            first TypedInductiveProofError
                                                (setLfpBoundProof
                                                    context
                                                    domain
                                                    operator)
                                        recursiveElement <-
                                            checkedTerm context
                                                =<< lowerTerm
                                                    environment
                                                    (preparedRecursiveTerm
                                                        nested)
                                        transportNestedRecursiveMembership
                                            context
                                            environment
                                            nested
                                            fixedPoint
                                            domain
                                            recursiveElement
                                            bound
                                            premiseProof
                                | (condition, premiseProof) <-
                                    zip
                                        (preparedClauseConditions
                                            clause)
                                        premiseProofs
                                ]
                        inDomain <-
                            case conjunctionList
                                    conditionTerms of
                                Nothing ->
                                    pure specializedGuard
                                Just _condition -> do
                                    conjunction <-
                                        conjunctionIntroductionList
                                            context
                                            guardPremiseProofs
                                    first
                                        (TypedInductivePreparationContext
                                            "introduction guard application")
                                        (first TypedInductiveProofError
                                            (implicationEliminationProof
                                                context
                                                specializedGuard
                                                conjunction))
                        equality <-
                            first TypedInductiveProofError
                                (equalityReflexivityProof
                                    context
                                    result)
                        clauseProof <-
                            conjunctionIntroductionList
                                context
                                (premiseProofs
                                    <> [equality])
                        clauseExists <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction witnesses")
                                (introduceClauseWitnesses
                                    inductive
                                    clause
                                    context
                                    environment
                                    (scopedCoreTerm
                                        fixedPoint)
                                    result
                                    clauseProof)
                        alternatives <-
                            clauseFormulaTerms
                                inductive
                                environment
                                (scopedCoreTerm
                                    fixedPoint)
                                (scopedCoreTerm
                                    result)
                        disjunction <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction disjunction")
                                (injectDisjunction
                                    context
                                    clauseIndex
                                    alternatives
                                    clauseExists)
                        inOperator <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction separation")
                                (separationBackward
                                    context
                                    domain
                                    predicate
                                    result
                                    inDomain
                                    disjunction)
                        inAppliedTarget <-
                            checkedTerm context
                                (memberTerm
                                    (scopedCoreTerm
                                        result)
                                    (scopedCoreTerm
                                        appliedOperatorSet))
                        inAppliedOperator <-
                            first TypedInductiveProofError
                                (conversionProof
                                    context
                                    inOperator
                                    inAppliedTarget)
                        monotone <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction bounded monotonicity")
                                (proveBoundedMonotonicity
                                    foundation
                                    inductive
                                    context
                                    environment)
                        fixed <-
                            first TypedInductiveProofError
                                (setLfpFixedProof
                                    context
                                    domain
                                    operator
                                    monotone)
                        reversedFixed <-
                            first
                                (TypedInductivePreparationContext
                                    "introduction fixed-point symmetry")
                                (first TypedInductiveProofError
                                    (equalityReverseProof
                                        context
                                        fixed))
                        first
                            (TypedInductivePreparationContext
                                "introduction fixed-point transport")
                            (transportMembership
                                context
                                result
                                reversedFixed
                                inAppliedOperator))))
    preparedFact
        (introMarker
            marker
            (clauseIndex + 1))
        (if any isRecursiveCondition
                (preparedClauseConditions clause)
            then SetLfpBound :| [SetLfpFixed]
            else SetLfpFixed :| [])
        True
        proof
  where
    isRecursiveCondition = \case
        PreparedDirectRecursiveCondition{} -> True
        PreparedNestedRecursiveCondition{} -> True
        PreparedSideCondition{} -> False

preparedGuardProof
    :: ProofContext global
    -> PreparedInductiveGuard global
    -> Either
        TypedInductiveError
        (BuiltProof global)
preparedGuardProof context = \case
    PreparedFoundationGuard tag ->
        first TypedInductiveProofError
            (foundationProof context tag)
    PreparedImportedGuard index target ->
        first TypedInductiveProofError
            (importedProof context index target)

prepareDomainSubsetFact
    :: CheckedFoundation
    -> Text
    -> PreparedInductiveSource global
    -> Either
        TypedInductiveError
        (PreparedTypedInductiveFact global)
prepareDomainSubsetFact
        foundation
        marker
        inductive = do
    proof <-
        proveUnderVariables
            (rootProofContext
                foundation
                (preparedInductiveGlobalTyping inductive))
            emptyEnvironment
            (preparedInductiveParams
                inductive)
            (\context environment -> do
                domain <-
                    checkedTerm context
                        =<< lowerTerm
                            environment
                            (preparedInductiveDomain
                                inductive)
                operator <-
                    checkedTerm context
                        =<< operatorTerm
                            inductive
                            environment
                first TypedInductiveProofError
                    (setLfpBoundProof
                        context
                        domain
                        operator))
    preparedFact
        (derivedMarker marker "dom_subset")
        (SetLfpBound :| [])
        False
        proof

prepareCasesFact
    :: Eq global
    => CheckedFoundation
    -> Text
    -> PreparedInductiveSource global
    -> Either
        TypedInductiveError
        (PreparedTypedInductiveFact global)
prepareCasesFact
        foundation
        marker
        inductive = do
    proof <-
        proveUnderVariables
            (rootProofContext
                foundation
                (preparedInductiveGlobalTyping inductive))
            emptyEnvironment
            (preparedInductiveParams
                inductive)
            (\parameterContext parameterEnvironment ->
                forallIntroductionTyped
                    parameterContext
                    TySet
                    (\context result -> do
                        environment <-
                            shiftEnvironment
                                parameterEnvironment
                        domain <-
                            checkedTerm context
                                =<< lowerTerm
                                    environment
                                    (preparedInductiveDomain
                                        inductive)
                        operator <-
                            checkedTerm context
                                =<< operatorTerm
                                    inductive
                                    environment
                        fixedPoint <-
                            checkedTerm context
                                =<< fixedPointTerm
                                    inductive
                                    environment
                        predicate <-
                            checkedTerm context
                                =<< operatorPredicateAt
                                    inductive
                                    environment
                                    (scopedCoreTerm
                                        fixedPoint)
                        explicitOperatorSet <-
                            checkedTerm context
                                =<< separationSetAt
                                    inductive
                                    environment
                                    (scopedCoreTerm
                                        fixedPoint)
                        member <-
                            checkedTerm context
                                (memberTerm
                                    (scopedCoreTerm result)
                                    (scopedCoreTerm
                                        fixedPoint))
                        implicationIntroductionTyped
                            context
                            member
                            (\withMember memberProof -> do
                                monotone <-
                                    proveBoundedMonotonicity
                                        foundation
                                        inductive
                                        withMember
                                        environment
                                fixed <-
                                    first TypedInductiveProofError
                                        (setLfpFixedProof
                                            withMember
                                            domain
                                            operator
                                            monotone)
                                inOperator <-
                                    transportMembership
                                        withMember
                                        result
                                        fixed
                                        memberProof
                                explicitMembership <-
                                    checkedTerm withMember
                                        (memberTerm
                                            (scopedCoreTerm
                                                result)
                                            (scopedCoreTerm
                                                explicitOperatorSet))
                                inSeparation <-
                                    first TypedInductiveProofError
                                        (conversionProof
                                            withMember
                                            inOperator
                                            explicitMembership)
                                separation <-
                                    separationForward
                                        withMember
                                        domain
                                        predicate
                                        result
                                        inSeparation
                                predicateResult <-
                                    predicateAt
                                        inductive
                                        environment
                                        (scopedCoreTerm
                                            fixedPoint)
                                        (scopedCoreTerm
                                            result)
                                predicateProof <-
                                    first TypedInductiveProofError
                                        (conjunctionRightProof
                                            withMember
                                            separation)
                                predicateTarget <-
                                    checkedTerm
                                        withMember
                                        predicateResult
                                first TypedInductiveProofError
                                    (conversionProof
                                        withMember
                                        predicateProof
                                        predicateTarget))))
    preparedFact
        (derivedMarker marker "cases")
        (SetLfpFixed :| [])
        True
        proof

prepareInductionFact
    :: Eq global
    => CheckedFoundation
    -> Text
    -> PreparedInductiveSource global
    -> Either
        TypedInductiveError
        (PreparedTypedInductiveFact global)
prepareInductionFact
        foundation
        marker
        inductive = do
    proof <-
        proveUnderVariables
            (rootProofContext
                foundation
                (preparedInductiveGlobalTyping inductive))
            emptyEnvironment
            (preparedInductiveParams
                inductive)
            (\parameterContext parameterEnvironment ->
                forallIntroductionTyped
                    parameterContext
                    TySet
                    (\subsetContext subset -> do
                        environment <-
                            shiftEnvironment
                                parameterEnvironment
                        closures <-
                            closureTerms
                                inductive
                                environment
                                (scopedCoreTerm subset)
                        closureConjunction <-
                            checkedTerm subsetContext
                                (fromMaybe
                                    CTruth
                                    (conjunctionList
                                        closures))
                        implicationIntroductionTyped
                            subsetContext
                            closureConjunction
                            (\withClosures closuresProof -> do
                                fixedPoint <-
                                    checkedTerm withClosures
                                        =<< fixedPointTerm
                                            inductive
                                            environment
                                proveSubset
                                    withClosures
                                    fixedPoint
                                    subset
                                    (\elementContext element memberProof -> do
                                        elementEnvironment <-
                                            shiftEnvironment environment
                                        domain <-
                                            checkedTerm elementContext
                                                =<< lowerTerm
                                                    elementEnvironment
                                                    (preparedInductiveDomain
                                                        inductive)
                                        operator <-
                                            checkedTerm elementContext
                                                =<< operatorTerm
                                                    inductive
                                                    elementEnvironment
                                        fixedPointAtElement <-
                                            checkedTerm elementContext
                                                =<< fixedPointTerm
                                                    inductive
                                                    elementEnvironment
                                        subsetAtElement <-
                                            first TypedInductiveCoreError
                                                (weakenScopedCore
                                                    (preparedInductiveGlobalTyping
                                                        inductive)
                                                    TySet
                                                    subset)
                                        predicate <-
                                            membershipPredicate
                                                elementContext
                                                subsetAtElement
                                        monotone <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "induction bounded monotonicity")
                                                (proveBoundedMonotonicity
                                                    foundation
                                                    inductive
                                                    elementContext
                                                    elementEnvironment)
                                        closure <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "induction closure")
                                                (proveInductionClosure
                                                    foundation
                                                    inductive
                                                    elementContext
                                                    elementEnvironment
                                                    fixedPointAtElement
                                                    operator
                                                    subsetAtElement
                                                    closures
                                                    closuresProof)
                                        inducted <-
                                            first
                                            (TypedInductivePreparationContext
                                                "induction fixed-point rule")
                                            (first TypedInductiveProofError
                                                (setLfpInductProof
                                                elementContext
                                                domain
                                                operator
                                                predicate
                                                element
                                                monotone
                                                memberProof
                                                closure))
                                        expected <-
                                            checkedTerm elementContext
                                                (memberTerm
                                                    (scopedCoreTerm
                                                        element)
                                                    (scopedCoreTerm
                                                        subsetAtElement))
                                        first TypedInductiveProofError
                                            (conversionProof
                                                elementContext
                                                inducted
                                                expected)))))
    preparedFact
        (derivedMarker marker "induct")
        (SetLfpInduct :| [])
        True
        proof

proveUnderVariables
    :: ProofContext global
    -> InductiveEnvironment
    -> [InductiveBinder]
    -> ( ProofContext global
         -> InductiveEnvironment
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveUnderVariables context environment variables build =
    case variables of
        [] ->
            build context environment
        variable : remaining -> do
            extendedEnvironment <-
                extendEnvironment
                    variable
                    environment
            forallIntroductionTyped
                context
                (snd variable)
                (\extended _bound ->
                    proveUnderVariables
                        extended
                        extendedEnvironment
                        remaining
                        build)

checkedTerm
    :: ProofContext global
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (ScopedCheckedCore global)
checkedTerm context =
    first TypedInductiveProofError
        . scopedTerm context

preparedFact
    :: Text
    -> NonEmpty KernelRuleTag
    -> Bool
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (PreparedTypedInductiveFact global)
preparedFact marker rules requiresMonotonicities proof = do
    target <-
        maybe
            (Left TypedInductiveProofRemainedOpen)
            Right
            (closeScopedCore
                (builtProofStatement proof))
    pure
        (PreparedTypedInductiveFact
            ( marker
            , target
            , canonicalRules rules
            , requiresMonotonicities
            , builtProofDerivation proof
            ))
  where
    canonicalRules supplied =
        case Set.toAscList
                (Set.fromList (NonEmpty.toList supplied)) of
            firstRule : remainingRules ->
                firstRule :| remainingRules
            [] ->
                impossible "a nonempty guarded-rule set became empty"

introMarker :: Text -> Natural -> Text
introMarker marker index =
    marker
        <> "_intro_"
        <> Text.pack (show index)

derivedMarker :: Text -> Text -> Text
derivedMarker marker suffix =
    marker <> "_" <> suffix

eliminateWrittenForalls
    :: ProofContext global
    -> InductiveEnvironment
    -> [InductiveBinder]
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
eliminateWrittenForalls
        context
        environment
        variables
        initial =
    foldM
        (\proof variable -> do
            argument <-
                checkedTerm context
                    =<< lookupEnvironment
                        variable
                        environment
            first TypedInductiveProofError
                (forallEliminationProof
                    context
                    proof
                    argument))
        initial
        variables

provePremises
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> ( [BuiltProof global]
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
provePremises context premises build =
    case conjunctionList premises of
        Nothing ->
            build []
        Just conjunction -> do
            proposition <-
                checkedTerm context conjunction
            implicationIntroductionTyped
                context
                proposition
                (\extended conjunctionProof -> do
                    projections <-
                        projectConjunctionList
                            extended
                            premises
                            conjunctionProof
                    build projections)

conjunctionIntroductionList
    :: ProofContext global
    -> [BuiltProof global]
    -> Either
        TypedInductiveError
        (BuiltProof global)
conjunctionIntroductionList _context [] =
    Left
        (TypedInductiveUnsupportedExpression
            "an empty conjunction has no introduction proof")
conjunctionIntroductionList context proofs =
    first TypedInductiveProofError
        (buildLeftAssociatedConjunction context proofs)

projectConjunctionList
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either
        TypedInductiveError
        [BuiltProof global]
projectConjunctionList context terms proof =
    first TypedInductiveProofError
        (projectLeftAssociatedConjuncts context terms proof)

introduceClauseWitnesses
    :: Eq global
    => PreparedInductiveSource global
    -> PreparedInductiveClause global
    -> ProofContext global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
introduceClauseWitnesses
        _inductive
        clause
        context
        environment
        candidate
        result
        bodyProof =
    introduce
        (preparedClauseVariables clause)
  where
    introduce [] =
        pure bodyProof
    introduce (variable : remaining) = do
        inner <-
            introduce remaining
        witness <-
            checkedTerm context
                =<< lookupEnvironment
                    variable
                    environment
        underBinderEnvironment <-
            rebindEnvironment
                variable
                =<< shiftEnvironment
                    environment
        let candidate' =
                shiftCanonical 1 0 candidate
            result' =
                shiftCanonical
                    1
                    0
                    (scopedCoreTerm result)
        bodyUnderBinderTerm <-
            clauseFormulaWithBinders
                clause
                underBinderEnvironment
                candidate'
                result'
                remaining
        bodyUnderBinder <-
            first TypedInductiveCoreError
                (checkScopedTermUnderBinder
                    context
                    TySet
                    bodyUnderBinderTerm)
        first TypedInductiveProofError
            (existentialIntroductionProof
                context
                TySet
                bodyUnderBinder
                witness
                inner)

clauseFormulaWithBinders
    :: PreparedInductiveClause global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> [InductiveBinder]
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
clauseFormulaWithBinders
        clause
        environment
        candidate
        result = \case
    [] -> do
        conditions <-
            traverse
                (conditionTerm
                    environment
                    candidate)
                (preparedClauseConditions
                    clause)
        clauseResult <-
            lowerTerm
                environment
                (preparedClauseResult clause)
        pure
            (fromMaybe
                (CEq TySet result clauseResult)
                (conjunctionList
                    (conditions
                        <> [CEq
                            TySet
                            result
                            clauseResult])))
    variable : remaining -> do
        extended <-
            rebindEnvironment
                variable
                =<< shiftEnvironment
                    environment
        body <-
            clauseFormulaWithBinders
                clause
                extended
                (shiftCanonical
                    1
                    0
                    candidate)
                (shiftCanonical
                    1
                    0
                    result)
                remaining
        pure (existentialTerm TySet body)

rebindEnvironment
    :: InductiveBinder
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        InductiveEnvironment
rebindEnvironment (variable, binderType)
        (InductiveEnvironment variables) =
    pure
        (InductiveEnvironment
            (Map.insert variable (0, binderType) variables))

injectDisjunction
    :: ProofContext global
    -> Natural
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
injectDisjunction context index alternatives proof =
    first TypedInductiveProofError
        (introduceLeftAssociatedDisjunct
            context
            index
            alternatives
            proof)

closureTerms
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        [CanonicalTerm global]
closureTerms
        inductive
        environment
        subset =
    traverse closureFor
        (NonEmpty.toList
            (preparedInductiveClauses
                inductive))
  where
    closureFor clause = do
        clauseEnvironment <-
            extendVariables
                environment
                (preparedClauseVariables clause)
        let binderCount =
                fromIntegral
                    (length
                        (preparedClauseVariables
                            clause))
            subset' =
                shiftCanonical
                    binderCount
                    0
                    subset
        conditions <-
            traverse
                (conditionTerm
                    clauseEnvironment
                    subset')
                (preparedClauseConditions
                    clause)
        result <-
            lowerTerm
                clauseEnvironment
                (preparedClauseResult clause)
        pure
            (closeForalls
                (snd <$> preparedClauseVariables clause)
                (impliesIfNeeded
                    (conjunctionList conditions)
                    (memberTerm
                        result
                        subset')))

proveBoundedMonotonicity
    :: Eq global
    => CheckedFoundation
    -> PreparedInductiveSource global
    -> ProofContext global
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveBoundedMonotonicity
        _foundation
        inductive
        context
        environment = do
    domain <-
        checkedTerm context
            =<< lowerTerm
                environment
                (preparedInductiveDomain
                    inductive)
    operator <-
        checkedTerm context
            =<< operatorTerm
                inductive
                environment
    operatorDomain <-
        checkedTerm context
            (CApp
                (scopedCoreTerm operator)
                (scopedCoreTerm domain))
    bounded <-
        first
            (TypedInductivePreparationContext
                "bounded monotonicity range")
            (proveSubset
                context
                operatorDomain
                domain
                (\elementContext element membership -> do
                    elementEnvironment <-
                        shiftEnvironment environment
                    domainAtElement <-
                        checkedTerm elementContext
                            =<< lowerTerm
                                elementEnvironment
                                (preparedInductiveDomain
                                    inductive)
                    predicate <-
                        checkedTerm elementContext
                            =<< operatorPredicateAt
                                inductive
                                elementEnvironment
                                (scopedCoreTerm
                                    domainAtElement)
                    explicitOperator <-
                        checkedTerm elementContext
                            =<< separationSetAt
                                inductive
                                elementEnvironment
                                (scopedCoreTerm
                                    domainAtElement)
                    explicitMembership <-
                        checkedTerm elementContext
                            (memberTerm
                                (scopedCoreTerm element)
                                (scopedCoreTerm
                                    explicitOperator))
                    separatedMembership <-
                        first TypedInductiveProofError
                            (conversionProof
                                elementContext
                                membership
                                explicitMembership)
                    characteristic <-
                        separationForward
                            elementContext
                            domainAtElement
                            predicate
                            element
                            separatedMembership
                    first TypedInductiveProofError
                        (conjunctionLeftProof
                            elementContext
                            characteristic)))
    monotone <-
        first
            (TypedInductivePreparationContext
                "bounded monotonicity relation")
            (forallIntroductionTyped
                context
                TySet
                (\xContext _x ->
                forallIntroductionTyped
                    xContext
                    TySet
                    (\xyContext _y -> do
                        xyEnvironment <-
                            shiftEnvironment
                                =<< shiftEnvironment
                                    environment
                        x <-
                            checkedTerm xyContext
                                (CBound 1)
                        y <-
                            checkedTerm xyContext
                                (CBound 0)
                        domainXY <-
                            checkedTerm xyContext
                                =<< lowerTerm
                                    xyEnvironment
                                    (preparedInductiveDomain
                                        inductive)
                        relation <-
                            checkedTerm xyContext
                                (conjunctionTerm
                                    (subsetTerm
                                        (scopedCoreTerm x)
                                        (scopedCoreTerm y))
                                    (subsetTerm
                                        (scopedCoreTerm y)
                                        (scopedCoreTerm
                                            domainXY)))
                        implicationIntroductionTyped
                            xyContext
                            relation
                            (\relatedContext _relationProof -> do
                                operatorXY <-
                                    checkedTerm relatedContext
                                        =<< operatorTerm
                                            inductive
                                            xyEnvironment
                                operatorX <-
                                    checkedTerm relatedContext
                                        (CApp
                                            (scopedCoreTerm
                                                operatorXY)
                                            (scopedCoreTerm x))
                                operatorY <-
                                    checkedTerm relatedContext
                                        (CApp
                                            (scopedCoreTerm
                                                operatorXY)
                                            (scopedCoreTerm y))
                                proveSubset
                                    relatedContext
                                    operatorX
                                    operatorY
                                    (\elementContext element membership -> do
                                        elementEnvironment <-
                                            shiftEnvironment
                                                xyEnvironment
                                        xAtElement <-
                                            checkedTerm
                                                elementContext
                                                (CBound 2)
                                        yAtElement <-
                                            checkedTerm
                                                elementContext
                                                (CBound 1)
                                        domainAtElement <-
                                            checkedTerm
                                                elementContext
                                                =<< lowerTerm
                                                    elementEnvironment
                                                    (preparedInductiveDomain
                                                        inductive)
                                        predicateX <-
                                            checkedTerm
                                                elementContext
                                                =<< operatorPredicateAt
                                                    inductive
                                                    elementEnvironment
                                                    (scopedCoreTerm
                                                        xAtElement)
                                        predicateY <-
                                            checkedTerm
                                                elementContext
                                                =<< operatorPredicateAt
                                                    inductive
                                                    elementEnvironment
                                                    (scopedCoreTerm
                                                        yAtElement)
                                        explicitX <-
                                            checkedTerm
                                                elementContext
                                                =<< separationSetAt
                                                    inductive
                                                    elementEnvironment
                                                    (scopedCoreTerm
                                                        xAtElement)
                                        memberExplicitX <-
                                            checkedTerm
                                                elementContext
                                                (memberTerm
                                                    (scopedCoreTerm
                                                        element)
                                                    (scopedCoreTerm
                                                        explicitX))
                                        separatedX <-
                                            first TypedInductiveProofError
                                                (conversionProof
                                                    elementContext
                                                    membership
                                                    memberExplicitX)
                                        characteristicX <-
                                            separationForward
                                                elementContext
                                                domainAtElement
                                                predicateX
                                                element
                                                separatedX
                                        inDomain <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "monotonicity domain projection")
                                                (first TypedInductiveProofError
                                                    (conjunctionLeftProof
                                                        elementContext
                                                        characteristicX))
                                        satisfiesX <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "monotonicity predicate projection")
                                                (first TypedInductiveProofError
                                                    (conjunctionRightProof
                                                        elementContext
                                                        characteristicX))
                                        alternativesX <-
                                            clauseFormulaTerms
                                                inductive
                                                elementEnvironment
                                                (scopedCoreTerm
                                                    xAtElement)
                                                (scopedCoreTerm
                                                    element)
                                        alternativesY <-
                                            clauseFormulaTerms
                                                inductive
                                                elementEnvironment
                                                (scopedCoreTerm
                                                    yAtElement)
                                                (scopedCoreTerm
                                                    element)
                                        predicateXTarget <-
                                            checkedTerm
                                                elementContext
                                                (disjunctionList
                                                    alternativesX)
                                        satisfiesX' <-
                                            first TypedInductiveProofError
                                                (conversionProof
                                                    elementContext
                                                    satisfiesX
                                                    predicateXTarget)
                                        satisfiesY <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "monotonicity predicate transport")
                                                (transformPredicateProof
                                                    inductive
                                                    elementContext
                                                    elementEnvironment
                                                    (scopedCoreTerm
                                                        xAtElement)
                                                    (scopedCoreTerm
                                                        yAtElement)
                                                    (scopedCoreTerm
                                                        domainAtElement)
                                                    (scopedCoreTerm
                                                        element)
                                                    alternativesX
                                                    alternativesY
                                                    satisfiesX')
                                        separatedY <-
                                            first
                                                (TypedInductivePreparationContext
                                                    "monotonicity separation")
                                                (separationBackward
                                                    elementContext
                                                    domainAtElement
                                                    predicateY
                                                    element
                                                    inDomain
                                                    satisfiesY)
                                        let operatorYAtElement =
                                                weakenCheckedScopedCore
                                                    TySet operatorY
                                        explicitMembershipY <-
                                            checkedTerm
                                                elementContext
                                                (memberTerm
                                                    (scopedCoreTerm
                                                        element)
                                                    (scopedCoreTerm
                                                        operatorYAtElement))
                                        first TypedInductiveProofError
                                            (conversionProof
                                                elementContext
                                                separatedY
                                                explicitMembershipY))))))
    first
        (TypedInductivePreparationContext
            "bounded monotonicity conjunction")
        (first TypedInductiveProofError
            (conjunctionIntroductionProof
                context
                bounded
                monotone))

transformPredicateProof
    :: Eq global
    => PreparedInductiveSource global
    -> ProofContext global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> [CanonicalTerm global]
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
transformPredicateProof
        inductive
        context
        environment
        candidateX
        candidateY
        domain
        result
        alternativesX
        alternativesY
        proof = do
    target <-
        checkedTerm context
            (disjunctionList alternativesY)
    first
        (TypedInductivePreparationContext
            "predicate disjunction elimination")
        (eliminateDisjunctionAlternatives
            context
            alternativesX
            proof
            target
            (\caseContext clauseIndex clauseProof -> do
                clause <-
                    maybe
                        (Left
                            (TypedInductiveUnsupportedExpression
                                "inductive clause inventory changed during proof construction"))
                        Right
                        (nth
                            clauseIndex
                            (NonEmpty.toList
                                (preparedInductiveClauses
                                    inductive)))
                first
                    (TypedInductivePreparationContext
                        "predicate witness elimination")
                    (eliminateClauseWitnesses
                        clause
                        caseContext
                        environment
                        candidateX
                        result
                        clauseProof
                        target
                        (\depth
                            leafContext
                            leafEnvironment
                            candidateXAtLeaf
                            resultAtLeaf
                            bodyProof -> do
                            let candidateYAtLeaf =
                                    shiftCanonical
                                        depth
                                        0
                                        candidateY
                                domainAtLeaf =
                                    shiftCanonical
                                        depth
                                        0
                                        domain
                                alternativesYAtLeaf =
                                    shiftCanonical
                                        depth
                                        0
                                        <$> alternativesY
                            bodyY <-
                                first
                                    (TypedInductivePreparationContext
                                        "predicate clause body")
                                    (transformClauseBody
                                        clause
                                        leafContext
                                        leafEnvironment
                                        candidateXAtLeaf
                                        candidateYAtLeaf
                                        domainAtLeaf
                                        resultAtLeaf
                                        bodyProof)
                            resultAtLeaf' <-
                                checkedTerm
                                    leafContext
                                    resultAtLeaf
                            alternativeY <-
                                introduceClauseWitnesses
                                    inductive
                                    clause
                                    leafContext
                                    leafEnvironment
                                    candidateYAtLeaf
                                    resultAtLeaf'
                                    bodyY
                            first
                                (TypedInductivePreparationContext
                                    "predicate disjunction injection")
                                (injectDisjunction
                                    leafContext
                                    clauseIndex
                                    alternativesYAtLeaf
                                    alternativeY)))))

transformClauseBody
    :: Eq global
    => PreparedInductiveClause global
    -> ProofContext global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
transformClauseBody
        clause
        context
        environment
        candidateX
        candidateY
        domain
        result
        proof = do
    conditionsX <-
        traverse
            (conditionTerm
                environment
                candidateX)
            (preparedClauseConditions
                clause)
    clauseResult <-
        lowerTerm
            environment
            (preparedClauseResult clause)
    let equality =
            CEq TySet result clauseResult
        bodyTermsX =
            conditionsX <> [equality]
    projections <-
        projectConjunctionList
            context
            bodyTermsX
            proof
    let (conditionProofs, equalityProofs) =
            splitAt
                (length conditionsX)
                projections
    transformedConditions <-
        sequence
            [ case condition of
                PreparedSideCondition _formula ->
                    pure conditionProof
                PreparedDirectRecursiveCondition
                        recursiveTerm _context -> do
                    recursiveElement <-
                        checkedTerm context
                            =<< lowerTerm
                                environment
                                recursiveTerm
                    subsetProof <-
                        subsetRelationHypothesis
                            context
                            candidateX
                            candidateY
                            domain
                    implication <-
                        first TypedInductiveProofError
                            (forallEliminationProof
                                context
                                subsetProof
                                recursiveElement)
                    first TypedInductiveProofError
                        (implicationEliminationProof
                            context
                            implication
                            conditionProof)
                nested@PreparedNestedRecursiveCondition{} -> do
                    recursiveElement <-
                        checkedTerm context
                            =<< lowerTerm
                                environment
                                (preparedRecursiveTerm nested)
                    subsetProof <-
                        subsetRelationHypothesis
                            context
                            candidateX
                            candidateY
                            domain
                    left <- checkedTerm context candidateX
                    right <- checkedTerm context candidateY
                    transportNestedRecursiveMembership
                        context
                        environment
                        nested
                        left
                        right
                        recursiveElement
                        subsetProof
                        conditionProof
            | (condition, conditionProof) <-
                zip
                    (preparedClauseConditions clause)
                    conditionProofs
            ]
    equalityProof <-
        case equalityProofs of
            [only] ->
                pure only
            _ ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "inductive clause equality projection is inconsistent")
    conjunctionIntroductionList
        context
        (transformedConditions
            <> [equalityProof])

subsetRelationHypothesis
    :: Eq global
    => ProofContext global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (BuiltProof global)
subsetRelationHypothesis
        context
        left
        right
        domain = do
    let leftSubsetRight =
            subsetTerm left right
        rightSubsetDomain =
            subsetTerm right domain
        relation =
            conjunctionTerm
                leftSubsetRight
                rightSubsetDomain
    relationTerm <-
        checkedTerm context relation
    relationProof <-
        first TypedInductiveProofError
            (hypothesisProof
                context
                relationTerm)
    first TypedInductiveProofError
        (conjunctionLeftProof
            context
            relationProof)

preparedRecursiveTerm
    :: PreparedInductiveCondition global
    -> CheckedInductiveTerm global
preparedRecursiveTerm = \case
    PreparedDirectRecursiveCondition term _context -> term
    PreparedNestedRecursiveCondition term _context _index _target -> term
    PreparedSideCondition{} ->
        impossible "a side condition has no recursive element"

transportNestedRecursiveMembership
    :: Eq global
    => ProofContext global
    -> InductiveEnvironment
    -> PreparedInductiveCondition global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
transportNestedRecursiveMembership
        context
        environment
        condition
        left
        right
        element
        subsetProof
        membership = do
    monotonicity <-
        nestedRecursiveMonotonicityProof
            context environment condition left right subsetProof
    implication <-
        first TypedInductiveProofError
            (forallEliminationProof
                context monotonicity element)
    first TypedInductiveProofError
        (implicationEliminationProof
            context implication membership)

nestedRecursiveMonotonicityProof
    :: Eq global
    => ProofContext global
    -> InductiveEnvironment
    -> PreparedInductiveCondition global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
nestedRecursiveMonotonicityProof
        context
        environment
        (PreparedNestedRecursiveCondition
            _term
            (CheckedRecursiveCarrierContext variables _template)
            index
            target)
        left
        right
        subsetProof = do
    theorem <-
        first TypedInductiveProofError
            (importedProof context index target)
    specialized <-
        eliminateWrittenForalls
            context environment variables theorem
    atLeft <-
        first TypedInductiveProofError
            (forallEliminationProof context specialized left)
    atRight <-
        first TypedInductiveProofError
            (forallEliminationProof context atLeft right)
    first TypedInductiveProofError
        (implicationEliminationProof
            context atRight subsetProof)
nestedRecursiveMonotonicityProof
        _context _environment _condition _left _right _subsetProof =
    Left
        (TypedInductiveUnsupportedExpression
            "nested carrier transport requires a monotonicity import")

proveInductionCandidateSubset
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveInductionCandidateSubset
        context fixedPoint predicate candidate subset =
    proveSubset
        context candidate subset
        (\elementContext element membership -> do
            let fixedPointAtElement =
                    weakenCheckedScopedCore TySet fixedPoint
                predicateAtElement =
                    weakenCheckedScopedCore TySet predicate
            explicitMembership <-
                checkedTerm elementContext
                    (memberTerm
                        (scopedCoreTerm element)
                        (apply2
                            (CIntrinsic Sep)
                            (scopedCoreTerm fixedPointAtElement)
                            (scopedCoreTerm predicateAtElement)))
            membership' <-
                first TypedInductiveProofError
                    (conversionProof
                        elementContext membership explicitMembership)
            characteristic <-
                separationForward
                    elementContext
                    fixedPointAtElement
                    predicateAtElement
                    element
                    membership'
            satisfies <-
                first TypedInductiveProofError
                    (conjunctionRightProof
                        elementContext
                        characteristic)
            let expected =
                    weakenCheckedScopedCore TySet subset
            target <-
                checkedTerm elementContext
                    (memberTerm
                        (scopedCoreTerm element)
                        (scopedCoreTerm expected))
            first TypedInductiveProofError
                (conversionProof
                    elementContext satisfies target))

eliminateClauseWitnesses
    :: Eq global
    => PreparedInductiveClause global
    -> ProofContext global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> ( Natural
         -> ProofContext global
         -> InductiveEnvironment
         -> CanonicalTerm global
         -> CanonicalTerm global
         -> BuiltProof global
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
eliminateClauseWitnesses
        clause
        initialContext
        initialEnvironment
        initialCandidate
        initialResult
        initialProof
        initialTarget
        finish =
    go
        0
        initialContext
        initialEnvironment
        initialCandidate
        initialResult
        initialProof
        initialTarget
        (preparedClauseVariables clause)
  where
    go depth context environment candidate result proof target = \case
        [] ->
            finish
                depth
                context
                environment
                candidate
                result
                proof
        variable : remaining -> do
            underBinderEnvironment <-
                rebindEnvironment
                    variable
                    =<< shiftEnvironment
                        environment
            let candidate' =
                    shiftCanonical
                        1
                        0
                        candidate
                result' =
                    shiftCanonical
                        1
                        0
                        result
            bodyUnderBinderTerm <-
                clauseFormulaWithBinders
                    clause
                    underBinderEnvironment
                    candidate'
                    result'
                    remaining
            bodyUnderBinder <-
                first TypedInductiveCoreError
                    (checkScopedTermUnderBinder
                        context
                        TySet
                        bodyUnderBinderTerm)
            let targetUnderBinder =
                    weakenCheckedScopedCore TySet target
            first TypedInductiveProofError
                (existentialEliminationProof
                    context
                    TySet
                    bodyUnderBinder
                    proof
                    target
                    (\underBinderContext _witness bodyProof ->
                        first typedAsProofError
                            (go
                                (depth + 1)
                                underBinderContext
                                underBinderEnvironment
                                candidate'
                                result'
                                bodyProof
                                targetUnderBinder
                                remaining)))

eliminateDisjunctionAlternatives
    :: Eq global
    => ProofContext global
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> Natural
         -> BuiltProof global
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
eliminateDisjunctionAlternatives
        initialContext
        alternatives
        proof
        target
        handle =
    case alternatives of
        [] ->
            Left
                (TypedInductiveUnsupportedExpression
                    "an inductive predicate has no alternatives")
        _ ->
            first TypedInductiveProofError
                (eliminateLeftAssociatedDisjunction
                    initialContext
                    alternatives
                    proof
                    target
                    (\context index branch ->
                        first typedAsProofError
                            (handle context index branch)))

proveInductionClosure
    :: Eq global
    => CheckedFoundation
    -> PreparedInductiveSource global
    -> ProofContext global
    -> InductiveEnvironment
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> [CanonicalTerm global]
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveInductionClosure
        _foundation
        inductive
        context
        environment
        fixedPoint
        operator
        subset
        closures
        _closuresProof =
    forallIntroductionTyped
        context
        TySet
        (\elementContext element -> do
            elementEnvironment <-
                shiftEnvironment environment
            let fixedPointAtElement =
                    weakenCheckedScopedCore TySet fixedPoint
                operatorAtElement =
                    weakenCheckedScopedCore TySet operator
                subsetAtElement =
                    weakenCheckedScopedCore TySet subset
            inductionPredicate <-
                membershipPredicate
                    elementContext
                    subsetAtElement
            candidate <-
                checkedTerm elementContext
                    (apply2
                        (CIntrinsic Sep)
                        (scopedCoreTerm
                            fixedPointAtElement)
                        (scopedCoreTerm
                            inductionPredicate))
            unfolded <-
                checkedTerm elementContext
                    (CApp
                        (scopedCoreTerm
                            operatorAtElement)
                        (scopedCoreTerm
                            candidate))
            premise <-
                checkedTerm elementContext
                    (memberTerm
                        (scopedCoreTerm element)
                        (scopedCoreTerm unfolded))
            implicationIntroductionTyped
                elementContext
                premise
                (\withMember memberProof -> do
                    domain <-
                        checkedTerm withMember
                            =<< lowerTerm
                                elementEnvironment
                                (preparedInductiveDomain
                                    inductive)
                    operatorPredicate <-
                        checkedTerm withMember
                            =<< operatorPredicateAt
                                inductive
                                elementEnvironment
                                (scopedCoreTerm
                                    candidate)
                    explicitOperator <-
                        checkedTerm withMember
                            =<< separationSetAt
                                inductive
                                elementEnvironment
                                (scopedCoreTerm
                                    candidate)
                    explicitMembership <-
                        checkedTerm withMember
                            (memberTerm
                                (scopedCoreTerm
                                    element)
                                (scopedCoreTerm
                                    explicitOperator))
                    separated <-
                        first TypedInductiveProofError
                            (conversionProof
                                withMember
                                memberProof
                                explicitMembership)
                    characteristic <-
                        separationForward
                            withMember
                            domain
                            operatorPredicate
                            element
                            separated
                    predicateProof <-
                        first TypedInductiveProofError
                            (conjunctionRightProof
                                withMember
                                characteristic)
                    alternatives <-
                        clauseFormulaTerms
                            inductive
                            elementEnvironment
                            (scopedCoreTerm
                                candidate)
                            (scopedCoreTerm
                                element)
                    predicateTarget <-
                        checkedTerm
                            withMember
                            (disjunctionList
                                alternatives)
                    predicateProof' <-
                        first TypedInductiveProofError
                            (conversionProof
                                withMember
                                predicateProof
                                predicateTarget)
                    result <-
                        checkedTerm withMember
                            (memberTerm
                                (scopedCoreTerm
                                    element)
                                (scopedCoreTerm
                                    subsetAtElement))
                    subsetMembership <-
                        first
                        (TypedInductivePreparationContext
                            "induction clause alternatives")
                        (eliminateDisjunctionAlternatives
                            withMember
                            alternatives
                            predicateProof'
                            result
                            (\caseContext clauseIndex clauseProof -> do
                                clause <-
                                    maybe
                                        (Left
                                            (TypedInductiveUnsupportedExpression
                                                "inductive closure clause index is outside the source inventory"))
                                        Right
                                        (nth
                                            clauseIndex
                                            (NonEmpty.toList
                                                (preparedInductiveClauses
                                                    inductive)))
                                first
                                    (TypedInductivePreparationContext
                                        "induction clause witnesses")
                                    (eliminateClauseWitnesses
                                        clause
                                        caseContext
                                        elementEnvironment
                                        (scopedCoreTerm
                                            candidate)
                                        (scopedCoreTerm
                                            element)
                                        clauseProof
                                        result
                                        (\depth
                                            leafContext
                                            leafEnvironment
                                            _candidateAtLeaf
                                            resultAtLeaf
                                            bodyProof ->
                                                first
                                                    (TypedInductivePreparationContext
                                                        "induction clause proof")
                                                    (proveInductionClause
                                                        inductive
                                                        clauseIndex
                                                        clause
                                                        leafContext
                                                        leafEnvironment
                                                        (shiftCanonical
                                                            depth
                                                            0
                                                            (scopedCoreTerm
                                                                fixedPointAtElement))
                                                        (shiftCanonical
                                                            depth
                                                            0
                                                            (scopedCoreTerm
                                                                inductionPredicate))
                                                        (shiftCanonical
                                                            depth
                                                            0
                                                            (scopedCoreTerm
                                                                subsetAtElement))
                                                        (shiftCanonical
                                                            (depth + 2)
                                                            0
                                                            <$> closures)
                                                        resultAtLeaf
                                                        bodyProof)))))
                    appliedPredicate <-
                        checkedTerm withMember
                            (CApp
                                (scopedCoreTerm
                                    inductionPredicate)
                                (scopedCoreTerm
                                    element))
                    first TypedInductiveProofError
                        (conversionProof
                            withMember
                            subsetMembership
                            appliedPredicate)))

proveInductionClause
    :: Eq global
    => PreparedInductiveSource global
    -> Natural
    -> PreparedInductiveClause global
    -> ProofContext global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> [CanonicalTerm global]
    -> CanonicalTerm global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveInductionClause
        _inductive
        clauseIndex
        clause
        context
        environment
        fixedPoint
        predicate
        subset
        closures
        result
        bodyProof = do
    conditions <-
        traverse
            (conditionTerm
                environment
                (apply2
                    (CIntrinsic Sep)
                    fixedPoint
                    predicate))
            (preparedClauseConditions
                clause)
    clauseResult <-
        lowerTerm
            environment
            (preparedClauseResult clause)
    let equality =
            CEq TySet result clauseResult
        bodyTerms =
            conditions <> [equality]
    projections <-
        first
            (TypedInductivePreparationContext
                "induction clause body projections")
            (projectConjunctionList
                context
                bodyTerms
                bodyProof)
    let (conditionProofs, equalityProofs) =
            splitAt
                (length conditions)
                projections
    closureConditionProofs <-
        sequence
            [ case condition of
                PreparedSideCondition _formula ->
                    pure conditionProof
                PreparedDirectRecursiveCondition
                        recursiveTerm _context -> do
                    recursiveElement <-
                        checkedTerm context
                            =<< lowerTerm
                                environment
                                recursiveTerm
                    fixedPoint' <-
                        checkedTerm context fixedPoint
                    predicate' <-
                        checkedTerm context predicate
                    separated <-
                        separationForward
                            context
                            fixedPoint'
                            predicate'
                            recursiveElement
                            conditionProof
                    predicateMembership <-
                        first TypedInductiveProofError
                            (conjunctionRightProof
                                context
                                separated)
                    expected <-
                        checkedTerm context
                            (memberTerm
                                (scopedCoreTerm
                                    recursiveElement)
                                subset)
                    first TypedInductiveProofError
                        (conversionProof
                            context
                            predicateMembership
                            expected)
                nested@PreparedNestedRecursiveCondition{} -> do
                    recursiveElement <-
                        checkedTerm context
                            =<< lowerTerm
                                environment
                                (preparedRecursiveTerm nested)
                    fixedPoint' <- checkedTerm context fixedPoint
                    predicate' <- checkedTerm context predicate
                    candidate <-
                        checkedTerm context
                            (apply2
                                (CIntrinsic Sep)
                                fixedPoint
                                predicate)
                    subset' <- checkedTerm context subset
                    candidateSubset <-
                        proveInductionCandidateSubset
                            context
                            fixedPoint'
                            predicate'
                            candidate
                            subset'
                    transportNestedRecursiveMembership
                        context
                        environment
                        nested
                        candidate
                        subset'
                        recursiveElement
                        candidateSubset
                        conditionProof
            | (condition, conditionProof) <-
                zip
                    (preparedClauseConditions clause)
                    conditionProofs
            ]
    closureConjunction <-
        case conjunctionList closures of
            Nothing ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "inductive closure inventory is empty")
            Just conjunction ->
                first
                    (TypedInductivePreparationContext
                        "induction closure conjunction")
                    (checkedTerm context conjunction)
    allClosures <-
        first
            (TypedInductivePreparationContext
                "induction closure hypothesis")
            (first TypedInductiveProofError
                (hypothesisProof
                    context
                    closureConjunction))
    closureProofs <-
        first
            (TypedInductivePreparationContext
                "induction closure projections")
            (projectConjunctionList
                context
                closures
                allClosures)
    selectedClosure <-
        maybe
            (Left
                (TypedInductiveUnsupportedExpression
                    "inductive closure projection is outside the source inventory"))
            Right
            (nth clauseIndex closureProofs)
    specializedClosure <-
        first
            (TypedInductivePreparationContext
                "induction closure specialization")
            (eliminateWrittenForalls
                context
                environment
                (preparedClauseVariables clause)
                selectedClosure)
    resultMembership <-
        case closureConditionProofs of
            [] ->
                pure specializedClosure
            _ -> do
                conjunction <-
                    conjunctionIntroductionList
                        context
                        closureConditionProofs
                first TypedInductiveProofError
                    (implicationEliminationProof
                        context
                        specializedClosure
                        conjunction)
    equalityProof <-
        case equalityProofs of
            [only] ->
                pure only
            _ ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "inductive closure equality projection is inconsistent")
    subset' <-
        first
            (TypedInductivePreparationContext
                "induction subset target")
            (checkedTerm context subset)
    first
        (TypedInductivePreparationContext
            "induction result transport")
        (transportElementMembership
            context
            subset'
            equalityProof
            resultMembership)

transportElementMembership
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
transportElementMembership
        context
        set
        equality
        membership = do
    (sourceElement, targetElement) <-
        case scopedCoreTerm
                (builtProofStatement
                    equality) of
            CEq TySet source target ->
                Right (source, target)
            _ ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "element transport requires set equality")
    predicate <-
        membershipPredicate
            context
            set
    predicateReflexivity <-
        first TypedInductiveProofError
            (equalityReflexivityProof
                context
                predicate)
    propositionEquality <-
        first TypedInductiveProofError
            (equalityCongruenceApplicationProof
                context
                predicateReflexivity
                equality)
    reversed <-
        first TypedInductiveProofError
            (equalityReverseProof
                context
                propositionEquality)
    appliedTarget <-
        checkedTerm context
            (CApp
                (scopedCoreTerm predicate)
                targetElement)
    targetMembership <-
        first TypedInductiveProofError
            (conversionProof
                context
                membership
                appliedTarget)
    transported <-
        first TypedInductiveProofError
            (equalityModusPonensProof
                context
                reversed
                targetMembership)
    sourceMembership <-
        checkedTerm context
            (memberTerm
                sourceElement
                (scopedCoreTerm set))
    first TypedInductiveProofError
        (conversionProof
            context
            transported
            sourceMembership)

predicateAt
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
predicateAt
        inductive
        environment
        candidate
        result =
    disjunctionList
        <$> clauseFormulaTerms
            inductive
            environment
            candidate
            result

clauseFormulaTerms
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        [CanonicalTerm global]
clauseFormulaTerms
        inductive
        environment
        candidate
        result =
    traverse
        (clauseFormulaAt
            environment
            candidate
            result)
        (NonEmpty.toList
            (preparedInductiveClauses
                inductive))

clauseFormulaAt
    :: InductiveEnvironment
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> PreparedInductiveClause global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
clauseFormulaAt
        environment
        candidate
        result
        clause = do
    clauseEnvironment <-
        extendVariables
            environment
            (preparedClauseVariables clause)
    let binderCount =
            fromIntegral
                (length (preparedClauseVariables clause))
        candidate' =
            shiftCanonical binderCount 0 candidate
        result' =
            shiftCanonical binderCount 0 result
    conditions <-
        traverse
            (conditionTerm
                clauseEnvironment
                candidate')
            (preparedClauseConditions
                clause)
    clauseResult <-
        lowerTerm
            clauseEnvironment
            (preparedClauseResult clause)
    pure
        (closeExistentials
            (length
                (preparedClauseVariables
                    clause))
            (fromMaybe
                (CEq TySet result' clauseResult)
                (conjunctionList
                    (conditions
                        <> [CEq
                            TySet
                            result'
                            clauseResult]))))

extendVariables
    :: InductiveEnvironment
    -> [InductiveBinder]
    -> Either
        TypedInductiveError
        InductiveEnvironment
extendVariables =
    go []
  where
    go _seen environment [] =
        Right environment
    go seen environment (variable : remaining)
        | fst variable `elem` seen =
            Left
                (TypedInductiveDuplicateBinder
                    (fst variable))
        | otherwise = do
            extended <-
                rebindEnvironment
                    variable
                    =<< shiftEnvironment
                        environment
            go
                (fst variable : seen)
                extended
                remaining

membershipPredicate
    :: ProofContext global
    -> ScopedCheckedCore global
    -> Either
        TypedInductiveError
        (ScopedCheckedCore global)
membershipPredicate context set = do
    let weakenedSet = weakenCheckedScopedCore TySet set
    checkedTerm context
        (CLam TySet
            (memberTerm
                (CBound 0)
                (scopedCoreTerm
                    weakenedSet)))

operatorPredicateAt
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
operatorPredicateAt
        inductive
        environment
        candidate = do
    extended <-
        shiftEnvironment environment
    body <-
        predicateAt
            inductive
            extended
            (shiftCanonical
                1
                0
                candidate)
            (CBound 0)
    pure (CLam TySet body)

separationSetAt
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
separationSetAt
        inductive
        environment
        candidate = do
    domain <-
        lowerTerm
            environment
            (preparedInductiveDomain
                inductive)
    predicate <-
        operatorPredicateAt
            inductive
            environment
            candidate
    pure
        (apply2
            (CIntrinsic Sep)
            domain
            predicate)

foundationInstance
    :: ProofContext global
    -> FoundationAxiomTag
    -> [ScopedCheckedCore global]
    -> Either
        TypedInductiveError
        (BuiltProof global)
foundationInstance context tag arguments =
    first TypedInductiveProofError
        (foundationInstanceProof context tag arguments)

separationForward
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
separationForward
        context
        domain
        predicate
        element
        membership = do
    characteristic <-
        foundationInstance
            context
            SeparationCharacteristic
            [domain, predicate, element]
    first TypedInductiveProofError
        (equalityModusPonensProof
            context
            characteristic
            membership)

separationBackward
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
separationBackward
        context
        domain
        predicate
        element
        inDomain
        satisfies = do
    characteristic <-
        foundationInstance
            context
            SeparationCharacteristic
            [domain, predicate, element]
    reversed <-
        first TypedInductiveProofError
            (equalityReverseProof
                context
                characteristic)
    expectedSatisfies <-
        checkedTerm context
            (CApp
                (scopedCoreTerm predicate)
                (scopedCoreTerm element))
    satisfies' <-
        first TypedInductiveProofError
            (conversionProof
                context
                satisfies
                expectedSatisfies)
    conjunction <-
        first TypedInductiveProofError
            (conjunctionIntroductionProof
                context
                inDomain
                satisfies')
    first TypedInductiveProofError
        (equalityModusPonensProof
            context
            reversed
            conjunction)

transportMembership
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> BuiltProof global
    -> BuiltProof global
    -> Either
        TypedInductiveError
        (BuiltProof global)
transportMembership
        context
        element
        setEquality
        membership =
    first TypedInductiveProofError
        (transportMembershipProof
            context
            element
            setEquality
            membership)

proveSubset
    :: Eq global
    => ProofContext global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> ScopedCheckedCore global
         -> BuiltProof global
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
proveSubset context left right proveElement =
    forallIntroductionTyped
        context
        TySet
        (\extended element -> do
                let left' = weakenCheckedScopedCore TySet left
                    right' = weakenCheckedScopedCore TySet right
                memberLeft <-
                    checkedTerm extended
                        (memberTerm
                            (scopedCoreTerm element)
                            (scopedCoreTerm left'))
                implicationIntroductionTyped
                    extended
                    memberLeft
                    (\withMember memberProof ->
                        proveElement
                            withMember
                            element
                            memberProof
                            >>= \result -> do
                                expected <-
                                    checkedTerm withMember
                                        (memberTerm
                                            (scopedCoreTerm
                                                element)
                                            (scopedCoreTerm
                                                right'))
                                if builtProofStatement result
                                    == expected
                                    then pure result
                                    else
                                        Left
                                            (TypedInductiveUnsupportedExpression
                                                "subset proof produced the wrong membership target")))

typedAsProofError
    :: TypedInductiveError
    -> KernelProofBuildError
typedAsProofError = \case
    TypedInductiveProofError err ->
        err
    err ->
        ProofSetLfpRuleFailed
            (Text.pack (show err))

implicationIntroductionTyped
    :: ProofContext global
    -> ScopedCheckedCore global
    -> ( ProofContext global
         -> BuiltProof global
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
implicationIntroductionTyped context premise build =
    first TypedInductiveProofError
        (implicationIntroductionProof
            context
            premise
            (\extended proof ->
                first typedAsProofError
                    (build extended proof)))

forallIntroductionTyped
    :: ProofContext global
    -> CoreType
    -> ( ProofContext global
         -> ScopedCheckedCore global
         -> Either
            TypedInductiveError
            (BuiltProof global)
       )
    -> Either
        TypedInductiveError
        (BuiltProof global)
forallIntroductionTyped context binderType build =
    first TypedInductiveProofError
        (forallIntroductionProof
            context
            binderType
            (\extended variable ->
                first typedAsProofError
                    (build extended variable)))

buildUnderVariables
    :: InductiveEnvironment
    -> [InductiveBinder]
    -> ( InductiveEnvironment
         -> Either
            TypedInductiveError
            (CanonicalTerm global)
       )
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
buildUnderVariables
        environment
        []
        build =
    build environment
buildUnderVariables
        environment
        (variable : remaining)
        build = do
    extended <-
        extendEnvironment
            variable
            environment
    buildUnderVariables
        extended
        remaining
        build

fixedPointTerm
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
fixedPointTerm inductive environment = do
    domain <-
        lowerTerm
            environment
            (preparedInductiveDomain
                inductive)
    operator <-
        operatorTerm
            inductive
            environment
    pure
        (CApp
            (CApp
                (CIntrinsic ISetLfp)
                domain)
            operator)

operatorTerm
    :: PreparedInductiveSource global
    -> InductiveEnvironment
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
operatorTerm inductive parameterEnvironment = do
    candidateEnvironment <-
        shiftEnvironment parameterEnvironment
    domain <-
        lowerTerm
            candidateEnvironment
            (preparedInductiveDomain
                inductive)
    resultEnvironment <-
        shiftEnvironment candidateEnvironment
    clauses <-
        traverse
            (clausePredicateTerm
                resultEnvironment)
            (preparedInductiveClauses
                inductive)
    pure
        (CLam TySet
            (CApp
                (CApp
                    (CIntrinsic Sep)
                    domain)
                (CLam TySet
                    (disjunctionList
                        (NonEmpty.toList
                            clauses)))))

clausePredicateTerm
    :: InductiveEnvironment
    -> PreparedInductiveClause global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
clausePredicateTerm
        resultEnvironment
        clause = do
    clauseEnvironment <-
        extendVariables
            resultEnvironment
            (preparedClauseVariables clause)
    let variableCount =
            fromIntegral
                (length (preparedClauseVariables clause))
        resultVariable =
            CBound variableCount
        candidate =
            CBound (variableCount + 1)
    conditions <-
        traverse
            (conditionTerm
                clauseEnvironment
                candidate)
            (preparedClauseConditions
                clause)
    result <-
        lowerTerm
            clauseEnvironment
            (preparedClauseResult
                clause)
    pure
        (closeExistentials
            (length
                (preparedClauseVariables clause))
            (fromMaybe
                (CEq
                    TySet
                    resultVariable
                    result)
                (conjunctionList
                    (conditions
                        <> [CEq
                            TySet
                            resultVariable
                            result]))))

directConditionTerm
    :: InductiveEnvironment
    -> CanonicalTerm global
    -> DirectInductiveCondition global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
directConditionTerm environment candidate = \case
    DirectSideCondition formula ->
        lowerFormula environment formula
    DirectRecursiveCondition term context -> do
        carrier <-
            betaNormalizeCanonical
                <$> instantiateRecursiveCarrier
                    environment candidate
                    (checkedRecursiveContext context)
        memberTerm
            <$> lowerTerm environment term
            <*> pure carrier
  where
    checkedRecursiveContext
            (RecursiveCarrierContext _location _direct variables template) =
        CheckedRecursiveCarrierContext variables template

conditionTerm
    :: InductiveEnvironment
    -> CanonicalTerm global
    -> PreparedInductiveCondition global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
conditionTerm environment candidate = \case
    PreparedSideCondition formula ->
        lowerFormula
            environment
            formula
    PreparedDirectRecursiveCondition term context -> do
        carrier <-
            instantiateRecursiveCarrier environment candidate context
        memberTerm
            <$> lowerTerm
                environment
                term
            <*> pure carrier
    PreparedNestedRecursiveCondition term context _index _target -> do
        carrier <-
            instantiateRecursiveCarrier environment candidate context
        memberTerm
            <$> lowerTerm environment term
            <*> pure carrier

shiftEnvironment
    :: InductiveEnvironment
    -> Either
        TypedInductiveError
        InductiveEnvironment
shiftEnvironment
        (InductiveEnvironment variables) =
    pure
        (InductiveEnvironment
            (first succ <$> variables))

lowerFormula
    :: InductiveEnvironment
    -> CheckedInductiveFormula global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
lowerFormula environment
        (CheckedInductiveFormula variables template) =
    instantiateCheckedTemplate environment variables template

lowerTerm
    :: InductiveEnvironment
    -> CheckedInductiveTerm global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
lowerTerm environment (CheckedInductiveTerm variables template) =
    instantiateCheckedTemplate environment variables template

instantiateCheckedTemplate
    :: InductiveEnvironment
    -> [InductiveBinder]
    -> FrozenCheckedCore global
    -> Either
        TypedInductiveError
        (CanonicalTerm global)
instantiateCheckedTemplate environment variables template = do
    arguments <- traverse (`lookupEnvironment` environment) variables
    foldM instantiateLambda (frozenCoreTerm template) arguments
  where
    instantiateLambda term argument =
        case term of
            CLam _binderType body ->
                pure (instantiateCanonical argument body)
            _ ->
                Left
                    (TypedInductiveUnsupportedExpression
                        "a checked inductive expression lost its typed telescope")

memberTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
memberTerm =
    apply2 (CIntrinsic Member)

subsetTerm
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
subsetTerm left right =
    CForall TySet
        (CImp
            (memberTerm
                (CBound 0)
                (shiftCanonical
                    1
                    0
                    left))
            (memberTerm
                (CBound 0)
                (shiftCanonical
                    1
                    0
                    right)))

apply2
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
apply2 function firstArgument secondArgument =
    CApp
        (CApp function firstArgument)
        secondArgument

conjunctionList
    :: [CanonicalTerm global]
    -> Maybe (CanonicalTerm global)
conjunctionList = \case
    [] ->
        Nothing
    firstTerm : remaining ->
        Just
            (foldl'
                conjunctionTerm
                firstTerm
                remaining)

disjunctionList
    :: [CanonicalTerm global]
    -> CanonicalTerm global
disjunctionList = \case
    [] ->
        CFalsum
    firstTerm : remaining ->
        foldl'
            disjunctionTerm
            firstTerm
            remaining

impliesIfNeeded
    :: Maybe (CanonicalTerm global)
    -> CanonicalTerm global
    -> CanonicalTerm global
impliesIfNeeded = \case
    Nothing ->
        id
    Just premise ->
        CImp premise

closeLambdas
    :: [CoreType]
    -> CanonicalTerm global
    -> CanonicalTerm global
closeLambdas types body = foldr CLam body types

closeForalls
    :: [CoreType]
    -> CanonicalTerm global
    -> CanonicalTerm global
closeForalls types body = foldr CForall body types

closeExistentials
    :: Int
    -> CanonicalTerm global
    -> CanonicalTerm global
closeExistentials binderCount body =
    foldl'
        (\current _ ->
            existentialTerm TySet current)
        body
        [1 .. binderCount]

freezeClosedTarget
    :: GlobalTyping global
    -> CanonicalTerm global
    -> Either
        TypedInductiveError
        (FrozenCheckedCore global)
freezeClosedTarget globalTyping =
    first TypedInductiveCoreError
        . checkCanonicalCore globalTyping
