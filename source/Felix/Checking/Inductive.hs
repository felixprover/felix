{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Preparation and atomic publication of direct set inductives.
module Felix.Checking.Inductive
    ( PreparedInductive
    , preparedInductiveCarrierId
    , preparedInductiveCarrierType
    , preparedInductiveCarrierBody
    , preparedInductiveGuardTargets
    , preparedInductiveFacts
    , prepareInductive
    , CheckedInductiveAuthorization
    , lowerPreparedInductive
    , authorizeCheckedInductive
    , InductiveError(..)
    , inductiveErrorLocation
    , renderInductiveError
    ) where

import Base hiding (Empty)
import Felix.Checking.Planning qualified as Planning
import Felix.Checking.Authority
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Elaboration.Vocabulary
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.Semantic
import Felix.Checking.Inductive.Construction qualified as Typed
import Felix.Cache.Codec
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface

import Control.Monad (unless, when)
import Control.Monad.Except (ExceptT)
import Control.Monad.Except qualified as Except
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector


data PreparedInductive = PreparedInductive
    !Location
    !SemanticGlobalKey
    !ObjectId
    !(Maybe AssertedObject)
    !SemanticName
    !DeclarationSyntaxId
    !(Typed.PreparedTypedInductive ObjectId)
    ![SemanticFactOccurrenceFingerprint]

data CheckedInductiveAuthorization =
    CheckedInductiveAuthorization
        !ObjectId
        !(Typed.PreparedTypedInductive ObjectId)
        ![SemanticFactOccurrenceFingerprint]
        ![(Location, Declaration.PreparedVampireObligation Void ())]

preparedInductiveCarrierId
    :: PreparedInductive
    -> ObjectId
preparedInductiveCarrierId
        (PreparedInductive
            _location _key identity _asserted _alias _syntax _typed _guards) =
    identity

preparedInductiveCarrierType
    :: PreparedInductive
    -> CoreType
preparedInductiveCarrierType
        (PreparedInductive
            _location _key _identity _asserted _alias _syntax typed _guards) =
    Typed.typedInductiveCarrierType typed

preparedInductiveCarrierBody
    :: PreparedInductive
    -> FrozenCheckedCore ObjectId
preparedInductiveCarrierBody
        (PreparedInductive
            _location _key _identity _asserted _alias _syntax typed _guards) =
    Typed.typedInductiveCarrierBody typed

preparedInductiveGuardTargets
    :: PreparedInductive
    -> Vector.Vector (FrozenCheckedCore ObjectId)
preparedInductiveGuardTargets
        (PreparedInductive
            _location _key _identity _asserted _alias _syntax typed _guards) =
    Typed.typedInductiveGuardTargets typed

preparedInductiveFacts
    :: PreparedInductive
    -> NonEmpty (Typed.PreparedTypedInductiveFact ObjectId)
preparedInductiveFacts
        (PreparedInductive
            _location _key _identity _asserted _alias _syntax typed _guards) =
    Typed.typedInductiveFacts typed

data InductiveError
    = InductiveUnsupportedBlock !Location
    | InductiveOccurrenceMissing !Location
    | InductiveOccurrenceAmbiguous !Location
    | InductiveHeadMismatch !Location
    | InductiveDuplicateParameter !Location !Raw.VarSymbol
    | InductiveDomainFreeVariable !Location !Raw.VarSymbol
    | InductiveDomainMentionsCarrier !Location
    | InductiveResultShape !Location
    | InductiveResultMentionsCarrier !Location
    | InductiveRecursiveTermMentionsCarrier !Location
    | InductiveRecursiveCarrierWrongArguments !Location
    | InductiveRecursiveCarrierOutsideMembership !Location
    | InductiveUnsupportedRecursiveCarrierContext !Location
    | InductiveFixedSemanticCollision !Location !SemanticGlobalKey
    | InductiveGlobalAlreadyVisible !Location !SemanticGlobalKey
    | InductiveElaborationFailed !Elaboration.ElaborationError
    | InductivePreparationFailed
        !Location
        !Typed.TypedInductiveError
    | InductiveGuardMissing !Location
    | InductiveGuardAmbiguous !Location
    deriving stock (Show, Eq)

inductiveErrorLocation :: InductiveError -> Location
inductiveErrorLocation = \case
    InductiveUnsupportedBlock location -> location
    InductiveOccurrenceMissing location -> location
    InductiveOccurrenceAmbiguous location -> location
    InductiveHeadMismatch location -> location
    InductiveDuplicateParameter location _parameter -> location
    InductiveDomainFreeVariable location _variable -> location
    InductiveDomainMentionsCarrier location -> location
    InductiveResultShape location -> location
    InductiveResultMentionsCarrier location -> location
    InductiveRecursiveTermMentionsCarrier location -> location
    InductiveRecursiveCarrierWrongArguments location -> location
    InductiveRecursiveCarrierOutsideMembership location -> location
    InductiveUnsupportedRecursiveCarrierContext location -> location
    InductiveFixedSemanticCollision location _key -> location
    InductiveGlobalAlreadyVisible location _key -> location
    InductiveElaborationFailed failure ->
        Elaboration.elaborationErrorLocation failure
    InductivePreparationFailed location _failure -> location
    InductiveGuardMissing location -> location
    InductiveGuardAmbiguous location -> location

renderInductiveError :: InductiveError -> Text
renderInductiveError failure =
    locationToText (inductiveErrorLocation failure)
        <> ": "
        <> case failure of
            InductiveUnsupportedBlock{} ->
                "this inductive source form is not supported by the typed checker"
            InductiveOccurrenceMissing{} ->
                "the inductive declaration has no associated syntax occurrence"
            InductiveOccurrenceAmbiguous{} ->
                "the inductive declaration has more than one semantic head"
            InductiveHeadMismatch{} ->
                "the inductive head does not match its syntax occurrence"
            InductiveDuplicateParameter _location parameter ->
                "the inductive parameter is repeated: " <> shown parameter
            InductiveDomainFreeVariable _location variable ->
                "the inductive domain contains an unbound variable: "
                    <> shown variable
            InductiveDomainMentionsCarrier{} ->
                "the inductive domain must be independent of its carrier"
            InductiveResultShape{} ->
                "an inductive result must have the form t \\in F(args)"
            InductiveResultMentionsCarrier{} ->
                "an inductive result term must not mention its carrier"
            InductiveRecursiveTermMentionsCarrier{} ->
                "a recursive occurrence must be in the carrier of a membership premise"
            InductiveRecursiveCarrierWrongArguments{} ->
                "the inductive carrier occurs with arguments other than its declared parameters"
            InductiveRecursiveCarrierOutsideMembership{} ->
                "an inductive carrier occurrence must be in the set operand of a membership premise"
            InductiveUnsupportedRecursiveCarrierContext{} ->
                "this recursive carrier context is outside the supported first-order set-term fragment"
            InductiveFixedSemanticCollision _location key ->
                "the inductive carrier collides with fixed semantics for "
                    <> shown key
            InductiveGlobalAlreadyVisible _location key ->
                "the inductive carrier is already visible: " <> shown key
            InductiveElaborationFailed elaborationFailure ->
                "inductive expression elaboration failed: "
                    <> Elaboration.renderElaborationError elaborationFailure
            InductivePreparationFailed _location typedFailure ->
                "typed inductive preparation failed: " <> shown typedFailure
            InductiveGuardMissing{} ->
                "an inductive domain guard has no visible authorized fact"
            InductiveGuardAmbiguous{} ->
                "an inductive domain guard matches more than one visible fact"
  where
    shown :: Show value => value -> Text
    shown = Text.pack . show

type Prepare =
    ExceptT
        InductiveError
        (Declaration.LoweringDriver)

prepareInductive
    :: CheckedFoundation
    -> Raw.Block
    -> [CanonicalLexicalEntry]
    -> Declaration.LoweringDriver
        (Either InductiveError PreparedInductive)
prepareInductive foundation block entries =
    Except.runExceptT do
        (location, marker, rawInductive) <-
            case block of
                Raw.BlockInductive blockLocation _title blockMarker inductive ->
                    pure (blockLocation, blockMarker, inductive)
                _ ->
                    Except.throwError
                        (InductiveUnsupportedBlock (locate block))
        key <- validateOccurrence location rawInductive entries
        when
            (isJust (fixedSemanticMeaning key))
            (Except.throwError
                (InductiveFixedSemanticCollision location key))
        visible <-
            Trans.lift
                (Declaration.resolveVisibleGlobalLowering key)
        when (isJust visible)
            (Except.throwError
                (InductiveGlobalAlreadyVisible location key))
        closure <-
            Trans.lift Declaration.checkedObjectClosureLowering
        let globalTyping = globalTypingFromClosure closure
        direct <-
            prepareDirectInductive globalTyping location rawInductive
        let Raw.Marker markerText = marker
        typed <-
            Except.liftEither
                (first
                    (InductivePreparationFailed location)
                    (Typed.prepareTypedInductive
                        globalTyping
                        foundation
                        markerText
                        direct))
        guards <-
            traverse
                (resolveGuard location)
                (Vector.toList
                    (Typed.typedInductiveGuardTargets typed))
        theory <- Trans.lift Declaration.currentTheoryLowering
        let carrierType = Typed.typedInductiveCarrierType typed
            carrierBody = Typed.typedInductiveCarrierBody typed
            carrierTerm = frozenCoreTerm carrierBody
            carrier = transparentObject theory carrierType carrierTerm
            identity = assertedObjectId carrier
            alias = case marker of
                Raw.Marker name -> semanticName name
        available <-
            Trans.lift
                (Declaration.objectAvailableLowering identity)
        let asserted
                | available = Nothing
                | otherwise = Just carrier
            syntax =
                declarationSyntaxId
                    (encodePreparedInductive key alias typed)
        pure
            (PreparedInductive
                location
                key
                identity
                asserted
                alias
                syntax
                typed
                guards)
validateOccurrence
    :: Location
    -> Raw.Inductive
    -> [CanonicalLexicalEntry]
    -> Prepare SemanticGlobalKey
validateOccurrence location rawInductive entries = do
    entry <-
        case entries of
            [] ->
                Except.throwError
                    (InductiveOccurrenceMissing location)
            [single] -> pure single
            _ ->
                Except.throwError
                    (InductiveOccurrenceAmbiguous location)
    key <-
        maybe
            (Except.throwError
                (InductiveHeadMismatch location))
            pure
            (semanticGlobalKeyFromLexicalEntry entry)
    let Raw.SymbolPattern headSymbol _parameters =
            Raw.inductiveSymbolPattern rawInductive
        expected =
            SemanticExpressionFunction
                (Raw.mixfixPattern headSymbol)
    unless (key == expected)
        (Except.throwError
            (InductiveHeadMismatch location))
    pure key

data ValidatedInductive = ValidatedInductive
    ![Raw.VarSymbol]
    !Raw.Expr
    !(NonEmpty ValidatedInductiveClause)

data ValidatedInductiveClause = ValidatedInductiveClause
    ![Raw.VarSymbol]
    ![ValidatedInductiveCondition]
    !Raw.Expr

data ValidatedInductiveCondition
    = ValidatedSideCondition !Raw.Formula
    | ValidatedRecursiveCondition
        !Raw.Expr
        !Location
        !Bool
        !Raw.VarSymbol
        !Raw.Expr

prepareDirectInductive
    :: GlobalTyping ObjectId
    -> Location
    -> Raw.Inductive
    -> Prepare (Typed.DirectInductive ObjectId)
prepareDirectInductive globalTyping declarationLocation rawInductive = do
    validated <-
        Except.liftEither
            (validateDirectInductive declarationLocation rawInductive)
    let ValidatedInductive parameters domain clauses = validated
        allVariables =
            nubOrd
                (parameters
                    <> concat
                        [ variables
                        | ValidatedInductiveClause
                            variables _conditions _result <- toList clauses
                        ])
        variableIds =
            Map.fromList
                (zip allVariables
                    (Typed.InductiveVariable <$> [0 ..]))
        typedVariables variables =
            [(typedVariable variableIds variable, TySet) | variable <- variables]
    preparedDomain <-
        prepareSetTerm
            globalTyping
            variableIds
            declarationLocation
            parameters
            domain
    preparedClauses <-
        traverse
            (prepareClause
                variableIds parameters typedVariables)
            clauses
    pure
        (Typed.DirectInductive
            (typedVariables parameters)
            preparedDomain
            preparedClauses)
  where
    prepareClause variableIds parameters typedVariables
            (ValidatedInductiveClause variables conditions result) = do
        let sourceVariables = parameters <> variables
            checkedVariables = typedVariables sourceVariables
        preparedConditions <-
            traverse
                (prepareCondition
                    variableIds sourceVariables checkedVariables)
                conditions
        preparedResult <-
            prepareSetTerm
                globalTyping
                variableIds
                (locate result)
                sourceVariables
                result
        pure
            (Typed.DirectInductiveClause
                (typedVariables variables)
                preparedConditions
                preparedResult)

    prepareCondition variableIds sourceVariables
            checkedVariables = \case
        ValidatedSideCondition formula -> do
            Typed.DirectSideCondition
                <$> prepareProposition
                    globalTyping variableIds (locate formula)
                    sourceVariables formula
        ValidatedRecursiveCondition term location direct hole contextExpr -> do
            preparedTerm <-
                prepareSetTerm
                    globalTyping
                    variableIds
                    (locate term)
                    sourceVariables
                    term
            context <-
                binderContextWithHole variableIds sourceVariables hole
            preparedContextExpr <-
                Trans.lift
                    (Elaboration.elaborateExpression
                        context
                        (Raw.TypedExpressionExpr contextExpr))
                    >>= either
                        (Except.throwError
                            . InductiveElaborationFailed)
                        pure
            let scoped =
                    Elaboration.elaboratedExpressionCore
                        preparedContextExpr
            preparedContext <-
                Except.liftEither
                    (first
                        (InductivePreparationFailed location)
                        (Typed.prepareRecursiveCarrierContext
                            globalTyping
                            location
                            direct
                            checkedVariables
                            scoped))
            pure
                (Typed.DirectRecursiveCondition
                    preparedTerm preparedContext)

prepareSetTerm
    :: GlobalTyping ObjectId
    -> Map.Map Raw.VarSymbol Typed.InductiveVariable
    -> Location
    -> [Raw.VarSymbol]
    -> Raw.Expr
    -> Prepare (Typed.CheckedInductiveTerm ObjectId)
prepareSetTerm globalTyping variableIds location variables expression = do
    context <- binderContext variableIds variables
    prepared <-
        Trans.lift
            (Elaboration.elaborateExpression
                context
                (Raw.TypedExpressionExpr expression))
            >>= either
                (Except.throwError
                    . InductiveElaborationFailed)
                pure
    let scoped = Elaboration.elaboratedExpressionCore prepared
    Except.liftEither
        (first
            (InductivePreparationFailed location)
            (Typed.prepareCheckedInductiveTerm
                globalTyping
                [(typedVariable variableIds variable, TySet) | variable <- variables]
                scoped))

prepareProposition
    :: GlobalTyping ObjectId
    -> Map.Map Raw.VarSymbol Typed.InductiveVariable
    -> Location
    -> [Raw.VarSymbol]
    -> Raw.Formula
    -> Prepare (Typed.CheckedInductiveFormula ObjectId)
prepareProposition globalTyping variableIds location variables formula = do
    context <- binderContext variableIds variables
    prepared <-
        Trans.lift
            (Elaboration.elaborateProposition
                context
                (Raw.StmtFormula formula))
            >>= either
                (Except.throwError
                    . InductiveElaborationFailed)
                pure
    let scoped = Elaboration.elaboratedPropositionCore prepared
    Except.liftEither
        (first
            (InductivePreparationFailed location)
            (Typed.prepareCheckedInductiveFormula
                globalTyping
                [(typedVariable variableIds variable, TySet) | variable <- variables]
                scoped))

typedVariable
    :: Map.Map Raw.VarSymbol Typed.InductiveVariable
    -> Raw.VarSymbol
    -> Typed.InductiveVariable
typedVariable variableIds variable =
    fromMaybe
        (impossible "a validated inductive variable lost its identity")
        (Map.lookup variable variableIds)

binderContext
    :: Map.Map Raw.VarSymbol Typed.InductiveVariable
    -> [Raw.VarSymbol]
    -> Prepare Elaboration.ElaborationContext
binderContext variableIds variables =
    case NonEmpty.nonEmpty
            [ ( Elaboration.localId index
              , variable
              )
            | variable <- variables
            , let Typed.InductiveVariable index =
                    typedVariable variableIds variable
            ] of
        Nothing -> pure Elaboration.emptyElaborationContext
        Just binders ->
            Except.liftEither
                (first InductiveElaborationFailed
                    (Elaboration.extendElaborationContext
                        binders
                        Elaboration.emptyElaborationContext))

binderContextWithHole
    :: Map.Map Raw.VarSymbol Typed.InductiveVariable
    -> [Raw.VarSymbol]
    -> Raw.VarSymbol
    -> Prepare Elaboration.ElaborationContext
binderContextWithHole variableIds variables hole = do
    let holeIdentity =
            Elaboration.localId
                (fromIntegral (Map.size variableIds))
        additions =
            [ ( Elaboration.localId index
              , variable
              )
            | variable <- variables
            , let Typed.InductiveVariable index =
                    typedVariable variableIds variable
            ]
            <> [(holeIdentity, hole)]
    case NonEmpty.nonEmpty additions of
        Nothing -> impossible "a recursive carrier context has no hole"
        Just binders ->
            Except.liftEither
                (first InductiveElaborationFailed
                    (Elaboration.extendElaborationContext
                        binders
                        Elaboration.emptyElaborationContext))

validateDirectInductive
    :: Location
    -> Raw.Inductive
    -> Either InductiveError ValidatedInductive
validateDirectInductive declarationLocation rawInductive = do
    let Raw.SymbolPattern carrier parameters =
            Raw.inductiveSymbolPattern rawInductive
        domain = Raw.inductiveDomain rawInductive
        parameterSet = Set.fromList parameters
    case firstDuplicate parameters of
        Just duplicate ->
            Left
                (InductiveDuplicateParameter
                    (locate duplicate)
                    duplicate)
        Nothing -> pure ()
    validateFirstOrderSetExpression declarationLocation domain
    case find (\variable -> Set.notMember variable parameterSet)
            (expressionVariables domain) of
        Just variable ->
            Left
                (InductiveDomainFreeVariable
                    (locate variable)
                    variable)
        Nothing -> pure ()
    when
        (expressionMentions carrier domain)
        (Left
            (InductiveDomainMentionsCarrier
                (locate domain)))
    clauses <-
        traverse
            (validateClause carrier parameters)
            (Raw.inductiveIntros rawInductive)
    pure (ValidatedInductive parameters domain clauses)

validateClause
    :: Raw.FunctionSymbol
    -> [Raw.VarSymbol]
    -> Raw.IntroRule
    -> Either InductiveError ValidatedInductiveClause
validateClause carrier parameters rule = do
    conditions <-
        traverse
            (validateCondition carrier parameters)
            (Raw.introConditions rule)
    result <-
        validateResult carrier parameters (Raw.introResult rule)
    let parameterSet = Set.fromList parameters
        variables =
            List.filter
                (\variable -> Set.notMember variable parameterSet)
                (nubOrd
                    ( concatMap formulaVariables
                        (Raw.introConditions rule)
                      <> expressionVariables result
                    ))
    pure (ValidatedInductiveClause variables conditions result)

validateResult
    :: Raw.FunctionSymbol
    -> [Raw.VarSymbol]
    -> Raw.Formula
    -> Either InductiveError Raw.Expr
validateResult carrier parameters formula =
    case membershipFormula formula of
        Just (result, target)
            | not (matchesCarrier carrier parameters target) ->
                Left (InductiveResultShape (locate target))
            | expressionMentions carrier result ->
                Left
                    (InductiveResultMentionsCarrier
                        (locate result))
            | otherwise -> do
                validateFirstOrderSetExpression (locate result) result
                pure result
        Nothing ->
            Left (InductiveResultShape (locate formula))

validateCondition
    :: Raw.FunctionSymbol
    -> [Raw.VarSymbol]
    -> Raw.Formula
    -> Either InductiveError ValidatedInductiveCondition
validateCondition carrier parameters formula
    | not (formulaMentions carrier formula) = do
        validateFirstOrderFormula formula
        pure (ValidatedSideCondition formula)
    | otherwise =
        case membershipFormula formula of
            Just (recursiveTerm, recursiveCarrier)
                | expressionMentions carrier recursiveTerm ->
                    Left
                        (InductiveRecursiveTermMentionsCarrier
                            (locate recursiveTerm))
                | otherwise -> do
                    validateFirstOrderSetExpression
                        (locate recursiveTerm)
                        recursiveTerm
                    let hole =
                            freshCarrierHole
                                (expressionVariables recursiveCarrier
                                    <> parameters)
                                (locate recursiveCarrier)
                    context <-
                        replaceCarrier
                            carrier parameters hole recursiveCarrier
                    pure
                        (ValidatedRecursiveCondition
                            recursiveTerm
                            (locate recursiveCarrier)
                            (matchesCarrier
                                carrier parameters recursiveCarrier)
                            hole
                            context)
            Nothing ->
                Left
                    (InductiveRecursiveCarrierOutsideMembership
                        (locate formula))

membershipFormula :: Raw.Formula -> Maybe (Raw.Expr, Raw.Expr)
membershipFormula = \case
    Raw.FormulaChain
        (Raw.ChainBase
            (left :| [])
            Raw.Positive
            (Raw.Relation _location Raw.ElementSymbol [])
            (right :| [])) ->
                Just (left, right)
    _ -> Nothing

matchesCarrier
    :: Raw.FunctionSymbol
    -> [Raw.VarSymbol]
    -> Raw.Expr
    -> Bool
matchesCarrier carrier parameters = \case
    Raw.ExprOp _location candidate arguments ->
        candidate == carrier
            && length arguments == length parameters
            && and
                (zipWith
                    (\argument parameter ->
                        argument == Raw.ExprVar parameter)
                    arguments
                    parameters)
    _ -> False

replaceCarrier
    :: Raw.FunctionSymbol
    -> [Raw.VarSymbol]
    -> Raw.VarSymbol
    -> Raw.Expr
    -> Either InductiveError Raw.Expr
replaceCarrier carrier parameters hole = go
  where
    go = \case
        Raw.ExprOp location candidate arguments
            | candidate == carrier ->
                if matchesCarrier
                        carrier parameters
                        (Raw.ExprOp location candidate arguments)
                    then pure (Raw.ExprVar hole)
                    else
                        Left
                            (InductiveRecursiveCarrierWrongArguments
                                location)
            | otherwise ->
                Raw.ExprOp location candidate <$> traverse go arguments
        Raw.ExprFiniteSet location elements ->
            Raw.ExprFiniteSet location <$> traverse go elements
        expression@Raw.ExprVar{} -> pure expression
        expression@Raw.ExprNaturalNumeral{} -> pure expression
        expression@Raw.ExprOpaqueInteger{} -> pure expression
        expression ->
            Left
                (InductiveUnsupportedRecursiveCarrierContext
                    (locate expression))

freshCarrierHole :: [Raw.VarSymbol] -> Location -> Raw.VarSymbol
freshCarrierHole variables location =
    Raw.FreshVarAt location
        (1 + maximum (-1
            : [ index
              | Raw.FreshVarAt _variableLocation index <- variables
              ]))

validateFirstOrderSetExpression
    :: Location
    -> Raw.Expr
    -> Either InductiveError ()
validateFirstOrderSetExpression fallback = \case
    Raw.ExprVar{} -> pure ()
    Raw.ExprNaturalNumeral{} -> pure ()
    Raw.ExprOpaqueInteger{} -> pure ()
    Raw.ExprOp _location _symbol arguments ->
        traverse_ (validateFirstOrderSetExpression fallback) arguments
    Raw.ExprFiniteSet _location elements ->
        traverse_ (validateFirstOrderSetExpression fallback) elements
    expression ->
        unsupportedFirstOrder
            (preferKnownLocation (locate expression) fallback)

validateFirstOrderFormula
    :: Raw.Formula
    -> Either InductiveError ()
validateFirstOrderFormula = \case
    Raw.FormulaChain chain -> validateChain chain
    Raw.FormulaSetMap _location function domain codomain ->
        traverse_
            (validateFirstOrderSetExpression (locate function))
            [function, domain, codomain]
    Raw.FormulaPredicate _location _predicate _marker expressions ->
        traverse_
            (validateFirstOrderSetExpression (locate expressions))
            expressions
    Raw.Connected _location _connective left right ->
        validateFirstOrderFormula left
            *> validateFirstOrderFormula right
    Raw.FormulaNeg _location formula ->
        validateFirstOrderFormula formula
    Raw.PropositionalConstant{} -> pure ()
    formula ->
        unsupportedFirstOrder (locate formula)
  where
    validateChain = \case
        Raw.ChainBase left _sign relation right -> do
            traverse_ (validateFirstOrderSetExpression (locate left)) left
            validateRelation relation
            traverse_ (validateFirstOrderSetExpression (locate right)) right
        Raw.ChainCons left _sign relation rest -> do
            traverse_ (validateFirstOrderSetExpression (locate left)) left
            validateRelation relation
            validateChain rest

    validateRelation = \case
        Raw.Relation _location _symbol parameters ->
            traverse_
                (validateFirstOrderSetExpression (locate parameters))
                parameters
        Raw.RelationExpr _location expression ->
            validateFirstOrderSetExpression (locate expression) expression

unsupportedFirstOrder
    :: Location
    -> Either InductiveError a
unsupportedFirstOrder location =
    Left
        (InductivePreparationFailed
            location
            (Typed.TypedInductiveUnsupportedExpression
                "higher-order, quantified, and set-construction syntax is not supported in direct inductive declarations"))

expressionVariables :: Raw.Expr -> [Raw.VarSymbol]
expressionVariables = \case
    Raw.ExprVar variable -> [variable]
    Raw.ExprNaturalNumeral{} -> []
    Raw.ExprOpaqueInteger{} -> []
    Raw.ExprOp _location _symbol arguments ->
        concatMap expressionVariables arguments
    Raw.ExprFiniteSet _location elements ->
        concatMap expressionVariables elements
    _ -> []

formulaVariables :: Raw.Formula -> [Raw.VarSymbol]
formulaVariables = \case
    Raw.FormulaChain chain -> chainVariables chain
    Raw.FormulaSetMap _location function domain codomain ->
        concatMap expressionVariables [function, domain, codomain]
    Raw.FormulaPredicate _location _predicate _marker expressions ->
        concatMap expressionVariables expressions
    Raw.Connected _location _connective left right ->
        formulaVariables left <> formulaVariables right
    Raw.FormulaNeg _location formula ->
        formulaVariables formula
    _ -> []
  where
    chainVariables = \case
        Raw.ChainBase left _sign relation right ->
            concatMap expressionVariables left
                <> relationVariables relation
                <> concatMap expressionVariables right
        Raw.ChainCons left _sign relation rest ->
            concatMap expressionVariables left
                <> relationVariables relation
                <> chainVariables rest

    relationVariables = \case
        Raw.Relation _location _symbol parameters ->
            concatMap expressionVariables parameters
        Raw.RelationExpr _location expression ->
            expressionVariables expression

expressionMentions :: Raw.FunctionSymbol -> Raw.Expr -> Bool
expressionMentions carrier = \case
    Raw.ExprVar{} -> False
    Raw.ExprNaturalNumeral{} -> False
    Raw.ExprOpaqueInteger{} -> False
    Raw.ExprTypedConstant{} -> False
    Raw.ExprHigherApply _location function argument ->
        typedExpressionMentions carrier function
            || typedExpressionMentions carrier argument
    Raw.ExprLambda _location _variables _type body ->
        typedExpressionMentions carrier body
    Raw.ExprSelect _location _type predicate ->
        typedExpressionMentions carrier predicate
    Raw.ExprOp _location symbol arguments ->
        symbol == carrier
            || any (expressionMentions carrier) arguments
    Raw.ExprStructOp _location _symbol argument ->
        any (expressionMentions carrier) argument
    Raw.ExprFiniteSet _location elements ->
        any (expressionMentions carrier) elements
    Raw.ExprSep _location _variable bound predicate ->
        expressionMentions carrier bound
            || statementMentions carrier predicate
    Raw.ExprReplace _location value bounds condition ->
        expressionMentions carrier value
            || any (expressionMentions carrier . snd) bounds
            || any (statementMentions carrier) condition
    Raw.ExprReplacePred _location _range _domain bound predicate ->
        expressionMentions carrier bound
            || statementMentions carrier predicate
    Raw.ExprStructAggregate _location _schema entries ->
        any
            (expressionMentions carrier
                . Raw.structAggregateEntryExpression)
            entries
    Raw.ExprStructReduct _location _schema record ->
        expressionMentions carrier record
    Raw.ExprStructReconstruction _location (Raw.StructApplication _ arguments) record entries ->
        any (expressionMentions carrier) arguments
            || expressionMentions carrier record
            || any (expressionMentions carrier . Raw.structAggregateEntryExpression) entries

typedExpressionMentions
    :: Raw.FunctionSymbol
    -> Raw.TypedExpression
    -> Bool
typedExpressionMentions carrier = \case
    Raw.TypedExpressionExpr expression ->
        expressionMentions carrier expression
    Raw.TypedExpressionFormula formula ->
        formulaMentions carrier formula

statementMentions :: Raw.FunctionSymbol -> Raw.Stmt -> Bool
statementMentions carrier = \case
    Raw.StmtFormula formula ->
        formulaMentions carrier formula
    Raw.StmtNeg _location statement ->
        statementMentions carrier statement
    Raw.StmtConnected _connective _location left right ->
        statementMentions carrier left
            || statementMentions carrier right
    Raw.SymbolicQuantified
            _location _quantifier _variables bound condition statement ->
        boundMentionsCarrier carrier bound
            || any (statementMentions carrier) condition
            || statementMentions carrier statement
    _ -> False

boundMentionsCarrier :: Raw.FunctionSymbol -> Raw.Bound -> Bool
boundMentionsCarrier carrier = \case
    Raw.Unbounded -> False
    Raw.Bounded _location _sign relation expression ->
        relationMentionsCarrier carrier relation
            || expressionMentions carrier expression

relationMentionsCarrier :: Raw.FunctionSymbol -> Raw.Relation -> Bool
relationMentionsCarrier carrier = \case
    Raw.Relation _location _symbol parameters ->
        any (expressionMentions carrier) parameters
    Raw.RelationExpr _location expression ->
        expressionMentions carrier expression

formulaMentions :: Raw.FunctionSymbol -> Raw.Formula -> Bool
formulaMentions carrier = \case
    Raw.FormulaChain chain -> chainMentions chain
    Raw.FormulaSetMap _location function domain codomain ->
        any (expressionMentions carrier) [function, domain, codomain]
    Raw.FormulaExpression expression ->
        expressionMentions carrier expression
    Raw.FormulaPredicate _location _predicate _marker expressions ->
        any (expressionMentions carrier) expressions
    Raw.Connected _location _connective left right ->
        formulaMentions carrier left || formulaMentions carrier right
    Raw.FormulaNeg _location formula ->
        formulaMentions carrier formula
    Raw.FormulaQuantified _location _quantifier _variables bound formula ->
        boundMentionsCarrier carrier bound
            || formulaMentions carrier formula
    Raw.FormulaTypedQuantified _location _quantifier _variables _type formula ->
        formulaMentions carrier formula
    Raw.PropositionalConstant{} -> False
  where
    chainMentions = \case
        Raw.ChainBase left _sign relation right ->
            any (expressionMentions carrier) left
                || relationMentionsCarrier carrier relation
                || any (expressionMentions carrier) right
        Raw.ChainCons left _sign relation rest ->
            any (expressionMentions carrier) left
                || relationMentionsCarrier carrier relation
                || chainMentions rest

resolveGuard
    :: Location
    -> FrozenCheckedCore ObjectId
    -> Prepare SemanticFactOccurrenceFingerprint
resolveGuard location target = do
    matches <-
        Trans.lift
            (Declaration.resolveVisibleFactTargetsLowering target)
    case matches of
        [] ->
            Except.throwError (InductiveGuardMissing location)
        [fingerprint] ->
            pure fingerprint
        _ ->
            Except.throwError (InductiveGuardAmbiguous location)

lowerPreparedInductive
    :: PreparedInductive
    -> Declaration.LoweringDriver
        (Either
            Declaration.DeclarationError
            (Declaration.CheckedDeclaration
                CheckedInductiveAuthorization))
lowerPreparedInductive
        (PreparedInductive
            _location key identity asserted alias syntax typed guards) =
    do
        let facts = Typed.typedInductiveFacts typed
            monotonicities =
                Vector.toList
                    (Typed.typedInductiveMonotonicities typed)
            objects = maybeToList asserted
        definition <-
            Declaration.prepareDefinitionEquationSpecLowering
                objects identity alias
        preparedMonotonicities <-
            traverse
                (\monotonicity -> Except.runExceptT do
                    let factLocation =
                            Typed.typedInductiveMonotonicityLocation
                                monotonicity
                        target =
                            Typed.typedInductiveMonotonicityTarget
                                monotonicity
                    spec <-
                        Trans.lift
                            (Declaration.prepareFrozenCandidateSpecLowering
                                objects target SearchIneligible [])
                            >>= Except.liftEither
                    obligation <-
                        Trans.lift
                            (Declaration.prepareScopedVampireObligationLowering
                                Vector.empty
                                (embedClosedCore [] target)
                                []
                                []
                                Declaration.internalVampirePremisePolicy)
                            >>= either
                                (Except.throwError
                                    . Declaration.ProofObligationFailedAt
                                        factLocation
                                    . Declaration.CurrentCandidateVampirePreparationFailed)
                                pure
                    pure
                        ( Declaration.checkedCandidate
                            spec
                            (Declaration.checkedExternalSourceProofPlanning
                                ( Declaration.checkedPlannedVampireRequest
                                    factLocation obligation :| []
                                )
                                [])
                        , (factLocation, obligation)
                        ))
                monotonicities
        preparedCandidates <-
            traverse
                (\fact -> do
                    prepared <-
                        Declaration.prepareCandidateSpecLowering
                            objects
                            (embedClosedCore []
                                (Typed.typedInductiveFactTarget fact))
                            SearchEligible
                            [markerAlias
                                (Typed.typedInductiveFactMarker fact)]
                    let descriptor =
                            GuardedFoundationRules
                                (guardedRuleSet
                                    (Typed.typedInductiveFactRules fact))
                        planning
                            | null monotonicities =
                                Declaration.checkedKernelPlanning
                                    descriptor guards
                            | otherwise =
                                Declaration.checkedKernelPlanningWithStaged
                                    descriptor
                                    guards
                                    (if Typed.typedInductiveFactRequiresMonotonicities
                                            fact
                                        then
                                            [ Planning.plannedEarlierCandidate
                                                1 index
                                            | (index, _target) <-
                                                zip [0 ..] monotonicities
                                            ]
                                        else [])
                    pure
                        (fmap
                            (\spec ->
                                Declaration.checkedCandidate spec planning)
                            prepared))
                facts
        pure do
            definitionSpec <- definition
            monotonicityCandidates <- sequence preparedMonotonicities
            factCandidates <- sequence preparedCandidates
            let stages
                    | null monotonicityCandidates =
                        [ Declaration.checkedCandidate definitionSpec
                            (Declaration.checkedDefinitionEquationPlanning identity)
                            :| toList factCandidates
                        ]
                    | otherwise =
                        [ Declaration.checkedCandidate definitionSpec
                            (Declaration.checkedDefinitionEquationPlanning identity)
                            :| []
                        , NonEmpty.fromList (fst <$> monotonicityCandidates)
                        , factCandidates
                        ]
            pure
                (Declaration.checkedCompiledDeclaration
                    syntax
                    objects
                    []
                    [semanticGlobalBinding
                        key
                        (semanticBindingLabel (semanticNameText alias))
                        (GlobalReference identity)]
                    Nothing
                    stages
                    (CheckedInductiveAuthorization
                        identity typed guards
                        (snd <$> monotonicityCandidates)))
  where
    markerAlias = semanticName

authorizeCheckedInductive
    :: CheckedInductiveAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedInductive
        (CheckedInductiveAuthorization
            identity typed guards monotonicityObligations) = \case
    [definitionCandidate :| candidates] -> do
        unless (null monotonicityObligations)
            (Declaration.failDeclaration
                (Declaration.CheckedAuthorizationCandidateShapeMismatch 3 1))
        Declaration.authorizeDefinitionEquationCandidate
            identity definitionCandidate
        let facts = Typed.typedInductiveFacts typed
        case NonEmpty.nonEmpty candidates of
            Just factCandidates
                | NonEmpty.length factCandidates == NonEmpty.length facts ->
                    sequence_
                        (NonEmpty.zipWith
                            (authorizeFact [])
                            factCandidates
                            facts)
            _ ->
                Declaration.failDeclaration
                    (Declaration.CheckedAuthorizationCandidateShapeMismatch
                        (1 + NonEmpty.length facts)
                        (1 + length candidates))
    [ definitionCandidate :| []
      , monotonicityCandidates
      , factCandidates
      ]
        | NonEmpty.length monotonicityCandidates
                == length monotonicityObligations
        , NonEmpty.length factCandidates
                == NonEmpty.length (Typed.typedInductiveFacts typed) -> do
            obligations <-
                maybe
                    (Declaration.failDeclaration
                        (Declaration.CheckedAuthorizationCandidateShapeMismatch
                            1 0))
                    pure
                    (NonEmpty.nonEmpty monotonicityObligations)
            Declaration.authorizeDefinitionEquationCandidate
                identity definitionCandidate
            Declaration.authorizeVampireCandidateBatch
                (NonEmpty.zipWith
                    (\candidate (factLocation, obligation) ->
                        (factLocation, candidate, pure obligation))
                    monotonicityCandidates
                    obligations)
            sequence_
                (NonEmpty.zipWith
                    (\candidate fact ->
                        authorizeFact
                            (if Typed.typedInductiveFactRequiresMonotonicities
                                    fact
                                then NonEmpty.toList monotonicityCandidates
                                else [])
                            candidate
                            fact)
                    factCandidates
                    (Typed.typedInductiveFacts typed))
    stages ->
        Declaration.failDeclaration
            (Declaration.CheckedAuthorizationCandidateShapeMismatch
                (if null monotonicityObligations then 1 else 3)
                (length stages))
  where
    authorizeFact monotonicityCandidates candidate fact =
        Declaration.authorizeKernelConstructionCandidate
            (GuardedFoundationRules
                (guardedRuleSet
                    (Typed.typedInductiveFactRules fact)))
            candidate do
                traverse_ Declaration.useAuthorizedFact guards
                traverse_
                    Declaration.useStagedCandidate
                    monotonicityCandidates
                pure (Typed.typedInductiveFactDerivation fact)


encodePreparedInductive
    :: SemanticGlobalKey
    -> SemanticName
    -> Typed.PreparedTypedInductive ObjectId
    -> ByteString
encodePreparedInductive key alias typed =
    encodeCache do
        putCacheTag 0x04
        putSemanticGlobalKeyCache key
        putCoreTypeCache
            (Typed.typedInductiveCarrierType typed)
        putCanonicalTermCache putObjectIdCache
            (frozenCoreTerm
                (Typed.typedInductiveCarrierBody typed))
        putCacheList putFrozenTerm
            (Vector.toList
                (Typed.typedInductiveContextInventory typed))
        putCacheList
            (putFrozenTerm
                . Typed.typedInductiveMonotonicityTarget)
            (Vector.toList
                (Typed.typedInductiveMonotonicities typed))
        putCacheText (semanticNameText alias)
        putCacheList putFact
            (toList (Typed.typedInductiveFacts typed))
  where
    putFrozenTerm =
        putCanonicalTermCache putObjectIdCache . frozenCoreTerm

    putFact fact = do
        putCacheText (Typed.typedInductiveFactMarker fact)
        putCanonicalTermCache putObjectIdCache
            (frozenCoreTerm
                (Typed.typedInductiveFactTarget fact))
        putCacheList
            (putCacheBytes . encodeCache . putKernelRuleTagCache)
            (toList (Typed.typedInductiveFactRules fact))
