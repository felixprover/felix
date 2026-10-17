{-# LANGUAGE NoImplicitPrelude #-}

-- | Source normalization for structural recursion. Datatype provenance and
-- clause coverage belong here; construction and proof authority stay in Recursion.
module Felix.Checking.Recursion.Frontend (prepareRecursiveDefinition) where

import Base
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Bifunctor (first)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as E
import Felix.Checking.Elaboration.Vocabulary (fixedSemanticMeaning)
import Felix.Checking.Recursion (RecursiveDefinitionInput(..))
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as Source
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface

prepareRecursiveDefinition
    :: Raw.Block -> [CanonicalLexicalEntry]
    -> Declaration.LoweringDriver (Either E.ElaborationError RecursiveDefinitionInput)
prepareRecursiveDefinition block entries = Except.runExceptT do
    (location, Raw.Marker name, definition) <- case block of
        Raw.BlockRecursive location _ marker definition -> pure (location,marker,definition)
        _ -> Except.throwE (E.ElaborationUnsupportedDeclaration (locate block))
    let invalid = E.ElaborationRecursiveDefinitionInvalid location
        require :: Text -> Maybe a -> Except.ExceptT E.ElaborationError Declaration.LoweringDriver a
        require message = maybe (Except.throwE (invalid message)) pure
    key <- case entries of
        [entry] -> require "unrecognized head notation" (semanticGlobalKeyFromLexicalEntry entry)
        _ -> Except.throwE (invalid "expected exactly one head notation")
    (headKey, variables, resultType) <- case Raw.recursiveHead definition of
        Left (Raw.SymbolPattern symbol variables) -> pure
            (SemanticExpressionFunction (Raw.mixfixPattern symbol), variables, TySet)
        Right (Raw.DefnSymbolicPredicate (Raw.PrefixPredicate command arity) _ variables) -> pure
            (SemanticPrefixPredicate command (fromIntegral arity), toList variables, TyProp)
        _ -> Except.throwE (invalid "expected a set-valued symbolic head or prefix predicate")
    unless (key == headKey && semanticGlobalKeyType key == Just (foldr (const (TyArrow TySet)) resultType variables))
        (Except.throwE (invalid "the head disagrees with its declared notation"))
    unless (listToMaybe (reverse variables) == Just (Raw.recursiveVariable definition))
        (Except.throwE (invalid "the structural variable must be the final head argument"))
    when (isJust (firstDuplicate variables)) (Except.throwE (invalid "head variables must be distinct"))
    when (isJust (fixedSemanticMeaning key)) (Except.throwE (E.ElaborationFixedSemanticCollision location key))
    visible <- lift (Declaration.resolveVisibleGlobalLowering key)
    when (isJust visible) (Except.throwE (E.ElaborationGlobalAlreadyVisible location key))
    let parameters = take (length variables-1) variables
    context <- Except.except $ case NonEmpty.nonEmpty (zip (E.localId <$> [0..]) parameters) of
        Nothing -> pure E.emptyElaborationContext
        Just binders -> E.extendElaborationContext binders E.emptyElaborationContext
    domain <- Except.ExceptT (E.elaborateSetExpression context (Raw.recursiveDomain definition))
    let writtenDomain = E.elaboratedSetExpressionSource domain
    provider <- require "the structural domain must name a checked datatype" (Source.sourceTermOccurrenceProvider writtenDomain)
    reference <- case Source.sourceTermProviderHead provider of
        GlobalSourceProvider reference -> pure reference
        _ -> Except.throwE (invalid "the structural domain must name a checked datatype")
    resolved <- lift (Declaration.resolveVisibleGlobalLowering (globalBindingRefKey reference))
    (datatype,_) <- require "the structural datatype is not visible" resolved
    unless (resolvedBindingRef datatype == reference)
        (Except.throwE (invalid "the structural domain lost its source binding"))
    descriptor <- require "the structural domain is not a datatype"
        (semanticGlobalBindingDatatype (resolvedBindingDeclaration datatype))
    arguments <- for (toList (Source.sourceTermProviderArguments provider)) \argument ->
        case scopedCoreTerm (Source.sourceTermOccurrenceCore argument) of
            CBound index | index < fromIntegral (length parameters) -> pure index
            _ -> Except.throwE (invalid "datatype family arguments must be fixed head variables")
    let carrier = Source.forgetScopedSourceTermOccurrence writtenDomain
        owner = globalBindingRefOwner reference
        descriptions = datatypeDescriptorCases descriptor
    clauses <- for (Raw.recursiveClauses definition) \clause -> do
        (appliedKey, args, body) <- case Raw.recursiveClauseEquation clause of
            Left (Raw.ExprOp _ symbol args, value) | resultType == TySet -> pure
                (SemanticExpressionFunction (Raw.mixfixPattern symbol), args, Left value)
            Right (Raw.FormulaPredicate _ (Raw.PrefixPredicate command arity) _ args, value) | resultType == TyProp -> pure
                (SemanticPrefixPredicate command (fromIntegral arity), toList args, Right value)
            _ -> Except.throwE (invalid "each clause must be an equation for the declared head and result type")
        unless (appliedKey == key && length args == length variables
            && take (length parameters) args == (Raw.ExprVar <$> parameters))
            (Except.throwE (invalid "clause heads must preserve all fixed parameters"))
        constructor <- require "missing constructor pattern" (listToMaybe (reverse args))
        (symbol,fields) <- case constructor of
            Raw.ExprOp _ symbol fields -> pure (symbol,fields)
            _ -> Except.throwE (invalid "the structural pattern must be a constructor applied to distinct variables")
        let constructorKey = SemanticExpressionFunction (Raw.mixfixPattern symbol)
        description <- require "the clause constructor does not belong to the declared datatype"
            (find ((== constructorKey) . datatypeCaseConstructor) (toList descriptions))
        actual <- lift (Declaration.resolveVisibleGlobalLowering constructorKey) >>= require "the constructor is not visible"
        unless (resolvedBindingRef (fst actual) == globalBindingRef owner constructorKey)
            (Except.throwE (invalid "the constructor presentation has a different owner"))
        for_ (Raw.recursiveClauseName clause) \heading -> unless
            (Raw.datatypeCaseKey heading == Just (datatypeCaseName description))
            (Except.throwE (invalid "the clause heading does not name its constructor case"))
        names <- for fields \case
            Raw.ExprVar variable -> pure variable
            _ -> Except.throwE (invalid "constructor fields must be distinct variables")
        unless (length names == length (datatypeCaseFields description) && isNothing (firstDuplicate names))
            (Except.throwE (invalid "constructor fields must be distinct variables of the correct arity"))
        domains <- for (datatypeCasePremises description) \case
            DatatypeRecursivePremise -> pure (carrier,True)
            DatatypeFixedPremise term -> do
                specialized <- Except.except (first invalid (instantiateCanonicalPrefixWith (pure ())
                    (fromIntegral (length arguments)) (\depth slot ->
                        maybe (Left "a premise escapes its datatype parameters")
                            (pure . shiftCanonical depth 0 . CBound) (nth slot (reverse arguments))) 0 term))
                pure (Source.sourceTermOccurrence specialized TySet (E.LocatedSourceTerm location),False)
        stored <- for (zip names (datatypeCaseFields description)) \(variable,slot) -> do
            (domain,recursive) <- require "invalid stored-field slot in the datatype descriptor" (nth slot domains)
            pure (variable,domain,recursive)
        let witnesses = [domain | (slot,(domain,_)) <- zip [0..] domains, slot `notElem` datatypeCaseFields description]
        pure (constructorKey,E.RecursiveBranch stored witnesses body)
    unless (length clauses == NonEmpty.length descriptions && isNothing (firstDuplicate (fst <$> toList clauses)))
        (Except.throwE (invalid "exactly one clause is required for every constructor"))
    ordered <- for descriptions \description -> require "a constructor clause is missing"
        (Map.lookup (datatypeCaseConstructor description) (Map.fromList (toList clauses)))
    (headers,branches) <- Except.ExceptT (E.elaborateRecursiveBranches location key parameters
        (Raw.recursiveAssumptions definition) ordered)
    pure (RecursiveDefinitionInput name key (semanticBindingLabel name) datatype arguments headers branches)
