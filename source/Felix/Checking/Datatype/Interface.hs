{-# LANGUAGE NoImplicitPrelude #-}

-- | Recheck datatype descriptions against ordinary checked objects and laws.
-- The description guides source proofs; its referenced theorems justify
-- construction and induction. A carrier's binding supplies its source identity.
module Felix.Checking.Datatype.Interface
    ( checkDatatypeBindings
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Construction
import Felix.Checking.Identity
import Felix.Checking.GlobalTyping (lookupGlobalType)
import Felix.Checking.Semantic
import Felix.Syntax.Abstract qualified as Raw

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text

-- Bindings and facts must be the contributions of this one declaration.
checkDatatypeBindings
    :: CheckedObjectClosure
    -> [SemanticGlobalBinding]
    -> [(SemanticFactOccurrence, CheckedPropositionContent)]
    -> Either Text ()
checkDatatypeBindings closure bindings localFacts =
    for_ bindings \binding -> for_ (semanticGlobalBindingDatatype binding) (check binding)
  where
    typing = globalTypingFromClosure closure
    localBindings = Map.fromList [(semanticGlobalBindingKey binding, binding) | binding <- bindings]
    localLaws = Map.fromList [(semanticFactFingerprint occurrence, proposition) | (occurrence, proposition) <- localFacts]
    check binding descriptor = do
        carrier <- reference binding
        parameterCount <- arity carrier
        let parameters = CBound . fromIntegral <$> reverse [0 .. parameterCount - 1]
            carrierTerm = foldl' CApp (CGlobal carrier) parameters
            clauses = datatypeDescriptorCases descriptor
            keys = datatypeCaseName <$> toList clauses
            constructors = datatypeCaseConstructor <$> toList clauses
        unless (length keys == Set.size (Set.fromList keys))
            (Left "datatype case keys are not distinct")
        unless (length constructors == Set.size (Set.fromList constructors))
            (Left "datatype constructor bindings are not distinct")
        unless (semanticGlobalBindingKey binding `notElem` constructors)
            (Left "a datatype constructor reuses its carrier binding")
        prepared <- traverse (prepareCase parameterCount) clauses
        checkConstructorLaws parameterCount carrierTerm (zip (toList clauses) (toList prepared))
        checkLaw parameterCount (datatypeDescriptorCasesFact descriptor)
            (Construction.casesTarget parameterCount carrierTerm prepared)
        checkLaw parameterCount (datatypeDescriptorInductionFact descriptor)
            (Construction.inductionTarget parameterCount carrierTerm prepared)
        checkLaw parameterCount (datatypeDescriptorPredicateInductionFact descriptor)
            (Construction.predicateInductionTarget parameterCount carrierTerm prepared)

    checkConstructorLaws _ _ [] = pure ()
    checkConstructorLaws parameterCount carrier ((description, clause) : rest) = do
        checkLaw parameterCount (datatypeCaseIntroductionFact description)
            (Construction.introductionTarget parameterCount carrier clause)
        case (null (Construction.clauseArgumentSlots clause), datatypeCaseInjectivityFact description) of
            (True, Nothing) -> pure ()
            (False, Just fact) -> checkLaw 0 fact (pure (Construction.injectiveTarget clause))
            _ -> Left "datatype injectivity law does not match its constructor arity"
        let distinct = datatypeCaseDistinctnessFacts description
        unless ((fst <$> distinct) == [datatypeCaseConstructor later | (later, _) <- rest])
            (Left "datatype distinctness laws do not cover the later constructors in order")
        for_ (zip distinct rest) \((_, fact), (_, later)) ->
            checkLaw 0 fact (pure (Construction.distinctTarget clause later))
        checkConstructorLaws parameterCount carrier rest

    reference binding = case semanticGlobalBindingTarget binding of
        GlobalReference object -> Right object
        _ -> Left "a datatype binding must be an ordinary global reference"

    arity object = maybe (Left "datatype object type is unavailable") go (lookupGlobalType typing object)
      where
        go TySet = Right 0
        go (TyArrow TySet rest) = (+ 1) <$> go rest
        go _ = Left "datatype carriers and constructors must have set arguments and a set result"

    prepareCase parameterCount clause = do
        binding <- maybe (Left "datatype constructor is not declared by its owner") Right
            (Map.lookup (datatypeCaseConstructor clause) localBindings)
        let name = datatypeCaseName clause
            legacy = Text.toLower (semanticBindingLabelText (semanticGlobalBindingLabel binding))
        unless (Raw.datatypeCaseKey name == Just name || name == legacy)
            (Left "datatype case key is neither a normalized name nor its constructor label")
        constructor <- reference binding
        count <- arity constructor
        let slots = datatypeCaseFields clause
            premises = datatypeCasePremises clause
        unless (length slots == count && length slots == Set.size (Set.fromList slots)
                && all (< fromIntegral (length premises)) slots)
            (Left "datatype constructor fields do not match its premise telescope")
        domains <- traverse (\case
            DatatypeRecursivePremise -> Right Construction.Recursive
            DatatypeFixedPremise term -> do
                checked <- first (Text.pack . show) (checkScopedCanonicalCore typing (replicate parameterCount TySet) term)
                unless (scopedCoreType checked == TySet) (Left "a datatype premise domain must be a set")
                pure (Construction.FixedDomain checked)) premises
        pure (Construction.Clause constructor slots domains)

    checkLaw parameterCount fingerprint target = do
        proposition <- maybe (Left "datatype law is not declared by its owner") Right (Map.lookup fingerprint localLaws)
        body <- first (Text.pack . show) target
        let expected = foldr CForall body (replicate parameterCount TySet)
        unless (frozenCoreTerm (checkedPropositionTerm proposition) == expected)
            (Left "datatype description disagrees with its checked law")
