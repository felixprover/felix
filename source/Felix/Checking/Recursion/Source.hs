{-# LANGUAGE NoImplicitPrelude #-}

-- | Source descriptions at recursive substitution boundaries. Providers come
-- only from written operands or admitted templates, never from object equality.
module Felix.Checking.Recursion.Source
    ( SourceTerm
    , writtenOperands
    , instantiateSource
    , sealProposition
    , branchSource
    , preferredBindings
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.ScopedSource qualified as ScopedSource
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Recursion.Application
import Felix.Checking.Recursion.Interface
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Semantic
import Felix.Checking.SourceTemplate qualified as Template
import Felix.Checking.SourceTerm qualified as Source
import Felix.Report.Location

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import Data.Vector qualified as Vector

type SourceTerm = Source.SourceTermOccurrence Elaboration.SourceTermPresentation (CanonicalTerm ObjectId)
type Evidence = SourceEvidence SupportTermTemplate Elaboration.ScopedSourceNotionOccurrence
type Work = ExpansionWork Declaration.LoweringDriver

writtenOperands
    :: GlobalTyping ObjectId -> Location -> ScopedCheckedCore ObjectId -> Evidence
    -> Work [SourceTerm]
writtenOperands typing location goal evidence = do
    let portable = fmap (fmap (Source.sourceSupportTemplate scopedCoreTerm) . Notion.sourceAssertionAtom)
            (writtenSourceEvidence evidence)
        checking = Source.SourceTermCheckingContext typing (scopedCoreContext goal)
    operands <- expansionCoreWork (\work -> ScopedSource.sourceTemplateInputs typing work
        (scopedCoreContext goal) (scopedCoreTerm goal) portable)
    description <- Template.abstractSourceProposition Vector.empty
        (SourceInputs Nothing (SourceInput [] <$> operands)) []
    terms <- case description of
        PropositionExpansion (SourceInputs _ inputs) [] -> for inputs \case
            SourceInput [] term -> pure term
            _ -> invalid "a written operand retained a private binder"
        _ -> invalid "written operands changed shape during abstraction"
    providers <- resolveProviders description
    for terms \term -> Template.instantiateSourceTemplate checking providers location
        (Elaboration.LocatedSourceTerm location) (WrittenOrigin location Nothing)
        Vector.empty Vector.empty CTruth (TermExpansion term) >>= \case
            Template.InstantiatedTerm value -> pure value
            _ -> invalid "a written operand became a proposition"

instantiateSource
    :: GlobalTyping ObjectId -> [CoreType] -> Location -> [SourceTerm] -> [SourceTerm]
    -> ([CoreType], CanonicalTerm ObjectId, AbbreviationExpansion)
    -> Work (Template.SourceTemplateInstance Elaboration.SourceTermPresentation)
instantiateSource typing context location written arguments (formals,body,description) = do
    chargeExpansion (fromIntegral (length formals + length arguments))
    unless (length formals == length arguments) (invalid "a recursive source template changed arity")
    providers <- resolveProviders description
    -- Keep all explicitly retained views as additive evidence. Equal Core
    -- does not select one written provider as the identity of another slot.
    writtenParts <- concat <$> traverse operandParts written
    views <- for (zip [0..] arguments) \(index,argument) -> do
        matches <- for writtenParts \candidate -> do
            same <- expansionCoreWork (\work -> countedCanonicalIdentity work
                (Source.sourceTermOccurrenceCore argument) (Source.sourceTermOccurrenceCore candidate))
            pure [candidate | same]
        pure (index,concat matches)
    let layout = Vector.fromList (fromIntegral <$> reverse [0 .. length formals - 1])
    extras <- Template.sourceTemplateInputAnnotations layout (Map.fromList views) body
    instance' <- Template.instantiateSourceTemplate (Source.SourceTermCheckingContext typing context) providers location
        (Elaboration.LocatedSourceTerm location) (WrittenOrigin location Nothing)
        layout
        (Vector.fromList arguments) body description
    pure $ case instance' of
        Template.InstantiatedProposition formula evidence equalities ->
            Template.InstantiatedProposition formula (withSourceInputs extras evidence) equalities
        term -> term

operandParts :: SourceTerm -> Work [SourceTerm]
operandParts term = do
    chargeExpansion 1
    nested <- case Source.sourceTermOccurrenceProvider term of
        Just provider -> concat <$> traverse operandParts (toList (Source.sourceTermProviderArguments provider))
        Nothing -> case Source.sourceTermOccurrenceOrderedPair term of
            Just (left,right) -> (<>) <$> operandParts left <*> operandParts right
            Nothing -> pure []
    pure (term:nested)

preferredBindings
    :: GlobalTyping ObjectId -> Location -> ScopedCheckedCore ObjectId
    -> ScopedCheckedCore ObjectId -> Evidence -> Work [GlobalBindingRef]
preferredBindings typing location call goal evidence = do
    written <- writtenOperands typing location goal evidence >>= fmap concat . traverse operandParts
    catMaybes <$> for written \term -> case Source.sourceTermOccurrenceProvider term of
        Just provider | GlobalSourceProvider binding <- Source.sourceTermProviderHead provider -> do
            same <- expansionCoreWork (\work -> countedCanonicalIdentity work (scopedCoreTerm call) (Source.sourceTermOccurrenceCore term))
            pure (if same then Just binding else Nothing)
        _ -> pure Nothing

sealProposition
    :: GlobalTyping ObjectId -> [CoreType] -> Location
    -> Template.SourceTemplateInstance Elaboration.SourceTermPresentation
    -> Work (ScopedCheckedCore ObjectId, Evidence)
sealProposition typing context location = \case
    Template.InstantiatedProposition formula evidence _equalities -> do
        goal <- check context formula
        unless (scopedCoreType goal == TyProp) (invalid "a recursive guard is not a proposition")
        described <- traverseAtDepth (\depth atom -> do
            let types = replicate (fromIntegral depth) TySet <> context
            terms <- traverse (\term -> expansionCoreWork (\work ->
                Source.countedSealCanonicalSourceTermOccurrence work (Source.SourceTermCheckingContext typing types) term))
                (Notion.sourceAssertionAtom atom)
            target <- check types (Notion.sourceAssertionFormula atom)
            let result = Notion.sourceNotionAssertionFromTemplate terms target Notion.ConjunctionHere location
            pure (maybe result (`Notion.withSourceNotionOrigin` result) (Notion.sourceNotionWrittenOrigin atom))) evidence
        pure (goal,described)
    Template.InstantiatedTerm{} -> invalid "a recursive guard template returned a term"
  where
    check types term = expansionCoreWork (\work -> countedCheckScopedCanonicalCore typing work types term)

-- The branch's typed formal context includes its recursive results. Those
-- results get the owning function's declared view; other views remain the
-- explicit source annotations supplied to this substitution.
branchSource
    :: GlobalTyping ObjectId -> Location -> CheckedRecursiveDefinition -> RecursiveApplication
    -> [SourceTerm] -> Work (ScopedCheckedCore ObjectId,Evidence)
branchSource typing location definition application written = do
    description@(formals,_,_) <- require (nth (applicationCase application) (toList (recursiveSources definition)))
    clause <- require (nth (applicationCase application) (toList (recursiveClauses definition)))
    let arguments = applicationBranchArguments application
        parameterCount = recursiveParameterCount definition
        plainCount = parameterCount + length (Datatype.clauseArgumentSlots clause)
        opaque ty term = Source.sourceTermOccurrence term ty (Elaboration.LocatedSourceTerm location)
        parameters = opaque TySet <$> take parameterCount arguments
        context = scopedCoreContext (applicationEquality application)
    actuals <- for (zip3 [0 :: Int ..] (reverse formals) arguments) \(index,ty,term) -> do
        chargeExpansion 1
        if index < plainCount || ty /= TySet then pure (opaque ty term) else case term of
            CApp _ child -> require (Source.sourceGlobalProviderTermOccurrence (recursiveBinding definition)
                (Vector.fromList (parameters <> [opaque TySet child])) term (Elaboration.LocatedSourceTerm location))
            _ -> invalid "a recursive branch result lost its declared call"
    instance' <- instantiateSource typing context location written actuals description
    (body,evidence) <- case instance' of
        Template.InstantiatedProposition{} -> sealProposition typing context location instance'
        Template.InstantiatedTerm term -> do
            checked <- expansionCoreWork (\work -> countedCheckScopedCanonicalCore typing work context
                (Source.sourceTermOccurrenceCore term))
            pure (checked,SourceInputs Nothing [SourceInput [] (Source.sourceSupportTemplate id term)])
    pure (body,withSourceInputs [SourceInput [] (Source.sourceSupportTemplate id term) | term <- written] evidence)
  where
    require :: Maybe value -> Work value
    require = maybe (invalid "an admitted recursive branch lost its source layout") pure

resolveProviders :: AbbreviationExpansion -> Work (Map SourceProviderHead ObjectId)
resolveProviders description = do
    heads <- Template.sourceTemplateProviders description
    entries <- for (Set.toAscList heads) \provider -> do
        chargeExpansion 1
        case provider of
            GlobalSourceProvider reference -> do
                resolved <- lift (lift (Declaration.resolveVisibleGlobalLowering (globalBindingRefKey reference)))
                case resolved of
                    Just (binding,_)
                        | resolvedBindingRef binding == reference
                        , resolvedBindingSourceProviderHead binding == Just provider
                        , GlobalReference object <- semanticGlobalBindingTarget (resolvedBindingDeclaration binding) ->
                            pure (Just (provider,object))
                    _ -> invalid "a recursive source template lost its admitted provider"
            StructureFieldSourceProvider field projection -> do
                actual <- lift (lift (Declaration.resolveVisibleStructureFieldProviderLowering field))
                unless (actual == Just projection) (invalid "a recursive source field changed identity")
                pure (Just (provider,projection))
            _ -> pure Nothing
    chargeExpansion (fromIntegral (length entries))
    pure (Map.fromList (catMaybes entries))

invalid :: Text -> Work value
invalid = Except.throwE . ExpansionInvalid
