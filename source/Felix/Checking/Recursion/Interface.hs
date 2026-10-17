{-# LANGUAGE NoImplicitPrelude #-}

-- | Admission of binding-owned constructor equations. A transparent body's
-- identity does not own its source headers; the resolved binding does.
module Felix.Checking.Recursion.Interface
    ( CheckedRecursiveDefinition
    , recursiveBinding, recursiveObject, recursiveResultType, recursiveParameterCount
    , recursiveDescriptor, recursiveClauses, recursiveEquationTargets, recursiveSources, recursiveGuardSources
    , checkRecursiveDefinition
    , recursiveFormationContract
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.GlobalTyping (lookupGlobalType)
import Felix.Checking.Identity
import Felix.Checking.Notion.SourceEvidence qualified as Source
import Felix.Checking.Recursion.Construction qualified as Construction
import Felix.Checking.Semantic

import Control.Monad (unless)
import Data.Bifunctor (first)
import Data.Functor.Identity (runIdentity)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import Data.Vector qualified as Vector

type Term = CanonicalTerm ObjectId

data CheckedRecursiveDefinition = CheckedRecursiveDefinition
    { recursiveBinding :: !GlobalBindingRef
    , recursiveObject :: !ObjectId
    , recursiveResultType :: !CoreType
    , recursiveParameterCount :: !Int
    , recursiveDescriptor :: !(RecursiveDefinitionDescriptor SemanticFactOccurrenceFingerprint)
    , recursiveClauses :: !(NonEmpty Datatype.Clause)
    , recursiveEquationTargets :: !(NonEmpty (FrozenCheckedCore ObjectId))
    , recursiveSources :: !(NonEmpty ([CoreType], Term, AbbreviationExpansion))
    , recursiveGuardSources :: !(NonEmpty ([CoreType], Term, AbbreviationExpansion))
    }

-- The fact resolver supplies only this declaration's checked facts. Its
-- binding resolver includes the previously admitted datatype declaration.
checkRecursiveDefinition
    :: CheckedObjectClosure
    -> (GlobalBindingRef -> Maybe SemanticGlobalBinding)
    -> (SemanticFactOccurrenceFingerprint -> Maybe (FrozenCheckedCore ObjectId))
    -> GlobalBindingRef -> SemanticGlobalBinding
    -> RecursiveDefinitionDescriptor SemanticFactOccurrenceFingerprint
    -> Either Text CheckedRecursiveDefinition
checkRecursiveDefinition closure resolveBinding resolveFact owner binding descriptor = do
    object <- reference binding
    (objectType,body) <- case lookupCheckedObjectContent object closure of
        Just (TransparentObjectContent _ ty body) -> pure (ty,body)
        _ -> Left "a recursive definition must own a transparent body"
    (arity,resultType) <- maybe (Left "a recursive definition has an unsupported type") pure
        (firstOrderSymbolShape objectType)
    unless (arity > 0 && (resultType == TySet || resultType == TyProp))
        (Left "a recursive definition needs a structural Set argument")
    let parameterCount = arity - 1
        types = replicate parameterCount TySet
        arguments = recursiveDefinitionArguments descriptor
        parameters = CBound <$> arguments
        headers = recursiveDefinitionHeaders descriptor
        conditions = residualTemplateFormula <$> headers
    datatypeBinding <- maybe (Left "recursive datatype binding is not visible") pure
        (resolveBinding (recursiveDefinitionDatatype descriptor))
    datatype <- maybe (Left "recursive structural domain is not a checked datatype") pure
        (semanticGlobalBindingDatatype datatypeBinding)
    carrierObject <- reference datatypeBinding
    (datatypeArity,datatypeResult) <- maybe (Left "recursive datatype has an unsupported type") pure
        (lookupGlobalType typing carrierObject >>= firstOrderSymbolShape)
    unless (datatypeResult == TySet && length arguments == datatypeArity
        && all (< fromIntegral parameterCount) arguments)
        (Left "recursive datatype arguments do not name fixed parameters")
    traverse_ (checkTerm types TyProp) conditions
    contract <- recursiveFormationContract parameterCount descriptor
    unless (semanticGlobalBindingContract binding == Just contract)
        (Left "recursive headers disagree with the binding's formation contract")
    evaluator <- stripParameters parameterCount body
    unguarded <- if resultType == TyProp && not (null conditions)
        then case evaluator of
            CLam TySet (CAnd condition (CApp shifted (CBound 0)))
                | condition == shift (conjunction conditions) -> do
                    let candidate = instantiateCanonical (CIntrinsic Empty) shifted
                    unless (shift candidate == shifted)
                        (Left "recursive header body captures its structural argument")
                    pure candidate
            _ -> Left "predicate headers are not conjuncts of the recursive body"
        else pure evaluator
    let (headTerm,supplied) = applicationSpine unguarded
        descriptions = datatypeDescriptorCases datatype
        branchTerms = drop datatypeArity supplied
    recursor <- case headTerm of
        CGlobal identity -> pure identity
        _ -> Left "recursive body is not a recursor application"
    unless (take datatypeArity supplied == parameters
        && length supplied == datatypeArity + NonEmpty.length descriptions)
        (Left "recursive body has incompatible datatype arguments or branches")
    clauses <- for descriptions \description -> do
        constructorBinding <- maybe (Left "recursive constructor binding is not visible") pure
            (resolveBinding (globalBindingRef (globalBindingRefOwner (recursiveDefinitionDatatype descriptor))
                (datatypeCaseConstructor description)))
        constructor <- reference constructorBinding
        premises <- for (datatypeCasePremises description) \case
            DatatypeRecursivePremise -> pure Datatype.Recursive
            DatatypeFixedPremise term -> do
                specialized <- instantiateCanonicalPrefixWith (pure ()) (fromIntegral datatypeArity)
                    (\depth slot -> maybe (Left "datatype premise has an invalid parameter")
                        (pure . shiftCanonical depth 0 . CBound) (nth slot (reverse arguments))) 0 term
                checked <- first (Text.pack . show) (checkScopedCanonicalCore typing types specialized)
                pure (Datatype.FixedDomain checked)
        pure (Datatype.Clause constructor (datatypeCaseFields description) premises)
    let branchTypes = Construction.branchTypeFor resultType <$> toList clauses
        recursorType = foldr TyArrow (TyArrow TySet resultType) (replicate datatypeArity TySet <> branchTypes)
    unless (lookupGlobalType typing recursor == Just recursorType)
        (Left "recursive body uses an incompatible recursor")
    sequence_ (zipWith (checkTerm types) branchTypes branchTerms)
    unless ((fst <$> recursiveDefinitionEquations descriptor) == (datatypeCaseConstructor <$> descriptions))
        (Left "recursive equations do not cover the datatype constructors in order")
    let carrier = foldl' CApp (CGlobal carrierObject) parameters
        named = foldl' CApp (CGlobal object) (CBound . fromIntegral <$> reverse [0 .. parameterCount - 1])
    branches <- maybe (Left "recursive body has no branches") pure (NonEmpty.nonEmpty branchTerms)
    unless (NonEmpty.length branches == NonEmpty.length (recursiveDefinitionBranches descriptor))
        (Left "recursive branch descriptions do not cover the constructors")
    sources <- for (NonEmpty.zip branches (recursiveDefinitionBranches descriptor)) \(branch,description) -> do
        let (binders,value) = openBranch branch
        pure (reverse binders <> types,value,description)
    equations <- for (NonEmpty.zip (NonEmpty.zip clauses branches) (recursiveDefinitionEquations descriptor)) \((clause,branch),(_,fingerprint)) -> do
        target <- maybe (Left "recursive equation is not owned by its declaration") pure (resolveFact fingerprint)
        let fieldCount = length (Datatype.clausePremises clause)
            liftTerm = shiftCanonical (fromIntegral fieldCount) 0
            fields = CBound . fromIntegral <$> reverse [0 .. fieldCount - 1]
            guards = (liftTerm <$> conditions)
                <> Datatype.premiseTerms (parameterCount + fieldCount) (liftTerm carrier) clause fields
        constructor <- first (Text.pack . show) (Datatype.constructorTerm clause fields)
        value <- first (Text.pack . show) (Construction.branchValue clause (liftTerm branch) (liftTerm named) fields)
        let equality = CEq resultType (CApp (liftTerm named) constructor) value
            guarded = if null guards then equality else CImp (conjunction guards) equality
            expected = foldr CForall guarded (types <> replicate fieldCount TySet)
        unless (frozenCoreTerm target == expected)
            (Left "recursive equation disagrees with its transparent body or guards")
        description <- guardDescription parameterCount descriptor clause
        pure (target,(replicate fieldCount TySet <> types,conjunction guards,description))
    let targets = fst <$> equations
        guardSources = snd <$> equations
    pure (CheckedRecursiveDefinition owner object resultType parameterCount descriptor clauses targets sources guardSources)
  where
    typing = globalTypingFromClosure closure
    reference source = case semanticGlobalBindingTarget source of
        GlobalReference object -> pure object
        _ -> Left "recursive declarations require ordinary source bindings"
    checkTerm types expected term = do
        checked <- first (Text.pack . show) (checkScopedCanonicalCore typing types term)
        unless (scopedCoreType checked == expected) (Left "recursive source term has an incompatible type")
    stripParameters 0 term = pure term
    stripParameters count (CLam TySet body) = stripParameters (count - 1) body
    stripParameters _ _ = Left "recursive body does not bind its fixed parameters"
    openBranch (CLam ty body) = let (types,term) = openBranch body in (ty:types,term)
    openBranch term = ([],term)
    applicationSpine = go []
      where
        go arguments (CApp function argument) = go (argument:arguments) function
        go arguments function = (function,arguments)

-- Compile the portable header descriptions into the same source-template
-- language used by branch substitution. Domain ownership comes from the
-- admitted datatype; a fixed domain without a description remains opaque.
guardDescription
    :: Int -> RecursiveDefinitionDescriptor fact -> Datatype.Clause
    -> Either Text AbbreviationExpansion
guardDescription parameterCount descriptor clause = do
    headers <- traverse describeHeader (recursiveDefinitionHeaders descriptor)
    let domains = [Source.SourceAtom (MembershipAtomTemplate
            (ExpansionFormal (fromIntegral (parameterCount + index))) (domain premise))
            | (index,premise) <- zip [0..] (Datatype.clausePremises clause)]
        evidence = case headers <> domains of
            [] -> Source.SourceResidual Nothing
            initial:rest -> foldl' Source.SourceAnd initial rest
    pure (PropositionExpansion evidence [])
  where
    fieldCount = fromIntegral (length (Datatype.clausePremises clause))
    domain Datatype.Recursive = ExpansionProvider (GlobalSourceProvider (recursiveDefinitionDatatype descriptor))
        (Vector.fromList [ExpansionFormal (fromIntegral parameterCount - index - 1)
            | index <- recursiveDefinitionArguments descriptor])
    domain (Datatype.FixedDomain value) = ExpansionOpaque (shiftCanonical fieldCount 0 (scopedCoreTerm value))
    describeHeader header = case residualTemplateEvidence header of
        Nothing -> pure (Source.SourceResidual Nothing)
        Just evidence -> Source.traverseSourceAtDepth
            (\depth -> describeTerm (pure . ExpansionOpaque . shiftCanonical fieldCount depth))
            (\depth -> traverse (describeTerm (formal depth))) evidence
    formal depth (ViewVariableIx index)
        | index < depth = pure (ExpansionLocal index)
        | index - depth < fromIntegral parameterCount =
            pure (ExpansionFormal (fromIntegral parameterCount - (index - depth) - 1))
        | otherwise = Left "a recursive header source variable escapes its parameters"
    describeTerm variable = \case
        TemplateVariable value -> variable value
        TemplateClosed value -> pure (ExpansionOpaque (closedSetValueTerm value))
        TemplateProvider provider children -> ExpansionProvider provider <$> traverse (describeTerm variable) children
        TemplateOrderedPair left right -> ExpansionPair <$> describeTerm variable left <*> describeTerm variable right

recursiveFormationContract :: Int -> RecursiveDefinitionDescriptor fact -> Either Text FormationContract
recursiveFormationContract parameterCount descriptor = do
    unless (parameterCount >= 0 && all (< fromIntegral parameterCount) (recursiveDefinitionArguments descriptor))
        (Left "recursive formation contract has an invalid parameter")
    pure (formationContract (domain :| headers))
  where
    domain = AtomicLeaf (MembershipAtomTemplate (TemplateVariable (OccurrenceArgumentIx (fromIntegral parameterCount)))
        (TemplateProvider (GlobalSourceProvider (recursiveDefinitionDatatype descriptor))
            (Vector.fromList [TemplateVariable (OccurrenceArgumentIx (fromIntegral parameterCount - index - 1))
                | index <- recursiveDefinitionArguments descriptor])))
    headers = WholeLeaf . WholeResidual . shiftHeader <$> recursiveDefinitionHeaders descriptor
    shiftHeader header = case residualTemplateEvidence header of
        Nothing -> ResidualTemplate (shift (residualTemplateFormula header))
        Just evidence -> describedResidualTemplate (shift (residualTemplateFormula header))
            (runIdentity (Source.traverseSourceAtDepth
                (\depth -> pure . fmap (shiftCanonical 1 depth))
                (\depth -> pure . fmap (fmap (\(ViewVariableIx index) ->
                    ViewVariableIx (if index < depth then index else index + 1)))) evidence))

shift :: Term -> Term
shift = shiftCanonical 1 0

conjunction :: [Term] -> Term
conjunction [] = CTruth
conjunction (firstTerm:rest) = foldl' CAnd firstTerm rest
