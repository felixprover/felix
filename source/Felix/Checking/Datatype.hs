{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}

-- | Conservative datatype definitions and proof-producing declaration lowering.
-- Representation equations use the ordinary checked definition boundary; every
-- generated law is independently replayed by the declaration owner.
module Felix.Checking.Datatype
    ( PreparedDatatype
    , preparedDatatypeObjects
    , preparedDatatypeBindings
    , PreparedDatatypeFact
    , preparedDatatypeFacts
    , preparedDatatypeFactMarker
    , preparedDatatypeFactTarget
    , preparedDatatypeFactReference
    , prepareDatatype
    , CheckedDatatypeAuthorization
    , lowerPreparedDatatype
    , authorizeCheckedDatatype
    , DatatypeError(..)
    , datatypeErrorLocation
    , renderDatatypeError
    ) where

import Base hiding (Empty)
import Felix.Checking.Authority
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Construction
import Felix.Checking.Foundation (CheckedFoundation)
import Felix.Checking.Kernel.Derivation qualified as Kernel
import Felix.Checking.Kernel.Proof qualified as Proof
import Felix.Checking.Planning
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Elaboration.Vocabulary
import Felix.Checking.Identity
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.RuleTerm qualified as RuleTerm
import Felix.Checking.Semantic
import Felix.Cache.Codec
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface

import Control.Monad (foldM, unless, when)
import Control.Monad.Except (ExceptT)
import Control.Monad.Except qualified as Except
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor qualified as Bifunctor
import Data.ByteString (ByteString)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.List qualified as List
import Effectful.Error.Static qualified as Error
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector


data PreparedDatatypeObject = PreparedDatatypeObject
    !Raw.FunctionSymbol
    !SemanticGlobalKey
    !CoreType
    !ObjectId
    !AssertedObject

data PreparedDatatypeFact = PreparedDatatypeFact
    !Raw.Marker
    !(FrozenCheckedCore ObjectId)
    !TheoremRef

preparedDatatypeFactMarker
    :: PreparedDatatypeFact
    -> Raw.Marker
preparedDatatypeFactMarker
        (PreparedDatatypeFact marker _target _reference) =
    marker

preparedDatatypeFactTarget
    :: PreparedDatatypeFact
    -> FrozenCheckedCore ObjectId
preparedDatatypeFactTarget
        (PreparedDatatypeFact _marker target _reference) =
    target

preparedDatatypeFactReference
    :: PreparedDatatypeFact
    -> TheoremRef
preparedDatatypeFactReference
        (PreparedDatatypeFact _marker _target reference) =
    reference

data DatatypeEvidence
    = ImplementationEquation !ObjectId
    | DerivedFact ![PlannedFactReference] !(Kernel.KernelDerivation ObjectId)

data PreparedCandidate = PreparedCandidate
    !(FrozenCheckedCore ObjectId)
    !(Maybe Raw.Marker)
    !DatatypeEvidence

data PreparedDatatype = PreparedDatatype
    !Location
    !DeclarationSyntaxId
    !TheoryId
    !(NonEmpty PreparedDatatypeObject)
    ![AssertedObject]
    !(NonEmpty (NonEmpty PreparedCandidate))
    ![Registration PlannedCandidatePosition]
    !(DatatypeDescriptor PlannedCandidatePosition)

newtype CheckedDatatypeAuthorization = CheckedDatatypeAuthorization
    [NonEmpty DatatypeEvidence]

preparedDatatypeObjects :: PreparedDatatype -> NonEmpty (ObjectId, CoreType)
preparedDatatypeObjects (PreparedDatatype _ _ _ objects _ _ _ _) = fmap
    (\(PreparedDatatypeObject _ _ coreType identity _) -> (identity, coreType)) objects

preparedDatatypeBindings :: PreparedDatatype -> NonEmpty (SemanticGlobalKey, SemanticGlobalTarget)
preparedDatatypeBindings (PreparedDatatype _ _ _ objects _ _ _ _) = fmap
    (\(PreparedDatatypeObject _ key _ identity _) -> (key, GlobalReference identity)) objects

preparedDatatypeFacts :: PreparedDatatype -> NonEmpty PreparedDatatypeFact
preparedDatatypeFacts (PreparedDatatype _ _ theory _ _ stages _ _) =
    fromMaybe (impossible "a datatype has no public facts") . NonEmpty.nonEmpty $
        [ PreparedDatatypeFact marker target (theoremRef theory (propositionIdOf (frozenCoreTerm target)))
        | stage <- toList stages
        , PreparedCandidate target (Just marker) _ <- toList stage
        ]

lowerPreparedDatatype
    :: PreparedDatatype
    -> Declaration.LoweringDriver
        (Either Declaration.DeclarationError
            (Declaration.CheckedDeclaration CheckedDatatypeAuthorization))
lowerPreparedDatatype (PreparedDatatype _ syntax _ objects assertions stages registrations descriptor) = do
    candidates <- traverse (traverse lower) stages
    pure do
        checked <- traverse sequenceA candidates
        let PreparedDatatypeObject _ carrierKey _ _ _ = NonEmpty.head objects
        pure (Declaration.withDatatypeDescriptor carrierKey descriptor
            (Declaration.checkedCompiledDeclarationWithRegistrations syntax assertions [] bindings Nothing registrations
                (toList checked) (CheckedDatatypeAuthorization (toList (fmap (fmap evidenceOf) stages)))))
  where
    bindings = [semanticGlobalBinding key (bindingLabelFromFunctionSymbol symbol) (GlobalReference identity)
        | PreparedDatatypeObject symbol key _ identity _ <- toList objects]
    evidenceOf (PreparedCandidate _ _ evidence) = evidence
    lower (PreparedCandidate target marker evidence) = do
        spec <- Declaration.prepareFrozenCandidateSpecLowering assertions target
            (maybe SearchIneligible (const SearchEligible) marker)
            [semanticName name | Raw.Marker name <- maybeToList marker]
        let planning = case evidence of
                ImplementationEquation identity -> Declaration.checkedImplementationDefinitionPlanning identity
                DerivedFact references _ -> Declaration.checkedKernelPlanningReferences CheckedDerivedConstruction references
        pure (fmap (\candidate -> Declaration.checkedCandidate candidate planning) spec)

authorizeCheckedDatatype
    :: CheckedDatatypeAuthorization
    -> [NonEmpty Declaration.ReservedCandidate]
    -> Declaration.Declaration ()
authorizeCheckedDatatype (CheckedDatatypeAuthorization evidence) stages = do
    unless (length evidence == length stages
        && and (zipWith (\a b -> NonEmpty.length a == NonEmpty.length b) evidence stages))
        (Declaration.failDeclaration (Declaration.CheckedAuthorizationCandidateShapeMismatch (length evidence) (length stages)))
    traverse_ (traverse_ (uncurry authorize) . uncurry NonEmpty.zip) (zip evidence stages)
  where
    authorize (ImplementationEquation identity) candidate =
        Declaration.authorizeImplementationDefinitionCandidate identity candidate
    authorize (DerivedFact references derivation) candidate =
        Declaration.authorizeKernelConstructionCandidate CheckedDerivedConstruction candidate do
            actual <- traverse consume references
            maybe (Error.throwError_ Declaration.KernelConstructionDescriptorMismatch) pure
                (Kernel.remapKernelDerivationImports
                    (\index -> nth (Kernel.importIxValue index) actual) derivation)
    consume = \case
        EnvironmentOccurrenceReference fingerprint -> Declaration.useAuthorizedFact fingerprint
        LocalCandidateReference position -> case Declaration.candidateAtPosition position stages of
            Just candidate -> Declaration.useStagedCandidate candidate
            Nothing -> Error.throwError_ Declaration.KernelConstructionDescriptorMismatch


data DatatypeError
    = DatatypeUnsupportedBlock !Location
    | DatatypeOccurrenceCountMismatch !Location !Int !Int
    | DatatypeOccurrenceMismatch !Location
    | DatatypeInvalid !Location !Text
    | DatatypeDuplicateGlobal !Location !SemanticGlobalKey
    | DatatypeFixedSemanticCollision !Location !SemanticGlobalKey
    | DatatypeGlobalAlreadyVisible !Location !SemanticGlobalKey
    | DatatypeElaborationFailed !Elaboration.ElaborationError
    | DatatypeExpectedSet !Location !CoreType
    | DatatypeExpectedProposition !Location !CoreType
    deriving stock (Show, Eq)

datatypeErrorLocation :: DatatypeError -> Location
datatypeErrorLocation = \case
    DatatypeUnsupportedBlock location -> location
    DatatypeOccurrenceCountMismatch location _expected _actual -> location
    DatatypeOccurrenceMismatch location -> location
    DatatypeInvalid location _message -> location
    DatatypeDuplicateGlobal location _key -> location
    DatatypeFixedSemanticCollision location _key -> location
    DatatypeGlobalAlreadyVisible location _key -> location
    DatatypeElaborationFailed failure ->
        Elaboration.elaborationErrorLocation failure
    DatatypeExpectedSet location _actual -> location
    DatatypeExpectedProposition location _actual -> location

renderDatatypeError :: DatatypeError -> Text
renderDatatypeError failure =
    locationToText (datatypeErrorLocation failure)
        <> ": "
        <> case failure of
            DatatypeUnsupportedBlock{} ->
                "this datatype source form is not supported by the typed checker"
            DatatypeOccurrenceCountMismatch _location expected actual ->
                "the datatype has " <> shown actual
                    <> " syntax occurrences, but " <> shown expected
                    <> " are required"
            DatatypeOccurrenceMismatch{} ->
                "a datatype syntax occurrence does not match its declaration"
            DatatypeInvalid _location message ->
                "invalid datatype declaration: " <> message
            DatatypeDuplicateGlobal _location key ->
                "the datatype declares the semantic key more than once: "
                    <> shown key
            DatatypeFixedSemanticCollision _location key ->
                "the datatype collides with fixed semantics for " <> shown key
            DatatypeGlobalAlreadyVisible _location key ->
                "the datatype global is already visible: " <> shown key
            DatatypeElaborationFailed elaborationFailure ->
                "datatype expression elaboration failed: "
                    <> Elaboration.renderElaborationError elaborationFailure
            DatatypeExpectedSet _location actual ->
                "a datatype premise domain has type " <> shown actual
                    <> " instead of Set"
            DatatypeExpectedProposition _location actual ->
                "a generated datatype fact has type " <> shown actual
                    <> " instead of Prop"
  where
    shown :: Show value => value -> Text
    shown = Text.pack . show

type Prepare =
    ExceptT DatatypeError Declaration.LoweringDriver

type SourceOccurrence = (Location, Raw.Marker, CanonicalLexicalEntry)

data ValidatedDatatype = ValidatedDatatype
    !Raw.FunctionSymbol
    ![Raw.VarSymbol]
    !(NonEmpty ValidatedDatatypeClause)

data ValidatedDatatypeClause = ValidatedDatatypeClause
    !Raw.FunctionSymbol
    ![Raw.VarSymbol]
    ![ValidatedDatatypePremise]
    !Text

data ValidatedDatatypePremise
    = ValidatedRecursivePremise !Raw.VarSymbol !Location
    | ValidatedNonRecursivePremise !Raw.VarSymbol !Raw.Expr

data PreparedClause = PreparedClause
    !Raw.FunctionSymbol
    !ObjectId
    ![Raw.VarSymbol]
    ![PreparedPremise]
    !Text

data PreparedPremise
    = PreparedRecursivePremise !Raw.VarSymbol
    | PreparedNonRecursivePremise
        !Raw.VarSymbol
        !(ScopedCheckedCore ObjectId)

prepareDatatype
    :: Raw.Block
    -> [SourceOccurrence]
    -> Declaration.LoweringDriver
        (Either DatatypeError PreparedDatatype)
prepareDatatype block occurrences = Except.runExceptT do
    (location, marker, rawDatatype) <- case block of
        Raw.BlockData blockLocation _title blockMarker datatype -> pure (blockLocation, blockMarker, datatype)
        _ -> Except.throwError (DatatypeUnsupportedBlock (locate block))
    keys <- validateOccurrences location marker rawDatatype occurrences
    ValidatedDatatype headSymbol parameters clauses <- Except.liftEither (validateDatatype location rawDatatype)
    unless (NonEmpty.length keys == 1 + NonEmpty.length clauses)
        (Except.throwError (DatatypeOccurrenceCountMismatch location (1 + NonEmpty.length clauses) (NonEmpty.length keys)))
    validateKeys occurrences keys
    theory <- Trans.lift Declaration.currentTheoryLowering
    owner <- Trans.lift Declaration.nextDeclarationSlotLowering
    foundation <- Trans.lift Declaration.currentFoundationLowering
    initial <- Trans.lift Declaration.checkedObjectClosureLowering
    let carrierKey = NonEmpty.head keys
        constructorKeys = case NonEmpty.nonEmpty (NonEmpty.tail keys) of
            Just nonempty -> nonempty
            Nothing -> impossible "a validated datatype has no constructor keys"
        count = fromIntegral (NonEmpty.length clauses)
        kType = TyArrow TySet (TyArrow TySet TySet)
        kObject = transparentObject theory kType Construction.kuratowskiBody
        k = assertedObjectId kObject
        constructors = NonEmpty.zipWith
            (\index (key, ValidatedDatatypeClause symbol arguments _ _) ->
                prepareObject theory symbol key (length arguments)
                    (Construction.constructorBody k count index (length arguments)))
            (0 :| [1 ..]) (NonEmpty.zip constructorKeys clauses)
        descriptions = kObject : [asserted | PreparedDatatypeObject _ _ _ _ asserted <- toList constructors]
    (constructorClosure, newConstructors) <- Except.liftEither (addObjects location initial descriptions)
    environment <- Except.liftEither (Bifunctor.first DatatypeElaborationFailed
        (Elaboration.datatypeElaborationEnvironment constructorClosure
            (fmap (\(PreparedDatatypeObject symbol _ _ _ object) -> (location, symbol, object)) constructors) parameters))
    let bySymbol = Map.fromList [(symbol,identity) | PreparedDatatypeObject symbol _ _ identity _ <- toList constructors]
    sourceClauses <- traverse (prepareClause carrierKey environment bySymbol) clauses
    let checkedClauses = constructionClause <$> sourceClauses
    (_, _, body) <- Except.liftEither (constructionResult location "carrier term" (Construction.carrierTerms (length parameters) checkedClauses))
    let carrierObject = prepareObject theory headSymbol carrierKey (length parameters)
            (foldr (const (CLam TySet)) body parameters)
        PreparedDatatypeObject _ _ _ carrier carrierAssertion = carrierObject
    (closure, newCarrier) <- Except.liftEither (addObjects location constructorClosure [carrierAssertion])
    let objects = carrierObject :| toList constructors
        assertions = newConstructors <> newCarrier
        definitions = descriptions <> [carrierAssertion]
    stages <- Except.liftEither (prepareStages location foundation closure headSymbol (length parameters) k carrier sourceClauses checkedClauses definitions)
    case firstDuplicate [name | stage <- toList stages, PreparedCandidate _ (Just name) _ <- toList stage] of
        Just (Raw.Marker name) -> Except.throwError (DatatypeInvalid location ("generated datatype aliases collide: " <> name))
        Nothing -> pure ()
    let publicPositions = Map.fromList
            [(name, PlannedCandidatePosition stage index)
            | (stage, candidates) <- zip [0 ..] (toList stages)
            , (index, PreparedCandidate _ (Just name) _) <- zip [0 ..] (toList candidates)]
        law suffix = fromMaybe (impossible "a datatype description lost its public law")
            (Map.lookup (Raw.Marker (functionSymbolText headSymbol <> "_" <> suffix)) publicPositions)
        namedClauses = NonEmpty.zip constructorKeys (NonEmpty.zip sourceClauses checkedClauses)
        caseDescription index (key, (PreparedClause _ _ _ _ name, clause)) = DatatypeCase
            (Text.toLower name) key
            [case premise of
                Construction.Recursive -> DatatypeRecursivePremise
                Construction.FixedDomain domain -> DatatypeFixedPremise (scopedCoreTerm domain)
            | premise <- Construction.clausePremises clause]
            (Construction.clauseArgumentSlots clause)
            (law (name <> "_intro"))
            (if null (Construction.clauseArgumentSlots clause) then Nothing else Just (law (name <> "_injective")))
            [(laterKey, law (name <> "_" <> laterName <> "_distinct"))
            | (laterKey, (PreparedClause _ _ _ _ laterName, _)) <- drop (index + 1) (toList namedClauses)]
        descriptor = DatatypeDescriptor
            (NonEmpty.zipWith caseDescription (0 :| [1 ..]) namedClauses)
            (law "cases") (law "induct") (law "predicate_induct")
        syntax = declarationSyntaxId (encodeCache (putSourceProviderHeadCache
            (GlobalSourceProvider (globalBindingRef owner carrierKey)))
            <> encodePreparedDatatype objects checkedClauses stages descriptor)
        registrations = constructorRegistrations owner (length parameters) carrierKey constructorKeys checkedClauses
    pure (PreparedDatatype location syntax theory objects assertions stages registrations descriptor)

-- Provider arguments are bare stored fields, and the requested carrier has
-- bare parameters. Thus an admissible fixed-domain guard must itself be a
-- parameter. Richer domains and unstored witnesses keep their explicit laws.
constructorRegistrations
    :: DeclarationSlot -> Int -> SemanticGlobalKey -> NonEmpty SemanticGlobalKey
    -> NonEmpty Construction.Clause -> [Registration PlannedCandidatePosition]
constructorRegistrations owner parameterCount carrierKey constructorKeys clauses =
    [ registration
    | (index, (key, clause)) <- zip [0 ..] (toList (NonEmpty.zip constructorKeys clauses))
    , Just registration <- [prepare index key clause]
    ]
  where
    provider key = GlobalSourceProvider (globalBindingRef owner key)
    variable = TemplateVariable . ViewVariableIx . fromIntegral
    prepare index key clause = do
        let count = length (Construction.clausePremises clause)
            carrier = TemplateProvider (provider carrierKey)
                (Vector.fromList (variable . (+ count) <$> reverse [0 .. parameterCount - 1]))
            constructor = resultProviderTemplate (provider key)
                (Vector.fromList [variable (count - 1 - fromIntegral slot) | slot <- Construction.clauseArgumentSlots clause])
            conclusion = MembershipAtomTemplate ResultRuleProviderValue (ResultRuleTerm carrier)
        guards <- for (zip [0 ..] (Construction.clausePremises clause)) \(slot, premise) -> do
            domain <- case premise of
                Construction.Recursive -> Just carrier
                Construction.FixedDomain checked -> case scopedCoreTerm checked of
                    CBound parameter -> Just (variable (count + fromIntegral parameter))
                    _ -> Nothing
            pure (RulePremiseAtom (MembershipAtomTemplate (variable (count - 1 - slot)) domain))
        let premises = case guards of
                [] -> ProviderResultUnconditional
                first : rest -> ProviderResultGuarded (RulePremiseBundles (foldl' RulePremiseAnd first rest :| []))
            scope = RuleTerm.providerResultPremiseScope constructor conclusion
            expected = Set.fromList (ViewVariableIx . fromIntegral <$> [0 .. parameterCount + count - 1])
        guard (RuleTerm.providerResultDeterminingVariables scope == expected)
        either (const Nothing) Just (RuleTerm.validateProviderResultPremises scope premises)
        pure (Registration (PlannedCandidatePosition 6 index) Notion.ConjunctionHere
            (RegisterProviderResult (ProviderResultRule constructor premises conclusion)))

addObjects :: Location -> CheckedObjectClosure -> [AssertedObject] -> Either DatatypeError (CheckedObjectClosure, [AssertedObject])
addObjects location initial objects = do
    (closure, reversed) <- foldM insert (initial, []) objects
    pure (closure, reverse reversed)
  where
    insert current@(closure, added) object
        | lookupCheckedObjectContent (assertedObjectId object) closure == Just (assertedObjectContent object) = pure current
        | otherwise = do
            extended <- Bifunctor.first (DatatypeInvalid location . Text.pack . show) (extendObjectClosure closure [object])
            pure (extended, object : added)

constructionResult :: Show err => Location -> Text -> Either err value -> Either DatatypeError value
constructionResult location description = Bifunctor.first
    (DatatypeInvalid location . ((description <> ": ") <>) . Text.pack . show)

constructionClause :: PreparedClause -> Construction.Clause
constructionClause (PreparedClause _ identity arguments premises _) = Construction.Clause identity slots domains
  where
    variables = Map.fromList (zip (preparedPremiseVariable <$> premises) [0 ..])
    slots = [fromMaybe (impossible "validated constructor argument has no premise") (Map.lookup argument variables) | argument <- arguments]
    domains = [case premise of
        PreparedRecursivePremise _ -> Construction.Recursive
        PreparedNonRecursivePremise _ domain -> Construction.FixedDomain domain | premise <- premises]


validateDatatype
    :: Location
    -> Raw.Datatype
    -> Either DatatypeError ValidatedDatatype
validateDatatype declarationLocation datatype = do
    (headSymbol, parameters) <- symbolicVariables "head" (Raw.datatypeHeadExpr datatype)
    unless (headSymbol /= Raw.ApplySymbol)
        (Left (DatatypeInvalid declarationLocation "datatype head must be a symbolic pattern"))
    case firstDuplicate parameters of
        Just variable -> Left (DatatypeInvalid (locate variable) "datatype parameters must be distinct")
        Nothing -> pure ()
    clauses <- traverse (validateClause headSymbol parameters) (Raw.datatypeClauses datatype)
    let constructors =
            [ constructor
            | ValidatedDatatypeClause constructor _arguments _premises _name <-
                toList clauses
            ]
    case firstDuplicate constructors of
        Just duplicate ->
            Left
                (DatatypeInvalid declarationLocation
                    ("datatype constructor patterns must be distinct: "
                        <> functionSymbolText duplicate))
        Nothing -> pure ()
    case firstDuplicate [Text.toLower name | ValidatedDatatypeClause _ _ _ name <- toList clauses] of
        Just duplicate -> Left (DatatypeInvalid declarationLocation ("datatype case names must be distinct: " <> duplicate))
        Nothing -> pure (ValidatedDatatype headSymbol parameters clauses)
  where
    validateClause headSymbol parameters clause = do
        unless (directDatatypeCarrier headSymbol parameters (Raw.datatypeClauseTargetExpr clause))
            (Left (DatatypeInvalid (locate (Raw.datatypeClauseTargetExpr clause))
                "every datatype clause must target the head with its parameters unchanged"))
        (constructor, arguments) <-
            datatypeConstructor (Raw.datatypeClauseConstructorExpr clause)
        unless (constructor /= Raw.ApplySymbol)
            (Left
                (DatatypeInvalid
                    (locate (Raw.datatypeClauseConstructorExpr clause))
                    "datatype constructor cannot be function application"))
        unless (constructor /= headSymbol)
            (Left
                (DatatypeInvalid
                    (locate (Raw.datatypeClauseConstructorExpr clause))
                    "datatype constructor cannot reuse the datatype symbol"))
        case firstDuplicate arguments of
            Just duplicate ->
                Left
                    (DatatypeInvalid
                        (locate duplicate)
                        "datatype constructor arguments must be linear")
            Nothing -> pure ()
        let rawPremises = Raw.datatypeClausePremises clause
            premiseVariables = fst <$> rawPremises
        case firstDuplicate premiseVariables of
            Just duplicate ->
                Left
                    (DatatypeInvalid
                        (locate duplicate)
                        "datatype premise variables must be linear")
            Nothing -> pure ()
        case List.find (`elem` parameters) premiseVariables of
            Just variable -> Left (DatatypeInvalid (locate variable) "datatype premise binders cannot shadow parameters")
            Nothing -> pure ()
        let missing =
                Set.fromList arguments
                    `Set.difference` Set.fromList premiseVariables
        unless (Set.null missing)
            (Left
                (DatatypeInvalid
                    (locate (Raw.datatypeClauseConstructorExpr clause))
                    "every datatype constructor argument requires a premise"))
        premises <- traverse (validatePremise headSymbol parameters) rawPremises
        name <- case Raw.datatypeClauseName clause of
            Nothing -> pure (functionSymbolText constructor)
            Just spelling -> maybe
                (Left (DatatypeInvalid (locate (Raw.datatypeClauseConstructorExpr clause))
                    "datatype case names must start with an ASCII letter and contain only ASCII letters, digits, underscores, or whitespace"))
                pure (Raw.datatypeCaseKey spelling)
        pure (ValidatedDatatypeClause constructor arguments premises name)

    validatePremise headSymbol parameters (variable, domain)
        | directDatatypeCarrier headSymbol parameters domain =
            Right (ValidatedRecursivePremise variable (locate domain))
        | otherwise = do
            validateDatatypeDomainSyntax domain
            Right (ValidatedNonRecursivePremise variable domain)

datatypeConstructor
    :: Raw.Expr
    -> Either DatatypeError (Raw.FunctionSymbol, [Raw.VarSymbol])
datatypeConstructor = symbolicVariables "constructor"

symbolicVariables
    :: Text -> Raw.Expr
    -> Either DatatypeError (Raw.FunctionSymbol, [Raw.VarSymbol])
symbolicVariables role = \case
    Raw.ExprOp _location symbol arguments ->
        (symbol,)
            <$> traverse
                (\case
                    Raw.ExprVar variable -> Right variable
                    expression ->
                        Left
                            (DatatypeInvalid
                                (locate expression)
                                ("datatype " <> role <> " requires bare variable arguments")))
                arguments
    expression ->
        Left
            (DatatypeInvalid
                (locate expression)
                ("datatype " <> role <> " must be a symbolic term"))

directDatatypeCarrier :: Raw.FunctionSymbol -> [Raw.VarSymbol] -> Raw.Expr -> Bool
directDatatypeCarrier symbol parameters = \case
    Raw.ExprOp _location candidate arguments -> candidate == symbol && arguments == (Raw.ExprVar <$> parameters)
    _ -> False

-- | Validate the deliberately supported source language for a nonrecursive
-- datatype premise domain.  Dependent functional-replacement telescopes and
-- proposition-context quantified terms are ordinary ways to describe the
-- fixed parameter-dependent set and are intentionally accepted. This validation does
-- not permit indirect carrier recursion; the carrier is withheld from the
-- elaboration context and checked separately in 'prepareClause'.
-- Relational replacement and iota terms remain outside this deliberately
-- narrow compilation language even though ordinary elaboration supports them.
validateDatatypeDomainSyntax
    :: Raw.Expr
    -> Either DatatypeError ()
validateDatatypeDomainSyntax = \case
    Raw.ExprTypedConstant location _token _coreType ->
        unsupportedDatatypeSyntax location
    Raw.ExprHigherApply location _function _argument ->
        unsupportedDatatypeSyntax location
    Raw.ExprLambda location _variables _coreType _body ->
        unsupportedDatatypeSyntax location
    Raw.ExprSelect location _coreType _predicate ->
        unsupportedDatatypeSyntax location
    Raw.ExprStructAggregate location _schema _entries ->
        unsupportedDatatypeSyntax location
    Raw.ExprStructReduct location _schema _record ->
        unsupportedDatatypeSyntax location
    Raw.ExprStructReconstruction location _schema _record _entries ->
        unsupportedDatatypeSyntax location
    Raw.ExprOp _location _symbol arguments ->
        traverse_ validateDatatypeDomainSyntax arguments
    Raw.ExprStructOp _location _symbol argument ->
        traverse_ validateDatatypeDomainSyntax argument
    Raw.ExprFiniteSet _location elements ->
        traverse_ validateDatatypeDomainSyntax elements
    Raw.ExprSep _location _variable bound predicate -> do
        validateDatatypeDomainSyntax bound
        validateDatatypeStatementSyntax predicate
    Raw.ExprReplace _location value bounds condition -> do
        validateDatatypeDomainSyntax value
        traverse_ (validateDatatypeDomainSyntax . snd) bounds
        traverse_ validateDatatypeStatementSyntax condition
    Raw.ExprReplacePred location _range _domainVariable _bound _predicate ->
        unsupportedDatatypeSyntax location
    Raw.ExprVar{} -> pure ()
    Raw.ExprNaturalNumeral{} -> pure ()
    Raw.ExprOpaqueInteger{} -> pure ()

validateDatatypeStatementSyntax
    :: Raw.Stmt
    -> Either DatatypeError ()
validateDatatypeStatementSyntax = \case
    Raw.StmtFormula formula ->
        validateDatatypeFormulaSyntax formula
    Raw.StmtVerbPhrase terms verbPhrase -> do
        traverse_ validateDatatypeTermSyntax terms
        validateDatatypeVerbPhraseSyntax verbPhrase
    Raw.StmtNoun _sign terms nounPhrase -> do
        traverse_ validateDatatypeTermSyntax terms
        validateDatatypeNounPhraseSyntax nounPhrase
    Raw.StmtStruct term
            (Raw.StructNounPhrase modifiers structure right condition) -> do
        validateDatatypeTermSyntax term
        traverse_
            (\(Raw.AdjL _location _item arguments) ->
                traverse_ validateDatatypeTermSyntax arguments)
            modifiers
        traverse_
            validateDatatypeTermSyntax
            (Raw.structApplicationArguments structure)
        traverse_ validateRightAdjective right
        traverse_ validateDatatypeStatementSyntax condition
    Raw.StmtExactStruct term _structure ->
        unsupportedDatatypeSyntax (locate term)
    Raw.StmtNeg _location statement ->
        validateDatatypeStatementSyntax statement
    Raw.StmtExists _location nounPhrase ->
        validateDatatypeNounPhraseSyntax nounPhrase
    Raw.StmtConnected _connective _location left right -> do
        validateDatatypeStatementSyntax left
        validateDatatypeStatementSyntax right
    Raw.StmtQuantPhrase _location quantPhrase statement -> do
        validateDatatypeQuantPhraseSyntax quantPhrase
        validateDatatypeStatementSyntax statement
    Raw.SymbolicQuantified
            _location _quantifier _variables bound condition statement -> do
        validateDatatypeBoundSyntax bound
        traverse_ validateDatatypeStatementSyntax condition
        validateDatatypeStatementSyntax statement
  where
    validateRightAdjective = \case
        Raw.AdjR _location _item terms ->
            traverse_ validateDatatypeTermSyntax terms
        Raw.AttrRThat verbPhrase ->
            validateDatatypeVerbPhraseSyntax verbPhrase

validateDatatypeFormulaSyntax
    :: Raw.Formula
    -> Either DatatypeError ()
validateDatatypeFormulaSyntax = \case
    Raw.FormulaChain chain ->
        validateDatatypeChainSyntax chain
    Raw.FormulaSetMap _location function domain codomain -> do
        validateDatatypeDomainSyntax function
        validateDatatypeDomainSyntax domain
        validateDatatypeDomainSyntax codomain
    Raw.FormulaExpression expression ->
        unsupportedDatatypeSyntax (locate expression)
    Raw.FormulaPredicate _location _predicate _marker expressions ->
        traverse_ validateDatatypeDomainSyntax expressions
    Raw.Connected _location _connective left right -> do
        validateDatatypeFormulaSyntax left
        validateDatatypeFormulaSyntax right
    Raw.FormulaNeg _location formula ->
        validateDatatypeFormulaSyntax formula
    Raw.FormulaQuantified
            _location _quantifier _variables bound formula -> do
        validateDatatypeBoundSyntax bound
        validateDatatypeFormulaSyntax formula
    Raw.FormulaTypedQuantified location
            _quantifier _variables _coreType _formula ->
        unsupportedDatatypeSyntax location
    Raw.PropositionalConstant{} -> pure ()

validateDatatypeChainSyntax
    :: Raw.Chain
    -> Either DatatypeError ()
validateDatatypeChainSyntax = \case
    Raw.ChainBase left _sign relation right -> do
        traverse_ validateDatatypeDomainSyntax left
        validateDatatypeRelationSyntax relation
        traverse_ validateDatatypeDomainSyntax right
    Raw.ChainCons left _sign relation rest -> do
        traverse_ validateDatatypeDomainSyntax left
        validateDatatypeRelationSyntax relation
        validateDatatypeChainSyntax rest

validateDatatypeRelationSyntax
    :: Raw.Relation
    -> Either DatatypeError ()
validateDatatypeRelationSyntax = \case
    Raw.Relation _location _symbol parameters ->
        traverse_ validateDatatypeDomainSyntax parameters
    Raw.RelationExpr _location expression ->
        validateDatatypeDomainSyntax expression

validateDatatypeBoundSyntax
    :: Raw.Bound
    -> Either DatatypeError ()
validateDatatypeBoundSyntax = \case
    Raw.Unbounded -> pure ()
    Raw.Bounded _location _sign relation expression -> do
        validateDatatypeRelationSyntax relation
        validateDatatypeDomainSyntax expression

validateDatatypeTermSyntax
    :: Raw.Term
    -> Either DatatypeError ()
validateDatatypeTermSyntax = \case
    Raw.TermExpr expression ->
        validateDatatypeDomainSyntax expression
    Raw.TermFun function ->
        traverse_ validateDatatypeTermSyntax (Raw.funArgs function)
    Raw.TermIota location _variable _statement ->
        unsupportedDatatypeSyntax location
    Raw.TermQuantified _quantifier _location nounPhrase ->
        validateDatatypeNounPhraseSyntax nounPhrase

validateDatatypeNounPhraseSyntax
    :: Raw.NounPhraseOf container Raw.Term
    -> Either DatatypeError ()
validateDatatypeNounPhraseSyntax
        (Raw.NounPhrase left noun (Raw.NounBinder _variables bound) right condition) = do
    traverse_ validateLeftAdjective left
    validateNoun noun
    validateDatatypeBoundSyntax bound
    traverse_ validateRightAdjective right
    traverse_ validateDatatypeStatementSyntax condition
  where
    validateLeftAdjective (Raw.AdjL _location _item terms) =
        traverse_ validateDatatypeTermSyntax terms

    validateRightAdjective = \case
        Raw.AdjR _location _item terms ->
            traverse_ validateDatatypeTermSyntax terms
        Raw.AttrRThat verbPhrase ->
            validateDatatypeVerbPhraseSyntax verbPhrase

    validateNoun (Raw.Noun _location _item terms) =
        traverse_ validateDatatypeTermSyntax terms

validateDatatypeVerbPhraseSyntax
    :: Raw.VerbPhrase
    -> Either DatatypeError ()
validateDatatypeVerbPhraseSyntax = \case
    Raw.VPVerb verb -> validateVerb verb
    Raw.VPAdj adjectives -> traverse_ validateAdjective adjectives
    Raw.VPVerbNot verb -> validateVerb verb
    Raw.VPAdjNot adjectives -> traverse_ validateAdjective adjectives
  where
    validateVerb (Raw.Verb _location _item terms) =
        traverse_ validateDatatypeTermSyntax terms

    validateAdjective (Raw.Adj _location _item terms) =
        traverse_ validateDatatypeTermSyntax terms

validateDatatypeQuantPhraseSyntax
    :: Raw.QuantPhrase
    -> Either DatatypeError ()
validateDatatypeQuantPhraseSyntax
        (Raw.QuantPhrase _quantifier nounPhrase) =
    validateDatatypeNounPhraseSyntax nounPhrase

unsupportedDatatypeSyntax
    :: Location
    -> Either DatatypeError value
unsupportedDatatypeSyntax location =
    Left
        (DatatypeInvalid location
            "this syntax is not supported in datatype premise domains")

validateOccurrences
    :: Location
    -> Raw.Marker
    -> Raw.Datatype
    -> [SourceOccurrence]
    -> Prepare (NonEmpty SemanticGlobalKey)
validateOccurrences location marker datatype occurrences = do
    expected <- Except.liftEither (expectedOccurrences location marker datatype)
    unless (length occurrences == NonEmpty.length expected)
        (Except.throwError
            (DatatypeOccurrenceCountMismatch
                location
                (NonEmpty.length expected)
                (length occurrences)))
    sequence
        (NonEmpty.zipWith validateOne expected
            (case NonEmpty.nonEmpty occurrences of
                Just nonempty -> nonempty
                Nothing ->
                    impossible "equal nonzero occurrence counts became empty"))
  where
    validateOne
            (expectedLocation, expectedMarker, expectedPattern)
            (actualLocation, actualMarker, entry) =
        case entry of
            CanonicalExpressionFunction pattern' marker' _fixity
                | actualMarker == expectedMarker
                , marker' == expectedMarker
                , pattern' == expectedPattern ->
                    pure (SemanticExpressionFunction pattern')
            _ ->
                Except.throwError
                    (DatatypeOccurrenceMismatch
                        (preferKnownLocation actualLocation expectedLocation))

expectedOccurrences
    :: Location
    -> Raw.Marker
    -> Raw.Datatype
    -> Either
        DatatypeError
        (NonEmpty (Location, Raw.Marker, Raw.Pattern))
expectedOccurrences location blockMarker datatype = do
    headOccurrence <- expectedSymbol blockMarker (Raw.datatypeHeadExpr datatype)
    clauses <-
        traverse
            (\clause ->
                case Raw.datatypeClauseConstructorExpr clause of
                    Raw.ExprOp constructorLocation symbol _arguments ->
                        Right
                            ( constructorLocation
                            , Raw.mixfixMarker symbol
                            , Raw.mixfixPattern symbol
                            )
                    expression ->
                        Left (DatatypeOccurrenceMismatch (locate expression)))
            (Raw.datatypeClauses datatype)
    pure (headOccurrence :| toList clauses)
  where
    expectedSymbol expectedMarker = \case
        Raw.ExprOp symbolLocation symbol _arguments ->
            Right
                ( symbolLocation
                , expectedMarker
                , Raw.mixfixPattern symbol
                )
        expression ->
            Left
                (DatatypeOccurrenceMismatch
                    (preferKnownLocation (locate expression) location))

validateKeys
    :: [SourceOccurrence]
    -> NonEmpty SemanticGlobalKey
    -> Prepare ()
validateKeys occurrences keys = do
    case firstDuplicateWithLocation of
        Just (duplicate, duplicateLocation) ->
            Except.throwError
                (DatatypeDuplicateGlobal duplicateLocation duplicate)
        Nothing -> pure ()
    traverse_ validateOne (NonEmpty.zip locations keys)
  where
    locations = validatedOccurrenceLocations occurrences
    firstDuplicateWithLocation =
        go Set.empty
            [ (key, occurrenceLocation)
            | (key, (occurrenceLocation, _marker, _entry)) <-
                zip (toList keys) occurrences
            ]

    go _seen [] = Nothing
    go seen ((key, occurrenceLocation) : remaining)
        | key `Set.member` seen = Just (key, occurrenceLocation)
        | otherwise = go (Set.insert key seen) remaining

    validateOne (occurrenceLocation, key) = do
        when (isJust (fixedSemanticMeaning key))
            (Except.throwError
                (DatatypeFixedSemanticCollision occurrenceLocation key))
        visible <- Trans.lift (Declaration.resolveVisibleGlobalLowering key)
        when (isJust visible)
            (Except.throwError
                (DatatypeGlobalAlreadyVisible occurrenceLocation key))

validatedOccurrenceLocations
    :: [SourceOccurrence]
    -> NonEmpty Location
validatedOccurrenceLocations occurrences =
    case NonEmpty.nonEmpty
            [ occurrenceLocation
            | (occurrenceLocation, _marker, _entry) <- occurrences
            ] of
        Just nonempty -> nonempty
        Nothing -> impossible "validated datatype occurrences are empty"

prepareObject :: TheoryId -> Raw.FunctionSymbol -> SemanticGlobalKey -> Int -> CanonicalTerm ObjectId -> PreparedDatatypeObject
prepareObject theory symbol key arity body =
    let coreType = foldr (const (TyArrow TySet)) TySet [1 .. arity]
        object = transparentObject theory coreType body
    in PreparedDatatypeObject symbol key coreType (assertedObjectId object) object

bindingLabelFromFunctionSymbol
    :: Raw.FunctionSymbol
    -> SemanticBindingLabel
bindingLabelFromFunctionSymbol symbol =
    case Raw.mixfixMarker symbol of
        Raw.Marker marker -> semanticBindingLabel marker

prepareClause
    :: SemanticGlobalKey
    -> Elaboration.DatatypeElaborationEnvironment
    -> Map.Map Raw.FunctionSymbol ObjectId
    -> ValidatedDatatypeClause
    -> Prepare PreparedClause
prepareClause carrierKey environment constructors
        (ValidatedDatatypeClause constructor arguments premises name) = do
    constructorIdentity <-
        maybe
            (impossible "validated datatype constructor lost its object")
            pure
            (Map.lookup constructor constructors)
    preparedPremises <- traverse preparePremise premises
    pure
        (PreparedClause
            constructor constructorIdentity arguments preparedPremises name)
  where
    preparePremise = \case
        ValidatedRecursivePremise variable _location ->
            pure (PreparedRecursivePremise variable)
        ValidatedNonRecursivePremise variable domain -> do
            prepared <-
                Trans.lift
                    (Elaboration.elaborateDatatypeExpression
                        environment
                        (Raw.TypedExpressionExpr domain))
                    >>= \case
                        Left failure ->
                            Except.throwError
                                (classifyElaborationFailure
                                    carrierKey domain failure)
                        Right value -> pure value
            let scoped = Elaboration.elaboratedExpressionCore prepared
            unless (scopedCoreType scoped == TySet)
                (Except.throwError
                    (DatatypeExpectedSet
                        (locate domain)
                        (scopedCoreType scoped)))
            pure (PreparedNonRecursivePremise variable scoped)

    classifyElaborationFailure expectedCarrierKey domain = \case
        Elaboration.ElaborationGlobalNotVisible _location key
            | key == expectedCarrierKey ->
                DatatypeInvalid
                    (locate domain)
                    "datatype recursive premise must be direct"
        Elaboration.ElaborationFreeVariable location _variable ->
            DatatypeInvalid
                location
                "datatype premise domains may contain only family parameters"
        failure -> DatatypeElaborationFailed failure

preparedPremiseVariable :: PreparedPremise -> Raw.VarSymbol
preparedPremiseVariable = \case
    PreparedRecursivePremise variable -> variable
    PreparedNonRecursivePremise variable _ -> variable

functionSymbolText :: Raw.FunctionSymbol -> Text
functionSymbolText symbol = case Raw.mixfixMarker symbol of Raw.Marker name -> name

unorderedPairs :: [value] -> [(value, value)]
unorderedPairs [] = []
unorderedPairs (first : remaining) = ((first,) <$> remaining) <> unorderedPairs remaining

prepareStages
    :: Location -> CheckedFoundation -> CheckedObjectClosure -> Raw.FunctionSymbol
    -> Int -> ObjectId -> ObjectId -> NonEmpty PreparedClause -> NonEmpty Construction.Clause
    -> [AssertedObject] -> Either DatatypeError (NonEmpty (NonEmpty PreparedCandidate))
prepareStages location foundation closure headSymbol parameterCount k carrier sourceClauses clauses definitions = do
    definitionStage <- traverse definitionCandidate definitions >>= nonempty "definitions"
    let stages0 = [definitionStage]
        count = fromIntegral (NonEmpty.length clauses)
        carrierPosition = PlannedCandidatePosition 0 (count + 1)
        position = PlannedCandidatePosition
        internal stages label references target build = derived stages label Nothing references target build
        public stages suffix references target build =
            derived stages suffix (Just (Raw.Marker (base <> "_" <> suffix))) references target build
        parameterized emit stages label references target build =
            emit stages label references
                ((\body -> foldr CForall body (replicate parameterCount TySet)) <$> target)
                (\imports -> Proof.introduceForalls context (replicate parameterCount TySet)
                    (\parameterContext -> build parameterContext imports))
        familyInternal = parameterized internal
        familyPublic = parameterized public
        carrierTerm = foldl' CApp (CGlobal carrier)
            (CBound . fromIntegral <$> reverse [0 .. parameterCount - 1])
        namedClauses = NonEmpty.zipWith (\index (PreparedClause _ _ _ _ name, clause) ->
            (index, name, clause)) (0 :| [1 ..]) (NonEmpty.zip sourceClauses clauses)
        domains = [scopedCoreTerm domain | clause <- toList clauses, Construction.FixedDomain domain <- Construction.clausePremises clause]
        domainPositions = zip domains [position 2 index | index <- [1 ..]]
    injection <- internal stages0 "Kuratowski injectivity" [position 0 0]
        (pure (Construction.kuratowskiInjectiveTarget k))
        (\imports -> Construction.proveKuratowskiInjective context k (imports 0))
    bits <- internal stages0 "bit inequality" [] (pure Construction.bitInequalityTarget)
        (\_ -> Construction.proveBitInequality context)
    zero <- internal stages0 "universe empty-set containment" [] (pure Construction.universeEmptyTarget)
        (\_ -> Construction.proveUniverseEmpty context)
    let stage1 = injection :| [bits, zero]
        stages1 = stages0 <> [stage1]
    pair <- internal stages1 "universe pair closure" [position 1 2, position 1 1]
        (pure Construction.universePairTarget)
        (\imports -> Construction.proveUniversePair context (imports 0) (imports 1))
    (bound, operator, _) <- constructionResult location "carrier terms" (Construction.carrierTerms parameterCount clauses)
    domainBounds <- traverse (\domain -> familyInternal stages1 "fixed-domain universe bound" []
        (pure (Construction.subsetTerm domain bound)) (\parameterContext _ -> Construction.proveDomainBound parameterContext clauses domain)) domains
    let stage2 = pair :| domainBounds
        stages2 = stages1 <> [stage2]
    kuratowski <- internal stages2 "universe Kuratowski closure" [position 0 0, position 2 0]
        (pure (Construction.universeKuratowskiTarget k))
        (\imports -> Construction.proveUniverseKuratowski context (imports 0) (imports 1))
    let stage3 = kuratowski :| []
        stages3 = stages2 <> [stage3]
    guards <- for namedClauses \(index, name, clause) -> do
        let needed = [scopedCoreTerm domain | Construction.FixedDomain domain <- Construction.clausePremises clause]
        selected <- traverse (\domain -> maybe (Left (DatatypeInvalid location "a fixed domain lost its candidate")) pure
            (List.lookup domain domainPositions)) needed
        familyInternal stages3 (name <> " universe guard")
            ([position 0 (index + 1), position 1 2, position 2 0, position 3 0] <> selected)
            (Construction.guardTarget parameterCount bound clause)
            (\parameterContext imports -> Construction.proveGuard parameterContext k clauses index (imports 0)
                (Construction.UniverseProofs (imports 1) (imports 2) (imports 3))
                (zip needed [imports i | i <- [4 ..]]))
    monotone <- familyInternal stages3 "bounded monotonicity" [] (Construction.boundedMonoTarget parameterCount clauses)
        (\parameterContext _ -> Construction.proveBoundedMono parameterContext clauses)
    let stage4 = append guards [monotone]
        stages4 = stages3 <> [stage4]
    bounded <- familyInternal stages4 "carrier bound" [carrierPosition]
        (pure (Construction.subsetTerm carrierTerm bound))
        (\parameterContext imports -> Construction.proveCarrierBound parameterContext carrierTerm clauses (imports 0))
    fixed <- familyInternal stages4 "carrier fixedness" [carrierPosition, position 4 count]
        (pure (CEq TySet carrierTerm (CApp operator carrierTerm)))
        (\parameterContext imports -> Construction.proveCarrierFixed parameterContext carrierTerm clauses (imports 0) (imports 1))
    let stage5 = bounded :| [fixed]
        stages5 = stages4 <> [stage5]
    introductions <- for namedClauses \(index, name, clause) ->
        familyPublic stages5 (name <> "_intro") [position 5 0, position 5 1, position 4 index]
            (Construction.introductionTarget parameterCount carrierTerm clause)
            (\parameterContext imports -> Construction.proveIntroduction parameterContext carrierTerm clauses index (imports 0) (imports 1) (imports 2))
    distinct <- for (unorderedPairs (toList namedClauses)) \((i, leftName, left), (j, rightName, right)) ->
        public stages5 (leftName <> "_" <> rightName <> "_distinct")
            [position 0 (i + 1), position 0 (j + 1), position 1 0, position 1 1]
            (pure (Construction.distinctTarget left right))
            (\imports -> Construction.proveDistinct context k count
                (i, left, imports 0) (j, right, imports 1) (imports 2) (imports 3))
    injective <- for [(i,name,clause) | (i,name,clause) <- toList namedClauses, not (null (Construction.clauseArgumentSlots clause))]
        \(index, name, clause) -> public stages5 (name <> "_injective") [position 0 (index + 1), position 1 0]
            (pure (Construction.injectiveTarget clause))
            (\imports -> Construction.proveInjective context k count index clause (imports 0) (imports 1))
    cases <- familyPublic stages5 "cases" [position 5 1] (Construction.casesTarget parameterCount carrierTerm clauses)
        (\parameterContext imports -> Construction.proveCases parameterContext carrierTerm clauses (imports 0))
    induction <- familyPublic stages5 "induct" [carrierPosition, position 4 count] (Construction.inductionTarget parameterCount carrierTerm clauses)
        (\parameterContext imports -> Construction.proveInduction parameterContext carrierTerm clauses (imports 0) (imports 1))
    let stage6 = append introductions (distinct <> injective <> [cases, induction])
        stages6 = stages5 <> [stage6]
        inductionPosition = position 6 (fromIntegral (NonEmpty.length stage6 - 1))
    predicateInduction <- familyPublic stages6 "predicate_induct"
        (inductionPosition : [position 6 index | index <- [0 .. count - 1]])
        (Construction.predicateInductionTarget parameterCount carrierTerm clauses)
        (\parameterContext imports -> Construction.provePredicateInduction parameterContext carrierTerm clauses
            (imports 0) [imports index | index <- [1 .. count]])
    pure (definitionStage :| [stage1, stage2, stage3, stage4, stage5, stage6, predicateInduction :| []])
  where
    base = functionSymbolText headSymbol
    typing = globalTypingFromClosure closure
    context = Proof.rootProofContext foundation typing
    append (initial :| rest) trailing = initial :| (rest <> trailing)
    nonempty label = maybe (Left (DatatypeInvalid location (label <> " stage is empty"))) Right . NonEmpty.nonEmpty
    checked label term = constructionResult location label (checkCanonicalCore typing term)
    definitionCandidate object = case assertedObjectContent object of
        TransparentObjectContent _ coreType body -> do
            let identity = assertedObjectId object
            target <- checked "implementation equation" (canonicalDefinitionEquationTarget identity coreType body)
            pure (PreparedCandidate target Nothing (ImplementationEquation identity))
        _ -> Left (DatatypeInvalid location "a datatype implementation object is not a definition")
    derived stages label marker positions target build = do
        expected <- constructionResult location label target >>= checked label
        targets <- traverse (\(PlannedCandidatePosition stage index) -> case nth stage stages >>= nth index . toList of
            Just (PreparedCandidate proposition _ _) -> Right proposition
            Nothing -> Left (DatatypeInvalid location (label <> " refers to an unavailable support candidate"))) positions
        let imports = zip [Kernel.importIx index | index <- [0 ..]] targets
            at index = fromMaybe (impossible "a datatype proof builder requested an unplanned import") (nth index imports)
        proof <- constructionResult location label (build at)
        pure (PreparedCandidate expected marker (DerivedFact (LocalCandidateReference <$> positions) (Proof.builtProofDerivation proof)))

encodePreparedDatatype
    :: NonEmpty PreparedDatatypeObject -> NonEmpty Construction.Clause
    -> NonEmpty (NonEmpty PreparedCandidate) -> DatatypeDescriptor PlannedCandidatePosition -> ByteString
encodePreparedDatatype objects clauses stages descriptor = encodeCache do
    putCacheTag 0x06
    putCacheList (\(PreparedDatatypeObject _ key coreType identity _) -> do
        putSemanticGlobalKeyCache key
        putCoreTypeCache coreType
        putObjectIdCache identity) (toList objects)
    putCacheList putClause (toList clauses)
    putCacheList (putCacheList putCandidate . toList) (toList stages)
    putDatatypeDescriptorCache (\(PlannedCandidatePosition stage index) ->
        putCacheNatural stage >> putCacheNatural index) descriptor
  where
    putTerm = putCanonicalTermCache putObjectIdCache
    putClause clause = do
        putObjectIdCache (Construction.clauseConstructor clause)
        putCacheList putCacheNatural (Construction.clauseArgumentSlots clause)
        putCacheList (\case
            Construction.Recursive -> putCacheTag 0x00
            Construction.FixedDomain domain -> do
                putCacheTag 0x01
                putCacheList putCoreTypeCache (scopedCoreContext domain)
                putTerm (scopedCoreTerm domain))
            (Construction.clausePremises clause)
    putCandidate (PreparedCandidate target marker evidence) = do
        putTerm (frozenCoreTerm target)
        -- Search eligibility is determined by the presence of the public alias.
        case marker of
            Nothing -> putCacheTag 0x00
            Just (Raw.Marker name) -> putCacheTag 0x01 >> putCacheText name
        case evidence of
            ImplementationEquation identity -> putCacheTag 0x00 >> putObjectIdCache identity
            DerivedFact references derivation -> do
                putCacheTag 0x01
                putCacheList putReference references
                Kernel.putKernelDerivationCache putObjectIdCache derivation
    putReference = \case
        LocalCandidateReference (PlannedCandidatePosition stage index) ->
            putCacheTag 0x00 >> putCacheNatural stage >> putCacheNatural index
        EnvironmentOccurrenceReference fingerprint ->
            putCacheTag 0x01 >> putSemanticFactOccurrenceFingerprintCache fingerprint
