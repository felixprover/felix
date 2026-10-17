{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Source elaboration into the common checked finite-schema compiler.
module Felix.Checking.Structure
    ( PreparedStructure
    , prepareStructure
    , CheckedStructureAuthorization
    , lowerPreparedStructure
    , authorizeCheckedStructure
    ) where

import Base
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Builtin qualified as Builtin
import Felix.Checking.Structure.Generated qualified as Generated
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Checking.SourceTerm qualified as SourceTerm
import Felix.Checking.Semantic (declarationSlotModule, declarationSlotOrdinal)
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Interface (CanonicalLexicalEntry(..))
import Control.Monad.Except (ExceptT)
import Control.Monad.Except qualified as Except
import Control.Monad (foldM, unless, when)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class qualified as Trans
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)

data PreparedStructure = PreparedStructure !CheckedObjectContribution !Schema.LocalStructureSchema

type CheckedStructureAuthorization = Generated.CheckedStructureBatchAuthorization

lowerPreparedStructure
    :: PreparedStructure -> Declaration.LoweringDriver
        (Either Declaration.DeclarationError (Declaration.CheckedDeclaration CheckedStructureAuthorization))
lowerPreparedStructure (PreparedStructure contribution input) =
    Generated.lowerStructureBatch contribution (input :| [])

authorizeCheckedStructure
    :: CheckedStructureAuthorization -> [NonEmpty Declaration.ReservedCandidate] -> Declaration.Declaration ()
authorizeCheckedStructure = Generated.authorizeStructureBatch

prepareStructure
    :: Raw.Block
    -> [CanonicalLexicalEntry]
    -> Declaration.LoweringDriver
        (Either ElaborationError PreparedStructure)
prepareStructure block entries =
    Except.runExceptT do
        (location, structure) <-
            case block of
                Raw.BlockStruct location _title _marker structure ->
                    pure (location, structure)
                _ -> Except.throwError
                    (ElaborationUnsupportedDeclaration (locate block))
        validateStructureOccurrences location structure entries
        let structurePhrase =
                Schema.structurePhrase (Raw.structPhrase structure)
            parentPhrases =
                ( Schema.structurePhrase
                    . Raw.structApplicationPhrase . Raw.structParentApplication
                ) <$> Raw.structParents structure
            preambleParameters =
                concatMap structureAssumptionVariables
                    (Raw.structPreamble structure)
            declaredParameters = Raw.structParameters structure
            localFields = Raw.structFields structure
            fieldSymbols = Raw.structFieldSymbol <$> localFields
        unless
            (preambleParameters == declaredParameters)
            (Except.throwError
                (ElaborationStructureParameterPreambleMismatch
                    location
                    declaredParameters
                    preambleParameters))
        case firstDuplicate declaredParameters of
            Just duplicate ->
                Except.throwError
                    (ElaborationDuplicateParameter location duplicate)
            Nothing -> pure ()
        when
            (structurePhrase `elem` parentPhrases)
            (Except.throwError
                (ElaborationStructureSelfParent location structurePhrase))
        visible <- Trans.lift
            (Declaration.resolveVisibleStructureLowering structurePhrase)
        when
            (isJust visible)
            (Except.throwError
                (ElaborationStructureAlreadyVisible location structurePhrase))
        parents <- traverse (resolveParent location)
            (Raw.structParentApplication <$> Raw.structParents structure)
        inherited <-
            foldM mergeParentFields Map.empty
                (zip parentPhrases parents)
        case firstDuplicate fieldSymbols of
            Just duplicate ->
                Except.throwError
                    (ElaborationStructureDuplicateField location duplicate)
            Nothing -> pure ()
        traverse_
            (\symbol ->
                when
                    (Map.member symbol inherited)
                    (Except.throwError
                        (ElaborationStructureFieldAlreadyInherited
                            location symbol)))
            fieldSymbols
        slot <- Trans.lift Declaration.nextDeclarationSlotLowering
        theory <- Trans.lift Declaration.currentTheoryLowering
        let makeField index field =
                let symbol = Raw.structFieldSymbol field
                    fieldSlot = structureFieldSlot index
                    fieldIdentity =
                        fieldId
                            (declarationSlotModule slot)
                            (declarationSlotOrdinal slot)
                            fieldSlot
                    resources = Record.fieldObjects theory fieldIdentity
                    selectorObject =
                        Record.fieldObjectsSelector resources
                    projectionObject =
                        Record.fieldObjectsProjection resources
                    selector = assertedObjectId selectorObject
                    identity = assertedObjectId projectionObject
                in ( field
                   , symbol
                   , fieldIdentity
                   , fieldSlot
                   , selector
                   , identity
                   , [selectorObject, projectionObject]
                   )
            ownFields =
                zipWith makeField [0 ..] localFields
            inheritedFields =
                (\(identity, _selector, projection) -> (identity, projection))
                    . fst
                    <$> inherited
            fieldObjects =
                concat
                    [ asserted
                    | ( _field, _symbol, _fieldIdentity, _fieldSlot
                      , _selector, _identity, asserted) <- ownFields
                    ]
            completeResources =
                Map.union
                    (Map.fromList
                        [ (symbol, (fieldIdentity, selector, projection))
                        | ( _field, symbol, fieldIdentity, _fieldSlot
                          , selector, projection, _asserted) <- ownFields
                        ])
                    (fst <$> inherited)
            completeAnnotatedFields =
                (\(identity, _selector, projection) -> (identity, projection))
                    <$> completeResources
        baseObjectClosure <-
            Trans.lift Declaration.checkedObjectClosureLowering
        fieldObjectClosure <-
            Except.liftEither
                (first
                    ElaborationProspectiveObjectInvalid
                    (extendObjectClosure baseObjectClosure fieldObjects))
        context <-
            either Except.throwError pure
                (extendElaborationContext
                    ( (localId 0, Raw.structLabel structure)
                        :| [ ( localId (fromIntegral index + 1)
                             , parameter
                             )
                           | (index, parameter) <-
                                zip [0 :: Int ..] declaredParameters
                           ]
                    )
                    emptyElaborationContext)
        let contextIndices = binderIndices context
            parameterArguments =
                [ SourceTerm.sourceTermOccurrence (CBound index) TySet
                    (LocatedSourceTerm (locate parameter))
                | parameter <- declaredParameters
                , let index =
                        maybe
                            (impossible
                                "a structure parameter is absent from its binder context")
                            fst
                            (Map.lookup parameter contextIndices)
                ]
            subjectIndex =
                maybe
                    (impossible
                        "a structure subject is absent from its binder context")
                    fst
                    (Map.lookup (Raw.structLabel structure) contextIndices)
            provisionalAnnotation =
                ResolvedStructureApplication
                    structurePhrase completeAnnotatedFields
                    parameterArguments
            structureContext =
                annotateBinderContext
                    (Map.singleton subjectIndex provisionalAnnotation)
                    context
        initialElaboration <- Trans.lift
            (initialElaborationStateLowering
                fieldObjectClosure structureContext)
        ( ( rawParameterPremises
          , rawParents
          , rawFields
          , rawAssumptions
          )
          , finalElaboration
          ) <-
            State.runStateT
                (do
                    parameterPremises <-
                        compileStructurePreamble
                            (Raw.structPreamble structure)
                    subject <-
                        compileIntroducedVariable
                            (Raw.structLabel structure)
                    compiledParents <-
                        traverse
                            (\(parentApplication, parent) -> do
                                arguments <-
                                    traverse
                                        compileSourceTermAsSet
                                        (Raw.structApplicationArguments
                                            parentApplication)
                                let resolvedApplication =
                                        ResolvedStructureApplication
                                            (Schema.structurePhrase
                                                (Raw.structApplicationPhrase
                                                    parentApplication))
                                            (Declaration.resolvedStructureFields
                                                parent)
                                            arguments
                                compiledProposition <- compileStructureNotionProposition
                                    location subject (AssertableStructureApplication
                                        resolvedApplication (Declaration.resolvedStructureRegistration parent))
                                retainStructureFormationComponent location compiledProposition
                                pure (resolvedApplication, compiledPropositionCore compiledProposition))
                            (zip (Raw.structParentApplication <$> Raw.structParents structure) parents)
                    let setAvailableFields fields =
                            setElaborationStructureAnnotation
                                subjectIndex
                                (ResolvedStructureApplication
                                    structurePhrase
                                    fields
                                    parameterArguments)
                        compileField
                                (available, compiled)
                                ( field
                                , symbol
                                , fieldIdentity
                                , fieldSlot
                                , selector
                                , object
                                , _asserted
                                ) = do
                            let available' =
                                    Map.insert
                                        symbol
                                        (fieldIdentity, object)
                                        available
                            setAvailableFields available'
                            compiledSpecification <-
                                traverse
                                    compileStatement
                                    (Raw.structFieldSpecification field)
                            traverse_
                                (retainStructureFormationComponent (locate field))
                                compiledSpecification
                            pure
                                ( available'
                                , ( locate field
                                  , Raw.structFieldMarker field
                                  , fieldIdentity
                                  , fieldSlot
                                  , symbol
                                  , selector
                                  , object
                                  , compiledPropositionCore
                                        <$> compiledSpecification
                                  ) : compiled
                                )
                    (_availableFields, reversedFields) <-
                        foldM
                            compileField
                            (inheritedFields, [])
                            ownFields
                    setAvailableFields completeAnnotatedFields
                    assumptions <-
                        traverse
                            (\(assumptionMarker, assumption) -> do
                                proposition <- compileStatement assumption
                                retainStructureFormationComponent
                                    (locate assumption)
                                    proposition
                                pure
                                    ( locate assumption
                                    , assumptionMarker
                                    , compiledPropositionCore proposition
                                    ))
                            (Raw.structAssumes structure)
                    pure
                        ( parameterPremises
                        , compiledParents
                        , reverse reversedFields
                        , assumptions
                        ))
                initialElaboration
        checkedParameterPremises <-
            for rawParameterPremises \(key, available, premiseLocation, premise) -> do
                let total = fromIntegral (length declaredParameters)
                _ <- checkEnvelopeProposition finalElaboration structureContext premiseLocation premise
                narrowed <- maybe
                    (Except.throwError (ElaborationStructureParameterDependencyViolation premiseLocation available total))
                    pure (narrowParameterPrefix total available premise)
                pure (key, available, premiseLocation, narrowed)
        checkedParents <-
            for rawParents \(annotation, proposition) -> do
                _ <- checkEnvelopeProposition finalElaboration structureContext location proposition
                pure annotation
        checkedFields <-
            traverse
                (\( fieldLocation
                   , fieldMarker
                   , fieldIdentity
                   , fieldSlot
                   , fieldSymbol
                   , fieldSelector
                   , fieldObject
                   , specification
                   ) -> do
                    checked <-
                        traverse
                            (checkEnvelopeProposition
                                finalElaboration
                                structureContext
                                fieldLocation)
                            specification
                    pure
                        ( fieldLocation
                        , fieldMarker
                        , fieldIdentity
                        , fieldSlot
                        , fieldSymbol
                        , fieldSelector
                        , fieldObject
                        , checked
                        ))
                rawFields
        checkedAssumptions <-
            traverse
                (\(assumptionLocation, assumptionMarker, proposition) -> do
                    checked <-
                        checkEnvelopeProposition
                            finalElaboration
                            structureContext
                            assumptionLocation
                            proposition
                    pure
                        ( assumptionLocation
                        , assumptionMarker
                        , checked
                        ))
                rawAssumptions
        root <- Trans.lift (Declaration.resolveVisibleStructureLowering Builtin.builtinRecordPhrase)
        let writtenParents =
                [Schema.structureApplicationKey
                    (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema parent))
                    (structureAnnotationArguments annotation)
                | (parent, annotation) <- zip parents checkedParents]
        defaultParents <- if null writtenParents
            then case root of
                Just parent -> pure [Schema.structureApplicationKey
                    (Schema.resolvedSchemaId (Declaration.resolvedStructureSchema parent)) []]
                Nothing -> Except.throwError
                    (ElaborationStructureNotVisible location Builtin.builtinRecordPhrase)
            else pure writtenParents
        let input = Schema.LocalStructureSchemaWire
                { Schema.localWireSlot = structureSlot 0
                , Schema.localWireParameters =
                    [Schema.LocalParameterOrdinal ordinal | (ordinal, _) <- zip [0 ..] declaredParameters]
                , Schema.localWirePreamble =
                    [Schema.LocalPreambleWire key available premise
                    | (key, available, _location, premise) <- checkedParameterPremises]
                , Schema.localWireParents = defaultParents
                , Schema.localWireFields =
                    [Schema.LocalStructureFieldWire fieldSlot symbol (scopedCoreTerm <$> specification)
                    | (_location, _marker, _identity, fieldSlot, symbol, _selector, _projection, specification) <- checkedFields]
                , Schema.localWireLaws =
                    [(Schema.LocalLawOrdinal ordinal, scopedCoreTerm proposition)
                    | (ordinal, (_location, _marker, proposition)) <- zip [0 ..] checkedAssumptions]
                }
            presentation = Schema.StructurePresentation
                { Schema.structurePresentationPhrase = structurePhrase
                , Schema.structurePresentationLocation = location
                , Schema.structurePresentationParameters = declaredParameters
                , Schema.structurePresentationParents =
                    if null writtenParents then [(Nothing, location)]
                    else [(Raw.structParentLabel parent, location) | parent <- Raw.structParents structure]
                , Schema.structurePresentationPreamble = Map.fromList
                    [(key, premiseLocation) | (key, _, premiseLocation, _) <- checkedParameterPremises]
                , Schema.structurePresentationFields = Map.fromList
                    [(fieldSlot, (fieldMarker, fieldLocation))
                    | (fieldLocation, fieldMarker, _, fieldSlot, _, _, _, _) <- checkedFields]
                , Schema.structurePresentationLaws = Map.fromList
                    [(Schema.LocalLawOrdinal ordinal, (lawMarker, lawLocation))
                    | (ordinal, (lawLocation, lawMarker, _)) <- zip [0 ..] checkedAssumptions]
                }
            origin = StructureOrigin (declarationSlotModule slot) (declarationSlotOrdinal slot) (structureSlot 0)
        local <- Except.liftEither
            (first (ElaborationStructureSchemaInvalid location)
                (Schema.checkLocalStructureSchema fieldObjectClosure origin input presentation))
        contribution <- Except.liftEither
            (first ElaborationProspectiveObjectInvalid (checkedObjectContribution fieldObjectClosure
                (assertedObjectId <$> fieldObjects)))
        pure (PreparedStructure contribution local)
  where
    resolveParent location application = do
        let structurePhrase =
                Schema.structurePhrase
                    (Raw.structApplicationPhrase application)
            actual =
                fromIntegral
                    (length
                        (Raw.structApplicationArguments application))
        resolved <- Trans.lift
            (Declaration.resolveVisibleStructureLowering structurePhrase)
        parent <- maybe
            (Except.throwError
                (ElaborationStructureNotVisible location structurePhrase))
            pure
            resolved
        let expected =
                Schema.resolvedSchemaParameterCount
                    (Declaration.resolvedStructureSchema parent)
        unless
            (expected == actual)
            (Except.throwError
                (ElaborationStructureParameterArityMismatch
                    location structurePhrase expected actual))
        pure parent

    structureAssumptionVariables = \case
        Raw.AsmSuppose{} -> []
        Raw.AsmLetNoun variables _nounPhrase -> toList variables
        Raw.AsmLetIn variables _domain -> toList variables
        Raw.AsmLetRelation variables _relation _right -> toList variables
        Raw.AsmLetThe variable _function -> [variable]
        Raw.AsmLetEq variable _expression -> [variable]
        Raw.AsmLetStruct variables _structure -> toList variables

    compileStructurePreamble = go 0 0
      where
        go _item _available [] = pure []
        go item available (assumption : rest) = do
            compiled <- compileHeaderAssumptionPropositions assumption
            traverse_ (retainCheckedStructureFormationComponent . snd) compiled
            let available' = available + fromIntegral (length (structureAssumptionVariables assumption))
                tagged =
                    [(Schema.LocalPreambleClauseKey item row, available', premiseLocation,
                        scopedCoreTerm (elaboratedPropositionCore proposition))
                    | (row, (premiseLocation, proposition)) <- zip [0 ..] compiled]
            (tagged <>) <$> go (item + 1) available' rest

    mergeParentFields inherited (parentPhrase, parent) =
        foldM
            (insertParentField parentPhrase)
            inherited
            [ (symbol, field)
            | symbol <- Declaration.resolvedStructureFieldOrder parent
            , let field =
                    fromMaybe
                        (impossible
                            "resolved parent presentation names a missing field")
                        (Map.lookup symbol
                            (Declaration.resolvedStructureFieldResources parent))
            ]

    insertParentField parentPhrase inherited (symbol, field) =
        case Map.lookup symbol inherited of
            Nothing ->
                pure
                    (Map.insert symbol (field, parentPhrase) inherited)
            Just (existing, existingOrigin)
                | existing == field -> pure inherited
                | otherwise ->
                    Except.throwError
                            (ElaborationStructureFieldConflict
                            (locate block)
                            symbol
                            existingOrigin
                            parentPhrase)

validateStructureOccurrences
    :: Location
    -> Raw.StructDefn
    -> [CanonicalLexicalEntry]
    -> ExceptT ElaborationError (Declaration.LoweringDriver) ()
validateStructureOccurrences location structure entries = do
    let Raw.LexicalItemSgPl forms structureMarker =
            Raw.structPhrase structure
        expected =
            CanonicalStructureNoun
                (Raw.sg forms)
                (Raw.pl forms)
                structureMarker
                : [ CanonicalStructureOperation command
                  | Raw.StructField
                        { Raw.structFieldSymbol = Raw.StructSymbol command } <-
                        Raw.structFields structure
                  ]
    unless
        (entries == expected)
        (Except.throwError
            (ElaborationStructureOccurrenceMismatch location))

-- Preamble clauses are elaborated with source names in the declaration context,
-- then checked in precisely the parameter prefix they may mention. This walk
-- removes the unavailable outer binders and preserves every inner binder.
narrowParameterPrefix
    :: Natural -> Natural -> CanonicalTerm global -> Maybe (CanonicalTerm global)
narrowParameterPrefix total available = go 0
  where
    omitted = total - available
    go depth = \case
        CBound index
            | index < depth -> Just (CBound index)
            | index - depth >= omitted && index - depth < total -> Just (CBound (index - omitted))
            | otherwise -> Nothing
        CGlobal global -> Just (CGlobal global)
        CIntrinsic intrinsic -> Just (CIntrinsic intrinsic)
        CLogicalSelect coreType -> Just (CLogicalSelect coreType)
        COpaqueInteger value -> Just (COpaqueInteger value)
        CApp function argument -> CApp <$> go depth function <*> go depth argument
        CLam coreType body -> CLam coreType <$> go (depth + 1) body
        CFalsum -> Just CFalsum
        CTruth -> Just CTruth
        CNot proposition -> CNot <$> go depth proposition
        CAnd left right -> CAnd <$> go depth left <*> go depth right
        COr left right -> COr <$> go depth left <*> go depth right
        CImp left right -> CImp <$> go depth left <*> go depth right
        CEq coreType left right -> CEq coreType <$> go depth left <*> go depth right
        CForall coreType body -> CForall coreType <$> go (depth + 1) body
        CExists coreType body -> CExists coreType <$> go (depth + 1) body
