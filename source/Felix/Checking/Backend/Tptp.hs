{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Deterministic task-wide TPTP preparation for checked typed problems.
module Felix.Checking.Backend.Tptp
    ( TypedFormulaOccurrence(..)
    , TypedTptpNameOrigin(..)
    , PreparedTypedTptpProblem
    , prepareTypedTptpProblem
    , preparedTypedTptpRoute
    , preparedTypedTptpText
    , preparedTypedTptpTextNewline
    , preparedTypedTptpConjectureText
    , preparedTypedTptpNameOrigins
    , TypedTptpPreparationError(..)
    ) where

import Base hiding (Empty)
import Felix.Checking.Backend.Problem
import Felix.Checking.Core
import Tptp.UnsortedFirstOrder qualified as Tptp

import Control.Monad (foldM)
import Control.Monad.State.Strict (StateT)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)
import TextBuilder


data TypedFormulaOccurrence ref
    = TypedGlobalPremiseOccurrence !ref
    | TypedLocalPremiseOccurrence !LocalPremiseOrdinal
    | TypedAuxiliaryOccurrence !Natural
    | TypedLogicalSelectionOccurrence !Natural !CoreType
    | TypedConjectureOccurrence
    deriving stock (Show, Eq, Ord)

data TypedTptpNameOrigin ref local global
    = TypedGlobalNameOrigin !global
    | TypedLocalNameOrigin !local
    | TypedIntrinsicNameOrigin !CoreIntrinsicTag
    | TypedLogicalSelectionNameOrigin !CoreType
    | TypedIntegerNameOrigin !Integer
    | TypedBinderNameOrigin !Natural
    | TypedFormulaNameOrigin !(TypedFormulaOccurrence ref)
    deriving stock (Show, Eq, Ord)

data PreparedTypedTptpProblem ref local global =
    PreparedTypedTptpProblem
        !TypedProblemRoute
        !Text
        !Text
        !(Map
            Text
            (TypedTptpNameOrigin ref local global))
    deriving stock (Eq)

preparedTypedTptpRoute
    :: PreparedTypedTptpProblem ref local global
    -> TypedProblemRoute
preparedTypedTptpRoute
        (PreparedTypedTptpProblem
            route
            _text
            _conjecture
            _origins) =
    route

preparedTypedTptpText
    :: PreparedTypedTptpProblem ref local global
    -> Text
preparedTypedTptpText
        (PreparedTypedTptpProblem
            _route
            problemText
            _conjecture
            _origins) =
    problemText

preparedTypedTptpTextNewline
    :: PreparedTypedTptpProblem ref local global
    -> Text
preparedTypedTptpTextNewline =
    (`Text.snoc` '\n')
        . preparedTypedTptpText

preparedTypedTptpConjectureText
    :: PreparedTypedTptpProblem ref local global
    -> Text
preparedTypedTptpConjectureText
        (PreparedTypedTptpProblem
            _route
            _text
            conjecture
            _origins) =
    conjecture

preparedTypedTptpNameOrigins
    :: PreparedTypedTptpProblem ref local global
    -> Map
        Text
        (TypedTptpNameOrigin ref local global)
preparedTypedTptpNameOrigins
        (PreparedTypedTptpProblem
            _route
            _text
            _conjecture
            origins) =
    origins

data TypedTptpPreparationError local global
    = InvalidGeneratedTypedTptpName !Text
    | DuplicateGeneratedTypedTptpName !Text
    | TypedTptpUnknownGlobal !global
    | TypedTptpUnknownLocal !local
    | TypedTptpUnboundIndex !Natural
    | TypedTptpFofProjectionMismatch
    deriving stock (Show, Eq)


data NameEnvironment ref local global =
    NameEnvironment
        !(Map global Tptp.AtomicWord)
        !(Map global CoreType)
        !(Map local Tptp.AtomicWord)
        !(Map CoreIntrinsicTag Tptp.AtomicWord)
        !(Map CoreType Tptp.AtomicWord)
        !(Map Integer Tptp.AtomicWord)
        !(Map
            Text
            (TypedTptpNameOrigin ref local global))

data RenderState ref local global =
    RenderState
        !Natural
        !Natural
        !(Map
            Text
            (TypedTptpNameOrigin ref local global))

type Render ref local global =
    StateT
        (RenderState ref local global)
        (Either
            (TypedTptpPreparationError local global))

data RenderedFormula ref = RenderedFormula
    !Tptp.AtomicWord
    !(TypedFormulaOccurrence ref)
    !TextBuilder

data BoundTarget
    = BoundFofVariable !Tptp.Variable
    | BoundTh0Variable !Tptp.Variable
    | AmbientConstant !Tptp.AtomicWord

prepareTypedTptpProblem
    :: (Ord local, Ord global)
    => TypedProblem ref local origin global
    -> Either
        (TypedTptpPreparationError local global)
        (PreparedTypedTptpProblem ref local global)
prepareTypedTptpProblem problem = do
    names <-
        allocateNames problem
    let initialState =
            RenderState
                0
                0
                (nameEnvironmentOrigins names)
    (rendered, finalState) <-
        State.runStateT
            (renderProblem names problem)
            initialState
    let (problemBuilder, conjectureBuilder) =
            rendered
        RenderState _nextBinder _nextHypothesis origins =
            finalState
    pure
        (PreparedTypedTptpProblem
            (typedProblemRoute problem)
            (TextBuilder.toText problemBuilder)
            (TextBuilder.toText conjectureBuilder)
            origins)

allocateNames
    :: (Ord local, Ord global)
    => TypedProblem ref local origin global
    -> Either
        (TypedTptpPreparationError local global)
        (NameEnvironment ref local global)
allocateNames problem = do
    globalAllocations <-
        allocateCategory
            "tg_g"
            TypedGlobalNameOrigin
            (Map.keys
                (typedProblemGlobalTypes
                    problem))
    localAllocations <-
        allocateCategory
            "tg_l"
            TypedLocalNameOrigin
            (Map.keys
                (typedProblemLocalTypes
                    problem))
    intrinsicAllocations <-
        allocateCategory
            "tg_i"
            TypedIntrinsicNameOrigin
            (Set.toAscList
                (problemIntrinsics problem))
    logicalSelectionAllocations <-
        allocateCategory
            "tg_s"
            TypedLogicalSelectionNameOrigin
            (typedLogicalSelectionAuxiliaryType
                <$> Vector.toList
                    (typedProblemLogicalSelections problem))
    integerAllocations <-
        allocateCategory
            "tg_n"
            TypedIntegerNameOrigin
            (Set.toAscList
                (problemIntegers problem))
    origins <-
        foldM
            (\current (target, nameOrigin) ->
                insertOrigin
                    (Tptp.atomicWordText target)
                    nameOrigin
                    current)
            Map.empty
            ( [ (target, nameOrigin)
              | (_global, target, nameOrigin) <-
                    globalAllocations
              ]
                <> [ (target, nameOrigin)
                   | (_local, target, nameOrigin) <-
                        localAllocations
                   ]
                <> [ (target, nameOrigin)
                   | (_intrinsic, target, nameOrigin) <-
                        intrinsicAllocations
                   ]
                <> [ (target, nameOrigin)
                   | (_coreType, target, nameOrigin) <-
                        logicalSelectionAllocations
                   ]
                <> [ (target, nameOrigin)
                   | (_integer, target, nameOrigin) <-
                        integerAllocations
                   ]
            )
    pure
        (NameEnvironment
            (Map.fromList
                [ (global, target)
                | (global, target, _nameOrigin) <-
                    globalAllocations
                ])
            (typedProblemGlobalTypes problem)
            (Map.fromList
                [ (local, target)
                | (local, target, _nameOrigin) <-
                    localAllocations
                ])
            (Map.fromList
                [ (intrinsic, target)
                | (intrinsic, target, _nameOrigin) <-
                    intrinsicAllocations
                ])
            (Map.fromList
                [ (coreType, target)
                | (coreType, target, _nameOrigin) <-
                    logicalSelectionAllocations
                ])
            (Map.fromList
                [ (integer, target)
                | (integer, target, _nameOrigin) <-
                    integerAllocations
                ])
            origins)
  where
    allocateCategory prefix makeOrigin semantics =
        traverse
            (\(ordinal, semantic) -> do
                target <-
                    generatedAtomicWord
                        (prefix
                            <> Text.pack
                                (show ordinal))
                pure
                    ( semantic
                    , target
                    , makeOrigin semantic
                    ))
            (zip [0 :: Int ..] semantics)

nameEnvironmentOrigins
    :: NameEnvironment ref local global
    -> Map
        Text
        (TypedTptpNameOrigin ref local global)
nameEnvironmentOrigins
        (NameEnvironment
            _globals
            _globalTypes
            _locals
            _intrinsics
            _logicalSelections
            _integers
            origins) =
    origins

generatedAtomicWord
    :: Text
    -> Either
        (TypedTptpPreparationError local global)
        Tptp.AtomicWord
generatedAtomicWord target =
    maybe
        (Left
            (InvalidGeneratedTypedTptpName
                target))
        Right
        (Tptp.atomicWord target)

generatedVariable
    :: Text
    -> Either
        (TypedTptpPreparationError local global)
        Tptp.Variable
generatedVariable target =
    maybe
        (Left
            (InvalidGeneratedTypedTptpName
                target))
        Right
        (Tptp.variable target)

insertOrigin
    :: Text
    -> TypedTptpNameOrigin ref local global
    -> Map
        Text
        (TypedTptpNameOrigin ref local global)
    -> Either
        (TypedTptpPreparationError local global)
        (Map
            Text
            (TypedTptpNameOrigin ref local global))
insertOrigin target nameOrigin origins =
    if Map.member target origins
        then
            Left
                (DuplicateGeneratedTypedTptpName
                    target)
        else
            Right
                (Map.insert
                    target
                    nameOrigin
                    origins)

renderProblem
    :: (Ord local, Ord global)
    => NameEnvironment ref local global
    -> TypedProblem ref local origin global
    -> Render
        ref
        local
        global
        (TextBuilder, TextBuilder)
renderProblem names problem = do
    hypotheses <-
        renderHypotheses names problem
    conjecture <-
        renderConjecture names problem
    declarations <-
        case typedProblemRoute problem of
            RouteFof ->
                pure []
            RouteTh0 ->
                renderTh0Declarations
                    names
                    problem
    let formulaBuilders =
            renderFormulaLine
                (typedProblemRoute problem)
                "axiom"
                <$> hypotheses
        conjectureBuilder =
            renderFormulaLine
                (typedProblemRoute problem)
                "conjecture"
                conjecture
        complete =
            intercalate
                (char '\n')
                (declarations
                    <> formulaBuilders
                    <> [conjectureBuilder])
    pure
        ( complete
        , conjectureBuilder
        )

renderHypotheses
    :: (Ord local, Ord global)
    => NameEnvironment ref local global
    -> TypedProblem ref local origin global
    -> Render
        ref
        local
        global
        [RenderedFormula ref]
renderHypotheses names problem = do
    globalFormulas <-
        traverse
            (\fact ->
                renderOccurrence
                    names
                    problem
                    (TypedGlobalPremiseOccurrence
                        (typedBackendFactReference
                            fact))
                    (weakenClosedSupportedProposition
                        (typedBackendFactProposition
                            fact)))
            (Vector.toList
                (typedProblemGlobalPremises
                    problem))
    localFormulas <-
        traverse
            (\premise ->
                renderOccurrence
                    names
                    problem
                    (TypedLocalPremiseOccurrence
                        (typedLocalPremiseOrdinal
                            premise))
                    (typedLocalPremiseProposition
                        premise))
            (Vector.toList
                (typedProblemLocalPremises
                    problem))
    auxiliaryFormulas <-
        traverse
            (\auxiliary ->
                renderOccurrence
                    names
                    problem
                    (TypedAuxiliaryOccurrence
                        (typedProblemAuxiliaryOrdinal
                            auxiliary))
                    (weakenClosedSupportedProposition
                        (typedProblemAuxiliaryProposition
                            auxiliary)))
            (Vector.toList
                (typedProblemAuxiliaries
                    problem))
    logicalSelectionFormulas <-
        traverse
            (\auxiliary ->
                renderOccurrence
                    names
                    problem
                    (TypedLogicalSelectionOccurrence
                        (typedLogicalSelectionAuxiliaryOrdinal auxiliary)
                        (typedLogicalSelectionAuxiliaryType auxiliary))
                    (weakenClosedSupportedProposition
                        (typedLogicalSelectionAuxiliaryProposition
                            auxiliary)))
            (Vector.toList
                (typedProblemLogicalSelections problem))
    pure
        (globalFormulas
            <> localFormulas
            <> auxiliaryFormulas
            <> logicalSelectionFormulas)

renderConjecture
    :: (Ord local, Ord global)
    => NameEnvironment ref local global
    -> TypedProblem ref local origin global
    -> Render
        ref
        local
        global
        (RenderedFormula ref)
renderConjecture names problem =
    renderOccurrence
        names
        problem
        TypedConjectureOccurrence
        (typedProblemClaim problem)

renderOccurrence
    :: (Ord local, Ord global)
    => NameEnvironment ref local global
    -> TypedProblem ref local origin global
    -> TypedFormulaOccurrence ref
    -> SupportedProposition local global
    -> Render
        ref
        local
        global
        (RenderedFormula ref)
renderOccurrence names problem occurrence proposition = do
    target <-
        case occurrence of
            TypedConjectureOccurrence ->
                liftEither
                    (generatedAtomicWord "tg_q0")
            _ -> do
                ordinal <-
                    nextHypothesisOrdinal
                liftEither
                    (generatedAtomicWord
                        ("tg_h"
                            <> Text.pack
                                (show ordinal)))
    registerOrigin
        (Tptp.atomicWordText target)
        (TypedFormulaNameOrigin occurrence)
    bounds <-
        initialBounds
            names
            proposition
    formula <-
        case typedProblemRoute problem of
            RouteFof ->
                renderFofFormula
                    names
                    bounds
                    (supportedPropositionTerm
                        proposition)
            RouteTh0 ->
                renderTh0Term
                    names
                    bounds
                    (supportedPropositionTerm
                        proposition)
    pure
        (RenderedFormula
            target
            occurrence
            formula)

-- Formula and binder ordinals use separate dense namespaces.
nextHypothesisOrdinal
    :: Render ref local global Natural
nextHypothesisOrdinal = do
    RenderState nextBinder nextHypothesis origins <-
        State.get
    State.put
        (RenderState
            nextBinder
            (nextHypothesis + 1)
            origins)
    pure nextHypothesis

registerOrigin
    :: Text
    -> TypedTptpNameOrigin ref local global
    -> Render ref local global ()
registerOrigin target nameOrigin = do
    RenderState nextBinder nextHypothesis origins <-
        State.get
    origins' <-
        liftEither
            (insertOrigin
                target
                nameOrigin
                origins)
    State.put
        (RenderState
            nextBinder
            nextHypothesis
            origins')

freshBinder
    :: Render ref local global Tptp.Variable
freshBinder = do
    RenderState nextBinder nextHypothesis origins <-
        State.get
    let target =
            "V" <> Text.pack (show nextBinder)
    variable <-
        liftEither
            (generatedVariable target)
    origins' <-
        liftEither
            (insertOrigin
                target
                (TypedBinderNameOrigin
                    nextBinder)
                origins)
    State.put
        (RenderState
            (nextBinder + 1)
            nextHypothesis
            origins')
    pure variable

liftEither
    :: Either
        (TypedTptpPreparationError local global)
        value
    -> Render ref local global value
liftEither =
    lift

initialBounds
    :: Ord local
    => NameEnvironment ref local global
    -> SupportedProposition local global
    -> Render ref local global [BoundTarget]
initialBounds
        (NameEnvironment
            _globals
            _globalTypes
            localNames
            _intrinsics
            _logicalSelections
            _integers
            _origins)
        proposition =
    traverse
        (\(local, _coreType) ->
            maybe
                (lift
                    (Left
                        (TypedTptpUnknownLocal
                            local)))
                (pure . AmbientConstant)
                (Map.lookup
                    local
                    localNames))
        (Vector.toList
            (supportedPropositionSupport
                proposition))

renderFormulaLine
    :: TypedProblemRoute
    -> TextBuilder
    -> RenderedFormula ref
    -> TextBuilder
renderFormulaLine route role
        (RenderedFormula target _occurrence formula) =
    dialect
        <> char '('
        <> Tptp.buildAtomicWord target
        <> char ','
        <> role
        <> char ','
        <> formula
        <> text ")."
  where
    dialect =
        case route of
            RouteFof ->
                text "fof"
            RouteTh0 ->
                text "thf"


renderFofFormula
    :: (Ord global)
    => NameEnvironment ref local global
    -> [BoundTarget]
    -> CanonicalTerm global
    -> Render ref local global TextBuilder
renderFofFormula names bounds = \case
    CFalsum ->
        pure (text "$false")
    CTruth ->
        pure (text "$true")
    CNot proposition -> do
        proposition' <-
            renderFofFormula names bounds proposition
        pure (parenthesize (char '~' <> proposition'))
    CAnd left right -> do
        left' <- renderFofFormula names bounds left
        right' <- renderFofFormula names bounds right
        pure (vampireConjunction left' right')
    COr left right -> do
        left' <- renderFofFormula names bounds left
        right' <- renderFofFormula names bounds right
        pure (vampireDisjunction left' right')
    CImp premise conclusion -> do
        premise' <-
            renderFofFormula names bounds premise
        conclusion' <-
            renderFofFormula names bounds conclusion
        pure
            (parenthesize
                (premise'
                    <> text "=>"
                    <> conclusion'))
    CEq TySet left right -> do
        left' <-
            renderFofTerm names bounds left
        right' <-
            renderFofTerm names bounds right
        pure
            (parenthesize
                (left'
                    <> char '='
                    <> right'))
    CEq TyProp left right -> do
        left' <-
            renderFofFormula names bounds left
        right' <-
            renderFofFormula names bounds right
        pure
            (parenthesize
                (left'
                    <> text "<=>"
                    <> right'))
    CForall TySet body -> do
        variable <-
            freshBinder
        body' <-
            renderFofFormula
                names
                (BoundFofVariable variable
                    : bounds)
                body
        pure
            (parenthesize
                (text "!["
                    <> Tptp.buildVariable variable
                    <> text "]:"
                    <> body'))
    CExists TySet body -> do
        variable <-
            freshBinder
        body' <-
            renderFofFormula
                names
                (BoundFofVariable variable
                    : bounds)
                body
        pure
            (parenthesize
                (text "?["
                    <> Tptp.buildVariable variable
                    <> text "]:"
                    <> body'))
    application ->
        renderFofApplication
            names
            bounds
            TyProp
            application

renderFofTerm
    :: Ord global
    => NameEnvironment ref local global
    -> [BoundTarget]
    -> CanonicalTerm global
    -> Render ref local global TextBuilder
renderFofTerm names bounds = \case
    CBound index ->
        renderBound index bounds
    CGlobal global ->
        Tptp.buildAtomicWord
            <$> lookupGlobal names global
    CIntrinsic intrinsic ->
        Tptp.buildAtomicWord
            <$> lookupIntrinsic names intrinsic
    CLogicalSelect{} ->
        lift
            (Left
                TypedTptpFofProjectionMismatch)
    COpaqueInteger integer ->
        Tptp.buildAtomicWord
            <$> lookupInteger names integer
    application ->
        renderFofApplication
            names
            bounds
            TySet
            application

renderFofApplication
    :: Ord global
    => NameEnvironment ref local global
    -> [BoundTarget]
    -> CoreType
    -> CanonicalTerm global
    -> Render ref local global TextBuilder
renderFofApplication names bounds expected application =
    case canonicalApplicationSpine application of
        (CGlobal global, arguments) -> do
            coreType <-
                maybe
                    (lift
                        (Left
                            (TypedTptpUnknownGlobal
                                global)))
                    pure
                    (Map.lookup
                        global
                        (nameEnvironmentGlobalTypes
                            names))
            renderHead
                coreType
                (lookupGlobal names global)
                arguments
        (CIntrinsic intrinsic, arguments) ->
            renderHead
                (coreIntrinsicType intrinsic)
                (lookupIntrinsic names intrinsic)
                arguments
        (CLogicalSelect{}, _arguments) ->
            lift
                (Left
                    TypedTptpFofProjectionMismatch)
        _ ->
            lift
                (Left
                    TypedTptpFofProjectionMismatch)
  where
    renderHead coreType targetAction arguments = do
        unlessFofApplication
            expected
            coreType
            arguments
        target <-
            targetAction
        arguments' <-
            traverse
                (renderFofTerm names bounds)
                arguments
        pure
            (applyAtomicWord
                target
                arguments')

-- Global types are retained in the problem, but names need only the allocated
-- symbols. FOF saturation was already checked by the projection witness.
nameEnvironmentGlobalTypes
    :: NameEnvironment ref local global
    -> Map global CoreType
nameEnvironmentGlobalTypes
        (NameEnvironment
            _globals
            globalTypes
            _locals
            _intrinsics
            _logicalSelections
            _integers
            _origins) =
    globalTypes

unlessFofApplication
    :: CoreType
    -> CoreType
    -> [CanonicalTerm global]
    -> Render ref local global ()
unlessFofApplication expected coreType arguments =
    case consume coreType arguments of
        Just result
            | result == expected ->
                pure ()
        _ ->
            lift
                (Left
                    TypedTptpFofProjectionMismatch)
  where
    consume current = \case
        [] ->
            Just current
        _argument : remaining ->
            case current of
                TyArrow TySet result ->
                    consume result remaining
                _ ->
                    Nothing

applyAtomicWord
    :: Tptp.AtomicWord
    -> [TextBuilder]
    -> TextBuilder
applyAtomicWord target = \case
    [] ->
        Tptp.buildAtomicWord target
    arguments ->
        Tptp.buildAtomicWord target
            <> Tptp.buildTuple arguments

renderBound
    :: Natural
    -> [BoundTarget]
    -> Render ref local global TextBuilder
renderBound index bounds =
    case nth index bounds of
        Nothing ->
            lift
                (Left
                    (TypedTptpUnboundIndex
                        index))
        Just (BoundFofVariable variable) ->
            pure
                (Tptp.buildVariable
                    variable)
        Just (BoundTh0Variable variable) ->
            pure
                (Tptp.buildVariable
                    variable)
        Just (AmbientConstant target) ->
            pure
                (Tptp.buildAtomicWord
                    target)


renderTh0Term
    :: Ord global
    => NameEnvironment ref local global
    -> [BoundTarget]
    -> CanonicalTerm global
    -> Render ref local global TextBuilder
renderTh0Term names bounds = \case
    CBound index ->
        renderBound index bounds
    CGlobal global ->
        Tptp.buildAtomicWord
            <$> lookupGlobal names global
    CIntrinsic intrinsic ->
        Tptp.buildAtomicWord
            <$> lookupIntrinsic names intrinsic
    CLogicalSelect coreType ->
        Tptp.buildAtomicWord
            <$> lookupLogicalSelection names coreType
    COpaqueInteger integer ->
        Tptp.buildAtomicWord
            <$> lookupInteger names integer
    CApp function argument -> do
        function' <-
            renderTh0Term names bounds function
        argument' <-
            renderTh0Term names bounds argument
        pure
            (parenthesize
                (function'
                    <> char '@'
                    <> argument'))
    CLam binderType body -> do
        variable <-
            freshBinder
        body' <-
            renderTh0Term
                names
                (BoundTh0Variable variable
                    : bounds)
                body
        pure
            (parenthesize
                (text "^ ["
                    <> Tptp.buildVariable variable
                    <> char ':'
                    <> renderCoreType binderType
                    <> text "] : "
                    <> body'))
    CFalsum ->
        pure (text "$false")
    CTruth ->
        pure (text "$true")
    CNot proposition -> do
        proposition' <-
            renderTh0Term names bounds proposition
        pure (parenthesize (char '~' <> proposition'))
    CAnd left right -> do
        left' <- renderTh0Term names bounds left
        right' <- renderTh0Term names bounds right
        pure (vampireConjunction left' right')
    COr left right -> do
        left' <- renderTh0Term names bounds left
        right' <- renderTh0Term names bounds right
        pure (vampireDisjunction left' right')
    CImp premise conclusion -> do
        premise' <-
            renderTh0Term names bounds premise
        conclusion' <-
            renderTh0Term names bounds conclusion
        pure
            (parenthesize
                (premise'
                    <> text "=>"
                    <> conclusion'))
    CEq operandType left right -> do
        left' <-
            renderTh0Term names bounds left
        right' <-
            renderTh0Term names bounds right
        pure
            (parenthesize
                (left'
                    <> (case operandType of
                        TyProp -> text "<=>"
                        _ -> char '=')
                    <> right'))
    CForall binderType body -> do
        variable <-
            freshBinder
        body' <-
            renderTh0Term
                names
                (BoundTh0Variable variable
                    : bounds)
                body
        pure
            (parenthesize
                (text "! ["
                    <> Tptp.buildVariable variable
                    <> char ':'
                    <> renderCoreType binderType
                    <> text "] : "
                    <> body'))
    CExists binderType body -> do
        variable <-
            freshBinder
        body' <-
            renderTh0Term
                names
                (BoundTh0Variable variable
                    : bounds)
                body
        pure
            (parenthesize
                (text "? ["
                    <> Tptp.buildVariable variable
                    <> char ':'
                    <> renderCoreType binderType
                    <> text "] : "
                    <> body'))

renderTh0Declarations
    :: (Ord local, Ord global)
    => NameEnvironment ref local global
    -> TypedProblem ref local origin global
    -> Render ref local global [TextBuilder]
renderTh0Declarations names problem = do
    globalDeclarations <-
        traverse
            (\(ordinal, (global, coreType)) -> do
                target <-
                    lookupGlobal names global
                label <-
                    liftEither
                        (generatedAtomicWord
                            ("tg_g_type_"
                                <> Text.pack
                                    (show ordinal)))
                pure
                    (typeDeclaration
                        label
                        target
                        (renderCoreType coreType)))
            (zip [0 :: Int ..]
                (Map.toAscList
                    (typedProblemGlobalTypes
                        problem)))
    localDeclarations <-
        traverse
            (\(ordinal, (local, coreType)) -> do
                target <-
                    lookupLocal names local
                label <-
                    liftEither
                        (generatedAtomicWord
                            ("tg_l_type_"
                                <> Text.pack
                                    (show ordinal)))
                pure
                    (typeDeclaration
                        label
                        target
                        (renderCoreType coreType)))
            (zip [0 :: Int ..]
                (Map.toAscList
                    (typedProblemLocalTypes
                        problem)))
    intrinsicDeclarations <-
        traverse
            (\(ordinal, intrinsic) -> do
                target <-
                    lookupIntrinsic names intrinsic
                label <-
                    liftEither
                        (generatedAtomicWord
                            ("tg_i_type_"
                                <> Text.pack
                                    (show ordinal)))
                pure
                    (typeDeclaration
                        label
                        target
                        (renderCoreType
                            (coreIntrinsicType
                                intrinsic))))
            (zip [0 :: Int ..]
                (Set.toAscList
                    (problemIntrinsics problem)))
    logicalSelectionDeclarations <-
        traverse
            (\(ordinal, auxiliary) -> do
                let coreType =
                        typedLogicalSelectionAuxiliaryType auxiliary
                target <-
                    lookupLogicalSelection names coreType
                label <-
                    liftEither
                        (generatedAtomicWord
                            ("tg_s_type_"
                                <> Text.pack
                                    (show ordinal)))
                pure
                    (typeDeclaration
                        label
                        target
                        (renderCoreType
                            (logicalSelectionType coreType))))
            (zip [0 :: Int ..]
                (Vector.toList
                    (typedProblemLogicalSelections problem)))
    integerDeclarations <-
        traverse
            (\(ordinal, integer) -> do
                target <-
                    lookupInteger names integer
                label <-
                    liftEither
                        (generatedAtomicWord
                            ("tg_n_type_"
                                <> Text.pack
                                    (show ordinal)))
                pure
                    (typeDeclaration
                        label
                        target
                        (renderCoreType TySet)))
            (zip [0 :: Int ..]
                (Set.toAscList
                    (problemIntegers problem)))
    pure
        (globalDeclarations
            <> localDeclarations
            <> intrinsicDeclarations
            <> logicalSelectionDeclarations
            <> integerDeclarations)

typeDeclaration
    :: Tptp.AtomicWord
    -> Tptp.AtomicWord
    -> TextBuilder
    -> TextBuilder
typeDeclaration label target coreType =
    text "thf("
        <> Tptp.buildAtomicWord label
        <> text ",type,("
        <> Tptp.buildAtomicWord target
        <> char ':'
        <> coreType
        <> text "))."

renderCoreType :: CoreType -> TextBuilder
renderCoreType = \case
    TyProp ->
        text "$o"
    TySet ->
        text "$i"
    TyArrow argument result ->
        parenthesize
            (renderCoreType argument
                <> char '>'
                <> renderCoreType result)

-- Vampire's 5.0.1 and 5.1.0 CASC portfolios are pathologically sensitive to
-- native Boolean presentation in the library's generated obligations.
-- Normalizing conjunction and disjunction avoids severe regressions in both
-- FOF and TH0.
-- These classically equivalent builders tune only the prover presentation:
-- checked Core and kernel replay retain their native logical nodes.
vampireConjunction :: TextBuilder -> TextBuilder -> TextBuilder
vampireConjunction left right =
    parenthesize
        (parenthesize
            (left
                <> text "=>"
                <> parenthesize
                    (right
                        <> text "=>$false"))
            <> text "=>$false")

vampireDisjunction :: TextBuilder -> TextBuilder -> TextBuilder
vampireDisjunction left right =
    parenthesize
        (parenthesize
            (left
                <> text "=>$false")
            <> text "=>"
            <> right)

parenthesize :: TextBuilder -> TextBuilder
parenthesize builder =
    char '(' <> builder <> char ')'


lookupGlobal
    :: Ord global
    => NameEnvironment ref local global
    -> global
    -> Render ref local global Tptp.AtomicWord
lookupGlobal names global =
    maybe
        (lift
            (Left
                (TypedTptpUnknownGlobal
                    global)))
        pure
        (lookupGlobalPure names global)

lookupGlobalPure
    :: Ord global
    => NameEnvironment ref local global
    -> global
    -> Maybe Tptp.AtomicWord
lookupGlobalPure
        (NameEnvironment
            globals
            _globalTypes
            _locals
            _intrinsics
            _logicalSelections
            _integers
            _origins) =
    (`Map.lookup` globals)

lookupLocalPure
    :: Ord local
    => NameEnvironment ref local global
    -> local
    -> Maybe Tptp.AtomicWord
lookupLocalPure
        (NameEnvironment
            _globals
            _globalTypes
            locals
            _intrinsics
            _logicalSelections
            _integers
            _origins) =
    (`Map.lookup` locals)

lookupLocal
    :: Ord local
    => NameEnvironment ref local global
    -> local
    -> Render ref local global Tptp.AtomicWord
lookupLocal names local =
    maybe
        (lift
            (Left
                (TypedTptpUnknownLocal
                    local)))
        pure
        (lookupLocalPure names local)

lookupIntrinsic
    :: NameEnvironment ref local global
    -> CoreIntrinsicTag
    -> Render ref local global Tptp.AtomicWord
lookupIntrinsic names intrinsic =
    maybe
        (lift
            (Left
                TypedTptpFofProjectionMismatch))
        pure
        (lookupIntrinsicPure names intrinsic)

lookupIntrinsicPure
    :: NameEnvironment ref local global
    -> CoreIntrinsicTag
    -> Maybe Tptp.AtomicWord
lookupIntrinsicPure
        (NameEnvironment
            _globals
            _globalTypes
            _locals
            intrinsics
            _logicalSelections
            _integers
            _origins) =
    (`Map.lookup` intrinsics)

lookupLogicalSelection
    :: NameEnvironment ref local global
    -> CoreType
    -> Render ref local global Tptp.AtomicWord
lookupLogicalSelection names coreType =
    maybe
        (lift
            (Left
                TypedTptpFofProjectionMismatch))
        pure
        (lookupLogicalSelectionPure names coreType)

lookupLogicalSelectionPure
    :: NameEnvironment ref local global
    -> CoreType
    -> Maybe Tptp.AtomicWord
lookupLogicalSelectionPure
        (NameEnvironment
            _globals
            _globalTypes
            _locals
            _intrinsics
            logicalSelections
            _integers
            _origins) =
    (`Map.lookup` logicalSelections)

lookupInteger
    :: NameEnvironment ref local global
    -> Integer
    -> Render ref local global Tptp.AtomicWord
lookupInteger names integer =
    maybe
        (lift
            (Left
                TypedTptpFofProjectionMismatch))
        pure
        (lookupIntegerPure names integer)

lookupIntegerPure
    :: NameEnvironment ref local global
    -> Integer
    -> Maybe Tptp.AtomicWord
lookupIntegerPure
        (NameEnvironment
            _globals
            _globalTypes
            _locals
            _intrinsics
            _logicalSelections
            integers
            _origins) =
    (`Map.lookup` integers)

problemIntrinsics
    :: TypedProblem ref local origin global
    -> Set CoreIntrinsicTag
problemIntrinsics =
    foldMap canonicalIntrinsics
        . problemTerms

problemIntegers
    :: TypedProblem ref local origin global
    -> Set Integer
problemIntegers =
    foldMap canonicalIntegers
        . problemTerms

problemTerms
    :: TypedProblem ref local origin global
    -> [CanonicalTerm global]
problemTerms problem =
    supportedPropositionTerm
        (typedProblemClaim problem)
        : (supportedPropositionTerm
            . typedBackendFactProposition
            <$> Vector.toList
                (typedProblemGlobalPremises
                    problem))
        <> (supportedPropositionTerm
            . typedLocalPremiseProposition
            <$> Vector.toList
                (typedProblemLocalPremises
                    problem))
        <> (supportedPropositionTerm
            . typedProblemAuxiliaryProposition
            <$> Vector.toList
                (typedProblemAuxiliaries
                    problem))
        <> (supportedPropositionTerm
            . typedLogicalSelectionAuxiliaryProposition
            <$> Vector.toList
                (typedProblemLogicalSelections
                    problem))

canonicalIntrinsics
    :: CanonicalTerm global
    -> Set CoreIntrinsicTag
canonicalIntrinsics = \case
    CBound{} ->
        mempty
    CGlobal{} ->
        mempty
    CIntrinsic intrinsic ->
        Set.singleton intrinsic
    CLogicalSelect{} ->
        mempty
    COpaqueInteger{} ->
        mempty
    CApp function argument ->
        canonicalIntrinsics function
            <> canonicalIntrinsics argument
    CLam _binderType body ->
        canonicalIntrinsics body
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        canonicalIntrinsics proposition
    CAnd left right ->
        canonicalIntrinsics left
            <> canonicalIntrinsics right
    COr left right ->
        canonicalIntrinsics left
            <> canonicalIntrinsics right
    CImp premise conclusion ->
        canonicalIntrinsics premise
            <> canonicalIntrinsics conclusion
    CEq _operandType left right ->
        canonicalIntrinsics left
            <> canonicalIntrinsics right
    CForall _binderType body ->
        canonicalIntrinsics body
    CExists _binderType body ->
        canonicalIntrinsics body

canonicalIntegers
    :: CanonicalTerm global
    -> Set Integer
canonicalIntegers = \case
    CBound{} ->
        mempty
    CGlobal{} ->
        mempty
    CIntrinsic{} ->
        mempty
    CLogicalSelect{} ->
        mempty
    COpaqueInteger integer ->
        Set.singleton integer
    CApp function argument ->
        canonicalIntegers function
            <> canonicalIntegers argument
    CLam _binderType body ->
        canonicalIntegers body
    CFalsum ->
        mempty
    CTruth ->
        mempty
    CNot proposition ->
        canonicalIntegers proposition
    CAnd left right ->
        canonicalIntegers left
            <> canonicalIntegers right
    COr left right ->
        canonicalIntegers left
            <> canonicalIntegers right
    CImp premise conclusion ->
        canonicalIntegers premise
            <> canonicalIntegers conclusion
    CEq _operandType left right ->
        canonicalIntegers left
            <> canonicalIntegers right
    CForall _binderType body ->
        canonicalIntegers body
    CExists _binderType body ->
        canonicalIntegers body
