{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden linear lifecycle controller for stable-local construction. Public
-- clients use the pure facade in "Felix.Checking.Core.Resolved".
module Felix.Checking.Core.Resolved.Internal
    ( LocalRef
    , CheckedExpr
    , CoreBuilder
    , CoreBuilderError(..)
    , checkedExprType
    , localRefType
    , runClosedBuilder
    , useLocal
    , useGlobal
    , embedClosed
    , intrinsic
    , apply
    , lambda
    , falsum
    , negation
    , conjunction
    , disjunction
    , forAll
    , exists
    , imply
    , equality
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
    ( CoreCheckError
    , CoreIntrinsicTag
    , CoreType
    , FrozenCheckedCore
    , admitFrozenCheckedCore
    )
import Felix.Checking.Core.Resolved.Substrate.Internal
    ( CheckedExpr
    , LocalRef
    , ScopeId
    , checkedExprOwnerInternal
    , checkedExprType
    , localRefScopeInternal
    , localRefType
    , scopeOrdinalInternal
    )
import Felix.Checking.Core.Resolved.Substrate.Internal qualified as Substrate
import Felix.Checking.GlobalTyping (GlobalTyping)

import Control.Monad.Reader qualified as Reader
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Class qualified as Trans
import Data.IntSet qualified as IntSet


newtype RootFrame region = RootFrame
    { rootFrameScope :: ScopeId region
    }

newtype BinderFrame region = BinderFrame
    { binderFrameLocal :: LocalRef region
    }

data ActivePath region = ActivePath
    { activeRoot :: !(RootFrame region)
    , activeBinders :: ![BinderFrame region]
    , activeScopeIndex :: !IntSet.IntSet
    }

type role BuilderState nominal
data BuilderState region = BuilderState
    { builderActivePath :: !(ActivePath region)
    , nextScopeId :: !Int
    , nextLocalId :: !Int
    }

type role CoreBuilderError nominal
data CoreBuilderError global
    = CoreBuilderCheckError !CoreCheckError
    | CoreBuilderInactiveLocal
    | CoreBuilderInactiveExpression
    | CoreBuilderGlobalNotVisible !global
    | CoreBuilderCheckedIngressRejected !CoreCheckError
    | CoreBuilderIdentityExhausted
    | CoreBuilderActivePathInvariant
    | CoreBuilderResolvedFreezeInvariant
    deriving stock (Show, Eq)

type role CoreBuilder nominal nominal nominal
newtype CoreBuilder region global value = CoreBuilder
    { unCoreBuilder
        :: State.StateT
            (BuilderState region)
            (Reader.ReaderT
                (GlobalTyping global)
                (Either (CoreBuilderError global)))
            value
    }
    deriving newtype (Functor, Applicative, Monad)

runClosedBuilder
    :: GlobalTyping global
    -> (forall region.
            CoreBuilder region global
                (CheckedExpr region global))
    -> Either
        (CoreBuilderError global)
        (FrozenCheckedCore global)
runClosedBuilder globalTyping build =
    Reader.runReaderT
        (State.evalStateT
            (unCoreBuilder (build >>= freezeClosedInternal))
            initialBuilderState)
        globalTyping

initialBuilderState :: BuilderState region
initialBuilderState =
    BuilderState
        { builderActivePath =
            initialActivePath
                (Substrate.scopeIdFromOrdinalInternal 0)
        , nextScopeId = 1
        , nextLocalId = 0
        }

initialActivePath :: ScopeId region -> ActivePath region
initialActivePath root =
    ActivePath
        { activeRoot = RootFrame root
        , activeBinders = []
        , activeScopeIndex =
            IntSet.singleton (scopeOrdinalInternal root)
        }

useLocal
    :: LocalRef region
    -> CoreBuilder region global
        (CheckedExpr region global)
useLocal localRef = do
    state <- getBuilderState
    let path = builderActivePath state
    if scopeIsActive (localRefScopeInternal localRef) path
        then
            pure
                (Substrate.makeLocalExprInternal
                    (currentActiveScope path)
                    localRef)
        else
            throwBuilder CoreBuilderInactiveLocal

useGlobal
    :: global
    -> CoreBuilder region global
        (CheckedExpr region global)
useGlobal global = do
    globalTyping <- getGlobalTyping
    owner <- getCurrentScope
    case Substrate.makeGlobalExprInternal globalTyping owner global of
        Nothing ->
            throwBuilder (CoreBuilderGlobalNotVisible global)
        Just checked ->
            pure checked

embedClosed
    :: Ord global
    => FrozenCheckedCore global
    -> CoreBuilder region global
        (CheckedExpr region global)
embedClosed frozen = do
    globalTyping <- getGlobalTyping
    admitted <-
        case admitFrozenCheckedCore globalTyping frozen of
            Left cause ->
                throwBuilder (CoreBuilderCheckedIngressRejected cause)
            Right checked ->
                pure checked
    owner <- getCurrentScope
    pure (Substrate.makeEmbeddedExprInternal owner admitted)

intrinsic
    :: CoreIntrinsicTag
    -> CoreBuilder region global
        (CheckedExpr region global)
intrinsic i = do
    owner <- getCurrentScope
    pure (Substrate.makeIntrinsicExprInternal owner i)

apply
    :: CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
apply function argument = do
    ensureExprActive function
    ensureExprActive argument
    owner <- getCurrentScope
    liftCheck
        (Substrate.makeApplicationExprInternal
            owner
            function
            argument)

lambda
    :: CoreType
    -> (LocalRef region
        -> CoreBuilder region global
            (CheckedExpr region global))
    -> CoreBuilder region global
        (CheckedExpr region global)
lambda binderType =
    withBinderInternal
        binderType
        (\owner localRef body ->
            Right
                (Substrate.makeLambdaExprInternal
                    owner
                    localRef
                    body))

falsum
    :: CoreBuilder region global
        (CheckedExpr region global)
falsum = do
    owner <- getCurrentScope
    pure (Substrate.makeFalsumExprInternal owner)

negation
    :: CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
negation proposition = do
    ensureExprActive proposition
    owner <- getCurrentScope
    liftCheck
        (Substrate.makeNegationExprInternal owner proposition)

conjunction
    :: CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
conjunction =
    checkedBinaryInternal Substrate.makeConjunctionExprInternal

disjunction
    :: CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
disjunction =
    checkedBinaryInternal Substrate.makeDisjunctionExprInternal

forAll
    :: CoreType
    -> (LocalRef region
        -> CoreBuilder region global
            (CheckedExpr region global))
    -> CoreBuilder region global
        (CheckedExpr region global)
forAll binderType =
    withBinderInternal
        binderType
        Substrate.makeForallExprInternal

exists
    :: CoreType
    -> (LocalRef region
        -> CoreBuilder region global
            (CheckedExpr region global))
    -> CoreBuilder region global
        (CheckedExpr region global)
exists binderType =
    withBinderInternal
        binderType
        Substrate.makeExistsExprInternal

imply
    :: CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
imply =
    checkedBinaryInternal Substrate.makeImplicationExprInternal

equality
    :: CoreType
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
equality operandType left right = do
    ensureExprActive left
    ensureExprActive right
    owner <- getCurrentScope
    liftCheck
        (Substrate.makeEqualityExprInternal
            owner
            operandType
            left
            right)

checkedBinaryInternal
    :: (ScopeId region
        -> CheckedExpr region global
        -> CheckedExpr region global
        -> Either CoreCheckError (CheckedExpr region global))
    -> CheckedExpr region global
    -> CheckedExpr region global
    -> CoreBuilder region global
        (CheckedExpr region global)
checkedBinaryInternal construct left right = do
    ensureExprActive left
    ensureExprActive right
    owner <- getCurrentScope
    liftCheck (construct owner left right)

withBinderInternal
    :: CoreType
    -> (ScopeId region
        -> LocalRef region
        -> CheckedExpr region global
        -> Either CoreCheckError (CheckedExpr region global))
    -> (LocalRef region
        -> CoreBuilder region global
            (CheckedExpr region global))
    -> CoreBuilder region global
        (CheckedExpr region global)
withBinderInternal binderType construct callback = do
    localRef <- enterLocalScope binderType
    body <- callback localRef
    ensureExprActive body
    state <- getBuilderState
    parent <-
        case parentAfterCurrentBinder
                localRef
                (builderActivePath state) of
            Nothing ->
                throwBuilder CoreBuilderActivePathInvariant
            Just scope ->
                pure scope
    result <- liftCheck (construct parent localRef body)
    actualParent <- leaveLocalScope localRef
    if actualParent == parent
        then pure result
        else throwBuilder CoreBuilderActivePathInvariant

enterLocalScope
    :: CoreType
    -> CoreBuilder region global
        (LocalRef region)
enterLocalScope binderType = do
    state <- getBuilderState
    newLocalSupply <- incrementSupply (nextLocalId state)
    newScopeSupply <- incrementSupply (nextScopeId state)
    let local =
            Substrate.localIdFromOrdinalInternal (nextLocalId state)
        child =
            Substrate.scopeIdFromOrdinalInternal (nextScopeId state)
        localRef =
            Substrate.makeLocalRefInternal child local binderType
        state' =
            state
                { builderActivePath =
                    pushBinderFrame
                        (BinderFrame localRef)
                        (builderActivePath state)
                , nextScopeId = newScopeSupply
                , nextLocalId = newLocalSupply
                }
    putBuilderState state'
    pure localRef

leaveLocalScope
    :: LocalRef region
    -> CoreBuilder region global (ScopeId region)
leaveLocalScope localRef = do
    state <- getBuilderState
    case popBinderFrame localRef (builderActivePath state) of
        Nothing -> throwBuilder CoreBuilderActivePathInvariant
        Just path -> do
            putBuilderState (state {builderActivePath = path})
            pure (currentActiveScope path)

pushBinderFrame
    :: BinderFrame region
    -> ActivePath region
    -> ActivePath region
pushBinderFrame frame path =
    path
        { activeBinders = frame : activeBinders path
        , activeScopeIndex =
            IntSet.insert
                (scopeOrdinalInternal
                    (localRefScopeInternal
                        (binderFrameLocal frame)))
                (activeScopeIndex path)
        }

popBinderFrame
    :: LocalRef region
    -> ActivePath region
    -> Maybe (ActivePath region)
popBinderFrame expected path =
    case activeBinders path of
        frame : remaining
            | let actual = binderFrameLocal frame
            , sameLocalRef expected actual
            , let child = localRefScopeInternal actual
            , scopeOrdinalInternal child
                `IntSet.member` activeScopeIndex path ->
                    Just
                        path
                            { activeBinders = remaining
                            , activeScopeIndex =
                                IntSet.delete
                                    (scopeOrdinalInternal child)
                                    (activeScopeIndex path)
                            }
        _ -> Nothing

parentAfterCurrentBinder
    :: LocalRef region
    -> ActivePath region
    -> Maybe (ScopeId region)
parentAfterCurrentBinder expected path =
    case activeBinders path of
        frame : parent : _remaining
            | sameLocalRef expected (binderFrameLocal frame) ->
                Just (localRefScopeInternal (binderFrameLocal parent))
        [frame]
            | sameLocalRef expected (binderFrameLocal frame) ->
                Just (rootFrameScope (activeRoot path))
        _ ->
            Nothing

currentActiveScope :: ActivePath region -> ScopeId region
currentActiveScope path =
    case activeBinders path of
        frame : _remaining ->
            localRefScopeInternal (binderFrameLocal frame)
        [] -> rootFrameScope (activeRoot path)

scopeIsActive :: ScopeId region -> ActivePath region -> Bool
scopeIsActive scope path =
    scopeOrdinalInternal scope `IntSet.member` activeScopeIndex path

sameLocalRef :: LocalRef region -> LocalRef region -> Bool
sameLocalRef left right =
    localRefScopeInternal left == localRefScopeInternal right

incrementSupply
    :: Int
    -> CoreBuilder region global Int
incrementSupply current
    | current == maxBound =
        throwBuilder CoreBuilderIdentityExhausted
    | otherwise =
        pure (current + 1)

ensureExprActive
    :: CheckedExpr region global
    -> CoreBuilder region global ()
ensureExprActive checked = do
    state <- getBuilderState
    if scopeIsActive
            (checkedExprOwnerInternal checked)
            (builderActivePath state)
        then pure ()
        else throwBuilder CoreBuilderInactiveExpression

getCurrentScope :: CoreBuilder region global (ScopeId region)
getCurrentScope =
    currentActiveScope . builderActivePath <$> getBuilderState

freezeClosedInternal
    :: CheckedExpr region global
    -> CoreBuilder region global
        (FrozenCheckedCore global)
freezeClosedInternal checked = do
    ensureExprActive checked
    state <- getBuilderState
    if isClosedRootState state
        then
            case Substrate.freezeClosedExprInternal checked of
                Left _failure ->
                    throwBuilder CoreBuilderResolvedFreezeInvariant
                Right frozen ->
                    pure frozen
        else
            throwBuilder CoreBuilderActivePathInvariant

isClosedRootState :: BuilderState region -> Bool
isClosedRootState state =
    let path = builderActivePath state
        root = rootFrameScope (activeRoot path)
    in null (activeBinders path)
        && activeScopeIndex path
            == IntSet.singleton (scopeOrdinalInternal root)

getBuilderState
    :: CoreBuilder region global (BuilderState region)
getBuilderState =
    CoreBuilder State.get

getGlobalTyping
    :: CoreBuilder region global (GlobalTyping global)
getGlobalTyping =
    CoreBuilder (Trans.lift Reader.ask)

putBuilderState
    :: BuilderState region
    -> CoreBuilder region global ()
putBuilderState state =
    CoreBuilder (State.modify' (const state))

liftCheck
    :: Either CoreCheckError value
    -> CoreBuilder region global value
liftCheck =
    either (throwBuilder . CoreBuilderCheckError) pure

throwBuilder
    :: CoreBuilderError global
    -> CoreBuilder region global value
throwBuilder failure =
    CoreBuilder
        (Trans.lift
            (Reader.ReaderT (const (Left failure))))
