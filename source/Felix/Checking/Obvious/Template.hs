{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked theorem templates with stable matcher slots.  This module is a
-- policy-free structural seam: callers supply a work allowance and decide
-- whether exhaustion belongs to focused or refutation search.
module Felix.Checking.Obvious.Template
    ( MatcherSlot(..)
    , BinderEnvironment
    , emptyBinderEnvironment
    , extendBinderEnvironment
    , binderEnvironmentCount
    , binderEnvironmentSourceTypes
    , binderEnvironmentScopedContext
    , binderEnvironmentAmbientContext
    , binderEnvironmentSlotType
    , CompiledTemplate
    , compiledTemplateTerm
    , compiledTemplateBinderEnvironment
    , TemplateSubstitution
    , emptyTemplateSubstitution
    , lookupTemplateSubstitution
    , insertTemplateSubstitution
    , missingTemplateSlotsCounted
    , TemplateClosure(..)
    , TemplateError(..)
    , retainCheckedPropositionTemplate
    , retainCheckedPropositionTemplateUnder
    , openCompiledForall
    , openCompiledExists
    , openCompiledImplication
    , splitCompiledNegation
    , splitCompiledConjunction
    , splitCompiledDisjunction
    , unsafeRetainResidualizedPropositionTemplate
    , compileTemplate
    , closeTemplate
    , matchTemplateExactly
    , ExactTemplateMatchError(..)
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.Trans.Maybe qualified as Maybe
import Control.Monad.State.Strict qualified as State
import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Word (Word)
import Numeric.Natural (Natural)


-- | Stable source-order index of a theorem binder.
newtype MatcherSlot = MatcherSlot Natural
    deriving stock (Show, Eq, Ord)

-- | One immutable removable binder prefix over a fixed ambient context.
-- Source-order lookup and nearest-first Core checking need opposite views, so
-- both are maintained at constant cost when a checked logical binder opens.
data BinderEnvironment = BinderEnvironment
    !Natural
    !(Seq CoreType)
    ![CoreType]
    ![CoreType]

emptyBinderEnvironment :: [CoreType] -> BinderEnvironment
emptyBinderEnvironment ambient =
    BinderEnvironment 0 Seq.empty ambient ambient

extendBinderEnvironment
    :: CoreType
    -> BinderEnvironment
    -> BinderEnvironment
extendBinderEnvironment binderType
        (BinderEnvironment count sourceTypes scoped ambient) =
    BinderEnvironment
        (count + 1)
        (sourceTypes Seq.|> binderType)
        (binderType : scoped)
        ambient

binderEnvironmentCount :: BinderEnvironment -> Natural
binderEnvironmentCount (BinderEnvironment count _types _scoped _ambient) =
    count

binderEnvironmentSourceTypes :: BinderEnvironment -> Seq CoreType
binderEnvironmentSourceTypes
        (BinderEnvironment _count sourceTypes _scoped _ambient) =
    sourceTypes

binderEnvironmentScopedContext :: BinderEnvironment -> [CoreType]
binderEnvironmentScopedContext
        (BinderEnvironment _count _types scoped _ambient) =
    scoped

binderEnvironmentAmbientContext :: BinderEnvironment -> [CoreType]
binderEnvironmentAmbientContext
        (BinderEnvironment _count _types _scoped ambient) =
    ambient

binderEnvironmentSlotType
    :: MatcherSlot
    -> BinderEnvironment
    -> Maybe CoreType
binderEnvironmentSlotType (MatcherSlot position)
        (BinderEnvironment count sourceTypes _scoped _ambient)
    | position < count = Seq.lookup (fromIntegral position) sourceTypes
    | otherwise = Nothing

-- | A checked proposition underneath a known source-ordered removable binder
-- prefix. The checked value retains the reverse binder stack required by de
-- Bruijn scope. Rule matching is the only client which interprets supported
-- leading universal positions as 'MatcherSlot's.
data CompiledTemplate global = CompiledTemplate
    { compiledTemplateTerm :: !(ScopedCheckedCore global)
    , compiledTemplateBinderEnvironment :: !BinderEnvironment
    }

-- Recursive Core values are payloads, never map keys.
newtype TemplateSubstitution global = TemplateSubstitution
    (Map.Map Natural (ScopedCheckedCore global))

emptyTemplateSubstitution :: TemplateSubstitution global
emptyTemplateSubstitution =
    TemplateSubstitution Map.empty

lookupTemplateSubstitution
    :: MatcherSlot
    -> TemplateSubstitution global
    -> Maybe (ScopedCheckedCore global)
lookupTemplateSubstitution (MatcherSlot slot) (TemplateSubstitution substitutions) =
    Map.lookup slot substitutions

insertTemplateSubstitution
    :: MatcherSlot
    -> ScopedCheckedCore global
    -> TemplateSubstitution global
    -> TemplateSubstitution global
insertTemplateSubstitution (MatcherSlot slot) value
        (TemplateSubstitution substitutions) =
    TemplateSubstitution (Map.insert slot value substitutions)

missingTemplateSlotsCounted
    :: Word
    -> BinderEnvironment
    -> TemplateSubstitution global
    -> (Either (CountedCoreFailure Void) [MatcherSlot], Word)
missingTemplateSlotsCounted remaining environment substitutions =
    go remaining 0 (Seq.viewl (binderEnvironmentSourceTypes environment))
  where
    go available _position Seq.EmptyL = (Right [], available)
    go 0 _position _remaining =
        (Left CountedCoreStructuralWorkExhausted, 0)
    go available position (_coreType Seq.:< rest) =
        let slot = MatcherSlot position
            missingHere =
                isNothing (lookupTemplateSubstitution slot substitutions)
        in missingHere `seq`
            case go (available - 1) (position + 1) (Seq.viewl rest) of
                (Left failure, afterRest) -> (Left failure, afterRest)
                (Right missing, afterRest) ->
                    ( Right
                        (if missingHere then slot : missing else missing)
                    , afterRest
                    )

data TemplateClosure global
    = TemplateClosed !(ScopedCheckedCore global)
    | TemplateOpen
        !(CompiledTemplate global)
        !(TemplateSubstitution global)
        !(Set Natural)

data TemplateError
    = TemplateCheckFailed !CoreCheckError
    | TemplateExpectedProposition !CoreType
    | TemplateInstantiationFailed !ScopedInstantiationError
    | TemplateContextMismatch ![CoreType] ![CoreType]
    deriving stock (Show, Eq)

-- | Attach the empty matcher environment determined by an already checked
-- proposition itself. This is the entry point for a prepared rule source;
-- no recursive Core check is repeated.
retainCheckedPropositionTemplate
    :: ScopedCheckedCore global
    -> Either TemplateError (CompiledTemplate global)
retainCheckedPropositionTemplate checked =
    case scopedCoreType checked of
        TyProp ->
            Right
                (CompiledTemplate checked
                    (emptyBinderEnvironment (scopedCoreContext checked)))
        other -> Left (TemplateExpectedProposition other)

retainCheckedPropositionTemplateUnder
    :: Word
    -> BinderEnvironment
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure TemplateError) (CompiledTemplate global), Word)
retainCheckedPropositionTemplateUnder remaining environment checked =
    case countedCoreTypeListIdentity remaining
            (binderEnvironmentScopedContext environment) (scopedCoreContext checked) of
        (Left failure, after) -> (Left (absurd <$> failure), after)
        (Right False, after) -> (Left (CountedCoreOperationFailed
            (TemplateContextMismatch (binderEnvironmentScopedContext environment)
                (scopedCoreContext checked))), after)
        (Right True, after) -> case scopedCoreType checked of
            TyProp -> (Right (CompiledTemplate checked environment), after)
            other -> (Left (CountedCoreOperationFailed
                (TemplateExpectedProposition other)), after)

-- | Open a checked leading universal and extend the template environment in
-- lockstep with Core's checked binder context.
openCompiledForall
    :: CompiledTemplate global
    -> Maybe (CoreType, CompiledTemplate global)
openCompiledForall (CompiledTemplate checked environment) = do
    (binderType, body) <- openScopedForall checked
    pure
        ( binderType
        , CompiledTemplate body
            (extendBinderEnvironment binderType environment)
        )

-- | Open a checked leading existential and extend the removable binder scope.
openCompiledExists
    :: CompiledTemplate global
    -> Maybe (CoreType, CompiledTemplate global)
openCompiledExists (CompiledTemplate checked environment) = do
    (binderType, body) <- openScopedExists checked
    pure
        ( binderType
        , CompiledTemplate body
            (extendBinderEnvironment binderType environment)
        )

-- | Open a checked implication without rechecking either proposition child.
openCompiledImplication
    :: CompiledTemplate global
    -> Maybe
        ( CompiledTemplate global
        , CompiledTemplate global
        )
openCompiledImplication (CompiledTemplate checked environment) = do
    (premise, conclusion) <- openScopedImplication checked
    pure
        ( CompiledTemplate premise environment
        , CompiledTemplate conclusion environment
        )

splitCompiledNegation
    :: CompiledTemplate global
    -> Maybe (CompiledTemplate global)
splitCompiledNegation (CompiledTemplate checked environment) =
    (`CompiledTemplate` environment) <$> splitScopedNegation checked

splitCompiledConjunction
    :: CompiledTemplate global
    -> Maybe
        ( CompiledTemplate global
        , CompiledTemplate global
        )
splitCompiledConjunction (CompiledTemplate checked environment) = do
    (left, right) <- splitScopedConjunction checked
    pure
        ( CompiledTemplate left environment
        , CompiledTemplate right environment
        )

splitCompiledDisjunction
    :: CompiledTemplate global
    -> Maybe
        ( CompiledTemplate global
        , CompiledTemplate global
        )
splitCompiledDisjunction (CompiledTemplate checked environment) = do
    (left, right) <- splitScopedDisjunction checked
    pure
        ( CompiledTemplate left environment
        , CompiledTemplate right environment
        )

-- | Retain the immediate successful head residual of this exact template.
-- The caller must obtain the second argument by residualizing the first
-- argument's checked term. Conversion has already preserved type and context;
-- retain its binder environment without another check or comparison.
unsafeRetainResidualizedPropositionTemplate
    :: CompiledTemplate global
    -> ScopedCheckedCore global
    -> CompiledTemplate global
unsafeRetainResidualizedPropositionTemplate (CompiledTemplate _original environment) residual =
    CompiledTemplate residual environment

-- | Check a typed template under the reverse de Bruijn binder prefix.  Binder
-- types are retained in source order for stable matcher-slot lookup.
compileTemplate
    :: GlobalTyping global
    -> Word
    -> BinderEnvironment
    -> CanonicalTerm global
    -> ( Either
            (CountedCoreFailure TemplateError)
            (CompiledTemplate global)
       , Word
       )
compileTemplate globalType remaining environment term =
    case countedCheckScopedCanonicalCore
            globalType
            remaining
            (binderEnvironmentScopedContext environment)
            term of
        (Left failure, afterCheck) ->
            (Left (TemplateCheckFailed <$> failure), afterCheck)
        (Right checked, afterCheck) ->
            ( Right
                (CompiledTemplate checked environment)
            , afterCheck
            )

-- | Close the checked template with its own lexical prefix. Core validates the
-- substitution premises and preserves typing; its caller owns input admission.
closeTemplate
    :: Word
    -> CompiledTemplate global
    -> TemplateSubstitution global
    -> (Either (CountedCoreFailure TemplateError) (TemplateClosure global), Word)
closeTemplate remaining template substitutions@(TemplateSubstitution replacements) =
    case countedInstantiateScopedPrefix remaining
            (binderEnvironmentCount (compiledTemplateBinderEnvironment template))
            replacements (compiledTemplateTerm template) of
        (Left failure, afterClosure) ->
            (Left (TemplateInstantiationFailed <$> failure), afterClosure)
        (Right (ScopedInstantiationClosed checked), afterClosure) ->
            (Right (TemplateClosed checked), afterClosure)
        (Right (ScopedInstantiationOpen unresolved), afterClosure) ->
            ( Right (TemplateOpen template substitutions unresolved)
            , afterClosure
            )

data ExactTemplateMatchError
    = TemplateOccurrenceAnalysisFailed !CheckedOccurrenceAnalysisError
    | TemplateOccurrenceRebaseFailed !CheckedOccurrenceRebaseError
    deriving stock (Show, Eq)

-- | Syntactic matching of a checked removable prefix against a scoped target.
-- Only target subterms can fill slots. Repeated occurrences must agree exactly,
-- and a subterm depending on a target-local binder cannot escape into a slot.
-- No conversion, candidate generation, or missing-slot completion occurs here.
matchTemplateExactly
    :: Eq global
    => GlobalTyping global
    -> Word
    -> CompiledTemplate global
    -> ScopedCheckedCore global
    -> (Either (CountedCoreFailure ExactTemplateMatchError) (Maybe (TemplateSubstitution global)), Word)
matchTemplateExactly typing work template target =
    State.runState (Except.runExceptT (Maybe.runMaybeT match)) work
  where
    environment = compiledTemplateBinderEnvironment template
    count = binderEnvironmentCount environment
    match = do
        sameContext <- exact (\remaining -> countedCoreTypeListIdentity remaining
            (binderEnvironmentAmbientContext environment) (scopedCoreContext target))
        guard sameContext
        if count == 0
            then do
                same <- exact (\remaining -> countedScopedCoreIdentity remaining
                    (compiledTemplateTerm template) target)
                guard same
                pure emptyTemplateSubstitution
            else do
                root <- operation TemplateOccurrenceAnalysisFailed
                    (\remaining -> countedAnalyseScopedOccurrencesUnderBinders typing remaining 0 target)
                go 0 (scopedCoreTerm (compiledTemplateTerm template)) root emptyTemplateSubstitution

    go depth patternTerm found substitutions = do
        debit
        let view = checkedOccurrenceView found
            atomic expected = do
                same <- exact (\remaining -> countedCanonicalIdentity remaining expected
                    (scopedCoreTerm (checkedOccurrenceScopedCore found)))
                guard same
                pure substitutions
            pair left foundLeft right foundRight = do
                updated <- go depth left foundLeft substitutions
                go depth right foundRight updated
            binder binderType body foundType foundBody = do
                same <- exact (\remaining -> countedCoreTypeIdentity remaining binderType foundType)
                guard same
                go (depth + 1) body foundBody substitutions
        case patternTerm of
            CBound index
                | index < depth -> atomic (CBound index)
                | index < depth + count -> do
                    candidate <- operation TemplateOccurrenceRebaseFailed
                        (\remaining -> countedRebaseCheckedOccurrence remaining found)
                        >>= Maybe.MaybeT . pure
                    let slot = MatcherSlot (count - (index - depth) - 1)
                    expected <- Maybe.MaybeT (pure (binderEnvironmentSlotType slot environment))
                    sameType <- exact (\remaining -> countedCoreTypeIdentity remaining expected
                        (scopedCoreType candidate))
                    guard sameType
                    case lookupTemplateSubstitution slot substitutions of
                        Nothing -> pure (insertTemplateSubstitution slot candidate substitutions)
                        Just previous -> do
                            same <- exact (\remaining -> countedScopedCoreIdentity remaining previous candidate)
                            guard same
                            pure substitutions
                | otherwise -> atomic (CBound (index - count))
            CGlobal identity -> atomic (CGlobal identity)
            CIntrinsic intrinsic -> atomic (CIntrinsic intrinsic)
            CLogicalSelect coreType -> atomic (CLogicalSelect coreType)
            COpaqueInteger integer -> atomic (COpaqueInteger integer)
            CApp function argument -> case view of
                OccurrenceApplication foundFunction foundArgument ->
                    pair function foundFunction argument foundArgument
                _ -> empty
            CLam coreType body -> case view of
                OccurrenceLambda foundType foundBody -> binder coreType body foundType foundBody
                _ -> empty
            CFalsum -> atomic CFalsum
            CTruth -> atomic CTruth
            CNot child -> case view of
                OccurrenceNegation foundChild -> go depth child foundChild substitutions
                _ -> empty
            CAnd left right -> case view of
                OccurrenceConjunction foundLeft foundRight -> pair left foundLeft right foundRight
                _ -> empty
            COr left right -> case view of
                OccurrenceDisjunction foundLeft foundRight -> pair left foundLeft right foundRight
                _ -> empty
            CImp premise conclusion -> case view of
                OccurrenceImplication foundPremise foundConclusion -> pair premise foundPremise conclusion foundConclusion
                _ -> empty
            CEq coreType left right -> case view of
                OccurrenceEquality foundType foundLeft foundRight -> do
                    same <- exact (\remaining -> countedCoreTypeIdentity remaining coreType foundType)
                    guard same
                    pair left foundLeft right foundRight
                _ -> empty
            CForall coreType body -> case view of
                OccurrenceUniversal foundType foundBody -> binder coreType body foundType foundBody
                _ -> empty
            CExists coreType body -> case view of
                OccurrenceExistential foundType foundBody -> binder coreType body foundType foundBody
                _ -> empty

    debit = operation id \remaining ->
        if remaining == 0 then (Left CountedCoreStructuralWorkExhausted, 0)
            else (Right (), remaining - 1)
    exact action = operation absurd action
    operation failure action = lift do
        remaining <- lift State.get
        let (result, after) = action remaining
        lift (State.put after)
        Except.ExceptT (pure (first (fmap failure) result))
