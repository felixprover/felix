{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Checked source semantics for named separation and functional replacement.
--
-- A value of 'NamedSetConstruction' is the sole transient owner of the
-- source decomposition.  Its smart constructors validate the complete
-- telescope and derive one canonical term.  Local views, transparent content,
-- direct extensional facts, and cache-scoped descriptors all consume that
-- same checked value.
module Felix.Checking.SetConstruction
    ( NamedSetConstruction
    , checkedSeparationConstruction
    , checkedFunctionalReplacementConstruction
    , checkedFamilyUnionReplacementConstruction
    , namedSetConstructionTerm
    , namedSetConstructionLocalViews
    , namedSetConstructionClosedBody
    , SetConstructionFoundation
    , setConstructionFoundation
    , checkedFoundationSetConstruction
    , NamedSetConstructionFact
    , namedSetConstructionFactProposition
    , namedSetConstructionFactDescriptor
    , namedSetConstructionObjectFact
    , CheckedRelationalSetConstruction
    , checkedRelationalReplacementConstruction
    , relationalSetConstructionTerm
    , relationalSetConstructionFunctionality
    , relationalSetConstructionClosedFunctionality
    , relationalSetConstructionLocalViews
    , relationalSetConstructionClosedBody
    , RelationalSetConstructionFact
    , relationalSetConstructionFactProposition
    , relationalSetConstructionFactDescriptor
    , relationalSetConstructionObjectFact
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.GlobalTyping
import Felix.Checking.Identity
import Felix.Cache.Codec
    ( CacheDigest
    , encodeCache
    , hashCacheFields
    , putCanonicalTermCache
    , putCoreTypeCache
    )

import Control.Monad (foldM, unless)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)


-- | The exact fixed rows used by the narrow derived extensionality schema.
-- Proof-local construction obtains these rows through the confined foundation
-- lookup; declaration authorization obtains them from 'CheckedFoundation'.
data SetConstructionFoundation = SetConstructionFoundation
    !(FrozenCheckedCore Void)
    !(FrozenCheckedCore Void)
    !(FrozenCheckedCore Void)

setConstructionFoundation
    :: FrozenCheckedCore Void
    -> FrozenCheckedCore Void
    -> FrozenCheckedCore Void
    -> SetConstructionFoundation
setConstructionFoundation =
    SetConstructionFoundation

checkedFoundationSetConstruction
    :: CheckedFoundation
    -> SetConstructionFoundation
checkedFoundationSetConstruction foundation =
    SetConstructionFoundation
        (foundationAxiomFrozen foundation FamilyUnionCharacteristic)
        (foundationAxiomFrozen foundation SeparationCharacteristic)
        (foundationAxiomFrozen foundation ReplacementCharacteristic)

-- The private map is a finite typing witness for every global appearing in the
-- retained source shape, built term, checked result, and characteristic rows.
-- Smart constructors derive it from 'GlobalTyping'; there is no observer or
-- replacement operation that can detach it from those owned terms.
data NamedSetConstruction global = NamedSetConstruction
    ![CoreType]
    !(Map.Map global CoreType)
    !(NamedSetConstructionShape global)
    !(BuiltSetConstruction global)
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    ![CheckedCharacteristicApplication global]
    deriving stock (Eq)

type role NamedSetConstruction nominal

data NamedSetConstructionShape global
    = SeparationShape
        !(CanonicalTerm global)
        !(CanonicalTerm global)
    | FunctionalReplacementShape
        !(NonEmpty (CanonicalTerm global))
        !(CanonicalTerm global)
        !(Maybe (CanonicalTerm global))
    | FamilyUnionReplacementShape
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !(Maybe (CanonicalTerm global))
    deriving stock (Eq)

-- | The one canonical build result retained by the checked construction.
-- Characteristic applications describe the exact primitive rows used by the
-- derived theorem schema; the flattened body is the deterministic composition
-- of those rows for the source telescope.
data BuiltSetConstruction global = BuiltSetConstruction
    !(CanonicalTerm global)
    !(CanonicalTerm global)
    ![CharacteristicApplication global]
    deriving stock (Eq)

data CharacteristicApplication global = CharacteristicApplication
        !CoreIntrinsicTag
        ![CoreType]
        !(CanonicalTerm global)
        !(NonEmpty (CoreType, CanonicalTerm global))
        !(CanonicalTerm global)
    deriving stock (Eq)

data CheckedCharacteristicApplication global =
    CheckedCharacteristicApplication
        !CoreIntrinsicTag
        !(ScopedCheckedCore global)
        !(NonEmpty (ScopedCheckedCore global))
        !(CanonicalTerm global)
    deriving stock (Eq)

data CheckedChoiceApplication global = CheckedChoiceApplication
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    !(ScopedCheckedCore global)
    deriving stock (Eq)

-- | One checked relational replacement.  Unlike the unconditional named
-- constructions above, its flattened membership theorem is available only
-- after the separately checked functionality proposition has authority.
-- This value owns the source telescope, the one canonical choice/replacement
-- term, and the exact primitive characteristic applications used by that
-- narrow derived schema.
-- As above, the private map covers the complete relational source/build tree.
-- It is ordinary captured support, never a prospective visibility overlay.
data CheckedRelationalSetConstruction global =
    CheckedRelationalSetConstruction
        ![CoreType]
        !(Map.Map global CoreType)
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !(CanonicalTerm global)
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        !(ScopedCheckedCore global)
        ![CheckedCharacteristicApplication global]
        !(CheckedChoiceApplication global)
    deriving stock (Eq)

type role CheckedRelationalSetConstruction nominal

-- | Validate one source relational replacement.  The relation is checked in
-- the nearest-first context @[range, domain] <> outer@, matching the source
-- binder order @y x A P@ without retaining source syntax.
checkedRelationalReplacementConstruction
    :: Ord global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (CheckedRelationalSetConstruction global)
checkedRelationalReplacementConstruction globalTyping domain relation = do
    guard (scopedCoreType domain == TySet)
    guard (scopedCoreType relation == TyProp)
    let context = scopedCoreContext domain
    guard (scopedCoreContext relation == TySet : TySet : context)
    globals <-
        captureGlobalTypes globalTyping
            [scopedCoreTerm domain, scopedCoreTerm relation]
    let domainTerm = scopedCoreTerm domain
        relationTerm = scopedCoreTerm relation
        domainPredicate = CLam TySet (logicalExists relationTerm)
        restrictedDomain = applyIntrinsic2 Sep domainTerm domainPredicate
        choiceFunction =
            CLam TySet
                (CApp
                    (CLogicalSelect TySet)
                    (CLam TySet relationTerm))
        replacement = applyIntrinsic2 Repl restrictedDomain choiceFunction
        functionality = relationalFunctionality domainTerm relationTerm
        membership = relationalMembership domainTerm relationTerm
        rawApplications =
            [ characteristicApplication
                Sep context restrictedDomain
                [ (TySet, domainTerm)
                , (TyArrow TySet TyProp, domainPredicate)
                ]
            , characteristicApplication
                Repl context replacement
                [ (TySet, restrictedDomain)
                , (TyArrow TySet TySet, choiceFunction)
                ]
            ]
    checkedTerm <-
        checkDerivedUnder globalTyping context TySet replacement
    checkedFunctionality <-
        checkDerivedUnder globalTyping context TyProp functionality
    checkedMembership <-
        checkDerivedUnder globalTyping (TySet : context) TyProp membership
    checkedApplications <-
        traverse (checkCharacteristicApplication globalTyping) rawApplications
    choiceApplication <-
        checkChoiceApplication globalTyping context relationTerm
    let construction =
            CheckedRelationalSetConstruction
                context globals domainTerm relationTerm replacement functionality
                membership checkedTerm checkedFunctionality checkedMembership
                checkedApplications choiceApplication
    guard (relationalSupportCovers construction)
    pure construction

-- | Check one source separation.  The callback supplies the exact visible
-- type of every global used by its already checked components.
checkedSeparationConstruction
    :: Ord global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (NamedSetConstruction global)
checkedSeparationConstruction globalTyping bound predicate = do
    guard (scopedCoreType bound == TySet)
    guard (scopedCoreType predicate == TyProp)
    let context = scopedCoreContext bound
    guard (scopedCoreContext predicate == TySet : context)
    globals <-
        captureGlobalTypes globalTyping
            [scopedCoreTerm bound, scopedCoreTerm predicate]
    finishConstruction
        context
        globalTyping
        globals
        (SeparationShape
            (scopedCoreTerm bound)
            (scopedCoreTerm predicate))

-- | Check source-ordered functional replacement once.  Domain @i@ is checked
-- beneath exactly the preceding @i - 1@ source binders; the value and optional
-- condition are checked beneath the complete telescope.
checkedFunctionalReplacementConstruction
    :: Ord global
    => GlobalTyping global
    -> NonEmpty (ScopedCheckedCore global)
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
    -> Maybe (NamedSetConstruction global)
checkedFunctionalReplacementConstruction
        globalTyping domains value condition = do
    let domainList = NonEmpty.toList domains
        firstDomain = NonEmpty.head domains
    guard (scopedCoreType firstDomain == TySet)
    let context = scopedCoreContext firstDomain
        expectedDomainContexts =
            [ replicate index TySet <> context
            | index <- [0 .. length domainList - 1]
            ]
        valueContext = replicate (length domainList) TySet <> context
    guard
        (and
            (zipWith
                (\domain expected ->
                    scopedCoreType domain == TySet
                        && scopedCoreContext domain == expected)
                domainList
                expectedDomainContexts))
    guard
        (scopedCoreType value == TySet
            && scopedCoreContext value == valueContext)
    traverse_
        (\predicate ->
            guard
                (scopedCoreType predicate == TyProp
                    && scopedCoreContext predicate == valueContext))
        condition
    globals <-
        captureGlobalTypes globalTyping
            ( (scopedCoreTerm <$> domainList)
              <> [scopedCoreTerm value]
              <> maybeToList (scopedCoreTerm <$> condition)
            )
    finishConstruction
        context
        globalTyping
        globals
        (FunctionalReplacementShape
            (scopedCoreTerm <$> domains)
            (scopedCoreTerm value)
            (scopedCoreTerm <$> condition))

-- | Check the exact set term obtained by taking the family union of one
-- functional replacement image.  This narrow shape is useful for totalized
-- graph lookup: its flattened membership view avoids exposing higher-order
-- separation and replacement applications to every downstream proof.
checkedFamilyUnionReplacementConstruction
    :: Ord global
    => GlobalTyping global
    -> ScopedCheckedCore global
    -> ScopedCheckedCore global
    -> Maybe (ScopedCheckedCore global)
    -> Maybe (NamedSetConstruction global)
checkedFamilyUnionReplacementConstruction
        globalTyping domain value condition = do
    guard (scopedCoreType domain == TySet)
    let context = scopedCoreContext domain
        valueContext = TySet : context
    guard
        (scopedCoreType value == TySet
            && scopedCoreContext value == valueContext)
    traverse_
        (\predicate ->
            guard
                (scopedCoreType predicate == TyProp
                    && scopedCoreContext predicate == valueContext))
        condition
    globals <-
        captureGlobalTypes globalTyping
            ( scopedCoreTerm domain
              : scopedCoreTerm value
              : maybeToList (scopedCoreTerm <$> condition)
            )
    finishConstruction
        context
        globalTyping
        globals
        (FamilyUnionReplacementShape
            (scopedCoreTerm domain)
            (scopedCoreTerm value)
            (scopedCoreTerm <$> condition))

namedSetConstructionTerm
    :: NamedSetConstruction global
    -> ScopedCheckedCore global
namedSetConstructionTerm =
    constructionCheckedTerm

-- | Introduce a fresh named set and return adjacent FOF extensional and exact
-- equation locals.  Weakening is internal so construction-local binders and
-- source-domain order cannot drift at a caller.
namedSetConstructionLocalViews
    :: Ord global
    => SetConstructionFoundation
    -> NamedSetConstruction global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
namedSetConstructionLocalViews foundation construction = do
    weakened <- weakenConstruction TySet construction
    let target = scopedBound (constructionContext construction) TySet
    extensional <- extensionalView foundation target weakened
    equation <- equalScopedCore target (constructionCheckedTerm weakened)
    pure (extensional, equation)

-- | Closed transparent content derived from the sole canonical construction
-- term.  This retains the pre-existing object-content identity exactly.
namedSetConstructionClosedBody
    :: NamedSetConstruction global
    -> FrozenCheckedCore global
namedSetConstructionClosedBody construction =
    closeCheckedTerm
        "a checked construction did not close"
        (constructionCheckedTerm construction)

data NamedSetConstructionFact = NamedSetConstructionFact
    !(FrozenCheckedCore ObjectId)
    !CacheDigest

namedSetConstructionFactProposition
    :: NamedSetConstructionFact
    -> FrozenCheckedCore ObjectId
namedSetConstructionFactProposition
        (NamedSetConstructionFact proposition _descriptor) =
    proposition

namedSetConstructionFactDescriptor
    :: NamedSetConstructionFact
    -> CacheDigest
namedSetConstructionFactDescriptor
        (NamedSetConstructionFact _proposition descriptor) =
    descriptor

-- | Derive the only proposition authorized by
-- @CheckedSetConstructionExtensionality@.  This is a deliberately small
-- trusted theorem schema over the fixed foundation: every primitive
-- characteristic specialization is checked against its exact membership
-- formula before the source telescope is composed.  The caller cannot supply
-- either the resulting proposition or its cache descriptor.
namedSetConstructionObjectFact
    :: SetConstructionFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> NamedSetConstruction ObjectId
    -> Maybe NamedSetConstructionFact
namedSetConstructionObjectFact
        foundation closure object construction = do
    let context = constructionContext construction
        objectType = foldr TyArrow TySet (reverse context)
        destinationTyping = globalTypingFromClosure closure
        closedBody = namedSetConstructionClosedBody construction
    guard (lookupGlobalType destinationTyping object == Just objectType)
    guard
        (lookupCheckedObjectContent object closure
            == Just
                (TransparentObjectContent
                    (checkedObjectClosureTheory closure)
                    (frozenCoreType closedBody)
                    (frozenCoreTerm closedBody)))
    guard (constructionVisibleUnder destinationTyping construction)
    let target =
            foldl'
                CApp
                (CGlobal object)
                [ CBound (fromIntegral index)
                | index <- reverse [0 .. length context - 1]
                ]
    checkedTarget <-
        checkDerivedUnder destinationTyping context TySet target
    view <- extensionalView foundation checkedTarget construction
    let proposition =
            closeCheckedProposition
                "a named construction fact did not close"
                view
    selfView <- extensionalView
        foundation
        (constructionCheckedTerm construction)
        construction
    let closedSelf =
            closeCheckedProposition
                "a named construction self-view did not close"
                selfView
    let descriptor =
            hashCacheFields
                "felix-checked-named-set-construction-v1"
                [ encodeCache do
                    putCoreTypeCache (frozenCoreType closedBody)
                    putCanonicalTermCache putObjectIdCache
                        (frozenCoreTerm closedBody)
                , encodeCache do
                    putCanonicalTermCache putObjectIdCache
                        (frozenCoreTerm closedSelf)
                ]
    pure (NamedSetConstructionFact proposition descriptor)

relationalSetConstructionTerm
    :: CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
relationalSetConstructionTerm =
    relationalConstructionCheckedTerm

-- | The exact source functionality obligation, still scoped by the outer
-- definition parameters.  It is discharged independently before the derived
-- extensional theorem can be authorized.
relationalSetConstructionFunctionality
    :: CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
relationalSetConstructionFunctionality =
    relationalConstructionCheckedFunctionality

relationalSetConstructionClosedFunctionality
    :: CheckedRelationalSetConstruction global
    -> FrozenCheckedCore global
relationalSetConstructionClosedFunctionality =
    closeRelationalFunctionality

-- | Introduce a fresh named set.  Assuming the exact checked functionality
-- proposition, derive its two local views; no arbitrary proposition can
-- unlock the extensional view.  The enclosing proof transaction owns the
-- corresponding authority.
relationalSetConstructionLocalViews
    :: Ord global
    => SetConstructionFoundation
    -> CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
    -> Maybe
        ( ScopedCheckedCore global
        , ScopedCheckedCore global
        )
relationalSetConstructionLocalViews foundation construction functionality = do
    guard
        (functionality
            == relationalSetConstructionFunctionality construction)
    validateRelationalSchema foundation construction
    let outer = relationalConstructionContext construction
        target = scopedBound outer TySet
        element = scopedBound (TySet : outer) TySet
        namedTarget = weakenCheckedScopedCore TySet target
    actualMembership <- memberScopedCore element namedTarget
    expectedMembership <-
        weakenCheckedScopedCoreAt 1 TySet
            (relationalConstructionCheckedMembership construction)
    extensionalBody <- equalScopedCore actualMembership expectedMembership
    extensional <- closeScopedForall extensionalBody
    equation <- equalScopedCore
        target
        (weakenCheckedScopedCore TySet
            (relationalConstructionCheckedTerm construction))
    pure (extensional, equation)

relationalSetConstructionClosedBody
    :: CheckedRelationalSetConstruction global
    -> FrozenCheckedCore global
relationalSetConstructionClosedBody construction =
    closeCheckedTerm
        "a checked relational construction did not close"
        (relationalConstructionCheckedTerm construction)

data RelationalSetConstructionFact = RelationalSetConstructionFact
    !(FrozenCheckedCore ObjectId)
    !CacheDigest

relationalSetConstructionFactProposition
    :: RelationalSetConstructionFact
    -> FrozenCheckedCore ObjectId
relationalSetConstructionFactProposition
        (RelationalSetConstructionFact proposition _descriptor) =
    proposition

relationalSetConstructionFactDescriptor
    :: RelationalSetConstructionFact
    -> CacheDigest
relationalSetConstructionFactDescriptor
        (RelationalSetConstructionFact _proposition descriptor) =
    descriptor

-- | The direct relational schema is a deterministic theorem over the fixed
-- separation, choice-witness, and replacement rows.  The functionality fact
-- is a real strictly-earlier candidate: its exact proposition is checked here
-- and its authority safety is consumed separately by declaration admission.
relationalSetConstructionObjectFact
    :: SetConstructionFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> CheckedRelationalSetConstruction ObjectId
    -> FrozenCheckedCore ObjectId
    -> Maybe RelationalSetConstructionFact
relationalSetConstructionObjectFact
        foundation closure object construction functionality = do
    let expectedFunctionality = closeRelationalFunctionality construction
    guard (functionality == expectedFunctionality)
    validateRelationalSchema foundation construction
    let context = relationalConstructionContext construction
        objectType = foldr TyArrow TySet (reverse context)
        destinationTyping = globalTypingFromClosure closure
        closedBody = relationalSetConstructionClosedBody construction
    guard (lookupGlobalType destinationTyping object == Just objectType)
    guard
        (lookupCheckedObjectContent object closure
            == Just
                (TransparentObjectContent
                    (checkedObjectClosureTheory closure)
                    (frozenCoreType closedBody)
                    (frozenCoreTerm closedBody)))
    guard (relationalConstructionVisibleUnder destinationTyping construction)
    let target =
            foldl'
                CApp
                (CGlobal object)
                [ CBound (fromIntegral index)
                | index <- reverse [0 .. length context - 1]
                ]
    checkedTarget <-
        checkDerivedUnder destinationTyping context TySet target
    view <- relationalExtensionalView checkedTarget construction
    let proposition =
            closeCheckedProposition
                "a relational construction fact did not close"
                view
    selfView <- relationalExtensionalView
        (relationalConstructionCheckedTerm construction)
        construction
    let closedSelf =
            closeCheckedProposition
                "a relational construction self-view did not close"
                selfView
    let descriptor =
            hashCacheFields
                "felix-checked-named-relational-set-construction-v1"
                [ encodeCache do
                    putCoreTypeCache (frozenCoreType closedBody)
                    putCanonicalTermCache putObjectIdCache
                        (frozenCoreTerm closedBody)
                , encodeCache do
                    putCanonicalTermCache putObjectIdCache
                        (frozenCoreTerm expectedFunctionality)
                , encodeCache do
                    putCanonicalTermCache putObjectIdCache
                        (frozenCoreTerm closedSelf)
                ]
    pure (RelationalSetConstructionFact proposition descriptor)

finishConstruction
    :: Ord global
    => [CoreType]
    -> GlobalTyping global
    -> Map.Map global CoreType
    -> NamedSetConstructionShape global
    -> Maybe (NamedSetConstruction global)
finishConstruction context globalTyping globals shape = do
    let built = buildConstruction context shape
    checkedTerm <-
        checkDerivedUnder globalTyping context TySet
            (builtConstructionTerm built)
    checkedMembership <-
        checkDerivedUnder globalTyping (TySet : context) TyProp
            (builtConstructionMembership built)
    checkedApplications <-
        traverse
            (checkCharacteristicApplication globalTyping)
            (builtConstructionApplications built)
    let construction =
            NamedSetConstruction
                context globals shape built checkedTerm checkedMembership
                checkedApplications
    guard (constructionSupportCovers construction)
    pure construction

buildConstruction
    :: [CoreType]
    -> NamedSetConstructionShape global
    -> BuiltSetConstruction global
buildConstruction context = \case
    SeparationShape bound predicate ->
        let function = CLam TySet predicate
            term = applyIntrinsic2 Sep bound function
            membership =
                logicalAnd
                    (member (CBound 0) (shiftCanonical 1 0 bound))
                    predicate
            application =
                characteristicApplication
                    Sep context term
                    [ (TySet, bound)
                    , (TyArrow TySet TyProp, function)
                    ]
        in BuiltSetConstruction term membership [application]
    FunctionalReplacementShape domains value condition ->
        let (term, applications) =
                buildFunctionalReplacement
                    context
                    domains
                    value
                    condition
            domainList = NonEmpty.toList domains
            binderCount = length domainList
            terminal =
                canonicalConjunction
                    ( maybeToList
                        (shiftCanonical 1 (fromIntegral binderCount)
                            <$> condition)
                      <> [ CEq TySet
                            (CBound (fromIntegral binderCount))
                            (shiftCanonical 1
                                (fromIntegral binderCount)
                                value)
                         ]
                    )
            membership =
                foldr
                    (\(depth, domain) rest ->
                        logicalExists
                            (logicalAnd
                                (member
                                    (CBound 0)
                                    (shiftCanonical 1 0
                                        (shiftCanonical 1 depth domain)))
                                rest))
                    terminal
                    (zip [0 :: Natural ..] domainList)
        in BuiltSetConstruction term membership applications
    FamilyUnionReplacementShape domain value condition ->
        let (replacement, replacementApplications) =
                buildFunctionalReplacement
                    context
                    (domain :| [])
                    value
                    condition
            term = applyIntrinsic FamilyUnion replacement
            membership =
                logicalExists
                    (canonicalConjunction
                        ( [ member
                                (CBound 0)
                                (shiftCanonical 2 0 domain)
                          ]
                          <> maybeToList
                                (shiftCanonical 1 1 <$> condition)
                          <> [ member
                                (CBound 1)
                                (shiftCanonical 1 1 value)
                             ]
                        ))
            unionApplication =
                characteristicApplication
                    FamilyUnion context term [(TySet, replacement)]
        in BuiltSetConstruction
            term membership (replacementApplications <> [unionApplication])

-- The only functional-replacement term builder.  Its result is reused by the
-- transparent body, exact-content matching, characteristic validation, local
-- views, and descriptor derivation.
buildFunctionalReplacement
    :: [CoreType]
    -> NonEmpty (CanonicalTerm global)
    -> CanonicalTerm global
    -> Maybe (CanonicalTerm global)
    -> (CanonicalTerm global, [CharacteristicApplication global])
buildFunctionalReplacement context (domain :| remaining) value condition =
    case remaining of
        [] ->
            let predicate = CLam TySet <$> condition
                filtered = maybe domain
                    (applyIntrinsic2 Sep domain)
                    predicate
                function = CLam TySet value
                replacement = applyIntrinsic2 Repl filtered function
                separationApplications = case predicate of
                    Nothing -> []
                    Just checkedPredicate ->
                        [ characteristicApplication
                            Sep context filtered
                            [ (TySet, domain)
                            , (TyArrow TySet TyProp, checkedPredicate)
                            ]
                        ]
                replacementApplication =
                    characteristicApplication
                        Repl context replacement
                        [ (TySet, filtered)
                        , (TyArrow TySet TySet, function)
                        ]
            in
                ( replacement
                , separationApplications <> [replacementApplication]
                )
        next : rest ->
            let (nested, nestedApplications) =
                    buildFunctionalReplacement
                        (TySet : context)
                        (next :| rest)
                        value
                        condition
                function = CLam TySet nested
                replacement = applyIntrinsic2 Repl domain function
                union = applyIntrinsic FamilyUnion replacement
            in
                ( union
                , characteristicApplication
                    Repl context replacement
                    [ (TySet, domain)
                    , (TyArrow TySet TySet, function)
                    ]
                  : characteristicApplication
                        FamilyUnion context union
                        [(TySet, replacement)]
                  : nestedApplications
                )

characteristicApplication
    :: CoreIntrinsicTag
    -> [CoreType]
    -> CanonicalTerm global
    -> [(CoreType, CanonicalTerm global)]
    -> CharacteristicApplication global
characteristicApplication intrinsic context target arguments =
    CharacteristicApplication
        intrinsic
        context
        target
        (NonEmpty.fromList arguments)
        (expectedCharacteristicBody intrinsic arguments)

expectedCharacteristicBody
    :: CoreIntrinsicTag
    -> [(CoreType, CanonicalTerm global)]
    -> CanonicalTerm global
expectedCharacteristicBody intrinsic arguments =
    case (intrinsic, arguments) of
        (Sep, [(_boundType, bound), (_predicateType, CLam TySet predicate)]) ->
            logicalAnd
                (member (CBound 0) (shiftCanonical 2 0 bound))
                (shiftCanonical 1 1 predicate)
        (Repl, [(_domainType, domain), (_functionType, CLam TySet value)]) ->
            logicalExists
                (logicalAnd
                    (member (CBound 0) (shiftCanonical 3 0 domain))
                    (CEq TySet
                        (CBound 1)
                        (shiftCanonical 2 1 value)))
        (FamilyUnion, [(_familyType, family)]) ->
            logicalExists
                (logicalAnd
                    (member (CBound 0) (shiftCanonical 3 0 family))
                    (member (CBound 1) (CBound 0)))
        _ ->
            impossible "invalid checked set-construction characteristic"

extensionalView
    :: Eq global
    => SetConstructionFoundation
    -> ScopedCheckedCore global
    -> NamedSetConstruction global
    -> Maybe (ScopedCheckedCore global)
extensionalView foundation target construction = do
    guard (scopedCoreContext target == constructionContext construction)
    guard (scopedCoreType target == TySet)
    traverse_
        (validateCharacteristic foundation)
        (constructionApplications construction)
    let element =
            scopedBound (constructionContext construction) TySet
        weakenedTarget = weakenCheckedScopedCore TySet target
    actualMembership <- memberScopedCore element weakenedTarget
    body <- equalScopedCore
        actualMembership
        (constructionCheckedMembership construction)
    closeScopedForall body

-- Each primitive step is specialized from the actual fixed row, and the
-- complete normalized membership body is checked.  The final flattened view
-- is then the deterministic composition of these exact primitive schemas.
validateCharacteristic
    :: Eq global
    => SetConstructionFoundation
    -> CheckedCharacteristicApplication global
    -> Maybe ()
validateCharacteristic foundation
        (CheckedCharacteristicApplication
            intrinsic target arguments expectedBody) = do
    row <- characteristicRow foundation intrinsic
    specialized <- scopedCharacteristicDefinition row target arguments
    case scopedCoreTerm specialized of
        CForall TySet
                (CEq TyProp actualMembership actualBody)
            | actualMembership
                == member (CBound 0) (CBound 1)
            , scopedCoreContext specialized
                == TySet : scopedCoreContext target
            , actualBody == expectedBody ->
                pure ()
        _ -> Nothing

characteristicRow
    :: SetConstructionFoundation
    -> CoreIntrinsicTag
    -> Maybe (FrozenCheckedCore Void)
characteristicRow
        (SetConstructionFoundation
            familyUnion separation replacement) =
    \case
        FamilyUnion -> Just familyUnion
        Sep -> Just separation
        Repl -> Just replacement
        _ -> Nothing

validateRelationalSchema
    :: Eq global
    => SetConstructionFoundation
    -> CheckedRelationalSetConstruction global
    -> Maybe ()
validateRelationalSchema foundation construction = do
    traverse_
        (validateRelationalCharacteristic foundation)
        (relationalConstructionApplications construction)
    validateChoiceWitness foundation construction

validateRelationalCharacteristic
    :: Eq global
    => SetConstructionFoundation
    -> CheckedCharacteristicApplication global
    -> Maybe ()
validateRelationalCharacteristic foundation
        (CheckedCharacteristicApplication
            intrinsic target arguments expectedBody) = do
    row <- characteristicRow foundation intrinsic
    specialized <- scopedCharacteristicDefinition row target arguments
    case scopedCoreTerm specialized of
        CForall TySet (CEq TyProp actualMembership actualBody)
            | actualMembership == member (CBound 0) (CBound 1)
            , scopedCoreContext specialized
                == TySet : scopedCoreContext target
            , actualBody == expectedBody ->
                pure ()
        _ -> Nothing

validateChoiceWitness
    :: Eq global
    => SetConstructionFoundation
    -> CheckedRelationalSetConstruction global
    -> Maybe ()
validateChoiceWitness
        _foundation
        construction = do
    let context = relationalConstructionContext construction
        relation = relationalConstructionRelation construction
        setSelection = logicalSelectionWitness TySet
        CheckedChoiceApplication target checkedPredicate witness =
            relationalConstructionChoiceApplication construction
    specialized <-
        scopedCharacteristicDefinition
            setSelection target (checkedPredicate :| [witness])
    guard
        (scopedCoreContext specialized
            == TySet : TySet : TySet : context)
    guard
        (scopedCoreTerm specialized
            == CImp
                (shiftCanonical 1 0 relation)
                (shiftCanonical 1 1 relation))

relationalFunctionality
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
relationalFunctionality domain relation =
    CForall TySet
        (CImp
            (member (CBound 0) (shiftCanonical 1 0 domain))
            (CForall TySet
                (CForall TySet
                    (CImp
                        (logicalAnd
                            (shiftCanonical 1 0 relation)
                            (shiftCanonical 1 1 relation))
                        (CEq TySet (CBound 1) (CBound 0))))))

relationalMembership
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
relationalMembership domain relation =
    logicalExists
        (logicalAnd
            (member (CBound 0) (shiftCanonical 2 0 domain))
            (applyRelation
                (shiftCanonical 2 0
                    (CLam TySet (CLam TySet relation)))
                (CBound 0)
                (CBound 1)))
  where
    applyRelation function domainValue rangeValue =
        case function of
            CLam TySet domainBody ->
                case instantiateCanonical domainValue domainBody of
                    CLam TySet rangeBody ->
                        instantiateCanonical rangeValue rangeBody
                    _ -> impossible "a checked relation lost its range binder"
            _ -> impossible "a checked relation lost its domain binder"

weakenConstruction
    :: Ord global
    => CoreType
    -> NamedSetConstruction global
    -> Maybe (NamedSetConstruction global)
weakenConstruction binderType construction =
    do
        checkedMembership <-
            weakenCheckedScopedCoreAt 1 binderType
                (constructionCheckedMembership construction)
        checkedApplications <-
            traverse
                (weakenCharacteristicApplication
                    (length (constructionContext construction))
                    binderType)
                (constructionApplications construction)
        let context = binderType : constructionContext construction
            shape = weakenConstructionShape binderType construction
            built = buildConstruction context shape
            checkedTerm =
                weakenCheckedScopedCore binderType
                    (constructionCheckedTerm construction)
            weakened =
                NamedSetConstruction
                    context
                    (constructionGlobals construction)
                    shape
                    built
                    checkedTerm
                    checkedMembership
                    checkedApplications
        unless
            (scopedCoreTerm checkedTerm == builtConstructionTerm built)
            (impossible "weakened construction term drifted")
        unless
            (scopedCoreTerm checkedMembership
                == builtConstructionMembership built)
            (impossible "weakened construction membership drifted")
        unless
            (checkedApplicationsMatch
                checkedApplications
                (builtConstructionApplications built))
            (impossible "weakened characteristic application drifted")
        unless
            (constructionSupportCovers weakened)
            (impossible "weakened construction escaped finite support")
        pure weakened

weakenConstructionShape
    :: CoreType
    -> NamedSetConstruction global
    -> NamedSetConstructionShape global
weakenConstructionShape _binderType construction =
    case constructionShape construction of
        SeparationShape bound predicate ->
            SeparationShape
                (shiftCanonical 1 0 bound)
                (shiftCanonical 1 1 predicate)
        FunctionalReplacementShape domains value condition ->
            let domainList = NonEmpty.toList domains
                weakenedDomains =
                    zipWith
                        (\depth domain -> shiftCanonical 1 depth domain)
                        [0..]
                        domainList
                binderDepth = fromIntegral (length domainList)
            in FunctionalReplacementShape
                (NonEmpty.fromList weakenedDomains)
                (shiftCanonical 1 binderDepth value)
                (shiftCanonical 1 binderDepth <$> condition)
        FamilyUnionReplacementShape domain value condition ->
            FamilyUnionReplacementShape
                (shiftCanonical 1 0 domain)
                (shiftCanonical 1 1 value)
                (shiftCanonical 1 1 <$> condition)

captureGlobalTypes
    :: Ord global
    => GlobalTyping global
    -> [CanonicalTerm global]
    -> Maybe (Map.Map global CoreType)
captureGlobalTypes globalTyping terms =
    Map.fromList <$> traverse capture
        (Set.toAscList (foldMap canonicalTermGlobals terms))
  where
    capture global = do
        coreType <- lookupGlobalType globalTyping global
        pure (global, coreType)

checkDerivedUnder
    :: GlobalTyping global
    -> [CoreType]
    -> CoreType
    -> CanonicalTerm global
    -> Maybe (ScopedCheckedCore global)
checkDerivedUnder globalTyping context expected term = do
    checked <- either (const Nothing) Just
        (checkScopedCanonicalCore globalTyping context term)
    guard (scopedCoreType checked == expected)
    pure checked

checkCharacteristicApplication
    :: GlobalTyping global
    -> CharacteristicApplication global
    -> Maybe (CheckedCharacteristicApplication global)
checkCharacteristicApplication globalTyping
        (CharacteristicApplication
            intrinsic context target arguments expectedBody) = do
    checkedTarget <- checkDerivedUnder globalTyping context TySet target
    checkedArguments <-
        traverse
            (\(coreType, argument) ->
                checkDerivedUnder globalTyping context coreType argument)
            arguments
    pure
        (CheckedCharacteristicApplication
            intrinsic checkedTarget checkedArguments expectedBody)

checkChoiceApplication
    :: GlobalTyping global
    -> [CoreType]
    -> CanonicalTerm global
    -> Maybe (CheckedChoiceApplication global)
checkChoiceApplication globalTyping context relation = do
    let predicate = CLam TySet relation
        choice = CApp (CLogicalSelect TySet) predicate
        witnessContext = TySet : TySet : context
    target <- checkDerivedUnder globalTyping witnessContext TySet
        (shiftCanonical 1 0 choice)
    checkedPredicate <- checkDerivedUnder globalTyping witnessContext
        (TyArrow TySet TyProp)
        (shiftCanonical 1 0 predicate)
    let witness = scopedBound (TySet : context) TySet
    pure (CheckedChoiceApplication target checkedPredicate witness)

closeCheckedTerm
    :: String
    -> ScopedCheckedCore global
    -> FrozenCheckedCore global
closeCheckedTerm failure checked =
    fromMaybe (impossible failure) do
        abstracted <-
            foldM
                (\body binderType -> abstractScopedCore binderType body)
                checked
                (scopedCoreContext checked)
        closeScopedCore abstracted

closeCheckedProposition
    :: String
    -> ScopedCheckedCore global
    -> FrozenCheckedCore global
closeCheckedProposition failure checked =
    fromMaybe (impossible failure) do
        closed <-
            foldM
                (\body _binderType -> closeScopedForall body)
                checked
                (scopedCoreContext checked)
        closeScopedCore closed

relationalExtensionalView
    :: ScopedCheckedCore global
    -> CheckedRelationalSetConstruction global
    -> Maybe (ScopedCheckedCore global)
relationalExtensionalView target construction = do
    guard
        (scopedCoreContext target
            == relationalConstructionContext construction)
    guard (scopedCoreType target == TySet)
    let element =
            scopedBound (relationalConstructionContext construction) TySet
        weakenedTarget = weakenCheckedScopedCore TySet target
    actualMembership <- memberScopedCore element weakenedTarget
    body <- equalScopedCore
        actualMembership
        (relationalConstructionCheckedMembership construction)
    closeScopedForall body

weakenCharacteristicApplication
    :: Int
    -> CoreType
    -> CheckedCharacteristicApplication global
    -> Maybe (CheckedCharacteristicApplication global)
weakenCharacteristicApplication outerLength binderType
        (CheckedCharacteristicApplication
            intrinsic target arguments expectedBody) = do
    let applicationContextLength = length (scopedCoreContext target)
    guard (outerLength <= applicationContextLength)
    let depth = fromIntegral (applicationContextLength - outerLength)
    weakenedTarget <-
        weakenCheckedScopedCoreAt depth binderType target
    weakenedArguments <-
        traverse (weakenCheckedScopedCoreAt depth binderType) arguments
    pure
        (CheckedCharacteristicApplication
            intrinsic
            weakenedTarget
            weakenedArguments
            (shiftCanonical 1 (depth + 2) expectedBody))

checkedApplicationsMatch
    :: Eq global
    => [CheckedCharacteristicApplication global]
    -> [CharacteristicApplication global]
    -> Bool
checkedApplicationsMatch checked raw =
    length checked == length raw
        && and (zipWith matches checked raw)
  where
    matches
            (CheckedCharacteristicApplication
                checkedIntrinsic target arguments checkedBody)
            (CharacteristicApplication
                rawIntrinsic context rawTarget rawArguments rawBody) =
        checkedIntrinsic == rawIntrinsic
            && scopedCoreContext target == context
            && scopedCoreType target == TySet
            && scopedCoreTerm target == rawTarget
            && fmap
                (\argument ->
                    (scopedCoreType argument, scopedCoreTerm argument))
                arguments
                == rawArguments
            && all ((== context) . scopedCoreContext) arguments
            && checkedBody == rawBody

constructionSupportCovers
    :: Ord global
    => NamedSetConstruction global
    -> Bool
constructionSupportCovers construction =
    supportCovers
        (constructionGlobals construction)
        ( constructionShapeTerms (constructionShape construction)
          <> builtConstructionTerms (constructionBuilt construction)
          <> checkedApplicationTerms (constructionApplications construction)
        )

relationalSupportCovers
    :: Ord global
    => CheckedRelationalSetConstruction global
    -> Bool
relationalSupportCovers construction =
    supportCovers
        (relationalConstructionGlobals construction)
        ( [ relationalConstructionDomain construction
          , relationalConstructionRelation construction
          , relationalConstructionCanonicalTerm construction
          , relationalConstructionFunctionalityTerm construction
          , relationalConstructionMembershipTerm construction
          ]
          <> checkedApplicationTerms
                (relationalConstructionApplications construction)
          <> checkedChoiceTerms
                (relationalConstructionChoiceApplication construction)
        )

supportCovers
    :: Ord global
    => Map.Map global CoreType
    -> [CanonicalTerm global]
    -> Bool
supportCovers globals terms =
    foldMap canonicalTermGlobals terms
        `Set.isSubsetOf` Map.keysSet globals

constructionShapeTerms
    :: NamedSetConstructionShape global
    -> [CanonicalTerm global]
constructionShapeTerms = \case
    SeparationShape bound predicate ->
        [bound, predicate]
    FunctionalReplacementShape domains value condition ->
        NonEmpty.toList domains <> (value : maybeToList condition)
    FamilyUnionReplacementShape domain value condition ->
        domain : value : maybeToList condition

builtConstructionTerms
    :: BuiltSetConstruction global
    -> [CanonicalTerm global]
builtConstructionTerms (BuiltSetConstruction term membership applications) =
    term : membership : foldMap characteristicApplicationTerms applications

characteristicApplicationTerms
    :: CharacteristicApplication global
    -> [CanonicalTerm global]
characteristicApplicationTerms
        (CharacteristicApplication
            _intrinsic _context target arguments expectedBody) =
    target : expectedBody : (snd <$> NonEmpty.toList arguments)

checkedApplicationTerms
    :: [CheckedCharacteristicApplication global]
    -> [CanonicalTerm global]
checkedApplicationTerms = foldMap \case
    CheckedCharacteristicApplication _intrinsic target arguments expectedBody ->
        scopedCoreTerm target
            : expectedBody
            : (scopedCoreTerm <$> NonEmpty.toList arguments)

checkedChoiceTerms
    :: CheckedChoiceApplication global
    -> [CanonicalTerm global]
checkedChoiceTerms (CheckedChoiceApplication target predicate witness) =
    scopedCoreTerm <$> [target, predicate, witness]

closeRelationalFunctionality
    :: CheckedRelationalSetConstruction global
    -> FrozenCheckedCore global
closeRelationalFunctionality construction =
    closeCheckedProposition
        "a relational functionality proposition did not close"
        (relationalConstructionCheckedFunctionality construction)

relationalConstructionContext
    :: CheckedRelationalSetConstruction global
    -> [CoreType]
relationalConstructionContext
        (CheckedRelationalSetConstruction
            context _globals _domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    context

relationalConstructionGlobals
    :: CheckedRelationalSetConstruction global
    -> Map.Map global CoreType
relationalConstructionGlobals
        (CheckedRelationalSetConstruction
            _context globals _domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    globals

relationalConstructionDomain
    :: CheckedRelationalSetConstruction global
    -> CanonicalTerm global
relationalConstructionDomain
        (CheckedRelationalSetConstruction
            _context _globals domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    domain

relationalConstructionRelation
    :: CheckedRelationalSetConstruction global
    -> CanonicalTerm global
relationalConstructionRelation
        (CheckedRelationalSetConstruction
            _context _globals _domain relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    relation

relationalConstructionCanonicalTerm
    :: CheckedRelationalSetConstruction global
    -> CanonicalTerm global
relationalConstructionCanonicalTerm
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    term

relationalConstructionFunctionalityTerm
    :: CheckedRelationalSetConstruction global
    -> CanonicalTerm global
relationalConstructionFunctionalityTerm
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    functionality

relationalConstructionMembershipTerm
    :: CheckedRelationalSetConstruction global
    -> CanonicalTerm global
relationalConstructionMembershipTerm
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    membership

relationalConstructionCheckedTerm
    :: CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
relationalConstructionCheckedTerm
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            _membership checkedTerm _checkedFunctionality _checkedMembership
            _applications _choice) =
    checkedTerm

relationalConstructionCheckedFunctionality
    :: CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
relationalConstructionCheckedFunctionality
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            _membership _checkedTerm checkedFunctionality _checkedMembership
            _applications _choice) =
    checkedFunctionality

relationalConstructionCheckedMembership
    :: CheckedRelationalSetConstruction global
    -> ScopedCheckedCore global
relationalConstructionCheckedMembership
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality checkedMembership
            _applications _choice) =
    checkedMembership

relationalConstructionApplications
    :: CheckedRelationalSetConstruction global
    -> [CheckedCharacteristicApplication global]
relationalConstructionApplications
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            applications _choice) =
    applications

relationalConstructionChoiceApplication
    :: CheckedRelationalSetConstruction global
    -> CheckedChoiceApplication global
relationalConstructionChoiceApplication
        (CheckedRelationalSetConstruction
            _context _globals _domain _relation _term _functionality
            _membership _checkedTerm _checkedFunctionality _checkedMembership
            _applications choice) =
    choice

constructionContext :: NamedSetConstruction global -> [CoreType]
constructionContext
        (NamedSetConstruction
            context _globals _shape _built _term _membership _applications) =
    context

constructionGlobals
    :: NamedSetConstruction global
    -> Map.Map global CoreType
constructionGlobals
        (NamedSetConstruction
            _context globals _shape _built _term _membership _applications) =
    globals

constructionShape
    :: NamedSetConstruction global
    -> NamedSetConstructionShape global
constructionShape
        (NamedSetConstruction
            _context _globals shape _built _term _membership _applications) =
    shape

constructionBuilt
    :: NamedSetConstruction global
    -> BuiltSetConstruction global
constructionBuilt
        (NamedSetConstruction
            _context _globals _shape built _term _membership _applications) =
    built

constructionCheckedTerm
    :: NamedSetConstruction global
    -> ScopedCheckedCore global
constructionCheckedTerm
        (NamedSetConstruction
            _context _globals _shape _built term _membership _applications) =
    term

constructionCheckedMembership
    :: NamedSetConstruction global
    -> ScopedCheckedCore global
constructionCheckedMembership
        (NamedSetConstruction
            _context _globals _shape _built _term membership _applications) =
    membership

constructionApplications
    :: NamedSetConstruction global
    -> [CheckedCharacteristicApplication global]
constructionApplications
        (NamedSetConstruction
            _context _globals _shape _built _term _membership applications) =
    applications

constructionVisibleUnder
    :: GlobalTyping global
    -> NamedSetConstruction global
    -> Bool
constructionVisibleUnder globalTyping =
    all visible . Map.toList . constructionGlobals
  where
    visible (global, coreType) =
        lookupGlobalType globalTyping global == Just coreType

relationalConstructionVisibleUnder
    :: GlobalTyping global
    -> CheckedRelationalSetConstruction global
    -> Bool
relationalConstructionVisibleUnder globalTyping =
    all visible . Map.toList . relationalConstructionGlobals
  where
    visible (global, coreType) =
        lookupGlobalType globalTyping global == Just coreType

builtConstructionTerm
    :: BuiltSetConstruction global
    -> CanonicalTerm global
builtConstructionTerm (BuiltSetConstruction term _membership _applications) =
    term

builtConstructionMembership
    :: BuiltSetConstruction global
    -> CanonicalTerm global
builtConstructionMembership
        (BuiltSetConstruction _term membership _applications) =
    membership

builtConstructionApplications
    :: BuiltSetConstruction global
    -> [CharacteristicApplication global]
builtConstructionApplications
        (BuiltSetConstruction _term _membership applications) =
    applications

applyIntrinsic
    :: CoreIntrinsicTag
    -> CanonicalTerm global
    -> CanonicalTerm global
applyIntrinsic intrinsic argument =
    CApp (CIntrinsic intrinsic) argument

applyIntrinsic2
    :: CoreIntrinsicTag
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
applyIntrinsic2 intrinsic first second =
    CApp (CApp (CIntrinsic intrinsic) first) second

member
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
member = applyIntrinsic2 Member

logicalAnd
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
logicalAnd left right =
    CAnd left right

logicalExists :: CanonicalTerm global -> CanonicalTerm global
logicalExists body =
    CExists TySet body
