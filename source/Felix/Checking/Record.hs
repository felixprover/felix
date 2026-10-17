{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked set-level resources used by the extensional record calculus.
module Felix.Checking.Record
    ( RecordSchemaLaw(..)
    , recordSchemaLawBuilder
    , recordSchemaLawCode
    , recordSchemaLawFromCode
    , FieldObjects
    , fieldObjects
    , fieldObjectsSelector
    , fieldObjectsProjection
    , fieldSelectorBody
    , fieldSelectorObjectId
    , fieldSelectorObject
    , fieldProjectionBody
    , fieldProjectionObjectId
    , fieldProjectionObject
    , fieldProjectionConstruction
    , recordProjectionMembershipLaw
    , recordProjectionEntryLaw
    , recordProjectionMissingLaw
    , recordSchemaProjectionAgreementLaw
    , recordSchemaProjectionEntryAgreementLaw
    , recordSchemaProjectionGraphAgreementLaw
    , recordSchemaProjectionExtensionalityLaw
    , recordSelectorDistinctLaws
    , recordSelectorDistinctLaw
    , recordSchemaAggregatePairCodedLaw
    , recordSchemaAggregateValueUniqueLaws
    , recordSchemaAggregateEntryLaws
    , recordSchemaAggregateSelectorClosedLaw
    , recordSchemaAggregateFunctionalLaw
    , recordSchemaAggregateComponentLaws
    , recordSchemaAggregateExactLaw
    , recordSchemaAggregateProjectionApplicationLaws
    , recordSchemaAggregateProjectionLaws
    , RecordAggregateContext
    , recordSchemaAggregateContext
    , recordAggregateContextSelectors
    , recordAggregateContextValues
    , recordAggregateContextTerm
    , recordFunctional
    , recordPairCoded
    , recordRightUnique
    , selectorPresent
    , selectorClosed
    , recordOpenShape
    , recordExactShape
    , recognizeRecordExactGlobalShape
    , recordAggregate
    , recordLookup
    , recordReduct
    , recordExactGraphExtensionality
    , recordReductExact
    , recordReductMembership
    , recordSchemaExactGraphLaw
    , recordSchemaReductExactLaw
    , recordSchemaReductMembershipLaw
    , recordSchemaReductIdentityLaw
    , recordSchemaReductProjectionLaws
    , recordSchemaReductCoreLaws
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity
import Felix.Checking.SetConstruction qualified as SetConstruction
import Felix.Math.Codec

import Data.Bits (testBit)
import Control.DeepSeq (NFData)
import Data.ByteString qualified as ByteString
import Data.ByteString.Builder qualified as Builder
import Data.Word (Word8)


data RecordSchemaLaw
    = RecordExactGraphLaw
    | RecordReductMembershipLaw
    | RecordReductExactLaw
    | RecordProjectionEntryLaw !FieldId
    | RecordProjectionAgreementLaw !FieldId
    | RecordProjectionEntryAgreementLaw
    | RecordProjectionGraphAgreementLaw
    | RecordProjectionExtensionalityLaw
    | RecordReductIdentityLaw
    | RecordReductProjectionLaw !FieldId
    | RecordSelectorPairDistinctLaw !FieldId !FieldId
    | RecordSelectorDistinctLaw
    | RecordAggregatePairCodedLaw
    | RecordAggregateValueUniqueLaw !FieldId
    | RecordAggregateEntryLaw !FieldId
    | RecordAggregateSelectorClosedLaw
    | RecordAggregateProjectionApplicationLaw !FieldId
    | RecordAggregateFunctionalLaw
    | RecordAggregateExactLaw
    | RecordAggregateProjectionLaw !FieldId
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Ord RecordSchemaLaw where
    compare = compare `on` recordSchemaLawCode

-- | Stable law tags are independent of Haskell constructor order. Field
-- identities have a fixed-width canonical byte encoding.
recordSchemaLawBuilder :: RecordSchemaLaw -> Builder.Builder
recordSchemaLawBuilder law =
    let (tag, fields) = recordSchemaLawCode law
    in Builder.word8 tag <> foldMap
        (Builder.byteString . mathematicalDigestBytes . fieldIdDigest) fields

recordSchemaLawCode :: RecordSchemaLaw -> (Word8, [FieldId])
recordSchemaLawCode = \case
    RecordExactGraphLaw -> (0, [])
    RecordReductMembershipLaw -> (1, [])
    RecordReductExactLaw -> (2, [])
    RecordProjectionEntryLaw field -> (3, [field])
    RecordProjectionAgreementLaw field -> (4, [field])
    RecordProjectionEntryAgreementLaw -> (5, [])
    RecordProjectionGraphAgreementLaw -> (6, [])
    RecordProjectionExtensionalityLaw -> (7, [])
    RecordReductIdentityLaw -> (8, [])
    RecordReductProjectionLaw field -> (9, [field])
    RecordSelectorPairDistinctLaw left right -> (10, [left, right])
    RecordSelectorDistinctLaw -> (11, [])
    RecordAggregatePairCodedLaw -> (12, [])
    RecordAggregateValueUniqueLaw field -> (13, [field])
    RecordAggregateEntryLaw field -> (14, [field])
    RecordAggregateSelectorClosedLaw -> (15, [])
    RecordAggregateProjectionApplicationLaw field -> (16, [field])
    RecordAggregateFunctionalLaw -> (17, [])
    RecordAggregateExactLaw -> (18, [])
    RecordAggregateProjectionLaw field -> (19, [field])

recordSchemaLawFromCode :: Word8 -> [FieldId] -> Maybe RecordSchemaLaw
recordSchemaLawFromCode tag fields = case (tag, fields) of
    (0, []) -> Just RecordExactGraphLaw
    (1, []) -> Just RecordReductMembershipLaw
    (2, []) -> Just RecordReductExactLaw
    (3, [field]) -> Just (RecordProjectionEntryLaw field)
    (4, [field]) -> Just (RecordProjectionAgreementLaw field)
    (5, []) -> Just RecordProjectionEntryAgreementLaw
    (6, []) -> Just RecordProjectionGraphAgreementLaw
    (7, []) -> Just RecordProjectionExtensionalityLaw
    (8, []) -> Just RecordReductIdentityLaw
    (9, [field]) -> Just (RecordReductProjectionLaw field)
    (10, [left, right]) -> Just (RecordSelectorPairDistinctLaw left right)
    (11, []) -> Just RecordSelectorDistinctLaw
    (12, []) -> Just RecordAggregatePairCodedLaw
    (13, [field]) -> Just (RecordAggregateValueUniqueLaw field)
    (14, [field]) -> Just (RecordAggregateEntryLaw field)
    (15, []) -> Just RecordAggregateSelectorClosedLaw
    (16, [field]) -> Just (RecordAggregateProjectionApplicationLaw field)
    (17, []) -> Just RecordAggregateFunctionalLaw
    (18, []) -> Just RecordAggregateExactLaw
    (19, [field]) -> Just (RecordAggregateProjectionLaw field)
    _ -> Nothing

-- | The transparent selector and projection for one record field, constructed
-- together so the projection reuses the selector identity.
data FieldObjects = FieldObjects
    !AssertedObject
    !AssertedObject

fieldObjects :: TheoryId -> FieldId -> FieldObjects
fieldObjects theory identity =
    let selector =
            transparentObject theory TySet (fieldSelectorBody identity)
        selectorId = assertedObjectId selector
        projection =
            transparentObject
                theory
                (TyArrow TySet TySet)
                (fieldProjectionBody selectorId)
    in FieldObjects selector projection

fieldObjectsSelector :: FieldObjects -> AssertedObject
fieldObjectsSelector (FieldObjects selector _projection) =
    selector

fieldObjectsProjection :: FieldObjects -> AssertedObject
fieldObjectsProjection (FieldObjects _selector projection) =
    projection


-- | A stable, transparent set code for one structure field.
--
-- The 256 bits of the field digest are the leaves of a fixed balanced binary
-- tree.  Ordered-pair injectivity makes the tree encoding injective, while the
-- empty set and its singleton give two checked, extensionally distinct bit
-- values.  The representation is deliberately hidden behind a transparent
-- global object when it is used by a record, so ordinary projection terms do
-- not duplicate this tree.
fieldSelectorBody :: FieldId -> CanonicalTerm global
fieldSelectorBody =
    balancedTree
        . fmap bitCode
        . digestBits
        . fieldIdDigest

fieldSelectorObjectId :: TheoryId -> FieldId -> ObjectId
fieldSelectorObjectId theory identity =
    transparentObjectId
        theory
        TySet
        (fieldSelectorBody identity)

fieldSelectorObject :: TheoryId -> FieldId -> AssertedObject
fieldSelectorObject theory identity =
    transparentObject theory TySet (fieldSelectorBody identity)

-- | The totalized lookup function for one field selector.
--
-- For a record @r@, retain the entries whose first projection is the field
-- selector, replace each by its second projection, and take the union of the
-- resulting value set.  A functional graph with that selector therefore
-- yields its unique value.  If the selector is absent, separation and
-- replacement both produce the empty set and the final union is empty, in
-- agreement with Felix's existing set-function application contract.
fieldProjectionBody :: ObjectId -> CanonicalTerm ObjectId
fieldProjectionBody selector =
    CLam TySet
        (recordLookup (CGlobal selector) (CBound 0))

fieldProjectionObjectId
    :: TheoryId
    -> FieldId
    -> ObjectId
fieldProjectionObjectId theory identity =
    transparentObjectId
        theory
        (TyArrow TySet TySet)
        (fieldProjectionBody
            (fieldSelectorObjectId theory identity))

fieldProjectionObject
    :: TheoryId
    -> FieldId
    -> AssertedObject
fieldProjectionObject theory identity =
    let body =
            fieldProjectionBody
                (fieldSelectorObjectId theory identity)
        coreType = TyArrow TySet TySet
    in transparentObject theory coreType body

-- | The checked construction view of a field projection.  Its canonical body
-- is exactly 'fieldProjectionBody'; the construction kernel can therefore
-- derive a flattened first-order membership interface without changing the
-- transparent projection representation.
fieldProjectionConstruction
    :: GlobalTyping ObjectId
    -> ObjectId
    -> Maybe (SetConstruction.NamedSetConstruction ObjectId)
fieldProjectionConstruction globalTyping selector = do
    domain <- checked [TySet] TySet (CBound 0)
    value <- checked [TySet, TySet] TySet
        (secondCoordinate (CBound 0))
    condition <- checked [TySet, TySet] TyProp
        (CEq TySet
            (firstCoordinate (CBound 0))
            (CGlobal selector))
    SetConstruction.checkedFamilyUnionReplacementConstruction
        globalTyping domain value (Just condition)
  where
    checked context coreType term = do
        result <- either (const Nothing) Just
            (checkScopedCanonicalCore globalTyping context term)
        guard (scopedCoreType result == coreType)
        pure result

-- | The flattened membership theorem derived for one transparent projection.
recordProjectionMembershipLaw
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordProjectionMembershipLaw selector projection =
    CForall TySet
        (CForall TySet
            (CEq TyProp
                (member
                    (CBound 0)
                    (CApp
                        (shiftCanonical 2 0 projection)
                        (CBound 1)))
                (existsSet
                    (conjunction2
                        (member
                            (CBound 0)
                            (CBound 2))
                        (conjunction2
                            (CEq TySet
                                (firstCoordinate (CBound 0))
                                (shiftCanonical 3 0 selector))
                            (member
                                (CBound 1)
                                (secondCoordinate (CBound 0))))))))

-- | A functional record returns the value of its unique entry at a selector.
-- This first-order consequence is proved from the flattened projection
-- membership interface rather than by unfolding the higher-order body.
recordProjectionEntryLaw
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordProjectionEntryLaw selector projection =
    CForall TySet
        (CForall TySet
            (CImp
                (recordFunctional (CBound 1))
                (CImp
                    (member
                        (orderedPair
                            (shiftCanonical 2 0 selector)
                            (CBound 0))
                        (CBound 1))
                    (CEq TySet
                        (CApp
                            (shiftCanonical 2 0 projection)
                            (CBound 1))
                        (CBound 0)))))

-- | Totalized projection returns the empty set when a functional record has
-- no entry at the selected field.
recordProjectionMissingLaw
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordProjectionMissingLaw selector projection =
    CForall TySet
        (CImp
            (recordFunctional (CBound 0))
            (CImp
                (negation
                    (selectorPresent
                        (shiftCanonical 1 0 selector)
                        (CBound 0)))
                (CEq TySet
                    (CApp
                        (shiftCanonical 1 0 projection)
                        (CBound 0))
                    (CIntrinsic Empty))))

-- | Equal projected values determine the same entry at one present selector
-- of two functional records.  These are the sharp hypotheses: no information
-- about the rest of either schema is needed.  Structure lowering proves this
-- component once per field so record extensionality scales linearly with the
-- width of a schema.
recordSchemaProjectionAgreementLaw
    :: (CanonicalTerm global, CanonicalTerm global)
    -> CanonicalTerm global
recordSchemaProjectionAgreementLaw (selector, projection) =
    CForall TySet
        (CForall TySet
            (CImp
                (recordFunctional (CBound 1))
                (CImp
                    (recordFunctional (CBound 0))
                    (CImp
                        (selectorPresent
                            (shiftCanonical 2 0 selector)
                            (CBound 1))
                        (CImp
                            (selectorPresent
                                (shiftCanonical 2 0 selector)
                                (CBound 0))
                            (CImp
                                (CEq TySet
                                    (CApp
                                        (shiftCanonical 2 0 projection)
                                        (CBound 1))
                                    (CApp
                                        (shiftCanonical 2 0 projection)
                                        (CBound 0)))
                                (CForall TySet
                                    (equivalence
                                        (member
                                            (orderedPair
                                                (shiftCanonical 3 0 selector)
                                                (CBound 0))
                                            (CBound 2))
                                        (member
                                            (orderedPair
                                                (shiftCanonical 3 0 selector)
                                                (CBound 0))
                                            (CBound 1))))))))))

-- | Pointwise equality of all schema projections yields agreement at each
-- named schema entry.  This is the finite join of the independent fieldwise
-- projection-agreement laws.
recordSchemaProjectionEntryAgreementLaw
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> CanonicalTerm global
recordSchemaProjectionEntryAgreementLaw fields =
    CForall TySet
        (CForall TySet
            (CImp
                (recordExactShape shiftedSelectors (CBound 1))
                (CImp
                    (recordExactShape shiftedSelectors (CBound 0))
                    (CImp
                        (conjunction
                            [ CEq TySet
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 1))
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 0))
                            | (_selector, projection) <- fields
                            ])
                        (conjunction
                            [ CForall TySet
                                (equivalence
                                    (member
                                        (orderedPair
                                            (shiftCanonical 3 0 selector)
                                            (CBound 0))
                                        (CBound 2))
                                    (member
                                        (orderedPair
                                            (shiftCanonical 3 0 selector)
                                            (CBound 0))
                                        (CBound 1)))
                            | (selector, _projection) <- fields
                            ])))))
  where
    shiftedSelectors =
        [ shiftCanonical 2 0 selector
        | (selector, _projection) <- fields
        ]

-- | Schema-entry agreement extends to extensional agreement of two exact
-- record graphs.  Structure lowering keeps this graph argument separate from
-- both the finite fieldwise join and the final use of set extensionality.
recordSchemaProjectionGraphAgreementLaw
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> CanonicalTerm global
recordSchemaProjectionGraphAgreementLaw fields =
    CForall TySet
        (CForall TySet
            (CImp
                (recordExactShape shiftedSelectors (CBound 1))
                (CImp
                    (recordExactShape shiftedSelectors (CBound 0))
                    (CImp
                        (conjunction
                            [ CEq TySet
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 1))
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 0))
                            | (_selector, projection) <- fields
                            ])
                        (CForall TySet
                            (equivalence
                                (member (CBound 0) (CBound 2))
                                (member (CBound 0) (CBound 1))))))))
  where
    shiftedSelectors =
        [ shiftCanonical 2 0 selector
        | (selector, _projection) <- fields
        ]

-- | Exact records over one schema are equal when all their field projections
-- agree.  The checked proof combines the flattened projection interfaces
-- with graph-level exact extensionality.
recordSchemaProjectionExtensionalityLaw
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> CanonicalTerm global
recordSchemaProjectionExtensionalityLaw fields =
    CForall TySet
        (CForall TySet
            (CImp
                (recordExactShape selectors (CBound 1))
                (CImp
                    (recordExactShape selectors (CBound 0))
                    (CImp
                        (conjunction
                            [ CEq TySet
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 1))
                                (CApp
                                    (shiftCanonical 2 0 projection)
                                    (CBound 0))
                            | (_selector, projection) <- fields
                            ])
                        (CEq TySet (CBound 1) (CBound 0))))))
  where
    selectors =
        [ shiftCanonical 2 0 selector
        | (selector, _projection) <- fields
        ]

-- | Pairwise distinctness of a schema's stable selector codes.  Structure
-- declaration lowering proves this once from the transparent FieldId
-- encodings, then keeps those large definition bodies out of the reusable
-- aggregate interface.
recordSelectorDistinctLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSelectorDistinctLaw selectors =
    conjunction (recordSelectorDistinctLaws selectors)

-- | The independently checkable pairwise components of
-- 'recordSelectorDistinctLaw'.  Wide schemas must not force one prover task
-- to expand every transparent selector body at once.
recordSelectorDistinctLaws
    :: [CanonicalTerm global]
    -> [CanonicalTerm global]
recordSelectorDistinctLaws selectors =
    [ negation (CEq TySet left right)
    | (index, left) <- zip [0 :: Int ..] selectors
    , right <- drop (index + 1) selectors
    ]

-- | Every member of a transparent aggregate is a checked ordered-pair code.
recordSchemaAggregatePairCodedLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaAggregatePairCodedLaw selectors =
    closeSchemaAggregateLaw selectors
        (recordPairCoded (recordAggregateContextTerm context))
  where
    context = recordSchemaAggregateContext selectors

-- | At each selector, a transparent aggregate contains no value other than
-- the one assigned by the aggregate.  Proving these cases independently is
-- the scalable checked core of aggregate right uniqueness.
recordSchemaAggregateValueUniqueLaws
    :: [CanonicalTerm global]
    -> [CanonicalTerm global]
recordSchemaAggregateValueUniqueLaws selectors =
    [ closeSchemaAggregateLaw selectors
        (CForall TySet
            (CImp
                (member
                    (orderedPair
                        (shiftCanonical 1 0 selector)
                        (CBound 0))
                    (shiftCanonical 1 0 aggregate))
                (CEq TySet
                    (CBound 0)
                    (shiftCanonical 1 0 value))))
    | (selector, value) <- zip shiftedSelectors values
    ]
  where
    context = recordSchemaAggregateContext selectors
    shiftedSelectors = recordAggregateContextSelectors context
    values = recordAggregateContextValues context
    aggregate = recordAggregateContextTerm context

-- | Each field's assigned selector-value pair belongs to the transparent
-- aggregate.
recordSchemaAggregateEntryLaws
    :: [CanonicalTerm global]
    -> [CanonicalTerm global]
recordSchemaAggregateEntryLaws selectors =
    [ closeSchemaAggregateLaw selectors
        (member (orderedPair selector value) aggregate)
    | (selector, value) <- zip shiftedSelectors values
    ]
  where
    context = recordSchemaAggregateContext selectors
    shiftedSelectors = recordAggregateContextSelectors context
    values = recordAggregateContextValues context
    aggregate = recordAggregateContextTerm context

-- | A transparent aggregate contains no selector outside its schema.
recordSchemaAggregateSelectorClosedLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaAggregateSelectorClosedLaw selectors =
    closeSchemaAggregateLaw selectors
        (selectorClosed shiftedSelectors aggregate)
  where
    context = recordSchemaAggregateContext selectors
    shiftedSelectors = recordAggregateContextSelectors context
    aggregate = recordAggregateContextTerm context

-- | Functionality of the complete aggregate, derived from pair coding,
-- selector closure, and the per-selector value-uniqueness laws.
recordSchemaAggregateFunctionalLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaAggregateFunctionalLaw selectors =
    closeSchemaAggregateLaw selectors
        (recordFunctional aggregate)
  where
    aggregate =
        recordAggregateContextTerm
            (recordSchemaAggregateContext selectors)

-- | The independent finite-graph invariants from which aggregate exactness
-- follows after functionality has been checked in its own stage.
recordSchemaAggregateComponentLaws
    :: [CanonicalTerm global]
    -> [CanonicalTerm global]
recordSchemaAggregateComponentLaws selectors =
    [recordSchemaAggregateFunctionalLaw selectors]
        <> recordSchemaAggregateEntryLaws selectors
        <> [recordSchemaAggregateSelectorClosedLaw selectors]

data RecordAggregateContext global = RecordAggregateContext
    { recordAggregateContextSelectors
        :: ![CanonicalTerm global]
    , recordAggregateContextValues
        :: ![CanonicalTerm global]
    , recordAggregateContextTerm
        :: !(CanonicalTerm global)
    }

recordSchemaAggregateContext
    :: [CanonicalTerm global]
    -> RecordAggregateContext global
recordSchemaAggregateContext selectors =
    RecordAggregateContext shiftedSelectors values aggregate
  where
    binderCount = fromIntegral (length selectors)
    shiftedSelectors = shiftCanonical binderCount 0 <$> selectors
    values =
        reverse
            [ CBound (fromIntegral index)
            | index <- [0 .. length selectors - 1]
            ]
    aggregate = recordAggregate (zip shiftedSelectors values)

closeSchemaAggregateLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
closeSchemaAggregateLaw selectors term =
    foldr (const (CForall TySet)) term selectors

-- | Exactness of the transparent finite aggregate of one schema.  Declaration
-- lowering proves this closed law from checked functionality, concrete-entry,
-- and selector-closure consequences.
recordSchemaAggregateExactLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaAggregateExactLaw selectors =
    foldr
        (const (CForall TySet))
        (recordExactShape shiftedSelectors aggregate)
        selectors
  where
    context = recordSchemaAggregateContext selectors
    shiftedSelectors = recordAggregateContextSelectors context
    aggregate = recordAggregateContextTerm context

-- | The generic projection-entry theorem specialized to each field of a
-- transparent aggregate, but with functionality and entry membership left
-- as hypotheses.  Checking this small instantiation separately keeps the
-- large finite graph out of the ATP's theorem-matching search when the final
-- unconditional projection equation is discharged.
recordSchemaAggregateProjectionApplicationLaws
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> [CanonicalTerm global]
recordSchemaAggregateProjectionApplicationLaws fields =
    [ close
        (CImp
            (recordFunctional aggregate)
            (CImp
                (member (orderedPair selector value) aggregate)
                (CEq TySet
                    (CApp projection aggregate)
                    value)))
    | ((selector, projection), value) <- zip shiftedFields values
    ]
  where
    binderCount = fromIntegral (length fields)
    close term = foldr (const (CForall TySet)) term fields
    shiftedFields =
        [ ( shiftCanonical binderCount 0 selector
          , shiftCanonical binderCount 0 projection
          )
        | (selector, projection) <- fields
        ]
    values =
        recordAggregateContextValues context
    aggregate = recordAggregateContextTerm context
    context =
        recordSchemaAggregateContext
            [ selector
            | (selector, _projection) <- fields
            ]

-- | One unconditional projection equation for each field of a transparent
-- aggregate.  The declaration proof for an equation consumes checked
-- aggregate functionality and entry membership together with the specialized
-- form of that projection's flattened entry theorem.
recordSchemaAggregateProjectionLaws
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> [CanonicalTerm global]
recordSchemaAggregateProjectionLaws fields =
    [ foldr
        (const (CForall TySet))
        (CEq TySet
            (CApp projection aggregate)
            value)
        fields
    | ((_, projection), value) <- zip shiftedFields values
    ]
  where
    binderCount = fromIntegral (length fields)
    shiftedFields =
        [ ( shiftCanonical binderCount 0 selector
          , shiftCanonical binderCount 0 projection
          )
        | (selector, projection) <- fields
        ]
    values =
        recordAggregateContextValues context
    aggregate = recordAggregateContextTerm context
    context =
        recordSchemaAggregateContext
            [ selector
            | (selector, _projection) <- fields
            ]


-- | A record is a set of primitive ordered pairs that is right-unique in its
-- first coordinate.  Requiring each entry to be reconstructed by the checked
-- projections excludes arbitrary non-pair junk from the graph.
recordFunctional
    :: CanonicalTerm global
    -> CanonicalTerm global
recordFunctional record =
    conjunction
        [ recordPairCoded record
        , recordRightUnique record
        ]

recordPairCoded
    :: CanonicalTerm global
    -> CanonicalTerm global
recordPairCoded record =
    CForall TySet
        (CImp
            (member (CBound 0) (shiftCanonical 1 0 record))
            (CEq TySet
                (CBound 0)
                (orderedPair
                    (firstCoordinate (CBound 0))
                    (secondCoordinate (CBound 0)))))

recordRightUnique
    :: CanonicalTerm global
    -> CanonicalTerm global
recordRightUnique record =
    CForall TySet
        (CForall TySet
            (CImp
                (conjunction
                    [ member
                        (CBound 1)
                        (shiftCanonical 2 0 record)
                    , member
                        (CBound 0)
                        (shiftCanonical 2 0 record)
                    , CEq TySet
                        (firstCoordinate (CBound 1))
                        (firstCoordinate (CBound 0))
                    ])
                (CEq TySet
                    (secondCoordinate (CBound 1))
                    (secondCoordinate (CBound 0)))))

-- | Open shape requires a functional record containing every selected field;
-- additional selector-value entries remain permitted.
recordOpenShape
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
recordOpenShape selectors record =
    conjunction
        (recordFunctional record
            : [ selectorPresent selector record
              | selector <- selectors
              ])

-- | Exact shape additionally excludes selectors outside the schema.
recordExactShape
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
recordExactShape selectors record =
    conjunction
        [ recordOpenShape selectors record
        , selectorClosed selectors record
        ]

-- | Strictly invert the checked exact-shape syntax emitted for global record
-- selectors.  Reconstruction is the final authority: the structural walk
-- only recovers a candidate subject and selector order.
recognizeRecordExactGlobalShape
    :: Eq global
    => ScopedCheckedCore global
    -> Maybe (CanonicalTerm global, [global])
recognizeRecordExactGlobalShape checked = do
    guard (scopedCoreType checked == TyProp)
    let proposition = scopedCoreTerm checked
    closure <- case proposition of
        CAnd _openShape selectorClosure -> pure selectorClosure
        _ -> Nothing
    (shiftedSubject, selectorTests) <- case closure of
        CForall TySet
                (CImp
                    (CApp
                        (CApp (CIntrinsic Member) (CBound 0))
                        subject)
                    tests) ->
            pure (subject, tests)
        _ -> Nothing
    subject <- removeInnermostBinder shiftedSubject
    selectors <-
        traverse recognizeSelectorTest
            =<< flattenSelectorTests selectorTests
    guard
        ( recordExactShape (CGlobal <$> selectors) subject
            == proposition
        )
    pure (subject, selectors)
  where
    recognizeSelectorTest = \case
        CEq TySet
                (CApp (CIntrinsic FirstProjection) (CBound 0))
                (CGlobal selector) ->
            Just selector
        _ -> Nothing

    flattenSelectorTests = \case
        CFalsum -> Just []
        COr left right ->
            (<>)
                <$> flattenSelectorTests left
                <*> flattenSelectorTests right
        test -> Just [test]

-- Remove exactly the binder introduced around the selector-closure
-- membership test.  A reference to that binder is rejected rather than
-- captured; binders already nested inside the subject remain untouched.
removeInnermostBinder
    :: CanonicalTerm global
    -> Maybe (CanonicalTerm global)
removeInnermostBinder = go 0
  where
    go localDepth = \case
        CBound index
            | index < localDepth -> pure (CBound index)
            | index == localDepth -> Nothing
            | otherwise -> pure (CBound (index - 1))
        CGlobal global -> pure (CGlobal global)
        CIntrinsic intrinsic -> pure (CIntrinsic intrinsic)
        CLogicalSelect coreType -> pure (CLogicalSelect coreType)
        COpaqueInteger integer -> pure (COpaqueInteger integer)
        CApp function argument ->
            CApp <$> go localDepth function <*> go localDepth argument
        CLam binderType body ->
            CLam binderType <$> go (localDepth + 1) body
        CFalsum -> pure CFalsum
        CTruth -> pure CTruth
        CNot proposition -> CNot <$> go localDepth proposition
        CAnd left right ->
            CAnd <$> go localDepth left <*> go localDepth right
        COr left right ->
            COr <$> go localDepth left <*> go localDepth right
        CImp premise conclusion ->
            CImp <$> go localDepth premise <*> go localDepth conclusion
        CEq operandType left right ->
            CEq operandType <$> go localDepth left <*> go localDepth right
        CForall binderType body ->
            CForall binderType <$> go (localDepth + 1) body
        CExists binderType body ->
            CExists binderType <$> go (localDepth + 1) body

selectorClosed
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
selectorClosed selectors record =
    CForall TySet
        (CImp
            (member (CBound 0) (shiftCanonical 1 0 record))
            (disjunction
                [ CEq TySet
                    (firstCoordinate (CBound 0))
                    (shiftCanonical 1 0 selector)
                | selector <- selectors
                ]))

-- | The transparent finite graph denoted by an aggregate.
recordAggregate
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> CanonicalTerm global
recordAggregate =
    foldr
        (\(selector, value) graph ->
            canonicalSetInsert
                (orderedPair selector value)
                graph)
        (CIntrinsic Empty)

-- | Totalized lookup of a selector in an arbitrary set.
recordLookup
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordLookup selector record =
    CApp
        (CIntrinsic FamilyUnion)
        (CApp
            (CApp (CIntrinsic Repl) matchingEntries)
            (CLam TySet
                (secondCoordinate (CBound 0))))
  where
    matchingEntries =
        CApp
            (CApp (CIntrinsic Sep) record)
            (CLam TySet
                (CEq TySet
                    (firstCoordinate (CBound 0))
                    (shiftCanonical 1 0 selector)))

-- | Restrict a record graph to the selectors of one schema.
recordReduct
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
recordReduct selectors record =
    CApp
        (CApp (CIntrinsic Sep) record)
        (CLam TySet
            (disjunction
                [ CEq TySet
                    (firstCoordinate (CBound 0))
                    (shiftCanonical 1 0 selector)
                | selector <- selectors
                ]))

-- | The graph-level extensionality core.  This first-order form avoids
-- unfolding totalized application: exact records with the same entry at each
-- schema selector are the same set.  Projection extensionality is derived by
-- combining this fact with the checked set-function application interface.
recordExactGraphExtensionality
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordExactGraphExtensionality selectors left right =
    CImp
        (recordExactShape selectors left)
        (CImp
            (recordExactShape selectors right)
            (CImp
                (conjunction
                    [ CForall TySet
                        (equivalence
                            (member
                                (orderedPair
                                    (shiftCanonical 1 0 selector)
                                    (CBound 0))
                                (shiftCanonical 1 0 left))
                            (member
                                (orderedPair
                                    (shiftCanonical 1 0 selector)
                                    (CBound 0))
                                (shiftCanonical 1 0 right)))
                    | selector <- selectors
                    ])
                (CEq TySet left right)))

-- | Restricting an open record to a schema yields an exact record for that
-- schema.  This says only something about record shape; mathematical parent
-- laws are transferred separately from the corresponding structure premise.
recordReductExact
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
recordReductExact selectors record =
    CImp
        (recordOpenShape selectors record)
        (recordExactShape selectors
            (recordReduct selectors record))

-- | Membership in a reduct is precisely membership in the original graph at
-- one of the retained selectors.
recordReductMembership
    :: [CanonicalTerm global]
    -> CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
recordReductMembership selectors entry record =
    equivalence
        (member entry (recordReduct selectors record))
        (conjunction
            [ member entry record
            , disjunction
                [ CEq TySet
                    (firstCoordinate entry)
                    selector
                | selector <- selectors
                ]
            ])

-- | Closed first-order exact-record extensionality for one schema.
recordSchemaExactGraphLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaExactGraphLaw selectors =
    CForall TySet
        (CForall TySet
            (recordExactGraphExtensionality
                (shiftCanonical 2 0 <$> selectors)
                (CBound 1)
                (CBound 0)))

-- | Closed exactness of schema restriction.
recordSchemaReductExactLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaReductExactLaw selectors =
    CForall TySet
        (recordReductExact
            (shiftCanonical 1 0 <$> selectors)
            (CBound 0))

-- | Closed membership characteristic of schema restriction.
recordSchemaReductMembershipLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaReductMembershipLaw selectors =
    CForall TySet
        (CForall TySet
            (recordReductMembership
                (shiftCanonical 2 0 <$> selectors)
                (CBound 0)
                (CBound 1)))

-- | Restricting an already exact record to its own schema is the identity.
-- Structure lowering publishes this law directly so clients need not recover
-- it indirectly through every field projection.
recordSchemaReductIdentityLaw
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaReductIdentityLaw selectors =
    CForall TySet
        (CImp
            (recordExactShape shiftedSelectors (CBound 0))
            (CEq TySet
                (recordReduct shiftedSelectors (CBound 0))
                (CBound 0)))
  where
    shiftedSelectors = shiftCanonical 1 0 <$> selectors

-- | Restriction to a schema preserves every projection named by that schema.
-- The declaration checker proves these equations from the flattened reduct-
-- membership and projection-membership interfaces.  Keeping the result as a
-- focused equation avoids unfolding totalized lookup in every user proof.
recordSchemaReductProjectionLaws
    :: [(CanonicalTerm global, CanonicalTerm global)]
    -> [CanonicalTerm global]
recordSchemaReductProjectionLaws fields =
    [ CForall TySet
        (CEq TySet
            (CApp
                (shiftCanonical 1 0 projection)
                (recordReduct shiftedSelectors (CBound 0)))
            (CApp
                (shiftCanonical 1 0 projection)
                (CBound 0)))
    | (_selector, projection) <- fields
    ]
  where
    shiftedSelectors =
        [ shiftCanonical 1 0 selector
        | (selector, _projection) <- fields
        ]

-- | Closed record-core laws for schema restriction.  Keeping this fact free
-- of projection globals makes it reusable for inherited fields without
-- duplicating their definition equations.
recordSchemaReductCoreLaws
    :: [CanonicalTerm global]
    -> CanonicalTerm global
recordSchemaReductCoreLaws selectors =
    conjunction
        [ recordSchemaReductExactLaw selectors
        , recordSchemaReductMembershipLaw selectors
        ]

selectorPresent
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
selectorPresent selector record =
    existsSet
        (member
            (orderedPair
                (shiftCanonical 1 0 selector)
                (CBound 0))
            (shiftCanonical 1 0 record))

member
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
member element set =
    CApp
        (CApp (CIntrinsic Member) element)
        set

orderedPair
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
orderedPair left right =
    CApp
        (CApp (CIntrinsic OrderedPair) left)
        right

firstCoordinate :: CanonicalTerm global -> CanonicalTerm global
firstCoordinate =
    CApp (CIntrinsic FirstProjection)

secondCoordinate :: CanonicalTerm global -> CanonicalTerm global
secondCoordinate =
    CApp (CIntrinsic SecondProjection)

conjunction :: [CanonicalTerm global] -> CanonicalTerm global
conjunction = \case
    [] -> CTruth
    first : rest -> foldl' conjunction2 first rest

conjunction2
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
conjunction2 left right =
    CAnd left right

equivalence
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
equivalence left right =
    conjunction
        [ CImp left right
        , CImp right left
        ]

disjunction :: [CanonicalTerm global] -> CanonicalTerm global
disjunction = \case
    [] -> CFalsum
    first : rest -> foldl' disjunction2 first rest

disjunction2
    :: CanonicalTerm global
    -> CanonicalTerm global
    -> CanonicalTerm global
disjunction2 left right =
    COr left right

existsSet :: CanonicalTerm global -> CanonicalTerm global
existsSet body =
    CExists TySet body

negation :: CanonicalTerm global -> CanonicalTerm global
negation = CNot


digestBits :: MathematicalDigest -> [Bool]
digestBits =
    concatMap byteBits
        . ByteString.unpack
        . mathematicalDigestBytes

byteBits :: Word8 -> [Bool]
byteBits byte =
    [ testBit byte index
    | index <- [7, 6 .. 0]
    ]

bitCode :: Bool -> CanonicalTerm global
bitCode = \case
    False -> emptySet
    True -> singleton emptySet
  where
    emptySet = CIntrinsic Empty
    singleton element =
        CApp
            (CApp (CIntrinsic PairSet) element)
            element

balancedTree :: [CanonicalTerm global] -> CanonicalTerm global
balancedTree = \case
    [] -> impossible "a mathematical digest has no bits"
    [single] -> single
    leaves -> balancedTree (pairAdjacent leaves)
  where
    pairAdjacent = \case
        [] -> []
        left : right : rest ->
            orderedPair left right : pairAdjacent rest
        [_unpaired] ->
            impossible "a digest-tree level has odd width"
