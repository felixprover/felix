{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Checked evidence for the distinguished natural-number successor.
--
-- The constructor stays module-private.  Production code carries this value
-- from final-prelude validation rather than treating an arbitrary object with
-- the right type as the meaning of a numeral.
module Felix.Checking.NaturalNumeral
    ( NaturalNumeralBasis
    , naturalNumeralBasisObject
    , naturalNumeralBasisTheory
    , NaturalNumeralBasisError(..)
    , checkNaturalNumeralBasis
    ) where

import Base hiding (Empty)
import Felix.Checking.Core
import Felix.Checking.Foundation
import Felix.Checking.Identity

import Control.Monad (unless)


data NaturalNumeralBasis = NaturalNumeralBasis
    !TheoryId
    !ObjectId

naturalNumeralBasisObject :: NaturalNumeralBasis -> ObjectId
naturalNumeralBasisObject (NaturalNumeralBasis _theory object) = object

naturalNumeralBasisTheory :: NaturalNumeralBasis -> TheoryId
naturalNumeralBasisTheory (NaturalNumeralBasis theory _object) = theory

data NaturalNumeralBasisError
    = NaturalNumeralBasisTheoryMismatch !TheoryId !TheoryId
    | NaturalNumeralBasisObjectMissing !ObjectId
    | NaturalNumeralBasisObjectTypeMismatch !CoreType !CoreType
    | NaturalNumeralBasisObjectNotTransparent !ObjectId
    | NaturalNumeralBasisObjectBodyMismatch !ObjectId
    deriving stock (Show, Eq)

checkNaturalNumeralBasis
    :: CheckedFoundation
    -> CheckedObjectClosure
    -> ObjectId
    -> Either NaturalNumeralBasisError NaturalNumeralBasis
checkNaturalNumeralBasis foundation closure object = do
    unless (actualTheory == expectedTheory)
        (Left
            (NaturalNumeralBasisTheoryMismatch
                expectedTheory actualTheory))
    content <- maybe
        (Left (NaturalNumeralBasisObjectMissing object))
        Right
        (lookupCheckedObjectContent object closure)
    case content of
        TransparentObjectContent contentTheory actualType body -> do
            unless (contentTheory == expectedTheory)
                (Left
                    (NaturalNumeralBasisTheoryMismatch
                        expectedTheory contentTheory))
            unless (actualType == expectedType)
                (Left
                    (NaturalNumeralBasisObjectTypeMismatch
                        expectedType actualType))
            unless (body == expectedSuccessorBody)
                (Left (NaturalNumeralBasisObjectBodyMismatch object))
            pure (NaturalNumeralBasis expectedTheory object)
        other -> do
            unless (objectContentType other == expectedType)
                (Left
                    (NaturalNumeralBasisObjectTypeMismatch
                        expectedType
                        (objectContentType other)))
            Left (NaturalNumeralBasisObjectNotTransparent object)
  where
    expectedTheory = theoryId foundation
    actualTheory = checkedObjectClosureTheory closure
    expectedType = TyArrow TySet TySet

expectedSuccessorBody :: CanonicalTerm ObjectId
expectedSuccessorBody =
    CLam TySet
        (canonicalSetInsert (CBound 0) (CBound 0))
