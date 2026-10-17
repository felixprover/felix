{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

-- | Source syntax retained by elaboration. Residual subexpressions retain
-- exact formula identity without acquiring atomic matching capabilities.
module Felix.Checking.Notion.SourceEvidence
    ( SourceEvidence(..), SourceInput(..)
    , WrittenOrigin(..)
    , SourceLeaf(..)
    , LeafDescription(..)
    , notionLeaves
    , AtomTree(..)
    , UniversalBody(..), universalBodyWith, universalEvidenceWith
    , UniversalOperand(..)
    , UniversalElimination(..)
    , SourceView(..)
    , directAtoms
    , sourceViews
    , sourceViewsWith
    , traverseAtDepth, traverseSourceAtDepth
    , withSourceInputs, sourceInputAnnotationsWith
    , writtenSourceEvidence
    , sourceInputsAtDepth, sourceInputOccursWith
    , zipUniversalBody
    , atomTreeLeaves
    ) where

import Base
import Control.DeepSeq (NFData)
import Data.Functor.Identity (runIdentity)
import Felix.Checking.Elimination (ConjunctionPath(..))
import Felix.Checking.Core
    (CanonicalTerm(..), CoreType(..), ScopedCheckedCore, scopedCoreTerm, splitScopedConjunction, compareCanonicalWith)
import Felix.Report.Location (Location)
import Numeric.Natural (Natural)

data SourceEvidence term atom
    = SourceResidual !(Maybe WrittenOrigin)
    -- Written set operands of an otherwise opaque proposition. These
    -- descriptions are complete, including when empty: Core discovery is
    -- suppressed. They contribute finite support, never facts or matching rows.
    | SourceInputs !(Maybe WrittenOrigin) ![SourceInput term]
    -- Additional written views, independent of the underlying evidence's
    -- complete operand description and inference capabilities.
    | SourceWithInputs ![SourceInput term] !(SourceEvidence term atom)
    | SourceAtom !atom
    | SourceAnd !(SourceEvidence term atom) !(SourceEvidence term atom)
    | SourceOr !(SourceEvidence term atom) !(SourceEvidence term atom)
    | SourceIff !(SourceEvidence term atom) !(SourceEvidence term atom)
    | SourceExists !(SourceEvidence term atom)
    | SourceBind !(SourceEvidence term atom)
    | SourceRequire !(SourceEvidence term atom) !(SourceEvidence term atom)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- The operand is written under these additional nearest-first binders. Keep
-- its complete view until preparation decides which parts are independent.
data SourceInput term = SourceInput ![CoreType] !term
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Preserve the distinction between a complete description (even an empty
-- one) and an additive annotation. Nested annotations retain source order.
withSourceInputs :: [SourceInput term] -> SourceEvidence term atom -> SourceEvidence term atom
withSourceInputs [] evidence = evidence
withSourceInputs outer (SourceWithInputs inner evidence) = withSourceInputs (inner <> outer) evidence
withSourceInputs inputs evidence = SourceWithInputs inputs evidence

-- Retain written operands and views while disabling discovery inside opaque
-- Core. Substitution and calculation captures share this source policy.
writtenSourceEvidence :: SourceEvidence term atom -> SourceEvidence term atom
writtenSourceEvidence = \case
    SourceResidual origin -> SourceInputs origin []
    SourceWithInputs inputs body -> withSourceInputs inputs (writtenSourceEvidence body)
    SourceAnd a b -> SourceAnd (writtenSourceEvidence a) (writtenSourceEvidence b)
    SourceBind body -> SourceBind (writtenSourceEvidence body)
    SourceExists body -> SourceExists (writtenSourceEvidence body)
    SourceOr a b -> SourceOr (writtenSourceEvidence a) (writtenSourceEvidence b)
    SourceIff a b -> SourceIff (writtenSourceEvidence a) (writtenSourceEvidence b)
    SourceRequire a b -> SourceRequire (writtenSourceEvidence a) (writtenSourceEvidence b)
    body -> body

-- Collect annotations at their owning proposition before conjunction leaves
-- are split. This never discovers operands inside opaque Core.
sourceInputAnnotationsWith :: Monad m => m () -> SourceEvidence term atom -> m [SourceInput term]
sourceInputAnnotationsWith charge = go []
  where
    go context expression = charge >> case expression of
        SourceWithInputs inputs body -> do
            nested <- go context body
            extras <- for inputs \(SourceInput binders term) -> charge >> pure (SourceInput (binders <> context) term)
            pure (nested <> extras)
        SourceAnd left right -> (<>) <$> go context left <*> go context right
        SourceOr left right -> (<>) <$> go context left <*> go context right
        SourceIff left right -> (<>) <$> go context left <*> go context right
        SourceExists body -> go (TySet:context) body
        SourceBind body -> go (TySet:context) body
        SourceRequire condition body -> (<>) <$> go context condition <*> go context body
        _ -> pure []

-- Diagnostic provenance is never part of formula or answer identity. A plain
-- written formula has a location; an expansion additionally names its call
-- and the selected path within the checked declaration body.
data WrittenOrigin = WrittenOrigin
    { writtenOriginLocation :: !Location
    , writtenOriginSpelling :: !(Maybe Text)
    , writtenOriginBodyPath :: !ConjunctionPath
    }
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

data LeafDescription atom
    = LeafAtom !atom
    | LeafUniversal !(UniversalBody atom)
    | LeafResidual !(Maybe WrittenOrigin)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data SourceLeaf path formula term atom = SourceLeaf
    { sourceLeafPath :: !path
    , sourceLeafFormula :: !formula
    , sourceLeafDescription :: !(LeafDescription atom)
    , sourceLeafEvidence :: !(SourceEvidence term atom)
    }
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- The admission owner supplies shared path extension. Select checked Core as
-- the evidence spine is visited, never by replaying a full path for each leaf.
-- SourceAtom must precede conjunction inspection: exact structures are single
-- atoms even though their logical encoding is a conjunction.
notionLeaves
    :: Monad m => m () -> (Bool -> path -> m path) -> path
    -> ScopedCheckedCore global -> SourceEvidence term atom
    -> m [SourceLeaf path (ScopedCheckedCore global) term atom]
notionLeaves charge extend root proposition evidence = ($ []) <$> go root proposition evidence
  where
    go path formula expression = charge >> case expression of
        SourceWithInputs _ body -> go path formula body
        SourceAtom atom -> pure (SourceLeaf path formula (LeafAtom atom) expression :)
        SourceAnd left right -> case splitScopedConjunction formula of
            Just (a, b) -> do
                leftPath <- extend False path
                leftLeaves <- go leftPath a left
                rightPath <- extend True path
                rightLeaves <- go rightPath b right
                pure (leftLeaves . rightLeaves)
            Nothing -> impossible "admitted source conjunction lost its checked Core spine"
        SourceResidual origin | CTruth <- scopedCoreTerm formula -> pure id
                             | otherwise -> pure (SourceLeaf path formula (LeafResidual origin) expression :)
        SourceInputs origin _ -> pure (SourceLeaf path formula (LeafResidual origin) expression :)
        SourceBind{} -> universalBodyWith charge expression >>= \case
            Just body -> pure (SourceLeaf path formula (LeafUniversal body) expression :)
            Nothing -> pure (SourceLeaf path formula (LeafResidual Nothing) expression :)
        SourceRequire{} -> pure (SourceLeaf path formula (LeafResidual Nothing) expression :)
        SourceOr{} -> pure (SourceLeaf path formula (LeafResidual Nothing) expression :)
        SourceIff{} -> pure (SourceLeaf path formula (LeafResidual Nothing) expression :)
        SourceExists{} -> pure (SourceLeaf path formula (LeafResidual Nothing) expression :)

data AtomTree atom = AtomLeaf !atom | AtomAnd !(AtomTree atom) !(AtomTree atom)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Guards remain at their original binder depth and in their original blocks.
data UniversalBody atom
    = UniversalReturn !(AtomTree atom)
    | UniversalBind !(UniversalBody atom)
    | UniversalRequire !(AtomTree atom) !(UniversalBody atom)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Inner variables use source order; outer values are rigid terms in the
-- enclosing registration or query context. Traversal visits only outer values.
data UniversalOperand outer = UniversalBound !Natural | UniversalOuter !outer
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data UniversalElimination argument premise
    = EliminateBinder !argument
    | EliminateGuard !premise
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

data SourceView atom
    = AtomicSource !ConjunctionPath !atom
    | UniversalSource !ConjunctionPath !(UniversalBody atom)
    deriving stock (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData)

-- Unopened binders and implications never expose atomic observations.
directAtoms :: SourceEvidence term atom -> [(ConjunctionPath, atom)]
directAtoms = go id
  where
    go path = \case
        SourceWithInputs _ body -> go path body
        SourceAtom atom -> [(path ConjunctionHere, atom)]
        SourceAnd left right ->
            go (path . ConjunctionLeft) left <> go (path . ConjunctionRight) right
        _ -> []

sourceViews :: SourceEvidence term atom -> [SourceView atom]
sourceViews = runIdentity . sourceViewsWith (pure ())

sourceViewsWith :: Monad m => m () -> SourceEvidence term atom -> m [SourceView atom]
sourceViewsWith charge = go id
  where
    go path expression = charge >> case expression of
        SourceWithInputs _ body -> go path body
        SourceAtom atom -> pure [AtomicSource (path ConjunctionHere) atom]
        SourceAnd left right ->
            (<>) <$> go (path . ConjunctionLeft) left <*> go (path . ConjunctionRight) right
        SourceBind{} -> universalBodyWith charge expression >>= \case
            Just universal -> pure [UniversalSource (path ConjunctionHere) universal]
            Nothing -> pure []
        _ -> pure []

universalBodyWith :: Monad m => m () -> SourceEvidence term atom -> m (Maybe (UniversalBody atom))
universalBodyWith charge = body
  where
    atoms expression = charge >> case expression of
        SourceWithInputs _ nested -> atoms nested
        SourceAtom atom -> pure (Just (AtomLeaf atom))
        SourceAnd left right -> liftA2 AtomAnd <$> atoms left <*> atoms right
        _ -> pure Nothing
    body expression = charge >> case expression of
        SourceWithInputs _ nested -> body nested
        SourceBind nested -> fmap UniversalBind <$> body nested
        SourceRequire condition nested -> liftA2 UniversalRequire <$> atoms condition <*> body nested
        _ -> fmap UniversalReturn <$> atoms expression

universalEvidenceWith :: Monad m => m () -> UniversalBody atom -> m (SourceEvidence term atom)
universalEvidenceWith charge = body
  where
    body expression = charge >> case expression of
        UniversalBind nested -> SourceBind <$> body nested
        UniversalRequire condition nested -> SourceRequire <$> atoms condition <*> body nested
        UniversalReturn result -> atoms result
    atoms expression = charge >> case expression of
        AtomLeaf atom -> pure (SourceAtom atom)
        AtomAnd left right -> SourceAnd <$> atoms left <*> atoms right

-- A binder-sensitive map is necessary for substitution and checked weakening:
-- atoms under a universal are not scoped in the enclosing proposition's context.
traverseAtDepth
    :: Applicative m => (Natural -> a -> m b) -> SourceEvidence term a -> m (SourceEvidence term b)
traverseAtDepth = traverseSourceAtDepth (const pure)

traverseSourceAtDepth
    :: Applicative m => (Natural -> term -> m term') -> (Natural -> a -> m b)
    -> SourceEvidence term a -> m (SourceEvidence term' b)
traverseSourceAtDepth input visit = go 0
  where
    go depth = \case
        SourceResidual origin -> pure (SourceResidual origin)
        SourceInputs origin terms -> SourceInputs origin <$> traverse
            (\(SourceInput binders term) -> SourceInput binders <$> input (depth + fromIntegral (length binders)) term) terms
        SourceWithInputs terms body -> withSourceInputs <$> traverse
            (\(SourceInput binders term) -> SourceInput binders <$> input (depth + fromIntegral (length binders)) term) terms
            <*> go depth body
        SourceAtom atom -> SourceAtom <$> visit depth atom
        SourceAnd left right -> SourceAnd <$> go depth left <*> go depth right
        SourceOr left right -> SourceOr <$> go depth left <*> go depth right
        SourceIff left right -> SourceIff <$> go depth left <*> go depth right
        SourceExists nested -> SourceExists <$> go (depth + 1) nested
        SourceBind nested -> SourceBind <$> go (depth + 1) nested
        SourceRequire guard nested -> SourceRequire <$> go depth guard <*> go depth nested

sourceInputsAtDepth :: (atom -> [term]) -> SourceEvidence term atom -> [SourceInput term]
sourceInputsAtDepth operands = go []
  where
    go context = \case
        SourceResidual{} -> []
        SourceInputs _ terms -> [SourceInput (binders <> context) term | SourceInput binders term <- terms]
        SourceWithInputs terms body -> go context body <>
            [SourceInput (binders <> context) term | SourceInput binders term <- terms]
        SourceAtom atom -> SourceInput context <$> operands atom
        SourceAnd a b -> go context a <> go context b
        SourceOr a b -> go context a <> go context b
        SourceIff a b -> go context a <> go context b
        SourceExists body -> go (TySet:context) body
        SourceBind body -> go (TySet:context) body
        SourceRequire a b -> go context a <> go context b

-- Validate a portable operand against its source, including private binders.
-- Inspecting syntax here grants no inference view or domain subterm. Retaining
-- the whole written parent also validates children erased by its expansion.
sourceInputOccursWith
    :: (Monad m, Ord global) => m () -> [CoreType] -> CanonicalTerm global
    -> CanonicalTerm global -> m Bool
sourceInputOccursWith visit binders operand = go []
  where
    go context term = do
        visit
        same <- if context == binders then (== EQ) <$> compareCanonicalWith visit operand term else pure False
        if same then pure True else case term of
            CApp a b -> eitherChild context a b
            CLam ty body -> under context ty body
            CForall ty body -> under context ty body
            CExists ty body -> under context ty body
            CNot body -> go context body
            CAnd a b -> eitherChild context a b
            COr a b -> eitherChild context a b
            CImp a b -> eitherChild context a b
            CEq _ a b -> eitherChild context a b
            _ -> pure False
    under context ty body
        | length context >= length binders = pure False
        | otherwise = go (ty:context) body
    eitherChild context a b = go context a >>= \same -> if same then pure True else go context b

atomTreeLeaves :: AtomTree atom -> [(ConjunctionPath, atom)]
atomTreeLeaves = go id
  where
    go path = \case
        AtomLeaf atom -> [(path ConjunctionHere, atom)]
        AtomAnd left right ->
            go (path . ConjunctionLeft) left <> go (path . ConjunctionRight) right

-- Exact structural zipping preserves the association and telescope of views
-- produced from the same checked source; mismatches are explicit.
zipUniversalBody :: UniversalBody a -> UniversalBody b -> Maybe (UniversalBody (a,b))
zipUniversalBody left right = case (left,right) of
    (UniversalBind a,UniversalBind b) -> UniversalBind <$> zipUniversalBody a b
    (UniversalRequire p a,UniversalRequire q b) -> UniversalRequire <$> atoms p q <*> zipUniversalBody a b
    (UniversalReturn a,UniversalReturn b) -> UniversalReturn <$> atoms a b
    _ -> Nothing
  where
    atoms (AtomLeaf a) (AtomLeaf b) = Just (AtomLeaf (a,b))
    atoms (AtomAnd a b) (AtomAnd c d) = AtomAnd <$> atoms a c <*> atoms b d
    atoms _ _ = Nothing
