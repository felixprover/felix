{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact proposition identities owned by one nominal scope. Scope extension
-- preserves the checked prefix; sibling scopes and requirement groups retain
-- their own immutable tables. IDs never escape with a selected proof or cache.
module Felix.Checking.Notion.FormulaIndex
    ( FormulaId, Formulas, FormulaFailure(..)
    , emptyFormulas, emptyFormulasWithHash
    , extendFormulas, internFormula, lookupFormula
    , FormulaTemplateId, prepareFormulaTemplate, instantiateFormulaTemplate
    , ResidualShape, residualShape, residualShapeFromChildren, residualShapeWork, residualShapeHash, residualShapeIntroducible, prepareFormulaShape
    ) where

import Base
import Control.Monad (unless)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Data.Word (Word)
import Felix.Checking.Core
import Felix.Checking.Core.StableCode (coreIntrinsicTagCode)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Notion.LeafIndex (OpaqueLeaf)
import Numeric.Natural (Natural)

newtype FormulaId = FormulaId Int
    deriving (Show, Eq, Ord)

type LevelFormula = CanonicalTerm (Either Natural ObjectId)

data Connective = Conjunction | Disjunction | Implication | Biconditional
    deriving (Eq, Ord, Enum)

data FormulaKey = ExactKey !LevelFormula | CompoundKey !Connective !FormulaId !FormulaId

data Formula = Formula !(ScopedCheckedCore ObjectId) !FormulaKey !(Maybe ResidualShape)

newtype FormulaTemplateId = FormulaTemplateId Int
    deriving (Eq, Ord)

data TemplateKey
    = TemplateLeaf !Natural !(ScopedCheckedCore ObjectId) !LevelFormula
    | TemplateCompound !Connective !FormulaTemplateId !FormulaTemplateId

data FormulaTemplate = FormulaTemplate !TemplateKey !(Set Natural)


-- Set operands cannot affect relevance: substituting an outer set parameter
-- preserves this shape. Bound predicate heads retain their type, not a set
-- argument or a de Bruijn index that could change under scope extension.
data ShapeHead = ShapeGlobal !ObjectId | ShapeIntrinsic !Int | ShapeBound !CoreType | ShapeOpaque
    deriving (Show, Eq, Ord)

data Shape
    = ShapeTruth | ShapeFalsum | ShapeNot !Shape
    | ShapeAnd !Shape !Shape | ShapeOr !Shape !Shape | ShapeImp !Shape !Shape
    | ShapeIff !Shape !Shape
    | ShapeEquality !CoreType | ShapeForall !CoreType !Shape | ShapeExists !CoreType !Shape
    | ShapeApplication !ShapeHead !Natural
    deriving (Show, Eq, Ord)

data ResidualShape = ResidualShape !Int !Shape !Natural
    deriving (Show, Eq, Ord)

residualShapeWork :: ResidualShape -> Natural
residualShapeWork (ResidualShape _ _ size) = size

residualShapeHash :: ResidualShape -> Int
residualShapeHash (ResidualShape digest _ _) = digest

residualShapeIntroducible :: ResidualShape -> Bool
residualShapeIntroducible (ResidualShape _ shape _) = case shape of
    ShapeTruth -> True
    ShapeAnd{} -> True
    ShapeOr{} -> True
    ShapeIff{} -> True
    ShapeExists TySet _ -> True
    ShapeEquality TySet -> True
    ShapeImp{} -> True
    ShapeForall TySet _ -> True
    _ -> False

-- Compound descriptions retain child shapes and their already computed hashes.
-- Building all suffixes of a query therefore visits each connective once.
residualShape :: Monad m => m () -> [CoreType] -> CanonicalTerm ObjectId -> m ResidualShape
residualShape debit context formula = do
    children <- case formula of
        CNot body -> traverse (residualShape debit context) [body]
        CAnd a b -> binary a b
        COr a b -> binary a b
        CImp a b -> binary a b
        CEq TyProp a b -> binary a b
        CForall ty body -> traverse (residualShape debit (ty:context)) [body]
        CExists ty body -> traverse (residualShape debit (ty:context)) [body]
        _ -> pure []
    residualShapeFromChildren debit context formula children
  where
    binary a b = traverse (residualShape debit context) [a,b]

residualShapeFromChildren
    :: Monad m => m () -> [CoreType] -> CanonicalTerm ObjectId -> [ResidualShape]
    -> m ResidualShape
residualShapeFromChildren debit context formula children = case (formula,children) of
    (CNot _,[a]) -> unary 2 ShapeNot a
    (CAnd _ _,[a,b]) -> binary 3 ShapeAnd a b
    (COr _ _,[a,b]) -> binary 4 ShapeOr a b
    (CImp _ _,[a,b]) -> binary 5 ShapeImp a b
    (CEq TyProp _ _,[a,b]) -> binary 6 ShapeIff a b
    (CForall ty _,[a]) -> binder 8 ShapeForall ty a
    (CExists ty _,[a]) -> binder 9 ShapeExists ty a
    (CNot _,[]) -> residualShape debit context formula
    (CAnd _ _,[]) -> residualShape debit context formula
    (COr _ _,[]) -> residualShape debit context formula
    (CImp _ _,[]) -> residualShape debit context formula
    (CEq TyProp _ _,[]) -> residualShape debit context formula
    (CForall _ _,[]) -> residualShape debit context formula
    (CExists _ _,[]) -> residualShape debit context formula
    (_,[]) -> do
        (shape,size) <- State.runStateT leaf 0
        digest <- fingerprintShape debit shape
        pure (ResidualShape digest shape size)
    _ -> error "a residual descriptor disagrees with its connective layout"
  where
    unary tag constructor (ResidualShape digest shape size) = do
        debit
        pure (ResidualShape (hashWithSalt tag digest) (constructor shape) (size+1))
    binary tag constructor (ResidualShape ha a sa) (ResidualShape hb b sb) = do
        debit
        pure (ResidualShape (hashWithSalt (hashWithSalt tag ha) hb) (constructor a b) (sa+sb+1))
    binder tag constructor ty (ResidualShape digest shape size) = do
        (hashed,work) <- State.runStateT (typeHash tag ty) 0
        debit
        pure (ResidualShape (hashWithSalt hashed digest) (constructor ty shape) (size+work+1))
    tick = State.lift debit >> State.modify' (+1)
    typeHash salt ty = tick >> case ty of
        TySet -> pure (hashWithSalt salt (0 :: Int))
        TyProp -> pure (hashWithSalt salt (1 :: Int))
        TyArrow a b -> typeHash (hashWithSalt salt (2 :: Int)) a >>= (`typeHash` b)
    leaf = tick >> case formula of
        CTruth -> pure ShapeTruth
        CFalsum -> pure ShapeFalsum
        CEq ty _ _ -> typeHash 0 ty >> pure (ShapeEquality ty)
        _ -> application 0 formula
    application arity = \case
        CApp function _ -> tick >> application (arity+1) function
        CGlobal global -> pure (ShapeApplication (ShapeGlobal global) arity)
        CIntrinsic intrinsic -> pure (ShapeApplication (ShapeIntrinsic (fromIntegral (coreIntrinsicTagCode intrinsic))) arity)
        CBound index -> do
            ty <- boundType index context
            _ <- typeHash 0 ty
            pure (ShapeApplication (ShapeBound ty) arity)
        _ -> pure (ShapeApplication ShapeOpaque arity)
    boundType index types = tick >> case (index, types) of
        (0, ty:_) -> pure ty
        (_, _:rest) -> boundType (index - 1) rest
        (_, []) -> error "a checked residual shape escaped its binder context"

-- Hash once when preparing a description. Catalogue comparisons first select
-- this fixed-size bucket, then check the complete shape on collisions.
fingerprintShape :: Monad m => m () -> Shape -> m Int
fingerprintShape debit = shapeHash 0
  where
    tag salt constructor = hashWithSalt salt (constructor :: Int)
    shapeHash salt shape = debit >> case shape of
        ShapeTruth -> pure (tag salt 0)
        ShapeFalsum -> pure (tag salt 1)
        ShapeNot body -> shapeHash (tag salt 2) body
        ShapeAnd a b -> binary (tag salt 3) a b
        ShapeOr a b -> binary (tag salt 4) a b
        ShapeImp a b -> binary (tag salt 5) a b
        ShapeIff a b -> binary (tag salt 6) a b
        ShapeEquality ty -> typeHash (tag salt 7) ty
        ShapeForall ty body -> typeHash (tag salt 8) ty >>= (`shapeHash` body)
        ShapeExists ty body -> typeHash (tag salt 9) ty >>= (`shapeHash` body)
        ShapeApplication head' arity -> do
            let seed = hashWithSalt (tag salt 10) arity
            case head' of
                ShapeGlobal global -> pure (hashWithSalt (tag seed 0) global)
                ShapeIntrinsic intrinsic -> pure (hashWithSalt (tag seed 1) intrinsic)
                ShapeBound ty -> typeHash (tag seed 2) ty
                ShapeOpaque -> pure (tag seed 3)
    binary salt a b = shapeHash salt a >>= (`shapeHash` b)
    typeHash salt ty = debit >> case ty of
        TySet -> pure (tag salt 0)
        TyProp -> pure (tag salt 1)
        TyArrow a b -> typeHash (tag salt 2) a >>= (`typeHash` b)

data Formulas = Formulas
    { formulaContext :: ![CoreType]
    , formulaBucket :: !(Int -> Int)
    , formulaPostings :: !(Map Int [FormulaId])
    , formulaValues :: !(Seq Formula)
    , templatePostings :: !(Map Int [FormulaTemplateId])
    , templateValues :: !(Seq FormulaTemplate)
    , templateInstances :: !(Map (FormulaTemplateId, [(Natural,OpaqueLeaf)]) FormulaId)
    }

data FormulaFailure = FormulaScopeMismatch | FormulaNotProposition | FormulaInvalidTemplate | FormulaWorkExhausted !Natural
    deriving (Show, Eq)

emptyFormulas :: [CoreType] -> Formulas
emptyFormulas = emptyFormulasWithHash id

-- Keep the bucket function fixed for the owner's lifetime. A constant function
-- exercises collisions without changing exact identity or the checking path.
emptyFormulasWithHash :: (Int -> Int) -> [CoreType] -> Formulas
emptyFormulasWithHash bucket context = Formulas context bucket Map.empty Seq.empty Map.empty Seq.empty Map.empty

type FormulaWork = Except.ExceptT FormulaFailure (State.State Word)

charge :: Natural -> FormulaWork ()
charge amount = do
    available <- State.get
    if amount <= fromIntegral available then State.put (available - fromIntegral amount)
    else Except.throwE (FormulaWorkExhausted amount)

core :: (Word -> (Either (CountedCoreFailure Void) value, Word)) -> FormulaWork value
core operation = do
    available <- State.get
    let (result, remaining) = operation available
    State.put remaining
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> Except.throwE (FormulaWorkExhausted 1)

-- The lexical owner establishes nominal descent, just as for checked source
-- alignment. Equal type lists alone are never permission to share this table.
extendFormulas :: Word -> [CoreType] -> Formulas -> (Either FormulaFailure Formulas, Word)
extendFormulas allowance context table =
    State.runState (Except.runExceptT do
        charge (fromIntegral (length context + length original))
        let difference = length context - length original
        unless (difference >= 0) (Except.throwE FormulaScopeMismatch)
        same <- core (\work -> countedCoreTypeListIdentity work original (drop difference context))
        unless same (Except.throwE FormulaScopeMismatch)
        pure table {formulaContext = context}) allowance
  where original = formulaContext table

lookupFormula
    :: Word -> FormulaId -> Formulas
    -> (Either FormulaFailure (Maybe (ScopedCheckedCore ObjectId)), Word)
lookupFormula allowance (FormulaId identifier) table =
    State.runState (Except.runExceptT do
        charge (indexWork (Seq.length values) 1)
        case Seq.lookup identifier values of
            Nothing -> pure Nothing
            Just (Formula formula _ _) -> core (\work -> countedAlignScopedCore work context formula)) allowance
  where
    context = formulaContext table
    values = formulaValues table

-- Exact lookup needs no relevance shape. Prepare it only after an exact miss,
-- retaining it in this owner's immutable extension for subsequent lookups.
prepareFormulaShape :: Word -> FormulaId -> Formulas -> (Either FormulaFailure (Maybe ResidualShape, Formulas), Word)
prepareFormulaShape allowance identifier table =
    State.runState (Except.runExceptT (State.runStateT (go identifier) table)) allowance
  where
    go (FormulaId ordinal) = do
        values <- State.gets formulaValues
        State.lift (charge (indexWork (Seq.length values) 1))
        case Seq.lookup ordinal values of
            Nothing -> pure Nothing
            Just (Formula _ _ (Just shape)) -> pure (Just shape)
            Just (Formula formula key Nothing) -> do
                children <- case key of
                    ExactKey{} -> pure []
                    CompoundKey _ left right -> traverse (fmap required . go) [left,right]
                shape <- residualShapeFromChildren (State.lift (charge 1))
                    (scopedCoreContext formula) (scopedCoreTerm formula) children
                State.lift (charge (indexWork (Seq.length values) 1))
                State.modify' (\owner -> owner {formulaValues = Seq.update ordinal
                    (Formula formula key (Just shape)) (formulaValues owner)})
                pure (Just shape)
    required = fromMaybe (error "a compound formula lost its child")

internFormula
    :: Word -> ScopedCheckedCore ObjectId -> Formulas
    -> (Either FormulaFailure (FormulaId, Formulas), Word)
internFormula allowance formula table = runIndex allowance table do
    context <- State.gets formulaContext
    same <- liftCore (\work -> countedCoreTypeListIdentity work context (scopedCoreContext formula))
    unless same (State.lift (Except.throwE FormulaScopeMismatch))
    unless (scopedCoreType formula == TyProp) (State.lift (Except.throwE FormulaNotProposition))
    intern formula

type FormulaIndex = State.StateT Formulas FormulaWork

runIndex :: Word -> Formulas -> FormulaIndex value -> (Either FormulaFailure (value,Formulas),Word)
runIndex allowance table action = State.runState (Except.runExceptT (State.runStateT action table)) allowance

liftCore :: (Word -> (Either (CountedCoreFailure Void) value,Word)) -> FormulaIndex value
liftCore = State.lift . core

childrenOf :: ScopedCheckedCore ObjectId -> Maybe (Connective,ScopedCheckedCore ObjectId,ScopedCheckedCore ObjectId)
childrenOf formula = case scopedCoreTerm formula of
    CAnd{} -> pair Conjunction (splitScopedConjunction formula)
    COr{} -> pair Disjunction (splitScopedDisjunction formula)
    CImp{} -> pair Implication (openScopedImplication formula)
    CEq TyProp _ _ -> case splitScopedEquality formula of
        Just (_,left,right) -> Just (Biconditional,left,right)
        Nothing -> Nothing
    _ -> Nothing
  where pair operation = fmap (\(left,right) -> (operation,left,right))

intern :: ScopedCheckedCore ObjectId -> FormulaIndex FormulaId
intern formula = do
    State.lift (charge 1)
    case childrenOf formula of
        Just (operation,left,right) -> do
            a <- intern left
            b <- intern right
            internKey formula (CompoundKey operation a b)
        Nothing -> do
            key <- liftCore (\work -> countedScopedLevelKey work formula)
            internKey formula (ExactKey key)

internKey :: ScopedCheckedCore ObjectId -> FormulaKey -> FormulaIndex FormulaId
internKey formula key = do
    table <- State.get
    digest <- formulaBucket table <$> State.lift (case key of
        ExactKey term -> fingerprint term
        CompoundKey operation (FormulaId a) (FormulaId b) -> charge 1 >>
            pure (hashWithSalt (hashWithSalt (fromEnum operation) a) b))
    let postings = formulaPostings table
        values = formulaValues table
    State.lift (charge (indexWork (Map.size postings) 1))
    existing <- findExact values (Map.findWithDefault [] digest postings)
    case existing of
        Just identifier -> pure identifier
        Nothing -> do
            State.lift (charge (1 + indexWork (Map.size postings) 1))
            let identifier = FormulaId (Seq.length values)
            State.put table {formulaPostings = Map.insert digest (identifier : Map.findWithDefault [] digest postings) postings,
                formulaValues = values Seq.|> Formula formula key Nothing}
            pure identifier
  where
    findExact _ [] = pure Nothing
    findExact values (identifier@(FormulaId ordinal):rest) = do
        State.lift (charge (indexWork (Seq.length values) 1))
        let Formula _ candidate _ = Seq.index values ordinal
        same <- case (key,candidate) of
            (ExactKey a,ExactKey b) -> liftCore (\work -> countedCanonicalIdentity work a b)
            (CompoundKey op a b,CompoundKey other x y) -> State.lift (charge 3) >> pure (op == other && a == x && b == y)
            _ -> pure False
        if same then pure (Just identifier) else findExact values rest

-- A template is prepared once for an admitted clause node. Its leaves retain
-- checked lexical layouts; compound keys use child descriptors. These handles
-- and their concrete assignments belong only to this nominal query owner.
prepareFormulaTemplate
    :: Word -> Natural -> ScopedCheckedCore ObjectId -> Formulas
    -> (Either FormulaFailure (FormulaTemplateId,Formulas),Word)
prepareFormulaTemplate allowance arity formula table = runIndex allowance table (prepare formula)
  where
    prepare term = do
        State.lift (charge 1)
        (key,parameters,digest) <- case childrenOf term of
            Just (operation,left,right) -> do
                a@(FormulaTemplateId ai) <- prepare left
                b@(FormulaTemplateId bi) <- prepare right
                FormulaTemplate _ leftSlots <- template a
                FormulaTemplate _ rightSlots <- template b
                State.lift (charge (fromIntegral (Set.size leftSlots + Set.size rightSlots)))
                pure (TemplateCompound operation a b,leftSlots <> rightSlots,
                    hashWithSalt (hashWithSalt (fromEnum operation) ai) bi)
            Nothing -> do
                level <- liftCore (\work -> countedScopedLevelKey work term)
                slots <- canonicalFreeIndicesWith (State.lift (charge 1)) (scopedCoreTerm term)
                digest <- State.lift (fingerprint level)
                pure (TemplateLeaf arity term level,Set.filter (< arity) slots,hashWithSalt digest arity)
        owner <- State.get
        let digest' = formulaBucket owner digest
            candidates = Map.findWithDefault [] digest' (templatePostings owner)
        State.lift (charge (indexWork (Map.size (templatePostings owner)) 1))
        known <- findTemplate key candidates
        case known of
            Just identifier -> pure identifier
            Nothing -> do
                State.lift (charge (indexWork (Map.size (templatePostings owner)) 1))
                let identifier = FormulaTemplateId (Seq.length (templateValues owner))
                State.put owner {templatePostings = Map.insert digest' (identifier:candidates) (templatePostings owner),
                    templateValues = templateValues owner Seq.|> FormulaTemplate key parameters}
                pure identifier
    findTemplate _ [] = pure Nothing
    findTemplate key (identifier:rest) = do
        FormulaTemplate candidate _ <- template identifier
        same <- case (key,candidate) of
            (TemplateCompound op a b,TemplateCompound other x y) -> State.lift (charge 3) >> pure (op == other && a == x && b == y)
            (TemplateLeaf count value level,TemplateLeaf other otherValue otherLevel) | count == other -> do
                contexts <- liftCore (\work -> countedCoreTypeListIdentity work (scopedCoreContext value) (scopedCoreContext otherValue))
                if contexts then liftCore (\work -> countedCanonicalIdentity work level otherLevel) else pure False
            _ -> pure False
        if same then pure (Just identifier) else findTemplate key rest

template :: FormulaTemplateId -> FormulaIndex FormulaTemplate
template (FormulaTemplateId identifier) = do
    values <- State.gets templateValues
    State.lift (charge (indexWork (Seq.length values) 1))
    maybe (State.lift (Except.throwE FormulaInvalidTemplate)) pure (Seq.lookup identifier values)

instantiateFormulaTemplate
    :: Word -> FormulaTemplateId -> Map Natural (OpaqueLeaf,ScopedCheckedCore ObjectId) -> Formulas
    -> (Either FormulaFailure (FormulaId,Formulas),Word)
instantiateFormulaTemplate allowance requested bindings table = runIndex allowance table (instantiate requested)
  where
    instantiate identifier = do
        FormulaTemplate key parameters <- template identifier
        selected <- for (Set.toAscList parameters) \slot -> do
            State.lift (charge (indexWork (Map.size bindings) 1))
            maybe (State.lift (Except.throwE FormulaInvalidTemplate)) (\value -> pure (slot,fst value)) (Map.lookup slot bindings)
        known <- State.gets templateInstances
        let instanceKey = (identifier,selected)
        State.lift (charge (indexWork (Map.size known) (1 + fromIntegral (length selected))))
        case Map.lookup instanceKey known of
            Just found -> pure found
            Nothing -> do
                found <- case key of
                    TemplateLeaf arity source _ -> do
                        context <- State.gets formulaContext
                        aligned <- liftCore (\work -> countedAlignScopedCoreAt work arity
                            (replicate (fromIntegral arity) TySet <> context) source)
                            >>= maybe (State.lift (Except.throwE FormulaScopeMismatch)) pure
                        let arguments = Map.fromList [(arity-slot-1,value) | (slot,(_,value)) <- Map.toAscList bindings, slot < arity]
                        State.lift (charge (fromIntegral (Map.size arguments)))
                        instance' <- State.lift (checkedCore (\work -> countedInstantiateScopedPrefix work arity arguments aligned))
                        case instance' of
                            ScopedInstantiationOpen{} -> State.lift (Except.throwE FormulaInvalidTemplate)
                            ScopedInstantiationClosed formula -> intern formula
                    TemplateCompound operation left right -> do
                        a <- instantiate left
                        b <- instantiate right
                        leftFormula <- lookupAligned a
                        rightFormula <- lookupAligned b
                        State.lift (charge (2 + fromIntegral (length (scopedCoreContext leftFormula))))
                        formula <- maybe (State.lift (Except.throwE FormulaScopeMismatch)) pure
                            ((case operation of Conjunction -> conjoinExactScopedCore; Disjunction -> disjoinScopedCore;
                                                Implication -> implyScopedCore; Biconditional -> equalScopedCore) leftFormula rightFormula)
                        internKey formula (CompoundKey operation a b)
                State.lift (charge (indexWork (Map.size known) (1 + fromIntegral (length selected))))
                State.modify' (\owner -> owner {templateInstances = Map.insert instanceKey found (templateInstances owner)})
                pure found
    lookupAligned identifier = do
        owner <- State.get
        State.lift (do
            available <- State.get
            let (result,remaining) = lookupFormula available identifier owner
            State.put remaining
            either Except.throwE pure result)
            >>= maybe (State.lift (Except.throwE FormulaScopeMismatch)) pure

checkedCore :: (Word -> (Either (CountedCoreFailure failure) value,Word)) -> FormulaWork value
checkedCore operation = do
    available <- State.get
    let (result,remaining) = operation available
    State.put remaining
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> Except.throwE (FormulaWorkExhausted 1)
        Left (CountedCoreOperationFailed _) -> Except.throwE FormulaInvalidTemplate

-- This transient hash is only a bucket selector. Every collision is resolved
-- against the complete level key above. Charge each visited term/type node;
-- the scheduler subsequently compares only FormulaId.
fingerprint :: LevelFormula -> FormulaWork Int
fingerprint = term 0
  where
    tag salt constructor = hashWithSalt salt (constructor :: Int)
    term salt expression = charge 1 >> case expression of
        CBound index -> pure (hashWithSalt (tag salt 0) index)
        CGlobal global -> pure (hashWithSalt (tag salt 1) global)
        CIntrinsic intrinsic -> pure (hashWithSalt (tag salt 2) (coreIntrinsicTagCode intrinsic))
        CLogicalSelect coreType -> typeHash (tag salt 3) coreType
        COpaqueInteger integer -> pure (hashWithSalt (tag salt 4) integer)
        CApp function argument -> binary (tag salt 5) function argument
        CLam coreType body -> typeHash (tag salt 6) coreType >>= (`term` body)
        CFalsum -> pure (tag salt 7)
        CTruth -> pure (tag salt 8)
        CNot body -> term (tag salt 9) body
        CAnd left right -> binary (tag salt 10) left right
        COr left right -> binary (tag salt 11) left right
        CImp left right -> binary (tag salt 12) left right
        CEq coreType left right -> typeHash (tag salt 13) coreType >>= \hashed -> binary hashed left right
        CForall coreType body -> typeHash (tag salt 14) coreType >>= (`term` body)
        CExists coreType body -> typeHash (tag salt 15) coreType >>= (`term` body)
    binary salt left right = term salt left >>= (`term` right)
    typeHash salt coreType = charge 1 >> case coreType of
        TySet -> pure (tag salt 0)
        TyProp -> pure (tag salt 1)
        TyArrow argument result -> typeHash (tag salt 2) argument >>= (`typeHash` result)
