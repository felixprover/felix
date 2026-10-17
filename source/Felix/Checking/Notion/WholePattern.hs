{-# LANGUAGE NoImplicitPrelude #-}

-- | Conservative inverse descriptions for complete whole-head parameters.
-- A set operand is a boundary: matching never decomposes a Core application
-- inside it to manufacture a provider view or guess its arguments.
module Felix.Checking.Notion.WholePattern
    ( WholePattern, compileWholePattern, wholePatternParameters, matchWholePattern, matchPartialWholePattern, mayEqualOperands, prepareOperandComparison
    ) where

import Base
import Control.Monad (unless)
import Control.Monad.State.Strict qualified as State
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Semantic (ViewVariableIx(..))
import Felix.Checking.Notion.TermIndex (indexWork)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Numeric.Natural (Natural)

data WholePattern
    = AnyFormula
    | RigidFormula !(CanonicalTerm ObjectId)
    | Negated !WholePattern
    | Conjoined !WholePattern !WholePattern
    | Disjoined !WholePattern !WholePattern
    | Implied !WholePattern !WholePattern
    | Equivalent !WholePattern !WholePattern
    | Universal !CoreType !WholePattern
    | Existential !CoreType !WholePattern
    | Application !WholePattern !OperandPattern
    | SetEquality !OperandPattern !OperandPattern

data OperandPattern
    = AnyOperand | BoundOperand !Natural | ParameterOperand !ViewVariableIx
    | RigidOperand !OperandHead !Natural

data OperandHead = GlobalOperand !ObjectId | IntrinsicOperand !CoreIntrinsicTag
    | SetChoiceOperand | IntegerOperand !Integer
    deriving (Eq)

-- A rigid outer constructor may disprove exact equality without exposing any
-- argument. This is only a filter: no interior supplies a parameter binding.
operandHead :: Monad m => (Natural -> m ()) -> CanonicalTerm ObjectId -> m (Maybe (OperandHead,Natural))
operandHead charge = go 0
  where
    go arity term = charge 1 >> case term of
        CApp function _ -> go (arity+1) function
        CGlobal identity -> pure (Just (GlobalOperand identity,arity))
        CIntrinsic tag -> pure (Just (IntrinsicOperand tag,arity))
        CLogicalSelect TySet -> pure (Just (SetChoiceOperand,arity))
        COpaqueInteger value -> pure (Just (IntegerOperand value,arity))
        _ -> pure Nothing

-- Partial denotations use an outer set slot for each unknown. Compare their
-- rigid syntax, including fixed arguments and binders, without returning any
-- bindings. Looking inside Core for this Boolean filter never supplies a view.
mayEqualOperands
    :: Monad m => (Natural -> m ()) -> Natural
    -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId -> m Bool
mayEqualOperands charge firstHole = compareOperands charge firstHole (\_ _ _ -> pure True)

-- Specialize the same comparison to a single varying outer slot. Fixed
-- mismatches and wildcard branches are decided once. Only occurrences of that
-- slot need the candidate, weakened under the binders at each occurrence.
-- The varying slot is a fresh hole distinct from all other unknown inputs.
prepareOperandComparison
    :: Monad m => (Natural -> m ()) -> Natural -> Natural
    -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId
    -> m (m (CanonicalTerm ObjectId) -> m Bool)
prepareOperandComparison charge firstHole varying template target = do
    (possible,checks) <- State.runStateT
        (compareOperands (lift . charge) firstHole record template target) []
    charge (fromIntegral (length checks))
    let ordered = reverse checks
    pure (\candidate -> if not possible then pure False else case ordered of
        [] -> pure True
        _ -> do
            value <- candidate
            checkOccurrences value ordered)
  where
    checkOccurrences _ [] = pure True
    checkOccurrences value ((depth,expected):rest) = do
        shifted <- if depth == 0 then pure value else shiftCanonicalWith (charge 1) depth 0 value
        matches <- mayEqualOperands charge (firstHole+depth) shifted expected
        if matches then checkOccurrences value rest else pure False
    record depth left right = do
        case (left,right) of
            (_,CBound index) | index >= firstHole+depth -> pure ()
            (CBound index,_) | index == varying+depth -> do
                lift (charge 1)
                State.modify' ((depth,right):)
            _ -> pure ()
        pure True

compareOperands
    :: Monad m => (Natural -> m ()) -> Natural
    -> (Natural -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId -> m Bool)
    -> CanonicalTerm ObjectId -> CanonicalTerm ObjectId -> m Bool
compareOperands charge firstHole atHole = term 0
  where
    hole depth = \case CBound index -> index >= firstHole+depth; _ -> False
    both first second = first >>= \same -> if same then second else pure False
    sameType left right = charge 1 >> case (left,right) of
        (TySet,TySet) -> pure True
        (TyProp,TyProp) -> pure True
        (TyArrow a b,TyArrow c d) -> both (sameType a c) (sameType b d)
        _ -> pure False
    term depth left right = do
        charge 1
        if hole depth left || hole depth right then atHole depth left right else case (left,right) of
            (CApp a b,CApp c d) -> binary depth a b c d
            (CLam ty a,CLam other b) -> binder depth ty a other b
            (CNot a,CNot b) -> term depth a b
            (CAnd a b,CAnd c d) -> binary depth a b c d
            (COr a b,COr c d) -> binary depth a b c d
            (CImp a b,CImp c d) -> binary depth a b c d
            (CEq ty a b,CEq other c d) -> both (sameType ty other) (binary depth a b c d)
            (CForall ty a,CForall other b) -> binder depth ty a other b
            (CExists ty a,CExists other b) -> binder depth ty a other b
            (CLogicalSelect ty,CLogicalSelect other) -> sameType ty other
            (CBound a,CBound b) -> pure (a == b)
            (CGlobal a,CGlobal b) -> pure (a == b)
            (CIntrinsic a,CIntrinsic b) -> pure (a == b)
            (COpaqueInteger a,COpaqueInteger b) -> pure (a == b)
            (CTruth,CTruth) -> pure True
            (CFalsum,CFalsum) -> pure True
            _ -> pure False
    binary depth a b c d = both (term depth a c) (term depth b d)
    binder depth ty a other b = both (sameType ty other) (term (depth+1) a b)

-- Parameters exposed as complete operands can participate in inverse matching.
-- This does not count parameters nested in opaque operands or retained only by
-- source annotations; rule admission uses residual occurrence instead.
wholePatternParameters :: Monad m => (Natural -> m ()) -> WholePattern -> m (Set ViewVariableIx)
wholePatternParameters charge = formula Set.empty
  where
    formula known pattern' = charge 1 >> case pattern' of
        Negated body -> formula known body
        Conjoined a b -> binary known a b
        Disjoined a b -> binary known a b
        Implied a b -> binary known a b
        Equivalent a b -> binary known a b
        Universal _ body -> formula known body
        Existential _ body -> formula known body
        Application function argument -> formula known function >>= \values -> operand values argument
        SetEquality a b -> operand known a >>= \values -> operand values b
        _ -> pure known
    binary known a b = formula known a >>= \values -> formula values b
    operand known = \case
        ParameterOperand slot -> charge (indexWork (Set.size known) 1) >> pure (Set.insert slot known)
        _ -> pure known

compileWholePattern :: Monad m => (Natural -> m ()) -> Natural -> CanonicalTerm ObjectId -> m WholePattern
compileWholePattern charge arity = formula 0
  where
    formula depth term = charge 1 >> case term of
        CTruth -> pure (RigidFormula CTruth)
        CFalsum -> pure (RigidFormula CFalsum)
        CGlobal{} -> pure (RigidFormula term)
        CIntrinsic{} -> pure (RigidFormula term)
        CBound index | index < depth -> pure (RigidFormula term)
        CNot body -> Negated <$> formula depth body
        CAnd left right -> Conjoined <$> formula depth left <*> formula depth right
        COr left right -> Disjoined <$> formula depth left <*> formula depth right
        CImp left right -> Implied <$> formula depth left <*> formula depth right
        CEq TyProp left right -> Equivalent <$> formula depth left <*> formula depth right
        CEq TySet left right -> SetEquality <$> operand depth left <*> operand depth right
        CForall ty body -> Universal ty <$> formula (depth+1) body
        CExists ty body -> Existential ty <$> formula (depth+1) body
        CApp function argument -> formula depth function >>= \case
            -- An unknown function does not fix the operand type. In particular,
            -- a lambda may consume a proposition rather than a set.
            AnyFormula -> pure AnyFormula
            known -> Application known <$> operand depth argument
        _ -> pure AnyFormula
    operand depth term = charge 1 >> case term of
        CBound index | index < depth -> pure (BoundOperand index)
                     | index-depth < arity -> pure (ParameterOperand (ViewVariableIx (index-depth)))
        _ -> maybe AnyOperand (uncurry RigidOperand) <$> operandHead charge term

matchWholePattern
    :: Monad m => (Natural -> m ()) -> WholePattern -> CanonicalTerm ObjectId
    -> m (Maybe (Map ViewVariableIx (CanonicalTerm ObjectId)))
matchWholePattern charge = matchPattern charge Nothing

-- Unknown set inputs can reject neither a rigid operand nor another input.
-- Only complete operands are returned as constraints on clause parameters.
matchPartialWholePattern
    :: Monad m => (Natural -> m ()) -> Natural -> WholePattern -> CanonicalTerm ObjectId
    -> m (Maybe (Map ViewVariableIx (CanonicalTerm ObjectId)))
matchPartialWholePattern charge firstHole = matchPattern charge (Just firstHole)

matchPattern
    :: Monad m => (Natural -> m ()) -> Maybe Natural -> WholePattern -> CanonicalTerm ObjectId
    -> m (Maybe (Map ViewVariableIx (CanonicalTerm ObjectId)))
matchPattern charge firstHole pattern' target = fmap (either (const Nothing) Just) $
    Except.runExceptT (formula 0 Map.empty pattern' target)
  where
    tick = lift (charge 1)
    mismatch = Except.throwE ()
    same left right = do
        compared <- compareCanonicalWith tick left right
        unless (compared == EQ) mismatch
    sameType left right = tick >> case (left,right) of
        (TySet,TySet) -> pure ()
        (TyProp,TyProp) -> pure ()
        (TyArrow a b,TyArrow c d) -> sameType a c >> sameType b d
        _ -> mismatch
    formula depth values description term = tick >> case (description,term) of
        (AnyFormula,_) -> pure values
        (RigidFormula expected,_) -> same expected term >> pure values
        (Negated body,CNot actual) -> formula depth values body actual
        (Conjoined a b,CAnd left right) -> binary depth values a b left right
        (Disjoined a b,COr left right) -> binary depth values a b left right
        (Implied a b,CImp left right) -> binary depth values a b left right
        (Equivalent a b,CEq TyProp left right) -> binary depth values a b left right
        (Universal ty body,CForall actualTy actual) -> sameType ty actualTy >> formula (depth+1) values body actual
        (Existential ty body,CExists actualTy actual) -> sameType ty actualTy >> formula (depth+1) values body actual
        (Application function argument,CApp actualFunction actualArgument) -> do
            known <- formula depth values function actualFunction
            operand depth known argument actualArgument
        (SetEquality a b,CEq TySet left right) -> do
            known <- operand depth values a left
            operand depth known b right
        _ -> mismatch
    binary depth values a b left right = do
        known <- formula depth values a left
        formula depth known b right
    operand depth values description term = do
      tick
      incomplete <- case firstHole of
        Nothing -> pure False
        Just first -> lift (hasHole (first+depth) term)
      if incomplete then pure values else case description of
        AnyOperand -> pure values
        RigidOperand head' arity -> do
            actual <- lift (operandHead charge term)
            unless (actual == Just (head',arity)) mismatch
            pure values
        BoundOperand index -> same (CBound index) term >> pure values
        ParameterOperand slot -> do
            value <- instantiateCanonicalPrefixWith tick depth (\_ _ -> mismatch) 0 term
            lift (charge (2 * indexWork (Map.size values) 1))
            case Map.lookup slot values of
                Just previous -> same previous value >> pure values
                Nothing -> pure (Map.insert slot value values)
    hasHole first term = do
        charge 1
        case term of
            CBound index -> pure (index >= first)
            CApp a b -> both a b
            CNot a -> hasHole first a
            CAnd a b -> both a b
            COr a b -> both a b
            CImp a b -> both a b
            CEq _ a b -> both a b
            CLam _ a -> hasHole (first+1) a
            CForall _ a -> hasHole (first+1) a
            CExists _ a -> hasHole (first+1) a
            _ -> pure False
      where
        both a b = hasHole first a >>= \found -> if found then pure True else hasHole first b
