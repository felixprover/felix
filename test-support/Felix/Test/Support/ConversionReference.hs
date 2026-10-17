{-# LANGUAGE NoImplicitPrelude #-}

-- | Small substitution-based beta-eta normalizer, independent of production
-- binding operations and the closure comparator. Nothing means exhausted fuel,
-- never an equality decision. All traversals share one account.
module Felix.Test.Support.ConversionReference
    ( referenceConvertibleWithLimit
    ) where

import Base
import Felix.Checking.Core (CanonicalTerm(..), CoreType(..))
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Word (Word)
import Numeric.Natural (Natural)

type Reference = StateT Word Maybe

referenceConvertibleWithLimit
    :: Eq global
    => Word -> CanonicalTerm global -> CanonicalTerm global -> Maybe Bool
referenceConvertibleWithLimit limit left right = evalStateT action limit
  where
    action = do
        leftNormal <- normal left
        rightNormal <- normal right
        sameTerm leftNormal rightNormal

tick :: Reference ()
tick = do
    remaining <- get
    guard (remaining > 0)
    put (remaining - 1)

-- Each constructor visit (including type payloads) is charged here. The local
-- binder depth is shared by lambdas and logical quantifiers.
children
    :: (Natural -> CanonicalTerm global -> Reference (CanonicalTerm global))
    -> Natural -> CanonicalTerm global -> Reference (CanonicalTerm global)
children visit depth term = do
    tick
    let child = visit depth
        binder constructor coreType body = do
            visitType coreType
            constructor coreType <$> visit (depth + 1) body
    case term of
        CApp function argument -> CApp <$> child function <*> child argument
        CLam coreType body -> binder CLam coreType body
        CForall coreType body -> binder CForall coreType body
        CExists coreType body -> binder CExists coreType body
        CNot body -> CNot <$> child body
        CAnd left right -> CAnd <$> child left <*> child right
        COr left right -> COr <$> child left <*> child right
        CImp left right -> CImp <$> child left <*> child right
        CEq coreType left right -> do
            visitType coreType
            CEq coreType <$> child left <*> child right
        CLogicalSelect coreType -> visitType coreType >> pure term
        CBound{} -> pure term
        CGlobal{} -> pure term
        CIntrinsic{} -> pure term
        COpaqueInteger{} -> pure term
        CFalsum -> pure term
        CTruth -> pure term

visitType :: CoreType -> Reference ()
visitType coreType = do
    tick
    case coreType of
        TyArrow domain result -> visitType domain >> visitType result
        TySet -> pure ()
        TyProp -> pure ()

-- Substitution removes the selected binder; shifting a replacement protects
-- its own inner binders. These operations are deliberately test-local.
rebind
    :: (Natural -> Natural -> Reference (CanonicalTerm global))
    -> Natural -> CanonicalTerm global -> Reference (CanonicalTerm global)
rebind variable depth term = case term of
    CBound index -> tick >> variable depth index
    _ -> children (rebind variable) depth term

shift :: Natural -> CanonicalTerm global -> Reference (CanonicalTerm global)
shift amount = rebind (\depth index -> pure
    (CBound (if index < depth then index else index + amount))) 0

substitute
    :: CanonicalTerm global -> CanonicalTerm global
    -> Reference (CanonicalTerm global)
substitute argument = rebind replace 0
  where
    replace depth index
        | index == depth = shift depth argument
        | index > depth = pure (CBound (index - 1))
        | otherwise = pure (CBound index)

-- A used binder is a normal non-contraction, distinct from exhausted fuel.
removeBinder :: CanonicalTerm global -> Reference (Maybe (CanonicalTerm global))
removeBinder term = do
    used <- uses 0 term
    if used then pure Nothing else Just <$> rebind remove 0 term
  where
    remove depth index = pure (CBound (if index > depth then index - 1 else index))
    uses depth value = do
        tick
        case value of
            CBound index -> pure (index == depth)
            CLam coreType body -> visitType coreType >> uses (depth + 1) body
            CForall coreType body -> visitType coreType >> uses (depth + 1) body
            CExists coreType body -> visitType coreType >> uses (depth + 1) body
            CApp function argument -> both depth function argument
            CNot body -> uses depth body
            CAnd left right -> both depth left right
            COr left right -> both depth left right
            CImp left right -> both depth left right
            CEq coreType left right -> visitType coreType >> both depth left right
            CLogicalSelect coreType -> visitType coreType >> pure False
            CGlobal{} -> pure False
            CIntrinsic{} -> pure False
            COpaqueInteger{} -> pure False
            CFalsum -> pure False
            CTruth -> pure False
    both depth left right = (||) <$> uses depth left <*> uses depth right

normal :: CanonicalTerm global -> Reference (CanonicalTerm global)
normal term = do
    rebuilt <- children (\_ -> normal) 0 term
    case rebuilt of
        CApp (CLam _ body) argument -> substitute argument body >>= normal
        CLam _ (CApp function (CBound 0)) -> do
            contracted <- removeBinder function
            pure (fromMaybe rebuilt contracted)
        _ -> pure rebuilt

sameType :: CoreType -> CoreType -> Reference Bool
sameType left right = do
    tick
    case (left, right) of
        (TySet, TySet) -> pure True
        (TyProp, TyProp) -> pure True
        (TyArrow a b, TyArrow c d) -> (&&) <$> sameType a c <*> sameType b d
        _ -> pure False

sameTerm :: Eq global => CanonicalTerm global -> CanonicalTerm global -> Reference Bool
sameTerm left right = do
    tick
    let pair a b c d = (&&) <$> sameTerm a c <*> sameTerm b d
        binder a b c d = (&&) <$> sameType a c <*> sameTerm b d
    case (left, right) of
        (CBound a, CBound b) -> pure (a == b)
        (CGlobal a, CGlobal b) -> pure (a == b)
        (CIntrinsic a, CIntrinsic b) -> pure (a == b)
        (COpaqueInteger a, COpaqueInteger b) -> pure (a == b)
        (CLogicalSelect a, CLogicalSelect b) -> sameType a b
        (CTruth, CTruth) -> pure True
        (CFalsum, CFalsum) -> pure True
        (CApp a b, CApp c d) -> pair a b c d
        (CLam a b, CLam c d) -> binder a b c d
        (CForall a b, CForall c d) -> binder a b c d
        (CExists a b, CExists c d) -> binder a b c d
        (CNot a, CNot b) -> sameTerm a b
        (CAnd a b, CAnd c d) -> pair a b c d
        (COr a b, COr c d) -> pair a b c d
        (CImp a b, CImp c d) -> pair a b c d
        (CEq t a b, CEq u c d) -> (&&) <$> sameType t u <*> pair a b c d
        _ -> pure False
