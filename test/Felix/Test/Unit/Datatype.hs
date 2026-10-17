{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Datatype (unitTests) where

import Base hiding (Empty, empty)
import Felix.Cache.Codec (encodeCache, putCanonicalTermCache)
import Felix.Checking.Core
import Felix.Checking.Datatype.Construction qualified as Datatype
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Kernel.Derivation
import Felix.Checking.Kernel.Proof qualified as Proof

import Data.Vector qualified as Vector
import Data.ByteString qualified as ByteString
import Test.Tasty
import Test.Tasty.HUnit

unitTests :: TestTree
unitTests = testGroup "Datatype construction"
    [ testCase "replays set encoding support" replaysEncodingSupport
    , testCase "keeps binary constructor encodings and proofs compact" compactConstructorProofs
    ]

replaysEncodingSupport :: Assertion
replaysEncodingSupport = do
    foundation <- right Foundation.checkedFoundation
    let kType = TyArrow TySet (TyArrow TySet TySet)
        object = Identity.transparentObject (Identity.theoryId foundation) kType Datatype.kuratowskiBody
        k = Identity.assertedObjectId object
    closure <- right (Identity.validateObjectClosure (Identity.theoryId foundation) [object])
    let typing = Identity.globalTypingFromClosure closure
        context = Proof.rootProofContext foundation typing
        app a b = CApp (CApp (CGlobal k) a) b
        empty = CIntrinsic Empty
        singleton a = CApp (CApp (CIntrinsic PairSet) a) a
        member a b = CApp (CApp (CIntrinsic Member) a) b
        forallSets n body = foldr (const (CForall TySet)) body [1 .. n :: Int]
    definition <- right (checkCanonicalCore typing (canonicalDefinitionEquationTarget k kType Datatype.kuratowskiBody))
    let run label imports expected action = do
            proof <- either (fail . ((label <> ": ") <>) . show) pure action
            target <- right (checkCanonicalCore typing expected)
            judgements <- traverse (right . derivationImportJudgement) imports
            result <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                (Vector.fromList judgements) target (Proof.builtProofDerivation proof))
            assertEqual label target (replayedKernelTarget result)
    run "Kuratowski injection, including coincident coordinates" [definition]
        (forallSets 4 (CImp (CEq TySet (app (CBound 3) (CBound 2)) (app (CBound 1) (CBound 0)))
            (CAnd (CEq TySet (CBound 3) (CBound 1)) (CEq TySet (CBound 2) (CBound 0)))))
        (Datatype.proveKuratowskiInjective context k (importIx 0, definition))
    run "bits are distinct" [] (CNot (CEq TySet empty (singleton empty)))
        (Datatype.proveBitInequality context)
    run "every chosen universe contains the empty set" []
        (CForall TySet (member empty (CApp (CIntrinsic UnivOf) (CBound 0))))
        (Datatype.proveUniverseEmpty context)
    bitTarget <- right (checkCanonicalCore typing (CNot (CEq TySet empty (singleton empty))))
    emptyTarget <- right (checkCanonicalCore typing
        (CForall TySet (member empty (CApp (CIntrinsic UnivOf) (CBound 0)))))
    let universe = CApp (CIntrinsic UnivOf) (CBound 2)
        pair = CApp (CApp (CIntrinsic PairSet) (CBound 1)) (CBound 0)
        closed value = forallSets 3 (CImp (member (CBound 1) universe)
            (CImp (member (CBound 0) universe) (member value universe)))
    run "universes contain unordered pairs" [emptyTarget,bitTarget] (closed pair)
        (Datatype.proveUniversePair context (importIx 0, emptyTarget) (importIx 1, bitTarget))
    pairTarget <- right (checkCanonicalCore typing (closed pair))
    run "universes contain Kuratowski codes" [definition,pairTarget] (closed (app (CBound 1) (CBound 0)))
        (Datatype.proveUniverseKuratowski context (importIx 0, definition) (importIx 1, pairTarget))

right :: Show e => Either e a -> IO a
right = either (fail . show) pure

compactConstructorProofs :: Assertion
compactConstructorProofs = do
    small <- measure 3
    large <- measure 32
    let (smallBytes, smallNodes, smallDepth) = small
        (largeBytes, largeNodes, largeDepth) = large
    assertBool ("binary tags have logarithmic term growth: " <> show (small, large))
        (largeBytes <= 3 * smallBytes)
    assertBool ("each distinctness proof stays compact: " <> show (small, large))
        (largeNodes <= 4 * smallNodes && largeDepth <= 4 * smallDepth)
  where
    measure count = do
        foundation <- right Foundation.checkedFoundation
        let theory = Identity.theoryId foundation
            coreType = TyArrow TySet (TyArrow TySet TySet)
            kObject = Identity.transparentObject theory coreType Datatype.kuratowskiBody
            k = Identity.assertedObjectId kObject
            constructors = [(i, Identity.transparentObject theory coreType (Datatype.constructorBody k count i 2))
                | i <- [0 .. count - 1]]
        closure <- right (Identity.validateObjectClosure theory (kObject : (snd <$> constructors)))
        let typing = Identity.globalTypingFromClosure closure
            context = Proof.rootProofContext foundation typing
            checked = right . checkCanonicalCore typing
            clause object = Datatype.Clause (Identity.assertedObjectId object) [0,1] [Datatype.Recursive, Datatype.Recursive]
            definition object = case Identity.assertedObjectContent object of
                Identity.TransparentObjectContent _ t body ->
                    checked (canonicalDefinitionEquationTarget (Identity.assertedObjectId object) t body)
                _ -> fail "constructor is not transparent"
            bytes object = case Identity.assertedObjectContent object of
                Identity.TransparentObjectContent _ _ body ->
                    ByteString.length (encodeCache (putCanonicalTermCache Identity.putObjectIdCache body))
                _ -> 0
        injection <- checked (Datatype.kuratowskiInjectiveTarget k)
        bits <- checked Datatype.bitInequalityTarget
        summaries <- for [(left, rightConstructor) | left@(i, _) <- constructors,
                rightConstructor@(j, _) <- constructors, i < j] \((i,left), (j,rightConstructor)) -> do
            leftDefinition <- definition left
            rightDefinition <- definition rightConstructor
            target <- checked (Datatype.distinctTarget (clause left) (clause rightConstructor))
            let imports = [leftDefinition,rightDefinition,injection,bits]
            proof <- right (Datatype.proveDistinct context k count
                (i,clause left,(importIx 0,leftDefinition))
                (j,clause rightConstructor,(importIx 1,rightDefinition))
                (importIx 2,injection) (importIx 3,bits))
            judgements <- traverse (right . derivationImportJudgement) imports
            replayed <- right (replayKernelDerivation foundation defaultKernelReplayLimits typing
                (Vector.fromList judgements) target (Proof.builtProofDerivation proof))
            pure (replayedKernelNodeCount replayed, replayedKernelMaximumDepth replayed)
        pure (maximum (bytes . snd <$> constructors), maximum (fst <$> summaries), maximum (snd <$> summaries))
