{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DerivingStrategies #-}

-- | Scoped binary predicates and the first-order calculus for choosing
-- composition laws. Matching and overlap use the same rigid Core syntax;
-- neither consults formation evidence or unfolds global definitions.
module Felix.Checking.Calculation
    ( Relator, relatorCore, relatorEndpointTypes, relatorIsEquality
    , prepareRelator, applyRelator
    , CompositionPattern, prepareCompositionPattern
    , matchCompositionPattern, compositionPatternsOverlap
    , CalculationError(..), renderCalculationError, CalculationWork
    , defaultCalculationWork, defaultCompositionAdmissionWork
    , runCalculationWork, chargeCalculationWork, calculationCoreWork
    , normalizeCalculationCore, calculationExpansionWork
    , CheckedCompositionLaw, compositionLawMetadata, compositionLawTypes
    , compositionLawConditions, compositionLawOutputTemplate, compositionLawLeft, compositionLawRight, compositionLawResult
    , prepareCompositionLaw
    , CompositionRegistry, emptyCompositionRegistry, compositionRegistryEntries
    , insertCompositionLaw, selectCompositionLaws, compositionRegistryMember
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.GlobalTyping (GlobalTyping)
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Semantic
import Felix.Checking.Notion.SourceEvidence
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Felix.Checking.Kernel.Conversion qualified as Conversion
import Felix.Checking.Notion.TermIndex (indexWork)
import Control.Monad (unless, when)
import Data.Bifunctor (first)
import Data.Maybe (catMaybes)
import Control.Monad.State.Strict qualified as State
import Control.Monad.Trans.Except qualified as Except
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Word (Word)
import Numeric.Natural (Natural)

data CalculationError
    = CalculationWorkExhausted
    | CalculationInvalid !Text
    deriving stock (Show, Eq)

renderCalculationError :: CalculationError -> Text
renderCalculationError CalculationWorkExhausted = "the calculation or composition admission work allowance was exhausted"
renderCalculationError (CalculationInvalid reason) = reason

type CalculationWork m = Except.ExceptT CalculationError (State.StateT Word m)

-- These allowances have distinct owners, independently of optional proof
-- preparation and formation search. An inner scan never replenishes either.
defaultCalculationWork :: Word
defaultCalculationWork = 1000000

defaultCompositionAdmissionWork :: Word
defaultCompositionAdmissionWork = 262144

runCalculationWork :: Word -> CalculationWork m value -> m (Either CalculationError value, Word)
runCalculationWork allowance action = State.runStateT (Except.runExceptT action) allowance

chargeCalculationWork :: Monad m => Natural -> CalculationWork m ()
chargeCalculationWork amount = do
    remaining <- State.get
    if amount <= fromIntegral remaining then State.put (remaining - fromIntegral amount)
        else Except.throwE CalculationWorkExhausted

calculationCoreWork
    :: (Monad m, Show failure)
    => (Word -> (Either (CountedCoreFailure failure) value, Word)) -> CalculationWork m value
calculationCoreWork operation = do
    allowance <- State.get
    let (result,remaining) = operation allowance
    State.put remaining
    case result of
        Right value -> pure value
        Left CountedCoreStructuralWorkExhausted -> Except.throwE CalculationWorkExhausted
        Left (CountedCoreOperationFailed failure) -> invalid (Text.pack (show failure))

invalid :: Monad m => Text -> CalculationWork m value
invalid = Except.throwE . CalculationInvalid

normalizeCalculationCore
    :: Monad m => GlobalTyping ObjectId -> ScopedCheckedCore ObjectId -> CalculationWork m (ScopedCheckedCore ObjectId)
normalizeCalculationCore typing term = do
    remaining <- State.get
    let report = Conversion.betaNormalizeChecked (Conversion.ConversionRecoveryTyping typing typing)
            (Conversion.conversionLimit remaining) term
        cost = Conversion.conversionCostAmount (Conversion.conversionCost report)
    State.put (remaining - cost)
    case Conversion.conversionResult report of
        Right normalized -> pure normalized
        Left Conversion.ConversionLimitExhausted{} -> Except.throwE CalculationWorkExhausted
        Left failure -> invalid (Text.pack (show failure))

calculationExpansionWork :: Monad m => ExpansionWork m value -> CalculationWork m value
calculationExpansionWork action = Except.ExceptT (first failure <$> Except.runExceptT action)
  where
    failure problem | Just _ <- expansionRejectedDebit problem = CalculationWorkExhausted
                    | otherwise = CalculationInvalid (renderExpansionFailure problem)

-- The occurrence tree shares the normalized Core and computes scope escape
-- information once. Each candidate then visits only the nodes it compares.
data Relator = Relator !(ScopedCheckedCore ObjectId) !(CheckedOccurrence ObjectId)

relatorCore :: Relator -> ScopedCheckedCore ObjectId
relatorCore (Relator value _) = value

relatorEndpointTypes :: Relator -> (CoreType, CoreType)
relatorEndpointTypes (Relator value _) = case scopedCoreType value of
    TyArrow left (TyArrow right TyProp) -> (left,right)
    _ -> impossible "a checked relator lost its binary predicate type"

relatorIsEquality :: Relator -> Bool
relatorIsEquality (Relator value _) = case scopedCoreTerm value of
    CLam _ (CLam _ (CEq _ (CBound 1) (CBound 0))) -> True
    _ -> False

prepareRelator :: Monad m => GlobalTyping ObjectId -> ScopedCheckedCore ObjectId -> CalculationWork m Relator
prepareRelator typing value = do
    normalized <- normalizeCalculationCore typing value
    case (scopedCoreType normalized, scopedCoreTerm normalized) of
        (TyArrow _ (TyArrow _ TyProp), CLam _ (CLam _ _)) -> pure ()
        _ -> invalid "a relator must be an explicit binary predicate"
    occurrences <- calculationCoreWork (\work -> countedAnalyseCanonicalOccurrences typing work
        (scopedCoreContext normalized) (scopedCoreTerm normalized))
    pure (Relator normalized occurrences)

applyRelator
    :: Monad m => GlobalTyping ObjectId -> Relator -> ScopedCheckedCore ObjectId -> ScopedCheckedCore ObjectId
    -> CalculationWork m (ScopedCheckedCore ObjectId)
applyRelator typing relation left right = do
    appliedLeft <- apply (relatorCore relation) left
    result <- apply appliedLeft right
    normalizeCalculationCore typing result
  where
    apply function argument = calculationCoreWork (\work -> countedApplyScopedCore work function argument)
        >>= maybe (invalid "a relator application changed scope or endpoint type") pure

-- A side bit gives independent laws disjoint metavariable namespaces during
-- overlap checking. Bound variables remain rigid de Bruijn indices.
data Meta = Meta !Bool !Natural deriving stock (Eq, Ord)
data Pattern
    = Parameter !Meta !CoreType
    | Rigid !CoreType !(CanonicalTerm ObjectId) ![Pattern]

data CompositionPattern = CompositionPattern !Pattern !Pattern

prepareCompositionPattern
    :: Monad m => Map Natural CoreType -> Relator -> Relator -> CalculationWork m CompositionPattern
prepareCompositionPattern = preparePatterns True

preparePatterns
    :: Monad m => Bool -> Map Natural CoreType -> Relator -> Relator -> CalculationWork m CompositionPattern
preparePatterns requireAll parameters (Relator left leftTree) (Relator right rightTree) = do
    same <- calculationCoreWork (\work -> countedCoreTypeListIdentity work (scopedCoreContext left) (scopedCoreContext right))
    unless same (invalid "composition inputs have different lexical contexts")
    (a,leftUsed) <- compile 0 leftTree
    (b,rightUsed) <- compile 0 rightTree
    chargeCalculationWork (fromIntegral (Map.size parameters))
    unless (not requireAll || leftUsed <> rightUsed == Map.keysSet parameters)
        (invalid "every composition parameter must occur in its normalized inputs")
    pure (CompositionPattern a b)
  where
    compile depth occurrence = do
        chargeCalculationWork 1
        case checkedOccurrenceView occurrence of
            OccurrenceBound index | index >= depth -> do
                chargeCalculationWork (indexWork (Map.size parameters) 1)
                expected <- maybe (invalid "a relator captures a composition endpoint") pure (Map.lookup (index-depth) parameters)
                same <- calculationCoreWork (\work -> countedCoreTypeIdentity work expected (checkedOccurrenceType occurrence))
                unless same (invalid "a composition parameter changed type")
                pure (Parameter (Meta False (index-depth)) expected,Set.singleton (index-depth))
            OccurrenceApplication function _ -> do
                case checkedOccurrenceView function of
                    OccurrenceBound index | index >= depth -> invalid "composition parameters cannot be applied as functions"
                    _ -> pure ()
                rigid depth occurrence
            _ -> rigid depth occurrence
    rigid depth occurrence = do
        let (tag,children) = occurrenceShape occurrence
            nested = depth + binderCount tag
        results <- traverse (compile nested) children
        chargeCalculationWork (sum (fromIntegral . Set.size . snd <$> results))
        pure (Rigid (checkedOccurrenceType occurrence) tag (fst <$> results), Set.unions (snd <$> results))

matchCompositionPattern
    :: Monad m => CompositionPattern -> Relator -> Relator
    -> CalculationWork m (Maybe (Map Natural (ScopedCheckedCore ObjectId)))
matchCompositionPattern (CompositionPattern left right) (Relator _ a) (Relator _ b) = do
    leftType <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType left) (checkedOccurrenceType a))
    rightType <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType right) (checkedOccurrenceType b))
    if not (leftType && rightType) then pure Nothing else do
        matchedLeft <- match Map.empty left a
        maybe (pure Nothing) (\bindings -> match bindings right b) matchedLeft
  where
    match bindings pattern' occurrence = do
        chargeCalculationWork 1
        same <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType pattern') (checkedOccurrenceType occurrence))
        if not same then pure Nothing else case pattern' of
            Parameter (Meta _ index) _ -> do
                value <- calculationCoreWork (\work -> countedRebaseCheckedOccurrence work occurrence)
                case value of
                    Nothing -> pure Nothing
                    Just captured -> do
                        chargeCalculationWork (indexWork (Map.size bindings) 2)
                        case Map.lookup index bindings of
                            Nothing -> pure (Just (Map.insert index captured bindings))
                            Just previous -> do
                                equal <- calculationCoreWork (\work -> countedScopedCoreIdentity work previous captured)
                                pure (if equal then Just bindings else Nothing)
            Rigid _ tag children -> do
                let (actual,arguments) = occurrenceShape occurrence
                equal <- calculationCoreWork (\work -> countedCanonicalIdentity work tag actual)
                if equal then matchChildren bindings children arguments else pure Nothing
    matchChildren bindings [] [] = pure (Just bindings)
    matchChildren bindings (p:ps) (value:values) = do
        found <- match bindings p value
        maybe (pure Nothing) (\next -> matchChildren next ps values) found
    matchChildren _ _ _ = impossible "equal Core constructors have different child counts"

compositionPatternsOverlap :: Monad m => CompositionPattern -> CompositionPattern -> CalculationWork m Bool
compositionPatternsOverlap (CompositionPattern a b) (CompositionPattern c d) = do
    sameLeft <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType a) (patternType c))
    sameRight <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType b) (patternType d))
    if not (sameLeft && sameRight) then pure False else do
        c' <- rename c
        d' <- rename d
        isJust <$> unify Map.empty [(a,c'),(b,d')]
  where
    rename pattern' = chargeCalculationWork 1 >> case pattern' of
        Parameter (Meta _ index) ty -> pure (Parameter (Meta True index) ty)
        Rigid ty tag children -> Rigid ty tag <$> traverse rename children
    dereference bindings pattern' = do
        chargeCalculationWork 1
        case pattern' of
            Parameter variable _ -> do
                chargeCalculationWork (indexWork (Map.size bindings) 1)
                maybe (pure pattern') (dereference bindings) (Map.lookup variable bindings)
            _ -> pure pattern'
    unify bindings [] = pure (Just bindings)
    unify bindings ((left,right):pending) = do
        a' <- dereference bindings left
        b' <- dereference bindings right
        same <- calculationCoreWork (\work -> countedCoreTypeIdentity work (patternType a') (patternType b'))
        if not same then pure Nothing else case (a',b') of
            (Parameter x _,Parameter y _) | x == y -> unify bindings pending
            (Parameter x _,value) -> bind bindings pending x value
            (value,Parameter x _) -> bind bindings pending x value
            (Rigid _ tag xs,Rigid _ other ys) -> do
                equal <- calculationCoreWork (\work -> countedCanonicalIdentity work tag other)
                if equal then unify bindings (zip xs ys <> pending) else pure Nothing
    bind bindings pending variable value = do
        allowed <- closedWithout bindings variable 0 value
        if not allowed then pure Nothing else do
            chargeCalculationWork (indexWork (Map.size bindings) 1)
            unify (Map.insert variable value bindings) pending
    -- A parameter may contain binders of its own, but cannot capture either
    -- endpoint or a binder surrounding the matched occurrence. This is also
    -- the occurs check, shared across the pair of input patterns.
    closedWithout bindings variable depth value = do
        current <- dereference bindings value
        case current of
            Parameter other _ -> pure (other /= variable)
            Rigid _ (CBound index) _ -> pure (index < depth)
            Rigid _ tag children -> allM (closedWithout bindings variable (depth + binderCount tag)) children
    allM _ [] = pure True
    allM action (x:xs) = action x >>= \accepted -> if accepted then allM action xs else pure False

patternType :: Pattern -> CoreType
patternType (Parameter _ ty) = ty
patternType (Rigid ty _ _) = ty

binderCount :: CanonicalTerm global -> Natural
binderCount = \case
    CLam{} -> 1
    CForall{} -> 1
    CExists{} -> 1
    _ -> 0

-- Shallow constructor tags retain all rigid labels and types. Their dummy
-- children are never admitted as terms; counted identity compares tags only.
occurrenceShape :: CheckedOccurrence ObjectId -> (CanonicalTerm ObjectId, [CheckedOccurrence ObjectId])
occurrenceShape occurrence = case checkedOccurrenceView occurrence of
    OccurrenceBound index -> (CBound index,[])
    OccurrenceGlobal global -> (CGlobal global,[])
    OccurrenceIntrinsic intrinsic -> (CIntrinsic intrinsic,[])
    OccurrenceLogicalSelect ty -> (CLogicalSelect ty,[])
    OccurrenceOpaqueInteger integer -> (COpaqueInteger integer,[])
    OccurrenceApplication a b -> (CApp CTruth CTruth,[a,b])
    OccurrenceLambda ty body -> (CLam ty CTruth,[body])
    OccurrenceFalsum -> (CFalsum,[])
    OccurrenceTruth -> (CTruth,[])
    OccurrenceNegation body -> (CNot CTruth,[body])
    OccurrenceConjunction a b -> (CAnd CTruth CTruth,[a,b])
    OccurrenceDisjunction a b -> (COr CTruth CTruth,[a,b])
    OccurrenceImplication a b -> (CImp CTruth CTruth,[a,b])
    OccurrenceEquality ty a b -> (CEq ty CTruth CTruth,[a,b])
    OccurrenceUniversal ty body -> (CForall ty CTruth,[body])
    OccurrenceExistential ty body -> (CExists ty CTruth,[body])

-- Checked schemas keep the theorem's actual telescope. Nothing is reordered
-- to make matching or proof instantiation more convenient.
data CheckedCompositionLaw = CheckedCompositionLaw
    { compositionLawOrigin :: !FactSlot
    , lawMetadata :: !SemanticRelationComposition
    , lawTypes :: !(Vector CoreType)
    , lawConditions :: !(Vector (ScopedCheckedCore ObjectId))
    , lawLeft :: !Relator
    , lawRight :: !Relator
    , lawOutputTemplate :: !(ScopedCheckedCore ObjectId)
    , lawResult :: !Relator
    , compositionLawPattern :: !CompositionPattern
    }

-- Ordinary accessors keep record updates behind the admission boundary.
compositionLawMetadata :: CheckedCompositionLaw -> SemanticRelationComposition
compositionLawMetadata = lawMetadata

compositionLawTypes :: CheckedCompositionLaw -> Vector CoreType
compositionLawTypes = lawTypes

compositionLawConditions :: CheckedCompositionLaw -> Vector (ScopedCheckedCore ObjectId)
compositionLawConditions = lawConditions

compositionLawLeft, compositionLawRight, compositionLawResult :: CheckedCompositionLaw -> Relator
compositionLawLeft = lawLeft
compositionLawRight = lawRight
compositionLawResult = lawResult

compositionLawOutputTemplate :: CheckedCompositionLaw -> ScopedCheckedCore ObjectId
compositionLawOutputTemplate = lawOutputTemplate

prepareCompositionLaw
    :: Monad m => GlobalTyping ObjectId
    -> ([CoreType] -> Vector Natural -> CanonicalTerm ObjectId -> AbbreviationExpansion -> CalculationWork m ())
    -> FactSlot -> ScopedCheckedCore ObjectId -> SemanticRelationComposition
    -> CalculationWork m CheckedCompositionLaw
prepareCompositionLaw typing validateSource origin theorem metadata = do
    unless (null (scopedCoreContext theorem)) (invalid "a composition theorem must be closed")
    (types,body) <- telescope [] (scopedCoreTerm theorem)
    let count = Vector.length types
        (x,y,z) = compositionEndpointPositions metadata
        endpoints = [x,y,z]
        context = reverse (toList types)
        layout = Vector.fromList (reverse (take count [0..]))
        parameterTypes = Map.fromList [(fromIntegral (count-1-i),ty)
            | (i,ty) <- zip [0..] (toList types), fromIntegral i `notElem` endpoints]
    chargeCalculationWork (fromIntegral count * 4)
    unless (x /= y && y /= z && x /= z && all (< fromIntegral count) endpoints)
        (invalid "composition endpoint positions must be distinct and inside the theorem telescope")
    (conditions,tail') <- peel (toList (compositionConditions metadata)) body
    (left,right,result) <- case tail' of
        CImp (CAnd a b) c -> pure (a,b,c)
        _ -> invalid "the last composition assumption must be a two-link conjunction"
    checkedConditions <- for (zip conditions (toList (compositionConditions metadata))) \(condition,source) -> do
        checked <- check context condition
        validateSource context layout condition source
        pure checked
    (a,_) <- relation context types x y left (compositionLeftSource metadata)
    (b,_) <- relation context types y z right (compositionRightSource metadata)
    (c,outputTemplate) <- relation context types x z result (compositionResultSource metadata)
    when (relatorIsEquality a || relatorIsEquality b)
        (invalid "composition inputs cannot be the equality relator")
    pattern' <- prepareCompositionPattern parameterTypes a b
    void (preparePatterns False parameterTypes c c)
    pure (CheckedCompositionLaw origin metadata types (Vector.fromList checkedConditions) a b outputTemplate c pattern')
  where
    check context term = calculationCoreWork (\work -> countedCheckScopedCanonicalCore typing work context term)
    telescope accumulated = \case
        CForall ty rest -> chargeCalculationWork 1 >> telescope (ty:accumulated) rest
        rest -> pure (Vector.fromList (reverse accumulated),rest)
    peel [] body = pure ([],body)
    peel (_:rest) (CImp premise conclusion) = do
        chargeCalculationWork 1
        (conditions,body) <- peel rest conclusion
        pure (premise:conditions,body)
    peel _ _ = invalid "composition condition metadata exceeds the theorem's implication prefix"
    relation context types left right formula source = do
        let count = fromIntegral (Vector.length types)
            leftIndex = count-left-1
            rightIndex = count-right-1
            leftType = types Vector.! fromIntegral left
            rightType = types Vector.! fromIntegral right
            replace depth index = pure (CBound (depth + if index == leftIndex then 1
                else if index == rightIndex then 0 else index+2))
            layout = Vector.fromList ([1,0] <> reverse (take (Vector.length types) [2..]))
        body <- instantiateCanonicalPrefixWith (chargeCalculationWork 1) count replace 0 formula
        -- The source template distinguishes fresh endpoint slots from captures,
        -- even when their written values happened to be equal.
        validateCaptures count source
        let sourceContext = rightType:leftType:context
        validateSource sourceContext layout body (relationSourceBody source)
        for_ (relationSourceCaptures source) \capture ->
            validateSource sourceContext layout CTruth (TermExpansion capture)
        predicate <- check context (CLam leftType (CLam rightType body))
        normalized <- prepareRelator typing predicate
        pure (normalized,predicate)
    validateCaptures count source = do
        let (x,y,z) = compositionEndpointPositions metadata
            forbidden = Set.fromList [count-x+1,count-y+1,count-z+1]
        let term capture depth value = chargeCalculationWork 1 >> case value of
                ExpansionFormal index -> when ((capture && index < 2) || (index >= 2 && index-2 `elem` [x,y,z]))
                    (invalid "a composition relator captures an endpoint as a parameter")
                ExpansionLocal index -> unless (index < depth) (invalid "a source template local escapes its binders")
                ExpansionOpaque core -> do
                    indices <- canonicalFreeIndicesWith (chargeCalculationWork 1) core
                    chargeCalculationWork (fromIntegral (Set.size indices))
                    when (any (\index -> index >= depth &&
                        (Set.member (index-depth) forbidden || (capture && index-depth < 2))) indices)
                        (invalid "a composition relator captures an endpoint inside an operand")
                ExpansionProvider _ children -> traverse_ (term capture depth) children
                ExpansionPair a b -> term capture depth a >> term capture depth b
            input depth (SourceInput binders value) = do
                chargeCalculationWork (fromIntegral (length binders))
                term False (depth + fromIntegral (length binders)) value
            evidence depth expression = chargeCalculationWork 1 >> case expression of
                SourceResidual{} -> pure ()
                SourceInputs _ inputs -> traverse_ (input depth) inputs
                SourceWithInputs inputs body -> traverse_ (input depth) inputs >> evidence depth body
                SourceAtom atom -> traverse_ (term False depth) atom
                SourceAnd a b -> evidence depth a >> evidence depth b
                SourceBind body -> evidence (depth+1) body
                SourceExists body -> evidence (depth+1) body
                SourceOr a b -> evidence depth a >> evidence depth b
                SourceIff a b -> evidence depth a >> evidence depth b
                SourceRequire a b -> evidence depth a >> evidence depth b
        traverse_ (term True 0) (relationSourceCaptures source)
        case relationSourceBody source of
            TermExpansion{} -> invalid "a composition source template must describe a proposition"
            PropositionExpansion described equalities -> do
                evidence 0 described
                for_ equalities \(ExpansionEquality a b _) -> term False 0 a >> term False 0 b

newtype CompositionRegistry = CompositionRegistry (Map SemanticFactOccurrenceFingerprint CheckedCompositionLaw)

emptyCompositionRegistry :: CompositionRegistry
emptyCompositionRegistry = CompositionRegistry Map.empty

compositionRegistryEntries :: CompositionRegistry -> [(SemanticFactOccurrenceFingerprint, CheckedCompositionLaw)]
compositionRegistryEntries (CompositionRegistry entries) = Map.toAscList entries

insertCompositionLaw
    :: Monad m => SemanticFactOccurrenceFingerprint -> CheckedCompositionLaw -> CompositionRegistry
    -> CalculationWork m CompositionRegistry
insertCompositionLaw fingerprint law registry@(CompositionRegistry entries) = do
    chargeCalculationWork (indexWork (Map.size entries) 1)
    if Map.member fingerprint entries then pure registry else do
        for_ (Map.toAscList entries) \(_previous,existing) -> do
            chargeCalculationWork 1
            overlaps <- compositionPatternsOverlap (compositionLawPattern law) (compositionLawPattern existing)
            when overlaps (invalid ("overlapping composition declarations: " <> Text.pack (show (compositionLawOrigin existing))
                <> " and " <> Text.pack (show (compositionLawOrigin law))))
        chargeCalculationWork (indexWork (Map.size entries) 1)
        pure (CompositionRegistry (Map.insert fingerprint law entries))

selectCompositionLaws
    :: Monad m => CompositionRegistry -> Relator -> Relator
    -> CalculationWork m [(SemanticFactOccurrenceFingerprint, CheckedCompositionLaw, Map Natural (ScopedCheckedCore ObjectId))]
selectCompositionLaws (CompositionRegistry entries) left right = fmap catMaybes $
    for (Map.toAscList entries) \(fingerprint,law) -> do
        chargeCalculationWork 1
        match <- matchCompositionPattern (compositionLawPattern law) left right
        pure ((\bindings -> (fingerprint,law,bindings)) <$> match)

compositionRegistryMember :: SemanticFactOccurrenceFingerprint -> CompositionRegistry -> Bool
compositionRegistryMember fingerprint (CompositionRegistry entries) = Map.member fingerprint entries
