{-# LANGUAGE NoImplicitPrelude #-}

-- | Pure source abstraction and substitution, shared by abbreviations and
-- calculation relators. Resolution and formation remain with the caller.
module Felix.Checking.SourceTemplate
    ( SourceTemplateInstance(..)
    , abstractSourceTerm, abstractSourceProposition
    , sourceTemplateInputAnnotations
    , sourceTemplateProviders
    , instantiateSourceTemplate
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity (ObjectId)
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Notion.SourceEvidence
import Felix.Checking.Notion.TermIndex (indexWork)
import Felix.Checking.Semantic
import Felix.Checking.SourceTerm qualified as Source
import Felix.Report.Location (Location)
import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except qualified as Except
import Control.Monad.State.Strict qualified as State
import Data.Map.Strict qualified as Map
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Numeric.Natural (Natural)

type SourceTerm presentation = Source.SourceTermOccurrence presentation (CanonicalTerm ObjectId)
type SourceAtom presentation = Notion.SourceNotionOccurrence presentation (SourceTerm presentation) (CanonicalTerm ObjectId)
type SourceEquality presentation = Notion.SourceEqualityOccurrence (SourceTerm presentation) (CanonicalTerm ObjectId)

-- Neutral parts; the source elaborator owns its proposition envelope.
data SourceTemplateInstance presentation
    = InstantiatedTerm !(SourceTerm presentation)
    | InstantiatedProposition !(CanonicalTerm ObjectId)
        !(SourceEvidence SupportTermTemplate (SourceAtom presentation))
        ![SourceEquality presentation]

-- The layout maps nearest-first formal binders to source-order slots. Private
-- binders remain local, and all other operands retain their complete Core.
abstractSourceTerm
    :: Monad m => Vector Natural -> Natural -> SourceTerm presentation -> ExpansionWork m ExpansionTerm
abstractSourceTerm layout depth occurrence = do
    chargeExpansion 1
    case Source.sourceTermOccurrenceProvider occurrence of
        Just provider -> ExpansionProvider (Source.sourceTermProviderHead provider)
            <$> traverse (abstractSourceTerm layout depth) (Source.sourceTermProviderArguments provider)
        Nothing -> case Source.sourceTermOccurrenceOrderedPair occurrence of
            Just (left,right) -> ExpansionPair <$> abstractSourceTerm layout depth left <*> abstractSourceTerm layout depth right
            Nothing -> abstractOpaque layout depth (Source.sourceTermOccurrenceCore occurrence)

abstractOpaque :: Monad m => Vector Natural -> Natural -> CanonicalTerm ObjectId -> ExpansionWork m ExpansionTerm
abstractOpaque layout depth = \case
    CBound index
        | index < depth -> pure (ExpansionLocal index)
        | index-depth < fromIntegral (Vector.length layout)
        , Just slot <- layout Vector.!? fromIntegral (index-depth) -> pure (ExpansionFormal slot)
    term -> do
        void (expansionCoreWork (\work -> countedCanonicalIdentity work term term))
        pure (ExpansionOpaque term)

abstractSourceProposition
    :: Monad m => Vector Natural
    -> SourceEvidence SupportTermTemplate (SourceAtom presentation)
    -> [SourceEquality presentation] -> ExpansionWork m AbbreviationExpansion
abstractSourceProposition layout evidence equalities = PropositionExpansion
    <$> describe 0 evidence <*> traverse equality equalities
  where
    describe depth expression = chargeExpansion 1 >> case expression of
        SourceResidual{} -> pure (SourceResidual Nothing)
        SourceInputs _ terms -> SourceInputs Nothing <$> traverse (input depth) terms
        SourceWithInputs terms body -> withSourceInputs <$> traverse (input depth) terms <*> describe depth body
        SourceAtom assertion -> SourceAtom <$> traverseAtomTemplateArguments
            (abstractSourceTerm layout depth) (Notion.sourceAssertionAtom assertion)
        SourceAnd left right -> SourceAnd <$> describe depth left <*> describe depth right
        SourceOr left right -> SourceOr <$> describe depth left <*> describe depth right
        SourceIff left right -> SourceIff <$> describe depth left <*> describe depth right
        SourceExists body -> SourceExists <$> describe (depth+1) body
        SourceBind body -> SourceBind <$> describe (depth+1) body
        SourceRequire premise body -> SourceRequire <$> describe depth premise <*> describe depth body
    input depth (SourceInput binders term) = SourceInput binders <$> support (depth + fromIntegral (length binders)) term
    support depth term = chargeExpansion 1 >> case term of
        TemplateVariable value -> abstractOpaque layout depth value
        TemplateClosed value -> pure (ExpansionOpaque (closedSetValueTerm value))
        TemplateProvider provider children -> ExpansionProvider provider <$> traverse (support depth) children
        TemplateOrderedPair left right -> ExpansionPair <$> support depth left <*> support depth right
    equality occurrence = do
        chargeExpansion 1
        left <- abstractSourceTerm layout 0 (Notion.sourceEqualityLeft occurrence)
        right <- abstractSourceTerm layout 0 (Notion.sourceEqualityRight occurrence)
        path (Notion.sourceEqualityPath occurrence)
        pure (ExpansionEquality left right (Notion.sourceEqualityPath occurrence))
    path = \case
        Notion.ConjunctionHere -> chargeExpansion 1
        Notion.ConjunctionLeft rest -> chargeExpansion 1 >> path rest
        Notion.ConjunctionRight rest -> chargeExpansion 1 >> path rest

-- Resolve each owner-bearing provider once before entering pure substitution.
sourceTemplateProviders :: Monad m => AbbreviationExpansion -> ExpansionWork m (Set SourceProviderHead)
sourceTemplateProviders expansion = State.execStateT (case expansion of
    TermExpansion term -> visit term
    PropositionExpansion evidence equalities -> do
        describe evidence
        for_ equalities \(ExpansionEquality left right _) -> lift (chargeExpansion 1) >> visit left >> visit right) Set.empty
  where
    visit term = lift (chargeExpansion 1) >> case term of
        ExpansionProvider provider arguments -> do
            known <- State.get
            lift (chargeExpansion (indexWork (Set.size known) 1))
            State.modify' (Set.insert provider)
            traverse_ visit arguments
        ExpansionPair left right -> visit left >> visit right
        _ -> pure ()
    describe evidence = lift (chargeExpansion 1) >> case evidence of
        SourceResidual{} -> pure ()
        SourceInputs _ terms -> traverse_ input terms
        SourceWithInputs terms body -> traverse_ input terms >> describe body
        SourceAtom atom -> traverse_ visit atom
        SourceAnd left right -> describe left >> describe right
        SourceBind body -> describe body
        SourceExists body -> describe body
        SourceOr a b -> describe a >> describe b
        SourceIff a b -> describe a >> describe b
        SourceRequire condition body -> describe condition >> describe body
    input (SourceInput binders term) = lift (chargeExpansion (1 + fromIntegral (length binders))) >> visit term

-- The read-only provider map contains the terminal object for every resolved
-- global or field provider. Intrinsic providers have their fixed denotation.
-- Actuals carry concrete types; the layout freezes their source slot identity,
-- including when two different slots happen to denote the same Core value.
instantiateSourceTemplate
    :: Monad m
    => Source.SourceTermCheckingContext ObjectId
    -> Map SourceProviderHead ObjectId
    -> Location -> presentation -> (Notion.ConjunctionPath -> WrittenOrigin)
    -> Vector Natural -> Vector (SourceTerm presentation)
    -> CanonicalTerm ObjectId -> AbbreviationExpansion
    -> ExpansionWork m (SourceTemplateInstance presentation)
instantiateSourceTemplate context providers location presentation origin layout actuals body expansion =
    State.evalStateT instantiate Map.empty
  where
    count = fromIntegral (Vector.length layout)
    charge amount = lift (chargeExpansion amount)
    core operation = lift (expansionCoreWork operation)
    invalid message = lift (Except.throwE (ExpansionInvalid message))
    required message value = maybe (invalid message) pure value
    slot depth index = do
        memo <- State.get
        charge (indexWork (Map.size memo) 1)
        case Map.lookup (index,depth) memo of
            Just term -> pure term
            Nothing -> do
                unless (index < fromIntegral (Vector.length actuals)) (invalid "source template formal is out of range")
                actual <- required "source template formal is out of range" (actuals Vector.!? fromIntegral index)
                shifted <- if depth == 0 then pure actual else core
                    (\work -> Source.countedShiftCanonicalSourceTermOccurrence work depth 0 actual)
                charge (indexWork (Map.size memo) 1)
                State.modify' (Map.insert (index,depth) shifted)
                pure shifted
    substitute depth = instantiateCanonicalPrefixWith (charge 1) count
        (\nested index -> do
            formal <- required "source template binder is out of range" (layout Vector.!? fromIntegral index)
            Source.sourceTermOccurrenceCore <$> slot nested formal) depth
    opaque binders term = do
        checked <- core (\work -> countedCheckScopedCanonicalCore (Source.sourceTermGlobalTyping context)
            work (binders <> Source.sourceTermBinderTypes context) term)
        pure (Source.sourceTermOccurrence term (scopedCoreType checked) presentation)
    instantiateTerm binders expression = charge 1 >> case expression of
        ExpansionFormal index -> slot (fromIntegral (length binders)) index
        ExpansionLocal index -> opaque binders (CBound index)
        ExpansionOpaque value -> substitute (fromIntegral (length binders)) value >>= opaque binders
        ExpansionPair left right -> do
            a <- instantiateTerm binders left
            b <- instantiateTerm binders right
            charge 3
            required "source template pair is not set-valued" (Source.sourceOrderedPairTermOccurrence a b
                (CApp (CApp (CIntrinsic OrderedPair) (Source.sourceTermOccurrenceCore a)) (Source.sourceTermOccurrenceCore b)) presentation)
        ExpansionProvider provider arguments -> do
            values <- traverse (instantiateTerm binders) arguments
            charge (1 + fromIntegral (Vector.length arguments))
            case provider of
                GlobalSourceProvider reference -> do
                    identity <- required "source template global provider is unavailable" (Map.lookup provider providers)
                    required "source template global provider has the wrong arity"
                        (Source.sourceGlobalProviderTermOccurrence reference values
                            (foldl' CApp (CGlobal identity) (Source.sourceTermOccurrenceCore <$> toList values)) presentation)
                StructureFieldSourceProvider identity projection -> do
                    selected <- required "source template field provider is unavailable" (Map.lookup provider providers)
                    unless (selected == projection) (invalid "source template field provider changed identity")
                    case toList values of
                        [receiver] -> required "source template field receiver is not a set"
                            (Source.sourceStructureFieldProviderTermOccurrence identity projection receiver presentation)
                        _ -> invalid "source template field provider has the wrong arity"
                IntrinsicSourceProvider provider' -> required "source template intrinsic provider has the wrong arity"
                    (Source.sourceIntrinsicProviderTermOccurrence provider' values presentation)
                FiniteSetLiteralSourceProvider -> do
                    spine <- required "source template finite set is empty" (NonEmpty.nonEmpty (toList values))
                    required "source template finite set contains a non-set"
                        (Source.sourceFiniteSetLiteralTermOccurrence spine presentation)
    input binders (SourceInput private value) = SourceInput private . Source.sourceSupportTemplate id <$> instantiateTerm (private <> binders) value
    evidence binders path formula expression = charge 1 >> case expression of
        SourceResidual _ -> pure (SourceResidual (Just (origin (path Notion.ConjunctionHere))))
        SourceInputs _ inputs -> SourceInputs (Just (origin (path Notion.ConjunctionHere))) <$> traverse (input binders) inputs
        SourceWithInputs inputs nested -> withSourceInputs <$> traverse (input binders) inputs <*> evidence binders path formula nested
        SourceAtom atom -> do
            instantiated <- traverseAtomTemplateArguments (instantiateTerm binders) atom
            pure (SourceAtom (Notion.withSourceNotionOrigin (origin (path Notion.ConjunctionHere))
                (Notion.sourceNotionAssertionFromTemplate instantiated formula Notion.ConjunctionHere location)))
        SourceAnd left right | CAnd a b <- formula -> SourceAnd
            <$> evidence binders (path . Notion.ConjunctionLeft) a left
            <*> evidence binders (path . Notion.ConjunctionRight) b right
        SourceBind nested | CForall TySet value <- formula -> SourceBind <$> evidence (TySet:binders) path value nested
        SourceExists nested | CExists TySet value <- formula -> SourceExists <$> evidence (TySet:binders) path value nested
        SourceOr a b | COr left right <- formula -> SourceOr <$> evidence binders path left a <*> evidence binders path right b
        SourceIff a b | CEq TyProp left right <- formula -> SourceIff <$> evidence binders path left a <*> evidence binders path right b
        SourceRequire premise nested | CImp a b <- formula -> SourceRequire <$> evidence binders path a premise <*> evidence binders path b nested
        _ -> invalid "source template evidence disagrees with its proposition"
    equality (ExpansionEquality left right path) = do
        charge 1
        a <- instantiateTerm [] left
        b <- instantiateTerm [] right
        pure (Notion.setSourceEqualityOccurrence a b
            (CEq TySet (Source.sourceTermOccurrenceCore a) (Source.sourceTermOccurrenceCore b)) path location)
    instantiate = do
        formula <- substitute 0 body
        case expansion of
            TermExpansion value -> InstantiatedTerm <$> instantiateTerm [] value
            PropositionExpansion described equalities -> InstantiatedProposition formula
                <$> evidence [] id formula described <*> traverse equality equalities

-- Extra views belong to the formula and binder scope in which their formal
-- operand occurs. Traverse the logical slot occurrences once; never mine Core
-- for provider constructions or choose a representative written view.
sourceTemplateInputAnnotations
    :: Monad m => Vector Natural -> Map Natural [SourceTerm presentation]
    -> CanonicalTerm ObjectId -> ExpansionWork m [SourceInput SupportTermTemplate]
sourceTemplateInputAnnotations layout views formula = do
    occurrences <- State.execStateT (collect [] formula) Set.empty
    fmap concat $ for (Set.toAscList occurrences) \(slot,binders) -> do
        chargeExpansion (indexWork (Map.size views) 1)
        for (Map.findWithDefault [] slot views) \view -> do
            chargeExpansion 1
            shifted <- expansionCoreWork (\work -> Source.countedShiftCanonicalSourceTermOccurrence
                work (fromIntegral (length binders)) 0 view)
            pure (SourceInput binders (Source.sourceSupportTemplate id shifted))
  where
    collect binders term = lift (chargeExpansion 1) >> case term of
        CBound index | index >= fromIntegral (length binders)
            , let formal = index - fromIntegral (length binders)
            , formal < fromIntegral (Vector.length layout) -> do
                let slot = layout Vector.! fromIntegral formal
                lift (chargeExpansion (indexWork (Map.size views) 1))
                when (Map.member slot views) do
                    known <- State.get
                    lift (chargeExpansion (indexWork (Set.size known) (1 + fromIntegral (length binders))))
                    State.modify' (Set.insert (slot,binders))
        CApp a b -> collect binders a >> collect binders b
        CLam ty body -> collect (ty:binders) body
        CForall ty body -> collect (ty:binders) body
        CExists ty body -> collect (ty:binders) body
        CNot body -> collect binders body
        CAnd a b -> collect binders a >> collect binders b
        COr a b -> collect binders a >> collect binders b
        CImp a b -> collect binders a >> collect binders b
        CEq _ a b -> collect binders a >> collect binders b
        _ -> pure ()
