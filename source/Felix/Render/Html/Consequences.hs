{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections #-}

-- | A presentation adapter for admitted record realization consequences.
-- It opens their checked envelopes; it neither elaborates source claims nor
-- reconstructs proofs. Unsupported term forms have no invented presentation.
module Felix.Render.Html.Consequences
    ( PublicConsequence(..)
    , ConsequenceMath(..)
    , checkedRecordConsequences
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Identity
import Felix.Checking.Module qualified as Typed
import Felix.Checking.Record qualified as Record
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text

data PublicConsequence = PublicConsequence
    { consequenceLabel :: !Raw.Marker
    , consequenceLocation :: !Location
    , consequenceTarget :: !(FrozenCheckedCore ObjectId)
    , consequenceBinders :: ![Raw.VarSymbol]
    , consequenceHeaders :: ![ConsequenceMath]
    , consequenceConclusion :: !ConsequenceMath
    }
    deriving stock (Show, Eq)

data ConsequenceMath
    = ConsequenceVariable !Raw.VarSymbol
    | ConsequenceGlobal !Semantic.SemanticGlobalKey !Raw.Marker ![ConsequenceMath]
    | ConsequenceField !Raw.StructSymbol !ConsequenceMath
    | ConsequenceStructure !Schema.StructurePhrase !ConsequenceMath ![ConsequenceMath]
    | ConsequenceExactFields ![Raw.StructSymbol] !ConsequenceMath
    | ConsequenceIntrinsic !CoreIntrinsicTag ![ConsequenceMath]
    | ConsequenceBinary !Text !ConsequenceMath !ConsequenceMath
    | ConsequenceUnary !Text !ConsequenceMath
    | ConsequenceQuantified !Text !Raw.VarSymbol !ConsequenceMath
    | ConsequenceTruth !Bool
    | ConsequenceInteger !Integer
    | ConsequenceSeparation !Raw.VarSymbol !ConsequenceMath !ConsequenceMath
    deriving stock (Show, Eq)

checkedRecordConsequences
    :: [Typed.SealedTypedModule]
    -> [(Typed.SealedTypedModule, [Raw.Block])]
    -> Either Text (Map Raw.Marker [PublicConsequence])
checkedRecordConsequences imports modules = Map.fromList . concat <$> traverse collect modules
  where
    allModules = imports <> (fst <$> modules)
    schemas = concatMap (Declaration.evidenceLocalStructureSchemas . Typed.sealedTypedModuleEvidence) allModules
    schemasById = Map.fromList [(Schema.resolvedSchemaId schema, schema) | schema <- schemas]
    structures = Map.fromList
        [(predicate, Schema.resolvedSchemaPhrase schema)
        | sealed <- allModules
        , (identity, predicate) <- Declaration.evidenceLocalStructurePredicates (Typed.sealedTypedModuleEvidence sealed)
        , schema <- maybeToList (Map.lookup identity schemasById)]
    predicates = Map.fromList (concatMap
        (Declaration.evidenceLocalStructurePredicates . Typed.sealedTypedModuleEvidence) allModules)
    declaredStructures = Map.fromList
        [(Schema.resolvedSchemaPhrase schema, predicate)
        | schema <- schemas, predicate <- maybeToList (Map.lookup (Schema.resolvedSchemaId schema) predicates)]
    fields = Map.fromList [(Schema.resolvedFieldProjection field, Schema.resolvedFieldSymbol field)
        | schema <- schemas, field <- Map.elems (Schema.resolvedSchemaFields schema)]
    selectors = Map.fromList [(Schema.resolvedFieldSelector field, Schema.resolvedFieldSymbol field)
        | schema <- schemas, field <- Map.elems (Schema.resolvedSchemaFields schema)]
    globals = Map.fromList
        [(Semantic.semanticGlobalTargetObject (Semantic.semanticGlobalBindingTarget binding),
            (Semantic.semanticGlobalBindingKey binding,
                Raw.Marker (Semantic.semanticBindingLabelText (Semantic.semanticGlobalBindingLabel binding))))
        | sealed <- allModules
        , delta <- Semantic.semanticInterfaceDeclarations (Typed.sealedTypedModuleSemantic sealed)
        , binding <- Semantic.semanticEnvironmentBindings (Semantic.declarationDeltaEnvironment delta)]

    collect (sealed, blocks) = traverse (entry targets) declarations
      where
        targets = Map.fromList
            [(Raw.Marker (Semantic.semanticNameText (Semantic.semanticAliasName alias)),
                (target, Semantic.declarationDeltaSlot delta))
            | delta <- Semantic.semanticInterfaceDeclarations (Typed.sealedTypedModuleSemantic sealed)
            , alias <- Semantic.declarationDeltaAliases delta
            , target <- maybeToList (Declaration.evidenceFactTarget (Typed.sealedTypedModuleEvidence sealed)
                (Semantic.semanticAliasTarget alias))]
        declarations = concatMap declaration blocks
        declaration = \case
            Raw.BlockConstruction here _ label construction ->
                let Raw.SymbolPattern _ variables = Raw.constructionHead construction
                in [(here, label, variables, Schema.structurePhrase
                    (Raw.structApplicationPhrase (Raw.constructionApplication construction)))]
            Raw.BlockInstance here _ label instance' -> [(here, label, [], Schema.structurePhrase
                (Raw.structApplicationPhrase (Raw.instanceApplication instance')))]
            _ -> []

    entry targets (here, label@(Raw.Marker name), variables, phrase) = do
        (_, owner) <- require ("missing admitted record result " <> name) (Map.lookup label targets)
        predicate <- require "record result schema has no admitted predicate" (Map.lookup phrase declaredStructures)
        let selected = [(marker, target) | (marker@(Raw.Marker candidate), (target, slot)) <- Map.toAscList targets
                , slot == owner
                , candidate == name || candidate == name <> "shape"
                    || (name <> "projection_") `Text.isPrefixOf` candidate]
        consequences <- for selected \(marker, target) -> do
            opened <- open variables (embedClosedCore [] target)
            (headers, conclusion) <- envelope (reverse variables)
                (if marker == label then Just (predicate, phrase) else Nothing) opened
            pure (PublicConsequence marker here target variables headers conclusion)
        pure (label, consequences)

    open [] target = Right target
    open (_ : rest) target = case openScopedForall target of
        Just (TySet, body) -> open rest body
        _ -> Left "admitted record consequence lost an explicit set binder"
    envelope variables preferred target = case openScopedImplication target of
        Just (header, rest) -> do
            presented <- proposition variables header
            (headers, conclusion) <- envelope variables preferred rest
            pure (presented : headers, conclusion)
        Nothing -> ([],) <$> case preferred of
            Nothing -> proposition variables target
            Just (predicate, phrase) -> case canonicalApplicationSpine (scopedCoreTerm target) of
                (CGlobal actual, subject : parameters) | actual == predicate ->
                    ConsequenceStructure phrase <$> term variables subject <*> traverse (term variables) parameters
                _ -> Left "the admitted result does not match its written structure predicate"

    proposition variables target
        | Just (subject, identities) <- Record.recognizeRecordExactGlobalShape target = do
            roles <- traverse (\identity -> require "unknown admitted exact-shape selector" (Map.lookup identity selectors)) identities
            ConsequenceExactFields roles <$> term variables subject
        | Just (left, right) <- splitScopedConjunction target = logical "∧" variables left right
        | Just (left, right) <- splitScopedDisjunction target = logical "∨" variables left right
        | Just (left, right) <- openScopedImplication target = logical "⇒" variables left right
        | Just body <- splitScopedNegation target = ConsequenceUnary "¬" <$> proposition variables body
        | Just (TySet, body) <- openScopedForall target = quantifiedProposition "∀" variables body
        | Just (TySet, body) <- openScopedExists target = quantifiedProposition "∃" variables body
        | otherwise = term variables (scopedCoreTerm target)
    logical symbol variables left right =
        ConsequenceBinary symbol <$> proposition variables left <*> proposition variables right
    quantifiedProposition symbol variables body =
        let variable = freshVariable variables
        in ConsequenceQuantified symbol variable <$> proposition (variable : variables) body
    term variables = \case
        COpaqueInteger value -> Right (ConsequenceInteger value)
        CApp (CApp (CIntrinsic Sep) domain) (CLam TySet body) -> do
            let variable = freshVariable variables
            ConsequenceSeparation variable <$> term variables domain <*> term (variable:variables) body
        CBound index -> ConsequenceVariable <$> require "unbound consequence variable" (at index variables)
        CEq _ left right -> binary "=" variables left right
        CAnd left right -> binary "∧" variables left right
        COr left right -> binary "∨" variables left right
        CImp left right -> binary "⇒" variables left right
        CNot body -> ConsequenceUnary "¬" <$> term variables body
        CForall TySet body -> quantified "∀" variables body
        CExists TySet body -> quantified "∃" variables body
        CTruth -> Right (ConsequenceTruth True)
        CFalsum -> Right (ConsequenceTruth False)
        expression -> case canonicalApplicationSpine expression of
            (CGlobal identity, arguments) -> do
                values <- traverse (term variables) arguments
                case (Map.lookup identity structures, Map.lookup identity fields, values) of
                    (Just phrase, _, subject : parameters) -> Right (ConsequenceStructure phrase subject parameters)
                    (_, Just field, [subject]) -> Right (ConsequenceField field subject)
                    _ -> do
                        (key, marker) <- require "admitted consequence has no notation binding" (Map.lookup identity globals)
                        pure (ConsequenceGlobal key marker values)
            (CIntrinsic intrinsic, arguments) -> ConsequenceIntrinsic intrinsic <$> traverse (term variables) arguments
            _ -> Left ("record consequence uses an unsupported term: " <> Text.pack (take 160 (show expression)))
    binary symbol variables left right = ConsequenceBinary symbol <$> term variables left <*> term variables right
    quantified symbol variables body =
        let variable = freshVariable variables
        in ConsequenceQuantified symbol variable <$> term (variable : variables) body
    freshVariable variables = choose (length variables + 1)
      where
        choose n = let variable = Raw.NamedVar ("z" <> Text.pack (show n))
                   in if variable `elem` variables then choose (n + 1) else variable
    at 0 (value : _) = Just value
    at n (_ : rest) = at (n - 1) rest
    at _ [] = Nothing
    require message = maybe (Left message) Right
