{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | The sealed local inputs for the final-prelude structural declaration.
module Felix.Checking.Structure.Builtin
    ( BuiltinStructureManifest
    , builtinStructureManifest
    , builtinStructureInputs
    , builtinRecordPhrase
    , builtinOnesortedPhrase
    , builtinRecordId
    , builtinOnesortedId
    , builtinCarrierFieldId
    , checkBuiltinStructureSchemas
    ) where

import Base
import Felix.Checking.Identity
import Felix.Checking.Record qualified as Record
import Felix.Checking.Structure.Schema
import Felix.Module
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Felix.Syntax.Lexicon qualified as Lexicon
import Control.Monad (unless)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

-- The declaration ordinal is the existing final-prelude base declaration;
-- adding a structure slot does not allocate another declaration or field slot.
newtype BuiltinStructureManifest = BuiltinStructureManifest LocalDeclarationOrdinal
    deriving stock (Show, Eq)

builtinStructureManifest :: LocalDeclarationOrdinal -> BuiltinStructureManifest
builtinStructureManifest = BuiltinStructureManifest

builtinRecordPhrase :: StructurePhrase
builtinRecordPhrase = structurePhrase Lexicon._Record

builtinOnesortedPhrase :: StructurePhrase
builtinOnesortedPhrase = structurePhrase Lexicon._Onesorted

builtinOrigin :: BuiltinStructureManifest -> StructureSlot -> StructureOrigin
builtinOrigin (BuiltinStructureManifest declaration) = StructureOrigin preludeModuleName declaration

builtinRecordId :: BuiltinStructureManifest -> StructureId
builtinRecordId manifest = structureId (builtinOrigin manifest (structureSlot 0))

builtinOnesortedId :: BuiltinStructureManifest -> StructureId
builtinOnesortedId manifest = structureId (builtinOrigin manifest (structureSlot 1))

builtinCarrierFieldId :: BuiltinStructureManifest -> FieldId
builtinCarrierFieldId (BuiltinStructureManifest declaration) =
    fieldId preludeModuleName declaration (structureFieldSlot 0)

builtinStructureInputs
    :: CheckedObjectClosure -> BuiltinStructureManifest
    -> Either LocalStructureSchemaError (NonEmpty LocalStructureSchema)
builtinStructureInputs closure manifest = do
    root <- checkManifestLocalStructureSchema closure (builtinOrigin manifest (structureSlot 0))
        GeneralRecordRoot rootWire (manifestPresentation builtinRecordPhrase rootWire)
    onesorted <- checkManifestLocalStructureSchema closure (builtinOrigin manifest (structureSlot 1))
        OrdinaryStructure onesortedWire (manifestPresentation builtinOnesortedPhrase onesortedWire)
    pure (root :| [onesorted])
  where
    rootWire = LocalStructureSchemaWire (structureSlot 0) [] [] [] [] []
    onesortedWire = LocalStructureSchemaWire (structureSlot 1) [] []
        [structureApplicationKey (builtinRecordId manifest) []]
        [LocalStructureFieldWire (structureFieldSlot 0) Raw.CarrierSymbol Nothing] []

manifestPresentation :: StructurePhrase -> LocalStructureSchemaWire -> StructurePresentation
manifestPresentation phrase input = StructurePresentation phrase Nowhere []
    ((Nothing, Nowhere) <$ localWireParents input) Map.empty
    (Map.fromList [(slot, (Nothing, Nowhere)) | LocalStructureFieldWire slot _ _ <- localWireFields input])
    Map.empty

-- Checked interfaces already establish predicate and theorem completeness.
-- Here the normalized inputs must be precisely the two reserved definitions.
checkBuiltinStructureSchemas
    :: BuiltinStructureManifest -> NonEmpty ResolvedStructureSchema -> Either Text ()
checkBuiltinStructureSchemas manifest schemas = do
    unless (length schemas == 2 && Map.keysSet indexed == Set.fromList [rootId, onesortedId])
        (Left "the built-in manifest must contain exactly record and onesorted structure")
    root <- require rootId
    onesorted <- require onesortedId
    unless (resolvedSchemaRole root == GeneralRecordRoot
            && resolvedSchemaPhrase root == builtinRecordPhrase
            && resolvedSchemaRoot root == rootId
            && null (resolvedSchemaParameters root)
            && null (resolvedSchemaDirectParents root)
            && null (resolvedSchemaAncestors root)
            && null (resolvedSchemaFields root)
            && null (resolvedSchemaRequirements root))
        (Left "the built-in record root differs from the sealed manifest")
    unless (resolvedSchemaRole onesorted == OrdinaryStructure
            && resolvedSchemaPhrase onesorted == builtinOnesortedPhrase
            && resolvedSchemaRoot onesorted == rootId
            && null (resolvedSchemaParameters onesorted)
            && resolvedSchemaDirectParents onesorted == Set.singleton parent
            && resolvedSchemaAncestors onesorted == Set.singleton parent
            && null (resolvedSchemaRequirements onesorted))
        (Left "the built-in onesorted structure differs from the sealed manifest")
    case Map.elems (resolvedSchemaFields onesorted) of
        [field] -> unless
            (resolvedFieldIdentity field == carrier
                && resolvedFieldOwner field == onesortedId
                && resolvedFieldSlot field == structureFieldSlot 0
                && resolvedFieldSymbol field == Raw.CarrierSymbol
                && resolvedFieldSelector field == Record.fieldSelectorObjectId (resolvedSchemaTheory onesorted) carrier
                && resolvedFieldProjection field == Record.fieldProjectionObjectId (resolvedSchemaTheory onesorted) carrier)
            (Left "the built-in carrier is not the canonical field")
        _ -> Left "the built-in onesorted structure must have exactly its carrier field"
  where
    indexed = Map.fromList [(resolvedSchemaId schema, schema) | schema <- toList schemas]
    rootId = builtinRecordId manifest
    onesortedId = builtinOnesortedId manifest
    carrier = builtinCarrierFieldId manifest
    parent = structureApplicationKey rootId []
    require identity = maybe (Left "the built-in manifest is incomplete") Right (Map.lookup identity indexed)
