{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Invocation-local context for a record's single mathematical proof.
-- Nothing here is a premise, registration, or persisted proof identity.
module Felix.Checking.Structure.Obligation
    ( RecordObligation(..)
    , ObligationContext(..)
    , obligationContext
    , renderObligationContext
    ) where

import Base
import Felix.Checking.Core
import Felix.Checking.Identity
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Report.Location
import Felix.Syntax.Abstract qualified as Raw
import Data.Map.Strict qualified as Map
import Data.List qualified as List

data RecordObligation = RecordObligation
    { recordObligationScope :: ![CoreType]
    , recordObligationFormula :: !(CanonicalTerm ObjectId)
    , recordObligationOrigins :: !(Map Schema.RequirementProvenanceKey Schema.RequirementOccurrence)
    , recordObligationResult :: !Location
    , recordObligationFields :: !(Map FieldId (Location, Text))
    }
    deriving stock (Show, Eq)

data ObligationContext = ObligationContext
    { contextIsMatchingRequirement :: !Bool
    , contextRequirements :: ![RecordObligation]
    }
    deriving stock (Show, Eq)

-- Exact comparison only. An intermediate or combined goal is context, never
-- evidence that one particular conjunct caused the failure.
obligationContext :: Maybe (ScopedCheckedCore ObjectId) -> [RecordObligation] -> ObligationContext
obligationContext goal obligations = case List.filter matches obligations of
    [] -> ObligationContext False obligations
    matched -> ObligationContext True matched
  where
    matches requirement = case goal of
        Just target -> scopedCoreContext target == recordObligationScope requirement
            && scopedCoreTerm target == recordObligationFormula requirement
        Nothing -> False

renderObligationContext :: ObligationContext -> [Text]
renderObligationContext (ObligationContext matched obligations) =
    [if matched then "record requirement matching the failed goal:"
        else "applicable record obligations (context, not an isolated failure cause):"
    | not (null obligations)] <> concatMap describe obligations
  where
    describe requirement =
        ["record result at " <> locationToText (recordObligationResult requirement)]
        <> concatMap (origin requirement) (Map.toAscList (recordObligationOrigins requirement))
    origin requirement (key, occurrence) =
        ["schema requirement " <> maybe "(unlabelled)" (\(Raw.Marker marker) -> "`" <> marker <> "`")
            (Schema.requirementOccurrenceMarker occurrence)
            <> " at " <> locationToText (Schema.requirementOccurrenceLocation occurrence)]
        <> case Schema.requirementOrigin key of
            Schema.FieldSpecificationOrigin _ field ->
                maybeToList (related <$> Map.lookup field (recordObligationFields requirement))
            _ -> ("related record context: " <>) . related <$> Map.elems (recordObligationFields requirement)
    related (location, description) = description <> " at " <> locationToText location
