{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Exact conjunction grouping shared by rule joins and checked witnesses.
module Felix.Checking.Notion.Composite
    ( CompositePremiseTree(..)
    ) where

import Base

data CompositePremiseTree goal
    = CompositePremiseTruth
    | CompositePremiseLeaf !goal
    | CompositePremiseAnd
        !(CompositePremiseTree goal)
        !(CompositePremiseTree goal)
    deriving stock (Show, Eq, Ord, Functor)
