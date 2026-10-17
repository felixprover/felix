module GenericSourceDescriptor where

import Felix.Report.Location (SourceDescriptor)
import GHC.Generics (Generic(..))

reconstruct :: Rep (SourceDescriptor) () -> SourceDescriptor
reconstruct = to
