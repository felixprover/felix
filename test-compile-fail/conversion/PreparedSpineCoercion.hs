module PreparedSpineCoercion where
import Data.Coerce (coerce)
import Felix.Checking.Kernel.Conversion (PreparedSpine)
newtype Renamed = Renamed Int
forge :: PreparedSpine Int -> PreparedSpine Renamed
forge = coerce
