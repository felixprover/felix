module PreparedSpineUpdate where
import Felix.Checking.Kernel.Conversion
replace prepared terminal = prepared { preparedSpineTerminal = terminal }
