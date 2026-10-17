module Felix.Test.Temp (withTemporaryDirectory) where


import Base

import System.Directory qualified as Directory
import System.IO.Temp qualified as Temp


-- | Supply the canonical host spelling of a fresh system temporary directory.
-- Tests that exercise filesystem identity can therefore compare exact paths
-- without depending on platform aliases such as macOS's /var symlink.
withTemporaryDirectory :: String -> (FilePath -> IO a) -> IO a
withTemporaryDirectory template action =
    Temp.withSystemTempDirectory template \directory ->
        Directory.canonicalizePath directory >>= action
