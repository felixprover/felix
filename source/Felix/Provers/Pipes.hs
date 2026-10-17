{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}

-- | Explicit ownership of the POSIX pipes passed to Vampire. This is the
-- only prover module depending on GHC's version-specific handle construction.
module Felix.Provers.Pipes (withVampirePipes) where

import Base
import Control.Exception qualified as Exception
import GHC.IO.Device (IODeviceType(Stream))
import GHC.IO.FD qualified as FD
import GHC.IO.Handle.Internals (mkFileHandleNoFinalizer)
import System.IO (IOMode(ReadMode, WriteMode), noNewlineTranslation)
import System.Posix.IO qualified as Posix
import System.Posix.Types (Fd)
import System.Process (ProcessHandle)
#if defined(darwin_HOST_OS) || defined(linux_HOST_OS)
import Foreign (Ptr, alloca, nullPtr, peek, withArray0, withMany)
import Foreign.C.Error (Errno(..), errnoToIOError)
import Foreign.C.String (CString, withCString)
import Foreign.C.Types (CInt(..))
import System.Posix.Internals (withFilePath)
import System.Posix.Types (CPid(..))
import System.Process.Internals (mkProcessHandle)
#endif
#if defined(linux_HOST_OS)
import Foreign.C.Error (eNOSYS)
#endif
#if !defined(darwin_HOST_OS)
import System.Process (CreateProcess(..), StdStream(UseHandle), createProcess_, proc)
#endif

-- Preallocate both ends of every pipe. process-1.6.26.1 constructs CreatePipe
-- handles after launching the child, and its withCreateProcess cleanup forks a
-- detached reaper. Neither boundary provides this supervisor's ownership law.
-- Closing unrelated descriptors on launch prevents parallel requests from
-- inheriting pipes during the short interval before CloseOnExec is set.
withVampirePipes
    :: (Handle -> Handle -> Handle -> Handle -> Handle -> Handle
        -> (FilePath -> [String] -> IO ProcessHandle) -> IO value)
    -> IO value
withVampirePipes action =
    withPipe False \(childInput, input) ->
        withPipe True \(output, childOutput) ->
            withPipe True \(err, childError) ->
                action (snd input) (snd output) (snd err)
                    (snd childInput) (snd childOutput) (snd childError)
                    (spawn childInput childOutput childError)
  where
    withPipe readerNonblocking = Exception.bracket (acquire readerNonblocking) close
    close (reader, writer) = hClose (snd reader) `Exception.finally` hClose (snd writer)
    acquire readerNonblocking = Exception.mask_ do
        (readFd, writeFd) <- Posix.createPipe
        reader <- pipeHandle ReadMode readerNonblocking readFd
            `Exception.onException` Posix.closeFd writeFd
        writer <- pipeHandle WriteMode (not readerNonblocking) writeFd
            `Exception.onException` hClose (snd reader)
        pure (reader, writer)

-- A host may have closed its standard descriptors. Move pipe ends above them
-- before passing UseHandle: dup2(fd,fd) would otherwise preserve CloseOnExec.
-- This operation consumes its descriptor on both success and failure.
pipeHandle :: IOMode -> Bool -> Fd -> IO (Fd, Handle)
pipeHandle mode nonblocking original
    | original > 2 = convert original `Exception.onException` Posix.closeFd original
    | otherwise = do
        moved <- duplicateAboveStdio original
            `Exception.onException` Posix.closeFd original
        Exception.bracketOnError (pure moved) Posix.closeFd \fd -> do
            Posix.closeFd original
            convert fd
  where
    convert fd = do
        Posix.setFdOption fd Posix.CloseOnExec True
        -- Parent ends are nonblocking for the RTS; child ends must be blocking
        -- for ordinary executables (process's UseHandle also enforces this).
        -- Explicit ownership closes every handle. A redundant GC
        -- finalizer retains closed handles and their last-decode buffers until
        -- it runs, materially increasing the live heap for short requests.
        (device, _) <- FD.mkFD (fromIntegral fd) mode
            (Just (Stream, 0, 0)) False False
        configured <- FD.setNonBlockingMode device nonblocking
        handle <- mkFileHandleNoFinalizer configured "<Vampire pipe>" mode Nothing noNewlineTranslation
        pure (fd, handle)

duplicateAboveStdio :: Fd -> IO Fd
duplicateAboveStdio original = do
    copy <- Posix.dup original
    if copy > 2 then pure copy else do
        moved <- duplicateAboveStdio original `Exception.onException` Posix.closeFd copy
        Posix.closeFd copy `Exception.onException` Posix.closeFd moved
        pure moved

-- Called masked by the supervisor: transfer the child directly into its existing
-- process-group/reaper ownership. No parent handles are closed during launch.
spawn :: (Fd, Handle) -> (Fd, Handle) -> (Fd, Handle)
    -> FilePath -> [String] -> IO ProcessHandle
#if defined(darwin_HOST_OS) || defined(linux_HOST_OS)
spawn input output err executable arguments =
    withFilePath executable \path -> withMany withCString arguments \strings ->
        withArray0 nullPtr (path : strings) \argv -> alloca \pid -> do
            status <- spawnVampire argv (fromIntegral (fst input)) (fromIntegral (fst output))
                (fromIntegral (fst err)) pid
            case Errno status of
                Errno 0 -> peek pid >>= \child -> mkProcessHandle child False
#if defined(linux_HOST_OS)
                failure | failure == eNOSYS ->
                    spawnWithProcess input output err executable arguments
#endif
                failure -> ioError (errnoToIOError "Vampire: posix_spawnp" failure
                    Nothing (Just executable))

-- A safe, non-interruptible FFI call lets other Haskell threads run while
-- preserving masked acquisition of the child PID.
foreign import ccall safe "felix_spawn_vampire"
    spawnVampire :: Ptr CString -> CInt -> CInt -> CInt -> Ptr CPid -> IO CInt
#else
spawn = spawnWithProcess
#endif

#if !defined(darwin_HOST_OS)
spawnWithProcess :: (Fd, Handle) -> (Fd, Handle) -> (Fd, Handle)
    -> FilePath -> [String] -> IO ProcessHandle
spawnWithProcess (_, input) (_, output) (_, err) executable arguments = do
    (_, _, _, child) <- createProcess_ "Vampire" (proc executable arguments)
        { std_in = UseHandle input, std_out = UseHandle output, std_err = UseHandle err
        , create_group = True, close_fds = True }
    pure child
#endif
