{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_haskell_structures (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/bin"
libdir     = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/lib/x86_64-osx-ghc-8.10.3/haskell-structures-0.1-2eH5H4JsaNDAly6ThMU14K"
dynlibdir  = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/lib/x86_64-osx-ghc-8.10.3"
datadir    = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/share/x86_64-osx-ghc-8.10.3/haskell-structures-0.1"
libexecdir = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/libexec/x86_64-osx-ghc-8.10.3/haskell-structures-0.1"
sysconfdir = "/Users/lucastornai/Documents/uni/pgc-ufabc/haskell-structures/.stack-work/install/x86_64-osx/20ad00536f4a3e0dba6752550b2d08421ccf6d58554b1ff58a840a2681cc409e/8.10.3/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "haskell_structures_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "haskell_structures_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "haskell_structures_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "haskell_structures_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "haskell_structures_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "haskell_structures_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
