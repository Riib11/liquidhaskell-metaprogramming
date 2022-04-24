module Main where

{-@ LIQUID "--compile-spec" @-}

import Building
import Debug
import File
import InlineTactic
import System.Environment as Environment
import System.Process as Process

main = do
  -- consoleIO "cleaning..."
  -- clean
  -- consoleIO "building..."
  -- mb_result <- build (defaultOptions_build {ddump_splices = True, capture_std_err = True})
  -- consoleIO $ "mb_result: " ++ show mb_result
  -- return ()

  args <- getArgs
  case args of
    [filePath] -> do
      filePath <- toGlobalFilePath filePath -- "src/Tactic/Test/Test4.hs"
      inlineTactics filePath
    [] -> error "No arguments! Requires exactly 1 argument, a filePath"
    _ -> error "Too many arguments! Requires exactly 1 argument, a filePath"
