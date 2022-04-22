module Main where

import Debug
import Building
import File
import InlineTactic
import System.Process as Process
import System.Environment as Environment


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
      filePath <- toGlobalFilePath "src/Tactic/Test/Test4.hs"
      inlineTactics filePath
    [] -> error "No arguments! Requires exactly 1 argument, a filePath"
    _ -> error "Too many arguments! Requires exactly 1 argument, a filePath"
