module Main where

import Debug
import Building
import File
import InlineTactic
import System.Process as Process


main = do
  -- consoleIO "cleaning..."
  -- clean
  -- consoleIO "building..."
  -- mb_result <- build (defaultOptions_build {ddump_splices = True, capture_std_err = True})
  -- consoleIO $ "mb_result: " ++ show mb_result
  -- return ()
  filePath <- toGlobalFilePath "src/Tactic/Test/Test4.hs"
  inlineTactics filePath
