{-# LANGUAGE BlockArguments #-}

module Debug where

{-@ LIQUID "--compile-spec" @-}

import Control.Monad
import System.IO.Unsafe (unsafePerformIO)

__DEBUG = False

debug :: String -> ()
debug msg =
  unsafePerformIO do
    when __DEBUG $ putStrLn $ "[#] " ++ msg

debugs :: [String] -> ()
debugs msgs =
  unsafePerformIO $
    when __DEBUG do
      putStrLn "[#] {"
      void (traverse putStrLn msgs)
      putStrLn "[#] }"

debugM :: Monad m => String -> m ()
debugM msg =
  when __DEBUG $
    return $! unsafePerformIO do
      putStrLn $ "[#] " ++ msg

debugsM :: Monad m => [String] -> m ()
debugsM msgs =
  return $! unsafePerformIO $
    when __DEBUG do
      putStrLn "[#] {"
      void (traverse putStrLn msgs)
      putStrLn "[#] }"
