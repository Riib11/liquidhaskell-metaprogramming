module Tactic.ReadTH where

{-@ LIQUID "--compile-spec" @-}

import Data.Char as Char
import Data.List as List
import System.IO as IO
import System.Process as Process

{-
Description:

Reads template haskell output.
Requires OPTIONS_GHC "-ddump-splices" for source file.
-}

data SectionTH
  = SectionNormal String -- unspliced, original source code
  | SectionSpliced String -- newly-spliced source code

{-
stack build --ghc-options "-ddump-splices -fplugin-opt=LiquidHaskell:--compile-spec"
-}

readTH :: FilePath -> IO [SectionTH]
readTH filePath = do
  -- str_file <- readFile filePath
  -- putStrLn "===[ str_file ]==="
  -- putStrLn str_file

  do
    (_, _, _, ph) <-
      createProcess $
        (shell "stack clean")
          { std_out = CreatePipe,
            std_err = CreatePipe -- capture std_(out|err)
          }
    waitForProcess ph

  hdl_err <- do
    (_, _, Just hdl_err, ph) <-
      createProcess $
        (shell "stack build --ghc-options \"-ddump-splices -fplugin-opt=LiquidHaskell:--compile-spec\"")
          { std_out = CreatePipe,
            std_err = CreatePipe -- capture std_(out|err)
          }
    waitForProcess ph
    return hdl_err
  str_err <- hGetContents hdl_err
  -- ? DEBUG
  putStrLn "===[ str_err ]==="
  putStrLn str_err

  let lines_err = lines str_err
  let splices = extractSplices lines_err

  

  return []

{- example
/Users/henry/Documents/Research/LiquidHaskell/liquidhaskell-metaprogramming/src/Tactic/Test/Test3.hs:(31,9)-(35,2): Splicing declarations
  Language.Haskell.TH.Quote.quoteDec
    tactic
    "\n\
    \test1 :: N -> Proof \n\
    \test1 x = \n\
    \    auto [add] 2\n"
======>
  test1 :: N -> Proof
  test1 = \ x -> ((use ((add x) x) &&& use x) &&& trivial)
-}

-- extracts splices in the form (filePath, lineNumber, spliceLines)
extractSplices :: [String] -> [(String, Int, [String])]
extractSplices [] = []
extractSplices (l : ls) =
  if "Splicing declarations" `isSuffixOf` l
    then
      let (splice, ls') = extractSplice (l : ls)
       in splice : extractSplices ls'
    else extractSplices ls

-- extracts the next splice of the form (filePath, lineNumber, spliceLines), along with the rest of the lines after
extractSplice :: [String] -> ((String, Int, [String]), [String])
extractSplice (l1 : ls1) =
  let -- extract (filePath, lineNumber) from first line
      Just i_period = findIndex (== '.') l1
      (filePath, l2) = splitAt (i_period + 3) l1
      lineNumber = read (takeWhile (not . flip elem [',', ':']) . dropWhile (flip elem [':', '(']) $ l2) :: Int

      -- ignore lines until (and including) "======>"
      ls2 = tail' $ dropWhile (not . isSuffixOf "======>") ls1

      -- capture lines after "======>"
      -- and before next line that ends with "Splicing declarations" or begins with "****"
      (spliceLines, ls3) =
        case findIndex (\l -> isTHMessage l || isLHMessage l || all isSpace l) ls2 of
          Just i -> splitAt i ls2
          Nothing -> (ls2, [])

      -- unindent
      spliceLines' = case spliceLines of
        [] -> []
        l : ls ->
          let indent = takeWhile isSpace l
           in map (\l -> case stripPrefix indent l of Just l' -> l') (l : ls)
   in ((filePath, lineNumber, spliceLines'), ls3)

isTHMessage :: String -> Bool
isTHMessage l = "Splicing declarations" `isSuffixOf` l

isLHMessage :: String -> Bool
isLHMessage l = "****" `isPrefixOf` l

tail' :: [a] -> [a]
tail' [] = []
tail' (_ : l) = l

main = do
  str_tmp <- readFile "/Users/henry/Documents/Research/LiquidHaskell/liquidhaskell-metaprogramming/tmp2.txt"
  let lines_tmp = lines str_tmp
  let splices = extractSplices lines_tmp
  mapM_
    ( \(filePath, lineNumber, spliceLines) -> do
        putStrLn $ "filePath: " ++ filePath
        putStrLn $ "lineNumber: " ++ show lineNumber
        putStrLn $ "spliceLines: {"
        mapM_ putStrLn spliceLines
        putStrLn $ "}"
    )
    splices
