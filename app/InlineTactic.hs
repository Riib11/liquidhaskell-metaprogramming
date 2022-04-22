{-# LANGUAGE BlockArguments #-}

{-@ LIQUID "--compile-spec" @-}

module InlineTactic where

import Building
import Control.Monad as Monad
import Data.Char as Char
import Data.List as List
import Data.Maybe as Maybe
import Debug
import File
import Parsing
import System.IO as IO
import System.Process as Process

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

-- returns filepath where tacticSplices are inlined
inlineTactics :: FilePath -> IO FilePath
inlineTactics filePath = do
  str_file <- readFile filePath
  consoleIO $ "inlining tactic splices in file: " ++ filePath
  let ls_file = lines str_file

  -- -- why the fuck does this hand when I set std_err to CreatePipe?? maybe try is by stack run or something??
  -- mb_hdl_err <- do
  --   -- _ <- do
  --   (_, _, mb_hdl_err, ph_build) <-
  --     createProcess $
  --       (shell "stack build --ghc-options \"-ddump-splices -fplugin-opt=LiquidHaskell:--compile-spec\"")
  --         { -- std_out = CreatePipe,
  --           std_err = CreatePipe
  --         }
  --   -- waitForProcess ph_build -- ? causes hang if std_err = CreatePipe
  --   return mb_hdl_err
  -- str_err <- hGetContents (fromJust mb_hdl_err)
  clean -- required when using `stack run`, since that builds first
  
  Just str_err <- build $ defaultOptions_build {ddump_splices = True, capture_std_err = True}
  debugIO "===[ str_err ]==="
  debugIO str_err

  let ls_err = lines str_err
  let tacticSplices = extractTacticSplices ls_err

  -- replace appropriate lineranges in str_file with tacticSplices
  let ls'_file =
        inlineTacticSplices
          (filter ((filePath ==) . filePath_TS) tacticSplices)
          ls_file

  debugIO $ unlines $ "==================== ls'_file" : ls'_file

  -- -- all version are stored in <filePath>.tactic/
  -- let tacticFilePath = filePath ++ ".tactic/"
  -- -- create tacticFilePath if it doesn't exist
  -- -- system $ "if [ -d "++ tacticFilePath ++ " ]; then; else mkdir " ++ tacticFilePath ++ "; fi"
  -- system $ "mkdir " ++ tacticFilePath
  -- -- get the number of versions already in .tactic
  -- n <- length . lines <$> readProcess "ls" [tacticFilePath] ""
  -- -- new version will be at <filePath>.tactic/<n>.hs
  -- let filePath' = tacticFilePath ++ show n ++ ".hs"
  -- system $ "mv " ++ filePath ++ " " ++ filePath'
  -- consoleIO $ "created cache of current version at: " ++ filePath'

  -- all version are stored in <filePath>.tactic/
  let tacticFilePath = filePath ++ ".tactic/"
  -- create tacticFilePath if it doesn't exist
  mkdir tacticFilePath
  -- get the number of versions already in .tactic
  n <- getDirSize tacticFilePath
  -- new version will be at <filePath>.tactic/<n>.hs
  let filePath' = tacticFilePath ++ show n ++ ".hs"
  mv filePath filePath'
  consoleIO $ "created cache of current version at: " ++ filePath'

  -- write new version of file
  writeFile filePath (unlines ls'_file)
  consoleIO $ "wrote inlined splices in file: " ++ filePath

  -- filePath that new version (with inlined tacticSplices) was written to
  return filePath'

data TacticSplice = TacticSplice
  { filePath_TS :: FilePath,
    lineRange_TS :: LineRange,
    name_TS :: String,
    lines_TS :: [String]
  }
  deriving (Eq, Show)

-- extracts tacticSplices in the form (filePath, lineRange, ls)
extractTacticSplices :: [String] -> [TacticSplice]
extractTacticSplices [] = []
extractTacticSplices (l : ls) =
  if "Splicing declarations" `isSuffixOf` l
    then case extractTacticSplice (l : ls) of
      Just (tacticSplice, ls') -> tacticSplice : extractTacticSplices ls'
      Nothing -> extractTacticSplices ls
    else extractTacticSplices ls

-- extracts the next splice of the form (filePath, lineRange, ls), along with the rest of the lines after
-- Nothng if splice is `return []`
extractTacticSplice :: [String] -> Maybe (TacticSplice, [String])
extractTacticSplice (l1 : ls1) =
  if case ls1 of (l : _) -> l == "    return [] ======>"; [] -> False
    then Nothing
    else
      let -- extract (filePath, lineRange) from first line
          Just (filePath, l2) = splitAtSuffix ".hs" l1
          lineRange = extractTacticLineRange l2

          -- ignore lines until (and including) "======>"
          ls2 = tail' $ dropWhile (not . isSuffixOf "======>") ls1

          -- capture lines after "======>"
          -- and before next line that isn't part of the splice
          (ls, ls3) =
            case findIndex (\l -> isTHMessage l || isLHMessage l || isBuildMessage l) ls2 of
              Just i -> splitAt i ls2
              Nothing -> (ls2, [])

          -- unindent
          ls' = case ls of
            [] -> error "empty splice??"
            l : ls ->
              let indent = takeWhile isSpace l
               in map
                    ( \l -> case stripPrefix indent l of
                        Just l' -> l'
                        Nothing -> l
                    )
                    (l : ls)

          name = takeWhile (not . isSpace) (head ls')
       in Just
            ( TacticSplice
                { filePath_TS = filePath,
                  lineRange_TS = lineRange,
                  name_TS = name,
                  lines_TS = ls'
                },
              ls3
            )

type LineRange = (Int, Int)

getStartLine = fst :: LineRange -> Int

getEndLine = snd :: LineRange -> Int

-- replace each tacticSplice with corresponding lines simultaneously
inlineTacticSplices :: [TacticSplice] -> [String] -> [String]
inlineTacticSplices tacticSplices ls =
  let -- split by tacticSplices of tacticSplices
      groups = splitByTacticSpliceLineRanges tacticSplices ls

      -- replace each group
      groups' =
        ( \(mb_tacticSplice, ls_group) ->
            case mb_tacticSplice of
              -- replace
              Just tacticSplice ->
                concat
                  [ ["-- %tactic:begin:" ++ name_TS tacticSplice],
                    lines_TS tacticSplice,
                    ["-- %tactic:end:" ++ name_TS tacticSplice]
                  ]
              -- don't replace
              Nothing -> ls_group
        )
          <$> groups
   in -- recombine
      concat groups'

-- split lines into groups where each group is designated by the beginning or end of a lineRange
splitByTacticSpliceLineRanges :: [TacticSplice] -> [String] -> [(Maybe TacticSplice, [String])]
splitByTacticSpliceLineRanges tacticSplices = go 1 Nothing []
  where
    go :: Int -> Maybe TacticSplice -> [a] -> [a] -> [(Maybe TacticSplice, [a])]
    go i mb_tacticSplice acc [] = [(mb_tacticSplice, reverse acc)]
    go i mb_tacticSplice acc (l : ls) =
      case mb_tacticSplice of
        Just tacticSplice ->
          if i == getEndLine (lineRange_TS tacticSplice)
            then -- end of this tacticSplice
              (Just tacticSplice, reverse acc) : go (i + 1) Nothing [] ls
            else -- still in this tacticSplice
              go (i + 1) (Just tacticSplice) (l : acc) ls
        Nothing ->
          case find ((i ==) . getStartLine . lineRange_TS) tacticSplices of
            -- start of new multiline tacticSplice
            Just tacticSplice ->
              (Nothing, reverse acc) : go (i + 1) (Just tacticSplice) [l] ls
            -- still outside all tacticSplices
            Nothing -> go (i + 1) Nothing (l : acc) ls

extractTacticLineRange :: String -> LineRange
extractTacticLineRange l1 =
  let Just l2 = stripPrefix ":" l1
   in if "(" `isPrefixOf` l2
        then -- multiline, of form "(n,n)-(n,n):"

          let Just (l3, _) = splitAtPrefix ":" l2
              [n1_str, _, n2_str, _] = splitBys "(,)-" l3
           in (read n1_str :: Int, read n2_str :: Int)
        else -- singleline, of form "n:n-n:"

          let n_str = takeWhile isDigit l2
           in (read n_str :: Int, read n_str :: Int)
