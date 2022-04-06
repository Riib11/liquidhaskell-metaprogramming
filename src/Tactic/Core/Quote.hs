{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Quote where

import Control.Monad.Trans.State
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax
import System.IO.Unsafe (unsafePerformIO)
import Tactic.Core.Parse
import Tactic.Core.Splice
import Tactic.Core.Syntax

tactic :: Quote.QuasiQuoter
tactic =
  Quote.QuasiQuoter
    { Quote.quoteExp = quoteExp,
      Quote.quoteDec = quoteDec,
      Quote.quotePat = error "cannot quote a pattern with tactic quasiquoter",
      Quote.quoteType = error "cannot quote a type with tactic quasiquoter"
    }

quoteExp :: String -> Q Exp
quoteExp str = do
  instrs <- runParser parseInstrs str
  evalStateT (spliceExp instrs) emptyEnvironment

quoteDec :: String -> Q [Dec]
quoteDec str = do
  (env, instrs) <- runParser parseDecInstrs str
  return $! unsafePerformIO $ putStrLn $ "instrs: " ++ show instrs
  return $! unsafePerformIO $ putStrLn $ "env: " ++ show env
  decs <- evalStateT (spliceDec instrs) env
  return $! unsafePerformIO $ putStrLn $ "====================================="
  pure decs
