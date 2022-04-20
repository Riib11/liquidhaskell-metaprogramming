{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Quote where

import Control.Monad.Trans.State
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax
import Debug
import Parse
import Splice
import Syntax

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
  debugM $ "====================================="
  debugM $ "instrs: " ++ show instrs
  debugM $ "env: " ++ show env
  decs <- evalStateT (spliceDec instrs) env
  pure decs
