{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Quote where

import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax
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
quoteExp str =
  case parseExpInstrs str of
    Right instrs -> spliceExp emptyEnvironment instrs
    Left msg -> fail msg

quoteDec :: String -> Q [Dec]
quoteDec str =
  case parseDecInstrs str of
    Right (env, instrs) -> spliceDec env instrs
    Left msg -> fail msg
