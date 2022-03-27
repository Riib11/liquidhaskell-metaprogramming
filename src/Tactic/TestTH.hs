{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Tactic.TestTH where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

spliceName :: String -> Q Exp
spliceName = pure . VarE . mkName

handleDec :: Q [Dec] -> Q [Dec]
handleDec _ =
  [d|
    x :: Int
    x = 1
    |]
