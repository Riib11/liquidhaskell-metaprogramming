{-@ LIQUID "--compile-spec" @-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Tactic.Repeat where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

-- tactic: map

tactic_map :: Q Exp -> [Q Exp] -> Q Exp
tactic_map qf qxs = join $ foldM step [|trivial|] qxs
  where
    step :: Q Exp -> Q Exp -> Q (Q Exp)
    step qe qx = return [|$qe `with` $qf $qx|]
