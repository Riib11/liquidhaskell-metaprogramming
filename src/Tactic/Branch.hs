{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Branch where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

-- explores all possible branches for boolean expressions.
tactic_branch :: [Code Q Bool] -> Code Q a -> Code Q a
tactic_branch [] a = a
tactic_branch (qcond : qconds) a = [||if $$qcond then $$(tactic_branch qconds a) else $$(tactic_branch qconds a)||]
