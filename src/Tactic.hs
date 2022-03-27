{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

data CoreDSL

-- data Tactic
--   = forall a. Expr (Code Q a)
--   | Branches [Code Q Bool] Tactic
--   | forall a. Applications (Code Q (a -> Proof)) [Code Q a] Tactic
--   | Contradictions

-- runTactic :: Tactic -> Code Q Proof
-- runTactic (Expr a) = [||$$a `by` trivial||]
-- runTactic (Branches conds tactic) = branch conds (runTactic tactic)
--   where
--     branch :: [Code Q Bool] -> Code Q a -> Code Q a
--     branch [] a = a
--     branch (qcond : qconds) a = [||if $$qcond then $$(branch qconds a) else $$(branch qconds a)||]
-- runTactic (Applications lem hyps tactic) = _
--   where
--     apply :: Code Q (a -> b) -> Code Q a -> Code Q b
--     apply qf qa = [||$$qf $$qa||]

--     applications :: Code Q (a -> b) -> [Code Q a] -> [Code Q b]
--     applications qf qas = fmap (apply qf) qas

combineProofs :: [Code Q Proof] -> Code Q Proof
combineProofs [] = [||trivial||]
combineProofs (p : ps) = [||$$p `by` $$(combineProofs ps)||]
