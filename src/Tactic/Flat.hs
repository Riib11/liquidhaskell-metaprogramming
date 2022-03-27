{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Flat where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

data FlatBranch = forall a. FlatBranch (Code Q (a -> Proof)) [Code Q a]

tactic_flat :: [FlatBranch] -> Code Q Proof
tactic_flat branches =
  combineProofs
    ( fmap
        ( \(FlatBranch qf qas) ->
            combineProofs (applications qf qas)
        )
        branches
    )

apply :: Code Q (a -> b) -> Code Q a -> Code Q b
apply qf qa = [||$$qf $$qa||]

applications :: Code Q (a -> b) -> [Code Q a] -> [Code Q b]
applications qf qas = fmap (apply qf) qas

-- unTypeCode :: Code m a -> m Exp

combineProofs :: [Code Q Proof] -> Code Q Proof
combineProofs [] = [||trivial||]
combineProofs (p : ps) = [||$$p `by` $$(combineProofs ps)||]

-- ! OLD
-- tactic_contradiction :: p:(a -> Bool) -> x:a -> {p x}
tactic_contradiction :: Q Exp -> Q Exp -> Q Exp
tactic_contradiction qp qx = [|if $qp $qx then trivial else trivial|]

-- -- repeat :: fuel:Int -> x:a -> p:(a -> Bool) -> {p x}
-- repeat :: Int -> Q Exp -> Q Exp -> Q Exp -> Q Exp
-- repeat fuel x p
--   | fuel == 0 = [|trivial|]
--   | fuel > 0 = _
