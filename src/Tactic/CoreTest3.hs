{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- {-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.CoreTest3 where

-- import Language.Haskell.TH
-- import Language.Haskell.TH.Datatype
-- import Language.Haskell.TH.Quote
import Data.Map
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core

{-@
data N = Z | S N
@-}
data N = Z | S N

{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (S m) n = S (add m n)

{-@
data ListN = NilN | ConsN N ListN
@-}
data ListN = NilN | ConsN N ListN

return []
