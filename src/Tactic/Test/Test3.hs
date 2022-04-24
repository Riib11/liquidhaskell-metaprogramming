{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}

module Tactic.Test.Test3 where

import Data.Map
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@
data N = Z | S N
@-}
data N = Z | S N

{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (S m) n = S (add m n)

return []

{-@
test1 :: x:N -> {add x x == add x x}
@-}
[tactic|
test1 :: N -> Proof 
test1 x = 
    auto [add] 2
|]

{-@
test2 :: x:N -> y:N -> {add x y == add x y}
@-}
[tactic|
test2 :: N -> N -> Proof 
test2 x y =
    auto [add] 2
|]