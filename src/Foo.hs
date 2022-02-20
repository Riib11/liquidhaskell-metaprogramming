{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Foo where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
-- import TH
-- import Tactic.Repeat
import Tactic.Auto

lem1 :: Int -> Proof
lem1 _ = undefined

lem2 :: Int -> Proof
lem2 _ = undefined

test_auto :: Proof
test_auto =
  $$( tactic_auto
        [ AutoBranch [||lem1||] [[||i||] | i <- [1 .. 10]],
          AutoBranch [||lem2||] [[||i||] | i <- [1 .. 10]]
        ]
    )

testQ :: [Code Q Bool]
testQ = applications [||not||] [[||True||], [||False||]]

-- {-@ measure r :: Int -> Bool @-}

-- {-@ assume lem :: x:{Int | r x} -> {r (x + 1)} @-}
-- lem :: Int -> Proof
-- lem _ = ()

-- {-@ fail test_fail @-}
-- {-@
-- test_fail :: x:{Int | r x} -> {r (x + 10)}
-- @-}
-- test_fail :: Int -> Proof
-- test_fail x = trivial `with` [lem (x + i) | i <- [0 .. 9]]

-- -- ! why does this cause 20,251 constraints to be checked?!?!?!?!?!?
-- {-@
-- test_verbose :: x:{Int | r x} -> {r (x + 10)}
-- @-}
-- test_verbose :: Int -> Proof
-- test_verbose x =
--   lem x `with` lem (x + 1)
--     `with` lem (x + 2)
--     `with` lem (x + 3)
--     `with` lem (x + 4)
--     `with` lem (x + 5)
--     `with` lem (x + 6)
--     `with` lem (x + 7)
--     `with` lem (x + 8)
--     `with` lem (x + 9)

-- -- ! why does this cause 23,084 constraints to be checked?!?!?!?!?!?
-- {-@
-- test_tactic_map :: x:{Int | r x} -> {r (x + 10)}
-- @-}
-- test_tactic_map :: Int -> Proof
-- test_tactic_map x =
--   $(tactic_map [|lem|] ([[|x + i|] | i <- ([0 .. 9] :: [Int])]))

-- import qualified DSL.Equivalence as EQ
-- import Proof

-- {-@
-- reflexivity :: x:a -> {x = x}
-- @-}
-- reflexivity :: a -> Proof
-- reflexivity _ = ()

-- {-@
-- symmetry :: x:a -> y:{a | x = y} -> {y = x}
-- @-}
-- symmetry :: a -> a -> Proof
-- symmetry _ _ = ()

-- {-@
-- transitivity :: x:a -> y:{a | x = y} -> z:{a | y = z} -> {x = z}
-- @-}
-- transitivity :: a -> a -> a -> Proof
-- transitivity _ _ _ = ()

-- equiv :: EQ.Equivalence
-- equiv =
--   EQ.Equivalence
--     { EQ.relationExp = [|(==)|],
--       EQ.reflexivityExp = [|reflexivity|],
--       EQ.symmetryExp = [|symmetry|],
--       EQ.transitivityExp = [|transitivity|]
--     }
