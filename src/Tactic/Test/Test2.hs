{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Test.Test2 where

import Data.Map
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@
data N = Z | S N
@-}
data N = Z | S N

{-@ measure prop1 :: N -> Bool @-}

{-@ assume lem_prop1 :: x:N -> {prop1 x} @-}
lem_prop1 :: N -> Proof
lem_prop1 x = trivial

{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (S m) n = S (add m n)

{-@
assume assume_add_comm :: x:N -> y:N -> {add x y == add y x}
@-}
assume_add_comm :: N -> N -> Proof 
assume_add_comm _ _ = trivial

{-@ measure prop2 :: N -> Bool @-}

{-@ assume lem_prop2_Z :: {prop2 Z} @-}
lem_prop2_Z :: Proof
lem_prop2_Z = trivial

{-@ assume lem_prop2_S :: x:N -> {prop2 x => prop2 (S x)} @-}
lem_prop2_S :: N -> Proof 
lem_prop2_S _ = trivial

return []

-- -- * pass
-- {-@
-- test1 :: x:N -> {prop1 x}
-- @-}
-- [tactic|
-- test1 :: N -> Proof 
-- test1 x = 
--     auto [lem_prop1] 2
-- |]

-- -- * pass
-- {-@
-- test2 :: x:N -> y:N -> {add x y == add y x}
-- @-}
-- [tactic|
-- test2 :: N -> N -> Proof 
-- test2 x y = 
--   auto [assume_add_comm] 2
-- |]

-- -- * pass
-- {-@
-- test3 :: x:N -> {prop2 x}
-- @-}
-- [tactic|
-- test3 :: N -> Proof
-- test3 x = 
--   induct x;
--   auto [lem_prop2_Z, lem_prop2_S] 2
-- |]
