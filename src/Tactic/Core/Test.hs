{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Core.Test where

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

{-@ automatic-instances add_m_Sn @-}
{-@
add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
-- TODO: why does this work when I paste the the dumped splices, but it doesn't work when I use the tactic macro here???
[tactic|
add_m_Sn :: N -> N -> Proof
add_m_Sn m n =
  induct m;
  auto [Z, S, add] 2
|]

-- add_m_Sn :: N -> N -> Proof
-- add_m_Sn = \m n ->
--   case m of
--     Z -> trivial
--     S m -> add_m_Sn m n

-- -- TODO: why does this work when I paste it from the dumped splices, but it doesn't work when I use the tactic macro???
-- add_m_Sn :: N -> N -> Proof
-- add_m_Sn =
--   \m ->
--     \n ->
--       case m of
--         Z ->
--           ( ( use ((add n) n)
--                 &&& ( use ((add n) Z)
--                         &&& ( use ((add Z) n)
--                                 &&& ( use ((add Z) Z)
--                                         &&& (use n &&& (use (S n) &&& (use (S Z) &&& use Z)))
--                                     )
--                             )
--                     )
--             )
--               &&& trivial
--           )
--         S n_a46ks ->
--           ( ( use ((add n) n)
--                 &&& ( use ((add n) n_a46ks)
--                         &&& ( use ((add n) Z)
--                                 &&& ( use ((add n_a46ks) n)
--                                         &&& ( use ((add n_a46ks) n_a46ks)
--                                                 &&& ( use ((add n_a46ks) Z)
--                                                         &&& ( use ((add Z) n)
--                                                                 &&& ( use ((add Z) n_a46ks)
--                                                                         &&& ( use ((add Z) Z)
--                                                                                 &&& ( use n
--                                                                                         &&& ( use n_a46ks
--                                                                                                 &&& ( use (S n)
--                                                                                                         &&& ( use
--                                                                                                                 (S n_a46ks)
--                                                                                                                 &&& ( use
--                                                                                                                         (S Z)
--                                                                                                                         &&& ( use
--                                                                                                                                 Z
--                                                                                                                                 &&& ( use
--                                                                                                                                         ((add_m_Sn n_a46ks) n)
--                                                                                                                                         &&& ( use ((add_m_Sn n_a46ks) n_a46ks)
--                                                                                                                                                 &&& use
--                                                                                                                                                   ((add_m_Sn n_a46ks) Z)
--                                                                                                                                             )
--                                                                                                                                     )
--                                                                                                                             )
--                                                                                                                     )
--                                                                                                             )
--                                                                                                     )
--                                                                                             )
--                                                                                     )
--                                                                             )
--                                                                     )
--                                                             )
--                                                     )
--                                             )
--                                     )
--                             )
--                     )
--             )
--               &&& trivial
--           )
