{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Test.Test1 where

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

-- {-@ automatic-instances add_Sm_n @-}
-- {-@
-- add_Sm_n :: m:N -> n:N -> {add (S m) n == S (add m n)}
-- @-}
-- -- TODO: why does this work when I paste the the dumped splices, but it doesn't work when I use the tactic macro here???
-- [tactic|
-- add_Sm_n :: N -> N -> Proof
-- add_Sm_n m n =
--   induct m;
--   auto [Z, S, add] 1
-- | ]

-- -- ! FAIL
-- {-@ automatic-instances add_m_Sn @-}
-- {-@
-- add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
-- @-}
-- -- TODO: why does this work when I paste the the dumped splices, but it doesn't work when I use the tactic macro here???
-- [tactic|
-- add_m_Sn :: N -> N -> Proof
-- add_m_Sn m n =
--   induct m;
--   auto [Z, S] 3

-- | ]

{-@ automatic-instances add_m_Sn @-}
{-@ add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)} @-}
add_m_Sn :: N -> N -> Proof
add_m_Sn = \m -> \n ->
  case m of
    Z -> ((use n &&& (use (S n) &&& (use (S (S n)) &&& (use (S (S Z)) &&& (use (S Z) &&& use Z))))) &&& trivial)
    S n_a7bk7 -> ((use n &&& (use n_a7bk7 &&& (use (S n) &&& (use (S n_a7bk7) &&& (use (S (S n)) &&& (use (S (S n_a7bk7)) &&& (use (S (S Z)) &&& (use (S Z) &&& (use Z &&& (use ((add_m_Sn n_a7bk7) n) &&& (use ((add_m_Sn n_a7bk7) n_a7bk7) &&& (use ((add_m_Sn n_a7bk7) (S n)) &&& (use ((add_m_Sn n_a7bk7) (S n_a7bk7)) &&& (use ((add_m_Sn n_a7bk7) (S Z)) &&& use ((add_m_Sn n_a7bk7) Z)))))))))))))) &&& trivial))

-- {-@ automatic-instances add_m_Sn_spliced @-}
-- {-@
-- add_m_Sn_spliced :: m:N -> n:N -> {add m (S n) == S (add m n)}
-- @-}
-- add_m_Sn_spliced :: N -> N -> Proof
-- add_m_Sn_spliced =
--   \m ->
--     \n ->
--       case m of
--         Z ->
--           ( ( use n
--                 &&& ( use (S n)
--                         &&& (use (S (S n)) &&& (use (S (S Z)) &&& (use (S Z) &&& use Z)))
--                     )
--             )
--               &&& trivial
--           )
--         S n_a7b6x ->
--           ( ( use n
--                 &&& ( use n_a7b6x
--                         &&& ( use (S n)
--                                 &&& ( use (S n_a7b6x)
--                                         &&& ( use (S (S n))
--                                                 &&& ( use (S (S n_a7b6x))
--                                                         &&& ( use (S (S Z))
--                                                                 &&& ( use (S Z)
--                                                                         &&& ( use Z
--                                                                                 &&& ( use ((add_m_Sn_spliced n_a7b6x) n)
--                                                                                         &&& ( use
--                                                                                                 ( (add_m_Sn_spliced n_a7b6x)
--                                                                                                     n_a7b6x
--                                                                                                 )
--                                                                                                 &&& ( use
--                                                                                                         ( ( add_m_Sn_spliced
--                                                                                                               n_a7b6x
--                                                                                                           )
--                                                                                                             (S n)
--                                                                                                         )
--                                                                                                         &&& ( use
--                                                                                                                 ( ( add_m_Sn_spliced
--                                                                                                                       n_a7b6x
--                                                                                                                   )
--                                                                                                                     (S n_a7b6x)
--                                                                                                                 )
--                                                                                                                 &&& ( use
--                                                                                                                         ( ( add_m_Sn_spliced
--                                                                                                                               n_a7b6x
--                                                                                                                           )
--                                                                                                                             (S Z)
--                                                                                                                         )
--                                                                                                                         &&& use
--                                                                                                                           ( ( add_m_Sn_spliced
--                                                                                                                                 n_a7b6x
--                                                                                                                             )
--                                                                                                                               Z
--                                                                                                                           )
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

-- -- -- ? PASS
-- {-@ automatic-instances add_m_Sn_manual @-}
-- {-@
-- add_m_Sn_manual :: m:N -> n:N -> {add m (S n) == S (add m n)}
-- @-}
-- add_m_Sn_manual :: N -> N -> Proof
-- add_m_Sn_manual = \m n ->
--   case m of
--     Z -> trivial
--     S m -> add_m_Sn_manual m n

-- -- ? PASS
-- -- TODO: why does this work when I paste it from the dumped splices, but it doesn't work when I use the tactic macro???
-- {-@ automatic-instances add_m_Sn_dumped @-}
-- {-@
-- add_m_Sn_dumped :: m:N -> n:N -> {add m (S n) == S (add m n)}
-- @-}
-- add_m_Sn_dumped :: N -> N -> Proof
-- add_m_Sn_dumped =
--   \m ->
--     \n ->
--       case m of
--         -- -- ! FAIL, unless turn on automatic-instances, because its missing (add Z (S n)) which is depth 3
--         Z -> (use ((add n) n) &&& (use ((add n) Z) &&& (use ((add Z) n) &&& (use ((add Z) Z) &&& (use n &&& (use (S n) &&& (use (S Z) &&& use Z)))))))
--         -- -- ? PASS
--         -- Z -> use ((add Z) (S n)) &&& use (add Z n)
--         -- -- ? PASS
--         -- Z -> trivial
--         -- -- ? PASS
--         -- Z -> trivial `byUse` add Z (S n) `byUse` add Z n
--         S n_a46ks -> undefined -- ((use ((add n) n) &&& (use ((add n) n_a46ks) &&& (use ((add n) Z) &&& (use ((add n_a46ks) n) &&& (use ((add n_a46ks) n_a46ks) &&& (use ((add n_a46ks) Z) &&& (use ((add Z) n) &&& (use ((add Z) n_a46ks) &&& (use ((add Z) Z) &&& (use n &&& (use n_a46ks &&& (use (S n) &&& (use (S n_a46ks) &&& (use (S Z) &&& (use Z &&& (use ((add_m_Sn_dumped n_a46ks) n) &&& (use ((add_m_Sn_dumped n_a46ks) n_a46ks) &&& use ((add_m_Sn_dumped n_a46ks) Z)))))))))))))))))) &&& trivial)

-- {-@
-- add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
-- @-}
-- add_m_Sn :: N -> N -> Proof
-- add_m_Sn =
--   \m ->
--     \n ->
--       case m of
--         Z ->
--           -- ( ( use ((add n) n)
--           --       &&& ( use ((add n) Z)
--           --               &&& ( use ((add Z) n)
--           --                       &&& ( use ((add Z) Z)
--           --                               &&& (use n &&& (use (S n) &&& (use (S Z) &&& use Z)))
--           --                           )
--           --                   )
--           --           )
--           --   )
--           --     &&& trivial
--           -- )
--           trivial
--         S n_a4ukW ->
--           -- ( ( use ((add n) n)
--           --       &&& ( use ((add n) n_a4ukW)
--           --               &&& ( use ((add n) Z)
--           --                       &&& ( use ((add n_a4ukW) n)
--           --                               &&& ( use ((add n_a4ukW) n_a4ukW)
--           --                                       &&& ( use ((add n_a4ukW) Z)
--           --                                               &&& ( use ((add Z) n)
--           --                                                       &&& ( use ((add Z) n_a4ukW)
--           --                                                               &&& ( use ((add Z) Z)
--           --                                                                       &&& ( use n
--           --                                                                               &&& ( use n_a4ukW
--           --                                                                                       &&& ( use (S n)
--           --                                                                                               &&& ( use
--           --                                                                                                       (S n_a4ukW)
--           --                                                                                                       &&& ( use
--           --                                                                                                               (S Z)
--           --                                                                                                               &&& ( use
--           --                                                                                                                       Z
--           --                                                                                                                       &&& ( use
--           --                                                                                                                               ( ( add_m_Sn
--           --                                                                                                                                     n_a4ukW
--           --                                                                                                                                 )
--           --                                                                                                                                   n
--           --                                                                                                                               )
--           --                                                                                                                               &&& ( use
--           --                                                                                                                                       ( ( add_m_Sn
--           --                                                                                                                                             n_a4ukW
--           --                                                                                                                                         )
--           --                                                                                                                                           n_a4ukW
--           --                                                                                                                                       )
--           --                                                                                                                                       &&& use
--           --                                                                                                                                         ( ( add_m_Sn
--           --                                                                                                                                               n_a4ukW
--           --                                                                                                                                           )
--           --                                                                                                                                             Z
--           --                                                                                                                                         )
--           --                                                                                                                                   )
--           --                                                                                                                           )
--           --                                                                                                                   )
--           --                                                                                                           )
--           --                                                                                                   )
--           --                                                                                           )
--           --                                                                                   )
--           --                                                                           )
--           --                                                                   )
--           --                                                           )
--           --                                                   )
--           --                                           )
--           --                                   )
--           --                           )
--           --                   )
--           --           )
--           --   )
--           --     &&& trivial
--           -- )
--           undefined
