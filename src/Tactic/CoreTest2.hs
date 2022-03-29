{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.CoreTest2 where

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

return []

{-@
add_m_Sn_manual :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
add_m_Sn_manual :: N -> N -> Proof
add_m_Sn_manual Z n =
  add Z (S n)
    === S (add Z n)
    *** QED
add_m_Sn_manual (S m) n =
  add (S m) (S n)
    === S (add m (S n))
    === S (S (add m n)) `by` add_m_Sn_manual m n
    === S (add (S m) n)
    *** QED

{-@
add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
add_m_Sn :: N -> N -> Proof
add_m_Sn m n =
  $( do
       ctx <- toCtx [([|m|], [t|N|]), ([|n|], [t|N|])]
       hints <- toCtx [([|Z|], [t|N|]), ([|S|], [t|N -> N|]), ([|add|], [t|N -> N -> N|])]
       mu <- pairM [|add_m_Sn|] [t|N -> N -> Proof|]
       compileCoreE
         Environment {ctx, recCtxs = replicate 2 Nothing, mu}
         ( buildCore
             [ Induct [|m|] ''N 0 {-iArg-},
               Auto hints 3 {-depth-}
             ]
         )
   )

{-@
add_n_Z :: n:N -> {add n Z == n}
@-}
add_n_Z :: N -> Proof
add_n_Z n =
  $( do
       ctx <- toCtx [([|n|], [t|N|])]
       hints <- toCtx [([|Z|], [t|N|]), ([|S|], [t|N -> N|]), ([|add|], [t|N -> N -> N|])]
       mu <- pairM [|add_n_Z|] [t|N -> Proof|]
       compileCoreE
         Environment {ctx, recCtxs = replicate 1 Nothing, mu}
         ( buildCore
             [ Induct [|n|] ''N 0 {-iArg-},
               Auto hints 2 {-depth-}
             ]
         )
   )

-- {-@
-- add_comm_manual :: m:N -> n:N -> {add m n == add n m}
-- @-}
-- add_comm_manual :: N -> N -> Proof
-- add_comm_manual Z n =
--   add Z n
--     === n
--     === add n Z `by` add_n_Z n
--     *** QED
-- add_comm_manual (S m) n =
--   add (S m) n
--     === S (add m n)
--     === S (add n m) `by` add_comm_manual m n
--     === add n (S m) `by` add_m_Sn_manual n m
--     *** QED

{-@
add_comm :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
add_comm :: N -> N -> Proof
add_comm m n =
  $( do
       ctx <- toCtx [([|m|], [t|N|]), ([|n|], [t|N|])]
       hints <-
         toCtx
           [ ([|Z|], [t|N|]),
             ([|S|], [t|N -> N|]),
             ([|add|], [t|N -> N -> N|]),
             ([|add_n_Z|], [t|N -> Proof|]),
             ([|add_m_Sn|], [t|N -> N -> Proof|])
           ]
       mu <- pairM [|add_comm|] [t|N -> N -> Proof|]
       compileCoreE
         Environment {ctx, recCtxs = replicate 2 Nothing, mu}
         ( buildCore
             [ Induct [|m|] ''N 0 {-iArg-},
               Auto hints 2 {-depth-} -- works on depth 2
             ]
         )
   )

{-@
add_comm :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
[proof|
add_comm :: N -> N -> Proof
add_comm m n = 
  induct m;
  auto [add, add_n_Z, add_m_Sn]
|]
