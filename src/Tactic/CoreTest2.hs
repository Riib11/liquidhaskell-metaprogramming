{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--compile-spec" @-}
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
    === S (S (add m n)) `con` add_m_Sn_manual m n
    === S (add (S m) n) `with` add (S m) n
    *** QED

{-@
add_m_Sn_tactical :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
add_m_Sn_tactical :: N -> N -> Proof
add_m_Sn_tactical m n =
  $( do
       ctx <-
         fromList
           <$> mapM
             (\(eQ, alphaQ) -> (,) <$> eQ <*> alphaQ)
             ( [ --  ([|m|], [t|N|]),
                 --  ([|n|], [t|N|]),
                 ([|Z|], [t|N|]),
                 ([|S|], [t|N -> N|])
                 --  ([|add|], [t|N -> N -> N|])
               ] ::
                 [(Q Exp, Q Type)]
             )
       mu <- (,) <$> [|add_m_Sn_tactical|] <*> [t|N -> N -> Proof|]
       compileCoreE
         ( buildCore
             [ -- Induct [|m|] ''N 0,
               Auto
             ]
         )
         Environment {ctx, inds = mempty, mu, gas = 11}
   )
