{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Test.Test4 where

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
-- %tactic:begin:add_m_Sn
add_m_Sn :: N -> N -> Proof
add_m_Sn
  = \ m
      -> \ n
           -> case m of
                Z -> ((use n
                         &&&
                           (use (S n)
                              &&&
                                (use (S (S n)) &&& (use (S (S Z)) &&& (use (S Z) &&& use Z)))))
                        &&& trivial)
                S n_anRY
                  -> ((use n
                         &&&
                           (use n_anRY
                              &&&
                                (use (S n)
                                   &&&
                                     (use (S n_anRY)
                                        &&&
                                          (use (S (S n))
                                             &&&
                                               (use (S (S n_anRY))
                                                  &&&
                                                    (use (S (S Z))
                                                       &&&
                                                         (use (S Z)
                                                            &&&
                                                              (use Z
                                                                 &&&
                                                                   (use ((add_m_Sn n_anRY) n)
                                                                      &&&
                                                                        (use
                                                                           ((add_m_Sn n_anRY)
                                                                              n_anRY)
                                                                           &&&
                                                                             (use
                                                                                ((add_m_Sn
                                                                                    n_anRY)
                                                                                   (S n))
                                                                                &&&
                                                                                  (use
                                                                                     ((add_m_Sn
                                                                                         n_anRY)
                                                                                        (S n_anRY))
                                                                                     &&&
                                                                                       (use
                                                                                          ((add_m_Sn
                                                                                              n_anRY)
                                                                                             (S Z))
                                                                                          &&&
                                                                                            use
                                                                                              ((add_m_Sn
                                                                                                  n_anRY)
                                                                                                 Z)))))))))))))))
                        &&& trivial)
-- %tactic:end:add_m_Sn

return []

{-@ automatic-instances add_n_Z @-}
{-@
add_n_Z :: n:N -> {add n Z == n}
@-}
-- %tactic:begin:add_n_Z
add_n_Z :: N -> Proof
add_n_Z
  = \ n
      -> case n of
           Z -> ((use ((add Z) Z) &&& (use (S Z) &&& use Z)) &&& trivial)
           S n_anTo
             -> ((use ((add n_anTo) n_anTo)
                    &&&
                      (use ((add n_anTo) Z)
                         &&&
                           (use ((add Z) n_anTo)
                              &&&
                                (use ((add Z) Z)
                                   &&&
                                     (use n_anTo
                                        &&&
                                          (use (S n_anTo)
                                             &&&
                                               (use (S Z)
                                                  &&& (use Z &&& use (add_n_Z n_anTo)))))))))
                   &&& trivial)
-- %tactic:end:add_n_Z

return []

{-@ automatic-instances add_comm @-}
{-@
add_comm :: m:N -> n:N -> {add m n == add n m}
@-}
-- %tactic:begin:add_comm
add_comm :: N -> N -> Proof
add_comm
  = \ m
      -> \ n
           -> case m of
                Z -> ((use ((add n) n)
                         &&&
                           (use ((add n) Z)
                              &&&
                                (use ((add Z) n)
                                   &&&
                                     (use ((add Z) Z)
                                        &&&
                                          (use ((add_m_Sn n) n)
                                             &&&
                                               (use ((add_m_Sn n) Z)
                                                  &&&
                                                    (use ((add_m_Sn Z) n)
                                                       &&&
                                                         (use ((add_m_Sn Z) Z)
                                                            &&&
                                                              (use (add_n_Z n)
                                                                 &&&
                                                                   (use (add_n_Z Z)
                                                                      &&&
                                                                        (use n
                                                                           &&&
                                                                             (use (S n)
                                                                                &&&
                                                                                  (use (S Z)
                                                                                     &&&
                                                                                       use
                                                                                         Z)))))))))))))
                        &&& trivial)
                S n_anUe
                  -> ((use ((add n) n)
                         &&&
                           (use ((add n) n_anUe)
                              &&&
                                (use ((add n) Z)
                                   &&&
                                     (use ((add n_anUe) n)
                                        &&&
                                          (use ((add n_anUe) n_anUe)
                                             &&&
                                               (use ((add n_anUe) Z)
                                                  &&&
                                                    (use ((add Z) n)
                                                       &&&
                                                         (use ((add Z) n_anUe)
                                                            &&&
                                                              (use ((add Z) Z)
                                                                 &&&
                                                                   (use ((add_m_Sn n) n)
                                                                      &&&
                                                                        (use
                                                                           ((add_m_Sn n) n_anUe)
                                                                           &&&
                                                                             (use
                                                                                ((add_m_Sn n) Z)
                                                                                &&&
                                                                                  (use
                                                                                     ((add_m_Sn
                                                                                         n_anUe)
                                                                                        n)
                                                                                     &&&
                                                                                       (use
                                                                                          ((add_m_Sn
                                                                                              n_anUe)
                                                                                             n_anUe)
                                                                                          &&&
                                                                                            (use
                                                                                               ((add_m_Sn
                                                                                                   n_anUe)
                                                                                                  Z)
                                                                                               &&&
                                                                                                 (use
                                                                                                    ((add_m_Sn
                                                                                                        Z)
                                                                                                       n)
                                                                                                    &&&
                                                                                                      (use
                                                                                                         ((add_m_Sn
                                                                                                             Z)
                                                                                                            n_anUe)
                                                                                                         &&&
                                                                                                           (use
                                                                                                              ((add_m_Sn
                                                                                                                  Z)
                                                                                                                 Z)
                                                                                                              &&&
                                                                                                                (use
                                                                                                                   (add_n_Z
                                                                                                                      n)
                                                                                                                   &&&
                                                                                                                     (use
                                                                                                                        (add_n_Z
                                                                                                                           n_anUe)
                                                                                                                        &&&
                                                                                                                          (use
                                                                                                                             (add_n_Z
                                                                                                                                Z)
                                                                                                                             &&&
                                                                                                                               (use
                                                                                                                                  n
                                                                                                                                  &&&
                                                                                                                                    (use
                                                                                                                                       n_anUe
                                                                                                                                       &&&
                                                                                                                                         (use
                                                                                                                                            (S n)
                                                                                                                                            &&&
                                                                                                                                              (use
                                                                                                                                                 (S n_anUe)
                                                                                                                                                 &&&
                                                                                                                                                   (use
                                                                                                                                                      (S Z)
                                                                                                                                                      &&&
                                                                                                                                                        (use
                                                                                                                                                           Z
                                                                                                                                                           &&&
                                                                                                                                                             (use
                                                                                                                                                                ((add_comm
                                                                                                                                                                    n_anUe)
                                                                                                                                                                   n)
                                                                                                                                                                &&&
                                                                                                                                                                  (use
                                                                                                                                                                     ((add_comm
                                                                                                                                                                         n_anUe)
                                                                                                                                                                        n_anUe)
                                                                                                                                                                     &&&
                                                                                                                                                                       use
                                                                                                                                                                         ((add_comm
                                                                                                                                                                             n_anUe)
                                                                                                                                                                            Z))))))))))))))))))))))))))))))
                        &&& trivial)
-- %tactic:end:add_comm
