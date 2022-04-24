{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Test.Test5 where

import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote
import Tactic.Test.Test4 (N (..), add, add_comm, add_m_Sn, add_n_Z)

{-@ automatic-instances add_assoc @-}
{-@
add_assoc :: l:N -> m:N -> n:N -> {add (add l m) n == add l (add m n)}
@-}
-- %tactic:begin:add_assoc
add_assoc :: N -> N -> N -> Proof
add_assoc
  = \ l
      -> \ m
           -> \ n
                -> case l of
                     Z -> case m of
                            Z -> ((use ((add_m_Sn n) n)
                                     &&&
                                       (use ((add_m_Sn n) Z)
                                          &&&
                                            (use ((add_m_Sn Z) n)
                                               &&&
                                                 (use ((add_m_Sn Z) Z)
                                                    &&&
                                                      (use (add_n_Z n) &&& use (add_n_Z Z))))))
                                    &&& trivial)
                            S n_aoO1
                              -> ((use ((add_m_Sn n) n)
                                     &&&
                                       (use ((add_m_Sn n) n_aoO1)
                                          &&&
                                            (use ((add_m_Sn n) Z)
                                               &&&
                                                 (use ((add_m_Sn n_aoO1) n)
                                                    &&&
                                                      (use ((add_m_Sn n_aoO1) n_aoO1)
                                                         &&&
                                                           (use ((add_m_Sn n_aoO1) Z)
                                                              &&&
                                                                (use ((add_m_Sn Z) n)
                                                                   &&&
                                                                     (use ((add_m_Sn Z) n_aoO1)
                                                                        &&&
                                                                          (use ((add_m_Sn Z) Z)
                                                                             &&&
                                                                               (use (add_n_Z n)
                                                                                  &&&
                                                                                    (use
                                                                                       (add_n_Z
                                                                                          n_aoO1)
                                                                                       &&&
                                                                                         use
                                                                                           (add_n_Z
                                                                                              Z))))))))))))
                                    &&& trivial)
                     S n_aoO2
                       -> case m of
                            Z -> ((use ((add_m_Sn n) n)
                                     &&&
                                       (use ((add_m_Sn n) n_aoO2)
                                          &&&
                                            (use ((add_m_Sn n) Z)
                                               &&&
                                                 (use ((add_m_Sn n_aoO2) n)
                                                    &&&
                                                      (use ((add_m_Sn n_aoO2) n_aoO2)
                                                         &&&
                                                           (use ((add_m_Sn n_aoO2) Z)
                                                              &&&
                                                                (use ((add_m_Sn Z) n)
                                                                   &&&
                                                                     (use ((add_m_Sn Z) n_aoO2)
                                                                        &&&
                                                                          (use ((add_m_Sn Z) Z)
                                                                             &&&
                                                                               (use (add_n_Z n)
                                                                                  &&&
                                                                                    (use
                                                                                       (add_n_Z
                                                                                          n_aoO2)
                                                                                       &&&
                                                                                         use
                                                                                           (add_n_Z
                                                                                              Z))))))))))))
                                    &&& trivial)
                            S n_aoO3
                              -> ((use ((add_m_Sn n) n)
                                     &&&
                                       (use ((add_m_Sn n) n_aoO2)
                                          &&&
                                            (use ((add_m_Sn n) n_aoO3)
                                               &&&
                                                 (use ((add_m_Sn n) Z)
                                                    &&&
                                                      (use ((add_m_Sn n_aoO2) n)
                                                         &&&
                                                           (use ((add_m_Sn n_aoO2) n_aoO2)
                                                              &&&
                                                                (use ((add_m_Sn n_aoO2) n_aoO3)
                                                                   &&&
                                                                     (use ((add_m_Sn n_aoO2) Z)
                                                                        &&&
                                                                          (use
                                                                             ((add_m_Sn n_aoO3)
                                                                                n)
                                                                             &&&
                                                                               (use
                                                                                  ((add_m_Sn
                                                                                      n_aoO3)
                                                                                     n_aoO2)
                                                                                  &&&
                                                                                    (use
                                                                                       ((add_m_Sn
                                                                                           n_aoO3)
                                                                                          n_aoO3)
                                                                                       &&&
                                                                                         (use
                                                                                            ((add_m_Sn
                                                                                                n_aoO3)
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
                                                                                                         n_aoO2)
                                                                                                      &&&
                                                                                                        (use
                                                                                                           ((add_m_Sn
                                                                                                               Z)
                                                                                                              n_aoO3)
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
                                                                                                                             n_aoO2)
                                                                                                                          &&&
                                                                                                                            (use
                                                                                                                               (add_n_Z
                                                                                                                                  n_aoO3)
                                                                                                                               &&&
                                                                                                                                 (use
                                                                                                                                    (add_n_Z
                                                                                                                                       Z)
                                                                                                                                    &&&
                                                                                                                                      (use
                                                                                                                                         (((add_assoc
                                                                                                                                              n_aoO2)
                                                                                                                                             n_aoO3)
                                                                                                                                            n)
                                                                                                                                         &&&
                                                                                                                                           (use
                                                                                                                                              (((add_assoc
                                                                                                                                                   n_aoO2)
                                                                                                                                                  n_aoO3)
                                                                                                                                                 n_aoO2)
                                                                                                                                              &&&
                                                                                                                                                (use
                                                                                                                                                   (((add_assoc
                                                                                                                                                        n_aoO2)
                                                                                                                                                       n_aoO3)
                                                                                                                                                      n_aoO3)
                                                                                                                                                   &&&
                                                                                                                                                     use
                                                                                                                                                       (((add_assoc
                                                                                                                                                            n_aoO2)
                                                                                                                                                           n_aoO3)
                                                                                                                                                          Z))))))))))))))))))))))))
                                    &&& trivial)
-- %tactic:end:add_assoc
