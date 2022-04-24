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
add_assoc =
  \l ->
    \m ->
      \n ->
        case l of
          Z -> case m of
            Z ->
              ( ( use ((add n) n)
                    &&& ( use ((add n) Z)
                            &&& ( use ((add Z) n)
                                    &&& ( use ((add Z) Z)
                                            &&& ( use ((add_m_Sn n) n)
                                                    &&& ( use ((add_m_Sn n) Z)
                                                            &&& ( use ((add_m_Sn Z) n)
                                                                    &&& ( use ((add_m_Sn Z) Z)
                                                                            &&& ( use (add_n_Z n)
                                                                                    &&& ( use (add_n_Z Z)
                                                                                            &&& ( use n
                                                                                                    &&& ( use
                                                                                                            (S n)
                                                                                                            &&& ( use
                                                                                                                    (S Z)
                                                                                                                    &&& use
                                                                                                                      Z
                                                                                                                )
                                                                                                        )
                                                                                                )
                                                                                        )
                                                                                )
                                                                        )
                                                                )
                                                        )
                                                )
                                        )
                                )
                        )
                )
                  &&& trivial
              )
            S n_apa6 ->
              ( ( use ((add n) n)
                    &&& ( use ((add n) n_apa6)
                            &&& ( use ((add n) Z)
                                    &&& ( use ((add n_apa6) n)
                                            &&& ( use ((add n_apa6) n_apa6)
                                                    &&& ( use ((add n_apa6) Z)
                                                            &&& ( use ((add Z) n)
                                                                    &&& ( use ((add Z) n_apa6)
                                                                            &&& ( use ((add Z) Z)
                                                                                    &&& ( use
                                                                                            ( (add_m_Sn n)
                                                                                                n
                                                                                            )
                                                                                            &&& ( use
                                                                                                    ( ( add_m_Sn
                                                                                                          n
                                                                                                      )
                                                                                                        n_apa6
                                                                                                    )
                                                                                                    &&& ( use
                                                                                                            ( ( add_m_Sn
                                                                                                                  n
                                                                                                              )
                                                                                                                Z
                                                                                                            )
                                                                                                            &&& ( use
                                                                                                                    ( ( add_m_Sn
                                                                                                                          n_apa6
                                                                                                                      )
                                                                                                                        n
                                                                                                                    )
                                                                                                                    &&& ( use
                                                                                                                            ( ( add_m_Sn
                                                                                                                                  n_apa6
                                                                                                                              )
                                                                                                                                n_apa6
                                                                                                                            )
                                                                                                                            &&& ( use
                                                                                                                                    ( ( add_m_Sn
                                                                                                                                          n_apa6
                                                                                                                                      )
                                                                                                                                        Z
                                                                                                                                    )
                                                                                                                                    &&& ( use
                                                                                                                                            ( ( add_m_Sn
                                                                                                                                                  Z
                                                                                                                                              )
                                                                                                                                                n
                                                                                                                                            )
                                                                                                                                            &&& ( use
                                                                                                                                                    ( ( add_m_Sn
                                                                                                                                                          Z
                                                                                                                                                      )
                                                                                                                                                        n_apa6
                                                                                                                                                    )
                                                                                                                                                    &&& ( use
                                                                                                                                                            ( ( add_m_Sn
                                                                                                                                                                  Z
                                                                                                                                                              )
                                                                                                                                                                Z
                                                                                                                                                            )
                                                                                                                                                            &&& ( use
                                                                                                                                                                    ( add_n_Z
                                                                                                                                                                        n
                                                                                                                                                                    )
                                                                                                                                                                    &&& ( use
                                                                                                                                                                            ( add_n_Z
                                                                                                                                                                                n_apa6
                                                                                                                                                                            )
                                                                                                                                                                            &&& ( use
                                                                                                                                                                                    ( add_n_Z
                                                                                                                                                                                        Z
                                                                                                                                                                                    )
                                                                                                                                                                                    &&& ( use
                                                                                                                                                                                            n
                                                                                                                                                                                            &&& ( use
                                                                                                                                                                                                    n_apa6
                                                                                                                                                                                                    &&& ( use
                                                                                                                                                                                                            (S n)
                                                                                                                                                                                                            &&& ( use
                                                                                                                                                                                                                    (S n_apa6)
                                                                                                                                                                                                                    &&& ( use
                                                                                                                                                                                                                            (S Z)
                                                                                                                                                                                                                            &&& use
                                                                                                                                                                                                                              Z
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                )
                                                                                                                                                                                                        )
                                                                                                                                                                                                )
                                                                                                                                                                                        )
                                                                                                                                                                                )
                                                                                                                                                                        )
                                                                                                                                                                )
                                                                                                                                                        )
                                                                                                                                                )
                                                                                                                                        )
                                                                                                                                )
                                                                                                                        )
                                                                                                                )
                                                                                                        )
                                                                                                )
                                                                                        )
                                                                                )
                                                                        )
                                                                )
                                                        )
                                                )
                                        )
                                )
                        )
                )
                  &&& trivial
              )
          S n_apa7 ->
            case m of
              Z ->
                ( ( use ((add n) n)
                      &&& ( use ((add n) n_apa7)
                              &&& ( use ((add n) Z)
                                      &&& ( use ((add n_apa7) n)
                                              &&& ( use ((add n_apa7) n_apa7)
                                                      &&& ( use ((add n_apa7) Z)
                                                              &&& ( use ((add Z) n)
                                                                      &&& ( use ((add Z) n_apa7)
                                                                              &&& ( use ((add Z) Z)
                                                                                      &&& ( use
                                                                                              ( (add_m_Sn n)
                                                                                                  n
                                                                                              )
                                                                                              &&& ( use
                                                                                                      ( ( add_m_Sn
                                                                                                            n
                                                                                                        )
                                                                                                          n_apa7
                                                                                                      )
                                                                                                      &&& ( use
                                                                                                              ( ( add_m_Sn
                                                                                                                    n
                                                                                                                )
                                                                                                                  Z
                                                                                                              )
                                                                                                              &&& ( use
                                                                                                                      ( ( add_m_Sn
                                                                                                                            n_apa7
                                                                                                                        )
                                                                                                                          n
                                                                                                                      )
                                                                                                                      &&& ( use
                                                                                                                              ( ( add_m_Sn
                                                                                                                                    n_apa7
                                                                                                                                )
                                                                                                                                  n_apa7
                                                                                                                              )
                                                                                                                              &&& ( use
                                                                                                                                      ( ( add_m_Sn
                                                                                                                                            n_apa7
                                                                                                                                        )
                                                                                                                                          Z
                                                                                                                                      )
                                                                                                                                      &&& ( use
                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                    Z
                                                                                                                                                )
                                                                                                                                                  n
                                                                                                                                              )
                                                                                                                                              &&& ( use
                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                            Z
                                                                                                                                                        )
                                                                                                                                                          n_apa7
                                                                                                                                                      )
                                                                                                                                                      &&& ( use
                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                    Z
                                                                                                                                                                )
                                                                                                                                                                  Z
                                                                                                                                                              )
                                                                                                                                                              &&& ( use
                                                                                                                                                                      ( add_n_Z
                                                                                                                                                                          n
                                                                                                                                                                      )
                                                                                                                                                                      &&& ( use
                                                                                                                                                                              ( add_n_Z
                                                                                                                                                                                  n_apa7
                                                                                                                                                                              )
                                                                                                                                                                              &&& ( use
                                                                                                                                                                                      ( add_n_Z
                                                                                                                                                                                          Z
                                                                                                                                                                                      )
                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                              n
                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                      n_apa7
                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                              (S n)
                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                      (S n_apa7)
                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                              (S Z)
                                                                                                                                                                                                                              &&& use
                                                                                                                                                                                                                                Z
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                  )
                                                                                                                                                                                                          )
                                                                                                                                                                                                  )
                                                                                                                                                                                          )
                                                                                                                                                                                  )
                                                                                                                                                                          )
                                                                                                                                                                  )
                                                                                                                                                          )
                                                                                                                                                  )
                                                                                                                                          )
                                                                                                                                  )
                                                                                                                          )
                                                                                                                  )
                                                                                                          )
                                                                                                  )
                                                                                          )
                                                                                  )
                                                                          )
                                                                  )
                                                          )
                                                  )
                                          )
                                  )
                          )
                  )
                    &&& trivial
                )
              S n_apa8 ->
                ( ( use ((add n) n)
                      &&& ( use ((add n) n_apa7)
                              &&& ( use ((add n) n_apa8)
                                      &&& ( use ((add n) Z)
                                              &&& ( use ((add n_apa7) n)
                                                      &&& ( use ((add n_apa7) n_apa7)
                                                              &&& ( use ((add n_apa7) n_apa8)
                                                                      &&& ( use ((add n_apa7) Z)
                                                                              &&& ( use ((add n_apa8) n)
                                                                                      &&& ( use
                                                                                              ( (add n_apa8)
                                                                                                  n_apa7
                                                                                              )
                                                                                              &&& ( use
                                                                                                      ( ( add
                                                                                                            n_apa8
                                                                                                        )
                                                                                                          n_apa8
                                                                                                      )
                                                                                                      &&& ( use
                                                                                                              ( ( add
                                                                                                                    n_apa8
                                                                                                                )
                                                                                                                  Z
                                                                                                              )
                                                                                                              &&& ( use
                                                                                                                      ( ( add
                                                                                                                            Z
                                                                                                                        )
                                                                                                                          n
                                                                                                                      )
                                                                                                                      &&& ( use
                                                                                                                              ( ( add
                                                                                                                                    Z
                                                                                                                                )
                                                                                                                                  n_apa7
                                                                                                                              )
                                                                                                                              &&& ( use
                                                                                                                                      ( ( add
                                                                                                                                            Z
                                                                                                                                        )
                                                                                                                                          n_apa8
                                                                                                                                      )
                                                                                                                                      &&& ( use
                                                                                                                                              ( ( add
                                                                                                                                                    Z
                                                                                                                                                )
                                                                                                                                                  Z
                                                                                                                                              )
                                                                                                                                              &&& ( use
                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                            n
                                                                                                                                                        )
                                                                                                                                                          n
                                                                                                                                                      )
                                                                                                                                                      &&& ( use
                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                    n
                                                                                                                                                                )
                                                                                                                                                                  n_apa7
                                                                                                                                                              )
                                                                                                                                                              &&& ( use
                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                            n
                                                                                                                                                                        )
                                                                                                                                                                          n_apa8
                                                                                                                                                                      )
                                                                                                                                                                      &&& ( use
                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                    n
                                                                                                                                                                                )
                                                                                                                                                                                  Z
                                                                                                                                                                              )
                                                                                                                                                                              &&& ( use
                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                            n_apa7
                                                                                                                                                                                        )
                                                                                                                                                                                          n
                                                                                                                                                                                      )
                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                    n_apa7
                                                                                                                                                                                                )
                                                                                                                                                                                                  n_apa7
                                                                                                                                                                                              )
                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                                            n_apa7
                                                                                                                                                                                                        )
                                                                                                                                                                                                          n_apa8
                                                                                                                                                                                                      )
                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                                    n_apa7
                                                                                                                                                                                                                )
                                                                                                                                                                                                                  Z
                                                                                                                                                                                                              )
                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                                                            n_apa8
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                          n
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                                                    n_apa8
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                  n_apa7
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                                                                            n_apa8
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                          n_apa8
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                                                                    n_apa8
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                  Z
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                                                                                            Z
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                          n
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                                                                                    Z
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                  n_apa7
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                      ( ( add_m_Sn
                                                                                                                                                                                                                                                                            Z
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                          n_apa8
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                              ( ( add_m_Sn
                                                                                                                                                                                                                                                                                    Z
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                  Z
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                      ( add_n_Z
                                                                                                                                                                                                                                                                                          n
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                              ( add_n_Z
                                                                                                                                                                                                                                                                                                  n_apa7
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                      ( add_n_Z
                                                                                                                                                                                                                                                                                                          n_apa8
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                              ( add_n_Z
                                                                                                                                                                                                                                                                                                                  Z
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                      n
                                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                                              n_apa7
                                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                                      n_apa8
                                                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                                                              (S n)
                                                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                                                      (S n_apa7)
                                                                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                                                                              (S n_apa8)
                                                                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                                                                      (S Z)
                                                                                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                                                                                              Z
                                                                                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                                                                                      ( ( ( add_assoc
                                                                                                                                                                                                                                                                                                                                                                                              n_apa7
                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                            n_apa8
                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                          n
                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                      &&& ( use
                                                                                                                                                                                                                                                                                                                                                                                              ( ( ( add_assoc
                                                                                                                                                                                                                                                                                                                                                                                                      n_apa7
                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                                    n_apa8
                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                  n_apa7
                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                              &&& ( use
                                                                                                                                                                                                                                                                                                                                                                                                      ( ( ( add_assoc
                                                                                                                                                                                                                                                                                                                                                                                                              n_apa7
                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                            n_apa8
                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                          n_apa8
                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                      &&& use
                                                                                                                                                                                                                                                                                                                                                                                                        ( ( ( add_assoc
                                                                                                                                                                                                                                                                                                                                                                                                                n_apa7
                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                              n_apa8
                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                            Z
                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                  )
                                                                                                                                                                                                          )
                                                                                                                                                                                                  )
                                                                                                                                                                                          )
                                                                                                                                                                                  )
                                                                                                                                                                          )
                                                                                                                                                                  )
                                                                                                                                                          )
                                                                                                                                                  )
                                                                                                                                          )
                                                                                                                                  )
                                                                                                                          )
                                                                                                                  )
                                                                                                          )
                                                                                                  )
                                                                                          )
                                                                                  )
                                                                          )
                                                                  )
                                                          )
                                                  )
                                          )
                                  )
                          )
                  )
                    &&& trivial
                )

-- %tactic:end:add_assoc
