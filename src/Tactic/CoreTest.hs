{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.CoreTest where

import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core

data A = A1 Int | A2 Bool | A3 String | A4 ()

odd' :: Int -> Bool
odd' = odd

and' :: Bool -> Bool -> Bool
and' b1 b2 = b1 && b2

false = False

true = True

hints = ['not, 'odd']

return []

$(
proof
test :: Bool -> Proof


test :: Proof 
test = _ with tactic
)


test :: Proof
test =
  $( compileCore'
       (Auto Trivial)
       PreEnvironment
         { pre_vars = ['not, 'true, 'false, 'and'],
           pre_mu = ([|test|], [t|Proof|]),
           pre_gas = 5
         }
   )

-- test :: A -> Proof
-- test a =
--   $( compileCore'
--        (Destruct ''A [|a|] (Auto Trivial))
--        PreEnvironment
--          { pre_vars = hints,
--            pre_mu = [|test|],
--            pre_gas = 5
--          }
--    )
