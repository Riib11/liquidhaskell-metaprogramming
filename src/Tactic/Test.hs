{-@ LIQUID "--reflection" @-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Tactic.Test where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Auto

{-@ reflect isTrue @-}
isTrue :: Bool -> Bool
isTrue b = b

{-@ test :: {isTrue True} @-}
test :: Proof
test = $(tactic_contradiction [|isTrue|] [|True|])
