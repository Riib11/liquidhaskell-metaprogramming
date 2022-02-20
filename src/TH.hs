{-@ LIQUID "--compile-spec" @-}
{-# LANGUAGE TemplateHaskell #-}

module TH where

import Language.Haskell.TH
import Proof

q1 :: Code Q Int
q1 = [||1||]
