{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core where

import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

data Core
  = Expression (Q Exp) Core
  | Branch (Q Exp) Core
  | Destruct
      Name -- datatype name
      (Q Exp) -- term to destruct
      Core
  | Application (Q Exp) (Q Exp) Core
  | Assertion (Q Exp) Core
  | Loop
      (Q Exp -> Q Exp) -- cond
      (Q Exp -> [Q Exp]) -- nexts
      (Q Exp) -- aQ_init
      (Q Exp -> Core) -- body
      Int -- gas
  | Block [Core]
  | Pass

compileCore :: Core -> Q Exp
compileCore Pass = [|trivial|]
compileCore (Expression eQ core) = [|$eQ `by` $(compileCore core)|]
compileCore (Branch cond core) = [|if $cond then $(compileCore core) else $(compileCore core)|]
compileCore (Destruct dtName aQ core) = do
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  let bodyQ = compileCore core
  let matchQs = map (\conInfo -> match wildP (normalB bodyQ) []) dtConInfos
  caseE aQ matchQs
compileCore (Application fQ aQ core) = [|$fQ $aQ `by` $(compileCore core)|]
compileCore (Assertion bQ core) = [|if $bQ then $(compileCore core) else trivial|]
compileCore (Loop cond nexts aQ_init body gas) =
  let loop aQ gas =
        if gas == 0
          then [|trivial|]
          else
            let tail = foldl (\pQ aQ -> [|$(loop aQ (gas - 1)) &&& $pQ|]) [|trivial|] (nexts aQ)
             in [|if $(cond aQ) then trivial else $(compileCore (body aQ)) &&& $tail|]
   in loop aQ_init gas
compileCore (Block cores) = foldl (\pQ core -> [|$pQ &&& $(compileCore core)|]) [|trivial|] cores

applyQ :: Q Exp -> Q Exp -> Q Exp
applyQ fQ aQ = [|$fQ $aQ|]

data A = A1 Int | A2 Bool | A3 String | A4 ()

-- reifyType gets the type of a variable
