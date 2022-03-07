{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

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
  | Applications Core
  | Assertion (Q Exp) Core
  | Loop
      (Q Exp -> Q Exp) -- cond
      (Q Exp -> [Q Exp]) -- nexts
      (Q Exp) -- aQ_init
      (Q Exp -> Core) -- body
      Int -- gas
  | Block [Core]
  | Pass

genConPat :: ConstructorInfo -> Q ([(Name, Type)], Pat)
genConPat conInfo = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  ctx <- mapM (\type_ -> do name <- newName "x"; return (name, type_)) conFields
  pat <- conP conName (map (varP . fst) ctx)
  return (ctx, pat)

reifyContext :: [Name] -> Q [(Name, Type)]
reifyContext = mapM (\name -> (name,) <$> reifyType name)

compileCore' :: Core -> [Name] -> Q Exp
compileCore' core names = compileCore core =<< reifyContext names

compileCore :: Core -> [(Name, Type)] -> Q Exp
compileCore Pass ctx = [|trivial|]
compileCore (Expression eQ core) ctx = [|$eQ `by` $(compileCore core ctx)|]
compileCore (Branch cond core) ctx = [|if $cond then $(compileCore core ctx) else $(compileCore core ctx)|]
compileCore (Destruct dtName aQ core) ctx = do
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  let matchQs =
        map
          ( \conInfo -> do
              -- adds newly bound variables to context
              (ctx', pat) <- genConPat conInfo
              match (return pat) (normalB (compileCore core (ctx <> ctx'))) []
          )
          dtConInfos
  caseE aQ matchQs
compileCore (Application fQ aQ core) ctx = [|$fQ $aQ `by` $(compileCore core ctx)|]
compileCore (Applications core) ctx = [|$(apps ctx) `by` $(compileCore core ctx)|]
  where
    apps = bys . map return . genApps
    genApps :: [(Name, Type)] -> [Exp]
    genApps ctx = flatten $ map (\(x, type_) -> fst <$> go (VarE x, type_)) ctx
      where
        go :: (Exp, Type) -> [(Exp, Type)]
        go (app, type_) = case type_ of
          -- is a function type, so need to find an argument
          AppT (AppT ArrowT alpha) beta ->
            -- apply to all valid arguments
            flatten [go (AppE app (VarE x), beta) | (x, _) <- filter (\(_, alpha') -> alpha == alpha') ctx]
          -- isn't a function type, so we are done applying
          _ -> [(app, type_)]
compileCore (Assertion bQ core) ctx = [|if $bQ then $(compileCore core ctx) else trivial|]
compileCore (Loop cond nexts aQ_init body gas) ctx =
  let loop aQ gas =
        if gas == 0
          then [|trivial|]
          else
            let tail = foldl (\pQ aQ -> [|$(loop aQ (gas - 1)) &&& $pQ|]) [|trivial|] (nexts aQ)
             in [|if $(cond aQ) then trivial else $(compileCore (body aQ) ctx) &&& $tail|]
   in loop aQ_init gas
compileCore (Block cores) ctx = foldl (\pQ core -> [|$pQ &&& $(compileCore core ctx)|]) [|trivial|] cores

applyQ :: Q Exp -> Q Exp -> Q Exp
applyQ fQ aQ = [|$fQ $aQ|]

bys :: [Q Exp] -> Q Exp
bys [] = [|trivial|]
bys (eQ : eQs) = [|$eQ `by` $(bys eQs)|]

flatten :: [[a]] -> [a]
flatten = foldMap id

data A = A1 Int | A2 Bool | A3 String | A4 ()

-- reifyType gets the type of a variable
