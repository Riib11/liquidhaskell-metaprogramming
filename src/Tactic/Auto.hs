{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Auto where

import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof

-- works!
applications :: [Name] -> Q Exp
applications names = do
  ctx <- mapM (\name -> do type_ <- reifyType name; return (name, type_)) names -- :: [(Name, Q Type)]
  let apps = genApplications ctx
  bys (map return apps)
  where
    genApplications :: [(Name, Type)] -> [Exp]
    genApplications ctx = flatten $ map (\(x, type_) -> fst <$> go (VarE x, type_)) ctx
      where
        go :: (Exp, Type) -> [(Exp, Type)]
        go (app, type_) = case type_ of
          -- is a function type, so need to find an argument
          AppT (AppT ArrowT alpha) beta ->
            -- apply to all valid arguments
            flatten [go (AppE app (VarE x), beta) | (x, _) <- filter (\(_, alpha') -> alpha == alpha') ctx]
          -- isn't a function type, so we are done applying
          _ -> [(app, type_)]

bys :: [Q Exp] -> Q Exp
bys [] = [|trivial|]
bys (eQ : eQs) = [|$eQ `by` $(bys eQs)|]

flatten :: [[a]] -> [a]
flatten = foldMap id

f :: Int -> Int
f x = x + 1

g :: Bool -> Bool -> Int
g a b = if a && b then 1 else 0

x = 1 :: Int

a = True

b = False
