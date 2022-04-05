module Tactic.Core.Utility where

{-@ LIQUID "--compile-spec" @-}

import Language.Haskell.TH.Syntax

flattenType :: Type -> ([Type], Type)
flattenType (AppT (AppT ArrowT alpha) beta) =
  let (alphas, delta) = flattenType beta
   in (alpha : alphas, delta)
flattenType alpha = ([], alpha)

index :: [a] -> Int -> Maybe a
index [] _ = Nothing
index (x : xs) 0 = Just x
index (_ : xs) i = index xs (i - 1)
