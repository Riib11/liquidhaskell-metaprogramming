{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module RecursionPrincipleTest where

import RecursionPrinciple

-- A

data A = A1 Int | A2 Bool

liftPref :: p:(a -> Bool) -> x:a -> {p x}
liftPred :: (a -> Bool) -> Proof

-- recA :: (Int -> a) -> (Bool -> a) -> A -> a
-- indA :: (A -> Bool) -> (Int -> a) -> (Bool -> a) -> A -> a
makeRecursionPrinciple ''A

instance Show A where
  show =
    recA
      (\i -> "A1(" ++ show i ++ ")")
      (\b -> "A2(" ++ show b ++ ")")

-- L

data L = Nil | Cons Int L

-- recL :: a -> (Int -> L -> a) -> L -> a
makeRecursionPrinciple ''L

instance Show L where
  show =
    recL
      "[]"
      (\h t -> show h ++ " :: " ++ show t)

-- I

data I a = I a

-- recI :: (a1 -> a2) -> I a1 -> a2
makeRecursionPrinciple ''I
