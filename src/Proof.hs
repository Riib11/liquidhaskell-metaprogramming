module Proof where

{-@ type Proof = () @-}
type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

refinement :: a -> Proof
refinement _ = trivial

{-@ reflect by @-}
by :: a -> Proof -> a
by a _ = a

{-@ reflect for @-}
for :: Proof -> a -> Proof
for _ _ = trivial

{-@ reflect &&& @-}
(&&&) :: Proof -> Proof -> Proof
p &&& q = p

infixl 5 `by`

infixl 5 `for`

infixl 4 ===

{-@ (===) :: x:a -> y:{a | x == y} -> {z:a | x == z && y == z} @-}
(===) :: a -> a -> a
_ === a = a

infix 3 ***

(***) :: a -> QED -> Proof
_ *** _ = trivial

data QED = QED
