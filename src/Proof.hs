module Proof where

{-@ type Proof = () @-}
type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-@ reflect by @-}
by :: a -> Proof -> Proof
by _ _ = trivial

{-@ reflect con @-}
con :: a -> Proof -> a
con a _ = a

{-@ reflect for @-}
for :: Proof -> a -> Proof
for _ _ = trivial

{-@ reflect &&& @-}
(&&&) :: Proof -> Proof -> Proof
p &&& q = p

{-@ reflect with @-}
with :: a -> b -> a
with a _ = a

infixl 5 `by`

infixl 5 `con`

infixl 5 `with`

infixl 5 `for`

infixl 4 ===

{-@ (===) :: x:a -> y:{a | x == y} -> {z:a | x == z && y == z} @-}
(===) :: a -> a -> a
_ === a = a

infix 3 ***

(***) :: a -> QED -> Proof
_ *** _ = trivial

data QED = QED
