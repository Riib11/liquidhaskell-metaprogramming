module Proof where

{-@ type Proof = () @-}
type Proof = ()

{-@ reflect trivial @-}
trivial :: Proof
trivial = ()

{-@ reflect by @-}
by :: a -> Proof -> Proof
by a _ = trivial

{-@ reflect with @-}
with :: a -> b -> a
with a _ = a
