module Test where

-- import Language.Haskell.TH
-- import Language.Haskell.TH.Quote
-- import Language.Haskell.TH.Syntax
import Proof

{-@ measure r :: Int -> Bool @-}

{-@ assume lem :: x:{Int | r x} -> {r (x + 1)} @-}
lem :: Int -> Proof
lem _ = ()

with' :: a -> a -> a
with' a _ = a

-- -- 2 constraints
-- -- TH: 2 constraints
-- -- MW: 2 constraints
-- {-@
-- test1 :: x:{Int | r x} -> {r (x + 1)}
-- @-}
-- test1 :: Int -> Proof
-- test1 x = lem x

-- -- 3 constraints
-- -- TH: 3 constraints
-- -- MW: 3 constraints
-- {-@
-- test2 :: x:{Int | r x} -> {r (x + 2)}
-- @-}
-- test2 :: Int -> Proof
-- test2 x =
--   lem x
--     `with'` lem (x + 1)

-- -- 97 constraints
-- -- TH: 833 constraints
-- -- MW: 42 constraints
-- {-@
-- test3 :: x:{Int | r x} -> {r (x + 3)}
-- @-}
-- test3 :: Int -> Proof
-- test3 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)

-- -- 269 constraints
-- -- TH: 2109 constraints
-- -- MW: 100 constraints
-- {-@
-- test4 :: x:{Int | r x} -> {r (x + 4)}
-- @-}
-- test4 :: Int -> Proof
-- test4 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)

-- -- 539 constraints
-- -- TH: 3851 constraints
-- -- MW: 177 constraints
-- {-@
-- test5 :: x:{Int | r x} -> {r (x + 5)}
-- @-}
-- test5 :: Int -> Proof
-- test5 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)

-- -- 927 constraints
-- -- TH: 6079 constraints
-- -- MW: 273 constraints
-- {-@
-- test6 :: x:{Int | r x} -> {r (x + 6)}
-- @-}
-- test6 :: Int -> Proof
-- test6 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)
--     `with'` lem (x + 5)

-- -- 1453 constraints
-- -- TH: 8813 constraints
-- -- MW: 388 constraints
-- {-@
-- test7 :: x:{Int | r x} -> {r (x + 7)}
-- @-}
-- test7 :: Int -> Proof
-- test7 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)
--     `with'` lem (x + 5)
--     `with'` lem (x + 6)

-- -- 2137 constraints
-- -- TH: 12073 constraints
-- -- MW: 522 constraints
-- {-@
-- test8 :: x:{Int | r x} -> {r (x + 8)}
-- @-}
-- test8 :: Int -> Proof
-- test8 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)
--     `with'` lem (x + 5)
--     `with'` lem (x + 6)
--     `with'` lem (x + 7)

-- -- 2999 constraints
-- -- TH: 15879 constraints
-- -- MW: 657 constraints
-- {-@
-- test9 :: x:{Int | r x} -> {r (x + 9)}
-- @-}
-- test9 :: Int -> Proof
-- test9 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)
--     `with'` lem (x + 5)
--     `with'` lem (x + 6)
--     `with'` lem (x + 7)
--     `with'` lem (x + 8)

-- -- 4059 constraints
-- -- TH: 20251 constraints
-- -- MW: 847 constraints
-- {-@
-- test10 :: x:{Int | r x} -> {r (x + 10)}
-- @-}
-- test10 :: Int -> Proof
-- test10 x =
--   lem x
--     `with'` lem (x + 1)
--     `with'` lem (x + 2)
--     `with'` lem (x + 3)
--     `with'` lem (x + 4)
--     `with'` lem (x + 5)
--     `with'` lem (x + 6)
--     `with'` lem (x + 7)
--     `with'` lem (x + 8)
--     `with'` lem (x + 9)
