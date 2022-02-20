{-@ LIQUID "--compile-spec" @-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module DSL.Equivalence where

import Data.Char
import Data.List
import qualified Language.Haskell.Meta.Parse as Meta
import Language.Haskell.TH
-- import Language.Haskell.TH.Ppr
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
import qualified Text.Parsec as P

-- _sym_chain_sep = "%=="

-- _sym_reason_sep = "%by"

-- _sym_reason_reflexivity = "%reflexivity"

-- _sym_reason_symmetry = "%symmetry"

-- -- |
-- -- A relation r is an *equivalence* if is is reflexive, symmetry, and transitive.
-- data Equivalence = Equivalence
--   { relationExp :: forall m. Quote m => m Exp, -- a -> a -> Bool
--     reflexivityExp :: forall m. Quote m => m Exp, -- a -> Proof
--     symmetryExp :: forall m. Quote m => m Exp, -- a -> a -> Proof
--     transitivityExp :: forall m. Quote m => m Exp -- a -> a -> a -> Proof
--   }

-- data Chain = Chain
--   { equiv :: Equivalence,
--     clauses :: forall m. Quote m => [(m Exp, ChainReason)]
--   }

-- data ChainReason
--   = ChainReason_Trivial
--   | ChainReason_Proof Exp
--   | ChainReason_Reflexivity
--   | ChainReason_Symmetry ChainReason

-- instance Lift Exp where
--   -- lift : Quote m => Exp -> m Exp
--   lift = return

--   -- liftTyped :: Quote m => Exp -> Code m Exp
--   liftTyped = unsafeCodeCoerce . lift -- ! how to implement?

-- instance Lift Chain where
--   lift :: forall m. Quote m => Chain -> m Exp
--   lift chain@(Chain {..}) =
--     case clauses of
--       [] -> error "A chain cannot be empty"
--       ((a1, _) : clauses) -> go (reverse clauses)
--         where
--           -- generate Exp for transitivityExp chain
--           go :: Quote m => [(m Exp, ChainReason)] -> m Exp
--           go [] = do
--             let refl = reflexivityExp equiv
--             [|$refl $a1|]
--           go [(a2, reason_12)] = do
--             let trans = transitivityExp equiv
--             let refl = reflexivityExp equiv
--             let r_12 = liftChainReason a1 a2 reason_12
--             [|$trans $a1 $a2 $a2 $r_12 ($refl $a2)|]
--           go [(a3, reason_23), (a2, reason_12)] = do
--             let trans = transitivityExp equiv
--             let r_12 = liftChainReason a1 a2 reason_12
--             let r_23 = liftChainReason a2 a3 reason_23
--             [|$trans $a1 $a2 $a3 $r_12 $r_23|]
--           go ((ak, reason_jk) : (aj, reason_ij) : clauses) = do
--             let trans = transitivityExp equiv
--             let r_1j = go ((aj, reason_ij) : clauses)
--             let r_jk = liftChainReason aj ak reason_jk
--             [|$trans $a1 $aj $ak $r_1j $r_jk|]

--           -- generate Exp for reason that `ai` is equiv to `aj`
--           liftChainReason :: Quote m => m Exp -> m Exp -> ChainReason -> m Exp
--           liftChainReason ai aj = \case
--             ChainReason_Trivial -> [|trivial|]
--             ChainReason_Proof pf -> [|pf|]
--             ChainReason_Reflexivity -> do
--               let refl = reflexivityExp equiv
--               [|$refl $ai|]
--             ChainReason_Symmetry reason -> do
--               let symm = symmetryExp equiv
--               let r = liftChainReason aj ai reason
--               [|$symm $ai ($aj `by` $r)|]

--   -- liftTyped :: Quote m => Exp -> Code m Exp
--   liftTyped = unsafeCodeCoerce . lift

-- -- chain :: Equivalence -> QuasiQuoter
-- -- chain equiv =
-- --   QuasiQuoter
-- --     { quoteExp = compileChain equiv,
-- --       quotePat = error "Cannot quote a pattern as a chain",
-- --       quoteType = error "Cannot quite a type as a chain",
-- --       quoteDec = error "Cannot quote a declaration as a chain"
-- --     }

-- -- compileChain :: forall m. Quote m => Equivalence -> String -> m Exp
-- -- compileChain equiv str = do
-- --   chain <- parseChain equiv str
-- --   [|chain|]

-- parseChain :: forall m1. Quote m1 => Equivalence -> String -> m1 Chain
-- parseChain equiv str = do
--   -- clauses <- parseChainClauses equiv str :: forall m2. Quote m2 => m1 [(m2 Exp, ChainReason)]
--   clauses <- undefined :: forall m2. Quote m2 => m1 [(m2 Exp, ChainReason)]
--   return (Chain {equiv, clauses})

-- parseChainClauses :: forall m1 m2. (Quote m1, Quote m2) => Equivalence -> String -> m1 [(m2 Exp, ChainReason)]
-- parseChainClauses = undefined

-- parseChainClause :: forall m1 m2. (Quote m1, Quote m2) => Equivalence -> String -> m1 (m2 Exp, ChainReason)
-- parseChainClause equiv str = do
--   let strs = split _sym_reason_sep str
--   case strs of
--     [] -> error "A chain clause cannot be empty"
--     (str_term : strs_reason) -> do
--       a <- parseExp str_term
--       r <- parseChainReason equiv strs_reason
--       return (return a, r)

-- parseChainReason :: forall m. Quote m => Equivalence -> [String] -> m ChainReason
-- parseChainReason equiv [] = return ChainReason_Trivial
-- parseChainReason equiv (str : strs)
--   | str == _sym_reason_reflexivity = return ChainReason_Reflexivity
--   | str == _sym_reason_symmetry = ChainReason_Symmetry <$> parseChainReason equiv strs
--   | otherwise = ChainReason_Proof <$> parseExp str

-- parseExp :: Quote m => String -> m Exp
-- parseExp str = case Meta.parseExp str of
--   Left msg -> error msg
--   Right exp -> return exp

-- -- |
-- -- == Utilities for Parsing

-- -- Split a string by a separator.
-- split :: String -> String -> [String]
-- split sep str = go str ""
--   where
--     go "" "" = []
--     go "" wrk = [wrk]
--     go str@(c : str') wrk = case stripPrefix sep str of
--       Just str2 -> wrk : go str2 ""
--       Nothing -> go str' (wrk ++ [c])
