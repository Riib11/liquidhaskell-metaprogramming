{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Tactic where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core

data Tactic
  = Cores [Core]
  | forall a. Expressions [Code Q a]
  | Branches [Code Q Bool]
  | forall a b. Applications [Code Q (a -> b)] [Code Q a]
  | Assertions [Code Q Bool]
  | Blocks [[Tactic]]

expandTactic :: Tactic -> [Core]
expandTactic (Cores cores) = cores
expandTactic (Expressions es) = Expression <$> es
expandTactic (Branches conds) = Branch <$> conds
expandTactic (Applications lems hyps) = [Application lem hyp | lem <- lems, hyp <- hyps]
expandTactic (Assertions conds) = Assertion <$> conds
expandTactic (Blocks blocks) = Block . mconcat . fmap expandTactic <$> blocks

compileTactics :: [Tactic] -> Code Q Proof
compileTactics = compileCore . mconcat . map expandTactic
