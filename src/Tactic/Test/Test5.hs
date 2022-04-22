{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC "-ddump-splices" #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Tactic.Test.Test5 where

import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote
import Tactic.Test.Test4 (N(..), add, add_m_Sn, add_n_Z, add_comm)

-- TODO: fix bug where its trying to inferType of m inside of auto, even though it should have been removed from the context since its being inducted on

-- {-@ automatic-instances add_assoc @-}
-- {-@
-- add_assoc :: l:N -> m:N -> n:N -> {add (add l m) n == add l (add m n)}
-- @-}
-- [tactic|
-- add_assoc :: N -> N -> N -> Proof 
-- add_assoc l m n =
--   induct l;
--   induct m;
--   auto [Z, S, add, add_n_Z, add_m_Sn] 0
-- |]