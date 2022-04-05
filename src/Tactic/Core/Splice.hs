{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Splice where

import Control.Monad.Trans as Trans
import Control.Monad.Trans.State as State
import qualified Data.Map as Map
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax hiding (lift)
import Proof
import Tactic.Core.Syntax
import Tactic.Core.Utility
import Prelude hiding (exp)

type Splice a = StateT Environment Q a

-- spliceExp :: Environment -> [Instr] -> Q Exp
spliceExp :: [Instr] -> Splice Exp
spliceExp [] = lift [|trivial|]
spliceExp (Intro {name} : instrs) = do
  types <- gets def_argTypes
  i <- gets goal_arg_i
  env <- get
  type_ <- case types `index` i of
    Just type_ -> pure type_
    Nothing -> fail $ "Cannot intro " ++ show name ++ " at non-function type"
  modify $ introArg name type_
  e <- spliceExp instrs
  lift [|\ $(varP name) -> $(pure e)|]
spliceExp (Destruct {name} : instrs) = do
  type_ <- get >>= \env -> lift $ inferType name env
  case type_ of
    ConT dtName -> do
      -- remove destructed target from environment
      modify $ deleteCtx name
      -- get datatype info
      dtInfo <- lift $ reifyDatatype dtName
      -- gen matches
      let dtConInfos = datatypeCons dtInfo

      let matches :: [Splice Match]
          matches =
            ( \conInfo -> do
                -- collects newly bound variables with types, generates match's pattern
                (vars, pat) <- lift $ getConVarsPat conInfo
                -- adds constructor's introduced terms to environment
                modify $ flip (foldl (flip (uncurry insertCtx))) vars
                -- gen match
                e <- spliceExp instrs
                lift $ match (pure pat) (normalB $ pure e) []
            )
              <$> dtConInfos
      -- generate case
      ms <- sequence matches
      lift $ caseE (varE name) (pure <$> ms)
    _ -> fail $ "Cannot destruct " ++ show name ++ " of non-datatype type " ++ show type_
  undefined
spliceExp (Induct {name} : instrs) = do
  type_ <- get >>= \env -> lift $ inferType name env
  case type_ of
    ConT dtName -> do
      -- remove destructed target from environment
      modify $ deleteCtx name
      -- get datatype info
      dtInfo <- lift $ reifyDatatype dtName
      -- gen matches
      let dtConInfos = datatypeCons dtInfo
      let matches =
            ( \conInfo -> do
                -- collects newly bound variables with types, generates match's pattern
                (vars, pat) <- lift $ getConVarsPat conInfo
                -- add constructor's variables to `arg_rec_ctx` at `name`
                modify $ \env -> env {arg_rec_ctx = Map.insert name (Map.fromList vars) (arg_rec_ctx env)}
                -- adds constructor's introduced terms to environment
                modify $ flip (foldl (flip (uncurry insertCtx))) vars
                -- gen match
                e <- spliceExp instrs
                lift $ match (pure pat) (normalB $ pure e) []
            )
              <$> dtConInfos
      -- generate case
      ms <- sequence matches
      lift $ caseE (varE name) (pure <$> ms)
    _ -> fail $ "Cannot induct " ++ show name ++ " of non-datatype type " ++ show type_
spliceExp (Assert {exp} : instrs) = do
  e <- spliceExp instrs
  lift [|if $(pure exp) then $(pure e) else trivial|]
spliceExp (Use {exp} : instrs) = do
  e <- spliceExp instrs
  lift [|use $(pure exp) &&& $(pure e)|]
spliceExp (Trivial : instrs) = spliceExp instrs
spliceExp (Auto {hints, depth} : instrs) = do
  e <- useMany <$> genNeutrals Nothing depth
  e' <- spliceExp instrs
  lift [|$(pure e) &&& $(pure e')|]

spliceDec :: [Instr] -> Splice [Dec]
spliceDec instrs = do
  env <- get
  sig <- lift $ sigD (def_name env) (pure $ def_type env)
  e <- spliceExp instrs
  imp <- lift $ funD (def_name env) [clause [] (normalB $ pure e) []]
  pure [sig, imp]

getConVarsPat :: ConstructorInfo -> Q ([(Name, Type)], Pat)
getConVarsPat = undefined

type Goal = Maybe Type

type Gas = Int

genNeutrals :: Goal -> Gas -> Splice [Exp]
genNeutrals goal gas = undefined

useMany :: [Exp] -> Exp
useMany = undefined
