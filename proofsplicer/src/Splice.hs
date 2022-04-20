{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--compile-spec" @-}

module Splice where

import Control.Monad
import Control.Monad.Trans as Trans
import Control.Monad.Trans.State as State
import Data.Char as Char
import Data.List as List
import qualified Data.Map as Map
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import qualified Language.Haskell.TH.Quote as Quote
import Language.Haskell.TH.Syntax hiding (lift)
import Proof
import Debug
import Syntax
import Utility
import Prelude hiding (exp)

_DUMP_AUTO = True

type Splice a = StateT Environment Q a

spliceExp :: [Instr] -> Splice Exp
spliceExp [] = lift [|trivial|]
spliceExp (Intro {name} : instrs) = do
  types <- gets def_argTypes
  i <- gets arg_i
  env <- get
  type_ <- case types `index` i of
    Just type_ -> do
      modify $ \env -> env {arg_i = 1 + arg_i env}
      pure type_
    Nothing -> fail $ "Cannot intro " ++ show name ++ " at non-function type"
  modify $ introArg name type_
  e <- spliceExp instrs
  lift [|\ $(varP name) -> $(pure e)|]
spliceExp (Destruct {name} : instrs) = do
  type_ <- get >>= lift . inferType (VarE name)
  case type_ of
    ConT dtName -> do
      -- remove destructed target from environment
      modify $ deleteCtx (VarE name)
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
                -- modify $ flip (foldl (flip (uncurry insertCtx))) vars
                modify $ flip (foldl (\env (e, type_) -> insertCtx e type_ env)) (fmap (\(n, t) -> (VarE n, t)) vars)
                -- gen match
                e <- spliceExp instrs
                lift $ match (pure pat) (normalB $ pure e) []
            )
              <$> dtConInfos
      -- generate case
      ms <- sequence matches
      lift $ caseE (varE name) (pure <$> ms)
    _ -> fail $ "Cannot destruct " ++ show name ++ " of non-datatype type " ++ show type_
spliceExp (Induct {name} : instrs) = do
  type_ <- get >>= \env -> lift $ inferType (VarE name) env
  case type_ of
    ConT dtName -> do
      -- remove destructed target from environment
      modify $ deleteCtx (VarE name)
      -- get datatype info
      dtInfo <- lift $ reifyDatatype dtName
      -- gen matches
      let dtConInfos = datatypeCons dtInfo
      let matches =
            ( \conInfo -> do
                -- collects newly bound variables with types, generates match's pattern
                (vars, pat) <- lift $ getConVarsPat conInfo
                -- add constructor's variables to `args_rec_ctx` at `name`
                arg_i <-
                  (List.elemIndex name <$> gets def_argNames) >>= \case
                    Just arg_i -> pure arg_i
                    Nothing -> fail $ "Cannot find argument index of argument " ++ show name
                modify $ \env -> env {args_rec_ctx = Map.insert arg_i (Map.fromList . fmap (\(n, t) -> (VarE n, t)) $ vars) (args_rec_ctx env)}
                -- adds constructor's introduced terms to environment
                modify $ flip (foldl (flip (uncurry insertCtx))) (fmap (\(n, t) -> (VarE n, t)) $ vars)
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
  do
    env <- get
    debugM $ "spliceExp.env: " ++ show env
  e <- do
    env <- get
    ctx' <- lift $ Map.fromList <$> mapM (\x -> (x,) <$> inferType x env) hints
    withStateT
      (\env -> env {ctx = Map.union ctx' (ctx env)})
      $ lift . useMany =<< genNeutrals Nothing depth
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
getConVarsPat conInfo = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  names <- mapM typeToTermName conFields
  let vars = (\(name, type_) -> (name, type_)) <$> zip names conFields
  let pat = ConP conName $ VarP <$> names
  pure (vars, pat)

type Goal = Maybe Type

type Gas = Int

genNeutrals :: Goal -> Gas -> Splice [Exp]
genNeutrals goal 0 = pure []
genNeutrals goal gas = do
  vars <- Map.toList <$> gets ctx
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>)
          <$> let (_, beta) = flattenType alpha
               in if matchesGoal beta goal
                    then genNeutrals' e alpha gas
                    else pure []
  es <- (<>) <$> foldM f [] vars <*> genRecursions goal gas
  debugM $ "genNeutrals.es: " ++ pprint es
  pure es

genNeutrals' :: Exp -> Type -> Gas -> StateT Environment Q [Exp]
genNeutrals' e type_ gas = do
  let (alphas, beta) = flattenType type_
  if List.null alphas
    then pure [e]
    else do
      argss <- fanout <$> traverse (\alpha -> genNeutrals (Just alpha) (gas - 1)) alphas
      let es = foldl AppE e <$> argss
      pure es

-- | generates any expressions directly from context (no applications) that have goal type
genAtomsFromCtx :: Ctx -> Type -> Splice [Exp]
genAtomsFromCtx ctx type_ = do
  let f :: [Exp] -> (Exp, Type) -> Splice [Exp]
      f es (e, alpha) =
        (es <>) <$> if alpha `compareTypes` type_ then pure [e] else pure []
  es <- foldM f [] (Map.toList ctx)
  pure es

genRecursions :: Goal -> Int -> Splice [Exp]
genRecursions goal gas = do
  canRecurse >>= \case
    True -> do
      r <- VarE <$> gets def_name
      rho <- gets def_type
      let (alphas, beta) = flattenType rho
      if matchesGoal beta goal
        then do
          if List.null alphas
            then fail "impossible: cannot recurse with 0 arguments"
            else do
              argss <-
                fanout
                  <$> traverse
                    ( \(arg_i, alpha) -> do
                        (Map.lookup arg_i <$> gets args_rec_ctx) >>= \case
                          Just rec_ctx -> genAtomsFromCtx rec_ctx alpha -- gen only vars from ctx
                          Nothing -> genNeutrals (Just alpha) (gas - 1) -- gen any neutral
                    )
                    (zip [0 .. length alphas] alphas)
              debugM $ "genRecursions.argss: " ++ pprint (foldl AppE r <$> argss)
              pure $ foldl AppE r <$> argss
        else pure []
    False -> pure []

canRecurse :: Splice Bool
canRecurse = not . Map.null <$> gets ctx

matchesGoal :: Type -> Goal -> Bool
matchesGoal type_ goal = maybe True (`compareTypes` type_) goal
