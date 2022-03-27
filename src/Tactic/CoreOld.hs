{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.CoreOld where

import Control.Monad
import qualified Data.List as List
import Data.Map hiding (foldl, null)
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Proof
import System.IO.Unsafe (unsafePerformIO)

nameE :: String -> Q Exp
nameE = pure . VarE . mkName

data Core
  = Expression (Q Exp) Core
  | Branch (Q Exp) Core
  | Destruct
      Name -- target
      Name -- datatype
      Core
  | Induct
      Name -- target
      Name -- datatype
      Int -- #argument
      Core
  | Application (Q Exp) (Q Exp) Core
  | Auto Core
  | Assertion (Q Exp) Core
  | Loop
      (Q Exp -> Q Exp) -- cond
      (Q Exp -> [Q Exp]) -- nexts
      (Q Exp) -- aQ_init
      (Q Exp -> Core) -- body
      Int -- gas
  | Block [Core]
  | Trivial

buildCore :: [Core -> Core] -> Core
buildCore ks = foldl (.) id ks Trivial

-- data PreEnvironment = PreEnvironment
--   { pre_vars :: [Name],
--     pre_mu :: (Name, Q Type), -- recursive
--     pre_gas :: Int
--   }

data Environment = Environment
  { vars :: Map Name Type,
    constrs :: Map Name Type,
    inds :: Map Name (Name, Int), -- induction targets: xName => dtName, #argument
    mu :: (Name, Type), -- recursive
    gas :: Int
  }

-- reifyEnvironment :: PreEnvironment -> Q Environment
-- reifyEnvironment pre_env = do
--   vars <- fromList <$> mapM (\name -> (name,) <$> reifyType name) (pre_vars pre_env)
--   let inds = mempty
--   let mu_name = fst (pre_mu pre_env)
--   mu_typ <- snd (pre_mu pre_env)
--   let mu = (mu_name, mu_typ)
--   let gas = pre_gas pre_env
--   pure $ Environment {vars, inds, mu, gas}

-- compileCoreE' :: Core -> PreEnvironment -> Q Exp
-- compileCoreE' core pre_env = compileCoreE core =<< reifyEnvironment pre_env

compileCoreE :: Core -> Environment -> Q Exp
compileCoreE Trivial env = [|trivial|]
compileCoreE (Expression eQ core) env = [|$eQ `by` $(compileCoreE core env)|]
compileCoreE (Branch cond core) env = [|if $cond then $(compileCoreE core env) else $(compileCoreE core env)|]
compileCoreE (Destruct x dtName core) env = do
  -- -- remove destruction target from vars
  -- let env1 = env {vars = delete x $ vars env}
  -- -- get datatype info
  -- dtInfo <- reifyDatatype dtName
  -- let dtConInfos = datatypeCons dtInfo
  -- -- generate matches
  -- let matchQs =
  --       fmap
  --         ( \conInfo -> do
  --             -- adds newly bound variables to context
  --             (vars', pat) <- genConPat conInfo
  --             match (pure pat) (normalB (compileCoreE core (env {vars = vars env <> vars'}))) []
  --         )
  --         dtConInfos
  -- -- generate cases
  -- caseE (pure $ VarE x) matchQs
  undefined
compileCoreE (Induct x dtName iArg core) env = do
  -- remove induction target from vars
  let env1 = env {vars = delete x $ vars env}
  -- add induction target to inds
  let env2 = env {inds = insert x (dtName, iArg) $ inds env}
  -- get datatype info
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  -- generate matches
  let matchQs =
        fmap
          ( \conInfo -> do
              -- adds newly bound variables to vars
              (vars', pat) <- genConPat conInfo
              let env3 = env {vars = vars env <> vars'}
              match (pure pat) (normalB $ compileCoreE core env3) []
          )
          dtConInfos
  -- generate cases
  caseE (pure $ VarE x) matchQs
compileCoreE (Application fQ aQ core) env = [|$fQ $aQ `by` $(compileCoreE core env)|]
compileCoreE (Assertion bQ core) env = [|if $bQ then $(compileCoreE core env) else trivial|]
compileCoreE (Loop cond nexts aQ_init body gas) env =
  let loop aQ gas =
        if gas == 0
          then [|trivial|]
          else
            let tail = foldl (\pQ aQ -> [|$(loop aQ (gas - 1)) &&& $pQ|]) [|trivial|] (nexts aQ)
             in [|if $(cond aQ) then trivial else $(compileCoreE (body aQ) env) &&& $tail|]
   in loop aQ_init gas
compileCoreE (Block cores) env = foldl (\pQ core -> [|$pQ &&& $(compileCoreE core env)|]) [|trivial|] cores
compileCoreE (Auto core) env = [|$(forQs $ genAllNeutrals env) `by` $(compileCoreE core env)|]

-- | generate all neutral forms in environement
genAllNeutrals :: Environment -> Q [Exp]
genAllNeutrals env = foldM f [] (toList $ vars env)
  where
    f :: [Exp] -> (Name, Type) -> Q [Exp]
    f es var = do
      (es <>) <$> genNeutrals env var

-- | generate all neutral forms in environemnt that have type `goal`
genAllNeutralsOfType :: Environment -> Type -> Q [Exp]
genAllNeutralsOfType env goal = foldM f [] (toList $ vars env)
  where
    f :: [Exp] -> (Name, Type) -> Q [Exp]
    f es var@(x, alpha) =
      let (_, beta) = flattenType alpha
       in -- only generate neutrals that have type `goal`
          if beta == goal
            then genNeutrals env var
            else pure []

-- | generate all neutral forms with applicant `x` of type `alpha`
genNeutrals :: Environment -> (Name, Type) -> Q [Exp]
genNeutrals env (x, alpha) =
  if gas env == 0
    then do
      pure $! unsafePerformIO $ print $ indent env <> "[out of gas]  " <> pprint (VarE x) <> " : " <> pprint alpha
      pure []
    else
      let (alphas, beta) = flattenType alpha
       in if null alphas
            then do
              -- pure $! unsafePerformIO $ print $ indent env <> "[genNeutrals]  " <> pprint (VarE x) <> " : " <> pprint alpha
              -- pure $! unsafePerformIO $ print $ indent env <> "==> " <> concatMap pprint [VarE x]
              pure [VarE x]
            else
              if x == fst (mu env)
                then -- recursive call
                do
                  let ialphas = mapWithIndex (,) alphas
                  ass <-
                    traverse
                      ( \(i, alpha) ->
                          let env' =
                                foldl
                                  ( \env (constrName, (dtName, i')) ->
                                      if i == i'
                                        then -- remove constructor from constrs
                                          env {constrs = delete constrName (constrs env)}
                                        else env
                                  )
                                  env
                                  (toList $ inds env)
                           in genAllNeutralsOfType env' {gas = gas env - 1} alpha
                      )
                      ialphas
                  let assRot = rotate ass
                  es <- traverse (\as -> pure $ foldl AppE (VarE x) as) assRot
                  pure es
                else -- nonrecursive call
                do
                  -- pure $! unsafePerformIO $ print $ indent env <> "[genNeutrals]  " <> pprint (VarE x) <> " : " <> pprint alpha
                  ass <- traverse (genAllNeutralsOfType env {gas = gas env - 1}) alphas
                  -- pure $! unsafePerformIO $ print $ indent env <> "ass    " <> List.intercalate ", " (pprint <$> ass)
                  let assRot = rotate ass
                  -- pure $! unsafePerformIO $ print $ indent env <> "assRot " <> List.intercalate ", " (pprint <$> assRot)
                  es <- traverse (\as -> pure $ foldl AppE (VarE x) as) assRot
                  -- pure $! unsafePerformIO $ print $ indent env <> "==> " <> concatMap pprint es
                  pure es

indent :: Environment -> String
indent env = replicate (5 - gas env) ' '

-- is this an actualy rotation?
-- [ [x1, x2], [y1, y2] ] ==> [ [x1, y1], [x1, y2], [x2, y1], [x2, y2] ]
rotate :: [[a]] -> [[a]]
rotate [] = []
rotate (xs : []) = [[x] | x <- xs]
rotate (xs : xss) = [x' : xs' | x' <- xs, xs' <- rotate xss]

byQs :: Q [Exp] -> Q Exp
byQs eQs = do
  es <- eQs
  foldl (\eQ' e -> [|$eQ' `by` $(pure e)|]) [|trivial|] es

forQs :: Q [Exp] -> Q Exp
forQs eQs = do
  es <- eQs
  foldl (\eQ' e -> [|$eQ' `for` $(pure e)|]) [|trivial|] es

-- | flattens a type of the form `alpha1 -> ... -> alphaN -> beta`
-- into the form `([alpha1, ..., alphaN], beta)
flattenType :: Type -> ([Type], Type)
flattenType (AppT (AppT ArrowT alpha) beta) =
  let (alphas, delta) = flattenType beta
   in (alpha : alphas, delta)
flattenType alpha = ([], alpha)

flatten :: [[a]] -> [a]
flatten = foldMap id

genConPat :: ConstructorInfo -> Q (Map Name Type, Pat)
genConPat conInfo = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  ctx <- fromList <$> mapM (\type_ -> do name <- newName "x"; pure (name, type_)) conFields
  pat <- conP conName (fmap (varP . fst) (toList ctx))
  pure (ctx, pat)

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = go 0
  where
    go _ [] = []
    go i (x : xs) = f i x : go (i + 1) xs
