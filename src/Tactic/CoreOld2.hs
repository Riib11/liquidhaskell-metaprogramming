{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.CoreOld2 where

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
      (Q Exp) -- target
      Name -- datatype
      Core
  | Induct
      (Q Exp) -- target
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

type Ctx = Map Exp Type

data Environment = Environment
  { ctx :: Ctx,
    inds :: [(Name, Int)], -- inducted arguments: [(dtName, #argument)]
    mu :: (Exp, Type), -- recursive
    gas :: Int
  }

compileCoreE :: Core -> Environment -> Q Exp
compileCoreE Trivial env = [|trivial|]
compileCoreE (Expression eQ core) env = [|$eQ `by` $(compileCoreE core env)|]
compileCoreE (Branch cond core) env = [|if $cond then $(compileCoreE core env) else $(compileCoreE core env)|]
compileCoreE (Induct eQ dtName iArg core) env = do
  -- remove induction target from ctx
  e <- eQ
  let env1 = env {ctx = delete e $ ctx env}
  -- add induction target to inds
  let env2 = env {inds = (dtName, iArg) : inds env}
  -- get datatype info
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  -- generate matches
  let matchQs =
        fmap
          ( \conInfo -> do
              -- adds newly bound variables to ctx
              (ctx', pat) <- genConPat conInfo
              let env3 = env {ctx = ctx env <> ctx'}
              match (pure pat) (normalB $ compileCoreE core env3) []
          )
          dtConInfos
  -- generate cases
  caseE (pure e) matchQs
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
genAllNeutrals env = foldM f [] (toList $ ctx env)
  where
    f :: [Exp] -> (Exp, Type) -> Q [Exp]
    f es (e, alpha) = do
      (es <>) <$> genNeutrals env e alpha

-- | generate all neutral forms in environemnt that have type `goal`
genAllNeutralsOfType :: Environment -> Type -> Q [Exp]
genAllNeutralsOfType env goal = foldM f [] (toList $ ctx env)
  where
    f :: [Exp] -> (Exp, Type) -> Q [Exp]
    f es (e, alpha) =
      let (_, beta) = flattenType alpha
       in -- only generate neutrals that have type `goal`
          if beta == goal
            then genNeutrals env e alpha
            else pure []

-- | generate all neutral forms with applicant `e` of type `alpha`
genNeutrals :: Environment -> Exp -> Type -> Q [Exp]
genNeutrals env e alpha =
  if gas env == 0
    then do
      pure $! unsafePerformIO $ print $ indent env <> "[out of gas]  " <> pprint e <> " : " <> pprint alpha
      pure []
    else
      let (alphas, beta) = flattenType alpha
       in if null alphas
            then do
              -- pure $! unsafePerformIO $ print $ indent env <> "[genNeutrals]  " <> pprint e <> " : " <> pprint alpha
              pure $! unsafePerformIO $ print $ indent env <> "==> " <> pprint e
              pure [e]
            else
              if e == fst (mu env)
                then -- recursive call
                do
                  let ialphas = mapWithIndex (,) alphas
                  ass <-
                    traverse
                      ( \(i, alpha) -> do
                          env' <- do
                            foldM
                              ( \env (dtName, i') ->
                                  if i == i'
                                    then do
                                      -- remove all constructors from ctx
                                      dtInfo <- reifyDatatype dtName
                                      let conInfos = datatypeCons dtInfo
                                      let conNames = constructorName <$> conInfos
                                      pure $ foldl (\env conName -> env {ctx = delete (VarE conName) $ ctx env}) env conNames
                                    else pure env
                              )
                              env
                              (inds env)
                          genAllNeutralsOfType env' {gas = gas env - 1} alpha
                      )
                      ialphas
                  let assRot = rotate ass
                  es <- traverse (\as -> pure $ foldl AppE e as) assRot
                  pure es
                else -- nonrecursive call
                do
                  -- pure $! unsafePerformIO $ print $ indent env <> "[genNeutrals]  " <> pprint e <> " : " <> pprint alpha
                  let env' = env {gas = gas env - 1}
                  ass <- traverse (genAllNeutralsOfType env') alphas
                  let assRot = rotate ass
                  es <- traverse (\as -> pure $ foldl AppE e as) assRot
                  pure $! unsafePerformIO $ print $ indent env <> "==> " <> List.intercalate ", " (pprint <$> es)
                  pure es

indent :: Environment -> String
indent env = replicate (10 - gas env) ' '

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

unArrowType :: Type -> Maybe (Type, Type)
unArrowType (AppT (AppT ArrowT alpha) beta) = Just (alpha, beta)
unArrowType _ = Nothing

flatten :: [[a]] -> [a]
flatten = foldMap id

genConPat :: ConstructorInfo -> Q (Ctx, Pat)
genConPat conInfo = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  names <- mapM (\type_ -> newName "x") conFields
  let ctx = fromList $ fmap (\(name, type_) -> (VarE name, type_)) (zip names conFields)
  let pat = ConP conName $ VarP <$> names
  pure (ctx, pat)

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = go 0
  where
    go _ [] = []
    go i (x : xs) = f i x : go (i + 1) xs
