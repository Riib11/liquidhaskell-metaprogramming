{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core where

import Control.Monad
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
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
  | -- | only works on inductively-defined datatypes (e.g. not Int)
    Induct
      (Q Exp) -- target
      Name -- datatype
      Int -- #argument
      Core
  | Application (Q Exp) (Q Exp) Core
  | Auto Ctx Int Core
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

toCtx :: [(Q Exp, Q Type)] -> Q Ctx
toCtx ls = Map.fromList <$> mapM (uncurry pairM) ls

data Environment = Environment
  { ctx :: Ctx,
    -- | applicants available for each argument of a recursion.
    -- length is the same as the number of parameters of `mu`
    recCtxs :: [Maybe Ctx],
    mu :: (Exp, Type) -- recursive
  }

compileCoreE :: Environment -> Core -> Q Exp
compileCoreE env Trivial = [|trivial|]
compileCoreE env (Expression eQ core) = [|refinement $eQ &&& $(compileCoreE env core)|]
compileCoreE env (Branch cond core) = [|if $cond then $(compileCoreE env core) else $(compileCoreE env core)|]
compileCoreE env (Destruct eQ dtName core) = do
  -- remove destruction target from ctx
  e <- eQ
  let env1 = env {ctx = Map.delete e $ ctx env}
  -- get datatype info
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  -- gen matches
  let matchQs =
        fmap
          ( \conInfo -> do
              -- adds newly bound variables to ctx
              (ctx', pat) <- genConPat conInfo
              -- add constructor's introduced terms to environment context
              let env2 = env1 {ctx = ctx env <> ctx'}
              -- gen match
              match (pure pat) (normalB $ compileCoreE env2 core) []
          )
          dtConInfos
  -- generate case
  caseE (pure e) matchQs
compileCoreE env (Induct eQ dtName iArg core) = do
  -- remove induction target from ctx
  e <- eQ
  let env1 = env {ctx = Map.delete e $ ctx env}
  -- get datatype info
  dtInfo <- reifyDatatype dtName
  let dtConInfos = datatypeCons dtInfo
  -- gen matches
  let matchQs =
        fmap
          ( \conInfo -> do
              -- adds newly bound variables to ctx
              (ctx', pat) <- genConPat conInfo
              -- add constructor's introduced terms to recCtx at `iArg` (index of the inducted argument)
              let env2 = env1 {recCtxs = updateAtList iArg (Just ctx') (recCtxs env1)}
              -- add constructor's introduced terms to environment context
              let env3 = env2 {ctx = ctx env <> ctx'}
              -- gen match
              match (pure pat) (normalB $ compileCoreE env3 core) []
          )
          dtConInfos
  -- generate case
  caseE (pure e) matchQs
compileCoreE env (Application fQ aQ core) = [|refinement ($fQ $aQ) &&& $(compileCoreE env core)|]
compileCoreE env (Assertion bQ core) = [|if $bQ then $(compileCoreE env core) else trivial|]
compileCoreE env (Loop cond nexts aQ_init body gas) =
  let loop aQ gas =
        if gas == 0
          then [|trivial|]
          else
            let tail = foldl (\pQ aQ -> [|$(loop aQ (gas - 1)) &&& $pQ|]) [|trivial|] (nexts aQ)
             in [|if $(cond aQ) then trivial else $(compileCoreE env (body aQ)) &&& $tail|]
   in loop aQ_init gas
compileCoreE env (Block cores) = foldl (\pQ core -> [|$pQ &&& $(compileCoreE env core)|]) [|trivial|] cores
compileCoreE env (Auto ctx' gas core) =
  let env' = env {ctx = ctx env <> ctx'}
   in [|refinement $(forQs $ genNeutrals env' Nothing gas) &&& $(compileCoreE env' core)|]

type Goal = Maybe Type

matchesGoal :: Type -> Goal -> Bool
matchesGoal alpha goal = maybe True (== alpha) goal

-- | generate all neutral forms in environemnt that have type `goal`
genNeutrals :: Environment -> Goal -> Int -> Q [Exp]
genNeutrals env goal gas =
  if gas == 0
    then do
      -- pure $! unsafePerformIO $ print $ indent env <> "[out of gas]"
      pure []
    else foldM f [] (Map.toList $ ctx env) <> genRecursions env goal gas
  where
    f :: [Exp] -> (Exp, Type) -> Q [Exp]
    f es (e, alpha) =
      (es <>)
        <$> let (_, beta) = flattenType alpha
             in if matchesGoal beta goal
                  then genApplications env e alpha gas
                  else pure []

-- | checks if it is consistent to make a recursive call in this context,  check there exists at least one Just in recCtxs
canRecurse :: Environment -> Bool
canRecurse env = List.foldl (\b mb_ctx -> b || isJust mb_ctx) False (recCtxs env)

-- | generates
genRecursions :: Environment -> Goal -> Int -> Q [Exp]
genRecursions env goal gas =
  if canRecurse env
    then
      let (r, rho) = mu env
          (alphas, beta) = flattenType rho
       in if matchesGoal beta goal
            then
              if List.null alphas
                then error "impossible" -- must have at least one of the recCtxs be a Just
                else do
                  argss <-
                    fanout
                      <$> traverse
                        ( \(alpha, recCtx) ->
                            case recCtx of
                              Just ctx -> genVariables env ctx alpha -- gen only from ctx
                              Nothing -> genNeutrals env (Just alpha) (gas - 1) -- gen any neutral
                        )
                        (zip alphas (recCtxs env))
                  let es = (foldl AppE r) <$> argss
                  -- pure $! unsafePerformIO $ print $ indent env <> "[gen recs] " <> List.intercalate ", " (pprint <$> es)
                  pure es
            else pure []
    else pure []

-- | generate all (full) applications of `e : alpha`
genApplications :: Environment -> Exp -> Type -> Int -> Q [Exp]
genApplications env e alpha gas =
  let (alphas, beta) = flattenType alpha
   in if List.null alphas
        then do
          pure [e]
        else do
          argss <- fanout <$> traverse (\alpha -> genNeutrals env alpha (gas - 1)) (Just <$> alphas)
          let es = (foldl AppE e) <$> argss
          if not $ List.null es
            then do
              -- pure $! unsafePerformIO $ print $ indent env <> "[gen apps] " <> List.intercalate ", " (pprint <$> es)
              pure es
            else pure es

-- | generates any expressions directly from context (no applications) that have goal type
genVariables :: Environment -> Ctx -> Type -> Q [Exp]
genVariables env ctx goal = do
  es <- foldM f [] (Map.toList ctx)
  -- pure $! unsafePerformIO $ print $ indent env <> "[gen vars] " <> List.intercalate ", " (pprint <$> es)
  pure es
  where
    f :: [Exp] -> (Exp, Type) -> Q [Exp]
    f es (e, alpha) =
      (es <>) <$> if alpha == goal then pure [e] else pure []

-- | for each list of the output, the ith element is from the ith list of the input.
-- all lists must be of the same length.
-- example: [ [x1, x2], [y1, y2] ] ==> [ [x1, y1], [x1, y2], [x2, y1], [x2, y2] ]
fanout :: [[a]] -> [[a]]
fanout [] = []
fanout (xs : []) = [[a] | a <- xs]
fanout (xs : xss) = [a' : xs' | a' <- xs, xs' <- fanout xss]

conjunctionQ :: Q [Exp] -> Q Exp
conjunctionQ eQs = do
  es <- eQs
  foldl (\eQ' e -> [|refinement $eQ' &&& $(pure e)|]) [|trivial|] es

forQs :: Q [Exp] -> Q Exp
forQs eQs = do
  es <- eQs
  foldl (\eQ' e -> [|$eQ' `for` $(pure e)|]) [|trivial|] es

-- | flattens a type of the form `alpha1 -> ... -> alphaN -> beta`
-- into the form `([alpha1, ..., alphaN], beta)`.
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

-- generates context with constructor's introduced terms, and constructor's pattern
genConPat :: ConstructorInfo -> Q (Ctx, Pat)
genConPat conInfo = do
  let conName = constructorName conInfo
  let conFields = constructorFields conInfo
  names <- mapM (\type_ -> newName "x") conFields
  let ctx = Map.fromList $ fmap (\(name, type_) -> (VarE name, type_)) (zip names conFields)
  let pat = ConP conName $ VarP <$> names
  pure (ctx, pat)

mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex f = go 0
  where
    go _ [] = []
    go i (x : xs) = f i x : go (i + 1) xs

traverseWithIndex :: Monad m => (Int -> a -> m b) -> [a] -> m [b]
traverseWithIndex k = go 0
  where
    go _ [] = pure []
    go i (x : xs) = (:) <$> k i x <*> go (i + 1) xs

updateAtList :: Int -> a -> [a] -> [a]
updateAtList _ _ [] = []
updateAtList 0 x' (x : xs) = x' : xs
updateAtList i x' (_ : xs) = updateAtList (i - 1) x' xs

pairM :: Applicative m => m a -> m b -> m (a, b)
pairM ma mb = (,) <$> ma <*> mb
