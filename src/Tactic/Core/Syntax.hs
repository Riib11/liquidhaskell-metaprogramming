{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Tactic.Core.Syntax where

import Data.Map as Map
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax

data Instr
  = -- | splices a lambda; adds name to environment
    Intro {name :: Name}
  | -- | destructs a datatype
    Destruct {name :: Name}
  | -- | inducts on an input argument
    Induct {name :: Name}
  | -- | auto
    Auto {hints :: [Name], depth :: Int}
  | -- | asserts a boolean exp must be true
    Assert {exp :: Exp}
  | -- | use refinment of an exp
    Use {exp :: Exp}
  | -- | trivial
    Trivial
  deriving (Show)

type Ctx = Map Name Type

data Environment = Environment
  { def_name :: Name,
    def_type :: Type,
    def_argTypes :: [Type],
    def_argNames :: [Name],
    goal_arg_i :: Int,
    arg_rec_ctx :: Map Name Ctx, -- recursive-allowed context for each arg
    ctx :: Ctx
  }
  deriving (Show)

introArg :: Name -> Type -> Environment -> Environment
introArg = undefined

insertCtx :: Name -> Type -> Environment -> Environment
insertCtx = undefined

deleteCtx :: Name -> Environment -> Environment
deleteCtx = undefined

emptyEnvironment :: Environment
emptyEnvironment = undefined

inferType :: Name -> Environment -> Q Type
inferType name env =
  case Map.lookup name (ctx env) of
    Just type_ -> pure type_
    Nothing -> reifyType name
