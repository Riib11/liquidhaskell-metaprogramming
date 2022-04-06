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
    Auto {hints :: [Exp], depth :: Int}
  | -- | asserts a boolean exp must be true
    Assert {exp :: Exp}
  | -- | use refinment of an exp
    Use {exp :: Exp}
  | -- | trivial
    Trivial
  deriving (Show)

type Ctx = Map Exp Type

data Environment = Environment
  { def_name :: Name,
    def_type :: Type,
    def_argTypes :: [Type],
    def_argNames :: [Name],
    arg_i :: Int,
    args_rec_ctx :: Map Int Ctx, -- recursive-allowed context for each arg
    ctx :: Ctx
  }
  deriving (Show)

introArg :: Name -> Type -> Environment -> Environment
introArg name type_ env =
  env
    { def_argNames = def_argNames env ++ [name],
      def_argTypes = def_argTypes env ++ [type_],
      ctx = Map.insert (VarE name) type_ $ ctx env
    }

insertCtx :: Exp -> Type -> Environment -> Environment
insertCtx e type_ env =
  env
    { ctx = Map.insert e type_ $ ctx env
    }

deleteCtx :: Exp -> Environment -> Environment
deleteCtx e env =
  env
    { ctx = Map.delete e $ ctx env
    }

emptyEnvironment :: Environment
emptyEnvironment =
  Environment
    { def_name = undefined,
      def_type = undefined,
      def_argTypes = [],
      def_argNames = [],
      arg_i = 0,
      args_rec_ctx = Map.empty,
      ctx = Map.empty
    }

inferType :: Exp -> Environment -> Q Type
inferType e env =
  case Map.lookup e (ctx env) of
    Just type_ -> pure type_
    Nothing -> case e of
      VarE name -> reifyType name
      ConE name -> reifyType name
