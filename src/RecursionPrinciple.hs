{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module RecursionPrinciple where

import qualified Data.Char as Char
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import System.IO.Unsafe

{-
Uses TH to derive the primitive recursion principle for a datatype.
Restrictions:
- datatype has no type variables
- cannot be recursive?? actually that might actually still work
-}

unqualifiedString :: Name -> String
unqualifiedString (Name occName _) = occString occName

makeRecursionPrinciple :: Name -> DecsQ
makeRecursionPrinciple datatypeName = do
  datatypeInfo <- reifyDatatype datatypeName

  case datatypeVariant datatypeInfo of
    Datatype -> pure ()
    _ -> fail "Only basic Datatype is supported."

  let vars = datatypeVars datatypeInfo
  let instTypes = datatypeInstTypes datatypeInfo
  let constructors = datatypeCons datatypeInfo
  let con = ConT datatypeName
  let recName = mkName $ "rec" ++ unqualifiedString datatypeName
  sig <-
    do
      let args = flip fmap vars $
            \case
              PlainTV name _ -> VarT name
              KindedTV name _ _ -> VarT name

      alpha <- VarT <$> newName "a"

      let input = foldl AppT con args

      SigD
        recName
        <$> arrowT_N
          ( map
              ( \constructor ->
                  let params = constructorFields constructor
                   in arrowT_N (map pure params) (pure alpha)
              )
              constructors
          )
          [t|$(pure input) -> $(pure alpha)|]
  imp <- do
    -- recs
    recsNames <-
      mapM
        (\constructor -> newName $ "rec" ++ unqualifiedString (constructorName constructor))
        constructors
    let recsExps = map VarE recsNames
    -- arg
    argName <- newName $ toLower (unqualifiedString datatypeName)
    let arg = VarE argName

    -- pats
    let pats :: [Pat]
        pats = map VarP (recsNames <> [argName])

    -- matches
    matches <-
      mapM
        ( \(recExp, constructor) -> do
            let consName = constructorName constructor
            let consParams = constructorFields constructor
            names <- mapM (\_ -> newName "x") consParams
            let pat = ConP consName $ map VarP names
            -- apply the correct recursor to arguments
            let body =
                  if length consParams == 0
                    then recExp
                    else foldl AppE recExp (VarE <$> names)
            return $ Match pat (NormalB body) []
        )
        (zip recsExps constructors)

    -- body
    let body = CaseE arg matches

    let clause = Clause pats (NormalB body) []
    return $ FunD recName [clause]

  return [sig, imp]

arrowT_N :: [Q Type] -> Q Type -> Q Type
arrowT_N [] output = output
arrowT_N (param : params) output = [t|$param -> $(arrowT_N params output)|]

--  [t|$param -> $(arrowT_N params output)|]

toLower :: String -> String
toLower "" = ""
toLower (c : s) = Char.toLower c : s
