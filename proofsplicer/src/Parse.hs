{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}

module Parse where

import Control.Monad.Trans as Trans
import Data.Char as Char
import qualified Language.Haskell.Meta.Parse as MP
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (lift)
import Debug
import Syntax
import Utility
import qualified Text.Parsec as P
import Prelude hiding (exp)

type Parser a = P.ParsecT String () Q a

runParser :: Parser a -> String -> Q a
runParser p str =
  P.runParserT p () "SourceName" str >>= \case
    Left err -> fail $ show err
    Right a -> pure a

parseInstrs :: Parser [Instr]
parseInstrs =
  concat
    <$> P.sepBy
      parseInstr
      (parseSymbol ";")

parseInstr :: Parser [Instr]
parseInstr =
  P.choice . fmap P.try $
    [ -- Intro
      do
        parseSymbol "intro"
        name <- parseName
        pure [Intro {name}],
      -- Destruct
      do
        parseSymbol "destruct"
        name <- parseName
        pure [Destruct {name}],
      -- Induct
      do
        parseSymbol "induct"
        name <- parseName
        pure [Induct {name}],
      -- Auto
      do
        parseSymbol "auto"
        parseSymbol "["
        hints <- fmap nameToExp <$> P.sepBy parseName (parseSymbol ",")
        parseSymbol "]"
        depth <- parseInt
        pure [Auto {hints, depth}],
      -- Assert
      do
        parseSymbol "assert"
        exp <- parseExp
        pure [Assert {exp}],
      -- Use
      do
        parseSymbol "use"
        exp <- parseExp
        pure [Use {exp}],
      -- Trivial
      do
        parseSymbol "trivial"
        pure [Trivial],
      -- comment
      do
        P.spaces
        P.string "--"
        P.manyTill P.anyChar (P.try P.newline)
        pure []
    ]

parseDecInstrs :: Parser (Environment, [Instr])
parseDecInstrs = do
  -- sig
  P.spaces
  def_name <- parseName
  P.string "::"
  P.many $ P.char ' '
  def_type_string <- parseUntil parseNextIsNewline
  def_type <- fromMP $ MP.parseType def_type_string
  let (def_argTypes, _) = flattenType def_type
  -- imp
  _ <- parseName -- == def_name
  names <- P.many parseName
  parseSymbol "="
  instrs <- parseInstrs
  pure
    ( emptyEnvironment
        { def_name = def_name,
          def_type = def_type,
          def_argTypes = def_argTypes
        },
      ((\name -> Intro {name}) <$> names)
        ++ instrs
    )

fromMP :: Either String a -> Parser a
fromMP e = case e of
  Right a -> pure a
  Left msg -> fail $ "metaparse: " ++ msg

lexeme :: Parser a -> Parser a
lexeme p = do
  a <- p
  P.spaces
  pure a

parseSymbol :: String -> Parser String
parseSymbol = lexeme . P.string

-- characters allowed in ids
parseNameChar :: Parser Char
parseNameChar = P.alphaNum P.<|> P.oneOf "_'"

parseName :: Parser Name
parseName = lexeme do
  mkName <$> P.many1 parseNameChar

parseInt :: Parser Int
parseInt = lexeme do
  ds <- P.many1 P.digit
  pure $ read ds

parseExp :: Parser Exp
parseExp = do
  rest <- lookAheadRest
  -- debugM $ "parseExp: " ++ rest
  -- str <- P.between (parseSymbol "{") (parseSymbol "}") (P.many1 P.anyChar)
  parseSymbol "{"
  str <- P.manyTill P.anyChar (P.try (parseSymbol "}"))
  debugM $ "str: " ++ str
  fromMP (MP.parseExp str)

parseNextIsNewline :: Parser Bool
parseNextIsNewline = do
  c <- P.lookAhead P.anyChar
  pure $ c == '\n'

-- parses the string until `p` parses `True`
parseUntil :: Parser Bool -> Parser String
parseUntil p = lexeme go
  where
    go = do
      b <- P.lookAhead p
      if b
        then pure ""
        else do
          c <- P.anyChar
          (c :) <$> go

lookAheadRest :: Parser String
lookAheadRest = P.lookAhead (P.many P.anyChar)

nameToExp :: Name -> Exp
nameToExp name =
  case nameBase name of
    (c : s) ->
      if Char.isLower c
        then VarE name
        else ConE name
