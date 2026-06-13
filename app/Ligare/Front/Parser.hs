module Ligare.Front.Parser where

import Data.List
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void
import Ligare.Core.Syntax

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

integer :: Parser Integer
integer = lexeme L.decimal

ident :: Parser String
ident = lexeme $ (:) <$> letterChar <*> many alphaNumChar

type Env = [String]

parseTerm :: Env -> Parser Term
parseTerm env = choice [parseLam env, parseApp env]

parseSimple :: Env -> Parser Term
parseSimple env = choice
  [ parseLam env
  , LitInt <$> integer
  , Var <$> parseVar env
  , parens (parseTerm env)
  ]

parseVar :: Env -> Parser Int
parseVar env = do
  name <- ident
  case elemIndex name env of
    Just i  -> pure i
    Nothing -> fail ("unbound variable: " ++ name)

parseLam :: Env -> Parser Term
parseLam env = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- ident
  _ <- symbol "."
  body <- parseTerm (x:env)
  pure (Lam body)

parseApp :: Env -> Parser Term
parseApp env = do
  t1 <- parseSimple env
  -- 贪心读取后续参数，形成左结合应用
  ts <- many (parseSimple env)
  pure $ foldl App t1 ts

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- 顶层入口
parseExpr :: String -> Either String Term
parseExpr input = case runParser (parseTerm []) "" input of
  Left e  -> Left (errorBundlePretty e)
  Right t -> Right t

