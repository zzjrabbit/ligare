module Ligare.Front.Parser where

import Control.Monad.Combinators.Expr (Operator (InfixL, InfixN), makeExprParser)
import Data.List (elemIndex)
import Data.Void (Void)
import Ligare.Core.Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keyword :: String -> Parser String
keyword s = sc >> string s <* sc

integer :: Parser Integer
integer = lexeme L.decimal

keywords :: [String]
keywords = ["let", "in", "if", "then", "else", "true", "false"]

ident :: Parser String
ident = lexeme $ do
  name <- (:) <$> letterChar <*> many alphaNumChar
  if name `elem` keywords
    then empty
    else pure name

type Env = [String]

parseExprTop :: String -> Either String Term
parseExprTop input = case runParser (sc >> parseExpr []) "" input of
  Left e -> Left (errorBundlePretty e)
  Right t -> Right t

parseExpr :: Env -> Parser Term
parseExpr env = parseIfExpr env <|> parseNonIfExpr env

parseNonIfExpr :: Env -> Parser Term
parseNonIfExpr env = makeExprParser (parseApp env) operators

parseIfExpr :: Env -> Parser Term
parseIfExpr env = do
  try (keyword "if")
  cond <- parseExpr env
  try (keyword "then")
  tbranch <- parseExpr env
  try (keyword "else")
  fbranch <- parseExpr env
  pure (IfThenElse cond tbranch fbranch)

parseApp :: Env -> Parser Term
parseApp env =
  parseLetExpr env <|> do
    t1 <- parseTerm env
    ts <- many (parseTerm env)
    return (foldl App t1 ts)

parseLetExpr :: Env -> Parser Term
parseLetExpr env = do
  try (keyword "let")
  name <- ident
  mconstr <- optional $ do
    _ <- symbol ":"
    parseConstraint
  _ <- symbol "="
  val <- parseExpr env
  _ <- keyword "in"
  body <- parseExpr (name : env)
  pure (Let name val body mconstr)

parseTerm :: Env -> Parser Term
parseTerm env =
  choice
    [ try (LitInt <$> integer),
      try (LitBool <$> parseBool),
      try (Var <$> parseVar env),
      parseLam env,
      parens (parseExpr env)
    ]

parseVar :: Env -> Parser Int
parseVar env = do
  name <- ident
  case elemIndex name env of
    Just i -> pure i
    Nothing -> fail ("unbound variable: " ++ name)

parseLam :: Env -> Parser Term
parseLam env = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- ident
  _ <- symbol "."
  body <- parseExpr (x : env)
  pure (Lam body)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

parseBool :: Parser Bool
parseBool =
  choice
    [ True <$ string "true",
      False <$ string "false"
    ]

binary :: PrimOp -> Term -> Term -> Term
binary op left right = App (App (PrimOp op) left) right

operators :: [[Operator Parser Term]]
operators =
  [ [ InfixL (binary Mul <$ symbol "*"),
      InfixL (binary Div <$ symbol "/"),
      InfixL (binary Mod <$ symbol "%")
    ],
    [ InfixL (binary Add <$ symbol "+"),
      InfixL (binary Sub <$ symbol "-")
    ],
    [ InfixN (binary Eq <$ symbol "=="),
      InfixN (binary Lt <$ symbol "<"),
      InfixN (binary Gt <$ symbol ">"),
      InfixN (binary Le <$ symbol "<="),
      InfixN (binary Ge <$ symbol ">="),
      InfixN (binary Neq <$ symbol "/=")
    ]
  ]

parseConstraintFromString :: String -> Either String Term
parseConstraintFromString input =
  case runParser parseConstraint "" input of
    Left e -> Left (errorBundlePretty e)
    Right t -> Right t

parseConstraint :: Parser Term
parseConstraint = sc >> parseArrow

parseArrow :: Parser Term
parseArrow = do
  left <- parseConstraintAtom
  rest left
  where
    rest left = do
      sc
      hasArrow <- optional (symbol "->")
      case hasArrow of
        Nothing -> return left
        Just _ -> do
          right <- parseArrow
          return (Arrow left right)

parseConstraintAtom :: Parser Term
parseConstraintAtom =
  choice
    [ try (Builtin <$> string "int") <* notFollowedBy alphaNumChar,
      try (Builtin <$> string "bool") <* notFollowedBy alphaNumChar,
      Universe UData <$ string "data",
      parens parseConstraint
    ]
