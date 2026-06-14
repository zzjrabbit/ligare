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

integer :: Parser Integer
integer = lexeme L.decimal

keywords :: [String]
keywords = ["let", "in", "if", "then", "else", "true", "false", "by"]

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
  _ <- try (sc >> symbol "if")
  cond <- parseExpr env
  _ <- try (sc >> symbol "then")
  tbranch <- parseExpr env
  _ <- try (sc >> symbol "else")
  fbranch <- parseExpr env
  pure (IfThenElse cond tbranch fbranch)

parseApp :: Env -> Parser Term
parseApp env =
  parseLetExpr env <|> parseFuncExpr env <|> do
    t1 <- parseTerm env
    ts <- many (parseTerm env)
    return (foldl App t1 ts)

parseLetExpr :: Env -> Parser Term
parseLetExpr env = do
  _ <- try (sc >> symbol "let")
  name <- ident
  mconstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- sc >> symbol "="
  val <- parseExpr env
  mproof <- optional $ try (sc >> symbol "by" >> parseTerm env)
  _ <- sc >> symbol "in"
  let val' = case mproof of
        Just p  -> ByProof val p
        Nothing -> val
  body <- parseExpr (name : env)
  pure (Let name val' body mconstr)

parseFuncExpr :: Env -> Parser Term
parseFuncExpr env = do
  _ <- try (sc >> symbol "func")
  fname <- ident
  params <- many parseCurriedParam
  mRetConstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- sc >> symbol "="
  let paramNames = map fst params
  let extendedEnv = reverse paramNames ++ env
  body <- parseExpr extendedEnv
  pure (Func fname params mRetConstr [] [] body)

parseCurriedParam :: Parser (String, Maybe Term)
parseCurriedParam = do
  _ <- sc >> symbol "("
  pname <- ident
  mconstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- symbol ")"
  pure (pname, mconstr)

parseAtom :: Env -> Parser Term
parseAtom env =
  choice
    [ try (LitInt <$> integer),
      try (LitBool <$> parseBool),
      try (Var <$> parseVar env),
      parseBuiltinProp,
      parseLam env,
      parseNeg env,
      parens (parseExpr env)
    ]

parseBuiltinProp :: Parser Term
parseBuiltinProp =
  choice
    [ Builtin "and" <$ symbol "∧"
    , Builtin "or"  <$ symbol "∨"
    , Builtin "not" <$ symbol "¬"
    , Builtin "implies" <$ symbol "→"
    ]

parseNeg :: Env -> Parser Term
parseNeg env = do
  _ <- symbol "-"
  t <- parseAtom env
  pure (App (App (PrimOp Sub) (LitInt 0)) t)

parseTermWithSuffix :: Env -> Parser Term
parseTermWithSuffix env = do
  t <- parseAtom env
  suffix t
  where
    suffix t =
      (parseAnnotSuffix t >>= suffix)
        <|> pure t
    parseAnnotSuffix t = do
      _ <- try (sc >> symbol ":")
      c <- parseConstraint
      pure (Annot t c)

parseTerm :: Env -> Parser Term
parseTerm env = parseTermWithSuffix env

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
    [ try (True <$ (optional sc >> string "true")),
      try (False <$ (optional sc >> string "false"))
    ]

binary :: PrimOp -> Term -> Term -> Term
binary op left right = App (App (PrimOp op) left) right

operators :: [[Operator Parser Term]]
operators =
  [ [ InfixL (try (binary Mul <$ symbol "*")),
      InfixL (try (binary Div <$ symbol "/")),
      InfixL (try (binary Mod <$ symbol "%"))
    ],
    [ InfixL (try (binary Add <$ symbol "+")),
      InfixL (try (binary Sub <$ symbol "-"))
    ],
    [ InfixN (try (binary Eq <$ symbol "==")),
      InfixN (try (binary Le <$ symbol "<=")),
      InfixN (try (binary Ge <$ symbol ">=")),
      InfixN (try (binary Neq <$ symbol "/=")),
      InfixN (try (binary Lt <$ symbol "<")),
      InfixN (try (binary Gt <$ symbol ">"))
    ]
  ]

parseConstraintFromString :: String -> Either String Term
parseConstraintFromString input =
  case runParser parseConstraint "" input of
    Left e -> Left (errorBundlePretty e)
    Right t -> Right t

parseConstraint :: Parser Term
parseConstraint = sc >> parseAppConstraint

parseAppConstraint :: Parser Term
parseAppConstraint = do
  t1 <- parseArrow
  ts <- many parseArrow
  return (foldl App t1 ts)

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
          return (Pi "" left right)

parseConstraintAtom :: Parser Term
parseConstraintAtom =
  choice
    [ try (Builtin <$> string "int") <* notFollowedBy alphaNumChar,
      try (Builtin <$> string "bool") <* notFollowedBy alphaNumChar,
      Universe UData <$ string "data",
      Universe UTheorem <$ string "theorem",
      parseBuiltinProp,
      parseDepArrow,
      parens parseConstraint,
      Builtin <$> ident
    ]

parseDepArrow :: Parser Term
parseDepArrow = do
  _ <- symbol "("
  x <- ident
  _ <- sc >> symbol ":"
  a <- parseConstraint
  _ <- symbol ")"
  _ <- sc >> symbol "->"
  b <- parseExpr [x]
  pure (Pi x a b)

parseRefineTop :: String -> Either String (Name, Term, Term)
parseRefineTop input = case runParser (sc >> parseRefineDef) "" input of
  Left e -> Left (errorBundlePretty e)
  Right t -> Right t

parseRefineDef :: Parser (Name, Term, Term)
parseRefineDef = do
  name <- ident
  _ <- symbol "="
  parent <- parseConstraintAtom
  _ <- sc
  _ <- symbol "("
  paramName <- ident
  _ <- sc >> symbol "=>"
  predicate <- parseExpr [paramName]
  _ <- symbol ")"
  pure (name, parent, replaceVarZero predicate)
  where
    replaceVarZero (Var 0) = RefParam
    replaceVarZero (App f a) = App (replaceVarZero f) (replaceVarZero a)
    replaceVarZero (Lam body) = Lam (replaceVarZero body)
    replaceVarZero (Let n v b mc) = Let n (replaceVarZero v) (replaceVarZero b) (fmap replaceVarZero mc)
    replaceVarZero (IfThenElse c t f) = IfThenElse (replaceVarZero c) (replaceVarZero t) (replaceVarZero f)
    replaceVarZero (Annot t c) = Annot (replaceVarZero t) (replaceVarZero c)
    replaceVarZero (ByProof t p) = ByProof (replaceVarZero t) (replaceVarZero p)
    replaceVarZero other = other
