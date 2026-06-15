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
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keywords :: [String]
keywords = ["let", "in", "if", "then", "else", "true", "false", "by", "func", "where"]

kw :: String -> Parser String
kw s = sc >> symbol s

ident :: Parser String
ident = lexeme $ do
  name <- (:) <$> letterChar <*> many alphaNumChar
  if name `elem` keywords
    then empty
    else pure name

type Env = [String]

--------------- top-level

parseExprTop :: String -> Either String Term
parseExprTop input =
  case runParser (sc >> parseExpr []) "" input of
    Left e -> Left (errorBundlePretty e)
    Right t -> Right t

parseDefTop :: String -> Either String (Name, Term)
parseDefTop input =
  case runParser (sc >> parseDef) "" input of
    Left e -> Left (errorBundlePretty e)
    Right t -> Right t

parseConstraintFromString :: String -> Either String Term
parseConstraintFromString input =
  case runParser parseConstraint "" input of
    Left e -> Left (errorBundlePretty e)
    Right t -> Right t

--------------- expressions

parseExpr :: Env -> Parser Term
parseExpr env = parseIfExpr env <|> parseOperators env

parseIfExpr :: Env -> Parser Term
parseIfExpr env = do
  _ <- try (kw "if")
  cond <- parseExpr env
  _ <- try (kw "then")
  tbranch <- parseExpr env
  _ <- try (kw "else")
  fbranch <- parseExpr env
  pure (IfThenElse cond tbranch fbranch)

parseOperators :: Env -> Parser Term
parseOperators env = makeExprParser (parseApp env) opTable

parseApp :: Env -> Parser Term
parseApp env =
  parseLetExpr env
    <|> parseFuncExpr env
    <|> try parseRefineTerm
    <|> do
      t1 <- parseTerm env
      ts <- many (parseTerm env)
      pure (foldl App t1 ts)

--------------- let

parseLetExpr :: Env -> Parser Term
parseLetExpr env = do
  _ <- try (kw "let")
  name <- ident
  mconstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  mproof <- optional $ try (kw "by" >> parseTerm env)
  _ <- kw "="
  val <- parseExpr env
  _ <- kw "in"
  let val' = case mproof of
        Just p -> ByProof val p
        Nothing -> val
  body <- parseExpr (name : env)
  pure (Let name val' body mconstr)

--------------- def

parseDef :: Parser (Name, Term)
parseDef = do
  _ <- kw "def"
  name <- ident
  params <- many parseCurriedParam
  mRetConstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- kw "="
  let paramNames = map fst params
  let env = reverse paramNames
  body <- parseExpr env
  let funcBody = foldr (\(_, _) b -> Lam b) body params
  let result = case mRetConstr of
        Just c -> Annot funcBody c
        Nothing -> funcBody
  pure (name, result)

--------------- func

parseFuncExpr :: Env -> Parser Term
parseFuncExpr env = do
  _ <- try (kw "func")
  _fname <- ident
  params <- many parseCurriedParam
  mRetConstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- kw "="
  let paramNames = map fst params
  let extendedEnv = reverse paramNames ++ env
  body <- parseExpr extendedEnv
  pure (Func _fname params mRetConstr [] [] body)

--------------- refine term

parseRefineTerm :: Parser Term
parseRefineTerm = do
  parent <- parseConstraintAtom
  _ <- kw "where"
  _ <- symbol "("
  paramName <- ident
  _ <- kw "=>"
  predicate <- parseExpr [paramName]
  _ <- symbol ")"
  pure (Refine "" parent (replaceVarZero predicate))
  where
    replaceVarZero (Var 0) = RefParam
    replaceVarZero (App f a) = App (replaceVarZero f) (replaceVarZero a)
    replaceVarZero (Lam b) = Lam (replaceVarZero b)
    replaceVarZero (Let n v b mc) = Let n (replaceVarZero v) (replaceVarZero b) (fmap replaceVarZero mc)
    replaceVarZero (IfThenElse c t f) = IfThenElse (replaceVarZero c) (replaceVarZero t) (replaceVarZero f)
    replaceVarZero (Annot t c) = Annot (replaceVarZero t) (replaceVarZero c)
    replaceVarZero (ByProof t p) = ByProof (replaceVarZero t) (replaceVarZero p)
    replaceVarZero other = other

parseCurriedParam :: Parser (String, Maybe Term)
parseCurriedParam = do
  _ <- sc
  _ <- symbol "("
  pname <- ident
  mconstr <- optional $ try (sc >> symbol ":" >> parseConstraint)
  _ <- symbol ")"
  pure (pname, mconstr)

--------------- terms

parseTerm :: Env -> Parser Term
parseTerm env = do
  t <- parseAtom env
  parseSuffix t
  where
    parseSuffix t =
      (try (sc >> symbol ":" >> parseConstraint >>= \c -> parseSuffix (Annot t c)))
        <|> pure t

parseAtom :: Env -> Parser Term
parseAtom env =
  choice
    [ try (LitInt <$> lexeme L.decimal),
      parseBool,
      try (parseVar env),
      parseBuiltinProp,
      try (parseLam env),
      parseNeg env,
      parseParens env
    ]

parseBool :: Parser Term
parseBool =
  lexeme $
    (LitBool True <$ string "true")
      <|> (LitBool False <$ string "false")

parseVar :: Env -> Parser Term
parseVar env = do
  name <- ident
  case elemIndex name env of
    Just i -> pure (Var i)
    Nothing -> fail ("unbound variable: " ++ name)

parseBuiltinProp :: Parser Term
parseBuiltinProp =
  choice
    [ try (Builtin "∧-intro" <$ (symbol "∧" >> symbol "-" >> symbol "intro")),
      try (Builtin "∧-elim-left" <$ (symbol "∧" >> symbol "-" >> symbol "elim" >> symbol "-" >> symbol "left")),
      Builtin "and" <$ symbol "∧",
      Builtin "or" <$ symbol "∨",
      Builtin "not" <$ symbol "¬",
      Builtin "implies" <$ symbol "→"
    ]

parseLam :: Env -> Parser Term
parseLam env = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- ident
  _ <- symbol "."
  body <- parseExpr (x : env)
  pure (Lam body)

parseNeg :: Env -> Parser Term
parseNeg env = do
  _ <- symbol "-"
  t <- parseAtom env
  pure (App (App (PrimOp Sub) (LitInt 0)) t)

parseParens :: Env -> Parser Term
parseParens env = between (symbol "(") (symbol ")") (parseExpr env)

--------------- operators

opTable :: [[Operator Parser Term]]
opTable =
  [ [ InfixL (try (bin Mul <$ symbol "*")),
      InfixL (try (bin Div <$ symbol "/")),
      InfixL (try (bin Mod <$ symbol "%"))
    ],
    [ InfixL (try (bin Add <$ symbol "+")),
      InfixL (try (bin Sub <$ symbol "-"))
    ],
    [ InfixN (try (bin Eq <$ symbol "==")),
      InfixN (try (bin Le <$ symbol "<=")),
      InfixN (try (bin Ge <$ symbol ">=")),
      InfixN (try (bin Neq <$ symbol "/=")),
      InfixN (try (bin Lt <$ symbol "<")),
      InfixN (try (bin Gt <$ symbol ">"))
    ]
  ]

bin :: PrimOp -> Term -> Term -> Term
bin op l r = App (App (PrimOp op) l) r

--------------- constraints

parseConstraint :: Parser Term
parseConstraint = sc >> parseArrow

parseArrow :: Parser Term
parseArrow = do
  left <- parseAppConstraint
  rest left
  where
    rest left = do
      sc
      hasArrow <- optional (symbol "->")
      case hasArrow of
        Nothing -> pure left
        Just _ -> do
          right <- parseArrow
          pure (Pi "" left right)

parseAppConstraint :: Parser Term
parseAppConstraint = do
  t1 <- parseConstraintAtom
  ts <- many (try (sc >> parseConstraintAtom))
  pure (foldl App t1 ts)

parseConstraintAtom :: Parser Term
parseConstraintAtom =
  choice
    [ parseBuiltinProp,
      try (Builtin "int" <$ string "int") <* notFollowedBy alphaNumChar,
      try (Builtin "bool" <$ string "bool") <* notFollowedBy alphaNumChar,
      try (Universe UData <$ string "data"),
      try (Universe UTheorem <$ string "theorem"),
      parseDepArrow,
      parseParensConstraint,
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

parseParensConstraint :: Parser Term
parseParensConstraint = between (symbol "(") (symbol ")") parseConstraint
