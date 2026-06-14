module Main where

import Ligare.Checker.Checker
import Ligare.Checker.Context
import Ligare.Core.Eval
import Ligare.Core.Syntax
import Ligare.Front.Parser
import Ligare.Pretty
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Ligare"
    [ parserTests,
      evalTests,
      checkerTests,
      refinementTests,
      prettyTests
    ]

-- ── Parser ──

parserTests :: TestTree
parserTests =
  testGroup
    "Parser"
    [ testCase "integer literal" $
        parseExprTop "42" @?= Right (LitInt 42),
      testCase "boolean literal" $
        parseExprTop "true" @?= Right (LitBool True),
      testCase "simple addition" $
        parseExprTop "1 + 2" @?= Right (bin Add (LitInt 1) (LitInt 2)),
      testCase "comparison" $
        parseExprTop "3 < 5" @?= Right (bin Lt (LitInt 3) (LitInt 5)),
      testCase "two-char operator >=" $
        parseExprTop "0 >= 0" @?= Right (bin Ge (LitInt 0) (LitInt 0)),
      testCase "two-char operator <=" $
        parseExprTop "1 <= 2" @?= Right (bin Le (LitInt 1) (LitInt 2)),
      testCase "negative number" $
        parseExprTop "-5" @?= Right (App (App (PrimOp Sub) (LitInt 0)) (LitInt 5)),
      testCase "if expression" $
        parseExprTop "if true then 1 else 0"
          @?= Right (IfThenElse (LitBool True) (LitInt 1) (LitInt 0)),
      testCase "let expression" $
        parseExprTop "let x = 5 in x"
          @?= Right (Let "x" (LitInt 5) (Var 0) Nothing),
      testCase "let with constraint" $
        parseExprTop "let x : int = 5 in x"
          @?= Right (Let "x" (LitInt 5) (Var 0) (Just (Builtin "int"))),
      testCase "lambda" $
        parseExprTop "\\x. x" @?= Right (Lam (Var 0)),
      testCase "annot expression" $
        parseExprTop "(5 : int)"
          @?= Right (Annot (LitInt 5) (Builtin "int")),
      testCase "by expression" $
        parseExprTop "(5 : int by true)"
          @?= Right (ByProof (Annot (LitInt 5) (Builtin "int")) (LitBool True)),
      testCase "arrow constraint" $
        parseConstraintFromString "int -> bool"
          @?= Right (Arrow (Builtin "int") (Builtin "bool")),
      testCase "refine definition" $
        parseRefineTop "nat = int (x => x >= 0)"
          @?= Right ("nat", Builtin "int", bin Ge RefParam (LitInt 0))
    ]

bin :: PrimOp -> Term -> Term -> Term
bin op l r = App (App (PrimOp op) l) r

-- ── Eval ──

evalTests :: TestTree
evalTests =
  testGroup
    "Eval"
    [ testCase "integer identity" $
        eval (LitInt 42) @?= Right (LitInt 42),
      testCase "arithmetic" $
        eval (parse' "1 + 2 * 3") @?= Right (LitInt 7),
      testCase "if true" $
        eval (parse' "if true then 10 else 20") @?= Right (LitInt 10),
      testCase "if false" $
        eval (parse' "if false then 10 else 20") @?= Right (LitInt 20),
      testCase "let" $
        eval (parse' "let x = 5 in x + 3") @?= Right (LitInt 8),
      testCase "beta reduction" $
        eval (parse' "(\\x. x + 1) 5") @?= Right (LitInt 6),
      testCase "annot strips annotation" $
        eval (Annot (LitInt 42) (Builtin "int")) @?= Right (LitInt 42),
      testCase "by proof strips proof" $
        eval (ByProof (LitInt 42) (LitBool True)) @?= Right (LitInt 42),
      testCase "arithmetic on bool fails" $
        case eval (bin Add (LitBool True) (LitInt 1)) of
          Left _ -> True @?= True
          Right _ -> assertFailure "expected failure",
      testCase "eval nested if" $
        eval (parse' "if (if true then false else true) then 1 else 2") @?= Right (LitInt 2)
    ]

parse' :: String -> Term
parse' s = case parseExprTop s of
  Right t -> t
  Left e -> error ("parse error in test: " ++ e)

-- ── Checker ──

checkerTests :: TestTree
checkerTests =
  testGroup
    "Checker"
    [ testCase "int literal" $
        check' (LitInt 5) (Builtin "int") @?= Right (),
      testCase "bool literal" $
        check' (LitBool True) (Builtin "bool") @?= Right (),
      testCase "int fails for bool" $
        case check' (LitInt 5) (Builtin "bool") of
          Left _ -> True @?= True
          Right _ -> assertFailure "expected failure",
      testCase "lambda int->int" $
        check' (parse' "\\x. x") (parseC "int -> int") @?= Right (),
      testCase "lambda bool->int with if" $
        check' (parse' "\\x. (if x then 0 else 1)") (parseC "bool -> int") @?= Right (),
      testCase "if branches checked" $
        check' (parse' "if true then 5 else 3") (Builtin "int") @?= Right (),
      testCase "let with constraint" $
        check' (parse' "let x : int = 5 in x") (Builtin "int") @?= Right (),
      testCase "unknown constraint fails" $
        case check' (LitInt 5) (Builtin "foo") of
          Left _ -> True @?= True
          Right _ -> assertFailure "expected failure"
    ]

check' :: Term -> Term -> Either String ()
check' t c = check emptyTable emptyCtx t c

parseC :: String -> Term
parseC s = case parseConstraintFromString s of
  Right c -> c
  Left e -> error ("parse constraint error: " ++ e)

-- ── Refinement ──

refinementTests :: TestTree
refinementTests =
  testGroup
    "Refinement"
    [ testCase "nat accepts 5" $
        checkWith [natDef] (LitInt 5) (Builtin "nat") @?= Right (),
      testCase "nat rejects -1" $
        case checkWith [natDef] (parse' "-1") (Builtin "nat") of
          Left _ -> True @?= True
          Right _ -> assertFailure "expected failure",
      testCase "nat accepts 0" $
        checkWith [natDef] (LitInt 0) (Builtin "nat") @?= Right (),
      testCase "pos rejects 0" $
        case checkWith [posDef] (LitInt 0) (Builtin "pos") of
          Left _ -> True @?= True
          Right _ -> assertFailure "expected failure",
      testCase "pos accepts 3" $
        checkWith [posDef] (LitInt 3) (Builtin "pos") @?= Right (),
      testCase "nat is subtype of int (variable check)" $
        checkWith [natDef] (parse' "\\x. x") (parseC "nat -> int") @?= Right (),
      testCase "pos is subtype of int (parent chain)" $
        checkWith [posDef] (parse' "\\x. x") (parseC "pos -> int") @?= Right ()
    ]

checkWith :: [(Name, Term, Term)] -> Term -> Term -> Either String ()
checkWith refs t c =
  let table = foldr (\(n, p, pr) -> addRefine n p pr) emptyTable refs
   in check table emptyCtx t c

natDef :: (Name, Term, Term)
natDef = ("nat", Builtin "int", bin Ge RefParam (LitInt 0))

posDef :: (Name, Term, Term)
posDef = ("pos", Builtin "int", bin Gt RefParam (LitInt 0))

-- ── Pretty ──

prettyTests :: TestTree
prettyTests =
  testGroup
    "Pretty"
    [ testCase "integer" $
        pretty (LitInt 42) @?= "42",
      testCase "lambda" $
        pretty (Lam (Var 0)) @?= "λ. $0",
      testCase "if" $
        pretty (IfThenElse (LitBool True) (LitInt 1) (LitInt 0))
          @?= "if True then 1 else 0",
      testCase "let" $
        pretty (Let "x" (LitInt 5) (Var 0) Nothing)
          @?= "let x = 5 in $0",
      testCase "annot" $
        pretty (Annot (LitInt 5) (Builtin "int")) @?= "(5 : int)"
    ]
