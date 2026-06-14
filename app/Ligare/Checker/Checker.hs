module Ligare.Checker.Checker where

import Debug.Trace
import Ligare.Checker.Context
import Ligare.Core.Eval (eval)
import Ligare.Core.Syntax

check :: Context -> Term -> Term -> Either String ()
check ctx term constraint = case term of
  Var i -> do
    expected <- case lookupCtx i ctx of
      Just t -> pure t
      Nothing -> Left ("Unbound variable index: " ++ show i)
    if expected == eval constraint
      then pure ()
      else Left ("Constraint mismatch for variable: expected " ++ show expected ++ ", but got " ++ show constraint)
  Let _name val body mconstr -> do
    case mconstr of
      Just c -> check ctx val c
      Nothing -> pure ()
    check (extendCtx constraint ctx) body constraint
  IfThenElse cond tbranch fbranch -> do
    check ctx cond (Builtin "bool")
    check ctx tbranch constraint
    check ctx fbranch constraint
  _ -> do
    let normConstraint = eval constraint
    case normConstraint of
      Builtin "int" -> checkInt term
      Builtin "bool" -> checkBool term
      Arrow a b -> checkArrow ctx term a b
      Universe UData -> pure ()
      _ -> Left $ "Cannot use " ++ show normConstraint ++ " as a constraint"
    where
      checkInt t = case eval t of
        LitInt _ -> pure ()
        _ -> Left "Expected an integer"
      checkBool t = case eval t of
        LitBool _ -> pure ()
        _ -> Left "Expected a boolean"
      checkArrow ctx' t a b = case eval t of
        Lam body -> do
          let ctx'' = extendCtx a ctx'
          let _ = trace (show body) ()
          check ctx'' body b
        _ -> Left "Expected a lambda"
