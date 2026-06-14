module Ligare.Core.Eval where

import Ligare.Core.Debruijn (shift, subst)
import Ligare.Core.Desugar (desugar)
import Ligare.Core.Syntax

eval :: Term -> Either String Term
eval (App (Lam body) arg) = eval (beta (Lam body) arg)
eval (App (App (PrimOp op) a) b) = do
  a' <- eval a
  b' <- eval b
  case (a', b') of
    (LitInt x, LitInt y) -> eval (arith op x y)
    _ -> Left "arithmetic on non-integer"
eval (App f a) = do
  f' <- eval f
  return (App f' a)
eval (Lam t) = do
  t' <- eval t
  return (Lam t')
eval (Let _name val body _mconstr) = eval (beta (Lam body) val)
eval (IfThenElse cond tbranch fbranch) = do
  cond' <- eval cond
  case cond' of
    LitBool True -> eval tbranch
    LitBool False -> eval fbranch
    _ -> return (IfThenElse cond' tbranch fbranch)
eval (Annot t _c) = eval t
eval (ByProof t _proof) = eval t
eval (Refine name parent p) = do
  parent' <- eval parent
  p' <- eval p
  return (Refine name parent' p')
eval AutoProof = return AutoProof
eval RefParam = return RefParam
eval t@(Func {}) = eval (desugar t)
eval (ProofBlock t) = eval t
eval other = return other

beta :: Term -> Term -> Term
beta (Lam body) arg = shift (-1) 0 (subst (shift 1 0 arg) 0 body)
beta _ _ = error "beta: first argument must be Lam"

arith :: PrimOp -> Integer -> Integer -> Term
arith Add = \a b -> LitInt (a + b)
arith Sub = \a b -> LitInt (a - b)
arith Mul = \a b -> LitInt (a * b)
arith Div = \a b -> LitInt (a `div` b)
arith Mod = \a b -> LitInt (a `mod` b)
arith Eq = \a b -> LitBool (a == b)
arith Lt = \a b -> LitBool (a < b)
arith Gt = \a b -> LitBool (a > b)
arith Le = \a b -> LitBool (a <= b)
arith Ge = \a b -> LitBool (a >= b)
arith Neq = \a b -> LitBool (a /= b)
