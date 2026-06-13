module Ligare.Core.Eval where

import Ligare.Core.Syntax

as_int :: Term -> Integer
as_int term = case term of
  LitInt i -> i
  _ -> error "expected lit int"

eval :: Term -> Term
eval (App (Lam body) arg) = eval (beta (Lam body) arg)
eval (App (App (PrimOp op) a) b) = 
  let
    a' = as_int (eval a)
    b' = as_int (eval b)
  in eval (LitInt (arith op a' b'))
eval (App f a) = let f' = eval f in App f' a
eval (Lam t) = Lam (eval t)
eval other = other

beta :: Term -> Term -> Term
beta (Lam body) arg = shift (-1) 0 (subst (shift 1 0 arg) 0 body)
beta _ _ = error "beta: first argument must be Lam"

subst :: Term -> Int -> Term -> Term
subst s i t = go 0 t
  where
    go c (Var j)
      | j == i + c  = shift c 0 s
      | otherwise   = Var j
    go c (Lam body)    = Lam (go (c + 1) body)
    go c (App f a)     = App (go c f) (go c a)
    go _c (LitInt n)    = LitInt n
    go _c (Universe u)  = Universe u
    go _c (Builtin s') = Builtin s'
    go c (Constraint t1 t2) = Constraint (go c t1) (go c t2)
    go _c (PrimOp op)   = PrimOp op

shift :: Int -> Int -> Term -> Term
shift d c (Var i)
  | i >= c    = Var (i + d)
  | otherwise = Var i
shift d c (Lam body)    = Lam (shift d (c + 1) body)
shift d c (App f a)     = App (shift d c f) (shift d c a)
shift _d _c (LitInt n)    = LitInt n
shift _d _c (Universe u)  = Universe u
shift _d _c (Builtin s) = Builtin s
shift d c (Constraint t1 t2) = Constraint (shift d c t1) (shift d c t2)
shift _d _c (PrimOp op)   = PrimOp op

arith :: PrimOp -> Integer -> Integer -> Integer
arith Add = (+)
arith Sub = (-)
arith Mul = (*)
arith Div = div
arith Mod = mod
arith Eq  = \a b -> if a == b then 1 else 0
arith Lt  = \a b -> if a < b  then 1 else 0
arith Gt  = \a b -> if a > b  then 1 else 0
arith Le  = \a b -> if a <= b then 1 else 0
arith Ge  = \a b -> if a >= b then 1 else 0
arith Neq = \a b -> if a /= b then 1 else 0

