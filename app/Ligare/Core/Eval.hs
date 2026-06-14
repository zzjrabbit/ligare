module Ligare.Core.Eval where

import Ligare.Core.Syntax

as_int :: Term -> Integer
as_int term = case term of
  LitInt i -> i
  _ -> error "expected lit int"

as_bool :: Term -> Bool
as_bool term = case term of
  LitBool i -> i
  _ -> error "expect lit bool"

eval :: Term -> Term
eval (App (Lam body) arg) = eval (beta (Lam body) arg)
eval (App (App (PrimOp op) a) b) =
  let a' = as_int a
      b' = as_int b
   in eval (arith op a' b')
eval (App f a) = let f' = eval f in App f' a
eval (Lam t) = Lam (eval t)
eval (Let _name val body _mconstr) = eval (beta (Lam body) val)
eval (IfThenElse cond tbranch fbranch) =
  case eval cond of
    LitBool True -> eval tbranch
    LitBool False -> eval fbranch
    cond' -> IfThenElse cond' tbranch fbranch
eval (Annot t _c) = eval t
eval (ByProof t _proof) = eval t
eval (Refine name parent p) = Refine name (eval parent) (eval p)
eval AutoProof = AutoProof
eval other = other

beta :: Term -> Term -> Term
beta (Lam body) arg = shift (-1) 0 (subst (shift 1 0 arg) 0 body)
beta _ _ = error "beta: first argument must be Lam"

subst :: Term -> Int -> Term -> Term
subst s i t0 = go 0 t0
  where
    go c (Var j)
      | j == i + c = shift c 0 s
      | otherwise = Var j
    go c (Lam body) = Lam (go (c + 1) body)
    go c (App f a) = App (go c f) (go c a)
    go _c (LitInt n) = LitInt n
    go _c (LitBool n) = LitBool n
    go c (Arrow a b) = Arrow (go c a) (go c b)
    go _c (Universe u) = Universe u
    go _c (Builtin s') = Builtin s'
    go c (Constraint t1 t2) = Constraint (go c t1) (go c t2)
    go _c (PrimOp op) = PrimOp op
    go c (Let name val body mconstr) =
      Let name (go c val) (go (c + 1) body) (fmap (go c) mconstr)
    go c (IfThenElse cond tbranch fbranch) =
      IfThenElse (go c cond) (go c tbranch) (go c fbranch)
    go c (Refine name parent p) =
      Refine name (go c parent) (go c p)
    go c (Annot term constr) = Annot (go c term) (go c constr)
    go c (ByProof term proof) = ByProof (go c term) (go c proof)
    go _c AutoProof = AutoProof

shift :: Int -> Int -> Term -> Term
shift d c (Var i)
  | i >= c = Var (i + d)
  | otherwise = Var i
shift d c (Lam body) = Lam (shift d (c + 1) body)
shift d c (App f a) = App (shift d c f) (shift d c a)
shift d c (Arrow a b) = Arrow (shift d c a) (shift d c b)
shift _d _c (LitInt n) = LitInt n
shift _d _c (LitBool n) = LitBool n
shift _d _c (Universe u) = Universe u
shift _d _c (Builtin s) = Builtin s
shift d c (Constraint t1 t2) = Constraint (shift d c t1) (shift d c t2)
shift _d _c (PrimOp op) = PrimOp op
shift d c (Let name val body mconstr) =
  Let name (shift d c val) (shift d (c + 1) body) (fmap (shift d c) mconstr)
shift d c (IfThenElse cond tbranch fbranch) =
  IfThenElse (shift d c cond) (shift d c tbranch) (shift d c fbranch)
shift d c (Refine name parent p) =
  Refine name (shift d c parent) (shift d c p)
shift d c (Annot term constr) = Annot (shift d c term) (shift d c constr)
shift d c (ByProof term proof) = ByProof (shift d c term) (shift d c proof)
shift _d _c AutoProof = AutoProof

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
