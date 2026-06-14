module Ligare.Core.Eval where

import Ligare.Core.Syntax
import Ligare.Core.Desugar (desugar)

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
eval other = return other

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
    go c (Pi name a b) = Pi name (go c a) (go (c + 1) b)
    go c (Let name val body mconstr) =
      Let name (go c val) (go (c + 1) body) (fmap (go c) mconstr)
    go c (IfThenElse cond tb fb) =
      IfThenElse (go c cond) (go c tb) (go c fb)
    go c (Refine name parent p) = Refine name (go c parent) (go c p)
    go c (Annot term constr) = Annot (go c term) (go c constr)
    go c (ByProof term proof) = ByProof (go c term) (go c proof)
    go c (Func n ps mc pr po b) = Func n [(nm, fmap (go c) mc') | (nm, mc') <- ps]
                                       (fmap (go c) mc)
                                       (map (go c) pr) (map (go c) po) (go (c + length ps) b)
    go _c other = other

shift :: Int -> Int -> Term -> Term
shift d c (Var i)
  | i >= c = Var (i + d)
  | otherwise = Var i
shift d c (Lam body) = Lam (shift d (c + 1) body)
shift d c (App f a) = App (shift d c f) (shift d c a)
shift d c (Pi name a b) = Pi name (shift d c a) (shift d (c + 1) b)
shift d c (Let name val body mconstr) =
  Let name (shift d c val) (shift d (c + 1) body) (fmap (shift d c) mconstr)
shift d c (IfThenElse cond tb fb) =
  IfThenElse (shift d c cond) (shift d c tb) (shift d c fb)
shift d c (Refine name parent p) = Refine name (shift d c parent) (shift d c p)
shift d c (Annot term constr) = Annot (shift d c term) (shift d c constr)
shift d c (ByProof term proof) = ByProof (shift d c term) (shift d c proof)
shift d c (Func n ps mc pr po b) = Func n [(nm, fmap (shift d c) mc') | (nm, mc') <- ps]
                                          (fmap (shift d c) mc)
                                          (map (shift d c) pr) (map (shift d c) po) (shift d (c + length ps) b)
shift _d _c other = other

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
