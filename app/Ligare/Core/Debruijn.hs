module Ligare.Core.Debruijn where

import Ligare.Core.Syntax

-- de Bruijn 替换: subst s i t  把 t 中索引 i 的变量替换为 s
subst :: Term -> Int -> Term -> Term
subst s i t0 = go 0 t0
  where
    go c (Var j)
      | j == i + c = shift c 0 s
      | otherwise = Var j
    go c (Lam body) = Lam (go (c + 1) body)
    go c (App f a) = App (go c f) (go c a)
    go c (Pi n a b) = Pi n (go c a) (go (c + 1) b)
    go c (Let n v b mc) = Let n (go c v) (go (c + 1) b) (fmap (go c) mc)
    go c (IfThenElse cd t f) = IfThenElse (go c cd) (go c t) (go c f)
    go c (Annot t ct) = Annot (go c t) (go c ct)
    go c (ByProof t p) = ByProof (go c t) (go c p)
    go c (Refine n par p) = Refine n (go c par) (go c p)
    go c (Func n ps mc pr po b) =
      Func
        n
        [(nm, fmap (go c) mc') | (nm, mc') <- ps]
        (fmap (go c) mc)
        (map (go c) pr)
        (map (go c) po)
        (go (c + length ps) b)
    go c (ProofBlock t) = ProofBlock (go c t)
    go _ other = other

-- de Bruijn 移位: shift d c t  把 t 中索引 >= c 的变量 +d
shift :: Int -> Int -> Term -> Term
shift d c (Var i)
  | i >= c = Var (i + d)
  | otherwise = Var i
shift d c (Lam body) = Lam (shift d (c + 1) body)
shift d c (App f a) = App (shift d c f) (shift d c a)
shift d c (Pi n a b) = Pi n (shift d c a) (shift d (c + 1) b)
shift d c (Let n v b mc) = Let n (shift d c v) (shift d (c + 1) b) (fmap (shift d c) mc)
shift d c (IfThenElse cd t f) = IfThenElse (shift d c cd) (shift d c t) (shift d c f)
shift d c (Annot t ct) = Annot (shift d c t) (shift d c ct)
shift d c (ByProof t p) = ByProof (shift d c t) (shift d c p)
shift d c (Refine n par p) = Refine n (shift d c par) (shift d c p)
shift d c (Func n ps mc pr po b) =
  Func
    n
    [(nm, fmap (shift d c) mc') | (nm, mc') <- ps]
    (fmap (shift d c) mc)
    (map (shift d c) pr)
    (map (shift d c) po)
    (shift d (c + length ps) b)
shift d c (ProofBlock t) = ProofBlock (shift d c t)
shift _ _ other = other
