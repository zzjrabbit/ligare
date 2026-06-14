module Ligare.Core.Desugar where

import Ligare.Core.Syntax

desugar :: Term -> Term
desugar (Func _fname params mRet _preconds _postconds body) =
  let funcBody = foldr (\(pn, _) b -> Lam b) body params
      funcType = foldr (\(pn, mc) b -> case mc of
                          Just c  -> Pi pn c b
                          Nothing -> Pi pn (Builtin "data") b
                        ) (maybe (Builtin "data") id mRet) (reverse params)
  in Annot funcBody funcType
desugar other = other

shiftTerm :: Int -> Term -> Term
shiftTerm d = go 0
  where
    go c (Var i) | i >= c    = Var (i + d)
                 | otherwise = Var i
    go c (Lam body)          = Lam (go (c + 1) body)
    go c (App f a)           = App (go c f) (go c a)
    go c (Pi n a b)          = Pi n (go c a) (go (c + 1) b)
    go c (Let n v b mc)      = Let n (go c v) (go (c + 1) b) (fmap (go c) mc)
    go c (IfThenElse cd t f) = IfThenElse (go c cd) (go c t) (go c f)
    go c (Annot t ct)        = Annot (go c t) (go c ct)
    go c (ByProof t p)       = ByProof (go c t) (go c p)
    go c (Refine n par p)    = Refine n (go c par) (go c p)
    go c (Func n ps mc pr po b) = Func n [(nm, fmap (go c) mc') | (nm, mc') <- ps]
                                       (fmap (go c) mc)
                                       (map (go c) pr) (map (go c) po) (go (c + length ps) b)
    go _ other               = other
