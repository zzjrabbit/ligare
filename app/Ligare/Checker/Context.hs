module Ligare.Checker.Context where

import Ligare.Core.Syntax

data CtxEntry = CtxEntry
  { ctxName       :: Name
  , ctxConstraint :: Term
  , ctxTheorems   :: [Term]
  }
  deriving (Eq, Show)

type Context = [CtxEntry]

emptyCtx :: Context
emptyCtx = []

extendCtx :: Name -> Term -> Context -> Context
extendCtx name constraint ctx =
  CtxEntry name constraint [] : ctx

extendCtxTerm :: Term -> Context -> Context
extendCtxTerm constraint ctx =
  CtxEntry "_" constraint [] : ctx

addTheorem :: Name -> Term -> Context -> Context
addTheorem _ _ [] = []
addTheorem name thm (CtxEntry n c thms : rest)
  | n == name = CtxEntry n c (thm : thms) : rest
  | otherwise = CtxEntry n c thms : addTheorem name thm rest

lookupCtx :: Int -> Context -> Maybe Term
lookupCtx i ctx
  | i < 0           = Nothing
  | i < length ctx  = Just (ctxConstraint (ctx !! i))
  | otherwise       = Nothing

lookupCtxName :: Name -> Context -> Maybe CtxEntry
lookupCtxName _ [] = Nothing
lookupCtxName name (e : rest)
  | ctxName e == name = Just e
  | otherwise         = lookupCtxName name rest

-- 全局约束表
-- Refinement:  (name, parent, predicate)  如 ("nat", Builtin "int", x>=0)
-- Constructor: (name, arity, body)        如 ("Vec", Pi "n" int (Universe UData), ...)
--                                            body 是 Pi ... (Universe UData) 表示返回约束
type ConstraintTable = [(Name, Term, Term)]

emptyTable :: ConstraintTable
emptyTable = []

addRefine :: Name -> Term -> Term -> ConstraintTable -> ConstraintTable
addRefine name parent p = ((name, parent, p) :)

lookupRefine :: Name -> ConstraintTable -> Maybe (Term, Term)
lookupRefine _ [] = Nothing
lookupRefine name ((n, p, pred') : rest)
  | n == name = Just (p, pred')
  | otherwise = lookupRefine name rest

-- 将约束 App (Builtin name) args 展开
-- 例如 App Vec 3 → 查 Vec 的构造器定义，beta-归约替换参数
expandConstraint :: ConstraintTable -> Term -> Maybe Term
expandConstraint table (App (Builtin name) arg) =
  case lookupRefine name table of
    Just (Universe UData, body) ->
      let bodyShifted = shiftTerm 1 body
          instantiated = subst arg 0 bodyShifted
          reduced = shiftTerm (-1) instantiated
      in Just reduced
    _ -> Nothing
expandConstraint _ _ = Nothing

shiftTerm :: Int -> Term -> Term
shiftTerm d = go 0
  where
    go _ RefParam = RefParam
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

subst :: Term -> Int -> Term -> Term
subst s i t0 = go 0 t0
  where
    go c (Var j)
      | j == i + c = shiftTerm c s
      | otherwise  = Var j
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
