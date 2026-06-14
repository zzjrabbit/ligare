module Ligare.Checker.Context where

import Ligare.Core.Syntax

data CtxEntry = CtxEntry
  { ctxName :: Name,
    ctxConstraint :: Term,
    ctxTheorems :: [Term]
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
  | i < 0 = Nothing
  | i < length ctx = Just (ctxConstraint (ctx !! i))
  | otherwise = Nothing

lookupCtxName :: Name -> Context -> Maybe CtxEntry
lookupCtxName _ [] = Nothing
lookupCtxName name (e : rest)
  | ctxName e == name = Just e
  | otherwise = lookupCtxName name rest

-- 全局约束表
type ConstraintTable = [(Name, Term, Term)] -- (name, parent, predicate)

emptyTable :: ConstraintTable
emptyTable = []

addRefine :: Name -> Term -> Term -> ConstraintTable -> ConstraintTable
addRefine name parent p = ((name, parent, p) :)

lookupRefine :: Name -> ConstraintTable -> Maybe (Term, Term)
lookupRefine _ [] = Nothing
lookupRefine name ((n, p, pred') : rest)
  | n == name = Just (p, pred')
  | otherwise = lookupRefine name rest
