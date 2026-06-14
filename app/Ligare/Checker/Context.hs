module Ligare.Checker.Context where

import Ligare.Core.Debruijn (shift, subst)
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

-- expandConstraint 需要处理 RefParam，用专用 shiftParam
expandConstraint :: ConstraintTable -> Term -> Maybe Term
expandConstraint table (App (Builtin name) arg) =
  case lookupRefine name table of
    Just (Universe UData, body) ->
      let bodyShifted = shiftParam 1 body
          instantiated = subst arg 0 bodyShifted
          reduced = shiftParam (-1) instantiated
       in Just reduced
    _ -> Nothing
expandConstraint _ _ = Nothing

shiftParam :: Int -> Term -> Term
shiftParam d = go 0
  where
    go _ RefParam = RefParam
    go c (Var i)
      | i >= c = Var (i + d)
      | otherwise = Var i
    go c other = shift d c other
