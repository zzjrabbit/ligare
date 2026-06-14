module Ligare.Checker.Checker where

import Ligare.Checker.Context
import Ligare.Core.Eval (eval, subst)
import Ligare.Core.Syntax

check :: ConstraintTable -> Context -> Term -> Term -> Either String ()
check table ctx term constraint = case term of
  Var i -> do
    expected <- case lookupCtx i ctx of
      Just t -> pure t
      Nothing -> Left ("Unbound variable index: " ++ show i)
    if expected == eval constraint
      then pure ()
      else Left ("Constraint mismatch for variable: expected " ++ show expected ++ ", but got " ++ show (eval constraint))
  Annot t c -> do
    check table ctx t c
    check table ctx t constraint
  ByProof t _proof -> do
    check table ctx t constraint
  Refine name parent p -> do
    let table' = addRefine name parent p table
    check table' ctx constraint constraint
  IfThenElse cond tbranch fbranch -> do
    check table ctx cond (Builtin "bool")
    let thmTrue = cond
    let thmFalse = notTerm cond
    let ctxT = addTheorem "_" thmTrue ctx
    let ctxF = addTheorem "_" thmFalse ctx
    check table ctxT tbranch constraint
    check table ctxF fbranch constraint
  Let name val body mconstr -> do
    case mconstr of
      Just c -> check table ctx val c
      Nothing -> pure ()
    check table (extendCtx name constraint ctx) body constraint
  _ -> do
    let normConstraint = eval constraint
    case normConstraint of
      Builtin "int" -> checkInt term
      Builtin "bool" -> checkBool term
      Arrow a b -> checkArrow table ctx term a b
      Universe UData -> pure ()
      _ -> case lookupRefine (constraintName normConstraint) table of
        Just (parent, pred') -> do
          check table ctx term parent
          proveAuto ctx term pred'
        Nothing -> Left $ "Cannot use " ++ show normConstraint ++ " as a constraint"
  where
    checkInt t = case eval t of
      LitInt _ -> pure ()
      _ -> Left "Expected an integer"
    checkBool t = case eval t of
      LitBool _ -> pure ()
      _ -> Left "Expected a boolean"
    checkArrow table' ctx' t a b = case eval t of
      Lam body -> do
        let ctx'' = extendCtxTerm a ctx'
        check table' ctx'' body b
      _ -> Left "Expected a lambda"

constraintName :: Term -> Name
constraintName (Builtin n) = n
constraintName (Refine n _ _) = n
constraintName _ = "?"

notTerm :: Term -> Term
notTerm t = App (Lam (IfThenElse (Var 0) (LitBool False) (LitBool True))) t

-- ── 半自动证明 ──

proveAuto :: Context -> Term -> Term -> Either String ()
proveAuto ctx subject pred' =
  let instantiated = subst subject 0 pred'
   in case eval instantiated of
        LitBool True -> pure ()
        LitBool False -> Left ("Predicate does not hold for " ++ show subject)
        _ -> case searchCtx ctx pred' of
          Just _ -> pure ()
          Nothing -> trySimpleDerive pred' ctx
  where
    searchCtx :: Context -> Term -> Maybe Term
    searchCtx [] _ = Nothing
    searchCtx (CtxEntry _ _ thms : rest) target =
      case filter (\t -> eval (subst subject 0 t) == eval (subst subject 0 target)) thms of
        (t : _) -> Just t
        [] -> searchCtx rest target

trySimpleDerive :: Term -> Context -> Either String ()
trySimpleDerive (App (App (PrimOp Neq) a) b) ctx = do
  let gt = App (App (PrimOp Gt) a) b
  case searchCtx' ctx gt of
    Just _ -> pure ()
    Nothing -> Left ("Cannot prove " ++ show (App (App (PrimOp Neq) a) b))
  where
    searchCtx' c t = case c of
      [] -> Nothing
      (CtxEntry _ _ thms : rest) ->
        case filter (\th -> eval th == eval t) thms of
          (th : _) -> Just th
          [] -> searchCtx' rest t
trySimpleDerive _pred' _ctx =
  Left "Automatic proof failed: provide a manual proof with `by`"

proveWith :: ConstraintTable -> Context -> Term -> Term -> Term -> Either String ()
proveWith _table _ctx _subject _goal (LitBool True) = pure ()
proveWith table ctx subject goal (ByProof _ inner) =
  proveWith table ctx subject goal inner
proveWith _table ctx _subject goal AutoProof =
  proveAuto ctx _subject goal
proveWith _table _ctx _subject _goal _proof =
  Left "Cannot use this term as a proof"
