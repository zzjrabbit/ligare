module Ligare.Checker.Checker where

import Ligare.Checker.Context
import Ligare.Core.Eval (eval)
import Ligare.Core.Desugar (desugar)
import Ligare.Core.Syntax

check :: ConstraintTable -> Context -> Term -> Term -> Either String ()
check table ctx term constraint = case desugar term of
  Var i -> do
    expected <- case lookupCtx i ctx of
      Just t  -> pure t
      Nothing -> Left ("Unbound variable index: " ++ show i)
    expected' <- eval expected
    constraint' <- eval constraint
    if expected' == constraint' || isRefinementOf table expected' constraint'
      then pure ()
      else Left ("Constraint mismatch for variable: expected " ++ show expected' ++ ", but got " ++ show constraint')
  Annot t c -> do
    check table ctx t c
    check table ctx t constraint
  ByProof t _proof ->
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
    normConstraint <- eval constraint
    case normConstraint of
      Builtin "int" -> checkInt term
      Builtin "bool" -> checkBool term
      Pi "" a b -> checkArrow table ctx term a b
      Pi name a b -> checkPi table ctx term name a b
      Universe UData -> pure ()
      Var j ->
        Left ("Variable " ++ show j ++ " is a data term, cannot be used as a constraint")
      App (App (Builtin "and") a) b -> do
        -- term must satisfy both a and b
        check table ctx term a
        check table ctx term b
      App (App (Builtin "or") a) b -> do
        -- term must satisfy either a or b (non-deterministic)
        case check table ctx term a of
          Right () -> pure ()
          Left _   -> check table ctx term b
      App (Builtin "not") _a ->
        -- negation: term must NOT satisfy a? No, negation is logical
        -- For now, just accept (proof obligation)
        pure ()
      App f a -> do
        case expandConstraint table normConstraint of
          Just expanded -> check table ctx term expanded
          Nothing ->
            case lookupRefine (constraintName f) table of
              Just (Universe UData, _body) -> do
                -- constraint constructor: Vec n
                let expanded = App _body a
                check table ctx term expanded
              _ -> do
                f' <- eval f
                a' <- eval a
                Left $ "Cannot apply " ++ show f' ++ " to " ++ show a' ++ " as a constraint"
      _ -> case lookupRefine (constraintName normConstraint) table of
        Just (parent, pred') -> do
          check table ctx term parent
          proveAuto ctx term pred'
        Nothing -> Left $ "Cannot use " ++ show normConstraint ++ " as a constraint"
  where
    checkInt t = do
      t' <- eval t
      case t' of
        LitInt _ -> pure ()
        _ -> Left "Expected an integer"
    checkBool t = do
      t' <- eval t
      case t' of
        LitBool _ -> pure ()
        _ -> Left "Expected a boolean"
    checkArrow table' ctx' t a b = do
      t' <- eval t
      case t' of
        Lam body -> do
          let ctx'' = extendCtxTerm a ctx'
          check table' ctx'' body b
        _ -> Left "Expected a lambda"
    checkPi table' ctx' t name a b = do
      t' <- eval t
      case t' of
        Lam body -> do
          let ctx'' = extendCtx name a ctx'
          check table' ctx'' body b
        _ -> Left "Expected a lambda"

constraintName :: Term -> Name
constraintName (Builtin n) = n
constraintName (Refine n _ _) = n
constraintName _ = "?"

isRefinementOf :: ConstraintTable -> Term -> Term -> Bool
isRefinementOf _ t1 t2 | t1 == t2 = True
isRefinementOf table (Builtin n) target =
  case lookupRefine n table of
    Just (parent, _) -> isRefinementOf table parent target
    Nothing -> False
isRefinementOf table (Refine n _ _) target =
  isRefinementOf table (Builtin n) target
isRefinementOf _ _ _ = False

notTerm :: Term -> Term
notTerm t = App (Lam (IfThenElse (Var 0) (LitBool False) (LitBool True))) t

-- ── 半自动证明 ──

proveAuto :: Context -> Term -> Term -> Either String ()
proveAuto ctx subject pred' = do
  let instantiated = substRefParam subject pred'
  instantiated' <- eval instantiated
  case instantiated' of
    LitBool True -> pure ()
    LitBool False -> Left ("Predicate does not hold for " ++ show subject)
    _ -> case searchCtx ctx pred' of
      Just _ -> pure ()
      Nothing -> trySimpleDerive pred' ctx
  where
    substRefParam :: Term -> Term -> Term
    substRefParam _ RefParam = subject
    substRefParam subj (App f a) = App (substRefParam subj f) (substRefParam subj a)
    substRefParam subj (Lam body) = Lam (substRefParam subj body)
    substRefParam subj (Let n v b mc) = Let n (substRefParam subj v) (substRefParam subj b) (fmap (substRefParam subj) mc)
    substRefParam subj (IfThenElse c t f) = IfThenElse (substRefParam subj c) (substRefParam subj t) (substRefParam subj f)
    substRefParam subj (Annot t c) = Annot (substRefParam subj t) (substRefParam subj c)
    substRefParam subj (ByProof t p) = ByProof (substRefParam subj t) (substRefParam subj p)
    substRefParam subj (Refine n par p) = Refine n (substRefParam subj par) (substRefParam subj p)
    substRefParam _ other = other

    searchCtx :: Context -> Term -> Maybe Term
    searchCtx [] _ = Nothing
    searchCtx (CtxEntry _ _ thms : rest) target =
      case filter (\t -> evalEq t target) thms of
        (t : _) -> Just t
        [] -> searchCtx rest target

    evalEq t1 t2 =
      case (eval (substRefParam subject t1), eval (substRefParam subject t2)) of
        (Right v1, Right v2) -> v1 == v2
        _ -> False

trySimpleDerive :: Term -> Context -> Either String ()
trySimpleDerive (App (App (PrimOp Neq) a) b) ctx =
  let gt = App (App (PrimOp Gt) a) b
   in case searchCtx' ctx gt of
        Just _ -> pure ()
        Nothing -> Left ("Cannot prove " ++ show (App (App (PrimOp Neq) a) b))
  where
    searchCtx' [] _ = Nothing
    searchCtx' (CtxEntry _ _ thms : rest) t =
      case filter (\th -> evalEq' th t) thms of
        (th : _) -> Just th
        [] -> searchCtx' rest t
    evalEq' t1 t2 =
      case (eval t1, eval t2) of
        (Right v1, Right v2) -> v1 == v2
        _ -> False
trySimpleDerive _ _ =
  Left "Automatic proof failed: provide a manual proof with `by`"
