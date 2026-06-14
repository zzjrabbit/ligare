module Ligare.Pretty where

import Ligare.Core.Syntax

pretty :: Term -> String
pretty (Var i) = "$" ++ show i
pretty (Lam body) = "λ. " ++ pretty body
pretty (App f a) = "(" ++ pretty f ++ " " ++ pretty a ++ ")"
pretty (LitInt n) = show n
pretty (Universe UData) = "data"
pretty (Universe UProp) = "prop"
pretty (Universe UTheorem) = "theorem"
pretty (Universe UProof) = "proof"
pretty (Arrow a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty (Builtin s) = s
pretty (Constraint t1 t2) = "(" ++ pretty t1 ++ " : " ++ pretty t2 ++ ")"
pretty (PrimOp Add) = "+"
pretty (PrimOp Sub) = "-"
pretty (PrimOp Mul) = "*"
pretty (PrimOp Div) = "/"
pretty (PrimOp Mod) = "%"
pretty (PrimOp Eq) = "=="
pretty (PrimOp Lt) = "<"
pretty (PrimOp Gt) = ">"
pretty (PrimOp Le) = "<="
pretty (PrimOp Ge) = ">="
pretty (PrimOp Neq) = "/="
pretty (LitBool b) = show b
pretty (Let name val body mconstr) =
  let constrStr = case mconstr of
        Just c -> " : " ++ pretty c
        Nothing -> ""
   in "let " ++ name ++ constrStr ++ " = " ++ pretty val ++ " in " ++ pretty body
pretty (IfThenElse cond tbranch fbranch) =
  "if " ++ pretty cond ++ " then " ++ pretty tbranch ++ " else " ++ pretty fbranch
