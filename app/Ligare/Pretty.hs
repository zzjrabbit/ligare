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
pretty (Pi "" a b) = "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
pretty (Pi name a b) = "(Pi " ++ name ++ " : " ++ pretty a ++ " => " ++ pretty b ++ ")"
pretty (Builtin s) = s
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
pretty (Refine name parent p) =
  "constraint " ++ name ++ " = " ++ pretty parent ++ " (x => " ++ pretty p ++ ")"
pretty (Annot t c) = "(" ++ pretty t ++ " : " ++ pretty c ++ ")"
pretty (ByProof t proof) = "(" ++ pretty t ++ " by " ++ pretty proof ++ ")"
pretty AutoProof = "auto"
pretty RefParam = "x"
pretty (ProofBlock t) = "proof { " ++ pretty t ++ " }"
pretty (Func name params mRet preconds postconds body) =
  "func "
    ++ name
    ++ "("
    ++ prettyParams params
    ++ ")"
    ++ maybe "" (\r -> " : " ++ pretty r) mRet
    ++ concat [" pre: " ++ pretty p | p <- preconds]
    ++ concat [" post: " ++ pretty p | p <- postconds]
    ++ " = "
    ++ pretty body
  where
    prettyParams [] = ""
    prettyParams [(n, Nothing)] = n
    prettyParams [(n, Just c)] = n ++ " : " ++ pretty c
    prettyParams ((n, mc) : rest) =
      (case mc of Nothing -> n; Just c -> n ++ " : " ++ pretty c)
        ++ ", "
        ++ prettyParams rest
