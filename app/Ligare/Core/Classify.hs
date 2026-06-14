module Ligare.Core.Classify where

import Ligare.Checker.Context (Context, lookupCtx)
import Ligare.Core.Syntax

classify :: Context -> Term -> Maybe Universe
classify _ (LitInt _) = Just UData
classify _ (LitBool _) = Just UData
classify _ (Lam _) = Just UData
classify ctx (App f _) = classify ctx f -- 应用程序的宇宙取决于函数
classify _ (PrimOp _) = Just UData
classify _ (Universe u) = Just u
classify _ AutoProof = Just UProof
classify _ RefParam = Just UData -- 精化参数是一个值
classify _ (Func {}) = Just UData -- 展开后是 lambda
classify ctx (Var i) = do
  t <- lookupCtx i ctx
  classify ctx t
classify ctx (Annot t _) = classify ctx t
classify ctx (ByProof t _) = classify ctx t
classify ctx (Let _ _ body _) = classify ctx body
classify ctx (IfThenElse _ t _) = classify ctx t
classify ctx (ProofBlock t) = classify ctx t -- proof block 的宇宙取决于其内容
classify _ (Pi _ _ _) = Just UProp
classify _ (Refine _ _ _) = Just UProp
classify _ (Builtin "int") = Just UProp -- int 优先作为约束
classify _ (Builtin "bool") = Just UProp
classify _ (Builtin "data") = Just UProp
classify _ (Builtin "theorem") = Just UTheorem
classify _ (Builtin "proof") = Just UProof
classify _ (Builtin "and") = Just UProp
classify _ (Builtin "or") = Just UProp
classify _ (Builtin "not") = Just UProp
classify _ (Builtin "implies") = Just UProp
classify _ (Builtin _) = Nothing -- 未知 builtin
