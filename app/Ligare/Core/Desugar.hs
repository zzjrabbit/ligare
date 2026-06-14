module Ligare.Core.Desugar where

import Ligare.Core.Syntax

desugar :: Term -> Term
desugar (Func _fname params mRet _preconds _postconds body) =
  let funcBody = foldr (\(_, _) b -> Lam b) body params
      funcType =
        foldr
          ( \(pn, mc) b -> case mc of
              Just c -> Pi pn c b
              Nothing -> Pi pn (Builtin "data") b
          )
          (maybe (Builtin "data") id mRet)
          (reverse params)
   in Annot funcBody funcType
desugar other = other
