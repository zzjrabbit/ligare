module Ligare.Checker.Context where

import Ligare.Core.Syntax

type Context = [Term]

emptyCtx :: Context
emptyCtx = []

extendCtx :: Term -> Context -> Context
extendCtx = (:)

lookupCtx :: Int -> Context -> Maybe Term
lookupCtx i ctx
  | i < 0 = Nothing
  | i < length ctx = Just (ctx !! i)
  | otherwise = Nothing

