module Ligare.Checker.Context where

import Ligare.Core.Syntax

type Context = [(String, Term)]

emptyCtx :: Context
emptyCtx = []

extend :: String -> Term -> Context -> Context
extend x t ctx = (x, t) : ctx

lookupVar :: String -> Context -> Maybe Term
lookupVar = lookup

