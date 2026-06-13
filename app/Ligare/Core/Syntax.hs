module Ligare.Core.Syntax where

data Universe
  = UData
  | UProp
  | UTheorem
  | UProof
  deriving (Eq, Show)

type Name = String

data Term
  = Var Int
  | App Term Term
  | Lam Term
  | Constraint Term Term
  | LitInt Integer
  | PrimOp PrimOp
  | Universe Universe
  | Builtin String
  deriving (Eq, Show)

data PrimOp
  = Add | Sub | Mul | Div | Mod
  | Eq | Lt | Gt | Le | Ge | Neq
  deriving (Eq, Show)

