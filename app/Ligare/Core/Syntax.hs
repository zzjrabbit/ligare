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
  | LitBool Bool
  | PrimOp PrimOp
  | Universe Universe
  | Builtin String
  | Arrow Term Term
  | Let Name Term Term (Maybe Term)
  | IfThenElse Term Term Term
  deriving (Eq, Show)

data PrimOp
  = Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Lt
  | Gt
  | Le
  | Ge
  | Neq
  deriving (Eq, Show)
