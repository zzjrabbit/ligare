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
  | LitInt Integer
  | LitBool Bool
  | PrimOp PrimOp
  | Universe Universe
  | Builtin Name
  | Pi Name Term Term
  | Let Name Term Term (Maybe Term)
  | IfThenElse Term Term Term
  | Refine Name Term Term
  | Annot Term Term
  | ByProof Term Term
  | AutoProof
  | RefParam
  | Func Name [(Name, Maybe Term)] (Maybe Term) [Term] [Term] Term
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
