module MLTT.Syntax where

type Name = String

data Expr
  = Var Name
  | Type Int
  | Pi Name Expr Expr
  | Lam Name Expr Expr
  | App Expr Expr
  deriving (Show, Eq)

