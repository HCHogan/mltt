module MLTT.NbE where

import MLTT.Syntax

data Value
  = VNe Neutural
  | VType Int
  | VPi Value (Value -> Value)

data Neutural
  = NVar Name
  | NApp Neutural Value
