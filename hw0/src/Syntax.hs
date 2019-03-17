module Syntax where

data BinOp = And | Or | To

instance Show BinOp where
  show And  = "&"
  show Or   = "|"
  show To   = "->"

data Expression 
    = Binary BinOp Expression Expression
    | Neg Expression
    | Var String

instance Show Expression where
  show (Binary op a b)  = "(" ++ show op ++ "," ++ show a ++ "," ++ show b ++ ")"
  show (Neg a)          = "(!" ++ show a ++ ")"
  show (Var name)       = name
