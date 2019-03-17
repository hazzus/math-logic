module Syntax where

data BinOp
  = And
  | Or
  | To
  deriving (Eq, Ord)

instance Show BinOp where
  show And = "&"
  show Or  = "|"
  show To  = "->"

data Expression
  = Binary BinOp
           !Expression
           !Expression
  | Neg !Expression
  | Var !String
  deriving (Eq, Ord)

instance Show Expression where
  show (Binary op a b) = "(" ++ show a ++ " " ++ show op ++ " " ++ show b ++ ")"
  show (Neg a) = "!" ++ show a
  show (Var name) = name
