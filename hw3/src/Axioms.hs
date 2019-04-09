module Axioms where

import           Syntax

-- Checking if it is an axiom
checkAxiom :: Expression -> Int
checkAxiom expr =
  case expr of
    (Binary To arg1 (Binary To arg2 arg3))
      | (arg1 == arg3) -> 1
    (Binary To (Binary To arg1 arg2) (Binary To (Binary To arg3 (Binary To arg4 arg5)) (Binary To arg6 arg7)))
      | (arg1 == arg3 && arg3 == arg6) && (arg2 == arg4) && (arg5 == arg7) -> 2
    (Binary To arg1 (Binary To arg2 (Binary And arg3 arg4)))
      | (arg1 == arg3) && (arg2 == arg4) -> 3
    (Binary To (Binary And arg1 arg2) arg3)
      | (arg1 == arg3) -> 4
      | (arg2 == arg3) -> 5
    (Binary To arg1 (Binary Or arg2 arg3))
      | (arg1 == arg2) -> 6
      | (arg1 == arg3) -> 7
    (Binary To (Binary To arg1 arg2) (Binary To (Binary To arg3 arg4) (Binary To (Binary Or arg5 arg6) arg7)))
      | (arg1 == arg5) && (arg2 == arg4 && arg4 == arg7) && (arg3 == arg6) -> 8
    (Binary To (Binary To arg1 arg2) (Binary To (Binary To arg3 (Neg arg4)) (Neg arg5)))
      | (arg1 == arg3 && arg3 == arg5) && (arg2 == arg4) -> 9
    (Binary To (Neg (Neg arg1)) arg2)
      | (arg1 == arg2) -> 10
    _ -> 0
