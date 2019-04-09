module Evaluator where

import Syntax
import Data.List        (elemIndex)

evaluate :: [Int] -> [Expression] -> Expression -> Bool
evaluate mask vars expr =
  case expr of
    Binary To  alpha beta -> (eval alpha) <= (eval beta)
    Binary And alpha beta -> (eval alpha) && (eval beta)
    Binary Or  alpha beta -> (eval alpha) || (eval beta)
    Neg        alpha   -> not (eval alpha)
    var            ->
      case elemIndex var vars of
        Just a  -> (mask !! a == 1)
        Nothing -> case elemIndex (Neg var) vars of
          Just a -> (mask !! a == 0)
          Nothing -> error (show var ++ show vars ++ show mask ++ show expr)
  where
    eval = evaluate mask vars
