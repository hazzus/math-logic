module ContextBuilder where

import Syntax
import Evaluator     (evaluate)

masks1 = [[0], [1]]

masks2 = [[0, 0], [0, 1], [1, 0], [1, 1]]

masks3 = [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0], [0, 1, 1], [1, 0, 1], [1, 1, 0], [1, 1, 1]]

chooseByMask :: [Expression] -> [Int] -> [Expression]
chooseByMask (v : vars) (cur : other) =
  if cur == 1
    then v : chooseByMask vars other
    else chooseByMask vars other
chooseByMask []         []            = []

findMinContext :: (Int, [Expression]) -> Expression -> ([Expression], [Expression])
findMinContext a b =
  case findPositiveMinContext a b of
    Just answer  -> answer
    Nothing      -> findNegativeMinContext a b

findPositiveMinContext :: (Int, [Expression]) -> Expression -> Maybe ([Expression], [Expression])
findPositiveMinContext (amount, vars) expr =
  if amount == 1
    then helper masks1
    else if amount == 2
           then helper masks2
           else helper masks3
  where
    helper :: [[Int]] -> Maybe ([Expression], [Expression])
    helper (m : ms) =
      if valid m
        then Just (vars, chooseByMask vars m)
        else helper ms
    helper []       = Nothing

    valid :: [Int] -> Bool
    valid fixingMask = validateAll $ genValueMasks fixingMask

    validateAll :: [[Int]] -> Bool
    validateAll (m : ms) = evaluate m vars expr && validateAll ms
    validateAll []       = True


findNegativeMinContext :: (Int, [Expression]) -> Expression -> ([Expression], [Expression])
findNegativeMinContext (amount, varss) e =
  if amount == 1
    then helper masks1
    else if amount == 2
           then helper masks2
           else helper masks3
  where
    vars = negateAll varss
    expr = Neg e
    helper :: [[Int]] -> ([Expression], [Expression])
    helper (m : ms) =
      if valid m
        then (vars, chooseByMask vars m)
        else helper ms
    helper []       = ([],[])


    valid :: [Int] -> Bool
    valid fixingMask = validateAll $ genValueMasks fixingMask

    validateAll :: [[Int]] -> Bool
    validateAll (m : ms) = evaluate m vars expr && validateAll ms
    validateAll []       = True

genValueMasks :: [Int] -> [[Int]]
genValueMasks (m : ms)  =
  if m == 1
    then map (1 :) (genValueMasks ms)
    else map (0 :) (genValueMasks ms) ++ map (1 :) (genValueMasks ms)
genValueMasks []        = [[]]

negateAll :: [Expression] -> [Expression]
negateAll (cur : exprs) = (Neg cur) : negateAll exprs
negateAll []            = []

removeNegation :: [Expression] -> [Expression]
removeNegation ((Neg cur) : exprs) = cur : removeNegation exprs
removeNegation (cur : exprs)       = cur : removeNegation exprs
removeNegation []                  = []
