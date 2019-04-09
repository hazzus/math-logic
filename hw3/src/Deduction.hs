module Deduction where

import Syntax
import Lexer
import Parser
import Info
import Axioms
import Prelude hiding (lookup)
import Data.Map.Strict as M
import Data.List (elemIndex)

data Instruments = Instruments { numered :: Map Int Expression, unique :: Map Expression Int, mp :: Map Expression [Int] } deriving Show

updateInstruments :: Instruments -> Expression -> Int -> Instruments
updateInstruments instrs expr n =
  case M.lookup expr (unique instrs) of
    Nothing -> Instruments (M.insert n expr (numered instrs)) (M.insert expr n (unique instrs)) nmp
    Just _ -> instrs
  where
    nmp = case expr of
      Binary To arg1 arg2 -> insertWith (++) arg2 [n] (mp instrs)
      _ -> (mp instrs)

deductImplementation :: [Expression] -> Expression -> Int -> [Expression] -> Instruments -> [Expression]
deductImplementation hyps last n (expr : proof) instrs =
  (convertDeduction hyps last instrs expr) ++ ((deductImplementation hyps last (n + 1) proof) $! (updateInstruments instrs expr n))
deductImplementation _ _ _ [] _ = []


convertDeduction :: [Expression] -> Expression -> Instruments -> Expression -> [Expression]
convertDeduction hyps last instrs expr =
  if expr == last
    then
      [
        Binary To expr (Binary To expr expr),
        Binary To (Binary To expr (Binary To expr expr)) (Binary To (Binary To expr (Binary To (Binary To expr expr) (expr))) (Binary To expr expr)),
        Binary To (Binary To expr (Binary To (Binary To expr expr) expr)) (Binary To expr expr),
        Binary To expr (Binary To (Binary To expr expr) expr),
        Binary To expr expr
      ]
    else
      case (M.lookup expr (unique instrs)) of
        Just _ -> []
        Nothing -> case (checkExpression hyps instrs expr) of
                    Axiom _            -> axHypDeduct last expr
                    Hypothesis _       -> axHypDeduct last expr
                    ModusPonens (a, b) -> mpDeduct a b instrs last expr
                    Wrong              -> [ Binary To (Var "YOU PROEBALSA") expr]

axHypDeduct last expr =
  [
    expr,
    Binary To expr (Binary To last expr),
    Binary To last expr
  ]

mpDeduct a b instrs last expr =
    [
      Binary To (Binary To last alpha) (Binary To (Binary To last alphaToBeta) (Binary To last expr)),
      Binary To (Binary To last alphaToBeta) (Binary To last expr),
      Binary To last expr
    ]
  where
    alphaToBeta = case (M.lookup a (numered instrs)) of
          Nothing -> undefined
          Just x  -> x
    alpha = case (M.lookup b (numered instrs)) of
                    Nothing -> undefined
                    Just x  -> x

deduct :: ([Expression], [Expression]) -> [Expression]
deduct (hyps, proof) =
  deductImplementation hyps (last hyps) 1 proof (Instruments M.empty M.empty M.empty)


checkExpression :: [Expression] -> Instruments -> Expression -> Information
checkExpression hyps instrs expr =
  if (axiom /= 0)
    then Axiom axiom
    else if (hypothesys /= 0)
            then Hypothesis hypothesys
            else ModusPonens modusp
  where
    axiom = checkAxiom expr
    hypothesys =
      case (elemIndex expr hyps) of
        Nothing -> 0
        Just a -> a + 1
    modusp =
      case (lookup expr (mp instrs)) of
        Nothing -> (0, 0)
        Just a -> takeFirstCorrect $ Prelude.map finder a
    finder x =
      case (lookup x (numered instrs)) of
        Just (Binary To alpha expr) ->
          case (lookup alpha (unique instrs)) of
            Just i -> (x, i)
            Nothing -> (x, 0)
        Nothing -> undefined
    takeFirstCorrect ((_, 0):xs) = takeFirstCorrect xs
    takeFirstCorrect (x:_) = x
    takeFirstCorrect [] = error $ show hyps ++ " " ++ show instrs
