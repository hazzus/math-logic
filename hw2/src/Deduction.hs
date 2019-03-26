module Deduction where

import Syntax
import Lexer
import Parser
import Info
import Axioms
import Prelude hiding (lookup)
import Data.Map.Strict as M
import Data.List.Split (splitOn)
import System.IO (isEOF)
import Data.List (elemIndex)
import Equivalents

data Instruments = Instruments { numered :: Map Int Expression, unique :: Map Expression Int, mp :: Map Expression [Int] }

updateInstruments :: Instruments -> Expression -> Int -> Instruments
updateInstruments instrs expr n =
  case M.lookup expr (unique instrs) of
    Nothing -> Instruments (M.insert n expr (numered instrs)) (M.insert expr n (unique instrs)) nmp
    Just _ -> instrs
  where
    nmp = case expr of
      Binary To arg1 arg2 -> insertWith (++) arg2 [n] (mp instrs)
      _ -> (mp instrs)


parseLine :: String -> Expression
parseLine input =
  case parseLogic $ alexScanTokens input of
    Left _     -> undefined
    Right expr -> expr

parseLines :: [Expression]-> Expression -> Int -> Instruments -> IO [Expression]
parseLines hyps last n instrs = do
  endMarker <- isEOF
  if endMarker
    then return []
    else do
      line <- getLine
      let expr = parseLine line
      tail <- (parseLines hyps last (n + 1)) $! (updateInstruments instrs expr n)
      return $! (convertDeduction hyps last instrs expr) ++ tail

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

deduct :: IO ()
deduct = do
  header <- getLine
  -- putStrLn $ unlines $ Prelude.map show $ func $ parseLine header
  let split1 = splitOn "|-" header
  let lspl = length split1
  let hyps =
        if (lspl == 2)
          then (if (split1 !! 0 == "")
               then []
               else Prelude.map (parseLine) (splitOn "," (split1 !! 0)))
          else []
  let proofing = parseLine $ split1 !! (if lspl == 2 then 1 else 0)
  answer <- parseLines hyps (last hyps) 1 (Instruments M.empty M.empty M.empty)
  putStrLn $ unlines $ Prelude.map show answer

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
    takeFirstCorrect [] = undefined

func (Binary To arg1 arg2) =
  contraposition arg1 arg2
