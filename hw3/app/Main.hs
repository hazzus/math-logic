module Main where

import Data.Set        as S
import Prelude         as P
import Lexer                (alexScanTokens)
import Parser               (parseLogic)
import Syntax
import ContextBuilder       (findMinContext, negateAll, removeNegation)
import Proofs               (makeProof)
import Data.List            (intercalate)


parseLine :: String -> Expression
parseLine input =
  case parseLogic $ alexScanTokens input of
    Left _     -> undefined
    Right expr -> expr

getVariables :: Expression -> Set Expression
getVariables expr =
  case expr of
    Binary _ alpha beta     -> S.union (getVariables alpha) (getVariables beta)
    Neg gamma            -> getVariables gamma
    r@(Var _)        -> S.singleton r

main :: IO ()
main = do
  line               <- getLine
  let expr           = parseLine line
  let setVars        = getVariables expr
  let vars           = toList $ setVars
  let amount         = length vars
  -- putStrLn $ show (amount, vars)
  -- putStrLn $ show expr
  let (latestVars, enough) = findMinContext (amount, vars) expr
  if P.null latestVars
    then putStrLn ":("
    else do
      let other = toList $ difference (fromList latestVars) (fromList enough)
      let notNegatedOther = removeNegation other
      let neededExpr = case head latestVars of
                         Neg (Var s) -> Neg expr
                         Var s       -> expr
                         _           -> error "I've trusted you!"
      putStrLn $ intercalate ", " (P.map show enough) ++ " |- " ++ show neededExpr
      let result = makeProof neededExpr enough notNegatedOther
      putStrLn $ unlines $ P.map show result
