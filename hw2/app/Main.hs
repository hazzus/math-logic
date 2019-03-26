module Main where

import           Axioms          (checkAxiom)
import           Info
import           Lexer           (alexScanTokens)
import           ModusPonens     (checkModusPonens)
import           Parser          (parseLogic)
import           Syntax
import           Equivalents     (equivalentAxiom, equivalentModusPonens, contraposition)
import           Deduction       (deduct, func)


import           Data.List       (elemIndex, intercalate)
import           Data.List.Split (splitOn)
import           Data.Map.Strict as M
import           Data.Set        as S
import           Prelude         hiding (lookup)
import           System.Exit     (exitSuccess)
import           System.IO       (isEOF)

data Instruments = Instruments { numered :: Map Int Expression, unique :: Map Expression Int, mp :: Map Expression [Int] }

updateInstruments :: Instruments -> Expression -> Int -> Instruments
updateInstruments instrs expr n =
  case lookup expr (unique instrs) of
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

parseLines :: [Expression] -> Int -> Instruments -> IO [Expression]
parseLines hyps n instrs = do
  endMarker <- isEOF
  if endMarker
    then return []
    else do
      line <- getLine
      if Prelude.null line then do
        tail <- parseLines hyps (n + 1) instrs
        return $! tail
      else do
        let expr = parseLine line
        -- putStrLn $ unlines $ Prelude.map show (translate hyps instrs expr)
        tail <- (parseLines hyps (n + 1)) $! (updateInstruments instrs expr n)
        return $! (translate hyps instrs expr) ++ tail

translate :: [Expression] -> Instruments -> Expression -> [Expression]
translate hyps instrs expr =
  case (checkExpression hyps instrs expr) of
                Axiom a -> equivalentAxiom expr a
                Hypothesis _ -> equivalentAxiom expr 0
                ModusPonens (a, b) -> equivalentModusPonens expr (lookup b (numered instrs))

checkExpression :: [Expression] -> Instruments -> Expression -> Information
checkExpression hyps instrs expr =
  if (axiom /= 0)
    then Axiom axiom
    else if (hypothesys /= 0)
            then Hypothesis hypothesys
            else if (modusp /= (0, 0))
                    then ModusPonens modusp
                    else undefined
  where
    axiom = checkAxiom expr
    hypothesys =
      case (elemIndex expr hyps) of
        Nothing -> 0
        Just a -> a + 1
    modusp =
      case (lookup expr (mp instrs)) of
        Nothing -> undefined
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

main :: IO ()
main = do
  -- deduct
  header <- getLine
  --putStrLn $ unlines $ Prelude.map show $ func $ parseLine header
  let split1 = splitOn "|-" header
  let lspl = length split1
  let hyps =
        if (lspl == 2)
          then (if (split1 !! 0 == "")
               then []
               else Prelude.map (parseLine) (splitOn "," (split1 !! 0)))
          else []
  let proofing = parseLine $ split1 !! (if lspl == 2 then 1 else 0)
  putStrLn $ intercalate "," (Prelude.map show hyps) ++ "|- " ++ show (Neg (Neg proofing))
  answer <- parseLines hyps 1 (Instruments M.empty M.empty M.empty)
  putStrLn $ unlines $ Prelude.map show answer
