module Main where

import           Axioms          (checkAxiom)
import           Info
import           Lexer           (alexScanTokens)
import           ModusPonens     (checkModusPonens)
import           Parser          (parseLogic)
import           Pretty          (prettyHead, prettyShow)
import           Syntax

import           Data.List       (elemIndex)
import           Data.List.Split (splitOn)
import           Data.Map.Strict as M
import           Data.Set        as S
import           Prelude         hiding (lookup)
import           System.Exit     (exitSuccess)
import           System.IO       (isEOF)

parseLine :: String -> Expression
parseLine input =
  case parseLogic $ alexScanTokens input of
    Left _     -> undefined
    Right expr -> expr

parseLines ::
     [Expression]
  -> Int
  -> Map Int Expression
  -> Map Expression Int
  -> Map Expression [Int]
  -> [(Int, Information)]
  -> Expression
  -> IO ( Int
        , Map Int Expression
        , Map Expression Int
        , Map Expression [Int]
        , [(Int, Information)]
        , Expression)
parseLines hyps n m1 m2 m3 info prev = do
  endMarker <- isEOF
  if endMarker
    then return (n - 1, m1, m2, m3, info, prev)
    else do
      line <- getLine
      let expr = parseLine line
      tail <-
        ((((parseLines hyps (n + 1) $!
            (case (lookup expr m2) of
               Nothing -> (M.insert n expr m1)
               Just _  -> m1)) $!
           (case (lookup expr m2) of
              Nothing -> (M.insert expr n m2)
              Just _  -> m2)) $!
          (case (lookup expr m2) of
             Just _ -> m3
             Nothing ->
               case expr of
                 Binary To arg1 arg2 -> insertWith (++) arg2 [n] m3
                 _                   -> m3)) $!
         (case (lookup expr m2) of
            Nothing -> (n, (checkExpression hyps m1 m2 m3 expr)) : info
            Just _  -> (n, Duplicate) : info))
          expr
      if (n /= 1 && head info == (n - 1, Wrong))
        then do
          putStrLn "Proof is incorrect"
          exitSuccess
        else return tail

checkExpression :: 
     [Expression]
  -> Map Int Expression
  -> Map Expression Int
  -> Map Expression [Int]
  -> Expression
  -> Information
checkExpression hyps m1 m2 m3 expr =
  if (axiom /= 0)
    then Axiom axiom
    else if (hypothesys /= 0)
           then Hypothesis hypothesys
           else if (mp /= (0, 0))
                  then ModusPonens mp
                  else Wrong
  where
    axiom = checkAxiom expr
    hypothesys =
      case (elemIndex expr hyps) of
        Nothing -> 0
        Just a  -> a + 1
    mp =
      case (lookup expr m3) of
        Nothing -> (0, 0)
        Just a  -> takeFirstCorrect $ Prelude.map finder a
    finder x =
      case (lookup x m1) of
        Just (Binary To alpha expr) ->
          case (lookup alpha m2) of
            Just i  -> (x, i)
            Nothing -> (x, 0)
        Nothing -> undefined
    takeFirstCorrect ((num, 0):xs) = takeFirstCorrect xs
    takeFirstCorrect (x:xs)        = x
    takeFirstCorrect []            = (0, 0)

main :: IO ()
main = do
  header <- getLine
  let split1 = splitOn "|-" header
  let lspl = length split1
  let hyps =
        if (lspl == 2)
          then (if (split1 !! 0 == "")
                  then []
                  else Prelude.map (parseLine) (splitOn "," (split1 !! 0)))
          else []
  let proofing =
        parseLine $
        split1 !!
        (if (lspl == 2)
           then 1
           else 0)
  (amount, m1, m2, m3, lines, lastExpr) <-
    parseLines hyps 1 M.empty M.empty M.empty [] (Var "KEK")
  -- putStrLn $ show amount
  if (amount == 0 || head lines == (amount, Wrong) || lastExpr /= proofing)
    then putStrLn "Proof is incorrect"
    else case (M.lookup proofing m2) of
           Nothing -> putStrLn "Proof is incorrect"
           Just a -> do
             putStrLn $ prettyHead hyps proofing
             let croppedToProof = cropDuplicates m1 proofing lines
             let used = collectUsed croppedToProof
             let filtered =
                   Prelude.filter (\(n, _) -> S.member n used) croppedToProof
             let prepared = reverse $ Prelude.map (prepFunc m1) filtered
             let realNumbers =
                   M.fromList $
                   Prelude.map
                     (\(realNum, (num, _, _)) -> (num, realNum))
                     (zip [1 ..] prepared)
             putStr $ unlines $ Prelude.map (prettyShow realNumbers) prepared

prepFunc m1 (x, info) =
  case (M.lookup x m1) of
    Nothing -> undefined
    Just e  -> (x, info, e)

cropDuplicates ::
     Map Int Expression
  -> Expression
  -> [(Int, Information)]
  -> [(Int, Information)]
cropDuplicates m1 proofing lst@((num, info):xs) =
  case info of
    Duplicate -> cropDuplicates m1 proofing xs
    _ ->
      case (lookup num m1) of
        Nothing -> undefined
        Just expr ->
          if (expr == proofing)
            then lst
            else cropDuplicates m1 proofing xs
cropDuplicates _ _ [] = undefined

collectUsed :: [(Int, Information)] -> Set Int
collectUsed lst = helper (S.insert (length lst) S.empty) lst
  where
    helper set [] = set
    helper set ((num, ModusPonens (mp1, mp2)):xs) =
      if (S.member num set)
        then (helper $! S.insert mp1 $! S.insert mp2 set) xs
        else helper set xs
    helper set (x:xs) = helper set xs
