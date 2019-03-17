module Pretty where

import           Data.List       (intercalate)
import           Data.Map.Strict hiding (map)
import           Info
import           Prelude         hiding (lookup)
import           Syntax

prettyHead :: [Expression] -> Expression -> String
prettyHead hyps proofing =
  intercalate ", " (map show hyps) ++ " |- " ++ show proofing

prettyShow :: Map Int Int -> (Int, Information, Expression) -> String
prettyShow map (num, ModusPonens (mp1, mp2), expr) =
  "[" ++
  (present num) ++
  ". " ++ "M.P. " ++ (present mp1) ++ ", " ++ (present mp2) ++ "] " ++ show expr
  where
    present x =
      case (lookup x map) of
        Nothing -> undefined
        Just a  -> show a
prettyShow map (num, info, expr) =
  "[" ++ present num ++ ". " ++ show info ++ "] " ++ show expr
  where
    present x =
      case (lookup x map) of
        Nothing -> undefined
        Just a  -> show a
