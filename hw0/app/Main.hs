module Main where

import Syntax (Expression (..))
import Lexer (alexScanTokens)
import Parser (parseLogic)

main :: IO ()
main = do
  input <- getLine
  case parseLogic (alexScanTokens input) of
    Left err   -> putStrLn err
    Right expr -> putStrLn $ show expr

