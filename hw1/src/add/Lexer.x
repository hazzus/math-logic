{
module Lexer where
}

%wrapper "basic"

$digit = 0-9
$chars = [A-Z]
$newline = [\n]

tokens :-
    $white+                     ;
    &                           { \s -> TokenAnd }
    \|                          { \s -> TokenOr }
    "->"                        { \s -> TokenTo }
    !                           { \s -> TokenNeg }
    \(                          { \s -> TokenLBrace }
    \)                          { \s -> TokenRBrace }
    $chars [$chars $digit \']*  { \s -> TokenVar s }

{


data Token
    = TokenAnd
    | TokenOr
    | TokenTo
    | TokenNeg
    | TokenLBrace
    | TokenRBrace
    | TokenVar String
    deriving (Eq, Show)

}
