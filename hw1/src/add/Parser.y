{
module Parser where

import Syntax
import Lexer
}

%name parseLogic
%tokentype  { Token }
%error      { parseError }
%monad      { Either String } { >>= } { return }

%token
    '&'     { TokenAnd }
    '|'     { TokenOr }
    '->'    { TokenTo }
    '!'     { TokenNeg }
    '('     { TokenLBrace }
    ')'     { TokenRBrace }
    VAR     { TokenVar $$ }
%%

Expression
    : Disjunction                               { $1 }
    | Disjunction '->' Expression               { Binary To $1 $3 }

Disjunction
    : Conjunction                               { $1 }
    | Disjunction '|' Conjunction               { Binary Or $1 $3 }

Conjunction
    : Negation                                  { $1 }
    | Conjunction '&' Negation                  { Binary And $1 $3 }

Negation
    : '!' Negation                              { Neg $2 }
    | VAR                                       { Var $1 }
    | '(' Expression ')'                        { $2 }

{
parseError = fail "Parse error"
}
