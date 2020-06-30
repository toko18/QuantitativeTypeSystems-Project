{
module Main where

import Data.Char
import LambdaCalculus
import SimpleTypes
import QuantRank2IntersectionTypes
}

%name parse
%tokentype { Token }
%error { parseError }

%token 
  '\\'            { TokenLambda }
  '.'             { TokenPoint }
  ' '             { TokenSpace }
  var             { TokenVar $$ }
  '('             { TokenOB }
  ')'             { TokenCB }
  typeinf0        { TokenInf0 }
  qtypeinf2       { TokenQInf2 }

%left ' '

%%

Exp   : TyInf                          { TyInf $1 }
      | Term                           { Term $1 }

Term  : var                            { Var (TeVar $1) }
      | Abs                            { $1 }
      | App                            { $1 }
      | '(' Term ')'                   { $2 }

Abs   : '\\' var '.' Term              { Abs (TeVar $2) $4 }

App   : Term ' ' Term                  { App $1 $3 }

TyInf : typeinf0 '(' Term ')'          { TyInf0 $3 (typeInf $3 0) }
      | qtypeinf2 '(' Term ')'         { QTyInf2 $3 (quantR2typeInf $3 0) }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Exp
      = TyInf TyInf
      | Term Term

data TyInf
      = TyInf0 Term (Basis, Type0, Int)
      | QTyInf2 Term (Env, Type2, Int ,Int)

type Neutral = [TeVar]

instance Show Exp where
    show (TyInf x) = show x
    show (Term x)  = "\tTerm = " ++ show x ++ ['\n']

instance Show TyInf where
    show (TyInf0 term (basis, t0, _)) = "\tTerm = " ++ show term ++ "\n\tBasis = " ++ show basis ++ "\n\tType = " ++ show t0 ++ ['\n']
    show (QTyInf2 term (env, t2, c, _)) = "\tTerm = " ++ show term ++ "\n\tEnvironment = " ++ show env ++ "\n\tType = " ++ show t2 ++ "\n\tCount = " ++ show c ++ ['\n']

data Token
      = TokenLambda
      | TokenPoint
      | TokenSpace
      | TokenVar String
      | TokenOB
      | TokenCB
      | TokenInf0
      | TokenQInf2
      deriving Show

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
 | isAlphaNum c = lexVar (c:cs)
lexer ('\\':cs) = TokenLambda : lexer cs
lexer ('.':cs)  = TokenPoint : lexer cs
lexer (' ':cs)  = TokenSpace : lexer cs
lexer ('(':cs)  = TokenOB : lexer cs
lexer (')':cs)  = TokenCB : lexer cs

lexVar cs =
   case span isAlphaNum cs of
      ("ti0",rest) -> TokenInf0 : lexer rest
      ("qti2",rest) -> TokenQInf2 : lexer rest
      (var,rest)   -> TokenVar var : lexer rest

main = do getLine >>= print . parse . lexer
          main
}