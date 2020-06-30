module LambdaCalculus where

data Term = Var TeVar
          | Abs TeVar Term
          | App Term Term
            deriving Eq

data TeVar = TeVar String
             deriving Eq

instance Show Term where
    show (Var x)     = show x
    show (Abs x m)   = ('(':'\\':show x) ++ ('.':show m) ++ [')']
    show (App m1 m2) = ('(':show m1) ++ (' ':show m2) ++ [')']

instance Show TeVar where
    show (TeVar x) = id x