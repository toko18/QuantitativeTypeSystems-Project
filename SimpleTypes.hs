module SimpleTypes where

import LambdaCalculus

data Type0 = TVar TyVar | TAp Type0 Type0
            deriving Eq

data TyVar = TyVar String
             deriving Eq

type EqSet = [(Type0, Type0)]

type Basis = [(TeVar, Type0)]

type Sub = (TyVar, Type0)

type Subst = [Sub]

data Unifier = Uni Subst | FAIL
               deriving (Eq, Show)

instance Show Type0 where
    show (TVar a)    = show a
    show (TAp t1 t2) = ('(':show t1) ++ ('-':'>':show t2) ++ [')']

instance Show TyVar where
    show (TyVar a) = id a

-------Type Unification-------

-- Given a Sub s=(a,t) and a simple type T0, replaces all free
-- occurrences of the type variable a in the type T0 with type t.
subst :: Sub -> Type0 -> Type0
subst (a1, t) (TVar a2) | a1 == a2  = t
                        | otherwise = TVar a2
subst s (TAp t1 t2)                 = TAp (subst s t1) (subst s t2)

-- Given a Sub s=(a,t) and an set of equations eqset, replaces all free
-- occurrences of the type variable a in the types in eqset with type t.
substE :: Sub -> EqSet -> EqSet
substE _ []           = []
substE s ((t1,t2):ts) = (t1',t2'):ts'
                     where t1' = subst s t1
                           t2' = subst s t2
                           ts' = substE s ts

-- Given a Sub s=(a,t) and an a type substitution subst, replaces all free
-- occurrences of the type variable a in the types in subst with type t.
substS :: Sub -> Subst -> Subst
substS _ []           = []
substS s ((t1,t2):ts) = (t1',t2'):ts'
                     where TVar t1' = subst s (TVar t1)
                           t2'      = subst s t2
                           ts'      = substS s ts

-- Checks if a type variable occurs (free) in a simple type.
isFVType :: TyVar -> Type0 -> Bool
isFVType a1 (TVar a2)  = a1 == a2
isFVType a (TAp t1 t2) = isFVType a t1 || isFVType a t2

-- Checks if a type variable occurs (free) in an equation set.
isFVTypeE :: TyVar -> EqSet -> Bool
isFVTypeE _ []            = False
isFVTypeE a ((t1, t2):ts) = isFVType a t1 || isFVType a t2 || isFVTypeE a ts

-- Checks if a type variable occurs (free) in a type substitution.
isFVTypeS :: TyVar -> Subst -> Bool
isFVTypeS _ []            = False
isFVTypeS a ((t1, t2):ts) = isFVType a (TVar t1) || isFVType a t2 || isFVTypeS a ts

-- Unification algorithm.
unify :: (EqSet, Unifier) -> (EqSet, Unifier)
unify ([], u)                          = ([], u)
unify ((t1, t2):ts, u) | t1 == t2      = unify (ts, u)
unify ((TAp t1 t2, TAp t1' t2'):ts, u) = unify ((t1, t1'):(t2, t2'):ts, u)
unify ((TAp t1 t2, TVar a):ts, u)      = unify ((TVar a, TAp t1 t2):ts, u)
unify ((TVar a, t):ts, Uni s)
     | isFVType a t                    = error ("UNIFICATION FAIL: " ++ show ((TVar a, t):ts, Uni s)) -- ([], FAIL)
     | isFVTypeE a ts || isFVTypeS a s = let ts' = substE (a, t) ts
                                             s'  = substS (a, t) s
                                             in unify (ts', Uni ((a, t):s'))
     | otherwise                       = unify (ts, Uni ((a, t):s))

-------Milner's Type-Inference Algorithm-------

substB :: Sub -> Basis -> Basis
substB _ []         = []
substB s ((x,t):ds) = (x, subst s t):substB s ds

substBasis :: Subst -> Basis -> Basis
substBasis [] b     = b
substBasis (s:ts) b = substBasis ts (substB s b)

isInBasis :: TeVar -> Basis -> Bool
isInBasis _ []            = False
isInBasis x1 ((x2, _):ds) = x1 == x2 || isInBasis x1 ds

findInBasis :: TeVar -> Basis -> Type0
findInBasis x1 ((x2, t):ds) | x1 == x2  = t
                            | otherwise = findInBasis x1 ds

rmFromBasis :: TeVar -> Basis -> Basis
rmFromBasis _ []                        = []
rmFromBasis x1 ((x2, t):ds) | x1 == x2  = rmFromBasis x1 ds
                            | otherwise = (x2, t):rmFromBasis x1 ds

mergeBasis :: Basis -> Basis -> EqSet
mergeBasis [] _                           = []
mergeBasis ((x,t):ds) b2 | isInBasis x b2 = (t, findInBasis x b2):mb
                         | otherwise      = mb
                        where mb = mergeBasis ds b2

substTyVar :: Subst -> TyVar -> Type0
substTyVar [] a                        = TVar a
substTyVar ((a1, t):ts) a2 | a1 == a2  = t
                           | otherwise = substTyVar ts a2

typeInf :: Term -> Int -> (Basis, Type0, Int)
typeInf (Var x) n0     = ([(x, TVar (TyVar ('a':(show n0))))], TVar (TyVar ('a':(show n0))), n0+1)
typeInf (App m1 m2) n0 = (substBasis s b, substTyVar s (TyVar ('a':(show n2))), n2+1)
                      where (b1, t1, n1) = typeInf m1 n0
                            (b2, t2, n2) = typeInf m2 n1
                            b            = b1 ++ b2
                            u            = mergeBasis b1 b2
                            ([], Uni s)  = unify (((t1, TAp t2 (TVar (TyVar ('a':(show n2))))):u), Uni [])
typeInf (Abs x m) n0
       | isInBasis x b = (rmFromBasis x b, TAp (findInBasis x b) t, n1)
       | otherwise     = (b, TAp (TVar (TyVar ('a':(show n1)))) t, n1+1)
      where (b, t, n1) = typeInf m n0