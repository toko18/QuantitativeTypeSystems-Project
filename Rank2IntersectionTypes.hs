module Rank2IntersectionTypes where

import LambdaCalculus
import SimpleTypes

data Type1 = T1_0 Type0 | Inters Type1 Type1
             deriving Eq

data Type2 = T2_0 Type0 | T2Ap Type1 Type2
             deriving Eq

type Ineq = (Type2, Type1)

type SatProblem = [Ineq]

type Env = [(TeVar, Type1)]

instance Show Type1 where
    show (T1_0 t)       = show t
    show (Inters t1 t2) = ('(':show t1) ++ ('/':'\\':show t2) ++ [')']

instance Show Type2 where
    show (T2_0 t)     = show t
    show (T2Ap t1 t2) = ('(':show t1) ++ ('-':'>':show t2) ++ [')']

-------Transformation of <=2,1-satisfaction problems into unification problems (based on Corollary 33 (Cap.3.1), Rank 2 type systems and recursive definitions)-------

transformSat :: (SatProblem, EqSet, Int) -> (SatProblem, EqSet, Int)
transformSat ([], eqs, n0)                                       = ([], eqs, n0)
transformSat ((T2Ap t1 t2, T1_0 (TVar a)):ts, eqs, n0)           = transformSat ((T2_0 t0, t1):(t2, T1_0 t0'):ts, (TVar a, TAp t0 t0'):eqs, n0+2)
                                                                where t0  = TVar (TyVar ('a':(show n0)))
                                                                      t0' = TVar (TyVar ('a':(show (n0+1))))
transformSat ((T2_0 (TAp t1 t2), T1_0 (TVar a)):ts, eqs, n0)     = transformSat ((T2_0 t0, T1_0 t1):(T2_0 t2, T1_0 t0'):ts, (TVar a, TAp t0 t0'):eqs, n0+2)
                                                                where t0  = TVar (TyVar ('a':(show n0)))
                                                                      t0' = TVar (TyVar ('a':(show (n0+1))))
transformSat ((T2Ap t1 t2, T1_0 (TAp t0 t0')):ts, eqs, n0)       = transformSat ((T2_0 t0, t1):(t2, T1_0 t0'):ts, eqs, n0)
transformSat ((T2_0 (TAp t1 t2), T1_0 (TAp t0 t0')):ts, eqs, n0) = transformSat ((T2_0 t0, T1_0 t1):(T2_0 t2, T1_0 t0'):ts, eqs, n0)
transformSat ((t2, Inters t1 t1'):ts, eqs, n0)                   = transformSat ((t2, t1):(t2, t1'):ts, eqs, n0)
transformSat ((T2_0 (TVar a), T1_0 t0):ts, eqs, n0)              = transformSat (ts, (TVar a, t0):eqs, n0)

-------Type-Inference Algorithm (based on Def.36 (Cap.3.2), Rank 2 type systems and recursive definitions)-------

listToInters :: [Type1] -> Type1
listToInters [t1]    = t1
listToInters (t1:ts) = Inters (listToInters ts) t1

subst1 :: Sub -> Type1 -> Type1
subst1 s (T1_0 t0)       = T1_0 (subst s t0)
subst1 s (Inters t1 t1') = Inters (subst1 s t1) (subst1 s t1')

subst2 :: Sub -> Type2 -> Type2
subst2 s (T2_0 t0)    = T2_0 (subst s t0)
subst2 s (T2Ap t1 t2) = T2Ap (subst1 s t1) (subst2 s t2)

substty2 :: Subst -> Type2 -> Type2
substty2 [] t2     = t2
substty2 (s:ts) t2 = substty2 ts (subst2 s t2)

substEn :: Sub -> Env -> Env
substEn _ []         = []
substEn s ((x,t):es) = (x, subst1 s t):substEn s es

substEnv :: Subst -> Env -> Env
substEnv [] e     = e
substEnv (s:ts) e = substEnv ts (substEn s e)

isInEnv :: TeVar -> Env -> Bool
isInEnv _ []            = False
isInEnv x1 ((x2, _):es) = x1 == x2 || isInEnv x1 es

findAllInEnv :: TeVar -> Env -> [Type1]
findAllInEnv _ []                        = []
findAllInEnv x1 ((x2, t):es) | x1 == x2  = t:findAllInEnv x1 es
                             | otherwise = findAllInEnv x1 es

findInEnv :: TeVar -> Env -> Type1
findInEnv x1 ((x2, t):es) | x1 == x2  = t
                          | otherwise = findInEnv x1 es

rmFromEnv :: TeVar -> Env -> Env
rmFromEnv _ []                        = []
rmFromEnv x1 ((x2, t):es) | x1 == x2  = rmFromEnv x1 es
                          | otherwise = (x2, t):rmFromEnv x1 es

mergeEnv :: Env -> Env
mergeEnv []           = []
mergeEnv ((x, t1):es) = (x, listToInters (findAllInEnv x ((x, t1):es))):mergeEnv (rmFromEnv x es)

genPPSat :: Type1 -> Term -> Int -> (Env, SatProblem, Int)
genPPSat (T1_0 t0) m n0       = (env, [(t, T1_0 t0)], n1)
                             where (env, t, n1) = r2typeInf m n0
genPPSat (Inters t1 t1') m n0 = (mergeEnv (envm1++envm2), sat1++sat2, n2)
                             where (envm1, sat1, n1) = genPPSat t1 m n0
                                   (envm2, sat2, n2) = genPPSat t1' m n1

r2typeInf :: Term -> Int -> (Env, Type2, Int)
r2typeInf (Var x) n0     = let t0 = TVar (TyVar ('a':(show n0))) in ([(x, T1_0 t0)], T2_0 t0, n0+1)
r2typeInf (App m1 m2) n0 = let (env1, t, n1) = r2typeInf m1 n0 in
                               case t of
                                   T2_0 (TVar t2_0)   -> (substEnv s env, substty2 s (T2_0 t0'), n3)
                                                     where (env2, t2, n2) = r2typeInf m2 n1
                                                           env            = mergeEnv (env1++env2)
                                                           t0             = TVar (TyVar ('a':(show n2)))
                                                           t0'            = TVar (TyVar ('a':(show (n2+1))))
                                                           ([], eqs, n3)  = transformSat ([(t2, T1_0 t0)], [((TVar t2_0), TAp t0 t0')], n2+2)
                                                           ([], Uni s)    = unify (eqs, Uni [])
                                   T2Ap t_1 t_2       -> (substEnv s (mergeEnv (env1++envs)), substty2 s t_2, n3)
                                                     where (envs, sat, n2) = genPPSat t_1 m2 n1
                                                           ([], eqs, n3)   = transformSat (sat, [], n2)
                                                           ([], Uni s)     = unify (eqs, Uni [])
                                   T2_0 (TAp t_1 t_2) -> (substEnv s (mergeEnv (env1++envs)), substty2 s (T2_0 t_2), n3)
                                                     where (envs, sat, n2) = genPPSat (T1_0 t_1) m2 n1
                                                           ([], eqs, n3)   = transformSat (sat, [], n2)
                                                           ([], Uni s)     = unify (eqs, Uni [])
r2typeInf (Abs x m) n0
         | isInEnv x env = (rmFromEnv x env, T2Ap (findInEnv x env) t2, n1)
         | otherwise     = (env, T2Ap (T1_0 (TVar (TyVar ('a':(show n1))))) t2, n1+1)
        where (env, t2, n1) = r2typeInf m n0