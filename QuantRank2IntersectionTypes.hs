module QuantRank2IntersectionTypes where

import LambdaCalculus
import SimpleTypes

-- Rank 1 intersection types.
data Type1 = T1_0 Type0 | Inters Type1 Type1
             deriving Eq

-- Rank 2 intersection types.
data Type2 = T2_0 Type0 | T2Ap Type1 Type2
             deriving Eq

-- Constraints (inequalities or equalities) of <=2,1-satisfaction problems.
data Constraint = Ineq (Type2, Type1) | Equal (Type2, Type1)

-- <=2,1-satisfaction problems.
type SatProblem = [Constraint]

-- Environments.
type Env = [(TeVar, Type1)]

instance Show Type1 where
    show (T1_0 t)       = show t
    show (Inters t1 t2) = ('(':show t1) ++ ('/':'\\':show t2) ++ [')']

instance Show Type2 where
    show (T2_0 t)     = show t
    show (T2Ap t1 t2) = ('(':show t1) ++ ('-':'>':show t2) ++ [')']

-- Note: every Int appearing in the last position of a returning tuple or
-- as the last argument of a function, is for generating new type variables (a1, a2, a3, ...).


-------Transformation of <=2,1-satisfaction problems into unification problems-------

-- Applies a substitution to a <=2,1-satisfaction problem.
substSat :: Sub -> SatProblem -> SatProblem
substSat _ []                  = []
substSat s (Ineq (t2,t1):sat)  = Ineq (subst2 s t2, subst1 s t1):substSat s sat
substSat s (Equal (t2,t1):sat) = Equal (subst2 s t2, subst1 s t1):substSat s sat

-- Transformation of <=2,1-satisfaction problems into unification problems, with counting of quantitative information.
-- (The third element of the returning tuple is the counter of the quantitative information.)
transformSat :: (SatProblem, EqSet, Int, Int) -> (SatProblem, EqSet, Int, Int)
transformSat ([], eqs, count, n0)                                            = ([], eqs, count, n0)
transformSat (Ineq (T2Ap t1 t2, T1_0 (TVar a)):ts, eqs, count, n0)           = transformSat (Ineq (T2_0 t0, t1):Ineq (t2, T1_0 t0'):Equal (T2_0 (TVar a), T1_0 (TAp t0 t0')):ts, eqs, count, n0+2)
                                                                            where t0  = TVar (TyVar ('a':(show n0)))
                                                                                  t0' = TVar (TyVar ('a':(show (n0+1))))
transformSat (Ineq (T2_0 (TAp t1 t2), T1_0 (TVar a)):ts, eqs, count, n0)     = transformSat (Ineq (T2_0 t0, T1_0 t1):Ineq (T2_0 t2, T1_0 t0'):Equal (T2_0 (TVar a), T1_0 (TAp t0 t0')):ts, eqs, count, n0+2)
                                                                            where t0  = TVar (TyVar ('a':(show n0)))
                                                                                  t0' = TVar (TyVar ('a':(show (n0+1))))
transformSat (Ineq (T2Ap t1 t2, T1_0 (TAp t0 t0')):ts, eqs, count, n0)       = transformSat (Ineq (T2_0 t0, t1):Ineq (t2, T1_0 t0'):ts, eqs, count+1, n0)
transformSat (Ineq (T2_0 (TAp t1 t2), T1_0 (TAp t0 t0')):ts, eqs, count, n0) = transformSat (Ineq (T2_0 t0, T1_0 t1):Ineq (T2_0 t2, T1_0 t0'):ts, eqs, count+1, n0)
transformSat (Ineq (t2, Inters t1 t1'):ts, eqs, count, n0)                   = transformSat (Ineq (t2, t1):Ineq (t2, t1'):ts, eqs, count, n0)
transformSat (Ineq (T2_0 (TVar a), T1_0 t0):ts, eqs, count, n0)              = transformSat (Equal (T2_0 (TVar a), T1_0 t0):ts, eqs, count, n0)
transformSat (Equal (T2_0 (TVar a), T1_0 t0):ts, eqs, count, n0)             = transformSat (substSat (a,t0) ts, (TVar a, t0):eqs, count, n0)


-------Type-Inference Algorithm-------

-- Given a list of rank 1 intersection types, returns a single type
-- consisting of the intersection of the types in the given list.
listToInters :: [Type1] -> Type1
listToInters [t1]    = t1
listToInters (t1:ts) = Inters (listToInters ts) t1

-- Given a Sub s=(a,t) and a rank 1 intersection type T1, replaces all free
-- occurrences of the type variable a in the type T1 with type t.
subst1 :: Sub -> Type1 -> Type1
subst1 s (T1_0 t0)       = T1_0 (subst s t0)
subst1 s (Inters t1 t1') = Inters (subst1 s t1) (subst1 s t1')

-- Given a Sub s=(a,t) and a rank 2 intersection type T2, replaces all free
-- occurrences of the type variable a in the type T2 with type t.
subst2 :: Sub -> Type2 -> Type2
subst2 s (T2_0 t0)    = T2_0 (subst s t0)
subst2 s (T2Ap t1 t2) = T2Ap (subst1 s t1) (subst2 s t2)

-- Applies a substitution to a rank 2 intersection type.
substty2 :: Subst -> Type2 -> Type2
substty2 [] t2     = t2
substty2 (s:ts) t2 = substty2 ts (subst2 s t2)

-- Given a Sub s=(a,t) and an environment env, replaces all free
-- occurrences of the type variable a in the types in env with type t.
substEn :: Sub -> Env -> Env
substEn _ []         = []
substEn s ((x,t):es) = (x, subst1 s t):substEn s es

-- Applies a substitution to an environment.
substEnv :: Subst -> Env -> Env
substEnv [] e     = e
substEnv (s:ts) e = substEnv ts (substEn s e)

-- Checks whether or not a term variable is in an environment.
isInEnv :: TeVar -> Env -> Bool
isInEnv _ []            = False
isInEnv x1 ((x2, _):es) = x1 == x2 || isInEnv x1 es

-- Given a term variable x and an environment env,
-- returns a list with all types of x in env.
findAllInEnv :: TeVar -> Env -> [Type1]
findAllInEnv _ []                        = []
findAllInEnv x1 ((x2, t):es) | x1 == x2  = t:findAllInEnv x1 es
                             | otherwise = findAllInEnv x1 es

-- Given a term variable x and an environment env,
-- returns the type of x in env.
-- (It is guaranteed that the function will only be called when
-- there is one and only one occurrence of x in env.)
findInEnv :: TeVar -> Env -> Type1
findInEnv x1 ((x2, t):es) | x1 == x2  = t
                          | otherwise = findInEnv x1 es

-- Removes all occurrences of a term variable from an environment.
rmFromEnv :: TeVar -> Env -> Env
rmFromEnv _ []                        = []
rmFromEnv x1 ((x2, t):es) | x1 == x2  = rmFromEnv x1 es
                          | otherwise = (x2, t):rmFromEnv x1 es

-- Given an environment, replaces all pairs (x,t1), (x,t2)... with a same
-- term variable x with a single pair (x,t) where t=(t1/\t2/\...), ie,
-- the intersection type of t1, t2, ... .
mergeEnv :: Env -> Env
mergeEnv []           = []
mergeEnv ((x, t1):es) = (x, listToInters (findAllInEnv x ((x, t1):es))):mergeEnv (rmFromEnv x es)

-- Auxiliar of the type inference algorithm, performs as many type inferences for the given term
-- as the number of simple types of the given intersection type, and returns the environment
-- and the generated satisfaction problem described in the algorithm.
-- (The third element of the returning tuple is the counter of the quantitative information.)
genPPSat :: Type1 -> Term -> Int -> (Env, SatProblem, Int, Int)
genPPSat (T1_0 t0) m n0       = (env, [Ineq (t, T1_0 t0)], count, n1)
                             where (env, t, count, n1) = quantR2typeInf m n0
genPPSat (Inters t1 t1') m n0 = (mergeEnv (envm1++envm2), sat1++sat2, count1+count2, n2)
                             where (envm1, sat1, count1, n1) = genPPSat t1 m n0
                                   (envm2, sat2, count2, n2) = genPPSat t1' m n1

-- Type inference algorithm for rank 2 intersection types with counting of quantitative information.
-- (The third element of the returning tuple is the counter of the quantitative information.)
quantR2typeInf :: Term -> Int -> (Env, Type2, Int, Int)
quantR2typeInf (Var x) n0     = let t0 = TVar (TyVar ('a':(show n0))) in ([(x, T1_0 t0)], T2_0 t0, 0, n0+1)
quantR2typeInf (App m1 m2) n0 = let (env1, t, count1, n1) = quantR2typeInf m1 n0 in
                                    case t of
                                        T2_0 (TVar t2_0)   -> (substEnv s env, substty2 s (T2_0 t0'), count1+count2, n3)
                                                          where (env2, t2, count2, n2) = quantR2typeInf m2 n1
                                                                env                    = mergeEnv (env1++env2)
                                                                t0                     = TVar (TyVar ('a':(show n2)))
                                                                t0'                    = TVar (TyVar ('a':(show (n2+1))))
                                                                ([], eqs, _, n3)       = transformSat ([Ineq (t2, T1_0 t0)], [((TVar t2_0), TAp t0 t0')], 0, n2+2)
                                                                ([], Uni s)            = unify (eqs, Uni [])
                                        T2Ap t_1 t_2       -> (substEnv s (mergeEnv (env1++envs)), substty2 s t_2, count1+count2+count3+1, n3)
                                                          where (envs, sat, count2, n2) = genPPSat t_1 m2 n1
                                                                ([], eqs, count3, n3)   = transformSat (sat, [], 0, n2)
                                                                ([], Uni s)             = unify (eqs, Uni [])
                                        T2_0 (TAp t_1 t_2) -> (substEnv s (mergeEnv (env1++envs)), substty2 s (T2_0 t_2), count1+count2+count3+1, n3)
                                                          where (envs, sat, count2, n2) = genPPSat (T1_0 t_1) m2 n1
                                                                ([], eqs, count3, n3)   = transformSat (sat, [], 0, n2)
                                                                ([], Uni s)             = unify (eqs, Uni [])
quantR2typeInf (Abs x m) n0
              | isInEnv x env = (rmFromEnv x env, T2Ap (findInEnv x env) t2, count, n1)
              | otherwise     = (env, T2Ap (T1_0 (TVar (TyVar ('a':(show n1))))) t2, count, n1+1)
             where (env, t2, count, n1) = quantR2typeInf m n0