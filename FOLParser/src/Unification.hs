module Unification where

import FOL

disagreeT :: Term -> Term -> Maybe (String,Term)
disagreeT (Var x) (Var y)
    | x == y = Nothing
    | otherwise = Just (x, Var y)
disagreeT (Var id) t@(Function _ _) = Just (id, t)
disagreeT t@(Function _ _) (Var id) = Just (id, t)
disagreeT (Function f ts1) (Function g ts2)
    | f /= g || length ts1 /= length ts2 = Nothing
    | otherwise = disagreeList ts1 ts2
    where 
        disagreeList :: [Term] -> [Term] -> Maybe (String,Term)
        disagreeList [] [] = Nothing
        disagreeList (t1:ts1) (t2:ts2) = maybe (disagreeList ts1 ts2) Just $ disagreeT t1 t2

inside :: String -> Term -> Bool
inside x (Var id) = x == id
inside x (Function id ts) = any (inside x) ts

unifyT :: Term -> Term -> Maybe Subst
unifyT t1 t2 = unifyT' mempty t1 t2
    where
        unifyT' :: Subst -> Term -> Term -> Maybe Subst
        unifyT' sub t1 t2
            | substT sub t1 == substT sub t2 = Just sub
            | otherwise = do (x,t) <- disagreeT (substT sub t1) (substT sub t2)
                             if x `inside` t
                             then Nothing
                             else unifyT' (sub <> singleton x t) t1 t2

unifyF :: Formula -> Formula -> Maybe Subst
unifyF (Atomic p1 ts1) (Atomic p2 ts2)
    | p1 /= p2 || length ts1 /= length ts2 = Nothing
    | otherwise = unifyF' mempty ts1 ts2
    where
        unifyF' :: Subst -> [Term] -> [Term] -> Maybe Subst
        unifyF' sub [] [] = Just sub
        unifyF' sub (t1:ts1) (t2:ts2) = do sub' <- unifyT (substT sub t1) (substT sub t2)
                                           unifyF' (sub <> sub') ts1 ts2

