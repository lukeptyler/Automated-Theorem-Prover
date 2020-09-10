module Substitution where

import FOL
import qualified Data.Map.Strict as M
import Data.List (nub, delete, intercalate, intersect)

newtype Subst = Subst (M.Map String Term)
    deriving (Eq)

instance Show Subst where
    show (Subst m) = '{' : intercalate ", " (map (\(v,t) -> v ++ "/" ++ show t) $ M.assocs m) ++ "}"

instance Semigroup Subst where
    (Subst m1) <> s2@(Subst m2) = Subst $ ((substT s2) <$> m1) `M.union` (m2 M.\\ m1) 

instance Monoid Subst where
    mempty = Subst $ M.empty

singleton :: VarId -> Term -> Subst
singleton id t = Subst $ M.singleton id t

fromList :: [(VarId,Term)] -> Subst
fromList ls = Subst $ M.fromList ls

restrict :: String -> Subst -> Subst
restrict id (Subst map) = Subst $ M.delete id map

support :: Subst -> [VarId]
support (Subst map) = M.keys map

varRange :: Subst -> [VarId]
varRange (Subst map) = concatMap varsInTerm $ M.elems map

varsInTerm :: Term -> [VarId]
varsInTerm (Var id) = [id]
varsInTerm (Function _ ts) = nub $ concatMap varsInTerm ts

varsInForm :: Formula -> [VarId]
varsInForm (Atomic pred ts) = nub $ concatMap varsInTerm ts
varsInForm (Neg        f) = varsInForm f
varsInForm (Binary _ l r) = nub $ varsInForm l ++ varsInForm r
varsInForm (Quant _ id f) = delete id $ varsInForm f

nextId :: VarId -> VarId
nextId (l:n)
    | null n = l : "1"
    | otherwise = l : (show $ succ $ (read n :: Int))

renameQuant :: VarId -> Formula -> Formula
renameQuant rename (Quant op id f) = Quant op rename $ substF (singleton id (Var rename)) f

substF :: Subst -> Formula -> Formula
substF sub (Atomic pred ts) = Atomic pred $ map (substT sub) ts
substF sub (Neg         f)  = Neg $ (substF sub) f
substF sub (Binary op l r)  = Binary op (substF sub l) (substF sub r)
substF sub qu@(Quant q id f)
    | id `elem` varRange sub && not (null $ intersect (varsInForm f) (support sub)) = substF sub $ renameQuant (nextId id) qu
    | otherwise = Quant q id $ substF (restrict id sub) f

substT :: Subst -> Term -> Term
substT sub (Function id ts) = Function id $ map (substT sub) ts
substT (Subst map) (Var id)
    | id `M.member` map = map M.! id
    | otherwise = Var id 

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

