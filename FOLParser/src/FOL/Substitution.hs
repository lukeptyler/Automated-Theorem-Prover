module FOL.Substitution where

import FOL.Types

import qualified Data.Map.Strict as M
import Data.List (intercalate, nub, delete, intersect)

nextId :: VarId -> VarId
nextId (l:n)
    | null n = l : "1"
    | otherwise = l : (show $ succ $ (read n :: Int))

renameQuant :: VarId -> Formula -> Formula
renameQuant rename (Quant op id f) = Quant op rename $ substF (singleton id (Var rename)) f

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

restrictRange :: String -> Subst -> Subst
restrictRange id (Subst map) = Subst $ M.filter (\f -> id `elem` varsInTerm f) map

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

substF :: Subst -> Formula -> Formula
substF sub (Atomic pred ts) = Atomic pred $ map (substT sub) ts
substF sub (Neg         f)  = Neg $ (substF sub) f
substF sub (Binary op l r)  = Binary op (substF sub l) (substF sub r)
substF sub qu@(Quant q id f)
    | id `elem` varRange sub && not (null $ intersect (varsInForm f) (support $ restrictRange id sub)) = substF sub $ renameQuant (nextId id) qu
    | otherwise = Quant q id $ substF (restrict id sub) f

substT :: Subst -> Term -> Term
substT sub (Function id ts) = Function id $ map (substT sub) ts
substT (Subst map) (Var id)
    | id `M.member` map = map M.! id
    | otherwise = Var id 