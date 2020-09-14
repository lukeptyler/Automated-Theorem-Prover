module FOL where

import qualified Data.Map.Strict as M
import Data.List (nub, delete, intercalate, intersect)

type VarId  = String
type PredId = String

data Term = Var VarId 
          | Function VarId [Term]
    deriving (Eq)
instance Show Term where
    show (Var v) = v
    show (Function f []) = f
    show (Function f ts) = f ++ "(" ++ intercalate "," (map show ts) ++ ")"

data BinaryOp = And | Or | Imp | Bicond
    deriving (Eq)
instance Show BinaryOp where
    show And    = " & "
    show Or     = " | "
    show Imp    = " -> "
    show Bicond = " <-> "

data Quantifier = All | Some
    deriving (Eq)
instance Show Quantifier where
    show All  = "all "
    show Some = "some "

data Formula = Atomic PredId [Term]
             | Neg    Formula
             | Binary BinaryOp Formula Formula
             | Quant  Quantifier VarId Formula
    deriving (Eq)
instance Show Formula where
    show (Atomic p [])   = p
    show (Atomic p ts)   = p ++ "(" ++ intercalate "," (map show ts) ++ ")"
    show (Neg f)         = "-" ++ show_ f ++ ""
    show (Binary op l r) = show_ l ++ show op ++ show_ r
    show (Quant  q id f) = show q ++ id ++ ".(" ++ show f ++ ")"

show_ :: Formula -> String
show_ f@(Atomic _ _) = show f
show_ f = "(" ++ show f ++ ")"

-- Formula Constructors --

constant :: VarId -> Term
constant id = Function id []

proposition :: PredId -> Formula
proposition id = Atomic id []

infixl 4 .&
(.&) :: Formula -> Formula -> Formula
l .& r = Binary And l r

infixl 3 .|
(.|) :: Formula -> Formula -> Formula
l .| r = Binary Or l r

infixl 2 .->
(.->) :: Formula -> Formula -> Formula
l .-> r = Binary Imp l r

infixl 1 .<->
(.<->) :: Formula -> Formula -> Formula
l .<-> r = Binary Bicond l r

neg :: Formula -> Formula
neg f = Neg f

univ :: VarId -> Formula -> Formula
univ id f = Quant All id f

exist :: VarId -> Formula -> Formula
exist id f = Quant Some id f

-- Substitutions --

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

-- Rewrite Utilities --

nextId :: VarId -> VarId
nextId (l:n)
    | null n = l : "1"
    | otherwise = l : (show $ succ $ (read n :: Int))

-- Precond:  Any FOL formula
-- Postcond: The formula written in prenex form and skolemized
normalize :: Formula -> Formula
normalize = skolemize . prenex . nameApart . freeVarToConst

-- Precond:  Any FOL formula
-- Postcond: The formula with all free variables to constants
freeVarToConst :: Formula -> Formula
freeVarToConst = freeVarToConstF []
    where
        freeVarToConstF :: [String] -> Formula -> Formula
        freeVarToConstF bound (Atomic pred ts) = Atomic pred $ map (freeVarToConstT bound) ts
        freeVarToConstF bound (Neg    f)       = Neg       (freeVarToConstF bound f)
        freeVarToConstF bound (Binary op l r)  = Binary op (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (Quant  q id f)  = Quant q id (freeVarToConstF (id:bound) f)

        freeVarToConstT :: [String] -> Term -> Term
        freeVarToConstT bound v@(Var id)
            | id `notElem` bound = Function id []
            | otherwise          = v
        freeVarToConstT bound (Function f ts) = Function f $ map (freeVarToConstT bound) ts

-- Precond:  Any FOL formula
-- Postcond: The formula with all free and bound variables unique (named apart)
nameApart :: Formula -> Formula
nameApart = undefined

-- Precond:  An FOL formula that is named apart
-- Postcond: The formula written in prenex form
prenex :: Formula -> Formula
prenex = undefined

-- Precond:  An FOL formula that is in prenex form
-- Postcond: The formula that has been skolemized
skolemize :: Formula -> Formula
skolemize = undefined