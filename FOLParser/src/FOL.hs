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
             | Quant  {quan::Quantifier, iden::VarId, form::Formula}
    deriving (Eq)
instance Show Formula where
    show (Atomic p [])   = p
    show (Atomic p ts)   = p ++ "(" ++ intercalate "," (map show ts) ++ ")"
    show (Neg f)         = "-" ++ show_ f ++ ""
    show (Binary op l r) = show_ l ++ show op ++ show_ r
    show (Quant  q id f) = show q ++ id ++ "." ++ show__ f

show_ :: Formula -> String
show_ f@(Atomic _ _) = show f
show_ f = "(" ++ show f ++ ")"

show__ qu@(Quant _ _ _) = show qu
show__ f = "(" ++ show f ++ ")"

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

renameQuant :: VarId -> Formula -> Formula
renameQuant rename (Quant op id f) = Quant op rename $ substF (singleton id (Var rename)) f

-- Precond:  Any FOL formula
-- Postcond: The formula written in prenex form and skolemized
normalize :: Formula -> Formula
normalize = skolemize . prenex . nameApart . splitBiconds . freeVarToConst

-- Precond:  Any FOL formula
-- Postcond: The formula with all free variables to constants
freeVarToConst :: Formula -> Formula
freeVarToConst = freeVarToConstF []
    where
        freeVarToConstF :: [VarId] -> Formula -> Formula
        freeVarToConstF bound (Atomic pred ts) = Atomic pred $ map (freeVarToConstT bound) ts
        freeVarToConstF bound (Neg         f)  = Neg       (freeVarToConstF bound f)
        freeVarToConstF bound (Binary op l r)  = Binary op (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (Quant  q id f)  = Quant q id (freeVarToConstF (id:bound) f)

        freeVarToConstT :: [VarId] -> Term -> Term
        freeVarToConstT bound v@(Var id)
            | id `notElem` bound = Function id []
            | otherwise          = v
        freeVarToConstT bound (Function f ts) = Function f $ map (freeVarToConstT bound) ts

-- Precond:  Any FOL formula
-- Postcond: The formula with every biconditional containing a quantifier split into two implications
-- Needed for conversion to prenex form
splitBiconds :: Formula -> Formula
splitBiconds f@(Atomic _ _) = f
splitBiconds (Neg f) = Neg $ splitBiconds f
splitBiconds f@(Binary Bicond l r)
    | hasQuant f = splitBiconds $ (l .-> r) .& (r .-> l)
    | otherwise = f
    where
        hasQuant :: Formula -> Bool
        hasQuant (Atomic _ _) = False
        hasQuant (Neg f) = hasQuant f
        hasQuant (Binary _ l r) = hasQuant l || hasQuant r
        hasQuant (Quant _ _ _) = True
splitBiconds (Binary op l r) = Binary op (splitBiconds l) (splitBiconds r)
splitBiconds (Quant  q id f) = Quant q id $ splitBiconds f

-- Precond:  An FOL formula with no free variables
-- Postcond: The formula with all bound variables unique (named apart)
nameApart :: Formula -> Formula
nameApart = snd . nameApart' []
    where
        nameApart' :: [VarId] -> Formula -> ([VarId], Formula)
        nameApart' bound (Atomic pred ts) = (bound, Atomic pred ts)
        nameApart' bound (Neg         f) = do f' <- nameApart' bound f
                                              return $ Neg f'
        nameApart' bound (Binary op l r) = let (bound', l') = nameApart' bound l 
                                           in (do r' <- nameApart' bound' r
                                                  return $ Binary op l' r'
                                              )
        nameApart' bound qu@(Quant  q id f)
            | id `elem` bound = nameApart' bound $ renameQuant (nextId id) qu
            | otherwise = do f' <- nameApart' (id:bound) f
                             return $ Quant q id f'

-- Precond:  An FOL formula that is named apart with biconditional split if containing quantifiers
-- Postcond: The formula written in prenex form
prenex :: Formula -> Formula
prenex f@(Atomic _ _) = f
prenex (Neg         f) = moveQuantsToFront $ Neg $ prenex f
prenex f@(Binary Bicond _ _) = f
prenex (Binary op l r) = moveQuantsToFront $ Binary op (prenex l) (prenex r)
prenex (Quant  q id f) = Quant q id $ moveQuantsToFront $ prenex f

moveQuantsToFront :: Formula -> Formula
moveQuantsToFront (Neg f)
    | isQuant f = Quant (switchQuantifier $ quan f) (iden f) $ moveQuantsToFront $ Neg $ form f
    | otherwise = Neg f
moveQuantsToFront (Binary op l r)
    | isQuant l = if positiveLeft op
                  then Quant (quan l) (iden l) $ moveQuantsToFront $ Binary op (form l) r
                  else Quant (switchQuantifier $ quan l) (iden l) $ moveQuantsToFront $ Binary op (form l) r
    | isQuant r = Quant (quan r) (iden r) $ moveQuantsToFront $ Binary op l $ form r
    | otherwise = Binary op l r
    where
        positiveLeft :: BinaryOp -> Bool
        positiveLeft And = True
        positiveLeft Or  = True
        positiveLeft Imp = False
moveQuantsToFront f = f

isQuant :: Formula -> Bool
isQuant (Quant _ _ _) = True
isQuant _ = False

switchQuantifier :: Quantifier -> Quantifier
switchQuantifier All  = Some
switchQuantifier Some = All

-- Precond:  An FOL formula that is in prenex form
-- Postcond: The formula that has been skolemized
skolemize :: Formula -> Formula
skolemize = skolemize' 1 []
    where
        skolemize' :: Int -> [VarId] -> Formula -> Formula
        skolemize' nextId boundVars (Quant All  id f) = Quant All id $ skolemize' nextId (boundVars ++ [id]) f
        skolemize' nextId boundVars (Quant Some id f) = skolemize' (nextId+1) boundVars $ substF (singleton id $ Function ("sko"++show nextId) $ map Var boundVars) f
        skolemize' _ _ f = f




