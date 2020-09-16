module FOL.Rewrite where

import FOL.Types
import FOL.Substitution

import Data.List (mapAccumL)

-- Precond:  Any FOL formula
-- Postcond: The formula with free variables as constants and skolemized
normalize :: Formula -> Formula
normalize = (snd . skolemize [] True 1) . (snd . nameApart []) . splitBiconds . freeVarToConst

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
nameApart :: [VarId] -> Formula -> ([VarId], Formula)
nameApart bound (Atomic pred ts) = (bound, Atomic pred ts)
nameApart bound (Neg         f) = Neg <$> nameApart bound f
nameApart bound (Binary op l r) = uncurry (Binary op) <$> (bound'', (l', r'))
    where
        (bound',  l') = nameApart bound  l
        (bound'', r') = nameApart bound' r
nameApart bound qu@(Quant  q id f)
    | id `elem` bound = nameApart bound $ renameQuant (nextId id) qu
    | otherwise = Quant q id <$> nameApart (id:bound) f

-- Precond:  A list of FOL Formulas with no free variable
-- PostCond: The formulas with all bound variables unique (named apart)
nameApartList :: [Formula] -> [Formula]
nameApartList = snd . mapAccumL nameApart []

-- Precond:  An FOL formula that is named apart with biconditionals split if containing quantifiers
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

-- Precond:  An FOL formula that is named apart with biconditionals split if containing quantifiers
-- Postcond: The formula that has been skolemized
skolemize :: [VarId] -> Bool -> Int -> Formula -> (Int, Formula)
skolemize _ _ n f@(Atomic _ _) = (n,f)
skolemize bound pos n (Neg f) = Neg <$> skolemize bound (not pos) n f
skolemize bound pos n f@(Binary Bicond _ _) = (n,f)
skolemize bound pos n (Binary Imp l r) = uncurry (Binary Imp) <$> (n'', (l', r'))
    where
        (n', l') = skolemize bound (not pos) n  l
        (n'',r') = skolemize bound pos       n' r
skolemize bound pos n (Binary op  l r) = uncurry (Binary op) <$> (n'', (l', r'))
    where
        (n', l') = skolemize bound pos n  l
        (n'',r') = skolemize bound pos n' r
skolemize bound True  n (Quant All  id f) = Quant All  id <$> skolemize (bound ++ [id]) True  n f
skolemize bound False n (Quant Some id f) = Quant Some id <$> skolemize (bound ++ [id]) False n f
skolemize bound pos   n (Quant q    id f) = skolemize bound pos (n+1) $ substF (singleton id $ Function ("sko"++show n) $ map Var bound) f

-- Precond:  A list of FOL formulas that are named apart with biconditionals split if containing quantifiers
-- Postcond: The formulas that have been skolemized
skolemizeList :: [Formula] -> [Formula]
skolemizeList = snd . mapAccumL (skolemize [] True) 1