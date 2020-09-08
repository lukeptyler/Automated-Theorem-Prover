module FOL
    ( VarId, PredId, Term(..), Formula(..), freeVarToConst
    ) where

import Data.List (intercalate)

type VarId  = String
type PredId = String

data Term = Var VarId | Function VarId [Term]
    deriving (Eq)

instance Show Term where
    show (Var v) = v
    show (Function f []) = f
    show (Function f ts) = f ++ "(" ++ intercalate "," (map show ts) ++ ")"

data Formula = Atomic PredId [Term]
             | Neg    Formula
             | And    Formula Formula
             | Or     Formula Formula
             | Imp    Formula Formula
             | Bicond Formula Formula
             | All    VarId   Formula
             | Some   VarId   Formula
    deriving (Eq)

instance Show Formula where
    show (Atomic p []) = p
    show (Atomic p ts) = p ++ "(" ++ intercalate "," (map show ts) ++ ")"
    show (Neg f)       = "-" ++ show' f ++ ""
    show (And l r)     = show' l ++ " & "   ++ show' r
    show (Or l r)      = show' l ++ " | "   ++ show' r
    show (Imp l r)     = show' l ++ " -> "  ++ show' r
    show (Bicond l r)  = show' l ++ " <-> " ++ show' r
    show (All v f)     = "All "  ++ v ++ ".(" ++ show f ++ ")"
    show (Some v f)    = "Some " ++ v ++ ".(" ++ show f ++ ")"

show' :: Formula -> String
show' f@(Atomic _ _) = show f
show' f = "(" ++ show f ++ ")"

freeVarToConst :: Formula -> Formula
freeVarToConst = freeVarToConstF []
    where
        freeVarToConstF :: [String] -> Formula -> Formula
        freeVarToConstF bound (Atomic pred ts) = Atomic pred $ map (freeVarToConstT bound) ts
        freeVarToConstF bound (Neg    f)   = Neg    (freeVarToConstF bound f)
        freeVarToConstF bound (And    l r) = And    (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (Or     l r) = Or     (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (Imp    l r) = Imp    (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (Bicond l r) = Bicond (freeVarToConstF bound l) (freeVarToConstF bound r)
        freeVarToConstF bound (All   id f) = All  id (freeVarToConstF (id:bound) f)
        freeVarToConstF bound (Some  id f) = Some id (freeVarToConstF (id:bound) f)

        freeVarToConstT :: [String] -> Term -> Term
        freeVarToConstT bound v@(Var id)
            | id `notElem` bound = Function id []
            | otherwise          = v
        freeVarToConstT bound (Function f ts) = Function f $ map (freeVarToConstT bound) ts