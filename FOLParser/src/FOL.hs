module FOL
    ( VarId, PredId, Term(..), BinaryOp(..), Quantifier(..), Formula(..),
      (.&), (.|), (.->), (.<->), neg, univ, exist,
      constant, proposition, freeVarToConst
    ) where

import Data.List (intercalate)

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
    show (Neg f)         = "-" ++ show' f ++ ""
    show (Binary op l r) = show' l ++ show op ++ show' r
    show (Quant  q id f) = show q ++ id ++ ".(" ++ show f ++ ")"

show' :: Formula -> String
show' f@(Atomic _ _) = show f
show' f = "(" ++ show f ++ ")"

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