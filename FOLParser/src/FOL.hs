module FOL
    ( VarId, PredId, Term(..), Formula(..)
    ) where

import Data.List (intercalate)

type VarId  = String
type PredId = String

data Term = Var VarId | Function VarId [Term]
    deriving (Eq)

instance Show Term where
    show (Var v) = v
    show (Function f ts) = f ++ "(" ++ (intercalate "," $ map show $ ts) ++ ")"

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
    show (Atomic p ts) = p ++ "(" ++ (intercalate "," $ map show $ ts) ++ ")"
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