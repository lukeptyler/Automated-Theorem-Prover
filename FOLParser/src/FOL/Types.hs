module FOL.Types where

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

infixl 5 .&
(.&) :: Formula -> Formula -> Formula
l .& r = Binary And l r

infixl 4 .|
(.|) :: Formula -> Formula -> Formula
l .| r = Binary Or l r

infixl 3 .->
(.->) :: Formula -> Formula -> Formula
l .-> r = Binary Imp l r

infixl 2 .<->
(.<->) :: Formula -> Formula -> Formula
l .<-> r = Binary Bicond l r

neg :: Formula -> Formula
neg f = Neg f

univ :: VarId -> Formula -> Formula
univ id f = Quant All id f

exist :: VarId -> Formula -> Formula
exist id f = Quant Some id f

-- Formula Classifications --

isAtomic :: Formula -> Bool
isAtomic (Atomic _ _)       = True
isAtomic (Neg (Atomic _ _)) = True
isAtomic _                  = False

isDoubleNeg :: Formula -> Bool
isDoubleNeg (Neg (Neg _)) = True
isDoubleNeg _             = False

isAlpha :: Formula -> Bool
isAlpha (Binary And _ _)       = True
isAlpha (Neg (Binary Or  _ _)) = True
isAlpha (Neg (Binary Imp _ _)) = True
isAlpha _                      = False

isBeta :: Formula -> Bool
isBeta (Neg (Binary And _ _))    = True
isBeta (Binary Or  _ _)          = True
isBeta (Binary Imp _ _)          = True
isBeta (Binary Bicond _ _)       = True
isBeta (Neg (Binary Bicond _ _)) = True
isBeta _                         = False

isDelta :: Formula -> Bool
isDelta (Quant Some _ _)      = True
isDelta (Neg (Quant All _ _)) = True
isDelta _                     = False

isGamma :: Formula -> Bool
isGamma (Quant All _ _)        = True
isGamma (Neg (Quant Some _ _)) = True
isGamma _                      = False

extractAtomic :: Formula -> Formula
extractAtomic f@(Atomic _ _)       = f
extractAtomic (Neg f@(Atomic _ _)) = f

extractBinary :: Formula -> (Formula, Formula)
extractBinary (Binary      _ l r)  = (l, r)
extractBinary (Neg (Binary _ l r)) = (l, r)

extractQuant :: Formula -> (VarId, Formula)
extractQuant (Quant      _ id f)  = (id, f)
extractQuant (Neg (Quant _ id f)) = (id, f)