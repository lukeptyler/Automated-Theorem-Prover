module Main where

import FOL
import Generator
import Parser

import Data.List (isInfixOf, intercalate)

main :: IO ()
main = putStrLn "test"

randFormula :: Integer -> Formula
randFormula = fst . runGen (genFormula maxFormDepth) . mkSeed

test x = either (\_ -> False) (\form -> form == randFormula x) $ parseFormula $ show $ randFormula x

testRange xs = all (== True) $ map test xs



showNoParen (Atomic p []) = p
showNoParen (Atomic p ts) = p ++ "(" ++ (intercalate "," $ map show $ ts) ++ ")"
showNoParen (Neg f)       = "-" ++ showNoParen f ++ ""
showNoParen (And l r)     = showNoParen l ++ " & "   ++ showNoParen r
showNoParen (Or l r)      = showNoParen l ++ " | "   ++ showNoParen r
showNoParen (Imp l r)     = showNoParen l ++ " -> "  ++ showNoParen r
showNoParen (Bicond l r)  = showNoParen l ++ " <-> " ++ showNoParen r
showNoParen (All v f)     = "All "  ++ v ++ "." ++ showNoParen f
showNoParen (Some v f)    = "Some " ++ v ++ "." ++ showNoParen f
























