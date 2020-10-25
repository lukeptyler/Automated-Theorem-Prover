module Main where

import FOL.Base
import Generator
import Unification
import Tableau

import Data.List (groupBy, sortBy, mapAccumL)

main :: IO ()
main = putStrLn "FOLParser"

extractExceed (Just (ExceedSteps ls)) = ls


