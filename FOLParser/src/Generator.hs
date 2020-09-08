module Generator
    ( Gen(..), genFormula, maxFormDepth, mkSeed, genFromList
    ) where

import FOL
import Data.Char (intToDigit, chr, ord)
import Control.Monad (replicateM)

newtype Seed = Seed { unSeed :: Integer }
  deriving (Eq,Show)

mkSeed :: Integer -> Seed
mkSeed = Seed

numToLower :: Integer -> Char
numToLower = chr . (ord 'a' + ) . (`mod` 26) . fromIntegral

numToUpper :: Integer -> Char
numToUpper = chr . (ord 'A' + ) . (`mod` 26) . fromIntegral

numToDigit :: Integer -> Char
numToDigit = intToDigit . (`mod` 10) . fromIntegral

newtype Gen a = Gen { runGen :: Seed -> (a, Seed) }

instance Functor Gen where
    fmap f genA = Gen $ \s -> let (a,s') = runGen genA s in (f a, s')

instance Applicative Gen where
    pure x = Gen ((,) x)
    genF <*> genA = Gen $ \s -> let (f,s') = runGen genF s in runGen (fmap f genA) s'

instance Monad Gen where
    return = pure
    genA >>= f = Gen $ \s -> let (x,s1) = runGen genA s in runGen (f x) s1

genInteger :: Gen Integer
genInteger = Gen $ \(Seed s) -> let s' = (s * 16807) `mod` 0x7FFFFFFF in (s', Seed s')

genLower :: Gen Char
genLower = numToLower <$> genInteger

genUpper :: Gen Char
genUpper = numToUpper <$> genInteger

genDigit :: Gen Char
genDigit = numToDigit <$> genInteger

genRange :: Int -> Gen Int -- 0-n
genRange n = (\x -> fromIntegral x `mod` (n+1)) <$> genInteger

genFromList :: [a] -> Gen a
genFromList [] = undefined
genFromList ls = do r <- genRange $ length ls - 1
                    return $ ls !! r

genBool :: Gen Bool
genBool = (== 1) <$> genRange 1

-------------------------------

maxIndexCount :: Int
maxIndexCount = 1
maxParamCount :: Int
maxParamCount = 2
maxTermDepth :: Int
maxTermDepth  = 1
maxFormDepth :: Int
maxFormDepth  = 5

genId :: Gen Char -> Gen String
genId charGen = do r <- genRange maxIndexCount
                   (:) <$> charGen <*> replicateM r genDigit

genVarId :: Gen VarId
genVarId = genId genLower

genPredId :: Gen PredId
genPredId = genId genUpper

genTerm :: Int -> Gen Term
genTerm 0        = genVar
genTerm maxDepth = do b <- genBool
                      if b then genVar else genFunc $ maxDepth - 1

genVar :: Gen Term
genVar = Var <$> genVarId

genFunc :: Int -> Gen Term
genFunc maxDepth = do r <- genRange (maxParamCount-1)
                      Function <$> genVarId <*> (replicateM (r+1) $ genTerm maxDepth)

genAtomic :: Gen Formula
genAtomic = do r <- genRange maxParamCount
               Atomic <$> genPredId <*> (replicateM r $ genTerm maxTermDepth)

genFormula :: Int -> Gen Formula
genFormula 0        = genAtomic
genFormula maxDepth = genRange 7 >>= \r -> case r of 
    0 -> genAtomic
    1 -> Neg    <$> genFormula (maxDepth - 1)
    2 -> And    <$> genFormula (maxDepth - 1) <*> genFormula (maxDepth - 1)
    3 -> Or     <$> genFormula (maxDepth - 1) <*> genFormula (maxDepth - 1)
    4 -> Imp    <$> genFormula (maxDepth - 1) <*> genFormula (maxDepth - 1)
    5 -> Bicond <$> genFormula (maxDepth - 1) <*> genFormula (maxDepth - 1)
    6 -> All    <$> genVarId <*> genFormula (maxDepth - 1)
    7 -> Some   <$> genVarId <*> genFormula (maxDepth - 1)