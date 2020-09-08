import FOL
import Generator
import Parser

import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)

main :: IO ()
main = hspec $ do
        describe "Parser Tests" $ do
            it "Fails on empty string" $ parseFormula "" `shouldSatisfy` parseError

            it "Parses atomic formula: P(f(x,y),z)" $ 
                parseFormula "P(f(x,y),z)" `shouldBe` Right (Atomic "P" [Function "f" [Var "x", Var "y"], Var "z"])

            it "Fails on invalid atomic formula: x" $
                parseFormula "x" `shouldSatisfy` parseError

            it "Fails on invalid atomic formula: P(x, (Q & R))" $
                parseFormula "P(x, (Q & R))" `shouldSatisfy` parseError

            it "Parses formula: P(x) -> (Q & all y.R(y))" $
                parseFormula "P(x) -> (Q & all y.R(y))" `shouldBe` Right (Imp (Atomic "P" [Var "x"]) (And (Atomic "Q" []) (All "y" (Atomic "R" [Var "y"]))))

            it "Ignores whitespace separating tokens: P  (  x)  \\n   -> (   Q &    all y  \\t  .  R (   y))" $
                parseFormula "P  (  x)     -> (   Q &    all y    .  R (   y))" `shouldBe` Right (Imp (Atomic "P" [Var "x"]) (And (Atomic "Q" []) (All "y" (Atomic "R" [Var "y"]))))

            it "Fails on whitespace inside tokens: P - > Q" $
                parseFormula "P - > Q" `shouldSatisfy` parseError

            it "Fails on whitespace inside tokens: P1 2 & Q" $
                parseFormula "P1 2 & Q" `shouldSatisfy` parseError

            it "Fails with unbalanced parentheses: P -> (Q & R" $
                parseFormula "P -> (Q & R" `shouldSatisfy` parseError

            it "Fails with unbalanced parentheses: P -> Q & R)" $
                parseFormula "P -> Q & R)" `shouldSatisfy` parseError

            it "Fails on invalid formula: P (& Q)" $
                parseFormula "P (& Q)" `shouldSatisfy` parseError

            it "Fails on invalid formula: (P & Q" $
                parseFormula "(P & Q" `shouldSatisfy` parseError

            it "Fails on invalid formula: P (&) Q" $
                parseFormula "P (&) Q" `shouldSatisfy` parseError

            it "Fails on invalid formula: P &| Q" $
                parseFormula "P (&) Q" `shouldSatisfy` parseError

            it "Fails on invalid formula: (P & Q)R" $
                parseFormula "(P & Q)R" `shouldSatisfy` parseError

            it "Fails on invalid formula: (P & Q)-R" $
                parseFormula "(P & Q)-R" `shouldSatisfy` parseError

            it "Fails on invalid formula: (P & Q)(R -> S)" $
                parseFormula "(P & Q)(R -> S)" `shouldSatisfy` parseError

            it "Correctly infers operator precedence: -P & Q -> R(x) | S <-> all x.some y. T" $
                parseFormula "-P & Q -> R(x) | S <-> all x.some y. T" `shouldBe` Right (
                    Bicond (Imp (And (Neg (Atomic "P" [])) (Atomic "Q" [])) (Or (Atomic "R" [Var "x"]) (Atomic "S" []))) (All "x" (Some "y" (Atomic "T" [])))
                )

            modifyMaxSuccess (const 100000) $
                it "Parsing a random formula should give the same formula" $ 
                property testParse

randFormula :: Integer -> Formula
randFormula = fst . runGen (genFormula maxFormDepth) . mkSeed

testParse :: Integer -> Bool
testParse s = either (const False) (== randForm) $ parseFormula $ show randForm
    where
        randForm = fst $ runGen (genFormula maxFormDepth) $ mkSeed s