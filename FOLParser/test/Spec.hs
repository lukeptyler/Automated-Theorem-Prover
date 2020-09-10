import FOL
import Generator
import Parser
import Substitution

import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)

import qualified Data.Map.Strict as M

main :: IO ()
main = hspec $ do
        describe "Parser Tests" $ do
            it "Fails on empty string" $ parseFormula "" `shouldSatisfy` parseError

            it "Parses atomic formula: P(f(x,y),z)" $ 
                parseFormula "P(f(x,y),z)" `shouldBe` Right (Atomic "P" [Function "f" [Function "x" [], Function "y" []], Function "z" []])

            it "Fails on invalid atomic formula: P(x,y" $
                parseFormula "P(x,y" `shouldSatisfy` parseError

            it "Fails on invalid atomic formula: x" $
                parseFormula "x" `shouldSatisfy` parseError

            it "Fails on invalid atomic formula: P(x, (Q & R))" $
                parseFormula "P(x, (Q & R))" `shouldSatisfy` parseError

            it "Parses formula: P(x) -> (Q & all y.R(y))" $
                parseFormula "P(x) -> (Q & all y.R(y))" `shouldBe` Right (Imp (Atomic "P" [Function "x" []]) (And (Atomic "Q" []) (All "y" (Atomic "R" [Var "y"]))))

            it "Ignores whitespace separating tokens: P  (  x)  \\n   -> (   Q &    all y  \\t  .  R (   y))" $
                parseFormula "P  (  x)     -> (   Q &    all y    .  R (   y))" `shouldBe` Right (Imp (Atomic "P" [Function "x" []]) (And (Atomic "Q" []) (All "y" (Atomic "R" [Var "y"]))))

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

            it "Correctly infers operator precedence: -P & Q -> R(w) | S <-> all x.some y. T(x,z)" $
                parseFormula "-P & Q -> R(w) | S <-> all x.some y. T(x,z)" `shouldBe` Right (
                    Bicond (Imp (And (Neg (Atomic "P" [])) (Atomic "Q" [])) (Or (Atomic "R" [Function "w" []]) (Atomic "S" []))) (All "x" (Some "y" (Atomic "T" [Var "x",Function "z" []])))
                )

            modifyMaxSuccess (const 100000) $
                it "Parsing a random formula should give the same formula" $ 
                property testParse

        describe "Substitution Tests" $ do
            it "Passes with: x, y => {x/y}" $
                unifyT (Var "x") 
                       (Var "y") 
                       `shouldBe` Just (Subst $ M.singleton "x" (Var "y"))

            it "Passes: f(x,c), y => {y/f(x,c)}" $
                unifyT (Function "f" [Var "x", Function "c" []]) 
                       (Var "y") 
                       `shouldBe` Just (Subst $ M.singleton "y" $ Function "f" [Var "x", Function "c" []])

            it "Fails:  f(x,c), x" $
                unifyT (Function "f" [Var "x", Function "c" []]) 
                       (Var "x") 
                       `shouldBe` Nothing

            it "Passes: f(c), f(x) => {x/c}" $
                unifyT (Function "f" [Function "c" []]) 
                       (Function "f" [Var "x"]) 
                       `shouldBe` Just (Subst $ M.singleton "x" $ Function "c" [])

            it "Passes: f(a,b), f(a,b) => {}" $
                unifyT (Function "f" [Function "a" [], Function "b" []]) 
                       (Function "f" [Function "a" [], Function "b" []]) 
                       `shouldBe` Just mempty

            it "Fails:  f(a,b), g(x,y)" $
                unifyT (Function "f" [Function "a" [], Function "b" []])
                       (Function "g" [Var "x", Var "y"])
                       `shouldBe` Nothing

            it "Fails:  f(x,a,b), f(a,b)" $
                unifyT (Function "f" [Var "x", Function "a" [], Function "b" []])
                       (Function "f" [Function "a" [], Function "b" []])
                       `shouldBe` Nothing

            it "Passes: P(x), P(f(c)) => {x/f(c)}" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [Function "f" [Function "c" []]])
                       `shouldBe` Just (Subst $ M.singleton "x" $ Function "f" [Function "c" []])

            it "Fails:  P(x), P(f(x))" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [Function "f" [Var "x"]])
                       `shouldBe` Nothing

            it "Fails:  P(x), P(a,b)" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [Function "a" [], Function "b" []])
                       `shouldBe` Nothing

            it "Fails:  P(x), Q(a)" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "Q" [Function "a" []])
                       `shouldBe` Nothing

            it "Fails:  P(x,f(y),g(z,c)), P(h(z),f(x),g(a,x)" $ 
                unifyF (Atomic "P" [Var "x", Function "f" [Var "y"], Function "g" [Var "z", Function "c" []]])
                       (Atomic "P" [Function "h" [Var "z"], Function "f" [Var "x"], Function "g" [Function "a" [], Var "x"]])
                       `shouldBe` Nothing

            it "Passes: P(x,f(y),g(z,c)), P(h(z),f(x),g(a,c) => {x/h(a), y/h(a), z/a}" $
                unifyF (Atomic "P" [Var "x", Function "f" [Var "y"], Function "g" [Var "z", Function "c" []]])
                       (Atomic "P" [Function "h" [Var "z"], Function "f" [Var "x"], Function "g" [Function "a" [], Function "c" []]])
                       `shouldBe` Just (Subst $ M.fromList [("x", Function "h" [Function "a" []]), ("y", Function "h" [Function "a" []]), ("z", Function "a" [])])

randFormula :: Integer -> Formula
randFormula = fst . runGen (genFormula maxFormDepth) . mkSeed

testParse :: Integer -> Bool
testParse s = either (const False) (== freeVarToConst randForm) $ parseFormula $ show randForm
    where
        randForm = fst $ runGen (genFormula maxFormDepth) $ mkSeed s