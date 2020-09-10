import FOL
import Generator
import Parser
import Substitution

import Test.Hspec
import Test.QuickCheck
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)

--import qualified Data.Map.Strict as M

main :: IO ()
main = hspec $ do
        describe "Parser Tests" $ do
            it "Fails on empty string" $ parseFormula "" `shouldSatisfy` parseError

            it "Parses atomic formula: P(f(x,y),z)" $ 
                parseFormula "P(f(x,y),z)" `shouldBe` Right (Atomic "P" [Function "f" [constant "x", constant "y"], constant "z"])

            it "Fails on invalid atomic formula: P(x,y" $
                parseFormula "P(x,y" `shouldSatisfy` parseError

            it "Fails on invalid atomic formula: x" $
                parseFormula "x" `shouldSatisfy` parseError

            it "Fails on invalid atomic formula: P(x, (Q & R))" $
                parseFormula "P(x, (Q & R))" `shouldSatisfy` parseError

            it "Parses formula: P(x) -> (Q & all y.R(y))" $
                parseFormula "P(x) -> (Q & all y.R(y))" 
                `shouldBe` Right 
                (Atomic "P" [constant "x"] .-> (proposition "Q" .& univ "y" (Atomic "R" [Var "y"])))

            it "Ignores whitespace separating tokens: P  (  x)  \\n   -> (   Q &    all y  \\t  .  R (   y))" $
                parseFormula "P  (  x)     -> (   Q &    all y    .  R (   y))" 
                `shouldBe` Right 
                (Atomic "P" [constant "x"] .-> (proposition "Q" .& univ "y" (Atomic "R" [Var "y"])))

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
                parseFormula "-P & Q -> R(w) | S <-> all x.some y. T(x,z)" 
                `shouldBe` Right 
                ((((neg $ proposition "P") .& proposition "Q") .-> (Atomic "R" [constant "w"] .| proposition "S")) .<-> (univ "x" (exist "y" (Atomic "T" [Var "x", constant "z"]))))

            modifyMaxSuccess (const 10000) $
                it "Parsing a random formula should give the same formula" $ 
                property testParse

        describe "Substitution Tests" $ do
            it "(x){x/c} => c" $
                substT (singleton "x" $ constant "c") 
                       (Var "x") 
                       `shouldBe` constant "c"

            it "(f(x,c)){x/c} => f(c,c)" $
                substT (singleton "x" $ constant "c")
                       (Function "f" [Var "x", constant "c"])
                       `shouldBe` Function "f" [constant "c", constant "c"]

            it "(f(x,c)){y/c} => f(x,c)" $
                substT (singleton "y" $ constant "c")
                       (Function "f" [Var "x", constant "c"])
                       `shouldBe` Function "f" [Var "x", constant "c"]

            it "(f(x)){x/g(y)} => f(g(y))" $
                substT (singleton "x" $ Function "g" [Var "y"])
                       (Function "f" [Var "x"])
                       `shouldBe` Function "f" [Function "g" [Var "y"]]

            it "(f(x)){x/g(y)}{y/c} => f(g(c))" $
                substT (singleton "y" $ constant "c")
                       (substT (singleton "x" $ Function "g" [Var "y"])
                              (Function "f" [Var "x"]))
                       `shouldBe` Function "f" [Function "g" [constant "c"]]

            it "{x/g(y), y/c}{y/a, z/w} => {x/g(a), y/c, z/w}" $
                (fromList [("x", Function "g" [Var "y"]), ("y", constant "c")]) <> 
                (fromList [("y", constant "a"), ("z", Var "w")])
                `shouldBe` fromList [("x", Function "g" [constant "a"]), ("y", constant "c"), ("z", Var "w")]

            it "(P(x,f(x))){x/c} => P(c,f(c))" $
                substF (singleton "x" $ constant "c")
                       (Atomic "P" [Var "x", Function "f" [Var "x"]])
                       `shouldBe` Atomic "P" [constant "c", Function "f" [constant "c"]]

            it "(P(x) & Q(y)){x/c,y/x} => P(c) & Q(x)" $
                substF (fromList [("x", constant "c"), ("y", Var "x")])
                       (Atomic "P" [Var "x"] .& Atomic "Q" [Var "y"])
                       `shouldBe` Atomic "P" [constant "c"] .& Atomic "Q" [Var "x"]

            it "(all x.P(x)){x/c} => all x.P(x)" $
                substF (singleton "x" $ constant "c")
                       (univ "x" $ Atomic "P" [Var "x"])
                       `shouldBe` univ "x" (Atomic "P" [Var "x"])

            it "(some x.(P(x) & Q(y)){x/c, y/a} => some x.(P(x) & Q(a))" $ 
                substF (fromList [("x", constant "c"), ("y", constant "a")])
                       (exist "x" (Atomic "P" [Var "x"] .& Atomic "Q" [Var "y"]))
                       `shouldBe` exist "x" (Atomic "P" [Var "x"] .& Atomic "Q" [constant "a"])

            it "(some x.P(y)){y/x} => some x1.P(x)" $
                substF (singleton "y" $ Var "x")
                       (exist "x" $ Atomic "P" [Var "y"])
                       `shouldBe` exist "x1" (Atomic "P" [Var "x"])

            it "(all x.(P(x) & Q(y)){x/f(c), y/f(x)} => all x1.(P(x1) & Q(f(x)))" $
                substF (fromList [("x", Function "f" [constant "c"]), ("y", Function "f" [Var "x"])])
                       (univ "x" (Atomic "P" [Var "x"] .& Atomic "Q" [Var "y"]))
                       `shouldBe` univ "x1" (Atomic "P" [Var "x1"] .& Atomic "Q" [Function "f" [Var "x"]])

        describe "Unification Tests" $ do
            it "Passes with: x, y => {x/y}" $
                unifyT (Var "x") 
                       (Var "y") 
                       `shouldBe` Just (singleton "x" (Var "y"))

            it "Passes: f(x,c), y => {y/f(x,c)}" $
                unifyT (Function "f" [Var "x", constant "c"]) 
                       (Var "y") 
                       `shouldBe` Just (singleton "y" $ Function "f" [Var "x", constant "c"])

            it "Fails:  f(x,c), x" $
                unifyT (Function "f" [Var "x", constant "c"]) 
                       (Var "x") 
                       `shouldBe` Nothing

            it "Passes: f(c), f(x) => {x/c}" $
                unifyT (Function "f" [constant "c"]) 
                       (Function "f" [Var "x"]) 
                       `shouldBe` Just (singleton "x" $ constant "c")

            it "Passes: f(a,b), f(a,b) => {}" $
                unifyT (Function "f" [constant "a", constant "b"]) 
                       (Function "f" [constant "a", constant "b"]) 
                       `shouldBe` Just mempty

            it "Fails:  f(a,b), g(x,y)" $
                unifyT (Function "f" [constant "a", constant "b"])
                       (Function "g" [Var "x", Var "y"])
                       `shouldBe` Nothing

            it "Fails:  f(x,a,b), f(a,b)" $
                unifyT (Function "f" [Var "x", constant "a", constant "b"])
                       (Function "f" [constant "a", constant "b"])
                       `shouldBe` Nothing

            it "Passes: P(x), P(f(c)) => {x/f(c)}" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [Function "f" [constant "c"]])
                       `shouldBe` Just (singleton "x" $ Function "f" [constant "c"])

            it "Fails:  P(x), P(f(x))" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [Function "f" [Var "x"]])
                       `shouldBe` Nothing

            it "Fails:  P(x), P(a,b)" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "P" [constant "a", constant "b"])
                       `shouldBe` Nothing

            it "Fails:  P(x), Q(a)" $
                unifyF (Atomic "P" [Var "x"])
                       (Atomic "Q" [constant "a"])
                       `shouldBe` Nothing

            it "Fails:  P(x,f(y),g(z,c)), P(h(z),f(x),g(a,x)" $ 
                unifyF (Atomic "P" [Var "x", Function "f" [Var "y"], Function "g" [Var "z", constant "c"]])
                       (Atomic "P" [Function "h" [Var "z"], Function "f" [Var "x"], Function "g" [constant "a", Var "x"]])
                       `shouldBe` Nothing

            it "Passes: P(x,f(y),g(z,c)), P(h(z),f(x),g(a,c) => {x/h(a), y/h(a), z/a}" $
                unifyF (Atomic "P" [Var "x", Function "f" [Var "y"], Function "g" [Var "z", constant "c"]])
                       (Atomic "P" [Function "h" [Var "z"], Function "f" [Var "x"], Function "g" [constant "a", constant "c"]])
                       `shouldBe` Just (fromList [("x", Function "h" [constant "a"]), ("y", Function "h" [constant "a"]), ("z", constant "a")])

randFormula :: Integer -> Formula
randFormula = fst . runGen (genFormula maxFormDepth) . mkSeed

testParse :: Integer -> Bool
testParse s = either (const False) (== freeVarToConst randForm) $ parseFormula $ show randForm
    where
        randForm = fst $ runGen (genFormula maxFormDepth) $ mkSeed s