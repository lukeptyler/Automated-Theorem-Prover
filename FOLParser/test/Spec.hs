import FOL.Base
import Generator
import Parser
import Unification

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

        describe "Rewrite Utilities Tests" $ do
            describe "Split Biconditional" $ do
                it "P(x) => P(x)" $
                    splitBiconds (Atomic "P" [Var "x"])
                    `shouldBe` Atomic "P" [Var "x"]

                it "P <-> Q => P <-> Q" $
                    splitBiconds (proposition "P" .<-> proposition "Q")
                    `shouldBe` proposition "P" .<-> proposition "Q"

                it "all x.(P(x) <-> Q) => all x.(P(x) <-> Q)" $
                    splitBiconds (univ "x" $ Atomic "P" [Var "x"] .<-> proposition "Q")
                    `shouldBe` univ "x" (Atomic "P" [Var "x"] .<-> proposition "Q")

                it "all x.P(x) <-> some y.Q(y) => (all x.P(x) -> some y.Q(y)) & (some y.Q(y) -> all x.P(x))" $
                    splitBiconds (univ "x" (Atomic "P" [Var "x"]) .<-> exist "y" (Atomic "Q" [Var "y"]))
                    `shouldBe` (univ "x" (Atomic "P" [Var "x"]) .-> exist "y" (Atomic "Q" [Var "y"])) .& (exist "y" (Atomic "Q" [Var "y"]) .-> univ "x" (Atomic "P" [Var "x"]))

            describe "Name Apart" $ do
                it "P => P" $ 
                    na (proposition "P")
                    `shouldBe` proposition "P"

                it "P(x) => P(x)" $
                    na (Atomic "P" [Var "x"])
                    `shouldBe` Atomic "P" [Var "x"]

                it "all x.P(x) => all x.P(x)" $
                    na (univ "x" $ Atomic "P" [Var "x"])
                    `shouldBe` univ "x" (Atomic "P" [Var "x"])

                it "some x.P(x) & all x.Q(x) => some x.P(x) & all x1.Q(x1)" $
                    na (exist "x" (Atomic "P" [Var "x"]) .& univ "x" (Atomic "Q" [Var "x"]))
                    `shouldBe` exist "x" (Atomic "P" [Var "x"]) .& univ "x1" (Atomic "Q" [Var "x1"])

                it "all x.some y.(P(x,y) & some x.Q(x,y)) => all x.some y.(P(x,y) & some x1.Q(x1,y))" $
                    na (univ "x" $ exist "y" (Atomic "P" [Var "x", Var "y"] .& exist "x" (Atomic "Q" [Var "x", Var "y"])))
                    `shouldBe` univ "x" (exist "y" (Atomic "P" [Var "x", Var "y"] .& exist "x1" (Atomic "Q" [Var "x1", Var "y"])))

                it "all x.some x.some y.all x.P(x,y,x) => all x.some x1.some y.all x2.P(x2,y,x2)" $
                    na (univ "x" $ exist "x" $ exist "y" $ univ "x" $ Atomic "P" [Var "x", Var "y", Var "x"])
                    `shouldBe` univ "x" (exist "x1" $ exist "y" $ univ "x2" $ Atomic "P" [Var "x2", Var "y", Var "x2"])

            describe "Skolemize" $ do
                it "P => P" $
                    sk (proposition "P")
                    `shouldBe` proposition "P"

                it "all x.P(x) => all x.P(x)" $
                    sk (univ "x" $ Atomic "P" [Var "x"])
                    `shouldBe` univ "x" (Atomic "P" [Var "x"])

                it "some x.P(x) => P(sko1)" $
                    sk (exist "x" $ Atomic "P" [Var "x"])
                    `shouldBe` Atomic "P" [constant "sko1"]

                it "-all x.P(x) => -P(sko1)" $
                    sk (neg $ univ "x" $ Atomic "P" [Var "x"])
                    `shouldBe` neg (Atomic "P" [constant "sko1"])

                it "all x.some y.P(y) | all z.some w.Q(w) => all x.P(sko1(x)) | all z.Q(sko2(z))" $
                    sk (univ "x" (exist "y" $ Atomic "P" [Var "y"]) .| univ "z" (exist "w" $ Atomic "Q" [Var "w"]))
                    `shouldBe` univ "x" (Atomic "P" [Function "sko1" [Var "x"]]) .| univ "z" (Atomic "Q" [Function "sko2" [Var "z"]])

                it "all x.(some y.P(y) & Q(x)) => all x.(P(sko1(x)) & Q(x))" $
                    sk (univ "x" $ exist "y" (Atomic "P" [Var "y"]) .& Atomic "Q" [Var "x"])
                    `shouldBe` univ "x" (Atomic "P" [Function "sko1" [Var "x"]] .& Atomic "Q" [Var "x"])

                it "some x.all y.P(x,y) -> Q => some x.P(x, sko1(x)) -> Q" $
                    sk (exist "x" (univ "y" $ Atomic "P" [Var "x", Var "y"]) .-> proposition "Q")
                    `shouldBe` exist "x" (Atomic "P" [Var "x", Function "sko1" [Var "x"]]) .-> proposition "Q"

                it "P -> all y.some x.Q(x,y) => P -> all y.Q(sko1(y), y)" $
                    sk (proposition "P" .-> univ "y" (exist "x" $ Atomic "Q" [Var "x", Var "y"]))
                    `shouldBe` proposition "P" .-> univ "y" (Atomic "Q" [Function "sko1" [Var "y"], Var "y"])

                it "-some x.(P(x) -> all y.Q(y)) => -some x.(P(x) -> Q(sko1(x)))" $
                    sk (neg $ exist "x" $ Atomic "P" [Var "x"] .-> univ "y" (Atomic "Q" [Var "y"]))
                    `shouldBe` neg (exist "x" $ Atomic "P" [Var "x"] .-> Atomic "Q" [Function "sko1" [Var "x"]])

                it "all x.some y.all z.some w.P(x,y,z,w) => all x.all z.P(x,sko1(x),z,sko2(x,z))" $
                    sk (univ "x" $ exist "y" $ univ "z" $ exist "w" $ Atomic "P" [Var "x", Var "y", Var "z", Var "w"])
                    `shouldBe` univ "x" (univ "z" $ Atomic "P" [Var "x", Function "sko1" [Var "x"], Var "z", Function "sko2" [Var "x", Var "z"]])

                it "-some x.some y.(P(x,y) -> all z.all w.Q(z,w)) => -some x.some y.(P(x,y) -> Q(sko1(x,y), sko2(x,y)))" $
                    sk (neg $ exist "x" $ exist "y" $ Atomic "P" [Var "x", Var "y"] .-> univ "z" (univ "w" $ Atomic "Q" [Var "z", Var "w"]))
                    `shouldBe` neg (exist "x" $ exist "y" $ Atomic "P" [Var "x", Var "y"] .-> Atomic "Q" [Function "sko1" [Var "x", Var "y"], Function "sko2" [Var "x", Var "y"]])

            describe "Normalize" $ do
                it "all x.some y.P(x,y) <-> all y.some x.Q(x,f(x,y)) \n\t=> (some y.P(sko1(y), y) -> all y1.Q(sko2(y1), f(sko1(y1),y1))) & (some x2.Q(x2, f(x2,sko3(x2))) -> all x3.P(x3, sko4(x3)))" $
                    normalize (univ "x" (exist "y" $ Atomic "P" [Var "x", Var "y"]) .<-> univ "y" (exist "x" $ Atomic "Q" [Var "x", Function "f" [Var "x", Var "y"]]))
                    `shouldBe` (exist "y" (Atomic "P" [constant "sko1", Var "y"]) .-> univ "y1" (Atomic "Q" [Function "sko2" [Var "y1"], Function "f" [Function "sko2" [Var "y1"], Var "y1"]])) .& 
                               (exist "x2" (Atomic "Q" [Var "x2", Function "f" [Var "x2", constant "sko3"]]) .-> univ "x3" (Atomic "P" [Var "x3", Function "sko4" [Var "x3"]]))

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
            it "Passes: x, y => {x/y}" $
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

sk :: Formula -> Formula
sk = snd . skolemize [] True 1

na :: Formula -> Formula
na = snd . nameApart []
