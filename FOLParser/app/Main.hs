module Main where

import FOL.Base
import Generator
import Unification
import Tableau
import Parser

import Control.Applicative (Alternative (..))
import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf)
import Data.Set (Set)
import qualified Data.Set as Set

data Command = Prem
             | Conc
             | Set Int
             | Remove Int
             | Preview
             | Clear
             | Prove
             | Quit
             | Help
             | Cont
    deriving (Show)

main :: IO ()
main = do putStrLn "Tableau Theorem Prover"
          putStrLn "Type :help or :? for help"
          commandLoop emptyTheorem

commandLoop :: Theorem -> IO ()
commandLoop t = do putStrLn ""
                   line <- getLine
                   if null $ filter (not . isSpace) line 
                   then commandLoop t
                   else commandLoopWithInput t line

continueInput :: Theorem -> Tableau -> IO ()
continueInput t tableau = do line <- getLine
                             if null $ filter (not . isSpace) line
                             then continueInput t tableau
                             else case match matchContinue line of
                                       Just (Cont, str) -> processContinue t tableau str
                                       _                    -> commandLoopWithInput t line


commandLoopWithInput :: Theorem -> String -> IO ()
commandLoopWithInput t = maybe (invalidCommand t) (processCommand t) . match matchCommand

invalidCommand :: Theorem -> IO ()
invalidCommand t = putStrLn "Invalid Command" >> commandLoop t

processCommand :: Theorem -> (Command, String) -> IO ()
processCommand t (Prem, str) = processFormula t 
                               (\f -> let t' = t {props = props t ++ [f]} in print t' >> commandLoop t') $
                               parseFormula str
processCommand t (Conc, str) = processFormula t
                               (\f -> let t' = t {conc = f} in print t' >> commandLoop t') $
                               parseFormula str

processCommand t (Set index, str) = processFormula t
                                    (\f -> let t' = t {props = set (props t) index f} in print t' >> commandLoop t') $ 
                                    parseFormula str
    where
        set :: [a] -> Int -> a -> [a]
        set ls index elem
            | index <= 0 = ls
            | index > length ls = ls
            | otherwise = let (x,_:ys) = splitAt (index-1) ls in x ++ [elem] ++ ys
processCommand t (Remove index, str)
    | notEmpty str = invalidCommand t
    | index <= 0 = commandLoop t
    | index > length (props t) = commandLoop t
    | otherwise = let (x,_:ys) = splitAt (index-1) $ props t in
                  let t' = t {props = x ++ ys} in
                  print t' >> commandLoop t'
processCommand t (Preview, str)
    | notEmpty str = invalidCommand t
    | otherwise = print t >> commandLoop t
processCommand t (Clear, str)
    | notEmpty str = invalidCommand t
    | otherwise = print emptyTheorem >> commandLoop emptyTheorem
processCommand t@(Theorem _ conc) (Prove, str)
    | Set.null args && notEmpty str = invalidCommand t
    | isNullFormula conc = putStrLn "Must set conclusion before proving." >> commandLoop t
    | otherwise = prove
    where
        args = getProveArgs str

        stepIndex = Set.lookupIndex (Steps 0) args

        prove :: IO ()
        prove = maybe (print "Error Proving" >> commandLoop t)
                      (printReport t (Set.member Verbose args)) $ 
                      maybe (proveTheorem t) 
                            (\index -> proveTheoremMaxSteps (steps $ Set.elemAt index args) t) 
                            stepIndex
processCommand t (Quit, str)
    | notEmpty str = invalidCommand t
    | otherwise = return ()
processCommand t (Help, str)
    | notEmpty str = invalidCommand t
    | otherwise = do mapM putStrLn ["Commands:",
                                    ":prem <form>",
                                    "      adds a formula to the end of the premises of the current theorem",
                                    ":conc <form>",
                                    "      sets the conclusion of the current theorem",
                                    ":set <index> <form>",
                                    "      sets the premise at the index to the formula",
                                    ":remove <index>",
                                    "      removes the premise at the index from the current theorem",
                                    ":preview",
                                    "      displayes the current theorem",
                                    ":clear",
                                    "      clears the current theorem",
                                    ":prove [-v] [-s <steps>]",
                                    "      proves the current theorem",
                                    "        -v : set output to verbose",
                                    "        -s <steps> : sets maximum gamma expansions to steps",
                                    ":cont [-v] [-s <steps>]",
                                    "      continues a proof after an assumption of an infinite branch",
                                    "        -v : set output to verbose",
                                    "        -s <steps> : sets maximum gamma expansions to steps",
                                    ":quit",
                                    "      exists the program",
                                    "",
                                    "Syntax:",
                                    "  universal quantifier:   all <varId>.",
                                    "  existential quantifier: some <varId>.",
                                    "  negation:               -",
                                    "  conjunction:            &",
                                    "  disjunction:            |",
                                    "  implication:            ->",
                                    "  biconditional:          <->"
                                   ]
                     commandLoop t


processFormula :: Theorem -> (Formula -> IO ()) -> Either ParseError Formula -> IO ()
processFormula t process form = either (\parseError -> putStrLn parseError >> commandLoop t) process form

invalidContinue :: Theorem -> Tableau -> IO ()
invalidContinue t tableau = putStrLn "Invalid Command\n" >> continueInput t tableau

processContinue :: Theorem -> Tableau -> String -> IO ()
processContinue t tableau argStr
    | Set.null args && notEmpty argStr = invalidContinue t tableau
    | otherwise = prove
    where
        args = getProveArgs argStr

        stepIndex = Set.lookupIndex (Steps 0) args

        prove :: IO ()
        prove = maybe (print "Error Proving" >> commandLoop t)
                      (printReport t (Set.member Verbose args)) $ 
                      maybe (continueTableau tableau) 
                            (\index -> continueTableauMaxSteps (steps $ Set.elemAt index args) tableau) 
                            stepIndex

notEmpty :: String -> Bool
notEmpty = not . null . filter (not . isSpace)

printReport :: Theorem -> Bool -> Report -> IO ()
printReport t True  (Valid rec) = putStrLn "Valid" >> print rec >> commandLoop t
printReport t False (Valid _)   = putStrLn "Valid" >> commandLoop t
printReport t True  (Counter example rec) = putStrLn ("Invalid: " ++ show example) >> print rec >> commandLoop t
printReport t False (Counter example _)   = putStrLn ("Invalid: " ++ show example) >> commandLoop t
printReport t _     (ExceedSteps steps example tableau) = do putStrLn ("Invalid: " ++ show example)
                                                             putStrLn ("Assumed to be on an infinite branch after " ++ show steps ++ " steps.")
                                                             putStrLn ("Use :cont [-v] [-s <steps>] to continue the tableau.\n")
                                                             continueInput t tableau

commandList = [(":prem ",   Prem),
               (":conc ",   Conc),
               (":preview", Preview),
               (":clear",   Clear),
               (":prove",   Prove),
               (":quit",    Quit),
               (":help",    Help),
               (":?",       Help)]

matchSet :: Match Command
matchSet = do _ <- matchStr ":set "
              index <- matchNum
              _ <- matchChar ' '
              return $ Set (read index :: Int)

matchRemove :: Match Command
matchRemove = do _ <- matchStr ":remove "
                 index <- matchNum
                 return $ Remove (read index :: Int)

matchCommand :: Match Command
matchCommand = foldl1 (<|>) $ map constructCommand commandList ++ [matchSet, matchRemove]
    where
        constructCommand (target, goal) = do _ <- matchStr target
                                             return goal

matchContinue :: Match Command
matchContinue = do _ <- matchStr ":cont"
                   return Cont

data ProveArgs = Verbose
               | Steps {steps :: Int}
    deriving (Show)
instance Eq ProveArgs where
    Verbose == Verbose = True
    (Steps _) == (Steps _) = True
    _ == _ = False
instance Ord ProveArgs where
    Verbose <= _ = True
    (Steps _) <= Verbose = False
    (Steps _) <= (Steps _) = True

getProveArgs :: String -> Set ProveArgs
getProveArgs = collectArgs Set.empty
    where
        collectArgs args str = maybe (if notEmpty str then Set.empty else args) 
                                     (\(arg, str') -> if Set.member arg args
                                                      then Set.empty
                                                      else collectArgs (Set.insert arg args) str') $ 
                                     match (foldl1 (<|>) [matchArgVerbose, matchArgSteps]) str

matchArgVerbose :: Match ProveArgs
matchArgVerbose = do _ <- matchChar ' '
                     _ <- matchSpaces
                     _ <- matchStr "-v"
                     return Verbose

matchArgSteps :: Match ProveArgs
matchArgSteps = do _ <- matchChar ' '
                   _ <- matchSpaces
                   _ <- matchStr "-s"
                   _ <- matchChar ' '
                   _ <- matchSpaces
                   steps <- matchNum
                   return $ Steps (read steps :: Int)
