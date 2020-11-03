module Main where

import FOL.Base
import Generator
import Unification
import Tableau
import Parser
import FileHandler

import Control.Applicative (Alternative (..))
import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf)
import Data.Set (Set)
import qualified Data.Set as Set

import System.Directory (getCurrentDirectory)
import System.Environment (getExecutablePath)

------ TODO file argument: match until next arg or eof
--                         edit matchUntil so it matches until other match matches
--                         matchUntil :: Match a -> Match String

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

type CommandLoopCallback = Theorem -> IO ()

main :: IO ()
main = do putStrLn "Tableau Theorem Prover"
          putStrLn "Type :help or :? for help"
          commandLoop emptyTheorem

commandLoop :: CommandLoopCallback
commandLoop t = do putStrLn ""
                   line <- getLine
                   if null $ filter (not . isSpace) line 
                   then commandLoop t
                   else commandLoopWithInput t line


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
                      (printReport t commandLoop (Set.member Verbose args)) $ 
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
                                    ":prove [-v] [-s <steps>] [-f <path>]",
                                    "      proves the current theorem",
                                    "        -v : set output to verbose",
                                    "        -s <steps> : sets maximum gamma expansions to steps",
                                    "        -f <path> : proves the theorems contained in a file instead of the current theorem",
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

notEmpty :: String -> Bool
notEmpty = not . null . filter (not . isSpace)

printReport :: Theorem -> CommandLoopCallback -> Bool -> Report -> IO ()
printReport t _ True  (Valid rec) = putStrLn "Valid" >> print rec >> commandLoop t
printReport t _ False (Valid _)   = putStrLn "Valid" >> commandLoop t
printReport t _ True  (Counter example rec) = putStrLn ("Invalid: " ++ show example) >> print rec >> commandLoop t
printReport t _ False (Counter example _)   = putStrLn ("Invalid: " ++ show example) >> commandLoop t
printReport t callback verbose (ExceedSteps steps example tableau) = do putStrLn ("Invalid: " ++ show example)
                                                                        putStrLn ("Assumed to be on an infinite branch after " ++ show steps ++ " steps.")
                                                                        continueInput t callback verbose tableau

continueInput :: Theorem -> CommandLoopCallback -> Bool -> Tableau -> IO ()
continueInput t callback verbose tableau = do putStrLn ("\nContinue tableau? <y [-s <steps>] | n>")
                                              line <- getLine
                                              case match (matchChar 'y' <|> matchChar 'n') line of
                                                   Nothing -> continueInput t callback verbose tableau
                                                   Just ('y', str) -> case match matchArgSteps str of
                                                                           Nothing | notEmpty str -> continueInput t callback verbose tableau
                                                                                   | otherwise    -> continue defaultMaxSteps
                                                                           Just (Steps steps, str') | notEmpty str' -> continueInput t callback verbose tableau
                                                                                                    | otherwise     -> continue steps
                                                   Just ('n', str) | notEmpty str -> continueInput t callback verbose tableau
                                                                   | otherwise    -> callback t
    where
        continue steps = maybe (print "Error Proving" >> callback t)
                               (printReport t callback verbose) $ 
                               continueTableauMaxSteps steps tableau 


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

data ProveArgs = Verbose
               | Steps {steps :: Int}
               | File {path :: String}
    deriving (Show)
instance Eq ProveArgs where
    Verbose == Verbose = True
    (Steps _) == (Steps _) = True
    (File _) == (File _) = True
    _ == _ = False
instance Ord ProveArgs where
    Verbose   <= _         = True
    (Steps _) <= Verbose   = False
    (Steps _) <= _         = True
    (File _)  <= Verbose   = False
    (File _)  <= (Steps _) = False
    (File _)  <= _         = True

getProveArgs :: String -> Set ProveArgs
getProveArgs = collectArgs Set.empty
    where
        collectArgs args str = maybe (if notEmpty str then Set.empty else args) 
                                     (\(arg, str') -> if Set.member arg args
                                                      then Set.empty
                                                      else collectArgs (Set.insert arg args) str') $ 
                                     match (foldl1 (<|>) [matchArgVerbose, matchArgSteps, matchArgFile]) str

matchArgVerbose :: Match ProveArgs
matchArgVerbose = do _ <- matchChar ' '
                     _ <- matchSpaces
                     _ <- matchStr "-v"
                     return Verbose

matchArgSteps :: Match ProveArgs
matchArgSteps = do _ <- matchChar ' '
                   _ <- matchSpaces
                   _ <- matchStr "-s "
                   _ <- matchSpaces
                   steps <- matchNum
                   return $ Steps (read steps :: Int)

matchArgFile :: Match ProveArgs
matchArgFile = do _ <- matchChar ' '
                  _ <- matchSpaces
                  _ <- matchStr "-f "
                  _ <- matchSpaces
                  path <- (matchUntil (\c -> c == '-')) <|> matchUntilEof
                  return $ File path
