module Main where

import FOL.Base
import Generator
import Unification
import Tableau
import Parser
import FileHandler

import Control.Applicative (Alternative (..))
import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf, isSubsequenceOf, isPrefixOf)
import Data.List.Split (splitOn)
import Data.Set (Set)
import qualified Data.Set as Set

--import System.IO (Handle, hIsEOF, hGetLine)
import System.IO

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

data CommandLoopCallback = MainCallback {theorem :: Theorem}
                         | FileCallback {theorem :: Theorem, args :: Set ProveArgs, theoremList :: [Theorem]}

main :: IO ()
main = do putStrLn "Tableau Theorem Prover"
          putStrLn "Type :help or :? for help"
          commandLoop emptyTheorem

commandLoop :: Theorem -> IO ()
commandLoop t = do line <- getLine
                   if null $ filter (not . isSpace) line 
                   then commandLoop t
                   else maybe (invalidCommand t) (processCommand t) $ match matchCommand line

invalidCommand :: Theorem -> IO ()
invalidCommand t = putStrLn "Invalid Command" >> commandLoop t

processCommand :: Theorem -> (Command, String) -> IO ()
processCommand t (Prem, str) = processFormula t 
                               (\f -> commandLoop $ t {props = props t ++ [f]}) $
                               parseFormula str
processCommand t (Conc, str) = processFormula t
                               (\f -> commandLoop $ t {conc = f}) $
                               parseFormula str

processCommand t (Set index, str) = processFormula t
                                    (\f -> commandLoop $ t {props = set (props t) index f}) $ 
                                    parseFormula str
    where
        set :: [a] -> Int -> a -> [a]
        set ls index elem
            | index <= 0 = ls
            | index > length ls = ls
            | otherwise = let (x,_:ys) = splitAt (index-1) ls in x ++ [elem] ++ ys
processCommand t (Remove index, str)
    | isNotEmpty str = invalidCommand t
    | index <= 0 = commandLoop t
    | index > length (props t) = commandLoop t
    | otherwise = let (x,_:ys) = splitAt (index-1) $ props t in
                  commandLoop $ t {props = x ++ ys}
processCommand t (Preview, str)
    | isNotEmpty str = invalidCommand t
    | otherwise = print t >> commandLoop t
processCommand t (Clear, str)
    | isNotEmpty str = invalidCommand t
    | otherwise = commandLoop emptyTheorem
processCommand t (Prove, str)
    | Set.null args && isNotEmpty str = invalidCommand t
    | Set.member (File "") args = processFile t args
    | isValidTheorem t = putStrLn "Must set conclusion before proving." >> commandLoop t
    | otherwise = prove t args $ MainCallback t
    where
        args = getProveArgs str
processCommand t (Quit, str)
    | isNotEmpty str = invalidCommand t
    | otherwise = return ()
processCommand t (Help, str)
    | isNotEmpty str = invalidCommand t
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

prove :: Theorem -> Set ProveArgs -> CommandLoopCallback -> IO ()
prove t args callback = maybe (print "Error Proving" >> commandLoop t)
                              (printReport t callback (Set.member Verbose args)) $ 
                              maybe (proveTheorem t) 
                                    (\index -> proveTheoremMaxSteps (steps $ Set.elemAt index args) t) 
                                    stepIndex
    where
        stepIndex = Set.lookupIndex (Steps 0) args

processFormula :: Theorem -> (Formula -> IO ()) -> Either ParseError Formula -> IO ()
processFormula t process form = either (\parseError -> putStrLn parseError >> commandLoop t) process form

isEmpty :: String -> Bool
isEmpty = null . filter (not . isSpace)

isNotEmpty :: String -> Bool
isNotEmpty = not . isEmpty

printReport :: Theorem -> CommandLoopCallback -> Bool -> Report -> IO ()
printReport t callback True  (Valid rec) = do putStrLn $ show t
                                              putStrLn "Valid"
                                              print rec
                                              putStrLn "\n"
                                              runCallback callback
printReport t callback False (Valid _)   = do putStrLn $ show t
                                              putStrLn "Valid"
                                              putStrLn "\n"
                                              runCallback callback
printReport t callback True  (Counter example rec) = do putStrLn $ show t
                                                        putStrLn $ "Invalid: " ++ show example
                                                        print rec
                                                        putStrLn "\n"
                                                        runCallback callback
printReport t callback False (Counter example _)   = do putStrLn $ show t
                                                        putStrLn $ "Invalid: " ++ show example
                                                        putStrLn "\n"
                                                        runCallback callback
printReport t callback verbose (ExceedSteps steps example tableau) = do putStrLn $ show t
                                                                        putStrLn $ "Invalid: " ++ show example
                                                                        putStrLn $ "Assumed to be on an infinite branch after " ++ show steps ++ " steps."
                                                                        continueInput t callback verbose tableau

continueInput :: Theorem -> CommandLoopCallback -> Bool -> Tableau -> IO ()
continueInput t callback verbose tableau = do putStrLn ("\nContinue tableau? <y [steps] | n>")
                                              line <- getLine
                                              case match (matchChar 'y' <|> matchChar 'n') line of
                                                   Nothing -> continueInput t callback verbose tableau
                                                   Just ('y', str) -> case match (matchSpaces >> matchInt) str of
                                                                           Nothing | isNotEmpty str -> continueInput t callback verbose tableau
                                                                                   | otherwise    -> continue defaultMaxSteps
                                                                           Just (steps, str') | isNotEmpty str' -> continueInput t callback verbose tableau
                                                                                              | otherwise     -> continue steps
                                                   Just ('n', str) | isNotEmpty str -> continueInput t callback verbose tableau
                                                                   | otherwise    -> runCallback callback
    where
        continue steps = maybe (print "Error Proving" >> runCallback callback)
                               (printReport t callback verbose) $ 
                               continueTableauMaxSteps steps tableau 

runCallback :: CommandLoopCallback -> IO ()
runCallback (MainCallback t) = commandLoop t
runCallback (FileCallback t args thms) = proveFile t args thms

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
              index <- matchInt
              _ <- matchChar ' '
              return $ Set index

matchRemove :: Match Command
matchRemove = do _ <- matchStr ":remove "
                 index <- matchInt
                 return $ Remove index

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
        collectArgs args str = maybe (if isNotEmpty str then Set.empty else args) 
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
                   steps <- matchInt
                   return $ Steps steps

matchArgFile :: Match ProveArgs
matchArgFile = do _ <- matchChar ' '
                  _ <- matchSpaces
                  _ <- matchStr "-f "
                  _ <- matchSpaces
                  path <- (matchUntil $ matchStr " -") <|> (matchUntil matchEof)
                  return $ File path

-- File Proving

processFile :: Theorem -> Set ProveArgs -> IO ()
processFile t args = do (validHandle, handle) <- getHandle relPath

                        if validHandle
                        then do fileContents <- parseFile handle
                                either (\err -> do putStrLn err
                                                   closeHandle handle
                                                   commandLoop t) 
                                       (\thms -> do proveFile t args thms
                                                    closeHandle handle) $ 
                                       fileContents
                        else closeHandle handle >> commandLoop t

    where
        (File relPath) = Set.elemAt (Set.findIndex (File "") args) args

proveFile :: Theorem -> Set ProveArgs -> [Theorem] -> IO ()
proveFile t args [] = commandLoop t
proveFile t args (thm:thms) = prove thm args $ FileCallback t args thms

-- File Parsing

parseFile :: Handle -> IO (Either ParseError [Theorem])
parseFile h = do hasAxioms <- parseAxiomHeader h
                 if hasAxioms
                 then do axioms <- parseAxioms h []
                         either (return . Left)
                                (\axs -> parseTheorems h axs []) $
                                axioms
                 else parseTheorems h [] []

parseAxiomHeader :: Handle -> IO (Bool)
parseAxiomHeader h = do eof <- hIsEOF h
                        if eof then return False
                        else do line <- hGetLine h
                                case filter (not . isSpace) line of
                                     "Axioms:" -> return True
                                     "Theorems:" -> return False
                                     _ -> parseAxiomHeader h

parseAxioms :: Handle -> [Formula] -> IO (Either ParseError [Formula])
parseAxioms h axioms = do eof <- hIsEOF h
                          if eof then return $ Right axioms
                          else do line <- hGetLine h
                                  case filter (not . isSpace) line of
                                       "Theorems:" -> return $ Right axioms
                                       _ | isEmpty line || "#" `isPrefixOf` line -> parseAxioms h axioms
                                         | ';' `elem` line -> either (return . Left)
                                                                     (\axs -> parseAxioms h $ axioms ++ axs) $
                                                                     parseList line
                                         | otherwise -> either (return . Left)
                                                               (\ax -> parseAxioms h $ axioms ++ [ax]) $
                                                               parseFormula line
                                                                    
parseTheorems :: Handle -> [Formula] -> [Theorem] -> IO (Either ParseError [Theorem])
parseTheorems h axioms theorems = do eof <- hIsEOF h
                                     if eof then (if null theorems 
                                                  then return $ Left "No theorems in file"
                                                  else return $ Right theorems)
                                     else do pos <- hGetPosn h
                                             line <- hGetLine h
                                             case line of
                                                  _ | isEmpty line || "#" `isPrefixOf` line -> parseTheorems h axioms theorems
                                                    | "|=" `isSubsequenceOf` line -> either (return . Left)
                                                                                            (\(Theorem prems conc display) -> parseTheorems h axioms $ theorems ++ [Theorem (axioms ++ prems) conc display]) $
                                                                                            parseTheoremList line
                                                    | otherwise -> do hSetPosn pos
                                                                      thm <- parseTheoremStack h
                                                                      either (return . Left)
                                                                             (\(Theorem prems conc display) -> parseTheorems h axioms $ theorems ++ [Theorem (axioms ++ prems) conc display]) $
                                                                             thm
                                                                          

parseList :: String -> Either ParseError [Formula]
parseList = sequence . map parseFormula . filter (\str -> not $ null str || isEmpty str) . splitOn ";"
                   
parseTheoremList :: String -> Either ParseError Theorem
parseTheoremList str
    | not $ null cs = Left $ "Invalid Theorem: " ++ str
    | otherwise     = do prems <- parseList premList
                         conc  <- parseFormula concStr
                         return $ Theorem prems conc List
    where
        (premList:concStr:cs) = splitOn "|=" str

parseTheoremStack :: Handle -> IO (Either ParseError Theorem)
parseTheoremStack h = do parsedPrems <- parseStackPrems h []
                         parsedConc <- parseStackConc h
                         return $ do prems <- parsedPrems
                                     conc <- parsedConc
                                     return $ Theorem prems conc Stack

parseStackPrems :: Handle -> [Formula] -> IO (Either ParseError [Formula])
parseStackPrems h prems = do eof <- hIsEOF h
                             if eof then return $ Left "Invalid Theorem: Missing Conclusion"
                             else do line <- hGetLine h
                                     case filter ((/=) '-') line of
                                          "" -> return $ Right prems
                                          _ | isEmpty line || "#" `isPrefixOf` line -> parseStackPrems h prems
                                            | otherwise -> either (return . Left)
                                                                  (\f -> parseStackPrems h $ prems ++ [f]) $ 
                                                                  parseFormula line

parseStackConc :: Handle -> IO (Either ParseError Formula)
parseStackConc h = do eof <- hIsEOF h
                      if eof then return $ Left "Invalid Theorem: Missing Conclusion"
                      else do line <- hGetLine h
                              case line of
                                   _ |  isEmpty line || "#" `isPrefixOf` line -> parseStackConc h
                                     | otherwise -> either (return . Left)
                                                           (return . Right) $
                                                           parseFormula line