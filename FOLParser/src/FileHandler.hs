module FileHandler (getHandle, closeHandle) where

import FOL.Base
import Parser
import Tableau

import System.IO
import System.Environment (getExecutablePath)
import System.FilePath ((</>), pathSeparator, isPathSeparator)
import Data.List (intercalate, unfoldr)

import Control.Exception (catch)

relativeToAbsolute :: FilePath -> IO FilePath
relativeToAbsolute path@(p:_) 
    | isPathSeparator p = return path
    | otherwise = (removeDots . (</> ("../" ++ path))) <$> getExecutablePath

{-
relativeToAbsolute :: FilePath -> IO (Maybe FilePath)
relativeToAbsolute path@(p:_) 
    | isPathSeparator p = return $ Just path
    | otherwise = do fmap (removeDots . (</> ("../" ++ path))) getExecutablePath
-}

-- Syntactically removes dots from path if possible
removeDots :: FilePath -> FilePath
removeDots = unslice . removeDotsList [] . slice
    where
        removeDotsList leftPath [] = leftPath
        removeDotsList [] rightPath@("..":_) = rightPath
        removeDotsList leftPath ("..":rightPath) = removeDotsList (init leftPath) rightPath
        removeDotsList leftPath (dir:rightPath) = removeDotsList (leftPath ++ [dir]) rightPath

{-
removeDots :: FilePath -> Maybe FilePath
removeDots = fmap unslice . removeDotsList [] . slice
    where
        removeDotsList leftPath [] = Just leftPath
        removeDotsList [] ("..":_) = Nothing
        removeDotsList leftPath ("..":rightPath) = removeDotsList (init leftPath) rightPath
        removeDotsList leftPath (dir:rightPath) = removeDotsList (leftPath ++ [dir]) rightPath
-}

slice :: FilePath -> [String]
slice "" = []
slice (c:cs) = if isPathSeparator c
               then case unfoldr slice' cs of
                         []     -> [[c]]
                         (p:ps) -> (c:p):ps
               else unfoldr slice' (c:cs)
    where
        slice' "" = Nothing
        slice' ls = Just $ fmap safeTail $ break isPathSeparator ls

        safeTail [] = []
        safeTail ls = tail ls

unslice :: [String] -> FilePath
unslice [] = "."
unslice ls = intercalate [pathSeparator] ls

getHandle :: FilePath -> IO (Bool, Handle)
getHandle relPath = do absPath <- relativeToAbsolute relPath
                       handle <- openFile absPath ReadMode `catch` (\e -> do putStrLn ("Warning: " ++ show (e :: IOError))
                                                                             return stderr)
                       return (handle /= stderr, handle)

closeHandle :: Handle -> IO ()
closeHandle = hClose