module FileHandler where

import System.Environment (getExecutablePath)
import System.FilePath ((</>), pathSeparator, isPathSeparator)
import Data.List (intercalate, unfoldr)

relativeToAbsolute :: String -> IO (Maybe String)
relativeToAbsolute path@(p:_) 
    | isPathSeparator p = return $ Just path
    | otherwise = do fmap (removeDots . (</> ("../" ++ path))) getExecutablePath

removeDots :: String -> Maybe String
removeDots = fmap unslice . removeDotsList [] . slice
    where
        removeDotsList leftPath [] = Just leftPath
        removeDotsList [] ("..":_) = Nothing
        removeDotsList leftPath ("..":rightPath) = removeDotsList (init leftPath) rightPath
        removeDotsList leftPath (dir:rightPath) = removeDotsList (leftPath ++ [dir]) rightPath

slice :: String -> [String]
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

unslice :: [String] -> String
unslice [] = "."
unslice ls = intercalate [pathSeparator] ls