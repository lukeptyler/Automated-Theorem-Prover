module Parser where

import FOL.Base
import Data.Char (isLower, isUpper, isDigit, isSpace)
import Data.List (isPrefixOf, isInfixOf, uncons)
import Data.Either (isLeft)
import Control.Applicative (Alternative(..))
import Control.Monad (guard)

data Token = AtomicToken String
           | NegToken
           | AndToken
           | OrToken
           | ImpToken
           | BicondToken
           | AllToken  VarId
           | SomeToken VarId
           | OpenToken
           | ClosedToken
    deriving (Show, Eq)

newtype Match a = Match {match :: String -> Maybe (a, String)}

instance Functor Match where
    fmap f matchA = Match $ \str -> do
                        (a,str') <- match matchA str
                        Just (f a, str')

instance Applicative Match where
    pure x = Match $ \str -> Just (x,str)

    matchF <*> matchA = Match $ \str -> do
                            (f,str')  <- match matchF str
                            (a,str'') <- match matchA str'
                            Just (f a, str'')

instance Monad Match where
    return = pure
    matchA >>= f = Match $ \str -> do
                        (a,str') <- match matchA str
                        match (f a) str'

instance Alternative Match where
    empty = Match $ const Nothing

    matchA <|> matchB = Match $ \str -> match matchA str <|> match matchB str

matchCond :: (Char -> Bool) -> Match Char
matchCond cond = Match $ \str -> case str of 
                x:xs | cond x    -> Just (x,xs)
                     | otherwise -> Nothing
                []               -> Nothing

matchChar :: Char -> Match Char
matchChar c = matchCond (== c)

matchCharIn :: String -> Match Char
matchCharIn str = matchCond (`elem` str)

matchLower :: Match Char
matchLower = matchCond isLower

matchUpper :: Match Char
matchUpper = matchCond isUpper

matchStr :: String -> Match String
matchStr = mapM matchChar

matchNum :: Match String
matchNum = Match $ \str -> Just $ span isDigit str

matchInt :: Match Int
matchInt = do n <- matchNum
              guard (not $ null n)
              return $ (read n :: Int)

matchSpaces :: Match String
matchSpaces = Match $ \str -> Just $ span isSpace str

matchUntil :: Match a -> Match String
matchUntil matchCondition = Match $ scan ""
    where
        scan :: String -> String -> Maybe (String, String)
        scan matched "" = Just (matched, "")
        scan matched str@(c:cs) = case match matchCondition str of
                               Nothing -> scan (matched ++ [c]) cs
                               _       -> Just (matched, str) 

matchEof :: Match String
matchEof = Match $ \str -> if null str
                           then Just ("","")
                           else Nothing

lookAhead :: Char -> Match Bool
lookAhead c = Match $ \str -> maybe 
                              (Just (False,str)) 
                              (\(h,_) -> Just (c==h,str)) $ 
                              uncons str

isEof :: Match Bool
isEof = Match $ \str -> if null str then Just (True,"") else Just (False,str)

matchVarId :: Match VarId
matchVarId = (:) <$> matchLower <*> matchNum

matchPredId :: Match PredId
matchPredId = (:) <$> matchUpper <*> matchNum

matchGroup :: Match String
matchGroup = do start <- lookAhead '('  
                if start 
                then (:) <$> matchChar '(' <*> matchInside 
                else return ""
    
matchInside :: Match String
matchInside = do err <- isEof
                 if err
                 then empty
                 else do inside <- matchUntil $ matchCharIn "()"
                         end <- lookAhead ')'
                         if end 
                         then (inside ++) <$> matchStr ")" 
                         else do rest <- (++) <$> matchGroup <*> matchInside
                                 return $ inside ++ rest

matchAtomicToken :: Match Token
matchAtomicToken = do pred <- matchPredId
                      _ <- matchSpaces
                      group <- matchGroup
                      return $ AtomicToken $ pred ++ group

matchAll :: Match Token
matchAll = do _  <- matchStr "all " <|> matchStr "All "
              _  <- matchSpaces
              id <- matchVarId
              _  <- matchSpaces
              _  <- matchChar '.'
              return $ AllToken id

matchSome :: Match Token
matchSome = do _  <- matchStr "some " <|> matchStr "Some "
               id <- matchVarId
               _  <- matchChar '.'
               return $ SomeToken id

constructMatch :: (String, a) -> Match a
constructMatch (target, goal) = do _ <- matchStr target
                                   return goal

tokenMap :: [(String, Token)]
tokenMap = [("->",  ImpToken), 
            ("<->", BicondToken), 
            ("-",   NegToken),
            ("&",   AndToken),
            ("|",   OrToken),
            ("(",   OpenToken),
            (")",   ClosedToken)]

matchToken :: Match Token
matchToken = do _ <- matchSpaces
                foldl1 (<|>) $ [matchAll, matchSome, matchAtomicToken] ++ map constructMatch tokenMap

matchAtomic :: Match Formula
matchAtomic = do pred <- matchPredId
                 hasGroup <- lookAhead '('
                 if hasGroup
                 then do terms <- matchTermList
                         _ <- matchEof
                         return $ Atomic pred terms
                 else do _ <- matchEof
                         return $ Atomic pred []

matchTermList :: Match [Term]
matchTermList = do _ <- matchChar '('
                   t1 <- matchTerm
                   terms <- matchTermList'
                   _ <- matchChar ')'
                   return $ t1:terms
    where
        matchTermList' :: Match [Term]
        matchTermList' = do nextTerm <- lookAhead ','
                            if nextTerm
                            then do _ <- matchChar ','
                                    (:) <$> matchTerm <*> matchTermList'
                            else return []

matchTerm :: Match Term
matchTerm = matchFunc <|> matchVar

matchFunc :: Match Term
matchFunc = Function <$> matchVarId <*> matchTermList

matchVar :: Match Term
matchVar = Var <$> matchVarId

----------------------------

{- TWO PASS PARSER -}
data Parser = Parser {tokenList :: [Token], opStack :: [Token], formStack :: [Formula]}
    deriving (Show)
type ParseError = String
type ParseResult = Either ParseError Parser

type ParseStep = Parser -> ParseResult

data Precedence = Prec {prec :: Int, leftAssoc :: Bool}

tokenize :: Match [Token]
tokenize = Match $ \str -> if null $ filter (not . isSpace) str
                           then Just ([], "")
                           else match ((:) <$> matchToken <*> tokenize) str

parseFormula :: String -> Either ParseError Formula
parseFormula str
    | "()" `isInfixOf` str = Left "Can not contain empty group ()"
    | otherwise = maybe (Left "Error tokenizing")
                        (\(tokens,_) -> either Left
                                               extractResult $
                                               parse $ Parser tokens [] []
                        ) $
                        match tokenize str

extractResult :: Parser -> Either ParseError Formula
extractResult p
    | (not . null . tokenList) p || (not . null . opStack) p || (length . formStack) p /= 1 = Left "Invalid formula"
    | otherwise = Right $ freeVarToConst $ head $ formStack p

parse :: ParseStep
parse p@(Parser tokens _ _)
    | null tokens = if null $ opStack p
                    then return p
                    else do p' <- resolveOp p
                            parse p'
    | otherwise = do p' <- processToken (head tokens) $ Parser (tail tokens) (opStack p) (formStack p)
                     parse p'

processToken :: Token -> ParseStep
processToken (AtomicToken atom) p = if (not . null . tokenList) p && (head . tokenList) p == OpenToken
                                    then Left "Invalid formula"
                                    else maybe (Left $ "Invalid atomic formula " ++ atom)
                                               (\(form, _) -> pushFormula form p) $
                                               match matchAtomic $ filter (not . isSpace) atom
processToken ClosedToken p = case uncons $ tokenList p of
                                  Just (AtomicToken _, _) -> Left "Invalid formula"
                                  Just (OpenToken,     _) -> Left "Invalid formula"
                                  _ -> resolveGroup p
processToken op p = pushOp op p


pushFormula :: Formula -> ParseStep
pushFormula form (Parser tokenList opStack formStack) = Right $ Parser tokenList opStack $ form:formStack

pushOp :: Token -> ParseStep
pushOp OpenToken (Parser tokenList opStack  formStack) = Right $ Parser tokenList (OpenToken:opStack) formStack
pushOp push      (Parser tokenList []       formStack) = Right $ Parser tokenList [push] formStack
pushOp push    p@(Parser tokenList (op:ops) formStack)
    | prec precOp > prec precPush || 
        (prec precOp == prec precPush && leftAssoc precOp) = do p' <- resolveOp p
                                                                pushOp push p'
    | otherwise = Right $ Parser tokenList (push:op:ops) formStack
    where
        precOp   = precedence op
        precPush = precedence push

resolveGroup :: ParseStep
resolveGroup p@(Parser _ opStack _)
    | OpenToken `elem` opStack = resolveGroup' p
    | otherwise                = Left "Unbalanced parentheses"
    where
        resolveGroup' :: ParseStep
        resolveGroup' (Parser tokenList (OpenToken:ops) formStack) = Right $ Parser tokenList ops formStack
        resolveGroup' p = do p' <- resolveOp p
                             resolveGroup' p'

resolveOp :: ParseStep
resolveOp (Parser _ [] _) = Left "Invalid formula"
resolveOp (Parser _ (OpenToken:_) _) = Left "Unbalanced parentheses"
resolveOp (Parser tokenList (op:ops) formStack)
    | argCount op == 1 = maybe
                         (Left "Invalid formula")
                         Right $ 
                         do (f, forms') <- uncons formStack
                            return $ Parser tokenList ops $ unary op f:forms'
    | argCount op == 2 = maybe 
                         (Left "Invalid formula")
                         Right $ 
                         do (r, forms')  <- uncons formStack
                            (l, forms'') <- uncons forms'
                            return $ Parser tokenList ops $ binary op l r:forms''
    where
        unary :: Token -> Formula -> Formula
        unary NegToken f       = Neg  f
        unary (AllToken id)  f = Quant All  id f
        unary (SomeToken id) f = Quant Some id f

        binary :: Token -> Formula -> Formula -> Formula
        binary AndToken    l r = Binary And    l r
        binary OrToken     l r = Binary Or     l r
        binary ImpToken    l r = Binary Imp    l r
        binary BicondToken l r = Binary Bicond l r
        
precedence :: Token -> Precedence
precedence NegToken      = Prec 5 False
precedence AndToken      = Prec 4 True
precedence OrToken       = Prec 3 True
precedence ImpToken      = Prec 2 True
precedence BicondToken   = Prec 1 True
precedence (AllToken _)  = Prec 6 False
precedence (SomeToken _) = Prec 6 False
precedence OpenToken     = Prec (-1) False

argCount :: Token -> Int
argCount NegToken      = 1
argCount AndToken      = 2
argCount OrToken       = 2
argCount ImpToken      = 2
argCount BicondToken   = 2
argCount (AllToken _)  = 1
argCount (SomeToken _) = 1

parseError :: Either ParseError Formula -> Bool
parseError = isLeft