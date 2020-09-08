module Parser where
--    ( parseFormula, parseError
--    ) where

import FOL
import Data.Char (isLower, isUpper, isDigit, isSpace)
import Data.List (isPrefixOf, isInfixOf, uncons)
import Data.Either (isLeft)
import Control.Applicative (Alternative(..))

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

matchLower :: Match Char
matchLower = matchCond isLower

matchUpper :: Match Char
matchUpper = matchCond isUpper

matchStr :: String -> Match String
matchStr = mapM matchChar

matchNum :: Match String
matchNum = Match $ \str -> Just $ span isDigit str

matchSpaces :: Match String
matchSpaces = Match $ \str -> Just $ span isSpace str

matchUntil :: (Char -> Bool) -> Match String
matchUntil cond = Match $ \str -> return $ break cond str

matchEmpty :: Match String
matchEmpty = Match $ \str -> if null str
                             then Just ("","")
                             else Nothing

lookAhead :: Char -> Match Bool
lookAhead c = Match $ \str -> maybe 
                              (Just (False,str)) 
                              (\(h,_) -> Just (c==h,str)) $ 
                              uncons str

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
matchInside = do inside <- matchUntil (`elem` "()")
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
                         _ <- matchEmpty
                         return $ Atomic pred terms
                 else do _ <- matchEmpty
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
tokenize = Match $ \str -> if null str
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
    | otherwise = Right $ head $ formStack p

parse :: ParseStep
parse p@(Parser tokens _ _)
    | null tokens = if null $ opStack p
                    then return p
                    else do p' <- resolveOp p
                            parse p'
    | otherwise = do p' <- processToken (head tokens) $ Parser (tail tokens) (opStack p) (formStack p)
                     parse p'

processToken :: Token -> ParseStep
processToken (AtomicToken atom) p = if (not. null . tokenList) p && (head . tokenList) p == OpenToken
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
                            return $ Parser tokenList ops $ oneArgForm op f:forms'
    | argCount op == 2 = maybe 
                         (Left "Invalid formula")
                         Right $ 
                         do (r, forms')  <- uncons formStack
                            (l, forms'') <- uncons forms'
                            return $ Parser tokenList ops $ twoArgForm op l r:forms''
    where
        oneArgForm :: Token -> Formula -> Formula
        oneArgForm NegToken f      = Neg  f
        oneArgForm (AllToken x) f  = All  x f
        oneArgForm (SomeToken x) f = Some x f

        twoArgForm :: Token -> Formula -> Formula -> Formula
        twoArgForm AndToken    l r = And    l r
        twoArgForm OrToken     l r = Or     l r
        twoArgForm ImpToken    l r = Imp    l r
        twoArgForm BicondToken l r = Bicond l r
        
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
