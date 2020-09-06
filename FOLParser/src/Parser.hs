module Parser where

import FOL
import Data.Char (isLower, isUpper, isDigit, isSpace)
import Data.List (isPrefixOf, isInfixOf, uncons)
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

data Match a = Match {match :: String -> Maybe (a, String)}

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
    empty = Match $ \_ -> Nothing

    matchA <|> matchB = Match $ \str -> (match matchA str) <|> (match matchB str)

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
matchStr str = sequence $ map matchChar str

matchNum :: Match String
matchNum = Match $ \str -> Just $ span isDigit str

matchSpaces :: Match String
matchSpaces = Match $ \str -> Just $ span isSpace str

matchUntil :: (Char -> Bool) -> Match String
matchUntil cond = Match $ \str -> return $ break cond str

lookAhead :: Char -> Match Bool
lookAhead c = Match $ \str -> maybe (Just (False,str)) (\(h,_) -> Just (c==h,str)) $ uncons str

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
matchInside = do inside <- matchUntil (\x -> x `elem` "()")
                 end <- lookAhead ')'
                 if end 
                 then (inside ++) <$> matchStr ")" 
                 else do rest <- (++) <$> matchGroup <*> matchInside
                         return $ inside ++ rest

matchAtomicToken :: Match Token
matchAtomicToken = do pred <- matchPredId
                      group <- matchGroup
                      return $ AtomicToken $ pred ++ group

matchAll :: Match Token
matchAll = do _  <- (matchStr "all " <|> matchStr "All ")
              id <- matchVarId
              _  <- matchChar '.'
              return $ AllToken id

matchSome :: Match Token
matchSome = do _  <- (matchStr "some " <|> matchStr "Some ")
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
                 then do _ <- matchSpaces
                         terms <- matchTermList
                         return $ Atomic pred terms
                 else return $ Atomic pred []

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
matchFunc = do id <- matchVarId
               terms <- matchTermList
               return $ Function id terms

matchVar :: Match Term
matchVar = do id <- matchVarId
              return $ Var id

----------------------------

data Parser = Parser [Token] [Formula]
    deriving (Show)

type ParseError  = String
type ParseResult = Either ParseError Formula

type ParseStep = (String, Parser)
type ParseStepResult = Either ParseError ParseStep

data Precedence = Prec {prec :: Int, leftAssoc :: Bool}

parseFormula :: String -> ParseResult
parseFormula str
    | isInfixOf "()" str = Left "Can not contain empty group ()"
    | otherwise = either (\err -> Left err) getResult $ parseStep (str, Parser [] [])

parseStep :: ParseStep -> ParseStepResult
parseStep step@("", Parser ops _)
    | length ops == 0   = Right step
    | otherwise         = do step' <- resolveOp step
                             parseStep step'
parseStep (str, parser) = do step' <- maybe 
                                      (Left $ "Error matching token from " ++ str)
                                      (\(token, str') -> parseToken token (str', parser)) $
                                      match matchToken str
                             parseStep step'

getResult :: ParseStep -> ParseResult
getResult (str, Parser ops forms)
    | (not . null) str || (not . null) ops || length forms /= 1 = Left "Invalid formula1"
    | otherwise = Right $ head forms

parseToken :: Token -> ParseStep -> ParseStepResult
parseToken (AtomicToken atom) step@(str, _) = case match matchToken str of
                                              Just (OpenToken, _) -> Left "Invalid formula"
                                              _ -> maybe (Left $ "Invalid atomic formula " ++ atom) 
                                                   (\(form, str') -> if null str' then pushFormula form step else Left $ "Invalid atomic formula " ++ atom) $ 
                                                   match matchAtomic atom
parseToken ClosedToken step@(str, _) = case match matchToken str of
                                       Just (AtomicToken _, _) -> Left "Invalid formula"
                                       Just (OpenToken, _)     -> Left "Invalid formula"
                                       _ -> resolveGroup step
parseToken op step = pushOp op step

pushFormula :: Formula -> ParseStep -> ParseStepResult
pushFormula formula (str, Parser ops forms) = Right (str, Parser ops $ formula:forms)

pushOp :: Token -> ParseStep -> ParseStepResult
pushOp OpenToken (str, Parser ops forms)        = Right (str, Parser (OpenToken:ops) forms)
pushOp push (str, Parser [] forms)              = Right (str, Parser [push] forms)
pushOp push (str, Parser (OpenToken:ops) forms) = Right (str, Parser (push:OpenToken:ops) forms)
pushOp push step@(str, Parser (op:ops) forms)
    | prec precOp > prec precPush || 
        (prec precOp == prec precPush && leftAssoc precOp) = do step' <- resolveOp step
                                                                pushOp push step'
    | otherwise = Right (str, Parser (push:op:ops) forms)
    where
        precOp   = precedence op
        precPush = precedence push

resolveGroup :: ParseStep -> ParseStepResult
resolveGroup step@(_, Parser ops _)
    | OpenToken `elem` ops = resolveGroup' step
    | otherwise            = Left "Unbalanced parantheses"
    where
        resolveGroup' :: ParseStep -> ParseStepResult
        resolveGroup' (str, Parser (OpenToken:ops) forms) = Right (str, Parser ops forms)
        resolveGroup' step = do step' <- resolveOp step
                                resolveGroup' step'

resolveOp :: ParseStep -> ParseStepResult
resolveOp (_,   Parser [] _) = Left "Invalid formula"
resolveOp (_,   Parser (OpenToken:_) _) = Left "Unbalanced parentheses"
resolveOp (str, Parser (op:ops) forms)
    | argCount op == 1 = maybe 
                         (Left "Invalid formula")
                         Right $ 
                         uncons forms >>= 
                            \(f, forms') -> Just $ (str, Parser ops $ (oneArgForm op f):forms')
    | argCount op == 2 = maybe 
                         (Left "Invalid formula")
                         Right $ 
                         uncons forms >>= 
                            \(r, forms') -> uncons forms' >>=
                            \(l, forms'') -> Just $ (str, Parser ops $ (twoArgForm op l r):forms'')
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

argCount :: Token -> Int
argCount NegToken      = 1
argCount AndToken      = 2
argCount OrToken       = 2
argCount ImpToken      = 2
argCount BicondToken   = 2
argCount (AllToken _)  = 1
argCount (SomeToken _) = 1
