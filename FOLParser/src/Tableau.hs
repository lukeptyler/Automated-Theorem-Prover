module Tableau where

import FOL.Base
import Unification (unifyF, unifyList)

import Data.List (groupBy, sortBy, mapAccumL, nub, partition, intercalate, nubBy)
import Data.Maybe (mapMaybe, fromJust)

-- Queue and Priority Queue --

data Queue a = Queue [a]
    deriving (Eq, Show)

initQueue :: [a] -> Queue a
initQueue ls = Queue ls

toListQueue :: Queue a -> [a]
toListQueue (Queue ls) = ls

isEmptyQueue :: Queue a -> Bool
isEmptyQueue (Queue []) = True
isEmptyQueue _          = False

pushQueue :: (Eq a) => a -> Queue a -> Queue a
pushQueue a (Queue ls) = Queue $ nub $ ls ++ [a]

pushQueueList :: (Eq a) => [a] -> Queue a -> Queue a
pushQueueList list (Queue ls) = Queue $ ls ++ list

popQueue :: Queue a -> Maybe (a, Queue a)
popQueue (Queue [])     = Nothing
popQueue (Queue (a:ls)) = Just (a, Queue ls)

data PriorityQueue a = PriorityQueue {classifiers :: [a -> Bool], queues :: [Queue a]}
instance Eq a => Eq (PriorityQueue a) where
    p1 == p2 = queues p1 == queues p2
instance Show a => Show (PriorityQueue a) where
    show (PriorityQueue _ queues) = "PriorityQueue " ++ show (concatMap (\(Queue ls) -> ls) queues)

initPriority :: [a -> Bool] -> PriorityQueue a
initPriority classifiers = PriorityQueue classifiers $ replicate (length classifiers + 1) $ Queue []

toListPriority :: PriorityQueue a -> [a]
toListPriority priority = concatMap toListQueue $ queues priority

isEmptyPriority :: PriorityQueue a -> Bool
isEmptyPriority priority = all isEmptyQueue $ queues priority

pushPriority :: (Eq a) => a -> PriorityQueue a -> PriorityQueue a
pushPriority a priority = priority {queues = front ++ [pushQueue a $ head back] ++ tail back}
    where
        index = length $ takeWhile (\f -> not $ f a) $ classifiers priority
        (front, back) = splitAt index $ queues priority

popPriority :: PriorityQueue a -> Maybe (a, PriorityQueue a)
popPriority priority = do (a, queues') <- popList $ queues priority
                          return $ (a, priority {queues = queues'})
    where
        popList :: [Queue a] -> Maybe (a, [Queue a])
        popList [] = Nothing
        popList (Queue []:queues) = do (a, queues') <- popList queues
                                       return $ (a, Queue [] : queues')
        popList (queue:queues) = do (a, queue') <- popQueue queue
                                    return $ (a, queue':queues)

-- Tableau --

data Branch = Branch {nextPar :: Int, posAtom :: [Formula], negAtom :: [Formula], forms :: PriorityQueue Formula}
    deriving (Eq)
instance Show Branch where
    show branch = "Branch (" ++ show (nextPar branch) ++ ", " ++ show (posAtom branch) ++ ", " ++ show (negAtom branch) ++ ", " ++ show (forms branch) ++ ")"

initBranch :: [Formula] -> Branch
initBranch forms = addToBranchList forms $ Branch 1 [] [] $ initPriority [isDoubleNeg, isAlpha, isBeta, isDelta, isGamma]

elemsOnBranch :: Branch -> [Formula]
elemsOnBranch branch = posAtom branch ++ (map neg $ negAtom branch) ++ toListPriority (forms branch)

isBranchClosed :: Branch -> Bool
isBranchClosed branch = not $ null $ mapMaybe (uncurry unifyF) $ pairAtomics (posAtom branch) (negAtom branch)
    where
        pairAtomics :: [Formula] -> [Formula] -> [(Formula, Formula)]
        pairAtomics [] _ = []
        pairAtomics (f@(Atomic p1 _):fs1) fs2 = (map ((,) f) $ filter (\(Atomic p2 _) -> p1 == p2) fs2) ++ pairAtomics fs1 fs2

-- Precond:  Branch that has already been checked for closure and failed
isBranchOpen :: Branch -> Bool
isBranchOpen branch = isEmptyPriority (forms branch)

addToBranch :: Formula -> Branch -> Branch
addToBranch f@(Atomic _ _)       branch = branch {posAtom = nub $ f:posAtom branch}
addToBranch (Neg f@(Atomic _ _)) branch = branch {negAtom = nub $ f:negAtom branch}
addToBranch f                    branch = branch {forms = pushPriority f $ forms branch}

addToBranchList :: [Formula] -> Branch -> Branch
addToBranchList forms branch = foldl (flip addToBranch) branch forms

nextOnBranch :: Branch -> Maybe (Formula, Branch)
nextOnBranch branch = do (f, forms') <- popPriority $ forms branch
                         return (f, branch {forms = forms'})

splitBranch :: [Formula] -> [Formula] -> Branch -> Expansion
splitBranch left right branch = Split left right $ map ((flip addToBranchList) branch) [left, right]

data Expansion = Expand {addedForms :: [Formula], newBranch :: Branch}
               | Split  {addedLeft :: [Formula], addedRight :: [Formula], newBranches :: [Branch]}

expansionForms :: Expansion -> [Formula]
expansionForms (Expand fs _)     = fs
expansionForms (Split lfs rfs _) = lfs ++ rfs

expansionBranches :: Expansion -> [Branch]
expansionBranches (Expand _ b)   = [b]
expansionBranches (Split _ _ bs) = bs

expandDoubleNeg :: Formula -> Branch -> Expansion
expandDoubleNeg (Neg (Neg f)) = Expand [f] . addToBranch f

expandAlpha :: Formula -> Branch -> Expansion
expandAlpha f = Expand [l, r] . addToBranchList [l, r]
    where
        (l, r) = extractAlpha f

expandBeta :: Formula -> Branch -> Expansion
expandBeta (Binary Bicond      l r)  = splitBranch [l, r] [neg l, neg r]
expandBeta (Neg (Binary Bicond l r)) = splitBranch [l, neg r] [neg l, r]
expandBeta f = splitBranch [l] [r]
    where
        (l, r) = extractBeta f

expandGamma :: Formula -> Branch -> Expansion
expandGamma f branch = Expand [f''] . addToBranchList [f'', f] $ branch {nextPar = nextPar branch + 1}
    where
        (id, f') = extractQuant f
        f'' = substF (singleton id $ Var $ "par" ++ show (nextPar branch)) f'

stepBranch :: Formula -> Branch -> Expansion
stepBranch f
    | isDoubleNeg f = expandDoubleNeg f
    | isAlpha f     = expandAlpha f
    | isBeta f      = expandBeta f
    | isGamma f     = expandGamma f

data Tableau = Tableau {initialSteps :: Int, maxSteps :: Int, open :: [Branch], closed :: [Branch], unfinished :: Queue Branch, record :: Record}
    deriving (Show)

data Report = Valid Record
            | Counter [Formula] Record
            | ExceedSteps Int [Formula]
    deriving (Show)

data Theorem = Theorem {props :: [Formula], conc :: Formula}

instance Show Theorem where
    show theorem = intercalate "\n" (zipWith (++) (map (\i -> show i ++ ":" ++ replicate (indexLen - 1 - length (show i)) ' ') [1..length (props theorem)]) 
                                                  (map show $ props theorem)) ++ 
                   "\n" ++ replicate (maxFormLen + indexLen) '-' ++ 
                   "\n" ++ replicate indexLen ' ' ++ show (conc theorem)
        where
            maxFormLen = (maximum $ map (length . show) $ conc theorem : props theorem)
            indexLen   = 2 + length (show $ length (props theorem) + 1)

emptyTheorem = Theorem [] $ Atomic "" []

-- Precond: A list of FOL formulas that have been normalized
initTableau :: Int -> [Formula] -> Tableau
initTableau maxSteps forms
    | isBranchClosed branch = blankTableau {closed = [branch]}
    | isBranchOpen   branch = blankTableau {open   = [branch]}
    | otherwise             = blankTableau {unfinished = initQueue [branch]}
    where 
        branch = initBranch forms
        blankTableau = Tableau maxSteps maxSteps [] [] (initQueue []) (Record branch (elemsOnBranch branch) [])

isTableauClosed :: Tableau -> Bool
isTableauClosed tableau = not (isTableauOpen tableau) && isEmptyQueue (unfinished tableau)

isTableauOpen :: Tableau -> Bool
isTableauOpen tableau = not $ null $ open tableau

--Tableau Step
--  pop off next branch
--  get next form from branch
--      if gamma, increase step count
--  step branch -> (added atomic, branch')
--  if added atomic -> if closed then add to closed, if open then add to open
--  otherwise, add to queue
stepTableau :: Tableau -> Maybe Tableau
stepTableau tableau = do (branch, queue) <- popQueue $ unfinished tableau
                         (f, branch') <- nextOnBranch branch
                         let newMaxSteps = maxSteps tableau - (if isGamma f then 1 else 0)
                         let expansion = stepBranch f branch'
                         return (if any isAtomic $ expansionForms expansion
                                 then let (closedBranches, branches')  = partition isBranchClosed $ expansionBranches expansion in
                                      let (openBranches,   branches'') = partition isBranchOpen branches' in
                                      let newRecord = addExpansionToRecord branch expansion $ record tableau in
                                      tableau {maxSteps = newMaxSteps, 
                                               open = open tableau ++ openBranches, 
                                               closed = closed tableau ++ closedBranches, 
                                               unfinished = pushQueueList branches'' queue,
                                               record = newRecord
                                              }
                                 else let newRecord = addExpansionToRecord branch expansion $ record tableau in
                                      tableau {maxSteps = newMaxSteps,
                                               unfinished = pushQueueList (expansionBranches expansion) queue,
                                               record = newRecord
                                              }
                                )

--Run Tableau with initial tableau
--  step tableau
--  if tableau is closed, open, or out out steps, report
--  otherwise, step
runTableau :: Tableau -> Maybe Report
runTableau tableau
    | isTableauOpen   tableau = return $ counterExample tableau
    | isTableauClosed tableau = return $ closedTableau  tableau
    | maxSteps tableau < 0    = return $ outOfSteps     tableau
    | otherwise               = do tableau' <- stepTableau tableau
                                   runTableau tableau'

closedTableau :: Tableau -> Report
closedTableau tableau = Valid $ record tableau

counterExample :: Tableau -> Report
counterExample tableau = Counter (posAtom openBranch ++ (map neg $ negAtom openBranch)) $ record tableau
    where
        openBranch = head $ open tableau

outOfSteps :: Tableau -> Report
outOfSteps tableau = ExceedSteps (initialSteps tableau) $ outOfStepsCounterExample forms
    where
        branch = fst $ fromJust $ popQueue $ unfinished tableau
        forms = posAtom branch ++ map neg (negAtom branch)

outOfStepsCounterExample :: [Formula] -> [Formula]
outOfStepsCounterExample ls = snd $ mapAccumL compress (Just mempty) fullList
    where
        eqAtomics :: Formula -> Formula -> Ordering
        eqAtomics (Atomic p _) (Atomic q _) = compare p q
        eqAtomics (Neg (Atomic _ _)) (Atomic _ _) = GT
        eqAtomics (Atomic _ _) (Neg (Atomic _ _)) = LT
        eqAtomics (Neg f) (Neg g) = eqAtomics f g

        fullList :: [[Formula]]
        fullList = groupBy (\p -> \q -> eqAtomics p q == EQ) $ sortBy eqAtomics ls

        compress :: Maybe Subst -> [Formula] -> (Maybe Subst, Formula)
        compress Nothing _ = (Nothing, Atomic "" [])
        compress (Just s) ls = (s', maybe (Atomic "" []) (\sub -> substF sub $ head ls) $ s')
            where
                s' = unifyList s (head ls) (tail ls)

defaultMaxSteps = 100

--Prove [Formula] -> Formula -> Report
--      premises -> conclusion -> result
--  normalize premizes and neg conclusion
--  initTableau with premises and neg conclusion
--  if tableau is closed or open, report
proveTheorem :: Theorem -> Maybe Report
proveTheorem = proveTheoremMaxSteps defaultMaxSteps

proveTheoremMaxSteps :: Int -> Theorem -> Maybe Report
proveTheoremMaxSteps maxSteps (Theorem prem conc) = runTableau $ (initTableau maxSteps) $ normalizeList $ prem ++ [neg conc]

proveTautology :: Formula -> Maybe Report
proveTautology = proveTautologyMaxSteps defaultMaxSteps

proveTautologyMaxSteps :: Int -> Formula -> Maybe Report
proveTautologyMaxSteps maxSteps taut = runTableau $ initTableau maxSteps [normalize $ neg taut]

-- Tableau Record --

data Record = Record {recId :: Branch, recForms :: [Formula], recChildren :: [Record]}
instance Show Record where
    show = printRecord

printRecord :: Record -> String
printRecord record = unlines $ printRecord' "" (True,record)
    where
        printRecord' :: String -> (Bool,Record) -> [String]
        printRecord' indent (last,record) = (indent ++ nextStart ++ (intercalate ", " $ map show (recForms record))) : (concatMap (printRecord' $ indent ++ nextIndent) $ zip (reverse $ True:replicate ((length $ recChildren record) - 1) False) $ recChildren record)
            where
                nextStart  = if last then "└─ " else "├─ "
                nextIndent = if last then "   " else "│  "
        printForms :: String -> [(String,Formula)] -> [String]
        printForms _ [] = []
        printForms indent ((start,form):rest) = (indent ++ start ++ show form) : printForms indent rest

addExpansionToRecord :: Branch -> Expansion -> Record -> Record
addExpansionToRecord parentBranch expansion record
    | null (recChildren record) && parentBranch == recId record = record {recChildren = createChildren expansion}
    | otherwise = record {recChildren = map (addExpansionToRecord parentBranch expansion) $ recChildren record}
    where
        createChildren :: Expansion -> [Record]
        createChildren (Expand fs branch) = [Record branch fs []]
        createChildren (Split lfs rfs branches) = [Record (head branches) lfs [], Record (last branches) rfs []]
