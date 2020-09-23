module Tableau where

import FOL.Base
import Unification (unifyF)

import Data.List (nub, partition)
import Data.Maybe (mapMaybe)

-- Queue and Priority Queue --

data Queue a = Queue [a]
    deriving (Eq, Show)

initQueue :: [a] -> Queue a
initQueue ls = Queue ls

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

splitBranch :: [[Formula]] -> Branch -> [Branch]
splitBranch forms branch = map ((flip addToBranchList) branch) forms

expandDoubleNeg :: Formula -> Branch -> (Bool, Branch)
expandDoubleNeg (Neg (Neg f)) = (,) (isAtomic f) . addToBranch f

expandAlpha :: Formula -> Branch -> (Bool, Branch)
expandAlpha f = (,) (any isAtomic [l, r]) . addToBranchList [l, r]
    where
        (l, r) = extractAlpha f

expandBeta :: Formula -> Branch -> (Bool, [Branch])
expandBeta (Binary Bicond      l r)  = (,) (any isAtomic [l, r]) . splitBranch [[l, r], [neg l, neg r]]
expandBeta (Neg (Binary Bicond l r)) = (,) (any isAtomic [l, r]) . splitBranch [[l, neg r], [neg l, r]]
expandBeta f = (,) (any isAtomic [l, r]) . splitBranch [[l], [r]]
    where
        (l, r) = extractBeta f

expandGamma :: Formula -> Branch -> (Bool, Branch)
expandGamma f branch = (,) (isAtomic f') . addToBranchList [substF sub f', f] $ branch {nextPar = nextPar branch + 1}
    where
        (id, f') = extractQuant f
        sub = singleton id $ Var $ "par" ++ show (nextPar branch)

stepBranch :: Formula -> Branch -> (Bool, [Branch])
stepBranch f
    | isDoubleNeg f = ((\x -> [x]) <$>) . expandDoubleNeg f
    | isAlpha f     = ((\x -> [x]) <$>) . expandAlpha f
    | isBeta f      = expandBeta f
    | isGamma f     = ((\x -> [x]) <$>) . expandGamma f

data Tableau = Tableau {maxSteps :: Int, open :: [Branch], closed :: [Branch], unfinished :: Queue Branch}
    deriving (Show)

data Report = Valid
            | Counter [Formula]
            | ExceedSteps Tableau
    deriving (Show)

-- Precond: A list of FOL formulas that have been normalized
initTableau :: Int -> [Formula] -> Tableau
initTableau maxSteps forms
    | isBranchClosed branch = blankTableau {closed = [branch]}
    | isBranchOpen   branch = blankTableau {open   = [branch]}
    | otherwise             = blankTableau {unfinished = initQueue [branch]}
    where 
        blankTableau = Tableau maxSteps [] [] $ initQueue []
        branch = initBranch forms

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
                         let (addedAtomic, branches) = stepBranch f branch'
                         return (if addedAtomic
                                 then let (closedBranches, branches')  = partition isBranchClosed branches in
                                      let (openBranches,   branches'') = partition isBranchOpen branches' in
                                          tableau {maxSteps = newMaxSteps, 
                                                   open = open tableau ++ openBranches, 
                                                   closed = closed tableau ++ closedBranches, 
                                                   unfinished = pushQueueList branches'' queue
                                                  }
                                 else tableau {maxSteps = newMaxSteps,
                                               unfinished = pushQueueList branches queue
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
    | maxSteps tableau == 0   = return $ outOfSteps     tableau
    | otherwise               = do tableau' <- stepTableau tableau
                                   runTableau tableau'

counterExample :: Tableau -> Report
counterExample tableau = Counter $ posAtom openBranch ++ (map neg $ negAtom openBranch)
    where
        openBranch = head $ open tableau

closedTableau :: Tableau -> Report
closedTableau _ = Valid

outOfSteps :: Tableau -> Report
outOfSteps = ExceedSteps

defaultMaxSteps = 100

--Prove [Formula] -> Formula -> Report
--      premises -> conclusion -> result
--  normalize premizes and neg conclusion
--  initTableau with premises and neg conclusion
--  if tableau is closed or open, report
proveTheorem :: [Formula] -> Formula -> Maybe Report
proveTheorem = proveTheoremMaxSteps defaultMaxSteps

proveTheoremMaxSteps :: Int -> [Formula] -> Formula -> Maybe Report
proveTheoremMaxSteps maxSteps prem conc = runTableau $ (initTableau maxSteps) $ normalizeList $ prem ++ [neg conc]

proveTautology :: Formula -> Maybe Report
proveTautology = proveTautologyMaxSteps defaultMaxSteps

proveTautologyMaxSteps :: Int -> Formula -> Maybe Report
proveTautologyMaxSteps maxSteps taut = runTableau $ initTableau maxSteps [normalize $ neg taut]
