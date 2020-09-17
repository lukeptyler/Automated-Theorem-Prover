module Tableau where

import FOL.Base

-- Queue and Priority Queue --

data Queue a = Queue [a]
    deriving (Show)

initQueue :: [a] -> Queue a
initQueue ls = Queue ls

isEmptyQueue :: Queue a -> Bool
isEmptyQueue (Queue []) = True
isEmptyQueue _          = False

pushQueue :: a -> Queue a -> Queue a
pushQueue a (Queue ls) = Queue $ ls ++ [a]

popQueue :: Queue a -> Maybe (a, Queue a)
popQueue (Queue [])     = Nothing
popQueue (Queue (a:ls)) = Just (a, Queue ls)

data PriorityQueue a = PriorityQueue {classifiers :: [a -> Bool], queues :: [Queue a]}
instance Show a => Show (PriorityQueue a) where
    show (PriorityQueue _ queues) = show queues

initPriority :: [a -> Bool] -> PriorityQueue a
initPriority classifiers = PriorityQueue classifiers $ replicate (length classifiers + 1) $ Queue []

isEmptyPriority :: PriorityQueue a -> Bool
isEmptyPriority priority = all isEmptyQueue $ queues priority

pushPriority :: a -> PriorityQueue a -> PriorityQueue a
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
    deriving (Show)

initBranch :: [Formula] -> Branch
initBranch forms = addToBranchList forms $ Branch 1 [] [] $ initPriority [isDoubleNeg, isAlpha, isBeta, isDelta, isGamma]

isBranchClosed :: Branch -> Bool
isBranchClosed branch = undefined

-- Precond:  Branch that has already been checked for closure and failed
isBranchOpen :: Branch -> Bool
isBranchOpen branch = isEmptyPriority (forms branch)

addToBranch :: Formula -> Branch -> Branch
addToBranch f@(Atomic _ _)       branch = branch {posAtom = f:posAtom branch}
addToBranch (Neg f@(Atomic _ _)) branch = branch {negAtom = f:negAtom branch}
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
        (l, r) = extractBinary f

expandBeta :: Formula -> Branch -> (Bool, [Branch])
expandBeta (Binary Bicond      l r)  = (,) (any isAtomic [l, r]) . splitBranch [[l, r], [neg l, neg r]]
expandBeta (Neg (Binary Bicond l r)) = (,) (any isAtomic [l, r]) . splitBranch [[l, neg r], [neg l, r]]
expandBeta f = (,) (any isAtomic [l, r]) . splitBranch [[l], [r]]
    where
        (l, r) = extractBinary f

expandGamma :: Formula -> Branch -> (Bool, Branch)
expandGamma f branch = (,) (isAtomic f) . addToBranchList [substF sub f', f] $ branch {nextPar = nextPar branch + 1}
    where
        (id, f') = extractQuant f
        sub = singleton id $ Var $ "par" ++ show (nextPar branch)

--Step Branch :: Formula -> (Bool, Branch)
--  switch on type of formula

data Tableau = Tableau {maxSteps :: Int, open :: [Branch], closed :: [Branch], unfinished :: Queue Branch}
    deriving (Show)

-- Precond: A list of FOL formulas that have been normalized
-- branch for closure and sort
initTableau :: [Formula] -> Tableau
initTableau forms
    | isBranchClosed branch = blankTableau {closed = [branch]}
    | isBranchOpen   branch = blankTableau {open   = [branch]}
    | otherwise             = blankTableau {unfinished = initQueue [branch]}
    where 
        blankTableau = Tableau 100 [] [] $ initQueue []
        branch = initBranch forms

isTableauClosed :: Tableau -> Bool
isTableauClosed tableau = isEmptyQueue (unfinished tableau) && null (open tableau)

isTableauOpen :: Tableau -> Bool
isTableauOpen tableau = isEmptyQueue (unfinished tableau) && null (closed tableau)

--Prove [Formula] -> Formula -> Report
--      premises -> conclusion -> result
--  initTableau with premises and neg conclusion
--  if tableau is closed or open, report

--Run Tableau with initial tableau
--  step tableau
--  if tableau is closed, open, or out out steps, report
--  otherwise, step

--Tableau Step
--  pop off next branch
--  get next form from branch
--      if gamma, increase step count
--  step branch -> (added atomic, branch')
--  if added atomic -> if closed then add to closed, if open then add to open
--  otherwise, add to queue
