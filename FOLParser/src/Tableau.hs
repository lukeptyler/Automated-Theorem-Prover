module Tableau where

import FOL.Base

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

data Branch = Branch {posAtom :: [Formula], negAtom :: [Formula], forms :: PriorityQueue Formula}
    deriving (Show)

initBranch :: [Formula] -> Branch
initBranch forms = addToBranchList forms $ Branch [] [] $ initPriority [isDoubleNeg, isAlpha, isBeta, isDelta, isGamma]

addToBranch :: Formula -> Branch -> Branch
addToBranch f@(Atomic _ _)       branch = branch {posAtom = f:posAtom branch}
addToBranch (Neg f@(Atomic _ _)) branch = branch {negAtom = f:negAtom branch}
addToBranch f                    branch = branch {forms = pushPriority f $ forms branch}

addToBranchList :: [Formula] -> Branch -> Branch
addToBranchList forms branch = foldl (flip addToBranch) branch forms

nextOnBranch :: Branch -> Maybe (Formula, Branch)
nextOnBranch branch = do (f, forms') <- popPriority $ forms branch
                         return (f, branch {forms = forms'})

isClosed :: Branch -> Bool
isClosed branch = undefined

isOpen :: Branch -> Bool
isOpen branch = isEmptyPriority (forms branch) && not (isClosed branch)

data Tableau = Tableau {open :: [Branch], closed :: [Branch], unfinished :: Queue Branch}
    deriving (Show)

initTableau :: [Formula] -> Tableau
initTableau forms = Tableau [] [] $ initQueue $ [initBranch forms]