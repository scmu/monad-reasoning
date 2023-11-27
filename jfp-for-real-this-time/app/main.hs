{-# Language FlexibleContexts #-}

module Main where

import Background
import LocalGlobal
import NondetState
import Combination
import MutableState
-- import qualified Stack2 as SC

import Control.DeepSeq (NFData(rnf))
import Data.Time
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

import qualified FusionLocal as Fl
import qualified FusionGlobal as Fg
import qualified FusionModify as Fm
import QueensMT (queensMT)
import Undo


-- queensStateLocal = hNil . flip local (0, []) . queens
--   where local = fmap (fmap (fmap fst) . runNDf) . runStateT . hState

funlist =
  [
  -- , (queensNaive, "queensNaive")
    (queensMT, "queensMT")
  , (queensLocal, "queensLocal")        -- local-state semantics, no simulation
  , (queensGlobal, "queensGlobal")      -- local2global
  , (queensLocalM, "queensLocalM")      --
  , (queensGlobalM, "queensGlobalM")    --
  , (queensState, "queensState")        -- local2global & nondet2state
  --  (queensStateR, "queensStateR")      -- queensR & nondet2state
  , (queensSim, "queensSim")            -- local2global & nondet2state & states2state
  -- , (queensSimR, "queensSimR")          -- queensR & nondet2state & states2state
  -- , (queensStackBFS, "queensStackBFS")  -- like a BFS using stack
  -- , (queensStack, "queensStack")        -- local2global & nondet2stack
  -- , (queensStackR, "queensStackR")      -- queensR & nondet2stack -- using stack2 now
  -- , (SC.queensStack, "queensStack2")        -- local2global & nondet2stack
  -- , (SC.queensStackR, "queensStack2R")      -- queensR & nondet2stack
  -- , (queensStateLocal, "queensStateLocal")      -- local-state semantics, nondet2state
  , (Fl.queensLocal,  "F.queensLocal")
  , (Fg.queensGlobal, "F.queensGlobal")
  , (Fm.queensGlobalM, "F.queensGlobalM")
  , (Fg.queensState,  "F.queensState")
  -- , (Fg.queensStackR, "F.queensStackR")
  ]

nlist = [10]

perform f n = do
  -- start <- getCurrentTime
  -- putStr $ show (length (f n)) ++ " "
  return $ length (f n)
  -- end   <- getCurrentTime
  -- return $ (diffUTCTime end start, len)

-- averPerform num f n = do
--   (t, len) <- multiplePerform num f n
--   return (t / num, len)
--   where
multiplePerform num f n = if num == 0
  then return 0
  else do
    len <- perform f n
    len' <- multiplePerform (num-1) f n
    return (len + len')


num = 5

testall n [] = return []
testall n ((f,name):xs) = do
  start <- getCurrentTime
  len <- multiplePerform num f n
  putStrLn $ show len ++ " "
  end <- getCurrentTime
  ts <- testall n xs
  return ((name, diffUTCTime end start / num):ts)

main = do
  ts <- testall 7 funlist
  putStrLn ""
  printList ts

printList [] = return ()
printList ((name, t):xs) = do putStrLn (name ++ "\t" ++ show t); printList xs


-- >>> Fg.queensStackR 4
-- [[3,1,4,2],[2,4,1,3]]


-- queensMT        0.0576136s
-- queensLocal     0.3550708s
-- queensModify    0.7152768s
-- queensStateR    0.3575462s
-- queensStackR    0.2978022s
-- F.queensLocal   0.0572374s
-- F.queensModify  0.14407s
-- F.queensStateR  0.1357452s
-- F.queensStackR  0.188084s


-- n = 10
-- queensMT        0.0588188s
-- F.queensLocal   0.0589982s
-- F.queensModify  0.1444444s
-- F.queensStateR  0.13299s
-- F.queensStackR  0.207929s

-- n = 11
-- queensMT        0.38883s
-- F.queensLocal   0.3763862s
-- F.queensModify  0.7751438s
-- F.queensStateR  0.7801738s
-- F.queensStackR  1.2131182s

-- n = 12
-- queensMT        2.1754152s
-- F.queensLocal   2.1582584s
-- F.queensModify  4.6744528s
-- F.queensStateR  8.632547s
-- F.queensStackR  11.2373052s

------------------------------------------------------------------------------
-- OLD:


-- queensLocal is the baseline
-- queensStackBFS is much faster than queensLocal
-- queensStateR is faster than queensLocal
-- queensSim is slower than queensState. I think it is because of the time used by the simulation function states2state ?
-- queensStack[R] is still a little slower than queensState
-- but queensStack[R]2 is even faster than queensLocal

{-
n=9
queensLocal     0.0723872s
queensGlobal    0.128872s
queensModify    0.139614s
queensState     0.0741924s
queensStateR    0.069604s
queensSim       0.1102444s
queensSimR      0.1113974s
queensStackBFS  0.0513904s
queensStack     0.097275s
queensStackR    0.0830048s
queensStack2    0.065528s
queensStackR2   0.0631138s
queensStateLocal        0.091166s

n=10
queensLocal     0.3929064s
queensGlobal    0.665637s
queensModify    0.6793106s
queensState     0.3999748s
queensStateR    0.3650656s
queensSim       0.5497036s
queensSimR      0.4962906s
queensStackBFS  0.268101s
queensStack     0.4378638s
queensStackR    0.4368402s
queensStack2    0.3780008s
queensStackR2   0.2992244s
queensStateLocal        0.5565514s

n=11

-}
