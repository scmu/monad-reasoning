{-# Language FlexibleContexts #-}

module Main where

import Background
import LocalGlobal
import NondetState
import Combination
import qualified Stack2 as SC

import Control.DeepSeq (NFData(rnf))
import Data.Time
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)


queensStateLocal = hNil . flip local (0, []) . queens
  where local = fmap (fmap (fmap fst) . runNDf) . runStateT . hState

funlist =
  [ (queensNaive, "queensNaive")
  , (queensMT, "queensMT")        
  , (queensLocal, "queensLocal")        -- local-state semantics, no simulation
  , (queensGlobal, "queensGlobal")      -- local2global
  , (queensModify, "queensModify")      -- queensR
  , (queensState, "queensState")        -- local2global & nondet2state
  , (queensStateR, "queensStateR")      -- queensR & nondet2state
  , (queensSim, "queensSim")            -- local2global & nondet2state & states2state
  , (queensSimR, "queensSimR")          -- queensR & nondet2state & states2state
  , (queensStackBFS, "queensStackBFS")  -- like a BFS using stack
  , (queensStack, "queensStack")        -- local2global & nondet2stack
  , (queensStackR, "queensStackR")      -- queensR & nondet2stack
  , (SC.queensStack, "queensStack2")        -- local2global & nondet2stack
  , (SC.queensStackR, "queensStackR2")      -- queensR & nondet2stack
  , (queensStateLocal, "queensStateLocal")      -- local-state semantics, nondet2state
  ]

nlist = [10]

perform f n = do
  start <- getCurrentTime
  -- let () = rnf (f n)
  -- putStrLn ("num: " ++ show (length (f n)))
  putStr $ show (length (f n)) ++ " "
  end   <- getCurrentTime
  return $ diffUTCTime end start

averPerform num f n = do
  t <- multiplePerform num f n
  return (t / num)
  where
    multiplePerform num f n = if num == 0
      then return 0
      else do
        t <- perform f n
        t' <- multiplePerform (num-1) f n
        return (t + t')

testall n [] = return []
testall n ((f,name):xs) = do
  t <- averPerform 5 f n
  ts <- testall n xs
  return ((name, t):ts)

main = do
  ts <- testall 10 funlist
  putStrLn ""
  printList ts

printList [] = return ()
printList ((name, t):xs) = do putStrLn (name ++ "\t" ++ show t); printList xs

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