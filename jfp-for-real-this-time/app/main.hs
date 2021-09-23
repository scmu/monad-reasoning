{-# Language FlexibleContexts #-}

module Main where

import Background
import LocalGlobal
import NondetState
import Combination

import Control.DeepSeq (NFData(rnf))
import Data.Time
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)


queensStateLocal = hNil . flip local (0, []) . queens
  where local = fmap (fmap (fmap fst) . runNDf) . runStateT . hState

funlist =
  [ (queensLocal, "queensLocal")        -- local-state semantics, no simulation
  , (queensGlobal, "queensGlobal")      -- local2global
  , (queensModify, "queensModify")      -- queensR
  , (queensState, "queensState")        -- local2global & nondet2state
  , (queensStateR, "queensStateR")      -- queensR & nondet2state
  , (queensSim, "queensSim")            -- local2global & nondet2state & states2state
  , (queensSimR, "queensSimR")          -- queensR & nondet2state & states2state
  , (queensStackBFS, "queensStackBFS")  -- like a BFS using stack
  , (queensStack, "queensStack")        -- local2global & nondet2stack
  , (queensStackR, "queensStackR")      -- queensR & nondet2stack
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

-- queensStackBFS is faster than queensLocal
-- Comparing queensGlobal with queensState, the optimization of nondet2state is obvious
-- queensSim is slower than queensState because of the time used by the simulation function ?
-- queensStack is still a little slower than queensState

{- 
n=9
queensLocal     0.082013s
queensGlobal    0.1443322s
queensModify    0.1519928s
queensState     0.0904284s
queensStateR    0.09149s
queensSim       0.1347476s
queensSimR      0.107251s
queensStackBFS  0.0534314s  ⭐️
queensStack     0.0961846s
queensStackR    0.0954376s
queensStateLocal        0.1029294s

n=10
queensLocal     0.3753108s
queensGlobal    0.668036s
queensModify    0.665608s
queensState     0.388065s
queensStateR    0.3521012s
queensSim       0.5711648s
queensSimR      0.5047398s
queensStackBFS  0.2361332s  ⭐️
queensStack     0.4336538s  slower than queensState
queensStackR    0.4083884s
queensStateLocal        0.5280488s

n=11

-}