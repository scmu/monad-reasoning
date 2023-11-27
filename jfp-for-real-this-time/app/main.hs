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
  , (queensLocalM, "queensLocalM")      -- local-state with undo
  , (queensGlobalM, "queensGlobalM")    -- local2globalM
  , (queensGlobalF, "queensGlobalF")    -- local2globalM fused
  , (queensState, "queensState")        -- local2global & nondet2state
  , (queensStateM, "queensStateM")      -- local2globalM & nondet2state
  , (queensStateF, "queensStateF")    -- local2globalM fused & nondet2state
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
  ts <- testall 11 funlist
  putStrLn ""
  printList ts

printList [] = return ()
printList ((name, t):xs) = do putStrLn (name ++ "\t" ++ show t); printList xs


-- n = 10
-- queensMT        0.0159434s
-- queensLocal     0.3363114s ★
-- queensGlobal    0.6448028s
-- queensLocalM    0.2914026s ★
-- queensGlobalM   0.51313s
-- queensGlobalF   0.4399704s
-- queensState     0.417572s
-- queensStateM    0.4051286s
-- queensStateF    0.3268356s ★
-- queensSim       0.661626s
-- F.queensLocal   0.0133942s
-- F.queensGlobal  0.0345506s
-- F.queensGlobalM 0.0669316s
-- F.queensState   0.0274124s

-- n = 11
-- queensMT        0.0710824s
-- queensLocal     1.6633336s ★
-- queensGlobal    3.5054034s
-- queensLocalM    1.53296s   ★
-- queensGlobalM   2.3953572s
-- queensGlobalF   2.1905802s
-- queensState     2.2615236s
-- queensStateM    1.9373316s
-- queensStateF    1.6740534s ★
-- queensSim       3.6168114s
-- F.queensLocal   0.064563s
-- F.queensGlobal  0.123203s
-- F.queensGlobalM 0.3171104s
-- F.queensState   0.212495s

