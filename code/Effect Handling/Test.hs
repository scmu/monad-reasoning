{-# LANGUAGE
    DataKinds
  , TypeOperators
  , UndecidableInstances
  , FlexibleContexts
  , DeriveFunctor
  , LambdaCase
  #-}

module Test where

import Control.Monad

import Data.Match.Subset
import Data.Match.Membership
import Data.Match.Effects

modify :: (fs <: fs, Mem (State s) fs) =>
          (s -> s) -> Free fs ()
modify h = get >>= (put . h)

-- tst1 :: Free '[State Int, Nondet] Int
tst1, tst2 :: Free '[Nondet, State [Int]] ()
tst1 = modify ((1 :: Int) :) >>
       ((modify ((2 :: Int) :)) `mPlus`
        (modify ((3 :: Int) :)))

tst2 = (modify ((1 :: Int) :) >> modify ((2 :: Int) :)) `mPlus`
       (modify ((1 :: Int) :) >> modify ((3 :: Int) :))
      
tst3, tst4 :: Free '[Nondet, State [Int]] ()
tst3 = (modify ((1 :: Int):) `mPlus` modify ((2 :: Int):)) >>
       modify ((3 :: Int):)
tst4 = (modify ((1 :: Int):) >> modify ((3 :: Int):)) `mPlus`
       (modify ((2 :: Int):) >> modify ((3 :: Int):))


runLocal :: Free '[State s, Nondet] a -> s -> [(a, s)]
runLocal prog s = runPure . runNondet . runState prog $ s

runGlobal :: Free '[Nondet, State s] a -> s -> ([a], s)
runGlobal prog s = runPure $ runState (runNondet prog) s
