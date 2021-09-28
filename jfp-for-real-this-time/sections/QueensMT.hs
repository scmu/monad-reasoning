{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module QueensMT where

import Background

import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

instance MNondet m => MState s (StateT s m) where
    get    = StateT $ \s -> return (s, s)
    put x  = StateT $ \s -> return ((), x)

instance MNondet m => MNondet (StateT s m) where
    mzero      = StateT $ \s -> mzero
    mplus x y  = StateT $ \s -> runStateT x s `mplus` runStateT y s

t :: StateT (Int, [Int]) [] [Int]
t = queens 4

queensMT :: Int -> [[Int]]
queensMT n = fmap fst $ runStateT (queens n) (0,[])