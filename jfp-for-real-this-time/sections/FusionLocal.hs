{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module FusionLocal where

import Prelude hiding (fail, or)
import Background
import Overview
import TermAlg

import Control.Monad (liftM, ap, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

----------------------------------------------------------------

instance (Monad m, TermAlgebra m (f :+: NondetF :+: g), Functor f, Functor g) => MNondet m where
  mzero = con (Inr . Inl $ Fail)
  mplus x y = con (Inr . Inl $ Or x y)

instance (Monad m, TermAlgebra m (StateF s :+: f), Functor f) => MState s m where
  get = con (Inl $ Get return)
  put x = con (Inl $ Put x (return ()))

fhLocal :: Monad m => StateT s (Cod (MList m)) a -> s -> m [a]
fhLocal = fmap (fmap (fmap fst) . unMList). fmap (runCod genMList) . runStateT


queensLocal :: Int -> [[Int]]
queensLocal = run . flip fhLocal (0, []) . queens
