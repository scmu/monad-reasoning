{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module FusionModify where

import Prelude hiding (fail, or)
import Background hiding (queens)
import Overview
import LocalGlobal (side, local2global)
import Undo hiding (queensM)
-- import Combination (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop))
-- import Stack2 (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop, GetSt, PutSt)
--               , getInfoSt, putInfoSt)
-- import MutableState (Stack(Stack, results, size, stack), Index, emptyStack, pushStack, popStack, StackF(Push, Pop, GetSt, PutSt))
-- import TermAlg

import Control.Monad (liftM, ap, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef
import Data.Functor.Identity (Identity (Identity))

----------------------------------------------------------------

class Functor f => TermAlgebra h f | h -> f where
  var :: forall a . a -> h a
  con :: forall a . f (h a) -> (h a)

-- instance Functor f => TermAlgebra (Free f) f where
--   var = Var
--   con = Op

class (Monad m, TermAlgebra m f) => TermMonad m f
instance (Monad m, TermAlgebra m f) => TermMonad m f

------------------------------------------------------------------------------

newtype Cod h a = Cod { unCod :: forall x . (a -> h x) -> h x }

instance Functor (Cod h) where
  fmap = liftM

instance Applicative (Cod h) where
  pure = return
  (<*>) = ap

instance Monad (Cod h) where
  return x = Cod (\ k -> k x)
  Cod m >>= f = Cod (\ k -> m (\ a -> unCod (f a) k))

algCod :: Functor f => (forall x . f (h x) -> h x) -> (f (Cod h a) -> Cod h a)
algCod alg op = Cod (\ k -> alg (fmap (\ m -> unCod m k) op))

runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g

------------------------------------------------------------------------------
instance TermAlgebra Identity NilF where
  var = return
  con = undefined

run :: Identity a -> a
run (Identity a) = a

-- newtype Id m a = Id { runId :: m a }
-- instance Monad m => Functor (Id m) where
--   fmap = liftM
-- instance Monad m => Applicative (Id m) where
--   pure = return
--   (<*>) = ap
-- instance Monad m => Monad (Id m) where
--   return x = Id $ return x
--   Id x >>= f = Id $ x >>= runId . f

-- instance TermAlgebra m f => TermAlgebra (Id m) (NilF :+: f) where
--   var = return
--   con (Inr op) = Id . con $ fmap runId op

newtype MList m a = MList { unMList :: m [a] }

instance Monad m => Functor (MList m) where
  fmap f (MList m) = MList $ fmap (fmap f) m

genMList :: Monad m => a -> MList m a
genMList = \ x -> MList $ return [x]
-- instance Monad m => Applicative (MList m) where
--   pure = return
--   (<*>) = ap
-- instance Monad m => Monad (MList m) where
--   return x = MList $ return [x]
--   -- (MList m) >>= f = let t = join $ fmap (fmap join. sequence . fmap (unMList . f)) m in MList t
--   m >>= f = trace "no!" undefined
--   -- a little strange that you need to implement this

-- instance TermAlgebra [] (NondetF) where
--   var = return
--   con Fail = []
--   con (Or p q) = p ++ q

instance (TermMonad m f) => TermAlgebra (Cod (MList m)) (NondetF :+: f) where
  var = return
  con = algCod con'
    where
      con' (Inl Fail) = MList $ return []
      con' (Inl (Or (MList p) (MList q))) = MList $ do x <- p; y <- q; return (x ++ y)
      con' (Inr op) = MList . con . fmap unMList $ op

instance (TermMonad m f, Undo s r) => TermAlgebra (StateT s m) (ModifyF s r :+: f) where
  var = return
  con (Inl (MGet     k))     = StateT $ \s -> runStateT (k s) s
  con (Inl (MUpdate r  k))   = StateT $ \s -> runStateT k (s `plus` r)
  con (Inl (MRestore r  k))  = StateT $ \s -> runStateT k (s `minus` r)
  con (Inr op)               = StateT $ \s -> con $ fmap (\k -> runStateT k s) op


----------------------------------------------------------------

instance (Monad m, TermAlgebra m (NondetF :+: g), Functor g) => MNondet m where
  mzero = con (Inl Fail)
  mplus x y = con (Inl $ Or x y)

instance (Undo s r, Monad m, TermAlgebra m (f :+: ModifyF s r :+: g), Functor f, Functor g)
  => MModify s r m where
  mget = con (Inr . Inl $ MGet return)
  update r = con (Inr . Inl $ MUpdate r (return ()))
  restore r = con (Inr . Inl $ MRestore r (return ()))

modifyR :: (MModify s r m, MNondet m) => r -> m ()
modifyR r = update r `mplus` side (restore r)

queensM :: (MModify (Int, [Int]) Int m, MNondet m) => Int -> m [Int]
queensM n = loop where
  loop = do  (c, sol) <- mget
             if c >= n then return sol
             else do  r <- choose [1..n]
                      guard (safe r 1 sol)
                      modifyR r
                      loop

fhGlobalM :: Cod (MList (StateT s Identity)) a -> s -> Identity [a]
fhGlobalM = fmap (fmap fst) . runStateT . unMList . runCod genMList

queensGlobalM :: Int -> [[Int]]
queensGlobalM = run . flip fhGlobalM (0, []) . queensM
