{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}


module Fusion4 where

import Prelude hiding (fail, or)
import Background
import LocalGlobal (queensR, comm2)

import Control.Monad (liftM, ap, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

----------------------------------------------------------------

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

----------------------------------------------------------------

class Functor f => TermAlgebra h f | h -> f where
  var :: forall a . a -> h a
  con :: forall a . f (h a) -> (h a)

instance Functor f => TermAlgebra (Free f) f where
  var = Var
  con = Op

class (Monad m, TermAlgebra m f) => TermMonad m f
instance (Monad m, TermAlgebra m f) => TermMonad m f
-- instance Functor f => TermMonad (Free f) f

newtype MList m a = MList { unMList :: m [a] }

instance Monad m => Functor (MList m) where
  fmap = liftM
instance Monad m => Applicative (MList m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (MList m) where
  return x = MList $ return [x]
  mx >>= f = undefined

instance (TermMonad m f) => TermAlgebra (MList m) (NondetF :+: f) where
  var x = MList $ return [x]
  con (Inl Fail) = MList $ return []
  con (Inl (Or (MList p) (MList q))) = MList $ do x <- p; y <- q; return (x ++ y)
  con (Inr op) = MList . con . fmap unMList $ op

instance (TermMonad m f) => TermAlgebra (StateT s m) (StateF s :+: f) where
  var x = StateT $ \s -> return (x, s)
  con (Inl (Get     k))  = StateT $ \s -> runStateT (k s) s
  con (Inl (Put s'  k))  = StateT $ \s -> runStateT k s'
  con (Inr op)           = StateT $ \s -> con $ fmap (\k -> runStateT k s) op

-- instance TermAlgebra (StateT )

fhND :: (TermMonad m f, Functor f) => Free (NondetF :+: f) a -> MList m a
fhND = fold var con

fhState :: (TermMonad m f, Functor f) => Free (StateF s :+: f) a -> StateT s m a
fhState = fold var con

fhLocal :: (TermMonad m f, Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> m [a]
fhLocal = fmap (fmap (fmap fst) . unMList) . runStateT . fhState

fhGlobal :: (TermMonad m f, Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> m [a]
fhGlobal = fmap (fmap fst) . runStateT . unMList . fhND . comm2

queensLocal :: Int -> [[Int]]
queensLocal = hNil . flip fhLocal (0, []) . queens

queensModify :: Int -> [[Int]]
queensModify = hNil . flip fhGlobal (0, []) . queensR
