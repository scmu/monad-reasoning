{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}


module Fusion3 where

import Prelude hiding (fail, or)
import Background

import Control.Monad (liftM, ap, liftM2)


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

newtype Cont r a = Cont { unCont :: forall x . (a -> r) -> r }

instance Functor (Cont r) where
  fmap = liftM

instance Applicative (Cont r) where
  pure = return
  (<*>) = ap

instance Monad (Cont r) where
  return x = Cont (\ k -> k x)
  Cont m >>= f = Cont (\ k -> m (\ a -> unCont (f a) k))

algCont :: Functor f => (f r -> r) -> (f (Cont r a) -> Cont r a)
algCont alg op = Cont (\ k -> alg (fmap (\ m -> unCont m k) op))

runCont :: (a -> r) -> Cont r a -> r
runCont g m = unCont m g

----------------------------------------------------------------

class Functor f => TermAlgebra r f | r -> f where
  con :: f r -> r

class TermGenerator r a | r -> a where
  var :: a -> r

instance Functor f => TermAlgebra (Free f a) f where
  con = Op

instance TermAlgebra r f => TermAlgebra (Cont r a) f where
  con = algCont con

instance TermGenerator (Cont r a) a where
  var = return

class (Monad m, forall a. TermAlgebra (m a) f) => TermMonad m f

instance (Monad m, forall a. TermAlgebra (m a) f) => TermMonad m f

instance TermAlgebra [a] NondetF where
  con Fail = []
  con (Or p q) = p ++ q

instance TermGenerator [a] a where
  var x = [x]

or :: TermAlgebra r NondetF => r -> r -> r
or p q = con (Or p q)

fail :: TermAlgebra r NondetF => r
fail = con Fail

example :: TermMonad m NondetF => m Int
example = or (return 1) (or fail (return 2))

result1a :: [Int]
result1a = fold var con example

result1b :: [Int]
result1b = runCont var example

-- Convert to state...

put' :: (TermMonad m (StateF s)) => s -> m ()
put' s = con (Put s (return ()))

get' :: (TermMonad m (StateF s)) => m s
get' = con (Get return)

newtype N2S n a = N2S { unN2S :: n a () }

data S n a = S { results :: [a], stack :: [N2S n a] }

popS :: TermMonad (n a) (StateF (S n a)) =>  N2S n a
popS = undefined

pushS :: TermMonad (n a) (StateF (S n a)) =>  N2S n a -> N2S n a -> N2S n a
pushS = undefined

appendS  :: TermMonad (n a) (StateF (S n a)) =>  a -> N2S n a -> N2S n a
appendS = undefined

instance TermMonad (n a) (StateF (S n a)) => TermAlgebra (N2S n a) NondetF where
  con Fail      =  popS
  con (Or p q)  =  pushS p q

instance TermMonad (n a) (StateF (S n a)) => TermGenerator (N2S n a) a where
  var x = appendS x popS
