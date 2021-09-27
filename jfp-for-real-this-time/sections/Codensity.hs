{-# LANGUAGE RankNTypes #-}

module Codensity where

import Control.Monad (liftM, ap, liftM2)

newtype Cod h a = Cod { unCod :: forall x . (a -> h x) -> h x }
instance Functor (Cod h) where
  fmap = liftM
instance Applicative (Cod h) where
  pure = return
  (<*>) = ap
instance Monad (Cod h) where
  return x = Cod (\ k -> k x)
  Cod m >>= f = Cod (\ k -> m (\ a -> unCod (f a) k))

algCod' :: Functor f => (forall x . f (h x) -> h x) -> (f (Cod h a) -> Cod h a)
algCod' alg op = Cod (\ k -> alg (fmap (\ m -> unCod m k) op))

runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g

newtype Cont r a = Cont { unCont :: (a -> r) -> r }

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

-- type Handler ctx m n = forall x . ctx (m x) -> n (ctx x)

-- alg :: (Monad m, Functor ctx)
--     => (forall x . ctx (n x) -> m (ctx x)) -> sig n a -> ctx () -> m (ctx a)
-- alg hdl sig ctx = undefined

-- algCod :: (Monad m, Functor ctx)
--        => ((forall x . ctx (n x) -> m (ctx x))     -> sig n a -> ctx () -> m (ctx a))
--        ->  (forall x . ctx (n x) -> Cont (m (ctx x))) -> sig n a -> ctx () -> Cont m (ctx a)
--    --  ->  (forall x . ctx (n x) -> (forall y . (ctx x -> m y) -> my))
--    --  ->  sig n a -> ctx () -> (forall y . (ctx a -> m y) -> m y)
-- algCod alg hdl sig ctx = Cod $ \ k -> let hdl' = flip (unCod . hdl) k in alg hdl' sig ctx

