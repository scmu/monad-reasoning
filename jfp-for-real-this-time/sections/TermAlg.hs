{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module TermAlg where

import Control.Monad (liftM, ap, liftM2, join)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.Functor.Identity (Identity (Identity, runIdentity))
import Debug.Trace
import Control.Monad.List

import Background
import Overview
import Undo

class Functor f => TermAlgebra h f | h -> f where
  var :: forall a . a -> h a
  con :: forall a . f (h a) -> h a

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
  con = undefined -- no con needed

run :: Identity a -> a
run = runIdentity

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
genMList x = MList $ return [x]
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

instance (TermMonad m f) => TermAlgebra (StateT s m) (StateF s :+: f) where
  var = return
  con (Inl (Get     k))  = StateT $ \s -> runStateT (k s) s
  con (Inl (Put s'  k))  = StateT $ \s -> runStateT k s'
  con (Inr op)           = StateT $ \s -> con $ fmap (\k -> runStateT k s) op


-- newtype StateT' s m a = StateT' { runStateT' :: s -> m (a, s) }

-- instance (Functor m) => Functor (StateT' s m) where
--     fmap f m = StateT' $ \ s ->
--         fmap (\ ~(a, s') -> (f a, s')) $ runStateT' m s
--     {-# INLINE fmap #-}

-- instance (Functor m, Monad m) => Applicative (StateT' s m) where
--     pure a = StateT' $ \ s -> return (a, s)
--     {-# INLINE pure #-}
--     StateT' mf <*> StateT' mx = StateT' $ \ s -> do
--         ~(f, s') <- mf s
--         ~(x, s'') <- mx s'
--         return (f x, s'')
--     {-# INLINE (<*>) #-}
--     m *> k = m >>= \_ -> k
--     {-# INLINE (*>) #-}

-- instance (Monad m) => Monad (StateT' s m) where
--     return a = StateT' $ \ s -> return (a, s)
--     {-# INLINE return #-}
--     m >>= k  = StateT' $ \ s -> do
--         ~(a, s') <- runStateT' m s
--         runStateT' (k a) s'
--     {-# INLINE (>>=) #-}

-- instance (TermMonad m f, Undo s r) => TermAlgebra (StateT' s m) (ModifyF s r :+: f) where
--   var = return
--   con (Inl (MGet     k))     = StateT' $ \s -> runStateT' (k s) s
--   con (Inl (MUpdate r  k))   = StateT' $ \s -> runStateT' k (s `plus` r)
--   con (Inl (MRestore r  k))  = StateT' $ \s -> runStateT' k (s `minus` r)
--   con (Inr op)               = StateT' $ \s -> con $ fmap (\k -> runStateT' k s) op
