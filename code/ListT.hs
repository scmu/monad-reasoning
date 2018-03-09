{-# LANGUAGE ScopedTypeVariables, FlexibleInstances,
             MultiParamTypeClasses, UndecidableInstances #-}

module ListT where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Cont

import Control.Arrow

import GHC.Base (Alternative(..))

newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }

foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT c n (ListT m) = maybe n (\(x,l) -> c x (foldListT c n l)) =<< m

-- In ListT from Control.Monad this one is the data constructor ListT, so sadly, this code can't be a drop-in replacement.
liftList :: Monad m => [a] -> ListT m a
liftList [] = ListT $ return Nothing
liftList (x:xs) = ListT . return $ Just (x, liftList xs)

instance Functor m => Functor (ListT m) where
  fmap f (ListT m) = ListT $ fmap (fmap $ f *** fmap f) m where

instance Monad m => Applicative (ListT m) where
  pure = return
  mf <*> mx = mf >>= \f ->
              mx >>= \x -> return (f x)

instance (Monad m) => Monad (ListT m) where
  return x = ListT . return $ Just (x, mzero)
  m >>= f = ListT $
    foldListT (\x l -> runListT $ f x `mplus` ListT l) (return Nothing) m

instance MonadTrans ListT where
  lift = ListT . liftM (\x -> Just (x, mzero))

instance Monad m => MonadPlus (ListT m) where
  mzero = ListT $ return Nothing
  ListT m1 `mplus` ListT m2 = ListT $
    maybe m2 (return . Just . second (`mplus` ListT m2)) =<< m1

instance Monad m => Alternative (ListT m) where
  empty = mzero
  (<|>) = mplus

-- These things typecheck, but I haven't made sure what they do is sensible.
instance (MonadIO m, Functor m) => MonadIO (ListT m) where
  liftIO = lift . liftIO

instance (MonadReader s m, Functor m) => MonadReader s (ListT m) where
  ask     = lift ask
  local f = ListT . local f . runListT

instance (MonadState s m, Functor m) => MonadState s (ListT m) where
  get = lift get
  put = lift . put

instance MonadCont m => MonadCont (ListT m) where
  callCC f = ListT $
    callCC $ \c -> runListT . f $ \a ->
      ListT . c $ Just (a, ListT $ return Nothing)

instance (MonadError e m) => MonadError e (ListT m) where
  throwError = lift . throwError
  -- I can't really decide between those two possible implementations.
  -- The first one is more like the IO monad works, the second one catches
  -- all possible errors in the list.
--  ListT m `catchError` h = ListT $ m `catchError` \e -> runListT (h e)
  (m :: ListT m a) `catchError` h = deepCatch m where
    deepCatch :: ListT m a -> ListT m a
    deepCatch (ListT xs) = ListT $ liftM (fmap $ second deepCatch) xs
      `catchError` \e -> runListT (h e)
