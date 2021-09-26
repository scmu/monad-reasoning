{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, DeriveFunctor #-}

module FusionUtilities where

import Control.Applicative
import Control.Effect.State
import Control.Algebra

newtype StateC2 s m a = StateC2 (s -> m (s, a))
  deriving (Functor)

instance Monad m => Applicative (StateC2 s m) where
  pure a = StateC2 (\ s -> pure (s, a))
  {-# INLINE pure #-}

  StateC2 f <*> StateC2 a = StateC2 $ \ s -> do
    (s', f') <- f s
    (s'', a') <- a s'
    pure (s'', f' a')
  {-# INLINE (<*>) #-}

  m *> k = m >>= const k
  {-# INLINE (*>) #-}

instance (Alternative m, Monad m) => Alternative (StateC2 s m) where
  empty = StateC2 (const empty)
  {-# INLINE empty #-}

  StateC2 l <|> StateC2 r = StateC2 (\ s -> l s <|> r s)
  {-# INLINE (<|>) #-}

instance Monad m => Monad (StateC2 s m) where
  StateC2 m >>= f = StateC2 $ \ s -> do
    (s', a) <- m s
    runState2 s' (f a)
  {-# INLINE (>>=) #-}

runState2 :: s -> StateC2 s m a -> m (s, a)
runState2 s (StateC2 runStateC2) = runStateC2 s

-- instance Algebra sig m => Algebra (State s :+: sig) (StateC2 s m) where
--   alg hdl sig ctx = StateC2 $ \ s -> case sig of
--     L Get     -> pure (s, s <$ ctx)
--     L (Put s) -> pure (s, ctx)
--     R other   -> thread (uncurry runState2 ~<~ hdl) other (s, ctx)
--   {-# INLINE alg #-}