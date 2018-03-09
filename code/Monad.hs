module Monad where

import Control.Monad
import Control.Monad.State

-- Monadic operations

(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
(f <=< g) x = f =<< g x

-- (<$>) :: Monad m => (a -> b) -> m a -> m b
-- f <$> mx = (return . f) =<< mx

(<.>) :: Monad m => (b -> c) -> (a -> m b) -> (a -> m c)
f <.> g = ((return . f) =<<) . g

(<<) :: Monad m => m b -> m a -> m b
m1 << m2 = m2 >> m1

assert :: MonadPlus m => (a -> Bool) -> a -> m a
assert p x = guard (p x) >> return x

overwrite :: MonadState s m => s -> b -> m b
overwrite s' x  = return x << put s'

displaceBy :: MonadState b m => (b -> b) -> m b
displaceBy f = (\s -> return s << put (f s)) =<< get

guardM :: (MonadPlus m) => m Bool -> m ()
guardM test =
  test >>= \t -> if t then return () else mzero

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM p t f  = p >>= (\p' -> if p' then t else f)

unfoldM :: Monad m => (b -> Bool ) -> (b -> m (a,b)) -> b -> m [a]
unfoldM p f y  | p y        = return []
               | otherwise  = g =<< f y
  where g (x,y') = (x:) <$> unfoldM p f y'

hyloM :: Monad m =>  (c -> m b -> m b) -> m b ->
                     (a -> Bool) -> (a -> m (c ,a)) -> a -> m b
hyloM otimes m p f y
  | p y = m
  | otherwise = f y >>= \(x,z) ->
                x `otimes` hyloM otimes m p f z
  -- hyloM otimes m p f = foldr otimes m <=< unfoldM p f
