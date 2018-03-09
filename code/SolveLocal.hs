{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances, MultiParamTypeClasses #-}
module SolveLocal where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..))
import GHC.Base (Alternative(..))

import Monad

protect :: MonadState s m => m b -> m b
protect m = get >>= \ini -> m >>= \x -> put ini >> return x

{- unfoldM p f z >>= assert (all ok . scanlp oplus st) =
    solve p f ok oplus st z
-}

solve :: (MonadState s m, MonadPlus m) =>
  (b -> Bool) -> (b -> m (a, b)) -> (s -> Bool) ->
  (s -> a -> s) -> s -> b -> m [a]
solve p f ok oplus st z = protect (put st >> hyloM odot (return []) p f z)
  where x `odot` m = get >>= \st ->
                     let st' = (st `oplus` x)
                     in guard (ok st') >> put st' >> ((x:) <$> m)
