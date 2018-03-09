{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances, MultiParamTypeClasses #-}
module SolveGlobal where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..), modify)
import GHC.Base (Alternative(..))

import Monad

side :: MonadPlus m => m a -> m b
side m = m >>= const mzero

putR :: (MonadState s m, MonadPlus m) => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0)

modifyR :: (MonadState s m, MonadPlus m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev = modify next `mplus` side (modify prev)

{- putR fin >> unfoldM p f z >>= assert (all ok . scanlp oplus st) =
    solve p f ok oplus ominus st fin z
-}

solveR :: (MonadState s m, MonadPlus m) =>
  (b -> Bool) -> (b -> m (a, b)) -> (s -> Bool) ->
  (s -> a -> s) -> (s -> a -> s) -> s -> s -> b -> m [a]
solveR p f ok oplus ominus st fin z =
   putR st >> hyloM ocirc (putR fin >> return []) p f z
  where x `ocirc` m = modifyR (`oplus` x) (`ominus` x) >>
                      (get >>= (guard . ok)) >>
                      ((x:) <$> m)
