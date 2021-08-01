%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

import Background
import Control.Monad.State.Lazy hiding (fail, mplus, mzero)

\end{code}
%endif
\section{Combination}
\label{sec:combination}

%-------------------------------------------------------------------------------
\subsection{Modeling Multiple States with State}
\label{sec:state}


%----------------------------------------------------------------
\subsection{New Simulation of Nondeterminism}
\wenhao{I think we can replace the simulation in S3 with this new simulation.}

A new simulation of nondeterminism with state which is similar to the simulation of local state with global state.
The simulation function is |nd2state :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free (StateF (SS m a f) :+: f) ()|, which is also a syntax-level simulation similar to |trans| in S4.
We have the equation |hStateT . nd2state = hNDf|, which is similar to the equation |hGlobal . trans = hLocal|.
It uses the syntax (free monad) of state to do the simulation instead of using the state monad directly.
In this way, we can easily combine the result of two simulations.

\begin{code}
-- StateT s ~> Free (State s)
newtype SS m a f = SS { unSS :: (m a, [Free (StateF (SS m a f) :+: f) ()]) }

get' :: Functor f => Free (StateF s :+: f) s
get' = Op (Inl $ Get return)

put' :: Functor f => s -> Free (StateF s :+: f) ()
put' s = Op (Inl $ Put s (return ()))

popSS :: Functor f => Free (StateF (SS m a f) :+: f) ()
popSS = do
  SS (xs, stack) <- get'
  case stack of
    [] -> return ()
    op : ps -> do
      put' (SS (xs, ps)); op
pushSS :: Functor f
       => Free (StateF (SS m a f) :+: f) ()
       -> Free (StateF (SS m a f) :+: f) ()
       -> Free (StateF (SS m a f) :+: f) ()
pushSS q p = do
  SS (xs, stack) <- get'
  put' (SS (xs, q : stack))
  p
appendSS :: (Functor f, MNondet m)
         => a
         -> Free (StateF (SS m a f) :+: f) ()
         -> Free (StateF (SS m a f) :+: f) ()
appendSS x p = do
 SS (xs, stack) <- get'
 put' (SS (xs `mplus` return x, stack))
 p

nd2state :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free (StateF (SS m a f) :+: f) ()
nd2state = fold gen (alg # fwd)
  where
    gen x = appendSS x popSS
    alg Fail = popSS
    alg (Or p q) = pushSS q p
    fwd :: Functor f => f (Free (StateF (SS m a f) :+: f) ()) -> Free (StateF (SS m a f) :+: f) ()
    fwd y = Op (Inr y)

hStateT :: Functor f => Free (StateF s :+: f) a -> StateT s (Free f) a -- (s -> Free f (a, s))
hStateT = fold gen (alg # fwd)
  where
    gen x = StateT $ \s -> return (x, s)
    alg :: StateF s (StateT s (Free f) a) -> StateT s (Free f) a
    alg (Get k) = StateT $ \s -> runStateT (k s) s
    alg (Put s' k) = StateT $ \s -> runStateT k s'
    fwd :: Functor f => f (StateT s (Free f) a) -> StateT s (Free f) a
    fwd op = StateT $ \s -> Op $ fmap (\k -> runStateT k s) op

extract'' :: (Functor f, MNondet m) => StateT (SS m a f) (Free f) () -> Free f (m a)
extract'' x = fst . unSS . snd <$> runStateT x (SS (mzero, []))

runndf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
runndf = extract'' . hStateT . nd2state
\end{code}

We have |runndf = runNDf = hNDf|.
Some test program:

\begin{code}
or' :: Functor f => Free (NondetF :+: f) a -> Free (NondetF :+: f) a -> Free (NondetF :+: f) a
or' x y = Op (Inl $ Or x y)

fail' :: Functor f => Free (NondetF :+: f) a
fail' = Op (Inl Fail)

prog1 :: Free (NondetF :+: Void) Int
prog1 = or' (or' (return 1) (return 2)) (or' fail' (return 3))

t :: [Int]
t = runVoid $ runndf prog1
-- [1,2,3]
\end{code}