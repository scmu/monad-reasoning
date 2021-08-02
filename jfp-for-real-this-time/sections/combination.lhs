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
import LocalGlobal (trans, hLocal)
import NondetState (runNDf)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero)

\end{code}
%endif
\section{Combination}
\label{sec:combination}

%-------------------------------------------------------------------------------
\subsection{Modeling Multiple States with State}
\label{sec:state}

\begin{code}
states2state :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> Free (StateF (s1, s2) :+: f) a
states2state = fold gen (alg # fwd)
  where
    gen = return
    alg :: Functor f => StateF s1 (Free (StateF (s1, s2) :+: f) a) -> Free (StateF (s1, s2) :+: f) a
    alg (Get k) = Op $ Inl $ Get (\ (s1, s2) -> k s1)
    alg (Put s1' k) = do
      (s1, s2) <- Op $ Inl $ Get return
      Op $ Inl $ Put (s1', s2) k
    fwd :: Functor f => (StateF s2 :+: f) (Free (StateF (s1, s2) :+: f) a) -> Free (StateF (s1, s2) :+: f) a
    fwd (Inl (Get k)) = Op $ Inl $ Get (\ (s1, s2) -> k s2)
    fwd (Inl (Put s2' k)) = do
      (s1, s2) <- Op $ Inl $ Get return
      Op $ Inl $ Put (s1, s2') k
    fwd (Inr op) = Op (Inr op)
\end{code}

%----------------------------------------------------------------
\subsection{New Simulation of Nondeterminism}
\wenhao{I think we can replace the simulation in S3 with this new simulation.}

A new simulation of nondeterminism with state which is similar to the simulation of local state with global state.
The simulation function is |nd2state :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free (StateF (SS m a f) :+: f) ()|, which is also a syntax-level simulation similar to |trans| in S4.
We have the equation |hStateT . nd2state = hNDf|, which is similar to the equation |hGlobal . trans = hLocal|.
It uses the syntax (free monad) of state to do the simulation instead of using the state monad directly.
In this way, we can easily combine the result of two simulations.

\begin{code}
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
t' :: [Int]
t' = runVoid $ runNDf prog1
-- [1,2,3]
\end{code}

\subsection{Combine S3 and S4}

By now we have three simulations: |nd2state, local2global, states2state|.
We want to combine these three simulations to simulate the local state semantics only with the state monad.

\begin{code}
comm2 :: (Functor f1, Functor f2)
     => Free (f1 :+: f2 :+: f) a -> Free (f2 :+: f1 :+: f) a
comm2 (Var x) = Var x
comm2 (Op (Inl k)) = (Op . Inr . Inl) (fmap comm2 k)
comm2 (Op (Inr (Inl k))) = (Op . Inl) (fmap comm2 k)

local2global :: Functor f
             => Free (StateF s :+: NondetF :+: f) a
             -> Free (NondetF :+: StateF s :+: f) a
local2global = comm2 . trans

local2state :: (Functor f, MNondet m)
            => Free (StateF s :+: NondetF :+: f) a
            -- -> Free (StateF (SS m a (StateF s :+: f)) :+: StateF s :+: f) ()
            -> Free (StateF (SS m a (StateF s :+: f), s) :+: f) ()
local2state = states2state . nd2state . local2global

simulate2 :: (Functor f, MNondet m)
          => Free (StateF s :+: NondetF :+: f) a
          -> StateT (SS m a (StateF s :+: f), s) (Free f) ()
simulate2 = hStateT . local2state

-- extract2 :: (Functor f, MNondet m)
--          => StateT (SS m a (StateF s :+: f), s) (Free f) ()
--          -> (s -> Free f (m a))
extract2 :: (Functor f)
         => StateT (SS ([]) a (StateF s :+: f), s) (Free f) ()
         -> (s -> Free f [a])
extract2 x = \s -> fst . unSS . fst . snd <$> runStateT x (SS (mzero, []), s)

hLocal' :: Functor f => Free (StateF s :+: NondetF :+: f) a -> (s -> Free f [a])
hLocal' = extract2 . simulate2

\end{code}

We have |extract2 . hStateT . states2state . nd2state . local2global = hLocal|.
Some test program:

\begin{code}
or1 :: Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a
or1 x y = Op (Inr $ Inl $ Or x y)

fail1 :: Free (f :+: (NondetF :+: g)) a
fail1 = Op (Inr $ Inl Fail)

get1 :: Functor f => Free (StateF s :+: f) s
get1 = Op (Inl $ Get return)

put1 :: Functor f => s -> Free (StateF s :+: f) ()
put1 s = Op (Inl $ Put s (return ()))

prog :: Free (StateF Int :+: NondetF :+: Void) Int
prog =
  or1 (do put1 10; return 5)
      (do x <- get1; return x)

tt :: [Int]
tt = runVoid $ hLocal' prog 0
-- [5, 0]
tt' :: [Int]
tt' = runVoid $ hLocal prog 0
-- [5, 0]
\end{code}