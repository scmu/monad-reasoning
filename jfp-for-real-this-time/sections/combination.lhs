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

module Combination where

import Background
import LocalGlobal (local2global, hLocal)
import NondetState (runNDf, SS(..), nondet2state)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero)

\end{code}
%endif
\section{Combination}
\label{sec:combination}

Throughout the paper, we have shown several cases in which a high-level effect
can be simulated by means of a lower-level effect. 
This section combines these simulations to ultimately model the combination of 
nondeterminism and state with a single state effect. 

%-------------------------------------------------------------------------------
\subsection{Modeling Multiple States with State}
\label{sec:multiple-states}

For an effect that contains multiple states we can define two approaches to handle them.

First, we can make an effect functor with two state functors |StateF s1 :+: StateF s2|.
The |hStates| function handles these two functors to interpret them with the |StateT| monad.

\begin{code}
hStates :: (Functor f) => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT (s1, s2) (Free f) a
hStates = fold gen (alg1 # (alg2 # fwd))
  where
    gen :: (Functor f) => a -> StateT (s1, s2) (Free f) a
    gen = return
    alg1 :: (Functor f) => StateF s1 (StateT (s1, s2) (Free f) a) -> StateT (s1, s2) (Free f) a
    alg1 (Get k)      = StateT $ \sts -> runStateT (k $ fst sts) sts
    alg1 (Put s1' k)  = StateT $ \sts -> runStateT k (s1', snd sts)

    alg2 :: (Functor f) => StateF s2 (StateT (s1, s2) (Free f) a) -> StateT (s1, s2) (Free f) a
    alg2 (Get k)      = StateT $ \sts -> runStateT (k $ snd sts) sts
    alg2 (Put s2' k)  = StateT $ \sts -> runStateT k (fst sts, s2')

    fwd :: (Functor f) => f (StateT (s1, s2) (Free f) a) -> StateT (s1, s2) (Free f) a
    fwd op = StateT $ \sts -> Op $ fmap (\k -> runStateT k sts) op
\end{code}

Second, we can also have a single state effect functor that contains a tuple of two states |StateF (s1, s2)|.
The hStateTuple function handles this representation.

\begin{code}
hStateTuple :: (Functor f) => Free (StateF (s1, s2) :+: f) a -> StateT (s1, s2) (Free f) a
hStateTuple = fold gen (alg # fwd)
  where
    gen :: (Functor f) => a -> StateT (s1, s2) (Free f) a
    gen = return

    alg :: (Functor f) => StateF (s1, s2) (StateT (s1, s2) (Free f) a) -> StateT (s1, s2) (Free f) a
    alg (Get k) = StateT $ \sts -> runStateT (k sts) sts
    alg (Put s k) = StateT $ \sts -> runStateT k s

    fwd :: (Functor f) => f (StateT (s1, s2) (Free f) a) -> StateT (s1, s2) (Free f) a
    fwd op = StateT $ \sts -> Op $ fmap (\k -> runStateT k sts) op
\end{code}

In fact, it is possible to simulate the situation with two state effect handlers using
the single state effect functor with the tuple of states. 
Indeed, we can define a simulation function |states2state| as follows.

\begin{code}
states2state  :: (Functor f) 
              => Free (StateF s1 :+: StateF s2 :+: f) a 
              -> Free (StateF (s1, s2) :+: f) a
states2state  = fold gen (alg1 # (alg2 # fwd))
  where
    gen :: (Functor f) => a -> Free (StateF (s1, s2) :+: f) a
    gen = return 

    alg1  :: (Functor f) 
          => StateF s1 (Free (StateF (s1, s2) :+: f) a) 
          -> Free (StateF (s1, s2) :+: f) a
    alg1 (Get k)      = get' >>= \(s1,  _)   -> k s1
    alg1 (Put s1' k)  = get' >>= \(_,   s2)  -> put' (s1', s2) k

    alg2  :: (Functor f)
          => StateF s2 (Free (StateF (s1, s2) :+: f) a)
          -> Free (StateF (s1, s2) :+: f) a
    alg2 (Get k)      = get' >>= \(_,   s2)  -> k s2
    alg2 (Put s2' k)  = get' >>= \(s1,  _)   -> put' (s1, s2') k

    fwd  :: (Functor f) 
         => f (Free (StateF (s1, s2) :+: f) a)
         -> Free (StateF (s1, s2) :+: f) a
    fwd op            = Op (Inr op)
\end{code}
Here, |get'| and |put'| are smart constructors for getting the state and putting a new state.
\begin{code}
get'        :: Functor f => Free (StateF (s1, s2) :+: f) (s1, s2)
get'        = Op $ Inl $ Get return

put'        :: (s1, s2) -> Free (StateF (s1, s2) :+: f) a -> Free (StateF (s1, s2) :+: f) a
put' sts k  = Op $ Inl $ Put sts k
\end{code}

To prove that the two representations are equivalent and that the simulation is correct, 
we show that |hStates = hStateTuple . states2state|.
\todo{prove in appendices and refer to it.}

\subsection{Simulating Nondeterminism and State with Only State}

By now we have defined three simulations for encoding a high-level effect as a lower-level effect.
\begin{itemize}
  \item The function |nondet2state| simulates the high-level nondeterminism effect with the state effect 
  (Section \ref{sec:nondeterminism-state}).
  \item The function |local2global| simulates the high-level local state effect with global state 
  semantics (Section \ref{sec:local-global}).
  \item The function |states2state| simulates multiple state effects with a single state semantics 
  (Section \ref{sec:multiple-states}).
\end{itemize}

Combining these simulations, we can encode the semantics for nondeterminism and state with 
just the state monad. 
We get to the following simulation:
\begin{code}
simulate  :: (Functor f, MNondet m) 
          => Free (StateF s :+: NondetF :+: f) a 
          -> StateT (SS m a (StateF s :+: f), s) (Free f) ()
simulate  = hState . states2state . nondet2state . comm2 . local2global
\end{code}
Furthermore, we can define an |extract| function to extract the final result.
\begin{code}
extract :: (Functor f)
         => StateT (SS ([]) a (StateF s :+: f), s) (Free f) ()
         -> (s -> Free f [a])
extract x s = fst . unSS . fst . snd <$> runStateT x (SS (mzero, []), s)
\end{code}
%if False
\begin{code}
comm2 :: (Functor f1, Functor f2)
     => Free (f1 :+: f2 :+: f) a -> Free (f2 :+: f1 :+: f) a
comm2 (Var x) = Var x
comm2 (Op (Inl k)) = (Op . Inr . Inl) (fmap comm2 k)
comm2 (Op (Inr (Inl k))) = (Op . Inl) (fmap comm2 k)
\end{code}
%endif

The simulation happens in several steps (Figure \ref{fig:simulation}).
First, |local2global| models the local-state semantics with a global state.
Second, a commutativity function |comm2| changes the order of state and nondeterminism.
Next, |nondet2state| transforms the nondeterminism effect into a simulation with state.
Then, |states2state| combines the two state effects into a single state.
Finally, |hState| handles this state effect and translates it to the state transformer |StateT|.
Additionally, the |extract| function pulls out the result in a more readable form.
\begin{figure}[h]
% https://q.uiver.app/?q=WzAsNyxbMCwwLCJ8RnJlZSAoU3RhdGVGIHMgOis6IE5vbmRldEYgOis6IGYpIGF8Il0sWzAsMSwifEZyZWUgKFN0YXRlRiBzIDorOiBOb25kZXRGIDorOiBmKSBhfCJdLFswLDIsInxGcmVlIChOb25kZXRGIDorOiAoU3RhdGVGIHMgOis6IGYpKSBhfCJdLFswLDMsInxGcmVlIChTdGF0ZUYgKFNTIG0gYSAoU3RhdGVGIHMgOis6IGYpKSA6KzogU3RhdGVGIHMgOis6IGYpICgpfCJdLFswLDQsInxGcmVlIChTdGF0ZUYgKFNTIG0gYSAoU3RhdGVGIHMgOis6IGYpLCBzKSA6KzogZikgKCl8Il0sWzAsNSwifFN0YXRlVCAoU1MgbSBhIChTdGF0ZUYgcyA6KzogZiksIHMpIChGcmVlIGYpICgpfCJdLFswLDYsInxzIC0+IEZyZWUgZiBbYV18Il0sWzAsMSwifGxvY2FsMmdsb2JhbHwiXSxbMSwyLCJ8Y29tbTJ8Il0sWzIsMywifG5vbmRldDJzdGF0ZXwiXSxbMyw0LCJ8c3RhdGVzMnN0YXRlfCJdLFs0LDUsInxoU3RhdGVUfCJdLFs1LDYsInxleHRyYWN0fCIsMCx7ImNvbG91ciI6WzAsMCw1MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdHRlZCJ9fX0sWzAsMCw1MCwxXV0sWzAsNSwifHNpbXVsYXRlfCIsMCx7Im9mZnNldCI6LTUsImN1cnZlIjotNSwiY29sb3VyIjpbMCwwLDUwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fSxbMCwwLDUwLDFdXV0=
\[\begin{tikzcd}
  {|Free (StateF s :+: NondetF :+: f) a|} \\
  {|Free (StateF s :+: NondetF :+: f) a|} \\
  {|Free (NondetF :+: StateF s :+: f) a|} \\
  {|Free (StateF (SS m a (StateF s :+: f)) :+: StateF s :+: f) ()|} \\
  {|Free (StateF (SS m a (StateF s :+: f), s) :+: f) ()|} \\
  {|StateT (SS m a (StateF s :+: f), s) (Free f) ()|} \\
  {|s -> Free f [a]|}
  \arrow["{|local2global|}", from=1-1, to=2-1]
  \arrow["{|comm2|}", from=2-1, to=3-1]
  \arrow["{|nondet2state|}", from=3-1, to=4-1]
  \arrow["{|states2state|}", from=4-1, to=5-1]
  \arrow["{|hState|}", from=5-1, to=6-1]
  \arrow["{|extract|}", color={rgb,255:red,128;green,128;blue,128}, dotted, from=6-1, to=7-1]
  \arrow["{|simulate|}", shift left=30, color={rgb,255:red,128;green,128;blue,128}, curve={height=-70pt}, shorten <=-10pt, dotted, from=1-1, to=6-1]
\end{tikzcd}\]
\label{fig:simulation}
\caption{The simulation explained.}
\end{figure}

To show that this simulation is correct, we need to prove that |extract . simulate = hLocal|, 
or, in a more elaborate form:
< extract . hState . states2state . nondet2state . comm2 . local2global = hLocal


%if False
\begin{code}
or1 :: Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a
or1 x y = Op (Inr $ Inl $ Or x y)

fail1 :: Free (f :+: (NondetF :+: g)) a
fail1 = Op (Inr $ Inl Fail)

get1 :: Functor f => Free (StateF s :+: f) s
get1 = Op (Inl $ Get return)

put1 :: Functor f => s -> Free (StateF s :+: f) ()
put1 s = Op (Inl $ Put s (return ()))

prog :: Free (StateF Int :+: NondetF :+: NilF) Int
prog =
  or1 (do put1 10; return 5)
      (do x <- get1; return x)

tt :: [Int]
tt = hNil $ (extract . simulate) prog 0
-- [5, 0]
tt' :: [Int]
tt' = hNil $ hLocal prog 0
-- [5, 0]
\end{code}
%endif

\subsection{The Simulation for N-queens}

\todo{show how this works on an example (n-queens?)}