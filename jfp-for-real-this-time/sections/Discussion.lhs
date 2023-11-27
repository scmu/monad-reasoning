%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Discussion where

import Data.List
import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef
import Debug.Trace as DT

import Background
import Overview
import LocalGlobal (local2global, hLocal, hGlobal, comm2, queensLocal, queensGlobal)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero, get, put, modify, guard)
import Undo
\end{code}
%endif

\section{Discussion}
\label{sec:discussion}

We discuss extensions of our simulations and show benchmarks.

\subsection{Extensions with Mutable States}
\label{sec:mutable-states}

One main advantage of using low-level effects is to enable low-level
optimisations such as replacing immutable states with mutable ones.
%
In this section, we discuss three potential optimisations introduced
by mutable states.

\paragraph*{Undo with Mutable States}\
%
Although the translation |local2globalM| which simulates local-state
semantics with global-state semantics using state updates and
restoration in \Cref{sec:undo} avoids the cost of copying the whole
state of |local2global| in \Cref{sec:local2global}, it still needs to
obtain and modify the whole immutable state when updating and
restoring.
%
A natural optimisation is to replace the immutable states with mutable
states in order to implement more efficient operations for state
updates and restoration.

\wenhao{TODO: show some code?}

\begin{code}
queens' :: (MState (Int,[[Int]]) m, MNondet m) => Int -> m [Int]
queens' n = loop
  where
    loop :: (MState (Int,[[Int]]) m, MNondet m) => m [Int]
    loop = do  (c, rest) <- get
               case rest of
                 []     -> return []
                 (d:ds) -> do r   <- choose d
                              ds' <- prune ds r 1
                              put (c + 1, ds')
                              fmap (r:) loop

prune :: MNondet m => [[Int]] -> Int -> Int -> m [[Int]]
prune []     _ _ = pure []
prune (d:ds) r o = do let d' = d \\ [r, r+o, r-o]
                      guard (not (null d'))
                      fmap (d':) (prune ds r (o+1))

initial :: Int -> (Int, [[Int]])
initial n = (0, replicate n [1..n])

queensLocal' :: Int -> [[Int]]
queensLocal' n = hNil . flip hLocal (initial n) . queens' $ n

queensGlobal' :: Int -> [[Int]]
queensGlobal' n = hNil . flip hGlobal (initial n) . queens' $ n
\end{code}

\paragraph*{Mutable Stacks for Simulating Nondeterminism}\
%
With mutable states, we can also implement a more efficient version of
|nondet2state|, the simulation of nondeterminism with states, by
replacing the immutable stack with a mutable one.

\wenhao{TODO: show some code?}

\subsection{Trail Stacks}
\label{sec:trail-stack}
%
%Both of |local2global| and |local2globalM|, our previous simulations
%of local-state semantics and global-state semantics, rely on using
%high-level nondeterminism operations to store the previous states or
%modifications, respectively.
The simulation |local2globalM| still relies on using the high-level
nondeterminism operations to store the previous modifications (deltas)
to the state.
%
We can do this in a more low-level and efficient way by storing them
in a (global and mutable) trail stack following the Warren Abstract
Machine~\citep{AitKaci91}.
%
The trail stack contains elements of type |Either r ()|, where |r| is
the type of deltas to the states. The |Left x| means an update to the
state with the delta |x|, and the |Right ()| means a time stamp.
%
Whenever we update the state, we push the delta into the trail stack.
%
When we enter a nondeterministic branch, we push a time stamp.
%
When we leave the branch, we keep popping the trail stack and
restoring the updates it stored until we reach the time stamp.

\wenhao{TODO: show some code?}

\subsection{Benchmark}
\label{sec:benchmark}

\wenhao{TODO: rewrite}

This paper has shown the tradeoff between constructing programs using
higher-level or lower-level effects.
Although higher-level effects are more natural to express programs, it is still
desired to have access to the optimizations a lower-level effect offers.
We have shown that we can simulate those higher-level effects using lower-level
effects.
In particular, we have studied the interaction between state and nondeterminism
and shown that we can simulate local state using global state or even only state.

Typical optimizations we have included is smart backtracking using undo semantics,
or mutable state semantics.
Using equational reasoning techniques and fold fusion, we have proven all simulations
correct.

As a running example, we have shown our simulations and optimizations on the
n-queens example.
Table~\ref{tbl:benchmarks-haskell} shows some benchmarks
\footnote{The benchmarks are run using GHC 8.10.4 and clang 12.0.5 with the
|-O2| optimization option turned on, on a MacBook Pro with a 2.3 GHz Intel Core i5 processor and 16 GB RAM.}
for several implementation of
n-queens in Haskell using fusion \cite{Wu15}.
\wenhao{explain that Haskell doesn't work well with mutable states so the |queensStackR| is slower? Or we just don't show it?}
Better benchmarks are acquired using an implementation in C++ (Table~\ref{tbl:benchmarks-c++}),
which allows more fine-grained, low-level optimizations.
The best results are achieved using the C++ |queensStackR| implementation,
which have a 8--11\% runtime improvement over |queensLocal|.

\birthe{why are the functions in the two tables different?}
\wenhao{I didn't implement the |queensGlobal| and |queensState| in Haskell. And I don't know how to distinguish between |queensMT| and |queensLocal| in C++.}
\birthe{what's the unit? seconds?} \wenhao{Yes. It is worth noting that the C++ implementation is much slower than Haskell in gneneral.}
%include BenchmarkTable.lhs
