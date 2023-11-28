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

\subsection{Mutable States}
\label{sec:mutable-states}

\wenhao{Do we want to show some code about extensions with mutable
states?}

One main advantage of using low-level effects is to make better use of
low-level features such as mutable states.
%
In this section, we discuss two potential optimisations enabled
by mutable states.

\paragraph*{Undo with Mutable States}\
%
Although the translation |local2globalM| which simulates local-state
semantics with global-state semantics using state updates and
restoration in \Cref{sec:undo} avoids the cost of copying the whole
state of the translation |local2global| in \Cref{sec:local2global}, it
still needs to retrieve and modify the whole immutable state when
updating and restoring.
%
A natural optimisation is to replace the immutable states with mutable
states so that we can implement more efficient versions of state
modification operations which only need to modify part of the mutable
states.
%
In addition to using mutable states, another option is to use
in-place update~\citep{LorenzenLS23} which also enables efficient
state updates and restoration.

%if False
\begin{code}
queens1 :: (MState (Int,[[Int]]) m, MNondet m) => Int -> m [Int]
queens1 n = loop
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

queens1Local :: Int -> [[Int]]
queens1Local n = hNil . flip hLocal (initial n) . queens1 $ n

queens1Global :: Int -> [[Int]]
queens1Global n = hNil . flip hGlobal (initial n) . queens1 $ n
\end{code}
%endif

\paragraph*{Mutable Stacks for Simulating Nondeterminism}\
%
The simulation of nondeterminism with states (|nondet2state|) in
\Cref{sec:combining-the-simulation-with-other-effects} implements
a stack containing the remaining branches with an immutable list.
%
With mutable states, we can also implement a more efficient version of
it by implementing a stack with a mutable array.

\subsection{Trail Stacks}
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
The idea is to use a trail stack to contain elements of type |Either r
()|, where |r| is the type of deltas to the states. The |Left x| means
an update to the state with the delta |x|, and the |Right ()| means a
time stamp.
%
Whenever we update the state, we push the delta into the trail stack.
%
When we enter a nondeterministic branch, we push a time stamp.
%
When we leave the branch, we keep popping the trail stack and
restoring the updates until we reach the latest time stamp.

\subsection{Benchmark}
\label{sec:benchmark}

As a running example, we have shown our simulations and optimisations
on the n-queens example. Table~\ref{tbl:benchmarks-haskell} shows
the benchmarks for all implementations of n-queens appeared in the
paper. \footnote{The benchmarks are run using GHC 8.10.7 with the
|-O2| optimization option turned on, on a MacBook Pro with a 2.3 GHz
Intel Core i5 processor and 16 GB RAM.}

% for several implementation of n-queens in Haskell using fusion
% \cite{Wu15}.  \wenhao{explain that Haskell doesn't work well with
% mutable states so the |queensStackR| is slower? Or we just don't show
% it?} Better benchmarks are acquired using an implementation in C++
% (Table~\ref{tbl:benchmarks-c++}), which allows more fine-grained,
% low-level optimizations.  The best results are achieved using the C++
% |queensStackR| implementation, which have a 8--11\% runtime
% improvement over |queensLocal|.

% \birthe{why are the functions in the two tables different?}
% \wenhao{I didn't implement the |queensGlobal| and |queensState| in Haskell. And I don't know how to distinguish between |queensMT| and |queensLocal| in C++.}
% \birthe{what's the unit? seconds?} \wenhao{Yes. It is worth noting that the C++ implementation is much slower than Haskell in gneneral.}

\begin{table}[]
\begin{tabular}{l||lllll}
Benchmark            & n=10  & n=11 & n=12  &  &  \\
\hline
|queensLocal|        & 0.328 & x.xx & x.xx  &  &  \\
|queensGlobal|       & 0.649 & x.xx & x.xx  &  &  \\
|queensState|        & 0.397 & x.xx & x.xx  &  &  \\
|queensSim|          & 0.693 & x.xx & x.xx  &  &  \\
|queensLocalM|       & 0.287 & x.xx & x.xx  &  &  \\
|queensGlobalM|      & 0.449 & x.xx & x.xx  &  &  \\
|queensStateM|       & 0.354 & x.xx & x.xx  &  &  \\
|queensStateMFused|  & 0.327 & x.xx & x.xx  &  &
\end{tabular}
\caption{Benchmarks of free monad implementations in the paper.}
\label{tbl:benchmarks-haskell}
\end{table}


% \begin{table}[]
% \begin{tabular}{l||lllll}
% Benchmark      & n=10  & n=11 & n=12  &  &  \\
% \hline
% |queensMT|     & 0.059 & 0.39 & 2.17  &  &  \\
% |queensLocal|  & 0.059 & 0.38 & 2.15  &  &  \\
% |queensModify| & 0.144 & 0.78 & 4.67  &  &  \\
% |queensStateR| & 0.133 & 0.78 & 8.63  &  &  \\
% |queensStackR| & 0.207 & 1.21 & 11.23 &  &
% \end{tabular}
% \caption{Results of free monad implementation (using fusion).}
% \label{tbl:benchmarks-haskell}
% \end{table}

% \begin{table}[]
% \begin{tabular}{l||lllll}
% Benchmark      & n=10 & n=11 & n=12  &  &  \\
% \hline
% |queensLocal|  & 1.27 & 7.87 & 55.00 &  &  \\
% |queensGlobal| & 1.19 & 7.61 & 52.60 &  &  \\
% |queensModify| & 1.14 & 7.26 & 51.02 &  &  \\
% |queensState|  & 1.33 & 8.20 & 55.29 &  &  \\
% |queensStateR| & 1.29 & 7.93 & 53.31 &  &  \\
% |queensStackR| & 1.14 & 7.22 & 48.92 &  &
% \end{tabular}
% \caption{Results of C++ implementation.}
% \label{tbl:benchmarks-c++}
% \end{table}
