%if False
% Wenhao: Just to make my Haskell plugin work
\begin{code}
\end{code}
%endif

\section{Discussion}
\label{sec:discussion}

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
