%if False
\begin{code}
\end{code}
%endif

\section{Conclusion}

\wenhao{TODO: update}

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
