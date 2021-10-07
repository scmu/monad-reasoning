\section{Discussion}
\label{sec:discussion}

\birthe{Proposal: we could change this to ``Discussion'' instead of ``Conclusion'' and discuss the performance improvements of the different optimizations,
and general statistics of the simulations.}

This paper has shown the tradeoff for a programmer to implement effects using higher-level
effect semantics or lower-level effects.
In particular, we have studied the interaction between state and nondeterminism and
defined a simulation to model the two using a single state effect.

We have taken three steps:
(1) simulating local state with global state;
(2) simulating nondeterminism with state; and
(3) simulating multiple states with a single state and combining all simulations.

Using the n-queens puzzle as an example, we showed that transforming effects to lower-level
ones allows a greater degree of control over resources and gives the opportunity to
optimize in several ways, for example efficient backtracking or mutable state.
