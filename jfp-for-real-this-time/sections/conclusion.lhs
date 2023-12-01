%if False
\begin{code}
\end{code}
%endif

\section{Conclusion and Future Work}
\label{sec:conclusion}

% The old conlusion:
% This paper has shown the tradeoff between constructing programs using
% higher-level or lower-level effects.
% Although higher-level effects are more natural to express programs, it is still
% desired to have access to the optimisations a lower-level effect offers.
% We have shown that we can simulate those higher-level effects using lower-level
% effects.
% In particular, we have studied the interaction between state and nondeterminism
% and shown that we can simulate local state using global state or even only state.

% Typical optimisations we have included is smart backtracking using undo semantics,
% or mutable state semantics.
% Using equational reasoning techniques and fold fusion, we have proven all simulations
% correct.

We studied the simulations of higher-level effects with lower-level
effects for state and nondeterminism.
%
We started with the translation from the local-state semantics of
state and nondeterminism to the global-state semantics. Then, we
further showed how to translate nondeterminism to state (a choicepoint stack), and translate
multiple state effects into one state effect. Combining these results,
we can simulate the local-state semantics, a high-level programming
abstraction, with only one low-level state effect.
%
We also demonstrated that we can simulate the local-state semantics
using a trail stack in a similar style to the
Warren Abstract Machine of Prolog.
%
We define the effects and their translations with algebraic effects and
effect handlers respectively. These are implemented as free monads and folds in
Haskell.
%
The correctness of all these translations has been proved using the
technique of program calculation, especially using the fusion properties.

In future work, we would like to explore the potential optimisations
enabled by mutable states. Mutable states fit the global-state
semantics naturally. With mutable states, we can implement more
efficient state update and restoration operations for the simulation
|local2globalM| (\Cref{sec:undo}), as well as more efficient
implementations of the choicepoint stacks and trail stacks used by the
simulations |nondet2state| (\Cref{sec:nondet2state}) and |local2trail|
(\Cref{sec:trail-stack}), respectively.
%
We would also like to consider the low-level simulations of other
control-flow constructs used in logical programming languages such as
Prolog's |cut| operator for trimming the search space.
%
Since operators like |cut| are usually implemented as scoped
or higher-order effects~\citep{Pirog18,Wu14,YangPWBS22,BergS23}, we would have to 
adapt our approach accordingly.
