\section{Introduction}
\label{sec:introduction}

% \subsection{Overview}
% \label{sec:overview}

Knowledge of the trade-off between ``high-level'' and ``low-level'' styles of programming is almost as old as the field of computer sciences itself.
In a high-level style of programming, we lean on abstractions to make our programs less prone to error, and easier to read and write.
We pay for this comfort by giving up precise control over the underlying machinery; we forego opportunities for optimization or have to trust a (usually opaque) compiler to optimize for us.
As such, for performance-sensitive applications, we often have to resort to lower-level programming techniques.
Although they allow a fine-grained control over program execution and the implementation of optimization techniques, they tend not to compose very well.
This is an important tradeoff to make when choosing an appropriate programming language for implementing an application.

Maybe surprisingly, as they are rarely described in this way, 
we can spot a similar pattern for side-effects within programming languages:
some effects can be described as ``lower-level'' than others.
We say that an effect is lower-level than another effect when the lower-level effect can simulate the higher-level effect.
In other words, it is always possible to write a lower-level program with identical semantics to the higher-level program.
Writing such a faithful simulation might require careful discipline and be quite error-prone to do by hand.

For example, nondeterminism and state can be composed in two distinct ways: 
a local-state variant, where the state is local to each branch of the nondeterministic computation; 
and a global-state variant, where a single state persists throughout the entire nondeterministic computation.
Of these two effects, the global-state variant is the lower level one: for every local state program we can construct a global state program that simulates it by carefully restoring the state at every branch of the computation.
But not all global state programs can be simulated by a local state program.

In a similar way, we can simulate nondeterminism using the ``lower-level'' state effect.
Especially mutable state is of interest as it allows for performance optimizations in several programs.

In this paper, we investigate how we can construct programs that are most naturally expressed with a high-level effect, 
but where we still want access to the optimization opportunities of a lower-level effect.
In particular, we look into the case of constructing programs using a nondeterminism and state effect. 
We distinguish between local state and global state and simulate the former using the latter.
We also simulate nondeterminism using state and take this a step further by showing optimizations these 
simulations allow, such as efficient backtracking semantics or mutable state. 

In this paper, we come close to modeling Warren's Abstract Machine (WAM) \cite{hassan91}. 
However, we illustrate the simulations and the resulting optimizations on the well-known n-queens
puzzle.
Furthermore, we proof all of our simulations correct using equational reasoning techniques.
We believe that, in particular, these proof techniques are of interest. 


%In particular, a purely functional programming style lets us reason about our programs equationally.
%At first glance, it may seem that equational reasoning is made possible by the lack of side effects in functional programming.
%But work such as \todo{hutton and fulger} and \todo{gibbons and hinze} shows that, when we model our side effects with monads, 


\subsection{Contributions}
\label{sec:contributions}

After introducing the reader to the appropriate background material and motivating the problem (Section \ref{sec:background}), 
this paper makes the following contributions:

\begin{itemize}
	\item We formally distinguish between local-state and global-state semantics.
		  We define a simulation to model local state using global state (\Cref{sec:local-global}).
	\item We define undo semantics to allow more efficient backtracking (\Cref{sec:local-global}).
	\item We simulate nondeterminism using state (\Cref{sec:nondeterminism-state}).
	\item We combine the previous simulations in a single simulation function where we model nondeterminism and state using 
		  a single state effect. As an extension, we work out mutable state as a possible optimization (\Cref{sec:combination}).
	\item We illustrate the simulations and resulting optimizations using the n-queens puzzle as a running example throughout
		  all sections.
	\item We prove all simulations correct using equational reasoning techniques (\Cref{app:universality-nondeterminism}, \Cref{app:app:nondet-state} and \Cref{app:local-global}).
\end{itemize}

Finally, we discuss related work (Section \ref{sec:related-work}) and conclude (Section \ref{sec:conclusion})
