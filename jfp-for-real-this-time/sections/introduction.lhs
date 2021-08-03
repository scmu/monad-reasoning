\section{Introduction}
\label{sec:introduction}
\todo{Intro}

\subsection{Overview}
\label{sec:overview}

Knowledge of the trade-off between ``high-level'' and ``low-level'' styles of programming is almost as old as the field of computer sciences itself.
In a high-level style of programming, we lean on abstractions to make our programs less prone to error, and easier to read and write.
We pay for this comfort by giving up precise control over the underlying machinery; we forego opportunities for optimization or have to trust a (usually opaque) compiler to optimize for us.
As such, for performance-sensitive applications, we often have to resort to lower-level programming techniques which tend not to compose very well.
\birthe{also briefly discuss the pros and cons of low-level languages?}

Although they are rarely described in this way, we can spot a similar pattern for side-effects within programming languages:
some effects can be described as ``lower-level'' than others.
We say that an effect is lower-level than another effect when the lower-level effect can simulate the higher-level effect (in other words, it is always possible to write a lower-level program with identical semantics to the higher-level program).
Writing such a faithful simulation might require careful discipline and be quite error-prone to do by hand.

\birthe{From here on, we could structure the introduction more similar to the flow of the paper.}

For example, nondeterminism and state can be composed in two distinct ways: a local-state variant, where the state is local to each branch of the nondeterministic computation; and a global-state variant, where a single state persists throughout the entire nondeterminstic computation.
Of these two effects, the global state variant is the lower level one: for every local state program we can construct a global state program that simulates it by carefully restoring the state at every branch of the computation.
But not all global state programs can be simulated by a local state program.

In this paper, we investigate how we can construct programs that are most naturally expressed with a high-level effect, but where we still want access to the optimization opportunities of a lower-level effect.
In particular, we will investigate the case of constructing programs based on local-state semantics, by writing them against a local-state interface and systematically transforming them into a semantically equivalent global-state program.
We also study several further extensions, such as mutable state, undo and cut semantics.


%In particular, a purely functional programming style lets us reason about our programs equationally.
%At first glance, it may seem that equational reasoning is made possible by the lack of side effects in functional programming.
%But work such as \todo{hutton and fulger} and \todo{gibbons and hinze} shows that, when we model our side effects with monads, 




\subsection{Contributions}
\label{sec:contributions}

After introducing the reader to the appropriate background material and motivating the problem (Section \ref{sec:background}), this paper makes the following contributions:

\begin{itemize}
	\item \todo{S3: modeling nondeterminism with state}
	\item \todo{S4: modeling local state with global state}
	\item \todo{S5: modeling state and nondet with state}
	\item \todo{S6: extension such as mutable state, undo and cut semantics}
	\item \todo{Apps: using equational reasoning and initiality of lists and state transformers to prove our simulations correct}
\end{itemize}

Finally, we discuss related work (Section \ref{sec:related-work}) and conclude (Section \ref{sec:conclusion})
