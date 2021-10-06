\section{Introduction}
\label{sec:introduction}

% \subsection{Overview}
% \label{sec:overview}

The trade-off between ``high-level'' and ``low-level'' styles of programming is almost as old as the field of computer sciences itself.
In a high-level style of programming, we lean on abstractions to make our
programs easier to read and write, and less error prone.  We pay for this
comfort by giving up precise control over the underlying machinery; we forego
optimization opportunities or have to trust a (usually opaque) compiler to
optimize for us. Hence, for performance-sensitive applications, we often
have to resort to lower-level programming techniques.  Although they allow a
fine-grained control over program execution and the implementation of
optimization techniques, they tend to be harder to write and not compose very well.  This is an
important trade-off to take into account when choosing an appropriate programming language
for implementing an application.

Maybe surprisingly, as they are rarely described in this way, there is a
similar pattern for side-effects within programming languages: some effects can
be described as ``lower-level'' than others.  We say that an effect is
lower-level than another effect when the lower-level effect can simulate the
higher-level effect. In other words, it is always possible to write a
program using lower-leel effects that has identical semantics to the same program with
higher-level effects.
Yet, due to the lack of abstraction of low-level effects, writing a faithful
simulation requires careful discipline and is quite error-prone.

This article investigates how how we can construct programs that are most
naturally expressed with a high-level effect, but where we still want access to
the optimization opportunities of a lower-level effect.  In particular,
inspired by Prolog and Constraint Programming systems, we investigate programs
that rely on the high-level interaction between the nondeterminism and state
effects, called \emph{local state}. Following low-level implementation
techniques for these systems, like the Warren Abstract Machine (WAM)
\cite{hassan91}, we show how these can be simulated in terms of the low-level
\emph{global state} interaction of state and nondeterminism, and finally by state alone. This
allows us to incorporate typical optimizations like exploiting mutable state
for efficient backtracking based on \emph{trailing}~\cite{}.

Our approach is based on algebraic effects and handlers~\cite{} to cleanly
separate the use of effects from their implementation. This way we can replace
a high-level implementation with an implementation in terms of a low-level
effect and incorporate optimizations. Moreover, we can prove all of our
simulations correct using equational reasoning techniques, exploiting in
particular the fusion property of handlers~\cite{}.

%In particular, a purely functional programming style lets us reason about our programs equationally.
%At first glance, it may seem that equational reasoning is made possible by the lack of side effects in functional programming.
%But work such as \todo{hutton and fulger} and \todo{gibbons and hinze} shows that, when we model our side effects with monads,


% \subsection{Contributions}
% \label{sec:contributions}

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
	\item We prove all simulations correct using equational reasoning techniques (\Cref{app:universality-nondeterminism}, \Cref{app:nondet-state} and \Cref{app:local-global}).
\end{itemize}

Finally, we discuss related work (Section \ref{sec:related-work}) and conclude (Section \ref{sec:conclusion})
