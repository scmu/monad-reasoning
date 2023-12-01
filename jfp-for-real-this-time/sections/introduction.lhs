%if False
\begin{code}
\end{code}
%endif

\section{Introduction}
\label{sec:introduction}

% \subsection{Overview}
% \label{sec:overview}

The trade-off between ``high-level'' and ``low-level'' styles of programming is almost as old as the field of computer sciences itself.
In a high-level style of programming, we lean on abstractions to make our
programs easier to read and write, and less error-prone.  We pay for this
comfort by giving up precise control over the underlying machinery; we forego
optimisation opportunities or have to trust a (usually opaque) compiler to
perform low-level optimisations for us. For performance-sensitive applications, compiler optimisations
are not reliable enough; instead we often resort to lower-level programming
techniques ourselves.  Although they allow a
fine-grained control over program execution and the implementation of
optimisation techniques, they tend to be harder to write and not compose very well.  This is an
important trade-off to take into account when choosing an appropriate programming language
for implementing an application.

Maybe surprisingly, as they are rarely described in this way, there is a
similar pattern for side-effects within programming languages: some effects can
be described as ``lower-level'' than others.  We say that an effect is
lower-level than another effect when the lower-level effect can simulate the
higher-level effect. In other words, it is possible to write a
program using lower-level effects that has identical semantics to the same program with
higher-level effects.
Yet, due to the lack of abstraction of low-level effects, writing a faithful
simulation requires careful discipline and is quite error-prone.

This article investigates how we can construct programs that are most
naturally expressed with a high-level effect, but where we still want access to
the optimisation opportunities of a lower-level effect. In particular,
inspired by Prolog and Constraint Programming systems, we investigate programs
that rely on the high-level interaction between the nondeterminism and state
effects which we call \emph{local state}. Following low-level implementation
techniques for these systems, like the Warren Abstract Machine (WAM)
\citep{AICPub641:1983,AitKaci91}, we show how these can be simulated in terms of the low-level
\emph{global state} interaction of state and nondeterminism, and finally by state alone. This
allows us to incorporate typical optimisations like exploiting mutable state
for efficient backtracking based on \emph{trailing} as opposed to copying or recomputing
the state from scratch ~\citep{Schulte:ICLP:1999}.

Our approach is based on algebraic effects and handlers
~\citep{PlotkinP03, Plotkin09, Plotkin13} to cleanly separate the use
of effects from their implementations. Effect handlers allow us to
flexibly interprets high-level effects with low-level effects and
incorporate optimisations.
% replace a high-level implementation with an implementation in terms
% of low-level effects and incorporate optimisations.

Of particular interest is the way we reason about the correctness of our
approach. There has been much debate in the literature on different equational
reasoning approaches for effectful computations. \citet{Hutton08} break the
abstraction boundaries and use the actual implementation in their equational
reasoning approach. \citet{Gibbons11} promote an alternative, law-based
approach to preserve abstraction boundaries and combine axiomatic with
equational reasoning. In an earlier version of this work \citep{Pauwels19}, we
have followed the latter, law-based approach for reasoning about the
correctness of simulating local state with global state. However, we have found
that approach to be unsatisfactory because it incorporates elements
that are usually found in the syntactic approach for reasoning about
programming languages \citep{Felleisen94}, leading to more boilerplate and
complication in the proofs: notions of contextual equivalence and explicit
manipulation of program contexts. Hence, for that reason we return to the
implementation-based reasoning approach, which we believe works well with
algebraic effects and handlers. Indeed, we can prove all of our simulations
correct using equational reasoning techniques, exploiting in particular the
fusion property of handlers ~\citep{Wu15}. Moreover, in part of our reasoning
we use initial effect implementations, which we argue do not leak any implementation details
but merely leverage the common properties of all implementations.

%In particular, a purely functional programming style lets us reason about our programs equationally.
%At first glance, it may seem that equational reasoning is made possible by the lack of side effects in functional programming.
%But work such as \todo{hutton and fulger} and \todo{gibbons and hinze} shows that, when we model our side effects with monads,


% \subsection{Contributions}
% \label{sec:contributions}

After introducing the reader to the appropriate background material and motivating the problem (\Cref{sec:background} 
and \Cref{sec:overview}),
this paper makes the following contributions:

\begin{itemize}
	\item We distinguish between local-state and global-state semantics,
              and simulate the former in terms of the latter (\Cref{sec:local-global}).
	\item We simulate nondeterminism using a state that consists of a choicepoint stack (\Cref{sec:nondeterminism-state}).
	\item We combine the previous two simulations and merge the two states into
		  a single state effect (\Cref{sec:combination}).
	\item By only allowing incremental, reversible updates to the state we can avoid holding on to multiple copies of the state (\Cref{sec:undo}).
	\item By storing the incremental updates in a trail stack state, we can restore them in batch when backtracking (\Cref{sec:trail-stack}).
	\item We prove all simulations correct using equational reasoning techniques and the fusion law for handlers in particular 
        (\Cref{app:local-global}, \Cref{app:nondet-state}, \Cref{app:states-state}, \Cref{app:final-simulate}, \Cref{app:modify-local-global} and \Cref{app:immutable-trail-stack}).
\end{itemize}
% \birthe{Compared to the MPC paper, the contribution of formulating a global state law is missing.}
% Wenhao: I don't think the global state law (put-or) is new.
Finally, we discuss related work (\Cref{sec:related-work}) and conclude (\Cref{sec:conclusion})
%
Throughout the paper, we use Haskell as a means to illustrate
our findings with code.
