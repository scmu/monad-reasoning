%%include lhs2TeX.fmt
%%include forall.fmt
%%include polycode.fmt
%%include Formatting.fmt

\section{Introduction}
Monads have been introduced to functional programming to support side effects
in a rigorous, mathematically manageable
manner~\cite{Moggi:89:Computational,Wadler:92:Monads}. Over time they have
become the main framework in which effects are modelled. Various monads were
developed for different effects, from general ones such as IO, state,
non-determinism, exception, continuation, environment passing, to specific
purposes such as parsing. Much research was also devoted to producing practical
monadic programs.

Equational reasoning about pure functional programs is particularly simple and
powerful. Yet, Hutton and Fulger~\cite{HuttonFulger:08:Reasoning} noted that a
lot less attention has been paid to reasoning about monadic programs in that
style. Gibbons and Hinze~\cite{GibbonsHinze:11:Just} argue that equational
reasoning about monadic programs becomes particularly convenient and elegant
when one respects the abstraction boundaries of the monad. This is possible
by reasoning in terms of axioms or laws that characterise the monad's
behavior without fixing its implementation.

This paper is a case study of equational reasoning with monadic programs.
Following the approach of algebraic effects and
handlers~\cite{Plotkin:09:Handlers}, we consider how one monad can be
implemented in terms of another---or, in other words, how one can be simulated
in by another using a careful discipline. Our core contribution is a novel
approach for proving the correctness of such a simulation. The proof approach is
a convenient hybrid between equational reasoning based on axioms and inductive
reasoning on the structure of programs. To capture the simulation we apply the
algebraic effects technique of \emph{handling} a free monad
representation~\cite{Wu:14:Effect}.
The latter provides a syntax tree on which to perform
induction. To capture the careful discipline of the simulation we use contextual
equivalence and perform inductive reasoning about program contexts. This allows
us to deal with a heterogeneous axiom set where different axioms may make use of
different notions of equality for programs.

We apply this proof technique to a situation where
each ``monad'' (both the simulating monad and the simulated monad)
is in fact a combination of two monads, with differing laws on how these effects
interact:
% following the approach of algebraic effects and
% handlers~\cite{Plotkin:09:Handlers}, we consider how one monad can be
% implemented in terms of another.
% Both monads we consider combine two effects:
non-determinism and state.

In the monad we want to implement, each
non-deterministic branch has its own `local' copy of the state. This is a
convenient effect interaction which is provided by many systems that solve
search problems, including Prolog.
A characterisation of this `local state' monad was given by Gibbons and
Hinze~\cite{GibbonsHinze:11:Just}.

We realise this local state semantics in terms of a more primitive monad where
a single state is sequentially threaded through the non-deterministic
branches. Because this state is shared among the branches, we call this the
`global state' semantics. The appearance of local state is obtained by
following a discipline of undoing changes to the state when backtracking to the
next branch. This folklore backtracking technique is implemented by most
sequential search systems because of its relative efficiency: remembering what
to undo often requires less memory than creating multiple copies of the state,
and undoing changes often takes less time than recomputing the state from
scratch.
To the best of our knowledge, our axiomatic characterisation of the global state
monad is novel.

In brief, our contributions can be summarized as follows:
\begin{itemize}
\item
  We provide an axiomatic characterisation for the interaction between the
  monadic effects of non-determinism and state where the state is persistent
  (i.e., does not backtrack), together with a model that satisfies this
  characterisation.                                                           
\item
  We prove that---with a careful discipline---our characterisation of
  persistent state can correctly simulate Gibbons and Hinze's
  monadic characterisation of backtrackable state~\cite{GibbonsHinze:11:Just}.
  We use our novel proof approach (the core contribution of this paper) to do so.
\item
  Our proof also comes with a mechanization in Coq.\footnote{The proof can be
    found at \url{https://github.com/KoenP/LocalAsGlobal}.}
\end{itemize}

The rest of the paper is structured as follows.
First, Section~\ref{sec:background} gives an overview of the main concepts
  used in the paper and defines our terminology. Then,
Section~\ref{sec:motivation} informally explores the differences
  between local and global state semantics. Next,
Section~\ref{sec:nd-state-global}  explains how to handle local state
in terms of global state.
Section~\ref{sec:ctxt-trans} formalizes this approach and proves it correct.
Finally, Sections~\ref{sec:related-work} and~\ref{sec:conclusion} respectively
discuss related work and conclude.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PREVIOUS INTRO BEGIN
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Monads have been introduced to functional programming to support side effects
%in a rigorous, mathematically manageable
%manner~\cite{Moggi:89:Computational,Wadler:92:Monads}. Over time they have
%become the main framework in which effects are modelled. Various monads were
%developed for different effects, from general ones such as IO, state,
%non-determinism, exception, continuation, environment passing, to specific
%purposes such as parsing. Much research was also devoted to producing practical
%monadic programs.
%
%Equational reasoning about pure functional programs is particularly simple and
%powerful. Yet, Hutton and Fulger~\cite{HuttonFulger:08:Reasoning} noted that a
%lot less attention has been paid to reasoning about monadic programs in that
%style. Gibbons and Hinze~\cite{GibbonsHinze:11:Just} argue that equational
%reasoning about monadic programs becomes particularly convenient and elegant
%when one respects the abstraction boundaries of the monad. This is possible
%by reasoning in terms of axioms or laws that characterise the monad's
%behavior without fixing its implementation.
%
%This paper carries out a case study of such axiomatic reasoning about monads.
%What is peculiar about our case study is that it involves two monads rather than
%one: Following the approach of algebraic effects and
%handlers~\cite{Plotkin:09:Handlers}, we consider how one monad can be
%implemented in terms of another. Both monads we consider combine two effects:
%non-determinism and state. In the monad we want to implement, each
%non-deterministic branch has its own `local' copy of the state. This is a
%convenient effect interaction which is provided by many systems that solve
%search problems, including Prolog.
%
%We realise this local state semantics in terms of a more primitive monad where
%a single state is sequentially threaded through the non-deterministic
%branches. Because this state is shared among the branches, we call this the
%`global state' semantics. The appearance of local state is obtained by
%following a discipline of undoing changes to the state when backtracking to the
%next branch. This folklore backtracking technique is implemented by most
%sequential search systems because of its relative efficiency: remembering what
%to undo often requires less memory than creating multiple copies of the state,
%and undoing changes often takes less time than recomputing the state from
%scratch.
%
%The main challenge is to show that the monad we implement satisfies the local
%state axioms, already provided by Gibbons and
%Hinze~\cite{GibbonsHinze:11:Just}, in terms of a novel axiomatic
%characterisation for global state.
%
%Our specific contributions of this paper are:
%\begin{itemize}
%
%\item We provide an axiomatic characterisation for the interaction between the
%      monadic effects of non-determinism and state where the state is persistent
%      (i.e., does not backtrack), together with a model that satisfies this
%      characterisation.
%
%\item We prove that---with a careful discipline---our characterisation of
%      persistent state can correctly simulate Gibbons and Hinze's
%      monadic characterisation of backtrackable state~\cite{GibbonsHinze:11:Just}.
%
%\item Our proof approach is a convenient hybrid between equational reasoning
%      based on axioms and inductive reasoning about the syntactic structure
%      of programs:
%      \begin{itemize}
%      \item To capture the simulation we apply the
%            algebraic effects technique of \emph{handling} a free monad representation.
%            The latter provides a syntax tree on which to perform induction.
%
%      \item To capture the careful discipline of the simulation
%            we use contextual equivalence and perform inductive reasoning about program
%            contexts.
%      \end{itemize}
%      We believe that this proof technique is the core contribution of this paper.
%
%\item Our proof comes with a mechanisation in Coq. \footnote{The proof can be found at \url{https://github.com/KoenP/LocalAsGlobal}.}
%\end{itemize}
%
%The rest of the paper is structured as follows.
%First, Section~\ref{sec:background} gives an overview of the main concepts
%  used in the paper and defines our terminology. Then,
%Section~\ref{sec:motivation} informally explores the differences
%  between local and global state semantics. Next,
%Section~\ref{sec:nd-state-global}  explains how to handle local state
%in terms of global state.
%Section~\ref{sec:ctxt-trans} formalizes this approach and proves it correct.
%Finally, Sections~\ref{sec:related-work} and~\ref{sec:conclusion} respectively
%discuss related work and conclude.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PREVIOUS INTRO END
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% \subsection{Old}
%
% It is misleading if one says that functional programming does not allow side
% effects. In fact, even a purely functional language may allow a variety of side
% effects --- in a rigorous, mathematically manageable manner. Since the
% introduction of {\em monads} into the functional programming
% community~\cite{Moggi:89:Computational,Wadler:92:Monads}, it has become the
% main framework in which effects are modelled. Various monads were developed for
% different effects, from general ones such as IO, state, non-determinism,
% exception, continuation, environment passing, to specific purposes such as
% parsing. Numerous research were also devoted to producing practical monadic
% programs.
%
% % Monad transformers~\cite{Liang:95:Monad} were introduced to allow modular construction of monads. Shortcomings of this approach were noticed, and it was proposed to see execution of monadic programs as interaction between programs and handlers~\cite{Plotkin:09:Handlers, Kiselyov:13:Extensible, KiselyovIshii:15:Freer}.
%
% Hutton and Fulger~\cite{HuttonFulger:08:Reasoning} noted that relatively less
% attention has been paid to reasoning about monadic programs.  We believe that
% the observation is still true today, perhaps due to the impression that impure
% programs are bound to be difficult to reason about.  In fact, the laws of
% monads and their operators are sufficient to prove quite a number of useful
% properties about monadic programs.  The validity of these properties, proved
% using only these laws, is independent from the particular implementation of the
% monad.
%
% This paper follows the trail of Hutton and
% Fulger~\cite{HuttonFulger:08:Reasoning} and~Gibbons and
% Hinze~\cite{GibbonsHinze:11:Just}, aiming to develop theorems and patterns that
% are useful for reasoning about monadic programs.  We focus on two effects ---
% non-determinism and state.  The interaction between non-determinism and state
% is known to be intricate.  When each non-deterministic branch has its own local
% state, we get a relatively well-behaved monad, providing a richer collection of
% properties to work with.  When all the non-deterministic branches share one
% global state, the properties of the monad is much less intuitive, as we shall
% see in this paper.
%
% In this paper we consider problem specifications that use a monadic unfold to
% generate possible solutions, which are filtered using a |scanl|-like predicate.
% We construct backtracking algorithms for such problems in two scenarios, in
% which the state is respectively local and global.  In the local-state case, we
% develop theorems that convert a variation of |scanl| to a |foldr| that uses the
% state monad, as well as theorems constructing hylomorphism.  For the case of
% global state, we study programming patterns that guarantee to restore the
% initial state after all non-deterministic branches, propose laws the global
% state monad should satisfy, and show that one may simulate local states using a
% global state.  The algorithms are used to solve the |n|-queens puzzle, our
% running example.
