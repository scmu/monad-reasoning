%===============================================================================
\section{Related Work}
\label{sec:related-work}

\subsection{Prolog}

Prolog is a prominent example of a system that exposes nondeterminism with
local state to the user, but is itself implemented in terms of a single global
state.

\paragraph{Warren Abstract Machine}
The folklore idea of undoing modifications upon backtracking is a key feature
of many Prolog implementations, in particular those based on the Warren Abstract Machine (WAM)~\cite{hassan}.
The WAM's global state is the program heap and Prolog programs modify this heap
during unification only in a very specific manner: following the union-find
algorithm, they overwrite cells that contain self-references with pointers to
other cells. Undoing these modifications only requires knowledge of the
modified cell's address, which can be written back in that cell during
backtracking. The WAM has a special stack, called the trail stack, for storing
theses addresses, and the process of restoring those cells is called
\emph{untrailing}.

\paragraph{The 4-Port Box Model}
While trailing happens under the hood, there is a folklore Prolog programming
pattern for observing and intervening at different points in the control flow 
of a producere call,
known as the {\em 4-port box model}.
In this model, upon the first entrance of a Prolog procedure it is {\em
called}; it may yield a result and {\em exits}; when the subsequent procedure
fails and backtracks, it is asked to {\em redo} its computation, possibly
yielding the next result; finally it may {\em fail}.  Given a Prolog procedure
|p| implemented in Haskell, the following program prints debugging messages
when each of the four ports are used:
\begin{spec}
  (putStr "call" `mplus` side (putStr "fail")) >>
  p >>= \x ->
  (putStr "exit" `mplus` side (putStr "redo")) >> return x {-"~~."-}
\end{spec}
This technique was applied the monadic setting by Hinze~\cite{DBLP:journals/ijfcs/Hinze01},
and it has been our inspiration for expressing the state restoration with global state.

%-------------------------------------------------------------------------------
\subsection{Reasoning About Side Effects}

There are many works on reasoning and modelling side effects. Here we cover
those that have most directly inspired this paper.

\paragraph{Axiomatic Reasoning}

Our work was directly inspired by Gibbons and Hinze's proposal to reason
axiomatically about programs with side effects, and their axiomatic
characterisation of local state in particular~\cite{GibbonsHinze:11:Just}. We
have extended their work with an axiomatic characterisation of global state and
on handling the former in terms of the latter. We also provide models that
satisfy the axioms, whereas their paper mistakenly claims that one model
satisfies the local state axioms and that another model is monadic.


\paragraph{Algebraic Effects}

Our formulation of implementing local state with global state is directly
inspired by the effect handlers approach of Plotkin and
Pretnar~\cite{Plotkin:09:Handlers}. By making the free monad explicit our
proofs benefit directly from the induction principle that Bauer and Pretnar
establish for effect handler programs~\cite{DBLP:journals/corr/BauerP13}.

While Lawvere theories were originally Plotkin's inspiration for studying
algebraic effects, the effect handlers community has for a long time paid
little attention to them. Yet, recently Luk\v{s}i\v{c} and
Pretnar~\cite{Pretnar:19} have investigated a framework for encoding axioms (or
``effect theories'') the type system: the type of an effectful function
declares the operators used in the function, as well as the equalities that
handlers for these operators should comply with.  The type of a handler
indicates which operators it handles and which equations it complies with. 
This type system would allow us to express at the type-level that our
handler interprets local state in terms of global state.

%===============================================================================
\section{Conclusions}
\label{sec:conclusion}

Starting from Gibbons and Hinze's observation~\cite{GibbonsHinze:11:Just}
\koen{is this the first mention of this observation?}
that the interaction between state and nondeterminism can be characterized
axiomatically in
multiple ways, we explored the differences between local state semantics (as
characterised by Gibbons and Hinze) and global state semantics (for which we
gave our own non-monadic characterisation).

In global state semantics, we find that we may use |mplus| to simulate sequencing, and that the idea can be elegantly packaged into commands like |putR| and |modifyR|.
The interaction between global state and non-determinism turns out to be rather tricky.
For a more rigorous treatment, we enforce a more precise separation between
syntax and semantics and, as a side contribution of this paper, propose a
\emph{global state law}, plus some additional laws, which the semantics should satisfy.
We verified (with the help of the Coq proof assistant) that there is an implementation satisfying these laws.

Using the $n$-queens puzzle as an example, we showed that one can end up in a
situation where a problem is naturally expressed with local state semantics, but
the greater degree of control over resources that global state semantics offers
is desired. We then describe a technique to systematically transform a
monadic program written against the local state laws into one that,
when interpreted under global state laws, produces the same results as the
original program. This transformation can be viewed as a handler (in the
algebraic effects sense): it implements the interface of one effect in terms of
the interface of another.
We also verified the correctness of this transformation in Coq.




% This paper started as a case study of reasoning and derivation of monadic programs.
% To study the interaction between non-determinism and state, we
% construct backtracking algorithms solving problems that can be specified in the form |unfoldM f p >=> assert (all ok . scanlp oplus st)|, for two scenarios.
% In the first scenario, we assume that right-distributivity and right-zero laws hold, which imply that each non-deterministic branch has its own state.
% The derivation of the backtracking algorithm works by fusing the two phases into a monadic hylomorphism.
% 
% In the second scenario we consider the case when the state is global.
% We find that we may use |mplus| to simulate sequencing, and that the idea can be elegantly packaged into commands like |putR| and |modifyR|.
% The interaction between global state and non-determinism turns out to be rather tricky.
% For a more rigorous treatment, we enforce a more precise separation between syntax and semantics and, as a side contribution of this paper, propose a collection of \emph{global state laws} which the semantics should satisfy,
% and verified in Coq that there is an implementation satisfying these laws.
% With the setting up, we show that a program written for local state works for the global state scenario if we replace all occurrences of |put| by |putR|.
% 
% It turns out that in derivations of programs using non-determinism and state, commutativity plays an important role. When the state is local, we have nicer properties at hand, and commutativity holds more generally.
% With a shared global state, commutativity holds in limited cases.
% In particular, |putR| still commutes with non-determinism.


% We noted that |M s a = \s -> ([a],s)| fails \eqref{eq:bind-mplus-dist} and is not a monad.
% The type |ListT (State s)| generated using the now standard Monad Transformer Library~\cite{MTL:14} expands to essentially the same implementation, and is flawed in the same way. More careful implementations of |ListT|, which does satisfy \eqref{eq:bind-mplus-dist} and the monad laws, have been proposed~\cite{Gale:07:ListT,Volkov:14:list-t}.
% Effect handlers, such as that of Wu~\cite{Wu:14:Effect} and Kiselyov and Ishii~\cite{KiselyovIshii:15:Freer}, do produce correct implementations by running the handler for non-determinism before that of state.

%\paragraph{Acknowledgements} to be added.
