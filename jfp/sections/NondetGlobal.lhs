%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}

module NondetGlobal where

import ListT  -- use option -i../../code

import Background
import Utilities
\end{code}
%endif

\section{Non-Determinism with Global State}
\label{sec:nd-state-global}
So far, we have evaded giving a precise axiomatic characterisation of global
state semantics: although in Section~\ref{sec:background} we provided an example
implementation that matches our intuition of global state semantics, we haven't
provided a clear formulation of that intuition. We begin this section by finally
stating the ``global state law'', which characterises exactly the property that
sets apart non-backtrackable state from backtrackable state.

In the rest of the section, we appeal to intuition and see what happens when we
work with a global state monad: what pitfalls we may encounter, and what
programming pattern we may use, to motivate the more formal treatment in
Section~\ref{sec:ctxt-trans}.

\subsection{The Global State Law}
\label{sec:laws-global-state}
We have already discussed general laws for nondeterministic monads
(laws~\eqref{eq:mplus-assoc} through~\eqref{eq:bind-mzero-zero}),
as well as laws which govern the interaction between state and nondeterminism in
a local state setting (laws~\eqref{eq:mplus-bind-dist} and
\eqref{eq:mzero-bind-zero}).
For global state semantics, an alternative law is required to govern the
interactions between nondeterminism and state.
We call this the \emph{global state law}.
\begin{alignat}{2}
&\mbox{\bf put-or}:\quad&
  |(put s >> m) `mplus` n| &=~ |put s >> (m `mplus` n)|~ \mbox{~~,}
    \label{eq:put-or}
\end{alignat}
This law allows the lifting of a |put| operation from the left
branch of a nondeterministic choice, an operation which does not preserve
meaning under local state semantics.
Suppose for example that |m = mzero|, then by
\eqref{eq:mzero-bind-zero} and~\eqref{eq:mzero-mplus}, the left-hand side of
the equation is equal to |n|, whereas by~\eqref{eq:mzero-mplus},
the right-hand side of the equation is equal to |put s >> n|.

By itself, this law leaves us free to choose from a large space of
implementations with different properties.
For example, in any given implementation, the programs |return x `mplus` return y| and
|return y `mplus` return x| may be considered semantically identical, or they may be
considered semantically distinct.
The same goes for the programs |return x `mplus` return x| and |return x|,
or the programs |(put s >> return x) `mplus` m| and
|(put s >> return x) `mplus` (put s >> m)|.
Additional axioms will be introduced as needed to cover these properties in
Section~\ref{sec:model-global-state-sem}.

%We will also require another property which we will only introduce informally
%here (and formulate more clearly later).
%In global state semantics, the right-distributivity rule does not hold in
%general. However, there are some cases where an operation does distribute over
%non-deterministic choice while preserving semantics; more precisely, this is the
%case when
%\begin{enumerate}
%\item the left branch of the choice operator does not modify the state,
%\item the operation that is distributed over the choice operator is idempotent
%  with respect to the state, and
%\item this operation is at the top-level of the program (i.e. it is not a
%  subterm of a larger term).
%\end{enumerate}
%This last property is a ``global'' property.
%In order to formulate it correctly, we first need to develop a notation that
%allows us to distinguish between local and global properties.
%We will do this in Section~\ref{sec:ctxt-trans}.

\subsection{Chaining Using Non-deterministic Choice}
\label{sec:chaining}

In backtracking algorithms that keep a global state, it is a common pattern to
1. update the current state to its next step,
2. recursively search for solutions, and
3. roll back the state to the previous step (regardless of whether a solution is found).
To implement such pattern as a monadic program, one might come up with something like the code below:
\begin{spec}
modify next >> search >>= modReturn prev {-"~~,"-}
\end{spec}
where |next| advances the state, |prev| undoes the modification of |next|
(|prev . next = id|), and |modify| and |modReturn| are defined by:
\begin{spec}
modify f       = get >>= (put . f) {-"~~,"-}
modReturn f v  = modify f >> return v {-"~~."-}
\end{spec}
Let the initial state be |st| and assume that |search| found three choices |m1 `mplus` m2 `mplus` m3|.
We wish that |m1|, |m2|, and |m3| all start running with state |next st|, and the state is restored to |prev (next st) = st| afterwards.
Due to \eqref{eq:bind-mplus-dist}, however, it expands to
\begin{spec}
 modify next >> (m1 `mplus` m2 `mplus` m3) >>= modReturn prev =
   modify next >> (  (m1 >>= modReturn prev) `mplus`
                     (m2 >>= modReturn prev) `mplus`
                     (m3 >>= modReturn prev)) {-"~~."-}
\end{spec}
With a global state, it means that |m2| starts with state |st|, after which the state is rolled back further to |prev st|. The computation |m3| starts with |prev st|, after which the state is rolled too far to |prev (prev st)|.
In fact, one cannot guarantee that |modReturn prev| is always executed --- if |search| fails and reduces to |mzero|, |modReturn prev| is not run at all, due to \eqref{eq:bind-mzero-zero}.

% In fact, one cannot guarantee that |modReturn prev| is always executed --- if |search| fails, we get |modify next >> search >>= modReturn prev| |= modify next >> mzero >>= modReturn prev = modify next >> mzero|. Thus the state is advanced to |next st|, but not rolled back to |st|.

We need a way to say that ``|modify next| and |modReturn prev| are run exactly once, respectively before and after all non-deterministic branches in |solve|.'' Fortunately, we have discovered a curious technique. Define
\begin{code}
side :: MNondet m => m a -> m b
side m = m >> mzero {-"~~."-}
\end{code}
Since non-deterministic branches are executed sequentially, the program
\begin{spec}
side (modify next) `mplus` m1 `mplus` m2 `mplus` m3 `mplus` side (modify prev)
\end{spec}
executes |modify next| and |modify prev| once, respectively before and after all the non-deterministic branches, even if they fail.
Note that |side m| does not generate a result.
Its presence is merely for the side-effect of |m|, hence the name.
%Note also that the type of |side m| need not be the same as that of |m|.

The reader might wonder: now that we are using |(`mplus`)| as a sequencing operator, does it simply coincide with |(>>)|?
Recall that we still have left-distributivity \eqref{eq:bind-mplus-dist} and, therefore,
|(m1 `mplus` m2) >> n| equals |(m1 >> n) `mplus` (m2 >> n)|.
That is, |(`mplus`)| acts as ``insertion points'', where future code followed by |(>>)| can be inserted into!
This is certainly a dangerous feature, whose undisciplined use can lead to chaos.
However, we will exploit this feature and develop a safer programming pattern in the next section.

\subsection{State-Restoring Operations}
\label{subsec:state-restoring-ops}

The discussion above suggests that one can implement backtracking, in a global-state setting, by using |mplus| and |side| appropriately.
We can even go a bit further by defining the following variation of |put|,
which restores the original state when it is backtracked over:
\begin{code}
putR :: MStateNondet s m => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~."-}
\end{code}

\begin{figure}
  \centering
  \includegraphics[scale=0.7]{sections/putR}
  \caption{Illustration of state-restoring put}
  \label{fig:putR}
\end{figure}

To help build understanding for |putR|, Figure~\ref{fig:putR} shows the flow of
execution for the expression |(putR t >> ret x) `mplus` ret y|. Initially, the
state is |s|; it gets modified to |t| at the |put t| node after which the value
|x| is output with the working state |t|. Then, because we found a result, we
backtrack (since we're using global-state semantics, the state modification
caused by |put t| is not reversed), arriving in the |side| operation branch. The
|put s| operation is executed, which resets the state to |s|, and then the
branch immediately fails, so we backtrack to the right branch of the topmost
|mplus|. There the value |y| is output with working state |s|.

For some further intuition about |putR|, consider |putR s >> comp| where |comp| is some arbitrary computation:
%if False
\begin{code}
putRExplain :: MStateNondet s m => s -> m b -> m b
putRExplain s comp =
\end{code}
%endif
\begin{code}
      putR s >> comp
 ===  (get >>= \s0 -> put s `mplus` side (put s0)) >> comp
 ===    {- monad law, left-distributivity \eqref{eq:bind-mplus-dist} -}
      get >>= \s0 -> (put s >> comp) `mplus` (side (put s0) >> comp)
 ===    {- by \eqref{eq:bind-mzero-zero} |mzero >> comp = mzero|, monad laws -}
      get >>= \s0 -> (put s >> comp) `mplus` side (put s0) {-"~~."-}
\end{code}
Thanks to left-distributivity \eqref{eq:bind-mplus-dist}, |(>> comp)| is promoted into |mplus|.
Furthermore, the |(>> comp)| after |side (put s0)| is discarded by
\eqref{eq:bind-mzero-zero}.
In words, |putR s >> comp| saves the current state, computes |comp| using state |s|, and restores the saved state!
The subscript |R| stands for ``restore.''
Note also that |(putR s >> m1) >> m2 = putR s >> (m1 >> m2)| --- the state restoration happens in the end.

The behaviour of |putR| is rather tricky. It is instructive comparing
\begin{enumerate}[label=(\alph*)]
\item |return x|,  \label{ex:putR-pitfalls-1}
\item |put s >> return x|, \label{ex:putR-pitfalls-2}
\item |putR s >> return x|. \label{ex:putR-pitfalls-3}
\end{enumerate}
When run in initial state |s0|, they all yield |x| as the result.
The final states after running \ref{ex:putR-pitfalls-1}, \ref{ex:putR-pitfalls-2} and \ref{ex:putR-pitfalls-3} are |s0|, |s| and |s0|, respectively.
However, \ref{ex:putR-pitfalls-3} does {\em not} behave identically to \ref{ex:putR-pitfalls-1} in all contexts!
For example, in the context |(>> get)|, we can tell them apart:
|return x >> get| returns |s0|, while |putR s >> return x >> get| returns |s|, even though the program yields final state |s0|.

We wish that |putR|, when run with a global state, satisfies laws \eqref{eq:put-put} through \eqref{eq:mplus-bind-dist} ---
the state laws and the \emph{local} state laws.
If so, one could take a program written for a local state monad, replace all occurrences of |put| by |putR|, and run the program with a global state.
Unfortunately this is not the case: |putR| does satisfy {\bf put-put}~\eqref{eq:put-put} and {\bf put-get}~\eqref{eq:put-get}, but {\bf get-put}~\eqref{eq:get-put} fails ---
|get >>= putR| and |return ()| can be
differentiated by some contexts, for example |(>> put t)|.
To see that, we calculate:
%if False
\begin{code}
getPutExplain :: MStateNondet s m => s -> m ()
getPutExplain t =
\end{code}
%endif
\begin{code}
      (get >>= putR) >> put t
 ===  (get >>= \s -> get >>= \s0 -> put s `mplus` side (put s0)) >> put t
 ===    {- {\bf get-get} -}
      (get >>= \s -> put s `mplus` side (put s)) >> put t
 ===    {- monad laws, left-distributivity -}
      get >>= \s -> (put s >> put t) `mplus` side (put s)
 ===    {- {\bf put-put} -}
      get >>= \s -> put t `mplus` side (put s) {-"~~."-}
\end{code}
Meanwhile, |return () >> put t = put t|, which does not behave in the same way as |get >>= \s -> put t `mplus` side (put s)| when $s \neq t$.

In a global-state setting, the left-distributivity law
\eqref{eq:bind-mplus-dist} makes it tricky to reason about combinations of
|mplus| and |(>>=)| operators. Suppose we have a program |(m `mplus` n)|, and we
construct an extended program by binding a continuation |f| to it such that we
get |(m `mplus` n) >>= f| (where |f| might modify the state). Under global-state
semantics, the evaluation of the right branch is influenced by the state
modifications performed by evaluating the left branch. So by
\eqref{eq:bind-mplus-dist}, this means that when we get to evaluating the |n|
subprogram in the extended program, it will do so with a different initial state
(the one obtained after running |m >>= f|) compared to the initial state in the
original program (the one obtained by running |m|). In other words, placing our
program in a different context changed the meaning of one of its subprograms. So
it is difficult to reason about programs compositionally in this
setting---some properties hold only when we take the entire program into
consideration.

It turns out that all properties we need do hold, provided that {\em all}
occurrences of |put| are replaced by |putR|---problematic contexts such as
|put t| above are thus ruled out. However, that ``all |put| are replaced by
|putR|'' is a global property, and to properly talk about it we have to formally
define contexts, which is what we will do in Section~\ref{sec:ctxt-trans}.
Notice though, that simulation of local state semantics by judicious use of
|putR| does not avoid the unnecessary copying mentioned in
Section~\ref{sec:space-usage}, it merely makes it explicit in the program.
We will address this shortcoming in Section~\ref{sec:backtrack-gs}.