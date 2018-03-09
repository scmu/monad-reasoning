%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}

module NondetGlobal where

import Prelude hiding ((>>))
import Control.Monad hiding ((>>))
import Control.Monad.State hiding ((>>))

import ListT  -- use option -i../../code

import Utilities
import Monads
import Queens

(>>) :: Monad m => m a -> m b -> m b
m1 >> m2 = m1 >>= const m2
\end{code}
%endif

\section{Non-Determinism with Global State}
\label{sec:nd-state-global}

For a monad with both non-determinism and state, right-distributivity \eqref{eq:mplus-bind-dist} implies that each non-deterministic branch has its own state. This is not costly for states consisting of linked data structures, for example the state |(Int, [Int], [Int])| in the |n|-queens problem. In some applications, however, the state might be represented by data structures, e.g. arrays, that are costly to duplicate. For such practical concerns, it is worth considering the situation when all non-deterministic branches share one global state.

Non-deterministic monads with a global state, however, is rather tricky.
One might believe that |M a = s -> ([a],s)| is a natural implementation of such a monad. The usual, naive implementation of |(>>=)| using this representation, however, does not satisfy left-distributivity \eqref{eq:bind-mplus-dist}, consequently violates monad laws, and is therefore not even a monad. See Section \ref{sec:conclusion} for previous work on construction of a correct monad.

Even after we do have a non-deterministic, global-state passing implementation that is a monad, its semantics can sometimes be surprising.
In |m1 `mplus` m2|, the computation |m2| receives the state computed by |m1|.
Thus |mplus| is still associative, but certainly cannot be commutative.
As mentioned in Section \ref{sec:right-distr-local-state}, right-distributivity \eqref{eq:mplus-bind-dist} implies commutativity of |mplus|.
Contravariantly, \eqref{eq:mplus-bind-dist} cannot be true when the state is global.
Right-zero \eqref{eq:mzero-bind-zero} does not hold either: |mzero| simply fails, while |put s >> mzero|, for example, fails with an altered global state.
These significantly limit the properties we may have.

\subsection{Chaining Using Non-deterministic Choice}

In backtracking algorithms that keep a global state, it is a common pattern to
1. update the current state to its next step,
2. recursively search for solutions, and
3. roll back the state to the previous step.
To implement such pattern as a monadic program, one might come up with something like the code below:
\begin{spec}
modify next >> solve >>= modReturn prev {-"~~."-}
\end{spec}
where |next| advances the state, |prev| undoes the modification of |next|, and |modify| and |modReturn| are defined by:
\begin{spec}
modify f       = get >>= (put . f) {-"~~,"-}
modReturn f v  = modify f >> return v {-"~~."-}
\end{spec}
Let the initial state be |st| and assume that |solve| found three choices |m1 `mplus` m2 `mplus` m3|. The intention is that all of |m1|, |m2|, and |m3| start running with state |next st|, and the state is restored to |prev (next st) = st| afterwards. By \eqref{eq:bind-mplus-dist}, however,
\begin{spec}
 modify next >> (m1 `mplus` m2 `mplus` m3) >>= modReturn prev =
   modify next >> (  (m1 >>= modReturn prev) `mplus`
                     (m2 >>= modReturn prev) `mplus`
                     (m3 >>= modReturn prev)) {-"~~,"-}
\end{spec}
which, with a shared state, means that |m2| starts with state |st|, after which the state is rolled back too early to |prev st|. The computation |m3| starts with |prev st|, after which the state is rolled too far to |prev (prev st)|.

In fact, one cannot guarantee that |modReturn prev| is always executed --- if |solve| fails, we get |modify next >> solve >>= modReturn prev| |= modify next >> mzero >>= modReturn prev = modify next >> mzero|. Thus the state is advanced to |next st|, but not rolled back to |st|.

We need a way to say that ``|modify next| and |modReturn prev| are run exactly once, respectively before and after all non-deterministic branches in |solve|.'' Fortunately, for the purpose of this pearl, there is a curious technique. Define
\begin{spec}
side :: N `mem` eps => Me eps a -> Me eps b
side m = m >> mzero {-"~~."-}
\end{spec}
%if False
\begin{code}
side :: MonadPlus m => m a -> m b
side m = m >> mzero {-"~~."-}
\end{code}
%endif
Since non-deterministic branches are executed sequentially, the program
\begin{spec}
side (modify next) `mplus` m1 `mplus` m2 `mplus` m3 `mplus` side (modify prev)
\end{spec}
executes |modify next| and |modify prev| once, respectively before and after all the non-deterministic branches, even if they fail. Note that |side m| does not generate a result. Its presence is merely for the side-effect of |m|, hence the name. Note also that the type of |side m| need not be the same as that of |m|.

\paragraph{Properties} In absence of \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero}, we instead assume the following properties.
\begin{align}
  |side m1 `mplus` side m2| &= |side (m1 >> m2)| \mbox{~~,}
    \label{eq:side-side} \\
  |put s >> (m1 `mplus` m2)| &= |(put s >> m1) `mplus` m2| \mbox{~~,}
    \label{eq:put-mplus}\\
  |get >>= (\x -> f x `mplus` m)| &=~ |(get >>= f) `mplus` m| \mbox{~~, |x| not free in |m|,}
      \label{eq:get-mplus}\\
  |(put s >> return x) `mplus`  m| &= |return x `mplus` (put s >> m)| ~~\mbox{,}
      \label{eq:put-ret-side}\\
  |side m `mplus` n| &=~ |n `mplus` side m| \mbox{~~, for |m :: Me N a|.}
        \label{eq:side-nd-mplus}
\end{align}
%if False
\begin{code}
propSideSide m1 m2 = (side m1 `mplus` side m2) === side (m1 >> m2)
propPutMPlus s m1 m2 = (put s >> (m1 `mplus` m2)) === ((put s >> m1) `mplus` m2)
propGetMPlus f m = (get >>= (\x -> f x `mplus` m)) === ((get >>= f) `mplus` m)
propPutRetSide s x m = ((put s >> return x) `mplus`  m) === (return x `mplus` (put s >> m))
propSideNdMPlus m n = (side m `mplus` n) === (n `mplus` side m)
\end{code}
%endif
They all show the sequential nature of |mplus| in this setting: in \eqref{eq:side-side}, adjacent |side| commands can be combined; in \eqref{eq:put-mplus} and \eqref{eq:get-mplus}, state operators bound before |mplus| branches can be bound to the leftmost branch, and in \eqref{eq:put-ret-side}, the effect of |put s >> return x| can be moved to the next branch. Finally, \eqref{eq:side-nd-mplus} allows side effects to commute with branches that only returns non-deterministic results.
By \eqref{eq:side-side} we have
\begin{equation}
 |side (put s) `mplus` side (put t) = side (put t)| \mbox{~~.}
  \label{eq:side-put-put}
\end{equation}
While we do not have right-distributivity in general, we may still assume distributivity for specific cases:
\begin{align}
 |get >>= \s -> f1 s `mplus` f2 s| &=~ |(get >>= f1) `mplus` (get >>= f2)| \mbox{~~, if |f1 s :: Me N a|}
    \label{eq:get-mplus-distr}\\
 |get >>= \s -> f1 s `mplus` f2 s| &=~ |(get >>= (\s -> f1 s `mplus` side (put s))) `mplus` (get >>= f2)| \mbox{~~.}
      \label{eq:get-mplus-side-distr}
\end{align}
%if False
\begin{code}
propGetMPlusDistr f1 f2 = (get >>= \x -> f1 x `mplus` f2 x) === ((get >>= f1) `mplus` (get >>= f2))
propGetMPlusSideDistr f1 f2 = (get >>= \x -> f1 x `mplus` f2 x) === ((get >>= (\x -> f1 x `mplus` side (put x))) `mplus` (get >>= f2))
\end{code}
%endif
Property \eqref{eq:get-mplus-distr} allows right-distributivity of |get| if the branches are only non-deterministic.
It helps to prove that |get| commutes with non-determinism.
In general cases, we need a |side (put x)| in the first branch to ensure that the second branch gets the correct value, as in \eqref{eq:get-mplus-side-distr}.

\subsection{State-Restoring Programs}
\label{sec:state-restoring}

In this section we present an interesting programming pattern that exploits left-distributivity \eqref{eq:bind-mplus-dist}.
Define the following variation of |put|:%
\footnote{The author owes the idea of |putR| to Tom Schrijvers. See Section \ref{sec:conclusion} for more details.}
\begin{spec}
putR :: {S s, N} `sse` eps => s -> Me eps ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}
\end{spec}
%if False
\begin{code}
putR :: (MonadPlus m, MonadState s m) => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}
\end{code}
%endif
and consider |putR s >> comp| where |comp| is some arbitray computation:
%if False
\begin{code}
putRExplain :: (MonadPlus m, MonadState s m) => s -> m b -> m b
putRExplain s comp =
\end{code}
%endif
\begin{code}
      putR s >> comp
 ===  (get >>= \s0 -> put s `mplus` side (put s0)) >> comp
 ===    {- monad law, left-distributivity \eqref{eq:bind-mplus-dist} -}
      get >>= \s0 -> (put s >> comp) `mplus` (side (put s0) >> comp)
 ===    {- by \eqref{eq:bind-mzero-zero}, |mzero >> comp = mzero| -}
      get >>= \s0 -> (put s >> comp) `mplus` side (put s0) {-"~~."-}
\end{code}
Thanks to left-distributivity \eqref{eq:bind-mplus-dist}, |(>> comp)| is promoted into |mplus|.
Furthermore, the |(>> comp)| after |side (put s0)| is discarded by
\eqref{eq:bind-mzero-zero}.
In words, |putR s >> comp| saves the current state, computes |comp| using state |s|, and restores the saved state, hence the subscript |R| in its name.

It might be instructive comparing |return x|, |m1 = put s >> return x|, and |m2 = putR s >> return x|, when run in initial state |s0|.
They all yield |x| as the result.
Certainly, |return x| terminates with state |s0|, and |m1| terminates with state |s|.
The program |m2| also terminates with state |s0|. However, |m2| does {\em not} equal |return x|!
There exist contexts, for example |(>>= f)|, with which we can tell them apart: in |return x >>= f|, |f| runs with state |s0|, while in |putR s >> return x >>= f|, |f| runs with state |s|, even though the program yields final state |s0|.

\begin{lemma}\label{lma:putR-basics}
The following laws regarding |putR| are true:
\begin{align*}
    |putR s >>= get| ~&=~ |putR s >>= return s| \mbox{~~,} \\
    |putR s >> putR s'| ~&=~ |putR s'|  \mbox{~~.}
\end{align*}
\end{lemma}

\begin{lemma}\label{lma:putR-nd-commute}
|putR| commutes with non-determinism. That is, |m >>= \x -> putR s >> return x = putR s >> m| for |m :: Me N a|.
\end{lemma}

Proof of Lemma \ref{lma:putR-basics} is a routine exercise. Lemma \ref{lma:putR-nd-commute} can be proved by induction on the syntax of |m|, using properties including \eqref{eq:side-side}, \eqref{eq:put-ret-side}, \eqref{eq:side-nd-mplus}, and \eqref{eq:get-mplus-side-distr}.

% \begin{proof}
% We present the proof for the |putR|-|putR| law for illustrative purpose. The proof demonstrates the use of \eqref{eq:put-mplus} and \eqref{eq:side-put-put}.
% \begin{spec}
%    putR s >> putR s'
% =  (get >>= \s0 -> (put s `mplus` side (put s0))) >>
%    (get >>= \s0 -> (put s' `mplus` side (put s0)))
% =    {- left-distributivity \eqref{eq:bind-mplus-dist} -}
%    get >>= \s0 -> (put s >> get >>= \s0 -> (put s' `mplus` side (put s0))) `mplus` side (put s0)
% =    {- |put|-|get| \eqref{eq:get-put} -}
%    get >>= \s0 -> (put s >> (put s' `mplus` side (put s))) `mplus` side (put s0)
% =    {- by \eqref{eq:put-mplus} -}
%    get >>= \s0 -> (put s >> puts') `mplus` side (put s) `mplus` side (put s0)
% =    {- |put|-|put| \eqref{eq:put-put} and \eqref{eq:side-put-put} -}
%    get >>= \s0 -> put s' `mplus` side (put s0)
% =  putR s' {-"~~."-}
% \end{spec}
% \end{proof}
Note that we do not have a |get|-|putR| law: |get >>= putR| does not equal |return ()|. To see that, observe that |(get >>= putR) >> put t| terminates with the initial state, while |return () >> put t| terminates with state |t|.

\paragraph{State-Restoration, Compositionally} Pushing the idea a bit further, we say that a monadic program |m| is {\em state-restoring} if, for all |comp|, the initial state in which |m >>= comp| is run is always restored when the computation finishes. Formally, it can be written as:
\begin{definition} |m :: {N, S s} `sse` eps => Me eps a| is called {\em state-restoring} if
  |m = get >>= \s0 -> m `mplus` side (put s0)|.
\end{definition}
Certainly, |putR s| is state-restoring. In fact, state-restoring programs can be built compositionally, using the following properties:
\begin{lemma} We have that
\begin{enumerate}
\item |mzero| is state-restoring,
\item |putR s| is state-restoring,
\item |guard p >> m| is state-restoring if |m| is,
\item |get >>= f| is state-restoring if |f x| is state-storing for all |x|, and
\item |m >>= f| is state restoring if |m| is state-restoring.
\end{enumerate}
\end{lemma}
Proof of these properties are routine exercises.

\paragraph{Incremental Updating and Restoration}
Identifying state-restoring programs helps to discover when we can update and restore the state in an incremental manner.
When the state |s| is a big structure, such as an array, it might not be feasible to perform |put s| that rewrites an entire array.
Instead one might use another command |modify f| that applies the function |f| to the state. It can be characterised by:
\begin{spec}
  modify f = get >>= \s -> put (f s) {-"~~,"-}
\end{spec}
but one may assume that, for commands such as |modify (\arr -> arr // [(i,x)])| (where |(// [(i,x)])| updates the |i|-th entry of the array to |x|), there exists a quicker implementation that mutates the array rather than creating a new array.

Given a function |next :: s -> s| that alters the state, and |prev :: s -> s| that is the inverse of |next|, we define the following state-restoring variation of |modify|:
\begin{spec}
modifyR :: {N, S s} `sse` eps -> (s -> s) -> (s -> s) -> Me eps ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{spec}
%if False
\begin{code}
modifyR :: (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{code}
%endif
such that |modifyR next prev >> comp| performs |modify next| before computation in |comp|, and |modify prev| afterwards. We have that:
\begin{lemma} Let |next| and |prev| be such that |prev . next = id|.
If |m| is state-restoring, we have
%if False
\begin{code}
putRSRModifyR ::
  (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m b -> m b
putRSRModifyR next prev m =
\end{code}
%endif
\begin{code}
  get >>= \s -> putR (next s) >> m {-"~~"-}=== {-"~~"-}
    modifyR next prev >> m {-"~~."-}
\end{code}
\end{lemma}
We look at its proof, which demonstrates the use of \eqref{eq:side-side} -- \eqref{eq:get-mplus}, monad laws, and laws regarding |get| and |put|.
For the rest of this pearl we use the following abbreviations:
\begin{code}
sidePut st  = side (put st)    {-"~~,"-}
sideMod f   = side (modify f)  {-"~~."-}
\end{code}
\begin{proof} We calculate:
%if False
\begin{code}
putRSRModifyRDer1 ::
  (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m b -> m b
putRSRModifyRDer1 next prev m =
\end{code}
%endif
\begin{code}
      modifyR next prev >> m
 ===    {- definiton of |modifyR|, |modify|, and left-distributivity \eqref{eq:bind-mplus-dist} -}
      (get >>= \s -> put (next s) >> m) `mplus` sideMod prev
 ===    {- by \eqref{eq:get-mplus} -}
      get >>= \s -> (put (next s) >> m) `mplus` sideMod prev {-"~~."-}
\end{code}
We focus on the part within |(get >>= \s -> _)|:
%if False
\begin{code}
putRSRModifyRDer2 ::
  (MonadPlus m, MonadState s m) =>
  (s -> s) -> (s -> s) -> s -> m a -> m a
putRSRModifyRDer2 next prev s m =
\end{code}
%endif
\begin{code}
      (put (next s) >> m) `mplus` sideMod prev
 ===    {- |m| state-restoring -}
      (put (next s) >> get >>= \s' -> m `mplus` sidePut s') `mplus` sideMod prev
 ===    {- |put|-|get| \eqref{eq:get-put} -}
      (put (next s) >> (m `mplus` sidePut (next s))) `mplus` sideMod prev
 ===    {- by \eqref{eq:put-mplus} -}
      put (next s) >> (m `mplus` sidePut (next s) `mplus` sideMod prev)
 ===    {- by \eqref{eq:side-side}, and |prev . next = id| -}
      put (next s) >> (m `mplus` sidePut s)
 ===    {- by \eqref{eq:put-mplus} -}
      (put (next s) >> m) `mplus` sidePut s {-"~~."-}
\end{code}
Put it back to the context |(get >>= \s -> _)|, and the expression simplifies to |get >>= \s -> putR (next s) >> m|.
\end{proof}
