%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances #-}
module Background ( MNondet(..), MState(..), MStateNondet(..),
                    module ControlMonad) where

import Control.Monad as ControlMonad hiding (mzero, mplus, guard)
import Control.Arrow ((***))
\end{code}
%endif

\section{Background}
\label{sec:background}
This section briefly summarises the main concepts we need for equational
reasoning about effects.
For a more extensive treatment we refer to the work of Gibbons and Hinze
\cite{GibbonsHinze:11:Just}.

\subsection{Monads, Nondeterminism and State}
\paragraph{Monads}
A monad consists of a type constructor |M :: * -> *| and two operators |return :: a -> M s a| and ``bind'' |(>>=) :: M s a -> (a -> M b) -> M b| that satisfy the following {\em monad laws}:
\begin{align}
  |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
We also define |m1 >> m2 = m1 >>= \ _ -> m2|,
which has type |(>>) :: m a -> m b -> m b|, and |f <$> m = m >> (return . f)|
which applies a pure function to a monadic value.
%if False
\begin{code}
(>>) :: Monad m => m a -> m b -> m b
m1 >> m2 = m1 >>= const m2
\end{code}
%endif

\paragraph{Nondeterminism}
The first effect we introduce is nondeterminism.
Following the trail of Hutton and Fulger \cite{HuttonFulger:08:Reasoning} and
Gibbons and Hinze, we introduce effects
based on an axiomatic characterisation (a set of laws that govern how the effect
operators behave with respect to one another) rather than a specific implementation.
We define a type class to capture this interface as follows:
\begin{code}
class Monad m => MNondet m where
    mzero  :: m a
    mplus  :: m a -> m a -> m a {-"~~."-}
\end{code}
In this interface, |mzero|
denotes failure, while |m `mplus` n| denotes that the computation may yield
either |m| or |n|.
Precisely what
laws these operators should satisfy, however, can be a tricky issue.
As discussed by Kiselyov~\cite{Kiselyov:15:Laws}, it eventually comes down to
what we use the monad for.

It is usually expected that |mplus| and |mzero| form a monoid. That
is, |mplus| is associative, with |mzero| as its zero:
\begin{align}
|(m `mplus` n) `mplus` k|~ &=~ |m `mplus` (n `mplus` k)| \mbox{~~,}
  \label{eq:mplus-assoc}\\
|mzero `mplus` m| ~=~ & |m| ~=~ |m `mplus` mzero| \mbox{~~.}
  \label{eq:mzero-mplus}
\end{align}

It is also assumed that monadic bind distributes into |mplus| from the end,
while |mzero| is a left zero for |(>>=)|:
\begin{alignat}{2}
  &\mbox{\bf left-distributivity}:\quad &
  |(m1 `mplus` m2) >>= f| ~&=~ |(m1 >>= f) `mplus` (m2 >>= f)| \mbox{~~,}
  \label{eq:bind-mplus-dist}\\
  &\mbox{\bf left-zero}:\quad &
  |mzero >>= f| ~&=~ |mzero| \label{eq:bind-mzero-zero} \mbox{~~.}
\end{alignat}
We will refer to the laws \eqref{eq:mplus-assoc}, \eqref{eq:mzero-mplus},
\eqref{eq:bind-mplus-dist}, \eqref{eq:bind-mzero-zero} collectively as the
\emph{nondeterminism laws}.

One might might intuitively expect some additional laws from a set of non-determinism
operators, such as idempotence (|p `mplus` p = p|) or
commutativity (|p `mplus` q = q `mplus` p|).
However, our primary interest lies in the study of combinations of effects and
-- as we shall see very soon -- in particular the combination of nondeterminism with
\emph{state}.
One of our characterisations of this interaction would be incompatible with both
idempotence and commutativity, at least if they are stated as strongly as we
have done here. We will eventually introduce a weaker notion of commutativity,
but it would not be instructive to do so here (as its properties would be
difficult to motivate at this point).

\paragraph{State}
The state effect provides two operators:
\begin{code}
class Monad m => MState s m | m -> s where
    get  :: m s
    put  :: s -> m () {-"~~."-}
\end{code}
The |get| operator retrieves the state, while |put| overwrites the state by the given value.
They are supposed to satisfy the \emph{state laws}:
\begin{alignat}{2}
&\mbox{\bf put-put}:\quad &
|put st >> put st'| &= |put st'|~~\mbox{,} \label{eq:put-put}\\
&\mbox{\bf put-get}:~ &
|put st >> get| &= |put st >> return st| ~~\mbox{,} \label{eq:get-put}\\
&\mbox{\bf get-put}:~ &
|get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
&\mbox{\bf get-get}:\quad &
|get >>= (\st -> get >>= k st)| &= |get >>= (\st -> k st st)|
~~\mbox{.} \label{eq:get-get}
\end{alignat}

\subsection{Combining Effects}
\label{sec:combining-effects}
As Gibbons and Hinze already noted, an advantage of defining our effects
axiomatically, rather than by providing some concrete implementation, is that it
is straightforward to reason about combinations of effects.
In this paper, we are interested in the interaction between nondeterminism and
state, specifically.
\begin{code}
class (MState s m, MNondet m) => MStateNondet s m | m -> s {-"~~."-}
\end{code}
The type class |MStateNondet s m| simply inherits the operators of its
superclasses |MState s m| and |MNondet m| without adding new operators, and
implementations of this class should comply with all laws of both superclasses.

However, this is not the entire story. Without additional `interaction laws',
the design space for implementations of this type class is left wide-open with
respect to questions about how these effects interact.
In particular, it seems hard to imagine that one could write nontrivial programs
which are agnostic towards the question of what happens to the state of the
program when the program backtracks.
We discuss two possible approaches.

\paragraph{Local State Semantics}
One is what Gibbons and Hinze call ``backtrackable state'', that is, when a
branch of the nondeterministic computation runs into a dead end and the
continuation of the computation is picked up at the most recent branching point,
any alterations made to the state by our terminated branch are invisible to the
continuation.
Because in this scheme state is local to a branch, we will refer to these
semantics as \emph{local state semantics}.
We characterise local state semantics with the following laws:
\begin{alignat}{2}
&\mbox{\bf right-zero}:~&
  |m >> mzero|~ &=~ |mzero| ~~\mbox{~~,}
    \label{eq:mzero-bind-zero}\\
&\mbox{\bf right-distributivity}:~&
  |m >>= (\x -> f1 x `mplus` f2 x)| &= |(m >>= f1) `mplus` (m >>= f2)| \mbox{.}
    \label{eq:mplus-bind-dist}
\end{alignat}
With some implementations of the monad, it is likely that in the lefthand side of \eqref{eq:mplus-bind-dist}, the effect of |m| happens once, while in the righthand side it happens twice. In \eqref{eq:mzero-bind-zero}, the |m| on the lefthand side may incur some effects that do not happen in the righthand side.

Having \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} leads to profound consequences on the semantics and implementation of monadic programs.
To begin with, \eqref{eq:mplus-bind-dist} implies that for |mplus| we have some
limited notion of commutativity.
For instance, both the left and right distributivity rules can be applied to
the term |(return x `mplus` return y) >>= \z -> return z `mplus` return z|.
It is then easy to show that this term must be equal to both
|return x `mplus` return x `mplus` return y `mplus` return y| and
|return x `mplus` return y `mplus` return x `mplus` return y|.%
\footnote{
  Gibbons and Hinze~\cite{GibbonsHinze:11:Just} were mistaken in their claim
  that the type |s -> [(a,s)]| constitutes a model of their backtrackable state
  laws; it is not a model because its |mplus| does not commute with itself.
  One could consider a relaxed semantics that admits |a -> [(a,s)]|, but that is
  not the focus of this paper.
}
%Implementations of such non-deterministic monads have been studied by
%Fischer~\cite{Fischer:11:Purely}.
%\scm{Removed this citation --- I don't think it is that necessary now that we mention Bags in the next paragraph.}

% Law~\eqref{eq:mzero-bind-zero} implies that when an effectful computation |m|
% is followed by a |mzero|, then the computation |m| might as well never have
% happened. In particular, |put s >> mzero| is equal to |mzero|, which matches our
% intuition about local (or backtrackable) state (whereas it clearly does not hold
% for non-backtrackable semantics).
% Law~\eqref{eq:mplus-bind-dist} also only holds for some monads with
% nondeterminism. The fact that sequentially composing a computation |m| with a
% nondeterministically chosen continuation might duplicate |m| (and therefore the
% effects of |m|) corresponds to our intuition for backtrackable state, but not for
% non-backtrackable state or other irriversible effects.

These requirements imply that each nondeterministic branch has its own copy of
the state.
One implementation satisfying the laws is |M s a = s -> Bag (a,s)|, where
|Bag a| is an implementation of a multiset or ``bag'' data structure.
If we ignore the unordered nature of the |Bag| type, this implementation is
similar to |StateT s (ListT Identity)| in the Monad Transformer
Library~\cite{MTL:14}. With effect
handling~\cite{Wu:14:Effect,KiselyovIshii:15:Freer}, the monad behaves similarly
(except for the limited commutativity implied by
law~\eqref{eq:mplus-bind-dist}) if we run the handler for state before that for
list.

\paragraph{Global State Semantics}
Alternatively, we can choose a semantics where state reigns over nondeterminism.
In this case of non-backtrackable state, alterations to the state persist over
backtracks.
Because only a single state is shared over all the branches of the
nondeterministic computation, we call this semantics \emph{global state semantics}.
We will return later to the question of how to define laws that capture our
intuition for this kind of semantics, because (to the best of our knowledge)
this constitutes a novel contribution.

Even just figuring out an implementation of a global state monad that matches
our intuition is already a bit tricky.
One might believe that |M s a = s -> ([a],s)| is a natural implementation of such a monad.
The usual, naive implementation of |(>>=)| using this representation, however, does not satisfy left-distributivity \eqref{eq:bind-mplus-dist}, violates monad laws, and is therefore not even a monad.
%See Section \ref{sec:conclusion} for previous work on construction of a correct monad.
The type |ListT (State s)| generated using the Monad Transformer Library~\cite{MTL:14} expands to essentially the same implementation, and is flawed in the same way.
More careful implementations of |ListT|, which do satisfy \eqref{eq:bind-mplus-dist} and the monad laws, have been proposed~\cite{Gale:07:ListT,Volkov:14:list-t}.
Effect handlers (e.g. Wu~\cite{Wu:14:Effect} and Kiselyov and
Ishii~\cite{KiselyovIshii:15:Freer}) do produce implementations which match our
intuition of a non-backtracking computation if we run the handler for
non-determinism before that of state.

We provide a direct implementation to aid the intuition of the reader.
Essentially the same implementation is obtained by using the type
|ListT (State s)| where |ListT| is implemented as a correct monad transformer.
This implementation has a non-commutative |mplus|.
\begin{spec}
M s a = s -> (Maybe (a, M s a), s) {-"~~."-}
\end{spec}
The |Maybe| in this type indicates that a computation might fail to produce a
result. But note that the |s| is outside of the |Maybe|: even if the computation
fails to produce any result, a modified state may be returned (this is different
from local state semantics).
|mzero|, of course, returns an empty continuation (|Nothing|) and an unmodified
state. |mplus| first exhausts the left branch (always collecting any state
modifications it performs), before switching to the right branch.
\begin{spec}
  mzero        = \s -> (Nothing, s) {-"~~,"-}
  p `mplus` q  = \s -> case p s of  (Nothing      , t) -> q t
                                    (Just (x, r)  , t) -> (Just (x, r `mplus` q), t) {-"~~."-}
\end{spec}
The state operators are implemented in a straightforward manner.
\begin{spec}
  get    = \s  -> (Just (s   , mzero)   , s) {-"~~,"-}
  put s  = \t  -> (Just (()  , mzero)   , s) {-"~~."-}
\end{spec}
And this implementation is also a monad. The implementation of |p >>= k| extends
every branch within |p| with |k|, threading the state through this entire process.
\begin{spec}
  return x  = \s -> (Just (x, mzero), s) {-"~~,"-}
  p >>= k   = \s -> case p s of  (Nothing      , t)  ->  (Nothing, t)
                                 (Just (x, q)  , t)  ->  (k x `mplus` (q >>= k)) t {-"~~."-}
\end{spec}

%if False
\begin{code}
data G s a = G {unG :: s -> (Maybe (a, G s a), s)}

instance Applicative (G s) where
  pure = return
  mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)

instance Functor (G s) where
  fmap f (G m) = G ((fmap (f *** fmap f) *** id) . m)

instance Monad (G s) where
  return x  = G (\s -> (Just (x, mzero), s))
  G p >>= k = G (\s -> case p s of
                         (Nothing      , t)  ->  (Nothing, t)
                         (Just (x, q)  , t)  ->  unG (k x `mplus` (q >>= k)) t)

instance MNondet (G s) where
  mzero        = G (\s -> (Nothing, s))
  p `mplus` q  = G (\s -> case unG p s of
                            (Nothing      , t) -> unG q t
                            (Just (x, r)  , t) -> (Just (x, r `mplus` q), t))

instance MState s (G s) where
  get    = G (\s  -> (Just (s   , mzero)   , s))
  put s  = G (\t  -> (Just (()  , mzero)   , s))
\end{code}
%endif
