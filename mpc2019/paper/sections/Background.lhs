\section{Background}
This section briefly summarises the main concepts we need for equational
reasoning about effects.
For a more extensive treatment we refer to the work of Gibbons and Hinze
\cite{GibbonsHinze:11:Just}.

\subsection{Monads, Nondeterminism and State}
\paragraph{Monads}
A monad consists of a type constructor |M :: * -> *| and two operators |return :: a -> M a| and ``bind'' |(>>=) :: M a -> (a -> M b) -> M b| that satisfy the following {\em monad laws}:
\begin{align}
  |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
We also define |m1 >> m2 = m1 >>= const m2|, which has type |(>>) :: m a -> m b -> m b|.

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
    mplus  :: m a -> m a -> m a
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
Other properties regarding |mzero| and |mplus| will be introduced when needed.

\paragraph{State}
The state effect provides two operators:
\begin{code}
  class Monad m => MState s m | m -> s where
    get  :: m s
    put  :: s -> m ()
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
  class (MState s m, MNondet m) => MStateNondet s m | m -> s
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
&\mbox{\bf right-zero}:\quad&
  |m >> mzero|~ &=~ |mzero| ~~\mbox{~~,}
    \label{eq:mzero-bind-zero}\\
&\mbox{\bf right-distributivity}:\quad&
  |m >>= (\x -> f1 x `mplus` f2 x)|~ &=~ |(m >>= f1) `mplus` (m >>= f2)| \mbox{~~.}
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
|return x `mplus` return y `mplus` return x `mplus` return y|.
\footnote{
  This also means that
  Gibbons and Hinze~\cite{GibbonsHinze:11:Just} were mistaken in their claim
  that the type |s -> [(a,s)]| constitutes a model of their backtrackable state
  laws.
  Law~\eqref{eq:mplus-bind-dist} is actually too strong to
  characterise all reasonable implementations of backtrackable state, but we
  will stick to this characterisation in our paper.}
Implementations of such non-deterministic monads have been studied by
Fischer~\cite{Fischer:11:Purely}.

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