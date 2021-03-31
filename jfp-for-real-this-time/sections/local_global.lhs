\section{Modeling Local State With Global State}
\label{sec:local-global}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module LocalGlobal where

import Background hiding (hNondet)
import Control.Monad (ap)
import Control.Arrow ((***))

\end{code}
%endif

Intro. Difference between local state and global state e.g.

%-------------------------------------------------------------------------------
\subsection{Local-State Semantics}
\label{sec:local-state}

One is what Gibbons and Hinze call ``backtrackable state''.
When a branch of a nondeterministic computation runs into a dead end and 
the continuation is picked up at the most recent branching point,
any alterations made to the state by the terminated branch are invisible to 
the continuation.
In this scheme state is local to a branch.
Therefore, we refer to these semantics as \emph{local-state semantics}. 

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Interaction Laws}
The following laws characterize the local state semantics for a monad |m|
with state and nondeterminism:
\begin{alignat}{2}
    &\mbox{\bf right-identity}:\quad &
    |m >> mzero| &= |mzero|~~\mbox{,} \label{eq:right-identity}\\
    &\mbox{\bf left-distributivity}:~ &
    |m >>= (\x -> f1 x `mplus` f2 x)| &= |(m >>= f1) `mplus` (m >>= f2)| ~~\mbox{.} \label{eq:left-dist}
\end{alignat}
The monad on the lefthand side in the right-identity law (\ref{eq:right-identity})
may incur some effects that do not happen in the righthand side.
Similarly, in the left-distributivity law (\ref{eq:left-dist}), 
for some implementations of |m|, 
the effect of the monad may happen once on the lefthand side and twice on the 
righthand side.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Commutativity}
Having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) leads to profound 
consequences on the semantics and implementation of monadic programs.
To begin with, (\ref{eq:left-dist}) implies that for |mplus| we have some limited
notion of commutativity. 
For instance, both the left and right distributivity rules can be applied to the 
term |(return x `mplus` return y) >>= \z -> return z `mplus` return z|.
It is then easy to show that this term must be equal to both
|return x `mplus` return x `mplus` return y `mplus` return y|
and 
|return x `mplus` return y `mplus` return x `mplus` return y|
\footnote{Gibbons and Hinze \cite{} were mistaken in their claim that the type
|s -> [(a, s)]| constitutes a model of their backtrackable state laws.
It is not a model because its |`mplus`| does not commute with itself.
One could consider a relaxed semantics that admits |s ->[(a, s)]|, 
but that is not the focus of this paper.}.
In fact, having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) gives us very 
strong and useful commutative properties.

\begin{definition}[Commutativity]
Let |m| and |n| be two monadic programs such that |x| does not occur free in |m|,
and |y| does not occur free in |n|. We say |m| and |n| commute if 
\begin{alignat}{2}
    &\mbox{\bf commutativity}:\quad &
    |m >>= \x -> n >>= \y -> f x y| &= |n >>= \y -> m >>= \x -> f x y|~~\mbox{.} \label{eq:commutativity}
\end{alignat}
We say that effects |eps| and |delta| commute if any |m| and |n| commute
as long as their only effects are |eps| and |delta|.
\end{definition}

One important result is that, in local-state semantics, nondeterminism commutes
with any effect. 

\begin{theorem}
If right-identity (\ref{eq:right-identity}) 
and left-distributivity (\ref{eq:left-dist}) hold in addition to the other laws,
nondeterminism commutes with any effect.
\end{theorem}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Implementation}
Implementation-wise, (\ref{eq:right-identity}) and (\ref{eq:left-dist}) 
imply that each nondeterministic branch has its own copy of the state. 
To see that, let |m = put 1|, |f1 () = put 2| and |f2 () = get| in 
(\ref{eq:left-dist}). The state we |get| in the second branch does not change, 
despite the |put 2| in the first branch.
One implementation satisfying the laws is 
< Local s a = s -> Bag (a, s)
where |Bag a| is an implementation of a multiset or ``bag'' datastructure.
If we ignore the unordered nature of the |Bag| type, this implementation is 
similar to |StateT s (ListT Identity)| in the Monad Transformer Library \cite{}.
With effect handling \cite{}, the monad behaves similarly
(except for the limited commutativity implied by law (\ref{eq:left-dist}))
if we run the handler for state before that for list.


%-------------------------------------------------------------------------------
\subsection{Global-State Semantics}
\label{sec:global-state}

Alternatively, one can choose a semantics where state reigns over nondeterminism.
In this case of non-backtrackable state, alterations to the state persist over
backtracks. Because only a single state is shared over all branches of 
nondeterministic computation, we call this state the \emph{global-state 
semantics}. 
\todo{}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Implementation}
Figuring out an implementation that matches our intuition about the global-state
monad is tricky. One might believe that
< Global s a = s -> ([a], s)
is a natural implementation of such a monad. 
However, the usual, naive implementation of |(>>=)| does not satisfy right 
distributivity (\ref{eq:mplus-dist}), violates monad laws and is therefore not
even a monad. 
The type |ListT (State s)| from the Monad Transformer Library \cite{}
expands to essentially the same implementation, with the same flaws.
More careful implementations of |ListT|, that do satisfy right distributivity
(\ref{eq:mplus-dist}) and the monad laws have been proposed by \todo{} \cite{}.
Effect handlers \cite{} produce implementations that match our intuition of 
non-backtrackable computations if we run the handler for nondeterminism before
that of state. 
The following implementation is correct and has a non-commutative |`mplus`|.
\begin{code}
newtype Global s a = Gl { runGl :: s -> (Maybe (a, Global s a), s) }
\end{code} 
The |Maybe| in this type indicates that a computation might fail to produce a
result. However, since the |s| is outside of the |Maybe|, a modified state 
might be returned even if the computation failed.
This |Global s a| type is an instance of the |MStateNondet| monad.

%if False
\begin{code}
instance Functor (Global s) where
    fmap f p = Gl ((fmap (f *** fmap f) *** id) . runGl p)

instance Applicative (Global s) where
    pure = return
    (<*>) = ap

instance Monad (Global s) where
    return x = Gl (\s -> (Just (x, mzero), s))
    p >>= k = Gl (\s -> case runGl p s of 
        (Nothing, t) -> (Nothing, t)
        (Just (x, q), t) -> runGl (k x `mplus` (q >>= k)) t
        )
\end{code}
%endif 

|mzero|, of course, returns an empty continuation and an unmodified state.
|mplus| first exhausts the left branch before switching to the right branch.

\begin{code}
instance MNondet (Global s) where
    mzero        = Gl   (\s ->  (Nothing, s))
    p `mplus` q  = Gl   (\s ->  case runGl p s of
        (Nothing,      t)   ->   runGl q t
        (Just (x, r),  t)   ->   (Just (x, r `mplus` q), t))

instance MState s (Global s) where
    get    =  Gl  (\s  ->  (Just (s,   mzero),   s))
    put s  =  Gl  (\_  ->  (Just ((),  mzero),   s))
\end{code}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{The Global-State Law}
The global-state law characterizes the property that sets apart 
non-backtrackable state from backtrackable state. 

In addition to the general laws for nondeterminism 
((\ref{eq:mzero}) -- (\ref{eq:mzero-zero})) and state
((\ref{eq:put-put}) -- (\ref{eq:get-get})), we provide a \emph{global-state law}
to govern the interaction between nondeterminism and state. 
\begin{alignat}{2}
    &\mbox{\bf put-or}:\quad &
    |(put s >> m) `mplus` n| &= |put s >> (m `mplus` n)|~~\mbox{.} \label{eq:put-or}
\end{alignat}

This law allows the lifting of a |put| operation from the left branch of a 
nondeterministic choice.
For instance, if |m = mzero| in the left-hand side of the equation, 
then under local-state semantics 
(laws (\ref{eq:mzero}) and (\ref{eq:right-identity})) 
the lefthand side becomes equal to |n|, 
whereas under global-state semantics 
(laws (\ref{eq:mzero}) and (\ref{eq:put-or}))
the equation simplifies to |put s >> n|.

By itself, this law leaves us free to choose from a large space of 
implementations with different properties. 
For example, in any given implementation, the programs 
|return x `mplus` return y| and |return y `mplus` return x| can be considered
either semantically identical or distinct.
The same goes for the programs |return x `mplus` return x| and |return x|
or other examples.
\todo{sth about S5.2 original paper}


\begin{itemize}
    \item chaining using nondeterministic choice??
    \item state-restoring operations
\end{itemize}

%-------------------------------------------------------------------------------
\subsection{Laws and Translation for the Global State Monad}
\label{sec:translation}


\begin{itemize}
    \item syntax
    \item semantics with example
    \item laws
    \item contextual equivalence
    \item simulating local state semantics
    \item backtracking with global state

\end{itemize}

