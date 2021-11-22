
%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

module Overview where

import Background
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.List

import Debug.Trace as DT

\end{code}
%endif

\section{Overview}
\label{sec:overview}

This section gives an overview of our approach to simulate state and
nondeterminism in terms of only state and of how to prove that approach
correct.

%-------------------------------------------------------------------------------
\subsection{Approach}

Although the second implementation of the n-queens problems is a noteworthy
improvement over the naive version by cleverly interleaving enumeration and
validation, it requires problem-specific knowledge. We can also make
application-agnostic improvements at the more generic level of the effect
implementation.

For example, we could avoid making an explicit copy of the state at every branching
point by evolving from local-state semantics to global-state semantics.
Furthermore, we can model nondeterminism with state, which allows for a smoother
undo semantics.
Mutable state would also improve performance significantly.

In the remainder of the paper, we define simulations for transforming
high-level effects into lower-level effects that enable the above optimizations and
establish the correctness of this approach.

In particular, we take the following steps:
\Cref{sec:local-global} simulates local state with global state;
\Cref{sec:nondeterminism-state} explains how to simulate nondeterminism with state; and
\Cref{sec:combination} shows how we can group multiple states into a single
state effect.

The figure below shows how this influences the n-queens example in the different sections.

% https://q.uiver.app/?q=WzAsMyxbMCwwLCJTdGF0ZSArIE5vbmRldGVybWluaXNtIl0sWzAsMSwiU3RhdGUgKyBTdGF0ZSJdLFswLDIsIlN0YXRlIl0sWzAsMSwiU2VjdGlvbiBcXHJlZnt9OiBOb25kZXRlcm1pbmlzbSAkXFxyaWdodGFycm93JCBTdGF0ZSIsMCx7ImxhYmVsX3Bvc2l0aW9uIjozMH1dLFsxLDIsIlNlY3Rpb24gXFxyZWZ7fSJdLFswLDEsIlNlY3Rpb24gXFxyZWZ7fTogTG9jYWwgc3RhdGUgJFxccmlnaHRhcnJvdyQgZ2xvYmFsIHN0YXRlIiwwLHsibGFiZWxfcG9zaXRpb24iOjcwfV1d
% \[\begin{tikzcd}
%   {\text{State + Nondeterminism}} \\
%   {\text{State + State}} \\
%   \text{State}
%   \arrow["{\text{\Cref{sec:local-global}: Local state to global state}}"{pos=0.2}, shift left=2, draw=none, from=1-1, to=2-1]
%   \arrow["{\text{\Cref{sec:multiple-states}}}", shift left=2, draw=none, from=2-1, to=3-1]
%   \arrow["{\text{\Cref{sec:nondeterminism-state}: Nondeterminism to State}}"{pos=0.7}, shift left=2, draw=none, from=1-1, to=2-1]
%   \arrow[from=1-1, to=2-1]
%   \arrow[from=2-1, to=3-1]
% \end{tikzcd}\]

% \birthe{we could put the names of the new n-queens definitions in this figure, starting with |queensNaive| and |queens|, for example:}

% https://q.uiver.app/?q=WzAsNyxbMSwwLCJ8cXVlZW5zTmFpdmV8Il0sWzEsMiwifHF1ZWVuc3wiXSxbMCw0LCJ8cXVlZW5zTG9jYWx8Il0sWzEsNCwifHF1ZWVuc0dsb2JhbHwiXSxbMiw0LCJ8cXVlZW5zU3RhdGV8Il0sWzMsNCwifHF1ZWVuc1NpbXwiXSxbMywxXSxbMCwxLCJlYXJseSBwcnVuaW5nIl0sWzQsNSwiXFxDcmVme3NlYzp9IiwyXSxbMyw0LCJcXENyZWZ7c2VjOn0iLDJdLFsyLDMsIlxcQ3JlZntzZWM6fSIsMl0sWzEsMl0sWzEsM10sWzEsNF0sWzEsNV1d
\[\begin{tikzcd}
	& {|queensNaive|} \\
	&&& {} \\
	& {|queens|} \\
	\\
	{|queensLocal|} & {|queensGlobal|} & {|queensState|} & {|queensSim|}
	\arrow["{\text{early pruning}}", from=1-2, to=3-2]
	\arrow["{S\ref{sec:combination}}"', from=5-3, to=5-4]
	\arrow["{S\ref{sec:nondeterminism-state}}"', from=5-2, to=5-3]
	\arrow["{S\ref{sec:local-global}}"', from=5-1, to=5-2]
	\arrow[from=3-2, to=5-1]
	\arrow[from=3-2, to=5-2]
	\arrow[from=3-2, to=5-3]
	\arrow[from=3-2, to=5-4]
\end{tikzcd}\]

%-------------------------------------------------------------------------------
\subsection{Free Monads and Their Folds}

Before taking the first step, we first revise our key ingredients for
simulating one effect in terms of another and establishing correctness: free
monads, their folds and their fusion properties.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Free Monads}
Free monads are gaining popularity for their use in algebraic effects \cite{Plotkin02}
and handlers \cite{Plotkin09, Plotkin13},
which elegantly separate syntax and semantics of effectful
operations.
A free monad, the syntax of an effectful program,
can be captured generically in Haskell.
\begin{code}
data Free f a = Var a | Op (f (Free f a))
\end{code}
This data type is a form of abstract syntax tree (AST) consisting of leaves (|Var a|)
and internal nodes (|Op (f (Free f a))|), whose branching structure is
determined by the functor |f|.
This functor is also known as the \emph{signature}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{A Fold Recursion Scheme}
Free monads % arise from the free-forgetful adjunction and
come equipped with a fold recursion scheme.
\begin{code}
fold :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
fold gen alg (Var x)  =  gen x
fold gen alg (Op op)  =  alg (fmap (fold gen alg) op)
\end{code}
This fold interprets an AST structure of type |Free f a| into some
semantic domain |b|. It does so compositionally using a generator
|gen :: a -> b| for the leaves and an algebra |alg :: f b -> b| for the internal
nodes; together these are also known as a \emph{handler}.

The monad instance of |Free| can now straightforwardly be implemented using
this fold.
%if False
\begin{code}
instance Functor f => Functor (Free f) where
    fmap = liftM

instance Functor f => Applicative (Free f) where
  pure = return
  (<*>) = ap
\end{code}
%endif
\begin{code}
instance Functor f => Monad (Free f) where
    return   = Var
    m >>= f  = fold f Op m
\end{code}

%fmap f (Op op) = Op (fmap (fmap f) op)
%(Op op) >>= f = Op (fmap (>>= f) op)

Under certain conditions a fold can be fused with a function that is applied right before or after it~\cite{Wu15, DBLP:conf/acmmpc/2000}.
This gives rise to the following laws:
\begin{alignat}{2}
    &\mbox{\bf fusion-pre}: &
    |fold (gen . h) alg| &= |fold gen alg . fmap h|\mbox{~~,} \label{eq:fusion-pre}\\
    &\mbox{\bf fusion-post}: &
    |h . fold gen alg| &= |fold (h . gen) alg'| \text{ with } |h . alg = alg' . fmap h| \label{eq:fusion-post}\mbox{~~,}\\
    &\mbox{\bf fusion-post'}: &
    |h . fold gen alg| &= |fold (h . gen) alg'| \text{ with } |h . alg . fmap f = alg' . fmap h . fmap f| \label{eq:fusion-post-strong}\mbox{~~.}
\end{alignat}
where |f = fold gen alg|.

These two fusion laws will turn out to be essential in the further proofs of this paper.

% We can define an empty signature and the run function for it.
% \begin{code}
% data Void a deriving Functor

% runVoid :: Free Void a -> a
% runVoid (Var x) = x

% \end{code}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Nondeterminism}
For nondeterminism, we do not use a monad like that of lists.
Following the algebraic effects approach, we
use instead a free monad over an appropriate signature, such as |Free NondetF|
where |NondetF| is the nondeterminism signature.
\begin{code}
data NondetF a   = Fail | Or a a
\end{code}
This signatures gives rise to a trivial |MNondet| instance:
\begin{code}
instance MNondet (Free NondetF) where
  mzero = Op Fail
  mplus p q = Op (Or p q)
\end{code}

This does not respect the identity or associativity law on the nose. Indeed,
|Op (Or Fail p)| is for instance a different abstract syntax tree than |p|.
Yet, these syntactic differences do not matter as long as their interpretation
is the same. This is where the handlers come in; the meaning they assign
should respect the laws.

This is case for the |hND| handler, which interprets the free monad in terms of
lists.
\begin{code}
hND :: Free NondetF a -> [a]
hND = fold genND algND
  where
    genND x         = [x]
    algND Fail      = []
    algND (Or p q)  = p ++ q
\end{code}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{State}
Also for state we take a more indirect route, through a free monad like |Free (StateF
s)| over the state signature.

\begin{code}
data StateF s a  = Get (s -> a) | Put s a
\end{code}
This state signature gives the following |MState s| instance:
\begin{code}
instance MState s (Free (StateF s)) where
  get    =  Op (Get return)
  put s  =  Op (Put s (return ()))
\end{code}

The handler maps this free monad to the |State s| monad.
\begin{code}
hState' :: Free (StateF s) a -> State s a
hState' = fold genS' algS'
  where
    genS' x            = State $ \s -> (x, s)
    algS' (Get     k)  = State $ \s -> runState (k s) s
    algS' (Put s'  k)  = State $ \s -> runState k s'
\end{code}

%-------------------------------------------------------------------------------
\subsection{Modularly Combining Effects}
\label{sec:combining-effects}

Combining multiple effects is relatively easy in the axiomatic approach based
on type classes. By imposing multiple constraints on the monad |m|, e.g.,
|(MState s m, MNondet m)|, we can express that |m| should support both state
and nondeterminism and respect their associated laws. In practice, this is
often insufficient: we usually require additional laws that govern the
interactions between the combined effects. We discuss possible interaction
laws between state and nondeterminism in detail in Section
\ref{sec:local-global}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{The Coproduct Operator for Combining Effects}
Combining effects with free monads is a bit more involved.
Firstly, the signatures of the effects are combined with
%if False
\begin{code}
-- class (MState s m, MNondet m) => MStateNondet s m | m -> s
infixr :+:
instance Functor (StateF s) where
    fmap f (Get s)    = Get (f . s)
    fmap f (Put s x)  = Put s (f x)

instance Functor NondetF where
    fmap f Fail      = Fail
    fmap f (Or x y)  = Or (f x) (f y)
\end{code}
%endif
the coproduct operator |(:+:)| for functors.
\begin{code}
data (f :+: g) a = Inl (f a) | Inr (g a)
\end{code}
This coproduct functor allows a
modular definition of the signature of effects.
For instance, we can encode programs with both state and nondeterminism as
effects using the data type
|Free (StateF :+: NondetF) a|.
The coproduct also has a neutral element |NilF|, representing the empty effect set.
%if False
\begin{code}
data NilF a deriving (Functor)
\end{code}
%endif

Consequently, we can compose state effects with any other
effect functor |f| using |Free (StateF s :+: f) a|.
It is also easy to see that |Free (StateF s :+: NondetF :+: f)| supports both state and nondeterminism.

\begin{code}
instance (Functor f) => MState s (Free (StateF s :+: f)) where
    get      = Op $ Inl $ Get return
    put x    = Op $ Inl $ Put x (return ())

instance (Functor f, Functor g) => MNondet (Free (g :+: NondetF :+: f)) where
  mzero        = Op $ Inr $ Inl Fail
  x `mplus` y  = Op $ Inr $ Inl (Or x y)
\end{code}

%if False
\begin{code}
-- instance (Functor f) => MStateNondet s (Free (StateF s :+: NondetF :+: f))
\end{code}
%endif

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Modularly Combining Effect Handlers}
In order to interpret composite signatures, we use the forwarding approach of
\citet{Schrijvers19}. This way the handlers can be modularly composed: they
only need to know about the part of the syntax their effect is handling, and
forward the rest of the syntax to other handlers.

A mediator |(#)| is used to separate the algebra |alg| for the handled effects and
the forwarding algebra |fwd| for the unhandled effects.
\begin{code}
(#) :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
(alg # fwd)  (Inl op)  =  alg op
(alg # fwd)  (Inr op)  =  fwd op
\end{code}
%if False
\begin{code}
infixr #
instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl x)  =  Inl (fmap f x)
    fmap f (Inr y)  =  Inr (fmap f y)

comm    :: (Functor f, Functor g)
        => Free (f :+: g) a
        -> Free (g :+: f) a
comm (Var x)      = Var x
comm (Op (Inl k)) = Op (Inr (fmap comm k))
comm (Op (Inr k)) = Op (Inl (fmap comm k))

assocl  :: (Functor f, Functor g, Functor h)
        => Free (f :+: (g :+: h)) a
        -> Free ((f :+: g) :+: h) a
assocl (Var x)            = Var x
assocl (Op (Inl k))       = Op (Inl (Inl (fmap assocl k)))
assocl (Op (Inr (Inl k))) = Op (Inl (Inr (fmap assocl k)))
assocl (Op (Inr (Inr k))) = Op (Inr (fmap assocl k))

assocr  :: (Functor f, Functor g, Functor h)
        => Free ((f :+: g) :+: h) a
        -> Free (f :+: (g :+: h)) a
assocr (Var x)            = Var x
assocr (Op (Inl (Inl k))) = Op (Inl (fmap assocr k))
assocr (Op (Inl (Inr k))) = Op (Inr (Inl (fmap assocr k)))
assocr (Op (Inr k))       = Op (Inr (Inr (fmap assocr k)))
\end{code}

\begin{spec}
hState' :: (Functor f, MState s m) => Free (StateF s :+: f) a -> Free f (m a)
hState' (Var x)               = Var (return x)
hState' (Op (Inl (Get k)))    = hState' (get >>= k)
hState' (Op (Inl (Put s x)))  = hState' (put s >> x)
hState' (Op (Inr y))          = Op (fmap hState' y)

hNondet' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
hNondet' = fold gen alg
  where
    gen = Var . return
    alg :: (Functor f, MNondet m) => (NondetF :+: f) (Free f (m a)) -> Free f (m a)
    alg (Inl Fail)      = Var mzero
    alg (Inl (Or p q))  = mplus <$> p <*> q
    alg (Inr y)         = Op y

hState :: Functor f => Free (StateF s :+: f) a -> (s -> Free f (a, s))
hState  =  fold genS (algS # fwdS)
  where
    genS x          s  = return (x, s)
    algS (Get k)    s  = k s s
    algS (Put s k)  _  = k s
    fwdS y          s  = Op (fmap ($s) y)
\end{spec}
%endif

The handlers for state and nondeterminism we have given earlier require a bit of
adjustment to be used in the composite setting.
They now interpret into composite domains,
|StateT (Free f) a| and |Free f [a]| respectively.
Here, |StateT| is the state transformer from the Monad Transformer Library \cite{mtl}.
< newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }
The handlers are defined as follows:
\begin{code}
hState :: Functor f => Free (StateF s :+: f) a -> StateT s (Free f) a
hState = fold genS (algS # fwdS)
  where
    genS x            = StateT $ \s -> return (x, s)
    algS (Get     k)  = StateT $ \s -> runStateT (k s) s
    algS (Put s'  k)  = StateT $ \s -> runStateT k s'
    fwdS op           = StateT $ \s -> Op $ fmap (\k -> runStateT k s) op
hNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
hNDf  =  fold genNDf (algNDf # fwdNDf)
  where
    genNDf           = Var . return
    algNDf Fail      = Var []
    algNDf (Or p q)  = (++) <$> p <*> q
    fwdNDf op        = Op op
\end{code}

Also, the empty signature |NilF| has a trivial associated handler.
\begin{code}
hNil :: Free NilF a -> a
hNil (Var x) = x
\end{code}
