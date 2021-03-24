
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

module Background where

import Control.Monad (ap)

\end{code}
%endif

\section{Background and Motivation}
\label{sec:background}

Intro.
Refer to "Just Do It".

%-------------------------------------------------------------------------------
\subsection{Free Monads}
\label{sec:free-monads}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Functors}

\begin{itemize}
    \item functor laws (identity, fusion)
    \item coproduct
\end{itemize}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Monads}

Side effects are those effects that are affected by previous computations. 
In Haskell, a pure functional language, we typically encapsulate side effects
in a monad \cite{Moggi1991}. 
A monad |M :: * -> *| instantiates the monad type class, which has two 
operations: return and bind.

< class Monad m where
<   return  :: a -> m a
<   (>>=)   :: m a -> (a -> m b) -> m b

Furthermore, a monad should satisfy the three monad laws:
\begin{alignat}{2}
    &\mbox{\bf return-bind}:\quad &
    |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-ret-bind}\\
    &\mbox{\bf bind-return}:~ &
    |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-bind-ret}\\
    &\mbox{\bf associativity}:~ &
    |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{alignat}

Haskell supports |do| blocks as syntactic sugar for monadic computations.
For example, |do x <- m; f x| is translated to |m >>= f|.  
Furthermore, it supports a `join' operator |(>>) :: m a -> m b -> m b| so that
|m1 >> m2 = m1 >>= \ _ -> m2|.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Free Monads} 

Free monads are gaining popularity for their use in algebraic effect handlers
\cite{PlotkinPower}, which elegantly seperate syntax and semantics of effectful
operations
A free monad, the syntax of an effectful program,
can be captured generically in Haskell.
\begin{code}
data Free f a = Var a | Op (f (Free f a))
\end{code}
This data type is an AST consisting of leaves |Var a| 
and nodes |Op (f (Free f a))| with a signature functor |f| 
representing the branching structure. 

Free monads arise from the free-forgetful adjunction and come equipped with a 
unique catamorphism or a fold, a recursion scheme over the free monad.
We can define this recursive structure and recursion scheme generically in Haskell:
\begin{code}
fold :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
fold gen alg (Var x)  =  gen x
fold gen alg (Op op)  =  alg (fmap (fold gen alg) op)
\end{code} 
This fold has two arguments: a generator |gen :: a -> b| 
and an algebra |alg :: f b -> b| and `folds' over the |Free f a| recursive data type.
The catamorphism is a handler for free monads; 
handling an effectful program constitutes folding over it with the correct
generator and algebra.

The monad instance of |Free| can now straightforwardly be implemented using
this fold.
%if False
\begin{code}
instance Functor f => Functor (Free f) where
    fmap f (Var x) = Var (f x)
    fmap f (Op op) = Op (fmap (fmap f) op)

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

When a fold is composed with other functions, it adheres to so-called fusion laws \cite{fusionForFree}.
Precomposing or postcomposing a function with a fold works as follows:
\begin{alignat}{2}
    &\mbox{\bf fusion-pre}:\quad &
    |fold alg gen . fmap h| &= |fold alg (gen . h)|\mbox{~~,} \label{eq:fusion-pre}\\
    &\mbox{\bf fusion-post}:~ &
    |h . fold alg gen| &= |fold alg' (h . gen)| \text{ with } |h . alg = alg' . fmap h| \label{eq:fusion-post}\mbox{~~.}
\end{alignat}

We use these laws in due course to prove correctness of laws for state, 
nondeterminism or a combination.

%-------------------------------------------------------------------------------
\subsection{Nondeterminism}
\label{sec:nondeterminism}

The first effect we introduce is nondeterminism.
Following the approach of \citet{HuttonFulger} and Gibbons and Hinze \cite{}, 
we introduce effects based on an axiomatic characterisation rather than 
a specific implementation.
We define a type class to capture the nondeterministic interface as follows:
\begin{code}
class Monad m => MNondet m where
  mzero  :: m a
  mplus  :: m a -> m a -> m a
\end{code}
Here, |mzero| denotes failure and |mplus| denotes nondeterministic choice.
Typically, the |MNondet| interface should satifsfy the following four laws:
\begin{alignat}{2}
    &\mbox{\bf identity}:\quad &
      |mzero `mplus` m| ~=~ & |m| ~=~ |m `mplus` mzero|\mbox{~~,} 
      \label{eq:mzero}\\
    &\mbox{\bf associativity}:~ &
      |(m `mplus` n) `mplus` k|~ &=~ |m `mplus` (n `mplus` k)| \mbox{~~,} 
      \label{eq:mplus-assoc}\\
    &\mbox{\bf right-distributivity}:~ &
      |(m1 `mplus` m2) >>= f| ~&=~ |(m1 >>= f) `mplus` (m2 >>= f)| \mbox{~~,}
      \label{eq:mplus-dist}\\
    &\mbox{\bf left-identity}:\quad &
      |mzero >>= f| ~&=~ |mzero| \label{eq:mzero-zero} \mbox{~~.}
\end{alignat}
The first two laws state that |mplus| with |mzero| should form a monoid,
i.e. |mplus| should be associative with |mzero| as its neutral element.
The last two laws show that |>>=| is right-distributive 
over |mplus| and that |mzero| is a left identity for the bind operation.

One might expect additional laws such as idempotence or commutativity. 
As argued by \cite{Kiselyov}, these laws differ depending on where the 
monad is used and their interactions with other effects.
We choose to present a minimal setting for nondeterminism here.

%-------------------------------------------------------------------------------
\subsection{State}

The signature for state has two operations: 
a |get| operation that reads and returns the state,
and a |put| operation that modifies the state, overwriting it with the given
value, and returns nothing.

\begin{code}
class Monad m => MState s m | m -> s where
    get :: m s
    put :: s -> m ()
\end{code}
These operations are related by the four so-called state laws:
\begin{alignat}{2}
    &\mbox{\bf put-put}:\quad &
    |put s >> put s'| &= |put s'|~~\mbox{,} \label{eq:put-put}\\
    &\mbox{\bf put-get}:~ &
    |put s >> get| &= |put s >> return s| ~~\mbox{,} \label{eq:get-put}\\
    &\mbox{\bf get-put}:~ &
    |get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
    &\mbox{\bf get-get}:\quad &
    |get >>= (\st -> get >>= k st)| &= |get >>= (\st -> k st st)|
    ~~\mbox{,} \label{eq:get-get}
\end{alignat}

Again, these state laws may be supplemented with other laws that deal with state
and its interaction with other effects.

%-------------------------------------------------------------------------------
\subsection{Combining Effects}
 
Because of the axiomatic definitions of our effects, it is straightforward to 
reason about their combinations and interactions.
This paper is about the interaction between nondeterminism and---local or global---state.
We define a class |MStateNondet| that inherits the operations of its 
superclasses |MState| and |MNondet| without adding new operations.
\begin{code}
class (MState s m, MNondet m) => MStateNondet s m | m -> s
\end{code}
Implementations of this class should satisfy all laws of its superclasses.
Furthermore, this monad comes with additional interaction laws that
differentiate between local and global state semantics.

\todo{local state and global state here? or refer to section 4}

Using free monads, as discussed in \cref{sec:free-monads}, 
we can separate syntax from semantics.
In the syntax, both stateful and nondeterministic computations 
can be represented by such a free monad construct.
For that, we define the |StateF| and |NondetF| functors:
\begin{code}
data StateF s a  = Get (s -> a) | Put s a
data NondetF a   = Fail | Or a a
\end{code}
Using this encoding, |Free (StateF s) a| represent stateful computations and
similarly, |Free NondetF a| represent nondeterministic computations.
%if False
\begin{code}
infixr :+:
instance Functor (StateF s) where
    fmap f (Get s)    = Get (f . s)
    fmap f (Put s x)  = Put s (f x) 

instance Functor NondetF where
    fmap f Fail      = Fail
    fmap f (Or x y)  = Or (f x) (f y)
\end{code}
%endif
Computations with multiple effects can be defined independently and combined 
with a coproduct operator |(:+:)|.
\begin{code}
data (f :+: g) a = Inl (f a) | Inr (g a)
\end{code}
For instance, we can encode programs with both state and nondeterminism as 
effects using the data type 
|Free (NondetF :+: StateF :+: NilF) a| where |NilF| is the neutral
element of the coproduct, representing the empty effect set.
\begin{code}
data NilF a
\end{code}
Similarly, we can compose the state effects with any other effect using 
|Free (StateF s :+: f) a| where |f| is a functor representing arbitrary other 
effects.

To give semantics to the free monad constructs of these effects, we can use
their folds, also called handlers. 
\todo{write |hState| as a fold, if possible?}
%if False
\begin{code}
instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (Inl x)  =  Inl (fmap f x)
    fmap f (Inr y)  =  Inr (fmap f y)

instance MState s (Free (StateF s)) where
    get    = Op (Get return)
    put x  = Op (Put x (return ()))


instance (Functor f, MState s (Free (StateF s))) => MState s (Free (StateF s :+: f)) where
    get    = Op (Inl (Get return))
    put x  = Op (Inl (Put x (return ())))
\end{code}
%endif
For state and nondeterminism, the handlers are defined as follows:
\begin{code}
hState :: (Functor f, MState s m) => Free (StateF s :+: f) a -> Free f (m a)
hState (Var x)               = Var (return x)
hState (Op (Inl (Get k)))    = hState (get >>= k)
hState (Op (Inl (Put s x)))  = hState (put s >> x)
hState (Op (Inr y))          = Op (fmap hState y)

hNondet :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
hNondet = fold gen alg 
  where 
    gen = Var . return 
    alg (Inl Fail)      = Var mzero
    alg (Inl (Or p q))  = mplus <$> p <*> q
    alg (Inr y)         = Op y
\end{code}

%-------------------------------------------------------------------------------
\subsection{Motivation and Challenges}
Show the n-queens example, explain the challenges




















