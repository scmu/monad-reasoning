
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

import Control.Monad (ap, liftM, join)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.List

import Debug.Trace as DT


choose :: MNondet m => [a] -> m a
choose = foldr (mplus . return) mzero

\end{code}
%endif

\section{Background and Motivation}
\label{sec:background}

This section summarizes the main concepts for equational reasoning with
effects.
For a more extensive treatment we refer to the work of \citep{Gibbons11}.
We discuss the two paramount effects of this paper: state and nondeterminism.
Furthermore, this section explains how to arbitrarily combine effects using
free monads and the coproduct operator.
Finally, we motivate the problem statement with an example and discuss the
main challenges.
Throughout the paper, we will use Haskell as a means to illustrate
our findings with code.


%-------------------------------------------------------------------------------
\subsection{Free Monads}
\label{sec:free-monads}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Functors}
In Haskell, a functor |f :: * -> *| instantiates the functor type class, which has a single
functor mapping operation.
< class Functor f where
<   fmap :: (a -> b) -> f a -> f b

Furthermore, a functor should satisfy the two functor laws:
\begin{alignat}{2}
    &\mbox{\bf identity}:\quad &
    |fmap id| &= |id|\mbox{~~,} \label{eq:functor-identity}\\
    &\mbox{\bf composition}:~ &
    |fmap (f . g)| &= |fmap f . fmap g| \mbox{~~.} \label{eq:functor-composition}
\end{alignat}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Applicatives}
Applicative functors, introcuced by \citet{mcbride08},
allow sequencing of functorial computations.
An applicative functor |f :: * -> *| in Haskell has two operations: |pure| for
embedding pure data and
|(<*>)| for sequencing.
< class Functor f => Applicative f where
<     pure   :: a -> f a
<     (<*>)  :: f (a -> b) -> f a -> f b

An applicative functor should satisfy the following four laws:
\begin{alignat}{2}
    &\mbox{\bf identity}:\quad &
    |pure id <*> x| &= |x|\mbox{~~,} \label{eq:functor-identity}\\
    &\mbox{\bf composition}:~ &
    |pure (.) <*> x <*> y <*> z| &= |x <*> (y <*> z)| \mbox{~~,} \\
    &\mbox{\bf homomorphism}:~ &
    |pure f <*> pure x| &= |pure (f x)| \mbox{~~,} \\
    &\mbox{\bf interchange}:~ &
    |x <*> pure y| &= |pure ($ y) <*> x| \mbox{~~.}
\end{alignat}

Often, the notation |f <$> x| is used to denote |pure f <*> x|, which is equivalent to |fmap f x|.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Monads}

Side effects are those effects that are affected by previous computations.
In Haskell, a pure functional language, we typically encapsulate side effects
in a monad \cite{Moggi91}.
A monad |m :: * -> *| instantiates the monad type class, which has two
operations: return (|eta|) and bind (|>>=|).

< class Monad m where
<   eta     :: a -> m a
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
Furthermore, it supports a join operator |(>>) :: m a -> m b -> m b| so that
|m1 >> m2 = m1 >>= \ _ -> m2|.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Free Monads and Their Folds}

Free monads are gaining popularity for their use in algebraic effects \cite{Plotkin02}
and their handlers \cite{Plotkin09, Plotkin13},
which elegantly separate syntax and semantics of effectful
operations.
A free monad, the syntax of an effectful program,
can be captured generically in Haskell.
\begin{code}
data Free f a = Var a | Op (f (Free f a))
\end{code}
This data type is an AST consisting of leaves |Var a|
and nodes |Op (f (Free f a))| with a signature functor |f|
representing the branching structure.

Free monads arise from the free-forgetful adjunction and come equipped with a
unique catamorphism or a fold: a recursion scheme over the free monad.
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

When a fold is composed with other functions, it adheres to so-called fusion laws \cite{Wu15}.
Precomposing or postcomposing a function with a fold works as follows:
\begin{alignat}{2}
    &\mbox{\bf fusion-pre}:\quad &
    |fold gen alg . fmap h| &= |fold (gen . h) alg|\mbox{~~,} \label{eq:fusion-pre}\\
    &\mbox{\bf fusion-post}:~ &
    |h . fold gen alg| &= |fold (h . gen) alg'| \text{ with } |h . alg = alg' . fmap h| \label{eq:fusion-post}\mbox{~~.}
\end{alignat}

We use these laws in due course to prove correctness of laws for state,
nondeterminism or a combination.

% We can define an empty signature and the run function for it.
% \begin{code}
% data Void a deriving Functor

% runVoid :: Free Void a -> a
% runVoid (Var x) = x

% \end{code}

%-------------------------------------------------------------------------------
\subsection{Nondeterminism}
\label{sec:nondeterminism}

The first effect we introduce is nondeterminism.
Following the approach of \citet{Hutton08} and \citet{Gibbons11},
we introduce effects based on an axiomatic characterisation rather than
a specific implementation.
We define a type class to capture the nondeterministic interface as follows:
\begin{code}
class Monad m => MNondet m where
  mzero  :: m a
  mplus  :: m a -> m a -> m a
\end{code}
Here, |mzero| denotes failure and |mplus| denotes nondeterministic choice.
Typically, the |MNondet| interface should satisfy the following four laws:
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
As argued by \cite{Kiselyov15monadplus}, these laws differ depending on where the
monad is used and their interactions with other effects.
We choose to present a minimal setting for nondeterminism here.

Haskell's implementation for nondeterminism is the |List| monad.

\begin{code}
instance MNondet [] where
  mzero  =  []
  mplus  =  (++)
\end{code}

The corresponding |Monad| instance has the following standard Haskell implementation.

< instance Monad [] where
<   return x   = [x]
<   xs >>= f    = concatMap f xs

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
%if False
\begin{code}
    state :: (s -> (a, s)) -> m a
    state f = do
      s <- get
      let ~(x, s') = f s
      put s'
      return x
\end{code}
%endif
These operations are related by the four so-called state laws:
\begin{alignat}{2}
    &\mbox{\bf put-put}:\quad &
    |put s >> put s'| &= |put s'|~~\mbox{,} \label{eq:put-put}\\
    &\mbox{\bf put-get}:~ &
    |put s >> get| &= |put s >> return s| ~~\mbox{,} \label{eq:get-put}\\
    &\mbox{\bf get-put}:~ &
    |get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
    &\mbox{\bf get-get}:\quad &
    |get >>= (\s -> get >>= k s)| &= |get >>= (\s -> k s s)|
    ~~\mbox{.} \label{eq:get-get}
\end{alignat}

Again, these state laws may be supplemented with other laws that deal with state
and its interaction with other effects.

Haskell's implementation for state is the |State s| monad.

\begin{code}
newtype State s a = State { runState :: s -> (a, s) }

instance MState s (State s) where
  get    = State (\s -> (s, s))
  put s  = State (\ _ -> ((), s))
\end{code}
%if False
\begin{code}
instance Functor (State s) where
  fmap = liftM

instance Applicative (State s) where
  pure  = return
  (<*>) = ap

instance Monad (State s) where
  return x = State (\s -> (x, s))
  m >>= f  = State (\s -> let (x, s') = runState m s in runState (f x) s')
\end{code}
%endif

%-------------------------------------------------------------------------------
\subsection{Combining Effects}
\label{sec:combining-effects}

Because of the axiomatic definitions of our effects, it is straightforward to
reason about their combinations and interactions.
This paper is about the interaction between nondeterminism and local or global state.
We define a class |MStateNondet| that inherits the operations of its
superclasses |MState| and |MNondet| without adding new operations.
\begin{code}
class (MState s m, MNondet m) => MStateNondet s m | m -> s
\end{code}
Implementations of this class should satisfy all laws of its superclasses.
Furthermore, this monad comes with additional interaction laws that
differentiate between local and global state semantics.
Section \ref{sec:local-global} discusses these interaction laws in detail.

Using free monads, as discussed in \cref{sec:free-monads},
we can separate syntax from semantics.
In the syntax, both stateful and nondeterministic computations
can be represented by such a free monad construct.
For that, we define the |StateF| and |NondetF| functors:
\begin{code}
data StateF s a  = Get (s -> a) | Put s a
data NondetF a   = Fail | Or a a
\end{code}
Using this encoding, stateful and nondeterministic computations
are represented by the types |Free (StateF s) a| and |Free NondetF a| respectively.
% \begin{code}
% type StateC s a  =  Free (StateF s) a
% type NondetC a   =  Free NondetF a
% \end{code}
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
with a coproduct operator |(:+:)| for functors.
\begin{code}
data (f :+: g) a = Inl (f a) | Inr (g a)
\end{code}
This coproduct functor allows a
modular definition of the signature of effects.
For instance, we can encode programs with both state and nondeterminism as
effects using the data type
|Free (StateF :+: NondetF) a|.
The coproduct also has a neutral element |NilF|, representing the empty effect set,
and a function |hNil|, extracting return values from |Free NilF a|.
\begin{code}
data NilF a deriving (Functor)

hNil :: Free NilF a -> a
hNil (Var x) = x
\end{code}
% \birthe{do we need this?}
% We also provide a helper function |addNil|, which adds a |NilF| to a free monad |Free f a|.
% \begin{code}
% addNil :: Functor f => Free f a -> Free (f :+: NilF) a
% addNil (Var a)  = Var a
% addNil (Op x)   = (Op $ Inl $ fmap addNil x)
% \end{code}

Consequently, we can compose the state effects with any other
effect functor |f| using |Free (StateF s :+: f) a|.

To give semantics to the free monad constructs of these effects, we can use
their folds, also called handlers.
The handlers can be modularly composed: they only need to know about
the part of the syntax their effect is handling, and forward the rest
of the syntax to other handlers.

A mediator |(#)| is used to separate the algebra |alg| for handling the effects and
the forwarding function |fwd| for forwarding the rest of the effects \cite{Schrijvers2019}.
\begin{code}
(#) :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
(alg # fwd) (Inl op) = alg op
(alg # fwd) (Inr op) = fwd op
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

instance MState s (Free (StateF s)) where
    get    = Op (Get return)
    put x  = Op (Put x (return ()))


instance (Functor f, MState s (Free (StateF s))) => MState s (Free (StateF s :+: f)) where
    get    = Op (Inl (Get return))
    put x  = Op (Inl (Put x (return ())))
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

The handlers for state and nondeterminism use the |StateT| monad and |List|
monad, respectively, to interpret their part of the semantics.
The |StateT| monad is the state transformer from the Monad Transformer Library \cite{mtl}.
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

We also provide simpler versions of the two handlers above which restrict the free monad to have no other effects (|f = NilF|).
\begin{code}
hState' :: Free (StateF s) a -> State s a
hState' = fold genS' algS'
  where
    genS' x            = State $ \s -> (x, s)
    algS' (Get     k)  = State $ \s -> runState (k s) s
    algS' (Put s'  k)  = State $ \s -> runState k s'

hND :: Free NondetF a -> [a]
hND = fold genND algND
  where
    genND           = return
    algND Fail      = []
    algND (Or p q)  = p ++ q
\end{code}


%-------------------------------------------------------------------------------
\subsection{Motivation and Challenges}
\label{sec:motivation-and-challenges}

The challenges we address in this paper relate to the tension between writing
programs with high-level effects or with low-level effects.
Often, we choose the high-level alternative which is easier to understand and
to debug, but we miss out on opportunities for optimization that would have
been available in the low-level style.

Existing systems such as Prolog, the Warren Abstract Machine (WAM) or
constraint-based systems in general \todo{citations} use a low-level state-based
representation that allows them to optimize their programs, e.g. with cut
semantics or intelligent backtracking.

In this paper, we argue that we can model high-level effects using state, which
will allow us to optimize in a way that is similar to well-known state-based
systems.
We transform high-level effects into lower-level effects, and prove these
tranformations correct using equational reasoning techniques.
These transformations allow optimizations of our programs.
As a running example, we will use the n-queens puzzle, which has nondeterminism
and state, and can be simulated using only state.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{The n-queens Puzzle}

The n-queens problem used here is an adapted and simplified version from that of
\todo{cite Gibbons and Hinze}.
The aim of the puzzle is to place $n$ queens on a $n \times n$ chess board such
that no two queens can attack eachother.
Given $n$, we number the rows and columns by |[0..n-1]|.
Since all queens should be placed on distinct rows and distinct columns, a
potential solution can be represented by a permutation |xs| of the list |[0..n-1]|,
such that |xs !! i = j| denotes that the queen on the |i|th column is placed on
the |j|th row.
Using this representation, queens cannot be put on the same row or column.
\todo{image}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{A Naive Algorithm}

The naive version of an algorithm for n-queens can be written as a
nondeterministic program:
\begin{code}
queensNaive :: MNondet m => Int -> m [Int]
queensNaive n = choose (permutations [1..n]) >>= filtr valid
\end{code}
On a high level, this function generates all permutations of queens, and then
checks them one by one for validity.
This version looks into the entire search space to find solutions.

Here, |permutations| nondeterministically computes a permutation of its input.
The function |choose| nondeterministically picks an element from a list, and is
implemented in \Cref{sec:interpreting-nondet-progs-with-list}.

The function |filtr p x| returns |x| if |p x| holds, and fails otherwise.
\begin{code}
filtr :: MNondet m => (a -> Bool) -> a -> m a
filtr p x = (if p x then return () else mzero) >> return x
\end{code}

The pure function |valid :: [Int] -> Bool| determines whether a solution is
valid: it only needs to make sure that no two queens are put on the same
diagonal.

%if False
\begin{code}
valid :: [Int] -> Bool
valid [] = True
valid (q:qs) = valid qs && safe q 1 qs
\end{code}
%endif

Although this solution works and it quite intuitive, it is not very efficient.
For example, it is obvious that all solutions that start with |[1,2]| are invalid,
but the algorithm still generates and tests all of these $(n-2)!$ candidates.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{A More Performant Backtracking Algorithm}

We wish to fuse the two phases of the algorithm to produce a faster implementation.
In fact, we want to improve the implementation on a high-level so that
generating candidates and checking for validity happens in a single pass.
We can do this by moving to a state-based implementation that allows early
pruning of branches that are unsafe.

In particular, we improve the previous implementation by placing the queens
column by column so that we only place a queen on a position that is compatible
with the previously placed queens.

We use a state |(Int, [[Int]])| that contains the column we are looking at, and
the list of current solutions with the already placed queens.
The new implementation of |queens| is as follows:
\begin{code}
queens :: MStateNondet (Int, [[Int]]) [] => Int -> [[Int]]
queens n = do
  put (0, [[]])
  loop
    where
        loop :: MStateNondet (Int, [[Int]]) [] => [[Int]]
        loop = do
          (c, sol) <- get
          if c >= n then sol
                    else do
                        put (c+1, join (fmap (expand n) sol))
                        loop
expand :: MStateNondet (Int, [[Int]]) [] => Int -> [Int] -> [[Int]]
expand n qs = choose [q : qs | q <- [1..n], safe q 1 qs]
\end{code}

%if False
\begin{code}
-- instance MStateNondet (Int, [[Int]]) [] where
--
-- instance MState (Int, [[Int]]) [] where
--     get = _ --[]
--     put s = _--  state (\_ -> ((), s))
\end{code}
%endif

The function |safe| checks whether the placement of a queen |q| is safe with
respect to the list of queens that is already present (for which we need its
distance from the queen in the list). We only have to check that the queens are
in different diagonals.

\begin{code}
safe :: Int -> Int -> [Int] -> Bool
safe _ _ [] = True
safe q n (q1:qs) = and [q /= q1 , q /= q1 + n , q /= q1 - n , safe q (n+1) qs]
\end{code}
\todo{first check is prob unnecessary}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Transformations and Optimizations}

Although the state-based implementation is a noteworthy improvement over the naive
version, we can also make strong improvements at a lower level of implementation.

For example, we could avoid making an explicit copy of the state at every branching
point by evolving from local-state semantics to global-state semantics.

Furthermore, we can model nondeterminism with state, which allows for a smoother
undo semantics.

Mutable state would also improve performance significantly.

In what follows, we define simulations for transforming a high-level effect into
a lower-level effect and show how these transformations lead to the optimizations
discussed above.

In particular, we take the following steps:
\Cref{sec:local-global} simulates local state with global state;
\Cref{sec:nondeterminism-state} explains how to simulate nondeterminism with state; and
\Cref{sec:multiple-states} shows how we can group multiple states into a single
state effect.


\todo{we could put the names of the new n-queens definitions in this figure, starting with |queensNaive| and |queens|}
% https://q.uiver.app/?q=WzAsMyxbMCwwLCJTdGF0ZSArIE5vbmRldGVybWluaXNtIl0sWzAsMSwiU3RhdGUgKyBTdGF0ZSJdLFswLDIsIlN0YXRlIl0sWzAsMSwiU2VjdGlvbiBcXHJlZnt9OiBOb25kZXRlcm1pbmlzbSAkXFxyaWdodGFycm93JCBTdGF0ZSIsMCx7ImxhYmVsX3Bvc2l0aW9uIjozMH1dLFsxLDIsIlNlY3Rpb24gXFxyZWZ7fSJdLFswLDEsIlNlY3Rpb24gXFxyZWZ7fTogTG9jYWwgc3RhdGUgJFxccmlnaHRhcnJvdyQgZ2xvYmFsIHN0YXRlIiwwLHsibGFiZWxfcG9zaXRpb24iOjcwfV1d
\[\begin{tikzcd}
  {\text{State + Nondeterminism}} \\
  {\text{State + State}} \\
  \text{State}
  \arrow["{\text{\Cref{sec:local-global}: Local state to global state}}"{pos=0.2}, shift left=2, draw=none, from=1-1, to=2-1]
  \arrow["{\text{\Cref{sec:multiple-states}}}", shift left=2, draw=none, from=2-1, to=3-1]
  \arrow["{\text{\Cref{sec:nondeterminism-state}: Nondeterminism to State}}"{pos=0.7}, shift left=2, draw=none, from=1-1, to=2-1]
  \arrow[from=1-1, to=2-1]
  \arrow[from=2-1, to=3-1]
\end{tikzcd}\]
