
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

This section summarizes the main prerequisites for equational reasoning with
effects.
% For a more extensive treatment we refer to the work of \citep{Gibbons11}.
We discuss the two paramount effects of this paper: state and nondeterminism.
% Furthermore, this section explains how to arbitrarily combine effects using
% free monads and the coproduct operator.
Throughout the paper, we will use Haskell as a means to illustrate
our findings with code.


The main challenges addressed in this paper relate to the tension between writing
programs with high-level effects or with low-level effects.
Often, we choose the high-level alternative which is easier to understand and
to debug, but we miss out on opportunities for optimization that would have
been available in the low-level style.

Existing systems such the Warren Abstract Machine (WAM) for Prolog or
constraint-based systems in general \cite{AICPub641:1983,hassan91}
offer a high-level programming interface to programmers, but
use a low-level state-based
representation under the hood that allow clever system-level optimizations.

In this paper, we provide:
\begin{enumerate}
\item
a purely functional, monadic model of the high-level effects that those
systems expose to their users,
\item
successive transformation steps from those high-level effects into the
low-level state effect in order to incorporate typical optimizations found in
those systems, and
\item
proofs based on equational reasoning to establish the correctness of those
transformations.
\end{enumerate}

As a running example, we will use the n-queens puzzle, which has
nondeterminism and state, and can be simulated using only state.


%-------------------------------------------------------------------------------
\subsection{Functors and Monads}
\label{sec:functors-and-monads}

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

We sometimes use the operator |(<$>)| which is an alias for |fmap|.

< (<$>) :: Functor f => (a -> b) -> f a -> f b
< (<$>) = fmap

% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph{Applicatives}
% \tom{Where do we use applicatives? If only minimally, we should check whether we can skip the
%      general introduction and provide a shorter, more targeted explanation.}
% \birthe{We use |<*>| and |<$>|.}
% Applicative functors, introduced by \citet{mcbride08},
% allow sequencing of functorial computations.
% An applicative functor |f :: * -> *| in Haskell has two operations: |pure| for
% embedding pure data and
% |(<*>)| for sequencing.
% < class Functor f => Applicative f where
% <     pure   :: a -> f a
% <     (<*>)  :: f (a -> b) -> f a -> f b
%
% An applicative functor should satisfy the following four laws:
% \begin{alignat}{2}
%     &\mbox{\bf identity}:\quad &
%     |pure id <*> x| &= |x|\mbox{~~,} \label{eq:functor-identity}\\
%     &\mbox{\bf composition}:~ &
%     |pure (.) <*> x <*> y <*> z| &= |x <*> (y <*> z)| \mbox{~~,} \\
%     &\mbox{\bf homomorphism}:~ &
%     |pure f <*> pure x| &= |pure (f x)| \mbox{~~,} \\
%     &\mbox{\bf interchange}:~ &
%     |x <*> pure y| &= |pure ($ y) <*> x| \mbox{~~.}
% \end{alignat}
%
% Often, the notation |f <$> x| is used to denote |pure f <*> x|, which is equivalent to |fmap f x|.
%
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Monads}

Monadic side-effects~\cite{Moggi91}, the main focus of this paper, are those that can dynamically determine what
happens next.
A monad |m :: * -> *| instantiates the monad type class, which has two
operations: return (|eta|) and bind (|>>=|).

< class Monad m where
<   eta     :: a -> m a
<   (>>=)   :: m a -> (a -> m b) -> m b

%NOTE: tag1
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
Finally, two convenient derived operators are |(>>)| and |(<*>)|.\footnote{We
deviate from the type class hierarchy of |Functor|, |Applicative| and |Monad|
that can be found in Haskell's standard library because its additional complexity
is not needed in this article.}

< (>>) :: Monad m => m a -> m b -> m b
< m1 >> m2 = m1 >>= \ _ -> m2
<
< (<*>) :: Monad m => m (a -> b) -> m a -> m b
< mf <*> mx = mf >>= \ f -> mx >>= \ x -> return (f x)

%-------------------------------------------------------------------------------
\subsection{Nondeterminism and State}
\label{sec:nondeterminism}

Following both the approaches of \citet{Hutton08} and of \citet{Gibbons11}, we introduce
effects on top of the |Monad| type class.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{Nondeterminism}
The first monadic effect we introduce in this way is nondeterminism.
We define a type class to capture the nondeterministic interface as follows:
\begin{code}
class Monad m => MNondet m where
  mzero  :: m a
  mplus  :: m a -> m a -> m a
\end{code}
Here, |mzero| denotes failure and |mplus| denotes nondeterministic choice.
Instances of the |MNondet| interface should satisfy four laws:\footnote{
One might expect additional laws such as idempotence or commutativity.
As argued by \cite{Kiselyov:15:Laws}, these laws differ depending on where the
monad is used and their interactions with other effects.
We choose to present a minimal setting for nondeterminism here.}
%NOTE: tag2
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
The first two laws state that |mplus| and |mzero| should form a monoid,
i.e., |mplus| should be associative with |mzero| as its neutral element.
The last two laws show that |(>>=)| is right-distributive
over |mplus| and that |mzero| cancels bind on the left. The approach of
\citet{Gibbons11} is to reason about programs by using these laws and
not to rely on the specific implementation of any particular instance
of |MNondet|.

In contrast, \citet{Hutton08} reason directly in terms of a particular
instance.  In the case of |MNondet|, the quintessential is that of lists,
which extends the following |Monad| instance for lists.

\begin{minipage}{0.5\textwidth}
\begin{code}
instance MNondet [] where
  mzero  =  []
  mplus  =  (++)
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
< instance Monad [] where
<   return x   = [x]
<   xs >>= f    = concatMap f xs
\end{minipage}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{State}
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
%NOTE: tag3
These operations are regulated by four laws:
\begin{alignat}{2}
    &\mbox{\bf put-put}:\quad &
    |put s >> put s'| &= |put s'|~~\mbox{,} \label{eq:put-put}\\
    &\mbox{\bf put-get}:~ &
    |put s >> get| &= |put s >> return s| ~~\mbox{,} \label{eq:put-get}\\
    &\mbox{\bf get-put}:~ &
    |get >>= put| &= |return ()| ~~\mbox{,} \label{eq:get-put}\\
    &\mbox{\bf get-get}:\quad &
    |get >>= (\s -> get >>= k s)| &= |get >>= (\s -> k s s)|
    ~~\mbox{.} \label{eq:get-get}
\end{alignat}

The standard instance of |MState| is that of |State s|.

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
\subsection{The n-queens Puzzle}
\label{sec:motivation-and-challenges}



% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph{The n-queens Puzzle}

The n-queens problem used here is an adapted and simplified version from that of
Gibbons and Hinze \cite{Gibbons11}.
The aim of the puzzle is to place $n$ queens on a $n \times n$ chess board such
that no two queens can attack each other.
Given $n$, we number the rows and columns by |[1..n]|.
Since all queens should be placed on distinct rows and distinct columns, a
potential solution can be represented by a permutation |xs| of the list |[1..n]|,
such that |xs !! i = j| denotes that the queen on the |i|th column is placed on
the |j|th row.
Using this representation, queens cannot be put on the same row or column.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{A Naive Algorithm}

The naive version of an algorithm for n-queens can be written as a
nondeterministic program:
\begin{code}
queensNaive :: MNondet m => Int -> m [Int]
queensNaive n = choose (permutations [1..n]) >>= filtr valid
\end{code}
The program |queensNaive 4 :: [[Int]]| gives as result |[[2,4,1,3],[3,1,4,2]]|.
On a high level, the function generates all permutations of queens, and then
checks them one by one for validity.
% This version enumerates the entire search space to find solutions.

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

Although this solution works and is quite intuitive, it is not very efficient.
For example, it is obvious that all solutions that start with |[1,2]| are invalid,
but the algorithm still generates and tests all of these $(n-2)!$ candidates.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph{A More Performant Backtracking Algorithm}

We wish to fuse the two phases of the algorithm to produce a faster implementation.
In fact, we want to improve the implementation on a high level so that
generating candidates and checking for validity happens in a single pass.
We can do this by moving to a state-based implementation that allows early
pruning of branches that are unsafe.

In particular, we improve the previous implementation by placing the queens
column by column so that we only place a queen on a position that is compatible
with the previously placed queens.

We use a state |(Int, [Int])| that contains the column we are looking at, and
the current solution with the already placed queens.
The new implementation of |queens| is as follows:
\begin{code}
queens :: (MState (Int, [Int]) m, MNondet m) => Int -> m [Int]
queens n = put (0, []) >> loop
  where
    loop = do  s@(c, sol) <- get
               if c >= n then return sol
               else do  r <- choose [1..n]
                        filtr valid (r:sol)
                        put (s `plus` r)
                        loop
\end{code}

The function |s `plus` r| updates the state with a new queen placed on row |r|.
\begin{code}
plus   :: (Int, [Int]) -> Int -> (Int, [Int])
plus   (c, sol) r = (c+1, r:sol)
\end{code}


The function |safe| checks whether the placement of a queen is safe with
respect to the list of queens that is already present (for which we need its
distance from the queen in the list). We only have to check that the queens are
in different diagonals.

\begin{code}
safe :: Int -> Int -> [Int] -> Bool
safe _ _ [] = True
safe q n (q1:qs) = and [q /= q1 , q /= q1 + n , q /= q1 - n , safe q (n+1) qs]
\end{code}

The above monadic version of |queens| is the starting point for this paper.  In the
remainder, we investigate how low-level optimizations, such as those found in
Prolog implementations and Constraint Programming systems, can be incorporated and shown correct.
