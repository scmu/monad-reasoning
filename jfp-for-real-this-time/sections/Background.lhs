
%if False
\begin{code}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Background where

import Control.Monad (ap, liftM, join, when)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.List

import Debug.Trace as DT


\end{code}
%endif

\section{Background and Motivation}
\label{sec:background}

This section summarises the main prerequisites for equational
reasoning with effects and motivates our translations from high-level
effects to low-level effects.
% For a more extensive treatment we refer to the work of % % %
% \citep{Gibbons11}.
We discuss the two central effects of this paper: state and
nondeterminism.
% Furthermore, this section explains how to arbitrarily combine %
% effects using free monads and the coproduct operator.

% The main challenges addressed in this paper relate to the tension between writing
% programs with high-level effects or with low-level effects.
% Often, we choose the high-level alternative which is easier to understand and
% to debug, but we miss out on opportunities for optimization that would have
% been available in the low-level style.
% 
% Existing systems such as the Warren Abstract Machine (WAM) for Prolog or
% constraint-based systems in general \cite{AICPub641:1983,AitKaci91}
% offer a high-level programming interface to programmers, but
% use a low-level state-based
% representation under the hood that allow clever system-level optimizations.
% 
% In this paper, we provide:
% \begin{enumerate}
% \item
% a purely functional, monadic model of the high-level effects that those
% systems expose to their users,
% \item
% successive transformation steps from those high-level effects into the
% low-level state effect in order to incorporate typical optimizations found in
% those systems, and
% \item
% proofs based on equational reasoning to establish the correctness of those
% transformations.
% \end{enumerate}
% 
% As a running example, we use the n-queens puzzle, which has
% nondeterminism and state, and can be simulated using only state.


%-------------------------------------------------------------------------------
\subsection{Functors and Monads}
\label{sec:functors-and-monads}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{Functors}\
In Haskell, a functor |f :: * -> *| instantiates the functor type class, which has a single
functor mapping operation.
< class Functor f where
<   fmap :: (a -> b) -> f a -> f b

Furthermore, a functor should satisfy the following two functor laws:
\begin{alignat}{2}
    &\mbox{\bf identity}:\quad &
    |fmap id| &= |id|\mbox{~~,} \label{eq:functor-identity}\\
    &\mbox{\bf composition}:~ &
    |fmap (f . g)| &= |fmap f . fmap g| \mbox{~~.} \label{eq:functor-composition}
\end{alignat}
%
We sometimes use the operator |<$>| as an alias for |fmap|.

< (<$>) :: Functor f => (a -> b) -> f a -> f b
< (<$>) = fmap
%if False
$
%endif

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
\paragraph*{Monads}\
Monadic side-effects~\citep{Moggi91}, the main focus of this paper,
are those that can dynamically determine what happens next.
A monad |m :: * -> *| is a functor instantiates the monad type class,
which has two operations return (|eta|) and bind (|>>=|).

< class Functor m => Monad m where
<   eta     :: a -> m a
<   (>>=)   :: m a -> (a -> m b) -> m b

Furthermore, a monad should satisfy the following three monad laws:
\begin{alignat}{2}
    &\mbox{\bf return-bind}:\quad &
    |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-ret-bind}\\
    &\mbox{\bf bind-return}:~ &
    |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-bind-ret}\\
    &\mbox{\bf associativity}:~ &
    |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{alignat}
%
Haskell supports |do| blocks as syntactic sugar for monadic computations.
For example, |do x <- m; f x| is translated to |m >>= f|.
Two convenient derived operators are |>>| and |<*>|.\footnote{We
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
\label{sec:state}

Following both the approaches of \citet{Hutton08} and of \citet{Gibbons11}, we introduce
effects as subclasses of the |Monad| type class.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{Nondeterminism}\
The first monadic effect we introduce is nondeterminism. We define a
subclass |MNondet| of |Monad| to capture the nondeterministic
interfaces as follows:
\begin{code}
class Monad m => MNondet m where
  mzero  :: m a
  mplus  :: m a -> m a -> m a
\end{code}
Here, |mzero| denotes failures and |mplus| denotes nondeterministic
choices.  Instances of the |MNondet| interface should satisfy the
following four laws:
%
\footnote{
One might expect additional laws such as idempotence or commutativity.
As argued by \cite{Kiselyov:15:Laws}, these laws differ depending on
how the monad is used and how it should interact with other effects.
We choose to present a minimal setting for nondeterminism here.}
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
over |mplus| and that |mzero| cancels bind on the left.

The approach of \citet{Gibbons11} is to reason about effectful
programs using an axiomatic characterisation given by these laws. It
does not rely on the specific implementation of any particular
instance of |MNondet|.
%
In contrast, \citet{Hutton08} reason directly in terms of a particular
instance.  In the case of |MNondet|, the quintessential instance is
that of lists, which extends the conventional |Monad| instance for lists.

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
\paragraph*{State}\
The signature for the state effect has two operations:
a |get| operation that reads and returns the state,
and a |put| operation that modifies the state, overwriting it with the given
value, and returns nothing.
%
Again, we define a subclass |MState| of |Monad| to capture its
interfaces.

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
%
The standard instance of |MState| is the state monad |State s|.

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
\cite{Gibbons11}.
The aim of the puzzle is to place $n$ queens on a $n \times n$ chess board such
that no two queens can attack each other.
Given $n$, we number the rows and columns by |[1..n]|.
Since all queens should be placed on distinct rows and distinct columns, a
potential solution can be represented by a permutation |xs| of the list |[1..n]|,
such that |xs !! i = j| denotes that the queen on the |i|th column is placed on
the |j|th row.
Using this representation, queens cannot be put on the same row or column.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{A Naive Algorithm}\
We have the following native nondeterministic algorithm for n-queens.
\begin{code}
queensNaive :: MNondet m => Int -> m [Int]
queensNaive n = choose (permutations [1..n]) >>= filtr valid
\end{code}
The program |queensNaive 4 :: [[Int]]| gives as result |[[2,4,1,3],
[3,1,4,2]]|.  The program uses a generate-and-test strategy: it
generates all permutations of queens as candiate solutions, and then
tests which ones are valid.
% This version enumerates the entire search space to find solutions.

The function |permutations :: [a] -> [[a]]| from |Data.List| computes
all the permutations of its input.
%
The function |choose| implemented as follows nondeterministically
picks an element from a list.
%
% We will further discuss
% in~\Cref{sec:interpreting-nondet-progs-with-list} that it is actually
% a monad morphism from the initial lawful instance of |MNondet| to any
% other nondeterministic monad.
% %
% \wenhao{I don't think the story of the initiality of |List| is
% essential to us since we're already working with the free monad
% representation. It is only discussed and used in S5.1.}

\begin{code}
choose :: MNondet m => [a] -> m a
choose = foldr (mplus . return) mzero
\end{code}

The function |filtr p x| returns |x| if |p x| holds, and fails otherwise.
\begin{code}
filtr :: MNondet m => (a -> Bool) -> a -> m a
filtr p x = if p x then return x else mzero
\end{code}

The pure function |valid :: [Int] -> Bool| determines whether the
input is a valid solution. 
\begin{code}
valid :: [Int] -> Bool
valid []      = True
valid (q:qs)  = valid qs && safe q 1 qs
\end{code}
A solution is valid when each queen is |safe| with respect
to the subsequent queens:
%format q1
\begin{code}
safe :: Int -> Int -> [Int] -> Bool
safe _ _ []       = True
safe q n (q1:qs)  = and [q /= q1 , q /= q1 + n , q /= q1 - n , safe q (n+1) qs]
\end{code}
The call |safe q n qs| checks whether the current queen |q| is on a different ascending and descending diagonal
than the other queens |qs|, where |n| is the number of columns that |q| is apart from the first queen |q1| in |qs|.

Although this generate-and-test approach works and is quite intuitive, it is not very efficient.
For example, all solutions of the form |(1:2:qs)| are invalid because the first two queens are on the same diagonal.
However, the algorithm still needs to generate and test all $(n-2)!$ candidate solutions of this form.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph*{A More Performant Backtracking Algorithm}\
\paragraph*{A Backtracking Algorithm}\
We can fuse the two phases of the naive algorithm to obtain a more
efficient algorithm, where both generating candidates and checking for
validity happens in a single pass.  The idea is to move to a
state-based backtracking implementation that allows early pruning of
branches that are invalid.
%
In particular, when placing the new queen in the next column, we make
sure that it is only placed in positions that are valid with respect
to the previously placed queens.

We use a state |(Int, [Int])| to contain the current column and the
previously placed queens.  The backtracking algorithm of n-queens is
implemented as follows.
\begin{code}
queens :: (MState (Int, [Int]) m, MNondet m) => Int -> m [Int]
queens n = loop where
  loop = do  (c, sol) <- get
             if c >= n then return sol
             else do  r <- choose [1..n]
                      guard (safe r 1 sol)
                      s <- get
                      put (s `plus` r)
                      loop
\end{code}

The function |guard| fails when the input is false.
\begin{code}
guard :: MNondet m => Bool -> m ()
guard True  = return ()
guard False = mzero
\end{code}
%
The function |s `plus` r| updates the state with a new queen placed on
row |r| in the next column.
%if False
\begin{code}
class Undo s r | s -> r where
  plus :: s -> r -> s
  minus :: s -> r -> s
instance Undo (Int, [Int]) Int where
  plus (c, sol) r   = (c+1, r:sol)
  minus (c, sol) r  = (c-1, tail sol)
\end{code}
%endif
\begin{spec}
plus   :: (Int, [Int]) -> Int -> (Int, [Int])
plus   (c, sol) r = (c+1, r:sol)
\end{spec}
%

The above monadic version of |queens| is the starting point of this
paper.  In the following sections, we investigate how low-level
optimisations, such as those found in Prolog implementations and
Constraint Programming systems, can be incorporated and shown correct.
