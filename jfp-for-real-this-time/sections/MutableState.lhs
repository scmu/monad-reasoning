%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module MutableState where

import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef

import Background
import Overview
import LocalGlobal (local2global, hLocal, comm2)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero, get, put, modify, guard)

\end{code}
%endif
%-------------------------------------------------------------------------------
\section{Mutable State}
\label{sec:mutable-state}

Performance-wise, it would be better to have an algorithm with mutable states,
instead of the built-in |State| monad that keeps track of state in a pure way.
In all previously defined functions, we make unnecessary copies of the state,
and keep track of them explicitly in the program.
This section shows how to avoid this by using a stack-based implementation
that has the functionality of a mutable state.

\subsection{Implementing Mutable State}
\label{sec:implementing-mutable-state}

It is easy to show that a mutable state handler can be defined in
Haskell.
We use a stack to implement mutable states.
\begin{code}
data Stack s b a = Stack {   stack     ::  STRef s   (STArray s Index a),
                             size      ::  STRef s   Index,
                             results   ::  STRef s   b }

type Index = Int
\end{code}
This stack consists of three reference cells:
(1) one with a (mutable) array containing the data,
(2) another with the size of the stack, and
(3) a third one with the results.
The size of the stack is the amount of allocated space that is actually
filled with data.
We distinguish between the allocated space for the array, obtained by the builtin
|getBounds| function and referred to as |space|, and the size of the array.
Both the |STRef| and the |STArray| datatypes come from Haskell's
|Control.Monad.ST| library that implements the strict |ST| monad.

Figure \ref{fig:grow-empty} defines a helper function to create an empty stack.

\begin{figure}[h]
\small
% \begin{subfigure}[t]{0.4\linewidth}
\begin{code}
emptyStack :: b -> ST s (Stack s b a)
emptyStack results = do
    stack        <- newArray_ (0, 1)
    sizeRef      <- newSTRef 0
    stackRef     <- newSTRef stack
    resultsRef   <- newSTRef results
    return (Stack stackRef sizeRef resultsRef)
\end{code}

% \caption{Empty stack.}
% \label{fig:empty}
% \end{subfigure}%
% \begin{subfigure}[t]{0.54\linewidth}
% \begin{code}
% growStack :: b -> Index -> [a] -> ST s (Stack s b a)
% growStack results space elems = do
%     stack        <- newListArray (0, space) elems
%     sizeRef      <- newSTRef (length elems)
%     stackRef     <- newSTRef stack
%     resultsRef   <- newSTRef results
%     return (Stack stackRef sizeRef resultsRef)
% \end{code}
% \caption{Growing the stack.}
% \label{fig:grow}
% \end{subfigure}

\caption{Helper functions |emptyStack|.}
\label{fig:grow-empty}
\end{figure}

Figure \ref{fig:pushstack-popstack} shows how to push to and pop from a stack.

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
pushStack :: a -> Stack s b a -> ST s ()
pushStack x (Stack stackRef sizeRef resRef) =
  do
    stack       <- readSTRef stackRef
    size        <- readSTRef sizeRef
    res         <- readSTRef resRef
    (_, space)  <- getBounds stack
    writeSTRef sizeRef (size + 1)
    if size < space
    then writeArray stack size x
    else do
        elems        <- getElems stack
        stack'       <- newListArray (0, space * 2) elems
        writeArray  stack' size x
        writeSTRef  stackRef stack'
\end{code}
\caption{Pushing to the stack.}
\label{fig:pushstack}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
popStack :: Stack s b a -> ST s (Maybe a)
popStack (Stack stackRef sizeRef _) =
  do
    stack  <- readSTRef stackRef
    size   <- readSTRef sizeRef
    if size == 0
    then return Nothing
    else do
        writeSTRef sizeRef (size - 1)
        Just <$> readArray stack (size - 1)
\end{code}
\caption{Popping from the stack.}
\label{fig:popstack}
\end{subfigure}%
\caption{Helper functions |pushStack| and |popStack|.}
\label{fig:pushstack-popstack}
\end{figure}

\subsection{A Stack Handler}
\label{sec:stack-hanler}

The functor |StackF| is the signature that represents a stack.
We can then represents the mutable state effect through a free monad over that
signature: |Free (StackF e b)|.

The signature should include the action of
pushing to and popping from the stack, where |e| rerpresents the elements.
This is very similar to the |StateF| functor, except for the |Maybe| in the
codomain of the |Pop| element.
This optional value may be |Nothing| when the stack is empty.
Furthermore, the signature includes operations for getting from and putting to
the current results, represented by |b|. This also reminds of a state effect
signature.
So, the |StackF| functor has four operations in total.

\begin{code}
data StackF e b a = Push e a | Pop (Maybe e -> a) | GetSt (b -> a) | PutSt b a
\end{code}
%if False
\begin{code}
instance Functor (StackF e b) where
    fmap f (Push x k)  = Push x (f k)
    fmap f (Pop k)     = Pop (f . k)
    fmap f (GetSt s)   = GetSt (f . s)
    fmap f (PutSt s x) = PutSt s (f x)
\end{code}
%endif

The handler for mutable state |hStack| then works as follows.
The |Push| and |Pop| operations are used to respectively push elements to the
stack and pop them from the stack.
The |GetSt| and |PutSt| operations can get and put results.
\begin{code}
hStack  :: Functor f
        => Free (StackF e b :+: f) a -> Stack s b e -> STT s (Free f) (a, b)
hStack = fold gen (alg # fwd)
  where
    gen x            stack = liftST ((readSTRef . results) stack)   >>= \b -> return (x, b)
    alg (Push x k)   stack = liftST (pushStack x stack)             >> k stack
    alg (Pop k)      stack = liftST (popStack stack)                >>= \x -> k x stack
    alg (GetSt k)    stack = liftST ((readSTRef . results) stack)   >>= \x -> k x stack
    alg (PutSt x k)  stack = liftST (writeSTRef (results stack) x)  >> k stack
    fwd op           stack = STT $ \s -> Op ((\f -> unSTT (f stack) s) <$> op)
\end{code}

\subsection{Simulating Nondeterminism with Mutable State}
\label{sec:sim-nondet-with-mut-state}

We can simulate a program with nondeterminism using the above representation
of a stack.
For this, we use a type |SK| that is essentially a computation with a stack.

\begin{code}
type CompSK s f b a = Free (StackF s b :+: f) a
data SK f a = SK { unSK :: CompSK (SK f a) f [a] () }
\end{code}

Compared to the previous simulations, the results (wrapped in the list monad)
are not included in the |SK| type, but instead incorporated in the
stack representation (|Stack stack size results|).

\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
getSK :: Functor f => CompSK s f b b
getSK = Op . Inl $ GetSt return
\end{code}
\end{minipage}
\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
putSK :: Functor f => b -> CompSK s f b ()
putSK b = Op . Inl $ PutSt b (return ())
\end{code}
\end{minipage}
\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
popSK' :: Functor f => CompSK s f b (Maybe s)
popSK' = Op . Inl $ Pop return
\end{code}
\end{minipage}
\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
pushSK' :: Functor f => s -> CompSK s f b ()
pushSK' s = Op . Inl $ Push s (return ())
\end{code}
\end{minipage}



\noindent
\begin{figure}[h]
\noindent
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popSK  :: Functor f
       => SK f a
popSK = SK $ do
  mtop <- popSK'
  case mtop of
    Nothing -> return ()
    Just (SK top) -> top
\end{code}
\caption{Popping from the stack.}
\label{fig:pop-sk}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushSK  :: Functor f
        => SK f a
        -> SK f a
        -> SK f a
pushSK q p = SK $ do
  pushSK' q
  unSK p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push-ss}
\end{subfigure}
\begin{subfigure}[t]{0.35\linewidth}
\begin{code}
appendSK  :: Functor f
          => a
          -> SK f a
          -> SK f a
appendSK x p = SK $ do
  xs <- getSK
  putSK (xs ++ [x]); unSK p
\end{code}
\caption{Appending a solution.}
\label{fig:append-sk}
\end{subfigure}%
\label{fig:pop-push-append-SK}
\caption{Helper functions |popSK|, |pushSK| and |appendSK|.}
\end{figure}

We can now define a simulation |nondet2stack| that handles the nondeterminism
effect in a similar way as |nondet2state|, except that we now use a mutable state,
represented by the stack of computations.
The other effects |f| are forwarded to other handlers using a forwarding algebra.

\begin{code}
nondet2stack :: Functor f => Free (NondetF :+: f) a -> SK f a
nondet2stack = fold gen (alg # fwd)
  where
    gen x         = appendSK x popSK
    alg Fail      = popSK
    alg (Or p q)  = pushSK q p
    fwd           = SK . Op . Inr . fmap unSK
\end{code}

Finally, |runNDSK| is an extenstion of the simulation that transfroms every monad
with nondeterminism and other effects |f| into a free monad.
The nondeterminism effects are handled, wrapping the result in a list monad,
so that only the other effects |f| remain.

% -- runNDSK p = fmap snd (runSTT $ liftST (emptyStack []) >>= hStack (unSK $ nondet2stack p))
\begin{code}
runNDSK :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDSK p = fmap snd (runhStack [] (unSK $ nondet2stack p))

runhStack :: Functor f => b -> Free (StackF e b :+: f) a -> Free f (a, b)
runhStack b x = runSTT $ liftST (emptyStack b) >>= hStack x
\end{code}

\wenhao{The correctness of |nondet2stack| is not proved.}

\subsection{Using Mutable State to Simulate Nondeterminism in N-queens}
\label{sec:n-queens-mut-state}

We revisit the n-queens example of \Cref{sec:motivation-and-challenges}.
In the simulation of n-queens with immutable state, we replace
|(extractSS . hState . nondet2state)| with |runNDSK|.

\begin{code}
queensStack   :: Int -> [[Int]]
queensStack   = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . runNDSK . comm2
              . local2global . queens
\end{code}
% Similarly, we develop a version of |queensStackR|, which uses the undo semantics
% together with mutable state.
% \begin{code}
% queensStackR  :: Int -> [[Int]]
% queensStackR  = hNil
%               . fmap fst . flip runStateT (0, []) . hState
%               . runNDSK . comm2
%               . modify2global . queensR
% \end{code}


%-------------------------------------------------------------------------------
\subsection{Optimisation with Undo}
\label{sec:undo-semantics}

% backtracking in local state

In \Cref{sec:transforming-between-local-and-global-state}, we give a
translation |local2global| which simulates local state with global
state by replacing |put| with |putR|.  The |putR| operation makes the
implicit copying of the local-state semantics explicit in the
global-state semantics.  This copying is rather costly if the state is
big (e.g., a long array), and especially wasteful if the modifications
made to that state are rather small (e.g., a single entry in the
array).
%
To improve upon this situation we can, instead of copying the state,
keep track of the modifications made to it, and undo them when
necessary.
%
This is especially efficient when we have mutable states.

For example, the |queens| program in
\Cref{sec:motivation-and-challenges} uses |s `plus` r| to update the
state.
%
We can define its left inverse as follows.
\begin{spec}
minus   :: (Int, [Int]) -> Int -> (Int, [Int])
minus   (c, sol) r = (c-1, tail sol)
\end{spec}
%
These two operators satisfy the equation |(`minus` x) . (`plus` x) = id|
for any |x :: Int|.
%
Then, we can just use |s `minus` r| to roll back the update, instead
of copying the whole state like |putR| in the global-state semantics.

In general, we define a type-class |Undo s r| and implement |Undo (Int, [Int]) Int|
as an instance using the previously defined |plus| and |minus|.
\begin{spec}
class Undo s r where
  plus :: s -> r -> s
  minus :: s -> r -> s
\end{spec}
% instance Undo (Int, [Int]) Int where
%   plus (c, sol) r   = (c+1, r:sol)
%   minus (c, sol) r  = (c-1, tail sol)

In general, we define a |modify| function as follows.
\begin{code}
modify           :: MState s m => (s -> s) -> m ()
modify f         = get >>= put . f
\end{code}

If all the state updates in a program are given by some |modify fwd|
where every |fwd| is accompanied with a left inverse |bwd| such that
|bwd . fwd = id|, we can simulate its local-state semantics with
global-state semantics by using |modify bwd| to roll back the updates.

% Rather than using |put|, some algorithms typically use a pair of
% commands |modify fwd| and |modify bwd| to update and roll back the
% state, respectively.  The |fwd| and |bwd| represent the modifications
% to the state, with |bwd . fwd = id|.
  % Following a style similar to |putR|, this can be modelled as follows:
% modifyR          :: (MState s m, MNondet m) => (s -> s) -> (s -> s) -> m ()
% modifyR fwd bwd  = modify fwd `mplus` side (modify bwd)
% We can implement |modify| with |get| and |put| as follows.

% Similar to \Cref{sec:putr}, we can give a translation and show its
% correctness.
%
% With |modify|, instead of copying the state in the global-state
% semantics, we can use |modify bwd| to restore the changes introduced
% by |modify fwd|.

In order to show it formally, we need to make sure that every state
update is given by some |modify fwd| with a left inverse |bwd| at the
syntax level. We define a new signature giving the syntax of two
operations for get and modify.
%
\begin{code}
data ModifyF s a  = MGet (s -> a) | ModifyR (s -> s) (s -> s) a
\end{code}
%
The operation |ModifyR fwd bwd| takes two functions with |bwd . fwd = id|.
%if False
\begin{code}
instance Functor (ModifyF s) where
    fmap f (MGet s)    = MGet (f . s)
    fmap f (ModifyR g h x) = ModifyR g h (f x)
\end{code}
%endif
As for nondeterminism and state, we define a subclass |MModify| of
|Monad| to capture its effectful interfaces, and implement the free
monad |Free (ModifyF s :+: f)| as an instance of it.
\begin{code}
class Monad m => MModify s m | m -> s where
    mget     :: m s
    modifyR  :: (s -> s) -> (s -> s) -> m ()
instance Functor f => MModify s (Free (ModifyF s :+: f)) where
  mget    =  Op (Inl (MGet return))
  modifyR fwd bwd  =  Op (Inl (ModifyR fwd bwd (return ())))
\end{code}

% We can interpret programs written with |ModifyF| and |NondetF| by
% translating |ModifyF| operations to |StateF| and |NondetF| operations.
%
The local-state semantics of programs with |ModifyF| and |NondetF| is
directly given by the local-state semantics of |StateF| and |NondetF|.
We have the following translation |modify2local| which only uses |fwd|.
%
\begin{code}
modify2local  :: Functor f
              => Free (ModifyF s :+: NondetF :+: f) a
              -> Free (StateF s :+: NondetF :+: f) a
modify2local  = fold Var alg
  where
    alg (Inl (ModifyR fwd _ k))  = modify fwd >> k
    alg (Inl (MGet k))           = get >>= k
    alg (Inr p)                  = Op (Inr p)
\end{code}
%
To simulate the local-state semantics with global-state semantics,
instead of using the translation |local2global| which uses the
inefficient operation |putR|, we can give another translation
|modify2global| as follows which makes use of |bwd| to roll back updates.
% with the global-state semantics, in addition to
% using |fwd|, we also need to use |bwd| to roll back the updates.
%
Similar to |putR|, it also uses |`mplus`| to implement backtracking.
%
\begin{code}
modify2global  :: Functor f
               => Free (ModifyF s :+: NondetF :+: f) a
               -> Free (StateF s :+: NondetF :+: f) a
modify2global  = fold Var alg
  where
    alg (Inl (ModifyR fwd bwd k))  = (modify fwd `mplus` modify bwd) >> k
    alg (Inl (MGet k))             = get >>= k
    alg (Inr p)                    = Op (Inr p)
\end{code}

The following theorem shows that the simulation of local-state
semantics with global-state semantics given by |modify2global|
coincides with the local-state semantics given by |modify2local|.
%
\begin{theorem}\label{thm:modify-local-global}
< hGlobal . modify2global = hLocal . modify2local
\end{theorem}
\wenhao{TODO: prove it.}

Combining it with \Cref{thm:local-global}, we also have
< hGlobal . modify2global = hGlobal . local2global . modify2local

Observe that, unlike |putR|, the interpretation of |modifyR| in
|modify2global| does not hold onto a copy of the old state.
%
Although the |modify| function still takes out the whole state and
apply a function to it, it can be more efficient with in-place
update~\citep{LorenzenLS23} or mutable states.
% TODO: probably add a forward reference to where we use mutable states


%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{N-queens with |modifyR|}\
%
% Let us revisit the n-queens example of \Cref{sec:motivation-and-challenges}.
% Recall that, for the puzzle, the operator that alters the state
% % (to check whether a chess placement is safe)
% is defined by
% < (c, sol) `plus` r = (c+1, r:sol)
% We can define its left inverse |minus| as
% < (c, sol) `minus` r = (c-1, tail sol)
% so that the equation |(`minus` x) . (`plus` x) = id| is satisfied.
% \footnote{This is similar to the properties of the addition and subtraction operations used in the differential lambda calculus \cite{Xu21}.}
% TODO: some literature survey on incremental computation if I have time
%
% Thus, we can compute all the solutions to the puzzle in a scenario with a
% shared global state as follows:
Now we can rewrite the |queens| program with modify and nondeterminism.
\begin{code}
queensR :: (MModify (Int, [Int]) m, MNondet m) => Int -> m [Int]
queensR n = loop where
  loop = do  (c, sol) <- mget
             if c >= n then return sol
             else do  r <- choose [1..n]
                      guard (safe r 1 sol)
                      modifyR (`plus` r) (`minus` r)
                      loop
\end{code}
%
It is not hard to see that
%
< modify2local queensR = queens
%
Combined with \Cref{thm:modify-local-global}, we have
< hGlobal (modify2global queensR) = hLocal queens

% This function replaces the |put| operation in the original implementation's
% |loop| by a call to |modifyR (`plus` r) (`minus` r)|.
% Taking into account that the local-state semantics
% discards the side-effects in the |side| branch, it is not difficult
% to see that
% % \begin{equation*}
% < hLocal . queens = hLocal . queensR
% % \end{equation*}
% Moreover, following Theorem~\ref{thm:local-global}, we can conclude that |queensR| also behaves the same
% under global-state semantics where the |side| branch takes care of backtracking
% the state.
% % \begin{equation*}
% < hGlobal . queens = hGlobal . queensR
% % \end{equation*}
The advantage of the left-hand side is that it does not keep any copies of
the state alive.

% The |put (0, [])| in the initialization of |queensR| does not
% influence this behaviour as the final state is dropped.
% The function |queensModify| implements global state with undo semantics.
%
% \begin{code}
% queensModify :: Int -> [[Int]]
% queensModify = hNil . flip hGlobal (0,[]) . queensR
% \end{code}

%if False
% \begin{code}
% minus   :: (Int, [Int]) -> Int -> (Int, [Int])
% minus   (c, sol) r = (c-1, tail sol)

% -- tR :: StateT (Int, [Int]) [] [Int]
% -- tR = queensR 9

% -- testR :: [[Int]]
% -- testR = fmap fst $ runStateT t (0,[])
% \end{code}
%endif


%include TrailStack.lhs

% The function |queensStackBFS| runs the |queens| by applyin the handlers of stack and nondeterminism sequentially.
% \begin{code}
% queensStackBFS :: Int -> [[Int]]
% queensStackBFS n = hND $ runSTT (liftST emptyStack >>= ((hStack (queensS n)) $))
% \end{code}
%
%
% The code below simulates the nondeterminism with the mutable stack.
% \begin{code}
% type CompSK s f b a = Free (StateF b :+: StackF s :+: f) a
% data SK f a = SK { unSK :: CompSK (SK f a) f [a] () }
%
% getSK :: Functor f => Free (StateF s :+: f) s
% getSK = Op . Inl $ Get return
%
% putSK :: Functor f => s -> Free (StateF s :+: f ) ()
% putSK s = Op . Inl $ Put s (return ())
%
% popSK' :: Functor f => CompSK s f b (Maybe s)
% popSK' = Op . Inr . Inl $ Pop return
%
% pushSK' :: Functor f => s -> CompSK s f b ()
% pushSK' s = Op . Inr . Inl $ Push s (return ())
%
% popSK :: Functor f => CompSK (SK f a) f [a] ()
% popSK = do
%   mtop <- popSK'
%   case mtop of
%     Nothing -> return ()
%     Just (SK top) -> top
%
% pushSK :: Functor f => CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
% pushSK q p = do
%   pushSK' (SK q)
%   p
%
% appendSK :: Functor f => a -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
% appendSK x p = do
%   xs <- getSK
%   putSK (xs ++ [x])
%   p
%
% -- simulation of nondeterminism with stack
% nondet2stack :: Functor f => Free (NondetF :+: f) a -> CompSK (SK f a) f [a] ()
% nondet2stack = fold gen (alg # fwd)
%   where
%     gen :: Functor f => a -> CompSK (SK f a) f [a] ()
%     gen x         = appendSK x popSK
%     alg :: Functor f => NondetF (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
%     alg Fail      = popSK
%     alg (Or p q)  = pushSK q p
%     fwd :: Functor f => f (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
%     fwd y = Op (Inr (Inr y))
%
%
% runNDSK :: Functor f => Free (NondetF :+: f) a -> Free f [a]
% runNDSK p = let t = runSTT $ liftST emptyStack >>= ((hStack . flip runStateT [] . hState $ nondet2stack p) $) in fmap snd t
%
% queensStack   :: Int -> [[Int]]
% queensStack   = hNil
%               . fmap fst . flip runStateT (0, []) . hState
%               . runNDSK . comm2
%               . local2global . queens
%
% queensStackR :: Int -> [[Int]]
% queensStackR = hNil
%               . fmap fst . flip runStateT (0, []) . hState
%               . runNDSK . comm2
%               . queensR
% \end{code}
