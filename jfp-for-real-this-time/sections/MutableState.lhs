%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module MutableState where

import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef

import Background
import Overview
import LocalGlobal (local2global, hLocal, comm2, queensR)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState, queensStateR)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero)

\end{code}
%endif
%-------------------------------------------------------------------------------
\section{Mutable State}
\label{sec:mutable-state}

Performance-wise, it would be better to have an algorithm with mutable state,
instead of the built-in |State| monad that keeps track of state in a pure way.
In all previously defined functions, we make unnecessary copies of the state,
and keep track of them explicitly in the program.
This section shows how to avoid this by using a stack-based implementation
that has the functionality of a mutable state.

\subsection{Implementing Mutable State}
\label{sec:implementing-mutable-state}

It is easy to show that a mutable state handler can be defined in
Haskell.
We will use a stack to implement mutable state.
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
pushStack x (Stack stackRef sizeRef resRef) = do
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
popStack (Stack stackRef sizeRef _) = do
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
    fwd y            stack = STT $ \s -> Op ((\f -> unSTT (f stack) s) <$> y)
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

\begin{code}
runNDSK :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDSK p = fmap snd (runSTT $ liftST (emptyStack []) >>= hStack (unSK $ nondet2stack p))
\end{code}

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
Similarly, we develop a version of |queensStackR|, which uses the undo semantics
together with mutable state.
\begin{code}
queensStackR  :: Int -> [[Int]]
queensStackR  = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . runNDSK . comm2
              . queensR
\end{code}

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
