%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Optimizations where

import Background

import Data.Array.ST
import Control.Monad.ST
-- import qualified Control.Monad.ST.Trans as T
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef
import Control.Monad (ap, join, liftM)
import Control.Monad.Trans (lift)

import LocalGlobal
\end{code}
%endif


\section{Optimizations of the State-Based Interpretation}
\label{sec:optimizations}

\todo{Intro}

%-------------------------------------------------------------------------------
\subsection{Mutable State}
\label{sec:mutable-state}

Performance-wise, it would be better to have an algorithm with mutable state,
instead of the built-in |State| monad that keeps track of state in a pure way.

It is easy to show that a mutable state handler can easily be defined in 
Haskell. 
We will use a stack to implement mutable state.
\begin{code}
data Stack s a = Stack {   getStack  ::  STRef s   (STArray s Index a), 
                           getSize   ::  STRef s   Index }

type Index = Int
\end{code}
This stack consists of two reference cells, one with a (mutable) array 
containing the data, another with the size of the stack. 
The size of the stack is the amount of allocated space that is actually
filled with data.
We distinguish between the allocated space for the array, obtained by the builtin
|getBounds| function and referred to as |space|, and the size of the array.
Both the |STRef| and the |STArray| datatypes come from Haskell's 
|Control.Monad.ST| library that implements the strict |ST| monad.

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
growStack :: Index -> [a] -> ST s (Stack s a)
growStack space elems = do
    stack     <- newListArray (0, space) elems
    sizeRef   <- newSTRef (length elems)
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)
\end{code}
\caption{Growing the stack.}
\label{fig:grow}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
emptyStack :: ST s (Stack s a)
emptyStack = do
    stack     <- newArray_ (0, 1)
    sizeRef   <- newSTRef 0
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)
\end{code}
\caption{Empty stack.}
\label{fig:empty}
\end{subfigure}
\label{fig:grow-empty}
\caption{Helper functions |growStack| and |emptyStack|.}
\end{figure}

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
pushStack :: a -> Stack s a -> ST s ()
pushStack x (Stack stackRef sizeRef) = do
    stack       <- readSTRef stackRef
    size        <- readSTRef sizeRef
    (_, space)  <- getBounds stack
    writeSTRef sizeRef (size + 1)
    if size < space 
    then writeArray stack size x
    else do
        elems              <- getElems stack
        Stack stackRef' _  <- growStack (space * 2) elems
        stack'             <- readSTRef stackRef'
        writeArray  stack'   size x
        writeSTRef  stackRef stack'
\end{code}
\caption{Pushing to the stack.}
\label{fig:pushstack}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
popStack :: Stack s a -> ST s (Maybe a)
popStack (Stack stackRef sizeRef) = do
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
\label{fig:pushstack-popstack}
\caption{Helper functions |pushStack| and |popStack|.}
\end{figure}

The functor |StackF| represents the action of
pushing to and popping from the stack.
This is very similar to the |StateF| functor, except for the |Maybe| in the
codomain of the |Pop| element. 
This optional value may be |Nothing| when the stack is empty.
\begin{code}
data StackF e a = Push e a | Pop (Maybe e -> a)
\end{code}
%if False
\begin{code}
instance Functor (StackF elem) where
    fmap f (Push x k) = Push x (f k)
    fmap f (Pop k) = Pop (f . k)
\end{code}
%endif

The handler for mutable state |hStack| then works as follows:
\begin{code}
hStack :: (Functor f) 
       => Free (StackF e :+: f) a 
       -> Stack s e 
       -> STT s (Free f) a
hStack = fold gen (alg # fwd)
  where 
    gen                   = const . return
    alg (Push x k)  stack = liftST (pushStack x stack)  >> k stack
    alg (Pop k)     stack = liftST (popStack stack)     >>= \x -> k x stack
    fwd y           stack = STT $ \s -> Op ((\f -> unSTT (f stack) s) <$> y)
\end{code}

%if False
\begin{code}
showStack :: Show a => Stack s a -> ST s String
showStack (Stack stackRef sizeRef) = do
    stack <- readSTRef stackRef
    elems <- getElems stack
    size  <- readSTRef sizeRef
    return $ show (take size elems)

test = runST $ do
    stack <- emptyStack
    pushStack (5 :: Int) stack
    pushStack 6 stack
    pushStack 7 stack
    pushStack 8 stack
    Just x <- popStack stack
    Just y <- popStack stack
    Just z <- popStack stack
    Just q <- popStack stack
    return [x, y, z, q]
\end{code}
%endif

%-------------------------------------------------------------------------------
\subsection{Undo Semantics}
\label{sec:undo-semantics}

% backtracking in local state

In \Cref{sec:local-global} we have discussed how to simulate local state using
a global state.
But, using |putR|, we clearly make the implicit copying of the local-state 
semantics explicit in the global-state semantics. 
This is problematic if the state is big, e.g. a long array.
Instead, we would want to keep track of the modifications made to the state, 
and possibly undo them when necessary.
As mentioned in \Cref{sec:transforming-between-local-and-global-state}, rather
than using |put|, some algorithms typically use a pair of commands |modify next|
and |modify prev| to update and roll back the state, respectively.
Here, |next| and |prev| represent the modifications to the state, with |next . prev = id|.
This approach is especially recommended when the state is represented using 
an array or other data structure that is usually not overwritten in its entirety.
Following a style similar to |putR|, this can be modelled as follows:
\begin{code}
modifyR :: MStateNondet s m => (s -> s) -> (s -> s) -> m ()
modifyR next prev = modify next `mplus` side (modify prev)
\end{code}

Unlike |putR|, |modifyR| does not keep any copies of the old state alive, as it does 
not introduce a branchgin point where the right branch refers to a variable
introduced outside the branching point. 










