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

module Combination where

import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef

import Background
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

The function |queensS| constructs a program which uses the operation of stack and nondeterminism to directly solve the n-queens problem.

\begin{code}
queensS :: Int -> Free (StackF (Int, [Int]) :+: NondetF) [Int]
queensS n = push (0, []) >> loop
  where
    loop = do  s <- pop
               case s of
                 Nothing -> mzero
                 Just (c, sol) ->
                    if c >= n then return sol
                    else do  r <- choose [1..n]
                             filtr valid (r:sol)
                             push ((c, sol) `plus` r)
                             loop

push :: Functor g => e -> Free (StackF e :+: g) ()
push e = Op . Inl $ Push e (return ())
pop :: Functor g => Free (StackF e :+: g) (Maybe e)
pop = Op . Inl $ Pop return

instance Functor f => MNondet (Free (f :+: NondetF)) where
  mzero = Op . Inr $ Fail
  mplus x y = Op . Inr $ Or x y
\end{code}

The function |queensStackBFS| runs the |queens| by applyin the handlers of stack and nondeterminism sequentially.
\begin{code}
queensStackBFS :: Int -> [[Int]]
queensStackBFS n = hND $ runSTT (liftST emptyStack >>= ((hStack (queensS n)) $))
\end{code}


The code below simulates the nondeterminism with the mutable stack.
\begin{code}
type CompSK s f b a = Free (StateF b :+: StackF s :+: f) a
data SK f a = SK { unSK :: CompSK (SK f a) f [a] () }

getSK :: Functor f => Free (StateF s :+: f) s
getSK = Op . Inl $ Get return

putSK :: Functor f => s -> Free (StateF s :+: f ) ()
putSK s = Op . Inl $ Put s (return ())

popSK' :: Functor f => CompSK s f b (Maybe s)
popSK' = Op . Inr . Inl $ Pop return

pushSK' :: Functor f => s -> CompSK s f b ()
pushSK' s = Op . Inr . Inl $ Push s (return ())

popSK :: Functor f => CompSK (SK f a) f [a] ()
popSK = do
  mtop <- popSK'
  case mtop of
    Nothing -> return ()
    Just (SK top) -> top

pushSK :: Functor f => CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
pushSK q p = do
  pushSK' (SK q)
  p

appendSK :: Functor f => a -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
appendSK x p = do
  xs <- getSK
  putSK (xs ++ [x])
  p

-- simulation of nondeterminism with stack
nondet2stack :: Functor f => Free (NondetF :+: f) a -> CompSK (SK f a) f [a] ()
nondet2stack = fold gen (alg # fwd)
  where
    gen :: Functor f => a -> CompSK (SK f a) f [a] ()
    gen x         = appendSK x popSK
    alg :: Functor f => NondetF (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
    alg Fail      = popSK
    alg (Or p q)  = pushSK q p
    fwd :: Functor f => f (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
    fwd y = Op (Inr (Inr y))


runNDSK :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDSK p = let t = runSTT $ liftST emptyStack >>= ((hStack . flip runStateT [] . hState $ nondet2stack p) $) in fmap snd t

queensStack   :: Int -> [[Int]]
queensStack   = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . runNDSK . comm2
              . local2global . queens

queensStackR :: Int -> [[Int]]
queensStackR = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . runNDSK . comm2
              . queensR
\end{code}
