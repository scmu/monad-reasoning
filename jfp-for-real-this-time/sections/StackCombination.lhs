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

module StackCombination where

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

\subsection{Mutable State}
\label{sec:mutable-state}

Another implementation that combines two states.

\begin{code}
data Stack s b a = Stack {  getStack  ::  STRef s  (STArray s Index a),
                            getSize   ::  STRef s  Index,
                            getInfo   ::  STRef s  b }

type Index = Int
\end{code}

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
growStack :: b -> Index -> [a] -> ST s (Stack s b a)
growStack info space elems = do
    stack     <- newListArray (0, space) elems
    sizeRef   <- newSTRef (length elems)
    stackRef  <- newSTRef stack
    infoRef   <- newSTRef info
    return (Stack stackRef sizeRef infoRef)
\end{code}
\caption{Growing the stack.}
\label{fig:grow}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
emptyStack :: b -> ST s (Stack s b a)
emptyStack info = do
    stack     <- newArray_ (0, 1)
    sizeRef   <- newSTRef 0
    stackRef  <- newSTRef stack
    infoRef   <- newSTRef info
    return (Stack stackRef sizeRef infoRef)
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
pushStack :: a -> Stack s b a -> ST s ()
pushStack x (Stack stackRef sizeRef infoRef) = do
    stack       <- readSTRef stackRef
    size        <- readSTRef sizeRef
    info        <- readSTRef infoRef
    (_, space)  <- getBounds stack
    writeSTRef sizeRef (size + 1)
    if size < space
    then writeArray stack size x
    else do
        elems                <- getElems stack
        Stack stackRef' _ _  <- growStack info (space * 2) elems
        stack'               <- readSTRef stackRef'
        writeArray  stack' size x
        writeSTRef  stackRef stack'
\end{code}
\caption{Pushing to the stack.}
\label{fig:pushstack}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
popStack :: Stack s b a -> ST s (Maybe a)
popStack (Stack stackRef sizeRef infoRef) = do
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

\begin{code}
getInfoSt :: Stack s b a -> ST s b
getInfoSt (Stack _ _ infoRef) = do
    info  <- readSTRef infoRef
    return info

putInfoSt :: b -> Stack s b a -> ST s ()
putInfoSt b (Stack _ _ infoRef) = do
    writeSTRef infoRef b
\end{code}

The functor |StackF| represents the action of
pushing to and popping from the stack.
This is very similar to the |StateF| functor, except for the |Maybe| in the
codomain of the |Pop| element.
This optional value may be |Nothing| when the stack is empty.
\begin{code}
data StackF e b a = Push e a | Pop (Maybe e -> a) | GetSt (b -> a) | PutSt b a
\end{code}
%if False
\begin{code}
instance Functor (StackF elem info) where
    fmap f (Push x k)   = Push x (f k)
    fmap f (Pop k)      = Pop (f . k)
    fmap f (GetSt s)    = GetSt (f . s)
    fmap f (PutSt s x)  = PutSt s (f x)
\end{code}
%endif


The handler for mutable state |hStack| then works as follows:
\begin{code}
hStack :: (Functor f)
       => Free (StackF e b :+: f) a
       -> Stack s b e
       -> STT s (Free f) (a, b)
hStack = fold gen (alg # fwd)
  where
    -- a -> Stack s b e -> STT s (Free f) (a, b)
    gen x            stack = liftST (getInfoSt stack)    >>= \b -> return (x, b)
    alg (Push x k)   stack = liftST (pushStack x stack)  >> k stack
    alg (Pop k)      stack = liftST (popStack stack)     >>= \x -> k x stack
    alg (GetSt k)    stack = liftST (getInfoSt stack)    >>= \x -> k x stack
    alg (PutSt x k)  stack = liftST (putInfoSt x stack)  >> k stack
    fwd y            stack = STT $ \s -> Op ((\f -> unSTT (f stack) s) <$> y)
\end{code}


The code below simulates the nondeterminism with the mutable stack.
\begin{code}
type CompSK s f b a = Free (StackF s b :+: f) a
data SK f a = SK { unSK :: CompSK (SK f a) f [a] () }

getSK :: Functor f => Free (StackF s b :+: f) b
getSK = Op . Inl $ GetSt return

putSK :: Functor f => b -> Free (StackF s b :+: f ) ()
putSK b = Op . Inl $ PutSt b (return ())

popSK' :: Functor f => CompSK s f b (Maybe s)
popSK' = Op . Inl $ Pop return

pushSK' :: Functor f => s -> CompSK s f b ()
pushSK' s = Op . Inl $ Push s (return ())

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

nondet2stack :: Functor f => Free (NondetF :+: f) a -> CompSK (SK f a) f [a] ()
nondet2stack = fold gen (alg # fwd)
  where
    gen :: Functor f => a -> CompSK (SK f a) f [a] ()
    gen x         = appendSK x popSK
    alg :: Functor f => NondetF (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
    alg Fail      = popSK
    alg (Or p q)  = pushSK q p
    fwd :: Functor f => f (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
    fwd y = Op (Inr y)


runNDSK :: Functor f => Free (NondetF :+: f) a -> Free f [a]
-- runNDSK p = let t = runSTT $ liftST emptyStack >>= ((hStack . flip runStateT [] . hState $ nondet2stack p) $) in fmap snd t
runNDSK p = let t = runSTT $ liftST (emptyStack []) >>= ((hStack $ nondet2stack p) $) in fmap snd t

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
% still slower than queensState and queensStateR

% queensState  9: 4.3, 4.02
% queensStateR 9: 4.08, 3.96
% queensStack  9: 4.21, 
% queensStackR 9: 4.32, 4.17