%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Undo where

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
\section{Optimisation with Undo}
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

In general, we define a type-class |Undo s r| and implement |Undo
(Int, [Int]) Int| as an instance using the previously defined |plus|
and |minus|.
%
All instances of |Undo s r| satisfy the law |(`minus` x) . (`plus` x)
= id| for any |x :: r|.
% In general, we define a |modify| function as follows.
% \begin{code}
% modfun           :: MState s m => (s -> s) -> m ()
% modfun f         = get >>= put . f
% \end{code}
%
% If all the state updates in a program are given by some |modify fwd|
% where every |fwd| is accompanied with a left inverse |bwd| such that
% |bwd . fwd = id|, we can simulate its local-state semantics with
% global-state semantics by using |modify bwd| to roll back the updates.
%
In order to make sure that every state update is given in the form of
modification which can be restored, we define a new typeclass
|MModify| which restricts the |put| operation of |MState| to |update|
and |restore|.
\begin{code}
class Monad m => MModify s r m | m -> s, m -> r where
    mget     :: m s
    update   :: r -> m ()
    restore  :: r -> m ()
\end{code}
%
The two operations |update| and |restore| satisfy the following law.
\begin{alignat}{2}
    &\mbox{\bf update-restore}:\quad &
    |update r >> restore r| &= |return ()|~~\mbox{.} \label{eq:update-restore}
\end{alignat}

We also define a new functor |ModifyF| representing the syntax, and
implement the free monad |Free (ModifyF s r :+: f)| as an instance of
|MModify s r|.
\begin{code}
data ModifyF s r a = MGet (s -> a) | MUpdate r a | MRestore r a
\end{code}
%
%if False
\begin{code}
instance Functor (ModifyF s r) where
    fmap f (MGet s)        = MGet (f . s)
    fmap f (MUpdate r x)   = MUpdate r (f x)
    fmap f (MRestore r x)  = MRestore r (f x)
\end{code}
%endif
\begin{code}
instance Functor f => MModify s r (Free (ModifyF s r :+: f)) where
  mget       =  Op (Inl (MGet return))
  update r   =  Op (Inl (MUpdate r (return ())))
  restore r  =  Op (Inl (MRestore r (return ())))
\end{code}


We can implement a handler for |ModifyF| straightforwardly as follows.
\begin{code}
hModify :: (Functor f, Undo s r) => Free (ModifyF s r :+: f) a -> StateT s (Free f) a
hModify = fold gen (alg # fwd)
  where
    gen x               = StateT $ \s -> return (x, s)
    alg (MGet k)        = StateT $ \s -> runStateT (k s) s
    alg (MUpdate r k)   = StateT $ \s -> runStateT k (s `plus` r)
    alg (MRestore r k)  = StateT $ \s -> runStateT k (s `minus` r)
    fwd y               = StateT $ \s -> Op (fmap (\k -> runStateT k s) y)
\end{code}
%
It is easy to check that the update-restore law holds contextually up
to interpretation with |hModify|.

Similar to \Cref{sec:local-state} and \Cref{sec:global-state}, the
local-state and global-state semantics with modify are given by
the following |hLocalM| and |hGlobalM|, respectively.
%
\begin{code}
hLocalM   :: (Functor f, Undo s r)
          => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
hLocalM   = fmap (fmap (fmap fst) . hNDf) . runStateT . hModify
hGlobalM  :: (Functor f, Undo s r)
          => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
hGlobalM  = fmap (fmap fst) . runStateT . hModify . hNDf . comm2
\end{code}
%
To simulate the local-state semantics with global-state semantics,
instead of using the translation |local2global| defined in
\Cref{sec:local2global} which uses the inefficient operation |putR|,
we can give another translation |local2globalM| as follows which makes
use of |restore| to roll back updates.
%
Similar to |putR|, it also uses |`mplus`| to implement backtracking.
%
\begin{code}
local2globalM  :: (Functor f, Undo s r)
               => Free (ModifyF s r :+: NondetF :+: f) a
               -> Free (ModifyF s r :+: NondetF :+: f) a
local2globalM  = fold Var alg
  where
    alg (Inl (MUpdate r k)) = (update r `mplus` restore r) >> k
    alg p               = Op p
\end{code}

The following theorem shows that the simulation of local-state
semantics with global-state semantics given by |modify2global|
coincides with the local-state semantics given by |modify2local|.
%
\begin{theorem}\label{thm:modify-local-global}
< hGlobalM . local2globalM = hLocalM
\end{theorem}
\wenhao{TODO: prove it.}

% Observe that, unlike |putR|, the interpretation of |modifyR| in
% |modify2global| does not hold onto a copy of the old state.
% %
% Although the |modify| function still takes out the whole state and
% apply a function to it, it can be more efficient with in-place
% update~\citep{LorenzenLS23} or mutable states.

% WT: An old version which uses translations from ModifyF to StateF.
%
% The local-state semantics of programs with |ModifyF| and |NondetF| is
% directly given by the local-state semantics of |StateF| and |NondetF|.
% We have the following translation |modify2local| which only uses |fwd|.
% %
% \begin{code}
% modify2local  :: (Functor f, Undo s r)
%               => Free (ModifyF s r :+: NondetF :+: f) a
%               -> Free (StateF s :+: NondetF :+: f) a
% modify2local  = fold Var alg
%   where
%     alg (Inl (MUpdate r k))  = modfun (`plus` r) >> k
%     alg (Inl (MRestore r k))  = modfun (`minus` r) >> k
%     alg (Inl (MGet k))      = get >>= k
%     alg (Inr p)             = Op (Inr p)
% \end{code}
% %
% To simulate the local-state semantics with global-state semantics,
% instead of using the translation |local2global| which uses the
% inefficient operation |putR|, we can give another translation
% |modify2global| as follows which makes use of |bwd| to roll back updates.
% %
% Similar to |putR|, it also uses |`mplus`| to implement backtracking.
% %
% \begin{code}
% modify2global  :: (Functor f, Undo s r)
%                => Free (ModifyF s r :+: NondetF :+: f) a
%                -> Free (StateF s :+: NondetF :+: f) a
% modify2global  = fold Var alg
%   where
%     alg (Inl (MUpdate r k))  = (modfun (`plus` r) `mplus` modfun (`minus` r)) >> k
%     alg (Inl (MRestore r k)) = error "no"
%     alg (Inl (MGet k))       = get >>= k
%     alg (Inr p)              = Op (Inr p)
% \end{code}

% The following theorem shows that the simulation of local-state
% semantics with global-state semantics given by |modify2global|
% coincides with the local-state semantics given by |modify2local|.
% %
% \begin{theorem}\label{thm:modify-local-global}
% < hGlobal . modify2global = hLocal . modify2local
% \end{theorem}
% \wenhao{TODO: prove it.}

% Combining it with \Cref{thm:local-global}, we also have
% < hGlobal . modify2global = hGlobal . local2global . modify2local

% Observe that, unlike |putR|, the interpretation of |modifyR| in
% |modify2global| does not hold onto a copy of the old state.
% %
% Although the |modify| function still takes out the whole state and
% apply a function to it, it can be more efficient with in-place
% update~\citep{LorenzenLS23} or mutable states.


%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{N-queens with |modifyR|}\
%
Now we can rewrite the |queens| program with modify and nondeterminism.
\begin{code}
queensM :: (MModify (Int, [Int]) Int m, MNondet m) => Int -> m [Int]
queensM n = loop where
  loop = do  (c, sol) <- mget
             if c >= n then return sol
             else do  r <- choose [1..n]
                      guard (safe r 1 sol)
                      update r
                      loop
\end{code}
% %
% It is not hard to see that
% %
% < modify2local queensR = queens
%
By \Cref{thm:modify-local-global}, we have
< hGlobalM (local2globalM queensR) = hLocalM queensR

% The advantage of the left-hand side is that it does not keep any copies of
% the state alive.