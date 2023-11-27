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
import Debug.Trace as DT

import Background
import Overview
import LocalGlobal (local2global, hLocal, comm2, side)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero, get, put, modify, guard, State)

\end{code}
%endif

%-------------------------------------------------------------------------------
\section{Optimisation with Undo}
\label{sec:undo}

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

\paragraph*{State Updates and Restoration}\
To characterise restorable state updates in general, we define a
typeclass |Undo s r| with two operations |plus| and |minus| and
implement |Undo (Int, [Int]) Int| as an instance using our previous
definitions of operations.
%
\begin{spec}
class Undo s r where
  plus   :: s -> r -> s
  minus  :: s -> r -> s
instance Undo (Int, [Int]) Int where
  plus (c, sol) r   = (c+1, r:sol)
  minus (c, sol) r  = (c-1, tail sol)
\end{spec}
%
Instances of |Undo| should satisfy the following law:
\begin{alignat}{2}
    &\mbox{\bf plus-minus}:\quad &
      |(`minus` x) . (`plus` x)| ~=~ & |id| \label{eq:plus-minus} \mbox{~~.}
\end{alignat}

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

% Then, in order to make sure that every state update is given in the
% form of a modification which can be restored, we define a new
% typeclass |MModify| which restricts the |put| operation of |MState| to
% |update| and |restore|.
Then, we define a new subclass |MModify s r m| of |Monad m| and |Undo
s r| to capture the interfaces of state updates and restoration.
It has three operations: a |mget| operation that reads and returns the
state (similar to the |get| operation of |MState|), a |update r|
operation that updates the state with the delta |r|, and a |restore r|
operations that restores the update introduced by the delta |r|.
\begin{code}
class (Monad m, Undo s r) => MModify s r m | m -> s, m -> r where
    mget     :: m s
    update   :: r -> m ()
    restore  :: r -> m ()
\end{code}
%
The two operations |update| and |restore| satisfy the following law:
\begin{alignat}{2}
    &\mbox{\bf mget-mget}:\quad &
    |mget >>= (\s -> mget >>= k s)| &= |mget >>= (\s -> k s s)|
    ~~\mbox{,} \label{eq:get-get} \\
    &\mbox{\bf update-get}:~ &
    |get >>= \s -> update r >> return (s `plus` r)|
    &=
    |update r >> get|
    ~~\mbox{,} \label{eq:update-get}\\
    &\mbox{\bf restore-get}:~ &
    |get >>= \s -> restore r >> return (s `minus` r)|
    &=
    |restore r >> get|
    ~~\mbox{,} \label{eq:restore-get}\\
    &\mbox{\bf update-restore}:\quad &
    |update r >> restore r| &= |return ()|
    ~~\mbox{.} \label{eq:update-restore}
\end{alignat}
%
% As in \Cref{sec:state}, we can also implement the state monad as an
% instance of |MModify|.
% \begin{code}
% instance MModify s r (State s) where
%   mget = State (\s -> (s,s))
%   update = undefined
%   restore = undefined
% \end{code}

As what we did for nondeterminism and state effects in
\Cref{sec:free-monads-and-their-folds}, we define a new signature
|ModifyF| representing the syntax of state updates and restoration,
and implement the free monad |Free (ModifyF s r :+: f)| as an instance
of |MModify s r|.
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
instance (Functor f, Undo s r) => MModify s r (Free (ModifyF s r :+: f)) where
  mget       =  Op (Inl (MGet return))
  update r   =  Op (Inl (MUpdate r (return ())))
  restore r  =  Op (Inl (MRestore r (return ())))
\end{code}

% We can implement a handler for |ModifyF| straightforwardly as follows.
The following handler |hModify| maps this free monad to the |StateT|
monad transformer using the operations |plus| and |minus| provided by
|Undo s r|.
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
It is easy to check that the four laws hold contextually up to
interpretation with |hModify|.

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
    alg (Inl (MUpdate r k)) = (update r `mplus` side (restore r)) >> k
    alg p               = Op p
\end{code}

The following theorem shows that the simulation of local-state
semantics with global-state semantics given by |modify2global|
coincides with the local-state semantics given by |modify2local|.
%
% \begin{theorem}
\begin{restatable}[]{theorem}{modifyLocalGlobal}
\label{thm:modify-local-global}
Given |Functor f| and |Undo s r|, the equation
< hGlobalM . local2globalM = hLocalM
holds for all programs |p :: Free (ModifyF s r :+: NondetF :+: f) a|
that do not use the operation |Op (Inl MRestore _ _)|.
\end{restatable}
% \end{theorem}

The proof of this theorem can be found in \Cref{app:modify-local-global}.
The proof structure is very similar to that in
\Cref{app:local-global}.

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

We have the following program:
\begin{code}
queensGlobalM :: Int -> [[Int]]
queensGlobalM = hNil . flip hGlobalM (0, []) . local2globalM . queensM

queensLocalM :: Int -> [[Int]]
queensLocalM = hNil . flip hLocalM (0, []) . queensM
\end{code}

% By \Cref{thm:modify-local-global}, we have
% < hGlobalM (local2globalM (queensM n)) = hLocalM (queensM n)

% The advantage of the left-hand side is that it does not keep any copies of
% the state alive.

%if False
% Just for testing code:
\begin{code}
hModify11  :: (Functor f, Undo s r) => Free (ModifyF s r :+: f) a -> (s -> Free f (a, s))
hModify11  =  fold genS (algS # fwdS)
  where
    genS x               s = Var (x, s)
    algS :: (Undo s r) => ModifyF s r (s -> p) -> s -> p
    algS (MGet k)        s = k s s
    algS (MUpdate r k)   s = k (s `plus` r)
    algS (MRestore r k)  s = k (s `minus` r)
    fwdS y               s = Op (fmap ($s) y)

-- hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
hL :: (Functor f, Functor g) => g (Free (NondetF :+: f) (a, s)) -> g (Free f [a])
hL = fmap (fmap (fmap fst) . _hNDf)

_hNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
_hNDf  =  fold genNDf (algNDf # fwdNDf)
  where
    genNDf           = Var . return
    algNDf Fail      = Var []
    algNDf (Or p q)  = liftM2 (++) p q
    fwdNDf op        = Op op

algSRHS :: (Undo s r) => ModifyF s r (s -> p) -> (s -> p)
algSRHS (MGet k)    = \ s -> k s s
algSRHS (MUpdate r k)  = \ s -> k (s `plus` r)
algSRHS (MRestore r k)  = \ s -> k (s `plus` r)

algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
algNDRHS Fail      = \ s -> Var []
algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)

fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
fwdRHS op = \s -> Op (fmap ($s) op)

\end{code}

\begin{code}
_local2globalM  :: (Functor f, Undo s r)
               => Free (ModifyF s r :+: NondetF :+: f) a
               -> Free (ModifyF s r :+: NondetF :+: f) a
_local2globalM  = fold Var alg
  where
    alg (Inl (MUpdate r k)) = (update r `mplus` side (restore r)) >> k
    alg p               = Op p

genLHS :: Functor f => a -> (s -> Free f [a])
genLHS x = \s -> Var [x]

algSLHS :: (Functor f, Undo s r) => ModifyF s r (s -> Free f [a]) -> (s -> Free f [a])
algSLHS (MGet k)       =  \s -> k s s
algSLHS (MUpdate r k)  = \ s -> k (s `plus` r)
algSLHS (MRestore r k) = \ s -> k (s `plus` r)

algNDLHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
algNDLHS Fail      = \s -> Var []
algNDLHS (Or p q)  = \s -> liftM2 (++) (p s) (q s)

fwdLHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
fwdLHS op = \s -> Op (fmap ($ s) op)

test :: (Functor f, Undo s r) => f (Free (ModifyF s r :+: NondetF :+: f) a) -> (s -> Free f [a])
test = fwdLHS . fmap hGlobalM
\end{code}
%endif
