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
% \section{Optimisation with Undo}
% \section{Modification-based State}
\section{Modelling Local State with Global State and Undo}
\label{sec:undo}

% backtracking in local state

In \Cref{sec:local2global}, we give a translation |local2global| which
simulates local state with global state by replacing |put| with its
state-restoring version |putR|.  The |putR| operation makes the
implicit copying of the local-state semantics explicit in the
global-state semantics. However, this copying still exists and can be
rather costly if the state is big (e.g., a long array), and especially
wasteful if the modifications made to that state are small (e.g., a
single entry in the array).
%
Fortunately, low-level features like the global-state semantics
give us more possibility to apply more fine-grained optimisation
strategies.
%
As a result, instead of copying the whole state to implement the
backtracking behaviour in the global-state semantics, we can just keep
track of the modifications made to the state, and undo them when
necessary.
%
%This is especially efficient when we have mutable states or in-place
%update.
In this section, we formalise this intuition with a translation from
the local-state semantics to the global-state semantics for restorable
state updates.

\subsection{State Update and Restoration}

We first need to characterise a specific subset of state effects where
all state update operations can be undone. We call them
modification-based state effects.
%
% We first need to characterise restorable updates.
%
For example, the |queens| program in
\Cref{sec:motivation-and-challenges} uses the operation |s `plus` r|
to update the state.
%
We can undo it using the following |`minus` r| operation which is
essentially the left inverse of |`plus` r|.
% It is restorable as we can define its left inverse as follows:
\begin{spec}
minus   :: (Int, [Int]) -> Int -> (Int, [Int])
minus   (c, sol) r = (c-1, tail sol)
\end{spec}
%
These two operators satisfy the equation |(`minus` r) . (`plus` r) = id|
for any |r :: Int|.
%
% Then, instead of copying the whole state like what we did in the
% simulation |local2global|, we can just use |s `minus` r| to roll back
% the update.

In general, we define a typeclass |Undo s r| with two operations
|plus| and |minus| to characterise restorable state updates. Here, |s|
is the type of states and |r| is the type of deltas.  We can
implement the previous state update and restoration operations of
n-queens as an instance |Undo (Int, [Int]) Int| of the typeclass.
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
Instances of |Undo| should satisfy the following law which says
|`minus` x| is a left inverse of |`plus` x|:
\begin{alignat}{2}
    &\mbox{\bf plus-minus}:\quad &
      |(`minus` x) . (`plus` x)| ~=~ & |id| \label{eq:plus-minus} \mbox{~~.}
\end{alignat}


Modification-based state effects restrict the general |put| operation
of |MState| to modification oprations.  We define a new typeclass
|MModify s r m| which inherits from |Monad m| and |Undo s r| to
capture the interfaces of state updates and restoration.  It has three
operations: a |mget| operation that reads and returns the state
(similar to the |get| operation of |MState|), a |update r| operation
that updates the state with the delta |r|, and a |restore r|
operations that restores the update introduced by the delta |r|.
%
Note that only the |mget| and |update| operations are expected to be
used by programmers; |restore| operations are automatically generated
by the translation to the global-state semantics.

% Then, in order to make sure that every state update is given in the
% form of a modification which can be restored, we define a new
% typeclass |MModify| which restricts the |put| operation of |MState|
% to |update| and |restore|.

\begin{code}
class (Monad m, Undo s r) => MModify s r m | m -> s, m -> r where
    mget     :: m s
    update   :: r -> m ()
    restore  :: r -> m ()
\end{code}
%
The three operations satisfy the following laws:
\begin{alignat}{2}
    &\mbox{\bf mget-mget}:\quad &
    |mget >>= (\s -> mget >>= k s)| &= |mget >>= (\s -> k s s)|
    ~~\mbox{,} \label{eq:mget-mget} \\
    &\mbox{\bf update-mget}:~ &
    |mget >>= \s -> update r >> return (s `plus` r)|
    &=
    |update r >> mget|
    ~~\mbox{,} \label{eq:update-mget}\\
    &\mbox{\bf restore-mget}:~ &
    |mget >>= \s -> restore r >> return (s `minus` r)|
    &=
    |restore r >> mget|
    ~~\mbox{,} \label{eq:restore-mget}\\
    &\mbox{\bf update-restore}:\quad &
    |update r >> restore r| &= |return ()|
    ~~\mbox{.} \label{eq:update-restore}
\end{alignat}
The first law for |mget| corresponds to that for |get|. The second
and third law respecively capture the impact of |update| and |restore|
on |mget|. Finally, the fourth law expresses that |restore| undoes the effect of
|update|.
%
% As in \Cref{sec:state}, we can also implement the state monad as an
% instance of |MModify|.
% \begin{code}
% instance MModify s r (State s) where
%   mget = State (\s -> (s,s))
%   update = undefined
%   restore = undefined
% \end{code}

As what we did for the nondeterminism and state effects in
\Cref{sec:free-monads-and-their-folds}, we define a new signature
|ModifyF| representing the syntax of modification-based state effects,
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

Note that here we still use the |StateT| monad transformer and
immutable states for the clarity of presentation and simplicity of
proofs. The |plus| and |minus| operations also take immutable
arguments. To be more efficient, we can use mutable states to
implement in-place updates or use the technique of functional but
in-place update~\citep{LorenzenLS23}. We will discuss mutable states
in \Cref{sec:mutable-states}.

Similar to \Cref{sec:local-state} and \Cref{sec:global-state}, the
local-state and global-state semantics of |ModifyF| and |NondetF| are
given by the following functions |hLocalM| and |hGlobalM|, respectively.
%
\begin{code}
hLocalM   :: (Functor f, Undo s r)
          => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
hLocalM   = fmap (fmap (fmap fst) . hNDf) . runStateT . hModify

hGlobalM  :: (Functor f, Undo s r)
          => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
hGlobalM  = fmap (fmap fst) . runStateT . hModify . hNDf . comm2
\end{code}

\subsection{Simulating Local State with Global State and Undo}
\label{sec:local2globalM}

% To simulate the local-state semantics with global-state semantics,
% instead of using the translation |local2global| defined in
% \Cref{sec:local2global} which uses the inefficient operation |putR|,
% we can give another translation |local2globalM| as follows which makes
% use of |restore| to roll back updates.
% %
% Similar to |putR|, it also uses |`mplus`| to implement backtracking.
We can implement the translation from local-state semantics to
global-state semantics for the modification-based state effects
in a similar style to the translation |local2global| in
\Cref{sec:local2global}.
%
The translation |local2globalM| still uses the mechanism of
nondeterminism to store the deltas used by previous updates.
%
In \Cref{sec:trail-stack} we will show a lower-level simulation of
local-state semantics without relying on nondeterminism.
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

Compared to |local2global|, the main difference is that we do not need
to copy and store the whole state. Instead, we store the delta |r| and
undo the state update using |restore r| in the second branch.
%
The following theorem shows the correctness of |local2globalM|.
%
% \vspace{-\baselineskip}
% \begin{theorem}
\begin{restatable}[]{theorem}{modifyLocalGlobal}
\label{thm:modify-local-global}
Given |Functor f| and |Undo s r|, the equation
< hGlobalM . local2globalM = hLocalM
holds for all programs |p :: Free (ModifyF s r :+: NondetF :+: f) a|
that do not use the operation |Op (Inl MRestore _ _)|.
\end{restatable}
% \end{theorem}
%
The proof of this theorem can be found in \Cref{app:modify-local-global}.
% The proof structure is very similar to that in
% \Cref{app:local-global}.

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
\paragraph*{N-queens with State Update and Restoration}\
%
We can rewrite the |queens| program with modification-based state and
nondeterminism. Compared to the |queens| in
\Cref{sec:motivation-and-challenges}, we only need to change the |get|
and |put (s `plus` r)| with the update operation |update r|.
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

We can interpret it using |hLocalM| or |hGlobalM| composed with
|local2globalM|.
\begin{code}
queensLocalM :: Int -> [[Int]]
queensLocalM = hNil . flip hLocalM (0, []) . queensM

queensGlobalM :: Int -> [[Int]]
queensGlobalM = hNil . flip hGlobalM (0, []) . local2globalM . queensM
\end{code}

We can also further combine it with the |nondet2state| in
\Cref{sec:nondet2state}.
\begin{code}
queensStateM  :: Int -> [[Int]]
queensStateM  = hNil
              . fmap fst . flip runStateT (0, []) . hModify
              . runNDf . comm2
              . local2globalM . queensM
\end{code}

%if False
\begin{code}
queensF :: (MModify (Int, [Int]) Int m, MNondet m) => Int -> m [Int]
queensF n = loop where
  loop = do  (c, sol) <- mget
             if c >= n then return sol
             else do  r <- choose [1..n]
                      guard (safe r 1 sol)
                      update r `mplus` side (restore r)
                      loop

queensGlobalF :: Int -> [[Int]]
queensGlobalF = hNil . flip hGlobalM (0, []) . queensF

queensStateF  :: Int -> [[Int]]
queensStateF  = hNil
              . fmap fst . flip runStateT (0, []) . hModify
              . (extractSS . hState . nondet2state) . comm2
              . queensF
\end{code}
%endif

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
