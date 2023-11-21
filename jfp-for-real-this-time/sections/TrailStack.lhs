%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module TrailStack where

import Background
import Overview
import Control.Monad (ap, liftM, liftM2)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import LocalGlobal hiding (ModifyF)
import Undo
import MutableState
import Debug.Trace

\end{code}
%endif

\subsection{Trail Stack}
\label{sec:trail-stack}

The trail stack contains elements of type |Either s ()|.
The |Left s| means a state of type |s|; the |Right ()| means a time stamp.

The following naive implementation uses |StateF| and stores the whole
state in the trail stack.

\begin{code}
local2trail :: (Functor f)
            => Free (StateF s :+: NondetF :+: f) a -- local state
            -> Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a -- global state and stack
local2trail = fold Var (alg1 # alg2 # fwd)
  where
    alg1 (Put s k)  = do t <- get; push (Left t); put s; k
    alg1 oth        = Op . Inl $ oth
    alg2 (Or p q)   = Op . Inr . Inl $ Or (do push (Right ()); p) (do undoTrail; q)
    alg2 oth        = Op . Inr . Inl $ oth
    fwd op          = Op . Inr . Inr . Inr $ op
    undoTrail = do  top <- pop;
                    case top of
                      Nothing -> return ()
                      Just (Right ()) -> return ()
                      Just (Left s) -> do put s; undoTrail

    push e = Op . Inr . Inr . Inl $ Push e (return ())
    pop = Op . Inr . Inr . Inl $ Pop return
\end{code}

We have the following theorem.
< hLocal = fmap (fmap fst . runhStack ()) . hGlobal . local2trail

%if False
\begin{code}
t1 :: Functor f => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
t1 = hLocal

t2 :: (Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
t2 = fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . local2trail
\end{code}
%endif

The n-queens example using the trail stack:
\begin{code}
queensTrail :: Int -> [[Int]]
queensTrail = hNil . flip (fmap (fmap fst . runhStack ()) . hGlobal . local2trail) (0, []) . queens
\end{code}

The following version which uses |ModifyF| is more efficient.

\begin{code}
local2trailM :: (Functor f)
             => Free (ModifyF s r :+: NondetF :+: f) a -- local state
             -> Free (ModifyF s r :+: NondetF :+: StackF (Either r ()) () :+: f) a -- global state and stack
local2trailM = fold Var (alg1 # alg2 # fwd)
  where
    alg1 (MUpdate r k)  = do push (Left r); update r; k
    alg1 oth            = Op . Inl $ oth
    alg2 (Or p q)       = Op . Inr . Inl $ Or (do push (Right ()); p) (do undoTrail; q)
    alg2 Fail           = Op . Inr . Inl $ Fail
    fwd op              = Op . Inr . Inr . Inr $ op
    undoTrail = do  top <- pop;
                    case top of
                      Nothing -> return ()
                      Just (Right ()) -> return ()
                      Just (Left r) -> do restore r; undoTrail

    push e = Op . Inr . Inr . Inl $ Push e (return ())
    pop = Op . Inr . Inr . Inl $ Pop return
\end{code}

We can combine it with either |hGlobalM| or |hGlobalMu|, giving two
theorems as follows (with different typeclass conditions).

< hLocal = fmap (fmap fst . runhStack ()) . hGlobalM . local2trailM
< hLocal = fmap (fmap fst . runhStack ()) . hGlobalMu . local2trailM
%if False
\begin{code}
tM :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
tM = fmap (fmap fst . runhStack ()) . hGlobalM . local2trailM

tMu :: (Functor f, MUndo st r, MIM st s)
    => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
tMu = fmap (fmap fst . runhStack ()) . hGlobalMu . local2trailM
\end{code}
%endif

The n-queens example using the trail stack:

\begin{code}
queensTrailM :: Int -> [[Int]]
queensTrailM =
    hNil
  . flip (fmap (fmap fst . runhStack ()) . hGlobalM . local2trailM) (0, [])
  . queensM
queensTrailMu :: Int -> [[Int]]
queensTrailMu =
    hNil
  . flip (fmap (fmap fst . runhStack ()) . hGlobalMu . local2trailM) (0, [])
  . queensM
\end{code}
