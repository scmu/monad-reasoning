%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module TrailStack where

import Background
import Overview
import Control.Monad (ap, liftM, liftM2)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import LocalGlobal hiding (ModifyF)
import MutableState
import Debug.Trace

\end{code}
%endif

\subsection{Trail Stack}
\label{sec:trail-stack}

The trail stack contains elements of type |Either s ()|.
The |Left s| means a state of type |s|; the |Right ()| means a time stamp.
The current implementation is not efficient because we store the whole state in the trail stack for every operation.
Another option is to store the |`minus` r| in the trail stack.

\begin{code}
local2trail :: (Functor f)
            => Free (StateF s :+: NondetF :+: f) a -- local state
            -> Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a -- global state and stack
local2trail = fold Var (alg1 # alg2 # fwd)
  where
    -- alg1 (Put s k)  = do t <- get; push (Left t); put s; k
    alg1 (Put s k)  = do t <- get; push (Left t); Op (Inl (Put s k))
    alg1 oth        = Op . Inl $ oth
    alg2 (Or p q)   = Op . Inr . Inl $ Or (do push (Right ()); p) (do undoTrail; q)
    alg2 oth        = Op . Inr . Inl $ oth
    fwd op          = Op . Inr . Inr . Inr $ op
    undoTrail = do  top <- pop;
                    case top of
                      Nothing -> return ()
                      Just (Right ()) -> return ()
                      Just (Left s) -> do put s; undoTrail

    push :: (Functor f1, Functor f2, Functor g) => e -> Free (f1 :+: (f2 :+: (StackF e b :+: g))) ()
    push e = Op . Inr . Inr . Inl $ Push e (return ())
    pop :: (Functor f1, Functor f2, Functor g) => Free (f1 :+: (f2 :+: (StackF e b :+: g))) (Maybe e)
    pop = Op . Inr . Inr . Inl $ Pop return

\end{code}

Simulation : |hLocal == t2|.
\begin{code}
t1 :: Functor f => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
t1 = hLocal

t2 :: (Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
t2 = fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . local2trail
\end{code}


% NOTE: for proof
%if False
\begin{code}
-- h1 . aaf = alg' . fmap h1
h1 :: Functor f => Free (StateF s :+: NondetF :+: StackF e () :+: f) a -> s -> Free f [a]
h1 = fmap (\ x -> fmap fst (runhStack () x)) . hGlobal

aaf :: Functor f => (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a) -> Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a
aaf = undefined

alg' :: Functor f => (StateF s :+: NondetF :+: f) (s -> Free f [a]) -> (s -> Free f [a])
alg' = alg1' # alg2' # fwd'
  where
    alg1' (Get k)    = \ s -> k s s
    alg1' (Put s k)  = \ _ -> k s
    alg2' Fail       = \ s -> Var []
    alg2' (Or p q)   = \ s -> liftM2 (++) (p s) (q s)
    fwd' y           = \ s -> Op (fmap ($s) y)


t :: Functor f => (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a)
t = undefined

qwq :: Functor f => (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a) -> Int
qwq t = case t of
      (Inr (Inr y)) ->
        let tmp     = \ s -> Op (fmap ((\ x -> fmap fst (runhStack () x)) . (\ k -> k s) . hGlobal) y)
        in let tmp' = \ s -> fmap fst (runhStack () (Op (fmap ((\ k -> k s) . hGlobal) (Inr y))))
        in 1
      _ -> 2
\end{code}
%endif

The n-queens example using the trail stack:
\begin{code}
queensLocal :: Int -> [[Int]]
queensLocal = hNil . flip hLocal (0, []) . queens

queensTrail :: Int -> [[Int]]
queensTrail = hNil . flip t2 (0, []) . queens
\end{code}

To better illustrate the idea of undo semantics, we introduce another version of state effect which uses |get| and |modify|.
\wenhao{We can also rewrite |queensR| using |ModifyF|.}
% class Undo s r where
  % plus :: s -> r -> s
  % minus :: s -> r -> s
\begin{code}

data ModifyF s r a = GetM (s -> a) | PlusM r a deriving Functor
-- instance MState s (Free (ModifyF s r)) where
--   get    =  Op (GetM return)
--   put s  =  Op (ModifyM (const s) (return ()))

hModify :: (Functor f, Undo s r) => Free (ModifyF s r :+: f) a -> (s -> Free f (a, s))
hModify = fold gen (alg # fwd)
  where
    gen x              s  = return (x, s)
    alg (GetM k)       s  = k s s
    alg (PlusM r k)    s  = k (s `plus` r)
    fwd y              s  = Op (fmap ($s) y)

getM :: Functor f => Free (ModifyF s r :+: f) s
getM = Op . Inl $ GetM return
plusM :: Functor f => r -> Free (ModifyF s r :+: f) ()
plusM r = Op . Inl $ PlusM r (return ())
\end{code}


\begin{code}
local2trailM :: (Functor f, Undo s r)
             => Free (ModifyF s r :+: NondetF :+: f) a -- local state
             -> Free (StateF s :+: NondetF :+: StackF (Either r ()) () :+: f) a -- global state and stack
local2trailM = fold Var (alg1 # alg2 # fwd)
  where
    -- alg1 (PlusM r k)  = do push (Left r); plusM r; k
    alg1 (PlusM r k)  = do push (Left r); s <- get; Op . Inl $ Put (s `plus` r) k
    alg1 (GetM k)     = Op . Inl $ Get k
    alg2 (Or p q)     = Op . Inr . Inl $ Or (do push (Right ()); p) (do undoTrail; q)
    alg2 Fail         = Op . Inr . Inl $ Fail
    fwd op            = Op . Inr . Inr . Inr $ op
    undoTrail = do  top <- pop;
                    case top of
                      Nothing -> return ()
                      Just (Right ()) -> return ()
                      Just (Left r) -> do s <- get; put (s `minus` r); undoTrail

    push :: (Functor f1, Functor f2, Functor g) => e -> Free (f1 :+: (f2 :+: (StackF e b :+: g))) ()
    push e = Op . Inr . Inr . Inl $ Push e (return ())
    pop :: (Functor f1, Functor f2, Functor g) => Free (f1 :+: (f2 :+: (StackF e b :+: g))) (Maybe e)
    pop = Op . Inr . Inr . Inl $ Pop return
\end{code}

Simulation: |hLocalM = tM|.
\begin{code}
hLocalM :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
hLocalM = fmap (fmap (fmap fst) . hNDf) . hModify

hGlobalM :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
hGlobalM = fmap (fmap fst) . hModify . hNDf . comm2

tM :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
tM = fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . local2trailM
\end{code}

The n-queens example using the trail stack:
% instance Undo (Int, [Int]) Int where
%   plus (c, sol) r   = (c+1, r:sol)
%   minus (c, sol) r  = (c-1, tail sol)

\begin{code}
--queensR :: (MState (Int, [Int]) m, MNondet m) => Int -> m [Int]
queensM :: Functor f => Int -> Free (ModifyF (Int, [Int]) Int :+: NondetF :+: f) [Int]
queensM n = loop
  where
    loop = do  s@(c, sol) <- getM
               if c >= n then return sol
               else do  r <- choose [1..n]
                        filtr valid (r:sol)
                        plusM r
                        --modifyR (`plus` r) (`minus` r)
                        loop

queensLocalM :: Int -> [[Int]]
queensLocalM = hNil . flip hLocalM (0, []) . queensM

queensTrailM :: Int -> [[Int]]
queensTrailM = hNil . flip tM (0, []) . queensM

\end{code}
