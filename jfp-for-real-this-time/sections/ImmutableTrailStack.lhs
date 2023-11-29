%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module ImmutableTrailStack where

import Background
import Overview
import Control.Monad (ap, liftM, liftM2)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import LocalGlobal hiding (ModifyF)
import Undo
import Debug.Trace
import NondetState
import Combination

\end{code}
%endif

\section{Trail Stack}
\label{sec:trail-stack}

The trail stack contains elements of type |Either r ()|.  The |Left r|
means a delta of type |r|; the |Right ()| means a time stamp.

We can easily implement the |Stack| data type with lists.
\begin{code}
newtype Stack s = Stack [s]
\end{code}

We define the pop and push operations for stacks using the state
operations.
% -- popStack :: Functor f => Free (StateF (Stack s) :+: f) (Maybe s)
% -- pushStack :: Functor f => s -> Free (StateF (Stack s) :+: f) ()
\begin{code}
popStack :: MState (Stack s) m => m (Maybe s)
popStack = do
  Stack xs <- get
  case xs of
    []       -> return Nothing
    (x:xs')  -> do put (Stack xs'); return (Just x)

pushStack :: MState (Stack s) m => s -> m ()
pushStack x = do
  Stack xs <- get
  put (Stack (x:xs))

instance (Functor f, Functor g, Functor h)
  => MState s (Free (f :+: g :+: StateF s :+: h)) where
    get      = Op . Inr . Inr . Inl $ Get return
    put x    = Op . Inr . Inr . Inl $ Put x (return ())

\end{code}
% instance (Functor f, Functor h)
%   => MState s (Free (f :+: StateF s :+: h)) where
%     get      = Op . Inr . Inl $ Get return
%     put x    = Op . Inr . Inl $ Put x (return ())


The following translation |local2trail| simulates the local-state
semantics with global-state semantics using a trail stack.

\begin{code}
local2trail :: (Functor f, Undo s r)
            => Free (ModifyF s r :+: NondetF :+: f) a
            -> Free (ModifyF s r :+: NondetF :+: StateF (Stack (Either r ())) :+: f) a
local2trail = fold Var (alg1 # alg2 # fwd)
  where
    alg1 (MUpdate r k)  = pushStack (Left r) >> update r >> k
    alg1 p              = Op . Inl $ p
    alg2 (Or p q)       = (pushStack (Right ()) >> p) `mplus` (undoTrail >> q)
    alg2 p              = Op . Inr . Inl $ p
    fwd p               = Op . Inr . Inr . Inr $ p
    undoTrail = do  top <- popStack;
                    case top of
                      Nothing -> return ()
                      Just (Right ()) -> return ()
                      Just (Left r) -> do restore r; undoTrail
\end{code}

Now, we can combine the simulation |local2trail| with the global
semantics provided by |hGlobalM|, and handle the trail stack at the
end.
\begin{code}
hGlobalT :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
hGlobalT = fmap (fmap fst . flip runStateT (Stack []) . hState) . hGlobalM . local2trail
\end{code}

We have the following theorem showing its correctness by the
equivalence between |hGlobalT| and the local-state semantics given by
|hLocal|.
\begin{restatable}[]{theorem}{localTrail}
\label{thm:local2trail}
Given |Functor f| and |Undo s r|, the equation
< hGlobalT = hLocalM
holds for all programs |p :: Free (ModifyF s r :+: NondetF :+: f) a|
that do not use the operation |Op (Inl MRestore _ _)|.
\end{restatable}

The n-queens example using the trail stack:
\begin{code}
queensGlobalT :: Int -> [[Int]]
queensGlobalT = hNil . flip hGlobalT (0, []) . queensM
\end{code}

We can further combine it with |nondet2state| (hidden in |runNDf|).
\begin{code}
queensStateT  :: Int -> [[Int]]
queensStateT  = hNil
              . fmap fst . flip runStateT (Stack []) . hState
              . fmap fst . flip runStateT (0, []) . hModify
              . runNDf . comm2
              . local2trail . queensM
\end{code}

Then even further combined with |states2state|, we get the |simulateT|.
\begin{code}
simulateT      :: (Functor f, Undo s r)
               => Free (ModifyF s r :+: NondetF :+: f) a
               -> s -> Free f [a]
simulateT x s  = extract . hState . states2state
               . fmap fst . flip runStateT s . hModify
               . comm2 . nondet2state . comm2
               . local2trail $ x
    where
      extract x = resultsSS . fst . snd <$> runStateT x (SS [] [], Stack [])
\end{code}
%
Note that our initial state is |(SS [], [], Stack [])|, which
essentially contains an empty results list, an empty stack of
branches (which Prolog calls the choicepoint stack), and an empty
trail stack.

Use |simulateT| to solve n-queens:
\begin{code}
queensSimT :: Int -> [[Int]]
queensSimT = hNil . flip simulateT (0, []) . queensM
\end{code}

%if False
% some testing code for proofs
\begin{code}
undoTrail :: (Functor f, Functor g, Undo s r)
  => Free (ModifyF s r :+: (g :+: (StateF (Stack (Either r ())) :+: f))) ()
undoTrail = do  top <- popStack;
                case top of
                  Nothing -> return ()
                  Just (Right ()) -> return ()
                  Just (Left r) -> do restore r; undoTrail

hState1 :: Functor f => Free (StateF s :+: f) a -> (s -> Free f (a, s))
hState1  =  fold genS (algS # fwdS)
  where
    genS x          s  = Var (x, s)
    algS (Get k)    s  = k s s
    algS (Put s k)  _  = k s
    fwdS y          s  = Op (fmap ($s) y)

hModify1  :: (Functor f, Undo s r) => Free (ModifyF s r :+: f) a -> (s -> Free f (a, s))
hModify1  =  fold genS (algS # fwdS)
  where
    genS x               s = Var (x, s)
    algS :: (Undo s r) => ModifyF s r (s -> p) -> s -> p
    algS (MGet k)        s = k s s
    algS (MUpdate r k)   s = k (s `plus` r)
    algS (MRestore r k)  s = k (s `minus` r)
    fwdS y               s = Op (fmap ($s) y)

_hGlobalM  :: (Functor f, Undo s r)
           => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
_hGlobalM  = fmap (fmap fst) . hModify1 . hNDf . comm2

_hGlobalT :: (Functor f, Undo s r) => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
_hGlobalT = fmap (fmap fst . flip runStateT (Stack []) . hState) . hGlobalM . local2trail

_fusedhLocalM  :: (Functor f, Undo s r)
               => Free (ModifyF s r :+: NondetF :+: f) a -> (s -> Free f [a])
_fusedhLocalM = fold genRHS (algSRHS # algNDRHS # fwdRHS)
  where
    genRHS :: Functor f => a -> (s -> Free f [a])
    genRHS x = \s -> Var [x]
    algSRHS :: Undo s r => ModifyF s r (s -> p) -> (s -> p)
    algSRHS (MGet k)        = \ s -> k s s
    algSRHS (MUpdate r k)   = \ s -> k (s `plus` r)
    algSRHS (MRestore r k)  = \ s -> k (s `plus` r)
    algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
    algNDRHS Fail      = \ s -> Var []
    algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)
    fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
    fwdRHS op = \s -> Op (fmap ($s) op)

runStack :: Functor f => Free (StateF (Stack s) :+: f) b -> Free f b
runStack = fmap fst . flip hState1 (Stack [])
-- runStack :: Functor f => (a -> Free (StateF (Stack s) :+: f) b) -> a -> Free f b
-- runStack = fmap (fmap fst . flip runStateT (Stack []) . hState)

test1 p q = do
  -- x <- pushStack (Right ()) >> hNDf (comm2 p)
  -- y <- undoTrail >> hNDf (comm2 q)
  hNDf (comm2 (pushStack (Right ())))
  x <- hNDf (comm2 p)
  hNDf (comm2 undoTrail)
  y <- hNDf (comm2 q)
  return (x ++ y)

test2 p q s = do
    pushStack (Right ())
    (x, s1) <- hModify1 (hNDf (comm2 p)) s
    (_, s2) <- hModify1 undoTrail s1
    (y, s3) <- hModify1 (hNDf (comm2 q)) s2
    return (x ++ y, s3)

test3 p s t =
 hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t

test3' p s t ys =
  do ((x, s), Stack xs) <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) (Stack []); return ((x, s), Stack (xs ++ ys))

extend :: Stack s -> [s] -> Stack s
extend (Stack xs) ys = Stack (ys ++ xs)
fplus :: Undo s r => s -> [Either r b] -> s
fplus s ys = foldr (\ (Left r) s -> s `plus` r) s ys

test4 p s t ys =
  do  ((x, s'), t') <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t
      return (x, t' == extend t ys, s' == fplus s ys)

test5 s t r k =
   do  ((_, s1), t1) <- hState1 ((hModify1 . hNDf . comm2 $ do
         Stack xs <- get
         put (Stack (Left r : xs))) s) t
       hState1 ((hModify1 . hNDf . comm2 . local2trail $ k) (s1 `plus` r)) t1
\end{code}
%endif



% -------------------------------------------------------------
% Some deprecated code but might be useful in the future
% -------------------------------------------------------------

% \begin{code}
% data StackF s a = Push s a | Pop (Maybe s -> a)
% \end{code}
% %if False
% \begin{code}
% instance Functor (StackF s) where
%     fmap f (Push x k)  = Push x (f k)
%     fmap f (Pop k)     = Pop (f . k)
% \end{code}
% %endif


% \begin{code}
% emptyStack :: Stack s
% emptyStack = Stack []

% pushStack :: s -> Stack s -> Stack s
% pushStack x (Stack y) = Stack (x : y)

% popStack :: Stack s -> (Maybe s, Stack s)
% popStack (Stack y) = case y of
%   []      -> (Nothing, Stack y)
%   (y:ys)  -> (Just y, Stack ys)
% \end{code}


% \begin{code}
% hStack  :: Functor f
%         => Stack s -> Free (StackF s :+: f) a -> StateT (Stack s) (Free f) a
% hStack stack = fold gen (alg # fwd)
%   where
%     gen x            = StateT $ \s -> return (x, s)
%     alg (Pop k)      = StateT $ \s -> let (x, s') = popStack s in runStateT (k x) s'
%     alg (Push x k)   = StateT $ \s -> let s' = pushStack x s in runStateT k s'
%     fwd op           = StateT $ \s -> Op $ fmap (\k -> runStateT k s) op
% \end{code}


% The following naive implementation uses |StateF| and stores the whole
% state in the trail stack.

% \begin{code}
% local2trail :: (Functor f)
%             => Free (StateF s :+: NondetF :+: f) a
%             -> Free (StateF s :+: NondetF :+: StateF (Stack (Either s ())) :+: f) a
% local2trail = fold Var (alg1 # alg2 # fwd)
%   where
%     alg1 (Put s k)  = do t <- get; pushStack (Left t); put s; k
%     alg1 oth        = Op . Inl $ oth
%     alg2 (Or p q)   = Op . Inr . Inl $ Or (do pushStack (Right ()); p) (do undoTrail; q)
%     alg2 oth        = Op . Inr . Inl $ oth
%     fwd op          = Op . Inr . Inr . Inr $ op
%     undoTrail = do  top <- popStack;
%                     case top of
%                       Nothing -> return ()
%                       Just (Right ()) -> return ()
%                       Just (Left s) -> do put s; undoTrail

%     getStack :: (Functor f, Functor g, Functor h)
%       => Free (f :+: g :+: StateF s :+: h) s
%     getStack = Op . Inr . Inr . Inl $ Get return
%     putStack :: (Functor f, Functor g, Functor h)
%       => s -> Free (f :+: g :+: StateF s :+: h) ()
%     putStack x = Op . Inr . Inr . Inl $ Put x (return ())
%     pushStack :: (Functor f, Functor g, Functor h)
%       => s -> Free (f :+: g :+: StateF (Stack s) :+: h) ()
%     pushStack x = do
%       Stack xs <- getStack
%       putStack (Stack (x:xs))
%     popStack :: (Functor f, Functor g, Functor h)
%       => Free (f :+: g :+: StateF (Stack s) :+: h) (Maybe s)
%     popStack = do
%       Stack xs <- getStack
%       case xs of
%         []       -> return Nothing
%         (x:xs')  -> do putStack (Stack xs'); return (Just x)
% \end{code}

% We have the following theorem.
% < hLocal = fmap (fmap fst . runhStack ()) . hGlobal . local2trail

% %if False
% \begin{code}
% t1 :: Functor f => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
% t1 = hLocal

% t2 :: (Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> Free f [a]
% t2 x s = fmap fst . flip runStateT (Stack []) . hState $ (hGlobal . local2trail) x s
% \end{code}
% %endif

% The n-queens example using the trail stack:
% \begin{code}
% queensTrail :: Int -> [[Int]]
% queensTrail = hNil . flip t2 (0, []) . queens
% \end{code}