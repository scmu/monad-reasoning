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
import NondetState hiding (results, Comp)
import Combination hiding (results, Comp)

\end{code}
%endif

\section{Modelling Local State with Trail Stack}
\label{sec:trail-stack}

In order
to trigger the restoration of the previous state, the simulations |local2global| in \Cref{sec:local2global} and |local2globalM|
in \Cref{sec:undo} introduce a call to |or| and to |fail|
at every modification of the state.
%
The Warren Abstract Machine (WAM)~\citep{AitKaci91} does this in a more efficient and
lower-level way: it uses a \emph{trail stack} to batch consecutive restorative steps.
%
In this section, we first make use of the idea of trail stacks to
implement a lower-level translation from local-state semantics to
global-state semantics for the modifcation-based version of state
effects in \Cref{sec:undo} which does not require extra calls to
nondeterminism operations.
%
Then, we combine this simulation with other simulations
% the simulation of nondeterminism
% in \Cref{sec:nondeterminism-state} and the simulation of multiple
% states in \Cref{sec:multiple-states}
to obtain another ultimate simulation function which uses two stacks,
a choicepoint stack and a trail stack, simultaneously.


\subsection{Simulating Local State with Global State and Trail Stack}
\label{sec:local2trail}

%
For example, for the modification-based version |local2globalM|,
%
we can model this idea with a trail stack to contain elements of type |Either r
()|, where |r| is the type of deltas to the states. Each |Left x| entry represents
an update to the state with the delta |x|, and each |Right ()| is a
marker.
%
When we enter a left branch, we push a marker on the trail stack.
%
For every update we perform in that branch, we push the corresponding
delta on the trail stack, on top of the marker.
%
When we backtrack to the right branch, we unwind the trail stack down to the
marker and restore all deltas along the way. This process is known as ``untrailing''.

We can easily model the |Stack| data type with Haskell lists.
\begin{code}
newtype Stack s = Stack [s]
\end{code}

We thread the stack through the computation using the state effect and define primitive pop and push operations  
as follows.
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
\end{code}

We also need to define a new instance of |MState| in order to
correctly use state operations for the trail stack.
\begin{code}
instance (Functor f, Functor g, Functor h)
  => MState s (Free (f :+: g :+: StateF s :+: h)) where
    get      = Op . Inr . Inr . Inl $ Get return
    put x    = Op . Inr . Inr . Inl $ Put x (return ())
\end{code}


With these in place, the following translation function |local2trail| simulates the
local-state semantics with global-state semantics by means of the trail stack.

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
                      Nothing          -> return ()
                      Just (Right ())  -> return ()
                      Just (Left r)    -> restore r >> undoTrail
\end{code}
As already informally explained above, this translation function
introduces code to push a marker in the left branch of a choice, and 
untrail in the right branch. Whenever an update happens, it is also
recorded on the trail stack. All other operations remain as is.

Now, we can combine the simulation |local2trail| with the global-state
semantics provided by |hGlobalM|, and handle the trail stack at the
end.
\begin{code}
hGlobalT  :: (Functor f, Undo s r)
          => Free (ModifyF s r :+: NondetF :+: f) a -> s -> Free f [a]
hGlobalT  = fmap (fmap fst . flip runStateT (Stack []) . hState) . hGlobalM . local2trail
\end{code}

The following theorem establishes the correctness of |hGlobalT| with respect to
the local-state semantics given by |hLocal| defined in \Cref{sec:local-state}.
\begin{restatable}[]{theorem}{localTrail}
\label{thm:trail-local-global}
Given |Functor f| and |Undo s r|, the equation
< hGlobalT = hLocalM
holds for all programs |p :: Free (ModifyF s r :+: NondetF :+: f) a|
that do not use the operation |Op (Inl MRestore _ _)|.
\end{restatable}
The proof can be found in Appendix~\ref{app:immutable-trail-stack};
it uses the same fold fusion strategy as in the proofs of other theorems.

%if False
%
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
%endif

\subsection{Putting Everything Together, Again}

We can further combine the simulation |local2trail| with the
simulation |nondet2state| of nondeterminism in
\Cref{sec:nondeterminism-state} and the simulation |state2state| of
multiple states in \Cref{sec:multiple-states}.
% \begin{itemize} \item The function |nondet2state| simulates the
% high-level nondeterminism effect with the state effect
% (\Cref{sec:nondeterminism-state}).  \item The function
% |states2state| simulates multiple state effects with a single state
% effect (\Cref{sec:multiple-states}).  \end{itemize}
%
The result simulation encodes the local-state semantics with one
modification-based state and two stacks, a choicepoint stack generated
by |nondet2state| and a trail stack generated by |local2trail|.
%
This has a close relationship to the WAM of Prolog.
%
The modifcation-based state models the state of the program.
%
The choicepoint stack stores the remaining branches to implement the
nondeterministic searching.
%
The trail stack stores the privous state updates to implement the
backtracking.

The combined simulation function |simulateT| is defined
as follows:
% old definition:
% simulateT x s  = extract . hState . states2state
%                . fmap fst . flip runStateT s . hModify
%                . comm2 . nondet2state . comm2
%                . local2trail $ x
% type of extractT:
% extractT :: Functor f => StateT (SS g a, Stack b) (Free f) () -> (Free f) [a]
\begin{code}
simulateT      :: (Functor f, Undo s r)
               => Free (ModifyF s r :+: NondetF :+: f) a
               -> s -> Free f [a]
simulateT x s  = extractT . hState
               . fmap fst . flip runStateT s . hModify
               . comm2 . states2state . rotate3
               . comm2 . nondet2state . comm2
               . local2trail $ x
\end{code}

It uses the auxiliary function |extractT| to get the final results,
and |rotate3| to reorder the signatures.
%
Note that the initial state used by |extractT| is |(SS [] [], Stack
[])|, which essentially contains an empty results list, an empty
choicepoint stack, and an empty trail stack.
\begin{code}
extractT x = resultsSS . fst . snd <$> runStateT x (SS [] [], Stack [])

rotate3  :: (Functor f1, Functor f2, Functor f3, Functor f4)
         => Free (f1 :+: f2 :+: f3 :+: f4) a -> Free (f2 :+: f3 :+: f1 :+: f4) a
rotate3 (Var x)                   = Var x
rotate3 (Op (Inl k))              = (Op . Inr . Inr . Inl)  (fmap rotate3 k)
rotate3 (Op (Inr (Inl k)))        = (Op . Inl)              (fmap rotate3 k)
rotate3 (Op (Inr (Inr (Inl k))))  = (Op . Inr . Inl)        (fmap rotate3 k)
rotate3 (Op (Inr (Inr (Inr k))))  = (Op . Inr . Inr . Inr)  (fmap rotate3 k)
\end{code}

\Cref{fig:simulation-trail} illustrates each step of this simulation.
The state type |St s r f a| is defined as |SS (ModifyF s r :+: StateF (Stack
(Either r ())) :+: f) a|.
%
\begin{figure}[h]
% https://q.uiver.app/#q=WzAsNixbMCwwLCJ8RnJlZSAoTW9kaWZ5RiBzIHIgOis6IE5vbmRldEYgOis6IGYpIGF8Il0sWzAsMSwifEZyZWUgKE1vZGlmeUYgcyByIDorOiBOb25kZXRGIDorOiBTdGF0ZUYgKFN0YWNrIChFaXRoZXIgciAoKSkpIDorOiBmKSBhfCJdLFswLDIsInxGcmVlIChNb2RpZnlGIHMgciA6KzogU3RhdGVGIChTdCBzIHIgZiBhKSA6KzogU3RhdGVGIChTdGFjayAoRWl0aGVyIHIgKCkpKSA6KzogZikgKCl8Il0sWzAsMywifEZyZWUgKE1vZGlmeUYgcyByIDorOiBTdGF0ZUYgKFN0IHMgciBmIGEsIFN0YWNrIChFaXRoZXIgciAoKSkpIDorOiBmKSAoKXwiXSxbMCw0LCJ8RnJlZSAoU3RhdGVGIChTdCBzIHIgZiBhLCBTdGFjayAoRWl0aGVyIHIgKCkpKSA6KzogZikgKCl8Il0sWzAsNSwifEZyZWUgZiBbYV18Il0sWzAsMSwifGxvY2FsMnRyYWlsfCJdLFsxLDIsInxjb21tMiAuIG5vbmRldDJzdGF0ZSAuIGNvbW0yfCJdLFszLDQsInxmbWFwIGZzdCAuIGZsaXAgcnVuU3RhdGVUIHMgLiBoTW9kaWZ5fCJdLFsyLDMsInxjb21tMiAuIHN0YXRlczJzdGF0ZSAuIHJvdGF0ZTN8Il0sWzQsNSwifGV4dHJhY3RUIC4gaFN0YXRlfCJdXQ==
\[\begin{tikzcd}
	{|Free (ModifyF s r :+: NondetF :+: f) a|} \\
	{|Free (ModifyF s r :+: NondetF :+: StateF (Stack (Either r ())) :+: f) a|} \\
	{|Free (ModifyF s r :+: StateF (St s r f a) :+: StateF (Stack (Either r ())) :+: f) ()|} \\
	{|Free (ModifyF s r :+: StateF (St s r f a, Stack (Either r ())) :+: f) ()|} \\
	{|Free (StateF (St s r f a, Stack (Either r ())) :+: f) ()|} \\
	{|Free f [a]|}
	\arrow["{|local2trail|}", from=1-1, to=2-1]
	\arrow["{|comm2 . nondet2state . comm2|}", from=2-1, to=3-1]
	\arrow["{|fmap fst . flip runStateT s . hModify|}", from=4-1, to=5-1]
	\arrow["{|comm2 . states2state . rotate3|}", from=3-1, to=4-1]
	\arrow["{|extractT . hState|}", from=5-1, to=6-1]
\end{tikzcd}\]
\caption{An overview of the |simulateT| function.}
\label{fig:simulation-trail}
\end{figure}

In the |simulateT| function, we first use our three simulations
|local2trail|, |nondet2state| and |states2state| (together with some
reordering of signatures) to interpret the local-state semantics for
state and nondeterminism in terms of a modification-based state and a
general state containing two stacks. Then, we use the handler
|hModify| to interpret the modification-based state effect, and use
the handler |hState| to interpret the two stacks. Finally, we use the
function |extractT| to get the final results.

Finally, we can also fuse |simulateT| into a single
handler.
\begin{code}
type Comp f a s r = (WAM f a s r, s) -> Free f [a]
data WAM f a s r = WAM  { results  :: [a]
                        , cpStack  :: [Comp f a s r] 
                        , trStack  :: [Either r ()]}

simulateTF  :: (Functor f, Undo s r)
            => Free (ModifyF s r :+: NondetF :+: f) a
            -> s
            -> Free f [a]
simulateTF  x s =  fold gen (alg1 # alg2 # fwd) x (WAM [] [] [], s)
  where
    gen x                (WAM xs cp tr, s) =  continue (xs++[x]) cp tr s
    alg1 (MGet k)        (WAM xs cp tr, s) =  k s (WAM xs cp tr, s)
    alg1 (MUpdate r k)   (WAM xs cp tr, s) =  k (WAM xs cp (Left r:tr), s `plus` r)
    alg1 (MRestore r k)  (WAM xs cp tr, s) =  k (WAM xs cp tr, s `minus` r)
    alg2 Fail            (WAM xs cp tr, s) =  continue xs cp tr s
    alg2 (Or p q)        (WAM xs cp tr, s) =  p (WAM xs (undoTrail q : cp) (Right () : tr), s)
    fwd op               (WAM xs cp tr, s) =  Op (fmap ($(WAM xs cp tr, s)) op)
    undoTrail q          (WAM xs cp tr, s) =  case tr of
                                                [] -> q (WAM xs cp tr, s)
                                                Right () : tr'  -> q (WAM xs cp tr', s)
                                                Left r : tr'    -> undoTrail q (WAM xs cp tr', s `minus` r)
    continue xs cp tr s                    =  case cp of 
                                                []     -> return xs
                                                p:cp'  -> p (WAM xs cp' tr, s)
           
\end{code}
Here, the carrier type of the algebras is |Comp f a s r|. It differs from that of |simulateF|
in that it also takes a trail stack as an input.

\paragraph*{N-queens with Two Stacks}\
%
With |simulateT|, we can implement the backtracking algorithm of the
n-queens problem with one modification-based state and two stacks.

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

--  Stack xs <- get
--  case xs of
--    []       -> return Nothing
--    (x:xs')  -> do put (Stack xs'); return (Just x)


test3 :: (Functor f, Undo s r) => s -> Stack (Either r ()) -> Free f (([()], s), Stack (Either r ()))
test3 s t =
   hState1 ((hModify1 . hNDf . comm2) (do
     top <- popStack
     case top of
       Nothing -> return ()
       Just (Right ()) -> return ()
       Just (Left r) -> do restore r; undoTrail
   ) s) t

test4 s t =
   hState1 ((hModify1 . hNDf . comm2) (do
     Stack xs <- get
     case xs of
       []       -> return ()
       (Right () : xs')  -> do put (Stack xs'); return ()
       (Left r   : xs')  -> do put (Stack xs'); restore r; undoTrail
   ) s) t

test4' s t =
   hState1 (hModify1 (Op . Inr . Inl . Get $ \ (Stack xs) ->
     case xs of
       []                -> return [()]
       (Right () : xs')  -> hNDf . comm2 $ do put (Stack xs'); return ()
       (Left r   : xs')  -> hNDf . comm2 $ do put (Stack xs'); restore r; undoTrail
   ) s) t

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
