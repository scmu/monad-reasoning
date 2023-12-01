%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Combination where

import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef

import Background
import Overview
import LocalGlobal (local2global, hLocal, comm2, side)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState,
  popSS, appendSS, pushSS)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero, get, put)

\end{code}
%endif
\section{All in One}
\label{sec:combination}

% Throughout the paper, we have shown several cases in which a high-level effect
% can be simulated by means of a lower-level effect.
This section combines the results of the previous two sections to ultimately simulate the combination of
nondeterminism and state with a single state effect.

%-------------------------------------------------------------------------------
\subsection{Modeling Two States with One State}
\label{sec:multiple-states}

When we combine the two simulation steps from the two previous sections, we end
up with a computation that features two state effects. The first state effect
is the one present originally, and the second state effect keeps track of the
results and the stack of remaining branches to simulate the nondeterminism.

For a computation of type |Free (StateF s1 :+: StateF s2 :+: f) a|
that features two state effects,
% \begin{enumerate}
%   \item A representation using and effect functor with two state functors |StateF s1 :+: StateF s2|,
%         and a corresponding handler |hStates|, which interprets the two state functors as two nested
%         |StateT| monads. In essence, this handler applies two |hState| handlers in sequence.
% \begin{code}
% hStates :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT s1 (StateT s2 (Free f)) a
% hStates t = StateT $ \s1 -> hState $ runStateT (hState t) s1
% \end{code}
%   \item A representation using a single state effect functor that contains a tuple of two states
%         |StateF (s1, s2)|. The corresponding handler, |hStateTuple|,
%         interprets the state functor as a |StateT| monad. This implementation is exactly the definition
%         of the |hState| handler, in which state |s| is defined as a tuple of two states.
% \begin{code}
% hStateTuple :: Functor f => Free (StateF (s1, s2) :+: f) a -> StateT (s1, s2) (Free f) a
% hStateTuple = hState
% \end{code}
% \end{enumerate}
%
we can go to a slightly more primitive representation
|Free (StateF (s1, s2) :+: f) a| featuring only a single state
effect that is a pair of the previous two states.

The handler |states2state| implements the simulation by projecting
different |get| and |put| operations to different components of the
pair of states.

\begin{code}
states2state  :: Functor f
              => Free (StateF s1 :+: StateF s2 :+: f) a
              -> Free (StateF (s1, s2) :+: f) a
states2state  = fold Var (alg1 # alg2 # fwd)
  where
    alg1 (Get k)      = get >>= \(s1,  _)   -> k s1
    alg1 (Put s1' k)  = get >>= \(_,   s2)  -> put (s1', s2) >> k
    alg2 (Get k)      = get >>= \(_,   s2)  -> k s2
    alg2 (Put s2' k)  = get >>= \(s1,  _)   -> put (s1, s2') >> k
    fwd op            = Op (Inr op)
\end{code}
% Here, |get'| and |put'| are smart constructors for getting the state and putting a new state.
% \begin{code}
% get'        :: Functor f => Free (StateF s :+: f) s
% get'        = Op (Inl (Get return))

% put'        :: s -> Free (StateF s :+: f) a -> Free (StateF s :+: f) a
% put' sts k  = Op (Inl (Put sts k))
% \end{code}

% \paragraph*{Correctness}\
We have the following theorem showing the correctness of |states2state|:
\begin{restatable}[]{theorem}{statesState}
\label{thm:states-state}
< hStates = nest . hState . states2state
\end{restatable}
\noindent
On the left-hand side, we write |hStates| for the composition of two
consecutive state handlers:
\begin{code}
hStates :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT s1 (StateT s2 (Free f)) a
hStates x = StateT (hState . runStateT (hState x))
hStates' :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT (s1, s2) (Free f) a
hStates' t = StateT $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2
\end{code}
On the right-hand side, we use the isomorphism |nest| to mediate
between the two different carrier types. The definition of |nest| and
its inverse |flatten| are defined as follows:
\begin{code}
nest        :: Functor f =>  StateT (s1, s2) (Free f) a -> StateT s1 (StateT s2 (Free f)) a
nest t      = StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)
flatten     :: Functor f =>  StateT s1 (StateT s2 (Free f)) a -> StateT (s1, s2) (Free f) a
flatten t   = StateT $ \ (s1, s2) -> alpha <$> runStateT (runStateT t s1) s2
\end{code}
where the isomorphism |alpha1| and its inverse |alpha| rearrange a
nested tuple
\begin{code}
alpha   :: ((a, x), y) -> (a, (x, y))
alpha ((a, x), y)   = (a, (x, y))
alpha1  :: (a, (x, y)) -> ((a, x), y)
alpha1 (a, (x, y))  = ((a, x), y)
\end{code}
The proof of \Cref{thm:states-state} can be found in
\Cref{app:states-state}. Instead of proving it directly, we show the
correctness of the isomorphism of |nest| and |flatten|, and prove the
following equation:
< flatten . hStates = hState . states2state
% The proof of the |nest| / |flatten| isomorphism can be found in
% \Cref{app:flatten-nest} and the proof of the theorem is written out in
% \Cref{app:states-state-sim}.  The theorem is a trivial
% corollary of the lemma.

% The function |alpha| is .
% https://q.uiver.app/?q=WzAsMixbMCwwLCJ8KChhLHgpLHkpfCJdLFsyLDAsInwoYSwgKHgseSkpfCJdLFswLDEsInxhbHBoYXwiLDAseyJvZmZzZXQiOi0zfV0sWzEsMCwifGFscGhhMXwiLDAseyJvZmZzZXQiOi0zfV1d
% \[\begin{tikzcd}
%   {|((x,y),z)|} && {|(x,(y,z))|}
%   \arrow["{|alpha|}", shift left=3, from=1-1, to=1-3]
%   \arrow["{|alpha1|}", shift left=3, from=1-3, to=1-1]
% \end{tikzcd}\]
% the nested state transformer and the state transformer with a tuple of states.
% This transformation can be defined in terms of two isomorphic functions
% |flatten| and |nested|.

% As |flatten| has an inverse, which we call |nested|, the following corollary holds
% as well:
% < hStates = nested . hStateTuple . states2state
% Here, |nested| is defined as follows:
% \begin{code}
% nested     :: Functor f =>  StateT (s1, s2) (Free f) a -> StateT s1 (StateT s2 (Free f)) a
% nested t   = StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)
% \end{code}

The following commuting diagram simmuarises the simulation.

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ8RnJlZSAoU3RhdGVGIHMxIDorOiBTdGF0ZUYgczIgOis6IGYpIGF8Il0sWzAsMiwifEZyZWUgKFN0YXRlRiAoczEsIHMyKSA6KzpmKSBhfCJdLFsyLDAsInxTdGF0ZVQgczEgKFN0YXRlVCBzMiAoRnJlZSBmKSkgYXwiXSxbMiwyLCJ8U3RhdGVUIChzMSwgczIpIChGcmVlIGYpIGF8Il0sWzIsMywifGZsYXR0ZW58IiwyLHsib2Zmc2V0Ijo1fV0sWzMsMiwifG5lc3RlZHwiLDIseyJvZmZzZXQiOjV9XSxbMCwyLCJ8aFN0YXRlc3wiXSxbMSwzLCJ8aFN0YXRlVHVwbGV8IiwyXSxbMCwxLCJ8c3RhdGVzMnN0YXRlfCIsMl1d
\[\begin{tikzcd}
  {|Free (StateF s1 :+: StateF s2 :+: f) a|} && {|StateT s1 (StateT s2 (Free f)) a|} \\
  \\
  {|Free (StateF (s1, s2) :+:f) a|} && {|StateT (s1, s2) (Free f) a|}
  \arrow["{|flatten|}"', shift right=5, from=1-3, to=3-3]
  \arrow["{|nest|}"', shift right=5, from=3-3, to=1-3]
  \arrow["{|hStates|}", from=1-1, to=1-3]
  \arrow["{|hState|}"', from=3-1, to=3-3]
  \arrow["{|states2state|}"', from=1-1, to=3-1]
\end{tikzcd}\]

% TOM: What is the point of this?
% WT: just remove it
% We can easily fuse the composition |flatten . hStates| using equational reasoning techniques,
% as shown in \Cref{app:states-state-fusion}.

%if False
% NOTE: some test code to assit in writing proofs
\begin{code}
t :: Functor f => Free (StateF (SS (StateF s :+: f) a) :+: (StateF s :+: f)) () -> s -> Free f [a]
t = extract . hStates'

input :: Functor f => Free (StateF (SS (StateF s :+: f) a) :+: (StateF s :+: f)) ()
input = undefined

step1 :: Functor f => Free (StateF s :+: f) ((), SS (StateF s :+: f) a)
step1 = runStateT (hState input) (SS [] [])

_hStates :: Functor f => s -> Free (StateF s :+: f) a -> Free f (a, s)
_hStates = flip (runStateT . hState)

fhStates :: Functor f => s -> Free (StateF s :+: f) a -> Free f a
fhStates s = fmap fst . _hStates s

t1 s = fmap (resultsSS . snd . fst) step2
  where
    step2 = _hStates s step1


t2 :: Functor f => t -> Free f [a]
t2 s = fhStates s . fmap (resultsSS . snd) $ step1

t3 :: Functor f => t -> Free f [a]
t3 s = fmap (resultsSS . snd) . fhStates s $ step1
\end{code}
%endif

%-------------------------------------------------------------------------------
\subsection{Putting Everything Together}\
\label{sec:final-simulate}
%
We have defined three translations for encoding high-level effects as
low-level effects.
\begin{itemize}
  \item The function |local2global| simulates the high-level
  local-state semantics with global-state semantics for the
  nondeterminism and state effects  (\Cref{sec:local-global}).
  \item The function |nondet2state| simulates the high-level
  nondeterminism effect with the state effect
  (\Cref{sec:nondeterminism-state}).
  \item The function |states2state| simulates multiple state effects
  with a single state effect (\Cref{sec:multiple-states}).
\end{itemize}

Combining them, we can encode the local-state semantics
for nondeterminism and state with just one state effect. The ultimate
simulation function |simulate| is defined as follows:
\begin{code}
simulate  :: Functor f
          => Free (StateF s :+: NondetF :+: f) a
          -> s -> Free f [a]
simulate  = extract . hState . states2state . nondet2state . comm2 . local2global
\end{code}
Similar to the |extractSS| function in \Cref{sec:nondet2state}, we use
the |extract| function to get the final results from the final state.
\begin{code}
extract   :: Functor f
          => StateT (SS (StateF s :+: f) a, s) (Free f) ()
          -> s -> Free f [a]
extract x s = resultsSS . fst . snd <$> runStateT x (SS [] [], s)
\end{code}
% An overview of this simulation is given in Figure
% \ref{fig:simulation}.
\Cref{fig:simulation} illustrates each step of this simulation.
%
\begin{figure}[h]
% https://q.uiver.app/#q=WzAsNyxbMCwwLCJ8RnJlZSAoU3RhdGVGIHMgOis6IE5vbmRldEYgOis6IGYpIGF8Il0sWzAsMSwifEZyZWUgKFN0YXRlRiBzIDorOiBOb25kZXRGIDorOiBmKSBhfCJdLFswLDIsInxGcmVlIChOb25kZXRGIDorOiBTdGF0ZUYgcyA6KzogZikgYXwiXSxbMCwzLCJ8RnJlZSAoU3RhdGVGIChTUyAoU3RhdGVGIHMgOis6IGYpIGEpIDorOiBTdGF0ZUYgcyA6KzogZikgKCl8Il0sWzAsNCwifEZyZWUgKFN0YXRlRiAoU1MgKFN0YXRlRiBzIDorOiBmKSBhLCBzKSA6KzogZikgKCl8Il0sWzAsNSwifFN0YXRlVCAoU1MgKFN0YXRlRiBzIDorOiBmKSBhLCBzKSAoRnJlZSBmKSAoKXwiXSxbMCw2LCJ8cyAtPiBGcmVlIGYgW2FdfCJdLFswLDEsInxsb2NhbDJnbG9iYWx8Il0sWzEsMiwifGNvbW0yfCJdLFszLDQsInxzdGF0ZXMyc3RhdGV8Il0sWzQsNSwifGhTdGF0ZXwiXSxbNSw2LCJ8ZXh0cmFjdHwiXSxbMiwzLCJ8bm9uZGV0MnN0YXRlfCJdXQ==
\[\begin{tikzcd}
	{|Free (StateF s :+: NondetF :+: f) a|} \\
	{|Free (StateF s :+: NondetF :+: f) a|} \\
	{|Free (NondetF :+: StateF s :+: f) a|} \\
	{|Free (StateF (SS (StateF s :+: f) a) :+: StateF s :+: f) ()|} \\
	{|Free (StateF (SS (StateF s :+: f) a, s) :+: f) ()|} \\
	{|StateT (SS (StateF s :+: f) a, s) (Free f) ()|} \\
	{|s -> Free f [a]|}
	\arrow["{|local2global|}", from=1-1, to=2-1]
	\arrow["{|comm2|}", from=2-1, to=3-1]
	\arrow["{|states2state|}", from=4-1, to=5-1]
	\arrow["{|hState|}", from=5-1, to=6-1]
	\arrow["{|extract|}", from=6-1, to=7-1]
	\arrow["{|nondet2state|}", from=3-1, to=4-1]
\end{tikzcd}\]
\caption{An overview of the |simulate| function.}
\label{fig:simulation}
\end{figure}

In the |simulate| function, we first use our three simulations
|local2global|, |nondet2state| and |states2state| to interpret the
local-state semantics for state and nondeterminism in terms of only
one state effect. Then, we use the handler |hState| to interpret the
state effect into a state monad transformer. Finally, we use the
function |extract| to get the final results.

% First, |local2global| models the local-state semantics with a global
% state.  Second, we use commutativity and associativity of the
% coproduct operator to change the order of state and nondeterminism.

% Next, |nondet2state| transforms the nondeterminism effect into a
% simulation with state.  Then, we use the definition of |CompSS| to
% represent it as a free monad so that the |states2state| simulation can
% combine the two state effects into a single state.  Finally, |hState|
% handles this state effect and translates it to the state transformer
% |StateT|.

% Additionally, the |extract| function extracts the final result from
% the state monad transformer into a more readable form.

We have the following theorem showing that the |simulate| function exactly
behaves the same as the local-state semantics given by |hLocal|.
\begin{restatable}[]{theorem}{finalSimulate}
\label{thm:final-simulate}
< simulate = hLocal
\end{restatable}
%
The proof can be found in \Cref{app:final-simulate}.

To show the idea of |simulate| more clearly, we manually fuse it to
the function |simulateF| defined as follows. The state |CP| contains
the result list and a choicepoint stack.

\begin{code}

type Comp s f a = s -> Free f (a, s)
data CP f a s = CP { results :: [a], cpStack :: [Comp (CP f a s, s) f ()] }

simulateF  :: Functor f
           => Free (StateF s :+: NondetF :+: f) a
           -> s
           -> Free f [a]
simulateF  x s =  results . fst . snd <$>
                  fold gen (alg1 # alg2 # fwd) x (CP [] [], s)
  where
    gen x           (CP xs stack, s) =  case stack of
                                           [] -> return ((), (CP (xs++[x]) stack, s))
                                           p:ps -> p (CP (xs++[x]) ps, s)
    alg1 (Get k)    (CP xs stack, s) =  k s (CP xs stack, s)
    alg1 (Put t k)  (CP xs stack, s) =  k (CP xs (backtracking s : stack), t)
    alg2 Fail       (CP xs stack, s) =  case stack of
                                           [] -> return ((), (CP xs stack, s))
                                           p:ps -> p (CP xs ps, s)
    alg2 (Or p q)   (CP xs stack, s) =  p (CP xs (q:stack), s)
    fwd op          (CP xs stack, s) =  Op (fmap ($(CP xs stack, s)) op)
    backtracking s  (CP xs stack, _) =  case stack of
                                          [] -> return ((), (CP xs stack, s))
                                          p:ps -> p (CP xs ps, s)
\end{code}

%if False
Manual fusion of |simulate|:
\begin{code}
hLocalFused :: Functor f
            => Free (StateF s :+: NondetF :+: f) a
            -> s -> Free f [a]
hLocalFused = fold gen (alg1 # alg2 # fwd)
  where
    gen x s          = return [x]
    alg1 (Get k) s   = k s s
    alg1 (Put t k) _ = k t
    alg2 Fail s      = return []
    alg2 (Or p q) s  = liftM2 (++) (p s) (q s)
    fwd op s         = Op (fmap ($s) op)

hGlobalFused :: Functor f
            => Free (StateF s :+: NondetF :+: f) a
            -> s -> Free f [a]
hGlobalFused = fmap (fmap fst) . fold gen (alg1 # alg2 # fwd)
  where
    gen x            s = return ([x], s)
    alg1 (Get k)     s = k s s
    alg1 (Put t k)   _ = k t
    alg2 Fail        s = return ([], s)
    alg2 (Or p q)    s = do (x, s1) <- p s; do (y, s2) <- q s1; return (x++y, s2)
    fwd op           s = Op (fmap ($s) op)

hGlobalL2GFused :: Functor f
                => Free (StateF s :+: NondetF :+: f) a
                -> s -> Free f [a]
hGlobalL2GFused = fmap (fmap fst) . fold gen (alg1 # alg2 # fwd)
  where
    gen x            s = return ([x], s)
    alg1 :: Functor f => StateF s (s -> Free f ([a], s)) -> s -> Free f ([a], s)
    alg1 (Get k)     s = k s s
    alg1 (Put t k)   s = do (x, _) <- k t; return (x, s)
    alg2 Fail        s = return ([], s)
    alg2 (Or p q)    s = do (x, s1) <- p s; do (y, s2) <- q s1; return (x++y, s2)
    fwd op           s = Op (fmap ($s) op)

-- popF = do
--   SS xs stack <- get
--   case stack of
--     []       -> return ()
--     p : ps   -> do
--       put (SS xs ps); p

\end{code}
%endif

%if False
\begin{code}
or1 :: Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a -> Free (f :+: (NondetF :+: g)) a
or1 x y = Op (Inr $ Inl $ Or x y)

fail1 :: Free (f :+: (NondetF :+: g)) a
fail1 = Op (Inr $ Inl Fail)

get1 :: Functor f => Free (StateF s :+: f) s
get1 = Op (Inl $ Get return)

put1 :: Functor f => s -> Free (StateF s :+: f) ()
put1 s = Op (Inl $ Put s (return ()))

prog :: Free (StateF Int :+: NondetF :+: NilF) Int
prog =
  or1 (do put1 10; return 5)
      (do x <- get1; return x)

tt :: [Int]
tt = hNil $ (simulate) prog 0
-- [5, 0]
tt' :: [Int]
tt' = hNil $ hLocal prog 0
-- [5, 0]
\end{code}
%endif

\paragraph*{N-queens with Only One State}\
%
With |simulate|, we can implement the backtracking algorithm of the
n-queens problem in \Cref{sec:motivation-and-challenges} with only
one state effect as follows.

\begin{code}
queensSim  :: Int -> [[Int]]
queensSim  = hNil . flip simulate (0, []) . queens
\end{code}

% Furthermore, we can replace the simulation |local2global| in the definition of |simulate|
% with the manual simulation |queensR| using the undo semantics.
% \begin{code}
% queensSimR   :: Int -> [[Int]]
% queensSimR   = hNil . flip extract (0, [])
%              . hState . states2state . nondet2state . comm2 . modify2global . queensR
% \end{code}
