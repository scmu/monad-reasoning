%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Overview
import LocalGlobal (local2global, hLocal, comm2)
import NondetState (runNDf, SS(..), nondet2state, extractSS, queensState)
import Control.Monad.State.Lazy hiding (fail, mplus, mzero)

\end{code}
%endif
\section{Combination}
\label{sec:combination}

Throughout the paper, we have shown several cases in which a high-level effect
can be simulated by means of a lower-level effect.
This section combines these simulations to ultimately simulate the combination of
nondeterminism and state with a single state effect.

%-------------------------------------------------------------------------------
\subsection{Modeling Multiple States with State}
\label{sec:multiple-states}

For an effect that contains multiple states we can define two approaches to represent and handle them:
\begin{enumerate}
  \item A representation using and effect functor with two state functors |StateF s1 :+: StateF s2|,
        and a corresponding handler |hStates|, which interprets the two state functors as two nested
        |StateT| monads. In essence, this handler applies two |hState| handlers in sequence.
\begin{code}
hStates :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT s1 (StateT s2 (Free f)) a
hStates t = StateT $ \s1 -> hState $ runStateT (hState t) s1
\end{code}
  \item A representation using a single state effect functor that contains a tuple of two states
        |StateF (s1, s2)|. The corresponding handler, |hStateTuple|,
        interprets the state functor as a |StateT| monad. This implementation is exactly the definition
        of the |hState| handler, in which state |s| is defined as a tuple of two states.
\begin{code}
hStateTuple :: Functor f => Free (StateF (s1, s2) :+: f) a -> StateT (s1, s2) (Free f) a
hStateTuple = hState
\end{code}
\end{enumerate}

We can define a simulation of the first representation |StateF s1 :+: StateF s2| in terms of the
second representation |StateF (s1, s2)|.
The |states2state| function defines this simulation using a |fold|:

\begin{code}
states2state  :: Functor f
              => Free (StateF s1 :+: StateF s2 :+: f) a
              -> Free (StateF (s1, s2) :+: f) a
states2state  = fold gen (alg1 # alg2 # fwd)
  where
    gen :: Functor f => a -> Free (StateF (s1, s2) :+: f) a
    gen = return

    alg1  :: Functor f  => StateF s1 (Free (StateF (s1, s2) :+: f) a)
                        -> Free (StateF (s1, s2) :+: f) a
    alg1 (Get k)      = get' >>= \(s1,  _)   -> k s1
    alg1 (Put s1' k)  = get' >>= \(_,   s2)  -> put' (s1', s2) k

    alg2  :: Functor f  => StateF s2 (Free (StateF (s1, s2) :+: f) a)
                        -> Free (StateF (s1, s2) :+: f) a
    alg2 (Get k)      = get' >>= \(_,   s2)  -> k s2
    alg2 (Put s2' k)  = get' >>= \(s1,  _)   -> put' (s1, s2') k

    fwd  :: Functor f   => f (Free (StateF (s1, s2) :+: f) a)
                        -> Free (StateF (s1, s2) :+: f) a
    fwd op            = Op (Inr op)
\end{code}
Here, |get'| and |put'| are smart constructors for getting the state and putting a new state.
\begin{code}
get'        :: Functor f => Free (StateF s :+: f) s
get'        = Op (Inl (Get return))

put'        :: s -> Free (StateF s :+: f) a -> Free (StateF s :+: f) a
put' sts k  = Op (Inl (Put sts k))
\end{code}

To prove this simulation correct, we define a function to transform between
the nested state transformer and the state transformer with a tuple of states.
This transformation can be defined in terms of two isomorphic functions
|flatten| and |nested|.
The proof of this isomorphism can be found in \ref{app:flatten-nested}.

\begin{code}
flatten    :: Functor f =>  StateT s1 (StateT s2 (Free f)) a -> StateT (s1, s2) (Free f) a
flatten t  = StateT $ \ (s1, s2) -> alpha <$> runStateT (runStateT t s1) s2
nested     :: Functor f =>  StateT (s1, s2) (Free f) a -> StateT s1 (StateT s2 (Free f)) a
nested t   = StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)
\end{code}

%if False
\begin{code}
alpha :: ((a, x), y) -> (a, (x, y))
alpha ((a, x), y) = (a, (x, y))
alpha1 :: (a, (x, y)) -> ((a, x), y)
alpha1 (a, (x, y)) = ((a, x), y)


f t = StateT $ \ s1 -> StateT $ \ s2 -> (fmap (alpha1 . alpha) (runStateT (runStateT t s1) s2))
\end{code}
%endif

The isomorphic functions |alpha| and |alpha1| are defined as in the following diagram.

% https://q.uiver.app/?q=WzAsMixbMCwwLCJ8KChhLHgpLHkpfCJdLFsyLDAsInwoYSwgKHgseSkpfCJdLFswLDEsInxhbHBoYXwiLDAseyJvZmZzZXQiOi0zfV0sWzEsMCwifGFscGhhMXwiLDAseyJvZmZzZXQiOi0zfV1d
\[\begin{tikzcd}
  {|((x,y),z)|} && {|(x,(y,z))|}
  \arrow["{|alpha|}", shift left=3, from=1-1, to=1-3]
  \arrow["{|alpha1|}", shift left=3, from=1-3, to=1-1]
\end{tikzcd}\]

The following commuting diagram shows how the simulation works.

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ8RnJlZSAoU3RhdGVGIHMxIDorOiBTdGF0ZUYgczIgOis6IGYpIGF8Il0sWzAsMiwifEZyZWUgKFN0YXRlRiAoczEsIHMyKSA6KzpmKSBhfCJdLFsyLDAsInxTdGF0ZVQgczEgKFN0YXRlVCBzMiAoRnJlZSBmKSkgYXwiXSxbMiwyLCJ8U3RhdGVUIChzMSwgczIpIChGcmVlIGYpIGF8Il0sWzIsMywifGZsYXR0ZW58IiwyLHsib2Zmc2V0Ijo1fV0sWzMsMiwifG5lc3RlZHwiLDIseyJvZmZzZXQiOjV9XSxbMCwyLCJ8aFN0YXRlc3wiXSxbMSwzLCJ8aFN0YXRlVHVwbGV8IiwyXSxbMCwxLCJ8c3RhdGVzMnN0YXRlfCIsMl1d
\[\begin{tikzcd}
  {|Free (StateF s1 :+: StateF s2 :+: f) a|} && {|StateT s1 (StateT s2 (Free f)) a|} \\
  \\
  {|Free (StateF (s1, s2) :+:f) a|} && {|StateT (s1, s2) (Free f) a|}
  \arrow["{|flatten|}"', shift right=5, from=1-3, to=3-3]
  \arrow["{|nested|}"', shift right=5, from=3-3, to=1-3]
  \arrow["{|hStates|}", from=1-1, to=1-3]
  \arrow["{|hStateTuple|}"', from=3-1, to=3-3]
  \arrow["{|states2state|}"', from=1-1, to=3-1]
\end{tikzcd}\]

To prove the simulation correct we have to prove the following theorem:
\begin{theorem}\label{thm:states-state}
< flatten . hStates = hStateTuple . states2state
\end{theorem}
As |flatten| and |nested| are isomorphic functions, the following equivalence should hold
as well:
< hStates = nested . hStateTuple . states2state

We can easily fuse the composition |flatten . hStates| using equational reasoning techniques,
as shown in \Cref{app:states-state-fusion}.
The correctness of the simulation is written out in Appendix \Cref{app:states-state-sim}.

%if False
% NOTE: some test code to assit in writing proofs
\begin{code}

extractqwq x s = resultsSS . fst . snd <$> runStateT x (SS [] [], s)
extractSSqwq :: Functor f1 => StateT (SS f2 a1) f1 a2 -> f1 [a1]
extractSSqwq x = resultsSS . snd <$> runStateT x (SS [] [])

qwq :: (Functor f) => StateT (SS (StateF s :+: f) a) (StateT s (Free f)) () -> (s -> Free f [a])
qwq = extract . flatten

qwq' :: Functor f => StateT (SS f a) (Free f) () -> Free f [a]
qwq' = extractSS

sar :: Functor f => Free (StateF (SS (StateF s :+: f) a) :+: StateF s :+: f) () -> s -> Free f [a]
sar t =
  \s -> fmap (resultsSS . snd . fst) $ (flip runStateT s . hState) $ runStateT (hState t) (SS [] [])
  -- resultsSS . snd :: ((), SS (StateF s :+: f) a) -> [a]
  -- hState :: Free (StateF s :+: f) ((), SS (StateF s :+: f) a) -> StateT s (Free f) ((), SS (StateF s :+: f) a)
  -- runStateT :: StateT s (Free f) ((), SS (StateF s :+: f) a) -> s -> Free f (((), SS (StateF s :+: f) a), s)

sar' :: Functor f => Free (StateF (SS (StateF s :+: f) a) :+: StateF s :+: f) () -> s -> Free f [a]
sar' t =
  \s -> fmap fst . (flip runStateT s . hState) $ fmap (resultsSS . snd) $ runStateT (hState t) (SS [] [])
  -- resultsSS . snd :: ((), SS (StateF s :+: f) a) -> [a]
  -- hState :: Free (StateF s :+: f) [a] -> StateT s (Free f) [a]
  -- runStateT :: Free (StateF s :+: f) [a] -> StateT s (Free f) [a]

www :: Functor f => s -> Free (StateF s :+: f) a -> Free f (a, s)
www s = flip runStateT s . hState
----------------------------------------------------------------

x0 :: a -> Free (StateF s1 :+: StateF s2 :+: f) a
x0 x = Var x

x1 :: Functor f => (s1 -> Free (StateF s1 :+: StateF s2 :+: f) a) -> Free (StateF s1 :+: StateF s2 :+: f) a
x1 k = Op (Inl (Get k))

x2 :: Functor f => s1 -> Free (StateF s1 :+: StateF s2 :+: f) a -> Free (StateF s1 :+: StateF s2 :+: f) a
x2 s k = Op (Inl (Put s k))

x3 :: Functor f => (s2 -> Free (StateF s1 :+: StateF s2 :+: f) a) -> Free (StateF s1 :+: StateF s2 :+: f) a
x3 k =
  let tmp =
          StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
          $ runStateT (hState (runStateT (StateT $ \s -> Op $ (Inl (Get ((\k -> runStateT k s) . hState . k)))) s1)) s2
  in Op (Inr (Inl (Get k)))

fwdS op           = StateT $ \s -> Op $ fmap (\k -> runStateT k s) op
algS (Get     k)  = StateT $ \s -> runStateT (k s) s
algS (Put s'  k)  = StateT $ \s -> runStateT k s'

x4 :: Functor f => s2 -> Free (StateF s1 :+: StateF s2 :+: f) a -> Free (StateF s1 :+: StateF s2 :+: f) a
x4 s k =
  let tmp =
        StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
          $ runStateT (hState (runStateT (fwdS (Inl (Put s (hState k)))) s1)) s2
  in Op (Inr (Inl (Put s k)))

x5 :: Functor f => f (Free (StateF s1 :+: StateF s2 :+: f) a) -> Free (StateF s1 :+: StateF s2 :+: f) a
x5 y =
  let tmp =
        StateT $ \ (s1, s2) -> Op (fmap (fmap (\ ((a, x), y) -> (a, (x, y))) . (\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
  in let tmp2 = StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap (\t -> StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (runStateT (hState t) s1)) s2) y)
  in Op (Inr (Inr y))
\end{code}
%endif

%-------------------------------------------------------------------------------
\paragraph*{Simulating Nondeterminism and State with Only State}\
%
By now we have defined three simulations for encoding a high-level effect as a lower-level effect.
\begin{itemize}
  \item The function |nondet2state| simulates the high-level nondeterminism effect with the state effect
  (Section \ref{sec:nondeterminism-state}).
  \item The function |local2global| simulates the high-level local-state effect with global-state
  semantics (Section \ref{sec:local-global}).
  \item The function |states2state| simulates multiple state effects with a single-state semantics
  (Section \ref{sec:multiple-states}).
\end{itemize}

Combining these simulations, we can encode the semantics for nondeterminism and state with
just the state transformer monad.
An overview of this simulation is given in Figure \ref{fig:simulation}.

\begin{figure}[h]
% https://q.uiver.app/?q=WzAsOCxbMCwwLCJ8RnJlZSAoU3RhdGVGIHMgOis6IE5vbmRldEYgOis6IGYpIGF8Il0sWzAsMSwifEZyZWUgKFN0YXRlRiBzIDorOiBOb25kZXRGIDorOiBmKSBhfCJdLFswLDIsInxGcmVlIChOb25kZXRGIDorOiBTdGF0ZUYgcyA6KzogZikgYXwiXSxbMCwzLCJ8Q29tcFNTIChTUyAoU3RhdGVGIHMgOis6IGYpIGEpIChTdGF0ZUYgcyA6KzogZikgKCl8Il0sWzAsNCwifEZyZWUgKFN0YXRlRiAoU1MgKFN0YXRlRiBzIDorOiBmKSBhKSA6KzogU3RhdGVGIHMgOis6IGYpICgpfCJdLFswLDUsInxGcmVlIChTdGF0ZUYgKFNTIChTdGF0ZUYgcyA6KzogZikgYSwgcykgOis6IGYpICgpfCJdLFswLDYsInxTdGF0ZVQgKFNTIChTdGF0ZUYgcyA6KzogZikgYSwgcykgKEZyZWUgZikgKCl8Il0sWzAsNywifHMgLT4gRnJlZSBmIFthXXwiXSxbMCwxLCJ8bG9jYWwyZ2xvYmFsfCJdLFsxLDIsInxjb21tMnwiXSxbMiwzLCJ8bm9uZGV0MnN0YXRlfCJdLFszLDQsIlxcdGV4dHtkZWZpbml0aW9uIG9mIH0gfENvbXBTU3wiXSxbNCw1LCJ8c3RhdGVzMnN0YXRlfCJdLFs1LDYsInxoU3RhdGV8Il0sWzAsNSwifHNpbXVsYXRlfCIsMCx7Im9mZnNldCI6LTUsImN1cnZlIjotNSwiY29sb3VyIjpbMCwwLDUwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fSxbMCwwLDUwLDFdXSxbNiw3LCJ8ZXh0cmFjdHwiLDAseyJjb2xvdXIiOlswLDAsNTBdLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3R0ZWQifX19LFswLDAsNTAsMV1dXQ==
\[\begin{tikzcd}
  {|Free (StateF s :+: NondetF :+: f) a|} \\
  {|Free (StateF s :+: NondetF :+: f) a|} \\
  {|Free (NondetF :+: StateF s :+: f) a|} \\
  {|CompSS (SS (StateF s :+: f) a) (StateF s :+: f) ()|} \\
  {|Free (StateF (SS (StateF s :+: f) a) :+: StateF s :+: f) ()|} \\
  {|Free (StateF (SS (StateF s :+: f) a, s) :+: f) ()|} \\
  {|StateT (SS (StateF s :+: f) a, s) (Free f) ()|} \\
  {|s -> Free f [a]|}
  \arrow["{|local2global|}", from=1-1, to=2-1]
  \arrow["{|comm2|}", from=2-1, to=3-1]
  \arrow["{|nondet2state|}", from=3-1, to=4-1]
  \arrow["{\text{definition of } |CompSS|}", from=4-1, to=5-1]
  \arrow["{|states2state|}", from=5-1, to=6-1]
  \arrow["{|hState|}", from=6-1, to=7-1]
  \arrow["{|simulate|}", shift left=25, color={rgb,255:red,128;green,128;blue,128}, curve={height=-150pt}, dotted, from=1-1, to=6-1]
  \arrow["{|extract|}", color={rgb,255:red,128;green,128;blue,128}, dotted, from=7-1, to=8-1]
\end{tikzcd}\]
\caption{The simulation explained.}
\label{fig:simulation}
\end{figure}

We explain the steps here in detail.
Broadly speaking, we use a simulation function |simulate| to interpret the semantics for state, nondeterminism
and possibly other effects in terms of a state transformer,
and afterwards a function |extract| that gets the result form the state transformer.

The simulation function is a composition of the different handlers we have defined:
\begin{code}
simulate  :: Functor f
          => Free (StateF s :+: NondetF :+: f) a
          -> StateT (SS (StateF s :+: f) a, s) (Free f) ()
simulate  = hState . states2state . nondet2state . comm2 . local2global
\end{code}
First, |local2global| models the local-state semantics with a global state.
Second, we use commutativity and associativity of the coproduct operator to change
the order of state and nondeterminism.

Next, |nondet2state| transforms the nondeterminism effect into a simulation with state.
Then, we use the definition of |CompSS| to represent it as a free monad so that the
|states2state| simulation can combine the two state effects into a single state.
Finally, |hState| handles this state effect and translates it to the state transformer |StateT|.

Additionally, the |extract| function extracts the final result from the state monad transformer
into a more readable form.
\begin{code}
extract   :: (Functor f)
          => StateT (SS (StateF s :+: f) a, s) (Free f) ()
          -> (s -> Free f [a])
extract x s = resultsSS . fst . snd <$> runStateT x (SS [] [], s)
\end{code}

To show that this simulation is correct, we need to prove that |extract . simulate = hLocal|,
or, in a more elaborate form:
< hLocal = extract . hState . states2state . nondet2state . comm2 . local2global
The proof of this simulation can be found in \Cref{app:final-simulate}.

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
tt = hNil $ (extract . simulate) prog 0
-- [5, 0]
tt' :: [Int]
tt' = hNil $ hLocal prog 0
-- [5, 0]
\end{code}
%endif

\paragraph*{N-queens with Only State}\
%
Using the simulation methods shown in Figure \ref{fig:simulation},
we can simulate the backtracking algorithm of the n-queens problem
of \Cref{sec:motivation-and-challenges} with only state.
The function |queensSim| shows this simulation for the n-queens example.
\begin{code}
queensSim  :: Int -> [[Int]]
queensSim  = hNil . flip extract (0, []) . simulate . queens
\end{code}

% Furthermore, we can replace the simulation |local2global| in the definition of |simulate|
% with the manual simulation |queensR| using the undo semantics.
% \begin{code}
% queensSimR   :: Int -> [[Int]]
% queensSimR   = hNil . flip extract (0, [])
%              . hState . states2state . nondet2state . comm2 . modify2global . queensR
% \end{code}
