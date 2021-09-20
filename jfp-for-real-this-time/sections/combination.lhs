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

module Combination where

import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef

import Background
import LocalGlobal (local2global, hLocal, comm2, queensR)
import NondetState (runNDf, SS(..), nondet2state, extractSS)
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
\subsection{Simulating Nondeterminism and State with Only State}

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
\label{fig:simulation}
\caption{The simulation explained.}
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

\paragraph{N-queens with Only State}
Using the simulation methods shown in Figure \ref{fig:simulation},
we can simulate the backtracking algorithm of the n-queens problem
of \Cref{sec:motivation-and-challenges} with only state.
The function |queensSim| shows this simulation for the n-queens example.
\begin{code}
queensSim  :: Int -> [[Int]]
queensSim  = hNil . flip extract (0, []) . simulate . queens
\end{code}
Furthermore, we can replace the simulation |local2global| in the definition of |simulate|
with the manual simulation |queensR| using the undo semantics.
\begin{code}
queensSimR   :: Int -> [[Int]]
queensSimR   = hNil . flip extract (0, [])
             . hState . states2state . nondet2state . comm2 . queensR
\end{code}

%-------------------------------------------------------------------------------
\subsection{Mutable State}
\label{sec:mutable-state}

Performance-wise, it would be better to have an algorithm with mutable state,
instead of the built-in |State| monad that keeps track of state in a pure way.

It is easy to show that a mutable state handler can easily be defined in
Haskell.
We will use a stack to implement mutable state.
\begin{code}
data Stack s a = Stack {   getStack  ::  STRef s   (STArray s Index a),
                           getSize   ::  STRef s   Index }

type Index = Int
\end{code}
This stack consists of two reference cells, one with a (mutable) array
containing the data, another with the size of the stack.
The size of the stack is the amount of allocated space that is actually
filled with data.
We distinguish between the allocated space for the array, obtained by the builtin
|getBounds| function and referred to as |space|, and the size of the array.
Both the |STRef| and the |STArray| datatypes come from Haskell's
|Control.Monad.ST| library that implements the strict |ST| monad.

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
growStack :: Index -> [a] -> ST s (Stack s a)
growStack space elems = do
    stack     <- newListArray (0, space) elems
    sizeRef   <- newSTRef (length elems)
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)
\end{code}
\caption{Growing the stack.}
\label{fig:grow}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
emptyStack :: ST s (Stack s a)
emptyStack = do
    stack     <- newArray_ (0, 1)
    sizeRef   <- newSTRef 0
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)
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
pushStack :: a -> Stack s a -> ST s ()
pushStack x (Stack stackRef sizeRef) = do
    stack       <- readSTRef stackRef
    size        <- readSTRef sizeRef
    (_, space)  <- getBounds stack
    writeSTRef sizeRef (size + 1)
    if size < space
    then writeArray stack size x
    else do
        elems              <- getElems stack
        Stack stackRef' _  <- growStack (space * 2) elems
        stack'             <- readSTRef stackRef'
        writeArray  stack'   size x
        writeSTRef  stackRef stack'
\end{code}
\caption{Pushing to the stack.}
\label{fig:pushstack}
\end{subfigure}%
\begin{subfigure}[t]{0.48\linewidth}
\begin{code}
popStack :: Stack s a -> ST s (Maybe a)
popStack (Stack stackRef sizeRef) = do
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

The functor |StackF| represents the action of
pushing to and popping from the stack.
This is very similar to the |StateF| functor, except for the |Maybe| in the
codomain of the |Pop| element.
This optional value may be |Nothing| when the stack is empty.
\begin{code}
data StackF e a = Push e a | Pop (Maybe e -> a)
\end{code}
%if False
\begin{code}
instance Functor (StackF elem) where
    fmap f (Push x k) = Push x (f k)
    fmap f (Pop k) = Pop (f . k)
\end{code}
%endif

The handler for mutable state |hStack| then works as follows:
\begin{code}
hStack :: (Functor f)
       => Free (StackF e :+: f) a
       -> Stack s e
       -> STT s (Free f) a
hStack = fold gen (alg # fwd)
  where
    gen                   = const . return
    alg (Push x k)  stack = liftST (pushStack x stack)  >> k stack
    alg (Pop k)     stack = liftST (popStack stack)     >>= \x -> k x stack
    fwd y           stack = STT $ \s -> Op ((\f -> unSTT (f stack) s) <$> y)
\end{code}

%if False
\begin{code}
showStack :: Show a => Stack s a -> ST s String
showStack (Stack stackRef sizeRef) = do
    stack <- readSTRef stackRef
    elems <- getElems stack
    size  <- readSTRef sizeRef
    return $ show (take size elems)

test = runST $ do
    stack <- emptyStack
    pushStack (5 :: Int) stack
    pushStack 6 stack
    pushStack 7 stack
    pushStack 8 stack
    Just x <- popStack stack
    Just y <- popStack stack
    Just z <- popStack stack
    Just q <- popStack stack
    return [x, y, z, q]

\end{code}
%endif

The function |queensS| constructs a program which uses the operation of stack and nondeterminism to directly solve the n-queens problem.

\begin{code}
queensS :: Int -> Free (StackF (Int, [Int]) :+: NondetF) [Int]
queensS n = push (0, []) >> loop
  where
    loop = do  s <- pop
               case s of
                 Nothing -> mzero
                 Just (c, sol) ->
                    if c >= n then return sol
                    else do  r <- choose [1..n]
                             filtr valid (r:sol)
                             push ((c, sol) `plus` r)
                             loop

push :: Functor g => e -> Free (StackF e :+: g) ()
push e = Op . Inl $ Push e (return ())
pop :: Functor g => Free (StackF e :+: g) (Maybe e)
pop = Op . Inl $ Pop return

instance Functor f => MNondet (Free (f :+: NondetF)) where
  mzero = Op . Inr $ Fail
  mplus x y = Op . Inr $ Or x y
\end{code}

The function |queensStack| runs the |queens| by applyin the handlers of stack and nondeterminism sequentially.
\begin{code}
queensStack :: Int -> [[Int]]
queensStack n = hND $ runSTT (liftST emptyStack >>= ((hStack (queensS n)) $))
\end{code}

% \begin{code}
% type CompSK s f a = Free (Stack s :+: f ) a
% data SK f a = SK (Free (Stack (SK f a) :+: f) [a])

% popST :: Functor f => SK f a
% popST = SK . Op . Inl $ Pop 

% nondet2stack :: Functor f => Free (NondetF :+: f) a -> Free (StackF s :+: f) [a]
% nondet2stack = fold gen (alg # fwd)
%   where
%     gen = undefined
%     alg = undefined
%     fwd = undefined
% \end{code}
