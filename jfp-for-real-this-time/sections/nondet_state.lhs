\section{Modeling Nondeterminism With State}
\label{sec:nondeterminism-state}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module NondetState where

import Background hiding (hNondet)
import Control.Monad (ap, join, liftM)
import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans (lift)

\end{code}
%endif

Two of the most well-known and well-investigated side-effects are nondeterminism
and state. 
Typically, nondeterminism is modelled using a |List| monad.
However, many efficient nondeterministic systems, such as Prolog, 
use a state-based implementation to simulate this effect.
This section shows how this simulation works, and proofs it correct using 
equational reasoning techniques and initiality of the |List| monad.

%-------------------------------------------------------------------------------
\subsection{Interpreting Nondeterministic Programs with List}

The |List| monad, which is used in Haskell to implement nondeterminism, is a lawful instance of |MNondet|.
Indeed, all nondeterminism laws of \cref{sec:nondeterminism} are satisfied by
this implementation.
The return |etal| of the |List| monad is a singleton list 
and the join operation is concatenation or flattening: 
|mul = foldr (++) []|.
This leads us towards the following monad instance.

< instance Monad [] where
<   return x   = [x]
<   m >>= f    = foldr ((++) . f) [] m

We can interpret these nondeterministic programs encoded in lists 
by means of the |choose| function, which can be implemented as a fold.
%if False
\begin{code}
etand :: MNondet m => a -> m a
etand = return

mul :: [[a]] -> [a]
mul = foldr (++) []
\end{code}
%endif
\begin{code}
choose :: MNondet m => [a] -> m a
choose = foldr (mplus . etand) mzero
\end{code}

In fact, the |List| monad is not just an instance for nondeterminism; 
it is the initial lawful instance. 
This means that, for every other lawful instance of nondeterminism, there is a
unique monad morphism from |List| to that instance.
The above definition of |choose| is exactly that monad morphism.
Indeed, for every nondeterminism monad |m| (instance of |MNondet m|), 
the following equalities hold.
\begin{align*}
  |choose . etal| &= |etand|\\
  |choose . mul| &= |mund . choose . fmap choose|\\
                 &= |mund . fmap choose . choose|
\end{align*}

To prove that the morphism is unique, we use the universality of fold, 
which is stated for lists and |choose| as follows:
\begin{align*}
|choose []| &= |v| &  & \\
& &\Longleftrightarrow \hspace{10ex} |choose| &= |fold f v| \\
|choose (x:xs)| &= |f x (choose xs)| & & 
\end{align*}
An extended version of this proof, which uses equational reasoning techniques
to show these properties are satisfied, 
can be found in Appendix \ref{app:initiality-nondeterminism}.

%-------------------------------------------------------------------------------
\subsection{Simulating Nondeterministic Programs with State}
\label{sec:sim-nondet-state}

This section shows how to use a state-based implementation to simulate nondeterminism.

For this, we use a wrapper |ST| around |State| that uses as state a tuple with 
(1) the current solution(s) |m a| wrapped in a monad and 
(2) the branches to be evaluated, which we will call the \emph{stack}.
The return type of |State| is a unit |()|.
\begin{code}
newtype ST m a = ST { runST :: State (m a, [ST m a]) () }
\end{code}
To simulate a nondeterministic computation |NondetC| with this state wrapper, 
we define a few helper functions (Figure \ref{fig:pop-push-append}).
The function |pop| takes the upper element of the stack.
The function |push| adds a branch to the stack.
The function |append| adds a solution to the given solutions. 
\begin{figure}[h]
\small
\begin{subfigure}[t]{0.33\linewidth}
\begin{code}
pop  :: MNondet m 
     => ST m a 
pop = ST $ do 
    (xs, stack) <- get
    case stack of 
        []         ->  return ()
        ST p : ps  ->  do 
            put (xs, ps) ; p
\end{code}
\caption{Popping from the stack.}
\label{fig:pop}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
push  :: MNondet m 
      => ST m a 
      -> ST m a 
      -> ST m a
push q p = ST $ do
    (x, stack) <- get
    put (x, q:stack)
    runST p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
append  :: MNondet m 
        => a 
        -> ST m a 
        -> ST m a
append x p = ST $ do
    (xs, stack) <- get
    put (xs `mplus` return x, stack)
    runST p
\end{code}
\caption{Appending a solution.}
\label{fig:append}
\end{subfigure}%
\label{fig:pop-push-append}
\caption{Helper functions |pop|, |push| and |append|.}
\end{figure}
Now everything is in place to define a simulation function |simulate| that
interprets every nondeterministic computation as a state-wrapped program. 
\begin{code}
simulate :: MNondet m => NondetC a -> ST m a
simulate = fold gen alg
  where
    gen x         = append x pop
    alg Fail      = pop
    alg (Or p q)  = push q p
\end{code}
To extract the final result from the |ST| wrapper, we define the |extract| function.
\begin{code}
extract :: MNondet m => ST m a -> m a
extract x = fst . snd $ runState (runST x) (mzero, [])
\end{code}
This way, |runNondet| is a trivial extension of 
the simulate function. It transforms
every nondeterministic computation to a result that is encapsulated in a
nondeterminism monad.
\begin{code}
runNondet :: MNondet m => NondetC a -> m a
runNondet = extract . simulate
\end{code}

To prove that this simulation is correct, we should show that this 
|runNondet| function is equivalent to a nondeterminism handler. 
For that, we zoom in on a version of such a handler 
(Section \ref{sec:combining-effects}) with no other effects
(|f = NilF|). 
We replace the |List| monad by any other nondeterminism monad |m|.
Consequently, the type signature for the handler changes from
|hNondet :: MNondet m => Free (NondetF :+: NilF) a -> Free NilF (m a)|
to 
|hNondet :: MNondet m => NondetC a -> m a|.
This leaves us with the following implementation for the handler.
\begin{code}
hNondet :: MNondet m => NondetC a -> m a
hNondet = fold genND algND
  where 
    genND           = return 
    algND Fail      = mzero
    algND (Or p q)  = p `mplus` q
\end{code}
We can now show that this handler is equal to the |runNondet| function defined 
above.
\begin{theorem}
|runNondet = hNondet|
\end{theorem}
The proof of this theorem is added in the appendices. 

%-------------------------------------------------------------------------------
\subsection{Combining the Simulation with Other Effects}
\label{sec:combining-the-simulation-with-other-effects}
We can generalize this simulation to work with arbitrary other effects.
These effects are represented by the |sig| monad.
Again, we define a type that encapsulates a form of state. 
< newtype ST' sig m a = ST' { unST :: StateT (m a, [ST' sig m a]) sig () }
%if False
\begin{code}
newtype ST' sig m a = ST' { unST :: S.StateT (m a, [ST' sig m a]) sig () }
\end{code}
%endif
This time we use the state transformer |StateT|, as defined in the 
Monad Transformer Library \ref{}.
< newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }
Thus, the state is |ST'| is again represented by a pair of 
a value a encapsulated in a nondeterminism monad |m a| and
a stack of |ST' sig m a| computations or branches to be evaluated.

We can redefine the |simulate| function as follows:

\begin{code}
simulate' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> ST' (Free f) m a
simulate' = fold gen' alg'
  where
    gen'  x              = append' x pop'
    alg' (Inl Fail)      = pop'
    alg' (Inl (Or p q))  = push' p q
    alg' (Inr y)         = ST' $ join $ lift $ Op (return . unST <$> y)
\end{code}

%if False
\begin{code}
jj :: (Functor f) 
   => S.StateT (m a, [ST' (Free f) m a]) (Free f) (S.StateT (m a, [ST' (Free f) m a]) (Free f) ())
   -> S.StateT (m a, [ST' (Free f) m a]) (Free f) ()
jj fx = S.StateT $ \s -> S.runStateT fx s >>= \(x, s') -> S.runStateT x s'

ll :: (Functor f) 
   => Free f (S.StateT (m a, [ST' (Free f) m a]) (Free f) ())
   -> S.StateT (m a, [ST' (Free f) m a]) (Free f) (S.StateT (m a, [ST' (Free f) m a]) (Free f) ())
ll m = S.StateT $ \s -> m >>= \x -> return (x, s)

hh :: (Functor f)
   => Free f (S.StateT (m a, [ST' (Free f) m a]) (Free f) ())
   -> ST' (Free f) m a
hh fx = ST' $ S.StateT $ \s -> fx >>= \x -> S.runStateT x s
       -- ST' $ S.StateT (\s -> fx >>= \x -> S.runStateT (return x) s
                                 -- >>= \(x', s') -> S.runStateT x' s')
\end{code}
%endif

This function is very similar to the |simulate| function 
of Section \ref{sec:sim-nodet-state}, which now interprets every nondeterministic
program as a state-wrapped computation, leaving other effects alone.
The helper functions |pop'|, |push'| and |append'| 
(Figure \ref{fig:pop-push-append-2}) are very much like the
previous definitions, but adapted to the new state-wrapper type.

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.33\linewidth}
< pop'   :: Monad sig 
<        => ST' sig m a 
< pop' = ST' $ do 
<    (xs, stack) <- get
<    case stack of 
<        []          ->  return ()
<        ST' p : ps  ->  do 
<               put (xs, ps) ; p
\caption{Popping from the stack.}
\label{fig:pop-2}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
< push'   :: Monad sig 
<         => ST' sig m a 
<         -> ST' sig m a 
<         -> ST' sig m a
< push' q p = ST' $ do
<     (xs, stack) <- get
<     put (xs, q:stack)
<     unST p
\caption{Pushing to the stack.}
\label{fig:push-2}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
< append'   :: (Monad sig, MNondet m) 
<           => a 
<           -> ST' sig m a 
<           -> ST' sig m a
< append' x p = ST' $ do
<     (xs, stack) <- get
<     put (xs `mplus` return x, stack)
<     unST p
\caption{Appending a solution.}
\label{fig:append-2}
\end{subfigure}%
\label{fig:pop-push-append-2}
\caption{Helper functions |pop'|, |push'| and |append'|.}
\end{figure}

To extract the final result from the |ST'| wrapper, we define an |extract'| 
function.
< extract' :: (Functor f, MNondet m) => ST' (Free f) m a -> Free f (m a)
< extract' x = fst . snd <$> runStateT (unST x) (mzero,[])
%if False
\begin{code}
pop' :: Monad sig => ST' sig m a 
pop' = ST' $ do 
    (xs, stack) <- S.get
    case stack of 
        []          ->  return ()
        ST' p : ps  ->  do S.put (xs, ps) ; p

push' :: Monad sig => ST' sig m a -> ST' sig m a -> ST' sig m a
push' q p = ST' $ do
    (xs, stack) <- S.get
    S.put (xs, q:stack)
    unST p

append' :: (Monad sig, MNondet m) => a -> ST' sig m a -> ST' sig m a
append' x p = ST' $ do
    (xs, stack) <- S.get
    S.put (xs `mplus` return x, stack)
    unST p

extract' :: (Functor f, MNondet m) => ST' (Free f) m a -> Free f (m a)
extract' x = fst . snd <$> S.runStateT (unST x) (mzero,[])
\end{code}
%endif

Finally, |runNondet'| is again a trivial extension of the simulation.
It transforms every monad with nondeterminism and other effects |f| into
a free monad where the result is wrapped in the nondeterminism monad. 
The other effects |f| are to be dealt with by the appropriate handlers.
\begin{code}
runNondet' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
runNondet' = extract' . simulate'
\end{code}

To prove this approach correct, we should show that this |runNondet'| function
is equal to a nondeterminism handler.
For that, we compare with a version of the handler defined in Section
\ref{sec:combining-effects}, with the |List| monad replaced by any other
nondeterminism monad |m|.
< hNondet' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
< hNondet' = fold gen alg 
<   where 
<     genND' = Var . return 
<     algND' (Inl Fail)      = Var mzero
<     algND' (Inl (Or p q))  = mplus <$> p <*> q
<     algND' (Inr y)         = Op y
We prove that this handler |hNondet'| and the |runNondet'| function are equal.
\begin{theorem}
|runNondet' = hNondet'|
\end{theorem}
The proof of this theorem uses equational reasoning and is added in the 
appendices.












