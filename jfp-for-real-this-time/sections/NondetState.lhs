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

import Background hiding (hND)
import Overview
import Control.Monad (ap, join, liftM)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT, state)
import Control.Monad.Trans (lift)
import LocalGlobal

\end{code}
%endif

Two of the most well-known and well-investigated side-effects are nondeterminism
and state.
Typically, nondeterminism is modelled using the |List| monad.
However, many efficient nondeterministic systems, such as Prolog,
use a lower-level state-based implementation to simulate this effect.
This section shows how this simulation works, and proves it correct using
equational reasoning techniques and initiality of the |List| monad.

%-------------------------------------------------------------------------------
\subsection{Interpreting Nondeterministic Programs with List}
\label{sec:interpreting-nondet-progs-with-list}

The |List| monad, which is used in Haskell to implement nondeterminism, is a lawful instance of |MNondet|.
Indeed, all nondeterminism laws of \cref{sec:nondeterminism} are satisfied by
this implementation.
The return |etal| of the |List| monad is a singleton list
and the join operation is concatenation or flattening, which can be expressed in terms of a |foldr|:
|mul = foldr (++) []|.

We can interpret nondeterministic programs encoded as lists
by means of the |choose| function, which can be implemented using a fold.
This |choose| function is a nondeterminism-monad morphism
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
it is the \emph{initial} lawful instance.
This means that, for every other lawful instance of nondeterminism, there is a
unique nondeterminism-monad morphism from |List| to that instance.
The above definition of |choose| is exactly that nondeterminism-monad morphism.
Indeed, for every nondeterminism monad |m| (instance of |MNondet m|),
the following equalities hold.
\begin{align*}
  |choose []|       &= |mzero|\\
  |choose (x ++ y)| &= |g x `mplus` g y| \\
  |choose . etal|   &= |etand|\\
  |choose . mul|    &= |mund . choose . fmap choose|\\
                    &= |mund . fmap choose . choose|
\end{align*}

To prove that the morphism is unique, we use the universality of fold,
which is stated for lists and |choose| as follows:
\begin{equation*}
\begin{array}{r@@{\,}c@@{\,}l}
|choose []| & = & |v| \\
|choose (x:xs)| & = & |f x (choose x)| \\
\end{array}
\qquad\Longleftrightarrow\qquad
|choose = fold f v|
\end{equation*}


An extended version of this proof, which uses equational reasoning techniques
to show these properties are satisfied,
can be found in Appendix \ref{app:universality-nondeterminism}.

%-------------------------------------------------------------------------------
\subsection{Simulating Nondeterministic Programs with State}
\label{sec:sim-nondet-state}

This section shows how to use a state-based implementation to simulate nondeterminism.

For this, we use a type |S| that is a essentially a tuple of
(1) the current solution(s) |[a]| wrapped in the list monad (|results|), and
(2) the branches with computations to be evaluated, which we will call the
residual computations or the |residue|.
The branches in the residue are represented by the free state monad.
\begin{code}
type Comp s a = Free (StateF s) a
data S a = S { results :: [a], residue :: [Comp (S a) ()]}
\end{code}
To simulate a nondeterministic computation |Free NondetF a| with this state wrapper,
we define a helper functions in Figure \ref{fig:pop-push-append}.
The function |popS| takes the upper element of the residue.
The function |pushS| adds a branch to the residue.
The function |appendS| adds a solution to the given solutions.

\noindent
\begin{figure}[t]
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popS :: Comp (S a) ()
popS = do
  S xs res <- getS
  case res of
    []       -> return ()
    op : ps  -> do
      putS (S xs ps); op
\end{code}
\caption{Popping from the residue.}
\label{fig:pop}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushS   :: Comp (S a) ()
        -> Comp (S a) ()
        -> Comp (S a) ()
pushS q p = do
  S xs res <- getS
  putS (S xs (q : res)); p
\end{code}
\caption{Pushing to the residue.}
\label{fig:push}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
appendS   :: a
          -> Comp (S a) ()
          -> Comp (S a) ()
appendS x p = do
 S xs res <- getS
 putS (S (xs ++ [x]) res); p
\end{code}
\caption{Appending a solution.}
\label{fig:append}
\end{subfigure}%
\label{fig:pop-push-append}
\caption{Helper functions |popS|, |pushS| and |appendS|.}
\end{figure}

Furthermore, we define smart constructors |getS| and |putS s| for getting
the current state and putting a new state.

\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
getS :: Comp s s
getS = Op (Get return)
\end{code}
\end{minipage}
\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
putS :: s -> Comp s ()
putS s = Op (Put s (return ()))
\end{code}
\end{minipage}

Now, everything is in place to define a simulation function |nondet2stateS| that
interprets every nondeterministic computation as a state-wrapped program.
\begin{code}
nondet2stateS :: Free NondetF a -> Comp (S a) ()
nondet2stateS = fold gen alg
  where
    gen x         = appendS x popS
    alg Fail      = popS
    alg (Or p q)  = pushS q p
\end{code}
To extract the final result from the |S| wrapper, we define the |extractS| function.
\begin{code}
extractS :: State (S a) () -> [a]
extractS x = results . snd $ runState x (S [] [])
\end{code}
This way, |runND| is a trivial extension of
the simulate function. It transforms
every nondeterministic computation to a result that is encapsulated in a
nondeterminism monad.
\begin{code}
runND :: Free NondetF a -> [a]
runND = extractS . hState' . nondet2stateS
\end{code}

To prove this simulation correct, we show that the
|runND| function is equivalent to the nondeterminism handler |hND| defined in Section \ref{sec:combining-effects}.

\begin{theorem}
|runND = hND|
\end{theorem}

We start with expanding the definition of |runND|:
< extractS . hState' . nondet2stateS = hND
Both |nondet2stateS| and |hND| are written as a fold.
We can use the universal property of fold to show that the two sides of the equation
are equal.
For this, we use the fold fusion law for postcomposition as defined in
Equation \ref{eq:fusion-post}.

We have to prove the following two equations.
\begin{enumerate}
    % \item |extractS . gen = genND|
    % \item |extractS . alg = algND . fmap extractS|
    \item |(extractS . hState') . gen = genND|
    \item |(extractS . hState') . alg = algND . fmap (extractS . hState')|
\end{enumerate}
The full proof of this theorem is added in Appendix \ref{app:runnd-hnd}.

%-------------------------------------------------------------------------------
\subsection{Combining the Simulation with Other Effects}
\label{sec:combining-the-simulation-with-other-effects}

We can generalize this simulation to work with arbitrary other effects.
Adding this \emph{modularity} has an impact on several definitions, as well as on
the implementation and proof.

Again, we define a type |SS| that encapsulates a form of state.
The results are, as before, encapsulated in a list, and
the residual computations can possibly contain
other effects, captured by the effect functor |f|.
\begin{code}
type CompSS s f a = Free (StateF s :+: f) a
data SS f a = SS { resultsSS :: [a], residueSS :: [CompSS (SS f a) f ()] }
\end{code}

We can define a simulation function |nondet2state| that handles the state effect
in a similar way as |nondet2statesS|.
The other effects are left for other handlers, using a forwarding algebra |fwd|.

\begin{code}
nondet2state  :: Functor f => Free (NondetF :+: f) a -> CompSS (SS f a) f ()
nondet2state = fold gen (alg # fwd)
  where
    gen x         = appendSS x popSS
    alg Fail      = popSS
    alg (Or p q)  = pushSS q p
    fwd y         = Op (Inr y)
\end{code}

The helper functions |popSS|, |pushSS| and |appendSS|
(Figure \ref{fig:pop-push-append-SS}) are very similar to the
previous definitions, but adapted to the new state-wrapper type.
Similarly, |getSS| and |putSS s| are smart constructors for getting
the stating and putting a new state, adapted from their previous definitions
to take the coproduct operator into account.

\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
getSS :: Functor f => CompSS s f s
getSS = Op (Inl (Get return))
\end{code}
\end{minipage}
\begin{minipage}[t][][t]{0.5\textwidth}
\begin{code}
putSS :: Functor f => s -> CompSS s f ()
putSS s = Op (Inl (Put s (return ())))
\end{code}
\end{minipage}

\noindent
\begin{figure}[h]
\noindent
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popSS  :: Functor f
       => CompSS (SS f a) f ()
popSS = do
  SS xs res <- getSS
  case res of
    []       -> return ()
    op : ps  -> do
      putSS (SS xs ps); op
\end{code}
\caption{Popping from the residue.}
\label{fig:pop-ss}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushSS  :: Functor f
        => CompSS (SS f a) f ()
        -> CompSS (SS f a) f ()
        -> CompSS (SS f a) f ()
pushSS q p = do
  SS xs res <- getSS
  putSS (SS xs (q : res)); p
\end{code}
\caption{Pushing to the residue.}
\label{fig:push-ss}
\end{subfigure}
\begin{subfigure}[t]{0.35\linewidth}
\begin{code}
appendSS  :: Functor f => a
          -> CompSS (SS f a) f ()
          -> CompSS (SS f a) f ()
appendSS x p = do
  SS xs res <- getSS
  putSS (SS (xs ++ [x]) res); p
\end{code}
\caption{Appending a solution.}
\label{fig:append-ss}
\end{subfigure}%
\label{fig:pop-push-append-SS}
\caption{Helper functions |popSS|, |pushSS| and |appendSS|.}
\end{figure}

To extract the final result from the |SS| wrapper, we define an |extractSS|
function.
Compared to |extractS|, this function deals with the state transformer |StateT|
instead of |State|.
\begin{code}
extractSS :: Functor f => StateT (SS f a) (Free f) () -> Free f [a]
extractSS x = resultsSS . snd <$> runStateT x (SS [] [])
\end{code}

Finally, |runNDf| is again a trivial extension of the simulation.
It transforms every monad with nondeterminism and other effects |f| into
a free monad where the result is wrapped in the nondeterminisc list monad.
Other effects |f| are to be dealt with by their appropriate handlers.
\begin{code}
runNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDf = extractSS . hState . nondet2state
\end{code}

To prove this approach correct, we show that this |runNDf| function
is equivalent to the nondeterminism handler |hNDf| defined in \ref{sec:combining-effects}.
% For that, we compare with the version of the nondeterminism handler |hNDf| defined in \ref{sec:combining-effects}.
% \begin{code}
% hNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
% hNDf = fold genNDf (algNDf # fwdNDf)
%   where
%     genNDf           = Var . return
%     algNDf Fail      = Var []
%     algNDf (Or p q)  = (++) <$> p <*> q
%     fwdNDf op        = Op op
% \end{code}
% We prove that this handler |hNDf| and the |runNDf| function are equal.
\begin{theorem}\label{thm:nondet-state}
|runNDf = hNDf|
\end{theorem}
As before, we first expand the definition of |runNDf|,
which is written in terms of |nondet2state|, a fold.
We use fold fusion to incorporate |extractSS . hState| in this fold.
The universal property of fold then teaches us that |runNDf| and
|hNDf| are equal.
More concretely, we have to prove the following two things:
\begin{enumerate}
    % \item |extractSS . gen = genNDf|
    % \item |extractSS . (alg # fwd) = (algNDf # fwdNDf) . fmap extractSS|
    \item |(extractSS . hState) . gen = genNDf|
    \item |(extractSS . hState) . (alg # fwd) = (algNDf # fwdNDf) . fmap (extractSS . hState)|
\end{enumerate}
Due to the modularity, we need to include a different case for the forwarding algebra.
The full proof of this theorem, using equational reasoning techniques,
is included in \Cref{app:in-combination-with-other-effects}.

%-------------------------------------------------------------------------------
\subsection{Using State to Simulate Nondeterminism in N-queens}

We revisit the n-queens example of \Cref{sec:motivation-and-challenges}.
We can apply the simulation function |nondet2state| to the n-queens problem
after the simulation |local2global|.
We start with the definition of |queensGlobal| and reason as follows:
< {-~ definition of |queensGlobal| -}
< hNil . flip hGlobal (0, []) . local2global . queens
< {-~ definition of |hGlobal| -}
< hNil
<    . flip (fmap (fmap fst) . runStateT . hState . hNDf . comm2) (0, [])
<    . local2global . queens
< {-~ reorder -}
< hNil
<    . fmap fst . flip runStateT (0, []) . hState . hNDf . comm2
<    . local2global . queens
< {-~ simulation function for |hNDf| -}
< hNil
<    . fmap fst . flip runStateT (0, []) . hState
<    . (extractSS . hState . nondet2state) . comm2
<    . local2global . queens

Thus, the function |queensState| uses the two simulation functions in sequence.
\begin{code}
queensState   :: Int -> [[Int]]
queensState   = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . (extractSS . hState . nondet2state) . comm2
              . local2global . queens
\end{code}
Similarly, we can develop a version of |queensStateR| based on |queensModify|,
which uses the undo semantics.
\begin{code}
queensStateR  :: Int -> [[Int]]
queensStateR  = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . (extractSS . hState . nondet2state) . comm2
              . queensR
\end{code}
\birthe{Don't know what this sentence says.}
It also has two simulations, except that the simulation of local state with global state is implemented manually with the |modifyR| in |queensR|.
