\section{Modeling Nondeterminism With State}
\label{sec:nondeterminism-state}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
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

In the previous section, we have mapped the local-state semantics, which is a
high-level combination of state and nondeterminism, onto the global-state
semantics, which is a more low-level combination of state and nondeterminism.
This section takes on the resulting nondeterminism component, which is itself a
relatively high-level effect that can be mapped onto a more low-level
implementation in terms of state. Indeed, while nondeterminism typically
modelled using the |List| monad, many efficient nondeterministic systems, such
as Prolog, use a lower-level state-based implementation to simulate this
effect.

This section shows how the simulation works, and proves it correct using
equational reasoning techniques.

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
by means of the |choose| function defined in \Cref{sec:motivation-and-challenges},
which is a nondeterminism-monad morphism.
%if False
\begin{code}
etand :: MNondet m => a -> m a
etand = return

mul :: [[a]] -> [a]
mul = foldr (++) []
\end{code}
%endif
% \begin{code}
% choose :: MNondet m => [a] -> m a
% choose = foldr (mplus . etand) mzero
% \end{code}

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

For this, we use a type of state |S a| that is a essentially a tuple of
(1) the |results| found so far |[a]|, and
(2) a stack the branches with computations yet to be explored, which we call the
residual computations or the |stack|.
The branches in the stack are represented by computations in the monad over the
state signature.
\begin{code}
type Comp s a = Free (StateF s) a
data S a = S { results :: [a], stack :: [Comp (S a) ()]}
\end{code}
To simulate a nondeterministic computation |Free NondetF a| with this state wrapper,
we define three helper functions in Figure \ref{fig:pop-push-append}.
The function |popS| takes the upper element of the stack.
The function |pushS| adds a branch to the stack.
The function |appendS| adds a result to the given results.

\noindent
\begin{figure}[t]
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popS :: Comp (S a) ()
popS = do
  S xs stack <- getS
  case stack of
    []       -> return ()
    op : ps  -> do
      putS (S xs ps); op
\end{code}
\caption{Popping from the stack.}
\label{fig:pop}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushS   :: Comp (S a) ()
        -> Comp (S a) ()
        -> Comp (S a) ()
pushS q p = do
  S xs stack <- getS
  putS (S xs (q : stack)); p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
appendS   :: a
          -> Comp (S a) ()
          -> Comp (S a) ()
appendS x p = do
 S xs stack <- getS
 putS (S (xs ++ [x]) stack); p
\end{code}
\caption{Appending a result.}
\label{fig:append}
\end{subfigure}%
\caption{Helper functions |popS|, |pushS| and |appendS|.}
\label{fig:pop-push-append}
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
The generator of this handler records a new result and then pops the next
branch from the stack stack and proceeds with it. Likewise, failure
simply pops and proceeds with the next branch. Lastly, a choice pushes
the second branch on the stack and proceeds with the first branch.

To extract the final result from the |S| wrapper, we define the |extractS| function.
\begin{code}
extractS :: State (S a) () -> [a]
extractS x = results . snd $ runState x (S [] [])
\end{code}
At last, |runND| wraps everything up to handle a nondeterministic
computation to a list of results.
\begin{code}
runND :: Free NondetF a -> [a]
runND = extractS . hState' . nondet2stateS
\end{code}

To prove this simulation correct, we show that the
|runND| function is equivalent to the nondeterminism handler |hND| defined in Section \ref{sec:free-monads-and-their-folds}.

\begin{theorem}
|runND = hND|
\end{theorem}

For the proof it is convenient to expand the definition of |runND| again,
and to add parentheses for grouping:
< (extractS . hState') . nondet2stateS = hND
As both |nondet2stateS| and |hND| are folds,
we can use the fold fusion law for postcomposition as defined in
Equation \ref{eq:fusion-post} to show that the two sides of the equation
are equal.
Hence, we have to prove the following two equations.
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

We can generalize the above simulation to work in combination with other effects.
Adding this \emph{modularity} has an impact on several definitions, as well as on
the implementation and proof.

Firstly, we augment the signature in the computation type
with an additional component |f| for the additional effects.
\begin{code}
type CompSS s f a = Free (StateF s :+: f) a
data SS f a = SS { resultsSS :: [a], stackSS :: [CompSS (SS f a) f ()] }
\end{code}

As a consequence, the |nondet2state| handler requires a forwarding
algebra |fwd| to deal with |f|.

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
  SS xs stack <- getSS
  case stack of
    []       -> return ()
    op : ps  -> do
      putSS (SS xs ps); op
\end{code}
\caption{Popping from the stack.}
\label{fig:pop-ss}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushSS  :: Functor f
        => CompSS (SS f a) f ()
        -> CompSS (SS f a) f ()
        -> CompSS (SS f a) f ()
pushSS q p = do
  SS xs stack <- getSS
  putSS (SS xs (q : stack)); p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push-ss}
\end{subfigure}
\begin{subfigure}[t]{0.35\linewidth}
\begin{code}
appendSS  :: Functor f => a
          -> CompSS (SS f a) f ()
          -> CompSS (SS f a) f ()
appendSS x p = do
  SS xs stack <- getSS
  putSS (SS (xs ++ [x]) stack); p
\end{code}
\caption{Appending a solution.}
\label{fig:append-ss}
\end{subfigure}%
\caption{Helper functions |popSS|, |pushSS| and |appendSS|.}
\label{fig:pop-push-append-SS}
\end{figure}

Finally, |runNDf| puts everything together:
it transforms the non-determinism effect into the state effect and forwards
|f|. Then it uses the, now modular, state handler to interpret the
state effect. Lastly, it extracts the results from the state.
\begin{code}
runNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDf = extractSS . hState . nondet2state

extractSS :: Functor f => StateT (SS f a) (Free f) () -> Free f [a]
extractSS x = resultsSS . snd <$> runStateT x (SS [] [])
\end{code}

We can again show that this modular |runNDf| function is equivalent to the
modular nondeterminism handler |hNDf| defined in \ref{sec:combining-effects}.
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
The proof proceeds essentially in the same way as in the non-modular setting.
The main difference, due to the modularity, is an additional proof case for the forwarding
algebra.
\begin{equation*}
|(extractSS . hState) . fwd = fwdNDf . fmap (extractSS . hState)|
\end{equation*}
The full proof
is included in \Cref{app:in-combination-with-other-effects}.

%-------------------------------------------------------------------------------
%if False
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
              . modify2global . queensR
\end{code}
\birthe{Don't know what this sentence says.}
It also has two simulations, except that the simulation of local state with global state is implemented manually with the |modifyR| in |queensR|.
%endif
