\section{Modeling Nondeterminism with State}
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

In the previous section, we have translated the local-state semantics,
a high-level combination of the state and nondeterminism effects, to
the global-state semantics, a more low-level combination of the state
and nondeterminism effects.
%
In this section, we further translate the resulting nondeterminism
component, which is itself a relatively high-level effect, to a more
low-level implementation with the state effect.
%
Our translation coincides with the fact that, while nondeterminism is
typically modelled using the |List| monad, many efficient
nondeterministic systems, such as Prolog, use a more low-level
state-based implementation to implement the nondeterminism mechanism.

% This section shows how the simulation works, and proves it correct using
% equational reasoning techniques.

% %-------------------------------------------------------------------------------
% \subsection{Interpreting Nondeterministic Programs with List}
% \label{sec:interpreting-nondet-progs-with-list}
% 
% The |List| monad, which is used in Haskell to implement nondeterminism, is a lawful instance of |MNondet|.
% Indeed, all nondeterminism laws of \cref{sec:nondeterminism} are satisfied by
% this implementation.
% The return |etal| of the |List| monad is a singleton list
% and the join operation is concatenation or flattening, which can be expressed in terms of a |foldr|:
% |mul = foldr (++) []|.
% 
% We can interpret nondeterministic programs encoded as lists
% by means of the |choose| function defined in \Cref{sec:motivation-and-challenges},
% which is a nondeterminism-monad morphism.
% %if False
% \begin{code}
% etand :: MNondet m => a -> m a
% etand = return
% 
% mul :: [[a]] -> [a]
% mul = foldr (++) []
% \end{code}
% %endif
% % \begin{code}
% % choose :: MNondet m => [a] -> m a
% % choose = foldr (mplus . etand) mzero
% % \end{code}
% 
% In fact, the |List| monad is not just an instance for nondeterminism;
% it is the \emph{initial} lawful instance.
% This means that, for every other lawful instance of nondeterminism, there is a
% unique nondeterminism-monad morphism from |List| to that instance.
% The above definition of |choose| is exactly that nondeterminism-monad morphism.
% Indeed, for every nondeterminism monad |m| (instance of |MNondet m|),
% the following equalities hold.
% \begin{align*}
%   |choose []|       &= |mzero|\\
%   |choose (x ++ y)| &= |g x `mplus` g y| \\
%   |choose . etal|   &= |etand|\\
%   |choose . mul|    &= |mund . choose . fmap choose|\\
%                     &= |mund . fmap choose . choose|
% \end{align*}
% 
% To prove that the morphism is unique, we use the universality of fold,
% which is stated for lists and |choose| as follows:
% \begin{equation*}
% \begin{array}{r@@{\,}c@@{\,}l}
% |choose []| & = & |v| \\
% |choose (x:xs)| & = & |f x (choose x)| \\
% \end{array}
% \qquad\Longleftrightarrow\qquad
% |choose = fold f v|
% \end{equation*}
% 
% 
% An extended version of this proof, which uses equational reasoning techniques
% to show these properties are satisfied,
% can be found in Appendix \ref{app:universality-nondeterminism}.
% 
%-------------------------------------------------------------------------------
\subsection{Simulating Nondeterministic Programs with State}
\label{sec:sim-nondet-state}

To simulate nondeterminism, we use states of type |S a| that is a
essentially a tuple of: \begin{enumerate}
\item
a list of the |results| found so far, and
\item
a list of yet to be explored branches, which we call a |stack|.
\end{enumerate}
The branches in the stack are represented by computations in the form
of free monads over the |StateF| signature.
%
The type |S a| is formally defined as follows:
\begin{code}
type Comp s a = Free (StateF s) a
data S a = S { results :: [a], stack :: [Comp (S a) ()]}
\end{code}
%
% To simulate a nondeterministic computation |Free NondetF a| with this
% state wrapper,
We define three auxiliary functions in \Cref{fig:pop-push-append} to
interact with the stack:
\begin{itemize}
\item
The function |popS| removes and executes the top element of the stack.
\item
The function |pushS| pushes a branch into the stack.
\item
The function |appendS| adds a result to the given results.
\end{itemize}

\noindent
\begin{figure}[t]
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popS :: Comp (S a) ()
popS = do
  S xs stack <- get
  case stack of
    []       -> return ()
    p : ps   -> do
      put (S xs ps); p
\end{code}
\caption{Popping from the stack.}
\label{fig:pop}
\end{subfigure}
%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushS   ::  Comp (S a) ()
        ->  Comp (S a) ()
        ->  Comp (S a) ()
pushS q p = do
  S xs stack <- get
  put (S xs (q : stack))
  p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push}
\end{subfigure}
%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
appendS  ::  a
         ->  Comp (S a) ()
         ->  Comp (S a) ()
appendS x p = do
  S xs stack <- get
  put (S (xs ++ [x]) stack)
  p
\end{code}
\caption{Appending a result.}
\label{fig:append}
\end{subfigure}%
\caption{Auxiliary functions |popS|, |pushS| and |appendS|.}
\label{fig:pop-push-append}
\end{figure}

% TOM: The following have already been defined earlier in section 3, named get and put without the S
% Furthermore, we define smart constructors |getS| and |putS s| for getting
% the current state and putting a new state.
% WT: Yes, this is also true for |getSS| and |putSS|. We should deprecate them.
%if False
% \begin{minipage}[t][][t]{0.5\textwidth}
% \begin{code}
% get :: Comp s s
% get = Op (Get return)
% \end{code}
% \end{minipage}
% \begin{minipage}[t][][t]{0.5\textwidth}
% \begin{code}
% put :: s -> Comp s ()
% put s = Op (Put s (return ()))
% \end{code}
% \end{minipage}
%endif

Now, everything is in place to define a simulation function
|nondet2stateS| that interprets nondeterministic programs
represented by the free monad |Free NondetF a| as state-wrapped
programs represented by the free monad |Free (StateF (S a)) ()|.
% (i.e., |Comp (S a) ()|).
\begin{code}
nondet2stateS :: Free NondetF a -> Free (StateF (S a)) ()
nondet2stateS = fold gen alg
  where
    gen x         = appendS x popS
    alg Fail      = popS
    alg (Or p q)  = pushS q p
\end{code}
The generator of this handler records a new result and then pops the
next branch from the stack and proceeds with it. Likewise, for failure
the handler simply pops and proceeds with the next branch. For
nondeterministic choices, the handler pushes the second branch on the
stack and proceeds with the first branch.

To extract the final result from the |S| wrapper, we define the |extractS| function.
\begin{code}
extractS :: State (S a) () -> [a]
extractS x = results . snd $ runState x (S [] [])
\end{code}
Finally, we define the function |runND| which wraps everything up to
handle a nondeterministic computation to a list of results.
%
It uses the state handler |hState'| in
\Cref{sec:free-monads-and-their-folds}.
\begin{code}
runND :: Free NondetF a -> [a]
runND = extractS . hState' . nondet2stateS
\end{code}

We have the following theorem showing the correctness of the
simulation via the equivalence of the |runND| function
and the nondeterminism handler |hND| defined in
\Cref{sec:free-monads-and-their-folds}.

\begin{restatable}[]{theorem}{nondetStateS}
\label{thm:nondet2stateS}
< runND = hND
\end{restatable}

The proof can be found in \Cref{app:runnd-hnd}.
%
The main idea is again to use fold fusion and the universal property
of folds.
%
Consider the expanded form
< (extractS . hState') . nondet2stateS = hND
As both |nondet2stateS| and |hND| are folds, we fuse the left-hand
side into a single fold with \Cref{eq:fusion-post} and then show the
two folds on both sides are equivalent by proving the equivalence of
their generators and algebras.
%
For the latter we only need to prove the following two equations:
\begin{enumerate}
    \item |(extractS . hState') . gen = genND|
    \item |(extractS . hState') . alg = algND . fmap (extractS . hState')|
\end{enumerate}
where |gen| and |alg| are from the definition of |nondet2stateS|, and
|genND| and |algND| are from the definition of |hND|.

%-------------------------------------------------------------------------------
\subsection{Combining the Simulation with Other Effects}
\label{sec:combining-the-simulation-with-other-effects}
\label{sec:nondet2state}

The |nondet2stateS| function only considers nondeterminism as the only
effect. In this section, we generalise it to work in combination with
other effects. One immediate benefit is that we can use it in
together with our previous simulation |local2global| in
\Cref{sec:local2global}.
% \emph{modularity} has an impact on several definitions, as well as
% on the implementation and proof.

Firstly, we need to augment the signature in the computation type with
an additional functor |f| for other effects.
%
The computation type essentially changes from |Free (StateF s) a| to
|Free (StateF s :+: f) a|.
%
We define the state type |SS f a| as follows:
\begin{code}
type CompSS s f a = Free (StateF s :+: f) a
data SS f a = SS { resultsSS :: [a], stackSS :: [CompSS (SS f a) f ()] }
\end{code}

Similarly, we define three auxiliary functions the helper functions
|popSS|, |pushSS| and |appendSS| in \Cref{fig:pop-push-append-SS} to
interact with the stack. They are almost the same as those in
\Cref{fig:pop-push-append} but adapted to the new state-wrapper type
|SS f a|.

% \begin{minipage}[t][][t]{0.5\textwidth}
% \begin{code}
% get :: Functor f => CompSS s f s
% get = Op (Inl (Get return))
% \end{code}
% \end{minipage}
% \begin{minipage}[t][][t]{0.5\textwidth}
% \begin{code}
% put :: Functor f => s -> CompSS s f ()
% put s = Op (Inl (Put s (return ())))
% \end{code}
% \end{minipage}
% \begin{code}
% instance Functor f => MState s (Free (StateF s :+: f)) where
%   get    = Op (Inl (Get return))
%   put s  = Op (Inl (Put s (return ())))
% \end{code}

\noindent
\begin{figure}[h]
\noindent
\small
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
popSS  :: Functor f
  => CompSS (SS f a) f ()
popSS = do
  SS xs stack <- get
  case stack of
    []       -> return ()
    p : ps   -> do
      put (SS xs ps); p
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
  SS xs stack <- get
  put (SS xs (q : stack))
  p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push-ss}
\end{subfigure}
\begin{subfigure}[t]{0.35\linewidth}
\begin{code}
appendSS  :: Functor f
  => a
  -> CompSS (SS f a) f ()
  -> CompSS (SS f a) f ()
appendSS x p = do
  SS xs stack <- get
  put (SS (xs ++ [x]) stack)
  p
\end{code}
\caption{Appending a result.}
\label{fig:append-ss}
\end{subfigure}%
\caption{Auxiliary functions |popSS|, |pushSS| and |appendSS|.}
\label{fig:pop-push-append-SS}
\end{figure}


The simulation function |nondet2state| is also very similar to
|nondet2stateS| except for requiring a forwarding algebra |fwd| to
deal with the additional effects in |f|.

% nondet2state  :: Functor f => Free (NondetF :+: f) a -> CompSS (SS f a) f ()
\begin{code}
nondet2state  :: Functor f => Free (NondetF :+: f) a -> Free (StateF (SS f a) :+: f) ()
nondet2state = fold gen (alg # fwd)
  where
    gen x         = appendSS x popSS
    alg Fail      = popSS
    alg (Or p q)  = pushSS q p
    fwd y         = Op (Inr y)
\end{code}

The function |runNDf| puts everything together: it translates the
nondeterminism effect into the state effect and forwards other
effects, handles the state effect, and extracts the results from the
final state.
%
\begin{code}
runNDf :: Functor f => Free (NondetF :+: f) a -> Free f [a]
runNDf = extractSS . hState . nondet2state
extractSS :: Functor f => StateT (SS f a) (Free f) () -> Free f [a]
extractSS x = resultsSS .  snd <$> runStateT x (SS [] [])
\end{code}

% We can again show that this modular |runNDf| function is equivalent to the
% modular nondeterminism handler |hNDf| defined in \ref{sec:combining-effects}.
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

We have the following theorem showing that the simulation |runNDf| is
equivalent to the modular nondeterminism handler |hNDf| in
\Cref{sec:combining-effects}.

\begin{restatable}[]{theorem}{nondetState}
\label{thm:nondet-state}
< runNDf = hNDf
\end{restatable}

The proof proceeds essentially in the same way as in the non-modular
setting.  The main difference, due to the modularity, is an additional
proof case for the forwarding algebra.
\begin{equation*}
|(extractSS . hState) . fwd = fwdNDf . fmap (extractSS . hState)|
\end{equation*}
The full proof can be found in \Cref{app:in-combination-with-other-effects}.

%-------------------------------------------------------------------------------
%if False
\subsection{Using State to Simulate Nondeterminism in N-queens}

\begin{code}
queensState   :: Int -> [[Int]]
queensState   = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . runNDf . comm2
              . local2global . queens
\end{code}

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
-- global
queensState0  :: Int -> [[Int]]
queensState0  = hNil
              . fmap fst . flip runStateT (0, []) . hState
              . (extractSS . hState . nondet2state) . comm2
              . local2global . queens

-- local
queensState'  :: Int -> [[Int]]
queensState'  = hNil
              . (extractSS . hState . nondet2state)
              . fmap fst . flip runStateT (0, []) . hState
              . queens

-- global !
queensState'' :: Int -> [[Int]]
queensState'' = hNil
              . extractSS' . hState
              . fmap fst . flip runStateT (0, []) . hState
              . comm2 . nondet2state . comm2
              . local2global . queens
    where
              extractSS' x = resultsSS . snd <$> runStateT x (SS [] [])
\end{code}
% Similarly, we can develop a version of |queensStateR| based on |queensModify|,
% which uses the undo semantics.
% \begin{code}
% queensStateR  :: Int -> [[Int]]
% queensStateR  = hNil
%               . fmap fst . flip runStateT (0, []) . hState
%               . (extractSS . hState . nondet2state) . comm2
%               . modify2global . queensR
% \end{code}
% \birthe{Don't know what this sentence says.}
% It also has two simulations, except that the simulation of local state with global state is implemented manually with the |modifyR| in |queensR|.
%endif
