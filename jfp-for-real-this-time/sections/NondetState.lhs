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
import Control.Monad (ap, join, liftM)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT, state)
import Control.Monad.Trans (lift)

\end{code}
%endif

Two of the most well-known and well-investigated side-effects are nondeterminism
and state. 
Typically, nondeterminism is modelled using a |List| monad.
However, many efficient nondeterministic systems, such as Prolog, 
use a state-based implementation to simulate this effect.
This section shows how this simulation works, and proves it correct using 
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

\wenhao{ I have changed this section to the same style of Section 3.3, i.e. using a syntax-level simulation like |nondet2stateS :: MNondet m => Free NondetF a -> Free (StateF (S m a)) ()|.
I was wondering whether this section is needed.
I think it is ok to directly give the simulation with other effects.
It is what we do in Section 4, where we also only give a simulation |local2global| with other effects.}

This section shows how to use a state-based implementation to simulate nondeterminism.

For this, we use a type |S| that uses as a tuple with 
(1) the current solution(s) |m a| wrapped in a monad and 
(2) the branches to be evaluated, which we will call the \emph{stack}.
The braches in the stack are represented by the free monad of state.
\begin{code}
newtype S m a = S { runS :: (m a, [Free (StateF (S m a)) ()]) }
\end{code}
To simulate a nondeterministic computation |Free NondetF a| with this state wrapper, 
we define a helper functions in Figure \ref{fig:pop-push-append}.
The function |popS| takes the upper element of the stack.
The function |pushS| adds a branch to the stack.
The function |appendS| adds a solution to the given solutions. 
Furthermore, we define smart constructors |getS| and |putS s| for getting 
the state and putting a new state.
\begin{code}
getS :: Free (StateF s) s
getS = Op (Get return)

putS :: s -> Free (StateF s) ()
putS s = Op (Put s (return ()))
\end{code} 

\noindent
\begin{figure}[h]
\small
\begin{subfigure}[t]{0.33\linewidth}
\begin{code}
popS  :: Free (StateF (S m a)) ()
popS = do
  S (xs, stack) <- getS
  case stack of
    []       -> return ()
    op : ps  -> do
      putS (S (xs, ps)); op
\end{code}
\caption{Popping from the stack.}
\label{fig:pop}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
pushS   :: Free (StateF (S m a)) ()
        -> Free (StateF (S m a)) ()
        -> Free (StateF (S m a)) ()
pushS q p = do
  S (xs, stack) <- getS
  putS (S (xs, q : stack)); p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push}
\end{subfigure}%
\begin{subfigure}[t]{0.3\linewidth}
\begin{code}
appendS   :: (MNondet m) => a
          -> Free (StateF (S m a)) ()
          -> Free (StateF (S m a)) ()
appendS x p = do
 S (xs, stack) <- getS
 putS (S (xs `mplus` return x, stack)); p
\end{code}
\caption{Appending a solution.}
\label{fig:append}
\end{subfigure}%
\label{fig:pop-push-append}
\caption{Helper functions |popS|, |pushS| and |appendS|.}
\end{figure}
Now everything is in place to define a simulation function |simulate| that
interprets every nondeterministic computation as a state-wrapped program.
\begin{code}
nondet2stateS :: MNondet m => Free NondetF a -> Free (StateF (S m a)) ()
nondet2stateS = fold gen alg
  where
    gen x         = appendS x popS
    alg Fail      = popS
    alg (Or p q)  = pushS q p
\end{code}
To extract the final result from the |S| wrapper, we define the |extractS| function.
\begin{code}
extractS :: MNondet m => State (S m a) () -> m a
extractS x = fst . runS <$> snd $ runState x (S (mzero, []))
\end{code}
This way, |runND| is a trivial extension of 
the simulate function. It transforms
every nondeterministic computation to a result that is encapsulated in a
nondeterminism monad.
\begin{code}
runND :: MNondet m => Free NondetF a -> m a
runND = extractS . hState' . nondet2stateS
\end{code}

To prove that this simulation is correct, we should show that this 
|runND| function is equivalent to a nondeterminism handler. 
For that, we zoom in on a version of such a handler 
(Section \ref{sec:combining-effects}) with no other effects
(|f = NilF|). 
We replace the |List| monad by any other nondeterminism monad |m|.
% Consequently, the type signature for the handler changes from 
% |hND :: MNondet m => Free (NondetF :+: NilF) a -> Free NilF (m a)|
% to 
% |hND :: MNondet m => Free NondetF a -> m a|.
This leaves us with the following implementation for the handler.
\begin{code}
hND :: MNondet m => Free NondetF a -> m a
hND = fold genND algND
  where 
    genND           = return 
    algND Fail      = mzero
    algND (Or p q)  = p `mplus` q
\end{code}
We can now show that this handler is equal to the |runND| function defined 
above.
\begin{theorem}
|runND = hND|
\end{theorem}
The proof of this theorem is added in Appendix \ref{app:runnd-hnd}. 
\todo{adapt the proof to the new function definition.}

\subsection{Combining the Simulation with Other Effects}
\label{sec:combining-the-simulation-with-other-effects}

We can generalize this simulation to work with arbitrary other effects. 
Again, we define a type |SS| that encapsulates a form of state.
\begin{code}
newtype SS m a f = SS { unSS :: (m a, [Free (StateF (SS m a f) :+: f) ()]) }
\end{code}

Thus, the state type |SS| is again represented by a pair of 
a value encapsulated in a nondeterminism monad, |m a|, and
a stack of computations or branches to be evaluated.

We can define a simulation function as follows:

\begin{code}
nondet2state  :: (Functor f, MNondet m)
              => Free (NondetF :+: f) a
              -> Free (StateF (SS m a f) :+: f) ()
nondet2state = fold gen (alg # fwd)
  where
    gen x         = appendSS x popSS
    alg Fail      = popSS
    alg (Or p q)  = pushSS q p
    fwd y         = Op (Inr y)
\end{code}

The helper functions |popSS|, |pushSS| and |appendSS| 
(Figure \ref{fig:pop-push-append-SS}) are very much like the
previous definitions, but adapted to the new state-wrapper type.
Furtermore, |getSS| and |putSS s| are smart constructors for getting 
the stating and putting a new state.
\begin{code}
getSS :: Functor f => Free (StateF s :+: f) s
getSS = Op (Inl $ Get return)

putSS :: Functor f => s -> Free (StateF s :+: f) ()
putSS s = Op (Inl $ Put s (return ()))
\end{code}

\begin{figure}[h]
\small
\begin{subfigure}[t]{0.5\linewidth}
\begin{code}
popSS  :: Functor f 
       => Free (StateF (SS m a f) :+: f) ()
popSS = do
  SS (xs, stack) <- getSS
  case stack of
    []       -> return ()
    op : ps  -> do
      putSS (SS (xs, ps)); op
\end{code}
\caption{Popping from the stack.}
\label{fig:pop-ss}
\end{subfigure}%
\begin{subfigure}[t]{0.5\linewidth}
\begin{code}
pushSS  :: Functor f
        => Free (StateF (SS m a f) :+: f) ()
        -> Free (StateF (SS m a f) :+: f) ()
        -> Free (StateF (SS m a f) :+: f) ()
pushSS q p = do
  SS (xs, stack) <- getSS
  putSS (SS (xs, q : stack)); p
\end{code}
\caption{Pushing to the stack.}
\label{fig:push-ss}
\end{subfigure}
\begin{subfigure}[t]{0.5\linewidth}
\begin{code}
appendSS  :: (Functor f, MNondet m) => a
          -> Free (StateF (SS m a f) :+: f) () 
          -> Free (StateF (SS m a f) :+: f) ()
appendSS x p = do
 SS (xs, stack) <- getSS
 putSS (SS (xs `mplus` return x, stack)); p
\end{code}
\caption{Appending a solution.}
\label{fig:append-ss}
\end{subfigure}%
\label{fig:pop-push-append-SS}
\caption{Helper functions |popSS|, |pushSS| and |appendSS|.}
\end{figure}

To extract the final result from the |SS| wrapper, we define an |extractState| 
function.
\begin{code}
extractState :: (Functor f, MNondet m) => StateT (SS m a f) (Free f) () -> Free f (m a)
extractState x = fst . unSS . snd <$> runStateT x (SS (mzero, []))
\end{code}

Finally, |runNDf| is again a trivial extension of the simulation.
It transforms every monad with nondeterminism and other effects |f| into
a free monad where the result is wrapped in the nondeterminism monad. 
The other effects |f| are to be dealt with by the appropriate handlers.
\begin{code}
runNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
runNDf = extractState . hState . nondet2state
\end{code}

To prove this approach correct, we should show that this |runNDf| function
is equal to a nondeterminism handler.
For that, we compare with a version of the handler defined in Section
\ref{sec:combining-effects}, with the |List| monad replaced by any other
nondeterminism monad |m|.
\begin{code}
hNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
hNDf = fold genNDf (algNDf # Op)
  where 
    genNDf           = Var . return 
    algNDf Fail      = Var mzero
    algNDf (Or p q)  = mplus <$> p <*> q
\end{code}
We prove that this handler |hNDf| and the |runNDf| function are equal.
\begin{theorem}
|runNDf = hNDf|
\end{theorem}
The proof of this theorem uses equational reasoning and is added in the 
appendices.
\todo{adapt the proof to the new function definition.}

% -------------------------------------------------------------------------
% Old 3.2 and 3.3
% -------------------------------------------------------------------------
% \subsection{Simulating Nondeterministic Programs with State}
% \label{sec:sim-nondet-state}

% This section shows how to use a state-based implementation to simulate nondeterminism.

% For this, we use a wrapper |STND| around |State| that uses as state a tuple with 
% (1) the current solution(s) |m a| wrapped in a monad and 
% (2) the branches to be evaluated, which we will call the \emph{stack}.
% The return type of |State| is a unit |()|.
% \begin{code}
% newtype STND m a = STND { runSTND :: State (m a, [STND m a]) () }
% \end{code}
% To simulate a nondeterministic computation |Free NondetF a| with this state wrapper, 
% we define a helper functions in Figure \ref{fig:pop-push-append}.
% The function |popND| takes the upper element of the stack.
% The function |pushND| adds a branch to the stack.
% The function |appendND| adds a solution to the given solutions. 

% \noindent
% \begin{figure}[h]
% \small
% \begin{subfigure}[t]{0.33\linewidth}
% \begin{code}
% popND  :: MNondet m 
%        => STND m a 
% popND = STND $ do 
%     (xs, stack) <- get
%     case stack of 
%         []         ->  return ()
%         STND p : ps  ->  do 
%             put (xs, ps) ; p
% \end{code}
% \caption{Popping from the stack.}
% \label{fig:pop}
% \end{subfigure}%
% \begin{subfigure}[t]{0.3\linewidth}
% \begin{code}
% pushND  :: MNondet m 
%         => STND m a 
%         -> STND m a 
%         -> STND m a
% pushND q p = STND $ do
%     (x, stack) <- get
%     put (x, q:stack)
%     runSTND p
% \end{code}
% \caption{Pushing to the stack.}
% \label{fig:push}
% \end{subfigure}%
% \begin{subfigure}[t]{0.3\linewidth}
% \begin{code}
% appendND  :: MNondet m 
%           => a 
%           -> STND m a 
%           -> STND m a
% appendND x p = STND $ do
%     (xs, stack) <- get
%     put (xs `mplus` return x, stack)
%     runSTND p
% \end{code}
% \caption{Appending a solution.}
% \label{fig:append}
% \end{subfigure}%
% \label{fig:pop-push-append}
% \caption{Helper functions |popND|, |pushND| and |appendND|.}
% \end{figure}
% Now everything is in place to define a simulation function |simulate| that
% interprets every nondeterministic computation as a state-wrapped program. 
% \begin{code}
% simulate :: MNondet m => Free NondetF a -> STND m a
% simulate = fold gen alg
%   where
%     gen x         = appendND x popND
%     alg :: MNondet m => NondetF (STND m a) -> STND m a
%     alg Fail      = popND
%     alg (Or p q)  = pushND q p
% \end{code}
% To extract the final result from the |STND| wrapper, we define the |extract| function.
% \begin{code}
% extract :: MNondet m => STND m a -> m a
% extract x = fst . snd $ runState (runSTND x) (mzero, [])
% \end{code}
% This way, |runND| is a trivial extension of 
% the simulate function. It transforms
% every nondeterministic computation to a result that is encapsulated in a
% nondeterminism monad.
% \begin{code}
% runND :: MNondet m => Free NondetF a -> m a
% runND = extract . simulate
% \end{code}

% To prove that this simulation is correct, we should show that this 
% |runND| function is equivalent to a nondeterminism handler. 
% For that, we zoom in on a version of such a handler 
% (Section \ref{sec:combining-effects}) with no other effects
% (|f = NilF|). 
% We replace the |List| monad by any other nondeterminism monad |m|.
% Consequently, the type signature for the handler changes from 
% |hND :: MNondet m => Free (NondetF :+: NilF) a -> Free NilF (m a)|
% to 
% |hND :: MNondet m => Free NondetF a -> m a|.
% This leaves us with the following implementation for the handler.
% \begin{code}
% hND :: MNondet m => Free NondetF a -> m a
% hND = fold genND algND
%   where 
%     genND           = return 
%     algND Fail      = mzero
%     algND (Or p q)  = p `mplus` q
% \end{code}
% We can now show that this handler is equal to the |runND| function defined 
% above.
% \begin{theorem}
% |runND = hND|
% \end{theorem}
% The proof of this theorem is added in Appendix \ref{app:runnd-hnd}.

% %-------------------------------------------------------------------------------
% \subsection{Combining the Simulation with Other Effects}
% \label{sec:combining-the-simulation-with-other-effects}
% We can generalize this simulation to work with arbitrary other effects.
% These effects are represented by the |sig| monad.
% Again, we define a type that encapsulates a form of state. 
% < newtype STNDf sig m a = STNDf { runSTNDf :: StateT (m a, [STNDf sig m a]) sig () }
% %if False
% \begin{code}
% newtype STNDf sig m a = STNDf { runSTNDf :: S.StateT (m a, [STNDf sig m a]) sig () }
% \end{code}
% %endif
% This time we use the state transformer |StateT|, as defined in the 
% Monad Transformer Library \ref{}.
% < newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }
% Thus, the state type |STNDf| is again represented by a pair of 
% a value encapsulated in a nondeterminism monad, |m a|, and
% a stack of |STNDf sig m a| computations or branches to be evaluated.

% We can redefine the |simulate| function as follows:

% \begin{code}
% simulate' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> STNDf (Free f) m a
% simulate' = fold gen' (alg' # fwd')
%   where
%     gen'  x        = appendNDf x popNDf
%     alg' Fail      = popNDf
%     alg' (Or p q)  = pushNDf q p
%     fwd' y         = STNDf $ join $ lift $ Op (return . runSTNDf <$> y)
% \end{code}
%     % alg' (Inr y)         = STNDf $ S.StateT $ \s -> Op $ fmap ((\k -> k s) . S.runStateT . runSTNDf) y


% This function is very similar to the |simulate'| function 
% of Section \ref{sec:sim-nodet-state}, which now interprets every nondeterministic
% program as a state-wrapped computation, leaving other effects alone.
% The helper functions |popNDf|, |pushNDf| and |appendNDf| 
% (Figure \ref{fig:pop-push-append-2}) are very much like the
% previous definitions, but adapted to the new state-wrapper type.

% \begin{figure}[h]
% \small
% \begin{subfigure}[t]{0.3\linewidth}
% < popNDf   :: Monad sig 
% <          => STNDf sig m a 
% < popNDf = STNDf $ do 
% <    (xs, stack) <- get
% <    case stack of 
% <        []          ->  return ()
% <        STNDf p : ps  ->  do 
% <               put (xs, ps) ; p
% \caption{Popping from the stack.}
% \label{fig:pop-2}
% \end{subfigure}%
% \begin{subfigure}[t]{0.3\linewidth}
% < pushNDf   :: Monad sig 
% <           => STNDf sig m a 
% <           -> STNDf sig m a 
% <           -> STNDf sig m a
% < pushNDf q p = STNDf $ do
% <     (xs, stack) <- get
% <     put (xs, q:stack)
% <     runSTNDf p
% \caption{Pushing to the stack.}
% \label{fig:push-2}
% \end{subfigure}%
% \begin{subfigure}[t]{0.3\linewidth}
% < appendNDf   :: (Monad sig, MNondet m) 
% <             => a 
% <             -> STNDf sig m a 
% <             -> STNDf sig m a
% < appendNDf x p = STNDf $ do
% <     (xs, stack) <- get
% <     put (xs `mplus` return x, stack)
% <     runSTNDf p
% \caption{Appending a solution.}
% \label{fig:append-2}
% \end{subfigure}%
% \label{fig:pop-push-append-2}
% \caption{Helper functions |popNDf|, |pushNDf| and |appendNDf|.}
% \end{figure}

% To extract the final result from the |STNDf| wrapper, we define an |extractNDf| 
% function.
% < extractNDf :: (Functor f, MNondet m) => STNDf (Free f) m a -> Free f (m a)
% < extractNDf x = fst . snd <$> runStateT (runSTNDf x) (mzero,[])
% %if False
% \begin{code}
% popNDf :: Monad sig => STNDf sig m a 
% popNDf = STNDf $ do 
%     (xs, stack) <- S.get
%     case stack of 
%         []          ->  return ()
%         STNDf p : ps  ->  do S.put (xs, ps) ; p

% pushNDf :: Monad sig => STNDf sig m a -> STNDf sig m a -> STNDf sig m a
% pushNDf q p = STNDf $ do
%     (xs, stack) <- S.get
%     S.put (xs, q:stack)
%     runSTNDf p

% appendNDf :: (Monad sig, MNondet m) => a -> STNDf sig m a -> STNDf sig m a
% appendNDf x p = STNDf $ do
%     (xs, stack) <- S.get
%     S.put (xs `mplus` return x, stack)
%     runSTNDf p

% extractNDf :: (Functor f, MNondet m) => STNDf (Free f) m a -> Free f (m a)
% extractNDf x = fmap (fst . snd) (S.runStateT (runSTNDf x) (mzero,[]))
% \end{code}
% %endif

% Finally, |runNDf| is again a trivial extension of the simulation.
% It transforms every monad with nondeterminism and other effects |f| into
% a free monad where the result is wrapped in the nondeterminism monad. 
% The other effects |f| are to be dealt with by the appropriate handlers.
% \begin{code}
% runNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
% runNDf = extractNDf . simulate'
% \end{code}

% To prove this approach correct, we should show that this |runNDf| function
% is equal to a nondeterminism handler.
% For that, we compare with a version of the handler defined in Section
% \ref{sec:combining-effects}, with the |List| monad replaced by any other
% nondeterminism monad |m|.
% < hNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
% < hNDf = fold genNDf (algNDf # Op)
% <   where 
% <     genNDf = Var . return 
% <     algNDf Fail      = Var mzero
% <     algNDf (Or p q)  = mplus <$> p <*> q
% We prove that this handler |hNDf| and the |runNDf| function are equal.
% \begin{theorem}
% |runNDf = hNDf|
% \end{theorem}
% The proof of this theorem uses equational reasoning and is added in the 
% appendices.

