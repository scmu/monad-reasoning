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
import Control.Monad (ap, join)
import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans (lift)

\end{code}
%endif

Intro. Refer to WAM. 

%-------------------------------------------------------------------------------
\subsection{Interpreting Nondeterministic Programs with List}

The |List| monad, which is used in Haskell to implement nondeterminism, is a lawful instance of |MNondet|.
Indeed, all nondeterminism laws of \cref{sec:nondeterminism} are satisfied by
this implementation.
The return |etal| of the |List| monad is a singleton list 
and the join operation |mul| is concatenation or flattening.

< instance Monad [] where
<   return x   = [x]
<   m >>= f    = [y | x <- xs, y <- f x]

We can interpret these nondeterministic programs encoded in lists 
by means of the |choose| function, which can be implemented as a fold.
%if False
\begin{code}
etam :: MNondet m => a -> m a
etam = return
\end{code}
%endif
\begin{code}
choose :: MNondet m => [a] -> m a
choose = foldr (mplus . etam) mzero
\end{code}

\todo{include Willem's graphical example?}

In fact, the |List| monad is not just an instance for nondeterminism; 
it is the initial lawful instance. 
This means that, for every other lawful instance of nondeterminism, there is a
unique monad morphism from |List| to that instance.
The above definition of |choose| is exactly that monad morphism.
Indeed, for every nondeterminism monad |m| (|MNondet m|), we have that
\begin{align*}
  |choose . etal| &= |etam|\\
  |choose . mul| &= |mum . choose . fmap choose|\\
                 &= |mum . fmap choose . choose|
\end{align*}

\[\begin{tikzcd}
    {[a]} && {m\,a} && {[[a]]} &&&& {m\,(m\, a)} \\
    \\
    & a & && {[a]} &&&& {m\,a}
    \arrow["{\mu_{[]}}", from=1-5, to=3-5]
    \arrow["{|choose . fmap choose|}", from=1-5, to=1-9]
    \arrow["{|fmap choose . choose|}"', draw=none, from=1-5, to=1-9]
    \arrow["{\mu_m}", from=1-9, to=3-9]
    \arrow["{|choose|}"', from=3-5, to=3-9]
    \arrow["{|choose|}", from=1-1, to=1-3]
    \arrow["{\eta_m}"', from=3-2, to=1-3]
    \arrow["{\eta_{[]}}", from=3-2, to=1-1]
\end{tikzcd}\]

\todo{equational reasoning? here or in appendices?}

To prove that this morphism is unique, we use the universality of fold, which
is stated for lists as follows:
\begin{align*}
|g []| &= |v| &  & \\
& &\Longleftrightarrow \hspace{10ex} |g| &= |fold f v| \\
|g (x:xs)| &= |f x (g xs)| & & 
\end{align*}


%-------------------------------------------------------------------------------
\subsection{Simulating Nondeterministic Programs with State}
\label{sec:sim-nondet-state}

This section shows how to use a state-based implementation to simulate nondeterminism.

\todo{is |\s -> (s, a)| the initial state instance?}

For this, we use a wrapper |ST| around |State| that uses as state a tuple with 
(1) the current solution(s) |m a| wrapped in a monad and 
(2) the branches to be evaluated, which we will call the \emph{stack}.
The return type of |State| is a unit |()|.
\begin{code}
newtype ST m a = ST { runST :: State (m a, [ST m a]) () }
\end{code}
To simulate a nondeterministic computation |NondetC| with this state wrapper, 
we define a few helper functions.
The function |pop| takes the upper element of the stack.
\begin{code}
pop :: MNondet m => ST m a 
pop = ST $ do 
    (xs, stack) <- get
    case stack of 
        []           ->  return ()
        ST p : ps  ->  do put (xs, ps) ; p
\end{code}
The function |push| adds a branch to the stack.
\begin{code}
push :: MNondet m => ST m a -> ST m a -> ST m a
push q p = ST $ do
    (x, stack) <- get
    put (x, q:stack)
    runST p
\end{code}
The function |append| adds a solution to the given solutions. 
\begin{code}
append :: MNondet m => a -> ST m a -> ST m a
append x p = ST $ do
    (xs, stack) <- get
    put (xs `mplus` return x, stack)
    runST p
\end{code}
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

% \todo{Monadic computation with continuation monad to avoid |NondetC| data type.
% To add or not to add?}
% \begin{code}
% newtype STCont m a b = STCont {runCont :: (b -> ST m a) -> ST m a} 
%     deriving (Functor)

% instance Applicative (STCont m a) where
%     pure   = return 
%     (<*>)  = ap

% instance Monad (STCont m a) where
%     return x  = STCont (\k -> k x)
%     m >>= f   = STCont (\k -> runCont m (\x -> runCont (f x) k))

% instance MNondet m => MNondet (STCont m a) where
%     mzero      = STCont (\k -> pop)
%     mplus p q  = STCont (\k -> push (runCont p k) (runCont q k))

% runNondetC :: MNondet m => STCont m a a -> m a
% runNondetC = fst . snd . ($ (mzero, [])) . runState . runST . flip runCont (\x -> append x pop)

% \end{code}


%-------------------------------------------------------------------------------
\subsection{Proof of correctness}
\todo{here or in appendices?}

This section shows that the |runNondet| function, defined above, is equivalent
to a nondeterminism handler.
For that, we zoom in on a version of the nondeterminism handler of 
Section \ref{sec:combining-effects}
with no other effects (|f = NilF|). We replace the |List| monad by any other 
nondeterminism monad |m|.
The type signature now changes from
|hNondet :: MNondet m => Free (NondetF :+: NilF) a -> Free NilF (m a)|
to 
|hNondet :: MNondet m => NondetC a -> m a|
\begin{code}
hNondet :: MNondet m => NondetC a -> m a
hNondet = fold genND algND
  where 
    genND           = return 
    algND Fail      = mzero
    algND (Or p q)  = p `mplus` q
\end{code}
We can now show that this handler is equal to the |runNondet| function
of Section \ref{sec:sim-nondet-state}.
\begin{theorem}
|runNondet = hNondet|
\end{theorem}
\begin{proof}
We start with expanding the definition of |runNondet|:
< extract . simulate = hNondet
Both |simulate| and |hNondet| are written as a fold.
We can use the universal property of fold to show that |runNondet| and
|hNondet| are equal.
Therefore, we will use the fold fusion law for postcomposition as defined in 
Equation \ref{eq:fusion-post}.
We have to prove that
\begin{enumerate}
    \item |extract . gen = genND|
    \item |extract . alg = algND . fmap extract|
\end{enumerate}
The first item is simple to prove with equational reasoning.
<    extract (gen x)
< = {-~  definition of |gen|  -}
<    extract (append x pop)
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runST (append x pop)) (mzero, [])
< = {-~  evaluation of |append|  -}
<    fst . snd $ runState (runST pop) (mzero `mplus` return x, [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd $ runState (runST pop) (return x, [])
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst . snd $ ((), (return x, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    return x
< = {-~  definition of |genND|  -}
<    genND x
The property that |extract . gen = return| is called 
\emph{extract-gen}\label{eq:extract-gen}.
For the second item that we have to prove, we do a case analysis.

\fbox{|Fail|}

<    extract (alg Fail)
< = {-~  definition of |alg|  -}
<    extract pop
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runST pop) (mzero, [])
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst . snd $ ((), (mzero, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    mzero
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) Fail
The property that |extract (alg Fail) = mzero| is called 
\emph{extract-alg-1}\label{eq:extract-alg-1}.

\fbox{|Or p q|}

<    extract (alg (Or p q))
< = {-~  definition of |alg|  -}
<    extract (push q p)
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runST (push q p)) (mzero, [])
< = {-~  evaluation of |push q p|  -}
<    fst . snd $ runState (runST p) (mzero, [q])
< = {-~  property of |ST|  -}
<    fst . snd $ runState (runST pop) (mzero `mplus` extract p, [q])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd $ runState (runST pop) (extract p, [q])
< = {-~  evaluation of |pop|  -}
<    fst . snd $ runState (runST q) (extract p, [])
< = {-~  property of |ST|  -}
<    fst . snd $ runState (runST pop) (extract p `mplus` extract q, [])
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst . snd $ ((), (extract p `mplus` extract q, []))
< = {-~  evaluation of |fst|, |snd|.  -}
<    extract p `mplus` extract q
< = {-~  definition of |algND|  -}
<    algND (Or (extract p) (extract q))
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) (Or p q)
The property that |extract (alg (Or p q)) = extract p `mplus` extract q| 
is called \emph{extract-alg-2}\label{eq:extract-alg-2}.
\end{proof}

In this proof we have used the property of |ST m a| stating the following: 
\begin{theorem}[pop-extract]
<    runState  (runST p)    (q, stack) 
< =  runState  (runST pop)  (q `mplus` extract p, stack)
\end{theorem}
We call this property the pop-extract property.
The key element to have this property is to 
only utilize a subset of terms with type |ST m a|, namely those
that are generated by the fold of the |simulate| function,
so for which this property is true.
Indeed, we only generate such terms.
To prove this, we need to show that 
(1) the generator of |simulate| only generates programs of this subset;
and (2) the algebra preserves this property.

\begin{theorem}[pop-extract part 1]
<      runState  (runST (gen x))   (q, stack) 
< =    runState  (runST pop)       (q `mplus` extract (gen x), stack)
\end{theorem}
We use equational reasoning to prove this theorem.
\begin{proof}
<    runState (runST (gen x)) (q, stack)
< = {-~  definition of |gen|  -}
<    runState (runST (append x pop)) (q, stack)
< = {-~  evaluation of |append|  -}
<    runState (runST pop) (q `mplus` return x, stack)
< = {-~  property extract-gen (\ref{eq:extract-gen})  -}
<    runState (runST pop) (q `mplus` extract (gen x), stack)
\end{proof}

\begin{theorem}[pop-extract part 2]
<     runState  (runST (alg x))  (q, stack) 
< =   runState  (runST pop)      (q `mplus` extract (alg x), stack)
\end{theorem}
\begin{proof}
We use equational reasoning with case analysis on |x|.

\fbox{|Fail|}

<    runState (runST (alg Fail)) (q, stack)
< = {-~  definition of |alg|  -}
<    runState (runST pop) (q, stack)
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    runState (runST pop) (q `mplus` mzero, stack)
< = {-~  property extract-alg-1 (\ref{eq:extract-alg-1})  -}
<    runState (runST pop) (q `mplus` extract (alg Fail), stack)

\fbox{|Or p1 p2|}
Assume that |p1| and |p2| satisfy this theorem.

<    runState (runST (alg (Or p1 p2))) (q, stack)
< = {-~  definition of |alg|  -}
<    runState (runST (push p2 p1)) (q, stack)
< = {-~  evaluation of |push p2 p1|  -}
<    runState (runST p1) (q, p2:stack)
< = {-~  recursion: property of |p1|  -}
<    runState (runST pop) (q `mplus` extract p1, p2:stack)
< = {-~  evaluation of |pop|  -}
<    runState (runST p2) (q `mplus` extract p1, stack)
< = {-~  recursion: property of |p2|  -}
<    runState (runST pop) (q `mplus` extract p1 `mplus` extract p2, stack)
< = {-~  property extract-alg-1 (\ref{eq:extract-alg-1})  -}
<    runState (runST pop) (q `mplus` extract (alg (Or p1 p2)), stack)
Note that the above two proofs are mutually recursive \todo{}
\end{proof}

%-------------------------------------------------------------------------------
\subsection{Combining the Simulation with Other Effects}
We can generalize this simulation to work with arbitrary other effects.
These effects are represented by the |sig| monad.
Again, we define a type that encapsulates a form of state. 
< newtype ST' sig m a = ST' { unST :: StateT (m a, [ST' sig m a]) sig () }
%if False
\begin{code}
newtype ST' sig m a = ST' { unST :: S.StateT (m a, [ST' sig m a]) sig () }
\end{code}
%endif
This time we use the state transformer |StateT|, as defined in the State library
\ref{}.
< newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }
Thus, the state is |ST'| is again represented by a pair of 
a value a encapsulated in a nondeterminism monad |m a| and
a stack of |ST' sig m a| computations or branches to be evaluated.

We can redefine the |simulate| function as follows:
\begin{code}
simulate' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> ST' (Free f) m a
simulate' = fold gen' alg'
  where
    gen' x = append' x pop'
    alg' (Inl Fail) = pop'
    alg' (Inl (Or p q)) = push' p q
    alg' (Inr y) = ST' $ join $ lift $ Op (return . unST <$> y)
\end{code}
This function is very similar to the |simulate| function 
of Section \ref{sec:sim-nodet-state}, which now interprets every nondeterministic
program as a state-wrapped computation, leaving other effects alone.
The helper functions |pop'|, |push'| and |append'| are very much like the
previous definitions, but adapted to the new state-wrapper type.

< pop' :: Monad sig => ST' sig m a 
< pop' = ST' $ do 
<    (xs, stack) <- get
<    case stack of 
<        []          ->  return ()
<        ST' p : ps  ->  do put (xs, ps) ; p
<
< push' :: Monad sig => ST' sig m a -> ST' sig m a -> ST' sig m a
< push' q p = ST' $ do
<     (xs, stack) <- get
<     put (xs, q:stack)
<     unST p
<
< append' :: (Monad sig, MNondet m) => a -> ST' sig m a -> ST' sig m a
< append' x p = ST' $ do
<     (xs, stack) <- get
<     put (xs `mplus` return x, stack)
<     unST p

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
The other effects |f| are to be dealth with by the appropriate handlers.
\begin{code}
runNondet' :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
runNondet' = extract' . simulate'
\end{code}

%-------------------------------------------------------------------------------
\subsection{Proof of correctness}
\todo{Proposal: put this proof in appendices and refer to it, also
for the regular simulation, which is a special instance of this.}

This section shows that |runNondet'| is equivalent to a nondeterminism handler.
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
We prove that this handler |hNondet'| is equal to the |runNondet'| function
defined above.
\begin{theorem}
|runNondet' = hNondet'|
\end{theorem}
As before, we first expand the definition of |runNondet'|, 
which is written in terms of |simulate'|, a fold. 
We use fold fusion to incorporate |extract'| in the fold of |simulate'|.
The universal property of fold then teaches us that |runNondet'| and
|hNondet'| are equal.
More concretely, we have to prove the following two things:
\begin{enumerate}
    \item |extract' . gen' = genND'|
    \item |extract' . alg' = algND' . fmap extract'|
\end{enumerate}
\begin{proof}
For the first item we use simple equational reasoning techniques.
<    extract' (gen' x)
< = {-~  definition of |gen'|  -}
<    extract' (append' x pop')
< = {-~  definition of |extract'|  -}
<    fst . snd <$> runStateT (unST (append' x pop')) (mzero, [])
< = {-~  evaluation of |append'|  -}
<    fst . snd <$> runStateT (unST pop') (mzero `mplus` return x, [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (unST pop') (return x, [])
< = {-~  evaluation of |unST pop'|, |runStateT|  -}
<    fst . snd <$> Var ((), (return x, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (return x)
< = {-~  definition of |genND'|  -}
<    genND' x

For the second item that we have to prove, we do a case analysis.

\fbox{|Inl Fail|}

<    extract' (alg' (Inl Fail))
< = {-~  definition of |alg'|  -}
<    extract' pop'
< = {-~  definition of |extract'|  -}
<    fst . snd <$> runStateT (unST pop') (mzero, [])
< = {-~  evaluation of |unST pop'|, |runStateT|  -}
<    fst . snd <$> Var ((), (mzero, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var mzero
< = {-~  definition of |algND'|  -}
<    algND' (Inl Fail)
< = {-~  definition of |fmap|  -}
<    (algND' . fmap extract') (Inl Fail)

\fbox{|Inl (Or p q)|}

<    extract' (alg' (Inl (Or p q)))
< = {-~  definition of |alg'|  -}
<    extract' (push' q p)
< = {-~  definition of |extract'|  -}
<    fst . snd <$> runStateT (unST (push' q p)) (mzero, [])
< = {-~  evaluation of |push' q p|  -}
<    fst . snd <$> runStateT (unST p) (mzero, [q])
< = {-~  property of |ST'|  -}
<    fst . snd <$> runStateT (unST pop') (mzero `mplus` extract' p, [q])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (unST pop') (extract' p, [q])
< = {-~  evaluation of |pop'|  -}
<    fst . snd <$> runStateT (unST q) (extract' p, []) 
< = {-~  property of |ST'|  -}
<    fst . snd <$> runStateT (unST pop') (extract' p `mplus` extract' q, []) 
< = {-~  evaluation of |unST pop'|, |runStateT|  -}
<    fst . snd <$> Var ((), (extract' p `mplus` extract' q, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (extract' p `mplus` extract' q)
< = {-~  definition of |liftA2|  -}
<    mplus <$> extract' p <*> extract' q
< = {-~  definition of |algND'|  -}
<    algND' (Inl (Or (extract' p) (extract' q)))
< = {-~  definition of |fmap|  -}
<    (algND' . fmap extract') (Inl (Or p q))

\fbox{|Inr y|}

<    extract' (alg' (Inr y))
< = {-~  definition of |alg'|  -}
<    extract' (ST' $ join $ lift $ Op (return . unST <$> y))
< = {-~  definition of |extract'|  -}
<    fst . snd <$> runStateT (unST (ST' $ join $ lift $ Op (return . unST <$> y))) (mzero, [])
< = {-~  property of |ST'|  -}
<    fst . snd <$> runStateT (unST pop') (mzero `mplus` extract' (ST' $ join $ lift $ Op (return . unST <$> y)), [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (unST pop') (extract' (ST' $ join $ lift $ Op (return . unST <$> y)), [])
< = {-~  evaluation of |unST pop'|, |runStateT|  -}
<    fst . snd <$> Var ((), (extract' (ST' $ join $ lift $ Op (return . unST <$> y)), []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (extract' (ST' $ join $ lift $ Op (return . unST <$> y)))
\todo{stuck}
<    Op (extract' y)
< = {-~  definition of |algND'|  -}
<    algND' (Inr (extract' y))
< = {-~  definition of |fmap|  -}
<    (algND' . fmap extract') (Inr y)
\end{proof}













