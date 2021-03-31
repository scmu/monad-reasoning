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

module NondetState where

import Background hiding (hNondet)
import Control.Monad (ap)

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
Indeed, for every nondeterministic monad |m| (|MNondet m|), we have that
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
\label{sec:sim-nodet-state}

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
extract = fst . fst . ($ (mzero, [])) . runState . runST
\end{code}
This way, |runNondet| is a trivial extension of 
the simulate function. It transforms
every nondeterministic computation to a result that is encapsulated in a
nondeterminism monad.
\begin{code}
runNondet :: MNondet m => NondetC a -> m a
runNondet = extract . simulate
\end{code}

\todo{Monadic computation with continuation monad to avoid |NondetC| data type.
To add or not to add?}
\begin{code}
newtype STCont m a b = STCont {runCont :: (b -> ST m a) -> ST m a} 
    deriving (Functor)

instance Applicative (STCont m a) where
    pure   = return 
    (<*>)  = ap

instance Monad (STCont m a) where
    return x  = STCont (\k -> k x)
    m >>= f   = STCont (\k -> runCont m (\x -> runCont (f x) k))

instance MNondet m => MNondet (STCont m a) where
    mzero      = STCont (\k -> pop)
    mplus p q  = STCont (\k -> push (runCont p k) (runCont q k))

runNondetC :: MNondet m => STCont m a a -> m a
runNondetC = fst . fst . ($ (mzero, [])) . runState . runST . flip runCont (\x -> append x pop)

\end{code}


%-------------------------------------------------------------------------------
\subsection{Proof of correctness}

This section shows that the |runNondet| function, defined above, is equivalent
to a nondeterminism handler.
For that, we zoom in on a version of the nondeterminism handler of 
Section \ref{sec:combining-effects}
with no other effects (|f = NilF|). We replace the |List| monad by any other 
nondeterministic monad |m|.
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
We can now show that this handler is equivalent to the |runNondet| function
of Section \ref{sec:sim-nondet-state}.
\todo{define equivalence, |=|}
\begin{theorem}
|runNondet = hNondet|
\end{theorem}
\begin{proof}
We start with expanding the definition of |runNondet|:
< extract . simulate = hNondet
Both |simulate| and |hNondet| are written as a fold.
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
<    (fst . fst . ($ (mzero, [])) . runState . runST) (append x pop)
< = {-~  reformulation  -}
<    fst (fst (runState (runST (append x pop)) (mzero, [])))
< = {-~  evaluation of |append|  -}
<    fst (fst (runState (runST pop) (mzero `mplus` return x, [])))
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst (fst (runState (runST pop) (return x, [])))
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst (fst ((return x, []), ()))
< = {-~  evaluation of |fst|, twice \todo{Name this property *}  -}
<    return x
< = {-~  definition of |genND|  -}
<    genND x
For the second item, we do a case analysis.

\fbox{|Fail|}

<    extract (alg Fail)
< = {-~  definition of |alg|  -}
<    extract pop
< = {-~  definition of |extract|  -}
<    (fst . fst . ($ (mzero, [])) . runState . runST) pop
< = {-~  reformulation  -}
<    fst (fst (runState (runST pop) (mzero, [])))  
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst (fst ((mzero, []), ()))
< = {-~  evaluation of |fst|, twice \todo{Name this property **}  -}
<    mzero
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) Fail

\fbox{|Or p q|}

<    extract (alg (Or p q))
< = {-~  definition of |alg|  -}
<    extract (push q p)
< = {-~  definition of |extract|  -}
<    (fst . fst . ($ (mzero, [])) . runState . runST) (push q p)
< = {-~  reformulation  -}
<    fst (fst (runState (runST (push q p)) (mzero, [])))  
< = {-~  evaluation of |push q p|  -}
<    fst (fst (runState (runST p) (mzero, [q]))) 
< = {-~  property of |ST|  -}
<    fst (fst (runState (runST pop) (mzero `mplus` extract p, [q]))) 
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst (fst (runState (runST pop) (extract p, [q])))
< = {-~  evaluation of |pop|  -}
<    fst (fst (runState (runST q) (extract p, []))) 
< = {-~  property of |ST|  -}
<    fst (fst (runState (runST pop) (extract p `mplus` extract q, []))) 
< = {-~  evaluation of |runST pop|, |runState|  -}
<    fst (fst ((extract p `mplus` extract q, []),()))
< = {-~  evaluation of |fst|, twice \todo{Name this property ***}  -}
<    extract p `mplus` extract q
< = {-~  definition of |algND|  -}
<    algND (Or (extract p) (extract q))
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) (Or p q)
\end{proof}

In this proof we used the property of |ST m a| stating that 
< runState (runST p) (q, stack) = runState (runST pop) (q `mplus` extract p, stack)
Indeed, we only utilize a subset of terms with type |ST m a|, namely those
that are generated by the fold of the |simulate| function,
so for which this property is true.
To prove this, we need to show that 
(1) the generator of |simulate| only generates programs of this subset;
and (2) the algebra preserves this property.

\begin{theorem}
< runState (runST (gen x)) (q, stack) = runState (runST pop) (q `mplus` extract (gen x), stack)
\end{theorem}
We use equational reasoning to prove this theorem.
\begin{proof}
<    runState (runST (gen x)) (q, stack)
< = {-~  definition of |gen|  -}
<    runState (runST (append x pop)) (q, stack)
< = {-~  evaluation of |append|  -}
<    runState (runST pop) (q `mplus` return x, stack)
< = {-~  \todo{property *}  -}
<    runState (runST pop) (q `mplus` extract (gen x), stack)
\end{proof}

\begin{theorem}
< runState (runST (alg x)) (q, stack) = runState (runST pop) (q `mplus` extract (alg x), stack)
\end{theorem}
\begin{proof}
We use equational reasoning with case analysis on |x|.

\fbox{Fail}

<    runState (runST (alg Fail)) (q, stack)
< = {-~  definition of |alg|  -}
<    runState (runST pop) (q, stack)
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    runState (runST pop) (q `mplus` mzero, stack)
< = {-~  \todo{property **}  -}
<    runState (runST pop) (q `mplus` extract (alg Fail), stack)

\fbox{Or p1 p2}
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
< = {-~  \todo{property ***}  -}
<    runState (runST pop) (q `mplus` extract (alg (Or p1 p2)), stack)

\end{proof}

%-------------------------------------------------------------------------------
\subsection{Combining the Simulation with Other Effects}

\begin{code}
newtype ST' m f a = ST' { unST :: State (Free f (m a), [ST' m f a]) () }

hND :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> ST' m f a
hND (Var x) = append' x pop'
hND (Op (Inl Fail)) = pop'
hND (Op (Inl (Or p q))) = push' (hND p) (hND q)
hND (Op (Inr y)) = ST' $ do
  (xs, stack) <- get
  put (xs, stack)

  -- (hNondet' (Op (Inr y)))

pop' :: MNondet m => ST' m f a 
pop' = ST' $ do 
    (xs, stack) <- get
    case stack of 
        []          ->  return ()
        ST' p : ps  ->  do put (xs, ps) ; p

push' :: MNondet m => ST' m f a -> ST' m f a -> ST' m f a
push' q p = ST' $ do
    (xs, stack) <- get
    put (xs, q:stack)
    unST p

append' :: (Functor f, MNondet m) => a -> ST' m f a -> ST' m f a
append' x p = ST' $ do
    (xs, stack) <- get
    put ((`mplus` return x) <$> xs, stack)
    unST p

\end{code}






