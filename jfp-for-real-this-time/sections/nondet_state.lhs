\section{Modeling Nondeterminism With State}
\label{sec:nondeterminism-state}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module NondetState where

-- import qualified Control.Monad.State.Lazy as S
import Background
import Control.Monad (ap)
-- import Control.Applicative

newtype State s a = State { runState :: s -> (s, a) } deriving (Functor)

instance Applicative (State s) where
    pure   = return 
    (<*>)  = ap

instance Monad (State s) where
    return x  = State (\s -> (s, x))
    m >>= f   = State (\s -> let (s', x') = runState m s in runState (f x') s')

instance MState s (State s) where
    get    = State (\s -> (s, s))
    put s  = State (\_ -> (s, ()))

type Nondet a = Free NondetF a
\end{code}
%endif

Intro. Refer to WAM. 

%-------------------------------------------------------------------------------
\subsection{Interpreting Nondeterministic Programs with List}

Haskell's implementation of nondeterminism is the |List| monad, 
which is a lawful instance of |MNondet|.

\begin{code}
instance MNondet [] where
	mzero  =  []
	mplus  =  (++)
\end{code}
Indeed, all nondeterminism laws of \cref{sec:nondeterminism} are satisfied by
this implementation.
The return of the |List| monad is a singleton list and the bind operation is
concatenation or flattening.

We can interpret these nondeterministic programs encoded in lists 
by means of the |choose| function, which can be implemented as a fold.

\begin{code}
choose :: MNondet m => [a] -> m a
choose = foldr (mplus . return) mzero
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

Now, we can also give a state-based implementation of nondeterminism, which uses
Haskell's state monad |MonadState|.

\begin{code}

newtype Prog m a = Prog (State (m a, [Prog m a]) ())

runProg :: Prog m a -> (m a, [Prog m a]) -> ((m a, [Prog m a]), ())
runProg (Prog p) = runState p

emit :: MNondet m => a -> Prog m a -> Prog m a
emit x (Prog p) = Prog $ do
	(xs, stack) <- get
	put (xs `mplus` return x, stack)
	p

pop :: MNondet m => Prog m a 
pop = Prog $ do 
	(xs, stack) <- get
	case stack of 
		[]           ->  return ()
		Prog p : ps  ->  do put (xs, ps) ; p

push :: MNondet m => Prog m a -> Prog m a -> Prog m a
push q (Prog p) = Prog $ do
	(x, stack) <- get
	put (x, q:stack)
	p

simulate :: MNondet m => Nondet a -> Prog m a
simulate (Var x)        = emit x pop
simulate (Op Fail)      = pop
simulate (Op (Or p q))  = push (simulate q) (simulate p)

runNondetList :: Nondet a -> [a]
runNondetList (Var x)        = [x]
runNondetList (Op Fail)      = []
runNondetList (Op (Or a b))  = (runNondetList a) ++ (runNondetList b)

runNondet :: MNondet m => Nondet a -> m a
runNondet p = fst $ fst $ runProg (simulate p) $ (mzero, [])

newtype CProg m a b = CProg {runCProg :: (b -> Prog m a) -> Prog m a} 
    deriving (Functor)

instance Applicative (CProg m a) where
	pure   = return 
	(<*>)  = ap

instance Monad (CProg m a) where
	return x  = CProg (\k -> k x)
	m >>= f   = CProg (\k -> runCProg m (\x -> runCProg (f x) k))

instance MNondet m => MNondet (CProg m a) where
	mzero      = CProg (\k -> pop)
	mplus p q  = CProg (\k -> push (runCProg p k) (runCProg q k))

runNondetC :: MNondet m => CProg m a a -> m a
runNondetC p = fst $ fst $ runProg (runCProg p (\x -> emit x pop)) (mzero, [])

\end{code}


%-------------------------------------------------------------------------------
\subsection{Proof of correctness}

%-------------------------------------------------------------------------------
\subsection{ND + $\Sigma$ $\to$ S + $\Sigma$}








