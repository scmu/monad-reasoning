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

module Cut where

import Background

import Control.Monad (ap, join, liftM, when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.Either (isLeft)
import Prelude hiding (fail)
import Debug.Trace
\end{code}
%endif

\section{Extension: Simulating Cut Semantics with State}

Prolog interpreters implement more complex control-flow constructs.
The |cut| operator, 
known from Prolog as a goal that always succeeds and never backtracks, 
trims the search space either to improve the program's efficiency 
or to enforce its correct behaviour.
This section explains how syntax and semantics of the |cut| operator can be simulated
with state.

%-------------------------------------------------------------------------------
\subsection{Representing Cut and Backtracking}

List monads and backtracking are unseparable in functional programming.
Therefore, it is natural to encode the representation of backtracking with cut as
an advanced version of a |List| monad.
We can think of |cut| then as a list with a single element: |[()]|. 

As suggested by \citet{Pirog17}, to represent |cut| with backtracking, 
we use monoids extended with a |cut| operation
that is a left-zero for the monoid's associative operator.
In Prolog, the |cut| operation is represented by a nullary symbol |!|.
However, the scope of |!| is delimited to the predicate where it is called.
To enforce this in this representation, \citet{Pirog17} argue that it should be a unary
idempotent operation.

Thus, the monoid for representing |cut| consists of three constructs: 
an identity |eps|, an associative binary operation |dot| and a cut operator |-*|
where |x*| corresponds to |cut >> x|.
This monoidal theory then satisfies the following laws:
\begin{alignat}{2}
    &\mbox{\bf left-identity}:\quad &
    |eps dot x| &= |x|\mbox{~~,} \label{eq:monoid-left-id}\\
    &\mbox{\bf right-identity}:\quad &
    |x dot eps| &= |x|\mbox{~~,} \label{eq:monoid-right-id}\\
    &\mbox{\bf associativity}:~ &
    |(x dot y) dot z| &= |x dot (y dot z)| \mbox{~~,} \label{eq:monoid-assoc}\\
    &\mbox{\bf left-cut}:~ &
    |x* dot y| &= |x*| \mbox{~~,} \label{eq:left-cut} \\
    &\mbox{\bf right-cut}:~ &
    |x dot y*| &= |(x dot y)*| \mbox{~~,} \label{eq:right-cut} \\
    &\mbox{\bf idempotence}:~ &
    |(x*)*| &= |x*| \mbox{~~.} \label{eq:idempotence}
\end{alignat}
The first three laws are the monoid laws.
The left-cut law (\ref{eq:left-cut}) states that operations after a |cut| are ignored.
The right-cut law (\ref{eq:right-cut}) indicates that the |cut| leaves previous computations untouched.
The final law (\ref{eq:idempotence}) contains the idempotence of |-*|.
In what follows, we describe how to model this representation in Haskell.

The idempotent cut operation |-*| is represented by a datatype |Idem|
that either returns its value (|x|) or flags it (|x*|).

\begin{code}
data Idem a = Ret a | Flag a 
\end{code}
%if False
\begin{code}
  deriving Show
\end{code}
%endif 
\begin{code}
unIdem :: Idem a -> a
unIdem (Ret   x)  = x
unIdem (Flag  x)  = x
\end{code}

A |CutList| then is a list in which some operations might be flagged with a cut operation.
For a proper implementation of this |CutList|, a distributive law is required.
For a more detailed argumentation of this distributivity, we refer to \citet{Pirog17}.
\begin{code}
newtype CutList a = CutList { unCutList :: Idem [a] }
\end{code}
%if False
\begin{code}
  deriving Show
\end{code}
%endif 
\begin{code}
distr :: [Idem a] -> Idem [a]
distr (Ret   x  : xs)   = fmap ((:) x) (distr xs)
distr (Flag  x  : xs)   = Flag [x]
distr []                = Ret []
\end{code}
Both datatypes |Idem a| and |CutList a| are monadic.
% The |(>>=)| operation of |Idem a| also preserves the |Flag| constructor as the |distr| function.
The |(>>=)| operation of |CutList a| uses the |distr| function.
%if False
\begin{code}
instance Functor Idem where
  fmap f (Ret a)   = Ret (f a)
  fmap f (Flag a)  = Flag (f a)
instance Applicative Idem where
  pure = return
  (<*>) = ap
instance Functor CutList where
  fmap f x = CutList $ fmap (fmap f) (unCutList x)
instance Applicative CutList where
  pure = return
  (<*>) = ap
instance Foldable CutList where
  foldMap f x = foldMap f (unIdem $ unCutList x)
\end{code}
%endif
\begin{code}
instance Monad Idem where
  return a = Ret a
  Ret a >>= f   = f a
  Flag a >>= f  = Flag (unIdem (f a))
instance Monad CutList where
  return a = CutList $ return (return a)
  m >>= f = CutList $ fmap join (join (fmap distr (fmap (fmap (unCutList . f)) (unCutList m))))
\end{code}

What's more, |CutList a| is also traversable. Its |traverse| function just uses the |traverse| function of list and preserves the data constructor of |Idem|.
\begin{code}
instance Traversable CutList where
  traverse f (CutList (Ret xs))  = fmap (CutList . Ret)  $ traverse f xs
  traverse f (CutList (Flag xs)) = fmap (CutList . Flag) $ traverse f xs
\end{code}

We can now encode smart constructors for cutting (|cut|), failing (|fail|), 
constructing a |CutList| (|cutList|), delimiting a scope (|call|)
and appending two |CutList|s (|append|).

\begin{code}
cut      :: CutList ()
cut      = CutList $ Flag [()]

fail     :: CutList a
fail     = CutList $ Ret []

cutList  :: [a] -> CutList a
cutList  = CutList . Ret

call     :: CutList a -> CutList a
call     = cutList . unIdem . unCutList

append   :: CutList a -> CutList a -> CutList a
append xs ys = (CutList . fmap join . distr) [unCutList xs, unCutList ys]
\end{code}
% append   (CutList (Ret xs))   ys  = CutList $ fmap ((++) xs) $ unCutList ys
% append   (CutList (Flag xs))  _   = CutList (Flag xs)

%-------------------------------------------------------------------------------
\subsection{Encoding Cut as a Free Monad}

To separate syntax and semantics of the cut representation, we use free monads.
Similar to the functors |StateF|, |NondetF| or |StackF| of the previous sections, 
we introduce |CutF| and |CallF|:

\begin{code}
data CutF   a  = Cut
data CallF  a  = Call a
\end{code}
%if False
\begin{code}
instance Functor CutF where
  fmap f Cut = Cut

instance Functor CallF where
  fmap f (Call x) = Call (f x)
\end{code}
%endif

It is necessary to split these functors in two separate ones 
as |Cut| is an algebraic operation, whereas |Call| is not.
To be algebraic, an operation |op| should satisfy the algebraicity property 
which states that
%format p1
%format pn = "\Varid{p}_{n}"
|op (p1, ..., pn) >>= k = op (p1 >>= k, ..., pn >>= k)|.
Indeed, |Call| does not satisfy this property:
< call (cutList [1,2,3]) >> cut = cut
< call (cutList [1,2,3] >> cut) = cutList [()]
This is a typical example of a scoped effect \cite{Pirog18,Wu14}.

Effects with scoping operations can be captured modularly in an adapted version of
the free monad we defined in Section \ref{sec:free-monads}.

\begin{code}
data FreeS f g a  =  VarS     a
                  |  OpS      (f (FreeS f g a))
                  |  ScopeS   (g (FreeS f g (FreeS f g a)))
\end{code}
%if False
\begin{code}
instance (Functor f, Functor g) => Functor (FreeS f g) where
  fmap = liftM

instance (Functor f, Functor g) => Applicative (FreeS f g) where
  pure   = return
  (<*>)  = ap

instance (Functor f, Functor g) => Monad (FreeS f g) where
  return = VarS
  (>>=) (VarS x)     f = f x 
  (>>=) (OpS op)     f = OpS    (fmap (>>= f) op) 
  (>>=) (ScopeS op)  f = ScopeS (fmap (fmap (>>= f)) op)
\end{code}
%endif
This implementation, borrowed from \citet{Pirog18}, is also monadic.
We can fold over this |FreeS| monad using the following algebra:

\begin{code}
data Alg f g a = Alg  { opS   :: f a -> a
                      , scopeS  :: g (FreeS f g a) -> a }

foldS :: (Functor f, Functor g) => (a -> b) -> Alg f g b -> FreeS f g a -> b
foldS gen alg (VarS     x)   = gen x
foldS gen alg (OpS      op)  = (opS   alg    . fmap (foldS gen alg))         op
foldS gen alg (ScopeS   op)  = (scopeS  alg  . fmap (fmap (foldS gen alg)))  op
\end{code}

With this, we have everything in place to write a handler for the cut effect.

The algebraic effects consist of nondeterministic operations, the cut operation
and possibly other effects |f|. 
The scoped effects consist of the scoping operation and possibly other effects |g|.
\begin{code}
type NondetF' = NondetF :+: CutF
\end{code}

% To deal with the scoped operations, we will use a \emph{forwarding algebra},
% inspired by the work of \citet{Schrijvers19}.
% They propose a modular approach to composing algebraic effects so that each handler
% only needs to know about the part of the syntax its effect is handling.
% This is achieved through an adapted version of a modular carrier that features
% a forwarding algebra |fwd|.

% \begin{code}
% class Modular (g :: * -> *) (f1 :: * -> *) (f2 :: * -> *) (m :: * -> *) where
%   fwd :: g (f1 (f2 (m a))) -> f2 (m a)

% instance (Functor f, Functor g) 
%          => Modular g (FreeS (NondetF' :+: f) (CallF :+: g)) (FreeS f g) CutList 
%          where
%   fwd = Enter . fmap (fmap (fmap join . sequenceA) . hCut)
% \end{code}

The handler for the cut effect can now be defined as follows:

\begin{code}
hCut  :: (Functor f, Functor g)
      => FreeS (NondetF' :+: f) (CallF :+: g) a
      -> FreeS f g (CutList a)
hCut = foldS gen (Alg (algNDCut # OpS) (algSC # fwdSC))
  where
    gen                      = return . return
    algNDCut (Inl Fail)      = return fail
    algNDCut (Inl (Or x y))  = append <$> x <*> y
    algNDCut (Inr Cut)       = return (cut >> fail)
    algSC    (Call k)        = (algCut . hCut) k
    fwdSC                    = ScopeS . fmap (fwdCut . hCut)

algCut  :: (Functor f, Functor g)
        => FreeS f g (CutList (FreeS f g (CutList a)))
        -> FreeS f g (CutList a)
algCut  = join . fwdCut . fmap call
fwdCut  :: (Functor f, Functor g)
        => FreeS f g (CutList (FreeS f g (CutList a)))
        -> FreeS f g (FreeS f g (CutList a))
fwdCut  = fmap (fmap join . sequenceA)
\end{code}

%-------------------------------------------------------------------------------
\subsection{Example}

To show the semantics of the cut operation and scoped effect, we can define a function
|takeWhileS| that returns all programs |prog| that satisfy a predicate |p|.
Throughout this example, we will use smart constructors |or'|, |fail'|, |cut'| and |scope'|
for their corresponding datatype.
\begin{code}
takeWhileS  :: (Functor f, Functor g) 
            => (a -> Bool) 
            -> FreeS (NondetF' :+: f) (CallF :+: g) a 
            -> FreeS (NondetF' :+: f) (CallF :+: g) a
takeWhileS p prog = call' $ do
  x <- prog
  when (not $ p x) cut'
  return $ return x
\end{code}

We define two example programs and a |prefixes| function which takes the
even prefixes of these programs:
%format prog1
%format prog2
\begin{code}
prog1 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (CallF :+: g) Int
prog1 = or' (or' (return 2) (return 4)) (or' (return 5) (return 8))

prog2 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (CallF :+: g) Int
prog2 = or' (or' (return 6) (return 9)) (return 10)

prefixes :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (CallF :+: g) Int
prefixes = or' (takeWhileS even prog1) (takeWhileS even prog2)
\end{code}
The result of handling this |prefixes| function, is a |CutList| of the even prefixes
of |prog1| and |prog2|.
< > run (hCut prefixes)
< CutList {unCutList = Ret [2,4,6]}
Here, |run| takes the final result from the leave of the |FreeS| monad:
\begin{code}
run :: FreeS NilF NilF a -> a
run (VarS x) = x
\end{code}

%if False
\begin{code}
fail'     = (OpS . Inl . Inl) Fail
or' x y   = (OpS . Inl . Inl) $ Or x y
cut'      = (OpS . Inl . Inr) Cut
call' x   = (ScopeS . Inl) $ Call x

-- > (run . hCut) (takeWhileS even prog1)
-- CutList {unCutList = Flag [2,4]}

prog :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (CallF :+: g) Int
prog = or' (call' (or' (return $ return 2) (return $ return 4))) (return 6)
\end{code}
%endif

%-------------------------------------------------------------------------------
\subsection{Simulating the Cut Effect with State}

This section shows how to use a state-based implementation to simulate the cut effect.
We use a wrapper |SCut|.
\begin{code}
type CompCut s f g a = FreeS (StateF s :+: f) g a
data SCut f g a = SCut { resultsCut :: CutList a, stackCut :: [CompCut (SCut f g a) f g ()] }
\end{code}
The type |SCut| is represented by a pair of a cutlist, |CutList a|, and a stack of computations or branches to be evaluated.

We can define a simulation function as follows:
\begin{code}
cut2state  :: (Functor f, Functor g)
           => FreeS (NondetF' :+: f) (CallF :+: g) a
           -> CompCut (SCut f g a) f g ()
cut2state = foldS genCut (Alg (algNDCut # fwd) (algSCCut # fwdSc))
  where
  genCut x = appendSC x popSC
  algNDCut (Inl Fail) = popSC
  algNDCut (Inl (Or p q)) = pushSC q p
  algNDCut (Inr Cut) = undoSC
  fwd = OpS . Inr
  algSCCut (Call k)  =  cutlist2state $ algCut
                     .  fmap (fmap state2cutlist) .  state2cutlist . cut2state $ k
  fwdSc oth =  let tmp = fmap  (  fwdCut
                               .  fmap (fmap state2cutlist) .  state2cutlist . cut2state) oth
               in ScopeS $ fmap (shiftRight . fmap cutlist2state) tmp
\end{code}

There are some helper functions |getSC|, |putSC|, |popSC|, |pushSC|, |appendSC|, |undoSC|, |state2cutlist| and |cutlist2state|.

\begin{code}
getSC :: (Functor f, Functor g) => CompCut s f g s
getSC = OpS (Inl $ Get return)

putSC :: (Functor f, Functor g) => s -> CompCut s f g ()
putSC s = OpS (Inl $ Put s (return ()))

popSC :: (Functor f, Functor g) => CompCut (SCut f g a) f g ()
popSC = do
  SCut xs stack <- getSC
  case stack of
    [] -> return ()
    p : ps -> do putSC (SCut xs ps); p

pushSC :: (Functor f, Functor g)
       => CompCut (SCut f g a) f g ()
       -> CompCut (SCut f g a) f g ()
       -> CompCut (SCut f g a) f g ()
pushSC q p = do
  SCut xs stack <- getSC
  putSC (SCut xs (q : stack)); p

appendSC :: (Functor f, Functor g) => a
         -> CompCut (SCut f g a) f g ()
         -> CompCut (SCut f g a) f g ()
appendSC x p = do
  SCut xs stack <- getSC
  putSC (SCut (append xs (return x)) stack); p

undoSC :: (Functor f, Functor g) => CompCut (SCut f g a) f g ()
undoSC = do
  SCut xs stack <- getSC
  putSC (SCut (append xs (cut >> fail)) stack)  -- can we drop the stack here?

state2cutlist  :: (Functor f, Functor g)
               => CompCut (SCut f g a) f g () -> FreeS f g (CutList a)
state2cutlist = extractSC . hStateS

cutlist2state  :: (Functor f, Functor g)
               => FreeS f g (CutList a) -> CompCut (SCut f g a) f g ()
cutlist2state m = do
    t <- shiftRight m
    SCut xs stack <- getSC
    putSC $ SCut (append xs t) stack
    --case stack of
    --  [] -> putSC $ SCut (append xs t) []
    --  p : ps -> do putSC $ SCut (append xs t) ps ; p

shiftRight :: (Functor f, Functor g) => FreeS f g a -> FreeS (f' :+: f) g a
shiftRight (VarS x)   = VarS x
shiftRight (OpS k)    = (OpS (Inr (fmap shiftRight k)))
shiftRight (ScopeS k) = ScopeS $ fmap (shiftRight . (fmap shiftRight)) k
\end{code}

To extract the result from the |SC| wrapper, we define an |extractSC| function.
\begin{code}
extractSC :: (Functor f, Functor g) => StateT (SCut f g a) (FreeS f g) () -> FreeS f g (CutList a)
extractSC x = resultsCut . snd <$> runStateT x (SCut (cutList []) [])
\end{code}

We also need a new handler |hStateS| of |StateF| which is similar to |hState| but adapted to |FreeS|.
\begin{code}
hStateS :: (Functor f, Functor g) => CompCut s f g a -> StateT s (FreeS f g) a
hStateS = foldS gen (Alg (alg # fwd) fwdsc)
  where
    gen x            = StateT $ \s -> return (x, s)
    alg (Get     k)  = StateT $ \s -> runStateT (k s) s
    alg (Put s'  k)  = StateT $ \s -> runStateT k s'
    fwd op           = StateT $ \s -> OpS $ fmap (\k -> runStateT k s) op
    fwdsc x          = StateT $ \s -> 
      ScopeS $ fmap (fmap (\(a, b) -> runStateT a b) . ($s) . runStateT . hStateS) x
\end{code}

Finally, we have the function |runCut|, which transforms every monad with nondeterminism, cut and other effects |f| into
a free monad where the result is wrapped in the |CutList| monad.
\begin{code}
runCut  :: (Functor f, Functor g)
        => FreeS (NondetF' :+: f) (CallF :+: g) a
        -> FreeS f g (CutList a)
runCut = extractSC . hStateS . cut2state
\end{code}
To show that the simulation is correct, we prove that |runCut = hCut|.
\wenhao{Do we need to prove it? It seems the proof would be long.}

%if False
% The old simulation
\wenhao{I have wrote two simulations here, one directly uses the state monad to simulate nondet free monad, and the other uses the state free monad to simulate nondet free monad. I think we should remain the second simulation as it is more consistent with S3 and S4. And I have combine the second simulation with other effects.}

The first simulation is given by:
< simulate :: FreeS (NondetF' :+: NilF) (CallF :+: NilF) a -> FreeS Nil Nil (STCut a)
< extractCut . run . simulate :: FreeS (NondetF' :+: NilF) (CallF :+: NilF) a -> CutList a

Code :
\begin{code}
newtype STCut a = STCut {runSTCut :: State (CutList a, [STCut a]) ()}

type V a = FreeS NilF NilF a

simulate :: FreeS (NondetF' :+: NilF) (CallF :+: NilF) a -> V (STCut a)
simulate = foldS genCut (Alg (algNDCut # undefined) (algSCCut # undefined)) where
  genCut :: a -> V (STCut a)
  genCut x                 = return $ appendCut x popCut
  algNDCut :: (NondetF :+: CutF) (V (STCut a)) -> V (STCut a)
  algNDCut (Inl Fail)      = return $ popCut
  algNDCut (Inl (Or p q))  = return $ pushCut (run q) (run p)
  algNDCut (Inr Cut)       = return $ undoCut
  algSCCut :: CallF (FreeS (NondetF' :+: NilF) (CallF :+: NilF) (V (STCut a))) -> V (STCut a)
  algSCCut (Call k)       = return $ joinSTCut (run (simulate (fmap run k)))

joinSTCut :: STCut (STCut a) -> STCut a
joinSTCut x = let t = call $ fmap extractCut (extractCut x) in STCut $ State $ \ (cl, stack) ->
  case stack of
    [] -> ((), (append cl (join t), []))
    STCut p : ps -> runState p (append cl (join t), ps)

joinSTCut' :: STCut (STCut a) -> STCut a
joinSTCut' x = let t = call $ fmap extractCut (extractCut x) in STCut $ do
  (cl, stack) <- get
  case stack of
    [] -> put (append cl (join t), [])
    STCut p : ps -> do put (append cl (join t), ps); p

extractCut :: STCut a -> CutList a
extractCut x = fst $ snd $ runState (runSTCut x) (fail, [])

popCut :: STCut a
popCut = STCut $ do
  (xs, stack) <- get
  case stack of
    [] -> return ()
    STCut p : ps -> do put (xs, ps); p

appendCut :: a -> STCut a -> STCut a
appendCut x p = STCut $ do
  (xs, stack) <- get
  put (append xs (return x), stack)
  runSTCut p

pushCut :: STCut a -> STCut a -> STCut a
pushCut q p = STCut $ do
  (xs, stack) <- get
  put (xs, q : stack)
  runSTCut p

undoCut :: STCut a
undoCut = STCut $ do
  (xs, stack) <- get
  put (append xs (cut >> fail), stack)

test1 :: FreeS (NondetF' :+: NilF) (CallF :+: NilF) a -> CutList a
test1 = extractCut . run . simulate
\end{code}
%endif





























