%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}

import Background

import Control.Monad (ap, join, liftM, when)
import Control.Monad.Trans (lift)
import Prelude hiding (fail)
\end{code}
%endif

\subsection{New Cut Semantics}
\label{sec:cuts}

\wenhao{This section is a new implementation of the cut extension using the EM Algebras.
It is equivalent to the implementation using the scope effects calculus.}

Scoped effects:

\begin{code}
data FreeS f g a  = Return a
                  | Call (f (FreeS f g a))
                  | Enter (g (FreeS f g (FreeS f g a)))

instance (Functor f, Functor g) => Functor (FreeS f g) where
  fmap = liftM

instance (Functor f, Functor g) => Applicative (FreeS f g) where
  pure   = return
  (<*>)  = ap

instance (Functor f, Functor g) => Monad (FreeS f g) where
  return = Return
  (>>=) (Return x)  f = f x 
  (>>=) (Call op)   f = Call (fmap (>>= f) op) 
  (>>=) (Enter op)  f = Enter (fmap (fmap (>>= f)) op)

data Alg f g a = Alg  { call   :: f a -> a
                      , enter  :: g (FreeS f g a) -> a }

foldS :: (Functor f, Functor g) => (a -> b) -> Alg f g b -> FreeS f g a -> b
foldS gen alg (Return  x)   = gen x
foldS gen alg (Call    op)  = (call alg  . fmap (foldS gen alg)) op
foldS gen alg (Enter   op)  = (enter alg . fmap (fmap (foldS gen alg))) op

data Void a deriving Functor

run :: FreeS Void Void a -> a
run (Return x) = x

\end{code}

Cutlist:
\begin{code}
newtype CutList a = CutList { unCutList :: Idem [a] } deriving Show
data Idem a = Ret a | Flag a deriving Show

unIdem :: Idem a -> a
unIdem (Ret a) = a
unIdem (Flag a) = a

instance Functor Idem where
  fmap f (Ret a)   = Ret (f a)
  fmap f (Flag a)  = Flag (f a)
instance Applicative Idem where
  pure = return
  (<*>) = ap
instance Monad Idem where
  return a = Ret a
  Ret a >>= f   = f a
  Flag a >>= f  = Flag (unIdem (f a))

distr :: [Idem a] -> Idem [a]
distr (Ret a : xs) = fmap (\y -> a : y) (distr xs)
distr (Flag a : xs) = Flag [a]
distr [] = Ret []

instance Functor CutList where
  fmap f x = CutList $ fmap (fmap f) (unCutList x)
instance Applicative CutList where
  pure = return
  (<*>) = ap
instance Monad CutList where
  return a = CutList $ return (return a)
  m >>= f = CutList $ fmap join (join (fmap distr (fmap (fmap (unCutList . f)) (unCutList m))))
instance Foldable CutList where
  foldMap f x = foldMap f (unIdem $ unCutList x)
instance Traversable CutList where
  traverse f (CutList (Ret xs)) = fmap (CutList . Ret) $ traverse f xs
  traverse f (CutList (Flag xs)) = fmap (CutList . Flag) $ traverse f xs

cut :: CutList ()
cut = CutList $ Flag [()]

fail :: CutList a
fail = CutList $ Ret []

scope :: CutList a -> CutList a
scope = fromList . toList

fromList :: [a] -> CutList a
fromList = CutList . Ret

toList :: CutList a -> [a]
toList = unIdem . unCutList

append :: CutList a -> CutList a -> CutList a
append (CutList (Ret xs)) ys = CutList $ fmap ((++) xs) $ unCutList ys
append (CutList (Flag xs)) _ = CutList (Flag xs)
\end{code}

Handler for cut:
\begin{code}
(#) :: (sig1 a -> p) -> (sig2 a -> p) -> (sig1 :+: sig2) a -> p
(alg1 # alg2) (Inl op) = alg1 op
(alg1 # alg2) (Inr op) = alg2 op

data CutF a = Cut deriving Functor
data ScopeF a = Scope a deriving Functor
type NondetF' = NondetF :+: CutF

hCut  :: (Functor f, Functor g)
      => FreeS (NondetF' :+: f) (ScopeF :+: g) a
      -> FreeS f g (CutList a)
hCut = foldS gen (Alg (algND' # Call) (algSC' # fwd))
  where
    gen  :: (Functor f, Functor g) => a -> FreeS f g (CutList a)
    gen = return . return
    algND'  :: (Functor f, Functor g)
            => NondetF' (FreeS f g (CutList a)) 
            -> FreeS f g (CutList a)
    algND' (Inl Fail)      = return fail
    algND' (Inl (Or x y))  = do x' <- x; y' <- y; return (append x' y')
    algND' (Inr Cut)       = return (cut >> fail)
    algSC'  :: (Functor f, Functor g)
            => ScopeF (FreeS (NondetF' :+: f) (ScopeF :+: g) (FreeS f g (CutList a)))
            -> FreeS f g (CutList a)
    algSC' (Scope k) = join $ fmap (fmap join . sequenceA . scope) (hCut k)
    fwd     :: (Functor f, Functor g)
            => g (FreeS (NondetF' :+: f) (ScopeF :+: g) (FreeS f g (CutList a)))
            -> FreeS f g (CutList a)
    fwd k = Enter $ fmap (fmap (fmap join . sequenceA) . hCut) k
\end{code}

Examples:
\begin{code}
fail' = (Call . Inl . Inl) Fail
or' x y = (Call . Inl . Inl) $ Or x y
cut' = (Call . Inl . Inr) Cut
scope' x = (Enter . Inl) $ Scope x

takeWhileS :: (Functor f, Functor g) => (a -> Bool) -> FreeS (NondetF' :+: f) (ScopeF :+: g) a -> FreeS (NondetF' :+: f) (ScopeF :+: g) a
takeWhileS p prog = scope'
  (do x <- prog; when (not (p x)) cut'; return $ return x)

prog1 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prog1 = or' (or' (return 2) (return 4)) (or' (return 5) (return 8))

prog2 :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prog2 = or' (or' (return 8) (return 9)) (return 10)

prefixes' :: (Functor f, Functor g) => FreeS (NondetF' :+: f) (ScopeF :+: g) Int
prefixes' = or' (takeWhileS even prog1) (takeWhileS even prog2)

-- > (run . hCut) (takeWhileS even prog1)
-- CutList {unCutList = Flag [2,4]}

-- > (run . hCut) prefixes'
-- CutList {unCutList = Ret [2,4,8]}

\end{code}