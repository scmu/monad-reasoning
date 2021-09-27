{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}


module Fusion4 where

import Prelude hiding (fail, or)
import Background
import LocalGlobal (queensR, comm2)

import Control.Monad (liftM, ap, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

----------------------------------------------------------------

newtype Cod h a = Cod { unCod :: forall x . (a -> h x) -> h x }

instance Functor (Cod h) where
  fmap = liftM

instance Applicative (Cod h) where
  pure = return
  (<*>) = ap

instance Monad (Cod h) where
  return x = Cod (\ k -> k x)
  Cod m >>= f = Cod (\ k -> m (\ a -> unCod (f a) k))

algCod :: Functor f => (forall x . f (h x) -> h x) -> (f (Cod h a) -> Cod h a)
algCod alg op = Cod (\ k -> alg (fmap (\ m -> unCod m k) op))

runCod :: (a -> f x) -> Cod f a -> f x
runCod g m = unCod m g

----------------------------------------------------------------

class Functor f => TermAlgebra h f | h -> f where
  var :: forall a . a -> h a
  con :: forall a . f (h a) -> (h a)

instance Functor f => TermAlgebra (Free f) f where
  var = Var
  con = Op

class (Monad m, TermAlgebra m f) => TermMonad m f
instance (Monad m, TermAlgebra m f) => TermMonad m f
-- instance Functor f => TermMonad (Free f) f

newtype MList m a = MList { unMList :: m [a] }

instance Monad m => Functor (MList m) where
  fmap = liftM
instance Monad m => Applicative (MList m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (MList m) where
  return x = MList $ return [x]
  mx >>= f = undefined

instance (TermMonad m f) => TermAlgebra (MList m) (NondetF :+: f) where
  var = return
  con (Inl Fail) = MList $ return []
  con (Inl (Or (MList p) (MList q))) = MList $ do x <- p; y <- q; return (x ++ y)
  con (Inr op) = MList . con . fmap unMList $ op

instance (TermMonad m f) => TermAlgebra (StateT s m) (StateF s :+: f) where
  var = return
  con (Inl (Get     k))  = StateT $ \s -> runStateT (k s) s
  con (Inl (Put s'  k))  = StateT $ \s -> runStateT k s'
  con (Inr op)           = StateT $ \s -> con $ fmap (\k -> runStateT k s) op

fhND :: (TermMonad m f, Functor f) => Free (NondetF :+: f) a -> MList m a
fhND = fold var con

fhState :: (TermMonad m f, Functor f) => Free (StateF s :+: f) a -> StateT s m a
fhState = fold var con

fhLocal :: (TermMonad m f, Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> m [a]
fhLocal = fmap (fmap (fmap fst) . unMList) . runStateT . fhState

fhGlobal :: (TermMonad m f, Functor f) => Free (StateF s :+: NondetF :+: f) a -> s -> m [a]
fhGlobal = fmap (fmap fst) . runStateT . unMList . fhND . comm2

queensLocal :: Int -> [[Int]]
queensLocal = hNil . flip fhLocal (0, []) . queens

queensModify :: Int -> [[Int]]
queensModify = hNil . flip fhGlobal (0, []) . queensR

-- >>> queensLocal 4
-- >>> queensModify 4
-- [[3,1,4,2],[2,4,1,3]]
-- [[3,1,4,2],[2,4,1,3]]

------------------------------------------------------------------------------

data SS m a = SS { resultsSS :: [a], stackSS :: [StateT (SS m a) m ()] }
newtype QwQ m a = QwQ {unQwQ :: StateT (SS m a) m ()}

nondet2state :: (TermMonad m f, Functor f) => Free (NondetF :+: f) a -> QwQ m a
nondet2state = runCod (\x -> appendQwQ x popQwQ) . fold var con

simND :: (TermMonad m f, Functor f) => Free (NondetF :+: f) a -> MList m a
simND = extractSS . unQwQ . nondet2state

extractSS :: (TermMonad m f, Functor f) => StateT (SS m a) m () -> MList m a
extractSS x = MList $ resultsSS . snd <$> runStateT x (SS [] [])

queensStateR :: Int -> [[Int]]
queensStateR =  hNil . fmap fst . flip runStateT (0::Int, []::[Int])
              . unMList . simND . comm2 . queensR
-- >>> queensStateR 4
-- [[3,1,4,2],[2,4,1,3]]

instance (TermMonad m f) => TermAlgebra (Cod (QwQ m)) (NondetF :+: f) where
  var = return
  con = algCod con'
    where
      con' :: TermMonad m f => (NondetF :+: f) (QwQ m x) -> QwQ m x
      con' (Inl Fail) = popQwQ
      con' (Inl (Or p q)) = pushQwQ q p
      -- con' (Inr op) = let t = fmap (runStateT . unQwQ) $ op in undefined
      con' (Inr op) = QwQ . StateT $ \s -> con $ fmap (\k -> runStateT (unQwQ k) s) op

getSS :: Monad f => StateT s f s
getSS = StateT $ \ s -> return (s, s)
putSS :: Monad f => s -> StateT s f ()
putSS s = StateT $ \ _ -> return ((), s)

popQwQ  :: Monad f => QwQ f a
popQwQ = QwQ $ popSS

pushQwQ :: Monad f => QwQ f a -> QwQ f a -> QwQ f a
pushQwQ (QwQ q) (QwQ p) = QwQ $ pushSS q p

appendQwQ :: Monad f => a
          -> QwQ f a
          -> QwQ f a
appendQwQ x (QwQ p) = QwQ $ appendSS x p

popSS  :: Monad f => StateT (SS f a) f ()
popSS = do
  SS xs stack <- getSS
  case stack of
    []       -> return ()
    op : ps  -> do
      putSS (SS xs ps); op

pushSS  :: Monad f
        => StateT (SS f a) f ()
        -> StateT (SS f a) f ()
        -> StateT (SS f a) f ()
pushSS q p = do
  SS xs stack <- getSS
  putSS (SS xs (q : stack)); p

appendSS  :: Monad f => a
          -> StateT (SS f a) f ()
          -> StateT (SS f a) f ()
appendSS x p = do
  SS xs stack <- getSS
  putSS (SS (xs ++ [x]) stack); p
