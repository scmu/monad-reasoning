{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module FusionGlobal where

import Prelude hiding (fail, or)
import Background
import Overview
import LocalGlobal (queensR)
-- import Combination (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop))
import Stack2 (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop, GetSt, PutSt)
              , getInfoSt, putInfoSt)
import TermAlg

import Control.Monad (liftM, ap, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import Data.Array.ST
import Control.Monad.ST
import Control.Monad.ST.Trans (STT, runSTT)
import Control.Monad.ST.Trans.Internal (liftST, STT(..), unSTT)
import Data.STRef
import Data.Functor.Identity (Identity (Identity))

----------------------------------------------------------------

instance (Monad m, TermAlgebra m (NondetF :+: g), Functor g) => MNondet m where
  mzero = con (Inl $ Fail)
  mplus x y = con (Inl $ Or x y)

instance (Monad m, TermAlgebra m (f :+: StateF s :+: g), Functor f, Functor g) => MState s m where
  get = con (Inr . Inl $ Get return)
  put x = con (Inr . Inl $ Put x (return ()))

fhGlobal :: Cod (MList (StateT s Identity)) a -> s -> Identity [a]
fhGlobal = fmap (fmap fst) . runStateT . unMList . runCod genMList

queensModify :: Int -> [[Int]]
queensModify = run . flip fhGlobal (0, []) . queensR

-- >>> queensModify 4
-- [[3,1,4,2],[2,4,1,3]]

------------------------------------------------------------------------------
-- nondet2state
------------------------------------------------------------------------------

data SS m a = SS { resultsSS :: [a], stackSS :: [StateT (SS m a) m ()] }
newtype QwQ m a = QwQ {unQwQ :: StateT (SS m a) m ()}
genQwQ :: Monad m => a -> QwQ m a
genQwQ = \x -> appendQwQ x popQwQ

extractSS :: Monad m => StateT (SS m a) m () -> m [a]
extractSS x = resultsSS . snd <$> runStateT x (SS [] [])

simND :: Monad m => Cod (QwQ (StateT s m)) a -> StateT s m [a]
simND = extractSS . unQwQ . runCod genQwQ

queensStateR :: Int -> [[Int]]
queensStateR = run . fmap fst . flip runStateT (0, [])
            --  . unMList . extractSS . unQwQ . runCod genQwQ . queensR
             . simND . queensR
-- queensStateR  :: Int -> [[Int]]
-- queensStateR  = hNil
--               . fmap fst . flip runStateT (0, []) . hState
--               . (extractSS . hState . nondet2state) . comm2
--               . queensR
-- >>> queensStateR 4
-- [[3,1,4,2],[2,4,1,3]]

instance (TermMonad m f) => TermAlgebra (Cod (QwQ m)) (NondetF :+: f) where
  var = return
  con = algCod con'
    where
      con' :: TermMonad m f => (NondetF :+: f) (QwQ m x) -> QwQ m x
      con' (Inl Fail) = popQwQ
      con' (Inl (Or p q)) = pushQwQ q p
      con' (Inr op) = QwQ . StateT $ \s -> con $ fmap (\k -> runStateT (unQwQ k) s) op

popQwQ  :: Monad f => QwQ f a
popQwQ = QwQ $ popSS

pushQwQ :: Monad f => QwQ f a -> QwQ f a -> QwQ f a
pushQwQ (QwQ q) (QwQ p) = QwQ $ pushSS q p

appendQwQ :: Monad f => a
          -> QwQ f a
          -> QwQ f a
appendQwQ x (QwQ p) = QwQ $ appendSS x p

getSS :: Monad f => StateT s f s
getSS = StateT $ \ s -> return (s, s)
putSS :: Monad f => s -> StateT s f ()
putSS s = StateT $ \ _ -> return ((), s)

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

----------------------------------------------------------------
-- nondet2stack
-- using Stack2
----------------------------------------------------------------

newtype StackT s b e m a = StackT { runStackT :: Stack s b e -> STT s m (a, b) }

instance Monad m => Functor (StackT s b e m) where
  fmap = liftM
instance Monad m => Applicative (StackT s b e m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (StackT s b e m) where
  -- return = StackT . const . return
  return x = StackT $ \ stack -> liftST (getInfoSt stack) >>= \b -> return (x, b)
  (StackT m) >>= f = StackT $ \stack -> let t = do (a, b) <- m stack;
                                                   (b', b) <- runStackT (f a) stack ;
                                                   return (b', b) in t
                                                   -- NOTE: correct?

instance (TermMonad m f) => TermAlgebra (StackT s b e m) (StackF e b :+: f) where
  var = return
  con (Inl (Pop k)) = StackT $ \stack -> liftST (popStack stack) >>= \x -> runStackT (k x) stack
  con (Inl (Push x k)) = StackT $ \stack -> liftST (pushStack x stack) >> runStackT k stack
  con (Inr op) = StackT $ \stack -> STT $ \s -> con ((\f -> unSTT (f stack) s) <$> fmap runStackT op)
  -- con (Inl (Push x k)) = StackT $ \stack -> liftST (pushStack x stack)  >> runStackT k stack

newtype SK s m a = SK { unSK :: StackT s [a] (SK s m a) m () }
genSK :: Monad m => a -> SK s m a
genSK = \x -> appendTwT x popTwT


-- instance (TermMonad m f) => TermAlgebra (Cod (SK s m)) (NondetF :+: f) where
instance (TermMonad m f) => TermAlgebra (Cod (SK s m)) (NondetF :+: f) where
  var = return
  con = algCod con'
    where
      con' (Inl Fail) = popTwT
      con' (Inl (Or p q)) = pushTwT q p
      con' (Inr op) = SK . StackT $ \stack -> STT $ \s -> con ((\f -> unSTT (runStackT (unSK f) stack) s) <$> op)

-- simNDSK :: Monad m => (forall s . Cod (SK s (StateT s' m)) a) -> StateT s' m [a]
-- simNDSK :: Monad m => Cod (SK s (StateT s' m)) a -> StateT s' m [a]
-- simNDSK p =
--   runSTT (fmap snd $ liftST (emptyStack []) >>= \stack -> flip runStackT stack . unSK . runCod genSK $ p)

queensStackR :: Int -> [[Int]]
queensStackR n = run . fmap fst . flip runStateT (0, [])
              $ (runSTT (fmap snd $ liftST (emptyStack []) >>= \stack -> flip runStackT stack . unSK . runCod genSK $ queensR n))

-- >>> queensStackR 4
-- [[3,1,4,2],[2,4,1,3]]

popTwT :: Monad f => SK s f a
popTwT = SK $ popSK

pushTwT :: Monad f => SK s f a -> SK s f a -> SK s f a
pushTwT (SK q) (SK p) = SK $ pushSK q p

appendTwT :: Monad f => a -> SK s f a -> SK s f a
appendTwT x (SK p) = SK $ appendSK x p

dup x = (x, x)
pw x y = (y, x)

getSK :: Monad m => StackT s b e m b
getSK = StackT $ liftST . fmap dup . getInfoSt

putSK :: Monad m => b -> StackT s b e m ()
putSK b = StackT $ liftST . fmap (pw b) . putInfoSt b

popSK' :: Monad m => StackT s b e m (Maybe e)
popSK' = do b <- getSK; StackT $ liftST . fmap (pw b) . popStack

pushSK' :: Monad m => e -> StackT s b e m ()
pushSK' e = do b <- getSK; StackT $ liftST . fmap (pw b) . pushStack e

popSK :: Monad m => StackT s [a] (SK s m a) m ()
popSK = do
  mtop <- popSK'
  case mtop of
    Nothing -> return ()
    Just (SK top) -> top

pushSK :: Monad m
       => StackT s [a] (SK s m a) m ()
       -> StackT s [a] (SK s m a) m ()
       -> StackT s [a] (SK s m a) m ()
pushSK q p = do
  pushSK' (SK q)
  p

appendSK :: Monad m
         => a
         -> StackT s [a] (SK s m a) m ()
         -> StackT s [a] (SK s m a) m ()
appendSK x p = do
  xs <- getSK
  putSK (xs ++ [x])
  p
