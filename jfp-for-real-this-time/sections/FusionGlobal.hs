{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes, QuantifiedConstraints #-}

module FusionGlobal where

import Prelude hiding (fail, or)
import Background
import LocalGlobal (queensR)
-- import Combination (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop))
import Stack2 (Stack, Index, growStack, emptyStack, pushStack, popStack, StackF(Push, Pop))
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
genQwQ = \x -> appendQwQ x popQwQ

extractSS :: (TermMonad m f, Functor f) => StateT (SS m a) m () -> MList m a
extractSS x = MList $ resultsSS . snd <$> runStateT x (SS [] [])

queensStateR :: Int -> [[Int]]
queensStateR = run . fmap fst . flip runStateT (0, [])
             . unMList . extractSS . unQwQ . runCod genQwQ . queensR
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

----------------------------------------------------------------
-- nondet2stack
-- using Stack2
----------------------------------------------------------------

-- newtype StackT s b e m a = StackT { runStackT :: Stack s b e -> STT s m a }

-- instance Monad m => Functor (StackT s b e m) where
--   fmap = liftM
-- instance Monad m => Applicative (StackT s b e m) where
--   pure = return
--   (<*>) = ap
-- instance Monad m => Monad (StackT s b e m) where
--   return = StackT . const . return
--   m >>= f = undefined

-- instance (TermMonad m f) => TermAlgebra (StackT s b e m) (StackF e :+: f) where
--   var = return
--   con (Inl (Pop k)) = StackT $ \stack -> liftST (popStack stack) >>= \x -> runStackT (k x) stack
--   con (Inl (Push x k)) = StackT $ \stack -> liftST (pushStack x stack)  >> runStackT k stack
--   con (Inr op) = StackT $ \stack -> STT $ \s -> con ((\f -> unSTT (f stack) s) <$> fmap runStackT op)

-- type CompSK s f b a = Free (StateF b :+: StackF s :+: f) a
-- -- just use StackT b s f a
-- -- data SK s m a = SK { unSK :: StackT (SK s m a) s m () }
-- data TwT m a = TwT {unTwT :: m a}

-- instance Monad m => Functor (TwT m) where
--   fmap = liftM
-- instance Monad m => Applicative (TwT m) where
--   pure = return
--   (<*>) = ap
-- instance Monad m => Monad (TwT m) where
--   return x = TwT $ return x
--   mx >>= f = undefined

-- -- simulation of nondeterminism with stack
-- -- nondet2stack :: Functor f => Free (NondetF :+: f) a -> CompSK (SK f a) f [a] ()
-- -- nondet2stack = fold gen (alg # fwd)
-- --   where
-- --     gen :: Functor f => a -> CompSK (SK f a) f [a] ()
-- --     gen x         = appendSK x popSK
-- --     alg :: Functor f => NondetF (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
-- --     alg Fail      = popSK
-- --     alg (Or p q)  = pushSK q p
-- --     fwd :: Functor f => f (CompSK (SK f a) f [a] ()) -> CompSK (SK f a) f [a] ()
-- --     fwd y = Op (Inr (Inr y))

-- instance (TermMonad m (StateF b :+: StackF s :+: f), Functor f)
--       => TermAlgebra (TwT m) (NondetF :+: f) where
--   var = return
--   con (Inl Fail) = popTwT

-- -- getSK :: Functor f => Free (StateF s :+: f) s
-- -- getSK = StateT $ \ s -> return (s, s)

-- -- putSK :: Functor f => s -> Free (StateF s :+: f ) ()
-- -- putSK s = Op . Inl $ Put s (return ())

-- -- popSK'' :: (TermMonad m (StateF b :+: StackF s :+: f)) => 

-- -- popSK' :: Functor f => CompSK s f b (Maybe s)
-- -- popSK' = Op . Inr . Inl $ Pop return

-- -- pushSK' :: Functor f => s -> CompSK s f b ()
-- -- pushSK' s = Op . Inr . Inl $ Push s (return ())

-- popTwT :: TwT m a
-- popTwT = undefined

-- -- popSK :: Functor f => CompSK (SK f a) f [a] ()
-- -- popSK = do
-- --   mtop <- popSK'
-- --   case mtop of
-- --     Nothing -> return ()
-- --     Just (SK top) -> top

-- -- pushSK :: Functor f => CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
-- -- pushSK q p = do
-- --   pushSK' (SK q)
-- --   p

-- -- appendSK :: Functor f => a -> CompSK (SK f a) f [a] () -> CompSK (SK f a) f [a] ()
-- -- appendSK x p = do
-- --   xs <- getSK
-- --   putSK (xs ++ [x])
-- --   p
