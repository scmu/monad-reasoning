{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TypeOperators, UndecidableInstances, FunctionalDependencies, FlexibleContexts, GADTs, KindSignatures, RankNTypes #-}


module Fusion where

import Control.Algebra
import Control.Effect.NonDet
import Control.Effect.State
import Control.Effect.Reader
import Control.Carrier.State.Strict
import Control.Carrier.NonDet.Church

import FusionUtilities
import Codensity
import Data.Kind (Type)
import Control.Monad (liftM, ap, liftM2)
import Control.Applicative (liftA2)
import Data.Functor.Identity (Identity, runIdentity)
import Debug.Trace

action0 :: Has (State String) sig m => m String
action0 = return "hi"


action1 :: Has (State String) sig m => m ()
action1 = get >>= \ s -> put ("hello, " ++ s)

-- t :: Algebra sig m => m (String, ())
t = run $ runState "cat" action1

-- >>> t
-- ("hello, cat",())

action2 :: (Has (State String) sig m, Has (Reader Int) sig m) => m ()
action2 = do
  i <- ask
  put (replicate i '!')

action3 :: (Has (State Int) sig m, Has NonDet sig m, MonadPlus m) => m Int
action3 = do
  x <- get
  put (3::Int)
  return 1 <|> return x

t3 :: (Int, [Int])
t3 = run . runState (0::Int) . runNonDetA $ action3
t3' :: [(Int, Int)]
t3' = run . runNonDetA . runState (0::Int) $ action3

-- >>> t3
-- >>> t3'
-- (3,[1,0])
-- [(3,1),(3,0)]

----------------------------------------------------------------

valid :: [Int] -> Bool
valid [] = True
valid (q:qs) = valid qs && safe q 1 qs
filtr :: (Has NonDet sig m, MonadPlus m) => (a -> Bool) -> a -> m a
filtr p x = (if p x then return () else mzero) >> return x
choose :: (Has NonDet sig m, MonadPlus m) => [a] -> m a
choose = foldr (mplus . return) mzero
safe :: Int -> Int -> [Int] -> Bool
safe _ _ [] = True
safe q n (q1:qs) = and [q /= q1 , q /= q1 + n , q /= q1 - n , safe q (n+1) qs]
plus   :: (Int, [Int]) -> Int -> (Int, [Int])
plus   (c, sol) r = (c+1, r:sol)
minus   :: (Int, [Int]) -> Int -> (Int, [Int])
minus   (c, sol) r = (c-1, tail sol)

queens :: (Has (State (Int, [Int])) sig m, Has NonDet sig m, MonadPlus m) => Int -> m [Int]
queens n = put (0::Int, []::[Int]) >> loop
  where
    loop = do  s@(c, sol) <- get
               if c >= n then return sol
               else do  r <- choose [1..n]
                        filtr valid (r:sol)
                        put (s `plus` r)
                        loop

modifyR :: (Has (State s) sig m, Has NonDet sig m, MonadPlus m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev = modify next `mplus` side (modify prev)
side :: (Has NonDet sig m, MonadPlus m) => m a -> m b
side m = m >> mzero

-- queensR :: (MState (Int, [Int]) m, MNondet m) => Int -> m [Int]
queensR :: (Has (State (Int, [Int])) sig m, Has NonDet sig m, MonadPlus m) => Int -> m [Int]
queensR n = put (0::Int, []::[Int]) >> loop
  where
    loop = do  s@(c, sol) <- get
               if c >= n then return sol
               else do  r <- choose [1..n]
                        filtr valid (r:sol)
                        modifyR (`plus` r) (`minus` r)
                        loop

-- hLocal :: (Has (State s) sig m, Has NonDet sig m, MonadPlus m, Algebra sig m') => s -> m a -> m' (s, a)
hLocal :: (Alternative f, Applicative m) => s -> StateC s (NonDetC m) a -> m (f a)
hLocal s = fmap (fmap snd) . runNonDetA . runState s

hGlobal :: (Alternative f, Monad m) => s -> NonDetC (StateC s m) a -> m (f a)
hGlobal s = fmap snd . runState s . runNonDetA

queensLocal :: Int -> [[Int]]
-- queensLocal n = fmap snd . run . runNonDetA . runState (0::Int, []::[Int]) $ queens n
queensLocal n = run . hLocal (0::Int, []::[Int]) $ queens n

queensModify :: Int -> [[Int]]
queensModify n = run . hGlobal (0::Int, []::[Int]) $ queensR n

-- >>> queensLocal 4
-- >>> queensModify 4
-- [[3,1,4,2],[2,4,1,3]]
-- [[3,1,4,2],[2,4,1,3]]

----------------------------------------------------------------
-- local2global
----------------------------------------------------------------

-- TODO: use a new StateC to implement it


----------------------------------------------------------------
-- nondet2state
----------------------------------------------------------------

-- TODO: wrong

queensR' :: (Has (State (Int, [Int])) sig m, Has NonDet sig m, MonadPlus m) => Int -> m [Int]
queensR' n = put (0::Int, []::[Int]) >> loop
  where
    loop = do  s@(c, sol) <- get
               if c >= n then return sol
               else do  r <- choose [1..n]
                        filtr valid (r:sol)
                        modifyR (`plus` r) (`minus` r)
                        loop

queensState   :: Int -> [[Int]]
queensState n = let t = snd . runIdentity . runState (0, []) . runQwQ ((SS [] []) :: SS (StateC (Int, [Int]) Identity) [Int]) $ queensR n in t

-- >>> queensState 4
-- Prelude.undefined

instance Monad m => Alternative (QwQ m) where
  empty = trace "1" undefined
  (<|>) = trace "2" undefined
instance Monad m => MonadPlus (QwQ m) where


data SS f a = SS { resultsSS :: [a], stackSS :: [StateC2 (SS f a) f ()] }

newtype QwQ m a = QwQ {unQwQ :: StateC2 (SS m a) m ()}
instance (Monad m) => Functor (QwQ m) where
  fmap = liftM
instance (Monad m) => Applicative (QwQ m) where
  pure = return
  (<*>) = ap
instance Monad m => Monad (QwQ m) where
  return x = appendQwQ x popQwQ
  (QwQ (StateC2 m)) >>= f = QwQ . StateC2 $ \ ssmb -> undefined
  -- (>>=) = trace "3" undefined
  -- TODO: I don't know how to make it a monad.

runQwQ :: Monad m => SS m a -> QwQ m a -> m [a]
runQwQ s (QwQ x) = let t = fmap (resultsSS . fst) $ runState2 s x in t

instance (Algebra sig m) => Algebra (NonDet :+: sig) (Cod (QwQ m)) where
  alg hdl sig ctx = algCod alg' hdl sig ctx

alg' :: (Algebra sig m, Functor ctx)
     => Handler ctx n (QwQ m) -> (NonDet :+: sig) n a -> ctx () -> QwQ m (ctx a)
alg' hdl sig ctx = case sig of
  -- L (L Empty)  -> popSS' ctx
  L (L Empty)  -> popQwQ -- return type should be (ctx a)
  L (R Choose) -> let x = (True <$ ctx)
                  in let y = (False <$ ctx)
                  in pushQwQ (return x) (return y)
  -- R other      -> StateC2 $ \s -> thread (uncurry runState2 ~<~ hdl) other (s, ctx)
  -- sig n a -> QwQ m (ctx a)
  R other -> alg' hdl sig ctx -- NOTE: don't know if it is correct

getSS :: Monad f => StateC2 s f s
getSS = StateC2 $ \ s -> return (s, s)
putSS :: Monad f => s -> StateC2 s f ()
putSS s = StateC2 $ \ _ -> return (s, ())


popQwQ  :: Monad f => QwQ f a
popQwQ = QwQ $ popSS

pushQwQ :: Monad f => QwQ f a -> QwQ f a -> QwQ f a
pushQwQ (QwQ q) (QwQ p) = QwQ $ pushSS q p

appendQwQ :: Monad f => a
          -> QwQ f a
          -> QwQ f a
appendQwQ x (QwQ p) = QwQ $ appendSS x p

popSS  :: Monad f => StateC2 (SS f a) f ()
popSS = do
  SS xs stack <- getSS
  case stack of
    []       -> return ()
    op : ps  -> do
      putSS (SS xs ps); op

pushSS  :: Monad f
        => StateC2 (SS f a) f ()
        -> StateC2 (SS f a) f ()
        -> StateC2 (SS f a) f ()
pushSS q p = do
  SS xs stack <- getSS
  putSS (SS xs (q : stack)); p

appendSS  :: Monad f => a
          -> StateC2 (SS f a) f ()
          -> StateC2 (SS f a) f ()
appendSS x p = do
  SS xs stack <- getSS
  putSS (SS (xs ++ [x]) stack); p



