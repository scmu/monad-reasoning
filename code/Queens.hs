{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
             FlexibleInstances, MultiParamTypeClasses #-}

module Queens where

import Control.Arrow((***))
import Control.Monad
import Control.Monad.State (MonadState(..), State, runState)
import GHC.Base (Alternative(..))

import ListT

import Monad
import SolveLocal
import SolveGlobal

-- specification

select :: MonadPlus m => [a] -> m (a,[a]) {-"~~."-}
select []      =  mzero
select (x:xs)  =  return (x,xs) `mplus`
                  ((id *** (x:)) <$> select xs)

perm :: MonadPlus m => [a] -> m [a]
perm = unfoldM null select

ups, downs :: [Int] -> [Int]
ups    xs  = zipWith (+) [0..] xs
downs  xs  = zipWith (-) [0..] xs

safe     :: [Int] -> Bool
safe xs  = nodup (ups xs) && nodup (downs xs)

nodup :: Eq a => [a] -> Bool
nodup [] = True
nodup (x:xs) = not (x `elem` xs) && nodup xs

scanlp :: (b -> a -> b) -> b -> [a] -> [b]
scanlp oplus st []      = []
scanlp oplus st (x:xs)  = (st `oplus` x) : scanlp oplus (st `oplus` x) xs {-"~~."-}

safeAcc :: (Int, [Int], [Int]) -> [Int] -> Bool
safeAcc (i,us,ds) = all ok . scanlp oplus (i,us,ds)
  where (i,us,ds) `oplus` x = (i+1, (i+x:us), (i-x:ds))
        ok (i,(x:us),(y:ds)) = not (x `elem` us) && not (y `elem` ds)

  -- safe = safeAcc (0,[],[])

queensSpec :: MonadPlus m => Int -> m [Int]
queensSpec n = perm [0..n-1] >>= assert safe
      -- = unfoldM null select [0..n-1] >>=
      --         assert (all ok . scanlp oplus (0,[],[]))

-- solution using local state

queensLocal :: (MonadPlus m, MonadState (Int, [Int], [Int]) m) =>
               Int -> m [Int]
queensLocal n = solve null select ok oplus (0,[],[]) [0..n-1]
  where (i,us,ds) `oplus` x = (i+1, (i+x:us), (i-x:ds))
        ok (i,(x:us),(y:ds)) = not (x `elem` us) && not (y `elem` ds)
  -- try in GHCi:
  --    runSNv (queensLocal 8) undefined

-- solution using global state

queensGlobal :: (MonadPlus m, MonadState (Int, [Int], [Int]) m) =>
                Int -> m [Int]
queensGlobal n = solveR null select ok oplus ominus (0,[],[]) (0,[],[]) [0..n-1]
  where (i,us,ds) `oplus` x = (i+1, (i+x:us), (i-x:ds))
        (i,us,ds) `ominus` _ = (i-1, tail us, tail ds)
        ok (i,(x:us),(y:ds)) = not (x `elem` us) && not (y `elem` ds)
  -- try in GHCi:
  --    fst (runM (queensGlobal 8) undefined)


-- Definitions of monads used for this problem.

-- A non-det monad with local states.
-- Equivalent to what you get from StateT . List.

newtype SN s a = SN {runSN :: s -> [(a,s)]}

runSNv :: SN s a -> s -> [a]
runSNv m s = map fst (runSN m s)

instance Functor (SN s) where
  fmap f (SN m) = SN (map (f *** id) . m)

instance Applicative (SN s) where
  pure = return
  mf <*> mx = mf >>= \f ->
              mx >>= \x -> return (f x)

instance Monad (SN s) where
  return x = SN (\s -> [(x,s)])
  (SN m) >>= f =
    SN (\s -> concat [runSN (f y) s' | (y,s') <- m s])

instance Alternative (SN s) where
  empty = SN (const [])
  (SN m1) <|> (SN m2) =
    SN (\s -> m1 s ++ m2 s)

instance MonadPlus (SN s) where

instance MonadState s (SN s) where
  get = SN (\s -> [(s,s)])
  put t = SN (const [((),t)])

-- A global state monad

type M s a = ListT (State s) a

runM :: M s a -> s -> ([a],s)
runM m s = runState (runListT' m) s

runListT' :: (Monad m) => ListT m a -> m [a]
runListT' = foldListT cons (return [])
    where cons x m = (x:) <$> m


---

overwriteR s = \x -> putR s >> return x

m1, m2, m3, m4 :: M Int Int
-- m1 = (return 4 `mplus` return 5) >>= (\x -> putR 3 >> return x) >>= overwrite 6
-- m2 = putR 3 >> (return 4 `mplus` return 5) >>= overwrite 6 >>

m1 = (put 3 >> return 4) `mplus` (put 3 >> return 5)
m2 = put 3 >> ((return 4) `mplus` (return 5))

-- context (>> get >>= overwrite 8)
m3 = (return 4 `mplus` return 5) >>= (\x -> putR 3 >> return x)
m4 = putR 3 >> (return 4 `mplus` return 5)
-- try runM (m3 >> get >>= overwrite 8) 7 and
--     runM (m4 >> get >>= overwrite 8) 7
