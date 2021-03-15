{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}

import Control.Monad
import Control.Monad.ST
import Control.Applicative
import qualified Data.Vector.Unboxed.Mutable as V
import Data.Vector.Unboxed.Mutable (STVector)
import Data.STRef

-- vec [3,0,0,0,0,0,0,0] @ 1

-- Immutable state
--class State s a where
--  get :: State s s 
--  put :: s -> State s ()

--class MutVecState e a where 
--  peek :: Int -> MutVecState e e 
--  poke :: Int -> e -> MutVecState e ()

{-
peek-peek 
peek-poke 
poke-peek 
poke-poke 

-}
--class Stack e a where 
--  elems :: Stack e [e]
--  push  :: e -> Stack e ()
--  pop   :: Stack e (Maybe e)

{-
push-pop : do {push x >> pop} = return (Just x)
-}

-- Visie wat we willen doen
-- workflow
-- probleem: speedup aantonen gaat moeilijk met n-queens
--  -> testen of het werkelijk een probleem is met n-queens
--  -> zoeken naar een (beter?) voorbeeld
-- redeneren zelf: immutable global state -> mutable global state 
--   (interface beperkt tot de datastructuur die je wilt gebruiken (bv stack)
--   + benchmarking
-- integreren werk van willem en aram
-- paper xhixuan inspiratie

{-
Fusion aanpak:
  1. maak implementaties voor local en global state 
  2. bewijs dat die implementaties aan hun laws voldoen
  3. toon aan dat hGlobal . trans = hLocal

-}

{-


-}

data Free f a where 
  Ret :: a -> Free f a 
  Op  :: f (Free f a) -> Free f a 
  deriving (Functor)

fold :: Functor f => (a -> r) -> (f r -> r) -> Free f a -> r 
fold gen alg (Ret x) = gen x 
fold gen alg (Op op) = alg $ fmap (fold gen alg) op

instance Functor f => Applicative (Free f) where 
  pure = return
  (<*>) = ap

instance Functor f => Monad (Free f) where
  return = Ret 
  m >>= k = fold k Op m

data (:+:) f g a = Inl (f a) | Inr (g a)
  deriving (Functor, Show)

data NondetF a where 
  (:|) :: a -> a -> NondetF a 
  Fail :: NondetF a 

data StackF elem a where
  -- voegt element toe op top 
  Push :: elem -> a -> StackF elem a

  -- verwijdert top element
  Pop  :: (Maybe elem -> a) -> StackF elem a

  -- neem een kijkje in de stack
  Spy  :: Int -> (Maybe elem -> a) -> StackF elem a

  Len  :: (Int -> a) -> StackF elem a
  -- Reserve :: Int -> StackF elem () -- Reserve 8
  deriving Functor

hStack :: forall f a elem. Functor f
       => Free (StackF elem :+: f) a
       -> [elem] -> Free f ([elem] , a)
  -- TODO eens proberen:
  -- -> Free (StateF [elem] :+: f) a
hStack = fold gen alg
  where
    gen :: a -> [elem] -> Free f ([elem] , a)
    gen x stack = return (stack , x)

    alg :: (StackF elem :+: f) ([elem] -> Free f ([elem] , a))
        -> [elem] -> Free f ([elem] , a)
    alg (Inl (Push x k)) stack = k (x : stack)
    alg (Inl (Pop k)   ) stack = case stack of
      (x:xs) -> k (Just x) xs
      []     -> k Nothing []
    alg (Inl (Spy i k) ) stack = k (stack !? i) stack
    alg (Inl (Len k)   ) stack = k (length stack) stack
    alg (Inr op        ) stack = Op $ fmap ($ stack) op

hStackMut' :: forall a s elem. Free (StackF elem) a
           -> STVector s elem -> ST s a
hStackMut' = fold gen alg
  where
    gen :: a -> (STVector s elem -> ST s a)
    gen x = const $ return x

    alg :: StackF elem (STVector s elem -> ST s a)
        -> (STVector s elem -> ST s a)
    alg (Push x k) stack = do
      stack' <- unsafeGrow stack 1
      
      k stack'
      

(??) :: Functor f => f (a -> b) -> (a -> f b)
fab ?? a = fmap ($ a) fab

foo :: Functor f => f (a -> b) -> (a -> f b)
foo f = \a -> fmap ($ a) f

(!?) :: [a] -> Int -> Maybe a
(x:xs) !? 0 = Just x
(_:xs) !? n = xs !? (n-1)
_      !? _ = Nothing
      

main = putStrLn "all good"
