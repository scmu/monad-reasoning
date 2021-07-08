%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

import Background

import Data.Array.ST
import Control.Monad.ST
import qualified Control.Monad.ST.Trans as T
import Control.Monad.ST.Trans.Internal (liftST)
import Data.STRef
import Control.Monad (ap, join, liftM)
import Control.Monad.Trans (lift)
\end{code}
%endif
\section{Extensions}
\label{sec:extensions}

\todo{Intro}

\subsection{Mutable State}
\label{sec:mutable-state}

Performance-wise, it might be better to have an algorithm with mutable state,
instead of the built-in |State| monad that keeps track of state in a pure way.

It is easy to show that a mutable state handler can easily be defined in 
Haskell. 
We will use a stack to implement mutable state.
\begin{code}
type Index = Int
data Stack s a = Stack {   getStack  ::  STRef s   (STArray s Index a), 
                           getSize   ::  STRef s   Index }
\end{code}
This stack consists of two reference cells, one with a (mutable) array 
containing the data, another with the size of the stack. 
The size of the stack is the amount of allocated space that is actually
filled with data.
Both the |STRef| and the |STArray| datatypes come from Haskell's 
|Control.Monad.ST| library that implements the strict |ST| monad.

\todo{operations one can do with the stack in Figure}
\todo{explain diff between allocated space and size}

\begin{code}
growStack :: Index -> [a] -> ST s (Stack s a)
growStack space elems = do
    stack     <- newListArray (0, space) elems
    sizeRef   <- newSTRef (length elems)
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)

emptyStack :: ST s (Stack s a)
emptyStack = do
    stack     <- newArray_ (0, 1)
    sizeRef   <- newSTRef 0
    stackRef  <- newSTRef stack
    return (Stack stackRef sizeRef)

pushStack :: a -> Stack s a -> ST s ()
pushStack x (Stack stackRef sizeRef) = do
    stack       <- readSTRef stackRef
    size        <- readSTRef sizeRef
    (_, space)  <- getBounds stack
    writeSTRef sizeRef (size + 1)
    if size < space then writeArray stack size x
        else do
            elems              <- getElems stack
            Stack stackRef' _  <- growStack (space * 2) elems
            stack'             <- readSTRef stackRef'
            writeArray  stack'   size x
            writeSTRef  stackRef stack'

popStack :: Stack s a -> ST s (Maybe a)
popStack (Stack stackRef sizeRef) = do
    stack  <- readSTRef stackRef
    size   <- readSTRef sizeRef
    if size == 0 then return Nothing
        else do 
            writeSTRef sizeRef (size - 1)
            Just <$> readArray stack (size - 1)

\end{code}

The functor |StackF| represents the action of
pushing to and popping from the stack.
This is very similar to the |StateF| functor, except for the |Maybe| in the
codomain of the |Pop| element. 
This optional value may be |Nothing| when the stack is empty.
\begin{code}
data StackF e a = Push e a | Pop (Maybe e -> a)
\end{code}
%if False
\begin{code}
instance Functor (StackF elem) where
    fmap f (Push x k) = Push x (f k)
    fmap f (Pop k) = Pop (f . k)
\end{code}
%endif

The handler for mutable state |hStack| then works as follows:
\todo{Inr case}
\todo{example ST transformer}
\begin{code}
hStack :: forall s e a f . (Functor f) 
       => Free (StackF e :+: f) a 
       -> Stack s e 
       -> T.STT s (Free f) a
hStack = fold gen alg
  where 
    gen = const . return
    alg (Inl (Push x k))  stack = liftST (pushStack x stack)  >> k stack
    alg (Inl (Pop k))     stack = liftST (popStack stack)     >>= \x -> k x stack
    alg (Inr y)           stack = lift $ Op (fmap (T.runSTT @s . ($ stack)) y)
\end{code}


%if False
\begin{code}
showStack :: Show a => Stack s a -> ST s String
showStack (Stack stackRef sizeRef) = do
    stack <- readSTRef stackRef
    elems <- getElems stack
    size  <- readSTRef sizeRef
    return $ show (take size elems)

test = runST $ do
    stack <- emptyStack
    pushStack (5 :: Int) stack
    pushStack 6 stack
    pushStack 7 stack
    pushStack 8 stack
    Just x <- popStack stack
    Just y <- popStack stack
    Just z <- popStack stack
    Just q <- popStack stack
    return [x, y, z, q]
\end{code}
%endif





% \subsection{Undo Semantics}
% \label{sec:undo-semantics}

% \subsection{Cut Semantics}
% \label{sec:cuts}

% Prolog interpreters implement more complex control flow constructs 
% such as cuts.

% \todo{Sth on left zero where cut operator is global, equivalence with idempotent operation + dist law}

% \begin{code}
% type CutList a  = Idem [a]
% data Idem    a  = Ret a | Flag a 

% instance Functor Idem where
%     fmap = liftM

% instance Applicative Idem where
%     pure = return
%     (<*>) = ap

% instance Monad Idem where
%     return a = Ret a
%     Ret a >>= f = f a
%     Flag a >>= f = Flag (unIdem (f a))

% unIdem :: Idem a -> a
% unIdem (Ret  x)   =  x
% unIdem (Flag x)   =  x

% dist :: [Idem a] -> Idem [a]
% dist [] = Ret []
% dist (Ret x : xs) = fmap ((:) x) (dist xs)
% dist (Flag x : xs) = Flag [x]
% \end{code}

% \todo{argue that scope is not an algebraic operation}

% \begin{code}
% fromList :: [a] -> CutList a
% fromList xs = Ret xs

% append :: CutList a -> CutList a -> CutList a
% append (Ret xs) ys = fmap ((++) xs) ys
% append (Flag xs) _ = Flag xs

% close :: CutList a -> CutList a 
% close = Flag . unIdem

% reopen :: CutList a -> CutList a 
% reopen = Ret . unIdem
% \end{code}

% \todo{Cut k is like cut with a continuation k}

% \begin{code}
% data CutF a = Cut a | Scope a

% instance Functor CutF where
%     fmap f (Cut x) = Cut (f x)
%     fmap f (Scope x) = Scope (f x)

% data FreeS f g a = Return a 
%                  | Call (f (FreeS f g a)) 
%                  | Enter (g (FreeS f g (FreeS f g a)))

% instance (Functor f, Functor g) => Functor (FreeS f g) where
%   fmap = liftM

% instance (Functor f, Functor g) => Applicative (FreeS f g) where
%   pure  = return
%   (<*>) = ap

% instance (Functor f, Functor g) => Monad (FreeS f g) where
%   return = Return
%   (>>=) (Return x)  f = f x 
%   (>>=) (Call op)   f = Call (fmap (>>= f) op) 
%   (>>=) (Enter op)  f = Enter (fmap (fmap (>>= f)) op)

% data Alg f g a = Alg { call   :: f a -> a
%                      , enter  :: g (FreeS f g a) -> a }

% foldS :: (Functor f, Functor g) => (a -> b) -> Alg f g b -> FreeS f g a -> b
% foldS gen alg (Return  x)   = gen x
% foldS gen alg (Call    op)  = (call alg  . fmap (foldS gen alg)) op
% foldS gen alg (Enter   op)  = (enter alg . fmap (fmap (foldS gen alg))) op

% hCut :: (Functor f, Functor g) 
%      => FreeS (NondetF :+: f) (CutF :+: g) a 
%      -> FreeS f g (CutList a)
% hCut = foldS gen alg
%   where
%     gen :: a -> FreeS f g (CutList a) 
%     gen = Return . return . return 
%     alg :: (Functor f, Functor g) => Alg (NondetF :+: f) (CutF :+: g) (FreeS f g (CutList a))
%     alg = Alg call enter
%       where
%         call :: (Functor f, Functor g) => (NondetF :+: f) (FreeS f g (CutList a)) -> FreeS f g (CutList a)
%         call (Inl Fail)     = Return (return []) --Return [] 
%         call (Inl (Or p q)) = append <$> p <*> q -- (++) <$> p <*> q
%         call (Inr y)        = Call y 
%         enter :: (Functor f, Functor g) 
%               => (CutF :+: g) (FreeS (NondetF :+: f) (CutF :+: g) (FreeS f g (CutList a))) 
%               -> (FreeS f g (CutList a))
%         enter = undefined
%         -- enter (Inl (Cut op)) = _ op
%         -- enter (Inl (Scope op))  = _ op
%         -- enter (Inr y) = Enter (fmap (fmap unIdem . hCut) y)

% \end{code}



















