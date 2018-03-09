%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances,
             ScopedTypeVariables, MultiParamTypeClasses, KindSignatures #-}

module Queens where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State

import Utilities
import Monads
\end{code}
%endif

\section{Example: The |n|-Queens Problem}
\label{sec:queens}

Reasoning about monadic programs gets more interesting when more than one effect is involved.
Backtracking algorithms make good examples of programs that are stateful and non-deterministic, and the |n|-queens problem, also dealt with by Gibbons and Hinze~\shortcite{GibbonsHinze:11:Just}, is among the most well-known examples of backtracking.\footnote{Curiously, Gibbons and Hinze~\shortcite{GibbonsHinze:11:Just} did not finish their derivation and stopped at a program that exhaustively generates all permutations and tests each of them. Perhaps it was sufficient to demonstrate their point.}

In this section we present a specification of the problem, before transforming it into the form |unfoldM p f >=> assert (all ok . scanlp oplus st)| (whose components will be defined later), which is the general form of problems we will deal with in this pearl.
The specification is non-deterministic, but not stateful.
In the next few sections we will introduce state into the specification,
under different assumption of the interaction between non-determinism and state.

\subsection{Non-Determinism}

%format m1
%format m2

Since the |n|-queens problem will be specified by a non-deterministic program,
we discuss non-determinism before presenting the specification.
We assume two operators |mzero| and |mplus|: the former denotes failure, while |m `mplus` n| denotes that the computation may yield either |m| or |n|. What laws they should satisfy, however, can be a tricky issue. As discussed by Kiselyov~\shortcite{Kiselyov:15:Laws}, it eventually comes down to what we use the monad for. It is usually expected that |mplus| and |mzero| form a monoid. That is, |mplus| is associative, with |mzero| as its zero:
\begin{align*}
|(m `mplus` n) `mplus` k|~ &=~ |m `mplus` (n `mplus` k)| \mbox{~~,}\\
|mzero `mplus` m| ~=~ & |m| ~=~ |m `mplus` mzero| \mbox{~~.}
\end{align*}
It is also assumed that monadic bind distributes into |mplus| from the end,
while |mzero| is a left zero for |(>>=)|:
\begin{alignat}{2}
  &\mbox{\bf left-distributivity}:\quad &
  |(m1 `mplus` m2) >>= f| ~&=~ |(m1 >>= f) `mplus` (m2 >>= f)| \mbox{~~,}
  \label{eq:bind-mplus-dist}\\
  &\mbox{\bf left-zero}:\quad &
  |mzero >>= f| ~&=~ |mzero| \label{eq:bind-mzero-zero} \mbox{~~.}
\end{alignat}
%if False
\begin{code}
propBindMPlus f m1 m2  = (f =<< (m1 `mplus` m2)) === ((f =<< m1) `mplus` (f =<< m2))
propBindMZeroZero f    = (mzero >>= f) === mzero
\end{code}
%endif
% Properties \eqref{eq:bind-mplus-dist} and \eqref{eq:bind-mzero-zero} are called {\em left-distributivity} and {\em left-zero}.
Other properties regarding |mzero| and |mplus| will be introduced when needed.

\subsection{Specification}
\label{sec:queens-spec}

{\arraycolsep=1.4pt
\begin{figure}
\centering
\subfloat[]{
$\scriptsize
\begin{array}{rrrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\
0 & . & . & . & . & . & Q & . & .\\
1 & . & . & . & Q & . & . & . & .\\
2 & . & . & . & . & . & . & Q & .\\
3 & Q & . & . & . & . & . & . & .\\
4 & . & . & . & . & . & . & . & Q\\
5 & . & Q & . & . & . & . & . & .\\
6 & . & . & . & . & Q & . & . & .\\
7 & . & . & Q & . & . & . & . & .
\end{array}$
} %subfloat
\qquad
\subfloat[]{
$\scriptsize
\begin{array}{r||rrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\ \hline
0 & 0 & 1 & 2 & 3 & 4 & . & . & .\\
1 & 1 & 2 & 3 & 4 & . & . & . & .\\
2 & 2 & 3 & 4 & . & . & . & . & .\\
3 & 3 & 4 & . & . & . & . & . & .\\
4 & 4 & . & . & . & . & . & . & .\\
5 & . & . & . & . & . & . & . & 12\\
6 & . & . & . & . & . & . & 12& 13\\
7 & . & . & . & . & . & 12& 13& 14
\end{array}
$} %subfloat
\qquad
\subfloat[]{
$\scriptsize
\begin{array}{r||rrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\ \hline
0 & 0 &-1 & . & . & . &-5 &-6 &-7\\
1 & . & 0 &-1 & . & . & . &-5 &-6\\
2 & . & . & 0 &-1 & . & . & . &-5\\
3 & 3 & . & . & 0 & . & . & . & .\\
4 & 4 & 3 & . & . & 0 & . & . & .\\
5 & 5 & 4 & 3 & . & . & 0 & . & .\\
6 & 6 & 5 & 4 & 3 & . & . & 0 & .\\
7 & 7 & 6 & 5 & 4 & 3 & . & . & 0
\end{array}
$
} %subfloat
\caption{(a) This placement can be represented by |[3,5,7,1,6,0,2,4]|. (b) Up diagonals.
(c) Down diagonals.}
\label{fig:queens-examples}
\end{figure}
} %arraycolsep

The aim of the puzzle is to place |n| queens on a |n| by |n| chess board such that no two queens can attack each other. Given |n|, we number the rows and columns by |[0..n-1]|. Since all queens should be placed on distinct rows and distinct columns, a potential solution can be represented by a permutation |xs| of the list |[0..n-1]|, such that |xs !! i = j| denotes that the queen on the $i$th column is placed on the $j$th row (see Figure \ref{fig:queens-examples}(a)). In this representation queens cannot be put on the same row or column, and the problem is reduced to filtering, among permutations of |[0..n-1]|, those placements in which no two queens are put on the same diagonal. The specification can be written as a non-deterministic program:
\begin{spec}
queens :: N `mem` eps => Int -> Me eps [Int]
queens n = perm [0..n-1] >>= assert safe {-"~~,"-}
\end{spec}
%if False
\begin{code}
queens :: MonadPlus m => Int -> m [Int]
queens n = perm [0..n-1] >>= assert safe
\end{code}
%endif
where |perm| non-deterministically computes a permutation of its input, and the pure function |safe :: [Int] -> Bool| determines whether no queens are on the same diagonal. The monadic function |assert p x| returns |x| if |p x| holds, and fails otherwise:
\begin{spec}
assert :: N `mem` eps => (a -> Bool) -> a -> Me eps a
assert p x = guard (p x) >> return x {-"~~,"-}
\end{spec}
%if False
\begin{code}
assert :: MonadPlus m => (a -> Bool) -> a -> m a
assert p x = guard (p x) >> return x {-"~~,"-}
\end{code}
%endif
where |guard| is a standard monadic function defined by:
\begin{spec}
guard :: N `mem` eps => Bool -> Me eps ()
guard b = if b then return () else mzero {-"~~."-}
\end{spec}

This specification of |queens| generates all the permutations, before checking them one by one, in two separate phases. We wish to fuse the two phases and produce a faster implementation. The overall idea is to define |perm| in terms of an unfold, transform |assert safe| into a fold, and fuse the two phases into a {\em hylomorphism}~\cite{Meijer:91:Functional}. During the fusion, some non-safe choices can be pruned off earlier, speeding up the computation.

\paragraph{Permutation}
The monadic function |perm| can be written both as a fold or an unfold.
For this problem we choose the latter.
The function |select| non-deterministically splits a list into a pair containing one chosen element and the rest:
\begin{spec}
select :: N `mem` eps => [a] -> Me eps (a,[a]) {-"~~."-}
select []      =  mzero
select (x:xs)  =  return (x,xs) `mplus` ((id *** (x:)) <$> select xs) {-"~~,"-}
\end{spec}
%if False
\begin{code}
select :: MonadPlus m => [a] -> m (a,[a]) {-"~~."-}
select []      =  mzero
select (x:xs)  =  return (x,xs) `mplus` ((id *** (x:)) <$> select xs) {-"~~."-}
\end{code}
%endif
where |(f *** g) (x,y) = (f x, g y)|.
For example, |select [1,2,3]| yields one of |(1,[2,3])|, |(2,[1,3])| and |(3,[1,2])|. The function call |unfoldM p f y| generates a list |[a]| from a seed |y :: b|. If |p y| holds, the generation stops. Otherwise an element and a new seed is generated using |f|. It is like the usual |unfoldr| apart from that |f|, and thus the result, is monadic:
\begin{spec}
unfoldM :: (b -> Bool) -> (b -> Me eps (a,b)) -> b -> Me eps [a]
unfoldM p f y  | p y        = return []
               | otherwise  = f y >>= \(x,z) -> (x:) <$> unfoldM p f z {-"~~."-}
\end{spec}
%if False
\begin{code}
unfoldM :: Monad m => (b -> Bool) -> (b -> m (a,b)) -> b -> m [a]
unfoldM p f y  | p y        = return []
               | otherwise  = f y >>= \(x,z) -> (x:) <$> unfoldM p f z {-"~~."-}
\end{code}
%endif
Given these definitions, |perm| can be defined by:
\begin{spec}
perm :: N `mem` eps => [a] -> Me eps [a]
perm = unfoldM null select {-"~~."-}
\end{spec}
%if False
\begin{code}
perm :: MonadPlus m => [a] -> m [a]
perm = unfoldM null select {-"~~."-}
\end{code}
%endif

\subsection{Safety Check in a |scanl|}

We have yet to defined |safe|.
Representing a placement as a permutation allows an easy way to check whether two queens are put on the same diagonal.
An 8 by 8 chess board has 15 {\em up diagonals} (those running between bottom-left and top-right). Let them be indexed by |[0..14]| (see Figure \ref{fig:queens-examples}(b)).
If we apply |zipWith (+) [0..]| to a permutation, we get the indices of the up-diagonals where the chess pieces are placed.
Similarly, there are 15 {\em down diagonals} (those running between top-left and bottom right).
By applying |zipWith (-) [0..]| to a permutation, we get the indices of their down-diagonals (indexed by |[-7..7]|.
See Figure \ref{fig:queens-examples}(c)).
A placement is safe if the diagonals contain no duplicates:
% A safe placement is one whose up and down diagonals contains no duplicates:
\begin{code}
ups, downs :: [Int] -> [Int]
ups    xs  = zipWith (+) [0..] xs  {-"~~,"-}
downs  xs  = zipWith (-) [0..] xs  {-"~~,"-}

safe     :: [Int] -> Bool
safe xs  = nodup (ups xs) && nodup (downs xs) {-"~~,"-}
\end{code}
where |nodup :: Eq a => [a] -> Bool| determines whether there is no duplication in a list.
%if False
\begin{code}
nodup :: Eq a => [a] -> Bool
nodup [] = True
nodup (x:xs) = not (x `elem` xs) && nodup xs
\end{code}
%endif

The eventual goal is to transform |assert safe| into a |foldr|, to be fused with |perm|, an unfold that generates a list from left to right.
In order to do so, it helps if |safe| can be expressed in a computation that processes the list left-to-right, that is, a |foldl| or a |scanl|.
To derive such a definition we use the standard trick --- introducing accumulating parameters, and generalising |safe| to |safeAcc| below:
\begin{code}
safeAcc :: (Int, [Int], [Int]) -> [Int] -> Bool
safeAcc (i,us,ds) xs =  nodup us' &&  nodup ds' &&
                        all (`notelem` us) us' && all (`notelem` ds) ds' {-"~~,"-}
  where  us'  = zipWith (+) [i..] xs
         ds'  = zipWith (-) [i..] xs {-"~~."-}
\end{code}
It is a generalisation because |safe = safeAcc (0,[],[])|.
By plain functional calculation, one may conclude that |safeAcc| can be defined using a variation of |scanl|:
\begin{spec}
safeAcc (i,us,ds) = all ok . scanlp oplus (i,us,ds) {-"~~,"-}
  where  (i,us,ds) `oplus` x  = (i+1, (i+x : us), (i-x : ds))
         ok (i,(x:us), (y:ds)) = x `notelem` us && y `notelem` ds {-"~~,"-}
\end{spec}
%if False
\begin{code}
safeAcc' :: (Int, [Int], [Int]) -> [Int] -> Bool
safeAcc' (i,us,ds) = all ok . scanlp oplus (i,us,ds) {-"~~,"-}
  where  (i,us,ds) `oplus` x  = (i+1, (i+x : us), (i-x : ds))
         ok (i,(x:us), (y:ds)) = x `notelem` us && y `notelem` ds {-"~~,"-}
\end{code}
%endif
where |all p = foldr (&&) True . map p| and |scanlp| is like |scanl|, but applies |foldl| to all non-empty prefixes of a list:
\begin{code}
scanlp :: (b -> a -> b) -> b -> [a] -> [b]
scanlp oplus st []      = []
scanlp oplus st (x:xs)  = (st `oplus` x) : scanlp oplus (st `oplus` x) xs {-"~~."-}
\end{code}

Operationally, |safeAcc| examines the list from left to right, while keeping a state |(i,us,ds)|, where |i| is the current position being examined, while |us| and |ds| are respectively indices of all the up and down diagonals encountered so far. Indeed, in a function call |scanlp oplus st|, the value |st| can be seen as a ``state'' that is explicitly carried around. This naturally leads to the idea: can we convert a |scanlp| to a monadic program that stores |st| in its state? This is the goal of the next section.

As a summary of this section, after defining |queens|, we have transformed it into the following form:
%if False
\begin{code}
probSpec :: MonadPlus m =>
  (b -> Bool) -> (b -> m (c, b)) -> (a -> Bool) ->
  (a -> c -> a) -> a -> b -> m [c]
probSpec p f ok oplus st =
\end{code}
%endif
\begin{code}
  unfoldM p f >=> assert (all ok . scanlp oplus st)  {-"~~."-}
\end{code}
This is the form of problems we will consider for the rest of this paper: problems whose solutions are generated by an monadic unfold, before being filtered by an |assert| that takes the result of a |scanlp|.
