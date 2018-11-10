%% This section is not included in the paper anymore.
%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}

module BacktrackGlobal where

import Prelude hiding ((>>))
import Control.Monad hiding ((>>))
import Control.Monad.State hiding ((>>))

import ListT  -- use option -i../../code

import Utilities
import Monads
import Queens
import StateLocal
import NondetGlobal

\end{code}
%endif

\section{Backtracking Algorithms using a Global State}

Having developed the tools we need in Section \ref{sec:nd-state-global}, we again look back at our goal: developing algorithms for problems of the form
|unfoldM p f >=> assert (all ok . scanlp oplus st)|.

\subsection{The Derivation}
\label{sec:backtrack-g-der}

Following the trail of the first derivation, the first step would be to turn |scanlp oplus st| to a monadic scan.
One might go for something like |return (scanlp oplus st xs) = put st >> foldr ...|, but that will not work --- as we have mentioned in Section \ref{sec:state-restoring}, |return x| can not be equal to any term starting with |(put st >>)|.

To make such equality possible, we consider prefixing |return (scanlp oplus st xs)| with a |(putR fin >>)|, where |fin| is any state that subsequent computation will run in. We also define a variation of |scanlM| that takes this additional state:
\begin{spec}
scanlMR :: {N, S s} `sse` eps => (s -> a -> s) -> s -> s -> [a] -> Me eps [s]
scanlMR oplus st fin xs = putR st >> foldr otimes (putR fin >> return []) xs
  where x `otimes` m =  get >>= \st -> ((st `oplus` x):) <$> (putR (st `oplus` x) >> m) {-"~~."-}
\end{spec}
%if False
\begin{code}
scanlMR :: (MonadPlus m, MonadState s m) =>
  (s -> a -> s) -> s -> s -> [a] -> m [s]
scanlMR oplus st fin xs = putR st >> foldr otimes (putR fin >> return []) xs
  where x `otimes` m =  get >>= \st -> ((st `oplus` x):) <$> (putR (st `oplus` x) >> m) {-"~~."-}
\end{code}
%endif
The global-state counterparts Theorem \ref{lma:scanl-loop} and \ref{lma:foldr-guard-fusion} are stated below.
Note the duality: in Theorem \ref{lma:scanl-loop} we use |protect| to remember the initial state, while in here we supply a final state.
\begin{theorem}\label{thm:putR-scanlp-scanM}
For all |oplus :: (s -> a -> s)|, |fin, st :: s|, and |xs :: [a]|,
%if False
\begin{code}
putRScanlpScanM :: (MonadPlus m, MonadState s m) =>
  s -> (s -> a -> s) -> s -> [a] -> m [s]
putRScanlpScanM fin oplus st xs =
\end{code}
%endif
\begin{code}
  putR fin >> return (scanlp oplus st xs) === scanlMR oplus st fin xs {-"~~."-}
\end{code}
\end{theorem}

\begin{theorem}\label{thm:putR-assert-scanlp-foldr} The following is true:
%if False
\begin{code}
putRAssertScanlpFoldr :: (MonadPlus m, MonadState s m) =>
  s -> (s -> Bool) -> (s -> a -> s) -> s -> [a] -> m [a]
putRAssertScanlpFoldr fin ok oplus st xs =
\end{code}
%endif
\begin{code}
  putR fin >> assert (all ok . scanlp oplus st) xs ===
     putR st >> foldr odot (putR fin >> return []) xs {-"~~."-}
    where x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                        putR (st `oplus` x) >> ((x:) <$> m) {-"~~."-}
\end{code}
\end{theorem}

Furthermore, one can prove that |foldr odot (putR fin >> m) xs| is state-restoring, and therefore,
\begin{lemma}\label{lma:odot-ocirc} Let |ominus| be such that |(st `oplus` x) `ominus` x = st| for all |st| and |x|. We have
    |foldr odot (putR fin >> m) = foldr ocirc (putR fin >> m)|,
where |ocirc| is defined by:
%if False
\begin{code}
odotOcirc :: (MonadPlus m, MonadState s m) =>
  s -> (s -> a -> s) -> (s -> a -> s) -> (s -> Bool)
  -> m [a] -> [a] -> m [a]
odotOcirc fin oplus ominus ok m =
     foldr odot (putR fin >> m) === foldr ocirc (putR fin >> m)
 where
  x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                putR (st `oplus` x) >> ((x:) <$> m)
\end{code}
%endif
\begin{code}
  x `ocirc` m =  modifyR (`oplus` x) (`ominus` x) >>
                 (get >>= (guard . ok)) >>
                 ((x:) <$> m) {-"~~."-}
\end{code}
\end{lemma}

\paragraph{Derivation Outline} We can now carry out the derivation. For reason stated above, we start with a slightly altered specification, attaching |(putR fin >>)| before the unfold:
\begin{spec}
 putR fin >> unfoldM p f z >>= assert (all ok . scanlp oplus st) {-"~~."-}
\end{spec}
The derivation of the algorithm thus goes:
%if False
\begin{code}
probStateGlobDer   :: (MonadPlus m, MonadState s m) =>
     s -> (b -> Bool) -> (b -> m (a, b)) -> (s -> Bool)
     -> (s -> a -> s) -> (s -> a -> s) -> (a -> m [a] -> m [a])
     -> s -> b -> m [a]
probStateGlobDer fin p f ok oplus ominus ocirc st z =
\end{code}
%endif
\begin{code}
       putR fin >> unfoldM p f z >>= assert (all ok . scanlp oplus st)
  ===    {- |putR| commutes with non-determinism -}
       unfoldM p f z >>= \ys -> putR fin >> assert (all ok . scanlp oplus st) ys
  ===    {- Theorem \ref{thm:putR-scanlp-scanM}, \ref{thm:putR-assert-scanlp-foldr}, and Lemma \ref{lma:odot-ocirc} -}
       unfoldM p f z >>= \ys -> putR st >> foldr ocirc (putR fin >> return []) ys
  ===    {- |putR| commutes with non-determinism -}
       putR st >> unfoldM p f z >>= foldr ocirc (putR fin >> return [])
  ===    {- hylo-fusion Theorem \ref{thm:hylo-fusion} -}
       putR st >> hyloM ocirc (putR fin >> return []) p f z {-"~~."-}
\end{code}
The proof that |ocirc| meets the requirement for Theorem \ref{thm:hylo-fusion} is a routine one. In conclusion, we define:
\begin{spec}
solveR ::  (b -> Bool) -> (b -> Me {N,S s} (a, b)) -> (s -> Bool) ->
           (s -> a -> s) -> (s -> a -> s) -> s -> s -> b -> Me {N,S s} [a]
solveR p f ok oplus ominus st fin z = putR st >> hyloM ocirc (putR fin >> return []) p f z
  where x `ocirc` m =  modifyR (`oplus` x) (`ominus` x) >>
                       (get >>= (guard . ok)) >>
                       ((x:) <$> m) {-"~~."-}
\end{spec}
%if False
\begin{code}
solveR :: (MonadState s m, MonadPlus m) =>
  (b -> Bool) -> (b -> m (a, b)) -> (s -> Bool) ->
  (s -> a -> s) -> (s -> a -> s) -> s -> s -> b -> m [a]
solveR p f ok oplus ominus st fin z =
   putR st >> hyloM ocirc (putR fin >> return []) p f z
  where x `ocirc` m = modifyR (`oplus` x) (`ominus` x) >>
                      (get >>= (guard . ok)) >>
                      ((x:) <$> m)
\end{code}
%endif
\begin{theorem}
If all the properties in this section hold in addition to the monad laws,  |(not . p)? . snd . (=<<) . f| is well-founded, and |(st `oplus` x) `ominus` x = x|, we have
\begin{spec}
  putR fin >> unfoldM p f z >>= assert (all ok . scanlp oplus st) ===
    solveR p f ok oplus ominus st fin z {-"~~."-}
\end{spec}
\end{theorem}
% Expanding the definitions, we get:
% \begin{spec}
% solveR z = putR st >> solveBody z
% solveBody z  | p z        =  putR fin >> return []
%              | otherwise  =  f z >>= \(x,w) ->
%                              modifyR (`oplus` x) (`ominus` x) >>
%                              (get >>= (guard . ok)) >>
%                              ((x:) <$> solveBody w) {-"~~."-}
% \end{spec}
%if False
\begin{code}
solveBody :: (MonadPlus m, MonadState a m) => t1 -> m [t]
solveBody z  | p z        =  putR fin >> return []
             | otherwise  =  f z >>= \(x,w) ->
                             modifyR (`oplus` x) (`ominus` x) >>
                             (get >>= (guard . ok)) >>
                             ((x:) <$> solveBody w) {-"~~."-}
    where p = undefined
          f = undefined
          oplus = undefined
          ominus = undefined
          fin = undefined
          ok = undefined
\end{code}
%endif

\subsection{Example: A Sudoku Solver}

To demonstrate an application where an array is used in the state, we implemented a backtracking, brute-force Sudoku solver. For those who have not yet heard of the puzzle: given is a 9 by 9 grid, some cells being blank and some filled with numbers. The aim is to fill in the blank cells such that each column, each row, and each of the nine 3 by 3 sub-grids (also called ``boxes'') contains all of the digits from 1 to 9.

In the specification, we simply try, for each blank cell, each of the 9 digits. Define:
\begin{spec}
allChoices :: N `mem` eps => Int -> Me eps [Int]
allChoices = unfoldM (0==) (\n -> liftList [1..9] >>= \x -> return (x,n-1)) {-"~~,"-}
\end{spec}
%if False
\begin{code}
allChoices :: Monad m => Int -> ListT m [Int]
allChoices = unfoldM (0==) (\n -> liftList [1..9] >>= \x -> return (x,n-1))
 {-"~~,"-}
\end{code}
%endif
where |liftList :: N `mem` eps => [a] => Me eps a| non-deterministically returns an element in the given list, such that |allChoices n| returns a list of length |n| whose elements are independently chosen from |[1..9]|. If a given grid contains |n| blank cells, a list of length |n| represents a proposed solution.

To check whether a solution is valid, we inspect the list left-to-right,  keeping a state. It is sufficient letting the state be the current partially filled grid. For convenience, and also for simplifying the definition of |oplus| and |ominus|, we also maintain a zipper of positions:
\begin{spec}
type Pos = (Int, Int) {-"~~,\qquad"-}  type Grid = Array Pos Entry{-"~~,"-}
type Entry = Int{-"~~,"-}              type State = (Grid, [Pos], [Pos]) {-"~~."-}
\end{spec}
Therefore, in the state |(grid, todo, done)|, |grid| is an array representing the current status of the grid (an empty cell being filled |0|), |todo| is a list of blank positions to be filled, and |done| is the list of positions that were blank but are now filled.

We assume a function |collisions :: Pos -> [Pos]| which, given a position, returns a list of positions that should be checked. That is, |collisions i| returns all the positions that are on the same row, column, and in the same box as~|i|. With that, we may define:
\begin{spec}
safe st = all ok . scanlp oplus st {-"~~,"-}
  where  (grid, i:is, js) `oplus`  x  = (grid // [(i,x)], is, i:js) {-"~~,"-}
         ok (grid, is, i:js) = all ((grid ! i) /=) (map (grid !) (collisions i)) {-"~~,"-}
\end{spec}
where |(!)| and |(//)| respectively performs array reading and updating. The reverse operation of |oplus| is |(grid, is, i:js) `ominus` x  = (grid // [(i,0)], i:is, js)|. A program solving the puzzle can be specified by
\begin{spec}
sudoku grid = putR fin >> allChoices (length empties) >>= assert (safe initState) {-"~~,"-}
   where initState = (grid, empties, []) {-"~~,"-}
\end{spec}
where |grid| is the array representing the initial puzzle and |empties| are the blank positions.

By the calculation in Section \ref{sec:backtrack-g-der}, |solve| can be transformed to a hylomorphism.
The actual implementation is slightly complicated by conversion from |Array| to |STUArray|, the array that supports in-place update in Haskell. In the code below, |guardNoCollision| is specified by |get >>= (guard . ok)|. Operations |modNext x| and |modPrev x| are respectively specified by |modify (`oplus` x)| and |modify (`ominus` x)|, but alters the array directly.
\begin{spec}
sudoku grid  = putR initState >> sudokuBody (length empties) {-"~~,"-}
sudokuBody 0  =  putR fin >> return []
sudokuBody n  =  liftList [1..9] >>= \x ->
                 modifyR (modNext x) (modPrev x) >>
                 guardNoCollision x >>
                 (x:) <$> solve (n-1) {-"~~."-}
\end{spec}
The handle of an |STUArray| is usually stored in a reader monad. The actual monad we use is constructed by
\begin{spec}
type Grid s   = STUArray s Pos Entry {-"~~,"-}
type SudoM s  = ListT (StateT ([Pos], [Pos]) (ReaderT (Grid s) (ST s))) {-"~~,"-}
\end{spec}
where |ListT| is one of the correct implementations~\cite{Gale:07:ListT}.

This Sudoku solver is not very effective --- a puzzle rated as ``hard'' could take minutes to solve. For Sudoku, naive brute-force searching does not make a good algorithm. In comparison, Bird~\shortcite{Bird:10:Pearls} derived a purely functional program, based on constraint refining, that is able to solve the same puzzle in an instant. Nevertheless, the algorithm in this section does the job, and demonstrates that our pattern of derivation is applicable.
