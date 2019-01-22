%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances,
             ScopedTypeVariables, MultiParamTypeClasses #-}

module StateLocal where

import GHC.Base (Alternative(..))
import Control.Monad
import Control.Monad.State
import Control.Arrow ((***))

import Utilities
import Monads
import Queens
import MonadicScanL
\end{code}
%endif

\section{Monadic Hylomorphism}
\label{sec:nd-state-local}

To recap what we have done: for all |p|, |ok|, |oplus|, |st|, and |f :: b -> Me N (a,b)|,
%if False
\begin{code}
stateLocalDer1 p f z ok oplus st odot xs =
\end{code}
%endif
\begin{code}
      unfoldM p f z >>= assert (all ok . scanlp oplus st)
 ===    {- Corollary \ref{thm:assert-scanlp-foldr}, with |odot| defined as in Theorem \ref{lma:foldr-guard-fusion} -}
      unfoldM p f z >>= \xs -> protect (put st >> foldr odot (return []) xs)
 ===   {- nondeterminism commutes with state -}
      protect (put st >> unfoldM p f z >>= foldr odot (return [])) {-"~~."-}
\end{code}
% Define |queensBody xs = perm xs >>= foldr odot (return [])|.
% We have
% \begin{spec}
% queens n =  get >>= \ini -> put (0,[],[]) >>
%             queensBody [0..n-1] >>= overwrite ini {-"~~."-}
% \end{spec}
The final task is to fuse |unfoldM p f| with |foldr odot (return [])|.

\subsection{Monadic Hylo-Fusion}

In a pure setting, it is known that, provided that the unfolding phase terminates, |foldr otimes e . unfoldr p f| is the unique solution of |hylo| in the equation below~\cite{Hinze:15:Conjugate}:
\begin{spec}
hylo y  | p y        = e
        | otherwise  = let f y = (x,z) in x `otimes` hylo z {-"~~."-}
\end{spec}
Hylomorphisms with monadic folds and unfolds are a bit tricky.
Pardo \shortcite{Pardo:01:Fusion} discussed hylomorphism for regular base functors, where the unfolding phase is monadic while the folding phase is pure.
As for the case when both phases are monadic, he noted ``the drawback ... is that they cannot be always transformed into a single function that avoids the construction of the intermediate data structure.''

For our purpose, we focus our attention on lists, and have a theorem fusing the monadic unfolding and folding phases under a side condition.
Given |otimes :: b -> Me eps c -> Me eps c|, |e :: c|, |p :: a -> Bool|, and |f :: a -> Me eps (b, a)| (with no restriction on |eps|), consider the expression:
\begin{spec}
  unfoldM p f >=> foldr otimes (return e) {-"~\,"-}:: {-"~\,"-} a -> Me eps c{-"~~."-}
\end{spec}
%Note that |p| is pure, while |f| and |otimes| are both monadic.
%The definition put no restrictions on what effects are allowed.
The following theorem says that this combination of folding and unfolding can be fused into one if |f| eventually terminates (in the sense explained at the end of this section) and for all |x| and |m|, |(x `otimes`)| commutes with |m| in the sense that |x `otimes` m{-"\,"-} ={-"\,"-} (m >>= \y -> x `otimes` return y)|. That is, it does not matter whether the effects of |m| happens inside or outside |(x `otimes`)|.
\begin{theorem} \label{thm:hylo-fusion}
For all |eps|, |otimes :: a -> Me eps c -> Me eps c|, |m :: Me eps c|, |p :: b -> Bool|, |f :: b -> Me eps (a,c)|, we have that |unfoldM p f >=> foldr otimes m = hyloM otimes m p f|, defined by:
\begin{code}
hyloM otimes m p f y
  | p y        = m
  | otherwise  = f y >>= \(x,z) ->  x `otimes` hyloM otimes m p f z {-"~~,"-}
\end{code}
if |x `otimes` n = n >>= ((x`otimes`) . return)| for all |n :: Me eps c|, and that the relation |(not . p)? . snd . (=<<) . f| is well-founded. (See the note below.)
%if False
\begin{code}
hyloMFuse ::
  Monad m =>
  (a -> m c -> m c)
  -> m c -> (b -> Bool) -> (b -> m (a, b)) -> b -> m c
hyloMFuse otimes m p f =
  unfoldM p f >=> foldr otimes m === hyloM otimes m p f
\end{code}
%endif
\end{theorem}
\begin{proof}
We start with showing that |unfoldM p f >=> foldr otimes m| is a fixed-point of the recursive equations of |hyloM|. When |p y| holds, it is immediate that
\begin{spec}
  return [] >>= foldr otimes m {-"~"-}= {-"~"-} m {-"~~."-}
\end{spec}
When |not (p y)|, we reason:
%if False
\begin{code}
hyloFusion1 :: Monad m =>
  (a -> m b -> m b) -> m b -> (b1 -> Bool) -> (b1 -> m (a, b1)) -> b1 -> m b
hyloFusion1 otimes m p f y =
\end{code}
%endif
\begin{code}
    unfoldM p f y >>= foldr otimes m
 ===    {- definition of |unfoldM|, |not (p y)| -}
    (f y >>= (\(x,z) -> (x:) <$> unfoldM p f z)) >>=
    foldr otimes m
 ===    {- monadic law \eqref{eq:monad-bind-ret} and |foldr| -}
    f y >>= (  \(x,z) -> unfoldM p f z >>= \xs ->
               x `otimes` foldr otimes m xs) {-"~~."-}
\end{code}
We focus on the expression inside the $\lambda$ abstraction:
%if False
\begin{code}
hyloFusion2 :: Monad m =>
  (a -> m b -> m b) -> a -> m b -> (b1 -> Bool) -> (b1 -> m (a, b1)) -> b1 -> m b
hyloFusion2 otimes x m p f z =
\end{code}
%endif
\begin{code}
    unfoldM p f z >>= (\xs -> x `otimes` foldr otimes m xs)
 ===    {- assumption: |x `otimes` n = n >>= ((x`otimes`) . return)|, see below -}
    unfoldM p f z >>= (foldr otimes m >=> ((x `otimes`) . return))
 ===    {- since |m >>= (f >=> g) = (m >>= f) >>= g| -}
    (unfoldM p f z >>= foldr otimes m) >>= ((x `otimes`) . return)
 ===    {- by assumption |x `otimes` m = m >>= ((x`otimes`) . return)| -}
   x `otimes` (unfoldM p f z >>= foldr otimes m) {-"~~."-}
\end{code}
To understand the first step, note that
|h xs >>= ((x `otimes`) . return) {-"\,"-}= {-"\,"-} (h >=> ((x `otimes`) . return)) xs|.

Now that |unfoldM p f z >>= foldr otimes m| is a fixed-point, we may conclude that it equals |hyloM otimes m p f| if the latter has a unique fixed-point. See the note below.
\end{proof}

\paragraph{Note} Let |q| be a predicate, |q?| is a relation defined by |{(x,x) `mid` q x}|. The parameter |y| in |unfoldM| is called the {\em seed} used to generate the list. The relation |(not.p)? . snd . (=<<) . f| maps one seed to the next seed (where |(=<<)| is |(>>=)| written reversed). If it is {\em well-founded}, intuitively speaking, the seed generation cannot go on forever and |p| will eventually hold. It is known that inductive types (those can be folded) and coinductive types (those can be unfolded) do not coincide in {\sf SET}. To allow a fold to be composed after an unfold, typically one moves to a semantics based on complete partial orders. However, it was shown~\cite{DoornbosBackhouse:95:Induction} that, in {\sf Rel}, when the relation generating seeds is well-founded, hylo-equations do have unique solutions. One may thus stay within a set-theoretic semantics. Such an approach is recently explored again~\cite{Hinze:15:Conjugate}. ({\em End of Note})

\vspace{1em}
Theorem \ref{thm:hylo-fusion} does not rely on \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero}, and does not put restriction on |eps|.
To apply the theorem to our particular case, we have to show that the precondition holds for our particular |odot|. Fortunately it is indeed the case, although we do need \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero}. In the lemma below we slightly generalise |odot| in Theorem \ref{lma:foldr-guard-fusion}:
\begin{lemma} Assuming that state and non-determinism commute, and |m >>= mzero = mzero|. Given |p :: a -> s -> Bool|, |next :: a -> s -> s|, |res :: a -> b -> b|, define |odot :: a -> Me eps b -> Me eps b| with |{N, S s} `sse` eps|:
\begin{spec}
  x `odot` m =  get >>= \st -> guard (p x st) >>
                put (next x st) >> (res x <$> m) {-"~~."-}
\end{spec}
We have |x `odot` m = m >>= ((x `odot`) . return)|.
\end{lemma}
\begin{proof}
Routine, using commutativity of state and non-determinism.
\end{proof}

\subsection{Summary, and Solving |n|-Queens}
\label{sec:solve-n-queens}

To conclude our derivation, a problem formulated as |unfoldM p f z >>= assert (all ok . scanlp oplus st)| can be solved by a hylomorphism. Define:
\begin{spec}
solve :: {N, S s} `sse` eps => (b -> Bool) -> (b -> Me eps (a, b)) -> (s -> Bool) -> (s -> a -> s) -> s -> b -> Me eps [a]
solve p f ok oplus st z = protect (put st >> hyloM odot (return []) p f z)
  where x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                      put (st `oplus` x) >> ((x:) <$> m) {-"~~."-}
\end{spec}
%if False
\begin{code}
solve :: (MonadState s m, MonadPlus m) =>
  (b -> Bool) -> (b -> m (a, b)) -> (s -> Bool) ->
  (s -> a -> s) -> s -> b -> m [a]
solve p f ok oplus st z = protect (put st >> hyloM odot (return []) p f z)
  where x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                      put (st `oplus` x) >> ((x:) <$> m)
\end{code}
%endif
\begin{corollary} \label{cor:unfold-assert-scanl-local}
% Given |p :: b -> Bool|, |f :: b -> Me eps (a,b)|, |z :: b|, |ok :: s -> Bool|, |oplus :: s -> a -> s|, |st :: s|, where |{N, S s} `sse` eps|,
If the relation |(not . p)? . snd . (=<<) . f| is well-founded, and \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} hold in addition to the other laws, we have
%if False
\begin{code}
corUnfoldAssertScanlLocal :: (MonadPlus m, MonadState s m) =>
  (b -> Bool) -> (b -> m (a, b)) -> b -> (s -> Bool) -> (s -> a -> s)
  -> s -> m [a]
corUnfoldAssertScanlLocal p f z ok oplus st =
\end{code}
%endif
\begin{code}
 unfoldM p f z >>= assert (all ok . scanlp oplus st) ===
    solve p f ok oplus st z {-"~~."-}
\end{code}
\end{corollary}

\paragraph{|n|-Queens Solved}
Recall that
\begin{spec}
queens n  = perm [0 .. n-1] >>= assert safe
          = unfoldM null select [0..n-1] >>= assert (all ok . scanlp oplus (0,[],[])) {-"~~,"-}
\end{spec}
where the auxiliary functions |select|, |ok|, |oplus| are defined in Section \ref{sec:queens}.
The function |select| cannot be applied forever since the length of the given list decreases after each call.
Therefore, Corollary \ref{cor:unfold-assert-scanl-local} applies, and we have |queens n = solve null select ok oplus (0,[],[]) [0..n-1]|.
Expanding the definitions we get:
\begin{spec}
queens :: {N, S (Int, [Int], [Int])} `sse` eps => Int -> Me eps [Int]
queens n = protect (put (0,[],[]) >> queensBody [0..n-1]) {-"~~,"-}

queensBody :: {N, S (Int, [Int], [Int])} `sse` eps => [Int] -> Me eps [Int]
queensBody []  =  return []
queensBody xs  =  select xs >>= \(x,ys) ->
                  get >>= \st -> guard (ok (st `oplus` x)) >>
                  put (st `oplus` x) >> ((x:) <$> queensBody ys) {-"~~,"-}
  where  (i,us,ds) `oplus` x = (1 + i, (i+x):us, (i-x):ds)
         ok (_,u:us,d:ds) = (u `notElem` us) && (d `notElem` ds) {-"~~."-}
\end{spec}
This completes the derivation of our first algorithm for the |n|-queens problem.
%if False
\begin{code}
queensBody :: (MonadPlus m, MonadState (Int, [Int], [Int]) m) => [Int] -> m [Int]
queensBody []  =  return []
queensBody xs  =  select xs >>= \(x,ys) ->
                  get >>= \st -> guard (ok (st `oplus` x)) >>
                  put (st `oplus` x) >> ((x:) <$> queensBody ys) {-"~~,"-}
  where  (i,us,ds) `oplus` x = (1 + i, (i+x):us, (i-x):ds)
         ok (_,u:us,d:ds) = (u `notElem` us) && (d `notElem` ds) {-"~~."-}

runQueens :: (MonadPlus m, MonadState (Int, [Int], [Int]) m) => Int -> m [Int]
runQueens n = protect (put (0,[],[]) >> queensBody [0..n-1])

-- try runSN (runQueens 8) undefined

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

\end{code}
\begin{code}
modify h        = get >>= \st -> put (h st)
\end{code}
%endif
