\documentclass{article}

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{../paper/doubleequals}
\usepackage{scalerel}
\usepackage{authblk}


% build using
%    lhs2TeX NQueens.lhs | pdflatex --jobname=NQueens

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include ../paper/Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

%if False
\begin{code}
{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
    FlexibleInstances, KindSignatures, MultiParamTypeClasses #-}

module NQueens where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..), modify)
import GHC.Base (Alternative(..))
\end{code}
%endif

\begin{document}

\title{Notes: N-Queens}

\author[1]{Shin-Cheng Mu}
\affil[1]{Academia Sinica, Taiwan}

\date{May 2019}

\maketitle

%format m1
%format m2

\paragraph{Specification} Adapted from previous version:
\begin{code}
queens :: MNondet m => Int -> m [Int]
queens n = perm [0..n-1] >>= filt safe {-"~~,"-}

filt :: MNondet m => (a -> Bool) -> a -> m a
filt p x = guard (p x) >> return x {-"~~,"-}
\end{code}
where |guard| is a standard monadic function defined by:
\begin{code}
guard :: MNondet m => Bool -> m ()
guard b = if b then return () else mzero {-"~~."-}
\end{code}

\paragraph{Safety Check} based on up and down diagonals:
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

Define a generalisation of |safe|:
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

\paragraph{Safety Check, Statefully} Introducing a state:

%if False
\begin{code}
filtScanlpFoldr :: (MonadPlus m, MonadState s m) =>
  (s -> Bool) -> (s -> a -> s) -> s -> [a] ->
  (a -> m [a] -> m [a]) -> m [a]
filtScanlpFoldr ok oplus st xs odot =
\end{code}
%endif
\begin{code}
 filt (all ok . scanlp oplus st) xs ===
   protect (put st >> foldr odot (return []) xs) {-"~~."-}
\end{code}

%% APPENDIX:
%% Auxiliary definitions used in this file.

%if False
\begin{code}
infixr 0 ===

(===) :: a -> a -> a
(===) = undefined

wrap x = [x]

(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
(f <=< g) x = f =<< g x

-- (<$>) :: Monad m => (a -> b) -> m a -> m b
-- f <$> mx = (return . f) =<< mx

(<.>) :: Monad m => (b -> c) -> (a -> m b) -> (a -> m c)
f <.> g = ((return . f) =<<) . g

(<<) :: Monad m => m b -> m a -> m b
m1 << m2 = m2 >> m1

side :: MonadPlus m => m a -> m b
side m = m >>= const mzero
\end{code}
%endif
\end{document}
