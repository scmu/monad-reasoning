\documentclass{article}

% build using
%    lhs2TeX Corrected.lhs | pdflatex --jobname=Corrected

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{../doubleequals}
\usepackage{scalerel}
\usepackage{authblk}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include ../Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

%if False
\begin{code}
{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
    FlexibleInstances, KindSignatures, MultiParamTypeClasses #-}

module Corrected where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..), modify)
import GHC.Base (Alternative(..))
\end{code}
%endif

\newtheorem{innercustomgeneric}{\customgenericname}
\providecommand{\customgenericname}{}
\newcommand{\newcustomtheorem}[2]{%
  \newenvironment{#1}[1]
  {%
   \renewcommand\customgenericname{#2}%
   \renewcommand\theinnercustomgeneric{##1}%
   \innercustomgeneric
  }
  {\endinnercustomgeneric}
}

\newcustomtheorem{customthm}{Theorem}
\newcustomtheorem{customlemma}{Lemma}

\begin{document}

\title{Corrected Lemmas}

\author{}
%\affil{}

\date{}

\maketitle

%format m1
%format m2

\begin{customthm}{5.1} \label{thm:hylo-fusion}
For all |eps|, |otimes :: a -> Me eps c -> Me eps c|, |m :: Me eps c|, |p :: b -> Bool|, |f :: b -> Me eps (a,c)|, we have that |unfoldM p f >=> foldr otimes m = hyloM otimes m p f|, defined by:
\begin{code}
hyloM otimes m p f y
  | p y        = m
  | otherwise  = f y >>= \(x,z) ->  x `otimes` hyloM otimes m p f z {-"~~,"-}
\end{code}
if the relation |(not . p)? . snd . (=<<) . f| is well-founded, and
|unfoldM p f z >>= ((x `otimes`) . k) === x `otimes` (unfoldM p f z >>= k)| for all |k|.
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
\end{customthm}
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
    (f y >>= (\(x,z) -> (x:) <$> unfoldM p f z)) >>= foldr otimes m
 ===    {- monad law  and |foldr| -}
    f y >>= (\(x,z) -> unfoldM p f z >>= \xs -> x `otimes` foldr otimes m xs)
 ===    {- since |n >>= ((x `otimes`) . k) === x `otimes` (n >>= k)| where |n = unfoldM p f z| -}
    f y >>= (\(x,z) -> x `otimes` (unfoldM p f z >>=  foldr otimes m))
\end{code}
Now that |unfoldM p f z >>= foldr otimes m| is a fixed-point, we may conclude that it equals |hyloM otimes m p f| if the latter has a unique fixed-point.
\end{proof}

Theorem \ref{thm:hylo-fusion} is not specific to local state. The following lemma applies to any |n| that commutes with state, for example, if |n :: Me N a|.

\begin{customlemma}{5.2}\label{lma:odot-fusable} Given |p :: a -> s -> Bool|, |next :: a -> s -> s|, |res :: a -> b -> b|, define |odot :: a -> Me eps b -> Me eps b| with |{N, S s} `sse` eps|:
\begin{spec}
  x `odot` m =  get >>= \st -> guard (p x st) >>
                put (next x st) >> (res x <$> m) {-"~~."-}
\end{spec}
We have |n >>= ((x `odot`) . k) === x `odot` (n >>= k)|, if |n| commutes with state and |m >>= mzero = mzero| for all |m|.
\end{customlemma}
\begin{proof} We reason:
\begin{spec}
     n >>= ((x `odot`) . k)
===  n >>= \y -> x `odot` k y
===    {- definition of |odot| -}
     n >>= \y -> get >>= \st ->
     guard (p x st) >> put (next x st) >>
     (res x <$> k y)
===    {- non-determinism and state commute -}
     get >>= \st -> n >>= \y ->
     guard (p x st) >> put (next x st) >>
     (res x <$> (k y))
===   {- since |m >>= mzero = mzero| -}
     get >>= \st -> guard (p x st) >>
     n >>= \y -> put (next x st) >>
     (res x <$> (k y))
===   {- non-determinism and state commute -}
     get >>= \st -> guard (p x st) >>
     put (next x st) >> n >>= \y ->
     (res x <$> (k y))
===    {- properties of |(<$>)|  -}
     get >>= \st -> guard (p x st) >>
     put (next x st) >>
     (res x <$> n >>= k)
===    {- definition of |odot| -}
     x `odot` (n >>= k) {-"~~."-}
\end{spec}
\end{proof}

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

unfoldM :: Monad m => (b -> Bool) -> (b -> m (a,b)) -> b -> m [a]
unfoldM p f z  | p z        =  return []
               | otherwise  =  f z >>= \(x,w) ->
                               (x:) <$> unfoldM p f w {-"~~."-}
\end{code}
%endif
\end{document}
