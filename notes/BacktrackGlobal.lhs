\documentclass{article}

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{doubleequals}
\usepackage{scalerel}
\usepackage{authblk}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}

\newcommand{\delete}[1]{}

%if False
\begin{code}
{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
    FlexibleInstances, KindSignatures, MultiParamTypeClasses #-}

module BacktrackGlobal where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..), modify)
import GHC.Base (Alternative(..))

-- import Monad
-- import QueensSpec
-- import QueensLocal
\end{code}
%endif


\begin{document}

\title{Notes: Backtracking Algorithm using Global State}

\author[1]{Shin-Cheng Mu}
\affil[1]{Academia Sinica, Taiwan}

\date{March 2018}

\maketitle

\section{Setting Up}

\paragraph{Axioms}
\begin{align}
  |side (put s) `mplus` side m2| &= |side (put s >> m2)| \mbox{~~,}
    \label{eq:side-side} \\
  |put s >> (m1 `mplus` m2)| &= |(put s >> m1) `mplus` m2| \mbox{~~,}
    \label{eq:put-mplus}\\
  |get >>= (\x -> f x `mplus` m)| &=~ |(get >>= f) `mplus` m| \mbox{~~, |x| not free in |m|.}
    \label{eq:get-mplus}\\
%  |(put s >> return x) `mplus` m| &= |(put s >> return x) `mplus` (put s >> m)| ~~\mbox{,}
%        \label{eq:put-ret-side}\\
%  |sidePut cmd `mplus` m| &=~ |m `mplus` sidePut cmd| \mbox{~~,}
%    \label{eq:side-nd-mplus}\\
  |get >>= \x -> f1 x `mplus` f2 x| &=~ |(get >>= f1) `mplus` (get >>= f2)| \mbox{~~, if |f1 x :: Me N a|}
      \label{eq:get-mplus-distr}\\
  |get >>= \x -> f1 x `mplus` f2 x| &=~ |(get >>= (\x -> f1 x `mplus` side (put x))) `mplus` (get >>= f2)| \mbox{~~.}
        \label{eq:get-mplus-side-distr}
\end{align}

By \eqref{eq:side-side} we have:
\begin{equation}
 |side (put s) `mplus` side (put t) = side (put t)| \mbox{~~.}
  \label{eq:side-put-put}
\end{equation}

With \eqref{eq:get-mplus-distr} we can prove that |get| and non-determinism commute.

\paragraph{Restoring Put} Define
\begin{code}
side m = m >> mzero {-"~~,"-}
putR s = get >>= \s0 -> (put s `mplus` side (put s0)) {-"~~."-}
\end{code}

\paragraph{Basic Laws}
The following laws are still true:
\begin{align*}
    |putR s >>= get| ~&=~ |putR s >>= return s| \mbox{~~,} \\
    |putR s >> putR s'| ~&=~ |putR s'|  \mbox{~~,} \\
\end{align*}

\begin{proof} We reason:
\begin{spec}
   putR s >>= get
=  (get >>= \s0 -> (put s `mplus` side (put s0))) >>= get
=    {- left distributivity -}
   get >>= \s0 -> (put s >>= get) `mplus` side (put s0)
=    {- |put|-|get| -}
   get >>= \s0 -> (put s >>= return s) `mplus` side (put s0)
=  (get >>= \s0 -> (put s `mplus` side (put s0))) >>= return s
=  putR s >>= return s {-"~~."-}
\end{spec}

\begin{spec}
   putR s >> putR s'
=  (get >>= \s0 -> (put s `mplus` side (put s0))) >>
   (get >>= \s0 -> (put s' `mplus` side (put s0)))
=    {- left distributivity -}
   get >>= \s0 ->
     (put s >> get >>= \s0 -> (put s' `mplus` side (put s0))) `mplus` side (put s0)
=    {- |put|-|get| -}
   get >>= \s0 ->
     (put s >> (put s' `mplus` side (put s))) `mplus` side (put s0)
=    {- by \eqref{eq:put-mplus} -}
   get >>= \s0 ->
     (put s >> puts') `mplus` side (put s) `mplus` side (put s0)
=    {- |put|-|put| and \eqref{eq:side-put-put} -}
   get >>= \s0 -> put s' `mplus` side (put s0)
=  putR s' {-"~~."-}
\end{spec}
\end{proof}
Note that we do not have |get >>= putR = return ()|. To see that, we calculate:
\begin{spec}
   (get >>= putR) >> put t
=  (get >>= (\s -> get >>= \s0 -> put s `mplus` side (put s0))) >> put t
=   {- |get|-|get| -}
   (get >>= \s -> put s `mplus` side (put s)) >> put t
=   {- monad laws, left-distributivity -}
   get >>= \s -> (put s >> put t) `mplus` side (put s)
=   {- |put|-|put| -}
   get >>= \s -> put t `mplus` side (put s) {-"~~."-}
\end{spec}
Meanwhile, |return () >> put t = put t|. The two side are not equal when |s /= t|.

\section{State-Restoration}

\begin{definition}
  |m| is {\em state-restoring} if |m = get >>= \s0 -> m `mplus` sidePut s0|.
\end{definition}

Define:
\begin{spec}
modifyR next prev =  modify next `mplus` side (modify prev)
\end{spec}
\begin{lemma} Let |next| and |prev| be such that |prev . next = id|.
  If |m| is state-restoring, we have
  \begin{spec}
  get >>= \s -> putR (next s) >> m =
    modifyR next prev >> m {-"~~."-}
  \end{spec}
\end{lemma}
\begin{proof} We reason:
\begin{spec}
   modifyR next prev >> m
=  (modify next `mplus` sideMod prev) >> m
=    {- left distributivity -}
   (modify next >> m) `mplus` sideMod prev
=  (get >>= \s -> put (next s) >> m) `mplus` sideMod prev
     {- by \eqref{eq:get-mplus} -}
=  get >>= \s -> (put (next s) >> m) `mplus` sideMod prev
=    {- |m| state-restoring -}
   get >>= \s ->  (put (next s) >> get >>= \s' -> m `mplus` sidePut s') `mplus`
                  sideMod prev
=    {- |put|-|get| -}
   get >>= \s ->  (put (next s) >> (m `mplus` sidePut (next s))) `mplus`
                  sideMod prev
=    {- by \eqref{eq:put-mplus} -}
   get >>= \s -> put (next s) >>
                 (m `mplus` sidePut (next s)) `mplus` sideMod prev)
=    {- by \eqref{eq:side-side} -}
   get >>= \s -> put (next s) >>
                 (m `mplus` side (put (next s) >> modify prev))
=  get >>= \s -> put (next s) >> (m `mplus` sidePut s)
=    {- by \eqref{eq:put-mplus} -}
   get >>= \s -> (put (next s) >> m) `mplus` sidePut s
=    {- |get|-|get|, definition of |putR| -}
   get >>= \s -> putR (next s) >> m {-"~~."-}
\end{spec}
\end{proof}

\paragraph{Compositional State-Restoration}
\begin{lemma} We have the following properties:
\begin{enumerate}
\item |mzero| is state-restoring;
\item |putR s >> m| is state-restoring;
\item if |m| is state-restoring, so is |guard p >> m|;
\item if |f x| is state-restoring for all |x|, so is |get >>= f|;
\item |m >>= f| is state-restoring if |m| is.
\end{enumerate}
\end{lemma}
\begin{proof} In turns:
\begin{enumerate}
  %
\item |mzero| is state-restoring.
\begin{spec}
   get >>= \s -> mzero `mplus` sidePut s
=  get >>= \s -> sidePut s
=  get >>= \s -> put s >> mzero
=   {- |get|-|put| -}
   mzero {-"~~."-}
\end{spec}
%
\item |putR s >> m| is state-restoring.
\begin{spec}
   get >>= \s0 -> (putR s >> m) `mplus` sidePut s0
=  get >>= \s0 -> (get >>= \s1 -> (put s >> m) `mplus` sidePut s1) `mplus` sidePut s0
=    {- by \eqref{eq:get-mplus} -}
   get >>= \s0 -> get >>= \s1 -> (put s >> m) `mplus` sidePut s1 `mplus` sidePut s0
=    {- |get|-|get| -}
   get >>= \s0 -> (put s >> m) `mplus` sidePut s0 `mplus` sidePut s0
=    {- by \eqref{eq:side-put-put} -}
   get >>= \s0 -> (put s >> m) `mplus` sidePut s0
=    {- left-distributivity -}
   get >>= \s0 -> (put s `mplus` sidePut s0) >> m
=    {- monad law, definition of |putR| -}
   putR s >> m {-"~~."-}
\end{spec}
%
\item If |m| is state-restoring, so is |guard p >> m|. \\
When |p| holds, |guard p >> m = m|; when |p| does not hold, |guard p >> m = mzero|.
%
\item If |f x| is state-restoring for all |x|, so is |get >>= f|.
\begin{spec}
   get >>= \s -> (get >>= f) `mplus` sidePut s
=    {- \eqref{eq:get-mplus} -}
   get >>= \s -> get >>= (\x -> f x `mplus` sidePut s)
=    {- |get|-|get| -}
   get >>= \s -> f s `mplus` sidePut s
=    {- |get|-|get|-}
   get >>= \s -> get >>= (\x -> f s `mplus` sidePut x)
=    {- |f s| state-restoring -}
   get >>= \s0 -> f s0
=  get >>= f {-"~~."-}
\end{spec}
%
\item |m >>= f| is state-restoring if |m| is.
\begin{spec}
   get >>= \s -> (m >>= f) `mplus` sidePut s
=    {- since |mzero >>= f = mzero| -}
   get >>= \s -> (m >>= f) `mplus` (sidePut s >>= f)
=    {- left-distributivity -}
   (get >>= \s -> m `mplus` sidePut s) >>= f
=    {- |m| state-restoring -}
   m >>= f {-"~~."-}
\end{spec}
\end{enumerate}
\end{proof}

\section{Commutivity with |guard|}

|putR| and |get| commute with |guard|, which will be useful later.
\begin{lemma} |putR s >> guard p = guard p >> putR s|.
\end{lemma}
\begin{proof} We reason:
\begin{spec}
     putR s >> guard p
===  get >>= \s0 ->
     (put s `mplus` side (put s0)) >> guard p
===    {- left distributivity, |side m >> k = side m| -}
     get >>= \s0 ->
     (put s >> guard p) `mplus` side (put s0)
\end{spec}

\noindent{\bf Case} |not p|, thus |guard p = mzero|:
\begin{spec}
     get >>= \s0 ->
     (put s >> guard p) `mplus` side (put s0)
===    {- since |guard p = mzero| -}
     get >>= \s0 ->
     (put s >> mzero) `mplus` side (put s0)
===    {- by \eqref{eq:side-put-put} -}
     get >>= \s0 -> side (put s0)
===  get >>= \s0 -> put s0 >> mzero
===  mzero
===  mzero >> putR s
===  guard p >> putR s {-"~~."-}
\end{spec}

\noindent{\bf Case} |p|, thus |guard p = return ()|:
\begin{spec}
     get >>= \s0 ->
     (put s >> guard p) `mplus` side (put s0)
===    {- since |guard p = return ()|, monad laws -}
     get >>= \s0 ->
     put s `mplus` side (put s0)
===    {- monad laws -}
     return () >> get >>= \s0 ->
     put s `mplus` side (put s0)
===    {- since |guard p = return ()| -}
     guard p >> get >>= \s0 ->
     put s `mplus` side (put s0)
===  guard p >> putR s {-"~~."-}
\end{spec}
\end{proof}

\begin{lemma} If |s| does not occur free in |p|,
\begin{spec}
  get >>= \s -> guard p >> f s === guard p >> get >>= f  {-"~~."-}
\end{spec}
\end{lemma}
\begin{proof}
\noindent{\bf Case} |not p|, thus |guard p = mzero|:
\begin{spec}
     get >>= \s -> mzero >> f s
===  get >>= \s -> mzero
===  mzero
===  mzero >> get >>= f{-"~~."-}
\end{spec}

\noindent{\bf Case} |p|, thus |guard p = return ()|:
\begin{spec}
     get >>= \s -> return () >> f s
===  get >>= \s -> f s
===  return () >> get >>= f {-"~~."-}
\end{spec}
\end{proof}

\delete{
\subsection*{Commutivity}

Not sure what we may have here now.
\begin{theorem}
  |putR| commutes with non-determinism. That is,
  |m >>= \x -> putR s >> return x = putR s >> m|.
\end{theorem}
\begin{proof}
[{\bf Warning}: This is not right. It may be true if all contexts uses only |putR| and not |put|. Or under some other constraints.]

Induction on |m|.

\noindent{\bf Case} |m := mzero|.
It was shown that |putR s >> mzero = mzero >> putR s|.

\noindent{\bf Case} |m := return x|. Immediate.

\noindent{\bf Case} |m := m1 `mplus` m2|. If |m1 = m2 = mzero| we fall back to a base case. If either |m1| or |m2| is |mzero| we can use induction. Assume that neither |m1| nor |m2| is |mzero|:
\begin{spec}
   (m1 `mplus` m2) >>= \x -> putR s >> return x
=    {- left-distributivity -}
   (m1 >>= \x -> putR s >> return x) `mplus` (m2 >>= \x -> putR s >> return x)
=    {- induction -}
   (putR s >> m1) `mplus` (putR s >> m2)
=    {- definition of |putR| -}
   (get >>= \s0 -> (put s >> m1) `mplus` putSide s0) `mplus`
   (get >>= \s0 -> (put s >> m2) `mplus` putSide s0)
=    {- by \eqref{eq:get-mplus-side-distr} -}
   get >>= \s0 -> (put s >> m1) `mplus` (put s >> m2) `mplus` putSide s0
=    {- ?? -}
   get >>= \s0 -> (put s >> (m1 `mplus` m2)) `mplus` putSide s0
=    {- definition of |putR| -}
   putR s >> (m1 `mplus` m2)
\end{spec}
\begin{spec}
   (m1 `mplus` m2) >>= \x -> putR s >> return x
=    {- left-distributivity -}
   (m1 >>= \x -> putR s >> return x) `mplus` (m2 >>= \x -> putR s >> return x)
=    {- definition of |putR| -}
   (m1 >>= \x -> get >>= \s0 -> (put s >> return x) `mplus` sidePut s0) `mplus`
   (m2 >>= \x -> get >>= \s0 -> (put s >> return x) `mplus` sidePut s0)
=    {- |get| and non-determinism commute -}
   (get >>= \s0 -> m1 >>= (\x -> (put s >> return x) `mplus` sidePut s0)) `mplus`
   (get >>= \s0 -> m2 >>= (\x -> (put s >> return x) `mplus` sidePut s0))
=    {- Lemma \ref{lma:sidePut-distr} -}
   (get >>= \s0 -> m1 `mplus` sidePut s0) `mplus`
   (get >>= \s0 -> m2 `mplus` sidePut s0)
=    {- by \eqref{eq:get-mplus-side-distr} -}
   get >>= \s0 -> m1 `mplus` m2 `mplus` sidePut s0
=    {- by \eqref{eq:put-ret-side} -}
   get >>= \s0 -> put s >> (m1 `mplus` m2) `mplus` sidePut s0
=    {- definition -}
   putR s >> (m1 `mplus` m2) {-"~~."-}
\end{spec}
\end{proof}
} %delete

\section{Properties about |scanl|}

\paragraph{Scan} Recall the definitions:
\begin{code}
scanlp :: (b -> a -> b) -> b -> [a] -> [b]
scanlp oplus st []      = []
scanlp oplus st (x:xs)  = (st `oplus` x) : scanlp oplus (st `oplus` x) xs {-"~~,"-}
\end{code}
\begin{code}
scanlMR :: (MonadState s m) => (s -> a -> s) -> s -> s -> [a] -> m [s]
scanlMR oplus st fin xs = putR st >> foldr otimes (putR fin >> return []) xs
  where x `otimes` m =  get >>= \st -> ((st `oplus` x):) <$> (putR (st `oplus` x) >> m) {-"~~."-}
\end{code}

\begin{theorem}\label{thm:putR-scanlp-scanM}
For all |oplus :: (s -> a -> s)|, |fin, st :: s|, and |xs :: [a]|,
\begin{spec}
putR fin >> return (scanlp oplus st xs) === scanlMR oplus st fin xs {-"~~."-}
\end{spec}
\end{theorem}
\begin{proof}
%[{\bf Warning}: not sure this is true. Gotta check again.]
% Should be true.

Induction on |xs|.

\noindent{\bf Case} |xs := []|.
Both sides reduce to |putR fin >> return []|.

\noindent{\bf Case} |xs := x:xs|.
\begin{spec}
   scanlMR oplus st (x:xs)
=    {- definition, abbreviate |putR fin >> return []| to |ret| -}
   putR st >> (x `otimes` foldr otimes ret xs)
=   {- definition of |otimes|, let |st' = st `oplus` x| -}
   putR st >> get >>= \st ->
   (st':) <$> (putR st' >> foldr otimes ret xs)
=   {- |putR|-|get| -}
   putR st >> (st':) <$> (putR st' >> foldr otimes ret xs)
=  (st':) <$> putR st >> putR st' >> foldr otimes ret xs
=   {- |putR|-|putR| -}
   (st':) <$> putR st' >> foldr otimes ret xs
=   {- induction -}
   ((st `oplus` x):) <$> (putR fin >> return (scanlp oplus (st `oplus` x) xs))
=  putR fin >> return ((st `oplus` x) : scanlp oplus (st `oplus` x) xs)
=  putR fin >> return (scanlp oplus st (x:xs)) {-"~~."-}
\end{spec}
\end{proof}

\paragraph{Safety Check in a |foldr|} We calculate:
\begin{spec}
   putR fin >> assert (all ok . scanlp oplus st) xs
=    {- definition of |assert| -}
   putR fin >> guard (all ok . scanlp oplus st xs) >> return xs
=    {- monad law -}
   putR fin >> return (scanlp oplus st xs) >>= \ys ->
   guard (all ok ys) >> return xs
=    {- Theorem \ref{thm:putR-scanlp-scanM} -}
   scanlMR oplus st fin xs >>= \ys ->
   guard (all ok ys) >> return xs
=    {- definition of |scanlMR| -}
   putR st >> foldr otimes (putR fin >> return []) xs >>= \ys ->
   guard (all ok ys) >> return xs {-"~~."-}
\end{spec}
We now try to fuse the |foldr| and |guard| together.

\begin{theorem}[|foldr|-|guard| fusion] \label{lma:foldr-guard-fusion}
Let |otimes| be defined as that in |scanlMR| for any given |oplus :: s -> a -> s|. We have that for all |ok :: s -> Bool| and |xs :: [a]|:
\begin{spec}
  foldr otimes (putR fin >> return []) xs >>= \ys -> guard (all ok ys) >> return xs =
      foldr odot (putR fin >> return []) xs {-"~~,"-}
    where x `odot` m =  get >>= \st -> putR (st `oplus` x) >>
                        guard (ok (st `oplus` x)) >>
                        ((x:) <$> m) {-"~~."-}
\end{spec}
\end{theorem}
\begin{proof} Induction on |xs|.

\noindent {\bf Case} |xs := []|. Both sides reduce to |putR fin >> return []|.

\noindent {\bf Case} |xs := x:xs|. We abbreviate |putR fin >> return []| to |finR|.
\begin{spec}
   foldr otimes finR (x:xs) >>= \ys -> guard (all ok ys) >> return (x:xs)
=    {- definition of |otimes| -}
   (get >>= \st -> ((st `oplus` x):) <$> (putR (st `oplus` x) >> foldr otimes finR xs)) >>= \ys ->
   guard (all ok ys) >> return (x:xs)
=   {- monad laws -}
   get >>= \st ->  putR (st `oplus` x) >> foldr otimes finR xs >>= \ys ->
                   guard (all ok ((st `oplus` x) : ys)) >> return (x:xs)
=   {- definition of |all|, and |guard (p && q) = guard p >> guard q| -}
   get >>= \st ->  putR (st `oplus` x) >> foldr otimes finR xs >>= \ys ->
                   guard (ok (st `oplus` x)) >> guard (all ok ys) >> return (x:xs)
=   {- commutivity, see below -}
   get >>= \st ->  putR (st `oplus` x) >> guard (ok (st `oplus` x)) >>
                   foldr otimes finR xs >>= \ys -> guard (all ok ys) >> return (x:xs)
=   {- monad laws, induction -}
   get >>= \st -> putR (st `oplus` x) >> guard (ok (st `oplus` x)) >>
   foldr odot finR xs >>= \xs' -> return (x:xs')
=   {- definition of |odot| -}
   foldr odot finR (x:xs) {-"~~."-}
\end{spec}
In the 3rd step from the last we need |guard (ok (st `oplus` x))| to commute with |foldr otimes finR xs|. This can be proved by induction using the fact that |guard| commutes with |get| and |putR|, as shown previously.
\end{proof}

\begin{theorem}\label{thm:putR-modifyR} Let |ominus| be such that |(st `oplus` x) `ominus` x = st| for all |st| and |x|. We have
  |foldr odot (putR fin >> return e) = foldr ocirc (putR fin >> return e)|,
where |ocirc| is defined by:
\begin{spec}
x `ocirc` m =  modifyR (`oplus` x) (`ominus` x) >>
               get >>= (guard . ok) >>
               ((x:) <$> m) {-"~~."-}
\end{spec}
\end{theorem}
To be verified.

\begin{corollary}\label{thm:putR-assert-scanlp-foldr} The following is true, where |ocirc| is as defined in Theorem \ref{thm:putR-modifyR}:
\begin{spec}
putR fin >> assert (all ok . scanlp oplus st) xs =
  putR st >> foldr ocirc (putR fin >> return []) xs {-"~~."-}
\end{spec}
\end{corollary}

\section{Hylo-Fusion}

To do...

\section{Deriving a Backtracking Algorithm}

Consider problems specified in the form
\begin{spec}
  unfoldM p f >=> assert (all ok . scanlp oplus st) {-"~~."-}
\end{spec}

Calculate.
\begin{spec}
    unfoldM p f z >>= \xs -> putR fin >> assert (all ok . scanlp oplus st) xs
=     {- Corollary \ref{thm:putR-assert-scanlp-foldr} -}
    unfoldM p f z >>= \xs -> putR st >> foldr ocirc finR xs
=     {- ??? -}
    putR st >> unfoldM p f z >>= foldr ocirc finR
=     {- ??? -}
    putR st >> hyloM ...?
\end{spec}

\end{document}
