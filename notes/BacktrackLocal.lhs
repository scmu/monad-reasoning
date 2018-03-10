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

%if False
\begin{code}
{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables,
    FlexibleInstances, KindSignatures, MultiParamTypeClasses #-}

module BacktrackLocal where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State (MonadState(..), modify)
import GHC.Base (Alternative(..))
\end{code}
%endif

\begin{document}

\title{Notes: Backtracking Algorithm using Local State}

\author[1]{Shin-Cheng Mu}
\affil[1]{Academia Sinica, Taiwan}

\date{}

\maketitle

%format m1
%format m2

In this note we consider developing backtracking algorithms for problems that can be specified in this form
\begin{spec}
   unfoldM p f >=> assert (all ok . scanlp oplus st) {-"~~,"-}
\end{spec}
where |unfoldM| is defined by:
\begin{code}
unfoldM :: Monad m => (b -> Bool) -> (b -> m (a,b)) -> b -> m [a]
unfoldM p f z  | p z        =  return []
               | otherwise  =  f z >>= \(x,w) ->
                               (x:) <$> unfoldM p f w {-"~~."-}
\end{code}

\section{Setting Up}


\paragraph{Laws regarding monads} Recall the monad laws
\begin{align}
  |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
Also recall that |m1 >> m2 = m1 >>= const m2|.

Regarding monad-plus, we want |mplus| to be associative, with |mzero| as identity. Monadic bind distributes into |mplus| from the end, while
|mzero| is a zero for |(>>=)|:
%format +++ = mplus
\begin{align}
  |mzero >>= f| &= |mzero| \label{eq:bind-mzero-zero} \mbox{~~,}\\
  \label{eq:bind-mplus-dist}
  |(m `mplus` n) >>= f| &= |(m >>= f) `mplus` (n >>= f)| \mbox{~~.}
\end{align}

Laws regarding state operations:
\begin{align}
|put s >> put s'| &= |put s'|~~\mbox{,} \label{eq:put-put}\\
|put s >> get| &= |put s >> return s| ~~\mbox{,} \label{eq:get-put}\\
|get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
|get >>= (\s -> get >>= k s)| &= |get >>= (\s -> k s s)|
~~\mbox{.} \label{eq:get-get}
\end{align}

\paragraph{Basic Properties}
We assume we are working with total functions and thus have the following:
\begin{align}
  |f (if p then e1 else e2)| &= |if p then f e1 else f e2| \mbox{~~,}
  \label{eq:if-distr}\\
  |if p then (\x -> e1) else (\x -> e2)| &=
    |\x -> if p then e1 else e2| \mbox{~~.}\label{eq:if-fun}
\end{align}

\paragraph{Properties of |guard|}
Also define:
\begin{spec}
guard :: MonadPlus m => Bool -> m ()
guard b = if b then return () else mzero
\end{spec}
\begin{code}
assert :: MonadPlus m => (a -> Bool) -> a -> m a
assert p x = guard (p x) >> return x {-"~~."-}
\end{code}
The following properties appear obvious, but let us prove them to be safe.
\begin{align}
  |guard (p && q)| &= |guard q << guard p| \mbox{~~,}
  \label{eq:guard-conj} \\
  |(f <$> m) << guard p| &= |f <$> (m << guard p)| \mbox{~~.}
  \label{eq:guard-fmap}
\end{align}
With \eqref{eq:guard-fmap} we may denote both sides by
|f <$> m << guard p|.
\begin{proof}
Proof of \eqref{eq:guard-conj} relies only on property of |if|
and conjunction:
\begin{spec}
   guard (p && q)
=  if p && q then return () else mzero
=  if p then (if q then return () else mzero) else mzero
=  if p then guard q else mzero
=  guard q << guard p {-"~~."-}
\end{spec}

To prove \eqref{eq:guard-fmap}, surprisingly, we need only
distributivity and {\em not} \eqref{eq:bind-mzero-zero}:
\begin{spec}
   (f <$> m) << guard p
=   {- definition of |guard| -}
   (f <$> m) << (if p then return () else mzero)
=   {- by \eqref{eq:if-distr} -}
   if p then (f <$> m) << return () else (f <$> m) << mzero
=   {- by \eqref{eq:monad-assoc} and \eqref{eq:monad-bind-ret} -}
   if p then f <$> (m << return ()) else f <$> (m << mzero)
=   {- by \eqref{eq:if-distr} -}
   f <$> (m << (if p then return () else mzero))
=   {- definition of |guard| -}
   f <$> (m << guard p)
\end{spec}
\end{proof}

\begin{lemma}\label{lma:guard-commute}
|guard p >> m = m >>= (\x -> guard p >> return x)|
if |m >> mzero = mzero|.
\end{lemma}
\begin{proof} We reason:
\begin{spec}
   m >>= \x -> guard p >> return x
=   {- definition of |guard| -}
   m >>= \x -> (if p then return () else mzero) >> return x
=   {- by \eqref{eq:if-distr}, with |f n = m >>= \x -> n >> return x| -}
   if p  then  m >>= \x -> return () >> return x
         else  m >>= \x -> mzero >> return x
=   {- since |return () >> n = n| and \eqref{eq:bind-mzero-zero} -}
   if p then m else m >> mzero
=   {- assumption: |m >> mzero = mzero| -}
   if p then m else mzero
=   {- since |return () >> n = n| and \eqref{eq:bind-mzero-zero} -}
   if p then return () >> m
        else mzero >> m
=   {- by \eqref{eq:if-distr}, with |f = (>> m)| -}
   (if p then return () else mzero) >> m
=   {- definition of |guard| -}
   guard p >> m {-"~~."-}
\end{spec}
\end{proof}

\section{Local States}

Now we consider monads that satisfy the distributive law:
%format f1
%format f2
\begin{align}
  |m >>= (\x -> f1 x `mplus` f2 x)| &= |(m >>= f1) `mplus` (m >>= f2)| \mbox{~~,}
    \label{eq:mplus-bind-dist}\\
  |m >> mzero| &= |mzero| ~~\mbox{~~.}
    \label{eq:mzero-bind-zero}
\end{align}
In particular, they are satisfied by non-deterministic, stateful monads whose states are duplicated for each non-deterministic branch.

With the law we can prove that state operations and non-determinism
commute.

\paragraph{Commutativity} One important consequence of \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} is that
non-determinism commutes with other effects.

\begin{theorem} \label{thm:nondet-commute}
Assume that \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} hold in addition to the monad laws stated before. Let |m| be a non-deterministic monad in which |x| does not occur free. We have, for |stmt| with arbitrary
effects,
\begin{spec}
  stmt >> \x -> m >>= \y -> f x y =
    m >>= \y -> stmt >>= \x -> f x y {-"~~."-}
\end{spec}
\end{theorem}
\begin{proof} Induction on the structure of |m|.

\noindent{\bf Case} |m := return e|:
\begin{spec}
   stmt >>= \x -> return e >>= \y -> f x y
=    {- monad law \eqref{eq:monad-bind-ret} -}
   stmt >>= \x -> f x e
=    {- monad law \eqref{eq:monad-bind-ret} -}
   return e >>= \y -> stmt >>= \x -> f x y {-"~~."-}
\end{spec}

\noindent{\bf Case} |m := m1 `mplus` m2|:
\begin{spec}
   stmt >>= \x -> (m1 `mplus` m2) >>= \y -> f x y
=   {- by \eqref{eq:bind-mplus-dist} -}
   stmt >>= \x -> (m1 >>= f x) `mplus` (m2 x >>= f x)
=   {- by \eqref{eq:mplus-bind-dist} -}
   (stmt >>= \x -> m1 >>= f x) `mplus` (stmt >>= \x -> m2 >>= f x)
=   {- induction -}
   (m1 >>= \y -> stmt >>= \x -> f x y) `mplus` (m2 >>= \y -> stmt >>= \x -> f x y)
=   {- by \eqref{eq:bind-mplus-dist} -}
   (m1 `mplus` m2) >>= \y -> stmt >>= \x -> f x y {-"~~."-}
\end{spec}

\noindent{\bf Case} |m := mzero|:
\begin{spec}
   stmt >>= \x -> mzero >>= \y -> f x y
=    {- by \eqref{eq:bind-mzero-zero} -}
   stmt >>= \x -> mzero
=    {- by \eqref{eq:mzero-bind-zero} -}
   mzero
     {- by \eqref{eq:bind-mzero-zero} -}
=  mzero >>= \y -> stmt >>= \x -> f x y {-"~~."-}
\end{spec}
\end{proof}

\section{Pure and Monadic Scan}

\paragraph{Scan-left} Define
\begin{code}
scanlM :: (MonadState s m) => (s -> a -> s) -> s -> [a] -> m [s]
scanlM oplus st xs = put st >> foldr otimes (wrap <$> get) xs
  where x `otimes` m =  get >>= \st ->
                        put (st `oplus` x) >>
                        (st:) <$> m {-"~,"-}
\end{code}
where |wrap x = [x]|, and
\begin{code}
protect :: MonadState s m => m b -> m b
protect m = get >>= \ini -> m >>= \x -> put ini >> return x {-"~~."-}
\end{code}

\begin{theorem} We have
%if False
\begin{code}
prop1 ::  forall (m :: * -> *) a s . (MonadState s m)=>
          (s -> a -> s) -> s -> [a] -> m [s]
prop1 oplus st xs =
\end{code}
%endif
\begin{code}
  return (scanl oplus st xs) === protect (scanlM oplus st xs) {-"~~."-}
\end{code}
\end{theorem}
\begin{proof}
Proof by induction on |xs|.

{\bf Case} |xs := []|.
%if False
\begin{code}
prop1_der1 oplus st xs =
\end{code}
%endif
\begin{code}
      protect (scanlM oplus st [])
 ===    {- definitions of |protect| and |scanlM| -}
      get >>= \ini -> put st >> (wrap <$> get) >>= \ys -> put ini >> return ys
 ===    {- definition of |(<$>)| -}
      get >>= \ini -> put st >> get >>= \y -> put ini >> return [y]
 ===    {- |put|-|get| -}
      get >>= \ini -> put st >> put ini >> return [st]
 ===    {- |put|-|put| -}
      get >>= \ini -> put ini >> return [st]
 ===    {- |get|-|put| -}
      return [st]
 ===    {- definition of |scanl| -}
      return (scanl oplus st [])  {-"~~."-}
\end{code}

{\bf Case} |xs := x:xs|.
%if False
\begin{code}
prop1_der2 oplus st x xs =
\end{code}
%endif
\begin{code}
       protect (scanlM oplus st (x:xs))
  ===    {- definition of |protect| and |scanlM|, let |wg = wrap <$> get| -}
       get >>= \ini -> put st >> get >>= \st ->
       put (st `oplus` x) >> ((st:) <$> foldr otimes wg xs) >>= \ys ->
       put ini >> return ys
  ===    {- properties of |(<$>)| -}
       get >>= \ini -> put st >> get >>= \st ->
       put (st `oplus` x) >> foldr otimes wg xs >>= \ys ->
       put ini >> return (st:ys)
  ===    {- |put|-|get| -}
       get >>= \ini -> put st >> put (st `oplus` x) >>
       foldr otimes wg xs >>= \ys -> put ini >> return (st:ys)
  ===    {- |put|-|put| -}
       get >>= \ini -> put (st `oplus` x) >> foldr otimes wg xs >>= \ys ->
       put ini >> return (st:ys)
  ===    {- definition of |scanlM| -}
       get >>= \ini -> scanlM oplus (st `oplus` x) xs >>= \ys ->
       put ini >> return (st:ys)
  ===    {- properties of |(<$>)| -}
       (st:) <$> (get >>= \ini -> scanlM oplus (st `oplus` x) xs >>= \ys ->
      put ini >> return ys)
  ===    {- induction -}
       (st:) <$> return (scanl oplus (st `oplus` x) xs)
  ===  return (st : scanl oplus (st `oplus` x) xs)
  ===  return (scanl oplus st (x:xs)) {-"~~."-}
\end{code}
%if False
\begin{code}
 where x `otimes` m =  get >>= \st ->
                       put (st `oplus` x) >>
                       (st:) <$> m
       wg = wrap <$> get
\end{code}
%endif
\end{proof}

\paragraph{Scan left variation} We define a variation of |scanl| that does not include the initial state in the output.
\begin{code}
scanlp :: (b -> a -> b) -> b -> [a] -> [b]
scanlp oplus st [] = []
scanlp oplus st (x:xs) =
    (st `oplus` x) : scanlp oplus (st `oplus` x) xs {-"~~."-}
\end{code}
For that we define:
\begin{code}
scanlMp :: (MonadState s m) => (s -> a -> s) -> s -> [a] -> m [s]
scanlMp oplus st xs = put st >> foldr otimes (return []) xs
  where x `otimes` m =  get >>= \st ->
                        let st' = st `oplus` x
                        in (st':) <$> (put st' >> m) {-"~~."-}
\end{code}
This |scanlMp| is called |scanlM| in the paper.

\begin{lemma}\label{lma:scanl-loop} We have
%if False
\begin{code}
scanlpscanlMp ::  forall (m :: * -> *) a s . (MonadState s m)=>
          (s -> a -> s) -> s -> [a] -> m [s]
scanlpscanlMp oplus st xs =
\end{code}
%endif
\begin{code}
  return (scanlp oplus st xs) ===
     protect (scanlMp oplus st xs) {-"~~."-}
\end{code}
\end{lemma}
\begin{proof}
Proof by induction on |xs|.

{\bf Case} |xs := []|.
%if False
\begin{code}
scanlpscanlMp_der1 oplus st xs =
\end{code}
%endif
\begin{code}
      protect (scanlMp oplus st [])
 ===  get >>= \ini -> put st >> return [] >>= \ys -> put ini >> return ys
 ===  get >>= \ini -> put st >> put ini >> return []
 ===    {- |put|-|put| -}
      get >>= \ini -> put ini >> return []
 ===    {- |get|-|put| -}
      return []
 ===    {- definition of |scanl| -}
      return (scanlp oplus st [])  {-"~~."-}
\end{code}

{\bf Case} |xs := x:xs|.
%if False
\begin{code}
scanlpscanlMp_der2 oplus st x xs =
\end{code}
%endif
\begin{code}
      protect (scanlMp oplus st (x:xs))
 ===    {- expanding definitions -}
      get >>= \ini -> put st >> get >>= \st ->
      (((st `oplus` x) :) <$> (put (st `oplus` x) >> foldr otimes (return []) xs)) >>= \ys ->
      put ini >> return ys
 ===    {- by \eqref{eq:get-put} -}
      get >>= \ini -> put st >>
      (((st `oplus` x) :) <$> (put (st `oplus` x) >> foldr otimes (return []) xs)) >>= \ys ->
      put ini >> return ys
 ===    {- properties of  |(<$>)| and monad laws -}
      ((st `oplus` x) :) <$> (get >>= \ini -> put st >> put (st `oplus` x) >>
        foldr otimes (return []) xs >>= \ys ->
        put ini >> return ys)
 ===     {- by \eqref{eq:put-put} -}
      ((st `oplus` x) :) <$> (get >>= \ini -> put (st `oplus` x) >>
        foldr otimes (return []) xs >>= \ys ->
        put ini >> return ys)
 ===    {- definitions of |scanlMp| and |protect| -}
      ((st `oplus` x) :) <$> protect (scanlMp oplus (st `oplus` x) xs)
 ===    {- induction -}
      ((st `oplus` x) :) <$> return (scanlp oplus (st `oplus` x) xs)
 ===  return ((st `oplus` x) : scanlp oplus (st `oplus` x) xs)
 ===  return (scanlp oplus st (x:xs)) {-"~~."-}
\end{code}
%if False
\begin{code}
 where x `otimes` m =  get >>= \st ->
                       let st' = st `oplus` x
                       in (st':) <$> (put st' >> m) {-"~~."-}
\end{code}
%endif
\end{proof}

\section{Assert in a Fold}

Consider |assert (all ok . scanlp oplus st)|. We calculate
%if False
\begin{code}
assert_safe_der :: (MonadState s m, MonadPlus m) =>
     (s -> a -> s) -> s -> (s -> Bool) -> [a] -> m [a]
assert_safe_der oplus st ok xs =
\end{code}
%endif
\begin{code}
      assert (all ok . scanlp oplus st) xs
 ===  guard (all ok (scanlp oplus st xs)) >> return xs
 ===  return (scanlp oplus st xs) >>= \ys ->
      guard (all ok ys) >> return xs
 ===    {- Lemma \ref{lma:scanl-loop}, definition of |scanlMp| -}
      protect (scanlMp oplus st xs) >>= \ys ->
      guard (all ok ys) >> return xs
 ===    {- definition of |protect| -}
      get >>= \ini -> scanlMp oplus st xs >>= \ys ->
      put ini >> guard (all ok ys) >> return xs
 ===    {- non-determinism and state commute -}
      get >>= \ini -> scanlMp oplus st xs >>= \ys ->
      guard (all ok ys) >> put ini >> return xs
 ===    {- monad laws, definition of |protect| -}
      protect (scanlMp oplus st xs >>= (guard . all ok) >> return xs)
 ===    {- definition of |scanlMp| -}
      protect (put st >> foldr otimes (return []) xs >> (guard . all ok) >> return xs) {-"~~."-}
\end{code}
%if False
\begin{code}
 where x `otimes` m =  get >>= \st ->
                       put (st `oplus` x) >>
                       (st:) <$> m
\end{code}
%endif

We focus on the sub-expression |foldr otimes (return []) xs  >> (guard . all ok) >> return xs|.
\begin{lemma} \label{lma:foldr-guard-fusion}
Let |otimes| be defined as in |scanlMp|. We have
\begin{spec}
  foldr otimes (return []) xs >>= (guard . all ok) >> return xs =
     foldr odot (return []) xs
    where x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                        put (st `oplus` x) >> ((x:) <$> m) {-"~~."-}
\end{spec}
\end{lemma}
\begin{proof}
Proof by induction on |xs|. (Unfortunately not a |foldr|-fusion, because
|xs| appears in |(guard . all ok) >> return xs|.)

\noindent {\bf Case} |xs := []|.
%if False
\begin{code}
loop_guard_fusion_1 ok =
\end{code}
%endif
\begin{code}
      return [] >>= (guard . all ok) >> return []
 ===  guard (all ok []) >> return []
 ===  return [] {-"~~."-}
\end{code}

\noindent {\bf Case} |xs := x:xs|.
%if False
\begin{code}
loop_guard_fusion_2 oplus ok x xs =
\end{code}
%endif
\begin{code}
      (x `otimes` foldr otimes (return []) xs) >>=
      (guard . all ok) >> return (x:xs)
 ===     {- definition of |otimes| -}
      get >>= \st ->
        (((st `oplus` x):) <$> (put (st `oplus` x) >> foldr otimes (return []) xs)) >>= \ys ->
        guard (all ok ys) >> return (x:xs)
 ===     {- properties of |(<$>)| -}
      get >>= \st -> put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (all ok (st `oplus` x : ys)) >> return (x:xs)
 ===     {- since |guard (p && q) = guard p >> guard q| -}
      get >>= \st -> put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (ok (st `oplus` x)) >>
      guard (all ok ys) >> return (x:xs)
 ===    {- non-determinism commutes with state -}
      get >>= \st -> guard (ok (st `oplus` x)) >>
      put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (all ok ys) >> return (x:xs)
 ===    {- monad laws and properties of |(<$>)| -}
      get >>= \st -> guard (ok (st `oplus` x)) >> put (st `oplus` x) >>
      (x:) <$> (  foldr otimes (return []) xs >>= \ys ->
                  guard (all ok ys) >> return xs)
 ===    {- induction -}
      get >>= \st -> guard (ok (st `oplus` x)) >> put (st `oplus` x) >>
      (x:) <$> foldr odot (return []) xs
 ===    {- definition of |odot| -}
      foldr odot (return []) (x:xs) {-"~~."-}
\end{code}
%if False
\begin{code}
 where x `otimes` m =  get >>= \st ->
                       let st' = st `oplus` x
                       in (st':) <$> (put st' >> m) {-"~~."-}
\end{code}
%endif
\end{proof}


In summary, we now have this corollary performing |assert (all ok . scanlp oplus st)| using a non-deterministic and stateful foldr:
\begin{corollary}\label{thm:assert-scanlp-foldr} Let |odot| be defined as in Theorem \ref{lma:foldr-guard-fusion}. If state and non-determinism commute, we have:
%if False
\begin{code}
assertScanlpFoldr :: (MonadPlus m, MonadState s m) =>
  (s -> Bool) -> (s -> a -> s) -> s -> [a] ->
  (a -> m [a] -> m [a]) -> m [a]
assertScanlpFoldr ok oplus st xs odot =
\end{code}
%endif
\begin{code}
 assert (all ok . scanlp oplus st) xs ===
   protect (put st >> foldr odot (return []) xs) {-"~~."-}
\end{code}
\end{corollary}

\section{Monadic Hylomorphism}

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
The next task is to fuse |unfoldM p f| with |foldr odot (return [])|.

\begin{theorem} \label{thm:hylo-fusion}
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
    (f y >>= (\(x,z) -> (x:) <$> unfoldM p f z)) >>= foldr otimes m
 ===    {- monadic law \eqref{eq:monad-bind-ret} and |foldr| -}
    f y >>= (\(x,z) -> unfoldM p f z >>= \xs -> x `otimes` foldr otimes m xs)
 ===    {- since |n >>= ((x `otimes`) . k) === x `otimes` (n >>= k)| where |n = unfoldM p f z| -}
    f y >>= (\(x,z) -> x `otimes` unfoldM p f z >>=  foldr otimes m)
\end{code}
Now that |unfoldM p f z >>= foldr otimes m| is a fixed-point, we may conclude that it equals |hyloM otimes m p f| if the latter has a unique fixed-point.
\end{proof}

Theorem \ref{thm:hylo-fusion} is not specific to local state. The following lemma applies to any |n| that commutes with state, for example, if |n :: Me N a|.

\begin{lemma} Given |p :: a -> s -> Bool|, |next :: a -> s -> s|, |res :: a -> b -> b|, define |odot :: a -> Me eps b -> Me eps b| with |{N, S s} `sse` eps|:
\begin{spec}
  x `odot` m =  get >>= \st -> guard (p x st) >>
                put (next x st) >> (res x <$> m) {-"~~."-}
\end{spec}
We have |n >>= ((x `odot`) . k) === x `odot` (n >>= k)|, if |n| commutes with state and |m >>= mzero = mzero| for all |m|.
\end{lemma}
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
===   {- since |m >>= mzero = mzero|, by Lemma \ref{lma:guard-commute} -}
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

\paragraph{Concolusion}
To conclude our derivation, a problem formulated as |unfoldM p f >>= assert (all ok . scanlp oplus st)| can be solved by a hylomorphism. Define:
\begin{spec}
solve ::  {N, S s} `sse` eps => (b -> Bool) -> (b -> Me eps (a, b)) ->
          (s -> Bool) -> (s -> a -> s) -> s -> b -> Me eps [a]
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
Given |p :: b -> Bool|, |f :: b -> Me eps (a,b)|, |z :: b|, |ok :: s -> Bool|, |oplus :: s -> a -> s|, |st :: s|, where |{N, S s} `sse` eps|.
If the relation |(not . p)? . snd . (=<<) . f| is well-founded,  \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} hold in addition to the other laws, and |unfoldM p f z| can be typed as |Me N [a]|, we have
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

\section{n-Queens}

Definitions and proofs specific to the |n|-Queens problem.

\paragraph{Permutations} Starting with permutations.

\begin{code}
select :: MonadPlus m => [a] -> m (a, [a])
select []      = mzero
select (x:xs)  = return (x, xs) `mplus` ((id *** (x:)) <$> select xs) {-"~~,"-}

perm :: MonadPlus m => [a] -> m [a]
perm []  = return []
perm xs  = select xs >>= \(x,ys) -> (x:) <$> perm ys {-"~~."-}
\end{code}

\paragraph{Safety} Up and down diagonals, and safety.

\begin{code}
ups, downs :: [Int] -> [Int]
ups    xs  = zipWith (+) [0..] xs  {-"~~,"-}
downs  xs  = zipWith (-) [0..] xs  {-"~~."-}

safe     :: [Int] -> Bool
safe xs  = nodup (ups xs) && nodup (downs xs) {-"~~."-}
\end{code}

%if False
\begin{code}
nodup :: Eq a => [a] -> Bool
nodup [] = True
nodup (x : xs) = not (x `elem` xs) && nodup xs
\end{code}
%endif

\paragraph{Queens} The specification:
\begin{code}
queens :: MonadPlus m => Int -> m [Int]
queens n = assert safe =<< perm [0..n-1] {-"~~."-}
\end{code}

\paragraph{Safety in a |foldl|-ish manner}
If we define:
\begin{spec}
safeL (i,us,ds) xs =
   nodup us' &&  nodup ds' && all (`notelem` us) us' && all (`notelem` ds) ds' {-"~~,"-}
  where  us'  = zipWith (+) [i..] xs
         ds'  = zipWith (-) [i..] xs {-"~~."-}
\end{spec}
We have |safe = safeL (0,[],[])|.


For the next lemma we need this property:
\begin{equation}
  |all (`notelem` (x:xs)) ys = all (`notelem` xs) ys && x `notelem` ys {-"~~."-}| \label{eq:all-notelem-cons}
\end{equation}

\begin{lemma} |safeL st = all ok . scanlp oplus st|, where |oplus| and |ok| are defined by:
\begin{spec}
(i,us,ds) `oplus` x    = (i+1, (i+x : us), (i-x : ds)) {-"~~,"-}
ok (i,(x:us), (y:ds))  = x `notelem` us && y `notelem` ds {-"~~."-}
\end{spec}
\end{lemma}
\begin{proof} Prove that
|safeL st xs = all ok . scanlp oplus st $ xs| by induction on |xs|.

\noindent{\bf Case} |xs := []|. Both sides reduce to |True|.

\noindent{\bf Case} |xs := x:xs|.
\begin{spec}
   all ok (scanlp oplus (i,us,ds) (x:xs))
=    {- definition of |scanlp| -}
   all ok ((i,us,ds) `oplus` x : scanlp oplus ((i,us,ds) `oplus` x) xs)
=    {- definition of |all| -}
   ok ((i,us,ds) `oplus` x) &&
   all ok (scanlp oplus ((i,us,ds) `oplus` x) xs)
=    {- induction -}
   ok ((i,us,ds) `oplus` x) && safeL ((i,us,ds) `oplus` x) xs
=    {- definition of |oplus| and |safeL|, let |us' = zipWith (+) [i+1..] xs| and |ds' = ...| -}
   ok (i+1, (i+x : us), (i-x : ds)) &&
   nodup us' && nodup ds' &&
   all (`notelem` (i+x : us)) us' && all (`notelem` (i-x : ds)) ds'
=    {- by \eqref{eq:all-notelem-cons} -}
   ok (i+1, (i+x : us), (i-x : ds)) &&
   nodup us' && nodup ds' &&
   all (`notelem` us) us' && (i+x) `notelem` us' &&
   all (`notelem` ds) ds' && (i-x) `notelem` ds'
=    {- definiton of |ok| -}
   (i+x) `notelem` us && (i-x) `notelem` ds &&
   nodup us' && nodup ds' &&
   all (`notelem` us) us' && (i+x) `notelem` us' &&
   all (`notelem` ds) ds' && (i-x) `notelem` ds'
=    {- |(&&)| commutative, rearranging for clarity -}
   (i+x) `notelem` us' && nodup us' {-"~"-}&&{-"~"-} (i-x) `notelem` ds' && nodup ds' &&
   (i+x) `notelem` us && all (`notelem` us) us' {-"~"-}&&{-"~"-} (i-x) `notelem` ds && all (`notelem` ds) ds'
=    {- definitions of |nodup| and |all| -}
   nodup ((i+x):us') && nodup ((i-x) :ds') &&
   all (`notelem` us) ((i+x):us') && all (`notelem` ds) ((i-x):ds')
=    {- definition of |safeL| -}
   safeL (i,us,ds) (x:xs) {-"~~."-}
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
\end{code}
%endif
\end{document}
