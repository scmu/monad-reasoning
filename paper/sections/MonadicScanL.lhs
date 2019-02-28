%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances,
             ScopedTypeVariables, MultiParamTypeClasses, KindSignatures #-}

module MonadicScanL where

import Control.Arrow ((***))
import Control.Monad
import Control.Monad.State

import Utilities
import Monads

import Queens
\end{code}
%endif

\section{From Pure to Stateful |scanl|}
\label{sec:monadic-scanl}

The aim of this section is to turn the filtering phase |filt (all ok . scanlp oplus st)| into a |foldr|. For that we introduce a state monad to pass the state around.

The state effect provides two operators: |get :: S s `mem` eps => Me eps s| retrieves the state, while |put :: S s `mem` eps =>  s -> Me eps ()| overwrites the state by the given value. They are supposed to satisfy the \emph{state laws}:
\begin{alignat}{2}
&\mbox{\bf put-put}:\quad &
|put st >> put st'| &= |put st'|~~\mbox{,} \label{eq:put-put}\\
&\mbox{\bf put-get}:~ &
|put st >> get| &= |put st >> return st| ~~\mbox{,} \label{eq:get-put}\\
&\mbox{\bf get-put}:~ &
|get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
&\mbox{\bf get-get}:\quad &
|get >>= (\st -> get >>= k st)| &= |get >>= (\st -> k st st)|
~~\mbox{.} \label{eq:get-get}
\end{alignat}
% We define:
% \begin{code}
% overwrite st x  = put st >> return x {-"~~,"-}
% \end{code}
% such that |m >>= overwrite st| overwrites the state to |st| while returning the result of |m|.
% The laws \eqref{eq:put-put} -- \eqref{eq:get-get} will be respectively called |put|-|put|, |put|-|get|, |get|-|put|, and |get|-|get|.

\subsection{From |scanlp| to monadic |foldr|}
\label{sec:scanl-scanlM}

Consider the following monadic variation of |scanl|:
\begin{spec}
scanlM :: S s `mem` eps => (s -> a -> s) -> s -> [a] -> Me eps [s]
scanlM oplus st xs = put st >> foldr otimes (return []) xs
  where x `otimes` m =  get >>= \st -> let st' = st `oplus` x
                        in (st':) <$> (put st' >> m) {-"~~,"-}
\end{spec}
%if False
\begin{code}
scanlM :: (MonadState s m) => (s -> a -> s) -> s -> [a] -> m [s]
scanlM oplus st xs = put st >> foldr otimes (return []) xs
  where x `otimes` m =  get >>= \st -> let st' = st `oplus` x
                        in (st':) <$> (put st' >> m) {-"~~,"-}
\end{code}
%endif
It behaves like |scanlp|, but stores the accumulated information in a monadic state, which is retrieved and stored in each step. The main body of the computation is implemented using a |foldr|.

To relate |scanlp| and |scanlM|, one would like to have |return (scanlp oplus st xs) = scanlM oplus st xs|.
However, the lefthand side does not alter the state, while the righthand side does.
One of the ways to make the equality hold is to manually backup and restore the state.
Define
%if False
\begin{code}
protect :: MonadState s m => m b -> m b
\end{code}
%endif
\begin{code}
protect m {-"~"-}={-"~"-} get >>= \ini -> m >>= \x -> put ini >> return x {-"~~,"-}
\end{code}
We have
\begin{theorem}\label{lma:scanl-loop}
For all |oplus :: (s -> a -> s)|, |st :: s|, and |xs :: [a]|,
%if False
\begin{code}
scanlpscanlM :: forall (m :: * -> *) a s . (MonadState s m)=>
          (s -> a -> s) -> s -> [a] -> m [s]
scanlpscanlM oplus st xs =
\end{code}
%endif
\begin{code}
  return (scanlp oplus st xs) === protect (scanlM oplus st xs) {-"~~."-}
\end{code}
\end{theorem}
\begin{proof} By induction on |xs|. We present the case |xs := x:xs|.
%if False
\begin{code}
scanlpscanlM_der2 :: MonadState s m =>
   (s -> a -> s) -> s -> a -> [a] -> m [s]
scanlpscanlM_der2 oplus st x xs =
\end{code}
%endif
\begin{code}
      protect (scanlM oplus st (x:xs))
 ===    {- expanding definitions, let |st' = st `oplus` x| -}
      get >>= \ini -> put st >> get >>= \st ->
      ((st' :) <$> (put st' >> foldr otimes (return []) xs)) >>= \r ->
      put ini >> return r
 ===    {- by |put|-|get| \eqref{eq:get-put} -}
      get >>= \ini -> put st >>
      ((st' :) <$> (put st' >> foldr otimes (return []) xs)) >>= \r ->
      put ini >> return r
 ===    {- by \eqref{eq:ap-bind-ap} -}
      (st' :) <$> (  get >>= \ini -> put st >> put st' >>
                     foldr otimes (return []) xs >>= \r ->
                     put ini >> return r)
 ===     {- by |put|-|put| \eqref{eq:put-put} -}
      (st' :) <$> (  get >>= \ini -> put st' >> foldr otimes (return []) xs
                     >>= \r -> put ini >> return r)
 ===    {- definitions of |scanlM| and |protect| -}
      (st' :) <$> protect (scanlM oplus st' xs)
 ===    {- induction -}
      (st' :) <$> return (scanlp oplus st' xs)
 ===  return ((st `oplus` x) : scanlp oplus (st `oplus` x) xs)
 ===  return (scanlp oplus st (x:xs)) {-"~~."-}
\end{code}
%if False
\begin{code}
 where st' = st `oplus` x
       x `otimes` m =  get >>= \st ->
                       let st' = st `oplus` x
                       in (st':) <$> (put st' >> m) {-"~~."-}
\end{code}
%endif
%    $
\end{proof}
This proof is instructive due to the use of properties \eqref{eq:put-put} and \eqref{eq:get-put}, and that |(st' :)|, being a pure function, can be easily moved around using \eqref{eq:ap-bind-ap}.

We have learned that |scanlp oplus st| can be turned into |scanlM oplus st|, defined in terms of a stateful |foldr|.
In the definition, state is the only effect involved.
The next task is to transform |filt (scanlp oplus st)| into a |foldr|.
The operator |filt| is defined using non-determinism. The transform therefore involves the interaction between two effects, a tricky topic this paper tries to deal with.

\subsection{Right-Distributivity and Local State}
\label{sec:right-distr-local-state}

We now digress a little to discuss one form of interaction between non-determinism and state.
When mixed with other effects, the following laws hold for some monads with non-determinism, but not all:
\begin{alignat}{2}
&\mbox{\bf right-distributivity}:\quad&
  |m >>= (\x -> f1 x `mplus` f2 x)|~ &=~ |(m >>= f1) `mplus` (m >>= f2)| \mbox{~~,}
    \label{eq:mplus-bind-dist}\\
&\mbox{\bf right-zero}:\quad&
  |m >> mzero|~ &=~ |mzero| ~~\mbox{~~.}
    \label{eq:mzero-bind-zero}
\end{alignat}
With some implementations of the monad, it is likely that in the lefthand side of \eqref{eq:mplus-bind-dist}, the effect of |m| happens once, while in the righthand side it happens twice. In \eqref{eq:mzero-bind-zero}, the |m| on the lefthand side may incur some effects that do not happen in the righthand side.

Having \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} leads to profound consequences on the semantics and implementation of monadic programs.
To begin with, \eqref{eq:mplus-bind-dist} implies that |mplus| be commutative: let |m = m1 `mplus` m2| and |f1 = f2 = return| in \eqref{eq:mplus-bind-dist}.
Implementation of such non-deterministic monads have been studied by Fischer~\shortcite{Fischer:11:Purely}.

When mixed with state, one consequence of \eqref{eq:mplus-bind-dist} is that |get >>= (\s -> f1 s `mplus` f2 s) = (get >>= f1 `mplus` get >>= f2)|. That is, |f1| and |f2| get the same state regardless of whether |get| is performed outside or inside the non-deterministic branch.
Similarly, \eqref{eq:mzero-bind-zero} implies |put s >> mzero = mzero| --- when a program fails, the changes it performed on the state can be discarded.
These requirements imply that each non-deterministic branch has its own copy of the state.
Therefore, we will refer to \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} as \emph{local state laws} in this paper --- even though they do not explicitly mention state operators at all!
One monad satisfying the laws is |Me {N,S s} a = s -> [(a,s)]|, which is the same monad one gets by |StateT s (ListT Identity)| in the Monad Transformer Library~\cite{MTL:14}.
With effect handling~\cite{Wu:14:Effect, KiselyovIshii:15:Freer}, the monad meets the requirements if we run the handler for state before that for list.

The advantage of having the local state laws is that we get many useful properties, which make this stateful non-determinism monad preferred for program calculation and reasoning.
In particular, non-determinism commutes with other effects.
\begin{definition}
Let |m :: Me eps a| where |x| does not occur free, and |n :: Me delta b| where |y| does not occur free. We say |m| and |n| commute if
\begin{equation} \label{eq:commute}
\begin{split}
  |m >>= \x -> n >>= \y -> f x y {-"~"-}=|\\
   |n >>= \y -> m >>= \x -> f x y {-"~~."-}|
\end{split}
\end{equation}
(Notice that |m| and |n| can also be typed as |Me (eps `union` delta)|.) We say that |m| commutes with effect |delta| if |m| commutes with any |n| of type |Me delta b|, and that effects |eps| and |delta| commute if any |m :: Me eps a| and |n :: Me delta b| commute.
\end{definition}

\begin{theorem} \label{thm:nondet-commute}
If right-distributivity \eqref{eq:mplus-bind-dist} and right-zero \eqref{eq:mzero-bind-zero} hold
in addition to the monad laws stated before, non-determinism commutes with any effect |eps|.
\end{theorem}
\begin{proof} By induction on syntax of |n|.
%   The aim is to prove \eqref{eq:commute}, where |n :: Me N a|, by structural induction on syntax of |n|. We show only the case |n := n1 `mplus` n2|:
% \begin{spec}
%    m >>= \x -> (n1 `mplus` n2) >>= \y -> f x y
% =   {- by \eqref{eq:bind-mplus-dist} -}
%    m >>= \x -> (n1 >>= f x) `mplus` (n2 x >>= f x)
% =   {- by \eqref{eq:mplus-bind-dist} -}
%    (m >>= \x -> n1 >>= f x) `mplus` (m >>= \x -> n2 >>= f x)
% =   {- induction -}
%    (n1 >>= \y -> m >>= \x -> f x y) `mplus` (n2 >>= \y -> m >>= \x -> f x y)
% =   {- by \eqref{eq:bind-mplus-dist} -}
%    (n1 `mplus` n2) >>= \y -> m >>= \x -> f x y {-"~~."-}
% \end{spec}
\end{proof}

For the rest of Section \ref{sec:monadic-scanl} and \ref{sec:nd-state-local}, we assume that \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero} hold.

\paragraph{Note} We briefly justify proofs by induction on the syntax tree.
Finite monadic programs can be represented by the free monad constructed out of |return| and the effect operators, which can be represented by an inductively defined data structure, and interpreted by effect handlers~\cite{Kiselyov:13:Extensible, KiselyovIshii:15:Freer}.
When we say two programs |m1| and |m2| are equal, we mean that they have the same denotation when interpreted by the effect handlers of the corresponding effects, for example, |hdNondet (hdState s m1) = hdNondet (hdState s m2)|, where |hdNondet| and |hdState| are respectively handlers for nondeterminism and state.
Such equality can be proved by induction on some sub-expression in |m1| or |m2|, which are treated like any inductively defined data structure.
A more complete treatment is a work in progress, which cannot be fully covered in this paper.
({\em End of Note})



\subsection{Filtering Using a Stateful, Non-Deterministic Fold}
\label{sec:monadic-state-passing-local}

Having dealt with |scanlp oplus st| in Section \ref{sec:scanl-scanlM},
in this section we aim to turn a filter of the form |filt (all ok . scanlp oplus st)| to a stateful and non-deterministic |foldr|.

We calculate, for all |ok|, |oplus|, |st|, and |xs|:
%if False
\begin{code}
filt_safe_der :: (MonadState s m, MonadPlus m) =>
     (s -> a -> s) -> s -> (s -> Bool) -> [a] -> m [a]
filt_safe_der oplus st ok xs =
\end{code}
%endif
\begin{code}
      filt (all ok . scanlp oplus st) xs
 ===  guard (all ok (scanlp oplus st xs)) >> return xs
 ===  return (scanlp oplus st xs) >>= \ys ->
      guard (all ok ys) >> return xs
 ===    {- Theorem \ref{lma:scanl-loop}, definition of |protect|, monad law -}
      get >>= \ini -> scanlM oplus st xs >>= \ys -> put ini >>
      guard (all ok ys) >> return xs
 ===    {- non-determinism commutes with state -}
      get >>= \ini -> scanlM oplus st xs >>= \ys ->
      guard (all ok ys) >> put ini >> return xs
 ===    {- definition of |protect|, monad laws -}
      protect (scanlM oplus st xs >>= (guard . all ok) >> return xs) {-"~~."-}
\end{code}
%if False
\begin{code}
 where x `otimes` m =  get >>= \st ->
                       put (st `oplus` x) >>
                       (st:) <$> m
\end{code}
%endif

Recall that |scanlM oplus st xs = put st >> foldr otimes (return []) xs|.
The following theorem fuses a monadic |foldr| with a |guard| that uses its result.
\begin{theorem}\label{lma:foldr-guard-fusion}
Assume that state and non-determinism commute.
Let |otimes| be defined as that in |scanlM| for any given |oplus :: s -> a -> s|. We have that for all |ok :: s -> Bool| and |xs :: [a]|:
\begin{spec}
  foldr otimes (return []) xs >>= (guard . all ok) >> return xs =
      foldr odot (return []) xs {-"~~,"-}
    where x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                        put (st `oplus` x) >> ((x:) <$> m) {-"~~."-}
\end{spec}
\end{theorem}
\begin{proof} Unfortunately we cannot use a |foldr| fusion, since |xs|
occurs free in |\ys -> guard (all ok ys) >> return xs|. Instead we
use a simple induction on |xs|. For the case |xs := x:xs|:
%if False
\begin{code}
loop_guard_fusion_2 oplus ok x xs =
\end{code}
%endif
\begin{code}
      (x `otimes` foldr otimes (return []) xs) >>= (guard . all ok) >> return (x:xs)
 ===    {- definition of |otimes| -}
      get >>= \st ->
      (((st `oplus` x):) <$> (put (st `oplus` x) >> foldr otimes (return []) xs)) >>=
      (guard . all ok) >> return (x:xs)
 ===    {- monad laws, \eqref{eq:comp-bind-ap}, and \eqref{eq:ap-bind-ap} -}
      get >>= \st -> put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (all ok (st `oplus` x : ys)) >> return (x:xs)
 ===   {- since |guard (p && q) = guard q >> guard p| -}
      get >>= \st -> put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (ok (st `oplus` x)) >> guard (all ok ys) >>
      return (x:xs)
 ===    {- nondeterminism commutes with state -}
      get >>= \st -> guard (ok (st `oplus` x)) >> put (st `oplus` x) >>
      foldr otimes (return []) xs >>= \ys ->
      guard (all ok ys) >> return (x:xs)
 ===    {- monad laws and definition of |(<$>)|  -}
      get >>= \st -> guard (ok (st `oplus` x)) >> put (st `oplus` x) >>
      (x:) <$> (foldr otimes (return []) xs >>= \ys -> guard (all ok ys) >> return xs)
 ===    {- induction -}
      get >>= \st -> guard (ok (st `oplus` x)) >> put (st `oplus` x) >>
      (x:) <$> foldr odot (return []) xs
 ===    {- definition of |odot| -}
      foldr odot (return []) (x:xs) {-"~~."-}
\end{code}
%if False
\begin{code}
 where  x `otimes` m =  get >>= \st ->
                        let st' = st `oplus` x
                        in (st':) <$> (put st' >> m)
        x `odot` m =  get >>= \st -> guard (ok (st `oplus` x)) >>
                      put (st `oplus` x) >> ((x:) <$> m)
\end{code}
%endif
\end{proof}
This proof is instructive due to extensive use of commutativity.

In summary, we now have this corollary performing |filt (all ok . scanlp oplus st)| using a non-deterministic and stateful foldr:
\begin{corollary}\label{thm:filt-scanlp-foldr} Let |odot| be defined as in Theorem \ref{lma:foldr-guard-fusion}. If state and non-determinism commute, we have:
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
\end{corollary}
