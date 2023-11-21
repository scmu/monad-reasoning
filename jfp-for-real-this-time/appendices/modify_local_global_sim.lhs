%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

import Background
import Overview
import Control.Monad (ap, liftM, liftM2)
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)
import LocalGlobal
\end{code}
%endif

\section{Proofs for Simulating Local State with Global State using Undo}
\label{app:modify-local-global}

%-------------------------------------------------------------------------------

In this section, we prove the following theorem in \Cref{sec:undo}:

\modifyLocalGlobal*

The proofs are similar to those in \Cref{app:local-global}.

\paragraph*{Preliminary}
It is easy to see that |runStateT . hState| can be fused into a single
fold defined as follows:
\begin{code}
hModify1  :: (Functor f, Undo s r) => Free (ModifyF s r :+: f) a -> (s -> Free f (a, s))
hModify1  =  fold genS (algS # fwdS)
  where
    genS x               s = Var (x, s)
    algS (MGet k)        s = k s s
    algS (MUpdate r k)   s = k (s `plus` r)
    algS (MRestore r k)  s = k (s `minus` r)
    fwdS y               s = Op (fmap ($s) y)
\end{code}
For brevity, we use |hModify1| to replace |runStateT . hModify| in the
following proofs.

%format genLHS = "\Varid{gen}_{\Varid{LHS}}"
%format genRHS = "\Varid{gen}_{\Varid{RHS}}"
%format algSLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{S}}"
%format algSRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{S}}"
%format algNDLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{ND}}"
%format algNDRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{ND}}"
%format fwdLHS = "\Varid{fwd}_{\Varid{LHS}}"
%format fwdRHS = "\Varid{fwd}_{\Varid{RHS}}"
\subsection{Main Proof Structure}
% The main theorem we prove in this section is:
% \begin{theorem}\label{eq:local-global}
% |hGlobal . local2global = hLocal|
% \end{theorem}
The main proof structure of \Cref{thm:modify-local-global} is as
follows.
\begin{proof}
Both the left-hand side and the right-hand side of the equation consist of
function compositions involving one or more folds.
We apply fold fusion separately on both sides to contract each
into a single fold:
\begin{eqnarray*}
|hGlobalM . local2globalM| & = & |fold genLHS (algSLHS # algNDRHS # fwdLHS)| \\
|hLocalM|& = & |fold genRHS (algSRHS # algNDRHS # fwdRHS)|
\end{eqnarray*}
Finally, we show that both folds are equal by showing that their
corresponding parameters are equal:
\begin{eqnarray*}
|genLHS| & = & |genRHS| \\
|algSLHS| & = & |algSRHS| \\
|algNDLHS| & = & |algNDRHS| \\
|fwdLHS| & = & |fwdRHS|
\end{eqnarray*}
We elaborate each of these steps below.
\end{proof}

\subsection{Fusing the Right-Hand Side}
We calculate as follows:
\begin{spec}
    hLocalM
 = {-~  definition -}
    hL . hModify1
      {-" \text{with } "-}
         hL  :: (Functor f, Functor g)
             => g (Free (NondetF :+: f) (a, s)) -> g (Free f [a])
         hL  = fmap (fmap (fmap fst) . hNDf)
 = {-~  definition of |hModify1|  -}
    hL . fold genS (algS # fwdS)
 = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
    fold genRHS (algSRHS # algNDRHS # fwdRHS)
\end{spec}
This last step is valid provided that the fusion conditions are satisfied:
\begin{eqnarray*}
|hL . genS| & = & |genRHS| \\
|hL . (algS # fwdS)| & = & |(algSRHS # algNDRHS # fwdRHS) . fmap hL|
\end{eqnarray*}

We calculate for the first fusion condition:
<   hL (genS x)
< = {-~ definition of |genS| -}
<   hL (\s -> Var (x, s))
< = {-~ definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\s -> Var (x,s))
< = {-~ definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (Var (x,s)))
< = {-~ definition of |hNDf| -}
<   \s -> fmap (fmap fst) (Var [(x,s)])
< = {-~ definition of |fmap| (twice) -}
<   \s -> Var [x]
< = {-~ define |genRHS x = \s -> Var [x]| -}
< = genRHS x

We conclude that the first fusion condition is satisfied by:

< genRHS :: Functor f => a -> (s -> Free f [a])
< genRHS x = \s -> Var [x]

By a straightforward case analysis on the two cases |Inl| and |Inr|,
the second fusion condition decomposes into two separate conditions:
\[\ba{rclr}
|hL . algS| & = & |algSRHS . fmap hL| &\refa{} \\
|hL . fwdS| & = & |(algNDRHS # fwdRHS) . fmap hL| &\refb{}
\ea\]

The first subcondition \refa{} is met by taking:

> algSRHS :: Undo s r => StateF s (s -> p) -> (s -> p)
> algSRHS (MGet k)        = \ s -> k s s
> algSRHS (MUpdate r k)   = \ s -> k (s `plus` r)
> algSRHS (MRestore r k)  = \ s -> k (s `plus` r)

Given this defintion of |algSRHS| we establish that the subcondition
holds, when we apply both sides of the equation to any |t :: StateF s
(s -> Free (NondetF :+: f) (a, s))|.

\vspace{.5\baselineskip}
\noindent \mbox{\underline{case |t = Get k|}}
<   hL (algS (Get k))
< = {-~  definition of |algS| -}
<   hL (\s -> k s s)
< = {-~  definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\s -> k s s)
< = {-~  definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (k s s))
< = {-~  beta-expansion (twice) -}
< = \s -> (\ s1 s2 -> fmap (fmap fst) (hNDf (k s2 s1))) s s
< = {-~  definition of |fmap| (twice) -}
< = \s -> (fmap (fmap (fmap (fmap fst) . hNDf)) (\ s1 s2 -> k s2 s1)) s s
< = {-~  eta-expansion of |k| -}
< = \s -> (fmap (fmap (fmap (fmap fst) . hNDf)) k) s s
< = {-~  definition of |algRHS| -}
< = algSRHS (Get (fmap (fmap (fmap (fmap fst) . hNDf)) k))
< = {-~  definition of |fmap| -}
< = algSRHS (fmap (fmap (fmap (fmap fst) . hNDf)) (Get k))
< = {-~  definition of |hL| -}
< = algSRHS (fmap hL (Get k))

\noindent \mbox{\underline{case |t = MUpdate r k|}}
<   hL (algS (MUpdate r k))
< = {-~  definition of |algS| -}
<   hL (\ s -> k (s `plus` r))
< = {-~  definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\ s -> k (s `plus` r))
< = {-~  definition of |fmap| -}
<   \ s -> fmap (fmap fst) (hNDf (k (s `plus` r)))
< = {-~  beta-expansion -}
< = \ s -> (\ s1 -> fmap (fmap fst) (hNDf (k s1))) (s `plus` r)
< = {-~  definition of |fmap| -}
< = \ s -> (fmap (fmap (fmap fst) . hNDf) (\ s1 -> k s1)) (s `plus` r)
< = {-~  eta-expansion of |k| -}
< = \ s -> (fmap (fmap (fmap fst) . hNDf) k) (s `plus` r)
< = {-~  definition of |algSRHS| -}
< = algSRHS (MUpdate r (fmap (fmap (fmap fst) . hNDf) k))
< = {-~  definition of |fmap| -}
< = algSRHS (fmap (fmap (fmap fst) . hNDf)) (MUpdate r k))
< = {-~  definition of |hL| -}
< = algSRHS (fmap hL (MUpdate r k))

\noindent \mbox{\underline{case |t = MRestore r k|}}
<   hL (algS (MRestore r k))
< = {-~  definition of |algS| -}
<   hL (\ s -> k (s `minus` r))
< = {-~  definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\ s -> k (s `minus` r))
< = {-~  definition of |fmap| -}
<   \ s -> fmap (fmap fst) (hNDf (k (s `minus` r)))
< = {-~  beta-expansion -}
< = \ s -> (\ s1 -> fmap (fmap fst) (hNDf (k s1))) (s `minus` r)
< = {-~  definition of |fmap| -}
< = \ s -> (fmap (fmap (fmap fst) . hNDf) (\ s1 -> k s1)) (s `minus` r)
< = {-~  eta-expansion of |k| -}
< = \ s -> (fmap (fmap (fmap fst) . hNDf) k) (s `minus` r)
< = {-~  definition of |algSRHS| -}
< = algSRHS (MRestore r (fmap (fmap (fmap fst) . hNDf) k))
< = {-~  definition of |fmap| -}
< = algSRHS (fmap (fmap (fmap fst) . hNDf)) (MRestore r k))
< = {-~  definition of |hL| -}
< = algSRHS (fmap hL (MRestore r k))

For the second subcondition \refb{}, we again do a straightforward
case analysis to split it up in two further subconditions:
\[\ba{rclr}
|hL . fwdS . Inl|& = & |algNDRHS . fmap hL| &\refc{}\\
|hL . fwdS . Inr|& = & |fwdRHS . fmap hL| &\refd{}
\ea\]

The first one \refc{} is met by
< algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
< algNDRHS Fail      = \ s -> Var []
< algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)

To show its correctness, given |op :: NondetF (s -> Free (NondetF :+:
f) (a, s))| with |Functor f|, we calculate:

<   hL (fwdS (Inl op))
< = {-~ definition of |fwdS| -}
<   hL (\s -> Op (fmap ($ s) (Inl op)))
< = {-~ definition of |fmap| -}
<   hL (\s -> Op (Inl (fmap ($ s) op)))
< = {-~ definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\s -> Op (Inl (fmap ($ s) op)))
< = {-~ definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (Op (Inl (fmap ($ s) op))))
< = {-~ definition of |hNDf| -}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) op)))

We proceed by a case analysis on |op|:

\noindent \mbox{\underline{case |op = Fail|}}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) Fail)))
< = {-~ defintion of |fmap| (twice) -}
<   \s -> fmap (fmap fst) (algNDf Fail)
< = {-~ definition of |algNDf| -}
<   \s -> fmap (fmap fst) (Var [])
< = {-~ definition of |fmap| (twice) -}
<   \s -> Var []
< = {-~ definition of |algNDRHS| -}
<   algNDRHS Fail
< = {- definition of |fmap| -}
<   algNDRHS (fmap hL fail)

\noindent \mbox{\underline{case |op = Or p q|}}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) (Or p q))))
< = {-~ defintion of |fmap| (twice) -}
<   \s -> fmap (fmap fst) (algNDf (Or (hNDf (p s)) (hNDf (q s))))
< = {-~ definition of |algNDf| -}
<   \s -> fmap (fmap fst) (liftM2 (++) (hNDf (p s)) (hNDf (q s)))
< = {-~ Lemma~\ref{eq:liftM2-fst-comm} -}
<   \s -> liftM2 (++) (fmap (fmap fst) (hNDf (p s))) (fmap (fmap fst) (hNDf (q s)))
< = {-~ definition of |algNDRHS| -}
<   algNDRHS (Or (fmap (fmap fst) . hNDf . p) (fmap (fmap fst) . hNDf . q))
< = {-~ defintion of |fmap| (twice) -}
<   algNDRHS (fmap (fmap (fmap (fmap fst) . hNDf)) (Or p q))
< = {-~ defintion of |hL| -}
<   algNDRHS (fmap hL (Or p q))

% From this we conclude that the definition of |algNDRHS| should be:

% < algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
% < algNDRHS Fail      = \ s -> Var []
% < algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)

The last subcondition \refd{} is met by
< fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
< fwdRHS op = \s -> Op (fmap ($s) op)

To show its correctness, given |op :: f (s -> Free (NondetF :+: f) (a, s))|
with |Functor f|, we calculate:

<   hL (fwdS (Inr op))
< = {-~ definition of |fwdS| -}
<   hL (\s -> Op (fmap ($s) (Inr op)))
< = {-~ definition of |fmap| -}
<   hL (\s -> Op (Inr (fmap ($ s) op)))
< = {-~ definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\s -> Op (Inr (fmap ($ s) op)))
< = {-~ definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (Op (Inr (fmap ($ s) op))))
< = {-~ definition of |hNDf| -}
<   \s -> fmap (fmap fst) (fwdNDf (fmap hNDf (fmap ($ s) op)))
< = {-~ definition of |fwdNDf| -}
<   \s -> fmap (fmap fst) (Op (fmap hNDf (fmap ($ s) op)))
< = {-~ definition of |fmap| -}
<   \s -> Op (fmap (fmap (fmap fst)) (fmap hNDf (fmap ($ s) op)))
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap (fmap (fmap fst) . hNDf) (fmap ($ s) op))
< = {-~ definition of |hL| -}|
<   \s -> Op (hL (fmap ($ s) op))
< = {-~ \Cref{eq:comm-app-fmap} -}
<   \s -> Op (fmap (($s) . hL) op)
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap ($s) (fmap hL op))
< = {-~ definition of |fwdRHS| -}
<   fwdRHS (fmap hL op)

% From this we conclude that the definition of |fwdRHS| should be:

% < fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
% < fwdRHS op = \s -> Op (fmap ($s) op)
