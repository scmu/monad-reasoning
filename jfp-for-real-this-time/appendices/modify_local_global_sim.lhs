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
import Undo
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

< algSRHS :: Undo s r => StateF s (s -> p) -> (s -> p)
< algSRHS (MGet k)        = \ s -> k s s
< algSRHS (MUpdate r k)   = \ s -> k (s `plus` r)
< algSRHS (MRestore r k)  = \ s -> k (s `plus` r)

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
%if False
$
%endif

% From this we conclude that the definition of |fwdRHS| should be:

% < fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
% < fwdRHS op = \s -> Op (fmap ($s) op)

\subsection{Fusing the Left-Hand Side}

% We proceed in the same fashion with fusing left-hand side,
% discovering the definitions that we need to satisfy the fusion
% condition.

We calculate as follows:
\begin{spec}
    hGlobalM . local2globalM
 = {-~  definition of |local2globalM| -}
    hGlobalM . fold Var alg
      where
        alg (Inl (MUpdate r k))  = (update r `mplus` side (restore r)) >> k
        alg p                    = Op p
 = {-~  fold fusion-post' (Equation \ref{eq:fusion-post-strong})  -}
    fold genLHS (algSLHS # algNDLHS # fwdLHS)
\end{spec}

This last step is valid provided that the fusion conditions are satisfied:
\[\ba{rclr}
|hGlobalM . Var| & = & |genLHS| &\refa{}\\
|hGlobalM . alg . fmap local2globalM| & = & |(algSLHS # algNDLHS # fwdLHS) . fmap hGlobalM . fmap local2globalM| &\refb{}
\ea\]

The first subcondition \refa{} is met by
< genLHS :: Functor f => a -> (s -> Free f [a])
< genLHS x = \s -> Var [x]
as established in the following calculation:
<   hGlobalM (Var x)
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2 (Var x))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (Var x)))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (Var [x]))
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst) (\s -> Var ([x], s))
< = {-~ definition of |fmap| (twice) -}
<   \s -> Var [x]
< = {-~ definition of |genLHS| -}
<   genLHS x


We can split the second fusion condition \refb{} in three
subconditions:
\[\ba{rclr}
|hGlobalM . alg . Inl . fmap local2globalM| & = & |algSLHS . fmap hGlobalM . fmap local2globalM| &\refc{}\\
|hGlobalM . alg . Inr . Inl . fmap local2globalM| & = & |algNDLHS . fmap hGlobalM . fmap local2globalM| &\refd{}\\
|hGlobalM . alg . Inr . Inr . fmap local2globalM| & = & |fwdLHS . fmap hGlobalM . fmap local2globalM| &\refe{}
\ea\]

For the first subcondition \refc{}, we can define |algSLHS| as follows.
< algSLHS :: (Functor f, Undo s r) => ModifyF s r (s -> Free f [a]) -> (s -> Free f [a])
< algSLHS (MGet k)        =  \s -> k s s
< algSLHS (MUpdate r k)   = \ s -> k (s `plus` r)
< algSLHS (MRestore r k)  = \ s -> k (s `plus` r)

We prove it by a case analysis on the shape of input |op :: ModifyF s
r (Free (ModifyF s r :+: NondetF :+: f) a)|.
%
For brevity, we omit the last common part |fmap local2globalM| of the
equation \refc{}. Instead, we assume that |op| is in the codomain of
|fmap local2globalM|.

We proceed by a case analysis on |op|.

\vspace{0.5\lineskip}

\noindent \mbox{\underline{case |op = MGet k|}}
<   hGlobalM (alg (Inl (MGet k)))
< = {-~ definition of |alg| -}
<   hGlobalM (Op (Inl (MGet k)))
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2 (Op (Inl (MGet k))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inr (Inl (fmap comm2 (MGet k)))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inr (Inl (MGet (comm2 . k)))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (Op (fmap hNDf (Inl (MGet (comm2 . k))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hModify1 (Op (Inl (MGet (hNDf . comm2 . k)))))
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst) (\s -> (hModify1 . hNDf . comm2 . k) s s)
< = {-~ definition of |fmap| -}
<   (\s -> fmap fst ((hModify1 . hNDf . comm2 . k) s s))
< = {-~ definition of |fmap| -}
<   (\s -> ((fmap (fmap fst) . hModify1 . hNDf . comm2 . k) s s))
< = {-~ definition of |algSLHS| -}
<   algSLHS (MGet (hGlobalM . k))
< = {-~ definition of |fmap| -}
<   algSLHS (fmap hGlobalM (MGet k))

\noindent \mbox{\underline{case |op = MUpdate r k|}}
From |op| is in the codomain of |fmap local2globalM| we obtain |k| is
in the codomain of |local2globalM|.

<   hGlobalM (alg (Inl (MUpdate r k)))
< = {-~ definition of |alg| -}
<   hGlobalM ((update r `mplus` side (restore r)) >> k)
< = {-~ definitions of |side|, |update|, |restore|, |mplus|, and |(>>)| -}
<   hGlobalM (Op (Inr (Inl (Or  (Op (Inl (MUpdate r k)))
<                               (Op (Inl (MRestore r (Op (Inr (Inl Fail))))))))))
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2
<     (Op (Inr (Inl (Or  (Op (Inl (MUpdate r k)))
<                        (Op (Inl (MRestore r (Op Inr ((Inl Fail)))))))))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (
<     (Op (Inl (Or  (Op (Inr (Inl (MUpdate r (comm2 k)))))
<                   (Op (Inr (Inl (MRestore r (Op (Inl Fail))))))))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (
<     (liftM2 (++)  (Op (Inl (MUpdate r (hNDf (comm2 k)))))
<                   (Op (Inl (MRestore r (Var [])))))))
< = {-~ definition of |liftM2| -}
<   fmap (fmap fst) (hModify1 (
<     do  x <- Op (Inl (MUpdate r (hNDf (comm2 k))))
<         y <- Op (Inl (MRestore r (Var [])))
<         Var (x ++ y)
<   ))
< = {-~ \Cref{lemma:dist-hModify1} -}
<   fmap (fmap fst) (\ t ->
<     do  (x,t1) <- hModify1 (Op (Inl (MUpdate r (hNDf (comm2 k))))) t
<         (y,t2) <- hModify1 (Op (Inl (MRestore r (Var [])))) t1
<         hModify1 (Var (x ++ y)) t2
<   )
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst)
<     (\t -> do  (x,_)   <- hModify1 (hNDf (comm2 k)) (t `plus` r)
<                (y,t2)  <- Var ([], t `minus` r)
<                Var (x ++ y, t2)
<     )
< = {-~ monad law -}
<   fmap (fmap fst)
<     (\t -> do  (x,t1) <- hModify1 (hNDf (comm2 k)) (t `plus` r)
<                Var (x ++ [], t1 `minus` r)
<     )
< = {-~ right unit of |(++)| -}
<   fmap (fmap fst)
<     (\t -> do  (x,t1) <- hModify1 (hNDf (comm2 k)) (t `plus` r)
<                Var (x, t1 `minus` r)
<     )
< = {-~ \Cref{lemma:modify-state-restore} -}
<   fmap (fmap fst)
<     (\t -> do  (x, t `plus` r) <- hModify1 (hNDf (comm2 k)) (t `plus` r)
<                Var (x, (t `plus` r) `minus` r)
<     )
< = {-~ \Cref{eq:plus-minus} -}
<   fmap (fmap fst)
<     (\t -> do  (x, _) <- hModify1 (hNDf (comm2 k)) (t `plus` r)
<                Var (x, t)
<     )
< = {-~ definition of |fmap fst| -}
<   fmap (fmap fst)
<     (\t -> do  x <- fmap fst (hModify1 (hNDf (comm2 k)) (t `plus` r))
<                Var (x, t)
<     )
< = {-~ definition of |fmap| -}
<   fmap (fmap fst)
<     (\t -> do  x <- (fmap (fmap fst) (hModify1 (hNDf (comm2 k)))) (t `plus` r)
<                Var (x, t)
<     )
< = {-~ definition of |fmap (fmap fst)| -}
<   \ t -> do  x <- (fmap (fmap fst) (hModify1 (hNDf (comm2 k)))) (t `plus` r)
<              Var x
< = {-~ monad law -}
<   \ t -> (fmap (fmap fst) (hModify1 (hNDf (comm2 k)))) (t `plus` r)
< = {-~ definition of |hGlobalM| -}
<   \ t -> (hGlobalM k) (t `plus` r)
< = {-~ definition of |algSLHS| -}
<   algSLHS (MUpdate r (hGlobalM k))
< = {-~ definition of |fmap| -}
<   algSLHS (fmap hGlobalM (MUpdate r k))


% Let's consider the second subcondition \refd{}. It has also two cases:
For the second subcondition \refd{}, we can define |algNDLHS| as
follows.
< algNDLHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
< algNDLHS Fail      = \s -> Var []
< algNDLHS (Or p q)  = \s -> liftM2 (++) (p s) (q s)

We prove it by a case analysis on the shape of input |op :: NondetF
(Free (ModifyF s r :+: NondetF :+: f) a)|.
%
For brevity, we omit the last common part |fmap local2globalM| of the
equation \refc{}. Instead, we assume that |op| is in the codomain of
|fmap local2globalM|.

We proceed by a case analysis on |op|.

\noindent \mbox{\underline{case |op = Fail|}}
<   hGlobalM (alg (Inr (Inl Fail)))
< = {-~ definition of |alg| -}
<   hGlobalM (Op (Inr (Inl Fail)))
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2 (Op (Inr (Inl Fail))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inl (fmap comm2 Fail)))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inl Fail))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (Var []))
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst) (\s -> Var ([], s))
< = {-~ definition of |fmap| twice and |fst| -}
<   \s -> Var []
< = {-~ definition of |algNDRHS|  -}
<  algNDRHS Fail
< = {-~ definition of |fmap| -}
<  algNDRHS (fmap hGlobalM Fail)

\noindent \mbox{\underline{case |op = Or p q|}}
<   hGlobalM (alg (Inr (Inl (Or p q))))
< = {-~ definition of |alg| -}
<   hGlobalM (Op (Inr (Inl (Or p q))))
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2 (Op (Inr (Inl (Or p q)))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inl (fmap comm2 (Or p q))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inl (Or (comm2 p) (comm2 q))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (liftM2 (++) (hNDf (comm2 p)) (hNDf (comm2 q))))
< = {-~ definition of |liftM2| -}
<   fmap (fmap fst) (hModify1 (do  x <- hNDf (comm2 p)
<                                  y <- hNDf (comm2 q)
<                                  return (x ++ y)))
< = {-~ \Cref{lemma:dist-hModify1} -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- hModify1 (hNDf (comm2 p)) s0
<                               (y, s2) <- hModify1 (hNDf (comm2 q)) s1
<                               hModify1 (return (x ++ y)) s2))
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- hModify1 (hNDf (comm2 p)) s0
<                               (y, s2) <- hModify1 (hNDf (comm2 q)) s1
<                               Var (x ++ y, s2)))
< = {-~ Lemma \ref{lemma:modify-state-restore} (|p| and |q| are in the codomain of |local2globalM|) -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- do {(x,_) <- hModify1 (hNDf (comm2 p)) s0; return (x, s0)}
<                               (y, s2) <- do {(y,_) <- hModify1 (hNDf (comm2 q)) s1; return (x, s1)}
<                               Var (x ++ y, s2)))
< = {-~ monad laws -}
<   fmap (fmap fst) (\s0-> (do  (x,_) <- hModify1 (hNDf (comm2 p)) s0
<                               (y,_) <- hModify1 (hNDf (comm2 q)) s0
<                               Var (x ++ y, s0)))
< = {-~ definition of |fmap| (twice) and |fst| -}
<   \s0-> (do  (x,_) <- hModify1 (hNDf (comm2 p)) s0
<              (y,_) <- hModify1 (hNDf (comm2 q)) s0
<              Var (x ++ y))
< = {-~ definition of |fmap|, |fst| and monad laws -}
<   \s0-> (do  x <- fmap fst (hModify1 (hNDf (comm2 p)) s0)
<              y <- fmap fst (hModify1 (hNDf (comm2 q)) s0)
<              Var (x ++ y))
< = {-~ definition of |fmap| -}
<   \s0-> (do  x <- fmap (fmap fst) (hModify1 (hNDf (comm2 p))) s0
<              y <- fmap (fmap fst) (hModify1 (hNDf (comm2 q))) s0
<              Var (x ++ y))
< = {-~ definition of |hGlobalM| -}
<   \s0-> (do  x <- hGlobalM p s0
<              y <- hGlobalM q s0
<              Var (x ++ y))
< = {-~ definition of |liftM2| -}
<   \s0-> liftM2 (++) (hGlobalM p s0) (hGlobalM q s0)
< = {-~ definition of |algNDLHS|  -}
<   algNDLHS (Or (hGlobalM p) (hGlobalM q))
< = {-~ definition of |fmap| -}
<   algNDLHS (fmap hGobal (Or p q))

% Finally, the last subcondition:
For the second subcondition \refe{}, we can define |algNDLHS| as
follows.
< fwdLHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
< fwdLHS op = \s -> Op (fmap ($ s) op)

We prove it by a case analysis on the shape of input |op :: f
(Free (ModifyF s r :+: NondetF :+: f) a)|.
%
For brevity, we omit the last common part |fmap local2globalM| of the
equation \refc{}. Instead, we assume that |op| is in the codomain of
|fmap local2globalM|.

<   hGlobalM (alg (Inr (Inr op)))
< = {-~ definition of |alg| -}
<   hGlobalM (Op (Inr (Inr op)))
< = {-~ definition of |hGlobalM| -}
<   fmap (fmap fst) (hModify1 (hNDf (comm2 (Op (Inr (Inr op))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hModify1 (hNDf (Op (Inr (Inr (fmap comm2 op))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hModify1 (Op (fmap hNDf (Inr (fmap comm2 op)))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hModify1 (Op (Inr (fmap hNDf (fmap comm2 op)))))
< = {-~ |fmap| fusion -}
<   fmap (fmap fst) (hModify1 (Op (Inr (fmap (hNDf . comm2) op))))
< = {-~ definition of |hModify1| -}
<   fmap (fmap fst) (\s -> Op (fmap ($ s) (fmap hModify1 (fmap (hNDf . comm2) op))))
< = {-~ |fmap| fusion -}
<   fmap (fmap fst) (\s -> Op (fmap ($ s) (fmap (hModify1 . hNDf . comm2) op)))
< = {-~ definition of |fmap| -}
<   \s -> fmap fst (Op (fmap ($ s) (fmap (hModify1 . hNDf . comm2) op)))
< = {-~ definition of |fmap| -}
<   \s -> Op (fmap (fmap fst) (fmap ($ s) (fmap (hModify1 . hNDf . comm2) op)))
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap (fmap fst . ($ s)) (fmap (hModify1 . hNDf . comm2) op)))
< = {-~ \Cref{eq:comm-app-fmap} -}
<   \s -> Op (fmap (($ s) . fmap (fmap fst)) (fmap (hModify1 . hNDf . comm2) op)))
< = {-~ |fmap| fission -}
<   \s -> Op ((fmap ($ s) . fmap (fmap (fmap fst))) (fmap (hModify1 . hNDf . comm2) op))
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap ($ s) (fmap (fmap (fmap fst) . hModify1 . hNDf . comm2) op))
< = {-~ definition of |hGlobalM| -}
<   \s -> Op (fmap ($ s) (fmap hGlobalM op))
< = {-~ definition of |fwdLHS|  -}
<   fwdLHS (fmap hGlobalM op)


\subsection{Equating the Fused Sides}

We observe that the following equations hold trivially.
\begin{eqnarray*}
|genLHS| & = & |genRHS| \\
|algSLHS| & = & |algSRHS| \\
|algNDLHS| & = & |algNDRHS| \\
|fwdLHS| & = & |fwdRHS|
\end{eqnarray*}

Therefore, the main theorem (\Cref{thm:modify-local-global}) holds.

\subsection{Auxiliary Lemmas}

The derivations above made use of several auxliary lemmas.
We prove them here.

\begin{lemma}[Distributivity of |hModify1|] \label{lemma:dist-hModify1} \ \\
\[
|hModify1 (p >>= k) s| \quad =\quad |hModify1 p s >>= \ (x,s') -> hModify1 (k x) s'|
\]
\end{lemma}

\begin{proof}
The proof follows the same structure of \Cref{lemma:dist-hState1}.
%
We proceed by induction on |p|.

\noindent \mbox{\underline{case |p = Var x|}}

<    hModify1 (Var x >>= k) s
< = {-~  monad law  -}
<    hModify1 (k x) s
< = {-~  monad law  -}
<    return (x, s) >>= \ (x,s') -> hModify1 (k x) s'
< = {-~  definition of |hModify1|  -}
<    hModify1 (Var x) s >>= \ (x,s') -> hModify1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inl (MGet p))|}}

<    hModify1 (Op (Inl (MGet p)) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hModify1 (Op (fmap (>>= k) (Inl (MGet p)))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hModify1 (Op (Inl (fmap (>>= k) (MGet p)))) s
< = {-~  definition of |fmap| for |MGet|  -}
<    hModify1 (Op (Inl (MGet (\x -> p s >>= k)))) s
< = {-~  definition of |hModify1|  -}
<    hModify1 (p s >>= k) s
< = {-~  induction hypothesis  -}
<    hModify1 (p s) s >>= \ (x,s') -> hModify1 (k x) s'
< = {-~  definition of |hModify1|  -}
<    hModify1 (Op (Inl (MGet p))) s >>= \ (x,s') -> hModify1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inl (MUpdate r p))|}}

<    hModify1 (Op (Inl (MUpdate r p)) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hModify1 (Op (fmap (>>= k) (Inl (MUpdate r p)))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hModify1 (Op (Inl (fmap (>>= k) (MUpdate r p)))) s
< = {-~  definition of |fmap| for |MUpdate|  -}
<    hModify1 (Op (Inl (MUpdate r (p >>= k)))) s
< = {-~  definition of |hModify1|  -}
<    hModify1 (p >>= k) (s `plus` r)
< = {-~  induction hypothesis  -}
<    hModify1 p (s `plus` r) >>= \ (x, s') -> hModify1 (k x) s'
< = {-~  definition of |hModify1|  -}
<    hModify1 (Op (Inl (MUpdate r p))) s >>= \ (x, s') -> hModify1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inl (MRestore r p))|}}

<    hModify1 (Op (Inl (MRestore r p)) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hModify1 (Op (fmap (>>= k) (Inl (MRestore r p)))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hModify1 (Op (Inl (fmap (>>= k) (MRestore r p)))) s
< = {-~  definition of |fmap| for |MRestore|  -}
<    hModify1 (Op (Inl (MRestore r (p >>= k)))) s
< = {-~  definition of |hModify1|  -}
<    hModify1 (p >>= k) (s `minus` r)
< = {-~  induction hypothesis  -}
<    hModify1 p (s `minus` r) >>= \ (x, s') -> hModify1 (k x) s'
< = {-~  definition of |hModify1|  -}
<    hModify1 (Op (Inl (MRestore r p))) s >>= \ (x, s') -> hModify1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inr y)|}}

<    hModify1 (Op (Inr y) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hModify1 (Op (fmap (>>= k) (Inr y))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hModify1 (Op (Inr (fmap (>>= k) y))) s
< = {-~  definition of |hModify1|  -}
<    Op (fmap (\x -> hModify1 x s) (fmap (>>= k) y))
< = {-~  |fmap| fusion  -}
<    Op (fmap ((\x -> hModify1 (x >>= k) s)) y)
< = {-~  induction hypothesis  -}
<    Op (fmap (\x -> hModify1 x s >>= \ (x',s') -> hModify1 (k x') s') y)
< = {-~  |fmap| fission -}
<    Op (fmap (\x -> x >>= \ (x',s') -> hModify1 (k x') s') (fmap (\x -> hModify1 x s) y))
< = {-~  definition of |(>>=)| -}
<    Op ( (fmap (\x -> hModify1 x s) y)) >>= \ (x',s') -> hModify1 (k x') s'
< = {-~  definition of |hModify1|  -}
<    Op (Inr y) s >>= \ (x',s') -> hModify1 (k x') s'

\end{proof}

\begin{lemma}[State is Restored] \label{lemma:modify-state-restore} \ \\
\[\ba{ll}
  &|hModify1 (hNDf (local2globalM p)) s| \\
= &|do (x, _) <- hModify1 (hNDf (local2globalM p)) s; return (x, s)|
\ea\]
\end{lemma}

\begin{proof}
The proof follows the same structure of \Cref{lemma:state-restore}.
%
We proceed by induction on |t|.
% In the following proofs, we assume implicit commutativity and associativity of
% the coproduct operator |(:+:)| (\Cref{sec:transforming-between-local-and-global-state}).
% We assume the smart constructors |getOp, putOp, orOp, failOp|, which are wrappers around
% constructors |Get, Put, Or, Fail|, respectively, automatically insert correct |Op, Inl, Inr|
% constructors based on the context to make the term well-typed in the following proof.

\noindent \mbox{\underline{case |t = Var y|}}
<    hModify1 (hNDf (comm2 (local2globalM (Var y)))) s
< = {-~  definition of |local2globalM|  -}
<    hModify1 (hNDf (comm2 (Var y))) s
< = {-~  definition of |comm2|  -}
<    hModify1 (hNDf (Var y)) s
< = {-~  definition of |hNDf|  -}
<    hModify1 (Var [y]) s
< = {-~  definition of |hModify1|  -}
<    Var ([y], s)
< = {-~  monad law -}
<    do (x,_) <- Var ([y], s); Var (x, s)
< = {-~  definition of |local2globalM, hNDf, comm2, hModify1| and |return|  -}
<    do (x,_) <- hModify1 (hNDf (comm2 (local2globalM (Var y)))) s; return (x, s)

\noindent \mbox{\underline{case |t = Op (Inl (MGet k))|}}
<    hModify1 (hNDf (comm2 (local2globalM (Op (Inl (MGet k)))))) s
< = {-~  definition of |local2globalM|  -}
<    hModify1 (hNDf (comm2 (Op (Inl (MGet (local2globalM . k)))))) s
< = {-~  definition of |comm2|  -}
<    hModify1 (hNDf (Op (Inr (Inl (MGet (comm2 . local2globalM . k)))))) s
< = {-~  definition of |hNDf|  -}
<    hModify1 (Op (Inl (MGet (hNDf . comm2 . local2globalM . k)))) s
< = {-~  definition of |hModify1|  -}
<    (hModify1 . hNDf . comm2 . local2globalM . k) s s
< = {-~  definition of |(.)|  -}
<    (hModify1 (hNDf (comm2 (local2globalM (k s))))) s
< = {-~  induction hypothesis  -}
<    do (x, _) <- hModify1 (comm2 (hNDf (local2globalM (k s)))) s; return (x, s)
< = {-~  definition of |local2globalM, comm2, hNDf, hModify1|  -}
<    do (x, _) <- hModify1 (hNDf (local2globalM (Op (Inl (MGet k))))) s; return (x, s)

\noindent \mbox{\underline{case |t = Op (Inr (Inl Fail))|}}
<    hModify1 (hNDf (comm2 (local2globalM (Op (Inr (Inl Fail)))))) s
< = {-~  definition of |local2globalM|  -}
<    hModify1 (hNDf (comm2 (Op (Inr (Inl Fail))))) s
< = {-~  definition of |comm2|  -}
<    hModify1 (hNDf (Op (Inl Fail))) s
< = {-~  definition of |hNDf|  -}
<    hModify1 (Var []) s
< = {-~  definition of |hModify1|  -}
<    Var ([], s)
< = {-~  monad law -}
<    do (x, _) <- Var ([], s); Var (x, s)
< = {-~  definition of |local2globalM, comm2, hNDf, hModify1|  -}
<    do (x, _) <- hModify1 (hNDf (comm2 (local2globalM (Op (Inr (Inl Fail)))))) s; return (x, s)

TODO

\end{proof}
