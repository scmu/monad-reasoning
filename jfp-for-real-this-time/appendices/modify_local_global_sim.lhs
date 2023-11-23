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
< = {-~ \Cref{eq:dist-hModify1} -}
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
< = {-~ \Cref{eq:modify-state-restore} -}
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




\subsection{Equating the Fused Sides}

We observe that the following equations hold trivially.
\begin{eqnarray*}
|genLHS| & = & |genRHS| \\
|algSLHS| & = & |algSRHS| \\
|algNDLHS| & = & |algNDRHS| \\
|fwdLHS| & = & |fwdRHS|
\end{eqnarray*}

Therefore, the main theorem holds.

\subsection{Auxiliary Lemmas}

The derivations above made use of several auxliary lemmas.
We prove them here.

\begin{lemma}[Distributivity of |hModify1|] \label{lemma:dist-hModify1} \ \\
< hState1 (p >>= k) s = hState1 p s >>= \ (x,s') -> hState1 (k x) s'
\end{lemma}

\begin{proof}
The proof proceeds by induction on |p|.

\noindent \mbox{\underline{case |p = Var x|}}

<    hState1 (Var x >>= k) s
< = {-~  monad law  -}
<    hState1 (k x) s
< = {-~  monad law  -}
<    return (x, s) >>= \(x,s') -> hState1 (k x) s'
< = {-~  definition of |hState1|  -}
<    hState1 (Var x) s >>= \(x,s') -> hState1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inl (Get p))|}}

<    hState1 (Op (Inl (Get p)) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hState1 (Op (fmap (>>= k) (Inl (Get p)))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hState1 (Op (Inl (fmap (>>= k) (Get p)))) s
< = {-~  definition of |fmap| for |Get|  -}
<    hState1 (Op (Inl (Get (\x -> p s >>= k)))) s
< = {-~  definition of |hState1|  -}
<    hState1 (p s >>= k) s
< = {-~  induction hypothesis  -}
<    hState1 (p s) s >>= \(x,s') -> hState1 (k x) s'
< = {-~  definition of |hState1|  -}
<    hState1 (Op (Inl (Get p))) s >>= \(x,s') -> hState1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inl (Put t p))|}}

<    hState1 (Op (Inl (Put t p)) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hState1 (Op (fmap (>>= k) (Inl (Put t p)))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hState1 (Op (Inl (fmap (>>= k) (Put t p)))) s
< = {-~  definition of |fmap| for |Put|  -}
<    hState1 (Op (Inl (Put t (p >>= k)))) s
< = {-~  definition of |hState1|  -}
<    hState1 (p >>= k) t
< = {-~  induction hypothesis  -}
<    hState1 p t >>= \(x, s') -> hState1 (k x) s'
< = {-~  definition of |hState1|  -}
<    hState1 (Op (Inl (Put t p))) s >>= \(x,s') -> hState1 (k x) s'

\noindent \mbox{\underline{case |p = Op (Inr y)|}}

<    hState1 (Op (Inr y) >>= k) s
< = {-~  definition of |(>>=)| for free monad  -}
<    hState1 (Op (fmap (>>= k) (Inr y))) s
< = {-~  definition of |fmap| for coproduct |(:+:)|  -}
<    hState1 (Op (Inr (fmap (>>= k) y))) s
< = {-~  definition of |hState1|  -}
<    Op (fmap (\x -> hState1 x s) (fmap (>>= k) y))
< = {-~  |fmap| fusion  -}
<    Op (fmap ((\x -> hState1 (x >>= k) s)) y)
< = {-~  induction hypothesis  -}
<    Op (fmap (\x -> hState1 x s >>= \(x',s') -> hState1 (k x) s') y)
< = {-~  |fmap| fission -}
<    Op (fmap (\x -> x >>= \(x',s') -> hState1 (k x) s') (fmap (\x -> hState1 x s) y))
< = {-~  definition of |(>>=)| -}
<    Op ( (fmap (\x -> hState1 x s) y)) >>= \(x',s') -> hState1 (k x) s'
< = {-~  definition of |hState1|  -}
<    Op (Inr y) s >>= \ (x',s') -> hState1 (k x) s'

\end{proof}

\begin{lemma}[State is Restored] \label{lemma:modify-state-restore} \ \\
< hModify1 (hNDf (local2globalM t)) s = do (x, _) <- hModify1 (hNDf (local2globalM t)) s; return (x, s)
\end{lemma}

\begin{proof}
The proof proceeds by structural induction on |t|.
% In the following proofs, we assume implicit commutativity and associativity of
% the coproduct operator |(:+:)| (\Cref{sec:transforming-between-local-and-global-state}).
% We assume the smart constructors |getOp, putOp, orOp, failOp|, which are wrappers around
% constructors |Get, Put, Or, Fail|, respectively, automatically insert correct |Op, Inl, Inr|
% constructors based on the context to make the term well-typed in the following proof.

\noindent \mbox{\underline{case |t = Var y|}}
<    hState1 (hNDf (local2global (Var y))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf (Var y)) s
< = {-~  definition of |hNDf|  -}
<    hState1 (Var [y]) s
< = {-~  definition of |hState1|  -}
<    Var ([y], s)
< = {-~  monad law -}
<    do (x,_) <- Var ([y], s); Var (x, s)
< = {-~  definition of |local2global, hNDf, hState1| and |return|  -}
<    do (x,_) <- hState1 (hNDf (local2global (Var y))) s; return (x, s)

TODO

\noindent \mbox{\underline{case |t = getOp k|}}
<    hState1 (hNDf (local2global (getOp k))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf (getOp (local2global . k))) s
< = {-~  definition of |hNDf|  -}
<    hState1 (getOp (hNDf . local2global . k)) s
< = {-~  definition of |hState1|  -}
<    (hState1 . hNDf . local2global . k) s s
< = {-~  function application  -}
<    hState1 (hNDf (local2global (k s))) s
< = {-~  induction hypothesis  -}
<    do (x, _) <- hState1 (hNDf (local2global (k s))) s; return (x, s)
< = {-~  definition of |local2global, hNDf, hState1|  -}
<    do (x, _) <- hState1 (hNDf (local2global (getOp k))) s; return (x, s)

\noindent \mbox{\underline{case |t = failOp|}}
<    hState1 (hNDf (local2global (failOp))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf failOp) s
< = {-~  definition of |hNDf|  -}
<    hState1 (return []) s
< = {-~  definition of |hState1|  -}
<    \ s -> return ([], s)
< = {-~  reformulation  -}
<    do (x, _) <- return ([], s); return (x, s)
< = {-~  definition of |local2global, hNDf, hState1|  -}
<    do (x, _) <- hState1 (hNDf (local2global failOp)) s; return (x, s)

\noindent \mbox{\underline{case |t = putOp t k|}}
<    hState1 (hNDf (local2global (putOp t k))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf (putR t >> local2global k)) s
< = {-~  definition of |putR|  -}
<    hState1 (hNDf ((get >>= \t' -> put t `mplus` side (put t')) >> local2global k)) s
< = {-~  definition of |orOp|  -}
<    hState1 (hNDf (do t' <- get; orOp (put t) (side (put t')); local2global k)) s
< = {-~  definition of |side| and |failOp|  -}
<    hState1 (hNDf (do t' <- get; orOp (put t) ((put t') >> failOp); local2global k)) s
< = {-~  reformulation  -}
<    hState1 (hNDf (getOp (\t' -> orOp (putOp t (local2global k)) (putOp t' (failOp >> local2global k)))) s
< = {-~  Law (\ref{eq:mzero-zero}): left identity of |mzero| or |failOp|  -}
<    hState1 (hNDf (getOp (\t' -> orOp (putOp t (local2global k)) (putOp t' failOp))) s
< = {-~  definition of |hNDf|  -}
<    hState1 (do  t'  <- get;
<                 x   <- hNDf (putOp t (local2global k));
<                 y   <- hNDf (putOp t' failOp);
<                 return (x ++ y)) s
< = {-~  definition of |hNDf|  -}
<    hState1 (do  t'  <- get;
<                 put t;
<                 x   <- hNDf (local2global k);
<                 put t';
<                 y   <- hNDf failOp;
<                 return (x ++ y)) s
< = {-~  definition of |hNDf|  -}
<    hState1 (do  t'  <- get;
<                 put t;
<                 x   <- hNDf (local2global k);
<                 put t';
<                 return x) s
< = {-~  Law (\ref{eq:get-put}): get-put  -}
<    hState1 (do  put t;
<                 x   <- hNDf (local2global k);
<                 return x) s
< = {-~  reformulation  -}
<    hState1 (do  put t;
<                 hNDf (local2global k)) s
< = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
<    do  hState1 (put t) s;
<        hState1 (hNDf (local2global k)) s
< = {-~  induction hypothesis  -}
<    do  hState1 (put t) s;
<        (x, _) <- hState1 (hNDf (local2global k)) s;
<        return (x, s)
< = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
<    do  (x, _) -> hState1 (put t >> hNDf (local2global k)) s
<        return (x, s)
< = {-~  definition of |hNDf|  -}
<    do  (x, _) -> hState1 (hNDf (putOp t (local2global k))) s
<        return (x, s)
< = {-~  definition of |local2global|  -}
<    do  (x, _) -> hState1 (hNDf (local2global (putOp t k))) s
<        return (x, s)

\noindent \mbox{\underline{case |t = orOp p q|}}
<    hState1 (hNDf (local2global (orOp p q))) s
< = {-~  definition of |local2global|; let |p' = local2global p, q' = local2global q|  -}
<    hState1 (hNDf (orOp p' q')) s
< = {-~  definition of |hNDf|  -}
<    hState1 (liftM2 (++) (hNDf p') (hNDf q')) s
< = {-~  definition of |liftM2|  -}
<    hState1 (do x <- hNDf p'; y <- hNDf q'; return (x ++ y)) s
< = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
<    do (x, s1) <- hState1 (hNDf p') s; (y, s2) <- hState1 (hNDf q') s1; return (x++y, s2)
< = {-~  induction hypothesis  -}
<    do (x, _) <- hState1 (hNDf p') s; (y, _) <- hState1 (hNDf q') s; return (x++y, s)
< = {-~  definition of |local2global, hNDf, hState1|  -}
<    do (x, _) <- hState1 (hNDf (local2global (orOp p q))) s; return (x, s)

\noindent \mbox{\underline{case |t = Op (Inr (Inr y))|}}
<    hState1 (hNDf . local2global $ Op (Inr (Inr y))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf $ Op (Inr (Inr (fmap local2global y)))) s
< = {-~  definition of |hNDf|  -}
<    hState1 (Op (Inr (fmap hNDf (fmap local2global y)))) s
< = {-~  definition of |hState1|  -}
<    (\ s -> Op (fmap ($s) (fmap (hState1 (fmap hNDf (fmap local2global y)))))) s
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    (\ s -> Op (fmap (($s) . hState1 . hNDf . local2global) y)) s
< = {-~  function application  -}
<    Op (fmap (($s) . hState1 . hNDf . local2global) y)
< = {-~  induction hypothesis  -}
<    Op (fmap ((>>= \ (x, _) -> return (x, s)) . ($s) . hState1 . hNDf . local2global) y)
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    Op (fmap (>>= \ (x, _) -> return (x, s)) $ (fmap (($s) . hState1 . hNDf . local2global) y))
< = {-~  definition of |(>>=)|  -}
<    Op (fmap (($s) . hState1 . hNDf . local2global) y) >>= \ (x, _) -> return (x, s)
< = {-~  reformulation  -}
<    do (x, _) <- Op (fmap (($s) . hState1 . hNDf . local2global) y); return (x, s)
< = {-~  definition of |local2global, hNDf, hState1|  -}
<    do (x, _) <- hState1 (hNDf . local2global $ Op (Inr (Inr y))) s; return (x, s)

\end{proof}
