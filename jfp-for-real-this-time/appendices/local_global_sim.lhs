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

\section{Proofs for Simulating Local State with Global State}
\label{app:local-global}

%-------------------------------------------------------------------------------

This section shows that the function |hGlobal . local2global| is equivalent to |hLocal|,
where |hGlobal|, |local2global| and |hLocal| are defined in Section \ref{sec:local-global}.

\paragraph*{Preliminary}
It is easy to see that |runStateT . hState| can be fused into a single fold defined as follows:
\begin{code}
hState1 :: Functor f => Free (StateF s :+: f) a -> (s -> Free f (a, s))
hState1  =  fold genS (algS # fwdS)
  where
    genS x          s  = Var (x, s)
    algS (Get k)    s  = k s s
    algS (Put s k)  _  = k s
    fwdS y          s  = Op (fmap ($s) y)
\end{code}
For brevity, we use |hState1| to replace |runStateT . hState| in the following proofs.

%format genLHS = "\Varid{gen}_{\Varid{LHS}}"
%format genRHS = "\Varid{gen}_{\Varid{RHS}}"
%format algSLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{S}}"
%format algSRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{S}}"
%format algNDLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{ND}}"
%format algNDRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{ND}}"
%format fwdLHS = "\Varid{fwd}_{\Varid{LHS}}"
%format fwdRHS = "\Varid{fwd}_{\Varid{RHS}}"
\subsection{Main Proof Structure}
The main theorem we prove in this section is:
\begin{theorem}\label{eq:local-global}
|hGlobal . local2global = hLocal|
\end{theorem}
\begin{proof}
Both the left-hand side and the right-hand side of the equation consist of 
function compositions involving one or more folds.
We apply fold fusion separately on both sides to contract each
into a single fold:
\begin{eqnarray*}
|hGlobal . local2global| & = & |fold genLHS (algSLHS # algNDRHS # fwdLHS)| \\
|hLocal|& = & |fold genRHS (algSRHS # algNDRHS # fwdRHS)|
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
    hLocal
 = {-~  definition -}
    hL . hState1
      {-" \text{with } "-} 
         hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
         hL = fmap (fmap (fmap fst) . hNDf)
 = {-~  definition of |hState1|  -}
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

The second fusion condition decomposes into two separate conditions:
\begin{eqnarray*}
|hL . algS| & = & |algSRHS . fmap hL| \\
|hL . fwdS| & = & |(algNDRHS # fwdRHS) . fmap hL|
\end{eqnarray*}

The first subcondition is met by taking:

> algSRHS :: Functor f => StateF s (s -> Free f [a]) -> (s -> Free f [a])
> algSRHS (Get k)    = \ s -> k s s
> algSRHS (Put s k)  = \ _ -> k s

Given this defintion we establish that the subcondition holds, when we apply both
sides of the equation to any |t :: StateF s (s -> Free (NondetF :+: f) (a,s))|.

\noindent \mbox{\underline{case |t = Get k|}}
<   hL (algS (Get k))
< = {-~  definition of |algS| -}
<   hL (\s -> k s s)
< = {-~  definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\s -> k s s)
< = {-~  definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (k s s))
< = {-~  beta-expansion (twice) -}
< = \s -> (\s1 s2 -> fmap (fmap fst) (hNDf (k s2 s1))) s s
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
\noindent \mbox{\underline{case |t = Put s k|}}
<   hL (algS (Put s k))
< = {-~  definition of |algS| -}
<   hL (\ _ -> k s)
< = {-~  definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf) (\ _ -> k s)
< = {-~  definition of |fmap| -}
<   \ _ -> fmap (fmap fst) (hNDf (k s))
< = {-~  beta-expansion -}
< = \ _ -> (\ s1 -> fmap (fmap fst) (hNDf (k s1))) s
< = {-~  definition of |fmap| -}
< = \ _ -> (fmap (fmap (fmap fst) . hNDf) (\ s1 -> k s1)) s
< = {-~  eta-expansion of |k| -}
< = \ _ -> (fmap (fmap (fmap fst) . hNDf) k) s
< = {-~  definition of |algSRHS| -}
< = algSRHS (Put s (fmap (fmap (fmap fst) . hNDf) k))
< = {-~  definition of |fmap| -}
< = algSRHS (fmap (fmap (fmap fst) . hNDf)) (Put s k))
< = {-~  definition of |hL| -}
< = algSRHS (fmap hL (Put s k))

The second subcondition can be split up in two further subconditions:
\begin{eqnarray*}
|hL . fwdS . Inl|& = & |algNDRHS . fmap hL| \\
|hL . fwdS . Inr|& = & |fwdRHS . fmap hL|
\end{eqnarray*}

For the first of these, we calculate:

<   hL (fwdS (Inl op))
< = {-~ definition of |fwdS| -}
<   hL (\s -> Op (fmap ($ s) (Inl op)))
< = {-~ definition of |fmap| -}
<   hL (\s -> Op (Inl (fmap ($ s) op)))
< = {-~ definition of |hL| -}
<   fmap (fmap (fmap fst) . hNDf)(\s -> Op (Inl (fmap ($ s) op)))
< = {-~ definition of |fmap| -}
<   \s -> fmap (fmap fst) (hNDf (Op (Inl (fmap ($ s) op))))
< = {-~ definition of |hNDf| -}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) op)))

We split on |op|:

\noindent \mbox{\underline{case |op = Fail|}}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) Fail)))
< = {-~ defintion of |fmap| (twice) -}
<   \s -> fmap (fmap fst) (algNDf Fail)
< = {-~ definition of |algNDf| -}
<   \s -> fmap (fmap fst) (Var [])
< = {-~ definition of |fmap| (twice) -}
<   \s -> Var []
< = {-~ define |algNDRHS Fail = \s -> Var []| -}
<   algNDRHS Fail
< = {- definition fo |fmap| -}
<   algNDRHS (fmap hL fail)
\noindent \mbox{\underline{case |op = Or p q|}}
<   \s -> fmap (fmap fst) (algNDf (fmap hNDf (fmap ($ s) (Or p q))))
< = {-~ defintion of |fmap| (twice) -}
<   \s -> fmap (fmap fst) (algNDf (Or (hNDf (p s)) (hNDf (q s))))
< = {-~ definition of |algNDf| -}
<   \s -> fmap (fmap fst) (liftM2 (++) (hNDf (p s)) (hNDf (q s)))
< = {-~ Lemma~\ref{eq:liftM2-fst-comm} -}
<   \s -> liftM2 (++) (fmap (fmap fst) (hNDf (p s))) (fmap (fmap fst) (hNDf (q s)))
< = {-~ define |algNDRHS (Or p q) = \s -> liftM2 (++) (p s) (q s)| -}
<   algNDRHS (Or (fmap (fmap fst) . hNDf . p) (fmap (fmap fst) . hNDf . q))
< = {-~ defintion of |fmap| (twice) -}
<   algNDRHS (fmap (fmap (fmap (fmap fst) . hNDf)) (Or p q))
< = {-~ defintion of |hL| -}
<   algNDRHS (fmap hL (Or p q))

From this we conclude that the definition of |algNDRHS| should be:

< algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
< algNDRHS Fail      = \ s -> Var []
< algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)

For the last subcondition, we calculate:

<   hL (fwdS (Inr op))
< = {-~ definition of |fwdS| -}
<   hL (\s -> Op (fmap ($ s) (Inr op)))
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
< = {-~ definition of |hL| -}|
<   \s -> Op (hL (fmap ($ s) op))
< = {-~ \Cref{eq:comm-app-fmap} -}
<   \s -> Op (fmap ($ s) (fmap hL op))
< = {-~ define |fwdRHS op = \s -> Op (fmap ($s) op)| -}
<   fwdRHS (fmap hL op)

From this we conclude that the definition of |fwdRHS| should be:

< fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
< fwdRHS op = \s -> Op (fmap ($s) op)

\subsection{Fusing the Left-Hand Side}

We proceed in the same fashion with fusing left-hand side,
discovering the definitions that we need to satisfy the fusion
condition.

We calculate as follows:
\begin{spec}
    hGlobal . local2global
 = {-~  definition of |local2global| -}
    hGlobal . fold Var alg
      where
        alg (Inl (Put t k)) = putR t >> k
        alg p               = Op p
 = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
    fold genLHS (algSLHS # algNDLHS # fwdLHS) 
\end{spec}

This last step is valid provided that the fusion conditions are satisfied:
\begin{eqnarray*}
|hGlobal . Var| & = & |genLHS| \\
|hGlobal . alg| & = & |(algSLHS # algNDLHS # fwdLHS) . fmap hGlobal|
\end{eqnarray*}

We calculate for the first fusion condition:
<   hGlobal (Var x)
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2 (Var x))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (Var x)))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (Var [x]))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst) (\s -> Var ([x], s))
< = {-~ definition of |fmap| (twice) -}
<   \s -> Var [x]
< = {-~ define |genLHS x = \s -> Var [x]| -}
<   genLHS x

We conclude that the first fusion condition is satisfied by:

< genLHS :: Functor f => a -> (s -> Free f [a])
< genLHS x = \s -> Var [x]

We can split the second fusion condition in three subconditions:
\begin{eqnarray*}
|hGlobal . alg . Inl| & = & |algSLHS . fmap hGlobal| \\
|hGlobal . alg . Inr . Inl| & = & |algNDLHS . fmap hGlobal| \\
|hGlobal . alg . Inr . Inr| & = & |fwdLHS . fmap hGlobal|
\end{eqnarray*}

Let's consider the first subconditions. It has two cases:

\noindent \mbox{\underline{case |op = Get k|}}
<   hGlobal (alg (Inl (Get k)))
< = {-~ definition of |alg| -}
<   hGlobal (Op (Inl (Get k))) 
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2 (Op (Inl (Get k))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inr (Inl (fmap comm2 (Get k)))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inr (Inl (Get (comm2 . k)))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (Op (fmap hNDf (Inl (Get (comm2 . k))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hState1 (Op (Inl (Get (hNDf . comm2 . k)))))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst) (\s -> (hState1 . hNDf . comm2 . k) s s)
< = {-~ definition of |fmap| -}
<   (\s -> fmap fst ((hState1 . hNDf . comm2 . k) s s))
< = {-~ definition of |fmap| -}
<   (\s -> ((fmap (fmap fst) . hState1 . hNDf . comm2 . k) s s))
< = {-~ define |algSLHS (Get k) = \s -> k s s| -}
<   algSLHS (Get (hGLobal . k))
< = {-~ definition of |fmap| -}
<   algSLHS (fmap hGlobal (Get k))

\noindent \mbox{\underline{case |op = Put s k|}}

<   hGlobal (alg (Inl (Put s k)))
< = {-~ definition of |alg| -}
<   hGlobal (putR s >> k)
< = {-~ definition of |putR| -}
<   hGlobal ((get >>= \t -> put s `mplus` side (put t)) >> k)
< = {-~ definitions of |side|, |get|, |put|, |mplus|, |(>>=)| -}
<   hGlobal (Op (Inl (Get (\t -> Op (Inr (Inl (Or  (Op (Inl (Put s k))) 
<                                                  (Op (Inl (Put t (Op (Inr (Inl Fail)))))))))))))
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2
<     (Op (Inl (Get (\t -> Op (Inr (Inl (Or  (Op (Inl (Put s k))) 
<                                            (Op (Inl (Put t (Op Inr ((Inl Fail))))))))))))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (
<     (Op (Inr (Inl (Get (\t -> Op (Inl (Or  (Op (Inr (Inl (Put s (comm2 k))))) 
<                                            (Op (Inr (Inl (Put t (Op (Inl Fail))))))))))))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (
<     (Op (Inl (Get (\t -> liftM2 (++)  (Op (Inl (Put s (hNDf (comm2 k))))) 
<                                       (Op (Inl (Put t (Var []))))))))))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst)
<     (\t -> hState1 (liftM2 (++)  (Op (Inl (Put s (hNDf (comm2 k))))) 
<                                  (Op (Inl (Put t (Var []))))) t)
< = {-~ definition of |liftM2| -}
<   fmap (fmap fst)
<     (\t -> hState1 (do x <- Op (Inl (Put s (hNDf (comm2 k)))) 
<                        y <- Op (Inl (Put t (Var [])))
<                        Var (x ++ y)
<                    ) t)
< = {-~ TODO -}
<   fmap (fmap fst)
<     (\t -> do (x,t1) <- hState1 (Op (Inl (Put s (hNDf (comm2 k))))) t 
<               (y,t2) <- hState1 (Op (Inl (Put t (Var [])))) t1
<               hState1 (Var (x ++ y)) t2
<     )
< = {-~ definition of |hState1| -}
<   fmap (fmap fst)
<     (\t -> do (x,_) <- hState1 (hNDf (comm2 k)) s 
<               (y,t2) <- Var ([],t)
<               Var (x ++ y, t2)
<     )
< = {-~ monad law -}
<   fmap (fmap fst)
<     (\t -> do (x,_) <- hState1 (hNDf (comm2 k)) s 
<               Var (x ++ [], t)
<     )
< = {-~ right unit of |(++)| -}
<   fmap (fmap fst)
<     (\t -> do (x,_) <- hState1 (hNDf (comm2 k)) s 
<               Var (x, t)
<     )
< = {-~ definition of |fmap fst| -}
<   fmap (fmap fst)
<     (\t -> do x <- fmap fst (hState1 (hNDf (comm2 k)) s)
<               Var (x, t)
<     )
< = {-~ definition of |fmap| -}
<   fmap (fmap fst)
<     (\t -> do x <- (fmap (fmap fst) (hState1 (hNDf (comm2 k)))) s
<               Var (x, t)
<     )
< = {-~ definition of |fmap (fmap fst)| -}
<   \_ -> do x <- (fmap (fmap fst) (hState1 (hNDf (comm2 k)))) s
<            Var x
< = {-~ monad law -}
<   \_ -> (fmap (fmap fst) (hState1 (hNDf (comm2 k)))) s
< = {-~ definition of |hGlobal| -}
<   \_ -> (hGlobal k) s
< = {-~ define |algSLHS (Put s k) = \_ -> k s| -}
<   algSLHS (Put s (hGlobal k)) 
< = {-~ definition of |fmap| -}
<   algSLHS (fmap hGlobal (Put s)) 

We conclude that this fusion subcondition holds provided that:

< algSLHS :: Functor f => StateF s (s -> Free f [a]) -> (s -> Free f [a])
< algSLHS (Get k)    =  \s -> k s s
< algSLHS (Put s k)  =  \_ -> k s 

Let's consider the second subcondition. It has also two cases:

\noindent \mbox{\underline{case |op = Fail|}}
<   hGlobal (alg (Inr (Inl Fail)))
< = {-~ definition of |alg| -}
<   hGlobal (Op (Inr (Inl Fail)))
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2 (Op (Inr (Inl Fail))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inl (fmap comm2 Fail)))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inl Fail))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (Var []))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst) (\s -> Var ([], s))
< = {-~ definition of |fmap| twice and |fst| -}
<   \s -> Var []
< = {-~ define |algNDRHS Fail = \s -> Var []| -}
<  algNDRHS Fail 
< = {-~ definition of |fmap| -}
<  algNDRHS (fmap hGlobal Fail)
\noindent \mbox{\underline{case |op = Or p q|}}
<   hGlobal (alg (Inr (Inl (Or p q))))
< = {-~ definition of |alg| -}
<   hGlobal (Op (Inr (Inl (Or p q))))
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2 (Op (Inr (Inl (Or p q)))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inl (fmap comm2 (Or p q))))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inl (Or (comm2 p) (comm2 q))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (liftM2 (++) (hNDf (comm2 p)) (hNDf (comm2 q))))
< = {-~ definition of |liftM2| -}
<   fmap (fmap fst) (hState1 (do  x <- hNDf (comm2 p)
<                                 y <- hNDf (comm2 q)
<                                 return (x ++ y)))
< = {-~ |hState1| lemma -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- hState1 (hNDf (comm2 p)) s0
<                               (y, s2) <- hState1 (hNDf (comm2 q)) s1
<                               hState1 (return (x ++ y)) s2))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- hState1 (hNDf (comm2 p)) s0
<                               (y, s2) <- hState1 (hNDf (comm2 q)) s1
<                               Var (x ++ y, s2)))
< = {-~ Lemma \ref{lemma:dist-hState1} -}
<   fmap (fmap fst) (\s0-> (do  (x, s1) <- do {(x,_) <- hState1 (hNDf (comm2 p)) s0; return (x, s0)}
<                               (y, s2) <- do {(y,_) <- hState1 (hNDf (comm2 q)) s1; return (x, s1)}
<                               Var (x ++ y, s2)))
< = {-~ monad laws -}
<   fmap (fmap fst) (\s0-> (do  (x,_) <- hState1 (hNDf (comm2 p)) s0
<                               (y,_) <- hState1 (hNDf (comm2 q)) s0
<                               Var (x ++ y, s0)))
< = {-~ definition of |fmap| (twice) and |fst| -}
<   \s0-> (do  (x,_) <- hState1 (hNDf (comm2 p)) s0
<              (y,_) <- hState1 (hNDf (comm2 q)) s0
<              Var (x ++ y))
< = {-~ definition of |fmap|, |fst| and monad laws -}
<   \s0-> (do  x <- fmap fst (hState1 (hNDf (comm2 p)) s0)
<              y <- fmap fst (hState1 (hNDf (comm2 q)) s0)
<              Var (x ++ y))
< = {-~ definition of |fmap| -}
<   \s0-> (do  x <- fmap (fmap fst) (hState1 (hNDf (comm2 p))) s0
<              y <- fmap (fmap fst) (hState1 (hNDf (comm2 q))) s0
<              Var (x ++ y))
< = {-~ definition of |hGlobal| -}
<   \s0-> (do  x <- hGlobal p s0
<              y <- hGlobal q s0
<              Var (x ++ y))
< = {-~ definition of |liftM2| -}
<   \s0-> liftM2 (++) (hGlobal p s0) (hGlobal q s0)
< = {-~ define |algNDLHS (Or p q) = \s -> liftM2 (++) (p s) (q s)| -}
<   algNDLHS (Or (hGlobal p) (hGlobal q))
> = {-~ definition of |fmap| -}
<   algNDLHS (fmap hGobal (Or p q))

We conclude that this fusion subcondition holds provided that:

< algNDLHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
< algNDLHS Fail      = \s -> Var []
< algNDLHS (Or p q)  = \s -> liftM2 (++) (p s) (q s)

Finally, the last subcondition:
<   hGlobal (alg (Inr (Inr op)))
< = {-~ definition of |alg| -}
<   hGlobal (Op (Inr (Inr op)))
< = {-~ definition of |hGlobal| -}
<   fmap (fmap fst) (hState1 (hNDf (comm2 (Op (Inr (Inr op))))))
< = {-~ definition of |comm2| -}
<   fmap (fmap fst) (hState1 (hNDf (Op (Inr (Inr (fmap comm2 op))))))
< = {-~ definition of |hNDf| -}
<   fmap (fmap fst) (hState1 (Op (fmap hNDf (Inr (fmap comm2 op)))))
< = {-~ definition of |fmap| -}
<   fmap (fmap fst) (hState1 (Op (Inr (fmap hNDf (fmap comm2 op)))))
< = {-~ |fmap| fusion -}
<   fmap (fmap fst) (hState1 (Op (Inr (fmap (hNDf . comm2) op))))
< = {-~ definition of |hState1| -}
<   fmap (fmap fst) (\s -> Op (fmap ($ s) (fmap hState1 (fmap (hNDf . comm2) op))))
< = {-~ |fmap| fusion -}
<   fmap (fmap fst) (\s -> Op (fmap ($ s) (fmap (hState1 . hNDf . comm2) op)))
< = {-~ definition of |fmap| -}
<   \s -> fmap fst (Op (fmap ($ s) (fmap (hState1 . hNDf . comm2) op)))
< = {-~ definition of |fmap| -}
<   \s -> Op (fmap (fmap fst) (fmap ($ s) (fmap (hState1 . hNDf . comm2) op)))
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap (fmap fst . ($ s)) (fmap (hState1 . hNDf . comm2) op)))
< = {-~ naturality of |($ s)| -}
<   \s -> Op (fmap (($ s) . fmap (fmap fst)) (fmap (hState1 . hNDf . comm2) op)))
< = {-~ |fmap| fission -}
<   \s -> Op ((fmap ($ s) . fmap (fmap (fmap fst))) (fmap (hState1 . hNDf . comm2) op))
< = {-~ |fmap| fusion -}
<   \s -> Op (fmap ($ s) (fmap (fmap (fmap fst) . hState1 . hNDf . comm2) op))
< = {-~ definition of |hGlobal| -}
<   \s -> Op (fmap ($ s) (fmap hGlobal op))
< = {-~ define |fwdLHS op = \s -> Op (fmap ($ s) op| -}
<   fwdLHS (fmap hGlobal op)

We conclude that this fusion subcondition holds provided that:

< fwdLHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
< fwdLHS op = \s -> Op (fmap ($ s) op)

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

\begin{lemma} \label{eq:comm-app-fmap}
< ($x) . fmap f = f . ($x)
\end{lemma}
\begin{proof}~
<   (($x) . fmap f) m
< = {-~ function application -}
<   (fmap f m) x
< = {-~ eta-expansion -}
<   (fmap f (\ y . m y)) x
< = {-~ definition of |fmap| -}
<   (\ y . f (m y)) x
< = {-~ function application -}
<   f (m x)
< = {-~ definition of |.| and |$| -}
<   (f . ($x)) m
\end{proof}

\begin{lemma} \label{eq:liftM2-fst-comm}~
< fmap (fmap fst) (liftM2 (++) p q) = liftM2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{lemma}
\begin{proof}~

<    fmap (fmap fst) (liftM2 (++) p q)
< = {-~  definition of |liftM2| -}
<    fmap (fmap fst) (do {x <- p; y <- q; return (x ++ y)})
< = {-~  derived property for monad: |fmap f (m >>= k) = m >>= fmap f . k| -}
<    do {x <- p; y <- q; fmap (fmap fst) (return (x ++ y))}
< = {-~  definition of |fmap| -}
<    do {x <- p; y <- q; return (fmap fst (x ++ y))}
< = {-~  naturality of |(++)| -}
<    do {x <- p; y <- q; return ((fmap fst x) ++ (fmap fst y))}
< = {-~  monad left unit law (twice) -}
<    do {x <- p; x' <- return (fmap fst x); y <- q; y' <- return (fmap fst y) return (x' ++ y')}
< = {-~  definition of |fmap| -}
<    do {x <- fmap (fmap fst) p; y <- fmap (fmap fst) q; return (x ++ y)}
< = {-~  definition of |liftM2| -}
<    liftM2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{proof}

\begin{lemma}[Distributivity of |hState1|] \label{lemma:dist-hState1} \ \\
< hState1 (p >>= k) s = hState1 p s >>= \(x,s') -> hState1 (k x) s'
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
<    Op (Inr y) s >>= \(x',s') -> hState1 (k x) s'

\end{proof}

\begin{lemma}[State is Restored] \label{lemma:state-restore} \ \\
< hState1 (hNDf (local2global t)) s = do (x, _) <- hState1 (hNDf (local2global t)) s; return (x, s)
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

% \subsection{Old Stuff}
% 
% For the left hand side, we can also expand the definition of |local2global| and use the fold fusion law (Law (\ref{eq:functor-composition})):
% <    hGlobal . local2global
% < = {-~  definition of |local2global|  -}
% <    hGlobal . fold Var alg
% < = {-~  fold fusion-post' (Equation \ref{eq:fusion-post-strong})  -}
% <    fold (hGlobal . Var) alg'
% <      {-" \text{with } "-} hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global
% 
% \birthe{I believe that we don't need the strong fusion post law}
% 
% The algebras |alg'| and |algS'| are constructed later.
% % Note that we only need the equation |hGlobal . alg = alg' . fmap hGlobal| to hold for inputs |t :: (StateF s :+: (NondetF :+: f)) (Free (StateF s :+: NondetF :+: f) a)| in the range of |fmap local2global|.
% Then, we can use the universal property of fold to show that |hLocal = fold (hL . genS) algS'| and |hGlobal . local2global = fold (hGlobal . Var) alg'| are equal.
% To do this, we have to prove that
% \begin{enumerate}
%     \item |hL . genS  = hGlobal . Var|
%     \item |algS'      = alg'|
%     \item |fwdS'      = fwd'|
% \end{enumerate}
% The first item is simple to prove with equational reasoning.
% We want to prove that |hL . genS = hGlobal . Var| for all inputs |x :: a|.
% 
% <    (hL . genS) x
% < = {-~  definition of |hState1|  -}
% <    hL (\ s -> Var (x, s))
% < = {-~  definition of |hL|  -}
% <    fmap (fmap (fmap fst) . hNDf) (\ s -> Var (x, s))
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
% <    (fmap (fmap (fmap fst)) . fmap hNDf) (\ s -> Var (x, s))
% < = {-~  application of |fmap hNDf|  -}
% <    fmap (fmap (fmap fst)) (\ s -> hNDf (Var (x, s)))
% < = {-~  definition of |hNDf|  -}
% <    fmap (fmap (fmap fst)) (\ s -> (Var $ etal (x, s)))
% < = {-~  definition of |etal|  -}
% <    fmap (fmap (fmap fst)) (\ s -> Var [(x, s)])
% < = {-~  evaluation of |fmap (fmap (fmap fst))|  -}
% <    \ s -> Var [x]
% < = {-~  property of |fmap| and |fst|  -}
% <    fmap (fmap fst) (\ s -> Var ([x], s))
% < = {-~  definition of |hState1|  -}
% <    (fmap (fmap fst) . hState1) (Var [x])
% < = {-~  definition of |etal|  -}
% <    (fmap (fmap fst) . hState1) (Var $ etal x)
% < = {-~  definition of |hNDf|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (Var x)
% < = {-~  definition of |hGlobal|  -}
% <    hGlobal (Var x)
% < = {-~  reformulation  -}
% <    (hGlobal . Var) x
% 
% So we have |hL . genS = hGlobal . Var|.
% 
% For the second item, instead of constructing |alg'| and |algS'| individually, we only construct |alg'| and then verify that the following two equations hold:
% 
% \begin{enumerate}
%     \item |hL . algS = alg' . fmap hL|
%     \item |hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global|
% \end{enumerate}
% 
% The |alg'| is defined as follows:
% \begin{code}
% alg' :: Functor f => (StateF s :+: (NondetF :+: f)) (s -> Free f [a]) -> s -> Free f [a]
% alg' = alg1 # alg2 # fwd1
%   where alg1 (Get k)    = \ s -> k s s
%         alg1 (Put s k)  = \ _ -> k s
%         alg2 Fail       = \ s -> Var []
%         alg2 (Or p q)   = \ s -> liftM2 (++) (p s) (q s)
%         fwd1 y          = \ s -> Op (fmap ($s) y)
% \end{code}
% These two equations (1) and (2) are proved in Lemma \ref{eq:fusion-cond-1} and Lemma \ref{eq:fusion-cond-2} respectively.
% This implies that our original equation |hLocal = fold (hL . genS) alg' = fold (hGlobal . Var) alg' = hGlobal . local2global| holds.
% 
% \begin{lemma}[Fusion Condition 1] \label{eq:fusion-cond-1}
% |alg' . fmap hL = hL . algS|
% \end{lemma}
% \begin{proof}
% We need to prove it holds for all inputs |t :: (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))|.
% We do a case analysis on |t|.
% 
% \noindent \mbox{\underline{case |t = Inl (Get k)|}}
% % k :: s -> s -> Free (NondetF :+: f) (a, s)
% 
% <    (alg' . fmap hL) (Inl (Get k))
% < = {-~  definition of |fmap|  -}
% <    alg' (Inl (Get (hL . k)))
% < = {-~  definition of |alg'|  -}
% <    \ s -> hL (k s) s
% < = {-~  |eta|-expansion  -}
% <    \ s -> hL (\ s' -> k s s') s
% < = {-~  definition of |hL|  -}
% <    \ s -> (fmap hL') (\ s' -> k s s') s
% < = {-~  definition of |fmap|  -}
% <    \ s -> (\ s' -> hL' (k s s')) s
% < = {-~  function application  -}
% <    \ s -> hL' (k s s)
% < = {-~  definition of |fmap|  -}
% <    (fmap hL') (\ s -> k s s)
% < = {-~  definition of |hL|  -}
% <    hL (\ s -> k s s)
% < = {-~  definition of |hState1|  -}
% <    (hL . algS) (Inl (Get k))
% 
% \noindent \mbox{\underline{case |t = Inl (Put s k)|}}
% % s :: s, k :: s -> Free (NondetF :+: f) (a, s)
% 
% <    (alg' . fmap hL) (Inl (Put s k))
% < = {-~  definition of |fmap|  -}
% <    alg' (Inl (Put s (hL k)))
% < = {-~  definition of |alg'|  -}
% <    \ _ -> hL k s
% < = {-~  |eta|-expansion  -}
% <    \ _ -> hL (\ s' -> k s') s
% < = {-~  definition of |hL|  -}
% <    \ _ -> (fmap hL') (\ s' -> k s') s
% < = {-~  definition of |fmap|  -}
% <    \ _ -> (\ s' -> hL' (k s')) s
% < = {-~  function application  -}
% <    \ _ -> hL' (k s)
% < = {-~  definition of |fmap|  -}
% <    (fmap hL') (\ _ -> k s)
% < = {-~  definition of |hL|  -}
% <    hL (\ _ -> k s)
% < = {-~  definition of |hState1|  -}
% <    (hL . algS) (Inl (Put s k))
% 
% \noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}
% 
% <    (alg' . fmap hL) (Inr (Inl Fail))
% < = {-~  definition of |fmap|  -}
% <    alg' (Inr (Inl Fail))
% < = {-~  definition of |alg'|  -}
% <    \ s -> Var []
% < = {-~  definition of |fmap|  -}
% <    \ s -> fmap (fmap fst) (Var [])
% < = {-~  definition of |hNDf|  -}
% <    \ s -> (fmap (fmap fst) . hNDf) (Op (Inl Fail))
% < = {-~  definition of |hL'|  -}
% <    \ s -> hL' (Op (Inl Fail))
% < = {-~  definition of |fmap|  -}
% <    (fmap hL') (\ s -> Op (Inl Fail))
% < = {-~  definition of |hL|  -}
% <    hL (\ s -> Op (Inl Fail))
% < = {-~  definition of |fmap|  -}
% <    hL (\ s -> Op (fmap (\ k -> k s) (Inl Fail)))
% < = {-~  definition of |hState1|  -}
% <    (hL . algS) (Inr (Inl Fail))
% 
% \noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}
% % p, q :: s -> Free (NondetF :+: f) (a, s)
% 
% <    (alg' . fmap hL) (Inr (Inl (Or p q)))
% < = {-~  evaluation of |fmap hL|  -}
% <    alg' (Inr (Inl (Or (hL p) (hL q))))
% < = {-~  definition of |alg'|  -}
% <    \ s -> liftM2 (++) (hL p s) (hL q s)
% < = {-~  |eta|-expansion (twice)  -}
% <    \ s -> liftM2 (++) (hL (\ s' -> p s') s) (hL (\ s' -> q s') s)
% < = {-~  definition of |hL|  -}
% <    \ s -> liftM2 (++) ((fmap hL') (\ s' -> p s') s) ((fmap hL') (\ s' -> q s') s)
% < = {-~  definition of |fmap|  -}
% <    \ s -> liftM2 (++) ((\ s' -> hL' (p s')) s) ((\ s' -> hL' (q s')) s)
% < = {-~  function application  -}
% <    \ s -> liftM2 (++) (hL' (p s)) (hL' (q s))
% < = {-~  definition of |hL'|  -}
% <    \ s -> liftM2 (++) (fmap (fmap fst) (hNDf (p s))) (fmap (fmap fst) (hNDf (q s)))
% < = {-~  Lemma \ref{eq:liftM2-fst-comm}  -}
% <    \ s -> fmap (fmap fst) (liftM2 (++) (hNDf (p s)) (hNDf (q s)))
% < = {-~  definition of |hNDf|  -}
% <    \ s -> (fmap (fmap fst) . hNDf) (Op (Inl (Or (p s) (q s))))
% < = {-~  definition of |hL'|  -}
% <    \ s -> hL' (Op (Inl (Or (p s) (q s))))
% < = {-~  definition of |fmap|  -}
% <    (fmap hL') (\ s -> Op (Inl (Or (p s) (q s))))
% < = {-~  definition of |hL|  -}
% <    hL (\ s -> Op (Inl (Or (p s) (q s))))
% < = {-~  definition of |fmap|  -}
% <    hL (\ s -> Op (fmap (\ k -> k s) (Inl (Or p q))))
% < = {-~  definition of |hState1|  -}
% <    (hL . algS) (Inr (Inl (Or p q)))
% 
% \noindent \mbox{\underline{case |t = Inr (Inr y)|}}
% % y :: f (s -> Free (NondetF :+: f) (a, s))
% 
% <    (alg' . fmap hL) (Inr (Inr y))
% < = {-~  evaluation of |fmap hL|  -}
% <    alg' (Inr (Inr (fmap hL y)))
% < = {-~  definition of |alg'|  -}
% <    \ s -> Op (fmap (\ k -> k s) (fmap hL y))
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
% <    \ s -> Op (fmap ((\ k -> k s) . hL) y)
% < = {-~  definition of |hL|  -}
% <    \ s -> Op (fmap ((\ k -> k s) . (fmap hL')) y)
% < = {-~  |eta|-expansion and definition of |fmap| for |((->) r)| -}
% <    \ s -> Op (fmap (\t -> (\ k -> k s) . (hL' . t)) y)
% < = {-~  function application -}
% <    \ s -> Op (fmap (\t -> (hL' (t s))) y)
% < = {-~  reformulation -}
% <    \ s -> Op (fmap (hL' . ($s)) y)
% < = {-~  definition of |hL'|  -}
% <    \ s -> Op (fmap (fmap (fmap fst) . hNDf . ($s)) y)
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|   -}
% <    \ s -> Op (fmap (fmap (fmap fst) (fmap hNDf (fmap ($s) y))))
% < = {-~  definition of |fmap| for free monad  -}
% <    \ s -> fmap (fmap fst) (Op (fmap hNDf (fmap ($s) y)))
% < = {-~  definition of |hNDf|  -}
% <    \ s -> fmap (fmap fst) (hNDf (Op (Inr (fmap ($s) y))))
% < = {-~  definition of |fmap|  -}
% <    \ s -> fmap (fmap fst) (hNDf (Op (fmap ($s) (Inr y))))
% < = {-~  definition of |hL'|  -}
% <    \ s -> hL' (Op (fmap ($s) (Inr y)))
% < = {-~  definition of |fmap|  -}
% <    (fmap hL') (\ s -> Op (fmap ($s) (Inr y)))
% < = {-~  definition of |hL|  -}
% <    hL (\ s -> Op (fmap ($s) (Inr y)))
% < = {-~  definition of |hState1|  -}
% <    (hL . algS) (Inr (Inr y))
% \end{proof}
% 
% % no longer necessary
% % \begin{lemma}\label{eq:dollar-fmap-comm}~
% % < (\ k -> k s) . fmap f = f . (\ k -> k s)
% % with function |f :: a -> b| and input |t :: s -> a|.
% % % holds for any function |f :: a -> b| and input |t :: s -> a| in the above proof.
% % \end{lemma}
% % \begin{proof} ~
% % <    ((\ k -> k s) . fmap f) t
% % < = {-~  definition of |fmap|  -}
% % <    (\ k -> k s) (f . t)
% % < = {-~  function application  -}
% % <    (f . t) s
% % < = {-~  reformulation  -}
% % <    f (t s)
% % < = {-~  reformulation  -}
% % <    (f . (\ k -> k s)) t
% % \end{proof}
% 
% 
% % no longer necessary
% % \begin{lemma}[Fusion of |hL'|]\label{eq:hl-fusion}~
% %
% % < hL' = fold (fmap (fmap fst) . genND) algL'
% % where |algL'| is defined as follows:
% % <     algL' :: Functor f => (NondetF :+: f) (Free f [a]) -> Free f [a]
% % <     algL' (Inl Fail) = Var []
% % <     algL' (Inl (Or p q)) = liftM2 (++) p q
% % <     algL' (Inr y) = Op y
% % \end{lemma}
% %
% % \begin{proof} ~
% % <    hL'
% % < = {-~  definition of |hL'|  -}
% % <    fmap (fmap fst) . hNDf
% % < = {-~  definition of |hNDf|  -}
% % <    fmap (fmap fst) . fold genND algND
% % < = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
% % <    fold (fmap (fmap fst) genND) algL'
% %
% % So we only need to prove that the equation |fmap (fmap fst) . algND = algL' . fmap (fmap (fmap fst))| holds for all inputs |t :: (NondetF :+: f) (Free f [(a, s)])|.
% % We do this by a case analysis on |t|.
% %
% % \noindent \mbox{\underline{case |t = Inl Fail|}}
% % <    (fmap (fmap fst) . algND) (Inl Fail)
% % < = {-~  definition of |algND|  -}
% % <    fmap (fmap fst) (Var [])
% % < = {-~  definition of |fmap|  -}
% % <    Var []
% % < = {-~  definition of |algL'|  -}
% % <    algL' (Inl Fail)
% % < = {-~  definition of |fmap|  -}
% % <    (algL' . fmap (fmap (fmap fst))) (Inl Fail)
% %
% % \noindent \mbox{\underline{case |t = Inl (Or p q)|}}
% % <    (fmap (fmap fst) . algND) (Inl (Or p q))
% % < = {-~  definition of |algND|  -}
% % <    fmap (fmap fst) (liftM2 (++) p q)
% % < = {-~  Lemma \ref{eq:liftM2-fst-comm}  -}
% % <    liftM2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
% % < = {-~  definition of |algL'|  -}
% % <    algL' (Inl (Or (fmap (fmap fst) p) (fmap (fmap fst) q)))
% % < = {-~  definition of |fmap|  -}
% % <    (algL' . fmap (fmap (fmap fst))) (Inl (Or p q))
% %
% % \noindent \mbox{\underline{case |t = Inr y|}}
% % <    (fmap (fmap fst) . algND) (Inr y)
% % < = {-~  definition of |algND|  -}
% % <    fmap (fmap fst) (Op y)
% % < = {-~  definition of |fmap|  -}
% % <    Op ((fmap (fmap (fmap fst)) y))
% % < = {-~  definition of |algL'|  -}
% % <    algL' (Inr (fmap (fmap (fmap fst)) y))
% % < = {-~  definition of |fmap|  -}
% % <    (algL' . fmap (fmap (fmap fst))) (Inr y)
% %
% % \end{proof}
% 
% \begin{lemma}[Fusion Condition 2] \label{eq:fusion-cond-2}
% |hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global|
% \footnote{Note that the |alg| here refers to the |alg| in the definition of |local2global|.}
% \end{lemma}
% \begin{proof}
% We prove this equation in a similar way to Lemma \ref{eq:fusion-cond-1}.
% We need to prove |hGlobal (alg t) = alg' (fmap hGlobal t)| holds for all inputs |t :: (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: f) a)| that are in the range of |fmap local2global|.
% % All |local2global| formations relevant to commutativity and associativity are implicit and not shown in the following proofs.
% 
% \noindent \mbox{\underline{case |t = Inl (Get k)|}}
% 
% <    (hGlobal . alg) (Inl (Get k))
% < = {-~  definition of |alg|  -}
% <    hGlobal (Op (Inl (Get k)))
% < = {-~  definition of |hGlobal|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (Op (Inl (Get k)))
% < = {-~  definition of |hNDf|  -}
% <    (fmap (fmap fst) . hState1) (Op (Inl (Get (hNDf . k))))
% < = {-~  definition of |hState1|  -}
% % <    fmap (fmap fst) (algS (Inl (Get (hState1 . hNDf . k))))
% % < = {-~  evaluation of |algS|  -}
% <    fmap (fmap fst) (\ s -> (hState1 . hNDf . k) s s)
% < = {-~  function application  -}
% <    fmap (fmap fst) (\ s -> (hState1 . hNDf) (k s) s)
% < = {-~  definition of |fmap|  -}
% <    \ s -> fmap fst ((hState1 . hNDf) (k s) s)
% < = {-~  reformulation  -}
% <    \ s -> (fmap fst . (hState1 . hNDf) (k s)) s
% < = {-~  definition of |fmap|  -}
% <    \ s -> (fmap (fmap fst) ((hState1 . hNDf) (k s))) s
% < = {-~  reformulation  -}
% <    \ s -> (fmap (fmap fst) . hState1 . hNDf) (k s) s
% < = {-~  definition of |hGlobal|  -}
% <    \ s -> hGlobal (k s) s
% < = {-~  definition of |alg'|  -}
% <    alg' (Inl (Get (hGlobal . k)))
% < = {-~  definition of |fmap|  -}
% <    (alg' . fmap hGlobal) (Inl (Get k))
% 
% \noindent \mbox{\underline{case |t = Inl (Put s k)|}}
% 
% For simplicity, we assume that smart constructors |getOp, putOp, orOp, failOp|
% automatically insert correct |Op, Inl, Inr| constructors based on the context
% in order to make the term well-typed in the following proof.
% In this way, we avoid the tedious details of dealing with these constructors manually.
% 
% <    (hGlobal . alg) (Inl (Put s k))
% < = {-~  definition of |alg|  -}
% % NOTE: putR here
% % <    hGlobal (putROp s k)
% % < = {-~  definition of |putROp|  -}
% <    hGlobal (putR s >> k)
% < = {-~  definition of |putR|  -}
% <    hGlobal (get >>= \ s' -> put s `mplus` side (put s') >> k)
% < = {-~  definition of |side|  -}
% <    hGlobal (get >>= \ s' -> put s `mplus` (put s' >> mzero) >> k)
% < = {-~  definition of |get, put, `mplus`, mzero, (>>=)| and smart constructors  -}
% <    hGlobal (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
% < = {-~  definition of |hGlobal|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
% < = {-~  definition of |hNDf| (twice)  -}
% <    (fmap (fmap fst) . hState1) (getOp (\ s' -> liftM2 (++) (putOp s (hNDf k)) (putOp s' (Var []))))
% < = {-~  definition of |hState1|  -}
% <    fmap (fmap fst) (\ s' -> (hState1 .
% <      (\ s' -> liftM2 (++) (putOp s (hNDf k)) (putOp s' (Var [])))) s' s')
% < = {-~  function application  -}
% <    fmap (fmap fst) (\ s' -> hState1 (liftM2 (++) (putOp s (hNDf k)) (putOp s' (Var []))) s')
% < = {-~  definition of |fmap|  -}
% <    \ s' -> fmap fst (hState1 (liftM2 (++) (putOp s (hNDf k)) (putOp s' (Var []))) s')
% < = {-~  definition of |liftM2|  -}
% <    \ s' -> fmap fst (hState1 (do {x <- putOp s (hNDf k); y <- putOp s' (Var []); return (x++y)}) s')
% < = {-~  |y = []| (property of free monad)  -}
% <    \ s' -> fmap fst (hState1 (do {x <- putOp s (hNDf k); putOp s' (Var []); return x}) s')
% < = {-~  reformulation  -}
% <    \ s' -> fmap fst (hState1 (putOp s (hNDf k) >>= \ x -> putOp s' (Var []) >> return x) s')
% < = {-~  let |f = (>>= \ x -> putOp s' (Var []) >> return x)|  -}
% <    \ s' -> fmap fst (hState1 (putOp s (f (hNDf k))) s')
% < = {-~  definition of |hState1|  -}
% <    \ s' -> fmap fst ((\ _ -> hState1 (f (hNDf k)) s) s')
% < = {-~  function application  -}
% <    \ s' -> fmap fst (hState1 (f (hNDf k)) s)
% < = {-~  reformulation  -}
% <    \ s' -> (fmap (fmap fst) . hState1 . f . hNDf) k s
% < = {-~  definition of |f|  -}
% <    \ s' -> fmap (fmap fst) $ hState1 (hNDf k >>= \ x -> putOp s' (Var []) >> return x) s
% % < = {-~  definition of |do|  -}
% % <    \ s' -> fmap (fmap fst) $ hState1 (
% % <      do  x <- hNDf k
% % <          putOp s' (Var [])
% % <          return x) s
% < = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
% <    \ s' -> fmap (fmap fst) $ hState1 (hNDf k) s >>= \(x,_) -> return (x, s')
% % <    \ s' -> fmap (fmap fst) $
% % <      do  (x, _) <- hState1 (hNDf k) s
% % <          return (x, s')
% < = {-~  definition of |hGlobal|  -}
% <    \ _ -> hGlobal k s
% < = {-~  definition of |alg'|  -}
% <    alg' (Inl (Put s (hGlobal k)))
% < = {-~  definition of |fmap|  -}
% <    (alg' . fmap hGlobal) (Inl (Put s k))
% 
% \noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}
% 
% <    (hGlobal . alg) (Inr (Inl Fail))
% < = {-~  definition of |alg|  -}
% <    hGlobal (Op (Inr (Inl Fail)))
% < = {-~  definition of |hGlobal|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inl Fail)))
% < = {-~  definition of |hNDf|  -}
% <    (fmap (fmap fst) . hState1) (Var [])
% < = {-~  definition of |hState1|  -}
% <    fmap (fmap fst) (\ s -> Var ([], s))
% < = {-~  evaluation of |fmap (fmap fst)|  -}
% <    \ s -> Var []
% < = {-~  definition of |alg'|  -}
% <    alg' (Inr (Inl Fail))
% < = {-~  definition of |fmap|  -}
% <    (alg' . fmap hGlobal) (Inr (Inl Fail))
% 
% \noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}
% 
% <    (hGlobal . alg) (Inr (Inl (Or p q)))
% < = {-~  definition of |alg|  -}
% <    hGlobal (Op (Inr (Inl (Or p q))))
% < = {-~  definition of |hGlobal|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inl (Or p q))))
% < = {-~  definition of |hNDf|  -}
% <    (fmap (fmap fst) . hState1) (liftM2 (++) (hNDf p) (hNDf q))
% < = {-~  definition of |liftM2|  -}
% <    (fmap (fmap fst) . hState1) (do {x <- hNDf p; y <- hNDf q; return (x ++ y)})
% < = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
% <    fmap (fmap fst) $ \ s -> do {  (x, s1) <- hState1 (hNDf p) s;
% <                                   (y, s2) <- hState1 (hNDf q) s1;
% <                                   return (x ++ y, s2) }
% < = {-~  Lemma \ref{lemma:state-restore} for |p| and |q| (use the assumption: |p,q| is in the range of |local2global|)  -}
% <    fmap (fmap fst) $ \ s -> do {  (x, s1) <- do {(x, _) <- hState1 (hNDf p) s; return (x, s)}
% <                                   (y, s2) <- do {(x, _) <- hState1 (hNDf q) s1; return (x, s1)}
% <                                   return (x ++ y, s2)}
% < = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)| and Law (\ref{eq:monad-ret-bind}): return-bind  -}
% <    fmap (fmap fst) $ \ s -> do {  (x, _) <- hState1 (hNDf p) s;
% <                                   (y, _) <- hState1 (hNDf q) s;
% <                                   return (x ++ y, s)}
% < = {-~  definition of |fmap| -}
% <    \ s -> fmap fst $ do {  (x, _) <- hState1 (hNDf p) s;
% <                            (y, _) <- hState1 (hNDf q) s;
% <                            return (x ++ y, s)}
% < = {-~  derived property for monad: |fmap f (m >>= k) = m >>= fmap f . k|  -}
% <    \ s -> do {  (x, _) <- hState1 (hNDf p) s;
% <                 (y, _) <- hState1 (hNDf q) s;
% <                 fmap fst $ return (x ++ y, s)}
% < = {-~  definition of |fmap fst|  -}
% <    \ s -> do {  x <- fmap fst (hState1 (hNDf p) s);
% <                 y <- fmap fst (hState1 (hNDf q) s);
% <                 fmap fst $ return (x ++ y, s)}
% < = {-~  reformulation  -}
% <    \ s -> do {  x <- (fmap fst . (hState1 . hNDf) p) s;
% <                 y <- (fmap fst . (hState1 . hNDf) q) s;
% <                 fmap fst $ return (x ++ y, s)}
% < = {-~  definition of |fmap| for |(r ->)|: |fmap f g = f . g|  -}
% <    \ s -> do {  x <- (fmap (fmap fst) ((hState1 . hNDf) p)) s;
% <                 y <- (fmap (fmap fst) ((hState1 . hNDf) q)) s;
% <                 fmap fst $ return (x ++ y, s)}
% < = {-~  definition of |fmap fst|  -}
% <    \ s -> do {  x <- (fmap (fmap fst) ((hState1 . hNDf) p)) s;
% <                 y <- (fmap (fmap fst) ((hState1 . hNDf) q)) s;
% <                 return (x ++ y)}
% < = {-~  reformulation  -}
% <    \ s -> do {  x <- (fmap (fmap fst) . hState1 . hNDf) p s;
% <                 y <- (fmap (fmap fst) . hState1 . hNDf) q s;
% <                 return (x ++ y)}
% < = {-~  definition of |hGlobal|  -}
% <    \ s -> do {  x <- hGlobal p s;
% <                 y <- hGlobal q s;
% <                 return (x ++ y)}
% < = {-~  definition of |liftM2|  -}
% <    \ s -> liftM2 (++) (hGlobal p s) (hGlobal q s)
% < = {-~  definition of |alg'|  -}
% <    alg' (Inr (Inl Or (hGlobal p) (hGlobal q)))
% < = {-~  definition of |fmap|  -}
% <    (alg' . fmap hGlobal) (Inr (Inl (Or p q)))
% 
% \noindent \mbox{\underline{case |t = Inr (Inr y)|}}
% 
% <    (hGlobal . alg) (Inr (Inr y))
% < = {-~  definition of |alg|  -}
% <    hGlobal (Op (Inr (Inr y)))
% < = {-~  definition of |hGlobal|  -}
% <    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inr y)))
% < = {-~  definition of |hNDf|  -}
% <    (fmap (fmap fst) . hState1) (Op (Inr (fmap hNDf y)))
% < = {-~  definition of |hState1|  -}
% <    fmap (fmap fst) (\ s -> Op (fmap ((\ k -> k s) . hState1) (fmap hNDf y)))
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
% <    fmap (fmap fst) (\ s -> Op (fmap ((\ k -> k s) . hState1 . hNDf) y))
% < = {-~  evaluation of |fmap (fmap fst)|  -}
% <    \ s -> fmap fst (Op (fmap ((\ k -> k s) . hState1 . hNDf) y))
% < = {-~  definition of |fmap| for free monad  -}
% <    \ s -> Op (fmap (fmap fst) (fmap ((\ k -> k s) . hState1 . hNDf) y))
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
% <    \ s -> Op (fmap (fmap fst . (\ k -> k s) . hState1 . hNDf) y)
% < = {-~  reformulation  -}
% <    \ s -> Op (fmap ((\t -> fmap fst (t s)) . hState1 . hNDf) y)
% < = {-~  reformulation  -}
% <    \ s -> Op (fmap ((\ t -> (\ k -> k s) (fmap fst . t)) . hState1 . hNDf) y)
% < = {-~  definition of |fmap| for |((->) r)| and |eta|-expansion  -}
% <    \ s -> Op (fmap ((\ k -> k s) . fmap (fmap fst) . hState1 . hNDf) y)
% < = {-~  definition of |hGlobal|  -}
% <    \ s -> Op (fmap ((\ k -> k s) . hGlobal) y)
% < = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
% <    \ s -> Op (fmap (\ k -> k s) (fmap hGlobal y))
% < = {-~  definition of |alg'|  -}
% <    alg' (Inr (Inr (fmap hGlobal y)))
% < = {-~  definition of |fmap|  -}
% <    (alg' . fmap hGlobal) (Inr (Inr y))
% \end{proof}
% 
% %if False
% \begin{lemma} \label{lemma:local-local}
% |hLocal . local2global = hLocal|
% \end{lemma}
% 
% \begin{proof}
% The function |local2global| replace all |put t| with |putR t|.
% The definition of |putR| is |putR s = get >>= \t -> put s `mplus` side (put t)|, and the definition of |side| is |side m = m >> mzero|.
% For |hLocal|, we have the law \ref{eq:put-right-identity}, so |side (put t) = (put t) >> zero = zero|, which means |put t| is also equal to |putR t|.
% Thus, |hLocal . local2global = hLocal . identity = hLocal|.
% \end{proof}
% %endif


