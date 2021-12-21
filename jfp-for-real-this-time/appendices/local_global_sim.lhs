\section{Simulating Local State with Global State: The Proofs}
\label{app:local-global}

%-------------------------------------------------------------------------------

This section shows that the function |hGlobal . local2global| is equivalent to |hLocal|,
where |hGlobal|, |local2global| and |hLocal| are defined in Section \ref{sec:putr}.
In this section, we assume implicit commutativity and associativity of the coproduct
operator |(:+:)| (\Cref{sec:transforming-between-local-and-global-state}).

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


\begin{theorem}\label{eq:local-global}
|hGlobal . local2global = hLocal|
\end{theorem}
\begin{proof}
We start with applying fold fusion to both sides of the equation.
We rewrite |hLocal| as |hL . hState1|, where |hL| is defined as follows:
\begin{spec}
hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
hL = fmap hL'
  where hL' = fmap (fmap fst) . hNDf
\end{spec}
We can expand the definition of |hState1| and use the fold fusion law for postcomposition as defined in Equation \ref{eq:fusion-post}:
<    hL . hState1
< = {-~  definition of |hState1|  -}
<    hL . fold genS (algS # fwdS)
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hL . genS) (algS' # fwdS') {-" \text{with } "-} hL . (algS # fwdS) = (algS' # fwdS') . fmap hL

For the left hand side, we can also expand the definition of |local2global| and use the fold fusion law (Law (\ref{eq:functor-composition})):
<    hGlobal . local2global
< = {-~  definition of |local2global|  -}
<    hGlobal . fold Var alg
< = {-~  fold fusion-post' (Equation \ref{eq:fusion-post-strong})  -}
<    fold (hGlobal . Var) alg'
<      {-" \text{with } "-} hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global

The algebras |alg'| and |algS'| are constructed later.
% Note that we only need the equation |hGlobal . alg = alg' . fmap hGlobal| to hold for inputs |t :: (StateF s :+: (NondetF :+: f)) (Free (StateF s :+: NondetF :+: f) a)| in the range of |fmap local2global|.
Then, we can use the universal property of fold to show that |hLocal = fold (hL . genS) algS'| and |hGlobal . local2global = fold (hGlobal . Var) alg'| are equal.
To do this, we have to prove that
\begin{enumerate}
    \item |hL . genS  = hGlobal . Var|
    \item |algS'      = alg'|
    \item |fwdS'      = fwd'|
\end{enumerate}
The first item is simple to prove with equational reasoning.
We want to prove that |hL . genS = hGlobal . Var| for all inputs |x :: a|.

<    (hL . genS) x
< = {-~  definition of |hState1|  -}
<    hL (\ s -> Var (x, s))
< = {-~  definition of |hL|  -}
<    fmap (fmap (fmap fst) . hNDf) (\ s -> Var (x, s))
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    (fmap (fmap (fmap fst)) . fmap hNDf) (\ s -> Var (x, s))
< = {-~  application of |fmap hNDf|  -}
<    fmap (fmap (fmap fst)) (\ s -> hNDf (Var (x, s)))
< = {-~  definition of |hNDf|  -}
<    fmap (fmap (fmap fst)) (\ s -> (Var $ etal (x, s)))
< = {-~  definition of |etal|  -}
<    fmap (fmap (fmap fst)) (\ s -> Var [(x, s)])
< = {-~  evaluation of |fmap (fmap (fmap fst))|  -}
<    \ s -> Var [x]
< = {-~  property of |fmap| and |fst|  -}
<    fmap (fmap fst) (\ s -> Var ([x], s))
< = {-~  definition of |hState1|  -}
<    (fmap (fmap fst) . hState1) (Var [x])
< = {-~  definition of |etal|  -}
<    (fmap (fmap fst) . hState1) (Var $ etal x)
< = {-~  definition of |hNDf|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (Var x)
< = {-~  definition of |hGlobal|  -}
<    hGlobal (Var x)
< = {-~  reformulation  -}
<    (hGlobal . Var) x

So we have |hL . genS = hGlobal . Var|.

For the second item, instead of constructing |alg'| and |algS'| individually, we only construct |alg'| and then verify that the following two equations hold:

\begin{enumerate}
    \item |hL . algS = alg' . fmap hL|
    \item |hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global|
\end{enumerate}

The |alg'| is defined as follows:
\begin{code}
alg' :: Functor f => (StateF s :+: (NondetF :+: f)) (s -> Free f [a]) -> s -> Free f [a]
alg' = alg1 # alg2 # fwd1
  where alg1 (Get k)    = \ s -> k s s
        alg1 (Put s k)  = \ _ -> k s
        alg2 Fail       = \ s -> Var []
        alg2 (Or p q)   = \ s -> liftA2 (++) (p s) (q s)
        fwd1 y          = \ s -> Op (fmap ($s) y)
\end{code}
These two equations (1) and (2) are proved in Lemma \ref{eq:fusion-cond-1} and Lemma \ref{eq:fusion-cond-2} respectively.
This implies that our original equation |hLocal = fold (hL . genS) alg' = fold (hGlobal . Var) alg' = hGlobal . local2global| holds.
\end{proof}

\begin{lemma}[Fusion Condition 1] \label{eq:fusion-cond-1}
|alg' . fmap hL = hL . algS|
\end{lemma}
\begin{proof}
We need to prove it holds for all inputs |t :: (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))|.
We do a case analysis on |t|.

\noindent \mbox{\underline{case |t = Inl (Get k)|}}
% k :: s -> s -> Free (NondetF :+: f) (a, s)

<    (alg' . fmap hL) (Inl (Get k))
< = {-~  definition of |fmap|  -}
<    alg' (Inl (Get (hL . k)))
< = {-~  definition of |alg'|  -}
<    \ s -> hL (k s) s
< = {-~  |eta|-expansion  -}
<    \ s -> hL (\ s' -> k s s') s
< = {-~  definition of |hL|  -}
<    \ s -> (fmap hL') (\ s' -> k s s') s
< = {-~  definition of |fmap|  -}
<    \ s -> (\ s' -> hL' (k s s')) s
< = {-~  function application  -}
<    \ s -> hL' (k s s)
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ s -> k s s)
< = {-~  definition of |hL|  -}
<    hL (\ s -> k s s)
< = {-~  definition of |hState1|  -}
<    (hL . algS) (Inl (Get k))

\noindent \mbox{\underline{case |t = Inl (Put s k)|}}
% s :: s, k :: s -> Free (NondetF :+: f) (a, s)

<    (alg' . fmap hL) (Inl (Put s k))
< = {-~  definition of |fmap|  -}
<    alg' (Inl (Put s (hL k)))
< = {-~  definition of |alg'|  -}
<    \ _ -> hL k s
< = {-~  |eta|-expansion  -}
<    \ _ -> hL (\ s' -> k s') s
< = {-~  definition of |hL|  -}
<    \ _ -> (fmap hL') (\ s' -> k s') s
< = {-~  definition of |fmap|  -}
<    \ _ -> (\ s' -> hL' (k s')) s
< = {-~  function application  -}
<    \ _ -> hL' (k s)
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ _ -> k s)
< = {-~  definition of |hL|  -}
<    hL (\ _ -> k s)
< = {-~  definition of |hState1|  -}
<    (hL . algS) (Inl (Put s k))

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

<    (alg' . fmap hL) (Inr (Inl Fail))
< = {-~  definition of |fmap|  -}
<    alg' (Inr (Inl Fail))
< = {-~  definition of |alg'|  -}
<    \ s -> Var []
< = {-~  definition of |fmap|  -}
<    \ s -> fmap (fmap fst) (Var [])
< = {-~  definition of |hNDf|  -}
<    \ s -> (fmap (fmap fst) . hNDf) (Op (Inl Fail))
< = {-~  definition of |hL'|  -}
<    \ s -> hL' (Op (Inl Fail))
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ s -> Op (Inl Fail))
< = {-~  definition of |hL|  -}
<    hL (\ s -> Op (Inl Fail))
< = {-~  definition of |fmap|  -}
<    hL (\ s -> Op (fmap (\ k -> k s) (Inl Fail)))
< = {-~  definition of |hState1|  -}
<    (hL . algS) (Inr (Inl Fail))

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}
% p, q :: s -> Free (NondetF :+: f) (a, s)

<    (alg' . fmap hL) (Inr (Inl (Or p q)))
< = {-~  evaluation of |fmap hL|  -}
<    alg' (Inr (Inl (Or (hL p) (hL q))))
< = {-~  definition of |alg'|  -}
<    \ s -> liftA2 (++) (hL p s) (hL q s)
< = {-~  |eta|-expansion (twice)  -}
<    \ s -> liftA2 (++) (hL (\ s' -> p s') s) (hL (\ s' -> q s') s)
< = {-~  definition of |hL|  -}
<    \ s -> liftA2 (++) ((fmap hL') (\ s' -> p s') s) ((fmap hL') (\ s' -> q s') s)
< = {-~  definition of |fmap|  -}
<    \ s -> liftA2 (++) ((\ s' -> hL' (p s')) s) ((\ s' -> hL' (q s')) s)
< = {-~  function application  -}
<    \ s -> liftA2 (++) (hL' (p s)) (hL' (q s))
< = {-~  definition of |hL'|  -}
<    \ s -> liftA2 (++) (fmap (fmap fst) (hNDf (p s))) (fmap (fmap fst) (hNDf (q s)))
< = {-~  Lemma \ref{eq:liftA2-fst-comm}  -}
<    \ s -> fmap (fmap fst) (liftA2 (++) (hNDf (p s)) (hNDf (q s)))
< = {-~  definition of |hNDf|  -}
<    \ s -> (fmap (fmap fst) . hNDf) (Op (Inl (Or (p s) (q s))))
< = {-~  definition of |hL'|  -}
<    \ s -> hL' (Op (Inl (Or (p s) (q s))))
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ s -> Op (Inl (Or (p s) (q s))))
< = {-~  definition of |hL|  -}
<    hL (\ s -> Op (Inl (Or (p s) (q s))))
< = {-~  definition of |fmap|  -}
<    hL (\ s -> Op (fmap (\ k -> k s) (Inl (Or p q))))
< = {-~  definition of |hState1|  -}
<    (hL . algS) (Inr (Inl (Or p q)))

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}
% y :: f (s -> Free (NondetF :+: f) (a, s))

<    (alg' . fmap hL) (Inr (Inr y))
< = {-~  evaluation of |fmap hL|  -}
<    alg' (Inr (Inr (fmap hL y)))
< = {-~  definition of |alg'|  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap hL y))
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    \ s -> Op (fmap ((\ k -> k s) . hL) y)
< = {-~  definition of |hL|  -}
<    \ s -> Op (fmap ((\ k -> k s) . (fmap hL')) y)
< = {-~  |eta|-expansion and definition of |fmap| for |((->) r)| -}
<    \ s -> Op (fmap (\t -> (\ k -> k s) . (hL' . t)) y)
< = {-~  function application -}
<    \ s -> Op (fmap (\t -> (hL' (t s))) y)
< = {-~  reformulation -}
<    \ s -> Op (fmap (hL' . ($s)) y)
< = {-~  definition of |hL'|  -}
<    \ s -> Op (fmap (fmap (fmap fst) . hNDf . ($s)) y)
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|   -}
<    \ s -> Op (fmap (fmap (fmap fst) (fmap hNDf (fmap ($s) y))))
< = {-~  definition of |fmap| for free monad  -}
<    \ s -> fmap (fmap fst) (Op (fmap hNDf (fmap ($s) y)))
< = {-~  definition of |hNDf|  -}
<    \ s -> fmap (fmap fst) (hNDf (Op (Inr (fmap ($s) y))))
< = {-~  definition of |fmap|  -}
<    \ s -> fmap (fmap fst) (hNDf (Op (fmap ($s) (Inr y))))
< = {-~  definition of |hL'|  -}
<    \ s -> hL' (Op (fmap ($s) (Inr y)))
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ s -> Op (fmap ($s) (Inr y)))
< = {-~  definition of |hL|  -}
<    hL (\ s -> Op (fmap ($s) (Inr y)))
< = {-~  definition of |hState1|  -}
<    (hL . algS) (Inr (Inr y))
\end{proof}

% no longer necessary
% \begin{lemma}\label{eq:dollar-fmap-comm}~
% < (\ k -> k s) . fmap f = f . (\ k -> k s)
% with function |f :: a -> b| and input |t :: s -> a|.
% % holds for any function |f :: a -> b| and input |t :: s -> a| in the above proof.
% \end{lemma}
% \begin{proof} ~
% <    ((\ k -> k s) . fmap f) t
% < = {-~  definition of |fmap|  -}
% <    (\ k -> k s) (f . t)
% < = {-~  function application  -}
% <    (f . t) s
% < = {-~  reformulation  -}
% <    f (t s)
% < = {-~  reformulation  -}
% <    (f . (\ k -> k s)) t
% \end{proof}

\begin{lemma} \label{eq:liftA2-fst-comm}~
< fmap (fmap fst) (liftA2 (++) p q) = liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{lemma}
\begin{proof}~

<    fmap (fmap fst) (liftA2 (++) p q)
< = {-~  definition of |liftA2| -}
<    fmap (fmap fst) (do {x <- p; y <- q; return (x ++ y)})
< = {-~  derived property for monad: |fmap f (m >>= k) = m >>= fmap f . k| -}
<    do {x <- p; y <- q; fmap (fmap fst) (return (x ++ y))}
< = {-~  definition of |fmap| -}
<    do {x <- p; y <- q; return ((fmap fst x) ++ (fmap fst y))}
< = {-~  reformulation -}
<    do {x <- fmap (fmap fst) p; y <- fmap (fmap fst) q; return (x ++ y)}
< = {-~  definition of |liftA2| -}
<    liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{proof}

% no longer necessary
% \begin{lemma}[Fusion of |hL'|]\label{eq:hl-fusion}~
%
% < hL' = fold (fmap (fmap fst) . genND) algL'
% where |algL'| is defined as follows:
% <     algL' :: Functor f => (NondetF :+: f) (Free f [a]) -> Free f [a]
% <     algL' (Inl Fail) = Var []
% <     algL' (Inl (Or p q)) = liftA2 (++) p q
% <     algL' (Inr y) = Op y
% \end{lemma}
%
% \begin{proof} ~
% <    hL'
% < = {-~  definition of |hL'|  -}
% <    fmap (fmap fst) . hNDf
% < = {-~  definition of |hNDf|  -}
% <    fmap (fmap fst) . fold genND algND
% < = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
% <    fold (fmap (fmap fst) genND) algL'
%
% So we only need to prove that the equation |fmap (fmap fst) . algND = algL' . fmap (fmap (fmap fst))| holds for all inputs |t :: (NondetF :+: f) (Free f [(a, s)])|.
% We do this by a case analysis on |t|.
%
% \noindent \mbox{\underline{case |t = Inl Fail|}}
% <    (fmap (fmap fst) . algND) (Inl Fail)
% < = {-~  definition of |algND|  -}
% <    fmap (fmap fst) (Var [])
% < = {-~  definition of |fmap|  -}
% <    Var []
% < = {-~  definition of |algL'|  -}
% <    algL' (Inl Fail)
% < = {-~  definition of |fmap|  -}
% <    (algL' . fmap (fmap (fmap fst))) (Inl Fail)
%
% \noindent \mbox{\underline{case |t = Inl (Or p q)|}}
% <    (fmap (fmap fst) . algND) (Inl (Or p q))
% < = {-~  definition of |algND|  -}
% <    fmap (fmap fst) (liftA2 (++) p q)
% < = {-~  Lemma \ref{eq:liftA2-fst-comm}  -}
% <    liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
% < = {-~  definition of |algL'|  -}
% <    algL' (Inl (Or (fmap (fmap fst) p) (fmap (fmap fst) q)))
% < = {-~  definition of |fmap|  -}
% <    (algL' . fmap (fmap (fmap fst))) (Inl (Or p q))
%
% \noindent \mbox{\underline{case |t = Inr y|}}
% <    (fmap (fmap fst) . algND) (Inr y)
% < = {-~  definition of |algND|  -}
% <    fmap (fmap fst) (Op y)
% < = {-~  definition of |fmap|  -}
% <    Op ((fmap (fmap (fmap fst)) y))
% < = {-~  definition of |algL'|  -}
% <    algL' (Inr (fmap (fmap (fmap fst)) y))
% < = {-~  definition of |fmap|  -}
% <    (algL' . fmap (fmap (fmap fst))) (Inr y)
%
% \end{proof}

\begin{lemma}[Fusion Condition 2] \label{eq:fusion-cond-2}
|hGlobal . alg . fmap local2global = alg' . fmap hGlobal . fmap local2global|
\footnote{Note that the |alg| here refers to the |alg| in the definition of |local2global|.}
\end{lemma}
\begin{proof}
We prove this equation in a similar way to Lemma \ref{eq:fusion-cond-1}.
We need to prove |hGlobal (alg t) = alg' (fmap hGlobal t)| holds for all inputs |t :: (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: f) a)| that are in the range of |fmap local2global|.
% All |local2global| formations relevant to commutativity and associativity are implicit and not shown in the following proofs.

\noindent \mbox{\underline{case |t = Inl (Get k)|}}

<    (hGlobal . alg) (Inl (Get k))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inl (Get k)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (Op (Inl (Get k)))
< = {-~  definition of |hNDf|  -}
<    (fmap (fmap fst) . hState1) (Op (Inl (Get (hNDf . k))))
< = {-~  definition of |hState1|  -}
% <    fmap (fmap fst) (algS (Inl (Get (hState1 . hNDf . k))))
% < = {-~  evaluation of |algS|  -}
<    fmap (fmap fst) (\ s -> (hState1 . hNDf . k) s s)
< = {-~  function application  -}
<    fmap (fmap fst) (\ s -> (hState1 . hNDf) (k s) s)
< = {-~  definition of |fmap|  -}
<    \ s -> fmap fst ((hState1 . hNDf) (k s) s)
< = {-~  reformulation  -}
<    \ s -> (fmap fst . (hState1 . hNDf) (k s)) s
< = {-~  definition of |fmap|  -}
<    \ s -> (fmap (fmap fst) ((hState1 . hNDf) (k s))) s
< = {-~  reformulation  -}
<    \ s -> (fmap (fmap fst) . hState1 . hNDf) (k s) s
< = {-~  definition of |hGlobal|  -}
<    \ s -> hGlobal (k s) s
< = {-~  definition of |alg'|  -}
<    alg' (Inl (Get (hGlobal . k)))
< = {-~  definition of |fmap|  -}
<    (alg' . fmap hGlobal) (Inl (Get k))

\noindent \mbox{\underline{case |t = Inl (Put s k)|}}

For simplicity, we assume that smart constructors |getOp, putOp, orOp, failOp|
automatically insert correct |Op, Inl, Inr| constructors based on the context
in order to make the term well-typed in the following proof.
In this way, we avoid the tedious details of dealing with these constructors manually.

<    (hGlobal . alg) (Inl (Put s k))
< = {-~  definition of |alg|  -}
% NOTE: putR here
% <    hGlobal (putROp s k)
% < = {-~  definition of |putROp|  -}
<    hGlobal (putR s >> k)
< = {-~  definition of |putR|  -}
<    hGlobal (get >>= \ s' -> put s `mplus` side (put s') >> k)
< = {-~  definition of |side|  -}
<    hGlobal (get >>= \ s' -> put s `mplus` (put s' >> mzero) >> k)
< = {-~  definition of |get, put, `mplus`, mzero, (>>=)| and smart constructors  -}
<    hGlobal (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
< = {-~  definition of |hNDf| (twice)  -}
<    (fmap (fmap fst) . hState1) (getOp (\ s' -> liftA2 (++) (putOp s (hNDf k)) (putOp s' (Var []))))
< = {-~  definition of |hState1|  -}
<    fmap (fmap fst) (\ s' -> (hState1 .
<      (\ s' -> liftA2 (++) (putOp s (hNDf k)) (putOp s' (Var [])))) s' s')
< = {-~  function application  -}
<    fmap (fmap fst) (\ s' -> hState1 (liftA2 (++) (putOp s (hNDf k)) (putOp s' (Var []))) s')
< = {-~  definition of |fmap|  -}
<    \ s' -> fmap fst (hState1 (liftA2 (++) (putOp s (hNDf k)) (putOp s' (Var []))) s')
< = {-~  definition of |liftA2|  -}
<    \ s' -> fmap fst (hState1 (do {x <- putOp s (hNDf k); y <- putOp s' (Var []); return (x++y)}) s')
< = {-~  |y = []| (property of free monad)  -}
<    \ s' -> fmap fst (hState1 (do {x <- putOp s (hNDf k); putOp s' (Var []); return x}) s')
< = {-~  reformulation  -}
<    \ s' -> fmap fst (hState1 (putOp s (hNDf k) >>= \ x -> putOp s' (Var []) >> return x) s')
< = {-~  let |f = (>>= \ x -> putOp s' (Var []) >> return x)|  -}
<    \ s' -> fmap fst (hState1 (putOp s (f (hNDf k))) s')
< = {-~  definition of |hState1|  -}
<    \ s' -> fmap fst ((\ _ -> hState1 (f (hNDf k)) s) s')
< = {-~  function application  -}
<    \ s' -> fmap fst (hState1 (f (hNDf k)) s)
< = {-~  reformulation  -}
<    \ s' -> (fmap (fmap fst) . hState1 . f . hNDf) k s
< = {-~  definition of |f|  -}
<    \ s' -> fmap (fmap fst) $ hState1 (hNDf k >>= \ x -> putOp s' (Var []) >> return x) s
% < = {-~  definition of |do|  -}
% <    \ s' -> fmap (fmap fst) $ hState1 (
% <      do  x <- hNDf k
% <          putOp s' (Var [])
% <          return x) s
< = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
<    \ s' -> fmap (fmap fst) $ hState1 (hNDf k) s >>= \(x,_) -> return (x, s')
% <    \ s' -> fmap (fmap fst) $
% <      do  (x, _) <- hState1 (hNDf k) s
% <          return (x, s')
< = {-~  definition of |hGlobal|  -}
<    \ _ -> hGlobal k s
< = {-~  definition of |alg'|  -}
<    alg' (Inl (Put s (hGlobal k)))
< = {-~  definition of |fmap|  -}
<    (alg' . fmap hGlobal) (Inl (Put s k))

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

<    (hGlobal . alg) (Inr (Inl Fail))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inl Fail)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inl Fail)))
< = {-~  definition of |hNDf|  -}
<    (fmap (fmap fst) . hState1) (Var [])
< = {-~  definition of |hState1|  -}
<    fmap (fmap fst) (\ s -> Var ([], s))
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> Var []
< = {-~  definition of |alg'|  -}
<    alg' (Inr (Inl Fail))
< = {-~  definition of |fmap|  -}
<    (alg' . fmap hGlobal) (Inr (Inl Fail))

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}

<    (hGlobal . alg) (Inr (Inl (Or p q)))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inl (Or p q))))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inl (Or p q))))
< = {-~  definition of |hNDf|  -}
<    (fmap (fmap fst) . hState1) (liftA2 (++) (hNDf p) (hNDf q))
< = {-~  definition of |liftA2|  -}
<    (fmap (fmap fst) . hState1) (do {x <- hNDf p; y <- hNDf q; return (x ++ y)})
< = {-~  Lemma \ref{lemma:dist-hState1}: distributivity of |hState1|  -}
<    fmap (fmap fst) $ \ s -> do {  (x, s1) <- hState1 (hNDf p) s;
<                                   (y, s2) <- hState1 (hNDf q) s1;
<                                   return (x ++ y, s2) }
< = {-~  Lemma \ref{lemma:state-restore} for |p| and |q| (use the assumption: |p,q| is in the range of |local2global|)  -}
<    fmap (fmap fst) $ \ s -> do {  (x, s1) <- do {(x, _) <- hState1 (hNDf p) s; return (x, s)}
<                                   (y, s2) <- do {(x, _) <- hState1 (hNDf q) s1; return (x, s1)}
<                                   return (x ++ y, s2)}
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)| and Law (\ref{eq:monad-ret-bind}): return-bind  -}
<    fmap (fmap fst) $ \ s -> do {  (x, _) <- hState1 (hNDf p) s;
<                                   (y, _) <- hState1 (hNDf q) s;
<                                   return (x ++ y, s)}
< = {-~  definition of |fmap| -}
<    \ s -> fmap fst $ do {  (x, _) <- hState1 (hNDf p) s;
<                            (y, _) <- hState1 (hNDf q) s;
<                            return (x ++ y)}
< = {-~  derived property for monad: |fmap f (m >>= k) = m >>= fmap f . k|  -}
<    \ s -> do {  (x, _) <- hState1 (hNDf p) s;
<                 (y, _) <- hState1 (hNDf q) s;
<                 fmap fst $ return (x ++ y)}
< = {-~  reformulation \todo{I don't understand this step}  -}
<    \ s -> do {  x <- (fmap (fmap fst) . hState1 . hNDf) p s;
<                 y <- (fmap (fmap fst) . hState1 . hNDf) q s;
<                 return (x ++ y)}
< = {-~  definition of |hGlobal|  -}
<    \ s -> do {  x <- hGlobal p s;
<                 y <- hGlobal q s;
<                 return (x ++ y)}
< = {-~  definition of |liftA2|  -}
<    \ s -> liftA2 (++) (hGlobal p s) (hGlobal q s)
< = {-~  definition of |alg'|  -}
<    alg' (Inr (Inl Or (hGlobal p) (hGlobal q)))
< = {-~  definition of |fmap|  -}
<    (alg' . fmap hGlobal) (Inr (Inl (Or p q)))

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}

<    (hGlobal . alg) (Inr (Inr y))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inr y)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hNDf) (Op (Inr (Inr y)))
< = {-~  definition of |hNDf|  -}
<    (fmap (fmap fst) . hState1) (Op (Inr (fmap hNDf y)))
< = {-~  definition of |hState1|  -}
<    fmap (fmap fst) (\ s -> Op (fmap ((\ k -> k s) . hState1) (fmap hNDf y)))
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    fmap (fmap fst) (\ s -> Op (fmap ((\ k -> k s) . hState1 . hNDf) y))
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> fmap fst (Op (fmap ((\ k -> k s) . hState1 . hNDf) y))
< = {-~  definition of |fmap| for free monad  -}
<    \ s -> Op (fmap (fmap fst) (fmap ((\ k -> k s) . hState1 . hNDf) y))
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    \ s -> Op (fmap (fmap fst . (\ k -> k s) . hState1 . hNDf) y)
< = {-~  reformulation  -}
<    \ s -> Op (fmap ((\t -> fmap fst (t s)) . hState1 . hNDf) y)
< = {-~  reformulation  -}
<    \ s -> Op (fmap ((\ t -> (\ k -> k s) (fmap fst . t)) . hState1 . hNDf) y)
< = {-~  definition of |fmap| for |((->) r)| and |eta|-expansion  -}
<    \ s -> Op (fmap ((\ k -> k s) . fmap (fmap fst) . hState1 . hNDf) y)
< = {-~  definition of |hGlobal|  -}
<    \ s -> Op (fmap ((\ k -> k s) . hGlobal) y)
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap hGlobal y))
< = {-~  definition of |alg'|  -}
<    alg' (Inr (Inr (fmap hGlobal y)))
< = {-~  definition of |fmap|  -}
<    (alg' . fmap hGlobal) (Inr (Inr y))
\end{proof}

%if False
\begin{lemma} \label{lemma:local-local}
|hLocal . local2global = hLocal|
\end{lemma}

\begin{proof}
The function |local2global| replace all |put t| with |putR t|.
The definition of |putR| is |putR s = get >>= \t -> put s `mplus` side (put t)|, and the definition of |side| is |side m = m >> mzero|.
For |hLocal|, we have the law \ref{eq:put-right-identity}, so |side (put t) = (put t) >> zero = zero|, which means |put t| is also equal to |putR t|.
Thus, |hLocal . local2global = hLocal . identity = hLocal|.
\end{proof}
%endif

\begin{lemma}[Distributivity of |hState1|] \label{lemma:dist-hState1}
< hState1 (p >>= k) = hState1 p >>= hState1 . k
\end{lemma}

\begin{proof}
\todo{}
\end{proof}

\begin{lemma}[State is Restored] \label{lemma:state-restore}
For all |t :: Free (NondetF :+: StateF s :+: f) a|
< hState1 (hNDf (local2global t)) :: StateT s (Free f) [a]
does not change the state in the global-state semantics.
Formally,
< hState1 (hNDf t') s == do (x, _) <- hState1 (hNDf t') s; return (x, s)
where |t' = local2global t|.
\end{lemma}

%if False
% This proof is wrong because of circular argument
\begin{proof}
  We construct the program |q = Op . Inr . Inl $ Or (p >> get) get|.
  Because |p| is in the range of |local2global|, |q| is also in the range of |local2global|.
  By theorem \ref{eq:local-local} and the assumption |hGlobal (local2global p') = hLocal p'|, we have the equation that |hGlobal p = hGlobal (local2global p') = hLocal p' = hLocal (local2global p') = hLocal p|.
  We construct |q' = Op . Inr . Inl $ Or (p' >> get) get|.
  It is easy to verify that |q = local2global q'| and |hGlobal (local2global q') = hLocal q'|.
  Similarly, we also have |hGlobal q = hLocal q|. \wenhao{Wrong!Circular argument.}
  From the definition of |hGlobal| and |hLocal|, we have:
  < hGlobal q s = do [s1,s2] <- hGlobal q s; return [s1, s2] = do s1 <- hGlobal p s; return [s1, s1]
  < hLocal q s = do [s1,s2] <- hLocal q s; return [s1, s2] = do s1 <- hLocal p s; return [s1, s]
  % For the two expression |do ss <- hGlobal q s| and |do ss' <- hLocal q s|, we have |ss == [s', s']| and |ss' == [s', s]| by the definition of |hGlobal| and |hLocal|.
  From |hGlobal q s = hLocal q s| we have |s1 = s|, which means |hGlobal p s = do _ <- hGlobal p s; return s|.
  Because |hGlobal| is defined as |fmap (fmap fst) . runStateT . hState . hNDf|, we have the equation |hState1 (hNDf p) s == do (x, _) <- hState1 (hNDf p) s; return (x, s)|.
\end{proof}
%endif

\begin{proof}
The proof proceeds by structural induction on the free monad |t|.
% In the following proofs, we assume implicit commutativity and associativity of
% the coproduct operator |(:+:)| (\Cref{sec:transforming-between-local-and-global-state}).
We assume the smart constructors |getOp, putOp, orOp, failOp|, which are wrappers around
constructors |Get, Put, Or, Fail|, respectively, automatically insert correct |Op, Inl, Inr|
constructors based on the context to make the term well-typed in the following proof.

\noindent \mbox{\underline{case |t = Var y|}}
<    hState1 (hNDf (local2global (Var y))) s
< = {-~  definition of |local2global|  -}
<    hState1 (hNDf (Var y)) s
< = {-~  definition of |hNDf|  -}
<    hState1 (Var [y]) s
< = {-~  definition of |hState1|  -}
<    \ s -> Var ([y], s)
< = {-~  definition of |local2global, hNDf, hState1|  -}
<    do (x, _) <- hState1 (hNDf (local2global (Var y))) s; return (x, s)

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
< = {-~  definition of |do| and |orOp|  -}
<    hState1 (hNDf (do t' <- get; orOp (put t) (side (put t')); local2global k)) s
< = {-~  definition of |side| and |failOp|  -}
<    hState1 (hNDf (do t' <- get; orOp (put t) ((put t') >> failOp); local2global k)) s
< = {-~  Lemma \ref{lemma:dist-hNDf}: distributivity of |hNDf|  -}
<    hState1 (do  t'  <- get;
<                 x   <- hNDf (put t >> local2global k);
<                 y   <- hNDf (put t' >> failOp >> local2global k);
<                 return (x ++ y)) s
< = {-~  Law (\ref{eq:mzero-zero}): left identity of |mzero|  -}
<    hState1 (do  t'  <- get;
<                 x   <- hNDf (put t >> local2global k);
<                 y   <- hNDf (put t' >> failOp);
<                 return (x ++ y)) s
< = {-~  \todo{I don't understand this step}  -}
<    hState1 (do  t' <- get;
<                 x  <- hNDf (put t >> local2global k);
<                 put t';
<                 return x) s
< = {-~  Law (\ref{eq:get-put}): get-put  -}
<    hState1 (do  x  <- hNDf (put t >> local2global k);
<                 return x) s
< = {-~  reformulation  -}
<    hState1 (hNDf (put t >> local2global k)) s
< = {-~  \todo{I don't understand this step, can we do induction here?}  -}
< = {-~  induction hypothesis  -}
% <    do (x, _) <- do {(x, _) <- hState1 (hNDf (put t >> local2global k)) s; return (x, s)}; return (x, s)
% < = {-~  reformulation  -}
<    do (x, _) <- hState1 (hNDf (put t >> local2global k)) s; return (x, s)
< = {-~  definition of |putOp|  -}
<    do (x, _) <- hState1 (hNDf (local2global (putOp t k))) s; return (x, s)

\noindent \mbox{\underline{case |t = orOp p q|}}
<    hState1 (hNDf (local2global (orOp p q))) s
< = {-~  definition of |local2global|; let |p' = local2global p, q' = local2global q|  -}
<    hState1 (hNDf (orOp p' q')) s
< = {-~  definition of |hNDf|  -}
<    hState1 (liftA2 (++) (hNDf p') (hNDf q')) s
< = {-~  definition of |liftA2|  -}
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
