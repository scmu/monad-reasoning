\section{Simulating Local State with Global State: The Proofs}
\label{app:local-global}

%-------------------------------------------------------------------------------

This section shows that the function |hGlobal . local2global| is equivalent to |hLocal|, where |hGlobal|, |local2global| and |hLocal| are defined in Section \ref{sec:local2globalforming-between-local-and-global-state}.

It is easy to see that |runStateT . hState| can be fused into a single fold defined as follows:
\begin{code}
hState1 :: Functor f => Free (StateF s :+: f) a -> (s -> Free f (a, s))
hState1  =  fold genS (algS # fwdS)
  where 
    genS x          s  = return (x, s)
    algS (Get k)    s  = k s s
    algS (Put s k)  _  = k s
    fwdS y          s  = Op (fmap ($s) y)
\end{code}
For simplicity, we will use |hState1| to replace |runStateT . hState| in the following proofs.


\begin{theorem}\label{eq:local-global}
|hGlobal . local2global = hLocal|
\end{theorem}
\begin{proof}
We start with applying fold fusion to both sides of the equation.
We rewrite |hLocal| as |hL . hState1|, where |hL| is defined as follows:
\begin{code}
hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
hL = fmap hL'
  where hL' = fmap (fmap fst) . hND
\end{code}
We can expand the definition of |hState1| and use the fold fusion law for postcomposition as defined in Equation \ref{eq:fusion-post}:
<    hL . hState1
< = {-~  definition of |hState1|  -}
<    hL . fold genS algS
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hL . genS) algS' {-" \text{with } "-} hL . algS = algS' . fmap hL

For the left hand side, we can also expand the definition of |local2global| and use the fold fusion law:
<    hGlobal . local2global
< = {-~  definition of |local2global|  -}
<    hGlobal . fold Var alg
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hGlobal . Var) alg' {-" \text{with } "-} hGlobal . alg = alg' . fmap hGlobal

The algebras |alg'| and |algS'| will be constructed later.

Therefore, we can use the universal property of fold to show that |hLocal = fold (hL . genS) algS'| and |hGlobal . local2global = fold (hGlobal . Var) alg'| are equal.
To do this, we have to prove that
\begin{enumerate}
    \item |hL . genS = hGlobal . Var|
    \item |algS' = alg'|
\end{enumerate}
The first item is simple to prove with equational reasoning.
We want to prove that |hL . genS = hGlobal . Var| for all inputs |x :: a|.

<    (hL . genS) x
< = {-~  definition of |genS|  -}
<    hL (\ s -> Var (x, s))
< = {-~  definition of |hL|  -}
<    fmap (fmap (fmap fst) . hND) (\ s -> Var (x, s))
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition})  -}
<    (fmap (fmap (fmap fst)) . fmap hND) (\ s -> Var (x, s))
< = {-~  application of |fmap hND|  -}
<    fmap (fmap (fmap fst)) (\ s -> hND (Var (x, s)))
< = {-~  evaluation of |hND|  -}
<    fmap (fmap (fmap fst)) (\ s -> Var [(x, s)])
< = {-~  evaluation of |fmap (fmap (fmap fst))|  -}
<    \ s -> Var [x]
< = {-~  property of |fmap| and |fst|  -}
<    fmap (fmap fst) (\ s -> Var ([x], s))
< = {-~  property of |hState1|  -}
<    (fmap (fmap fst) . hState1) (Var [x])
< = {-~  property of |hND|  -}
<    (fmap (fmap fst) . hState1 . hND) (Var x)
< = {-~  definition of |hGlobal|  -}
<    hGlobal (Var x)
< = {-~  reformulation  -}
<    (hGlobal . Var) x

So we have |hL . genS = hGlobal . Var|.

For the second item, instead of constructing |alg'| and |algS'| individually, we only construct |alg'| and then verify that the following two equations hold: 

\begin{enumerate}
    \item |hL . algS = alg' . fmap hL|
    \item |hGlobal . alg = alg' . fmap hGlobal|
\end{enumerate}

The |alg'| is defined as follows:
\begin{code}
alg' :: Functor f => (StateF s :+: (NondetF :+: f)) (s -> Free f [a]) -> s -> Free f [a]
alg' (Inl (Get k))         = \ s -> k s s
alg' (Inl (Put s k))       = \ _ -> k s
alg' (Inr (Inl Fail))      = \ s -> Var []
alg' (Inr (Inl (Or p q)))  = \ s -> (++) <$> p s <*> q s
alg' (Inr (Inr y))         = \ s -> Op (fmap ($s) y)
\end{code}
The two equations (1) and (2) are proved in Lemma \ref{eq:fusion-cond-1} and Lemma \ref{eq:fusion-cond-2} respectively.
Thus, we have our original equation |hLocal = fold (hL . genS) alg' = fold (hGlobal . Var) alg' = hGlobal . local2global| holds.
\end{proof}

\begin{lemma}[Fusion Condition 1] \label{eq:fusion-cond-1}
|hL . algS = alg' . fmap hL|
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
< = {-~  definition of |algS|  -}
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
< = {-~  definition of |algS|  -}
<    (hL . algS) (Inl (Put s k))

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

<    (alg' . fmap hL) (Inr (Inl Fail))
< = {-~  definition of |fmap|  -}
<    alg' (Inr (Inl Fail))
< = {-~  definition of |alg'|  -}
<    \ s -> Var []
< = {-~  definition of |fmap|  -}
<    \ s -> fmap (fmap fst) (Var [])
< = {-~  definition of |hND|  -}
<    \ s -> (fmap (fmap fst) . hND) (Op (Inl Fail))
< = {-~  definition of |hL'|  -}
<    \ s -> hL' (Op (Inl Fail))
< = {-~  definition of |fmap|  -}
<    (fmap hL') (\ s -> Op (Inl Fail))
< = {-~  definition of |hL|  -}
<    hL (\ s -> Op (Inl Fail))
< = {-~  definition of |fmap|  -}
<    hL (\ s -> Op (fmap (\ k -> k s) (Inl Fail)))
< = {-~  definition of |algS|  -}
<    (hL . algS) (Inr (Inl Fail))

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}
% p, q :: s -> Free (NondetF :+: f) (a, s)

For the left-hand side, we have:
<    (hL . algS) (Inr (Inl (Or p q)))
< = {-~  definition of |algS|  -}
<    hL (\ s -> Op (fmap (\ k -> k s) (Inl (Or p q))))
< = {-~  evaluation of |fmap (\ k -> k s)|  -}
<    hL (\ s -> Op (Inl (Or (p s) (q s))))
< = {-~  definition of |hL|  -}
<    (fmap hL') (\ s -> Op (Inl (Or (p s) (q s))))
< = {-~  evaluation of |fmap hL'|  -}
<    \ s -> hL' (Op (Inl (Or (p s) (q s))))
< = {-~  |hL' = fold (fmap (fmap fst) . genND) algL'| (Lemma \ref{eq:hl-fusion})  -}
<    \ s -> (fold (fmap (fmap fst) . genND) algL') (Op (Inl (Or (p s) (q s))))
< = {-~  evaluation of |fold|  -}
<    \ s -> liftA2 (++)  ((fold (fmap (fmap fst) . genND) algL') (p s))
<                        ((fold (fmap (fmap fst) . genND) algL') (q s))
< = {-~  |hL' = fold (fmap (fmap fst) . genND) algL'| (Lemma \ref{eq:hl-fusion})  -}
<    \ s -> liftA2 (++) (hL' (p s)) (hL' (q s))

For the right-hand side, we have:
<    (alg' . fmap hL) (Inr (Inl (Or p q)))
< = {-~  evaluation of |fmap hL|  -}
<    alg' (Inr (Inl (Or (hL p) (hL q))))
< = {-~  definition of |alg'|  -}
<    \ s -> liftA2 (++) (hL p s) (hL q s)
< = {-~  reformulation  -}
<    \ s -> liftA2 (++) (hL (\ s' -> p s') s) (hL (\ s' -> q s') s)
< = {-~  definition of |hL|  -}
<    \ s -> liftA2 (++) ((fmap hL') (\ s' -> p s') s) ((fmap hL') (\ s' -> q s') s)
< = {-~  definition of |fmap|  -}
<    \ s -> liftA2 (++) ((\ s' -> hL' (p s')) s) ((\ s' -> hL' (q s')) s)
< = {-~  function application  -}
<    \ s -> liftA2 (++) (hL' (p s)) (hL' (q s))

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}
% y :: f (s -> Free (NondetF :+: f) (a, s))

For the left-hand side, we have:
<    (hL . algS) (Inr (Inr y))
< = {-~  definition of |algS|  -}
<    hL (\ s -> Op (fmap (\ k -> k s) (Inr y)))
< = {-~  definition of |hL|  -}
<    (fmap hL') (\ s -> Op (fmap (\ k -> k s) (Inr y)))
< = {-~  definition of |fmap|  -}
<    \ s -> hL' (Op (fmap (\ k -> k s) (Inr y)))
< = {-~  property of |fmap|  -}
<    \ s -> hL' (Op (Inr (fmap (\ k -> k s) y)))
< = {-~  |hL' = fold (fmap (fmap fst) . genND) algL'| (Lemma \ref{eq:hl-fusion})  -}
<    \ s -> fold (fmap (fmap fst) . genND) algL' (Op (Inr (fmap (\ k -> k s) y)))
< = {-~  evaluation of |fold|  -}
<    \ s -> algL' ((fmap hL' . fmap (\ k -> k s)) y)
< = {-~  definition of |algL'|  -}
<    \ s -> Op ((fmap hL' . fmap (\ k -> k s)) y)
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition})  -}
<    \ s -> Op (fmap (hL' . (\ k -> k s)) y)

For the right-hand side, we have:
<    (alg' . fmap hL) (Inr (Inr y))
< = {-~  evaluation of |fmap hL|  -}
<    alg' (Inr (Inr (fmap hL y)))
< = {-~  definition of |alg'|  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap hL y))
< = {-~  functor law: composition of |fmap| \ref{eq:functor-composition}  -}
<    \ s -> Op (fmap ((\ k -> k s) . hL) y)
< = {-~  definition of |hL|  -}
<    \ s -> Op (fmap ((\ k -> k s) . (fmap hL')) y)
< = {-~  Lemma \ref{eq:dollar-fmap-comm} with |f = hL'| -}
<    \ s -> Op (fmap (hL' . (\ k -> k s)) y)

\end{proof}

\begin{lemma}\label{eq:dollar-fmap-comm}~
< (\ k -> k s) . fmap f = f . (\ k -> k s)
with function |f :: a -> b| and input |t :: s -> a|.
% holds for any function |f :: a -> b| and input |t :: s -> a| in the above proof.
\end{lemma}
\begin{proof} ~
<    ((\ k -> k s) . fmap f) t
< = {-~  definition of |fmap|  -}
<    (\ k -> k s) (f . t)
< = {-~  function application  -}
<    (f . t) s
< = {-~  reformulation  -}
<    f (t s)
< = {-~  reformulation  -}
<    (f . (\ k -> k s)) t
\end{proof}

\begin{lemma} \label{eq:liftA2-fst-comm}~
< fmap (fmap fst) (liftA2 (++) p q) = liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{lemma}
\begin{proof}~

<    fmap (fmap fst) (liftA2 (++) p q)
< = {-~  definition of |liftA2| -}
<    fmap (fmap fst) (do {x <- p; y <- q; return (x ++ y)})
< = {-~  property of |monad|: |fmap f (m >>= k) = m >>= fmap f . k| -}
<    do {x <- p; y <- q; fmap (fmap fst) (return (x ++ y))}
< = {-~  definition of |fmap| -}
<    do {x <- p; y <- q; return ((fmap fst x) ++ (fmap fst y))}
< = {-~  reformulation -}
<    do {x <- fmap (fmap fst) p; y <- fmap (fmap fst) q; return (x ++ y)}
< = {-~  definition of |liftA2| -}
<    liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
\end{proof}

\begin{lemma}[Fusion of |hL'|]\label{eq:hl-fusion}~

< hL' = fold (fmap (fmap fst) . genND) algL'
where |algL'| is defined as follows:
<     algL' :: Functor f => (NondetF :+: f) (Free f [a]) -> Free f [a]
<     algL' (Inl Fail) = Var []
<     algL' (Inl (Or p q)) = liftA2 (++) p q
<     algL' (Inr y) = Op y
\end{lemma}

\begin{proof} ~
<    hL'
< = {-~  definition of |hL'|  -}
<    fmap (fmap fst) . hND
< = {-~  definition of |hND|  -}
<    fmap (fmap fst) . fold genND algND
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (fmap (fmap fst) genND) algL'

So we only need to prove that the equation |fmap (fmap fst) . algND = algL' . fmap (fmap (fmap fst))| holds for all inputs |t :: (NondetF :+: f) (Free f [(a, s)])|.
We do this by a case analysis on |t|.

\noindent \mbox{\underline{case |t = Inl Fail|}}
<    (fmap (fmap fst) . algND) (Inl Fail)
< = {-~  definition of |algND|  -}
<    fmap (fmap fst) (Var [])
< = {-~  definition of |fmap|  -}
<    Var []
< = {-~  definition of |algL'|  -}
<    algL' (Inl Fail)
< = {-~  definition of |fmap|  -}
<    (algL' . fmap (fmap (fmap fst))) (Inl Fail)

\noindent \mbox{\underline{case |t = Inl (Or p q)|}}
<    (fmap (fmap fst) . algND) (Inl (Or p q))
< = {-~  definition of |algND|  -}
<    fmap (fmap fst) (liftA2 (++) p q)
< = {-~  Lemma \ref{eq:liftA2-fst-comm}  -}
<    liftA2 (++) (fmap (fmap fst) p) (fmap (fmap fst) q)
< = {-~  definition of |algL'|  -}
<    algL' (Inl (Or (fmap (fmap fst) p) (fmap (fmap fst) q)))
< = {-~  definition of |fmap|  -}
<    (algL' . fmap (fmap (fmap fst))) (Inl (Or p q))

\noindent \mbox{\underline{case |t = Inr y|}}
<    (fmap (fmap fst) . algND) (Inr y)
< = {-~  definition of |algND|  -}
<    fmap (fmap fst) (Op y)
< = {-~  definition of |fmap|  -}
<    Op ((fmap (fmap (fmap fst)) y))
< = {-~  definition of |algL'|  -}
<    algL' (Inr (fmap (fmap (fmap fst)) y))
< = {-~  definition of |fmap|  -}
<    (algL' . fmap (fmap (fmap fst))) (Inr y)

\end{proof}

\begin{lemma}[Fusion Condition 2] \label{eq:fusion-cond-2}
|hGlobal . alg = alg' . fmap hGlobal|
\footnote{Note that the |alg| here refers to the |alg| in the definition of |local2global|.}
\end{lemma}
\begin{proof}
We prove this equation in a similar way to Lemma \ref{eq:fusion-cond-1}.
We need to prove it holds for all inputs |t :: (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))|.
In the following proofs, we assume implicit commutativity and associativity of the coproduct operator |(:+:)| as we have mentioned in Section \ref{sec:local2globalforming-between-local-and-global-state}.
All local2global formations relevant to commutativity and associativity are implicit and not shown in the following proofs.

\noindent \mbox{\underline{case |t = Inl (Get k)|}}

For the left-hand side, we have:
<    (hGlobal . alg) (Inl (Get k))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inl (Get k)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hND) (Op (Inl (Get k)))
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState1) (Op (Inl (Get (hND . k))))
< = {-~  evaluation of |hState1|  -}
<    fmap (fmap fst) (algS (Inl (Get (hState1 . hND . k))))
< = {-~  evaluation of |algS|  -}
<    fmap (fmap fst) (\ s -> (hState1 . hND . k) s s)
< = {-~  function application  -}
<    fmap (fmap fst) (\ s -> (hState1 . hND) (k s) s)
< = {-~  definition of |fmap|  -}
<    \ s -> fmap fst ((hState1 . hND) (k s) s)
< = {-~  reformulation  -}
<    \ s -> (fmap fst . (hState1 . hND) (k s)) s
< = {-~  definition of |fmap|  -}
<    \ s -> (fmap (fmap fst) ((hState1 . hND) (k s))) s
< = {-~  reformulation  -}
<    \ s -> (fmap (fmap fst) . hState1 . hND) (k s) s
< = {-~  definition of |hGlobal|  -}
<    \ s -> hGlobal (k s) s

For the right-hand side, we have:
<    (alg' . fmap hGlobal) (Inl (Get k))
< = {-~  definition of |fmap|  -}
<    alg' (Inl (Get (hGlobal . k)))
< = {-~  definition of |alg'|  -}
<    \ s -> hGlobal (k s) s

\noindent \mbox{\underline{case |t = Inl (Put s k)|}}

For simplicity, we assume the smart constructors |getOp, putOp, orOp, failOp| will automatically insert correct |Op, Inl, Inr| constructors based on the context to make the term well-typed in the following proof.
In this way, we can avoid the tedious details of dealing with these constructors manually.

For the left-hand side, we have:
<    (hGlobal . alg) (Inl (Put s k))
< = {-~  definition of |alg|  -}
<    hGlobal (putROp s k)
< = {-~  definition of |putROp|  -}
<    hGlobal (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hND) (getOp (\ s' -> orOp (putOp s k) (putOp s' failOp)))
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState1) (getOp (\ s' -> liftA2 (++) (putOp s (hND k)) (putOp s' (Var []))))
< = {-~  evaluation of |hState1|  -}
<    fmap (fmap fst) (\ s' -> (hState1 . (\ s' -> liftA2 (++) (putOp s (hND k)) (putOp s' (Var [])))) s' s')
< = {-~  function application  -}
<    fmap (fmap fst) (\ s' -> hState1 (liftA2 (++) (putOp s (hND k)) (putOp s' (Var []))) s')
< = {-~  definition of |fmap|  -}
<    \ s' -> fmap fst (hState1 (liftA2 (++) (putOp s (hND k)) (putOp s' (Var []))) s')
< = {-~  definition of |liftA2|  -}
<    \ s' -> fmap fst (hState1 (do {x <- putOp s (hND k); y <- putOp s' (Var []); return (x++y)}) s')
< = {-~  |y = []| (property of free monad)  -}
<    \ s' -> fmap fst (hState1 (do {x <- putOp s (hND k); putOp s' (Var []); return x}) s')
< = {-~  property of do-notation  -}
<    \ s' -> fmap fst (hState1 (putOp s (hND k) >>= \ x -> putOp s' (Var []) >> return x) s')
< = {-~  definition of |(>>=)|, let |f = (>>= \ x -> putOp s' (Var []) >> return x)|  -}
<    \ s' -> fmap fst (hState1 (putOp s (f (hND k))) s')
< = {-~  evaluation of |hState1|  -}
<    \ s' -> fmap fst ((\ _ -> hState1 (f (hND k)) s) s')
< = {-~  function application  -}
<    \ s' -> fmap fst (hState1 (f (hND k)) s)
< = {-~  reformulation, definition of |fmap|  -}
<    \ s' -> (fmap (fmap fst) . hState1 . f . hND) k s
< = {-~  because we drop the state in the end using |fmap (fmap fst)|, |f| won't make any changes  -}
<    \ s' -> (fmap (fmap fst) . hState1 . hND) k s
< = {-~  definition of |hGlobal|, replace |s'| with |_|  -}
<    \ _ -> hGlobal k s

For the right-hand side, we have:
<    (alg' . fmap hGlobal) (Inl (Put s k))
< = {-~  definition of |fmap|  -}
<    alg' (Inl (Put s (hGlobal k)))
< = {-~  definition of |alg'|  -}
<    \ _ -> hGlobal k s

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

For the left-hand side, we have:
<    (hGlobal . alg) (Inr (Inl Fail))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inl Fail)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hND) (Op (Inr (Inl Fail)))
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState1) (Var [])
< = {-~  evaluation of |hState1|  -}
<    fmap (fmap fst) (\ s -> Var ([], s))
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> Var []

For the right-hand side, we have:
<    (alg' . fmap hGlobal) (Inr (Inl Fail))
< = {-~  definition of |fmap|  -}
<    alg' (Inr (Inl Fail))
< = {-~  definition of |alg'|  -}
<    \ s -> Var []

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}

For the left-hand side, we have:
<    (hGlobal . alg) (Inr (Inl (Or p q)))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inl (Or p q))))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hND) (Op (Inr (Inl (Or p q))))
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState1) (algND (Inl (Or (hND p) (hND q))))
< = {-~  evaluation of |algND|  -}
<    (fmap (fmap fst) . hState1) (liftA2 (++) (hND p) (hND q))
< = {-~  definition of |liftA2|  -}
<    (fmap (fmap fst) . hState1) (do {x <- hND p; y <- hND q; return (x ++ y)})
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    hState' (do {x <- hND p; y <- hND q; return (x ++ y)})
% < = {-~  property of handlers \wenhao{add more?}\birthe{Say something like: propagate fold to the subtrees?} -}
< = {-~  property of fold: propagate fold to subtrees of free monad -}
<    \ s -> do {x <- hState' (hND p) s; y <- hState' (hND q) s; return (x ++ y)})
< = {-~  definition of |hState'|  -}
<    \ s -> do  x <- (fmap (fmap fst) . hState1) (hND p) s;
<               y <- (fmap (fmap fst) . hState1) (hND q) s;
<               return (x ++ y)}

For the right-hand side, we have:
<    (alg' . fmap hGlobal) (Inr (Inl (Or p q)))
< = {-~  definition of |fmap|  -}
<    alg' (Inr (Inl Or (hGlobal p) (hGlobal q)))
< = {-~  definition of |alg'|  -}
<    \ s -> liftA2 (++) (hGlobal p s) (hGlobal q s)
< = {-~  definition of |hGlobal|  -}
<    \ s -> liftA2 (++) ((fmap (fmap fst) . hState1 . hND) p s) ((fmap (fmap fst) . hState1 . hND) q s)
< = {-~  definition of |liftA2|  -}
<    \ s -> do  x <- (fmap (fmap fst) . hState1 . hND) p s;
<               y <- (fmap (fmap fst) . hState1 . hND) q s;
<               return (x ++ y)
< = {-~  reformulation  -}
<    \ s -> do  x <- fmap fst (hState1 (hND p) s);
<               y <- fmap fst (hState1 (hND p) s);
<               return (x ++ y)
% < = {-~  property of |monad|  -}
% <    \ s -> do  x <- hState1 (hND p) s;
% <               y <- hState1 (hND q) s;
% <               return (fst x ++ fst y)
% < = {-~  definition of |liftA2|  -}
% <    \ s -> liftA2 (\ x y -> fst x ++ fst y) (hState1 (hND p) s) (hState1 (hND q) s)

In the above proof, we fuse |fmap (fmap fst) . hState1| into a single handler |hState'| by dropping the second component of the result (the state).
\begin{code}
hState' :: Functor f => Free (StateF s :+: f) a -> (s -> Free f a)
hState'  =  fold (\ x s -> return x) algS
  where
    algS (Inl (Get k))    s  = k s s
    algS (Inl (Put s k))  _  = k s
    algS (Inr y)          s  = Op (fmap ($s) y)
\end{code}

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}

For the left-hand side, we have:
<    (hGlobal . alg) (Inr (Inr y))
< = {-~  definition of |alg|  -}
<    hGlobal (Op (Inr (Inr y)))
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState1 . hND) (Op (Inr (Inr y)))
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState1) (Op (Inr (fmap hND y)))
< = {-~  evaluation of |hState1|  -}
<    fmap (fmap fst) (\ s -> Op (fmap ((\ k -> k s) . hState1 . hND) y))
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> fmap fst (Op (fmap ((\ k -> k s) . hState1 . hND) y))
< = {-~  evaluation of |fmap fst|  -}
<    \ s -> Op (fmap (fmap fst . (\ k -> k s) . hState1 . hND) y)
< = {-~  Lemma \ref{eq:dollar-fmap-comm} with |f = fst|  -}
<    \ s -> Op (fmap ((\ k -> k s) . fmap (fmap fst) . hState1 . hND) y)
< = {-~  definition of |hGlobal|  -}
<    \ s -> Op (fmap ((\ k -> k s) . hGlobal) y)

For the right-hand side, we have:
<    (alg' . fmap hGlobal) (Inr (Inr y))
< = {-~  definition of |fmap|  -}
<    alg' (Inr (Inr (fmap hGlobal y)))
< = {-~  definition of |alg'|  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap hGlobal y))
< = {-~  reformulation  -}
<    \ s -> Op (fmap ((\ k -> k s) . hGlobal) y)

\end{proof}