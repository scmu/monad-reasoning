\section{Simulating Local State with Global State: The Proofs}
\label{app:local-global}

%-------------------------------------------------------------------------------

This section shows that the function |hGlobal . trans| is equivalent to |hLocal|, where |hGlobal|, |trans| and |hLocal| are defined in Section \ref{sec:transforming-between-local-and-global-state}.

% \begin{code}
% trans :: Functor f => Prog s f a -> Prog s f a
% trans = fold Var alg
%   where 
%     alg (Inl (Put t k)) = putROp t k
%     alg p = Op p

% hGlobal :: Functor f => Prog s f a -> s -> Free f [a]
% hGlobal = fmap (fmap fst) . hState . hNDl

% hLocal :: Functor f => Prog s f a -> s -> Free f [a]
% hLocal = fmap (fmap (fmap fst) . hNDl) . hState

% hState :: Functor f => Free (StateF s :+: f) a -> (s -> Free f (a, s))
% hState  =  fold genS algS 
%   where 
%     genS x                s  = return (s, x)
%     algS (Inl (Get k))    s  = k s s
%     algS (Inl (Put s k))  _  = k s
%     algS (Inr y)          s  = Op (fmap ($s) y)
    
% hNDl :: Functor f => Free (NondetF :+: f) a -> Free f [a]
% hNDl  =  fold genND algND
%   where
%     genND                 = Var . return
%     algND (Inl Fail)      = Var []
%     algND (Inl (Or p q))  = (++) <$> p <*> q
%     algND (Inr y)         = Op y
% \end{code}

\begin{theorem}\label{eq:local-global}
|hGlobal . trans = hLocal|
\end{theorem}
\begin{proof}
We start with applying fold fusion to both two sides.
We rewrite |hLocal| as |hL . hState|, where |hL| is defined as following:
\begin{code}
hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
hL = fmap hL'
  where hL' = fmap (fmap fst) . hNDl
\end{code}
We can expand the definition of |hState| and use the fold fusion law for postcomposition as defined in Equation \ref{eq:fusion-post}:
<    hL . hState
< = {-~  definition of |hState|  -}
<    hL . fold genS algS
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hL . genS) algS' {-" \text{with } "-} hL . algS = algS' . fmap hL

For the left hand side, we can also expand the definition of |trans| and use the fold fusion law:
<    hGlobal . trans
< = {-~  definition of |trans|  -}
<    hGlobal . fold Var alg
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hGlobal . Var) alg' {-" \text{with } "-} hGlobal . alg = alg' . fmap hGlobal

Therefore, we can use the universal property of fold to show that |hLocal = fold (hL . genS) algS'| and |hGlobal . trans = fold (hGlobal . Var) alg'| are equal.
To do this, we have to prove that
\begin{enumerate}
    \item |hL . genS = hGlobal . Var|
    \item |algS' = alg'|
\end{enumerate}
The first item is simple to prove with equational reasoning.
We want to prove that |hL . genS = hGlobal . Var| for all inputs |x :: a|.

For the left-hand side, we have:
<    (hL . genS) x
< = {-~  definition of |genS|  -}
<    hL (\ s -> Var (x, s))
< = {-~  definition of |hL|  -}
<    fmap (fmap (fmap fst) . hND) (\ s -> Var (x, s))
< = {-~  |fmap|-fusion law  -}
<    (fmap (fmap (fmap fst)) . fmap hND) (\ s -> Var (x, s))
< = {-~  application of |fmap hND|  -}
<    fmap (fmap (fmap fst)) (\ s -> hND (Var (x, s)))
< = {-~  evaluation of |hND|  -}
<    fmap (fmap (fmap fst)) (\ s -> Var [(x, s)])
< = {-~  evaluation of |fmap (fmap (fmap fst))|  -}
<    \ s -> Var [x]

And for the right-hand side, we have:
<    (hGlobal . Var) x
< = {-~  reformulation  -}
<    hGlobal (Var x)
< = {-~  definition of |hGlobal|  -}
<    (fmap (fmap fst) . hState . hND) (Var x)
< = {-~  evaluation of |hND|  -}
<    (fmap (fmap fst) . hState) (Var [x])
< = {-~  evaluation of |hState|  -}
<    fmap (fmap fst) (\ s -> Var ([x], s))
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> Var [x]

So we have |hL . genS = hGlobal . Var|.

For the second item, instead of constructing |alg'| and |algS'| individually, we only construct one |alg'| and then verify that the two equations |hL . algS = alg' . fmap hL| and |hGlobal . alg = alg' . fmap hGlobal| hold.
The |alg'| is defined as follows:
\begin{code}
alg' :: Functor f => (StateF s :+: (NondetF :+: f)) (s -> Free f [a]) -> s -> Free f [a]
alg' (Inl (Get k))         = \ s -> k s s
alg' (Inl (Put s k))       = \ _ -> k s
alg' (Inr (Inl Fail))      = \ s -> Var []
alg' (Inr (Inl (Or p q)))  = \ s -> (++) <$> p s <*> q s
alg' (Inr (Inr y))         = \ s -> Op (fmap ($s) y)
\end{code}
And the two equations are proved in Lemma \ref{eq:fusion-cond-1} and Lemma \ref{eq:fusion-cond-2} respectively.
Thus, we have our original equation |hLocal = fold (hL . genS) alg' = fold (hGlobal . Var) alg' = hGlobal . trans| holds.
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
< = {-~  reformulation  -}
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
< = {-~  reformulation  -}
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
< = {-~  definition of |hNDl|  -}
<    \ s -> (fmap (fmap fst) . hNDl) (Op (Inl Fail))
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
< = {-~  |fmap|-fusion law  -}
<    \ s -> Op (fmap (hL' . (\ k -> k s)) y)

For the right-hand side, we have:
<    (alg' . fmap hL) (Inr (Inr y))
< = {-~  evaluation of |fmap hL|  -}
<    alg' (Inr (Inr (fmap hL y)))
< = {-~  definition of |alg'|  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap hL y))
< = {-~  reformulation  -}
<    \ s -> Op ((fmap (\ k -> k s) . (fmap hL)) y)
< = {-~  definition of |hL|  -}
<    \ s -> Op ((fmap (\ k -> k s) . fmap (fmap hL')) y)
< = {-~  |fmap|-fusion law  -}
<    \ s -> Op (fmap ((\ k -> k s) . (fmap hL')) y)
< = {-~  equation |(\ k -> k s) . fmap f = f . (\ k -> k s)| with |f = hL'| -}
<    \ s -> Op (fmap (hL' . (\ k -> k s)) y)

We have used an equation |(\ k -> k s) . fmap f = f . (\ k -> k s)| for any function |f :: a -> b| and input |t :: s -> a| in the above proof.
It is easy to prove it using equational reasoning:
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
<    fmap (fmap fst) . hNDl
< = {-~  definition of |hNDl|  -}
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
< = {-~  property of |liftA2| -}
<    fmap (fmap fst) (do {x <- p; y <- q; return (x ++ y)})
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
\end{lemma}
\begin{proof}
We prove this equation in a similar way to Lemma \ref{eq:fusion-cond-1}.
We need to prove it holds for all inputs |t :: (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))|.

\noindent \mbox{\underline{case |t = Inl (Get k)|}}

\noindent \mbox{\underline{case |t = Inl (Put s k)|}}

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}


\end{proof}