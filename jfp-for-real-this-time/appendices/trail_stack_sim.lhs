\section{Simulating Local State with Trail Stack: The Proofs}
\label{app:trail-stack}

%-------------------------------------------------------------------------------

This section shows that |fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . local2trail| is equivalent to |hLocal|.
% \ref{sec:trail-stack}.

\begin{theorem}\label{eq:local-global}
|fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . local2trail = hLocal|
\end{theorem}
\begin{proof}
We start with applying fold fusion to both sides of the equation.
Similar to Appendix \ref{app:local-global}, we rewrite |hLocal| as |hL . hState1|.
We can expand the definition of |hState1| and use the fold fusion law for postcomposition as defined in Equation \ref{eq:fusion-post}:
<    hL . hState1
< = {-~  definition of |hState1|  -}
<    hL . fold genS algS
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (hL . genS) algS' {-" \text{with } "-} hL . algS = algS' . fmap hL

For the left hand side, we define |h1 = fmap (\ x -> fmap fst (runhStack () x)) . hGlobal|.
We can also expand the definition of |local2trail| and use the fold fusion law.
<    h1 . local2trail
< = {-~  definition of |local2trail|  -}
<    h1 . fold Var (alg1 # alg2 # fwd)
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post})  -}
<    fold (h1 . Var) alg' {-" \text{with } "-} h1 . (alg1 # alg2 # fwd) = alg' . fmap h1

The algebras |alg'| and |algS'| will be constructed later.

Therefore, we can use the universal property of fold to show that |hLocal = fold (hL . genS) algS'| and |h1 . local2trail = fold (h1 . Var) alg'| are equal.
To do this, we have to prove that
\begin{enumerate}
    \item |hL . genS = h1 . Var|
    \item |algS' = alg'|
\end{enumerate}
The first item is simple to prove with equational reasoning.
% We want to prove that |hL . genS = h1 . Var| for all inputs |x :: a|.
In Theorem \ref{eq:local-global}, we already proved that |hL . genS = hGlobal . Var|.
Thus, we only need to prove |h1 . Var = hGlobal . Var| for all inputs |x :: a|.

<    (h1 . Var) x
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal . Var) x
< = {-~  function application  -}
<    fmap (\ x -> fmap fst (runhStack () x)) $ hGlobal (Var x)
< = {-~  definition of |hGlobal|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) $ (fmap (fmap fst) . hState1 . hNDf) (Var x)
< = {-~  definition of |hNDf|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) $ (fmap (fmap fst) . hState1) (Var [x])
< = {-~  definition of |hState1|, function application  -}
<    fmap (\ x -> fmap fst (runhStack () x)) $ (\ s -> Var [x])
< = {-~  definition of |fmap|, function application  -}
<    (\ s -> fmap fst (runhStack () $ Var ([x], s)))
< = {-~  definition of |runhStack|  -}
<    (\ s -> fmap fst (runSTT $ liftST (emptyStack ()) >>= hStack (Var ([x], s))))
< = {-~  definition of |hStack|  -} % omit expansion
<    (\ s -> fmap fst (Var ([x], ())))
< = {-~  definition of |fmap|  -}
<    (\ s -> Var [x])
< = {-~  definition of |hGlobal|  -}
<    hGlobal (Var x)
< = {-~  reformulation  -} 
<    (hGlobal . Var) x

So we have |hL . genS = hGlobal . Var = h1 . Var|.

For the second item, instead of constructing |alg'| and |algS'| individually, we only construct |alg'| and then verify that the following two equations hold: 

\begin{enumerate}
    \item |hL . algS = alg' . fmap hL|
    \item |h1 . (alg1 # alg2 # fwd) = alg' . fmap h1|
\end{enumerate}

The |alg'| is defined as follows, which is the same as the |alg'| defined in Appendix \ref{app:local-global}.
\begin{spec}
alg' :: Functor f => (StateF s :+: NondetF :+: f) (s -> Free f [a]) -> (s -> Free f [a])
alg' = alg1' # alg2' # fwd'
  where
    alg1' (Get k)    = \ s -> k s s
    alg1' (Put s k)  = \ _ -> k s
    alg2' Fail       = \ s -> Var []
    alg2' (Or p q)   = \ s -> liftA2 (++) (p s) (q s)
    fwd' y           = \ s -> Op (fmap ($s) y)
\end{spec}
The equation (1) is already proved in Lemma \ref{eq:fusion-cond-1}.
We only need to prove the equation (2), which is shown in Lemma \ref{eq:fusion-cond-2-trail}.
Thus, we have our original equation |hLocal = fold (hL . genS) alg' = fold (h1 . Var) alg' = h1 . local2trail| holds.
\end{proof}


\begin{lemma}[Fusion Condition 2 of the Simulation with Trail Stack] \label{eq:fusion-cond-2-trail}
|h1 . (alg1 # alg2 # fwd) = (alg1' # alg2' # fwd') . fmap h1|
\end{lemma}

\begin{proof}
We need to prove it holds for all inputs |t :: (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a)|.
In the following proofs, we assume implicit commutativity and associativity of the coproduct operator |(:+:)| as we have mentioned in Section \ref{sec:transforming-between-local-and-global-state}.
All |local2trail| formations relevant to commutativity and associativity are implicit and not shown in the following proofs.

\noindent \mbox{\underline{case |t = Inl (Get k)|}}

<    (h1 . (alg1 # alg2 # fwd)) (Inl (Get k))
< = {-~  definition of |#|  -}
<    (h1 . alg1) (Get k)
< = {-~  definition of |alg1|  -}
<    h1 (Op (Inl (Get k)))
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (Op (Inl (Get k)))
< = {-~  definition of |hGlobal|  -} % proved in local-global
<    fmap (\ x -> fmap fst (runhStack () x)) (\ s -> hGlobal (k s) s)
< = {-~  definition of |fmap|  -}
<    \ s -> fmap fst (runhStack () (hGlobal (k s) s))
< = {-~  definition of |fmap|  -}
<    \ s -> (fmap (\ x -> fmap fst (runhStack () x)) (hGlobal (k s))) s
< = {-~  definition of |(.)|  -}
<    \ s -> (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (k s) s
< = {-~  definition of |h1|  -}
<    \ s -> h1 (k s) s
< = {-~  definition of |alg1'|  -}
<    alg1' (Get (h1 . k))
< = {-~  definition of |#|  -}
<    (alg1' # alg2' # fwd') (Inl (Get (h1 . k)))
< = {-~  definition of |fmap|  -}
<    ((alg1' # alg2' # fwd') . fmap h1) (Inl (Get k))

\noindent \mbox{\underline{case |t = Inr (Inl Fail)|}}

<    (h1 . (alg1 # alg2 # fwd)) (Inr (Inl Fail))
< = {-~  definition of |#| and |alg1|  -}
<    h1 (Op (Inr (Inl Fail)))
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (Op (Inr (Inl Fail)))
< = {-~  definition of |hGlobal|  -} % proved in local-global
<    (fmap (\ x -> fmap fst (runhStack () x))) (\ s -> Var [])
< = {-~  definition of |fmap|  -}
<    s -> fmap fst (runhStack () (Var []))
< = {-~  definition of |runhStack|  -} % omit some steps
<    s -> Var []
< = {-~  definition of |alg2'|  -}
<    alg2' Fail
< = {-~  definition of |fmap| and |#|  -}
<    ((alg1' # alg2' # fwd') . fmap h1) (Inr (Inl Fail))

\noindent \mbox{\underline{case |t = Inr (Inr y)|}}

For the left-hand side, we have:
<    (h1 . (alg1 # alg2 # fwd)) (Inr (Inr y))
< = {-~  definition of |#| and |fwd|  -}
<    h1 (Op (Inr (Inr (Inr y))))
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (Op (Inr (Inr (Inr y))))
< = {-~  definition of |hGlobal|  -} % proved in local-global
<    fmap (\ x -> fmap fst (runhStack () x)) (\ s -> Op (fmap ((\ k -> k s) . hGlobal) (Inr y)))
< = {-~  definition of |fmap|  -}
<    \ s -> fmap fst (runhStack () (Op (fmap ((\ k -> k s) . hGlobal) (Inr y))))
< = {-~  definition of |runhStack|  -}
<    \ s -> fmap fst (runSTT $ liftST (emptyStack ()) >>= 
<      hStack (Op (fmap ((\ k -> k s) . hGlobal) (Inr y))))
< = {-~  definition of |hStack|  -}
<    \ s -> fmap fst (runSTT $ liftST (emptyStack ()) >>= 
<      \ stack -> STT $ \s -> Op (fmap ((\f -> unSTT (f stack) s) . hStack) (fmap ((\ k -> k s) . hGlobal) (Inr y)))
< = {-~  |fmap| fusion  -}
<    \ s -> fmap fst (runSTT $ liftST (emptyStack ()) >>= 
<      \ stack -> STT $ \s -> Op (fmap ((\f -> unSTT (f stack) s) . hStack . (\ k -> k s) . hGlobal) (Inr y)))
< = {-~  \todo{not finished}  -}
<    \ s -> Op (fmap ((\ x -> fmap fst (runhStack () x)) . (\ k -> k s) . hGlobal) y)
< = {-~  Lemma \ref{eq:dollar-fmap-comm} with |f = (\ x -> fmap fst (runhStack () x))|  -}
<    \ s -> Op (fmap ((\ k -> k s) . fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) y)
< = {-~  definition of |runhStack|  -}
<    \ s -> Op (fmap ((\ k -> k s) . fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) y)
< = {-~  definition of |h1|  -}
<    \ s -> Op (fmap ((\ k -> k s) . h1) y)
< = {-~  |fmap| fusion  -}
<    \ s -> Op (fmap (\ k -> k s) (fmap h1 y))
< = {-~  definition of |#| and |fwd'|  -}
<    (alg1' # alg2' # fwd') (Inr (Inr (fmap h1 y)))
< = {-~  definition of |fmap|  -}
<    ((alg1' # alg2' # fwd') . fmap h1) (Inr (Inr y))

\noindent \mbox{\underline{case |t = Inl (Put s k)|}}

<    (h1 . (alg1 # alg2 # fwd)) (Inl (Put s k))
< = {-~  definition of |#|  -}
<    (h1 . alg1) (Put s k)
< = {-~  definition of |alg1|  -}
<    h1 (do t <- get; push (Left t); put s; k)
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (do t <- get; push (Left t); put s; k) 
< = {-~  definition of |hGlobal|  -} % omit some steps
<    fmap (\ x -> fmap fst (runhStack () x)) (\ t -> do push (Left t); hGlobal k s)
< = {-~  definition of |fmap|  -}
<    \ t -> fmap fst (runhStack () (do push (Left t); hGlobal k s))
< = {-~  (|push| does not make any influence)  -}
<    \ _ -> fmap fst (runhStack () (hGlobal k s))
< = {-~  definition of |fmap|  -}
<    \ _ -> (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) k s
< = {-~  definition of |h1|  -}
<    \ _ -> h1 k s
< = {-~  definition of |alg1'|  -}
<    alg1' (Put s (h1 k))
< = {-~  definition of |#|  -}
<    (alg1' # alg2' # fwd') (Inl (Put s (h1 k)))
< = {-~  definition of |fmap|  -}
<    ((alg1' # alg2' # fwd') . fmap h1) (Inl (Put s k))

\noindent \mbox{\underline{case |t = Inr (Inl (Or p q))|}}

<    (h1 . (alg1 # alg2 # fwd)) (Inr (Inl (Or p q)))
< = {-~  definition of |#|  -}
<    (h1 . alg2) (Or p q)
< = {-~  definition of |alg2|, define |or x y = Op . Inr . Inl $ Or x y|  -}
<    h1 (or (do push (Right ()); p) (do undoTrail; q))
< = {-~  definition of |h1|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) (or (do push (Right ()); p) (do undoTrail; q))
< = {-~  definition of |hGlobal|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . (fmap (fmap fst) . hState1 . hNDf))
<      (or (do push (Right ()); p) (do undoTrail; q))
< = {-~  definition of |hNDf|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1)
<      (liftA2 (++) (do push (Right ()); hNDf p) (do undoTrail; hNDf q))
< = {-~  definition of |liftA2|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1)
<      (do x <- (do push (Right ()); hNDf p); y <- (do undoTrail; hNDf q); return (x ++ y))
< = {-~  definition of |do|  -}
<    (fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1)
<      (do push (Right ()); x <- hNDf p; undoTrail; y <- hNDf q; return (x ++ y))
< = {-~  move |fmap (fmap fst)| to the first (parametricity), define |h2 = fmap (\ x -> fmap fst (runhStack () x)) . hState1|  -} % a lemma needed?
<    (fmap (fmap fst) . h2) (do push (Right ()); x <- hNDf p; undoTrail; y <- hNDf q; return (x ++ y))
< = {-~  evaluation of |h2|  -} % omit many steps
% NOTE: 这一步错误，至少应该把 |h2| 里创建stack的东西拿出来，然后加上一个传递stack。有点麻烦呜呜呜。
<    fmap (fmap fst) $ \s -> do  (_, s1) <- h2 (push (Right ())) s;
<                                (x, s2) <- h2 (hNDf p) s1;
<                                (_, s3) <- h2 undoTrail s2;
<                                (y, s4) <- h2 (hNDf q) s3;
<                                return (x ++ y, s4)
< = {-~  \todo{induction: |s == s1 == s3|; |p,q| is in the range of |local2global|; need a new lemma}  -}
% NOTE: 这里需要进一步说明，首先是归纳证明p中第一个or之下的部分不会影响，然后再证明undoTrail会把p中第一个or之上的部分都抵消掉
<    fmap (fmap fst) $ \s -> do  (_, s) <- h2 (push (Right ())) s;
<                                (x, s2) <- h2 (hNDf p) s;
<                                (_, s) <- h2 undoTrail s2;
<                                (y, s4) <- h2 (hNDf q) s;
<                                return (x ++ y, s4)
< = {-~  definition of |fmap|  -}
<    \s -> do  (_, s) <- h2 (push (Right ())) s;
<              (x, s2) <- h2 (hNDf p) s;
<              (_, s) <- h2 undoTrail s2;
<              (y, s4) <- h2 (hNDf q) s;
<              return (x ++ y)
< = {-~  |push (Right ()), undoTrail| does not make any difference   -}
<    \s -> do  (x, _) <- h2 (hNDf p) s;
<              (y, _) <- h2 (hNDf q) s;
<              return (x ++ y)
< = {-~  definition of |h2| and |hGlobal|  -}
<    \ s -> do  x <- fmap fst (runhStack () (hGlobal p s));
<               y <- fmap fst (runhStack () (hGlobal q s)); return (x ++ y)
< = {-~  definition of |fmap|  -}
<    \ s -> do  x <- (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) p s;
<               y <- (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) q s; return (x ++ y)
< = {-~  definition of |h1|  -}
<    \ s -> do x <- h1 p s; y <- h1 q s; return (x ++ y)
< = {-~  definition of |liftA2|  -}
<    \ s -> liftA2 (++) (h1 p s) (h1 q s)
< = {-~  definition of |alg2'|  -}
<    alg2' (Or (h1 p) (h1 q))
< = {-~  definition of |#|  -}
<    (alg1' # alg2' # fwd') (Inr (Inl (Or (h1 p) (h1 q))))
< = {-~  definition of |fmap|  -}
<    ((alg1' # alg2' # fwd') . fmap h1) (Inr (Inl (Or p q)))

\end{proof}