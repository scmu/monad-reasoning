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
<    h1 . fold Var alg
< = {-~  fold fusion-post (Equation \ref{eq:fusion-post-strong})  -}
<    fold (h1 . Var) alg'
<      {-" \text{with } "-} h1 . alg . fmap local2trail = alg' . fmap h1 . fmap local2trail

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
    \item |h1 . alg . fmap local2trail = alg' . fmap h1 . fmap local2trail|
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
|h1 . alg . fmap local2trail = alg' . fmap h1 . fmap local2trail|
\footnote{Note that the |alg| here refers to the |alg| in the definition of |local2trail|.}
\end{lemma}

\begin{proof}
We need to prove |h1 (alg t) = alg' (fmap h1 t)| holds for all inputs |t :: (StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a)| that are in the range of |fmap local2trail|.
In the following proofs, we assume implicit commutativity and associativity of the coproduct operator |(:+:)| as we have mentioned in Section \ref{sec:transforming-between-local-and-global-state}.
% All |local2trail| formations relevant to commutativity and associativity are implicit and not shown in the following proofs.

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
< = {-~  definition of |do|  -}
<    \ s -> fmap fst (runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack (Op (fmap ((\ k -> k s) . hGlobal) (Inr y))) st)
< = {-~  definition of |hStack|  -}
<    \ s -> fmap fst (runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack (Op (fmap ((\ k -> k s) . hGlobal) (Inr y))) st)
< = {-~  definition of |fmap|  -}
<    \ s -> fmap fst . runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack (Op . Inr $ fmap ((\ k -> k s) . hGlobal) y) st
< = {-~  definition of |hStack|, functiona application  -}
<    \ s -> fmap fst . runSTT $
<      do  st <- liftST (emptyStack ())
<          STT $ \ s' -> Op (fmap (\ f -> unSTT (f st) s') (fmap (hStack . (\ k -> k s) . hGlobal) y))
< = {-~  |fmap| fusion  -}
<    \ s -> fmap fst . runSTT $
<      do  st <- liftST (emptyStack ())
<          STT $ \ s' -> Op (fmap ((\ f -> unSTT (f st) s') . hStack . (\ k -> k s) . hGlobal) y)
< = {-~  property of |runSTT|  -} % NOTE: find some literature later ?
<    \ s -> fmap fst $ Op (fmap ((\ f -> runSTT $ 
<      do  st <- liftST (emptyStack ())
<          STT $ \ s' -> unSTT (f st) s') . hStack . (\ k -> k s) . hGlobal) y)
< = {-~  property of |unSTT| and |STT|  -}
<    \ s -> fmap fst $ Op (fmap ((\ f -> runSTT $
<      do  st <- liftST (emptyStack ())
<          f st) . hStack . (\ k -> k s) . hGlobal) y)
< = {-~  definition of |.|  -}
<    \ s -> fmap fst $ Op (fmap ((\ x -> runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack x st) . (\ k -> k s) . hGlobal) y)
< = {-~  definition of |.| and |$|  -}
<    \ s -> fmap fst . Op $ fmap ((\ x -> runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack x st) . (\ k -> k s) . hGlobal) y
< = {-~  definition of |Op| and |fmap fst|  -} % NOTE: more explanation
<    \ s -> Op $ fmap ((\ x -> fmap fst (runSTT $
<      do  st <- liftST (emptyStack ())
<          hStack x st)) . (\ k -> k s) . hGlobal) y
< = {-~  definition of |.| and |$|  -}
<    \ s -> Op (fmap ((\ x -> fmap fst (runSTT $ do  st <- liftST (emptyStack ())
<                                                    hStack x st))
<      . (\ k -> k s) . hGlobal) y)
< = {-~  definition of |do|  -}
<    \ s -> Op (fmap ((\ x -> fmap fst (runSTT $ liftST (emptyStack ()) >>= hStack x))
<      . (\ k -> k s) . hGlobal) y)
< = {-~  definition of |runhStack|  -}
<    \ s -> Op (fmap ((\ x -> fmap fst (runhStack () x)) . (\ k -> k s) . hGlobal) y)
< = {-~  Lemma \ref{eq:dollar-fmap-comm} with |f = (\ x -> fmap fst (runhStack () x))|  -}
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
<    fmap (\ x -> fmap fst (runhStack () x)) . hGlobal $ (or (do push (Right ()); p) (do undoTrail; q))
< = {-~  definition of |hGlobal|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) . (fmap (fmap fst) . hState1 . hNDf) $
<      (or (do push (Right ()); p) (do undoTrail; q))
< = {-~  definition of |hNDf|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1 $
<      (liftA2 (++) (do push (Right ()); hNDf p) (do hNDf undoTrail; hNDf q))
< = {-~  definition of |liftA2|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1 $
<      (do x <- (do push (Right ()); hNDf p); y <- (do hNDf undoTrail; hNDf q); return (x ++ y))
< = {-~  definition of |do|  -}
<    fmap (\ x -> fmap fst (runhStack () x)) . fmap (fmap fst) . hState1 $
<      (do push (Right ()); x <- hNDf p; hNDf undoTrail; y <- hNDf q; return (x ++ y))
< = {-~  move |fmap (fmap fst)| to the left-most position (parametricity)  -}
<    fmap (fmap fst) . fmap (\ x -> fmap fst (runhStack () x)) . hState1 $
<      (do push (Right ()); x <- hNDf p; hNDf undoTrail; y <- hNDf q; return (x ++ y))
< = {-~  evaluation of |hState1|  -} % omit many steps
<    fmap (fmap fst) . fmap (\ x -> fmap fst (runhStack () x)) $
<      \ s -> do  push (Right ());
<                 (x, s1) <- hState1 (hNDf p) s;
<                 (_, s2) <- hState1 (hNDf undoTrail) s1;
<                 (y, s3) <- hState1 (hNDf q) s2;
<                 return (x ++ y, s3)
< = {-~  definition of |fmap| and |runhStack|  -}
<    fmap (fmap fst) $
<      \ s -> fmap fst . runSTT . (\ x -> liftST (emptyStack ()) >>= hStack x) $
<             do  push (Right ());
<                 (x, s1) <- hState1 (hNDf p) s;
<                 (_, s2) <- hState1 (hNDf undoTrail) s1;
<                 (y, s3) <- hState1 (hNDf q) s2;
<                 return (x ++ y, s3)
< = {-~  evaluation of |(\ x -> liftST (emptyStack ()) >>= hStack x)|  -}
< = {-~  NOTE: Because the stack info has type |()|, we omit it in the results of |hStack|.  -}
<    fmap (fmap fst) $ \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            liftST (pushStack (Right ()) st)
<            (x, s1) <- hStack (hState1 (hNDf p) s) st;
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st;
<            (y, s3) <- hStack (hState1 (hNDf q) s2) st;
<            return (x ++ y, s3)
< = {-~  definition of |pushList|  -}
<    fmap (fmap fst) $ \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (x, s1) <- hStack (hState1 (hNDf p) s) st;
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st;
<            (y, s3) <- hStack (hState1 (hNDf q) s2) st;
<            return (x ++ y, s3)
< = {-~  apply Lemma \ref{lemma:stack-state-restore}  -}
<    fmap (fmap fst) $ \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (x, s1) <- hStack (hState1 (hNDf p) s) st;
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st;
<            (y, s3) <- hStack (hState1 (hNDf q) (head ([] ++ [s]))) st';
<            return (x ++ y, s3)
< = {-~  definition of |++|  -}
<    fmap (fmap fst) $ \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (x, s1) <- hStack (hState1 (hNDf p) s) st;
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st;
<            (y, s3) <- hStack (hState1 (hNDf q) s) st';
<            return (x ++ y, s3)
< = {-~  property of ST monad and |copy| (remove useless state operations)  -}
<        do  st <- liftST (emptyStack ())
<            (x, _) <- hStack (hState1 (hNDf p) s) st;
<            st <- liftST (emptyStack ())
<            (y, s3) <- hStack (hState1 (hNDf q) s) st;
<            return (x ++ y, s3)
< = {-~  evaluation of |fmap (fmap fst)|  -}
<    \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            (x, _) <- hStack (hState1 (hNDf p) s) st;
<            st <- liftST (emptyStack ())
<            (y, _) <- hStack (hState1 (hNDf q) s) st;
<            return (x ++ y)
< = {-~  definition of |fmap (fmap fst)|  -}
<    \ s -> fmap fst . runSTT $
<        do  st <- liftST (emptyStack ())
<            x <- hStack (fmap (fmap fst) (hState1 (hNDf p)) s) st;
<            st <- liftST (emptyStack ())
<            y <- hStack (fmap (fmap fst) (hState1 (hNDf q)) s) st;
<            return (x ++ y)
< = {-~  definition of |hGlobal|  -}
<    \ s -> fmap fst . runSTT $ do  st <- liftST (emptyStack ())
<                                   x <- hStack (hGlobal p s) st;
<                                   st <- liftST (emptyStack ())
<                                   y <- hStack (hGlobal q s) st;
<                                   return (x ++ y)
< = {-~  definition of |runSTT|  -} % NOTE: find some literature later
<    \ s -> do  x <- fmap fst . runSTT $ do  st <- liftST (emptyStack ());
<                                            hStack (hGlobal p s) st;
<               y <- fmap fst . runSTT $ do  st <- liftST (emptyStack ());
<                                            hStack (hGlobal q s) st;
<               return (x ++ y)

<    \ s -> do  x <- fmap fst (runSTT $ liftST (emptyStack ()) >>= hStack (hGlobal p s));
<               y <- fmap fst (runSTT $ liftST (emptyStack ()) >>= hStack (hGlobal q s));
<               return (x ++ y)
< = {-~  definition of |runhStack|  -}
<    \ s -> do  x <- fmap fst (runhStack () (hGlobal p s));
<               y <- fmap fst (runhStack () (hGlobal q s));
<               return (x ++ y)
< = {-~  definition of |fmap|  -}
<    \ s -> do  x <- (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) p s;
<               y <- (fmap (\ x -> fmap fst (runhStack () x)) . hGlobal) q s;
<               return (x ++ y)
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

\begin{lemma}[Stack and State are Restored] \label{lemma:stack-state-restore}
% For |t :: Free (StateF s :+: NondetF :+: StackF (Either s ()) () :+: f) a|, if |t| is in the range of |local2trail|, the following equation holds.
For |t :: Free (StateF s :+: NondetF :+: f) a|, the following equation holds for any |as :: [s]|, |st :: Stack s' () (Either s ())| and |u :: Free (StateF s :+: StackF (Either s ()) () :+: f) a|.
Again, because the stack infomation is simply a |()|, we omit it in the results of |hStack|.
% <    do  liftST (pushStack (Right ()) st)
% <        pushList as st
% <        (_, s1) <- hStack (hState1 (hNDf . local2trail $ t) s) st
% <        (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
% <        return (s2, st)
% < =
% <    return (head (as ++ [s]), st)
<    do  liftST (pushStack (Right ()) st)
<        pushList as st
<        (_, s1) <- hStack (hState1 (hNDf . local2trail $ t) s) st
<        (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<        return (s2, st)
< =
<    do  let st' = copy st % NOTE: is there a function to do that?
<        liftST (pushStack (Right ()) st)
<        pushList as st
<        (_, s1) <- hStack (hState1 (hNDf . local2trail $ t) s) st
<        (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<        return (head (as ++ [s]), st')
where the |pushList| is defined as
< pushList as st = case as of
<   [] -> return ()
<   (a:as') -> do liftST (pushStack (Left a) st); pushList as' st

\begin{spec}

\end{spec}
So this lemma states that after the evaluation of |pushStack, p, undoTrail|, the state is restored to the original state |s| and the stack is restored to the original empty stack.
\end{lemma}

\begin{proof}
The proof proceeds by structural induction on the free monad |t|.
In the following proofs, we assume implicit commutativity and associativity of the coproduct operator |(:+:)| as we have mentioned in Section \ref{sec:transforming-between-local-and-global-state}.
We assume the smart constructors |getOp, putOp, orOp, failOp, pushOp, popOp| which are wrappers of constructors |Get, Put, Or, Fail, Push, Pop| respectively will automatically insert correct |Op, Inl, Inr| constructors based on the context to make the term well-typed in the following proof.

\noindent \mbox{\underline{case |t = Var a|}}
The left-hand side is
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ Var a) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ Var a) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1, hNDf, hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s) st
<            return (s2, st)
< = {-~  definition of |undoTrail, pushList, hState1, hNDf, hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            liftST (popStack st)
<            return (head (as ++ [s]), st)
< = {-~  definition of |pushStack, popStack|  -}
<            return (head (as ++ [s]), st)
< = {-~  property of |copy|  -}
<        do  let st' = copy st
<            return (head (as ++ [s]), st)
< = {-~  inverse of the first few steps of this case  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ Var a) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st)

\noindent \mbox{\underline{case |t = failOp|}}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ failOp) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ failOp)) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1, hNDf, hStack, failOp|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s) st
<            return (s2, st)
< = {-~  definition of |undoTrail, pushList, hState1, hNDf, hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            liftST (popStack st)
<            return (head (as ++ [s]), st)
< = {-~  definition of |pushStack, popStack|  -}
<            return (head (as ++ [s]), st)
< = {-~  property of |copy|  -}
<        do  let st' = copy st
<            return (head (as ++ [s]), st)
< = {-~  inverse of the first few steps of this case  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ failOp) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st)


\noindent \mbox{\underline{case |t = getOp k|}}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ getOp k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ getOp (local2trail k)) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1, hNDf, hStack, getOp|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  induction hypothesis  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st')
< = {-~  definition of |getOp|  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ getOp k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st')

\noindent \mbox{\underline{case |t = putOp s' k|}}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ putOp s' k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ do {t <- get; push (Left t); putOp s' (local2trail k)}) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1, hNDf, hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            liftST (pushStack (Left s) st)
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s') st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |pushList|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList (as ++ [s]) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s') st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  induction hypothesis  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList (as ++ [s]) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s') st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s] ++ [s']), st')
< = {-~  definition of |head|  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList (as ++ [s]) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ k) s') st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st)
< = {-~  inverse of the first few steps of this case -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ putOp s' k) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st)

\noindent \mbox{\underline{case |t = orOp p q|}}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ orOp p q) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ orOp  (do push (Right ()); local2trail p)
<                                                     (do undoTrail; local2trail q)) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1, hNDf|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (do  push (Right ());
<                                   (_, t1) <- hState1 (hNDf . local2trail $ p) s
<                                   (_, t2) <- hState1 (hNDf undoTrail) t1
<                                   hState1 (hNDf . local2trail $ q) t2) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- do  liftST (pushStack (Right ()) st)
<                           (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<                           (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<                           hStack (hState1 (hNDf . local2trail $ q) t2) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |do|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            liftST (pushStack (Right ()) st)
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) t2) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |pushList|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) t2) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  induction hypothesis of |p|  -} 
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) (head ([] ++ [s]))) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            return (s2, st')
< = {-~  definition of |++|  -} 
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) s) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            return (s2, st')
< = {-~  property of ST monad (swap the order of original state operations)  -} 
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            let st' = copy st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) s) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            return (s2, st')
< = {-~  property of |copy|  -} 
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            liftST (pushStack (Right ()) st')
<            pushList as st'
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) s) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            return (s2, st')
< = {-~  induction hypothesis of |q|  -} 
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            let st'' = copy st'
<            liftST (pushStack (Right ()) st')
<            pushList as st'
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) s) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            return (head (as ++ [s]), st'')
< = {-~  property of |ST monad| and |copy|  -} 
<        do  let st'' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            let st' = copy st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ q) s) st'
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st'
<            liftST (pushStack (Right ()) st)
<            pushList [] st
<            (_, t1) <- hStack (hState1 (hNDf . local2trail $ p) s) st
<            (_, t2) <- hStack (hState1 (hNDf undoTrail) t1) st
<            return (head (as ++ [s]), st'')
< = {-~  inverse of the first few steps of this case  -}
<        do  let st'' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ orOp p q) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st'')

\noindent \mbox{\underline{case |t = Op (Inr (Inr y))|}}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ Op (Inr (Inr y))) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |local2trail|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf $ Op . Inr . Inr . Inr $ fmap local2trail y) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hNDf|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (Op . Inr . Inr $ fmap (hNDf . local2trail) y) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hState1|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (Op (fmap ($s) $ (Inr $ fmap (hState1 . hNDf . local2trail) y))) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |Inr|; |fmap| fusion  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (Op . Inr $ fmap (($s) . hState1 . hNDf . local2trail) y) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  definition of |hStack|  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- STT $ \s' -> Op (fmap (\f -> unSTT (f st) s')
<              (fmap (($s) . hState1 . hNDf . local2trail) y))
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  |fmap| fusion  -}
<        do  liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- STT $ \s' -> Op (fmap ((\f -> unSTT (f st) s') . ($s) . hState1 . hNDf . local2trail) y)
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (s2, st)
< = {-~  property of ST monad  -} % NOTE: literature?
<        Op $ fmap ( \t ->
<          do  liftST (pushStack (Right ()) st)
<              pushList as st
<              (_, s1) <- STT $ \s' -> (\f -> unSTT (f st) s') . ($s) . hState1 . hNDf . local2trail $ t
<              (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<              return (s2, st)
<        ) y
< = {-~  induction hypothesis  -} % NOTE: I expect the |st| is not shared, is it right?
<        Op $ fmap ( \t ->
<          do  let st' = copy st
<              liftST (pushStack (Right ()) st)
<              pushList as st
<              (_, s1) <- STT $ \s' -> (\f -> unSTT (f st) s') . ($s) . hState1 . hNDf . local2trail $ t
<              (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<              return (head (as ++ [s]), st')
<        ) y
< = {-~  inverse of the first few steps of this case  -}
<        do  let st' = copy st
<            liftST (pushStack (Right ()) st)
<            pushList as st
<            (_, s1) <- hStack (hState1 (hNDf . local2trail $ Op (Inr (Inr y))) s) st
<            (_, s2) <- hStack (hState1 (hNDf undoTrail) s1) st
<            return (head (as ++ [s]), st')

\end{proof}