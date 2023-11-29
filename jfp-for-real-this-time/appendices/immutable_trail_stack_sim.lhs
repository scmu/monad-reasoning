%if False
\begin{code}
\end{code}
%endif
\section{Proofs for Simulating Local State with Trail Stack}
\label{app:immutable-trail-stack}

%-------------------------------------------------------------------------------

In this section, we prove the following theorem in
\Cref{sec:trail-stack}.

\localTrail*


The proof follows a similar structure to those in
\Cref{app:local-global} and \Cref{app:modify-local-global}.

As in \Cref{app:modify-local-global}, we fuse |runStateT . hModify|
into |hModify1| and use it instead in the following proofs.

%format genLHS = "\Varid{gen}_{\Varid{LHS}}"
%format genRHS = "\Varid{gen}_{\Varid{RHS}}"
%format algSLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{S}}"
%format algSRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{S}}"
%format algNDLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{ND}}"
%format algNDRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{ND}}"
%format fwdLHS = "\Varid{fwd}_{\Varid{LHS}}"
%format fwdRHS = "\Varid{fwd}_{\Varid{RHS}}"
\subsection{Main Proof Structure}
The main proof structure of \Cref{thm:local2trail} is as follows.
\begin{proof}
The left-hand side is expanded to

< hGlobalT = fmap (fmap fst . flip runStateT (Stack []) . hState) . hGlobalM . local2trail

Both the left-hand side and the right-hand side of the equation
consist of function compositions involving one or more folds.
We apply fold fusion separately on both sides to contract each
into a single fold:
\begin{eqnarray*}
|hGlobalT| & = & |fold genLHS (algSLHS # algNDRHS # fwdLHS)| \\
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

We have already fused |hLocalM| in \Cref{app:modify-fusing-rhs}.
We just show the result here for easy reference.
%
\begin{spec}
hLocalM = fold genRHS (algSRHS # algNDRHS # fwdRHS)
  where
    genRHS :: Functor f => a -> (s -> Free f [a])
    genRHS x = \s -> Var [x]
    algSRHS :: Undo s r => StateF s (s -> p) -> (s -> p)
    algSRHS (MGet k)        = \ s -> k s s
    algSRHS (MUpdate r k)   = \ s -> k (s `plus` r)
    algSRHS (MRestore r k)  = \ s -> k (s `plus` r)
    algNDRHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
    algNDRHS Fail      = \ s -> Var []
    algNDRHS (Or p q)  = \ s -> liftM2 (++) (p s) (q s)
    fwdRHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
    fwdRHS op = \s -> Op (fmap ($s) op)
\end{spec}
%if False
$
%endif


\subsection{Fusing the Left-Hand Side}


As in \Cref{app:local-global}, we fuse |runStateT . hState|
into |hState1|.
%
For brevity, we define
< runStack = fmap fst . flip hState1 (Stack [])
%
The left-hand side is simplified to
< fmap runStack . hGlobalM . local2trail

We calculate as follows:
\begin{spec}
    fmap runStack . hGlobalM . local2trail
 = {-~  definition of |local2trail| -}
    fmap runStack . hGlobalM . fold Var (alg1 # alg2 # fwd)
      where
        alg1 (MUpdate r k)  = pushStack (Left r) >> update r >> k
        alg1 p              = Op . Inl $ p
        alg2 (Or p q)       = (pushStack (Right ()) >> p) `mplus` (undoTrail >> q)
        alg2 p              = Op . Inr . Inl $ p
        fwd p               = Op . Inr . Inr . Inr $ p
        undoTrail = do  top <- popStack;
                        case top of
                          Nothing -> return ()
                          Just (Right ()) -> return ()
                          Just (Left r) -> do restore r; undoTrail
 = {-~  fold fusion-post' (Equation \ref{eq:fusion-post-strong})  -}
    fold genLHS (algSLHS # algNDLHS # fwdLHS)
\end{spec}

This last step is valid provided that the fusion conditions are satisfied:
\[\ba{rclr}
|fmap runStack . hGlobalM . Var| & = & |genLHS| &\refa{}\\
\ea\]
\vspace{-\baselineskip}
\[\ba{rlr}
   &|fmap runStack . hGlobalM . (alg1 # alg2 # fwd) . fmap local2trail| \\
= & |(algSLHS # algNDLHS # fwdLHS) . fmap (fmap runStack . hGlobalM) . fmap local2trail| &\refb{}
\ea\]

The first subcondition \refa{} is met by
< genLHS :: Functor f => a -> (s -> Free f [a])
< genLHS x = \s -> Var [x]
as established in the following calculation:
<   fmap runStack $ hGlobalM (Var x)
< = {-~ definition of |hGlobalM| -}
<   fmap runStack $ fmap (fmap fst) (hModify1 (hNDf (comm2 (Var x))))
< = {-~ definition of |comm2| -}
<   fmap runStack $ fmap (fmap fst) (hModify1 (hNDf (Var x)))
< = {-~ definition of |hNDf| -}
<   fmap runStack $ fmap (fmap fst) (hModify1 (Var [x]))
< = {-~ definition of |hModify1| -}
<   fmap runStack $ fmap (fmap fst) (\s -> Var ([x], s))
< = {-~ definition of |fmap| (twice) -}
<   fmap runStack $ \s -> Var [x]
< = {-~ definition of |fmap| -}
<   \s -> runStack $ Var [x]
< = {-~ definition of |runStack| -}
<   \s -> fmap fst . flip hState1 (Stack []) $ Var [x]
< = {-~ definition of |hState1| -}
<   \s -> fmap fst $ (\ s -> Var ([x], s)) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst (Var ([x], Stack []))
< = {-~ definition of |fmap| -}
<   \s -> Var [x]
< = {-~ definition of |genLHS| -}
<   genLHS x


We can split the second fusion condition \refb{} in three
subconditions:
\[\ba{rlr}
  & |fmap runStack . hGlobalM . alg1 . fmap local2trail| \\
= & |algSLHS . fmap (fmap runStack . hGlobalM) . fmap local2trail| &\refc{}\\
  & |fmap runStack . hGlobalM . hGlobalM . alg2 . fmap local2trail| \\
= & |algNDLHS . fmap (fmap runStack . hGlobalM) . fmap local2trail| &\refd{}\\
  & |fmap runStack . hGlobalM . hGlobalM . fwd . fmap local2trail| \\
= & |fwdLHS . fmap (fmap runStack . hGlobalM) . fmap local2trail| &\refe{}
\ea\]

For brevity, we omit the last common part |fmap local2globalM| of
these equations. Instead, we assume that the input is in the codomain
of |fmap local2globalM|.

For the first subcondition \refc{}, we define |algSLHS| as follows.
< algSLHS :: (Functor f, Undo s r) => ModifyF s r (s -> Free f [a]) -> (s -> Free f [a])
< algSLHS (MGet k)        = \ s -> k s s
< algSLHS (MUpdate r k)   = \ s -> k (s `plus` r)
< algSLHS (MRestore r k)  = \ s -> k (s `minus` r)

We prove it by a case analysis on the shape of input |op :: ModifyF s
r (Free (ModifyF s r :+: NondetF :+: f) a)|.
%
We use the condition in \Cref{thm:modify-local-global} that the input
program does not use the |restore| operation.
%
We only need to consider the case that |op| is of form |MGet k| or
|MUpdate r k| where |restore| is also not used in the continuation
|k|.

\vspace{0.5\lineskip}

\noindent \mbox{\underline{case |op = MGet k|}}
%
In the corresponding case of \Cref{app:modify-fusing-lhs}, we have
calculated that |hGlobalM (Op (Inl (MGet k))) = \s -> (hGlobalM . k) s
s| \refs{}.

<   fmap runStack $ hGlobalM (alg1 (MGet k))
< = {-~ definition of |alg1| -}
<   fmap runStack $ hGlobalM (Op (Inl (MGet k)))
< = {-~ Equation \refs{} -}
<   fmap runStack $ \s -> (hGlobalM . k) s s
< = {-~ definition of |fmap| -}
<   \s -> runStack $ (hGlobalM . k) s s
< = {-~ definition of |fmap| -}
<   \s -> (fmap runStack . hGlobalM . k) s s
< = {-~ definition of |algSLHS| -}
<   algSLHS (MGet (fmap runStack . hGlobalM . k))
< = {-~ definition of |fmap| -}
<   algSLHS (fmap (fmap runStack . hGlobalM) (MGet k))

\noindent \mbox{\underline{case |op = MUpdate r k|}}
%
From |op| is in the codomain of |fmap local2globalM| we obtain |k| is
in the codomain of |local2globalM|.

<   fmap runStack . hGlobalM $ alg1 (MUpdate r k)
< = {-~ definition of |alg1| -}
<   fmap runStack . hGlobalM $ pushStack (Left r) >> update r >> k
< = {-~ definition of |pushStack| -}
<   fmap runStack . hGlobalM $ do
<     Stack xs <- get
<     put (Stack (Left r : xs))
<     update r >> k
< = {-~ definition of |get|, |put|, and |update| -}
<   fmap runStack . hGlobalM $
<     Op . Inr . Inr . Inl $ Get (\ (Stack xs) ->
<       Op . Inr . Inr . Inl $ Put (Stack (Left r : xs)) (
<         Op . Inl $ MUpdate r k))
< = {-~ definition of |hGlobalM| -}
<   fmap runStack . fmap (fmap fst) . hModify1 . hNDf . comm2 $
<     Op . Inr . Inr . Inl $ Get (\ (Stack xs) ->
<       Op . Inr . Inr . Inl $ Put (Stack (Left r : xs)) (
<         Op . Inl $ MUpdate r k))
< = {-~ definition of |comm2| -}
<   fmap runStack . fmap (fmap fst) . hModify1 . hNDf $
<     Op . Inr . Inr . Inl $ Get (\ (Stack xs) ->
<       Op . Inr . Inr . Inl $ Put (Stack (Left r : xs)) (
<         Op . Inr . Inl $ MUpdate r (comm2 k)))
< = {-~ definition of |hNDf| -}
<   fmap runStack . fmap (fmap fst) . hModify1 $
<     Op . Inr . Inl $ Get (\ (Stack xs) ->
<       Op . Inr . Inl $ Put (Stack (Left r : xs)) (
<         Op . Inl $ MUpdate r (hNDf . comm2 $ k)))
< = {-~ definition of |hModify1| -}
<   fmap runStack . fmap (fmap fst) $ \s ->
<     Op . Inl $ Get (\ (Stack xs) ->
<       Op . Inl $ Put (Stack (Left r : xs)) (
<         (hModify1 . hNDf . comm2 $ k) (s `plus` r)))
< = {-~ definition of |fmap (fmap fst)| -}
<   fmap runStack $ \s ->
<     Op . Inl $ Get (\ (Stack xs) ->
<       Op . Inl $ Put (Stack (Left r : xs)) (
<         (fmap (fmap fst) . hModify1 . hNDf . comm2 $ k) (s `plus` r)))
< = {-~ definition of |fmap| -}
<   \s -> runStack $
<     Op . Inl $ Get (\ (Stack xs) ->
<       Op . Inl $ Put (Stack (Left r : xs)) (
<         (fmap (fmap fst) . hModify1 . hNDf . comm2 $ k) (s `plus` r)))
< = {-~ definition of |hGlobalM| -}
<   \s -> runStack $
<     Op . Inl $ Get (\ (Stack xs) ->
<       Op . Inl $ Put (Stack (Left r : xs)) (
<         (hGlobalM k) (s `plus` r)))
< = {-~ definition of |runStack| -}
<   \s -> fmap fst . flip hState1 (Stack []) $
<     Op . Inl $ Get (\ (Stack xs) ->
<       Op . Inl $ Put (Stack (Left r : xs)) (
<         (hGlobalM k) (s `plus` r)))
< = {-~ definition of |hState1| -}
<   \s -> fmap fst $ (\t ->
<     (\ (Stack xs) -> \ _ ->
<       ((fmap hState1 . hGlobalM $ k) (s `plus` r)) (Stack (Left r : xs))
<     ) t t
<   ) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst $
<     (\ (Stack xs) -> \ _ ->
<       ((fmap hState1 . hGlobalM $ k) (s `plus` r)) (Stack (Left r : xs))
<     ) (Stack []) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst $
<     (\ _ ->
<       ((fmap hState1 . hGlobalM $ k) (s `plus` r)) (Stack (Left r : []))
<     ) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst $
<     ((fmap hState1 . hGlobalM $ k) (s `plus` r)) (Stack (Left r : []))
< = {-~ function application -}
<   \s -> fmap fst $
<     ((fmap hState1 . hGlobalM $ k) (s `plus` r)) (Stack (Left r : []))
< = {-~ definition of |flip| and reformulation -}
<   \s -> (fmap (fmap fst . flip hState1 (Stack [Left r])) . hGlobalM $ k) (s `plus` r)
< = {-~ \Cref{lemma:initial-stack-is-ignored} -}
<   \s -> (fmap (fmap fst . flip hState1 (Stack [])) . hGlobalM $ k) (s `plus` r)
< = {-~ definition of |runStack| -}
<   \s -> (fmap runStack . hGlobalM $ k) (s `plus` r)
< = {-~ definition of |algSLHS| -}
<   algSLHS (MUpdate r (fmap runStack . hGlobalM $ k))
< = {-~ definition of |fmap| -}
<   algSLHS (fmap (fmap runStack . hGlobalM) (MUpdate r k))


For the second subcondition \refd{}, we can define |algNDLHS| as
follows.
< algNDLHS :: Functor f => NondetF (s -> Free f [a]) -> (s -> Free f [a])
< algNDLHS Fail      = \s -> Var []
< algNDLHS (Or p q)  = \s -> liftM2 (++) (p s) (q s)

We prove it by a case analysis on the shape of input |op :: NondetF
(Free (ModifyF s r :+: NondetF :+: f) a)|.

\noindent \mbox{\underline{case |op = Fail|}}
%
In the corresponding case of \Cref{app:modify-fusing-lhs}, we have
calculated that |hGlobalM (Op (Inr (Inl Fail))) = \s -> Var []| \refs{}.

<   fmap runStack $ hGlobalM (alg2 (Fail))
< = {-~ definition of |alg2| -}
<   fmap runStack $ hGlobalM (Op (Inr (Inl Fail)))
< = {-~ Equation \refs{} -}
<   fmap runStack $ \s -> Var []
< = {-~ definition of |fmap| -}
<   \s -> runStack $ Var []
< = {-~ definition of |runStack| -}
<   \s -> fmap fst . flip hState1 (Stack []) $ Var []
< = {-~ definition of |hState1| -}
<   \s -> fmap fst $ Var ([], Stack [])
< = {-~ definition of |fmap| -}
<   \s -> Var []
< = {-~ definition of |algNDRHS|  -}
<  algNDRHS Fail
< = {-~ definition of |fmap| -}
<  algNDRHS (fmap (fmap runStack . hGlobalM) Fail)


\noindent \mbox{\underline{case |op = Or p q|}}
%
From |op| is in the codomain of |fmap local2globalM| we obtain |p| and
|q| are in the codomain of |local2globalM|.

<   fmap runStack . hGlobalM $ alg2 (Or p q)
< = {-~ definition of |alg2| -}
<   fmap runStack . hGlobalM $ (pushStack (Right ()) >> p) `mplus` (undoTrail >> q)
< = {-~ definition of |mplus| -}
<   fmap runStack . hGlobalM $ Op . Inr . Inl $ Or
<     (pushStack (Right ()) >> p) (undoTrail >> q)
< = {-~ definition of |hGlobalM| -}
<   fmap runStack . fmap (fmap fst) . hModify1 . hNDf . comm2 $ Op . Inr . Inl $ Or
<     (pushStack (Right ()) >> p) (undoTrail >> q)
< = {-~ definition of |comm2| -}
<   fmap runStack . fmap (fmap fst) . hModify1 . hNDf $ Op . Inl $ Or
<     (pushStack (Right ()) >> comm2 p) (undoTrail >> comm2 q)
< = {-~ definition of |hNDf| and |liftM2| -}
<   fmap runStack . fmap (fmap fst) . hModify1 $ do
<     x <- hNDf (comm2 (pushStack (Right ()))) >> hNDf (comm2 p)
<     y <- hNDf (comm2 undoTrail) >> hNDf (comm2 q)
<     return (x ++ y)
< = {-~ monad law -}
<   fmap runStack . fmap (fmap fst) . hModify1 $ do
<     hNDf (comm2 (pushStack (Right ())))
<     x <- hNDf (comm2 p)
<     hNDf (comm2 undoTrail)
<     y <- hNDf (comm2 q)
<     return (x ++ y)
< = {-~ definition of |hModify1| and \Cref{lemma:dist-hModify1} -}
<   fmap runStack . fmap (fmap fst) $ \s -> do
<     _ <- hModify1 (hNDf (comm2 (pushStack (Right ())))) s
<     (x, s1) <- hModify1 (hNDf (comm2 p)) s
<     (_, s2) <- hModify1 (hNDf (comm2 undoTrail)) s1
<     (y, s3) <- hModify1 (hNDf (comm2 q)) s2
<     return (x ++ y, s3)
< = {-~ definition of |fmap| (twice) -}
<   fmap runStack $ \s -> do
<     _ <- hModify1 (hNDf (comm2 (pushStack (Right ())))) s
<     (x, s1) <- hModify1 (hNDf (comm2 p)) s
<     (_, s2) <- hModify1 (hNDf (comm2 undoTrail)) s1
<     (y,  _) <- hModify1 (hNDf (comm2 q)) s2
<     return (x ++ y)
< = {-~ definition of |fmap| and |runStack| -}
<   \s -> fmap fst . flip hState1 (Stack []) $ do
<     _ <- hModify1 (hNDf (comm2 (pushStack (Right ())))) s
<     (x, s1) <- hModify1 (hNDf (comm2 p)) s
<     (_, s2) <- hModify1 (hNDf (comm2 undoTrail)) s1
<     (y,  _) <- hModify1 (hNDf (comm2 q)) s2
<     return (x ++ y)
< = {-~ definition of |hState1| and \Cref{lemma:dist-hState1} -}
<   \s -> fmap fst $ (\t -> do
<     (_, t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) t
<     ((x, s1), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s) t1
<     ((_, s2), t3) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s1) t2
<     ((y,  _), t4) <- hState1 (hModify1 (hNDf (comm2 q)) s2) t3
<     return (x ++ y, t4) ) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst $ do
<     (_, t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) (Stack [])
<     ((x, s1), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s) t1
<     ((_, s2), t3) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s1) t2
<     ((y,  _), t4) <- hState1 (hModify1 (hNDf (comm2 q)) s2) t3
<     return (x ++ y, t4)
< = {-~ definition of |fmap| -}
<   \s -> do
<     (_, t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) (Stack [])
<     ((x, s1), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s) t1
<     ((_, s2), t3) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s1) t2
<     ((y,  _),  _) <- hState1 (hModify1 (hNDf (comm2 q)) s2) t3
<     return (x ++ y)
< = {-~ \Cref{lemma:state-stack-restore} -}
<   \s -> do
<     (_,  t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) (Stack [])
<     ((x, s1), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s) t1
<     ((_,  _),  _) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s1) t2
<     ((y,  _),  _) <- hState1 (hModify1 (hNDf (comm2 q)) s) t1
<     return (x ++ y)
< = {-~ monad law and \Cref{lemma:initial-stack-is-ignored} -}
<   \s -> do
<     ((x, _), _)   <- hState1 (hModify1 (hNDf (comm2 p)) s) (Stack [])
<     ((y,  _),  _) <- hState1 (hModify1 (hNDf (comm2 q)) s) (Stack [])
<     return (x ++ y)
< = {-~ definition of |runStack| -}
<   \s -> do
<     (x, _) <- runStack (hModify1 (hNDf (comm2 p)) s)
<     (y, _) <- runStack (hModify1 (hNDf (comm2 q)) s)
<     return (x ++ y)
< = {-~ definition of |hGlobalM| -}
<   \s -> do
<     x <- runStack (hGlobalM p s)
<     y <- runStack (hGlobalM q s)
<     return (x ++ y)
< = {-~ definition of |fmap| -}
<   \s -> do
<     x <- (fmap runStack . hGobalM) p s
<     y <- (fmap runStack . hGobalM) q s
<     return (x ++ y))
< = {-~ definition of |liftM2| -}
<   \s -> liftM2 (++) ((fmap runStack . hGobalM) p s) ((fmap runStack . hGobalM) q s)
< = {-~ definition of |algNDLHS|  -}
<   algNDLHS (Or ((fmap runStack . hGobalM) p) ((fmap runStack . hGobalM) q))
< = {-~ definition of |fmap| -}
<   algNDLHS (fmap (fmap runStack . hGobalM) (Or p q))


\subsection{Lemmas}

\begin{lemma}[Initial stack is ignored]~ \label{lemma:initial-stack-is-ignored}
<    fmap fst (hState1 (hGlobalM (local2trail p) s) t)
< =  fmap fst (hState1 (hGlobalM (local2trail p) s) (Stack []))
or
<    fmap fst . flip hState1 st . flip hGlobalM s . local2trail
< =  fmap fst . flip hState1 (Stack []) . flip hGlobalM s . local2trail
\end{lemma}

\begin{lemma}[State and stack are restored]~ \label{lemma:state-stack-restore}
<     ((_, s1),  t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) t
<     ((x, s2), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s1) t1
<     ((_, s3), t3) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s2) t2
<     return (s3, t3)
< =
<     ((_, s1), t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) (Stack [])
<     ((x, s1), t2) <- hState1 (hModify1 (hNDf (comm2 p)) s1) t1
<     ((_, s2), t3) <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s1) t2
<     return (s, t)
\end{lemma}
