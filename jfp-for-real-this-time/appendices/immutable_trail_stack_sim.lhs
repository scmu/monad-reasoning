import GHC.IO.Handle.Types (BufferList(BufferListCons))
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
<     _        <- hModify1 (hNDf (comm2 (pushStack (Right ())))) s
<     (x, s1)  <- hModify1 (hNDf (comm2 p)) s
<     (_, s2)  <- hModify1 (hNDf (comm2 undoTrail)) s1
<     (y, s3)  <- hModify1 (hNDf (comm2 q)) s2
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
<     ((y,  _),  _) <- hState1 (hModify1 (hNDf (comm2 q)) s) (Stack [])
<     return (x ++ y)
< = {-~ monad law -}
<   \s -> do
<     (_,  t1) <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) (Stack [])
<     ((x, s1), _) <- hState1 (hModify1 (hNDf (comm2 p)) s) t1
<     ((y,  _), _) <- hState1 (hModify1 (hNDf (comm2 q)) s) (Stack [])
<     return (x ++ y)
< = {-~ \Cref{lemma:initial-stack-is-ignored} -}
<   \s -> do
<     ((x, _), _) <- hState1 (hModify1 (hNDf (comm2 p)) s) (Stack [])
<     ((y, _), _) <- hState1 (hModify1 (hNDf (comm2 q)) s) (Stack [])
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


For the last subcondition \refe{}, we can define |fwdLHS| as follows.
< fwdLHS :: Functor f => f (s -> Free f [a]) -> (s -> Free f [a])
< fwdLHS op = \s -> Op (fmap ($ s) op)

We prove it by the following calculation for input |op :: f (Free
(ModifyF s r :+: NondetF :+: f) a)|.
%
In the corresponding case of \Cref{app:modify-fusing-lhs}, we have
calculated that |hGlobalM (Op (Inr (Inr op))) = \s -> Op (fmap ($ s)
(fmap hGlobalM op))| \refs{}.

<   fmap runStack $ hGlobalM (fwd op)
< = {-~ definition of |fwd| -}
<   fmap runStack $ hGlobalM (Op . Inr . Inr . Inr $ op)
< = {-~ Equation \refs{} -}
<   fmap runStack $ \s -> Op (fmap ($ s) (fmap hGlobalM (Inr op)))
< = {-~ fmap fusion -}
<   fmap runStack $ \s -> Op (fmap (($s) . hGlobalM) (Inr op))
< = {-~ reformulation -}
<   fmap runStack $ \s -> Op (fmap (\ x -> hGlobalM x s) (Inr op))
< = {-~ definition of |fmap| -}
<   \s -> runStack $ Op (fmap (\ x -> hGlobalM x s) (Inr op))
< = {-~ definition of |runStack| -}
<   \s -> fmap fst . flip hState1 (Stack []) $
<     Op (fmap (\ x -> hGlobalM x s) (Inr op))
< = {-~ definition of |hState1| -}
<   \s -> fmap fst $ (\ t ->
<     Op (fmap ($t) . fmap (hState1) $ fmap (\ x -> hGlobalM x s) op)) (Stack [])
< = {-~ fmap fusion and reformulation -}
<   \s -> fmap fst $ (\ t ->
<     Op (fmap (\ x -> hState1 (hGlobalM x s) t) op)) (Stack [])
< = {-~ function application -}
<   \s -> fmap fst $
<     Op (fmap (\ x -> hState1 (hGlobalM x s) (Stack [])) op)
< = {-~ definition of |fmap| -}
<   \s -> Op (fmap (\ x -> fmap fst (hState1 (hGlobalM x s) (Stack []))) op)
< = {-~ reformulation -}
<   \s -> Op (fmap (\ x -> fmap (fmap fst . flip hState1 (Stack [])) . hGlobalM $ x s ) op)
< = {-~ reformulation -}
<   \s -> Op (fmap (\ x -> (fmap runStack . hGlobalM $ x) s ) op)
< = {-~ fmap fission -}
<   \s -> Op (fmap ($ s) (fmap (fmap runStack . hGlobalM) op))
< = {-~ definition of |fwdLHS|  -}
<   fwdLHS (fmap (fmap runStack . hGlobalM) op)


\subsection{Lemmas}

\begin{lemma}[undoTrail undos]~ \label{lemma:undoTrail-undos}
|t = Stack (ys ++ [Right ()] ++ xs')| and |Right ()| does not appear in |ys|

<    do  ((_, s'), t') <- hState1 ((hModify1 . hNDf . comm2) undoTrail s) t
<        return (s', t')
< =
<    do  ((_,  _),  _) <- hState1 ((hModify1 . hNDf . comm2) undoTrail s) t
<        return (fminus s ys, Stack ([Right ()] ++ xs'))
\end{lemma}

\begin{lemma}[Trail stack tracks state]~
% Idea: local2trail p does not leave any Right (), and leaves all Left
% r that it uses
For |t :: Stack (Either r ())|, |s :: s|, and |p :: Free (ModifyF s r
:+: NondetF :+: f) a| which does not use the |restore| operation, we
have
% <  do  ((x, s'), t') <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t
% <      return (x, t' == extend t ys, s' == fplus s ys)
<    hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t
< =
<    do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) (Stack [])
<        return ((x, fplus s ys), extend t ys)
% <      return (x, True, True)
%
for some |ys = [Left r_n, ..., Left r_1]|. The functions |extend| and
|fplus| are defined as follows:
%
\begin{spec}
extend :: Stack s -> [s] -> Stack s
extend (Stack xs) ys = Stack (ys ++ xs)
fplus :: Undo s r => s -> [Either r b] -> s
fplus s ys = foldr (\ (Left r) s -> s `plus` r) s ys
fminus :: Undo s r => s -> [Either r b] -> s
fminus s ys = foldl (\ s (Left r) -> s `minus` r) s ys
\end{spec}
\end{lemma}

\begin{proof}
% Note that |hState1 ((hModify1 . hNDf . comm2) (local2trail p)) t|.
Note that an immediate corollary is that in addition to replace the
stack |t| with the empty stack |Stack []|, we can also replace it with
any other stack. The following equation holds.
%
<    hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t
< =
<    do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t'
<        return ((x, fplus s ys), extend t ys)
%
We will use this corollary in the induction hypothesis.

We proceed by induction on |p|.

\noindent \mbox{\underline{case |p = Var y|}}

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Var y)) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (Var y) s) t
< = {-~ definition of |comm2| -}
<   hState1 ((hModify1 . hNDf) (Var y) s) t
< = {-~ definition of |hNDf| -}
<   hState1 (hModify1 (Var [y]) s) t
< = {-~ definition of |hModify1| and functiona application -}
<   hState1 (Var ([y], s)) t
< = {-~ definition of |hState1| and functiona application -}
<  Var (([y], s), t)
< = {-~ similar derivation in reverse  -}
<  do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2) (local2trail (Var y)) s) (Stack [])
<      Var ((x, s), t)


\noindent \mbox{\underline{case |t = Op . Inr . Inl $ Fail|}}

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Op . Inr . Inl $ Fail)) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (Op . Inr . Inl $ Fail) s) t
< = {-~ definition of |comm2| and |hNDf| -}
<   hState1 (hModify1 (Var []) s) t
< = {-~ definition of |hModify1| and function application -}
<   hState1 (Var ([], s)) t
< = {-~ definition of |hState1| and functiona application -}
<  Var (([], s), t)
< = {-~ similar derivation in reverse  -}
<  do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2)
<                       (local2trail (Op . Inr . Inl $ Fail)) s) (Stack [])
<      Var ((x, s), t)


\noindent \mbox{\underline{case |t = Op (Inl (MGet k))|}}

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Op (Inl (MGet k)))) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (Op (Inl (MGet (local2trail . k)))) s) t
< = {-~ definition of |comm2| and |hNDf| -}
<   hState1 (hModify1 (Op (Inl (MGet (hNDf . comm2 . local2trail . k)))) s) t
< = {-~ definition of |hModify1| and function application -}
<   hState1 ((hModify1 . hNDf . comm2 . local2trail . k) s s) t
< = {-~ reformulation -}
<   hState1 ((hModify1 . hNDf . comm2) (local2trail (k s)) s) t
< = {-~ induction hypothesis on |k s| -}
<   do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2) (local2trail (k s)) s) (Stack [])
<       return ((x, fplus s ys), extend t ys)
< = {-~ similar derivation in reverse -}
<   do  ((x, _), _) <- hState1 ((hModify1 . hNDf . comm2)
<                        (local2trail (Op (Inl (MGet k)))) s) (Stack [])
<       return ((x, fplus s ys), extend t ys)


\noindent \mbox{\underline{case |t = Op (Inl (MUpdate r k))|}}
% NOTE: in some proofs of this section, I omitted a bit more steps.
% For example, I used the property that the application of |hNDf|
% distributes monad binding when there is no nondeterminism operations
% in the first computations. This property is obvious from the
% definition of the forwarding clause of |hNDf|.

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Op (Inl (MUpdate r k)))) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (do
<     pushStack (Left r)
<     update r
<     local2trail k
<   ) s) t
< = {-~ definition of |comm2| and |hNDf| -}
<   hState1 (hModify1 (do
<     hNDf . comm2 $ pushStack (Left r)
<     hNDf . comm2 $ update r
<     hNDf . comm2 . local2trail $ k
<   ) s) t
< = {-~ definition of |hModify1|, \Cref{lemma:dist-hModify1} and function application -}
<   hState1 (do
<     (_, s1) <- (hModify1 . hNDf . comm2 $ pushStack (Left r)) s
<     (_, s2) <- (hModify1 . hNDf . comm2 $ update r) s1
<     (hModify1 . hNDf . comm2 . local2trail $ k) s2
<   ) t
< = {-~ definition of |hModify1| and |update| -}
<   hState1 (do
<     (_, s1) <- (hModify1 . hNDf . comm2 $ pushStack (Left r)) s
<     (_, s2) <- return ([()], s1 `plus` r)
<     (hModify1 . hNDf . comm2 . local2trail $ k) s2
<   ) t
< = {-~ monad law -}
<   hState1 (do
<     (_, s1) <- (hModify1 . hNDf . comm2 $ pushStack (Left r)) s
<     (hModify1 . hNDf . comm2 . local2trail $ k) (s1 `plus` r)
<   ) t
< = {-~ definition of |hState1|, \Cref{lemma:dist-hState1}, and function application -}
<   do  ((_, s1), t1) <- hState1 ((hModify1 . hNDf . comm2 $ pushStack (Left r)) s) t
<       hState1 ((hModify1 . hNDf . comm2 . local2trail $ k) (s1 `plus` r)) t1
< = {-~ definition of |pushStack| -}
<   do  ((_, s1), t1) <- hState1 ((hModify1 . hNDf . comm2 $ do
<         Stack xs <- get
<         put (Stack (Left r : xs))) s) t
<       hState1 ((hModify1 . hNDf . comm2 . local2trail $ k) (s1 `plus` r)) t1
< = {-~ definition of |hState1|, |hModify1|, |hNDf|, |comm2|, |get|, and |put|; let |t = Stack xs| -}
<   do  ((_, s1), t1) <- return (([()], s), Stack (Left r : xs))
<       hState1 ((hModify1 . hNDf . comm2) (local2trail k) (s1 `plus` r)) t1
< = {-~ monad law -}
<   hState1 ((hModify1 . hNDf . comm2) (local2trail k) (s `plus` r)) (Stack (Left r : xs))
< = {-~ by induction hypothesis on |k|, for some |ys| the equation holds -}
<   do  ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2)
<                      (local2trail k) (s `plus` r)) (Stack [Left r])
<       return ((x, fplus (s `plus` r) ys), extend (Stack (Left r : xs)) ys)
< = {-~ definition of |fplus| and |extend| -}
<   do  ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2)
<                      (local2trail k) (s `plus` r)) (Stack [Left r])
<       return ((x, fplus s (ys ++ [Left r])), extend (Stack xs) (ys ++ [Left r]))
< = {-~ let |ys' = ys ++ [Left r]|; Equation |t = Stack xs| -}
<   do  ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2)
<                      (local2trail k) (s `plus` r)) (Stack [Left r])
<       return ((x, fplus s ys'), extend t ys')
< = {-~ similar derivation in reverse -}
<   do  ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2)
<                      (local2trail (Op (Inl (MUpdate r k)))) s) (Stack [])
<       return ((x, fplus s ys'), extend t ys')


\noindent \mbox{\underline{case |t = Op . Inr . Inl $ Or p q|}}

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Op . Inr . Inl $ Or p q)) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (
<     (pushStack (Right ()) >> local2trail p) `mplus` (undoTrail >> local2trail q)) s) t
< = {-~ definition of |mplus| -}
<   hState1 ((hModify1 . hNDf . comm2) (Op . Inr . Inl $ Or
<     (pushStack (Right ()) >> local2trail p)
<     (undoTrail >> local2trail q)) s) t
< = {-~ definition of |hNDf|, |comm2|, and |liftM2| -}
<   hState1 (hModify1 (do
<     x <- hNDf (comm2 (pushStack (Right ()))) >> hNDf (comm2 (local2trail p))
<     y <- hNDf (comm2 undoTrail) >> hNDf (comm2 (local2trail q))
<     return (x ++ y)
<   ) s) t
< = {-~ monad law -}
<   hState1 (hModify1 (do
<     hNDf (comm2 (pushStack (Right ())))
<     x <- hNDf (comm2 (local2trail p))
<     hNDf (comm2 undoTrail)
<     y <- hNDf (comm2 (local2trail q))
<     return (x ++ y)
<   ) s) t
< = {-~ definition of |hModify1|, \Cref{lemma:dist-hModify1}, and function application -}
<   hState1 (do
<     (_, s1)  <- hModify1 (hNDf (comm2 (pushStack (Right ())))) s
<     (x, s2)  <- hModify1 (hNDf (comm2 (local2trail p))) s1
<     (_, s3)  <- hModify1 (hNDf (comm2 undoTrail)) s2
<     (y, s4)  <- hModify1 (hNDf (comm2 (local2trail q))) s3
<     return (x ++ y, s4)
<   ) t
< = {-~ definition of |hState1|, \Cref{lemma:dist-hState1}, and function application -}
<   do  ((_, s1), t1)  <- hState1 (hModify1 (hNDf (comm2 (pushStack (Right ())))) s) t
<       ((x, s2), t2)  <- hState1 (hModify1 (hNDf (comm2 (local2trail p))) s1) t1
<       ((_, s3), t3)  <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s2) t2
<       ((y, s4), t4)  <- hState1 (hModify1 (hNDf (comm2 (local2trail q))) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ definition of |pushStack| -}
<   do  ((_, s1), t1)  <- hState1 (hModify1 (hNDf (comm2 (do
<         Stack xs <- get
<         put (Stack (Right () : xs))))) s) t
<       ((x, s2), t2)  <- hState1 (hModify1 (hNDf (comm2 (local2trail p))) s1) t1
<       ((_, s3), t3)  <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s2) t2
<       ((y, s4), t4)  <- hState1 (hModify1 (hNDf (comm2 (local2trail q))) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ definition of |hState1, hModify1, hNDf, comm2, get, put|; let |t = Stack xs| -}
<   do  ((_, s1), t1)  <- return (([()], s), Stack (Right () : xs))
<       ((x, s2), t2)  <- hState1 (hModify1 (hNDf (comm2 (local2trail p))) s1) t1
<       ((_, s3), t3)  <- hState1 (hModify1 (hNDf (comm2 undoTrail)) s2) t2
<       ((y, s4), t4)  <- hState1 (hModify1 (hNDf (comm2 (local2trail q))) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ monad law -}
<   do  ((x, s2), t2)  <-  hState1 (hModify1 (hNDf (comm2
<                            (local2trail p))) s) (Stack (Right () : xs))
<       ((_, s3), t3)  <-  hState1 (hModify1 (hNDf (comm2 undoTrail)) s2) t2
<       ((y, s4), t4)  <-  hState1 (hModify1 (hNDf (comm2 (local2trail q))) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ reformulation -}
<   do  ((x, s2), t2)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right () : xs))
<       ((_, s3), t3)  <-  hState1 ((hModify1 . hNDf . comm2) undoTrail s2) t2
<       ((y, s4), t4)  <-  hState1 ((hModify1 . hNDf . comm2) (local2trail q) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ by induction hypothesis on |p|, for some |ys| the equation holds  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right ()))
<       ((_, s3), t3)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            undoTrail (fplus s ys)) (extend (Stack (Right () : xs)) ys)
<       ((y, s4), t4)  <-  hState1 ((hModify1 . hNDf . comm2) (local2trail q) s3) t3
<       return ((x ++ y, s4), t4)
< = {-~ \Cref{lemma:undoTrail-undos}  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right ()))
<       ((_,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            undoTrail (fplus s ys)) (extend (Stack (Right () : xs)) ys)
<       ((y, s4), t4)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail q) (fminus (fplus s ys) ys)) (Stack xs)
<       return ((x ++ y, s4), t4)
< = {-~ \Cref{eq:plus-minus} gives |fminus (fplus s ys) ys = s|  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right ()))
<       ((_,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            undoTrail (fplus s ys)) (extend (Stack (Right () : xs)) ys)
<       ((y, s4), t4)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail q) s) (Stack xs)
<       return ((x ++ y, s4), t4)
< = {-~ by induction hypothesis on |p|, for some |ys'| the equation holds  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right ()))
<       ((_,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            undoTrail (fplus s ys)) (extend (Stack (Right () : xs)) ys)
<       ((y,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail q) s) (Stack [])
<       return ((x ++ y, fplus s ys'), extend (Stack xs) ys')
< = {-~ monad law  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail p) s) (Stack (Right ()))
<       ((y,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail q) s) (Stack [])
<       return ((x ++ y, fplus s ys'), extend (Stack xs) ys')
< = {-~ similar derivation in reverse  -}
<   do  ((x,  _),  _)  <-  hState1 ((hModify1 . hNDf . comm2)
<                            (local2trail (Op . Inr . Inl $ Or p q)) s) (Stack [])
<       return ((x, fplus s ys'), extend t ys')


\noindent \mbox{\underline{case |t = Op . Inr . Inr $ y|}}

<   hState1 ((hModify1 . hNDf . comm2) (local2trail (Op . Inr . Inr $ y)) s) t
< = {-~ definition of |local2trail| -}
<   hState1 ((hModify1 . hNDf . comm2) (Op . Inr . Inr . Inr . fmap local2trail $ y) s) t
< = {-~ definition of |comm2| and |hNDf| -}
<   hState1 (hModify1 (Op . Inr . Inr . fmap (hNDf . comm2 . local2trail) $ y) s) t
< = {-~ definition of |hModify1| and function application -}
<   hState1 (Op . Inr . fmap (($s) . hModify1 . hNDf . comm2 . local2trail) $ y) t
< = {-~ definition of |hState1| and function application -}
<   Op . fmap (($t) . hState1 . ($s) . hModify1 . hNDf . comm2 . local2trail) $ y
< = {-~ reformulation -}
<   Op . fmap (\k -> hState1 ((hModify1 . hNDf . comm2) (local2trail k) s) t) $ y
< = {-~ by induction hypothesis on |y|, for some |ys| the equation holds -}
<   Op . fmap (\k -> do
<     ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2) (local2trail k) s) t
<     return ((x, fplus s ys), extend t ys) ) $ y
< = {-~ definition of free monad -}
<   do  ((x, _), _) <- Op . fmap (\k ->
<         hState1 ((hModify1 . hNDf . comm2) (local2trail k) s) t) $ y
<       return ((x, fplus s ys), extend t ys)
< = {-~ similar derivation in reverse -}
<   do  ((x,_),_) <- hState1 ((hModify1 . hNDf . comm2) (local2trail (Op . Inr . Inr $ y)) s) t
<       return ((x, fplus s ys), extend t ys)

\end{proof}

\begin{lemma}[Initial stack is ignored]~ \label{lemma:initial-stack-is-ignored}
For any program |p :: Free (ModifyF s r :+: NondetF :+: f) a| that do
not use the operation |OP (Inl MRestore _ _)|, |s :: s|, and |t = Stack ys ::
Stack (Either r ())|, we have

<     hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) t
< =   do ((x, s), Stack xs) <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s) (Stack [])
<     return ((x, s), Stack (xs ++ ys))

% <    fmap fst (hState1 (hGlobalM (local2trail p) s) t)
% < =  fmap fst (hState1 (hGlobalM (local2trail p) s) (Stack []))
\end{lemma}

\begin{proof}

\end{proof}

\begin{lemma}[State and stack are restored]~ \label{lemma:state-stack-restore}
<  do
<    ((_, s1), t1)  <- hState1 ((hModify1 . hNDf . comm2) (pushStack (Right ())) s) t
<    ((x, s2), t2)  <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s1) t1
<    ((_, s3), t3)  <- hState1 ((hModify1 . hNDf . comm2) undoTrail s2) t2
<    return (s3, t3)
< =
<  do
<    ((_, s1), t1)  <- hState1 ((hModify1 . hNDf . comm2) (pushStack (Right ())) s) t
<    ((x, s2), t2)  <- hState1 ((hModify1 . hNDf . comm2) (local2trail p) s1) t1
<    ((_, s3), t3)  <- hState1 ((hModify1 . hNDf . comm2) undoTrail s2) t2
<    return (s, t)
\end{lemma}

\begin{proof}

\end{proof}
