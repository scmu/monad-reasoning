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

For brevity, we define
< runStack = fmap fst . flip runStateT (Stack []) . hState

We calculate as follows:
\begin{spec}
    fmap runStack . hGlobalM . local2trail
 = {-~  definition of |local2trail| -}
    fmap runStack . hGlobalM . fold Var (alg1 # alg2 # fwd)
      where
        alg1 (MUpdate r k)  = do pushStack (Left r); update r; k
        alg1 p              = Op . Inl $ p
        alg2 (Or p q)       = (do pushStack (Right ()); p) `mplus` (do undoTrail; q)
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
<   \s -> fmap fst . flip runStateT (Stack []) . hState $ Var [x]
< = {-~ definition of |hState| -}
<   \s -> fmap fst . flip runStateT (Stack []) $ StateT (\ s -> Var ([x], s)
< = {-~ definition of |runStateT| -}
<   \s -> fmap fst (Var ([x], Stack []))
< = {-~ definition of |fmap| -}
<   \s -> Var [x]
< = {-~ definition of |genLHS| -}
<   genLHS x
