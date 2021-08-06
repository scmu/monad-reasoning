\section{Simulating Multiple States with State: The Proofs}
\label{app:states-state}

%-------------------------------------------------------------------------------

This section shows that the function |combine . hStates| is equivalent to |hState . states2state|, where |flatten|, |hStates| and |states2state| are defined in Section \ref{sec:multiple-states}.

\begin{theorem}\label{eq:states-state}
|hStates' = hState . states2state|
\end{theorem}

\begin{proof}
We need to prove that for any input |t :: Free (StateF s1 :+: StateF s2 :+: f) a|, the equation |hStates' t = (hState . states2state) t| holds.
We do a structural induction on |t|.

\noindent \mbox{\underline{base case |t = Var x|}}
<    (hState . states2state) (Var x)
< = {-~  definition of |states2state|  -}
<    hState (gen x)
< = {-~  definition of |gen|  -}
<    hState (return x)
< = {-~  definition of |return|  -}
<    hState (Var x)
< = {-~  definition of |hState|  -}
<    genS x
< = {-~  definition of |genS|  -}
<   StateT $ \ s -> return (x, s) 
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> Var (x, (s1, s2))
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2)  ->  Var ((\ ((a, x), y) -> (a, (x, y))) ((x, s1), s2))
< = {-~  definition of |fmap|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ Var ((x, s1), s2)
< = {-~  definition of |return|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ return ((x, s1), s2)
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ (\ s -> return ((x, s1), s)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (StateT $ \ s -> return ((x, s1), s)) s2
< = {-~  definition of |genS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (genS (x, s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (return (x, s1))) s2
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState ((\ s -> return (x, s)) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (StateT $ \ s -> return (x, s)) s1)) s2
< = {-~  definition of |genS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (genS x) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (hState (Var x)) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Var x)

%if False
$
%endif

For each following case of |t|, we assume that the continuation |t'| in |t| satisfies the equation |hStates' t' = (hState . states2state) t'|.

\noindent \mbox{\underline{case |t = Op (Inl (Get k))|}}
<    (hState . states2state) (Op (Inl (Get k)))
< = {-~  definition of |states2state|  -}
<    (hState . fold gen (alg1 # alg2 # fwd)) (Op (Inl (Get k)))
< = {-~  definition of |fold|  -}
<    hState $ (alg1 # alg2 # fwd) (fmap states2state (Inl (Get k)))
< = {-~  definition of |fmap|  -}
<    hState $ (alg1 # alg2 # fwd) (Inl (Get (states2state . k)))
< = {-~  definition of |(#)|  -}
<    hState $ alg1 (Get (states2state . k))
< = {-~  definition of |alg1|  -}
<    hState $ get' >>= \ (s1,  _) -> states2state (k s1)
< = {-~  definition of |get'|  -}
<    hState $ Op (Inl (Get return)) >>= \(s1, _) -> states2state (k s1)
< = {-~  definition of |(>>=)|  -}
<    hState (Op (Inl (Get (\ (s1, _) -> states2state (k s1)))))
< = {-~  definition of |hState|  -}
<    fold genS (algS # fwdS) $ Op (Inl (Get (\ (s1, _) -> states2state (k s1))))
< = {-~  definition of |fold|  -}
<    (algS # fwdS) (fmap hState (Inl (Get (\ (s1, _) -> states2state (k s1)))))
< = {-~  definition of |fmap|  -}
<    (algS # fwdS) (Inl (Get (\ (s1, _) -> hState (states2state (k s1)))))
< = {-~  definition of |(#)|  -}
<    algS (Get (\ (s1, _) -> hState (states2state (k s1))))
< = {-~  definition of |algS|  -}
<    StateT $ \s -> runStateT ((\ (s1, _) -> hState (states2state (k s1))) s) s
< = {-~  function application  -}
<    StateT $ \s -> runStateT ((\ (s1, _) -> hState (states2state (k s1))) s) s
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (s1, _) -> hState (states2state (k s1))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state (k s1))) (s1, s2)
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2) -> runStateT ((hState . states2state) (k s1)) (s1, s2)
< = {-~  induction hypothesis of continuation |k s1|  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' (k s1)) (s1, s2)
< = {-~  definition of |hStates'|, function application -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState (k s1)) s1)) s2) (s1, s2)
< = {-~  definition of |runStateT|, function application -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (hState (k s1)) s1)) s2
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState ((\s -> runStateT (hState (k s)) s) s1)) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (StateT $ \s -> runStateT (hState (k s)) s) s1)) s2
< = {-~  definition of |algS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (algS (Get (hState . k))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (hState (Op (Inl (Get k)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inl (Get k)))

\end{proof}