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

\noindent \mbox{\underline{case |t = Op (Inl (Put s k))|}}
<    (hState . states2state) (Op (Inl (Put s k)))
< = {-~  definition of |states2state|  -}
<    (hState . fold gen (alg1 # alg2 # fwd)) (Op (Inl (Put s k)))
< = {-~  definition of |fold|  -}
<    hState $ (alg1 # alg2 # fwd) (fmap states2state (Inl (Put s k)))
< = {-~  definition of |fmap|  -}
<    hState $ (alg1 # alg2 # fwd) (Inl (Put s (states2state k)))
< = {-~  definition of |(#)|  -}
<    hState $ alg1 (Put s (states2state k))
< = {-~  definition of |alg1|  -}
<    hState $ get' >>= \ (_,   s2)  -> put' (s, s2) (states2state k)
< = {-~  definition of |get'| and |put'|  -}
<    hState $ Op (Inl (Get return)) >>= \(_, s2) -> Op (Inl (Put (s, s2) (states2state k)))
< = {-~  definition of |(>>=)|  -}
<    hState $ Op (Inl (Get (\ (_, s2) -> Op (Inl (Put (s, s2) (states2state k))))))
< = {-~  definition of |hState|  -}
<    algS (Get (\ (_, s2) -> hState (Op (Inl (Put (s, s2) (hState (states2state k))))))
< = {-~  definition of |algS|  -}
<    StateT $ \ s' -> runStateT ((\ (_, s2) -> hState (Op (Inl (Put (s, s2) (states2state k))))) s') s'
< = {-~  let |s' = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (_, s2) -> hState (Op (Inl (Put (s, s2) (states2state k))))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (Op (Inl (Put (s, s2) (states2state k))))) (s1, s2)
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2) -> runStateT (algS (Put (s, s2) (hState (states2state k)))) (s1, s2)
< = {-~  definition of |algS|  -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ s' -> runStateT (hState (states2state k)) (s, s2)) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> (\ s' -> runStateT (hState (states2state k)) (s, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state k)) (s, s2)
< = {-~  induction hypothesis of continuation |k|  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' k) (s, s2)
< = {-~  definition of |hStates'| -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
<       $ runStateT (hState (runStateT (hState k) s1)) s2) (s, s2)
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                                        $   runStateT (hState (runStateT (hState k) s1)) s2) (s, s2)
< = {-~  function application -}
<    StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (runStateT (hState k) s)) s2
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState ((\s' -> runStateT (hState k) s) s1)) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (StateT $ \s' -> runStateT (hState k) s) s1)) s2
< = {-~  definition of |algS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (algS (Put s (hState k))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (hState (Op (Inl (Put s k)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inl (Put s k)))

%if False
$
%endif

\noindent \mbox{\underline{case |t = Op (Inr (Inl (Get k)))|}}
<    (hState . states2state) (Op (Inr (Inl (Get k))))
< = {-~  definition of |states2state|  -}
<    (hState . fold gen (alg1 # alg2 # fwd)) (Op (Inr (Inl (Get k))))
< = {-~  definition of |fold|  -}
<    hState $ (alg1 # alg2 # fwd) (fmap states2state (Inr (Inl (Get k))))
< = {-~  definition of |fmap|  -}
<    hState $ (alg1 # alg2 # fwd) (Inr (Inl (Get (states2state . k))))
< = {-~  definition of |(#)|  -}
<    hState $ alg2 (Get (states2state . k))
< = {-~  definition of |alg2|  -}
<    hState $ get' >>= \ (_,  s2) -> states2state (k s2)
< = {-~  definition of |get'|  -}
<    hState $ Op (Inl (Get return)) >>= \ (_, s2) -> states2state (k s2)
< = {-~  definition of |(>>=)|  -}
<    hState (Op (Inl (Get (\ (_, s2) -> states2state (k s2)))))
< = {-~  definition of |hState|  -}
<    algS (Get (\ (_, s2) -> hState (states2state (k s2))))
< = {-~  definition of |algS|  -}
<    StateT $ \s -> runStateT ((\ (_, s2) -> hState (states2state (k s2))) s) s
< = {-~  function application  -}
<    StateT $ \s -> runStateT ((\ (_, s2) -> hState (states2state (k s2))) s) s
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (_, s2) -> hState (states2state (k s2))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state (k s2))) (s1, s2)
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2) -> runStateT ((hState . states2state) (k s2)) (s1, s2)
< = {-~  induction hypothesis of continuation |k s2|  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' (k s2)) (s1, s2)
< = {-~  definition of |hStates'|, function application -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState (k s2)) s1)) s2) (s1, s2)
< = {-~  definition of |runStateT|, function application -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                         $   runStateT (hState (runStateT (hState (k s2)) s1)) s2
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ (runStateT ((hState . (\k -> runStateT k s1) . hState . k) s2) s2)
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ (\s -> runStateT ((hState . (\k -> runStateT k s1) . hState . k) s) s) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (StateT $ \s -> runStateT ((hState . (\k -> runStateT k s1) . hState . k) s) s) s2
< = {-~  definition of |algS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (algS (Get (hState . (\k -> runStateT k s1) . hState . k))) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (Op (Inl (Get ((\k -> runStateT k s1) . hState . k))))) s2
< = {-~  definition of |($)|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (Op $ (Inl (Get ((\k -> runStateT k s1) . hState . k))))) s2
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState ((\s -> Op $ (Inl (Get ((\k -> runStateT k s) . hState . k)))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT 
<      (hState (runStateT (StateT $ \s -> Op $ (Inl (Get ((\k -> runStateT k s) . hState . k)))) s1)) s2
< = {-~  definition of |fmap|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT 
<      (hState (runStateT (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (Inl (Get (hState . k)))) s1)) s2
< = {-~  definition of |fwdS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT 
<      (hState (runStateT (fwdS (Inl (Get (hState . k)))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT 
<      (hState (runStateT (hState (Op (Inr (Inl (Get k))))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inl (Get k))))

\noindent \mbox{\underline{case |t = Op (Inr (Inl (Put s k)))|}}
<    (hState . states2state) (Op (Inr (Inl (Put s k))))
< = {-~  definition of |states2state|  -}
<    (hState . fold gen (alg1 # alg2 # fwd)) (Op (Inr (Inl (Put s k))))
< = {-~  definition of |fold|  -}
<    hState $ (alg1 # alg2 # fwd) (fmap states2state (Inr (Inl (Put s k))))
< = {-~  definition of |fmap|  -}
<    hState $ (alg1 # alg2 # fwd) (Inr (Inl (Put s (states2state k))))
< = {-~  definition of |(#)|  -}
<    hState $ alg2 (Put s (states2state k))
< = {-~  definition of |alg2|  -}
<    hState $ get' >>= \ (s1, _) -> put' (s1, s) (states2state k)
< = {-~  definition of |get'| and |put'|  -}
<    hState $ Op (Inl (Get return)) >>= \ (s1, _) -> Op (Inl (Put (s1, s) (states2state k)))
< = {-~  definition of |(>>=)|  -}
<    hState $ Op (Inl (Get (\ (s1, _) -> Op (Inl (Put (s1, s) (states2state k))))))
< = {-~  definition of |hState|  -}
<    algS (Get (\ (s1, _) -> hState (Op (Inl (Put (s1, s) (hState (states2state k)))))))
< = {-~  definition of |algS|  -}
<    StateT $ \ s' -> runStateT ((\ (s1, _) -> hState (Op (Inl (Put (s1, s) (states2state k))))) s') s'
< = {-~  let |s' = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (s1, _) -> hState (Op (Inl (Put (s1, s) (states2state k))))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (Op (Inl (Put (s1, s) (states2state k))))) (s1, s2)
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2) -> runStateT (algS (Put (s1, s) (hState (states2state k)))) (s1, s2)
< = {-~  definition of |algS|  -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \s' -> runStateT (hState (states2state k)) (s1, s)) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> (\s' -> runStateT (hState (states2state k)) (s1, s)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state k)) (s1, s)
< = {-~  induction hypothesis of continuation |k|  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' k) (s1, s)
< = {-~  definition of |hStates'| -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
<       $ runStateT (hState (runStateT (hState k) s1)) s2) (s1, s)
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                                        $   runStateT (hState (runStateT (hState k) s1)) s2) (s1, s)
< = {-~  function application -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (runStateT (hState k) s1)) s
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $
<      (\ s' -> runStateT (hState (runStateT (hState k) s1)) s) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (StateT $ \ s' -> runStateT (hState (runStateT (hState k) s1)) s) s2
< = {-~  definition of |algS| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (algS (Put s (hState (runStateT (hState k) s1)))) s2
< = {-~  definition of |hState| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op (Inl (Put s (runStateT (hState k) s1))))) s2
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op (Inl (Put s ((\k -> runStateT k s1) (hState k)))))) s2
< = {-~  definition of |($)| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op $ (Inl (Put s ((\k -> runStateT k s1) (hState k)))))) s2
< = {-~  definition of |fmap| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op $ fmap (\k -> runStateT k s1) (Inl (Put s (hState k))))) s2
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState ((\s' -> Op $ fmap (\k -> runStateT k s') (Inl (Put s (hState k)))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (StateT $ \s' -> Op $ fmap (\k -> runStateT k s') (Inl (Put s (hState k)))) s1)) s2
< = {-~  definition of |fwdS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (fwdS (Inl (Put s (hState k)))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (hState (Op (Inr (Inl (Put s k))))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inl (Put s k))))

\noindent \mbox{\underline{case |t = Op (Inr (Inr y))|}}
<    (hState . states2state) (Op (Inr (Inr y)))
< = {-~  definition of |states2state|  -}
<    (hState . fold gen (alg1 # alg2 # fwd)) (Op (Inr (Inr y)))
< = {-~  definition of |fold|  -}
<    hState $ (alg1 # alg2 # fwd) (fmap states2state (Inr (Inr y)))
< = {-~  definition of |fmap|  -}
<    hState $ (alg1 # alg2 # fwd) (Inr (Inr (fmap states2state y)))
< = {-~  definition of |(#)|  -}
<    hState $ fwd (fmap states2state y)
< = {-~  definition of |fwd|  -}
<    hState $ Op (Inr (fmap states2state y))
< = {-~  definition of |hState|  -}
<    fwdS (fmap (hState . states2state) y)
< = {-~  induction hypothesis of continuation in |y|  -}
<    fwdS (fmap hStates' y)
< = {-~  definition of |hStates'|  -}
<    fwdS (fmap (\t -> StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y)))
<                                     $   runStateT (hState (runStateT (hState t) s1)) s2) y)
< = {-~  definition of |fwdS|  -}
<    StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap (\t -> StateT
<      $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (runStateT (hState t) s1)) s2) y)
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition})  -}
<    StateT $ \s -> Op $ (fmap ((\k -> runStateT k s) . (\t -> StateT
<      $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT (hState (runStateT (hState t) s1)) s2)) y)
< = {-~  reformulation  -}
<    StateT $ \s -> Op $ (fmap (\t -> runStateT (StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState t) s1)) s2) s) y)
< = {-~  definition of |runStateT|  -}
<    StateT $ \s -> Op $ (fmap (\t -> (\ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState t) s1)) s2) s) y)
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> Op $ (fmap (\t -> (\ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState t) s1)) s2) (s1, s2)) y)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> Op $ (fmap (\t -> (fmap (\ ((a, x), y) -> (a, (x, y)))
<      $ runStateT (hState (runStateT (hState t) s1)) s2)) y)
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2) -> Op (fmap (fmap (\ ((a, x), y) -> (a, (x, y)))
<      . (\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
< = {-~  definition of |fmap|  -}
<    StateT $ \ (s1, s2) -> fmap (\ ((a, x), y) -> (a, (x, y))) $
<      Op (fmap ((\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
< = {-~  definition of |($)|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $
<      Op $ (fmap ((\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition})  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $
<      Op $ fmap (\k -> runStateT k s2) (fmap (hState . (\k -> runStateT k s1) . hState) y)
< = {-~  |eta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $
<      (\s -> Op $ fmap (\k -> runStateT k s) (fmap (hState . (\k -> runStateT k s1) . hState) y)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap (hState . (\k -> runStateT k s1) . hState) y)) s2
< = {-~  definition of |fwdS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (fwdS (fmap (hState . (\k -> runStateT k s1) . hState) y)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op (Inr (fmap ((\k -> runStateT k s1) . hState) y)))) s2
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition})  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op (Inr (fmap (\k -> runStateT k s1) (fmap hState y))))) s2
< = {-~  definition of |($)| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op $ (Inr (fmap (\k -> runStateT k s1) (fmap hState y))))) s2
< = {-~  definition of |fmap| -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (Op $ fmap (\k -> runStateT k s1) (Inr (fmap hState y)))) s2
< = {-~  |eta|-expansion -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState ((\s -> Op $ fmap (\k -> runStateT k s) (Inr (fmap hState y))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (Inr (fmap hState y))) s1)) s2
< = {-~  definition of |fwdS|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (fwdS (Inr (fmap hState y))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap (\ ((a, x), y) -> (a, (x, y))) $ runStateT
<      (hState (runStateT (hState (Op (Inr (Inr y)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inr y)))

Therefore, |hStates' t = (hState . states2state) t| holds for any |t :: Free (StateF s1 :+: StateF s2 :+: f) a|.
\end{proof}