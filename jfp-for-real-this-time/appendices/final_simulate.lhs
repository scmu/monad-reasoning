\section{Simulating Nondeterminism and State with Only State: The Proofs}
\label{app:final-simulate}

This section shows that |extract . simulate = hLocal|.

<    extract . simulate
< = {-~  definition of |simulate|  -}
<    extract . hState . states2state . nondet2state . comm2 . local2global
< = {-~  Theorem \ref{thm:states-state} and definition of |hStateTuple|  -}
<    extract . flatten . hStates . nondet2state . comm2 . local2global
< = {-~  Lemma \ref{thm:flatten-states}  -}
<    extract . hStates' . nondet2state . comm2 . local2global
< = {-~  Lemma \ref{thm:final1}  -}
<    fmap (fmap fst) . runStateT . hState . extractSS . hState . nondet2state . comm2 . local2global
< = {-~  definition of |runNDf|  -}
<    fmap (fmap fst) . runStateT . hState . runNDf . comm2 . local2global
< = {-~  Theorem \ref{thm:nondet-state}  -}
<    fmap (fmap fst) . runStateT . hState . hNDf . comm2 . local2global
< = {-~  definition of |hGlobal|  -}
<    hGlobal . local2global
< = {-~  Theorem \ref{thm:local-global}  -}
<    hLocal

\begin{lemma}\label{thm:final1}
<    extract . hStates' = fmap (fmap fst) . runStateT . hState . extractSS . hState
\end{lemma}

\begin{proof}~
<    extract . hStates' $ t
< = {-~  definition of |hStates'|  -}
<    (extract . (\t -> StateT $ \ (s1, s2) -> fmap alpha $ runStateT (hState (runStateT (hState t) s1)) s2)) t
< = {-~  definition of |extract|, function application  -}
<    \s -> resultsSS . fst . snd <$> runStateT
<      (StateT $ \ (s1, s2) -> fmap alpha $ runStateT (hState (runStateT (hState t) s1)) s2) (SS [] [], s)
< = {-~  definition of |runStateT|  -}
<    \s -> resultsSS . fst . snd <$> (\ (s1, s2) ->
<      fmap alpha $ runStateT (hState (runStateT (hState t) s1)) s2) (SS [] [], s)
< = {-~  function application  -}
<    \s -> resultsSS . fst . snd <$> (fmap alpha $ runStateT (hState (runStateT (hState t) (SS [] []))) s)
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    \s -> resultsSS . fst . snd . alpha <$> (runStateT (hState (runStateT (hState t) (SS [] []))) s)
< = {-~  |fst . snd . alpha = snd . fst|  -}
<    \s -> resultsSS . snd . fst <$> (runStateT (hState (runStateT (hState t) (SS [] []))) s)
< = {-~  reformulation  -}
<    \s -> fmap (resultsSS . snd . fst) $ (flip runStateT s . hState) $ runStateT (hState t) (SS [] [])
< = {-~  Law (\ref{eq:functor-composition}): composition of |fmap|  -}
<    \s -> fmap fst . (flip runStateT s . hState) $ fmap (resultsSS . snd) $ runStateT (hState t) (SS [] [])
< = {-~  definition of |fmap| and |eta|-reduction  -}
<    fmap (fmap fst) . runStateT . hState $ fmap (resultsSS . snd) $ runStateT (hState t) (SS [] [])
% < = {-~  definition of |<$>|  -}
% <    fmap (fmap fst) . runStateT . hState $ resultsSS . snd <$> runStateT (hState t) (SS [] [])
< = {-~  function application  -}
<    fmap (fmap fst) . runStateT . hState . (\x->resultsSS . snd <$> runStateT x (SS [] [])) . hState $ t
< = {-~  definition of |extractSS|  -}
<    fmap (fmap fst) . runStateT . hState . extractSS . hState
\end{proof}
