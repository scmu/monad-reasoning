%if False
\begin{code}
\end{code}
%endif
\section{Proofs for the Final Simulation}
\label{app:final-simulate}

In this section, we prove the correctness of the final simulation in
\Cref{sec:final-simulate}.

\finalSimulate*

\begin{proof}
We calculate as follows, using all our three previous theorems
\Cref{thm:local-global}, \Cref{thm:nondet-state},
\Cref{thm:states-state}, and an auxiliary lemma \Cref{lemma:final1}.

<    simulate
< = {-~  definition of |simulate|  -}
<    extract . hState . states2state . nondet2state . comm2 . local2global
< = {-~  \Cref{thm:states-state}  -}
<    extract . flatten . hStates . nondet2state . comm2 . local2global
< = {-~  \Cref{lemma:final1}  -}
<    fmap (fmap fst) . runStateT . hState . extractSS . hState . nondet2state . comm2 . local2global
< = {-~  definition of |runNDf|  -}
<    fmap (fmap fst) . runStateT . hState . runNDf . comm2 . local2global
< = {-~  \Cref{thm:nondet-state}  -}
<    fmap (fmap fst) . runStateT . hState . hNDf . comm2 . local2global
< = {-~  definition of |hGlobal|  -}
<    hGlobal . local2global
< = {-~  \Cref{thm:local-global}  -}
<    hLocal
\end{proof}

\begin{lemma}\label{lemma:final1}
<    extract . flatten . hStates = fmap (fmap fst) . runStateT . hState . extractSS . hState
\end{lemma}

\begin{proof}
As shown in \Cref{app:states-state}, we can combine |flatten .
hStates| into one function |hStates'| defined as follows:
< hStates' :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT (s1, s2) (Free f) a
< hStates' t = StateT $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2

Then we show that for any input |t :: Free (StateF (SS (StateF s :+:
f) a) :+: (StateF s :+: f)) ()|, we have |(extract . hStates') t =
(fmap (fmap fst) . runStateT . hState . extractSS . hState) t| via the
following calculation.

<    (extract . hStates') t
< = {-~  function application  -}
<    extract (hStates' t)
< = {-~  definition of |hStates'|  -}
<    extract (StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (hState (runStateT (hState t) s1)) s2)
< = {-~  definition of |extract|  -}
<    \s -> resultsSS . fst . snd <$> runStateT (StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (hState (runStateT (hState t) s1)) s2) (SS [] [], s)
< = {-~  definition of |runStateT|  -}
<    \s -> resultsSS . fst . snd <$> (\ (s1, s2) -> alpha <$>
<      runStateT (hState (runStateT (hState t) s1)) s2) (SS [] [], s)
< = {-~  function application  -}
<    \s -> resultsSS . fst . snd <$> (alpha <$>
<      runStateT (hState (runStateT (hState t) (SS [] []))) s)
< = {-~  \Cref{eq:functor-composition}  -}
<    \s -> resultsSS . fst . snd . alpha <$>
<      runStateT (hState (runStateT (hState t) (SS [] []))) s
< = {-~  |fst . snd . alpha = snd . fst|  -}
<    \s -> resultsSS . snd . fst <$> runStateT (hState (runStateT (hState t) (SS [] []))) s
< = {-~  \Cref{eq:functor-composition} and definition of |<$>|  -}
<    \s -> fmap (resultsSS . snd) . fmap fst $
<      runStateT (hState (runStateT (hState t) (SS [] []))) s
< = {-~  definition of |flip| and reformulation  -}
<    \s -> fmap (resultsSS . snd) . fmap fst $
<      flip (runStateT . hState) s (runStateT (hState t) (SS [] []))
< = {-~  reformulation  -}
<    \s -> fmap (resultsSS . snd) . (fmap fst . flip (runStateT . hState) s) $
<      runStateT (hState t) (SS [] [])
< = {-~  parametricity of free monads -}
<    \s -> (fmap fst . flip (runStateT . hState) s) . fmap (resultsSS . snd) $
<      runStateT (hState t) (SS [] [])
< = {-~  definition of |<$>| -}
<    \s -> (fmap fst . flip (runStateT . hState) s) $ resultsSS . snd <$>
<      runStateT (hState t) (SS [] [])
< = {-~  function application -}
<    \s -> fmap fst (runStateT (hState (resultsSS . snd <$>
<      runStateT (hState t) (SS [] []))) s)
< = {-~  definition of |fmap| -}
<    \s -> fmap (fmap fst) (runStateT (hState (resultsSS . snd <$>
<      runStateT (hState t) (SS [] [])))) s
< = {-~  reformulation -}
<    \s -> (fmap (fmap fst) . runStateT . hState $ resultsSS . snd <$>
<      runStateT (hState t) (SS [] [])) s
< = {-~  |eta|-reduction  -}
<    fmap (fmap fst) . runStateT . hState $ resultsSS . snd <$> runStateT (hState t) (SS [] [])
< = {-~  definition of |extractSS|  -}
<    fmap (fmap fst) . runStateT . hState $ extractSS (hState t)
< = {-~    -}
<    (fmap (fmap fst) . runStateT . hState . extractSS . hState) t

Note that in the above calculation, we use the
parametricity~\citep{Reynolds83, Wadler89} of free monads which is
formally stated as follows:
< fmap f . g = g . fmap f
for any |g :: forall a . Free F a -> Free G a| with two functors |F|
and |G|.

\end{proof}
