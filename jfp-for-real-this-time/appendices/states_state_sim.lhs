%if False
\begin{code}
\end{code}
%endif
\section{Proofs for Modelling Two States with One State}
\label{app:states-state}

In this section, we prove the following theorem in
\Cref{sec:multiple-states}.

\statesState*

\begin{proof}
Instead of proving it directly, we show the correctness of the
isomorphism of |nest| and |flatten|, and prove the following equation:
< flatten . hStates = hState . states2state
%
It is obvious that |alpha| and |alpha1| form an isomorphism, i.e.,
|alpha . alpha1 = id| and |alpha1 . alpha = id|. We show that |nest|
and |flatten| form an isomorphism by calculation.
%
For all |t :: StateT s1 (StateT s2 (Free f)) a|, we show that |(nest .
flatten) t = t|.

<    (nest . flatten) t
< = {-~  definition of |flatten|  -}
<    nest $ StateT $ \ (s1, s2) -> alpha <$> runStateT (runStateT t s1) s2
< = {-~  definition of |nest|  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$>
<      runStateT (StateT $ \ (s1, s2) -> alpha <$> runStateT (runStateT t s1) s2) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$>
<      (\ (s1, s2) -> alpha <$> runStateT (runStateT t s1) s2) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> (alpha <$> runStateT (runStateT t s1) s2)
< = {-~  \Cref{eq:functor-composition}  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> (fmap (alpha1 . alpha) (runStateT (runStateT t s1) s2))
< = {-~  |alpha1 . alpha = id|  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> (fmap id (runStateT (runStateT t s1) s2))
< = {-~  \Cref{eq:functor-identity}  -}
<    StateT $ \ s1 -> StateT $ \ s2 -> (runStateT (runStateT t s1) s2)
< = {-~  |eta|-reduction and reformulation  -}
<    StateT $ \ s1 -> (StateT . runStateT) (runStateT t s1)
< = {-~  |StateT . runStateT = id|  -}
<    StateT $ \ s1 -> runStateT t s1
< = {-~  |eta|-reduction  -}
<    StateT $ runStateT t
< = {-~  |StateT . runStateT = id|  -}
<    t

For all |t :: StateT (s1, s2) (Free f) a|, we show that |(flatten .
nest) t = t|.

<    (flatten . nest) t = t
< = {-~  definition of |nest|  -}
<    flatten $ StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)
< = {-~  definition of |flatten|  -}
<    StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (runStateT (StateT $ \ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)) s1) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> alpha <$>
<      runStateT ((\ s1 -> StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)) s1) s2
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> alpha <$> runStateT (StateT $ \ s2 -> alpha1 <$> runStateT t (s1, s2)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> alpha <$> (\ s2 -> alpha1 <$> runStateT t (s1, s2)) s2
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> alpha <$> (alpha1 <$> runStateT t (s1, s2))
< = {-~  definition of |<$>|  -}
<    StateT $ \ (s1, s2) -> fmap alpha (fmap alpha1 (runStateT t (s1, s2)))
< = {-~  \Cref{eq:functor-composition}  -}
<    StateT $ \ (s1, s2) -> fmap (alpha . alpha1) (runStateT t (s1, s2))
< = {-~  |alpha . alpha1 = id|  -}
<    StateT $ \ (s1, s2) -> fmap id (runStateT t (s1, s2))
< = {-~  \Cref{eq:functor-identity}  -}
<    StateT $ \ (s1, s2) -> runStateT t (s1, s2)
< = {-~  |eta|-reduction  -}
<    StateT $ runStateT t
< = {-~  |StateT . runStateT = id|  -}
<    t

Then, we first calculate the LHS |flatten . hStates| into one function
|hStates'| which is defined as
< hStates' :: Functor f => Free (StateF s1 :+: StateF s2 :+: f) a -> StateT (s1, s2) (Free f) a
< hStates' t = StateT $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2
%
For all |t :: Free (StateF s1 :+: StateF s2 :+: f) a|, we show the equation
|(flatten . hStates) t = hStates' t| by the following calculation.

<    (flatten . hStates) t
< = {-~  definition of |hStates|  -}
<    (flatten . (\ t -> StateT (hState . runStateT (hState t)))) t
< = {-~  function application  -}
<    flatten (StateT (hState . runStateT (hState t)))
< = {-~  definition of |flatten|  -}
<    StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (runStateT (StateT (hState . runStateT (hState t))) s1) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> alpha <$>
<      runStateT ((hState . runStateT (hState t)) s1) s2
< = {-~  definition of |hStates'|  -}
< hStates' t

Now we only need to show that for any input |t :: Free (StateF s1 :+:
StateF s2 :+: f) a|, the equation |hStates' t = (hState .
states2state) t| holds.  We proceed by induction on |t|.
%
% For the base case where |t = Var x|, we calculate as follows.

\noindent \mbox{\underline{case |t = Var x|}}
<    (hState . states2state) (Var x)
< = {-~  definition of |states2state|  -}
<    hState (Var x)
< = {-~  definition of |hState|  -}
<   StateT $ \ s -> return (x, s)
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> Var (x, (s1, s2))
< = {-~  definition of |alpha|  -}
<    StateT $ \ (s1, s2)  ->  Var (alpha ((x, s1), s2))
< = {-~  definition of |fmap|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ Var ((x, s1), s2)
< = {-~  definition of |return|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ return ((x, s1), s2)
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ (\ s -> return ((x, s1), s)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ runStateT (StateT $ \ s -> return ((x, s1), s)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ runStateT (hState (return (x, s1))) s2
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ runStateT (hState ((\ s -> return (x, s)) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ runStateT (hState (runStateT (StateT $ \ s -> return (x, s)) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  fmap alpha $ runStateT (hState (runStateT (hState (Var x)) s1)) s2
< = {-~  definition of |<$>|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (hState (Var x)) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Var x)

% There are five inductive cases of |t|, for each case the induction
% hypothesis states that the continuation |k| in |t| satisfies the
% equation |hStates' k = (hState . states2state) k|.  We show the
% induction hypothesis in detail at the beginning of each case.

\noindent \mbox{\underline{case |t = Op (Inl (Get k))|}}

Induction hypothesis: |hStates' (k s) = (hState .  states2state) (k
s)| for any |s|.

<    (hState . states2state) (Op (Inl (Get k)))
< = {-~  definition of |states2state|  -}
<    hState $ get >>= \ (s1,  _) -> states2state (k s1)
< = {-~  definition of |get|  -}
<    hState $ Op (Inl (Get return)) >>= \ (s1, _) -> states2state (k s1)
< = {-~  definition of |(>>=)|  -}
<    hState (Op (Inl (Get (\ (s1, _) -> states2state (k s1)))))
< = {-~  definition of |hState|  -}
<    StateT $ \s -> runStateT ((\ (s1, _) -> hState (states2state (k s1))) s) s
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (s1, _) -> hState (states2state (k s1))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state (k s1))) (s1, s2)
< = {-~  induction hypothesis  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' (k s1)) (s1, s2)
< = {-~  definition of |hStates'|  -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (k s1)) s1)) s2) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (k s1)) s1)) s2) (s1, s2)
< = {-~  function application -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (hState (k s1)) s1)) s2
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState ((\s -> runStateT (hState (k s)) s) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (StateT $ \s -> runStateT (hState (k s)) s) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (hState (Op (Inl (Get k)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inl (Get k)))

\noindent \mbox{\underline{case |t = Op (Inl (Put s k))|}}

Induction hypothesis: |hStates' k = (hState . states2state) k|.

<    (hState . states2state) (Op (Inl (Put s k)))
< = {-~  definition of |states2state|  -}
<    hState $ get >>= \ (_, s2)  -> put (s, s2) >> (states2state k)
< = {-~  definition of |get| and |put|  -}
<    hState $ Op (Inl (Get return)) >>= \ (_, s2) -> Op (Inl (Put (s, s2) (return ()))) >> (states2state k)
< = {-~  definition of |(>>=)| and |(>>)|  -}
<    hState $ Op (Inl (Get (\ (_, s2) -> Op (Inl (Put (s, s2) (states2state k))))))
< = {-~  definition of |hState|  -}
<    algS (Get (\ (_, s2) -> hState (Op (Inl (Put (s, s2) (states2state k))))))
< = {-~  definition of |algS|  -}
<    StateT $ \ s' -> runStateT
<      ((\ (_, s2) -> hState (Op (Inl (Put (s, s2) (states2state k))))) s') s'
< = {-~  let |s' = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT
<      ((\ (_, s2) -> hState (Op (Inl (Put (s, s2) (states2state k))))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT
<      (hState (Op (Inl (Put (s, s2) (states2state k))))) (s1, s2)
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2) -> runStateT
<      (StateT $ \ _ -> runStateT (hState (states2state k)) (s, s2)) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> (\ _ -> runStateT (hState (states2state k)) (s, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state k)) (s, s2)
< = {-~  induction hypothesis  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' k) (s, s2)
< = {-~  definition of |hStates'| -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2) -> alpha <$>
<       runStateT (hState (runStateT (hState k) s1)) s2) (s, s2)
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState k) s1)) s2) (s, s2)
< = {-~  function application -}
<    StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (hState (runStateT (hState k) s)) s2
< = {-~  |beta|-expansion -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState ((\s' -> runStateT (hState k) s) s1)) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (StateT $ \s' -> runStateT (hState k) s) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (Op (Inl (Put s k)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inl (Put s k)))

\noindent \mbox{\underline{case |t = Op (Inr (Inl (Get k)))|}}

Induction hypothesis: |hStates' (k s) = (hState . states2state) (k s)|
for any |s|.

<    (hState . states2state) (Op (Inr (Inl (Get k))))
< = {-~  definition of |states2state|  -}
<    hState $ get >>= \ (_,  s2) -> states2state (k s2)
< = {-~  definition of |get|  -}
<    hState $ Op (Inl (Get return)) >>= \ (_, s2) -> states2state (k s2)
< = {-~  definition of |(>>=)| for free monad  -}
<    hState (Op (Inl (Get (\ (_, s2) -> states2state (k s2)))))
< = {-~  definition of |hState|  -}
<    StateT $ \s -> runStateT ((\ (_, s2) -> hState (states2state (k s2))) s) s
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT ((\ (_, s2) -> hState (states2state (k s2))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state (k s2))) (s1, s2)
< = {-~  induction hypothesis  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' (k s2)) (s1, s2)
< = {-~  definition of |hStates'| -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (k s2)) s1)) s2) (s1, s2)
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (k s2)) s1)) s2) (s1, s2)
< = {-~  function application -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (k s2)) s1)) s2
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      (runStateT ((hState . (\k -> runStateT k s1) . hState . k) s2) s2)
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      (\s -> runStateT ((hState . (\k -> runStateT k s1) . hState . k) s) s) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (StateT $ \s -> runStateT ((hState . (\k -> runStateT k s1) . hState . k) s) s) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (Op (Inl (Get ((\k -> runStateT k s1) . hState . k))))) s2
< = {-~  definition of |fmap|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (Op $ fmap (\k -> runStateT k s1) (Inl (Get (hState . k))))) s2
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState ((\s -> Op $ fmap (\k -> runStateT k s) (Inl (Get (hState . k)))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState
<      (runStateT (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (Inl (Get (hState . k)))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (Op (Inr (Inl (Get k))))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inl (Get k))))

\noindent \mbox{\underline{case |t = Op (Inr (Inl (Put s k)))|}}

Induction hypothesis: |hStates' k = (hState . states2state) k|.

<    (hState . states2state) (Op (Inr (Inl (Put s k))))
< = {-~  definition of |states2state|  -}
<    hState $ get >>= \ (s1, _) -> put (s1, s) >> (states2state k)
< = {-~  definition of |get| and |put|  -}
<    hState $ Op (Inl (Get return)) >>= \ (s1, _) -> Op (Inl (Put (s1, s) (return ()))) >> (states2state k)
< = {-~  definition of |(>>=)| and |(>>)|  -}
<    hState $ Op (Inl (Get (\ (s1, _) -> Op (Inl (Put (s1, s) (states2state k))))))
< = {-~  definition of |hState|  -}
<    StateT $ \ s' -> runStateT
<      ((\ (s1, _) -> hState (Op (Inl (Put (s1, s) (states2state k))))) s') s'
< = {-~  let |s' = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> runStateT
<      ((\ (s1, _) -> hState (Op (Inl (Put (s1, s) (states2state k))))) (s1, s2)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT
<      (hState (Op (Inl (Put (s1, s) (states2state k))))) (s1, s2)
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $
<      \s' -> runStateT (hState (states2state k)) (s1, s)) (s1, s2)
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2) -> (\s' -> runStateT (hState (states2state k)) (s1, s)) (s1, s2)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> runStateT (hState (states2state k)) (s1, s)
< = {-~  induction hypothesis  -}
<    StateT $ \ (s1, s2) -> runStateT (hStates' k) (s1, s)
< = {-~  definition of |hStates'| -}
<    StateT $ \ (s1, s2) -> runStateT (StateT $ \ (s1, s2) -> alpha <$>
<      runStateT (hState (runStateT (hState k) s1)) s2) (s1, s)
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2) -> (\ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState k) s1)) s2) (s1, s)
< = {-~  function application -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState k) s1)) s
< = {-~  |beta|-expansion -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      (\ s' -> runStateT (hState (runStateT (hState k) s1)) s) s2
< = {-~  definition of |runStateT| -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (StateT $ \ s' -> runStateT (hState (runStateT (hState k) s1)) s) s2
< = {-~  definition of |hState| -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (Op (Inl (Put s (runStateT (hState k) s1))))) s2
< = {-~  reformulation -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (Op (Inl (Put s ((\k -> runStateT k s1) (hState k)))))) s2
< = {-~  definition of |fmap| -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (Op $ fmap (\k -> runStateT k s1) (Inl (Put s (hState k))))) s2
< = {-~  |beta|-expansion -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT
<      (hState ((\s' -> Op $ fmap (\k -> runStateT k s') (Inl (Put s (hState k)))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (StateT $
<      \s' -> Op $ fmap (\k -> runStateT k s') (Inl (Put s (hState k)))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (Op (Inr (Inl (Put s k))))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inl (Put s k))))

\noindent \mbox{\underline{case |t = Op (Inr (Inr y))|}}

Induction hypothesis: |hStates' y = (hState . states2state) y|.

<    (hState . states2state) (Op (Inr (Inr y)))
< = {-~  definition of |states2state|  -}
<    hState $ Op (Inr (fmap states2state y))
< = {-~  definition of |hState|  -}
<    fwdS (fmap (hState . states2state) y)
< = {-~  induction hypothesis  -}
<    fwdS (fmap hStates' y)
< = {-~  definition of |hStates'|  -}
<    fwdS (fmap (\t -> StateT
<      $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (hState t) s1)) s2) y)
< = {-~  definition of |fwdS|  -}
<    StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap (\t -> StateT
<      $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2) y)
< = {-~  \Cref{eq:functor-composition}  -}
<    StateT $ \s -> Op (fmap ((\k -> runStateT k s) . (\t -> StateT
<      $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2)) y)
< = {-~  reformulation  -}
<    StateT $ \s -> Op (fmap (\ t -> runStateT (StateT
<      $ \ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2) s) y)
< = {-~  definition of |runStateT|  -}
<    StateT $ \s -> Op (fmap (\t ->
<      (\ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2) s) y)
< = {-~  let |s = (s1, s2)|  -}
<    StateT $ \ (s1, s2) -> Op (fmap (\t ->
<      (\ (s1, s2) -> alpha <$> runStateT (hState (runStateT (hState t) s1)) s2) (s1, s2)) y)
< = {-~  function application  -}
<    StateT $ \ (s1, s2) -> Op (fmap (\t -> alpha <$>
<       runStateT (hState (runStateT (hState t) s1)) s2) y)
< = {-~  reformulation  -}
<    StateT $ \ (s1, s2) -> Op (fmap (alpha <$>
<      . (\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
< = {-~  definition of |<$>|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      Op (fmap ((\k -> runStateT k s2) . hState . (\k -> runStateT k s1) . hState) y)
< = {-~  \Cref{eq:functor-composition}  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      Op $ fmap (\k -> runStateT k s2) (fmap (hState . (\k -> runStateT k s1) . hState) y)
< = {-~  |beta|-expansion  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> (\s -> Op $
<      fmap (\k -> runStateT k s) (fmap (hState . (\k -> runStateT k s1) . hState) y)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (StateT $ \s -> Op $
<      fmap (\k -> runStateT k s) (fmap (hState . (\k -> runStateT k s1) . hState) y)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT
<      (hState (Op (Inr (fmap ((\k -> runStateT k s1) . hState) y)))) s2
< = {-~  \Cref{eq:functor-composition}  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT
<      (hState (Op (Inr (fmap (\k -> runStateT k s1) (fmap hState y))))) s2
< = {-~  definition of |fmap| -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT
<      (hState (Op $ fmap (\k -> runStateT k s1) (Inr (fmap hState y)))) s2
< = {-~  |beta|-expansion -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState
<      ((\s -> Op $ fmap (\k -> runStateT k s) (Inr (fmap hState y))) s1)) s2
< = {-~  definition of |runStateT|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$> runStateT (hState (runStateT (StateT $
<      \s -> Op $ fmap (\k -> runStateT k s) (Inr (fmap hState y))) s1)) s2
< = {-~  definition of |hState|  -}
<    StateT $ \ (s1, s2)  ->  alpha <$>
<      runStateT (hState (runStateT (hState (Op (Inr (Inr y)))) s1)) s2
< = {-~  definition of |hStates'|  -}
<    hStates' (Op (Inr (Inr y)))

\end{proof}
