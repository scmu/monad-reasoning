\section{Equations of Interaction in Local-State Semantics: The Proofs}
\label{app:local-law}

In this section we prove two equations relevant to the interaction of nondeterminism and state in the local-state semantics.

\begin{theorem}
|get >> mzero = mzero|
\end{theorem}


\begin{proof}~

<    get >> mzero
< = {-~  definition of |>>|  -}
<    get >>= (\ s -> mzero)
< = {-~  Law (\ref{eq:put-right-identity})  -}
<    get >>= (\ s -> put s >> mzero)
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    (get >>= put) >> mzero
< = {-~  Law (\ref{eq:get-put})  -}
<    return () >> mzero
< = {-~  definition of |return| and |>>|  -}
<    mzero
\end{proof}

\begin{theorem}
|get >>= (\x -> k1 x `mplus` k2 x) = (get >>= k1) `mplus` (get >>= k2)|
\end{theorem}

\begin{proof}~

<    get >>= (\x -> k1 x `mplus` k2 x)
< = {-~  definition of |return|  -}
<    return () >> (get >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    (return () >> get) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:get-put})  -}
<    ((get >>= put) >> get) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    (get >>= (\ s -> put s >> get)) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    get >>= (\ s -> (\ s -> put s >> get) s >>= (\x -> k1 x `mplus` k2 x))
< = {-~  function application  -}
<    get >>= (\ s -> (put s >> get) >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:put-get})  -}
<    get >>= (\ s -> (put s >> return s) >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    get >>= (\ s -> put s >> (return s >>= (\x -> k1 x `mplus` k2 x)))
< = {-~  definition of |return| and |>>=|  -}
<    get >>= (\ s -> put s >> (k1 s `mplus` k2 s))
< = {-~  Law (\ref{eq:put-left-dist})  -}
<    get >>= (\ s -> (put s >> k1 s) `mplus` (put s >> k2 s))
< = {-~  definition of |return| and |>>=|  -}
<    get >>= (\ s -> (put s >> (return s >>= k1)) `mplus` (put s >> (return s >>= k2)))
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    get >>= (\ s -> ((put s >> return s) >>= k1) `mplus` ((put s >> return s) >>= k2))
< = {-~  Law (\ref{eq:put-get})  -}
<    get >>= (\ s -> ((put s >> get) >>= k1) `mplus` ((put s >> get) >>= k2))
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    get >>= (\ s -> (put s >> (get >>= k1)) `mplus` (put s >> (get >>= k2)))
< = {-~  Law (\ref{eq:put-left-dist})  -}
<    get >>= (\ s -> put s >> ((get >>= k1) `mplus` (get >>= k2)))
< = {-~  Law (\ref{eq:monad-assoc})  -}
<    (get >>= put) >> ((get >>= k1) `mplus` (get >>= k2))
< = {-~  Law (\ref{eq:get-put})  -}
<    return () >> ((get >>= k1) `mplus` (get >>= k2))
< = {-~  definition of |return| and |>>|  -}
<    (get >>= k1) `mplus` (get >>= k2)
\end{proof}