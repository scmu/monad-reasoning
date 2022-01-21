\section{Equations of Interaction in Local-State Semantics: The Proofs}
\label{app:local-law}

In this section we prove two equations relevant to the interaction of nondeterminism and state in the local-state semantics.

\begin{theorem}
|get >> mzero = mzero|
\end{theorem}


\begin{proof}~

<    get >> mzero
< = {-~  definition of |(>>)|  -}
<    get >>= (\ s -> mzero)
< = {-~  Law (\ref{eq:put-right-identity}): put-right-identity  -}
<    get >>= (\ s -> put s >> mzero)
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
<    (get >>= put) >> mzero
< = {-~  Law (\ref{eq:get-put}): get-put  -}
<    return () >> mzero
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
<    mzero
\end{proof}

% Another proof without using law \ref{eq:put-right-identity} for local-state semantics.
%
% <    get >> mzero
% < = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
% <    return () >> (get >> mzero)
% < = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
% <    (return () >> get) >> mzero
% < = {-~  Law (\ref{eq:get-put}): get-put  -}
% <    ((get >>= put) >> get) >> mzero
% < = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)|  -}
% <    (get >>= (\ s -> put s >> get)) >> mzero
% < = {-~  Law (\ref{eq:put-get}): put-get  -}
% <    (get >>= (\ s -> put s >> return s)) >> mzero
% < = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)|  -}
% <    ((get >>= put) >> return s) >> mzero
% < = {-~  Law (\ref{eq:get-put}): get-put  -}
% <    (return () >> return s) >> mzero
% < = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
% <    return s >> mzero
% < = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
% <    mzero

\begin{theorem}
|get >>= (\x -> k1 x `mplus` k2 x) = (get >>= k1) `mplus` (get >>= k2)|
\end{theorem}

\begin{proof}~

<    get >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
<    return () >> (get >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)|  -}
<    (return () >> get) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:get-put}): get-put  -}
<    ((get >>= put) >> get) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
<    (get >>= (\ s -> put s >> get)) >>= (\x -> k1 x `mplus` k2 x)
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)|  -}
<    get >>= (\ s -> (\ s -> put s >> get) s >>= (\x -> k1 x `mplus` k2 x))
< = {-~  function application  -}
<    get >>= (\ s -> (put s >> get) >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:put-get}): put-get  -}
<    get >>= (\ s -> (put s >> return s) >>= (\x -> k1 x `mplus` k2 x))
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
<    get >>= (\ s -> put s >> (return s >>= (\x -> k1 x `mplus` k2 x)))
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and function application  -}
<    get >>= (\ s -> put s >> (k1 s `mplus` k2 s))
< = {-~  Law (\ref{eq:put-left-dist}): put-left-distributivity  -}
<    get >>= (\ s -> (put s >> k1 s) `mplus` (put s >> k2 s))
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind (twice) -}
<    get >>= (\ s -> (put s >> (return s >>= k1)) `mplus` (put s >> (return s >>= k2)))
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
<    get >>= (\ s -> ((put s >> return s) >>= k1) `mplus` ((put s >> return s) >>= k2))
< = {-~  Law (\ref{eq:put-get}): put-get  -}
<    get >>= (\ s -> ((put s >> get) >>= k1) `mplus` ((put s >> get) >>= k2))
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>)|  -}
<    get >>= (\ s -> (put s >> (get >>= k1)) `mplus` (put s >> (get >>= k2)))
< = {-~  Law (\ref{eq:put-left-dist}): put-left-distributivity  -}
<    get >>= (\ s -> put s >> ((get >>= k1) `mplus` (get >>= k2)))
< = {-~  Law (\ref{eq:monad-assoc}): associativity of |(>>=)|  -}
<    (get >>= put) >> ((get >>= k1) `mplus` (get >>= k2))
< = {-~  Law (\ref{eq:get-put}): get-put -}
<    return () >> ((get >>= k1) `mplus` (get >>= k2))
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind and definition of |(>>)|  -}
<    (get >>= k1) `mplus` (get >>= k2)
\end{proof}
