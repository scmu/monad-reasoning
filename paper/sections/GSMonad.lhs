%if False
\begin{code}
module GSMonad where
\end{code}
%endif

\section{An Implementation of the Semantical Domain}
\label{sec:GSMonad}

We present an implementation of |Dom| that satisfies the
axioms demanded by Section~\ref{sec:ctxt-trans}.
We let |Dom| be the union of |M s a| for all |a| and
for a given |s|.

\begin{figure}[H]
{\centering
\subfloat{
\begin{minipage}{0.3\textwidth}
\begin{code}
type M s a = s -> ([(a,s)],s)

fail :: M s a
fail = \s -> ([],s)

ret :: a -> M s a
ret x = \s -> ([(x,s)],s)

getD :: (s -> M s a) -> M s a
getD k = \s -> k s s

putD :: s -> M s a -> M s a
putD s k = \ _ -> k s

get :: M s s
get = getD ret

put :: s -> M s ()
put s = putD s (ret ())
\end{code}
\end{minipage}
} %subfloat1
\subfloat{
\begin{minipage}{0.3\textwidth}
\begin{code}
(<||>) :: M s a -> M s a -> M s a
(p <||> q) s0 =  let  (xs,s1)  = p s0
                      (ys,s2)  = p s1
                 in (xs ++ ys, s2)

(<&>) :: M s a -> M s a -> M s a
(p <&> q) s0 =  let  (xs,s1)  = p s0
                     (ys,s2)  = p s0
                in (xs ++ ys, s2)

run :: ntP -> M s a
run mzero          = fail
run (return x)     = ret x
run (p `mplus` q)  = run p <||> run q
run (Get k)        = getD (run . k)
run (Put s p)      = putD s (run p)
\end{code}
\end{minipage}
} %subfloat2
} %centering
\end{figure}
