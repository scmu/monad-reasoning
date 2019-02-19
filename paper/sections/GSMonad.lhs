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

{
\setlength{\columnsep}{-4cm}
\begin{multicols}{2}
\begin{samepage}
\begin{code}
type M s a = s -> ([(a,s)],s)

fail :: M s a
fail = \s -> ([],s)
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
ret :: a -> M s a
ret x = \s -> ([(x,s)],s)
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
getD :: (s -> M s a) -> M s a
getD k = \s -> k s s
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
putD :: s -> M s a -> M s a
putD s k = \ _ -> k s
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
get :: M s s
get = getD ret
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
put :: s -> M s ()
put s = putD s (ret ())
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
(<||>) :: M s a -> M s a -> M s a
(p <||> q) s0 =  let  (xs,s1)  = p s0
                      (ys,s2)  = p s1
                 in (xs ++ ys, s2)
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
(<&>) :: M s a -> M s a -> M s a
(p <&> q) s0 =  let  (xs,s1)  = p s0
                     (ys,s2)  = p s0
                in (xs ++ ys, s2)
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
run :: ntP -> M s a
run mzero          = fail
run (return x)     = ret x
run (p `mplus` q)  = run p <||> run q
run (Get k)        = getD (run . k)
run (Put s p)      = putD s (run p)
\end{code}
\end{samepage}
\end{multicols}
}
