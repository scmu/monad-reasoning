%if False
\begin{code}
module GSMonad where
\end{code}
%endif

\section{An Implementation of the Semantical Domain}
\label{sec:GSMonad}

We present an implementation of |Dom| that satisfies the
axioms demanded by Section~\ref{sec:ctxt-trans}.
The implementation is based on a multiset or |Bag| data structure.
We let |Dom| be the union of |M s a| for all |a| and
for a given |s|. \todo{Equality for |s|?}

{
\setlength{\columnsep}{-4cm}
\begin{multicols}{2}
\begin{samepage}
\begin{code}
type Bag a = a -> Nat

singleton :: Eq a => a -> Bag a
singleton x y  | x ==  y  = 1
               | x /=  y  = 0

emptyBag :: Bag a
emptyBag _ = 0

union :: Bag a -> Bag a -> Bag a
union xs ys = \z -> xs z + ys z
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
type M s a = s -> (Bag (a,s),s)

failD :: M s a
failD = \s -> (emptyBag,s)
\end{code}
\end{samepage}
\begin{samepage}
\begin{code}
retD :: a -> M s a
retD x = \s -> (singleton (x,s),s)
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
(<||>) :: M s a -> M s a -> M s a
(xs <||> ys) s =  let  (ansx, s')   = xs s
                       (ansy, s'')  = ys s'
                  in (union ansx ansy, s'')
\end{code}
\end{samepage}
\end{multicols}
}
