%if False
\begin{code}
module GSMonad where
\end{code}
%endif

\pagebreak
\section{An Implementation of the Semantical Domain}
\label{sec:GSMonad}

We present an implementation of |Dom| that satisfies the
axioms demanded by Section~\ref{sec:ctxt-trans}.
We have proven its compliance to the axioms laid out in
Section~\ref{sec:model-global-state-sem} by writing a machine-verified proof
($\checkmark$).
We let |Dom| be the union of |M s a| for all |a| and
for a given |s|.

%\setlength{\columnsep}{-4cm}
\begin{samepage}
The implementation is based on a multiset or |Bag| data structure.
\begin{code}
type Bag a

singleton  :: a -> Bag a
emptyBag   :: Bag a
sum        :: Bag a -> Bag a -> Bag a
\end{code}
\end{samepage}

\begin{samepage}
We model a stateful, nondeterministic computation with global state semantics as
a function that maps an initial state onto a bag of results, and a final state.
Each result is a pair of the value returned, as well as the state at that point
in the computation.
As we mentioned in Section~\ref{sec:model-global-state-sem}, a bind operator cannot be
defined for this implementation (and this is by design),
because we retain only the final result of the branch without any information on
how to continue the branch.
\begin{code}
type M s a = s -> (Bag (a,s),s)
\end{code}
\end{samepage}

\begin{samepage}
|failD| does not modify the state and produces no results.
|retD| does not modify the state and produces a single result.
\begin{code}
failD :: M s a
failD = \s -> (emptyBag,s)

retD :: a -> M s a
retD x = \s -> (singleton (x,s),s)
\end{code}
\end{samepage}

\begin{samepage}
  |getD| simply passes along the initial state to its continuiation.
  |putD| ignores the initial state and calls its continuation with the given
  parameter instead.
\begin{code}
getD :: (s -> M s a) -> M s a
getD k = \s -> k s s

putD :: s -> M s a -> M s a
putD s k = \ _ -> k s
\end{code}
\end{samepage}

\begin{samepage}
The |<||||>| operator runs the left computation with the initial state, then
runs the right computation with the final state of the left computation,
and obtains the final result by merging the two bags of results.
\begin{code}
(<||>) :: M s a -> M s a -> M s a
(xs <||> ys) s =  let  (ansx, s')   = xs s
                       (ansy, s'')  = ys s'
                  in (sum ansx ansy, s'')
\end{code}
\end{samepage}
