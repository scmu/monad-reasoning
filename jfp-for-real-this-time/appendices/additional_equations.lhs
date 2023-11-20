%if False
\begin{code}
\end{code}
%endif
\section{Additional Equations in Proofs}

In this section, we list the additional equations and properties we use in the proofs.

\subsection{Equations about ST Monad}

\begin{lemma} \label{eq:runst-homomorphism} ~
For monad |m|, |x :: STT s m a|, and |y :: a -> STT s m b|,
if the phantom type variable |s| does not appear freely in |a|, then
% < runST (m >>= f) == runST m >>= runST . f
< runSTT (x >>= y) == runSTT x >>= runSTT . y
\end{lemma}

\begin{lemma} \label{eq:st-into-op} ~
<  runSTT . STT $ \s -> Op $ fmap (f s) y
< =
<  Op $ fmap (\t -> runSTT . STT $ \s -> (f s) t) y
\end{lemma}


\subsection{Equations about |copyStack|}

\begin{lemma} \label{eq:copystack} ~
< f st == do st' <- copyStack st; f st'
\end{lemma}

\begin{lemma} \label{eq:copystack-reorder} ~
<  do liftST (pushStack a st); st' <- copyStack st; f st st'
< =
<  do st' <- copyStack st; liftST (pushStack a st); liftST (pushStack a st'); f st st'
\end{lemma}