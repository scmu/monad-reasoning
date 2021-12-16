\section{Additional Equations in Proofs}

In this section, we list the additional equations and properties we use in the proofs.

\subsection{Equations about ST Monad}

\begin{lemma} \label{eq:runst-homomorphism} ~
% < runST (m >>= f) == runST m >>= runST . f
< runSTT (m >>= f) == runSTT m >>= runST . f
\end{lemma}

\begin{lemma} \label{eq:st-into-op} ~
<  runSTT . STT $ \s -> Op $ fmap (f s) y
< =
<  Op $ fmap (\t -> runSTT . STT $ \s -> (f s) t) y
\end{lemma}



% copy