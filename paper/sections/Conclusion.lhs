\section{Conclusions and Related Work}
\label{sec:conclusion}

This is a case study of reasoning and derivation of monadic programs.
To study the interaction between non-determinism and state, we consider problems that can be specified in the form |unfoldM f p >=> assert (all ok . scanlp oplus st)|, and derive two backtracking algorithms.
In both derivations we fuse the two phases into a monadic hylomorphism.
For the first algorithm, we assume that right-distributivity and right-zero laws hold, which imply that each non-deterministic branch has its own state.
In the second algorithm we consider the case when the state is global. We find that we may use |mplus| to simulate sequencing, and that the idea can be elegantly packaged into commands like |putR| and |modifyR|, and proposed the concept of {\em state-restoring} programs to aid the development.

It turns out that in derivations of programs using non-determinism and state, commutativity plays an important role. When the state is local, we have nicer properties at hand, and commutativity holds more generally.
With a shared global state, commutativity holds in limited cases.
In particular, |putR| still commutes with non-determinism.

The idea of |putR| is suggested by Schrijvers \todo{what to cite?}.
He applied similar idea to implement debugging for the {\em 4-port box model} of Prolog.
In this model, upon the first entrance of a prolog procedure it is {\em called}; it may yield a result and {\em exits}; when the subsequent procedure fails and backtracks, it is asked to {\em redo} its computation, possibly yielding the next result; finally it may {\em fail}.
Given a Prolog procedure |p| implemented in Haskell, the following program prints debugging messages when each of the four ports are used:
\begin{spec}
  (putStr "call" `mplus` side (putStr "fail")) >>
  p >>= \x ->
  (putStr "exit" `mplus` side (putStr "redo")) >> return x {-"~~."-}
\end{spec}

We noted that |M s a = \s -> ([a],s)| fails \eqref{eq:bind-mplus-dist} and is not a monad.
The type |ListT (State s)| generated using the now standard Monad Transformer Library~\cite{MTL:14} expands to essentially the same implementation, and is flawed in the same way. More careful implementations of |ListT|, which does satisfy \eqref{eq:bind-mplus-dist} and the monad laws, have been proposed~\cite{Gale:07:ListT, Volkov:14:list-t}.
Effect handlers, such as that of Wu~\shortcite{Wu:14:Effect} and Kiselyov and Ishii~\shortcite{KiselyovIshii:15:Freer}, do produce correct implementations by running the handler for non-determinism before that of state.

\paragraph{Acknowledgements} to be added.
