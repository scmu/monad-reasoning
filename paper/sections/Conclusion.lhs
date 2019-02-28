\section{Conclusions and Related Work}
\label{sec:conclusion}

This pearl started as a case study of reasoning and derivation of monadic programs.
To study the interaction between non-determinism and state, we
construct backtracking algorithms solving problems that can be specified in the form |unfoldM f p >=> assert (all ok . scanlp oplus st)|, for two scenarios.
In the first scenario, we assume that right-distributivity and right-zero laws hold, which imply that each non-deterministic branch has its own state.
The derivation of the backtracking algorithm works by fusing the two phases into a monadic hylomorphism.

In the second scenario we consider the case when the state is global.
We find that we may use |mplus| to simulate sequencing, and that the idea can be elegantly packaged into commands like |putR| and |modifyR|.
The interaction between global state and non-determinism turns out to be rather tricky.
For a more rigorous treatment, we enforce a more precise separation between syntax and semantics and, as a side contribution of this pearl, propose a \emph{global state law} which the semantics should satisfy.
With the setting up, we show that a program written for local state works for the global state scenario if we replace all occurrences of |put| by |putR|.

It turns out that in derivations of programs using non-determinism and state, commutativity plays an important role. When the state is local, we have nicer properties at hand, and commutativity holds more generally.
With a shared global state, commutativity holds in limited cases.
In particular, |putR| still commutes with non-determinism.

\subsection{Related Work}
\paragraph{Prolog Four-Port Box Model}
One of the authors applied an idea, similar to |putR|, to implement debugging for the {\em 4-port box model} of Prolog.
In this model, upon the first entrance of a Prolog procedure it is {\em called}; it may yield a result and {\em exits}; when the subsequent procedure fails and backtracks, it is asked to {\em redo} its computation, possibly yielding the next result; finally it may {\em fail}.
Given a Prolog procedure |p| implemented in Haskell, the following program prints debugging messages when each of the four ports are used:
\begin{spec}
  (putStr "call" `mplus` side (putStr "fail")) >>
  p >>= \x ->
  (putStr "exit" `mplus` side (putStr "redo")) >> return x {-"~~."-}
\end{spec}

\paragraph{Local Algebraic Effect Theories}
In this paper, we have used two different techniques to distinguish between
effect operators from their implementations: type classes and free monads. In
both cases, the meaning of the effect operators is given by a set of externally
applied axioms.
\todo{(Lukšič and Pretnar, 2019)} explore another approach using algebraic
effects and handlers.
In their approach, axioms (or ``effect theories'') are encoded in the type
system: the type of an effectful function declares the operators used in the
function, as well as the equalities that handlers for these operators
should comply with.
The type of a handler indicates which operators it handles and which equations
it complies with.


% We noted that |M s a = \s -> ([a],s)| fails \eqref{eq:bind-mplus-dist} and is not a monad.
% The type |ListT (State s)| generated using the now standard Monad Transformer Library~\cite{MTL:14} expands to essentially the same implementation, and is flawed in the same way. More careful implementations of |ListT|, which does satisfy \eqref{eq:bind-mplus-dist} and the monad laws, have been proposed~\cite{Gale:07:ListT, Volkov:14:list-t}.
% Effect handlers, such as that of Wu~\shortcite{Wu:14:Effect} and Kiselyov and Ishii~\shortcite{KiselyovIshii:15:Freer}, do produce correct implementations by running the handler for non-determinism before that of state.

\paragraph{Acknowledgements} to be added.
