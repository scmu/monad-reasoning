\section{Related Work}
\label{sec:related-work}

%if False
\begin{code}

\end{code}
%endif

\todo{Just do it, state will do, Zhixuan}

Hutton and Fulger

Gibbons and Hinze

%-------------------------------------------------------------------------------
\subsection{Prolog}
\label{sec:prolog}

Prolog is a prominent example of a system that exposes nondeterminism with local
state to the user, but is itself implemented in terms of a single, global state.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Warren Abstract Machine}
The folklore idea of undoing modifications upon backtracking is a key feature
of many Prolog implementations, in particular those based on the Warren 
Abstract Machine (WAM) \ref{}.
The WAM's global state is the program heap and Prolog programs modigy this heap
during unification only in a very specific manner: following the union-find
algorithm, they overwrite cells that contain self-references with pointers to
other cells. 
Undoing these modifications only requires knowledge of the modified cell's
address, which can be written back in that cell during backtracking. 
The WAM has a special stack, called the trail stack, for storing these addresses, 
and the process of restoring those cells is called \emph{untrailing}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{The 4-Port Box Model}
While trailing happends under the hood, there is a folklore Prolog programming
pattern for observing and intervening at different point in the control flow of a
procedure call, known as the \emph{4-port box model}.
In this model, upon the first entrance of a Prolog procedure 
it is \emph{called};
it may yield a result and \emph{exits}; 
when the subsequent procedure fails and backtracks, it is asked to \emph{redo}
its computation, possibly yielding the next result;
finally it may fail. 
Given a Prolog procedure |p| implemented in Haskell, the following program prints
debugging messages when each of the four ports are used:
< (putStr "call" `mplus` side (putStr "fail")) >>
< p >>= \x -> 
< (putStr "exit" `mplus` side (putStr "redo")) >>
< return x

This technique was applied in the monadic setting by Hinze \ref{},
and it has been our inspiration for expressing the state restoration with global
state.

%-------------------------------------------------------------------------------
\subsection{Reasoning About Side Effects}
\label{sec:reasoning-about-side-effects}

There are many works on reasoning and modelling side effects. 
Here, we cover those that have most directly inspired this paper. 

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Axiomatic Reasoning}
Our work was directly inspired by Gibbons and Hinze's proposal to reason 
axiomatically about programs with side effects, and their axiomatic
characterization of local state in particular \ref{}.
We have extended their work with an axiomatic characterization of global state
and on handling the former in terms of the latter. 
We also provide models that satisfy the axioms, whereas their paper
mistakenly claims that one model satisfies the local state axioms and that
another model is monadic.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Algebraic Effects}
Our formulation of implementing local state with global state is directly 
inspired by the effect handlers approach of Plotkin and Pretnar \ref{}.
By making the free monad explicit our proofs benefit directly from the induction
principle that Bauer and Pretnar established for effect handler programs
\ref{}.
While Lawvere theories were originally Plotkin's inspiration for studying 
algebraic effects, the effect handlers community has for a long time paid little
attention to them. 
Yet, Luk\v{s}i\v{c} and Pretnar \ref{}
have investigated a framework for encoding axioms or effect theories in the type
system: the type of an effectful function declares the operators used in the 
function, as well as the equalities that handlers for these operators should 
comply with. 
The type of a handler indicates which operators it handles and which equations it
complies with. 
This type system would allow us to express at the type level that our handler
interprets local state in terms of global state.





























