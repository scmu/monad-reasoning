\section{Related Work}
\label{sec:related-work}

%if False
\begin{code}

\end{code}
%endif

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
The WAM's global state is the program heap and Prolog programs modify this heap
during unification only in a very specific manner: following the union-find
algorithm, they overwrite cells that contain self-references with pointers to
other cells. 
Undoing these modifications only requires knowledge of the modified cell's
address, which can be written back in that cell during backtracking. 
The WAM has a special stack, called the trail stack, for storing these addresses, 
and the process of restoring those cells is called \emph{untrailing}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{The 4-Port Box Model}
While trailing happens under the hood, there is a folklore Prolog programming
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
Gibbons and Hinze \ref{} proposed to reason axiomatically about
programs with effects and provided an axiomatic characterization of
local state semantics. Our earlier work in \ref{Pauwels19} was
directly inspired by their work: we introduced an axiomatic
characterization of global state and used axiomatic reasoning to prove
handling local state with global state correct.  We also provided
models that satisfy the axioms, whereas their paper mistakenly claims
that one model satisfies the local state axioms and that another model
is monadic.
This paper is an extension of \ref{Pauwels19}, but notably, we
departed from the axiomatic reasoning approach; instead we use proof
techniques based on algebraic effects and handlers.

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

Yang and Wu \ref{} remark that, although handlers are composable, the
semantics of these composed handlers are not always obvious and that
determining the correct order of composition to arrive at a desired
semantics is nontrivial.
They propose a technique based on modular handlers \ref{} which
considers conditions under which the fusion of these modular handlers
respect not only the laws of each of the handler's algebraic theories,
but also additional interaction laws. Using this technique they
provide succinct proofs of the correctness of local and global state
handlers, each constructed from a fusion of state and nondeterminism
handlers.