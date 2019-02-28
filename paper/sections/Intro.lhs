%%include lhs2TeX.fmt
%%include forall.fmt
%%include polycode.fmt
%%include Formatting.fmt

\section{Introduction}

Equational reasoning is among the many gifts that functional programming offers us. Functional programs preserve a rich set of mathematical properties, which not only helps to prove properties about programs in a relatively simple and elegant manner, but also aids the development of programs. One may refine a clear but inefficient specification, stepwise through equational reasoning, to an efficient program whose correctness may not be obvious without such a derivation.

It is misleading if one says that functional programming does not allow side effects. In fact, even a purely functional language may allow a variety of side effects --- in a rigorous, mathematically manageable manner. Since the introduction of {\em monads} into the functional programming community~\cite{Moggi:89:Computational, Wadler:92:Monads}, it has become the main framework in which effects are modelled. Various monads were developed for different effects, from general ones such as IO, state, non-determinism, exception, continuation, environment passing, to specific purposes such as parsing. Numerous research were also devoted to producing practical monadic programs.

% Monad transformers~\cite{Liang:95:Monad} were introduced to allow modular construction of monads. Shortcomings of this approach were noticed, and it was proposed to see execution of monadic programs as interaction between programs and handlers~\cite{Plotkin:09:Handlers, Kiselyov:13:Extensible, KiselyovIshii:15:Freer}.

Hutton and Fulger~\shortcite{HuttonFulger:08:Reasoning} noted that relatively less attention has been paid to reasoning about monadic programs.
We believe that the observation is still true today, perhaps due to the impression that impure programs are bound to be difficult to reason about.
In fact, the laws of monads and their operators are sufficient to prove quite a number of useful properties about monadic programs.
The validity of these properties, proved using only these laws, is independent from the particular implementation of the monad.

This paper follows the trail of Hutton and Fulger~\shortcite{HuttonFulger:08:Reasoning} and~Gibbons and Hinze~\shortcite{GibbonsHinze:11:Just}, aiming to develop theorems and patterns that are useful for reasoning about monadic programs.
We focus on two effects --- non-determinism and state.
The interaction between non-determinism and state is known to be intricate.
When each non-deterministic branch has its own local state, we get a relatively well-behaved monad, providing a richer collection of properties to work with.
When all the non-deterministic branches share one global state, the properties of the monad is much less intuitive, as we shall see in this paper.

In this paper we consider problem specifications that use a monadic unfold to generate possible solutions, which are filtered using a |scanl|-like predicate.
We construct backtracking algorithms for such problems in two scenarios, in which the state is respectively local and global.
In the local-state case, we develop theorems that convert a variation of |scanl| to a |foldr| that uses the state monad, as well as theorems constructing hylomorphism.
For the case of global state, we study programming patterns that guarantee to restore the initial state after all non-deterministic branches, propose laws the global state monad should satisfy, and show that one may simulate local states using a global state.
The algorithms are used to solve the |n|-queens puzzle, our running example.
