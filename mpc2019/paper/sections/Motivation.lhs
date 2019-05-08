\section{Motivation}
In the previous section we discussed two possible semantics for the interaction
of state and nondeterminism: global and local state semantics.
In this section, we will further explore the differences between these two
interpretations.
Using the classic $n$-queens puzzle as an example, we show that sometimes we
end up in a situation where we want to write our program according to local
state semantics (which is generally speaking easier to reason about), but desire
the performance characteristics of global state semantics.

\subsection{Example: The $n$-Queens Problem}
TODO

\subsection{Space Usage of Local State Implementations}
For a monad with both non-determinism and state, the local state laws imply that
each non-deterministic branch has its own state. This is not costly for states
consisting of linked data structures, for example the state
|(Int, [Int], [Int])| \koen{double check this state type after the example
  subsection has been rewritten}
in the |n|-queens problem. In some applications, however, the state
might be represented by data structures, e.g. arrays, that are costly to
duplicate.
Especially when each new state is only slightly different from the previous
(say, the array is updated in one place each time), we have a wasteful
duplication of information.
We would prefer it if each branch stores only the
delta with the state upon entering the branch, rather than storing its own copy
of the state. The state can then be backtracked by inverting these deltas.
\koen{TODO: picture?}

Programs written for global state semantics don't have the above issue; there we have
more precise control over when copies of the state get made.
So we might write our programs directly in the global state style. However, if
we do this to a program that would be more naturally expressed in the local
state style (such as our $n$-queens example), this will come at a great loss of
clarity. Furthermore, as we shall see, global state programs are significantly
more difficult to reason about.
We could also write our program first in a local state style and then translate
it to global state style.
Doing this manually is a tedious and
error-prone process that leaves us with code that is hard to maintain. A more
attractive proposition is to design a systematic program transformation that
takes a program written for local state semantics as input, and outputs a
program that, when interpreted under global state semantics, behaves exactly the
same as the original program interpreted under local state semantics.

In the remainder of the paper we define this program transformation and prove it
correct. \koen{should we stress here that the core contribution is not the
  program transformation but the proof/proof technique?}