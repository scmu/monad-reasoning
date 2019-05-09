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

Global state semantics, on the other hand, has a more ``low-level'' feel to it.
Because only a single state is threaded through the entire computation without
making any implicit copies, it is easier to reason about resource usage in this
setting. So we might write our programs directly in the global state style.
However, if we do this to a program that would be more naturally expressed in
the local state style (such as our $n$-queens example), this will come at a
great loss of clarity. Furthermore, as we shall see, although it is easier to
reason about resource usage of programs in the global state setting, it is
significantly more difficult to reason about their semantics. We could also
write our program first in a local state style and then translate it to global
state style. Doing this manually is a tedious and error-prone process that
leaves us with code that is hard to maintain. A more attractive proposition is
to design a systematic program transformation that takes a program written for
local state semantics as input, and outputs a program that, when interpreted
under global state semantics, behaves exactly the same as the original program
interpreted under local state semantics.

In the remainder of the paper we define this program transformation and prove it
correct. \koen{should we stress here that the core contribution is not the
  program transformation but the proof/proof technique?}