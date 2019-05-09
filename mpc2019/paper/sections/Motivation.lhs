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

{\arraycolsep=1.4pt
\begin{figure}
\centering
\subfloat[]{
$\scriptsize
\begin{array}{rrrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\
0 & . & . & . & . & . & Q & . & .\\
1 & . & . & . & Q & . & . & . & .\\
2 & . & . & . & . & . & . & Q & .\\
3 & Q & . & . & . & . & . & . & .\\
4 & . & . & . & . & . & . & . & Q\\
5 & . & Q & . & . & . & . & . & .\\
6 & . & . & . & . & Q & . & . & .\\
7 & . & . & Q & . & . & . & . & .
\end{array}$
} %subfloat
\qquad
\subfloat[]{
$\scriptsize
\begin{array}{r||rrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\ \hline
0 & 0 & 1 & 2 & 3 & 4 & . & . & .\\
1 & 1 & 2 & 3 & 4 & . & . & . & .\\
2 & 2 & 3 & 4 & . & . & . & . & .\\
3 & 3 & 4 & . & . & . & . & . & .\\
4 & 4 & . & . & . & . & . & . & .\\
5 & . & . & . & . & . & . & . & 12\\
6 & . & . & . & . & . & . & 12& 13\\
7 & . & . & . & . & . & 12& 13& 14
\end{array}
$} %subfloat
\qquad
\subfloat[]{
$\scriptsize
\begin{array}{r||rrrrrrrr}
  & 0 & 1 & 2 & 3 & 4 & 5 & 6 & 7\\ \hline
0 & 0 &-1 & . & . & . &-5 &-6 &-7\\
1 & . & 0 &-1 & . & . & . &-5 &-6\\
2 & . & . & 0 &-1 & . & . & . &-5\\
3 & 3 & . & . & 0 & . & . & . & .\\
4 & 4 & 3 & . & . & 0 & . & . & .\\
5 & 5 & 4 & 3 & . & . & 0 & . & .\\
6 & 6 & 5 & 4 & 3 & . & . & 0 & .\\
7 & 7 & 6 & 5 & 4 & 3 & . & . & 0
\end{array}
$
} %subfloat
\caption{(a) This placement can be represented by |[3,5,7,1,6,0,2,4]|. (b) Up diagonals.
(c) Down diagonals.}
\label{fig:queens-examples}
\end{figure}
} %arraycolsep

The $n$-queens puzzle presented in this section is adapted and simplified from that of Gibbons and Hinze~\cite{GibbonsHinze:11:Just}.
The aim of the puzzle is to place |n| queens on a |n| by |n| chess board such that no two queens can attack each other. Given |n|, we number the rows and columns by |[0..n-1]|. Since all queens should be placed on distinct rows and distinct columns, a potential solution can be represented by a permutation |xs| of the list |[0..n-1]|, such that |xs !! i = j| denotes that the queen on the $i$th column is placed on the $j$th row (see Figure \ref{fig:queens-examples}(a)). In this representation queens cannot be put on the same row or column, and the problem is reduced to filtering, among permutations of |[0..n-1]|, those placements in which no two queens are put on the same diagonal. The specification can be written as a non-deterministic program:
\begin{code}
queens :: MNondet m => Int -> m [Int]
queens n = perm [0..n-1] >>= filt safe {-"~~."-}
\end{code}
where |perm| non-deterministically computes a permutation of its input, and the pure function |safe :: [Int] -> Bool| determines whether no queens are on the same diagonal. The monadic function |filt p x| returns |x| if |p x| holds, and fails otherwise:
\begin{code}
filt :: MNondet m => (a -> Bool) -> a -> m a
filt p x = guard (p x) >> return x {-"~~,"-}
\end{code}
where |guard| is a standard monadic function defined by:
\begin{code}
guard :: MNondet m => Bool -> m ()
guard b = if b then return () else mzero {-"~~."-}
\end{code}
This specification of |queens| generates all the permutations, before checking them one by one, in two separate phases. We wish to fuse the two phases and produce a faster implementation.

\paragraph{Safety Check} Representing a placement as a permutation allows an easy way to check whether two queens are put on the same diagonal.
An 8 by 8 chess board has 15 {\em up diagonals} (those running between bottom-left and top-right). Let them be indexed by |[0..14]| (see Figure \ref{fig:queens-examples}(b)).
If we apply |zipWith (+) [0..]| to a permutation, we get the indices of the up-diagonals where the chess pieces are placed.
Similarly, there are 15 {\em down diagonals} (those running between top-left and bottom right).
By applying |zipWith (-) [0..]| to a permutation, we get the indices of their down-diagonals (indexed by |[-7..7]|.
See Figure \ref{fig:queens-examples}(c)).
A placement is safe if the diagonals contain no duplicates:
\begin{code}
ups, downs :: [Int] -> [Int]
ups    xs  = zipWith (+) [0..] xs  {-"~~,"-}
downs  xs  = zipWith (-) [0..] xs  {-"~~,"-}

safe     :: [Int] -> Bool
safe xs  = nodup (ups xs) && nodup (downs xs) {-"~~,"-}
\end{code}

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
