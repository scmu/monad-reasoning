\section{Appendix: Correctness of |hLocal| and |hGlobal|}
In this appendix we give a proof sketch for the correctness
of |hLocal| and |hGlobal|. By ``correctness'', we mean that they respectively
implement local state and global state semantics.
The proofs for both are analogous to (but a bit more straightforward than)
the proof of correctness for trans.
Since the proof structure is identical for local and global state, we use
a generic variable |h| to stand for either handler.

We begin by proving context-free versions of state and nondeterminism laws.
We re-write the original statements slightly
to fit more easily in our continuation-passing style (in fact, this
formulation is slightly more general).
To pick an arbitrary example, |put|-|put| law is forumulated as:
\begin{code}
h (Put s (Put t k) = h (Put t)
\end{code}
For instance, with |h = hLocal|, this is proven very easily:
\begin{code}
hLocal (Put s (Put t k))
===
\ _ -> (\ _ -> k t) s
===
\ _ -> k t
===
hLocal (Put t k)
\end{code}
Of course, for local state semantics we should prove the context-free versions
of the local state laws:
\begin{code}
hLocal (p >> mzero) = hLocal p
hLocal (p >>= \x -> q x `mplus` r x) = hLocal (p >>= q `mplus` p >>= r)
\end{code}
And similarly for global state semantics we show
\begin{code}
hGlobal (Put t (p `mplus` q)) = hGlobal (Put t p `mplus` q)
\end{code}
