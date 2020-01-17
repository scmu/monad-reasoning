\section{Appendix: Correctness of |hLocal| and |hGlobal|}
\label{ap:correctness-handlers}
We have defined handlers for local and global state semantics, in this appendix
we show their correctness, that is, we show that the handlers must each respect
the state and nondeterminism laws, and then respectively the local state and
global state laws.

The correctness of |hLocal'| with respect to all laws can be argued from
the fact that it is an algebra morphism.
Firstly, we remark that |Prog| implements the interface (if not, by itself, the
laws) of state and nondeterminism.
\begin{code}
  instance MState S Prog where
    put t  = PutOp t (Ret ())
    get    = GetOp Ret

  instance MNondet Prog where
    mzero        = mzeroOp
    p `mplus` q  = p `mplusOp` q

  instance MStateNondet S Prog
\end{code}
The semantic domain of the local state handler |hNondet'| also implements this
interface.
\begin{code}
  newtype DomLocal a = DomLocal { unDomLocal :: S -> Bag (a,S) }

  instance Monad DomLocal where
    return x  = DomLocal (\ s -> singleton (x,s))
    m >>= k   = DomLocal (\ s ->
      bagFlatten $ fmap (\ (x,s) -> unDomLocal (k x) s) (unDomLocal m s))
  
  instance MState S DomLocal where
    put t  = DomLocal (\ _ -> singleton (()  , t))
    get    = DomLocal (\ s -> singleton (s   , s))

  instance MNondet DomLocal where
    mzero        = DomLocal (\ _ -> mempty)
    p `mplus` q  = DomLocal (\ s -> p s <> q s)

  instance MStateNondet S DomLocal
\end{code} % $
It is easy to verify that this semantic domain does, in fact, conform to all laws
of state, nondeterminism and local state. And as |hLocal'| is a monad morphism from the
|Prog| to the |DomLocal| monads, the fact that all these laws hold for
|DomLocal| implies the correctness of |hLocal'|. Since the difference between
|hLocal'| and |hLocal| is only a postprocessing step, |hLocal| must fulfill
these properties as well.

The argument for the correctness of |hGlobal| is similar, but we need to tackle
one complication: the semantic domain for our global state handler is not a
monad! This means that we cannot map the bind operator as it occurs in |Prog|
onto such an operator in |DomGlobal|, as no such operator exists. This is not an
issue for those laws that can be readily rephrased in a continuation-passing
style. For instance, we do not prove the law |putG s >> putG t = putG t| of
our semantic domain (indeed it even does not make sense to state it), but
instead we prove |putG s (putG t k) = putG t k|. We then argue that, by algebra
morphism, the same law holds in |Prog|, and from that we can easily show that
the original formulation with |(>>=)| holds in |Prog|.
The only law that cannot be rewritten in this fashion is the
left-distributivity law~\eqref{eq:bind-mplus-dist}, but this law follows ``for
free'' from the definition of |(>>=)| for |Prog|.