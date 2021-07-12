\section{Simulating Nondeterminism with State: The Proofs}
%-------------------------------------------------------------------------------
\subsection{Only State and Nondeterminism}
\label{app:runnd-hnd}

This section shows that the |runND| function is equivalent
to the following nondeterminism handler.

\begin{code}
hND :: MNondet m => NondetC a -> m a
hND = fold genND algND
  where 
    genND           = return 
    algND Fail      = mzero
    algND (Or p q)  = p `mplus` q
\end{code}
In what follows, we show that this handler is equal to the |runND| function
of Section \ref{sec:sim-nondet-state}.
\begin{theorem}
|runND = hND|
\end{theorem}
\begin{proof}
We start with expanding the definition of |runND|:
< extract . simulate = hND
Both |simulate| and |hND| are written as a fold.
We can use the universal property of fold to show that |runND| and
|hND| are equal.
Therefore, we will use the fold fusion law for postcomposition as defined in 
Equation \ref{eq:fusion-post}.
We have to prove that
\begin{enumerate}
    \item |extract . gen = genND|
    \item |extract . alg = algND . fmap extract|
\end{enumerate}
The first item is simple to prove with equational reasoning.
<    extract (gen x)
< = {-~  definition of |gen|  -}
<    extract (appendND x popND)
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runSTND (appendND x popND)) (mzero, [])
< = {-~  evaluation of |append|  -}
<    fst . snd $ runState (runSTND pop) (mzero `mplus` return x, [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd $ runState (runSTND pop) (return x, [])
< = {-~  evaluation of |runSTND pop|, |runState|  -}
<    fst . snd $ ((), (return x, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    return x
< = {-~  definition of |genND|  -}
<    genND x
The property that |extract . gen = return| is called 
\emph{extract-gen}\label{eq:extract-gen}.
For the second item that we have to prove, we do a case analysis.

\fbox{|Fail|}

<    extract (alg Fail)
< = {-~  definition of |alg|  -}
<    extract pop
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runSTND pop) (mzero, [])
< = {-~  evaluation of |runSTND pop|, |runState|  -}
<    fst . snd $ ((), (mzero, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    mzero
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) Fail
The property that |extract (alg Fail) = mzero| is called 
\emph{extract-alg-1}\label{eq:extract-alg-1}.

\fbox{|Or p q|}

<    extract (alg (Or p q))
< = {-~  definition of |alg|  -}
<    extract (push q p)
< = {-~  definition of |extract|  -}
<    fst . snd $ runState (runSTND (push q p)) (mzero, [])
< = {-~  evaluation of |push q p|  -}
<    fst . snd $ runState (runSTND p) (mzero, [q])
< = {-~  property pop-extract for |p|  -}
<    fst . snd $ runState (runSTND pop) (mzero `mplus` extract p, [q])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd $ runState (runSTND pop) (extract p, [q])
< = {-~  evaluation of |pop|  -}
<    fst . snd $ runState (runSTND q) (extract p, [])
< = {-~  property pop-extract for |q|  -}
<    fst . snd $ runState (runSTND pop) (extract p `mplus` extract q, [])
< = {-~  evaluation of |runSTND pop|, |runState|  -}
<    fst . snd $ ((), (extract p `mplus` extract q, []))
< = {-~  evaluation of |fst|, |snd|.  -}
<    extract p `mplus` extract q
< = {-~  definition of |algND|  -}
<    algND (Or (extract p) (extract q))
< = {-~  definition of |fmap|  -}
<    (algND . fmap extract) (Or p q)
The property that |extract (alg (Or p q)) = extract p `mplus` extract q| 
is called \emph{extract-alg-2}\label{eq:extract-alg-2}.
\end{proof}

In this proof we have used the property pop-extract, which states the following: 
\begin{theorem}[pop-extract]
\,
<    runState (runSTND p) (q, stack) = runState (runSTND pop) (q `mplus` extract p, stack)
\end{theorem}
We call this property the pop-extract property.
The key element to have this property is to 
only utilize a subset of terms with type |ST m a|, namely those
that are generated by the fold of the |simulate| function,
so for which this property is true.
Indeed, we only generate such terms.
To prove this, we need to show that 
(1) the generator of |simulate| only generates programs of this subset;
and (2) the algebra preserves this property.

\begin{theorem}[pop-extract part 1]
\,
<   runState (runSTND (gen x)) (q, stack) = runState (runSTND pop) (q `mplus` extract (gen x), stack)
\end{theorem}
We use equational reasoning to prove this theorem.
\begin{proof}
<    runState (runSTND (gen x)) (q, stack)
< = {-~  definition of |gen|  -}
<    runState (runSTND (append x pop)) (q, stack)
< = {-~  evaluation of |append|  -}
<    runState (runSTND pop) (q `mplus` return x, stack)
< = {-~  property extract-gen (\ref{eq:extract-gen})  -}
<    runState (runSTND pop) (q `mplus` extract (gen x), stack)
\end{proof}

\begin{theorem}[pop-extract part 2]
\,
<     runState (runSTND (alg x)) (q, stack) = runState (runSTND pop) (q `mplus` extract (alg x), stack)
\end{theorem}
\begin{proof}
We use equational reasoning with case analysis on |x|.

\fbox{|Fail|}

<    runState (runSTND (alg Fail)) (q, stack)
< = {-~  definition of |alg|  -}
<    runState (runSTND pop) (q, stack)
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    runState (runSTND pop) (q `mplus` mzero, stack)
< = {-~  property extract-alg-1 (\ref{eq:extract-alg-1})  -}
<    runState (runSTND pop) (q `mplus` extract (alg Fail), stack)

\fbox{|Or p1 p2|}
Assume that |p1| and |p2| satisfy this theorem.

<    runState (runSTND (alg (Or p1 p2))) (q, stack)
< = {-~  definition of |alg|  -}
<    runState (runSTND (push p2 p1)) (q, stack)
< = {-~  evaluation of |push p2 p1|  -}
<    runState (runSTND p1) (q, p2:stack)
< = {-~  induction: property of |p1|  -}
<    runState (runSTND pop) (q `mplus` extract p1, p2:stack)
< = {-~  evaluation of |pop|  -}
<    runState (runSTND p2) (q `mplus` extract p1, stack)
< = {-~  induction: property of |p2|  -}
<    runState (runSTND pop) (q `mplus` extract p1 `mplus` extract p2, stack)
< = {-~  property extract-alg-2 (\ref{eq:extract-alg-2})  -}
<    runState (runSTND pop) (q `mplus` extract (alg (Or p1 p2)), stack)
Note that the above two proofs are mutually recursive. However, only the 
pop-extract proof uses induction. As we work inductively on (smaller) subterms,
the proofs do work out. 
\end{proof}

%-------------------------------------------------------------------------------
\subsection{In Combination with Other Effects}

This section shows that |runNDf| is equivalent to 
the following nondeterminism handler.

< hNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
< hNDf = fold genNDf algNDf
<   where 
<     genNDf = Var . return 
<     algNDf (Inl Fail)      = Var mzero
<     algNDf (Inl (Or p q))  = mplus <$> p <*> q
<     algNDf (Inr y)         = Op y
We prove that this handler |hNDf| is equal to the |runNDf| function of
Section \ref{sec:combining-the-simulation-with-other-effects}.
\begin{theorem}
|runNDf = hNDf|
\end{theorem}
As before, we first expand the definition of |runNDf|, 
which is written in terms of |simulate'|, a fold. 
We use fold fusion to incorporate |extractNDf| in the fold of |simulate'|.
The universal property of fold then teaches us that |runNDf| and
|hNDf| are equal.
More concretely, we have to prove the following two things:
\begin{enumerate}
    \item |extractNDf . gen' = genNDf|
    \item |extractNDf . alg' = algNDf . fmap extractNDf|
\end{enumerate}
\begin{proof}
For the first item we use simple equational reasoning techniques.
<    extractNDf (gen' x)
< = {-~  definition of |gen'|  -}
<    extractNDf (appendNDf x popNDf)
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (unSTNDf (appendNDf x popNDf)) (mzero, [])
< = {-~  evaluation of |appendNDf|  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (mzero `mplus` return x, [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (return x, [])
< = {-~  evaluation of |unSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (return x, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (return x)
< = {-~  definition of |genNDf|  -}
<    genNDf x

For the second item that we have to prove, we do a case analysis.

\fbox{|Inl Fail|}

<    extractNDf (alg' (Inl Fail))
< = {-~  definition of |alg'|  -}
<    extractNDf popNDf
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (mzero, [])
< = {-~  evaluation of |unSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (mzero, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var mzero
< = {-~  definition of |algNDf|  -}
<    algNDf (Inl Fail)
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap extractNDf) (Inl Fail)

\fbox{|Inl (Or p q)|}

<    extractNDf (alg' (Inl (Or p q)))
< = {-~  definition of |alg'|  -}
<    extractNDf (pushNDf q p)
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (unSTNDf (pushNDf q p)) (mzero, [])
< = {-~  evaluation of |pushNDf q p|  -}
<    fst . snd <$> runStateT (unSTNDf p) (mzero, [q])
< = {-~  property pop-extract for |p|  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (mzero `mplus` extractNDf p, [q])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (extractNDf p, [q])
< = {-~  evaluation of |popNDf|  -}
<    fst . snd <$> runStateT (unSTNDf q) (extractNDf p, []) 
< = {-~  property pop-extract for |q|  -}
<    fst . snd <$> runStateT (unSTNDf popNDf) (extractNDf p `mplus` extractNDf q, []) 
< = {-~  evaluation of |unSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (extractNDf p `mplus` extractNDf q, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (extractNDf p `mplus` extractNDf q)
< = {-~  definition of |liftA2|  -}
<    mplus <$> extractNDf p <*> extractNDf q
< = {-~  definition of |algNDf|  -}
<    algNDf (Inl (Or (extractNDf p) (extractNDf q)))
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap extractNDf) (Inl (Or p q))

\fbox{|Inr y|}

<    extractNDf (alg' (Inr y))
< = {-~  definition of |alg'|  -}
<    extractNDf (STNDf $ join $ lift $ Op (return . unSTNDf <$> y))
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (unSTNDf (STNDf $ join $ lift $ Op (return . unSTNDf <$> y))) (mzero, [])
< = {-~  |unSTNDf . STNDf = id|  -}
<    fst . snd <$> runStateT (join $ lift $ Op (return . unSTNDf <$> y)) (mzero, [])
< = {-~  definition of |join| for |StateT|  -}
<    fst . snd <$> runStateT 
<        (StateT $ \ s -> runStateT (lift $ Op (return . unSTNDf <$> y)) s >>= \(x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  |runStateT . StateT = id|  -}
<    fst . snd <$> 
<        (\ s -> runStateT (lift $ Op (return . unSTNDf <$> y)) s >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  definition of |lift|  -}
<    fst . snd <$> 
<        (\ s -> runStateT (StateT $ \ s -> Op (return . unSTNDf <$> y) 
<             >>= \ x -> return (x, s)) s 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  |runStateT . StateT = id|  -}
<    fst . snd <$> 
<        (\ s -> (\ s -> Op (return . unSTNDf <$> y) 
<             >>= \ x -> return (x, s)) s 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  application  -}
<    fst . snd <$> 
<        (\ s -> Op (return . unSTNDf <$> y) 
<             >>= \ x -> return (x, s) 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  simplification  -}
<    fst . snd <$> 
<        (\ s -> Op (return . unSTNDf <$> y) >>= \ x -> runStateT x s) 
<        (mzero, [])
< = {-~  application  -}
<    fst . snd <$> (Op (return . unSTNDf <$> y) >>= \ x -> runStateT x (mzero, []))
< = {-~  definition of |>>=| for |Op|   -}
<    fst . snd <$> Op (fmap (>>= \ x -> runStateT x (mzero, [])) (fmap (return . unSTNDf) y))
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition}) -}
<    fst . snd <$> Op (fmap ((>>= \ x -> runStateT x (mzero, [])) . return . unSTNDf) y)
< = {-~  monad law return-bind (\ref{eq:monad-ret-bind}) -}
<    fst . snd <$> Op (fmap ((\ x -> runStateT x (mzero, [])) . unSTNDf) y)
< = {-~  simplification -}
<    fst . snd <$> Op (fmap (\ x -> runStateT (unSTNDf x) (mzero, [])) y)
< = {-~  definition of |fmap| for |Free| -}
<    Op (fmap (fmap (fst . snd)) (fmap (\ x -> runStateT (unSTNDf x) (mzero, [])) y))
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition}) -}
<    Op (fmap ((fmap (fst . snd)) . (\ x -> runStateT (unSTNDf x) (mzero, []))) y)
< = {-~  simplification -}
<    Op (fmap (\x -> fst . snd <$> runStateT (unSTNDf x) (mzero, [])) y)
< = {-~  definition of |extractNDf|  -}
<    Op (fmap extractNDf y)
< = {-~  definition of |algNDf|  -}
<    algNDf (Inr (fmap extractNDf y))
< = {-~  definition of |fmap| for coproduct  -}
<    (algNDf (fmap extractNDf (Inr y))
< =  (algNDf . fmap extractNDf) (Inr y)
\end{proof}







