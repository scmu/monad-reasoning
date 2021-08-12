\section{Simulating Nondeterminism with State: The Proofs}
%-------------------------------------------------------------------------------
\subsection{Only State and Nondeterminism}
\label{app:runnd-hnd}

This section shows that the |runND| function in Section \ref{sec:sim-nondet-state} is equivalent
to the following nondeterminism handler |hND| in Section \ref{sec:combining-effects}.

\begin{theorem}\label{eq:runnd-hnd}
|runND = hND|
\end{theorem}
\begin{proof}
We start with expanding the definition of |runND|:
< extractS . hState' . nondet2stateS = hND
Both |nondet2stateS| and |hND| are written as a fold.
We can use the universal property of fold to show that the two sides of the equation
are equal.
For this, we use the fold fusion law for postcomposition as defined in 
Equation \ref{eq:fusion-post}.

We have to prove the following two equations.
\begin{enumerate}
    \item |(extractS . hState') . gen = genND|
    \item |(extractS . hState') . alg = algND . fmap (extractS . hState')|
\end{enumerate}

The first equation is simple to prove with equational reasoning.
For all input |x|, we need to prove that |extractS (hState' (gen x)) = genND x|
<    extractS (hState' (gen x))
< = {-~  definition of |gen|  -}
<    extractS (hState' (appendS x popS))

< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' (appendS x popS)) (S [] [])
< = {-~  evaluation of |appendS|  -}
\wenhao{Add more steps?}
<    results . snd $ runState (hState' popS) (S ([] ++ [x]) [])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S [x] [])
< = {-~  evaluation of |popS|  -}
\wenhao{Add more steps?}
% <    results . snd $ ((), S [x] [])

% < = {-~  definition of |appendS|, function application  -}
% <    extractS (hState' (do (S xs stack) <- getS; putS (S (xs ++ [x]) stack); popS))
% < = {-~  definition of |do|  -}
% <    extractS (hState' (getS >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS))
% < = {-~  definition of |getS|  -}
% <    extractS (hState' (Op (Get return) >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS))
% < = {-~  definition of |(>>=)|  -}
% <    extractS (hState' (Op (Get (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS))))
% < = {-~  definition of |hState'|  -}
% <    extractS (algS' (Get (hState' . (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS))))
% < = {-~  definition of |algS'|  -}
% <    extractS (State $ \s -> runState ((hState' . (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS)) s) s)
% < = {-~  definition of |extractS|, function application  -}
% <    results . snd $ runState (State $ \s -> runState ((hState' . (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS)) s) s) (S [] [])
% < = {-~  definition of |runState|  -}
% <    results . snd $ (\s -> runState ((hState' . (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS)) s) s) (S [] [])
% < = {-~  function application  -}
% <    results . snd $ (runState ((hState' . (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> popS)) (S [] [])) (S [] []))
% < = {-~  function application  -}
% <    results . snd $ (runState (hState' (putS (S ([] ++ [x]) []) >> popS)) (S [] []))
% < = {-~  definition of |(++)|  -}
% <    results . snd $ (runState (hState' (putS (S [x] []) >> popS)) (S [] []))
% < = {-~  definition of |popS|, evaluation of |hState'|  -}
% \wenhao{Add more steps?}
% <    results . snd $ (runState (State $ \ S xs stack -> ((), S [x] [])) (S [] []))
% < = {-~  definition of |runState|  -}
% <    results . snd $ ((\ S xs stack -> ((), S [x] [])) (S [] []))
% < = {-~  function application  -}

<    results . snd $ ((), S [x] [])
< = {-~  definition of |snd|  -}
<    results (S [x] [])
< = {-~  definition of |results|  -}
<    [x]
< = {-~  definition of |return|  -}
<    return x
< = {-~  definition of |genND|  -}
<    genND x

The property that |extractS . hState' . gen = return| is called 
\emph{extract-gen}\label{eq:extract-gen}.

For the second equation that we have to prove, we do a case analysis.

% \fbox{|Fail|}
\noindent
\mbox{\underline{case |Fail|}}

<    extractS (hState' (alg Fail))
< = {-~  definition of |alg|  -}
<    extractS (hState' popS)
< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' popS) (S [] [])
< = {-~  evaluation of |popS|  -}
\wenhao{Add more steps?}
<    results . snd $ ((), S [] [])
< = {-~  evaluation of |results|, |snd|  -}
<    []
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap (extractS . hState')) Fail
The property that |extractS (hState' (alg Fail)) = []| is called 
\emph{extract-alg-1}\label{eq:extract-alg-1}.

% \fbox{|Or p q|}
\noindent
\mbox{\underline{case |Or p q|}}

<    extractS (hState' (alg (Or p q)))
< = {-~  definition of |alg|  -}
<    extractS (hState' (pushS q p))
< = {-~  definition of |extract|  -}
<    results . snd $ runState (hState' (pushS q p)) (S [] [])
< = {-~  evaluation of |pushS|  -}
\wenhao{Add more steps?}
<    results . snd $ runState (hState' p) (S [] [q])
< = {-~  property pop-extract (\ref{eq:pop-extract}) for |p|  -}
<    results . snd $ runState (hState' popS) (S ([] ++ extractS (hState' p)) [q])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S (extractS (hState' p)) [q])
< = {-~  evaluation of |popS|  -}
\wenhao{Add more steps?}
<    results . snd $ ((), S (extractS (hState' p) ++ extractS (hState' q)) [])
< = {-~  evaluation of |results, snd|  -}
<    extractS (hState' p) ++ extractS (hState' q)
< = {-~  definition of |algND|  -}
<    algND (Or ((extractS . hState') p) ((extractS . hState') q))
< = {-~  definition of |fmap|  -}
<    (algND . fmap (extractS . hState')) (Or p q)

% < = {-~  evaluation of |pushND q p|  -}
% <    fst . snd $ runState (runSTND p) (mzero, [q])
% < = {-~  property pop-extract (\ref{eq:pop-extract}) for |p|  -}
% <    fst . snd $ runState (runSTND popND) (mzero `mplus` extract p, [q])
% < = {-~  identity of |mzero| (\ref{eq:mzero})  -}
% <    fst . snd $ runState (runSTND popND) (extract p, [q])
% < = {-~  evaluation of |popND|  -}
% <    fst . snd $ runState (runSTND q) (extract p, [])
% < = {-~  property pop-extract (\ref{eq:pop-extract}) for |q|  -}
% <    fst . snd $ runState (runSTND popND) (extract p `mplus` extract q, [])
% < = {-~  evaluation of |runSTND popND|, |runState|  -}
% <    fst . snd $ ((), (extract p `mplus` extract q, []))
% < = {-~  evaluation of |fst|, |snd|.  -}
% <    extract p `mplus` extract q
% < = {-~  definition of |algND|  -}
% <    algND (Or (extract p) (extract q))
% < = {-~  definition of |fmap|  -}
% <    (algND . fmap extract) (Or p q)
The property that |extractS (hState' (alg (Or p q))) = extractS (hState' p) ++ extractS (hState' q)|
is called \emph{extract-alg-2}\label{eq:extract-alg-2}.
\end{proof}


In this proof we have used the property pop-extract, which states the following: 
\begin{theorem}[pop-extract]\label{eq:pop-extract}
~
% <    runState (runSTND p) (q, stack) = runState (runSTND popND) (q `mplus` extract p, stack)
<    runState (hState' p) (S q stack) = runState (hState' popS) (S (q ++ extractS (hState' p)) stack)
holds for all |p| in the domain of the function |nondet2stateS|.
\end{theorem}
We call this property the pop-extract property.
The key element to have this property is to 
only utilize a subset of terms with type |Comp (S a) ()|, namely those
that are generated by the fold of the |nondet2stateS| function,
so for which this property is true.
Indeed, we only generate such terms.
To prove this, we need to show that 
(1) the generator of |nondet2stateS| only generates programs of this subset;
and (2) the algebra preserves this property.

\begin{proof} ~
First, we use equational reasoning to prove the first item:
% <   runState (runSTND (gen x)) (q, stack) = runState (runSTND popND) (q `mplus` extract (gen x), stack)
<    runState (hState' (gen x)) (S q stack) = runState (hState' popS) (S (q ++ extractS (hState' (gen x))) stack)

<    runState (hState' (gen x)) (S q stack)
< = {-~  definition of |gen|  -}
<    runState (hState' (appendS x popS)) (S q stack)
< = {-~  evaluation of |appendS|  -}
\wenhao{Add more steps?}
<    runState (hState' popS) (S (q ++ [x]) stack)
< = {-~  definition of |return|  -}
<    runState (hState' popS) (S (q ++ return x) stack)
< = {-~  property extract-gen (\ref{eq:extract-gen})  -}
<    runState (hState' popS) (S (q ++ extractS (hState' (gen x))) stack)

% <    runState (runSTND (gen x)) (q, stack)
% < = {-~  definition of |gen|  -}
% <    runState (runSTND (appendND x popND)) (q, stack)
% < = {-~  evaluation of |appendND|  -}
% <    runState (runSTND popND) (q `mplus` return x, stack)
% < = {-~  property extract-gen (\ref{eq:extract-gen})  -}
% <    runState (runSTND popND) (q `mplus` extract (gen x), stack)

Then, we use equational reasoning with case analysis and structural induction on |x| to prove the second item:
% <     runState (runSTND (alg x)) (q, stack) = runState (runSTND popND) (q `mplus` extract (alg x), stack)
<    runState (hState' (alg x)) (S q stack) = runState (hState' popS) (S (q ++ extractS (hState' (alg x))) stack)

\noindent
\mbox{\underline{case |Fail|}}

<    runState (hState' (alg Fail)) (S q stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (popS)) (S q stack)
< = {-~  definition of |[]|  -}
<    runState (hState' popS) (S (q ++ []) stack)
< = {-~  property extract-alg-1 (\ref{eq:extract-alg-1})  -}
<    runState (hState' popS) (S (q ++ extractS (hState' (alg Fail))) stack)

% \fbox{|Or p1 p2|}
\noindent
\mbox{\underline{case |Or p1 p2|}}

Assume that |p1| and |p2| satisfy this theorem.

<    runState (hState' (alg (Or p1 p2))) (S q stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (pushS p2 p1)) (S q stack)
< = {-~  evaluation of |pushS p2 p1|  -}
\wenhao{Add more steps?}
<    runState (hState' p1) (S q (p2:stack))
< = {-~  induction: property pop-extract of |p1|  -}
<    runState (hState' popS) (S (q ++ extractS (hState' p1)) (p2:stack))
< = {-~  evaluation of |popS|  -}
\wenhao{Add more steps?}
<    runState (hState' p2) (S (q ++ extractS (hState' p1)) stack)
< = {-~  induction: property pop-extract of |p2|  -}
<    runState (hState' popS) (S (q ++ extractS (hState' p1) ++ extractS (hState' p2)) stack)
< = {-~  property extract-alg-2 (\ref{eq:extract-alg-2})  -}
<    runState (hState' popS) (S (q ++ hState' (alg (Or p1 p2))) stack)

% < = {-~  evaluation of |popND|  -}
% <    runState (runSTND p2) (q `mplus` extract p1, stack)
% < = {-~  induction: property pop-extract of |p2|  -}
% <    runState (runSTND popND) (q `mplus` extract p1 `mplus` extract p2, stack)
% < = {-~  property extract-alg-2 (\ref{eq:extract-alg-2})  -}
% <    runState (runSTND popND) (q `mplus` extract (alg (Or p1 p2)), stack)

Note that the above two proofs of theorems \ref{eq:runnd-hnd} and \ref{eq:pop-extract} are mutually recursive. However, only the 
second proof uses induction. As we work inductively on (smaller) subterms,
the proofs do work out. 
\end{proof}

%-------------------------------------------------------------------------------
\subsection{In Combination with Other Effects}
\label{app:in-combination-with-other-effects}

This section shows that the |runNDf| function of
Section \ref{sec:combining-the-simulation-with-other-effects}
is equivalent to 
the following nondeterminism handler.

< hNDf :: (Functor f, MNondet m) => Free (NondetF :+: f) a -> Free f (m a)
< hNDf = fold genNDf algNDf
<   where 
<     genNDf = Var . return 
<     algNDf (Inl Fail)      = Var mzero
<     algNDf (Inl (Or p q))  = mplus <$> p <*> q
<     algNDf (Inr y)         = Op y

%if False
$
% only to make my syntax highlighting correct
%endif

\begin{theorem}
|runNDf = hNDf|
\end{theorem}
\begin{proof}
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
For the first item we use simple equational reasoning techniques.
<    extractNDf (gen' x)
< = {-~  definition of |gen'|  -}
<    extractNDf (appendNDf x popNDf)
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (runSTNDf (appendNDf x popNDf)) (mzero, [])
< = {-~  evaluation of |appendNDf|  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (mzero `mplus` return x, [])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (return x, [])
< = {-~  evaluation of |runSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (return x, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (return x)
< = {-~  definition of |genNDf|  -}
<    genNDf x

For the second item that we have to prove, we do a case analysis.

% \fbox{|Inl Fail|}
\noindent \mbox{\underline{case |Inl Fail|}}

<    extractNDf (alg' (Inl Fail))
< = {-~  definition of |alg'|  -}
<    extractNDf popNDf
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (mzero, [])
< = {-~  evaluation of |runSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (mzero, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var mzero
< = {-~  definition of |algNDf|  -}
<    algNDf (Inl Fail)
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap extractNDf) (Inl Fail)

% \fbox{|Inl (Or p q)|}
\noindent \mbox{\underline{case |Inl (Or p q)|}}

<    extractNDf (alg' (Inl (Or p q)))
< = {-~  definition of |alg'|  -}
<    extractNDf (pushNDf q p)
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (runSTNDf (pushNDf q p)) (mzero, [])
< = {-~  evaluation of |pushNDf q p|  -}
<    fst . snd <$> runStateT (runSTNDf p) (mzero, [q])
< = {-~  property pop-extract for |p|  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (mzero `mplus` extractNDf p, [q])
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (extractNDf p, [q])
< = {-~  evaluation of |popNDf|  -}
<    fst . snd <$> runStateT (runSTNDf q) (extractNDf p, []) 
< = {-~  property pop-extract for |q|  -}
<    fst . snd <$> runStateT (runSTNDf popNDf) (extractNDf p `mplus` extractNDf q, []) 
< = {-~  evaluation of |runSTNDf popNDf|, |runStateT|  -}
<    fst . snd <$> Var ((), (extractNDf p `mplus` extractNDf q, []))
< = {-~  evaluation of |fst|, |snd|  -}
<    Var (extractNDf p `mplus` extractNDf q)
< = {-~  definition of |liftA2|  -}
<    mplus <$> extractNDf p <*> extractNDf q
< = {-~  definition of |algNDf|  -}
<    algNDf (Inl (Or (extractNDf p) (extractNDf q)))
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap extractNDf) (Inl (Or p q))

% \fbox{|Inr y|}
\noindent \mbox{\underline{case |Inr y|}}

<    extractNDf (alg' (Inr y))
< = {-~  definition of |alg'|  -}
<    extractNDf (STNDf $ join $ lift $ Op (return . runSTNDf <$> y))
< = {-~  definition of |extractNDf|  -}
<    fst . snd <$> runStateT (runSTNDf (STNDf $ join $ lift $ Op (return . runSTNDf <$> y))) (mzero, [])
< = {-~  |runSTNDf . STNDf = id|  -}
<    fst . snd <$> runStateT (join $ lift $ Op (return . runSTNDf <$> y)) (mzero, [])
< = {-~  definition of |join| for |StateT|  -}
<    fst . snd <$> runStateT 
<        (StateT $ \ s -> runStateT (lift $ Op (return . runSTNDf <$> y)) s >>= \(x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  |runStateT . StateT = id|  -}
<    fst . snd <$> 
<        (\ s -> runStateT (lift $ Op (return . runSTNDf <$> y)) s >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  definition of |lift|  -}
<    fst . snd <$> 
<        (\ s -> runStateT (StateT $ \ s -> Op (return . runSTNDf <$> y) 
<             >>= \ x -> return (x, s)) s 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  |runStateT . StateT = id|  -}
<    fst . snd <$> 
<        (\ s -> (\ s -> Op (return . runSTNDf <$> y) 
<             >>= \ x -> return (x, s)) s 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  application  -}
<    fst . snd <$> 
<        (\ s -> Op (return . runSTNDf <$> y) 
<             >>= \ x -> return (x, s) 
<             >>= \ (x', s') -> runStateT x' s') 
<        (mzero, [])
< = {-~  simplification  -}
<    fst . snd <$> 
<        (\ s -> Op (return . runSTNDf <$> y) >>= \ x -> runStateT x s) 
<        (mzero, [])
< = {-~  application  -}
<    fst . snd <$> (Op (return . runSTNDf <$> y) >>= \ x -> runStateT x (mzero, []))
< = {-~  definition of |>>=| for |Op|   -}
<    fst . snd <$> Op (fmap (>>= \ x -> runStateT x (mzero, [])) (fmap (return . runSTNDf) y))
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition}) -}
<    fst . snd <$> Op (fmap ((>>= \ x -> runStateT x (mzero, [])) . return . runSTNDf) y)
< = {-~  monad law return-bind (\ref{eq:monad-ret-bind}) -}
<    fst . snd <$> Op (fmap ((\ x -> runStateT x (mzero, [])) . runSTNDf) y)
< = {-~  simplification -}
<    fst . snd <$> Op (fmap (\ x -> runStateT (runSTNDf x) (mzero, [])) y)
< = {-~  definition of |fmap| for |Free| -}
<    Op (fmap (fmap (fst . snd)) (fmap (\ x -> runStateT (runSTNDf x) (mzero, [])) y))
< = {-~  functor law: composition of |fmap| (\ref{eq:functor-composition}) -}
<    Op (fmap ((fmap (fst . snd)) . (\ x -> runStateT (runSTNDf x) (mzero, []))) y)
< = {-~  simplification -}
<    Op (fmap (\x -> fst . snd <$> runStateT (runSTNDf x) (mzero, [])) y)
< = {-~  definition of |extractNDf|  -}
<    Op (fmap extractNDf y)
< = {-~  definition of |algNDf|  -}
<    algNDf (Inr (fmap extractNDf y))
< = {-~  definition of |fmap| for coproduct  -}
<    (algNDf (fmap extractNDf (Inr y))
< = {-~  reformulation  -}
<    (algNDf . fmap extractNDf) (Inr y)
\end{proof}


In this proof we have also used the pop-extract property of |STNDf|, which is similar to the pop-extract of |STND| (Theorem \ref{eq:pop-extract}).
\begin{theorem}[pop-extract of |STNDf|]\label{eq:pop-extract-f}
\,
<    runStateT (runSTNDf p) (q, stack) = runStateT (runSTNDf popNDf) (q `mplus` extract' p, stack)
holds for all |p| in the domain of the function |simulate'|.
\end{theorem}

\wenhao{Should we include the proof of it?}




