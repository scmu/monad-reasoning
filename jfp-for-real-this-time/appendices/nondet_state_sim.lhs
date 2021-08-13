\section{Simulating Nondeterminism with State: The Proofs}
%-------------------------------------------------------------------------------
\subsection{Only State and Nondeterminism}
\label{app:runnd-hnd}

This section shows that the |runND| function in Section \ref{sec:sim-nondet-state} is equivalent
to the nondeterminism handler |hND| in Section \ref{sec:combining-effects}.

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
For all input |x|, we need to prove that |extractS (hState' (gen x)) = genND x|.
<    extractS (hState' (gen x))
< = {-~  definition of |gen|  -}
<    extractS (hState' (appendS x popS))
< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' (appendS x popS)) (S [] [])
< = {-~  Lemma \ref{eq:eval-append}  -}
<    results . snd $ runState (hState' popS) (S ([] ++ [x]) [])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S [x] [])
< = {-~  Lemma \ref{eq:eval-pop1}  -}
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

\noindent \mbox{\underline{case |Fail|}}

<    extractS (hState' (alg Fail))
< = {-~  definition of |alg|  -}
<    extractS (hState' popS)
< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' popS) (S [] [])
< = {-~  Lemma \ref{eq:eval-pop1}  -}
<    results . snd $ ((), S [] [])
< = {-~  evaluation of |results|, |snd|  -}
<    []
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap (extractS . hState')) Fail

The property that |extractS (hState' (alg Fail)) = []| is called 
\emph{extract-alg-1}\label{eq:extract-alg-1}.

\noindent \mbox{\underline{case |Or p q|}}

<    extractS (hState' (alg (Or p q)))
< = {-~  definition of |alg|  -}
<    extractS (hState' (pushS q p))
< = {-~  definition of |extract|  -}
<    results . snd $ runState (hState' (pushS q p)) (S [] [])
< = {-~  Lemma \ref{eq:eval-push}  -}
<    results . snd $ runState (hState' p) (S [] [q])
< = {-~  property pop-extract (\ref{eq:pop-extract}) for |p|  -}
<    results . snd $ runState (hState' popS) (S ([] ++ extractS (hState' p)) [q])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S (extractS (hState' p)) [q])
< = {-~  Lemma \ref{eq:eval-pop2}  -}
<    results . snd $ runState (hState' q) (S (extractS (hState' p)) [])
< = {-~  property pop-extract (\ref{eq:pop-extract}) for |q|  -}
<    results . snd $ runState (hState' popS) (S (extractS (hState' p) ++ extractS (hState' q)) [])
< = {-~  Lemma \ref{eq:eval-pop1}  -}
<    results . snd $ ((), S (extractS (hState' p) ++ extractS (hState' q)) [])
< = {-~  evaluation of |results, snd|  -}
<    extractS (hState' p) ++ extractS (hState' q)
< = {-~  definition of |algND|  -}
<    algND (Or ((extractS . hState') p) ((extractS . hState') q))
< = {-~  definition of |fmap|  -}
<    (algND . fmap (extractS . hState')) (Or p q)

%if False
$
%endif
The property that |extractS (hState' (alg (Or p q))) = extractS (hState' p) ++ extractS (hState' q)|
is called \emph{extract-alg-2}\label{eq:extract-alg-2}.
\end{proof}


In this proof we have used the property pop-extract, which states the following: 
\begin{theorem}[pop-extract]\label{eq:pop-extract}
~
% <    runState (runSTND p) (q, stack) = runState (runSTND popND) (q `mplus` extract p, stack)
<    runState (hState' p) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' p)) stack)
holds for all |p| in the range of the function |nondet2stateS|.
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
<    runState (hState' (gen x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (gen x))) stack)

<    runState (hState' (gen x)) (S xs stack)
< = {-~  definition of |gen|  -}
<    runState (hState' (appendS x popS)) (S xs stack)
< = {-~  Lemma \ref{eq:eval-append}  -}
<    runState (hState' popS) (S (xs ++ [x]) stack)
< = {-~  definition of |return|  -}
<    runState (hState' popS) (S (xs ++ return x) stack)
< = {-~  property extract-gen (\ref{eq:extract-gen})  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' (gen x))) stack)

Then, we use equational reasoning with case analysis and structural induction on |x| to prove the second item:
<    runState (hState' (alg x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (alg x))) stack)

\noindent \mbox{\underline{case |Fail|}}

<    runState (hState' (alg Fail)) (S xs stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (popS)) (S xs stack)
< = {-~  definition of |[]|  -}
<    runState (hState' popS) (S (xs ++ []) stack)
< = {-~  property extract-alg-1 (\ref{eq:extract-alg-1})  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' (alg Fail))) stack)

\noindent \mbox{\underline{case |Or p1 p2|}}

Assume that |p1| and |p2| satisfy this theorem.

<    runState (hState' (alg (Or p1 p2))) (S xs stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (pushS p2 p1)) (S xs stack)
< = {-~  Lemma \ref{eq:eval-push}  -}
<    runState (hState' p1) (S xs (p2:stack))
< = {-~  induction: property pop-extract of |p1|  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' p1)) (p2:stack))
< = {-~  Lemma \ref{eq:eval-pop2}  -}
<    runState (hState' p2) (S (xs ++ extractS (hState' p1)) stack)
< = {-~  induction: property pop-extract of |p2|  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' p1) ++ extractS (hState' p2)) stack)
< = {-~  property extract-alg-2 (\ref{eq:extract-alg-2})  -}
<    runState (hState' popS) (S (xs ++ hState' (alg (Or p1 p2))) stack)

Note that the above two proofs of theorems \ref{eq:runnd-hnd} and \ref{eq:pop-extract} are mutually recursive. However, only the 
second proof uses induction. As we work inductively on (smaller) subterms,
the proofs do work out. 
\end{proof}

We also have the following lemmas used in the above proof:

\begin{lemma}[evaluation-append]\label{eq:eval-append}~
< runState (hState' (appendS x p)) (S xs stack) = runState (hState' p) (S (xs ++ [x]) stack)
\end{lemma}
\begin{proof}~
<    runState (hState' (appendS x p)) (S xs stack)
< = {-~  definition of |appendS|  -}
<    runState (hState' (do S xs stack <- getS; putS (S (xs ++ [x]) stack); p)) (S xs stack)
< = {-~  definition of |do|  -}
<    runState (hState' (getS >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p)) (S xs stack)
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p)) (S xs stack)
< = {-~  definition of |(>>=)|  -}
<    runState (hState' (Op (Get (\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p)))) (S xs stack)
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' ((\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p) s)) s))
<      (S xs stack)
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' ((\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p) s)) s) (S xs stack)
< = {-~  function application  -}
<    runState (hState' ((\ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p) (S xs stack))) (S xs stack)
< = {-~  function application  -}
<    runState (hState' (putS (S (xs ++ [x]) stack) >> p)) (S xs stack)
< = {-~  definition of |putS|  -}
<    runState (hState' (Op (Put (S (xs ++ [x]) stack) (return ())) >> p)) (S xs stack)
< = {-~  definition of |(>>)|  -}
<    runState (hState' (Op (Put (S (xs ++ [x]) stack) p))) (S xs stack)
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' p) (S (xs ++ [x]) stack))) (S xs stack)
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' p) (S (xs ++ [x]) stack)) (S xs stack)
< = {-~  function application  -}
<    runState (hState' p) (S (xs ++ [x]) stack)
\end{proof}

\begin{lemma}[evaluation-pop1]\label{eq:eval-pop1}~
< runState (hState' popS) (S xs []) = ((), S xs [])
\end{lemma}
\begin{proof}
To prove this lemma, we rewrite the definition of |popS| using the definition of |do|:
< popS =  (getS >>= \ (S xs stack) ->
<           case stack of  []       -> return ()
<                          op : ps  -> do putS (S xs ps); op)

Then we use the equational reasoning.

<    runState (hState' popS) (S xs [])
< = {-~  definition of |popS|  -}
<    runState (hState' (getS >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs [])
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs [])
< = {-~  definition of |(>>=)|  -}
<    runState (hState' (Op (Get (\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)))) (S xs [])
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) s)) s)) (S xs [])
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) s)) s) (S xs [])
< = {-~  function application  -}
<    runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) (S xs []))) (S xs [])
< = {-~  function application, definition of |case|  -}
<    runState (hState' (return ())) (S xs [])
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> ((), s))) (S xs [])
< = {-~  definition of |runState|, function application  -}
<    ((), S xs [])
\end{proof}

\begin{lemma}[evaluation-pop2]\label{eq:eval-pop2}~
< runState (hState' popS) (S xs (q:stack)) = runState (hState' q) (S xs stack)
\end{lemma}
\begin{proof}~
<    runState (hState' popS) (S xs (q:stack))
< = {-~  definition of |popS|  -}
<    runState (hState' (getS >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs (q:stack))
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs (q:stack))
< = {-~  definition of |(>>=)|  -}
<    runState (hState' (Op (Get (\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)))) (S xs (q:stack))
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) s)) s)) (S xs (q:stack))
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) s)) s) (S xs (q:stack))
< = {-~  function application  -}
<    runState (hState' ((\ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op) (S xs (q:stack)))) (S xs (q:stack))
< = {-~  function application, definition of |case|  -}
<    runState (hState' (do putS (S xs stack); q)) (S xs (q:stack))
< = {-~  definition of |do|  -}
<    runState (hState' (putS (S xs stack) >> q)) (S xs (q:stack))
< = {-~  definition of |putS|  -}
<    runState (hState' (Op (Put (S xs stack) (return ())) >> q)) (S xs (q:stack))
< = {-~  definition of |(>>)|  -}
<    runState (hState' (Op (Put (S xs stack) q))) (S xs (q:stack))
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' q) (S xs stack))) (S xs (q:stack))
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' q) (S xs stack)) (S xs (q:stack))
< = {-~  function application  -}
<    runState (hState' q) (S xs stack)
\end{proof}

\begin{lemma}[evaluation-push]\label{eq:eval-push}~
< runState (hState' (pushS q p)) (S xs stack) = runState (hState' p) (S xs (q:stack))
\end{lemma}
\begin{proof}~
<    runState (hState' (pushS q p)) (S xs stack)
< = {-~  definition of |pushS|  -}
<    runState (hState' (do S xs stack <- getS; putS (S xs (q : stack)); p)) (S xs stack)
< = {-~  definition of |do|  -}
<    runState (hState' (getS >>= \ (S xs stack) -> putS (S xs (q : stack)) >> p)) (S xs stack)
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) -> putS (S xs (q : stack)) >> p)) (S xs stack)
< = {-~  definition of |(>>=)|  -}
<    runState (hState' (Op (Get (\ (S xs stack) -> putS (S xs (q : stack)) >> p)))) (S xs stack)
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' ((\ (S xs stack) -> putS (S xs (q : stack)) >> p) s)) s))
<      (S xs stack)
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' ((\ (S xs stack) -> putS (S xs (q : stack)) >> p) s)) s) (S xs stack)
< = {-~  function application  -}
<    runState (hState' ((\ (S xs stack) -> putS (S xs (q : stack)) >> p) (S xs stack))) (S xs stack)
< = {-~  function application  -}
<    runState (hState' (putS (S xs (q : stack)) >> p)) (S xs stack)
< = {-~  definition of |putS|  -}
<    runState (hState' (Op (Put (S xs (q : stack)) (return ())) >> p)) (S xs stack)
< = {-~  definition of |(>>)|  -}
<    runState (hState' (Op (Put (S xs (q : stack)) p))) (S xs stack)
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' p) (S xs (q : stack)))) (S xs stack)
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' p) (S xs (q : stack))) (S xs stack)
< = {-~  function application  -}
<    runState (hState' p) (S xs (q : stack))

\end{proof}

%-------------------------------------------------------------------------------
\subsection{In Combination with Other Effects}
\label{app:in-combination-with-other-effects}

This section shows that the |runNDf| function in
Section \ref{sec:combining-the-simulation-with-other-effects}
is equivalent to the nondeterminism handler |hNDf| in Section \ref{sec:combining-effects}.


\begin{theorem}\label{eq:runndf-hndf}
|runNDf = hNDf|
\end{theorem}
\begin{proof}
As before, we first expand the definition of |runNDf|, 
which is written in terms of |nondet2state|, a fold. 
We use fold fusion to incorporate |extractSS . hState| in this fold.
The universal property of fold then teaches us that |runNDf| and
|hNDf| are equal.
More concretely, we have to prove the following two equations.
\begin{enumerate}
    \item |(extractSS . hState) . gen = genNDf|
    \item |(extractSS . hState) . (alg # fwd) = (algNDf # fwdNDf) . fmap (extractSS . hState)|
\end{enumerate}

For the first item we use simple equational reasoning techniques.
For all input |x|, we need to prove that |extractSS (hState (gen x)) = genNDf x|

<    extractSS (hState (gen x))
< = {-~  definition of |gen|  -}
<    extractSS (hState (appendSS x popSS))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (hState (appendSS x popSS)) (SS [] [])
< = {-~  Lemma \ref{eq:eval-append-f}  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS ([] ++ [x]) [])
< = {-~  definition of |(++)|  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS [x] [])
< = {-~  Lemma \ref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$> return ((), SS [x] [])
< = {-~  evaluation of |results, snd|  -}
<    return [x]
< = {-~  definition of |return|  -}
<    Var [x]
< = {-~  definition of |return|  -}
<    (Var . return) x
< = {-~  definition of |genND|  -}
<    genNDf x

The property that |extractSS . hState . gen = Var . return| is called \emph{extract-gen'}\label{eq:extract-gen-f}.

For the second item that we have to prove, we do a case analysis.

\noindent \mbox{\underline{case |Inl Fail|}}

<    extractSS (hState ((alg # fwd) (Inl Fail)))
< = {-~  definition of |(#)|  -}
<    extractSS (hState (alg Fail))
< = {-~  definition of |alg|  -}
<    extractSS (hState popSS)
< = {-~  definition of |extractS|  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS [] [])
< = {-~  Lemma \ref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$> return ((), SS [] [])
< = {-~  evaluation of |results, snd|  -}
<    return []
< = {-~  definition of |return|  -}
<    Var []
< = {-~  definition of |algNDf|  -}
<    algNDf Fail
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap (extractSS . hState)) Fail
< = {-~  definition of |(#)|  -}
<    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inl Fail)

The property that |extractSS (hState (alg Fail)) = Var []| is called \emph{extract-alg-1'}\label{eq:extract-alg-1-f}.

\noindent \mbox{\underline{case |Inl (Or p q)|}}

<    extractSS (hState ((alg # fwd) (Inl (Or p q))))
< = {-~  definition of |(#)|  -}
<    extractSS (hState (alg (Or p q)))
< = {-~  definition of |alg|  -}
<    extractSS (hState (pushSS q p))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (hState (pushSS q p)) (SS [] [])
< = {-~  Lemma \ref{eq:eval-push-f}  -}
<    resultsSS . snd <$> runStateT (hState p) (SS [] [q])
< = {-~  property pop-extract (\ref{eq:pop-extract-f}) for |p|  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); runStateT (hState popSS) (SS ([]++p') [q]) }
< = {-~  definition of |(++)|  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); runStateT (hState popSS) (SS p' [q]) }
< = {-~  Lemma \ref{eq:eval-pop2-f}  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); runStateT (hState q) (SS p' []) }
< = {-~  property pop-extract (\ref{eq:pop-extract-f}) for |p|  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p);
<      do { q' <- extractSS (hState q); runStateT (hState popSS) (SS (p'++q') []) } }
< = {-~  property of |do|  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); q' <- extractSS (hState q);
<      runStateT (hState popSS) (SS (p'++q') []) }
< = {-~  Lemma \ref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); q' <- extractSS (hState q); return ((), SS (p'++q') []) }
< = {-~  evaluation of |resultsSS, snd|  -}
<    do { p' <- extractSS (hState p); q' <- extractSS (hState q); return (p'++q') }
< = {-~  definition of |(.)|  -}
<    do { p' <- ((extractSS . hState) p); q' <- ((extractSS . hState) q); return (p' ++ q')}
< = {-~  definition of |liftA2|  -}
<    liftA2 (++) ((extractSS . hState) p) ((extractSS . hState) q)
< = {-~  definition of |algNDf|  -}
<    algNDf (Or ((extractSS . hState) p) ((extractSS . hState) q))
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap (extractSS . hState)) (Or p q)
< = {-~  definition of |(#)|  -}
<    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inl (Or p q))

The property that |extractSS (hState (alg (Or p q))) = liftA2 (++) (extractSS (hState p)) (extractSS (hState q))|
is called \emph{extract-alg-2'}\label{eq:extract-alg-2-f}.

\noindent \mbox{\underline{case |Inr y|}}

<    extractSS (hState ((alg#fwd) (Inr y)))
< = {-~  definition of |(#)|  -}
<    extractSS (hState (fwd y))
< = {-~  definition of |fwd|  -}
<    extractSS (hState (Op (Inr y)))
< = {-~  definition of |hState|  -}
<    extractSS (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap hState y))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap hState y))
<      (SS [] [])
< = {-~  definition of |runStateT|  -}
<    resultsSS . snd <$> (\s -> Op $ fmap (\k -> runStateT k s) (fmap hState y)) (SS [] [])
< = {-~  function application  -}
<    resultsSS . snd <$> Op $ fmap (\k -> runStateT k (SS [] [])) (fmap hState y))
< = {-~  definition of |<$>|  -}
<    Op (fmap (\x -> resultsSS . snd <$> runStateT x (SS [] [])) (fmap hState y))
< = {-~  definition of |fwdNDf|  -}
<    fwdNDf (fmap (\x -> resultsSS . snd <$> runStateT x (SS [] [])) (fmap hState y))
< = {-~  definition of |extractSS|  -}
<    fwdNDf (fmap extractSS (fmap hState y))
< = {-~  definition of |(.)|  -}
<    fwdNDf (fmap (extractSS . hState) y)
< = {-~  definition of |(#)|  -}
<    (algNDf # fwdNDf) (Inr (fmap (extractSS . hState) y))
< = {-~  definition of |fmap|  -}
<    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inr y)
\end{proof}


In this proof we have also used the pop-extract property of |SS|, which is similar to the pop-extract of |S| (Theorem \ref{eq:pop-extract}).
\begin{theorem}[pop-extract of |SS|]\label{eq:pop-extract-f}
~
<    runStateT (hState p) (SS xs stack)
< =  do { p' <- extractSS (hState p); runStateT (hState popSS) (SS (xs++p') stack) }
holds for all |p| in the range of the function |nondet2state|.
\end{theorem}

As before, the key element to have this property is to 
only utilize a subset of terms with type |CompSS (S a) f ()|, namely those
that are generated by the fold of the |nondet2state| function,
so for which this property is true.
Indeed, we only generate such terms.
To prove this, we need to show that 
(1) the generator of |nondet2state| only generates programs of this subset;
and (2) the algebra preserves this property.

\begin{proof} ~
First, we use equational reasoning to prove the first item:
<    runStateT (hState (gen x)) (SS xs stack)
< =  do { p' <- extractSS (hState (gen x)); runStateT (hState popSS) (SS (xs++p') stack) }

<    runStateT (hState (gen x)) (SS xs stack)
< = {-~  definition of |gen|  -}
<    runStateT (hState (appendSS x popSS)) (SS xs stack)
< = {-~  Lemma \ref{eq:eval-append-f}  -}
<    runStateT (hState popSS) (SS (xs ++ [x]) stack)
< = {-~  definition of |return|  -}
<    runStateT (hState popSS) (SS (xs ++ return x) stack)
< = {-~  definition of |do| and |Var|  -}
<    do {p' <- Var (return x); runStateT (hState popSS) (SS (xs ++ p') stack) }
< = {-~  property extract-gen' (\ref{eq:extract-gen-f})  -}
<    do {p' <- extractSS (hState (gen x)); runStateT (hState popSS) (SS (xs ++ p') stack) }

Then, we use equational reasoning with case analysis and structural induction on |x| to prove the second item:
<    runStateT (hState (alg x)) (SS xs stack)
< =  do { p' <- extractSS (hState (alg x)); runStateT (hState popSS) (SS (xs++p') stack) }

\noindent \mbox{\underline{case |Fail|}}

<    runStateT (hState (alg Fail)) (SS xs stack)
< = {-~  definition of |alg|  -}
<    runStateT (hState popSS) (SS xs stack)
< = {-~  definition of |[]|  -}
<    runStateT (hState popSS) (SS (xs ++ []) stack)
< = {-~  definition of |do| and |Var|  -}
<    do {p' <- Var []; runStateT (hState popSS) (SS (xs ++ p') stack) }
< = {-~  property extract-alg-1' (\ref{eq:extract-alg-1-f})  -}
<    do {p' <- extractSS (hState (alg Fail)); runStateT (hState popSS) (SS (xs ++ p') stack) }

\noindent \mbox{\underline{case |Or p1 p2|}}

Assume that |p1| and |p2| satisfy this theorem.

<    runStateT (hState (alg (Or p1 p2))) (SS xs stack)
< = {-~  definition of |alg|  -}
<    runStateT (hState (pushSS p2 p1)) (SS xs stack)
< = {-~  Lemma \ref{eq:eval-push-f}  -}
<    runStateT (hState p1) (SS xs (p2:stack))
< = {-~  induction: property pop-extract of |p1|  -}
<    do { p1' <- extractSS (hState p1); runStateT (hState popSS) (SS (xs++p1') (p2:stack)) }
< = {-~  Lemma \ref{eq:eval-pop2-f}  -}
<    do { p1' <- extractSS (hState p1); runStateT (hState p2) (SS (xs++p1') stack) }
< = {-~  induction: property pop-extract of |p2|  -}
<    do { p2' <- extractSS (hState p2); do { p1' <- extractSS (hState p1);
<      runStateT (hState popSS) (SS (xs++p1'++p2') stack) } }
< = {-~  property of |do|  -}
<    do { p2' <- extractSS (hState p2); p1' <- extractSS (hState p1);
<      runStateT (hState popSS) (SS (xs++p1'++p2') stack) }
< = {-~  definition of |let|  -}
<    do { p2' <- extractSS (hState p2); p1' <- extractSS (hState p1);
<      let p' = (p1' ++ p2') in runStateT (hState popSS) (SS (xs++p') stack) }
< = {-~  definition of |liftA2|  -}
<    do { p' <- liftA2 (++) (extractSS (hState p2)) (extractSS (hState p1));
<      runStateT (hState popSS) (SS (xs++p') stack) }
< = {-~  property extract-alg-2' (\ref{eq:extract-alg-2-f})  -}
<    do { p' <- extractSS (hState (alg (Or p1 p2))); runStateT (hState popSS) (SS (xs++p') stack) }

Note that the above two proofs of theorems \ref{eq:runndf-hndf} and \ref{eq:pop-extract-f} are mutually recursive. However, only the 
second proof uses induction. As we work inductively on (smaller) subterms,
the proofs do work out. 
\end{proof}

We also have the following lemmas used in the above proof, which are also similar to the lemmas used in the proof of Theorem \ref{eq:runnd-hnd}.

\begin{lemma}[evaluation-append']\label{eq:eval-append-f}~
< runStateT (hState (appendSS x p)) (SS xs stack) = runStateT (hState p) (SS (xs ++ [x]) stack)
\end{lemma}
\begin{proof}~
<    runStateT (hState (appendSS x p)) (SS xs stack)
< = {-~  definition of |appendSS|  -}
<    runStateT (hState (do SS xs stack <- getSS; putSS (SS (xs ++ [x]) stack); p)) (SS xs stack)
< = {-~  definition of |do|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p)) (SS xs stack)
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p))
<      (SS xs stack)
< = {-~  definition of |(>>=)|  -}
<    runStateT (hState (Op (Inl (Get (\ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p))))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState ((\ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p) s)) s))
<      (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState ((\ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p) s)) s) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState ((\ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p) (SS xs stack))) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState (putSS (SS (xs ++ [x]) stack) >> p)) (SS xs stack)
< = {-~  definition of |putSS|  -}
<    runStateT (hState (Op (Inl (Put (SS (xs ++ [x]) stack) (return ()))) >> p)) (SS xs stack)
< = {-~  definition of |(>>)|  -}
<    runStateT (hState (Op (Inl (Put (SS (xs ++ [x]) stack) p)))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState p) (SS (xs ++ [x]) stack))) (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState p) (SS (xs ++ [x]) stack)) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState p) (SS (xs ++ [x]) stack)
\end{proof}

\begin{lemma}[evaluation-pop1']\label{eq:eval-pop1-f}~
< runStateT (hState popSS) (SS xs []) = return ((), SS xs [])
\end{lemma}
\begin{proof}
To prove this lemma, we rewrite the definition of |popS| using the definition of |do|:
< popSS =  (getSS >>= \ (SS xs stack) ->
<           case stack of  []       -> return ()
<                          op : ps  -> do putSS (SS xs ps); op)

Then we use the equational reasoning.

<    runStateT (hState popSS) (SS xs [])
< = {-~  definition of |popSS|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs [])
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs [])
< = {-~  definition of |(>>=)|  -}
<    runStateT (hState (Op (Inl (Get (\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op))))) (SS xs [])
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) s)) s)) (SS xs [])
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) s)) s) (SS xs [])
< = {-~  function application  -}
<    runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) (SS xs []))) (SS xs [])
< = {-~  function application, definition of |case|  -}
<    runStateT (hState (return ())) (SS xs [])
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> return ((), s))) (SS xs [])
< = {-~  definition of |runStateT|  -}
<    (\s -> return ((), s)) (SS xs [])
< = {-~  function application  -}
<    ((), SS xs [])
\end{proof}

\begin{lemma}[evaluation-pop2']\label{eq:eval-pop2-f}~
< runStateT (hState popSS) (SS xs (q:stack)) = runStateT (hState q) (SS xs stack)
\end{lemma}
\begin{proof}~
<    runStateT (hState popSS) (SS xs (q:stack))
< = {-~  definition of |popSS|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs (q:stack))
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs (q:stack))
< = {-~  definition of |(>>=)|  -}
<    runStateT (hState (Op (Inl (Get (\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op))))) (SS xs (q:stack))
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) s)) s)) (SS xs (q:stack))
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) s)) s) (SS xs (q:stack))
< = {-~  function application  -}
<    runStateT (hState ((\ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op) (SS xs (q:stack)))) (SS xs (q:stack))
< = {-~  function application, definition of |case|  -}
<    runStateT (hState (do putSS (SS xs stack); q)) (SS xs (q:stack))
< = {-~  definition of |do|  -}
<    runStateT (hState (putSS (SS xs stack) >> q)) (SS xs (q:stack))
< = {-~  definition of |putSS|  -}
<    runStateT (hState (Op (Inl (Put (SS xs stack) (return ()))) >> q)) (SS xs (q:stack))
< = {-~  definition of |(>>)|  -}
<    runStateT (hState (Op (Inl (Put (SS xs stack) q)))) (SS xs (q:stack))
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState q) (SS xs stack))) (SS xs (q:stack))
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState q) (SS xs stack)) (SS xs (q:stack))
< = {-~  function application  -}
<    runStateT (hState q) (SS xs stack)
\end{proof}

\begin{lemma}[evaluation-push']\label{eq:eval-push-f}~
< runStateT (hState (pushSS q p)) (SS xs stack) = runStateT (hState p) (SS xs (q:stack))
\end{lemma}
\begin{proof}~
<    runStateT (hState (pushSS q p)) (SS xs stack)
< = {-~  definition of |pushSS|  -}
<    runStateT (hState (do SS xs stack <- getS; putSS (SS xs (q : stack)); p)) (SS xs stack)
< = {-~  definition of |do|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) -> putSS (SS xs (q : stack)) >> p)) (SS xs stack)
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) -> putSS (SS xs (q : stack)) >> p)) (SS xs stack)
< = {-~  definition of |(>>=)|  -}
<    runStateT (hState (Op (Inl (Get (\ (SS xs stack) -> putSS (SS xs (q : stack)) >> p))))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState ((\ (SS xs stack) -> putSS (SS xs (q : stack)) >> p) s)) s))
<      (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState ((\ (SS xs stack) -> putSS (SS xs (q : stack)) >> p) s)) s) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState ((\ (SS xs stack) -> putSS (SS xs (q : stack)) >> p) (SS xs stack))) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState (putSS (SS xs (q : stack)) >> p)) (SS xs stack)
< = {-~  definition of |putSS|  -}
<    runStateT (hState (Op (Inl (Put (SS xs (q : stack)) (return ()))) >> p)) (SS xs stack)
< = {-~  definition of |(>>)|  -}
<    runStateT (hState (Op (Inl (Put (SS xs (q : stack)) p)))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState p) (SS xs (q : stack)))) (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState p) (SS xs (q : stack))) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState p) (SS xs (q : stack))

\end{proof}

