import Data.Bitraversable (Bitraversable)
%if False
\begin{code}
\end{code}
%endif
\section{Proofs for Modelling Nondeterminism with State}
\label{app:nondet-state}

In this secton, we prove the theorems in
\Cref{sec:nondeterminism-state}.

%-------------------------------------------------------------------------------
\subsection{Only Nondeterminism}
\label{app:runnd-hnd}

This section proves the following theorem in
\Cref{sec:sim-nondet-state}.

\nondetStateS*

\begin{proof}
We start with expanding the definition of |runND|:
< extractS . hState' . nondet2stateS = hND

Both |nondet2stateS| and |hND| are written as folds.
%
We use the fold fusion law {\bf fusion-post'}~(\ref{eq:fusion-post-strong}) to
fuse the left-hand side.
%
Since the right-hand side is already a fold, to prove the equation we
just need to check the components of the fold |hND| satisfy the
conditions of the fold fusion, i.e., the following two equations:

\[\ba{rl}
    &|(extractS . hState') . gen = genND| \\
    &|(extractS . hState') . alg . fmap nondet2stateS|\\
 |=|&  |algND . fmap (extractS . hState') . fmap nondet2stateS|
\ea\]

For brevity, we omit the last common part |fmap nondet2stateS| of
the second equation in the following proof. Instead, we assume that
the input is in the codomain of |fmap nondet2stateS|.

% \begin{enumerate}
%     \item |(extractS . hState') . gen = genND|
%     \item |(extractS . hState') . alg = algND . fmap (extractS . hState')|
% \end{enumerate}

% The first equation is simple to prove with equational reasoning.
% For all input |x|, we need to prove that |extractS (hState' (gen x)) = genND x|.
For the first equation, we calculate as follows:

<    extractS (hState' (gen x))
< = {-~  definition of |gen|  -}
<    extractS (hState' (appendS x popS))
< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' (appendS x popS)) (S [] [])
< = {-~  \Cref{eq:eval-append}  -}
<    results . snd $ runState (hState' popS) (S ([] ++ [x]) [])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S [x] [])
< = {-~  \Cref{eq:eval-pop1}  -}
<    results . snd $ ((), S [x] [])
< = {-~  definition of |snd|  -}
<    results (S [x] [])
< = {-~  definition of |results|  -}
<    [x]
< = {-~  definition of |genND|  -}
<    genND x


For the second equation, we proceed with a case analysis on the input.

\noindent \mbox{\underline{case |Fail|}}

<    extractS (hState' (alg Fail))
< = {-~  definition of |alg|  -}
<    extractS (hState' popS)
< = {-~  definition of |extractS|  -}
<    results . snd $ runState (hState' popS) (S [] [])
< = {-~  \Cref{eq:eval-pop1}  -}
<    results . snd $ ((), S [] [])
< = {-~  evaluation of |results|, |snd|  -}
<    []
< = {-~  definition of |algND|  -}
<    algND Fail
< = {-~  definition of |fmap|  -}
<    (algND . fmap (extractS . hState')) Fail


\noindent \mbox{\underline{case |Or p q|}}

<    extractS (hState' (alg (Or p q)))
< = {-~  definition of |alg|  -}
<    extractS (hState' (pushS q p))
< = {-~  definition of |extract|  -}
<    results . snd $ runState (hState' (pushS q p)) (S [] [])
< = {-~  \Cref{eq:eval-push}  -}
<    results . snd $ runState (hState' p) (S [] [q])
< = {-~  \Cref{eq:pop-extract}  -}
<    results . snd $ runState (hState' popS) (S ([] ++ extractS (hState' p)) [q])
< = {-~  definition of |(++)|  -}
<    results . snd $ runState (hState' popS) (S (extractS (hState' p)) [q])
< = {-~  \Cref{eq:eval-pop2}  -}
<    results . snd $ runState (hState' q) (S (extractS (hState' p)) [])
< = {-~  \Cref{eq:pop-extract}  -}
<    results . snd $ runState (hState' popS) (S (extractS (hState' p) ++ extractS (hState' q)) [])
< = {-~  \Cref{eq:eval-pop1}  -}
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

\end{proof}

In the above proof we have used several lemmas. Now we prove them.

\begin{lemma}[pop-extract]\label{eq:pop-extract}
~
% <    runState (runSTND p) (q, stack) = runState (runSTND popND) (q `mplus` extract p, stack)
<    runState (hState' p) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' p)) stack)
holds for all |p| in the codomain of the function |nondet2stateS|.
\end{lemma}

\begin{proof} ~
%
We prove this lemma by structural induction on |p :: Free (StateF (S
a)) ()|.
%
For each inductive case of |p|, we not only assume this lemma holds
for its sub-terms (this is the standard induction hypothesis), but
also assume \Cref{thm:nondet-stateS} holds for |p| and its sub-terms.
This is sound because in the proof of \Cref{thm:nondet-stateS}, for
|(extractS .  hState' . nondet2stateS) p = hND p|, we only apply
\Cref{eq:pop-extract} to the sub-terms of |p|, which is already
included in the induction hypothesis so there is no circular argument.

Since we assume \Cref{thm:nondet-stateS} holds for |p| and its
sub-terms, we can use several useful properties proved in the
sub-cases of the proof of \Cref{thm:nondet-stateS}. We list them here
for easy reference:
%
\begin{itemize}
\item {extract-gen}:
|extractS . hState' . gen = return|
\item {extract-alg1}:
|extractS (hState' (alg Fail)) = []|
\item {extract-alg2}:
|extractS (hState' (alg (Or p q))) = extractS (hState' p) ++ extractS (hState' q)|
\end{itemize}

% The key element to have this property is to
% only utilize a subset of terms with type |Comp (S a) ()|, namely those
% that are generated by the fold of the |nondet2stateS| function,
% so for which this property is true.

We proceed by structural induction on |p|.
%
Note that for all |p| in the codomain of |nondet2stateS|, it is either
generated by the |gen| or the |alg| of |nondet2stateS|.  Thus, we only
need to prove the following two equations where |p = gen x| or |p =
alg x| and |x| is in the codomain of |fmap nondet2stateS|.
%
\begin{enumerate}
    \item |runState (hState' (gen x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (gen x))) stack)|
    \item |runState (hState' (alg x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (alg x))) stack)|
\end{enumerate}

% (1) the generator of |nondet2stateS| only generates programs of this subset;
% and (2) the algebra preserves this property.

For the case |p = gen x|, we calculate as follows:
% <    runState (hState' (gen x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (gen x))) stack)

<    runState (hState' (gen x)) (S xs stack)
< = {-~  definition of |gen|  -}
<    runState (hState' (appendS x popS)) (S xs stack)
< = {-~  \Cref{eq:eval-append}  -}
<    runState (hState' popS) (S (xs ++ [x]) stack)
< = {-~  definition of |return|  -}
<    runState (hState' popS) (S (xs ++ return x) stack)
< = {-~  extract-gen  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' (gen x))) stack)

% Then, we use equational reasoning with case analysis and structural induction on |x| to prove the second item.
% <    runState (hState' (alg x)) (S xs stack) = runState (hState' popS) (S (xs ++ extractS (hState' (alg x))) stack)

For the case |p = alg x|, we proceed with a case analysis on |x|.

\noindent \mbox{\underline{case |Fail|}}

<    runState (hState' (alg Fail)) (S xs stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (popS)) (S xs stack)
< = {-~  definition of |[]|  -}
<    runState (hState' popS) (S (xs ++ []) stack)
< = {-~  extract-alg1  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' (alg Fail))) stack)

\noindent \mbox{\underline{case |Or p1 p2|}}

% Assume by induction that |p1| and |p2| satisfy this theorem.

<    runState (hState' (alg (Or p1 p2))) (S xs stack)
< = {-~  definition of |alg|  -}
<    runState (hState' (pushS p2 p1)) (S xs stack)
< = {-~  \Cref{eq:eval-push}  -}
<    runState (hState' p1) (S xs (p2:stack))
< = {-~  induction hypothesis  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' p1)) (p2:stack))
< = {-~  \Cref{eq:eval-pop2}  -}
<    runState (hState' p2) (S (xs ++ extractS (hState' p1)) stack)
< = {-~  induction hypothesis  -}
<    runState (hState' popS) (S (xs ++ extractS (hState' p1) ++ extractS (hState' p2)) stack)
< = {-~  extract-alg2  -}
<    runState (hState' popS) (S (xs ++ hState' (alg (Or p1 p2))) stack)

% Note that the above two proofs of theorems \ref{thm:nondet-stateS} and \ref{eq:pop-extract} are mutually recursive. However, only the
% second proof uses induction. As we work inductively on (smaller) subterms,
% the proofs do work out.
\end{proof}

% We also have the following lemmas, which were used in the above proof:
The following four lemmas characterise the behaviours of stack
operations.

\begin{lemma}[evaluation-append]\label{eq:eval-append}~
< runState (hState' (appendS x p)) (S xs stack) = runState (hState' p) (S (xs ++ [x]) stack)
\end{lemma}
\begin{proof}~
<    runState (hState' (appendS x p)) (S xs stack)
< = {-~  definition of |appendS|  -}
% <    runState (hState' (do S xs stack <- getS; putS (S (xs ++ [x]) stack); p)) (S xs stack)
% < = {-~  definition of |do|  -}
<    runState (hState' (getS >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p)) (S xs stack)
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) -> putS (S (xs ++ [x]) stack) >> p)) (S xs stack)
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
% To prove this lemma, we rewrite the definition of |popS| using |do|-notation:
% < popS =  (getS >>= \ (S xs stack) ->
% <           case stack of  []       -> return ()
% <                          op : ps  -> do putS (S xs ps); op)
%
% Then we use the equational reasoning.

<    runState (hState' popS) (S xs [])
< = {-~  definition of |popS|  -}
<    runState (hState' (getS >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs [])
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putS (S xs ps); op)) (S xs [])
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  function application, |case|-analysis  -}
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
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  function application, |case|-analysis  -}
% <    runState (hState' (do putS (S xs stack); q)) (S xs (q:stack))
% < = {-~  definition of |do|  -}
<    runState (hState' (putS (S xs stack) >> q)) (S xs (q:stack))
< = {-~  definition of |putS|  -}
<    runState (hState' (Op (Put (S xs stack) (return ())) >> q)) (S xs (q:stack))
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
% <    runState (hState' (do S xs stack <- getS; putS (S xs (q : stack)); p)) (S xs stack)
% < = {-~  definition of |do|  -}
<    runState (hState' (getS >>= \ (S xs stack) -> putS (S xs (q : stack)) >> p)) (S xs stack)
< = {-~  definition of |getS|  -}
<    runState (hState' (Op (Get return) >>= \ (S xs stack) -> putS (S xs (q : stack)) >> p)) (S xs stack)
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
<    runState (hState' (Op (Put (S xs (q : stack)) p))) (S xs stack)
< = {-~  definition of |hState'|  -}
<    runState (State (\s -> runState (hState' p) (S xs (q : stack)))) (S xs stack)
< = {-~  definition of |runState|  -}
<    (\s -> runState (hState' p) (S xs (q : stack))) (S xs stack)
< = {-~  function application  -}
<    runState (hState' p) (S xs (q : stack))

\end{proof}

%-------------------------------------------------------------------------------
\subsection{Combining with Other Effects}
\label{app:in-combination-with-other-effects}

% This section shows that the |runNDf| function in
% Section \ref{sec:combining-the-simulation-with-other-effects}
% is equivalent to the nondeterminism handler |hNDf| in Section \ref{sec:combining-effects}.

This section proves the following theorem in \Cref{sec:nondet2state}.

\nondetState*

\begin{proof}
The proof is very similar to that of \Cref{thm:nondet-stateS} in
\Cref{app:runnd-hnd}.

We start with expanding the definition of |runNDf|:
< extractSS . hState . nondet2state = hND

We use the fold fusion law {\bf fusion-post'}~(\ref{eq:fusion-post-strong}) to
fuse the left-hand side.
%
Since the right-hand side is already a fold, to prove the equation we
just need to check the components of the fold |hND| satisfy the
conditions of the fold fusion. The conditions can be splitted into
the following three equations:

\[\ba{rl}
    &|(extractSS . hState) . gen = genNDf| \\
    &|(extractSS . hState) . alg . fmap nondet2stateS|\\
 |=|&  |algNDf . fmap (extractSS . hState) . fmap nondet2stateS| \\
    &|(extractSS . hState) . fwd . fmap nondet2stateS|\\
 |=|&  |fwdNDf . fmap (extractSS . hState) . fmap nondet2stateS|
\ea\]

For brevity, we omit the last common part |fmap nondet2stateS| of
the second equation in the following proof. Instead, we assume that
the input is in the codomain of |fmap nondet2stateS|.

For the first equation, we calculate as follows:

<    extractSS (hState (gen x))
< = {-~  definition of |gen|  -}
<    extractSS (hState (appendSS x popSS))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (hState (appendSS x popSS)) (SS [] [])
< = {-~  \Cref{eq:eval-append-f}  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS ([] ++ [x]) [])
< = {-~  definition of |(++)|  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS [x] [])
< = {-~  \Cref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$> return ((), SS [x] [])
< = {-~  evaluation of |snd, resultsSS|  -}
<    return [x]
< = {-~  definition of |return| for free monad  -}
<    Var [x]
< = {-~  definition of |etal|  -}
<    (Var . return) x
< = {-~  definition of |genNDf|  -}
<    genNDf x

% The property that |extractSS . hState . gen = Var . return| is called \emph{extract-gen-ext}\label{eq:extract-gen-f}.

For the second equation, we proceed with a case analysis on the input.

\noindent \mbox{\underline{case |Fail|}}

% <    extractSS (hState (alg #  (Inl Fail)))
% < = {-~  definition of |(#)|  -}
<    extractSS (hState (alg Fail))
< = {-~  definition of |alg|  -}
<    extractSS (hState popSS)
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (hState popSS) (SS [] [])
< = {-~  \Cref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$> return ((), SS [] [])
< = {-~  evaluation of |snd, resultsSS|  -}
<    return []
< = {-~  definition of |return| for free monad  -}
<    Var []
< = {-~  definition of |algNDf|  -}
<    algNDf Fail
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap (extractSS . hState)) Fail
% < = {-~  definition of |(#)|  -}
% <    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inl Fail)

% The property that |extractSS (hState (alg Fail)) = Var []| is called \emph{extract-alg1-ext}\label{eq:extract-alg-1-f}.

\noindent \mbox{\underline{case |Inl (Or p q)|}}

% <    extractSS (hState ((alg # fwd) (Inl (Or p q))))
% < = {-~  definition of |(#)|  -}
<    extractSS (hState (alg (Or p q)))
< = {-~  definition of |alg|  -}
<    extractSS (hState (pushSS q p))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$> runStateT (hState (pushSS q p)) (SS [] [])
< = {-~  \Cref{eq:eval-push-f}  -}
<    resultsSS . snd <$> runStateT (hState p) (SS [] [q])
< = {-~  \Cref{eq:pop-extract-f}  -}
<    resultsSS . snd <$>
<      do { p' <- extractSS (hState p); runStateT (hState popSS) (SS ([]++p') [q]) }
< = {-~  definition of |(++)|  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); runStateT (hState popSS) (SS p' [q]) }
< = {-~  \Cref{eq:eval-pop2-f}  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); runStateT (hState q) (SS p' []) }
< = {-~  \Cref{eq:pop-extract-f}  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p);
<      do { q' <- extractSS (hState q); runStateT (hState popSS) (SS (p'++q') []) } }
< = {-~  Law (\ref{eq:monad-assoc}) for |do|-notation  -}
<    resultsSS . snd <$> do { p' <- extractSS (hState p); q' <- extractSS (hState q);
<      runStateT (hState popSS) (SS (p'++q') []) }
< = {-~  \Cref{eq:eval-pop1-f}  -}
<    resultsSS . snd <$>
<      do { p' <- extractSS (hState p); q' <- extractSS (hState q); return ((), SS (p'++q') []) }
< = {-~  evaluation of |snd, resultsSS|  -}
<    do { p' <- extractSS (hState p); q' <- extractSS (hState q); return (p'++q') }
< = {-~  definition of |liftM2|  -}
<    liftM2 (++) ((extractSS . hState) p) ((extractSS . hState) q)
< = {-~  definition of |algNDf|  -}
<    algNDf (Or ((extractSS . hState) p) ((extractSS . hState) q))
< = {-~  definition of |fmap|  -}
<    (algNDf . fmap (extractSS . hState)) (Or p q)
% < = {-~  definition of |(#)|  -}
% <    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inl (Or p q))

% The property that |extractSS (hState (alg (Or p q))) = liftM2 (++) (extractSS (hState p)) (extractSS (hState q))|
% is called \emph{extract-alg2-ext}\label{eq:extract-alg-2-f}.

For the last equation, we calculate as follows:

% \noindent \mbox{\underline{case |y|}}

% <    extractSS (hState ((alg#fwd) (Inr y)))
% < = {-~  definition of |(#)|  -}
<    extractSS (hState (fwd y))
< = {-~  definition of |fwd|  -}
<    extractSS (hState (Op (Inr y)))
< = {-~  definition of |hState|  -}
<    extractSS (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap hState y))
< = {-~  definition of |extractSS|  -}
<    resultsSS . snd <$>
<      runStateT (StateT $ \s -> Op $ fmap (\k -> runStateT k s) (fmap hState y)) (SS [] [])
< = {-~  definition of |runStateT|  -}
<    resultsSS . snd <$> (\s -> Op $ fmap (\k -> runStateT k s) (fmap hState y)) (SS [] [])
< = {-~  function application  -}
<    resultsSS . snd <$> Op $ fmap (\k -> runStateT k (SS [] [])) (fmap hState y))
< = {-~  definition of |<$>|  -}
<    Op (fmap (\k -> resultsSS . snd <$> runStateT k (SS [] [])) (fmap hState y))
< = {-~  definition of |fwdNDf|  -}
<    fwdNDf (fmap (\k -> resultsSS . snd <$> runStateT k (SS [] [])) (fmap hState y))
< = {-~  definition of |extractSS|  -}
<    fwdNDf (fmap extractSS (fmap hState y))
< = {-~  Law (\ref{eq:functor-composition})  -}
<    fwdNDf (fmap (extractSS . hState) y)
% < = {-~  definition of |(#)|  -}
% <    (algNDf # fwdNDf) (Inr (fmap (extractSS . hState) y))
% < = {-~  definition of |fmap|  -}
% <    ((algNDf # fwdNDf) . fmap (extractSS . hState)) (Inr y)

% Part of the above proof also shows:
% \begin{equation*}
% |extractSS (hState (fwd y))| = |fwdNDf (fmap (extractSS . hState) y)|
% \end{equation*}
% We call this property \emph{extract-fwd}\label{eq:extract-fwd}.

\end{proof}

% In this proof we have also used the pop-extract property of |SS|,
% which is similar to the pop-extract of |S| (Theorem
% \ref{eq:pop-extract}).
In the above proof we have used several lemmas. Now we prove them.

\begin{lemma}[pop-extract of |SS|]\label{eq:pop-extract-f}
~
<    runStateT (hState p) (SS xs stack)
< =  do { p' <- extractSS (hState p); runStateT (hState popSS) (SS (xs++p') stack) }
holds for all |p| in the codomain of the function |nondet2state|.
\end{lemma}

% As before, the key element to have this property is to
% only utilize a subset of terms with type |CompSS (S a) f ()|, namely those
% that are generated by the fold of the |nondet2state| function,
% so for which this property is true.
% Indeed, we only generate such terms.
% To prove this, we need to show that
% (1) the generator of |nondet2state| only generates programs of this subset;
% and (2) the algebra preserves this property.

\begin{proof} ~
The proof structure is similar to that of \Cref{eq:pop-extract}.
%
We prove this lemma by structural induction on |p :: Free (StateF (SS
f a) :+: f) ()|.
%
For each inductive case of |p|, we not only assume this lemma holds
for its sub-terms (this is the standard induction hypothesis), but
also assume \Cref{thm:nondet-state} holds for |p| and its sub-terms.
This is sound because in the proof of \Cref{thm:nondet-state}, for
|(extractSS .  hState . nondet2state) p = hNDf p|, we only apply
\Cref{eq:pop-extract-f} to the sub-terms of |p|, which is already
included in the induction hypothesis so there is no circular argument.

Since we assume \Cref{thm:nondet-state} holds for |p| and its
sub-terms, we can use several useful properties proved in the
sub-cases of the proof of \Cref{thm:nondet-state}. We list them here
for easy reference:
%
\begin{itemize}
\item {extract-gen-ext}:
|extractSS . hState . gen = Var . return|
\item {extract-alg1-ext}:
|extractSS (hState (alg Fail)) = Var []|
\item {extract-alg2-ext}:
|extractSS (hState (alg (Or p q))) = liftM2 (++) (extractSS (hState p)) (extractSS (hState q))|
\item {extract-fwd}
|extractSS (hState (fwd y)) = fwdNDf (fmap (extractSS . hState) y)|
\end{itemize}

% We need to prove that for all |p| generated by |nondet2state|, the equation holds.
% As |nondet2state| is a fold, we only need to show the following two equations:
We proceed by structural induction on |p|.
%
Note that for all |p| in the codomain of |nondet2state|, it is either
generated by the |gen|, |alg|, or |fwd| of |nondet2state|.  Thus, we
only need to prove the following three equations where |x| is in the
codomain of |fmap nondet2stateS| and |p = gen x|, |p = alg x|, and |p
= fwd x|, respectively.
\begin{enumerate}
    \item
<    runStateT (hState (gen x)) (SS xs stack)
< =  do { p' <- extractSS (hState (gen x)); runStateT (hState popSS) (SS (xs++p') stack) }
    \item
<    runStateT (hState (alg x)) (SS xs stack)
< =  do { p' <- extractSS (hState (alg x)); runStateT (hState popSS) (SS (xs++p') stack) }
    \item
<    runStateT (hState (fwd x)) (SS xs stack)
< =  do { p' <- extractSS (hState (fwd x)); runStateT (hState popSS) (SS (xs++p') stack) }
\end{enumerate}

For the case |p = gen x|, we calculate as follows:
% <    runStateT (hState (gen x)) (SS xs stack)
% < =  do { p' <- extractSS (hState (gen x)); runStateT (hState popSS) (SS (xs++p') stack) }

<    runStateT (hState (gen x)) (SS xs stack)
< = {-~  definition of |gen|  -}
<    runStateT (hState (appendSS x popSS)) (SS xs stack)
< = {-~  \Cref{eq:eval-append-f}  -}
<    runStateT (hState popSS) (SS (xs ++ [x]) stack)
< = {-~  definition of |etal|  -}
<    runStateT (hState popSS) (SS (xs ++ return x) stack)
< = {-~  definition of |Var| and reformulation  -}
<    do {p' <- Var (return x); runStateT (hState popSS) (SS (xs ++ p') stack) }
< = {-~  extract-gen-ext  -}
<    do {p' <- extractSS (hState (gen x)); runStateT (hState popSS) (SS (xs ++ p') stack) }

For the case |p = alg x|, we proceed with a case analysis on |x|.
% Then, we use equational reasoning with case analysis and structural induction on |x| to prove the second item.
% <    runStateT (hState (alg x)) (SS xs stack)
% < =  do { p' <- extractSS (hState (alg x)); runStateT (hState popSS) (SS (xs++p') stack) }

\noindent \mbox{\underline{case |Fail|}}

<    runStateT (hState (alg Fail)) (SS xs stack)
< = {-~  definition of |alg|  -}
<    runStateT (hState popSS) (SS xs stack)
< = {-~  definition of |[]|  -}
<    runStateT (hState popSS) (SS (xs ++ []) stack)
< = {-~  definition of |Var|  -}
<    do {p' <- Var []; runStateT (hState popSS) (SS (xs ++ p') stack) }
< = {-~  extract-alg1-ext  -}
<    do {p' <- extractSS (hState (alg Fail)); runStateT (hState popSS) (SS (xs ++ p') stack) }

\noindent \mbox{\underline{case |Or p1 p2|}}

% Assume by induction that |p1| and |p2| satisfy this theorem.

<    runStateT (hState (alg (Or p1 p2))) (SS xs stack)
< = {-~  definition of |alg|  -}
<    runStateT (hState (pushSS p2 p1)) (SS xs stack)
< = {-~  \Cref{eq:eval-push-f}  -}
<    runStateT (hState p1) (SS xs (p2:stack))
< = {-~  induction hypothesis: pop-extract of |p1|  -}
<    do { p1' <- extractSS (hState p1); runStateT (hState popSS) (SS (xs++p1') (p2:stack)) }
< = {-~  \Cref{eq:eval-pop2-f}  -}
<    do { p1' <- extractSS (hState p1); runStateT (hState p2) (SS (xs++p1') stack) }
< = {-~  induction hypothesis: pop-extract of |p2|  -}
<    do { p2' <- extractSS (hState p2); do { p1' <- extractSS (hState p1);
<      runStateT (hState popSS) (SS (xs++p1'++p2') stack) } }
< = {-~  Law (\ref{eq:monad-assoc}) with |do|-notation  -}
<    do { p2' <- extractSS (hState p2); p1' <- extractSS (hState p1);
<      runStateT (hState popSS) (SS (xs++p1'++p2') stack) }
< = {-~  definition of |liftM2|  -}
<    do { p' <- liftM2 (++) (extractSS (hState p2)) (extractSS (hState p1));
<      runStateT (hState popSS) (SS (xs++p') stack) }
< = {-~  extract-alg2-ext  -}
<    do { p' <- extractSS (hState (alg (Or p1 p2))); runStateT (hState popSS) (SS (xs++p') stack) }

% Finally, we use equational reasoning techniques to prove the third item.
For the case |p = fwd x|, we proceed with a case analysis on |x|.

<    runStateT (hState (fwd x)) (SS xs stack)
< = {-~  definition of |fwd|  -}
<    runStateT (hState (Op (Inr x))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> Op (fmap (\y -> runStateT (hState y s)) x))) (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    Op (fmap (\y -> runStateT (hState y (SS xs stack))) x) 
< = {-~  induction hypothesis -}
<   Op (fmap (\y -> do { p' <- extractSS (hState y); runStateT (hState popSS) (SS (xs++p') stack) }) x)
< = {-~  definition of |>>=| -}
<   do { p' <- Op (fmap (\y -> extractSS (hState y)) x); runStateT (hState popSS) (SS (xs++p') stack) }
< = {-~  definition of |fwdNDf| -}
<   do { p' <- fwdNDf (fmap (\y -> extractSS (hState y)) x); runStateT (hState popSS) (SS (xs++p') stack) }
< = {-~  extract-fwd -}
< =  do { p' <- extractSS (hState (fwd x)); runStateT (hState popSS) (SS (xs++p') stack) }

% Note that the above two proofs of theorems \ref{eq:runndf-hndf} and \ref{eq:pop-extract-f} are mutually recursive. However, only the
% second proof uses induction. As we work inductively on (smaller) subterms,
% the proofs do work out.
\end{proof}

The following four lemmas characterise the behaviours of stack
operations.
% We have also used the following lemmas in the above proof,
% which are similar to the lemmas used in the proof of Theorem \ref{eq:runnd-hnd}.

\begin{lemma}[evaluation-append-ext]\label{eq:eval-append-f}~
< runStateT (hState (appendSS x p)) (SS xs stack) = runStateT (hState p) (SS (xs ++ [x]) stack)
\end{lemma}
\begin{proof}~
<    runStateT (hState (appendSS x p)) (SS xs stack)
< = {-~  definition of |appendSS|  -}
% <    runStateT (hState (do SS xs stack <- getSS; putSS (SS (xs ++ [x]) stack); p)) (SS xs stack)
% < = {-~  definition of |do|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p)) (SS xs stack)
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) -> putSS (SS (xs ++ [x]) stack) >> p))
<      (SS xs stack)
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
<    runStateT (hState (Op (Inl (Put (SS (xs ++ [x]) stack) p)))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState p) (SS (xs ++ [x]) stack))) (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState p) (SS (xs ++ [x]) stack)) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState p) (SS (xs ++ [x]) stack)
\end{proof}

\begin{lemma}[evaluation-pop1-ext]\label{eq:eval-pop1-f}~
< runStateT (hState popSS) (SS xs []) = return ((), SS xs [])
\end{lemma}
\begin{proof}
% To prove this lemma, we rewrite the definition of |popS| using the definition of |do|:
% < popSS =  (getSS >>= \ (SS xs stack) ->
% <           case stack of  []       -> return ()
% <                          op : ps  -> do putSS (SS xs ps); op)
%
% Then we use the equational reasoning.

<    runStateT (hState popSS) (SS xs [])
< = {-~  definition of |popSS|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs [])
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) ->
<      case stack of  []       -> return ()
<                     op : ps  -> do putSS (SS xs ps); op)) (SS xs [])
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  function application, |case|-analysis  -}
<    runStateT (hState (return ())) (SS xs [])
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> return ((), s))) (SS xs [])
< = {-~  definition of |runStateT|  -}
<    (\s -> return ((), s)) (SS xs [])
< = {-~  function application  -}
<    ((), SS xs [])
\end{proof}

\begin{lemma}[evaluation-pop2-ext]\label{eq:eval-pop2-f}~
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
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  function application, |case|-analysis  -}
% <    runStateT (hState (do putSS (SS xs stack); q)) (SS xs (q:stack))
% < = {-~  definition of |do|  -}
<    runStateT (hState (putSS (SS xs stack) >> q)) (SS xs (q:stack))
< = {-~  definition of |putSS|  -}
<    runStateT (hState (Op (Inl (Put (SS xs stack) (return ()))) >> q)) (SS xs (q:stack))
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
<    runStateT (hState (Op (Inl (Put (SS xs stack) q)))) (SS xs (q:stack))
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState q) (SS xs stack))) (SS xs (q:stack))
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState q) (SS xs stack)) (SS xs (q:stack))
< = {-~  function application  -}
<    runStateT (hState q) (SS xs stack)
\end{proof}

\begin{lemma}[evaluation-push-ext]\label{eq:eval-push-f}~
< runStateT (hState (pushSS q p)) (SS xs stack) = runStateT (hState p) (SS xs (q:stack))
\end{lemma}
\begin{proof}~
<    runStateT (hState (pushSS q p)) (SS xs stack)
< = {-~  definition of |pushSS|  -}
% <    runStateT (hState (do SS xs stack <- getS; putSS (SS xs (q : stack)); p)) (SS xs stack)
% < = {-~  definition of |do|  -}
<    runStateT (hState (getSS >>= \ (SS xs stack) -> putSS (SS xs (q : stack)) >> p)) (SS xs stack)
< = {-~  definition of |getSS|  -}
<    runStateT (hState (Op (Inl (Get return)) >>= \ (SS xs stack) -> putSS (SS xs (q : stack)) >> p)) (SS xs stack)
< = {-~  definition of |(>>=)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
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
< = {-~  definition of |(>>)| for free monad and Law \ref{eq:monad-ret-bind}: return-bind  -}
<    runStateT (hState (Op (Inl (Put (SS xs (q : stack)) p)))) (SS xs stack)
< = {-~  definition of |hState|  -}
<    runStateT (StateT (\s -> runStateT (hState p) (SS xs (q : stack)))) (SS xs stack)
< = {-~  definition of |runStateT|  -}
<    (\s -> runStateT (hState p) (SS xs (q : stack))) (SS xs stack)
< = {-~  function application  -}
<    runStateT (hState p) (SS xs (q : stack))

\end{proof}
