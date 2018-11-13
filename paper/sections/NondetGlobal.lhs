%if False
\begin{code}
{-# LANGUAGE RankNTypes, FlexibleContexts, ScopedTypeVariables #-}

module NondetGlobal where

import Prelude hiding ((>>))
import Control.Monad hiding ((>>))
import Control.Monad.State hiding ((>>))

import ListT  -- use option -i../../code

import Utilities
import Monads
import Queens

(>>) :: Monad m => m a -> m b -> m b
m1 >> m2 = m1 >>= const m2
\end{code}
%endif

\section{Non-Determinism with Global State}
\label{sec:nd-state-global}

For a monad with both non-determinism and state, right-distributivity \eqref{eq:mplus-bind-dist} implies that each non-deterministic branch has its own state. This is not costly for states consisting of linked data structures, for example the state |(Int, [Int], [Int])| in the |n|-queens problem. In some applications, however, the state might be represented by data structures, e.g. arrays, that are costly to duplicate. For such practical concerns, it is worth considering the situation when all non-deterministic branches share one global state.

Non-deterministic monads with a global state, however, is rather tricky.
One might believe that |M a = s -> ([a],s)| is a natural implementation of such a monad. The usual, naive implementation of |(>>=)| using this representation, however, does not satisfy left-distributivity \eqref{eq:bind-mplus-dist}, violates monad laws, and is therefore not even a monad. See Section \ref{sec:conclusion} for previous work on construction of a correct monad.

Even after we do have a non-deterministic, global-state passing implementation that is a monad, its semantics can sometimes be surprising.
In |m1 `mplus` m2|, the computation |m2| receives the state computed by |m1|.
Thus |mplus| is still associative, but certainly cannot be commutative.
As mentioned in Section \ref{sec:right-distr-local-state}, right-distributivity \eqref{eq:mplus-bind-dist} implies commutativity of |mplus|.
Contravariantly, \eqref{eq:mplus-bind-dist} cannot be true when the state is global.
Right-zero \eqref{eq:mzero-bind-zero} does not hold either: |mzero| simply fails, while |put s >> mzero|, for example, fails with an altered global state.
These significantly limit the properties we may have.

\subsection{Chaining Using Non-deterministic Choice}

In backtracking algorithms that keep a global state, it is a common pattern to
1. update the current state to its next step,
2. recursively search for solutions, and
3. roll back the state to the previous step.
To implement such pattern as a monadic program, one might come up with something like the code below:
\begin{spec}
modify next >> search >>= modReturn prev {-"~~."-}
\end{spec}
where |next| advances the state, |prev| undoes the modification of |next|, and |modify| and |modReturn| are defined by:
\begin{spec}
modify f       = get >>= (put . f) {-"~~,"-}
modReturn f v  = modify f >> return v {-"~~."-}
\end{spec}
Let the initial state be |st| and assume that |search| found three choices |m1 `mplus` m2 `mplus` m3|. The intention is that all of |m1|, |m2|, and |m3| start running with state |next st|, and the state is restored to |prev (next st) = st| afterwards. By \eqref{eq:bind-mplus-dist}, however,
\begin{spec}
 modify next >> (m1 `mplus` m2 `mplus` m3) >>= modReturn prev =
   modify next >> (  (m1 >>= modReturn prev) `mplus`
                     (m2 >>= modReturn prev) `mplus`
                     (m3 >>= modReturn prev)) {-"~~,"-}
\end{spec}
which, with a shared state, means that |m2| starts with state |st|, after which the state is rolled back too early to |prev st|. The computation |m3| starts with |prev st|, after which the state is rolled too far to |prev (prev st)|.

In fact, one cannot guarantee that |modReturn prev| is always executed --- if |search| fails, we get |modify next >> solve >>= modReturn prev| |= modify next >> mzero >>= modReturn prev = modify next >> mzero|. Thus the state is advanced to |next st|, but not rolled back to |st|.

We need a way to say that ``|modify next| and |modReturn prev| are run exactly once, respectively before and after all non-deterministic branches in |solve|.'' Fortunately, we have discovered a curious technique. Define
\begin{spec}
side :: N `mem` eps => Me eps a -> Me eps b
side m = m >> mzero {-"~~."-}
\end{spec}
%if False
\begin{code}
side :: MonadPlus m => m a -> m b
side m = m >> mzero {-"~~."-}
\end{code}
%endif
Since non-deterministic branches are executed sequentially, the program
\begin{spec}
side (modify next) `mplus` m1 `mplus` m2 `mplus` m3 `mplus` side (modify prev)
\end{spec}
executes |modify next| and |modify prev| once, respectively before and after all the non-deterministic branches, even if they fail. Note that |side m| does not generate a result. Its presence is merely for the side-effect of |m|, hence the name. Note also that the type of |side m| need not be the same as that of |m|.

\subsection{State-Restoring Operations}

The discussion above suggests that one can implement backtracking, in a global-state setting, by using |mplus| and |side| appropriately.
We can even go a bit further by defining the following variations of |put| and |modify|:
\begin{spec}
putR :: {S s, N} `sse` eps => s -> Me eps ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}

modifyR :: {N, S s} `sse` eps -> (s -> s) -> (s -> s) -> Me eps ()
modifyR next prev = modify next `mplus` side (modify prev) {-"~~."-}
\end{spec}
%if False
\begin{code}
putR :: (MonadPlus m, MonadState s m) => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}

modifyR :: (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{code}
%endif
For some intuition about |putR|, consider |putR s >> comp| where |comp| is some arbitrary computation:
%if False
\begin{code}
putRExplain :: (MonadPlus m, MonadState s m) => s -> m b -> m b
putRExplain s comp =
\end{code}
%endif
\begin{code}
      putR s >> comp
 ===  (get >>= \s0 -> put s `mplus` side (put s0)) >> comp
 ===    {- monad law, left-distributivity \eqref{eq:bind-mplus-dist} -}
      get >>= \s0 -> (put s >> comp) `mplus` (side (put s0) >> comp)
 ===    {- by \eqref{eq:bind-mzero-zero}, |mzero >> comp = mzero| -}
      get >>= \s0 -> (put s >> comp) `mplus` side (put s0) {-"~~."-}
\end{code}
Thanks to left-distributivity \eqref{eq:bind-mplus-dist}, |(>> comp)| is promoted into |mplus|.
Furthermore, the |(>> comp)| after |side (put s0)| is discarded by
\eqref{eq:bind-mzero-zero}.
In words, |putR s >> comp| saves the current state, computes |comp| using state |s|, and restores the saved state! Similarly with |modifyR|. The subscript |R| in their names stand for ``restore.''

The behaviour of |putR|, however, is still rather tricky. It is instructive comparing
\begin{enumerate}[label=(\alph*)]
\item |return x|,  \label{ex:putR-pitfalls-1}
\item |put s >> return x|, and \label{ex:putR-pitfalls-2}
\item |putR s >> return x|. \label{ex:putR-pitfalls-3}
\end{enumerate}
When run in initial state |s0|, they all yield |x| as the result.
Certainly, \ref{ex:putR-pitfalls-1} terminates with state |s0|, and \ref{ex:putR-pitfalls-2} terminates with state |s|.
Program \ref{ex:putR-pitfalls-3} also terminates with state |s0|.
However, \ref{ex:putR-pitfalls-3} does {\em not} equal \ref{ex:putR-pitfalls-1}!
There exist contexts, for example |(>> get)|, with which we can tell them apart:
|return x >> get| returns |s0|, while |putR s >> return x >> get| returns |s|, even though the program yields final state |s0|.

We wish that |putR|, when run with a global state, still satisfies laws \eqref{eq:put-put} through \eqref{eq:mzero-bind-zero}.
If so, one could take a program written for a local state monad, replace all occurrences of |put| by |putR|, and run the program with a global state.
Unfortunately this is not the case: |putR| does satisfy |put|-|put|~\eqref{eq:put-put} and |get|-|put|~\eqref{eq:put-get}, but |put|-|get|~\eqref{eq:get-put} fails ---
|get >>= putR| and |return ()| can be
told apart by some contexts, for example |(>> put t)|.
To see that, we calculate:
\begin{spec}
   (get >>= putR) >> put t
=  (get >>= \s -> get >>= \s0 -> put s `mplus` side (put s0)) >> put t
=   {- |get|-|get| -}
   (get >>= \s -> put s `mplus` side (put s)) >> put t
=   {- monad laws, left-distributivity -}
   get >>= \s -> (put s >> put t) `mplus` side (put s)
=   {- |put|-|put| -}
   get >>= \s -> put t `mplus` side (put s) {-"~~."-}
\end{spec}
Meanwhile, |return () >> put t = put t|. The two side are not equal when |s /= t|.

In a global-state setting, reasoning about combination of |mplus| and |(>>=)| is tricky because, due to \eqref{eq:bind-mplus-dist}, every occurrence of |mplus| is a point where future code can be inserted.
This makes it hard to reason about programs compositionally --- some properties hold only when we take the entire program into consideration.

It turns out that all properties we need do hold, provided that {\em all} occurrences of |put| are replaced by |putR| --- problematic contexts such as |put t| above is thus ruled out.
However, that ``all |put| replaced by |putR|'' is a global property, and to properly talk about it we have to formally define contexts, which is what we will do in Section~\ref{sec:ctxt-trans}.

\subsection{Contexts and Translation}
\label{sec:ctxt-trans}

%format hole = "\square"
%format Dom = "\mathcal{D}"
%format apply z (e) = z "\lbrack" e "\rbrack"
%format ntC = "\mathcal{C}"
%format ntV = "\mathcal{V}"
%format <&> = "\mathbin{\scaleobj{0.8}{\langle\&\rangle}}"
%format <||> = "\mathbin{\scaleobj{0.8}{\langle[\!]\rangle}}"
%format getD = "\scaleobj{0.8}{\langle}\Varid{get}\scaleobj{0.8}{\rangle}"
%format putD = "\scaleobj{0.8}{\langle}\Varid{put}\scaleobj{0.8}{\rangle}"
%format retD = "\scaleobj{0.8}{\langle}\Varid{ret}\scaleobj{0.8}{\rangle}"

\begin{figure}
\centering
\small
\subfloat[]{
\begin{minipage}{0.3\textwidth}
\begin{spec}
ntE    ::=  {-"\mbox{pure expressions}"-}
ntEV   ::=  {-"\mbox{functions returning monad}"-}
ntP    ::=  return ntE | mzero | ntP `mplus` ntP
         |  Get ntEV | Put ntE ntP
ntC    ::=  hole | ntC; `mplus` ntP | ntC;ntP `mplus`
         |  ntC; Put ntE | ntC; Get ntE ntEV
\end{spec}
\end{minipage}
} %subfloat1
\quad
\subfloat[]{
\begin{minipage}{0.3\textwidth}
\begin{spec}
(>>=) :: ntP -> ntEV -> ntP
return x       >>= f  = f x
mzero          >>= f = mzero
(m `mplus` n)  >>= f = (m >>= f) `mplus` (n >>= f)
Get k          >>= f = Get ((>>= f) . k)
Put x e        >>= f = Put x (e >>= k)
\end{spec}
\end{minipage}
}%subfloat
\quad
\subfloat[]{
\begin{minipage}{0.3\textwidth}
\begin{spec}
run         :: ntP -> Dom
<||>   :: Dom -> Dom -> Dom
retD        :: ntV -> Dom
getD        :: (ntV -> Dom) -> Dom
putD        :: ntV -> Dom -> Dom
\end{spec}
\end{minipage}
}%subfloat
\caption{(a) Syntax for programs and contexts (zippers).
(b) The bind operator. (c) Semantic domain.}
\label{fig:context-semantics}
\todo{Change context notation; no need to distinguish between regular contexts and zipper contexts.}
\todo{Make types more informative, make it more clear that mathcal V refers to the state type}
\end{figure}

\newcommand{\orM}{\mathbin{\scaleobj{0.8}{[\!]}}}
\begin{figure}
  \begin{mathpar}
    \inferrule*[right=CHole]
    {~}
    {[] : \Gamma ; A \leftarrow \Gamma ; A}
    \\\\
    \inferrule*[right=COr1]
    {
      \Gamma_2 \vdash \mathcal{P} : B
      \\
      \mathcal{C} : (\Gamma_1; A) \leftarrow (\Gamma_2; B)
    }
    {\mathcal{C} ; \mathcal{P} \orM : (\Gamma_1; A) \leftarrow (\Gamma_2; B)}

    \inferrule*[right=COr2]
    {
      \Gamma_2 \vdash \mathcal{P} : B
      \\
      \mathcal{C} : (\Gamma_1; A) \leftarrow (\Gamma_2; B)
    }
    {\mathcal{C} ; \orM \mathcal{P} : (\Gamma_1; A) \leftarrow (\Gamma_2; B)}
    \\\\
    \inferrule*[right=CPut]
    {
      \Gamma_2 \vdash \mathcal{E} : S
      \\
      \mathcal{C} : (\Gamma_1; A) \leftarrow (\Gamma_2; B) 
    }
    {\mathcal{C} ; \text{Put}~v : (\Gamma_1; A) \leftarrow (\Gamma_2; B)}

    \inferrule*[right=CGet]
    {
      \emptyset \vdash p : S \rightarrow \text{bool}
      \\
      \Gamma_2, S \vdash \mathit{alt} : B
      \\
      \mathcal{C} : (\Gamma_1; A) \leftarrow (\Gamma_2, S; B) 
    }
    {\mathcal{C} ; \text{Get}~p~\mathit{alt} : (\Gamma_1; A) \leftarrow (\Gamma_2; B)}
  \end{mathpar}
  \todo{in CGet rule: empty environment, alt typing; not sure about those}
  \todo{this is a bit large, if we are going to do a separate mechanization paper it should probably be moved there}
\end{figure}

In this section we will state clearly what laws we expect from a global-state non-deterministic monad and show that, under our semantical assumptions, a program we get by replacing all occurrences of |put| by |putR| does satisfy all laws we demand of a local-state non-deterministic monad.
All these concepts need to be defined more formally, however.
In Figure~\ref{fig:context-semantics}(a) we present an altered syntax for monadic programs, in the usual free monad style --- |Get| and |Put| take continuations, while |(>>=)| is defined as a (meta)function in Figure~\ref{fig:context-semantics}(b).
One can see that the definition of |(>>=)| has laws \eqref{eq:bind-mplus-dist} and \eqref{eq:mzero-bind-zero} built-in.
Also defined in Figure~\ref{fig:context-semantics}(a) are single-hole contexts |ntC|.
% TODO: are contexts so standard that they require no further explanation?
Given a context |C|, filling the hole by |e| is denoted by |apply C e|.

In the previous sections we have been mixing syntax and semantics.
Now we assume a semantic domain |Dom|, and a function |run :: ntP -> Dom| that ``runs'' a program into a value in |Dom|, and several operators |(<||||>)|, |getD|, and |putD|, shown in Figure~~\ref{fig:context-semantics}(c).  Semantics of |mplus|, |get|, and |put| may thus be defined compositionally:
\begin{spec}
run (m1 `mplus` m2) = run m1 <||> run m2 {-"~~,"-}
run (Get k) = getD (\s -> run (k s)) {-"~~,"-}
run (Put x m) = putD x (run m) {-"~~."-}
\end{spec}

In order to lighten the notational burden, we define a notion of ``contextual equivalence'' of programs:
\begin{align*}
  |m1| \triangleq_C |m2| \iff |run (apply C m1)| = |run (apply C m2)|
\end{align*}

The following laws are assumed to hold.
There should be nothing surprising here:
they are merely variations of the monad laws \eqref{eq:monad-bind-ret} and \eqref{eq:monad-assoc}, \eqref{eq:bind-mzero-zero} and the monoid property of |mplus|, and laws \eqref{eq:put-put} -- \eqref{eq:get-get} regard states, which we discussed earlier.
% TODO: maybe add some motivation why we use contexts here.

\newcommand{\CEq}{\triangleq_C}

\begin{align*}
|m >>= return|                      &\CEq |m| \mbox{~~,}\\
|(m >>= f) >>= g|                   &\CEq |m >>= \x -> (f x >>= g)|\mbox{~~,}\\
|mzero `mplus` m|                   &\CEq |m `mplus` mzero = m|\mbox{~~,}\\
|(m1 `mplus` m2) `mplus` m3|        &\CEq |m1 `mplus` (m2 `mplus` m3)|\mbox{~~,}\\
|mzero >>= k|                       &\CEq |mzero|\mbox{~~,}\\
|Get (\s1 -> Get (\s2 -> k s1 s2))| &\CEq |(Get (\s1 -> k s1 s2))|\mbox{~~,}\\
|Get (\s -> Put s m)|               &\CEq |m|\mbox{~~,}\\
|Put x (Get k)|                     &\CEq |Put x (k V)|\mbox{~~,}\\
|Put x (Put y m)|                   &\CEq |Put y m|\mbox{~~.}
\end{align*}
The laws specific for global-state non-deterministic monads are the following three:
\todo{I'm not sure law~\eqref{eq:get-mplus} is specific to global-state semantics}
\begin{align}
|(Put x m1 `mplus` m2)|      &\CEq |(Put x (m1 `mplus` m2))|\mbox{~~,} \label{eq:put-mplus-g}\\
|(Get k `mplus` m)|          &\CEq |(Get (\x -> k x `mplus` m))|\mbox{~~, |x| not in |k| and |m|,} \label{eq:get-mplus}\\
|Put x (return y `mplus` m)| &\CEq |Put x (return y) `mplus` Put x m| \label{eq:put-ret-mplus-g}\mbox{~~.}
\end{align}
Law~\eqref{eq:put-mplus-g} says that a |Put| prefixing the first  non-deterministic branch can be pulled out of that branch --- either way, the effect of |put| applies to the first branch.
Law~\eqref{eq:get-mplus} allows us to pull a |Get| out of non-deterministic branches.
Law~\eqref{eq:put-ret-mplus-g} will form the base case for a proof that a |Put| operation can be distributed over non-deterministic branches if the first branch does not modify the state.
Note that we expect it to hold only at the top level --- no context is involved. This law is crucial in our proofs.

Let |trans :: ntP -> ntP| be the function that replaces all occurrences of |put| in its input program by |putR|. Define:
\begin{spec}
eval :: ntP -> Dom
eval = run . trans {-"~~."-}
\end{spec}
We have proved the following theorems:
\begin{theorem} \label{thm:putG-state-laws}
The four state laws \eqref{eq:put-put} -- \eqref{eq:get-get} hold for the translated program, in the sense below:
\begin{align*}
  |eval (apply C (Get (\s1 -> Get (\s2 -> k s1 s2))))| &=
     |eval (apply C (Get (\s1 -> k s1 s2)))| \mbox{~~,}\\
  |eval (apply C (Put x (Get k)))| &= |eval (apply C (Put x (k x)))|\mbox{~~,}\\
  |eval (apply C (Get (\s -> Put s k)))| &=
    |eval (apply C k)| \mbox{~~, |s| not free in |k|,} \\
  |eval (apply C (Put x (Put y m)))| &=
     |eval (apply C (Put y m))|\mbox{~~.}
\end{align*}
\end{theorem}
Proof of these laws basically start with promoting |trans| inside, before applying \eqref{eq:put-mplus-g} and other laws mentioned earlier in this section.

\begin{theorem}\label{thm:putG-mplus-distr}
  In the translated program, |putR| distributes into |mplus| and is cancelled by |mzero|:
\begin{align*}
  |eval (apply C (Put x mzero))| &= |eval (apply C mzero)| \mbox{~~,}\\
  |eval (apply C (Put x m1 `mplus` Put x m2))| &=
    |eval (apply C (Put x (m1 `mplus` m2)))| \mbox{~~.}
\end{align*}
\end{theorem}
\noindent
The two properties in Theorem~\ref{thm:putG-mplus-distr} allow us to show that |putR| commutes with non-deterministic choice (i.e. |putR v >> choose x y >> k = choose x y >> putR v >> k| where |choose x y = return x `mplus` return y| \todo{Check this; also where do we prove this in the mechanization?}).
Proof of these laws uses \eqref{eq:put-mplus-g} and \eqref{eq:get-mplus}.
In addition, both Theorem~\ref{thm:putG-state-laws} and \ref{thm:putG-mplus-distr} uses the following crucial lemma, proved by
induction on |m1| and |C|, using~\eqref{eq:put-ret-mplus-g}.
\begin{lemma} |run (apply C (Put x (trans m1 `mplus` m2))) = run (apply C (Put x (trans m1) `mplus` Put x m2))|.
\end{lemma}

Finally, we need a congruence theorem:
\begin{theorem} For all |m1|, |m2| and |n| we have:
\begin{spec}
  (forall C k, eval (apply C (m1 >>= k) = eval (apply C (m2 >>= k)))) =>
    (forall C k, eval (apply C ((n >>= \x -> m1) >>= k)) = eval (apply C ((n >>= \x -> m2) >>= k))) {-"~~."-}
\end{spec}
\end{theorem}%
\noindent The proof proceeds by induction on |n|.

\subsection{Backtracking with a Global State Monad}

\todo{Put all these to work. In particular, replace |put| by |modify|.}

\delete{
\paragraph{Properties} In absence of \eqref{eq:mplus-bind-dist} and \eqref{eq:mzero-bind-zero}, we instead assume the following properties.
\begin{align}
  |side m1 `mplus` side m2| &= |side (m1 >> m2)| \mbox{~~,}
    \label{eq:side-side} \\
  |put s >> (m1 `mplus` m2)| &= |(put s >> m1) `mplus` m2| \mbox{~~,}
    \label{eq:put-mplus}\\
  |get >>= (\x -> f x `mplus` m)| &=~ |(get >>= f) `mplus` m| \mbox{~~, |x| not free in |m|,}
      \label{eq:get-mplus}\\
  |(put s >> return x) `mplus`  m| &= |return x `mplus` (put s >> m)| ~~\mbox{,}
      \label{eq:put-ret-side}\\
  |side m `mplus` n| &=~ |n `mplus` side m| \mbox{~~, for |m :: Me N a|.}
        \label{eq:side-nd-mplus}
\end{align}
%if False
\begin{code}
propSideSide m1 m2 = (side m1 `mplus` side m2) === side (m1 >> m2)
propPutMPlus s m1 m2 = (put s >> (m1 `mplus` m2)) === ((put s >> m1) `mplus` m2)
propGetMPlus f m = (get >>= (\x -> f x `mplus` m)) === ((get >>= f) `mplus` m)
propPutRetSide s x m = ((put s >> return x) `mplus`  m) === (return x `mplus` (put s >> m))
propSideNdMPlus m n = (side m `mplus` n) === (n `mplus` side m)
\end{code}
%endif
They all show the sequential nature of |mplus| in this setting: in \eqref{eq:side-side}, adjacent |side| commands can be combined; in \eqref{eq:put-mplus} and \eqref{eq:get-mplus}, state operators bound before |mplus| branches can be bound to the leftmost branch, and in \eqref{eq:put-ret-side}, the effect of |put s >> return x| can be moved to the next branch. Finally, \eqref{eq:side-nd-mplus} allows side effects to commute with branches that only returns non-deterministic results.
By \eqref{eq:side-side} we have
\begin{equation}
 |side (put s) `mplus` side (put t) = side (put t)| \mbox{~~.}
  \label{eq:side-put-put}
\end{equation}
While we do not have right-distributivity in general, we may still assume distributivity for specific cases:
\begin{align}
 |get >>= \s -> f1 s `mplus` f2 s| &=~ |(get >>= f1) `mplus` (get >>= f2)| \mbox{~~, if |f1 s :: Me N a|}
    \label{eq:get-mplus-distr}\\
 |get >>= \s -> f1 s `mplus` f2 s| &=~ |(get >>= (\s -> f1 s `mplus` side (put s))) `mplus` (get >>= f2)| \mbox{~~.}
      \label{eq:get-mplus-side-distr}
\end{align}
%if False
\begin{code}
propGetMPlusDistr f1 f2 = (get >>= \x -> f1 x `mplus` f2 x) === ((get >>= f1) `mplus` (get >>= f2))
propGetMPlusSideDistr f1 f2 = (get >>= \x -> f1 x `mplus` f2 x) === ((get >>= (\x -> f1 x `mplus` side (put x))) `mplus` (get >>= f2))
\end{code}
%endif
Property \eqref{eq:get-mplus-distr} allows right-distributivity of |get| if the branches are only non-deterministic.
It helps to prove that |get| commutes with non-determinism.
In general cases, we need a |side (put x)| in the first branch to ensure that the second branch gets the correct value, as in \eqref{eq:get-mplus-side-distr}.
} %delete


\delete{
\subsection{State-Restoring Programs}
\label{sec:state-restoring}

In this section we present an interesting programming pattern that exploits left-distributivity \eqref{eq:bind-mplus-dist}.
Define the following variation of |put|:%
\footnote{The author owes the idea of |putR| to Tom Schrijvers. See Section \ref{sec:conclusion} for more details.}
\begin{spec}
putR :: {S s, N} `sse` eps => s -> Me eps ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}
\end{spec}
%if False
\begin{code}
putR :: (MonadPlus m, MonadState s m) => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~,"-}
\end{code}
%endif
and consider |putR s >> comp| where |comp| is some arbitray computation:
%if False
\begin{code}
putRExplain :: (MonadPlus m, MonadState s m) => s -> m b -> m b
putRExplain s comp =
\end{code}
%endif
\begin{code}
      putR s >> comp
 ===  (get >>= \s0 -> put s `mplus` side (put s0)) >> comp
 ===    {- monad law, left-distributivity \eqref{eq:bind-mplus-dist} -}
      get >>= \s0 -> (put s >> comp) `mplus` (side (put s0) >> comp)
 ===    {- by \eqref{eq:bind-mzero-zero}, |mzero >> comp = mzero| -}
      get >>= \s0 -> (put s >> comp) `mplus` side (put s0) {-"~~."-}
\end{code}
Thanks to left-distributivity \eqref{eq:bind-mplus-dist}, |(>> comp)| is promoted into |mplus|.
Furthermore, the |(>> comp)| after |side (put s0)| is discarded by
\eqref{eq:bind-mzero-zero}.
In words, |putR s >> comp| saves the current state, computes |comp| using state |s|, and restores the saved state, hence the subscript |R| in its name.

It might be instructive comparing |return x|, |m1 = put s >> return x|, and |m2 = putR s >> return x|, when run in initial state |s0|.
They all yield |x| as the result.
Certainly, |return x| terminates with state |s0|, and |m1| terminates with state |s|.
The program |m2| also terminates with state |s0|. However, |m2| does {\em not} equal |return x|!
There exist contexts, for example |(>>= f)|, with which we can tell them apart: in |return x >>= f|, |f| runs with state |s0|, while in |putR s >> return x >>= f|, |f| runs with state |s|, even though the program yields final state |s0|.

\begin{lemma}\label{lma:putR-basics}
The following laws regarding |putR| are true:
\begin{align*}
    |putR s >>= get| ~&=~ |putR s >>= return s| \mbox{~~,} \\
    |putR s >> putR s'| ~&=~ |putR s'|  \mbox{~~.}
\end{align*}
\end{lemma}

\begin{lemma}\label{lma:putR-nd-commute}
|putR| commutes with non-determinism. That is, |m >>= \x -> putR s >> return x = putR s >> m| for |m :: Me N a|.
\end{lemma}

Proof of Lemma \ref{lma:putR-basics} is a routine exercise. Lemma \ref{lma:putR-nd-commute} can be proved by induction on the syntax of |m|, using properties including \eqref{eq:side-side}, \eqref{eq:put-ret-side}, \eqref{eq:side-nd-mplus}, and \eqref{eq:get-mplus-side-distr}.

% \begin{proof}
% We present the proof for the |putR|-|putR| law for illustrative purpose. The proof demonstrates the use of \eqref{eq:put-mplus} and \eqref{eq:side-put-put}.
% \begin{spec}
%    putR s >> putR s'
% =  (get >>= \s0 -> (put s `mplus` side (put s0))) >>
%    (get >>= \s0 -> (put s' `mplus` side (put s0)))
% =    {- left-distributivity \eqref{eq:bind-mplus-dist} -}
%    get >>= \s0 -> (put s >> get >>= \s0 -> (put s' `mplus` side (put s0))) `mplus` side (put s0)
% =    {- |put|-|get| \eqref{eq:get-put} -}
%    get >>= \s0 -> (put s >> (put s' `mplus` side (put s))) `mplus` side (put s0)
% =    {- by \eqref{eq:put-mplus} -}
%    get >>= \s0 -> (put s >> puts') `mplus` side (put s) `mplus` side (put s0)
% =    {- |put|-|put| \eqref{eq:put-put} and \eqref{eq:side-put-put} -}
%    get >>= \s0 -> put s' `mplus` side (put s0)
% =  putR s' {-"~~."-}
% \end{spec}
% \end{proof}
Note that we do not have a |get|-|putR| law: |get >>= putR| does not equal |return ()|. To see that, observe that |(get >>= putR) >> put t| terminates with the initial state, while |return () >> put t| terminates with state |t|.

\paragraph{State-Restoration, Compositionally} Pushing the idea a bit further, we say that a monadic program |m| is {\em state-restoring} if, for all |comp|, the initial state in which |m >>= comp| is run is always restored when the computation finishes. Formally, it can be written as:
\begin{definition} |m :: {N, S s} `sse` eps => Me eps a| is called {\em state-restoring} if
  |m = get >>= \s0 -> m `mplus` side (put s0)|.
\end{definition}
Certainly, |putR s| is state-restoring. In fact, state-restoring programs can be built compositionally, using the following properties:
\begin{lemma} We have that
\begin{enumerate}
\item |mzero| is state-restoring,
\item |putR s| is state-restoring,
\item |guard p >> m| is state-restoring if |m| is,
\item |get >>= f| is state-restoring if |f x| is state-storing for all |x|, and
\item |m >>= f| is state restoring if |m| is state-restoring.
\end{enumerate}
\end{lemma}
Proof of these properties are routine exercises.

\paragraph{Incremental Updating and Restoration}
Identifying state-restoring programs helps to discover when we can update and restore the state in an incremental manner.
When the state |s| is a big structure, such as an array, it might not be feasible to perform |put s| that rewrites an entire array.
Instead one might use another command |modify f| that applies the function |f| to the state. It can be characterised by:
\begin{spec}
  modify f = get >>= \s -> put (f s) {-"~~,"-}
\end{spec}
but one may assume that, for commands such as |modify (\arr -> arr // [(i,x)])| (where |(// [(i,x)])| updates the |i|-th entry of the array to |x|), there exists a quicker implementation that mutates the array rather than creating a new array.

Given a function |next :: s -> s| that alters the state, and |prev :: s -> s| that is the inverse of |next|, we define the following state-restoring variation of |modify|:
\begin{spec}
modifyR :: {N, S s} `sse` eps -> (s -> s) -> (s -> s) -> Me eps ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{spec}
%if False
\begin{code}
modifyR :: (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{code}
%endif
such that |modifyR next prev >> comp| performs |modify next| before computation in |comp|, and |modify prev| afterwards. We have that:
\begin{lemma} Let |next| and |prev| be such that |prev . next = id|.
If |m| is state-restoring, we have
%if False
\begin{code}
putRSRModifyR ::
  (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m b -> m b
putRSRModifyR next prev m =
\end{code}
%endif
\begin{code}
  get >>= \s -> putR (next s) >> m {-"~~"-}=== {-"~~"-}
    modifyR next prev >> m {-"~~."-}
\end{code}
\end{lemma}
We look at its proof, which demonstrates the use of \eqref{eq:side-side} -- \eqref{eq:get-mplus}, monad laws, and laws regarding |get| and |put|.
For the rest of this pearl we use the following abbreviations:
\begin{code}
sidePut st  = side (put st)    {-"~~,"-}
sideMod f   = side (modify f)  {-"~~."-}
\end{code}
\begin{proof} We calculate:
%if False
\begin{code}
putRSRModifyRDer1 ::
  (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m b -> m b
putRSRModifyRDer1 next prev m =
\end{code}
%endif
\begin{code}
      modifyR next prev >> m
 ===    {- definiton of |modifyR|, |modify|, and left-distributivity \eqref{eq:bind-mplus-dist} -}
      (get >>= \s -> put (next s) >> m) `mplus` sideMod prev
 ===    {- by \eqref{eq:get-mplus} -}
      get >>= \s -> (put (next s) >> m) `mplus` sideMod prev {-"~~."-}
\end{code}
We focus on the part within |(get >>= \s -> _)|:
%if False
\begin{code}
putRSRModifyRDer2 ::
  (MonadPlus m, MonadState s m) =>
  (s -> s) -> (s -> s) -> s -> m a -> m a
putRSRModifyRDer2 next prev s m =
\end{code}
%endif
\begin{code}
      (put (next s) >> m) `mplus` sideMod prev
 ===    {- |m| state-restoring -}
      (put (next s) >> get >>= \s' -> m `mplus` sidePut s') `mplus` sideMod prev
 ===    {- |put|-|get| \eqref{eq:get-put} -}
      (put (next s) >> (m `mplus` sidePut (next s))) `mplus` sideMod prev
 ===    {- by \eqref{eq:put-mplus} -}
      put (next s) >> (m `mplus` sidePut (next s) `mplus` sideMod prev)
 ===    {- by \eqref{eq:side-side}, and |prev . next = id| -}
      put (next s) >> (m `mplus` sidePut s)
 ===    {- by \eqref{eq:put-mplus} -}
      (put (next s) >> m) `mplus` sidePut s {-"~~."-}
\end{code}
Put it back to the context |(get >>= \s -> _)|, and the expression simplifies to |get >>= \s -> putR (next s) >> m|.
\end{proof}

} %delete
