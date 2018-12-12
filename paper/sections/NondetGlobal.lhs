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

\todo{this motivation doesn't work as-is because our putR operation still performs the duplication}
For a monad with both non-determinism and state, right-distributivity \eqref{eq:mplus-bind-dist} implies that each non-deterministic branch has its own state. This is not costly for states consisting of linked data structures, for example the state |(Int, [Int], [Int])| in the |n|-queens problem. In some applications, however, the state might be represented by data structures, e.g. arrays, that are costly to duplicate. For such practical concerns, it is worth considering the situation when all non-deterministic branches share one global state.

Non-deterministic monads with a global state, however, is rather tricky.
One might believe that |M a = s -> ([a],s)| is a natural implementation of such a monad.
The usual, naive implementation of |(>>=)| using this representation, however, does not satisfy left-distributivity \eqref{eq:bind-mplus-dist}, violates monad laws, and is therefore not even a monad.
%See Section \ref{sec:conclusion} for previous work on construction of a correct monad.
\footnote{
The type |ListT (State s)| generated using the now standard Monad Transformer Library~\cite{MTL:14} expands to essentially the same implementation, and is flawed in the same way.
More careful implementations of |ListT|, which does satisfy \eqref{eq:bind-mplus-dist} and the monad laws, have been proposed~\cite{Gale:07:ListT, Volkov:14:list-t}.
Effect handlers, such as that of Wu~\shortcite{Wu:14:Effect} and Kiselyov and Ishii~\shortcite{KiselyovIshii:15:Freer}, do produce correct implementations by running the handler for non-determinism before that of state.
}

Even after we do have a non-deterministic, global-state passing implementation that is a monad, its semantics can sometimes be surprising.
In |m1 `mplus` m2|, the computation |m2| receives the state computed by |m1|.
Thus |mplus| is still associative, but certainly cannot be commutative.
As mentioned in Section \ref{sec:right-distr-local-state}, right-distributivity \eqref{eq:mplus-bind-dist} implies commutativity of |mplus|.
Contravariantly, \eqref{eq:mplus-bind-dist} cannot be true when the state is global.
Right-zero \eqref{eq:mzero-bind-zero} does not hold either: |mzero| simply fails, while |put s >> mzero|, for example, fails with an altered global state.
These significantly limit the properties we may have.

\subsection{Chaining Using Non-deterministic Choice}
\label{sec:chaining}

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
We can even go a bit further by defining the following variations of |put|:
\begin{spec}
putR :: {S s, N} `sse` eps => s -> Me eps ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~."-}
\end{spec}
%if False
\begin{code}
putR :: (MonadPlus m, MonadState s m) => s -> m ()
putR s = get >>= \s0 -> put s `mplus` side (put s0) {-"~~."-}
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
In words, |putR s >> comp| saves the current state, computes |comp| using state |s|, and restores the saved state!
The subscript |R| stands for ``restore.''

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
Unfortunately this is not the case: |putR| does satisfy |put|-|put|~\eqref{eq:put-put} and |put|-|get|~\eqref{eq:put-get}, but |get|-|put|~\eqref{eq:get-put} fails ---
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
Meanwhile, |return () >> put t = put t|. The two sides are not equal when |s /= t|.

In a global-state setting, reasoning about combination of |mplus| and |(>>=)| is tricky because, due to \eqref{eq:bind-mplus-dist}, every occurrence of |mplus| is a point where future code can be inserted.
This makes it hard to reason about programs compositionally --- some properties hold only when we take the entire program into consideration.

It turns out that all properties we need do hold, provided that {\em all} occurrences of |put| are replaced by |putR| --- problematic contexts such as |put t| above is thus ruled out.
However, that ``all |put| replaced by |putR|'' is a global property, and to properly talk about it we have to formally define contexts, which is what we will do in Section~\ref{sec:ctxt-trans}.

\subsection{Contexts and Translation}
\label{sec:ctxt-trans}

%format hole = "\square"
%format apply z (e) = z "\lbrack" e "\rbrack"
%format <||> = "\mathbin{\scaleobj{0.8}{\langle[\!]\rangle}}"
%format getD = "\scaleobj{0.8}{\langle}\Varid{get}\scaleobj{0.8}{\rangle}"
%format putD = "\scaleobj{0.8}{\langle}\Varid{put}\scaleobj{0.8}{\rangle}"
%format retD = "\scaleobj{0.8}{\langle}\Varid{ret}\scaleobj{0.8}{\rangle}"
%format emptyListLit = "`[]"

\begin{figure}
\centering
\small
\subfloat[]{
\begin{minipage}{0.5\textwidth}
\begin{spec}
data Prog a where
  Return  :: a -> Prog a
  mzero   :: Prog a
  mplus   :: Prog a -> Prog a -> Prog a
  Get     :: (S -> Prog a) -> Prog a
  Put     :: S -> Prog a -> Prog a

data Env (l :: [*]) where
  Nil  :: Env emptyListLit
  Cons :: a -> Env l -> Env (a:l)

type OProg e a = Env e -> Prog a
\end{spec}
\end{minipage}
}
\subfloat[]{
\begin{minipage}{0.5\textwidth}
\begin{spec}
data Ctx e1 a e2 b where
  hole    :: Ctx e1 a e2 b
  COr1    :: Ctx e1 a e2 b -> OProg e2 b -> Ctx e1 a e2 b
  COr2    :: OProg e2 b -> Ctx e1 a e2 b -> Ctx e1 a e2 b
  CPut    :: (Env e2 -> S) -> Ctx e1 a e2 b -> Ctx e1 a e2 b
  CGet    :: (S -> Bool) -> Ctx e1 a (S:e2) b
          -> (S -> OProg e2 b) -> Ctx e1 a e2 b
  CBind1  :: Ctx e1 a e2 b -> (b -> OProg e2 c) -> Ctx e1 a e2 c
  CBind2  :: OProg e2 a -> Ctx e1 b (a::e2) c -> Ctx e1 b e2 c
\end{spec}
\end{minipage}
}
\quad
\subfloat[]{
  \begin{minipage}{0.5\textwidth}
    \begin{spec}
      (>>=) :: Prog a -> (a -> Prog b) -> Prog b
      Return x       >>= f = f x
      mzero          >>= f = mzero
      (m `mplus` n)  >>= f = (m >>= f) `mplus` (n >>= f)
      Get k          >>= f = Get (\x -> k x >>= f)
      Put x e        >>= f = Put x (e >>= k)
    \end{spec}
  \end{minipage}
}
\subfloat[]{
  \begin{minipage}{0.5\textwidth}
    \begin{spec}
      run   :: Prog a -> Dom a
      <||>  :: Dom a -> Dom a -> Dom a
      retD  :: S -> Dom a
      getD  :: (S -> Dom a) -> Dom a
      putD  :: S -> Dom a -> Dom a
    \end{spec}
  \end{minipage}
}
\quad
\caption{(a) Syntax for programs. (b) Syntax for contexts. (c) Bind operator. (d) Semantic domain.}
\label{fig:context-semantics}
\end{figure}

In this section we will state clearly what laws we expect from a global-state non-deterministic monad and show that, under our semantical assumptions, a program we get by replacing all occurrences of |put| by |putR| does satisfy all laws we demand of a local-state non-deterministic monad.
All these concepts need to be defined more formally, however.

In Figure~\ref{fig:context-semantics}(a), we define a syntax for nondeterministic, stateful, closed programs |Prog| in a free monad style: |Get| and |Put| take continuations, while |(>>=)| is defined as a function in Figure~\ref{fig:context-semantics}(c).
One can see that the definition of |(>>=)| has laws \eqref{eq:bind-mplus-dist} and \eqref{eq:mzero-bind-zero} built-in.
We also define open programs |OProg| (that is, programs that may contain free variables) as functions that construct a closed program from an environment that contains the variables which occur free in the program.
Environments |Env|, in turn, are defined as heterogeneous lists.

Figure~\ref{fig:context-semantics}(b) provides the definition for single-hole contexts (|Ctx|).
A context of type |Ctx e1 a e2 b| can be interpreted as a function that, given a program that returns a value of type |b| under environment |e2| (in other words: the type and environment for the hole), produces a program that returns a value of type |a| under environment |e1| (the type and environment for the entire program).
Given a context |C|, filling the hole by |e| is denoted by |apply C e|.

In the previous sections we have been mixing syntax and semantics.
Now we assume a semantic domain |Dom| (Figure~\ref{fig:context-semantics}(d)), and a function |run :: Prog a -> Dom a| that ``runs'' a program |Prog a| into a value in |Dom a|, and several operators |(<||||>)|, |getD|, and |putD|, shown in Figure~~\ref{fig:context-semantics}(c).  Semantics of |mplus|, |get|, and |put| may thus be defined compositionally:
\begin{spec}
run (m1 `mplus` m2) = run m1 <||> run m2 {-"~~,"-}
run (Get k) = getD (\s -> run (k s)) {-"~~,"-}
run (Put x m) = putD x (run m) {-"~~."-}
\end{spec}


In order to lighten the notational burden, we define a notion of ``contextual equivalence'' of programs:
\newcommand{\CEq}{\triangleq_\mathtt{GS}}
\begin{align*}
  |m1| \CEq |m2| \iff \forall C. |run (apply C m1)| = |run (apply C m2)|
\end{align*}

The following laws are assumed to hold.
There should be nothing surprising here:
they are merely variations of the monad laws \eqref{eq:monad-bind-ret} and \eqref{eq:monad-assoc}, \eqref{eq:bind-mzero-zero} and the monoid property of |mplus|, and laws \eqref{eq:put-put} -- \eqref{eq:get-get} regard states, which we discussed earlier.


\begin{align*}
|m >>= return|                      &\CEq |m| \mbox{~~,}\\
|(m >>= f) >>= g|                   &\CEq |m >>= \x -> (f x >>= g)|\mbox{~~,}\\
|mzero `mplus` m|                   &\CEq |m `mplus` mzero = m|\mbox{~~,}\\
|(m1 `mplus` m2) `mplus` m3|        &\CEq |m1 `mplus` (m2 `mplus` m3)|\mbox{~~,}\\
|mzero >>= k|                       &\CEq |mzero|\mbox{~~,}\\
|Get (\s1 -> Get (\s2 -> k s1 s2))| &\CEq |(Get (\s1 -> k s1 s1))|\mbox{~~,}\\
|Get (\s -> Put s m)|               &\CEq |m|\mbox{~~,}\\
|Put x (Get k)|                     &\CEq |Put x (k x)|\mbox{~~,}\\
|Put x (Put y m)|                   &\CEq |Put y m|\mbox{~~.}
\end{align*}
\todo{In get-put: should we qualify by saying that s must not occur free in m? Alternatively, we might split the law into two: $\mathit{Get}~(\lambda s \rightarrow m) = m ~ \text{if s not free in m}$ and $\mathit{Get}~(\lambda s \rightarrow \mathit{Put}~s~m) = \mathit{Get}~(\lambda s \rightarrow m)$ )}

We require some additional laws to write our proofs.
We introduce law~\eqref{eq:put-mplus-g}, which states that a |Put| prefixing the first non-deterministic branch can be pulled out of that branch --- either way, the effect of |Put| applies to the first branch.
\begin{align}
|Put x m1 `mplus` m2| \CEq |Put x (m1 `mplus` m2)| \label{eq:put-mplus-g}
\end{align}
Note that this law is specific to \emph{global-state} non-deterministic monads.

We will also require a law that allows us to do the same for |Get|. This law is not specifically tied to global-state semantics.
\begin{align}
|Get k `mplus` m| \CEq |Get (\x -> k x `mplus` m)|\mbox{~~, |x| not in |k| and |m|} \label{eq:get-mplus}
\end{align}

In order to complete our proofs we will require the property that |Put| distributes into |(`mplus`)| at the top level if the first branch does not modify the state.
We will only be able to prove this property if we assume the following law, which shall form the base case of that proof:
\begin{align}
|run (Put x (return y `mplus` m))| = |run (Put x (return y) `mplus` Put x m)| \label{eq:put-ret-mplus-g}\mbox{~~.}
\end{align}
It bears repeating that we expect it to hold only at the top level --- no context is involved.
For example, the context |cBindProg1 hole (Put w)| \footnote{where |cBindProg1 ctx k = CBind1 ctx (const . k)|} can discriminate between the two sides of the equation of law~\ref{eq:put-ret-mplus-g}.

In Appendix~\ref{sec:GSMonad} we present one implementation of |Dom| and its operators that satisfy all the laws in this section.

Let |trans :: Prog a -> Prog a| be the function that replaces all occurrences of |put| in its input program by |putR|. Define:
\begin{spec}
eval :: Prog a -> Dom a
eval = run . trans {-"~~."-}
\end{spec}

In a similar fashion to the ``contextual equivalence'' shorthand, we define a ``contextual equivalence under simulated local-state semantics''.
\newcommand{\CEqLS}{\triangleq_\mathtt{LS}}
\begin{align*}
  |m1| \CEqLS |m2| \iff \forall C. |eval (apply C m1)| = |eval (apply C m2)|
\end{align*}

We have proved the following theorems:
\begin{theorem} \label{thm:putG-state-laws}
The four state laws \eqref{eq:put-put} -- \eqref{eq:get-get} hold for the translated program, in the sense below:
\begin{align*}
  |Get (\s1 -> Get (\s2 -> k s1 s2))| &\CEqLS |Get (\s1 -> k s1 s1)| \mbox{~~,}\\
  |Put x (Get k)|                     &\CEqLS |Put x (k x)|\mbox{~~,}\\
  |Get (\s -> Put s k))|              &\CEqLS |k| \mbox{~~, |s| not free in |k|,} \\
  |Put x (Put y m)|                   &\CEqLS |Put y m|\mbox{~~.}
\end{align*}
\end{theorem}
Proof of these laws basically start with promoting |trans| inside, before applying \eqref{eq:put-mplus-g} and other laws mentioned earlier in this section.

\begin{theorem}\label{thm:putG-mplus-distr}
  In the translated program, |putR| distributes into |mplus| and is cancelled by |mzero|:
\begin{align*}
  |Put x mzero|               &\CEqLS |mzero| \mbox{~~,}\\
  |Put x m1 `mplus` Put x m2| &\CEqLS |Put x (m1 `mplus` m2)| \mbox{~~.}
\end{align*}
\end{theorem}
\noindent
The two properties in Theorem~\ref{thm:putG-mplus-distr} allow us to show that |putR| commutes with non-deterministic choice (i.e. |putR v >> choose x y >> k = choose x y >> putR v >> k| where |choose x y = return x `mplus` return y| \todo{Check this; also where do we prove this in the mechanization?}).
Proof of these laws uses \eqref{eq:put-mplus-g} and \eqref{eq:get-mplus}.
In addition, both Theorem~\ref{thm:putG-state-laws} and \ref{thm:putG-mplus-distr} uses the following crucial lemma, proved by
induction on |m1| and |C|, using~\eqref{eq:put-ret-mplus-g}.
\begin{lemma} |run (Put x (trans m1 `mplus` m2)) = run (Put x (trans m1) `mplus` Put x m2)|.
\end{lemma}
Again, this lemma only holds at the top-level. The counter-example from law~\ref{eq:put-ret-mplus-g} also works here.
\todo{we've proved this for simplified contexts, but it doesn't hold in contexts with bind}

Finally, we need a congruence theorem:
\begin{theorem} For all |m1|, |m2| and |n| we have:
\begin{spec}
  (forall C k, eval (apply C (m1 >>= k) = eval (apply C (m2 >>= k)))) =>
    (forall C k, eval (apply C ((n >>= \x -> m1) >>= k)) = eval (apply C ((n >>= \x -> m2) >>= k))) {-"~~."-}
\end{spec}
\end{theorem}%
\noindent The proof proceeds by induction on |n|.
\todo{It is a crucial property. More explanations?}

\subsection{Backtracking with a Global State Monad}
\todo{This interface still doesn't really support mutable state. Do we want to go into this level of technical detail?}
There is still one technical detail to to deal with before we deliver a backtracking algorithm that uses a global state.
As mentioned in Section~\ref{sec:chaining}, rather than using |put|, such algorithms typically use a pair of commands |modify prev| and |modify next|, with |prev . next = id|, to update and restore the state.
This is especially true when the state is implemented using an array or other data structure that is usually not overwritten in its entirety.
Following a style similar to |putR|, this can be modelled by:
\begin{spec}
modifyR :: {N, S s} `sse` eps -> (s -> s) -> (s -> s) -> Me eps ()
modifyR next prev = modify next `mplus` side (modify prev) {-"~~."-}
\end{spec}
%if False
\begin{code}
modifyR :: (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m ()
modifyR next prev =  modify next `mplus` side (modify prev) {-"~~,"-}
\end{code}
%endif
One can see that |modifyR next prev >> m| expands to
|(modify next >> m) `mplus` side (modify prev)|, thus the two |modify|s are performed before and after |m|.

Assume that |s0| is the current state.
Is it safe to replace |putR (next s0) >> m| by |modifyR next prev >> m|?
We can do so if we are sure that |m| always restores the state to |s0| before |modify prev| is performed.
We say that a monadic program |m| is {\em state-restoring} if, for all |comp|, the initial state in which |m >>= comp| is run is always restored when the computation finishes. Formally, it can be written as:
\begin{definition} |m :: {N, S s} `sse` eps => Me eps a| is called {\em state-restoring} if
  |m = get >>= \s0 -> m `mplus` side (put s0)|.
\end{definition}
Certainly, |putR s| is state-restoring. In fact, the following properties allow state-restoring programs to be built compositionally:
\begin{lemma} We have that
\begin{enumerate}
\item |mzero| is state-restoring,
\item |putR s| is state-restoring,
\item |guard p >> m| is state-restoring if |m| is,
\item |get >>= f| is state-restoring if |f x| is state-storing for all |x|, and
\item |m >>= f| is state restoring if |m| is state-restoring.
\end{enumerate}
\end{lemma}
\noindent Proof of these properties are routine exercises.
With these properties, we also have that, for a program |m| written using our program syntax, |trans m| is always state-restoring.
The following lemma then allows us to replace certain |putR| by |modifyR|:
\begin{lemma} Let |next| and |prev| be such that |prev . next = id|.
If |m| is state-restoring, we have
%if False
\begin{code}
putRSRModifyR ::
  (MonadPlus m, MonadState s m) => (s -> s) -> (s -> s) -> m b -> m b
putRSRModifyR next prev m =
\end{code}
\begin{code}
  get >>= \s -> putR (next s) >> m {-"~~"-}=== {-"~~"-}
    modifyR next prev >> m {-"~~."-}
\end{code}
%endif
\begin{equation*}
  |get >>= \s -> putR (next s) >> m| ~=~
    |modifyR next prev >> m| \mbox{~~.}
\end{equation*}
\end{lemma}

\paragraph{Backtracking using a global-state monad}
Recall that, in Section~\ref{sec:solve-n-queens},
we showed that a problem formulated by |unfoldM p f z >>= assert (all ok . scanlp oplus st)| can be solved by a hylomorphism |solve p f ok oplus st z|,
run in a non-deterministic local-state monad.
Putting all the information in this section together,
we conclude that solutions of the same problem can be computed,
in a non-deterministic global-state monad,
by |run (solveR p f ok oplus ominus st z)|, where |(`ominus` x) . (`oplus` x) = id| for all |x|, and |solveR| is defined by:
\begin{spec}
solveR :: {N, S s} `sse` eps =>  (b -> Bool) -> (b -> Me eps (a, b)) ->
                                 (s -> Bool) -> (s -> a -> s) -> (s -> a -> s) -> s -> b -> Me eps [a]
solveR p f ok oplus ominus st z = putR st >> hyloM odot (return []) p f z
  where x `odot` m =  (get >>= guard . ok . (`oplus` x)) >>
                      modifyR (`oplus` x) (`ominus` x) >> ((x:) <$> m) {-"~~."-}
\end{spec}
Note that the use of |run| enforces that the program is run as a whole, that is, it cannot be further composed with other monadic programs.



\paragraph{|n|-Queens using a global state}
To wrap up, we revisit the |n|-queens puzzle.
Recall that, for the puzzle, |(i,us,ds) `oplus` x = (1 + i,  (i+x):us,  (i-x):ds)|.
By defining |(i,us,ds) `ominus` x  = (i - 1, tail us, tail ds)|,
we have |(`ominus` x) . (`oplus` x) = id|.
One may thus compute all solutions to the puzzle,
in a scenario with a shared global state, by |run (queensR n)|,
where |queens| expands to:
\begin{spec}
queensR n = put (0,[],[]) >> queensBody [0..n-1] {-"~~,"-}

queensBody []  =  return []
queensBody xs  =  select xs >>= \(x,ys) ->
                  (get >>= (guard . ok . (`oplus` x))) >>
                  modifyR (`oplus` x) (`ominus` x) >> ((x:) <$> queensBody ys) {-"~~,"-}
  where  (i,us,ds) `oplus` x   = (1 + i,  (i+x):us,  (i-x):ds)
         (i,us,ds) `ominus` x  = (i - 1,  tail us,   tail ds)
         ok (_,u:us,d:ds) = (u `notElem` us) && (d `notElem` ds) {-"~~."-}
\end{spec}

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
