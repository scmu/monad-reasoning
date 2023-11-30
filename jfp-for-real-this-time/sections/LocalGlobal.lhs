\section{Modeling Local State With Global State}
\label{sec:local-global}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module LocalGlobal where

import Background
import Overview
import Control.Monad (ap, liftM, liftM2)
-- import qualified Control.Monad.Trans.State.Lazy as S
import Control.Monad.Trans.State.Lazy (StateT (StateT), runStateT)

{-
class (MState s m, MNondet m) => MSt s m where
    alph :: n a -> m a

local :: MSt s n => StateT s m a -> n a
local x = do
    s <- get
    (a, s') <- alph (runStateT x s)
    put s'
    etan a

etan :: Monad n => a -> n a
etan = return

etals :: (MState s m, MNondet m) => a -> StateT s m a
etals x = StateT $ \s -> return (x, s)

muls :: (MState s m, MNondet m) => StateT s m (StateT s m a) -> StateT s m a
muls mx = StateT $ \s -> runStateT mx s >>= \(x, s') -> runStateT x s'

mun :: MSt s n => n (n a) -> n a
mun nx = alph nx >>= id -- do
    -- x <- alph nx
    -- x
-}

\end{code}
%endif

This section studies two flavors of effect interaction between state and
nondeterminism: local-state and global-state semantics.  Local
state is a higher-level effect than globale state.
% and we show that we can simulate the former using the latter.
%
In a program with local state, each nondeterministic branch has its own local
copy of the state.  This is a convenient programming abstraction provided
by many systems that solve search problems, e.g., Prolog.  In contrast, global
state linearly threads a single state through the nondeterministic
branches. This can be interesting for performance reasons: we can limit memory
use by avoiding multiple copies, and perform in-place updates to reduce allocation
and garbage collection, and to improve locality.

% The appearance of local state is obtained by the well-known backtracking
% technique, undoing changes to the state when going to the next branch.
% Therefore, local state is what Gibbons and Hinze call ``backtrackable state''
% \birthe{need citation?}.
% Backtracking is relatively efficient: remembering what to undo often requires
% less memory than creating multiple copies of the state, and undoing changes
% often takes less time than recomputing the state from scratch.
% \wenhao{I think the implementation of local state we give in 4.1 doesn't use the backtracking technique.}
% Global state is sometimes called non-backtrackable state.
In this section, we first formally characterise local-state and
global-state semantics, and then define a translation from the former
to the latter which uses the mechanism of nondeterminism to store
previous states and insert backtracking branches.
%

%-------------------------------------------------------------------------------
\subsection{Local-State Semantics}
\label{sec:local-state}

When a branch of a nondeterministic computation runs into a dead end and
the continuation is picked up at the most recent branching point,
any alterations made to the state by the terminated branch are invisible to
the continuation.
We refer to this semantics as \emph{local-state semantics}.
%
\citet{Gibbons11} also call it backtrackable state.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph*{Interaction Laws}\
\paragraph*{The Local-State Laws}\
The following two laws characterise the local-state semantics for a monad
with state and nondeterminism:
\begin{alignat}{2}
    % &\mbox{\bf get-right-identity}:\quad &
    % |get >> mzero| &= |mzero|~~\mbox{,} \label{eq:get-right-identity}\\
    &\mbox{\bf put-right-identity}:\quad &
    |put s >> mzero| &= |mzero|~~\mbox{,} \label{eq:put-right-identity}\\
    % &\mbox{\bf get-left-distributivity}:~ &
    % |get >>= (\x -> k1 x `mplus` k2 x)| &= |(get >>= k1) `mplus` (get >>= k2)| ~~\mbox{.} \label{eq:get-left-dist}\\
    &\mbox{\bf put-left-distributivity}:~ &
    |put s >> (m1 `mplus` m2)| &= |(put s >> m1) `mplus` (put s >> m2)| ~~\mbox{.} \label{eq:put-left-dist}
\end{alignat}

The equation (\ref{eq:put-right-identity}) expresses that |mzero| is the right
identity of |put|; it annihilates state updates.  The other law expresses that
|put| distributes from the left in |mplus|.

These two laws only focus on the interaction between |put| and
nondeterminism. The following laws for |get| can be derived from other
laws. The proof can be found in \Cref{app:local-law}.
\begin{alignat}{2}
    &\mbox{\bf get-right-identity}:\quad &
    |get >> mzero| &= |mzero|~~\mbox{,} \label{eq:get-right-identity}\\
    &\mbox{\bf get-left-distributivity}:~ &
    |get >>= (\x -> k1 x `mplus` k2 x)| &= |(get >>= k1) `mplus` (get >>= k2)| ~~\mbox{.} \label{eq:get-left-dist}
\end{alignat}

If we take these four equations together with the left-identity and right-distributivity
laws of nondeterminism, we can say that
that nondeterminism and state ``commute'';
if a |get| or |put| precedes a |mzero| or |`mplus`|, we
can exchange their order (and vice versa).

% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph{Interaction Laws}
% The following laws characterize the local state semantics for a monad |m|
% with state and nondeterminism:
% \begin{alignat}{2}
%     &\mbox{\bf right-identity}:\quad &
%     |m >> mzero| &= |mzero|~~\mbox{,} \label{eq:right-identity}\\
%     &\mbox{\bf left-distributivity}:~ &
%     |m >>= (\x -> f1 x `mplus` f2 x)| &= |(m >>= f1) `mplus` (m >>= f2)| ~~\mbox{.} \label{eq:left-dist}
% \end{alignat}
% Note that the computation |m| on the lefthand side in the right-identity law
% (\ref{eq:right-identity})
% may contain some effects that do not occur in the righthand side.
% Similarly, in the left-distributivity law (\ref{eq:left-dist}),
% effects in the computation |m|
% occur once on the lefthand side and twice on the
% righthand side.
% This is a typical property of local state: Effects are distributed into branches
% and
% annihilated by failure.
%
% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph{Commutativity}
% Having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) leads to profound
% consequences on the semantics and implementation of monadic programs.
% To begin with, (\ref{eq:left-dist}) implies that for |mplus| we have some limited
% notion of commutativity.
% For instance, both the left and right distributivity rules can be applied to the
% term |(return x `mplus` return y) >>= \z -> return z `mplus` return z|.
% It is then easy to show that this term must be equal to both
% |return x `mplus` return x `mplus` return y `mplus` return y|
% and
% |return x `mplus` return y `mplus` return x `mplus` return y|
% \footnote{Gibbons and Hinze \cite{Gibbons11} were mistaken in their claim that the type
% |s -> [(a, s)]| constitutes a model of their backtrackable state laws.
% It is not a model because its |`mplus`| does not commute with itself.
% One could consider a relaxed semantics that admits |s ->[(a, s)]|,
% but that is not the focus of this paper.}.
% In fact, having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) gives us very
% strong and useful commutative properties.
%
% \begin{definition}[Commutativity]
% Let |m| and |n| be two monadic programs such that |x| does not occur free in |m|,
% and |y| does not occur free in |n|. We say |m| and |n| commute if
% \begin{alignat}{2}
%     &\mbox{\bf commutativity}:\quad &
%     |m >>= \x -> n >>= \y -> f x y| &= |n >>= \y -> m >>= \x -> f x y|~~\mbox{.} \label{eq:commutativity}
% \end{alignat}
% We say that effects |eps| and |delta| commute if any |m| and |n| commute
% as long as their only effects are |eps| and |delta|.
% \end{definition}
%
% One important result is that, in local-state semantics, nondeterminism commutes
% with any effect.
%
% \begin{theorem} \label{thm:nondet-comm}
% If right-identity (\ref{eq:right-identity})
% and left-distributivity (\ref{eq:left-dist}) hold in addition to the other laws,
% nondeterminism commutes with any effect.
% \end{theorem}
%
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{Implementation}\
Implementation-wise, the laws
imply that each nondeterministic branch has its own copy of the state.
%
For instance, \Cref{eq:put-left-dist} gives us
< put 42 (put 21 `mplus` get) = (put 42 >> put 21) `mplus` (put 42 >> get)
% To see that, let |s = 1|, |m1 = put 2| and |m2 = get| in
% (\ref{eq:put-left-dist}).
The state we |get| in the second branch is still |42|, despite the
|put 21| in the first branch.

One implementation satisfying the laws is
< type Local s m a = s -> m (a, s)
where |m| is a nondeterministic monad, the simplest structure of which is a list.
This implementation is exactly that of |StateT s m a|
in the Monad Transformer Library \citep{mtl} which we have introduced in
\Cref{sec:combining-effects}.

With effect handling \citep{Kiselyov15, Wu14}, we get the local state semantics when
we run the state handler before the nondeterminism handler:
\begin{code}
hLocal :: Functor f => Free (StateF s :+: NondetF :+: f) a -> (s -> Free f [a])
hLocal = fmap (fmap (fmap fst) . hNDf) . runStateT . hState
\end{code}

In the case where the remaining signature is empty (|f = NilF|), we get:
%
< fmap hNil . hLocal :: Free (StateF s :+: NondetF :+: NilF) a -> (s -> [a])
%
Here, the result type |(s -> [a])| differs from |s -> [(a,s)]| in that it produces
only a list of results (|[a]|) and not pairs of results and their final state
(|[(a,s)]|). The latter is needed for |Local s m| to have the structure of a monad, in particular
to support the modular composition of computations with |(>>=)|. Such is not needed for the carriers of handlers, because
the composition of computations is taken care of by the |(>>=)| operator of the free monad.

%-------------------------------------------------------------------------------
\subsection{Global-State Semantics}
\label{sec:global-state}

Alternatively, one can choose a semantics where state reigns over nondeterminism.
In this case of non-backtrackable state, alterations to the state persist over
backtracks. Because only a single state is shared over all branches of
nondeterministic computation, we call this state the \emph{global-state
semantics}.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{The Global-State Law}\
The global-state semantics sets apart non-backtrackable state from
backtrackable state.
%
In addition to the general laws for nondeterminism
((\ref{eq:mzero}) -- (\ref{eq:mzero-zero})) and state
((\ref{eq:put-put}) -- (\ref{eq:get-get})), we provide a \emph{global-state law}
to govern the interaction between nondeterminism and state.
\begin{alignat}{2}
    &\mbox{\bf put-or}:\quad &
    |(put s >> m) `mplus` n| &= |put s >> (m `mplus` n)|~~\mbox{.} \label{eq:put-or}
\end{alignat}

This law allows lifting a |put| operation from the left branch of a
nondeterministic choice.
For instance, if |m = mzero| in the left-hand side of the equation,
then under local-state semantics
(laws (\ref{eq:mzero}) and (\ref{eq:put-right-identity}))
the left-hand side becomes equal to |n|,
whereas under global-state semantics
(laws (\ref{eq:mzero}) and (\ref{eq:put-or}))
the equation simplifies to |put s >> n|.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{Implementation}\
%
% This law leaves us free to choose from a large space of
% implementations with different properties.
% For example, in any given implementation, the programs
% |return x `mplus` return y| and |return y `mplus` return x| can be considered
% either semantically identical or distinct.
% The same goes for the programs |return x `mplus` return x| and |return x|
% or other examples. Also, there is no law that regulates |put s >> mzero|, which
% means that it may be distinguished from |mzero|.
% \wenhao{I'm confused. First, the first two equations are just about
% nondeterminism, right? Second, the third law |put s >> mzero = mzero|
% must not hold because of \Cref{eq:put-or}.}
% TOM: I think we better drop this altogether. It is not helpful.
Figuring out a correct implementation for the global-state monad is tricky.
One might believe that |Global s m a = s -> (m a, s)|
is a natural implementation of such a monad.
However, the usual naive implementation of |(>>=)| for it does not satisfy
right-distributivity (\ref{eq:mplus-dist}) and is therefore not even a monad.
The type |ListT (State s)| from the Monad Transformer Library \citep{mtl}
expands to essentially the same implementation with
monad |m| instantiated by the list monad.
This implementation has the same flaws.
More careful implementations of |ListT| (often referred to as
``|ListT| done right'') satisfying right-distributivity
(\ref{eq:mplus-dist}) and other monad laws have been proposed by
\citet{Volkov14, Gale}.
%
The following implementation is essentially that of Gale.
\begin{code}
newtype Global s a = Gl { runGl :: s -> (Maybe (a, Global s a), s) }
\end{code}
The |Maybe| in this type indicates that a computation may fail to produce a
result. However, since the |s| is outside of the |Maybe|, a modified state
is returned even if the computation fails.
This |Global s a| type is an instance of the |MState| and |MNondet|
typeclasses.

%if False
\begin{code}
instance Functor (Global s) where
    fmap = liftM

instance Applicative (Global s) where
    pure = return
    (<*>) = ap

instance Monad (Global s) where
    return x = Gl (\s -> (Just (x, mzero), s))
    p >>= k = Gl (\s -> case runGl p s of
        (Nothing, t) -> (Nothing, t)
        (Just (x, q), t) -> runGl (k x `mplus` (q >>= k)) t
        )
\end{code}
%endif

\begin{minipage}{0.5\textwidth}
\begin{code}
instance MNondet (Global s) where
    mzero        = Gl (\s ->  (Nothing, s))
    p `mplus` q  = Gl (\s ->  case runGl p s of
        (Nothing,      t)   ->   runGl q t
        (Just (x, r),  t)   ->   (Just (x, r `mplus` q), t))
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{code}
instance MState s (Global s) where
    get    =  Gl  (\s  ->  (Just (s,   mzero),   s))
    put s  =  Gl  (\ _  ->  (Just ((),  mzero),   s))


\end{code}
\end{minipage}

Failure, of course, returns an empty continuation and an unmodified state.
Branching first exhausts the left branch before switching to the right branch.

Effect handlers \citep{Kiselyov15, Wu14} also provide implementations
that match our intuition of non-backtrackable computations.
%  if we run the handler for nondeterminism before that for state.
%
The global-state semantics can be implemented by simply switching the
order of the two effect handlers compared to the local state handler
|hLocal|.
% < hGlobal :: Functor f => Free (StateF s :+: NondetF :+: f) a -> s
% -> Free f [a]
% < hGlobal = fmap (fmap fst) . runStateT . hState . hNDf
\begin{code}
hGlobal :: (Functor f) => Free (StateF s :+: NondetF :+: f) a -> (s -> Free f [a])
hGlobal = fmap (fmap fst) . runStateT . hState . hNDf . comm2
\end{code}
This also runs a single state through a nondeterministic computation.
The |comm2| isomorphism swaps the order of two functors in the
co-product signature of the free monad in order to let |hLocal| and
|hGlobal| have the same type signature.
\begin{code}
comm2 :: (Functor f1, Functor f2, Functor f) => Free (f1 :+: f2 :+: f) a -> Free (f2 :+: f1 :+: f) a
comm2 (Var x)             = Var x
comm2 (Op (Inl k))        = (Op . Inr . Inl)  (fmap comm2 k)
comm2 (Op (Inr (Inl k)))  = (Op . Inl)        (fmap comm2 k)
comm2 (Op (Inr (Inr k)))  = (Op . Inr . Inr)  (fmap comm2 k)
\end{code}
% By incorporating |comm2| in the definition of |hGlobal|, |hLocal| and |hGlobal| have exactly the same signature.

In the case where the remaining signature is empty (|f = NilF|), we get:
%
< fmap hNil . hGlobal :: Free (StateF s :+: NondetF :+: NilF) a -> (s -> [a])
%
The carrier type is again simpler than |Global s a| because it does not have to
support the |(>>=)| operator.

%-------------------------------------------------------------------------------
% \subsection{Transforming Between Local State and Global State}
\subsection{Simulating Local State with Global State}
\label{sec:transforming-between-local-and-global-state}
\label{sec:local2global}

Both local state and global state have their own laws and semantics.
Also, both interpretations of nondeterminism with state have their own
advantages and disadvantages.

Local-state semantics imply that each nondeterministic branch has its own state.
This may be expensive if the state is represented by data structures, e.g. arrays,
that are costly to duplicate.
For example, when each new state is only slightly different from the previous,
we have a wasteful duplication of information.

Global-state semantics, however, threads a single state through the entire
computation without making any implicit copies.
Consequently, it is easier to control resource usage and apply
optimisation strategies in this setting.
% Therefore, it is easier to reason about resource usage  in this setting.
% Consequently, it might be instructive to write our programs directly in the
% global-state style.
However, doing this to a program that has a backtracking structure, and would
be more naturally expressed in a local-state style,
comes at a great loss of clarity.
% Furthermore, reasoning about global-state semantics is significantly more
% challenging than local-state semantics.
Furthermore, it is significantly more challenging for programmers to
reason about global-state semantics than local-state semantics.

To resolve this dilemma, we can write our programs in a local-state style
and then translate them to the global-state style to enable low-level optimisations.
%
In this subsection, we show one systematic program translation that
alters a program written for local-state semantics to a program that,
when interpreted under global-state semantics, behaves exactly the
same as the original program interpreted under local-state semantics.
%
This translation makes explicit copying of the whole state and relies
on using the nondeterminism mechanism to insert state-restoring
branches.
%
We will show other translations from local-state semantics to
global-state semantics which avoid the copying and do not rely on
nondeterminism in \Cref{sec:undo} and \Cref{sec:trail-stack}.

% %- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
% \paragraph*{State-Restoring Put}
% Backtracking algorithms with global state often adhere to a pattern
% in which they:
% \begin{enumerate}
%     \item perform a step in the search that updates the current state,
%     \item recursively search for solutions, and
%     \item roll back the updated state to the previous step (regardless of whether
%     a solution was found).
% \end{enumerate}
% A naive monadic program that implements this pattern has the following structure.
% < get (\prev -> put next >> search >> put prev)
% Here |next| is the updated state, and |prev| is the old state.
%
% Now, assume a |search| that consists of two branches
% |(m1 `mplus` m2)|.
% We want both branches to start running with the |next| state,
% Furthermore, the state should be restored to |prev| when both branches are done.
% In turn, we will assume that |m1| and |m2| follow the same discipline, rolling
% back whatever further modifications they make to the state.
%
% Due to (\ref{eq:mplus-dist}), however, the monadic program expands to the following:
% < get (\prev -> put next >> (m1 `mplus` m2 `mplus` m3) >>= put prev
% <   =  get (\prev ->  (put next >>  m1 >> put prev)  `mplus`
% <                     (             m2 >> put prev)
% With a global state, this means that |m1| starts with the |next| state and ends
% with rolling back to to the |prev| state. This is wrong, because now |m2| now
% starts with this |prev| instead of |next|.  Moreover, also our second
% requirement can be violated, as we cannot guarantee that the state is rolled
% back at the end.  Indeed, if |m2| fails and thus ends with |mzero|, |put prev| is
% not run afterwards (because of (\ref{eq:mzero-zero})).
%
% This naive approach is of course not what we want. Both braches should
% start with the |next| state, and the |prev| state should be restored
% just once, after both branches are done.
%
% Therefore, we define the |side| function, which does not generate a result
% but rather represents a side-effect, hence the name.
% \begin{code}
% side :: MNondet m => m a -> m b
% side m = m >> mzero
% \end{code}
% Since nondeterministic branches are executed sequentially, the program
% < side (modify next) `mplus` m1 `mplus` m2 `mplus` m3 `mplus` side (modReturn prev)
% executes |modify next| and |modReturn prev| once, even if the nondeterministic
% branches fail.
%
% \wenhao{
%   I think it is more natural to use |modify next >> m1 `mplus` m2 `mplus` m3 `mplus` side(modify prev)|.
%   Also, this section is used to discuss the technique of "chaining using |`mplus`|", right?
%   But it seems a little convoluted to discuss |modify| here and then discuss |putR| in 4.4 and then come back to |modify| in 4.5.}
%
% The attentive reader may have noticed that we are using |mplus| as a kind of
% sequencing operator now.
% Recall from right-distributivity (\ref{eq:mplus-dist}) that
% |(m1 `mplus` m2) >> n = (m1 >> n) `mplus` (m2 >> n)|.
% That is, |mplus| acts as ``insertion points'', where future code followed by
% |(>>)| can be inserted into.
% This is a dangerous feature, which we replace by a safer programming pattern.
%
%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{State-Restoring Put}\
%
Central to the implementation of backtracking in the global state setting is
the backtracking variant of |put|.
Going forward, such a state-restoring |putR| modifies the state as usual,
but, when backtracked over, it restores the old state.

% This is accomplished with the following definition:
We implement |putR| using both state and nondeterminism as follows:
\begin{code}
putR :: (MState s m, MNondet m) => s -> m ()
putR s = get >>= \ s' -> put s `mplus` side (put s')
\end{code}
\label{eq:state-restoring-put}

Here the |side| branch is executed for its side-effect only; it fails
before yielding a result.
\begin{code}
side :: MNondet m => m a -> m b
side m = m >> mzero
\end{code}

Intuitively, the second branch generated by |putR| can be understood
as a backtracking or state-restoring branch.
%
The |putR s| operation changes the state to |s| in the first branch
|put s|, and then restores the it to the original state |s'| in the
second branch after we finish all computations in the first branch.
%
Then, the second branch immediately fails so that we can keep going to
other branches with the original state |s'|.
%
For example, assuming an arbitrary computation |comp| is placed after
a state-restoring put, we have the following calculation.
<    putR s >> comp
< = {-~  definition of |putR|  -}
<    (get >>= \s' -> put s `mplus` side (put s')) >> comp
< = {-~  right-distributivity (\ref{eq:mplus-dist})  -}
<    (get >>= \s' -> (put s >> comp) `mplus` (side (put s') >> comp))
< = {-~  left identity (\ref{eq:mzero-zero})  -}
<    (get >>= \s' -> (put s >> comp) `mplus` side (put s'))

This program saves the current state |s'|, computes |comp| using state |s|,
and then restores the saved state |s'|.
Figure \ref{fig:state-restoring-put} shows how the state-passing works
and the flow of execution for a computation after a state-restoring put.

\begin{figure}[ht]
% https://q.uiver.app/?q=WzAsNixbMSwwLCJ8Z2V0IFxccyd8Il0sWzEsMSwifG1wbHVzfCJdLFswLDIsInxwdXQgc3wiXSxbMCwzLCJ8Y29tcHwiXSxbMiwyLCJ8cHV0IHMnfCJdLFsyLDMsInxtemVyb3wiXSxbMCwxLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzEsMiwiIiwwLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsxLDQsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMiwzLCIiLDAseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNSwiIiwwLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFswLDIsInxzJ3wiLDIseyJvZmZzZXQiOjUsImN1cnZlIjotMywic2hvcnRlbiI6eyJzb3VyY2UiOjEwfSwiY29sb3VyIjpbMCwwLDUwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fSxbMCwwLDUwLDFdXSxbMiwzLCJ8c3wiLDIseyJvZmZzZXQiOjMsImNvbG91ciI6WzAsMCw1MF0sInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRvdHRlZCJ9fX0sWzAsMCw1MCwxXV0sWzQsNSwifHMnfCIsMix7Im9mZnNldCI6MywiY29sb3VyIjpbMCwwLDUwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fSxbMCwwLDUwLDFdXSxbMyw0LCJ8c3wiLDIseyJsYWJlbF9wb3NpdGlvbiI6NjAsImN1cnZlIjotNSwic2hvcnRlbiI6eyJzb3VyY2UiOjEwLCJ0YXJnZXQiOjEwfSwiY29sb3VyIjpbMCwwLDUwXSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZG90dGVkIn19fSxbMCwwLDUwLDFdXV0=
\[\begin{tikzcd}
    & {|get -> \s'|} \\
    & {|mplus|} \\
    {|put s|} && {|put s'|} \\
    {|comp|} && {|mzero|}
    \arrow[no head, from=1-2, to=2-2]
    \arrow[no head, from=2-2, to=3-1]
    \arrow[no head, from=2-2, to=3-3]
    \arrow[no head, from=3-1, to=4-1]
    \arrow[no head, from=3-3, to=4-3]
    \arrow["{|s'|}"', shift right=5, color={rgb,255:red,128;green,128;blue,128}, curve={height=-18pt}, shorten <=5pt, dotted, from=1-2, to=3-1]
    \arrow["{|s|}"', shift right=3, color={rgb,255:red,128;green,128;blue,128}, dotted, from=3-1, to=4-1]
    \arrow["{|s'|}"', shift right=3, color={rgb,255:red,128;green,128;blue,128}, dotted, from=3-3, to=4-3]
    \arrow["{|s|}"'{pos=0.6}, color={rgb,255:red,128;green,128;blue,128}, curve={height=-30pt}, shorten <=8pt, shorten >=8pt, dotted, from=4-1, to=3-3]
\end{tikzcd}\]
\caption{State-restoring put-operation.}
\label{fig:state-restoring-put}
\end{figure}


Another example of |putR| is shown in Table \ref{tab:state-restoring-put}, where
three programs are run with initial state |s0|.
Note the difference between the final state and the program result for the
state-restoring put.

\begin{table}[h]
\begin{center}
\begin{tabular}{l||ll}
                            & Program result & Final state \\ \hline
|return x >> get|           & |s0|           & |s0|        \\
|put s >> return x >> get|  & |s|            & |s|         \\
|putR s >> return x >> get| & |s|            & |s0|
\end{tabular}
\end{center}
\caption{Comparing |put| and |putR|.}
\label{tab:state-restoring-put}
\end{table}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
\paragraph*{Translation with State-Restoring Put}\
%
The idea is that |putR|, when run with a global state, satisfies laws
(\ref{eq:put-put}) to (\ref{eq:put-left-dist}) --- the state laws and
the local-state laws.
Then, one can take a program written for local-state semantics, replace
all occurrences of |put| by |putR|, and run the program with a global state.
However, to satisfy all of these laws,
care should be taken to replace \emph{all} occurrences of |put|.
Particularly, placing a program in a larger context, where |put| has not been replaced, can change the meaning
of its subprograms.
An example of such a problematic context is |(>> put t)|, where the |get|-|put| law
(\ref{eq:get-put}) breaks and programs |get >> putR| and |return ()| can be
differentiated:

\begin{minipage}{0.7\textwidth}
<    (get >> putR) >> put t
< = {-~  definition of |putR|  -}
<    (get >>= \s -> get >>= \s0 -> put s `mplus` side (put s0)) >> put t
< = {-~  get-get (\ref{eq:get-get})  -}
<    (get >>= \s -> put s `mplus` side (put s)) >> put t
< = {-~  right-distributivity (\ref{eq:mplus-dist})  -}
<    (get >>= \s -> (put s >> put t) `mplus` (side (put s)) >> put t)
< = {-~  left-identity (\ref{eq:mzero-zero})  -}
<    (get >>= \s -> (put s >> put t) `mplus` side (put s))
< = {-~  put-put (\ref{eq:put-put})  -}
<    (get >>= \s -> put t `mplus` side (put s))
\end{minipage}%
\begin{minipage}{0.3\textwidth}
<    return () >> put t
< =  put t
\end{minipage}

Those two programs do not behave in the same way when |s /= t|.
%
Hence, only provided that \emph{all} occurences of |put| in a program are replaced by |putR|
can we simulate local-state semantics. The replacement itself as well as the correctness statement
that incorporates this requirement can be easily epressed with effect handlers. As we will explain
below we need to articulate this global replacement in the
correctness proof. This requires using the {\bf fusion-post'} rule rather than the more widely used {\bf fusion-post} rule.

%\paragraph*{Proving the |putR| Operation Correct}
% \label{sec:putr}
% It is time to give a more formal definition for the translation between
% global-state and local-state semantics using the free monad representation.
% We use helper functions |getOp|, |putOp|, |orOp| and |failOp| to shorten
% notation and eliminate the overkill of writing the |Op| and |Inl|, |Inr|
% constructors. Their implementations are straightforwardly defined in terms of
% |Get|, |Put|, |Or| and |Fail|.

% %if False
% \begin{code}
% getOp     :: (s -> Free (StateF s :+: NondetF :+: f) a)
%           -> Free (StateF s :+: NondetF :+: f) a
% getOp     = Op . Inl . Get

% putOp     :: s
%           -> Free (StateF s :+: NondetF :+: f) a
%           -> Free (StateF s :+: NondetF :+: f) a
% putOp s   = Op . Inl  . Put s

% orOp      :: Free (StateF s :+: NondetF :+: f) a
%           -> Free (StateF s :+: NondetF :+: f) a
%           -> Free (StateF s :+: NondetF :+: f) a
% orOp p q  = (Op . Inr . Inl) (Or p q)

% failOp    :: Free (StateF s :+: NondetF :+: f) a
% failOp    = (Op . Inr . Inl) Fail
% \end{code}
% %endif

% We can then define |putROp| in terms of these helper functions.
% \begin{code}
% putROp :: s -> Free (StateF s :+: NondetF :+: f) a -> Free (StateF s :+: NondetF :+: f) a
% putROp t k = getOp (\s -> (putOp t k) `orOp` (putOp s failOp))
% \end{code}
% Note the similarity with the |putR| definition (\Cref{eq:state-restoring-put}) of the previous paragraph.
% Here, we use a continuation-based representation, from which we can always recover the
% representation of |putR| by setting the continuation to |return|.

We realize the global replacement of |put| with
a |putR| with the effect handler |local2global|:
\begin{code}
local2global  :: Functor f
              => Free (StateF s :+: NondetF :+: f) a
              -> Free (StateF s :+: NondetF :+: f) a
local2global = fold Var alg
  where
    alg (Inl (Put t k)) = putR t >> k
    alg p               = Op p
\end{code}
% Now, we want to prove this translation correct, but what does correctness mean
% in this context?
% Informally stated, it should transform between local-state and global-state
% semantics.
% For simplicity, we can implicitly assume
% commutativity and associativity of the coproduct operator |(:+:)|
% and omit the |comm2| in the definition of |hGlobal|.

The following theorem shows that the translation |local2global|
preserves the meaning when switching from local-state to global-state
semantics:
%
\begin{restatable}[]{theorem}{localGlobal}
\label{thm:local-global}
< hGlobal . local2global = hLocal
\end{restatable}
% Here, the |hGlobal| and |hLocal| handlers both eliminate all
% nondeterminsm and state effects in the program.
% WT: I don't think we need this sentence.

\begin{proof}
%format genLHS = "\Varid{gen}_{\Varid{LHS}}"
%format genRHS = "\Varid{gen}_{\Varid{RHS}}"
%format algSLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{S}}"
%format algSRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{S}}"
%format algNDLHS = "\Varid{alg}_{\Varid{LHS}}^{\Varid{ND}}"
%format algNDRHS = "\Varid{alg}_{\Varid{RHS}}^{\Varid{ND}}"
%format fwdLHS = "\Varid{fwd}_{\Varid{LHS}}"
%format fwdRHS = "\Varid{fwd}_{\Varid{RHS}}"
Both the left-hand side and the right-hand side of the equation consist of
function compositions involving one or more folds.
We apply fold fusion separately on both sides to contract each
into a single fold:
\begin{eqnarray*}
|hGlobal . local2global| & = & |fold genLHS (algSLHS # algNDRHS # fwdLHS)| \\
|hLocal|& = & |fold genRHS (algSRHS # algNDRHS # fwdRHS)|
\end{eqnarray*}
We approach this calculationally. That is to say, we do not first postulate
definitions of the unknowns above (|algSLHS| and so on) and then verify whether
the fusion conditions are satisfied. Instead, we discover the definitions of the unknowns.
We start from the known side of
each fusion condition and perform case analysis on the possible shapes of
input. By simplifying the resulting case-specific expression, and pushing the handler
applications inwards, we end up at a point where we can read off the definition
of the unknown that makes the fusion condition hold for that case.

Finally, we show that both folds are equal by showing that their
corresponding parameters are equal:
\begin{eqnarray*}
|genLHS| & = & |genRHS| \\
|algSLHS| & = & |algSRHS| \\
|algNDLHS| & = & |algNDRHS| \\
|fwdLHS| & = & |fwdRHS|
\end{eqnarray*}

A noteworthy observation is that, for fusing the left-hand side of the equation, we do not use the standard
fusion rule {\bf fusion-post}~(\ref{eq:fusion-post}):
\begin{eqnarray*}
    |hGlobal . fold Var alg| & = & |fold (hGlobal . Var) alg'| \\
     \Leftarrow \qquad
   |hGlobal . alg| & = & |alg' . fmap hGlobal|
\end{eqnarray*}
where |local2global = fold Var alg|. The problem is that we will not find an
appropriate |alg'| such that |alg' (fmap hGlobal t)| restores the state for any
|t| of type |(StateF s :+: NondetF :+: f) (Free (StateF s :+: NondetF :+: f)
a)|.

Fortunately, we do not need such an |alg'|. As we have already pointed out, we
can assume that the subterms of |t| have already been transformed by
|local2global|, and thus all occurrences of |Put| appear in the |putR|
constellation.

We can incorporate this assumption by using the alternative fusion rule
{\bf fusion-post'}~(\ref{eq:fusion-post-strong}):
\begin{eqnarray*}
    |hGlobal . fold Var alg| & = & |fold (hGlobal . Var) alg'| \\
     \Leftarrow \qquad
   |hGlobal . alg . fmap local2global| & = & |alg' . fmap hGlobal . fmap local2global|
\end{eqnarray*}
The additional |fmap local2global| in the condition captures the property that
all the subterms have been transformed by |local2global|.

In order to not clutter the proofs, we abstract everywhere over this additional |fmap local2global| application, except
% in the one place where we need it.
% That is the appeal to the key lemma:
% \begin{eqnarray*}
% & |hState1 (hNDf (comm2 (local2global t))) s| & \\
% & = & \\
% & |do (x, _) <- hState1 (hNDf (comm2 (local2global t))) s; return (x, s)| &
% \end{eqnarray*}
for the key lemma which
expresses that the syntactic transformation |local2global| makes sure
that, despite any temporary changes, the computation |t| restores the state
back to its initial value.

We elaborate each of these steps in \Cref{app:local-global}.
\end{proof}

% %-------------------------------------------------------------------------------
%if False
% \subsection{The N-Queens Puzzle with Local or Global State}
% \label{sec:n-queens-global}
% \wenhao{paragraph or subsubsection?}
%
% Recall the backtracking algorithm |queens| for the n-queens example in
% Section~\ref{sec:motivation-and-challenges}.
% It runs in the local-state semantics because every branch maintains its own copy
% of the state and has no influence on other branches.
% The function |queensLocal| solves the n-queens problem using the handler |hLocal| for local-state semantics.
\begin{code}
queensLocal :: Int -> [[Int]]
queensLocal = hNil . flip hLocal (0, []) . queens
\end{code}
% % For example, the program |queensLocal 4| gives the result |[[3,1,4,2],[2,4,1,3]]|.
%
% Using the simulation function |local2global|, we can also have a function |queensGlobal|
% which solves the n-queens problem using the handler |hGlobal| for global-state semantics.
\begin{code}
queensGlobal :: Int -> [[Int]]
queensGlobal = hNil . flip hGlobal (0, []) . local2global . queens
\end{code}
% These two functions are equivalent as we have proven that |hGlobal . local2global = hLocal|.
%endif
