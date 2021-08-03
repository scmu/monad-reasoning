\section{Modeling Local State With Global State}
\label{sec:local-global}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module LocalGlobal where

import Background
import Control.Monad (ap, liftM) 
import Control.Applicative (liftA2)
import qualified Control.Monad.Trans.State.Lazy as S

class MStateNondet s m => MSt s m where
    alph :: n a -> m a

local :: MSt s n => S.StateT s m a -> n a
local x = do 
    s <- get
    (a, s') <- alph (S.runStateT x s)
    put s'
    etan a

etan :: Monad n => a -> n a
etan = return

etals :: MStateNondet s m => a -> S.StateT s m a
etals x = S.StateT $ \s -> return (x, s)

muls :: MStateNondet s m => S.StateT s m (S.StateT s m a) -> S.StateT s m a
muls mx = S.StateT $ \s -> S.runStateT mx s >>= \(x, s') -> S.runStateT x s'

mun :: MSt s n => n (n a) -> n a
mun nx = alph nx >>= id -- do
    -- x <- alph nx
    -- x

instance (Monad m) => MState s (S.StateT s m) where
    get = S.StateT (\s -> return (s, s))
    put s = S.StateT (\ _ -> return ((), s))

\end{code}
%endif

\birthe{transition}

This section formally distinguishes local state from global state.

In a program with local state, each nondeterministic branch has its own local
copy of the state.
This is a convenient effect interaction which is provided by many systems that
solve search problems, e.g. Prolog.

On the other hand, in a program with global state a single state is sequentially
threaded through the nondeterministic branches. 

The appearance of local state is obtained by the well-known backtracking 
technique, undoing changes to the state when going to the next branch.
Therefore, local state is what Gibbons and Hinze call ``backtrackable state''.
Backtracking is relatively efficient: remembering what to undo often requires 
less memory than creating multiple copies of the state, and undoing changes
often takes less time than recomputing the state from scratch.
Global state is sometimes called non-backtrackable state.
Let's first focus on local-state and global-state semantics in order to 
define a formal translation between the two.

%-------------------------------------------------------------------------------
\subsection{Local-State Semantics}
\label{sec:local-state}

When a branch of a nondeterministic computation runs into a dead end and 
the continuation is picked up at the most recent branching point,
any alterations made to the state by the terminated branch are invisible to 
the continuation.
We refer to these semantics as \emph{local-state semantics}. 

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Interaction Laws}
The following laws characterize the local state semantics for a monad |m|
with state and nondeterminism:
\begin{alignat}{2}
    &\mbox{\bf right-identity}:\quad &
    |m >> mzero| &= |mzero|~~\mbox{,} \label{eq:right-identity}\\
    &\mbox{\bf left-distributivity}:~ &
    |m >>= (\x -> f1 x `mplus` f2 x)| &= |(m >>= f1) `mplus` (m >>= f2)| ~~\mbox{.} \label{eq:left-dist}
\end{alignat}
Note that the monad |m| on the lefthand side in the right-identity law 
(\ref{eq:right-identity})
may contain some effects that do not happen in the righthand side.
Similarly, in the left-distributivity law (\ref{eq:left-dist}), 
for some implementations of |m|, 
the effect of the monad may happen once on the lefthand side and twice on the 
righthand side.
This is a typical property of local state. Effects can be lifted over branches,
or can be undone for different branches.  

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Commutativity}
Having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) leads to profound 
consequences on the semantics and implementation of monadic programs.
To begin with, (\ref{eq:left-dist}) implies that for |mplus| we have some limited
notion of commutativity. 
For instance, both the left and right distributivity rules can be applied to the 
term |(return x `mplus` return y) >>= \z -> return z `mplus` return z|.
It is then easy to show that this term must be equal to both
|return x `mplus` return x `mplus` return y `mplus` return y|
and 
|return x `mplus` return y `mplus` return x `mplus` return y|
\footnote{Gibbons and Hinze \cite{} were mistaken in their claim that the type
|s -> [(a, s)]| constitutes a model of their backtrackable state laws.
It is not a model because its |`mplus`| does not commute with itself.
One could consider a relaxed semantics that admits |s ->[(a, s)]|, 
but that is not the focus of this paper.}.
In fact, having (\ref{eq:right-identity}) and (\ref{eq:left-dist}) gives us very 
strong and useful commutative properties.

\begin{definition}[Commutativity]
Let |m| and |n| be two monadic programs such that |x| does not occur free in |m|,
and |y| does not occur free in |n|. We say |m| and |n| commute if 
\begin{alignat}{2}
    &\mbox{\bf commutativity}:\quad &
    |m >>= \x -> n >>= \y -> f x y| &= |n >>= \y -> m >>= \x -> f x y|~~\mbox{.} \label{eq:commutativity}
\end{alignat}
We say that effects |eps| and |delta| commute if any |m| and |n| commute
as long as their only effects are |eps| and |delta|.
\end{definition}

One important result is that, in local-state semantics, nondeterminism commutes
with any effect. 

\begin{theorem} \label{thm:nondet-comm}
If right-identity (\ref{eq:right-identity}) 
and left-distributivity (\ref{eq:left-dist}) hold in addition to the other laws,
nondeterminism commutes with any effect.
\end{theorem}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Implementation}
Implementation-wise, (\ref{eq:right-identity}) and (\ref{eq:left-dist}) 
imply that each nondeterministic branch has its own copy of the state. 
To see that, let |m = put 1|, |f1 () = put 2| and |f2 () = get| in 
(\ref{eq:left-dist}). The state we |get| in the second branch does not change, 
despite the |put 2| in the first branch.
One implementation satisfying the laws is 
< Local s a = s -> m (a, s)
where |m| is a nondeterministic monad, the simplest structure of which is a list.
This implementation is exactly that of |StateT s m a| 
in the Monad Transformer Library \cite{}, or as we introduced in 
Section \ref{sec:combining-the-simulation-with-other-effects}.
With effect handling \cite{}, the monad behaves similarly
(except for the limited commutativity implied by law (\ref{eq:left-dist}))
if we run the handler for state before that for list.


%-------------------------------------------------------------------------------
\subsection{Global-State Semantics}
\label{sec:global-state}

Alternatively, one can choose a semantics where state reigns over nondeterminism.
In this case of non-backtrackable state, alterations to the state persist over
backtracks. Because only a single state is shared over all branches of 
nondeterministic computation, we call this state the \emph{global-state 
semantics}. 

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{The Global-State Law}
The global-state law sets apart 
non-backtrackable state from backtrackable state. 

In addition to the general laws for nondeterminism 
((\ref{eq:mzero}) to (\ref{eq:mzero-zero})) and state
((\ref{eq:put-put}) to (\ref{eq:get-get})), we provide a \emph{global-state law}
to govern the interaction between nondeterminism and state. 
\begin{alignat}{2}
    &\mbox{\bf put-or}:\quad &
    |(put s >> m) `mplus` n| &= |put s >> (m `mplus` n)|~~\mbox{.} \label{eq:put-or}
\end{alignat}

This law allows lifting a |put| operation from the left branch of a 
nondeterministic choice.
For instance, if |m = mzero| in the left-hand side of the equation, 
then under local-state semantics 
(laws (\ref{eq:mzero}) and (\ref{eq:right-identity})) 
the lefthand side becomes equal to |n|, 
whereas under global-state semantics 
(laws (\ref{eq:mzero}) and (\ref{eq:put-or}))
the equation simplifies to |put s >> n|.

This law leaves us free to choose from a large space of 
implementations with different properties. 
For example, in any given implementation, the programs 
|return x `mplus` return y| and |return y `mplus` return x| can be considered
either semantically identical or distinct.
The same goes for the programs |return x `mplus` return x| and |return x|
or other examples.
\todo{sth about S5.2 original paper}

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Implementation}
Figuring out a correct implementation for the global-state monad is tricky. 
One might believe that |Global s m a = s -> (m a, s)|
is a natural implementation of such a monad. 
However, the usual, naive implementation of |(>>=)| does not satisfy
right-distributivity (\ref{eq:mplus-dist}), 
violates monad laws and is therefore not even a monad. 
The type |ListT (State s)| from the Monad Transformer Library \cite{}
expands to essentially the same implementation with 
monad |m| instantiated by the list monad. 
This implementation has the same flaws.
More careful implementations of |ListT|\footnote{Often referred to as |ListT| done right.}, that do satisfy right-distributivity
(\ref{eq:mplus-dist}) and the monad laws have been proposed by \todo{} \cite{}.
Effect handlers \cite{} produce implementations that match our intuition of 
non-backtrackable computations if we run the handler for nondeterminism before
that for state. 
The following implementation has a non-commutative |mplus| operation.
\begin{code}
newtype Global s a = Gl { runGl :: s -> (Maybe (a, Global s a), s) }
\end{code} 
The |Maybe| in this type indicates that a computation might fail to produce a
result. However, since the |s| is outside of the |Maybe|, a modified state 
might be returned even if the computation failed.
This |Global s a| type is an instance of the |MStateNondet| monad.

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

\begin{code}
instance MNondet (Global s) where
    mzero        = Gl (\s ->  (Nothing, s))
    p `mplus` q  = Gl (\s ->  case runGl p s of
        (Nothing,      t)   ->   runGl q t
        (Just (x, r),  t)   ->   (Just (x, r `mplus` q), t))

instance MState s (Global s) where
    get    =  Gl  (\s  ->  (Just (s,   mzero),   s))
    put s  =  Gl  (\ _  ->  (Just ((),  mzero),   s))
\end{code}

Failure, of course, returns an empty continuation and an unmodified state.
Branching first exhausts the left branch before switching to the right branch.

%-------------------------------------------------------------------------------
\subsection{Transforming Between Local and Global State}
\label{sec:transforming-between-local-and-global-state}

Both local state and global state have their own laws and semantics. 
Also, both interpretations of nondeterminism with state have their own 
(dis)advantages. 

Local-state semantics imply that each nondeterministic branch has its own state.
This may be costly if the state is represented by data structures, e.g. arrays,
that are costly to duplicate. 
For example, when each new state is only slightly different from the previous, 
we have a wasteful duplication of information. 

Global-state semantics, however, threads a single state through the entire 
computation without making any implicit copies. 
Therefore, it is easier to reason about resource usage in this setting. 
Consequently, it might be instructive to write our programs directly in the 
global-state style.
However, doing this to a program that has a backtracking structure, and would 
be more naturally expressed in a local-state style,
comes at a great loss of clarity. 
Furthermore, reasoning about global-state semantics is significantly more 
challenging.

To address this issue, we can write our programs in a local-state style
and then translate them to global-state style. 
This subsection shows a systematic program transformation that alters a program
written for local-state semantics to a program that, when interpreted under
global-state semantics, behaves exactly the same as the original program 
interpreted under global-state semantics.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Chaining using Nondeterministic Choice}
Backtracking algorithms with global state often adhere to a pattern
in which they
\begin{enumerate}
    \item update the current state to its next step,
    \item recursively search for solutions, and
    \item roll back the state to the previous step (regardless of whether
    a solution was found).
\end{enumerate}
A monadic program that implements this pattern, looks like
< modify next >> search >>= modReturn prev
Here, |next| advances the state and |prev| undoes the modification so that
|prev . next = id = next . prev|.
The functions |modify| and |modReturn| are defined as follows:
\begin{code}
modify f = get >>= put . f
modReturn f v = modify f >> return v
\end{code}
Now, assume an initial state |s| and a |search| that finds three choices
|m1 `mplus` m2 `mplus` m3|.
We want all three choices to start running with state |next s|.
Furthermore, the state should be restored to |prev (next s) = s| afterwards.
Due to (\ref{eq:mplus-dist}), however, the monadic program expands to the following:
< modify next >> m1 `mplus` m2 `mplus` m3 >>= modReturn prev
<   = modify next >>   ((m1 >>= modReturn prev) `mplus`
<                       (m2 >>= modReturn prev) `mplus`
<                       (m3 >>= modReturn prev))
With a global state, this means that |m1| starts with state |next s|, 
after which the state is rolled back to |s|, after |m2| to |prev s| and
after |m3| to |prev (prev s)|.
In fact, one cannot guarantee that |modReturn prev| is always executed.
For example, if |search| fails and reduces to |mzero|, |modReturn prev| is not
run at all (because of (\ref{eq:mzero-zero})).
We need a way to say that |modify next| and |modReturn prev| are run exactly 
once, before and after all nondeterministic branches in |search|, respectively.
Therefore, we define the |side| function, which does not generate a result
but rather represents a side-effect, hence the name.
\begin{code}
side :: MNondet m => m a -> m b
side m = m >> mzero
\end{code}
Since nondeterministic branches are executed sequentially, the program
< side (modify next) `mplus` m1 `mplus` m2 `mplus` m3 `mplus` side (modReturn prev)
executes |modify next| and |modReturn prev| once, even if the nondeterministic
branches fail.

The attentive reader may have noticed that we are using |mplus| as a kind of
sequencing operator now. 
Recall from right-distributivity (\ref{eq:mplus-dist}) that 
|(m1 `mplus` m2) >> n = (m1 >> n) `mplus` (m2 >> n)|. 
That is, |mplus| acts as ``insertion points'', where future code followed by
|(>>)| can be inserted into. 
This is a dangerous feature, which we will replace by a safer prgramming pattern.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{State-Restoring Put}
The discussion above suggests that, if we use |mplus| and |side| appropriately,
we can implement backtracking in a global state setting.
We can go even further by defining a variation on |put|, 
which restores the original state when it is backtracked over.
\begin{code}
putR :: MStateNondet s m => s -> m ()
putR s = get >>= \t -> put s `mplus` side (put t)
\end{code}

For example, assume an arbitrary computation |comp| is placed after 
a state-restoring put. Now we reason as follows.
<    putR s >> comp
< = {-~  definition of |putR|  -}
<    (get >>= \t -> put s `mplus` side (put t)) >> comp
< = {-~  right-distributivity (\ref{eq:mplus-dist})  -}
<    (get >>= \t -> (put s >> comp) `mplus` (side (put t) >> comp))
< = {-~  left identity (\ref{eq:mzero-zero})  -}
<    (get >>= \t -> (put s >> comp) `mplus` side (put t))

So, |putR| saves the current state |t|, computes |comp| using state |s|,
and then restores the saved state |t|.
Figure \ref{fig:state-restoring-put} shows how the state-passing works
and the flow of execution for a computation after a state-restoring put.

\begin{figure}
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
\label{fig:state-restoring-put}
\caption{State-restoring put-operation.}
\end{figure}


Another example is shown in Table \ref{tab:state-restoring-put}, where
three programs are run with initial state |s0|. 
Note the difference between the final state and the program result for the
state-restoring put. 

\begin{table}[h]
\begin{tabular}{l||ll}
                            & Program result & Final state \\ \hline
|return x >> get|           & |s0|           & |s0|        \\
|put s >> return x >> get|  & |s|            & |s|         \\
|putR s >> return x >> get| & |s|            & |s0|           
\end{tabular}
\caption{Comparing |put| and |putR|.}
\label{tab:state-restoring-put}
\end{table}

We wish that |putR|, when run with a global state, satisfies laws 
(\ref{eq:put-put}) to (\ref{eq:left-dist}) --- the state laws and the local 
state laws.
If so, one could take a program written for a local state monad, replace 
all occurrences of |put| by |putR|, and run the program with a global state.
However, to satisfy all of these laws, 
care should be taken to replace \emph{all} occurrences, also those
|put| operations that occur in the context. 
Particularly, placing a program in a different context can change the meaning
of its subprograms. 
An example of such a problematic context is |(>> put t)|, where the get-put law
(\ref{eq:get-put}) breaks and programs |get >> putR| and |return ()| can be
differentiated:

<    return () >> put t
< =  put t
<
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

Those two programs do not behave in the same way when |s /= t|.

\todo{forward reference to formal definition of contexts}
Thus, provided that all occurences of |put| in a program are replaced by |putR|,
we can simulate local-state semantics.
However, the unnecessary copying of the state can not be avoided and even 
becomes explicit in the program.

%- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
\paragraph{Proving the |putR| Operation Correct}
It is time to give a more formal definition for the translation between 
global-state and local-state semantics. 
Let's define a datatype |Prog s f a| that represents a program with state, 
nondeterminism and some other effects.
\begin{code}
type Prog s f a = Free (StateF s :+: NondetF :+: f) a
\end{code}
We also use helper functions |getOp|, |putOp|, |orOp| and |failOp| to shorten
notation and eliminate the overkill of writing the |Op| and |Inl|, |Inr|
constructors. Their implementations are straightforwardly defined in terms of
|Get|, |Put|, |Or| and |Fail|.
%if False
\begin{code}
getOp     :: (s -> Prog s f a)  -> Prog s f a 
getOp     = Op . Inl . Get

putOp     :: s                  -> Prog s f a    -> Prog s f a 
putOp s   = Op . Inl  . Put s

orOp      :: Prog s f a         -> Prog s f a    -> Prog s f a
orOp p q  = (Op . Inr . Inl) (Or p q)

failOp    :: Prog s f a
failOp    = (Op . Inr . Inl) Fail 

hLocal :: (Functor f) => Prog s f a -> s -> Free f [a]
hLocal = fmap (fmap (fmap fst) . hNDl) . hState

hGlobal :: (Functor f) => Prog s f a -> s -> Free f [a]
hGlobal = fmap (fmap fst) . hState . comm . hNDl . assocr . comm

-- The code below is used to assist proof.
hL :: (Functor f) => (s -> Free (NondetF :+: f) (a, s)) -> s -> Free f [a]
hL = fmap hL'
  where
    hL' :: Functor f => Free (NondetF :+: f) (a, s) -> Free f [a]
    -- hL' = (fmap (fmap fst) . hNDl)
    hL' = fold (fmap (fmap fst) . genND) algL'
    genND = Var . return
    algL' :: Functor f => (NondetF :+: f) (Free f [a]) -> Free f [a]
    algL' (Inl Fail) = Var []
    algL' (Inl (Or p q)) = liftA2 (++) p q
    algL' (Inr y) = Op y

algS :: Functor f
     => (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))
     -> s -> Free (NondetF :+: f) (a, s)
algS (Inl (Get k))    = \ s -> k s s
algS (Inl (Put s k))  = \ _ -> k s
algS (Inr y)          = \ s -> Op (fmap ($s) y)

t :: Functor f
  => (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))
  -> s -> Free f [a]
t = hL . algS

t' :: Functor f
   => (StateF s :+: (NondetF :+: f)) (s -> Free (NondetF :+: f) (a, s))
   -> s -> Free f [a]
t' = alg' . fmap hL

alg' :: Functor f => (StateF s :+: (NondetF :+: f)) (s -> Free f [a]) -> s -> Free f [a]
-- alg' = undefined
alg' (Inl (Get k))         = \ s -> k s s
alg' (Inl (Put s k))       = \ _ -> k s
alg' (Inr (Inl Fail))      = \ s -> Var []
-- alg' (Inr (Inl (Or p q)))  = \ s -> (++) <$> p s <*> q s
alg' (Inr (Inl (Or p q)))  = \ s -> liftA2 (++) (p s) (q s)
alg' (Inr (Inr y))         = \ s -> Op (fmap ($s) y)

alg :: (StateF s :+: (NondetF :+: f)) (Free (StateF s :+: (NondetF :+: f)) a) -> Prog s f a
alg = undefined

t2 :: Functor f
   => (StateF s :+: (NondetF :+: f)) (Free (StateF s :+: (NondetF :+: f)) a)
   -> s -> Free f [a]
t2 = hGlobal . alg

t2' :: Functor f
    => (StateF s :+: (NondetF :+: f)) (Free (StateF s :+: (NondetF :+: f)) a)
    -> s -> Free f [a]
t2' = alg' . fmap hGlobal
  -- where alg' = undefined
\end{code}
%endif
We can then define |putROp| in terms of these helper functions.
\begin{code}
putROp :: s -> Prog s f a -> Prog s f a
putROp t k = getOp (\s -> orOp (putOp t k) (putOp s failOp))
\end{code}
Note the similarity with the |putR| definition of the previous paragraph.
The corresponding translation function |trans| transforms every |Put| into
a |putROp| and leaves the rest of the program untouched.
\begin{code}
trans :: Functor f => Prog s f a -> Prog s f a
trans = fold Var alg
  where 
    alg (Inl (Put t k)) = putROp t k
    alg p = Op p
\end{code}
Now, we want to prove this translation correct, but what does correctness mean 
in this context?
Informally stated, it should transform between local-state and global-state 
semantics. 
We can define handlers for these semantics.
Local-state semantics is the semantics where we nondeterministically choose
between different stateful computations. 
< hLocal :: Functor f => Prog s f a -> s -> Free f [a]
< hLocal = fmap (fmap (fmap fst) . hNDl) . hState
Global-state semantics can be implemented by simply inverting the order of the 
handlers: we run a single state through a nondeterministic computation.
< hGlobal :: Functor f => Prog s f a -> s -> Free f [a]
< hGlobal = fmap (fmap fst) . hState . hNDl
Note that, for this handler to work, we assume implicit
commutativity and associativity of the coproduct operator |(:+:)|.
A correct translation then transforms local state to global state.
< hGlobal . trans = hLocal
We use equational reasoning techniques to prove this equality. 
First, we use fold fusion to transfrom |hLocal| to a single fold.
Second, we do the same to |hGlobal . trans|: use fold fusion to make it a single
fold. 
Third, the universality of fold tells us that this equality holds.
\todo{refer to appendices for proof}

% %-------------------------------------------------------------------------------