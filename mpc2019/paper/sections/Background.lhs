\section{Background}
\koen{Maybe make this two sections}

\subsection{Monads, Nondeterminism and State}
\paragraph{Monads and Effect Operators}
A monad consists of a type constructor |M :: * -> *| and two operators |return :: a -> M a| and ``bind'' |(>>=) :: M a -> (a -> M b) -> M b| that satisfy the following {\em monad laws}:
\begin{align}
  |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
We also define |m1 >> m2 = m1 >>= const m2|, which has type |(>>) :: m a -> m b -> m b|.

Monads are used to model effects, and each effect comes with its collection of
operators. For example, to model non-determinism we assume two operators |mzero|
and |mplus| ($\Varid{mplus}$), respectively modeling failure and choice. A state
effect comes with operators |get| and |put|, which respectively reads from and
writes to an unnamed state variable.

A program may involve more than one effect. In Haskell, the type class
constraint |MonadPlus| in the type of a program denotes that the program may use
|mzero| or |mplus|, and possibly other effects, while |MonadState s| denotes
that it may use |get| and |put|. Some theorems in this paper, however, apply
only to programs that, for example, use non-determinism and no other effects. To
talk about such programs, we use a slightly different notation. We let the type
|Me eps a| denote a monad whose return type is |a| and, during whose execution,
effects in the set |eps| may occur. 
\koen{I'm thinking of adopting the `Just Do It' notation instead of this
  notation. This one is more elegant but less well-known, and since we'll be
  switching to free monad notation quite quickly, it might not be worth the
  extra space.}

\paragraph{Nondeterminism}
The first effect we introduce is nondeterminism.
Following the trail of Hutton and Fulger \cite{HuttonFulger:08:Reasoning} and
Gibbons and Hinze \cite{GibbonsHinze:11:Just}, we introduce effects 
based on an axiomatic characterisation (a set of laws that govern how the effect
operators behave with respect to one another) rather than a specific implementation.

We denote nondeterminism by |N|, and we assume two operators
|mzero :: N `mem` eps => Me eps a|
and
|mplus :: N `mem` eps => Me eps a -> Me eps a -> Me eps a|
: the former
denotes failure, while |m `mplus` n| denotes that the computation may yield
either |m| or |n|.
Precisely what
laws these operators should satisfy, however, can be a tricky issue.
As discussed by Kiselyov~\cite{Kiselyov:15:Laws}, it eventually comes down to
what we use the monad for. 

It is usually expected that |mplus| and |mzero| form a monoid. That
is, |mplus| is associative, with |mzero| as its zero:
\begin{align}
|(m `mplus` n) `mplus` k|~ &=~ |m `mplus` (n `mplus` k)| \mbox{~~,}
  \label{eq:mplus-assoc}\\
|mzero `mplus` m| ~=~ & |m| ~=~ |m `mplus` mzero| \mbox{~~.}
  \label{eq:mzero-mplus}
\end{align}

It is also assumed that monadic bind distributes into |mplus| from the end,
while |mzero| is a left zero for |(>>=)|:
\begin{alignat}{2}
  &\mbox{\bf left-distributivity}:\quad &
  |(m1 `mplus` m2) >>= f| ~&=~ |(m1 >>= f) `mplus` (m2 >>= f)| \mbox{~~,}
  \label{eq:bind-mplus-dist}\\
  &\mbox{\bf left-zero}:\quad &
  |mzero >>= f| ~&=~ |mzero| \label{eq:bind-mzero-zero} \mbox{~~.}
\end{alignat}
We will refer to the laws \eqref{eq:mplus-assoc}, \eqref{eq:mzero-mplus},
\eqref{eq:bind-mplus-dist}, \eqref{eq:bind-mzero-zero} collectively as the
\emph{nondeterminism laws}.
Other properties regarding |mzero| and |mplus| will be introduced when needed.

\paragraph{State}
The state effect provides two operators: |get :: S s `mem` eps => Me eps s| retrieves the state, while |put :: S s `mem` eps =>  s -> Me eps ()| overwrites the state by the given value. They are supposed to satisfy the \emph{state laws}:

\begin{alignat}{2}
&\mbox{\bf put-put}:\quad &
|put st >> put st'| &= |put st'|~~\mbox{,} \label{eq:put-put}\\
&\mbox{\bf put-get}:~ &
|put st >> get| &= |put st >> return st| ~~\mbox{,} \label{eq:get-put}\\
&\mbox{\bf get-put}:~ &
|get >>= put| &= |return ()| ~~\mbox{,} \label{eq:put-get}\\
&\mbox{\bf get-get}:\quad &
|get >>= (\st -> get >>= k st)| &= |get >>= (\st -> k st st)|
~~\mbox{.} \label{eq:get-get}
\end{alignat}
\koen{can we find a citation for these laws?}