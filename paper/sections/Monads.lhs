%if False
\begin{code}
module Monads where

import Control.Monad
import Utilities
\end{code}
%endif
\section{Monad and Effect Operators}

A monad consists of a type constructor |M :: * -> *| and two operators |return :: a -> M a| and ``bind'' |(>>=) :: M a -> (a -> M b) -> M b| that satisfy the following {\em monad laws}:
\begin{align}
  |return x >>= f| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |m >>= return| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
We also define |m1 >> m2 = m1 >>= const m2|, which has type |(>>) :: m a -> m b -> m b|.
%\begin{figure}
% \vspace{-1cm}
% \caption{Some monadic operators we find handy for this paper.}
% \label{figure:monadic-operators}
% \end{figure}
Kleisli composition, denoted by |(>=>)|, composes two monadic operations |a -> M b| and |b -> M c| into an operation |a -> M c|.
The operator |(<$>)| applies a pure function to a monad.
%
% Operators |(<$>)| and |(<.>)| are monadic counterparts of function application and composition: |(<$>)| applies a pure function to a monad, while |(<.>)| composes a pure function after a monadic function.
%
\begin{spec}
(>=>)  :: (a -> M b) -> (b -> M c) -> a -> M c
(f >=> g) x = f x >>= g {-"~~,"-}

(<$>)  :: (a -> b) -> M a -> M b
f <$> m = m >>= (return . f) {-"~~."-}
\end{spec}
%if False
\begin{code}
infixr 9 <.>

(<.>)    :: Monad m => (b -> c) -> (a -> m b) -> (a -> m c)
f <.> g  = (return . f) <=< g

infixr 1 <<
(<<) :: Monad m => m b -> m a -> m b
m1 << m2 = const m1 =<< m2
\end{code}
%endif
The following properties can be proved from their definitions and the monad laws:
\begin{align}
  |(f . g) <$> m| &= |f <$> (g <$> m)| \mbox{~~,}
    \label{eq:comp-ap-ap}\\
|(f <$> m) >>= g| &= |m >>= (g . f)| \mbox{~~,}
  \label{eq:comp-bind-ap}\\
|f <$> (m >>= k)| &= |m >>= (\x -> f <$> k x)|  \mbox{~~, |x| not free in |f|.}
  \label{eq:ap-bind-ap}
\end{align}
%if False
\begin{code}
propCompApAp f g m       = (f <$> (g <$> m)) === ((f . g) <$> m)
propCompBindAp f g m     = (f <$> m) >>= g === m >>= (g . f)
propApBindAp f m k       = f <$> (m >>= k) === m >>= (\x -> f <$> k x)
\end{code}
%endif

\paragraph{Effect and Effect Operators}
Monads are used to model effects, and each effect comes with its collection of operators. For example, to model non-determinism we might assume two operators |mzero| and |mplus| ($\Varid{mplus}$), respectively modeling failure and choice. A state effect comes with operators |get| and |put|, which respectively reads from and writes to an unnamed state variable.

A program might involve more than one effect.
In Haskell, the type class constraint |MonadPlus| in the type of a program denotes that the program may have used |mzero| or |mplus|, and possibly other effects, while |MonadState s| denotes that it may have used |get| and |put|.
Some theorems in this pearl, however, applies only to programs that, for example, use non-determinism and no other effects.
To talk about such programs, we use a slightly different notation.
We let the type |Me eps a| denote a monad whose return type is |a| and, during whose execution, effects in the set |eps| might occur.
This pearl considers only two effects: non-determinism and state.
Non-determinism is denoted by |N|, for which we assume two operators |mzero :: Me eps a| and |mplus :: Me eps a -> Me eps a -> Me eps a|, where |N `mem` eps|.
A state effect is denoted by |S s|, where |s| is the type of the state, with two operators |get :: Me eps s| and |put :: s -> Me eps ()| where |S s `mem` eps|.

We introduce a small language of effectful programs and a simple type system in Figure \ref{figure:type-system}.
If a program may have type |Me N a|, we know that non-determinism is the {\em only effect} allowed.
Inference of effects is not unique, however: a program having |mzero| can be typed as both |Me N a| and |Me {N, S Int} a|.
We sometimes denote the constraint on |eps| in a type-class-like syntax, e.g |mzero :: N `mem` eps => Me eps a|.
All these are merely notational convenience --- the point is that the effects a program uses can be determined statically.

\begin{figure}
\small
%format ntE = "\mathcal{E}"
%format ntEV = "\mathcal{F}"
%format ntP = "\mathcal{P}"
%format ntT = "\mathcal{T}"
%format ntEff = "\mathcal{F}"

\begin{spec}
ntE    = {-"\mbox{pure, non-monadic expressons}"-}
ntEV   = {-"\mbox{functions returning monadic programs}~~"-}
ntP    = return ntE | ntP >>= ntEV | mzero | ntP `mplus` ntP | get | put ntE   {-"\mbox{~~ --- monadic progs}~~"-}
ntT    = a | c | ntT -> ntT | Me {ntEff} ntT                                   {-"\mbox{~~ --- types}"-}
ntEff  = S a | S c | N                                                         {-"\mbox{~~ --- effects}"-}
{-"\quad\mbox{$a$ ranges over type variables,}"-}
{-"\quad\mbox{while $c$ ranges over for built-in type constants.}"-}
\end{spec}
%\vspace{-0.5cm}
\begin{align*}
\AXC{$\Gamma \vdash |e :: a| $}
\UIC{$\Gamma \vdash |return e :: Me eps a|$}
\DP
%
&\quad
%
\AXC{$\Gamma \vdash |m :: Me eps a|$}
\AXC{$\Gamma \vdash |f :: a -> Me eps b|$}
\BIC{$\Gamma \vdash |m >>= f :: Me eps b|$}
\DP
\\
%
\AXC{|N `mem` eps|}
\UIC{$\Gamma \vdash |mzero :: Me eps a|$}
\DP
%
&\quad
%
\AXC{$\Gamma \vdash |m1 :: Me eps a|$\hspace{-0.5cm}}
\AXC{$\Gamma \vdash |m2 :: Me eps a|$\hspace{-0.5cm}}
\AXC{|N `mem` eps|}
\TIC{$\Gamma \vdash |m1 `mplus` m2 :: Me eps a|$}
\DP
\\
\AXC{|S s `mem` eps|}
\UIC{$\Gamma \vdash |get :: Me eps s|$}
\DP
%
&\quad
%
\AXC{$\Gamma \vdash |e :: s|$}
\AXC{|S s `mem` eps|}
\BIC{$\Gamma \vdash |put e :: Me eps ()|$}
\DP
\end{align*}
\caption{A small language and type system for effectful programs.}
\label{figure:type-system}
\end{figure}

\paragraph{Total, Finite Programs} Like in other literature on program derivation, we assume a set-theoretic semantics in which functions are total. Lists in this pearl are inductive types, and unfolds generate finite lists too. Non-deterministic choices are finitely branching.
%In such a setting, hylomorphisms have unique solutions.
Given a concrete input, a function always expands to a finitely-sized expression consisting of syntax allowed by its type. We may therefore prove properties of a monad of type |Me eps a| by structural induction over its syntax.
