\documentclass{article}

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{mathptmx}
\usepackage{doubleequals}
\usepackage{scalerel}
\usepackage{authblk}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\begin{document}

\title{Notes: Reason about Non-deterministic Monad}

\author[1]{Shin-Cheng Mu}
\affil[1]{Academia Sinica, Taiwan}

\date{}

\maketitle

\paragraph{Laws regarding monads} Recall the monad laws
\begin{align}
  |f =<< return x| &= |f x|\mbox{~~,} \label{eq:monad-bind-ret}\\
  |return =<< m| &= |m| \mbox{~~,} \label{eq:monad-ret-bind}\\
  |f =<< (g =<< m)| &= |(\x -> f =<< g x) =<< m| \mbox{~~.}
    \label{eq:monad-assoc}
\end{align}
Monadic application and composition are defined as:
\begin{spec}
(<=<)  :: (b -> m c) -> (a -> m b) -> a -> m c
(f <=< g) x = f =<< g x

(<$>) :: (a -> b) -> m a -> m b
f <$> m = (return . f) =<< m

(<.>) :: (b -> c) -> (a -> m b) -> (a -> m c)
f <.> g = ((return . f) =<<) . g
\end{spec}
Laws concerning them include:
\begin{align}
|(f <.> g) x| &= |f <$> g x| \mbox{~~,}
  \label{eq:comp-ap}\\
|f =<< (g <$> m)| &= |(f . g) =<< m| \mbox{~~,}
  \label{eq:comp-bind-ap}\\
|f <$> (g <$> m)| &= |(f . g) <$> m| \mbox{~~,}
  \label{eq:comp-ap-ap}\\
|f <.> (g <.> m)| &= |(f . g) <.> m| \mbox{~~,}
  \label{eq:comp-mcomp-mcomp}\\
|f <=< (g <.> h)| &= |(f . g) <=< h| \mbox{~~,}
  \label{eq:kc-mcomp}\\
|f <.> (g <=< h)| &= |(f <.> g) <=< h| \mbox{~~.}
  \label{eq:mcomp-kc}
\end{align}
Proofs of the properties above will be given later, so as not to distract us
from the main theorems.

Regarding monad-plus, we want |mplus| to be associative, with |mzero| as identity. Monadic bind distributes into |mplus| from the end:
\begin{equation}
  |f =<< (m `mplus` n) = (f =<< m) `mplus` (f =<< n)| \mbox{~~.}
  \label{eq:bind-mplus-dist}
\end{equation}
It is less mentioned, but not uncommon, to demand that |mplus| is
also commutative and idempotent.

\section{Folding and Permutation}

Definitions:
\begin{code}
perm           ::  MonadPlus m => [a] -> m [a]
perm []        =   return []
perm (x : xs)  =   insert x =<< perm xs {-"~~,"-}

insert           ::  MonadPlus m => a -> [a] -> m [a]
insert x []      =   return [x]
insert x (y:xs)  =   return (x : y : xs) `mplus` ((y:) <$> insert x xs) {-"~~."-}
\end{code}

\begin{lemma} \label{lemma:fold-insert}
Given |odot :: a -> b -> b|, we have
< foldr odot z <.> insert x = return . foldr odot z . (x:) {-"~~,"-}
provided that |x `odot` (y `odot` z) = y `odot` (x `odot` z)|
for all |x, y :: a| and |z :: b|.
\end{lemma}
\begin{proof} Prove |foldr odot z <$> insert x xs = return (foldr odot z (x:xs))|. Induction on |xs|.

\noindent {\bf Case} |xs := []|.
\begin{spec}
   foldr odot z <$> insert x []
=    {- definition of |(<$>)| -}
   (return . foldr odot z) =<< insert x []
=    {- definition of |insert| -}
   (return . foldr odot z) =<< return [x]
=    {- monadic law \eqref{eq:monad-bind-ret}-}
   return (foldr odot z [x])  {-"~~."-}
\end{spec}

\noindent {\bf Case} |xs := y:xs|.
\begin{spec}
   foldr odot z <$> insert x (y:xs)
=    {- definition of |(<$>)| -}
   (return . foldr odot z) =<< insert x (y:xs)
=    {- definition of |insert| -}
   (return . foldr odot z) =<<
     (return (x : y : xs) `mplus` ((y:) <$> insert x xs))
=    {- by \eqref{eq:bind-mplus-dist} -}
   return (foldr odot z (x : y : xs)) `mplus`
   ((return . foldr odot z . (y:)) =<< insert x xs) {-"~~."-}
\end{spec}
Focus on the second branch:
\begin{spec}
   (return . foldr odot z . (y:)) =<< insert x xs
=    {- definition of |foldr| -}
   (return . (y `odot`) . foldr odot z) =<< insert x xs
=    {- by \eqref{eq:comp-bind-ap} -}
   (return . (y `odot`)) =<< (foldr odot z <$> insert x xs)
=     {- induction -}
   (return . (y `odot`)) =<< return (foldr odot z (x :xs))
=     {- monadic law \eqref{eq:monad-bind-ret} -}
   return (y `odot` foldr odot z (x:xs))
=     {- definition of |foldr| -}
   return (y `odot` (x `odot` foldr odot z xs))
=     {- since |x `odot` (y `odot` z) = y `odot` (x `odot` z)| -}
   return (foldr odot z (x:y:xs)) {-"~~."-}
\end{spec}
Thus we have
\begin{spec}
   (foldr odot z <.> insert x) (y:xs)
=    {- calculatiion above -}
   return (foldr odot z (x:y:xs)) `mplus` return (foldr odot z (x:y:xs))
=    {- idempotence of |mplus| -}
   return (foldr odot z (x:y:xs)) {-"~~."-}
\end{spec}
\end{proof}

\begin{lemma} \label{lemma:fold-perm}
  Given |odot :: a -> b -> b|, we have
< foldr odot z <.> perm = return . foldr odot z {-"~~,"-}
provided that |x `odot` (y `odot` z) = y `odot` (x `odot` z)|
for all |x, y :: a| and |z :: b|.
\end{lemma}
\begin{proof}
Prove that |foldr odot z <$> perm xs = return (foldr odot z xs)|.
Induction on |xs|.

\noindent {\bf Case} |xs := []|
\begin{spec}
  foldr odot z <$> perm []
=   {- definitions of |(<$>)| and |perm| -}
  (return . foldr odot z) =<< return []
=   {- monadic law \eqref{eq:monad-bind-ret} -}
  return (foldr odot z []) {-"~~."-}
\end{spec}

\noindent {\bf Case} |xs := x:xs|.
\begin{spec}
   foldr odot z <$> perm (x:xs)
=    {- definition of |perm| -}
   foldr odot z <$> (insert x =<< perm xs)
=    {- monadic law \eqref{eq:monad-assoc} -}
   (\ xs -> foldr odot z <$> insert x xs) =<< perm xs
=    {- Lemma \ref{lemma:fold-insert}-}
   (\ xs -> return (foldr odot z (x:xs))) =<< perm xs
=    {- definition of |foldr| -}
   (return . (x `odot`) . foldr odot z) =<< perm xs
=    {- by \eqref{eq:comp-bind-ap} -}
    (return . (x `odot`)) =<< (foldr odot z <$> perm xs)
=    {- induction -}
   (return . (x `odot`)) =<< (return (foldr odot z xs))
=    {- monadic law \eqref{eq:monad-bind-ret} -}
   return (x `odot` foldr odot z xs)
=    {- definition of |foldr| -}
   return (foldr odot z (x:xs)) {-"~~."-}
\end{spec}

\end{proof}

\section{Map, Filter, and Permutation}
\begin{lemma}
  |insert (f x) . map f = map f <.> insert x|.
\end{lemma}
\begin{proof} Prove that |map f <$> insert x xs = insert (f x) (map f xs)|
  for all |xs|, by induction on |xs|.

\noindent{\bf Case} |xs := y:xs|.
\begin{spec}
   map f <$> insert x (y:xs)
=   {- definition of |insert| -}
   map f <$> (return (x : y : xs) `mplus` ((y:) <$> insert x xs))
=   {- \eqref{eq:bind-mplus-dist}, definition of |(<$>)| -}
   (map f <$> return (x : y : xs)) `mplus` (map f <$> ((y:) <$> insert x xs)) {-"~~."-}
\end{spec}
The first branch, by definition of |(<$>)| and monadic law
\eqref{eq:monad-bind-ret}, simplifies to |return (map f (x:y:xs))|.
The second branch:
\begin{spec}
  map f <$> ((y:) <$> insert x xs)
=   {- \eqref{eq:comp-ap-ap} -}
  (map f . (y:)) <$> insert x xs
=   {- definition of |map| -}
  ((f y :) . map f) <$> insert x xs
=   {- \eqref{eq:comp-ap-ap} -}
  (f y :) <$> (map f <$> insert x xs)
=   {- induction -}
  (f y :) <$> (insert (f x) (map f xs)) {-"~~."-}
\end{spec}
Thus we have
\begin{spec}
   map f <$> insert x (y:xs)
=   {- calculation above -}
   return (f x : f y : map f xs) `mplus` ((f y :) <$> (insert (f x) (map f xs)))
=   {- definition of |insert| -}
   insert (f x) (f y : map f xs)
=   {- definition of |map| -}
   insert (f x) (map f (y:xs)) {-"~~."-}
\end{spec}
\end{proof}

\begin{lemma}
  \label{lemma:perm-map}
  |perm . map f = map f <.> perm|.
\end{lemma}

\begin{lemma}
  \label{lemma:perm-filter}
  |perm . filter p = filter p <.> perm|.
\end{lemma}

\section{Homomorphism, etc}

For an associative operator |oplus| with identity |z|, define
\begin{spec}
hom oplus z []          = z
hom oplus z (xs ++ ys)  = hom oplus z xs `oplus` hom oplus z ys {-"~~."-}
\end{spec}

We prove some properties about |hom|, to be used in the next section.

\begin{lemma} \label{lemma:hom-concat}
|h = hom oplus z| if and only if |foldr oplus z . map h = h . concat|.
\end{lemma}
\begin{proof} A Ping-pong proof.

\noindent {\bf Direction} $(\Rightarrow)$. Prove |foldr oplus z (map h xss) = h (concat xss)|
by induction on |xss|.

\noindent {\bf Case} |xss := []|:
\begin{spec}
   foldr oplus z (map h [])
=  foldr oplus z []
=  z
=  h (concat []) {-"~~."-}
\end{spec}

\noindent {\bf Case} |xss := xs : xss|:
\begin{spec}
   foldr oplus z (map h (xs : xss))
=  h xs `oplus` foldr oplus z (map h xss)
=    {- induction -}
   h xs `oplus` h (concat xss)
=    {- |h| homomorphism -}
   h (concat (xs : xss)) {-"~~."-}
\end{spec}

\noindent {\bf Direction} $(\Leftarrow)$. Show that |h| satisfies the properties being a list homomorphism. On empty list:
\begin{spec}
   h []
=  h (concat [])
=    {- assumption -}
   foldr oplus z (map h [])
=  z {-"~~."-}
\end{spec}
On concatentation:
\begin{spec}
   h (xs ++ ys)
=  h (concat [xs,ys])
=    {- assumption -}
   foldr oplus z (map h [xs,ys])
=  h xs `oplus` (h ys `oplus` z)
=  h xs `oplus` h ys {-"~~."-}
\end{spec}
\end{proof}

\begin{lemma}
Let |oplus :: b -> b -> b| be associative on |img (foldr otimes z)| with |z| as its identity, where |otimes :: a -> b -> b|.
We have |foldr otimes z = hom oplus z| if and only if
|x `otimes` (y `oplus` w) = (x `otimes` y) `oplus` w| for all
|x :: a| and |y, w `elem` img (foldr otimes z)|.
\end{lemma}
\begin{proof}A Ping-pong proof.

\noindent {\bf Direction} $(\Leftarrow)$. We show that |foldr otimes z| satisfies the homomorphic properties.
It is immediate that |foldr otimes z [] = z|. For |xs ++ ys|, note that
\begin{equation*}
  |foldr otimes z (xs ++ ys) = foldr otimes (foldr otimes ys) xs| \mbox{~~.}
  \label{eq:fold-cat}
\end{equation*}
The aim is thus to prove that
\begin{spec}
  foldr otimes (foldr otimes ys) xs = (foldr otimes z xs) `oplus` (foldr otimes z ys) {-"~~."-}
\end{spec}
We perform an induction on |xs|. The case when |xs := []| trivially
holds. For |xs := x:xs|, we reason:
\begin{spec}
   foldr otimes (foldr otimes ys) (x:xs)
=  x `otimes` foldr otimes (foldr otimes ys) xs
=   {- induction -}
   x `otimes` ((foldr otimes z xs) `oplus` (foldr otimes z ys))
=   {- assumption: |x `otimes` (y `oplus` w) = (x `otimes` y) `oplus` w| -}
   (x `otimes` (foldr otimes z xs)) `oplus` (foldr otimes z ys)
=  (foldr otimes z (x:xs)) `oplus` (foldr otimes z ys) {-"~~."-}
\end{spec}

\noindent {\bf Direction} $(\Rightarrow)$. Given
|foldr otimes z = hom oplus z|.
Let |y = foldr otimes z xs| and |w = foldr otimes z ys| for some
|xs| and |ys|. We reason:
\begin{spec}
  x `otimes` (y `oplus` w)
= x `otimes` (foldr otimes z xs `oplus` foldr otimes z ys)
=  {- since |foldr otimes z = hom oplus z| -}
  x `otimes` (foldr otimes z (xs ++ ys))
= foldr otimes z (x : xs ++ ys)
   {- since |foldr otimes z = hom oplus z| -}
= foldr otimes z (x : xs) `oplus` foldr otimes z ys
= (x `otimes` foldr otimes z xs) `oplus` foldr otimes z ys
= (x `otimes` y) `oplus` w {-"~~."-}
\end{spec}

\end{proof}

\section{Aggregation}

Definitions intended to model Spark aggregation:

\begin{code}
type Partition a  = [a] {-"~~,"-}
type RDD a        = [Partition a] {-"~~,"-}
\end{code}

\begin{spec}
aggregate  :: N `mem` eps => b -> (a -> b -> b) -> (b -> b -> b) -> RDD a -> Me eps b
aggregate z otimes oplus =
  foldr oplus z <.> (perm . map (foldr otimes z)) {-"~~."-}
\end{spec}

\begin{lemma} \label{lemma:fold-otimes-concat}
Given |otimes :: a -> b -> b| and define
|xs `odot` w = foldr otimes w xs|. We have |foldr otimes z . concat = foldr odot z|.
\end{lemma}
\begin{proof}
By |foldr| fusion the proof obligation is
\begin{spec}
  foldr otimes z (xs ++ ys) = foldr otimes (foldr otimes z ys) xs {-"~~."-}
\end{spec}
Induction on |xs|.

\noindent{Case} |xs := []|:
\begin{spec}
   foldr otimes (foldr otimes z ys) []
=  foldr otimes z ys
=  foldr otimes z ([] ++ ys) {-"~~."-}
\end{spec}

\noindent{Case} |xs := x : xs|:
\begin{spec}
   foldr otimes (foldr otimes z ys) (x:xs)
=  x `otimes` foldr otimes (foldr otimes z ys) xs
=    {- induction -}
   x `otimes` foldr otimes z (xs ++ ys)
=  foldr otimes z (x : xs++ ys) {-"~~."-}
\end{spec}
\end{proof}

% \begin{lemma} Given |otimes :: a -> b -> b| and define
% < odot         :: [a] -> b -> b
% < xs `odot` w  = foldr otimes w xs {-"~~."-}
% We have that |xs `odot` (ys `odot` w) = ys `odot` (xs `odot` w)| for all
% |xs|, |ys|, and |w|, provided that ....
% \end{lemma}

\begin{theorem}
\label{thm:aggregate-det}
|aggregate z otimes oplus = return . foldr oplus z . map (foldr otimes z)|,
provided that |oplus| is associative, commutative, and has |z| as identity.
\end{theorem}
\begin{proof} We reason:
\begin{spec}
   aggregate z otimes oplus
=   {- definition of |aggregate| -}
   foldr oplus z <.> (perm . map (foldr otimes z))
=   {- Lemma \ref{lemma:perm-map} -}
   foldr oplus z <.> (map (foldr otimes z) <.> perm)
=   {- by \eqref{eq:comp-mcomp-mcomp} -}
   (foldr oplus z . map (foldr otimes z)) <.> perm
=   {- Lemma \ref{lemma:fold-perm} -}
   return . foldr oplus z . map (foldr otimes z) {-"~~."-}
\end{spec}
The last step holds because by |foldr|-|map| fusion, for all |h|,
< foldr oplus z . map h = foldr odot z
<  where xs `odot` w = h xs `oplus` w {-"~~,"-}
and |odot| satisfies that
|xs `odot` (ys `odot` w) = ys `odot` (xs `odot` w)|
if |oplus| is associative, commutative,
and has |z| as identity.
\end{proof}

\begin{corollary}
\label{cor:aggregate-det-hom}
|aggregate z otimes oplus = return . foldr otimes z . concat|, provided that
|oplus| is associative, commutative, and has |z| as identity, and that
|foldr otimes z = hom oplus z|.
\end{corollary}
\begin{proof} We reason:
\begin{spec}
   aggregate z otimes oplus
=   {- Theorem \ref{thm:aggregate-det} -}
   return . foldr oplus z . map (foldr otimes z)
=   {- Lemma \ref{lemma:hom-concat} -}
   return . foldr otimes z . concat {-"~~."-}
\end{spec}
\end{proof}

\begin{lemma}
\label{lemma:aggregate-det-reasoning}
If |aggregate z otimes oplus = return . foldr otimes z . concat|,
and |perm xss = return yss `mplus` m|, we have
< foldr otimes z (concat xss) =
<   foldr oplus z (map (foldr otimes z) xss) =
<     foldr oplus z (map (foldr otimes z) yss) {-"~~."-}
\end{lemma}
\begin{proof}
We assume the following two properties of |MonadPlus|:
\begin{enumerate}
\item |m1 `mplus` m2 = return x| implies that |m1 = m2 = return x|.
\item |return x1 = return x2| implies that |x1 = x2|.
\end{enumerate}

For our problem, if |perm xss = return yss `mplus` m|, we have
\begin{spec}
   return . foldr otimes z . concat `app` xss
=    {- assumption -}
   aggregate z otimes oplus `app` xss
=    {- calculation in the previous lemma -}
   (foldr oplus z . map (foldr otimes z)) <$> perm xss
=    {- |perm xss = return yss `mplus` m| -}
   (return . foldr oplus z . map (foldr otimes z) `app` yss) `mplus`
      ((foldr oplus z . map (foldr otimes z)) <$> m) {-"~~."-}
\end{spec}
\end{proof}

\begin{theorem}
\label{thm:aggregate-cmonoid}
If |aggregate z otimes oplus = return . foldr otimes z . concat|,
we have that |oplus|, when restricted to values in |img (foldr otimes z)|, is associative, commutative, and has |z| as identity.
\end{theorem}
\begin{proof}
In the discussion below, let |x|,|y|, and |w| be in |img (foldr otimes z)|. That is, there exists |xs|, |ys|, and |ws| such that |x = foldr otimes z xs|,
|y = foldr otimes z ys|, and |w = foldr otimes z ws|.

\noindent {\bf Identity}. We reason:
\begin{spec}
   y
=  foldr otimes z (concat [xs])
=    {- |perm [xs] = return [xs] `mplus` mzero|, Lemma \ref{lemma:aggregate-det-reasoning} -}
   foldr oplus z (map (foldr otimes z) [xs])
=  y `oplus` z {-"~~."-}
\end{spec}
Thus |z| is a right identity of |oplus|.
\begin{spec}
   y
=  foldr otimes z (concat [[],xs])
=    {- |perm [[], xs] = return [[], xs] `mplus` m|, Lemma \ref{lemma:aggregate-det-reasoning} -}
   foldr oplus z (map (foldr otimes z) [[], xs])
=  z `oplus` (y `oplus` z)
=   {- |z| is a right identity of |oplus| -}
   z `oplus` y {-"~~."-}
\end{spec}
Thus |z| is also a left identity of |oplus|.

\noindent
{\bf Commutativity}. We reason:
\begin{spec}
   x `oplus` y
=    {- |z| is a right identity -}
   x `oplus` (y `oplus` z)
=  foldr oplus z (map (foldr otimes z) [xs, ys])
=    {- |perm [xs,ys] = return [ys,xs] `mplus` m|, Lemma \ref{lemma:aggregate-det-reasoning} -}
   foldr oplus z (map (foldr otimes z) [ys, xs])
=  y `oplus` (x `oplus` z)
   y `oplus` x {-"~~."-}
\end{spec}

\noindent
{\bf Associativity}. We reason:
\begin{spec}
   x `oplus` (y `oplus` w)
=    {- |z| is a right identity -}
   x `oplus` (y `oplus` (w `oplus` z))
=  foldr oplus z (map (foldr otimes z) [xs, ys, ws])
=    {- -}
   foldr oplus z (map (foldr otimes z) [ws, xs, ys])
=  w `oplus` (x `oplus` (y `oplus` z))
=    {- |z| is a right identity -}
   w `oplus` (x `oplus` y)
=    {- |oplus| commutative -}
   (x `oplus` y) `oplus` w {-"~~."-}
\end{spec}
\end{proof}

\begin{theorem}
\label{thm:aggregate-hom}
If |aggregate z otimes oplus = return . foldr otimes z . concat|,
we have |foldr otimes z = hom oplus z|.
\end{theorem}
\begin{proof}
Apparently |foldr otimes z [] = z|. We are left with proving the
case for concatenation.

\begin{spec}
   foldr otimes z (xs ++ ys)
=  foldr otimes z (concat [xs,ys])
=    {- Lemma \ref{lemma:aggregate-det-reasoning} -}
   foldr oplus z (map (foldr otimes z) [xs,ys])
=  foldr otimes z xs `oplus` (foldr oplus z ys `oplus` z)
=    {- Theorem \ref{thm:aggregate-cmonoid}, |z| is identity -}
   foldr otimes z xs `oplus` foldr oplus z ys {-"~~."-}
\end{spec}
\end{proof}

\begin{corollary} Given |otimes :: a -> b -> b| and |oplus :: b -> b -> b|.
|aggregate z otimes oplus = return . foldr otimes z . concat| if and only
if |(img (foldr otimes z), oplus, z)| forms a commutative monoid, and
that |foldr otimes z = hom oplus z|.
\end{corollary}
\begin{proof}
A conclusion following from Corollary \ref{cor:aggregate-det-hom},
Theorem \ref{thm:aggregate-cmonoid}, and Theorem \ref{thm:aggregate-hom}.
\end{proof}

Results about |treeAggregate| and |aggregateByKey|, etc,
are recorded in another document and omitted here.

\section{Proofs of monadic properties}

Proof of properties \eqref{eq:comp-bind-ap}-\eqref{eq:mcomp-kc}, as exercises.

\paragraph{Proving \eqref{eq:comp-bind-ap}} |f =<< (g <$> m) = (f . g) =<< m|.
\begin{proof} We reason:
\begin{spec}
   f =<< (g <$> m)
=    {- definition of |(<$>)| -}
   f =<< ((return . g) =<< m)
=    {- monadic law \eqref{eq:monad-assoc} -}
   (\x -> f =<< return (g x)) =<< m
=    {- monadic law \eqref{eq:monad-bind-ret} -}
   (\x -> f (g x)) =<< m
=  (f . g) =<< m {-"~~."-}
\end{spec}
\end{proof}

\paragraph{Proving \eqref{eq:comp-ap-ap}} |f <$> (g <$> m) = (f . g) <$> m|.
\begin{proof} We reason:
\begin{spec}
   f <$> (g <$> m)
=    {- definition of |(<$>)| -}
   (return . f) =<< (g <$> m)
=    {- by \eqref{eq:comp-bind-ap} -}
   (return . f . g) =<< m
=    {- definition of |(<$>)| -}
   (f . g) =<< m {-"~~."-}
\end{spec}
\end{proof}

For the next results we prove a lemma:
\begin{equation}
|(f =<<) . (g =<<) = (((f =<<) . g) =<<)| \mbox{~~.} \label{eq:bind-comp-bind}
\end{equation}
\begin{spec}
   (f =<<) . (g =<<)
=    {- $\eta$ intro. -}
   (\m -> f =<< (g =<< m))
=    {- monadic law \eqref{eq:monad-assoc} -}
   (\m -> (\y -> f =<< g y) =<< m)
=    {- $\eta$ reduction -}
   (((f =<<) . g) =<<) {-"~~."-}
\end{spec}

% For the next results we prove a lemma:
% \begin{equation}
% |(f =<<) . (g <.> h) = ((f . g) =<<) . h| \mbox{~~.} \label{eq:bind-comp-mcomp}
% \end{equation}
% \begin{proof}
% \begin{spec}
%    (f =<<) . (g <.> h)
% =    {- definition of |(<.>)| -}
%    (f =<<) . ((return . g) =<<) . h
% =    {- $\eta$ intro. -}
%    (\m -> f =<< ((return . g) =<< m)) . h
% =    {- monadic law \eqref{eq:monad-assoc} -}
%    (\m -> (\y -> f =<< return (g y)) =<< m) . h
% =    {- monadic law \eqref{eq:monad-bind-ret} -}
%    (\m -> (\y -> f (g y)) =<< m) . h
% =    {- $\eta$ reduction -}
%    ((f . g) =<<) . h {-"~~."-}
% \end{spec}
% \end{proof}

\paragraph{Proving \eqref{eq:comp-mcomp-mcomp}} |f <.> (g <.> m) = (f . g) <.> m|.
\begin{proof} We reason:
  \begin{spec}
     f <.> (g <.> m)
  =    {- definition of |(<.>)| -}
     ((return . f) =<<) . ((return . g) =<<) . m
  =    {- by \eqref{eq:bind-comp-bind} -}
     ((((return . f) =<<) . return . g) =<<) . m
  =    {- monadic law \eqref{eq:monad-bind-ret} -}
     ((return . f . g) =<<) . m
  =    {- definition of |(<.>)| -}
     (f . g) <.> m {-"~~."-}
  \end{spec}
% \begin{spec}
%    f <.> (g <.> m)
% =    {- definition of |(<.>)| -}
%    ((return . f) =<<) . (g <.> m)
% =    {- by \eqref{eq:bind-comp-mcomp} -}
%    ((return . f . g) =<<) . m
% =    {- definition of |(<.>)| -}
%    (f . g) <.> m {-"~~."-}
% \end{spec}
\end{proof}

\paragraph{Proving \eqref{eq:kc-mcomp}} |f <=< (g <.> h) = (f . g) <=< h|.
\begin{proof} We reason:
\begin{spec}
   f <=< (g <.> h)
=    {- definitions of |(<=<)| -}
   (f =<<) . ((return . g) =<<) . h
=    {- by \eqref{eq:bind-comp-bind} -}
   (((f =<<) . return . g) =<<) . h
=    {- monadic law \eqref{eq:monad-bind-ret} -}
   (((f . g) =<<) . h
=    {- definition of |(<=<)| -}
   (f . g) <=< h {-"~~."-}
\end{spec}
% \begin{spec}
%    f <=< (g <.> h)
% =    {- definitions of |(<=<)| -}
%    (f =<<) . (g <.> h)
% =    {- by \eqref{eq:bind-comp-mcomp} -}
%    ((f . g) =<<) . h
% =    {- definition of |(<=<)| -}
%    (f . g) <=< h {-"~~."-}
% \end{spec}
\end{proof}

\paragraph{Proving \eqref{eq:mcomp-kc}} |f <.> (g <=< h) = (f <.> g) <=< h|.
\begin{proof} We reason:
\begin{spec}
   f <.> (g <=< h)
=    {- definitions of |(<=<)| and |(<.>)| -}
   ((return . f) =<<) . (g =<<) . h
=    {- by \eqref{eq:bind-comp-bind} -}
   ((((return . f) =<<) . g) =<<) . h
=    {- definition of |(<.>)| -}
   ((f <.> g) =<<) . h
=    {- definition of |(<=<)| -}
   (f <.> g) <=< h {-"~~."-}
\end{spec}
\end{proof}
\end{document}
