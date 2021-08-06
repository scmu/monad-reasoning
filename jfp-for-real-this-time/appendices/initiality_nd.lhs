\section{Initiality of Lists for Nondeterminism}
\label{app:universality-nondeterminism}

This section shows, with a proof using equational reasoning techniques,
that the |List| monad is the inital lawful instance of state. 

Therefore, there must be a unique morphism from the |List| monad
to every other lawful instance of nondeterminism. 
To show this morphism exists, we have to show the following two
diagrams commute:

\[\begin{tikzcd}
    {|[a]|} && {|m a|} && {|[[a]]|} &&&& {|m (m a)|} \\
    \\
    & {|a|} & && {|[a]|} &&&& {|m a|}
    \arrow["{|mul|}", from=1-5, to=3-5]
    \arrow["{|choose . fmap choose|}", from=1-5, to=1-9]
    \arrow["{|fmap choose . choose|}"', draw=none, from=1-5, to=1-9]
    \arrow["{|mund|}", from=1-9, to=3-9]
    \arrow["{|choose|}"', from=3-5, to=3-9]
    \arrow["{|choose|}", from=1-1, to=1-3]
    \arrow["{|etand|}"', from=3-2, to=1-3]
    \arrow["{|etal|}", from=3-2, to=1-1]
\end{tikzcd}\]

The first equality is easy to prove using equational reasoning:

% \fbox{|choose . etal = etand|}

\begin{theorem}
|choose . etal = etand|
\end{theorem}

\begin{proof}~
<    choose (etal x)
< = {-~  definition of |etal|  -}
<    choose [x]
< = {-~  definition of |choose|  -}
<    foldr (mplus . etand) mzero [x]
< = {-~  evaluation of |foldr|  -}
<    (mplus . etand) x mzero
< = {-~  reformulation  -}
<    etand x `mplus` mzero
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    etand x
\vspace{-6mm}
\end{proof}

For the second proof, we require the distributivity of |choose|.

% \fbox{|choose (xs ++ ys) = choose xs `mplus` choose ys|}

\begin{lemma}
|choose (xs ++ ys) = choose xs `mplus` choose ys|
\end{lemma}

\begin{proof}
The proof proceeds by structrual induction on the list |xs|.

\noindent
\mbox{\underline{case |xs = []|}}

<    choose ([] ++ ys)
< = {-~  definition of |(++)|  -}
<    choose ys
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    mzero `mplus` choose ys
< = {-~  definition of |choose|  -}
<    choose [] `mplus` choose ys

% \noindent
% \mbox{\underline{case |xs = [x]|}}
% \wenhao{I think we need to include this case because it is used in the case |xs = (x:xs)|.}

% <    choose ([x] ++ ys)
% < = {-~  definition of |(++)|  -}
% <    choose (x : ys)
% < = {-~  definition of |choose = foldr (mplus . etand) mzero|  -}
% <    (mplus . etand) x (choose ys)
% < = {-~  reformulation  -}
% <    etand x `mplus` choose ys
% < = {-~  definition of |etand = choose . etal|  -}
% <    choose (etal x) `mplus` choose ys
% < = {-~  definition of |etal|  -}
% <    choose [x] `mplus` choose ys

\noindent
\mbox{\underline{case |xs = (x:xs)|}}

<    choose ((x:xs) ++ ys)
< = {-~  definition of |(++)|  -}
<    choose (x : (xs ++ ys))
< = {-~  definition of |choose = foldr (mplus . etand) mzero|  -}
<    (mplus . etand) x (choose (xs ++ ys))
< = {-~  induction hypothesis  -}
<    (mplus . etand) x (choose xs `mplus` choose ys)
< = {-~  reformulation  -}
<    etand x `mplus` (choose xs `mplus` choose ys)
< = {-~  associativity of |mplus| (\ref{eq:mplus-assoc})  -}
<    (etand x `mplus` choose xs) `mplus` choose ys
< = {-~  definition of |choose|  -}
<    (etand x `mplus` foldr (mplus . etand) mzero xs) `mplus` choose ys
< = {-~  property of |foldr|  -}
<    foldr (mplus . etand) mzero (x:xs) `mplus` choose ys
< = {-~  definition of |choose|  -}
<    choose (x:xs) `mplus` choose ys

% < = {-~  reformulation  -}
% <    etand x `mplus` choose (xs ++ ys)
% < = {-~  definition of |etand = choose . etal|  -}
% <    choose (etal x) `mplus` choose (xs ++ ys)
% < = {-~  definition of |etal|  -}
% <    choose [x] `mplus` choose (xs ++ ys)
% < = {-~  induction hypothesis  -}
% <    choose [x] `mplus` choose xs `mplus` choose ys
% < = {-~  induction hypothesis  -}
% <    choose ([x] ++ xs) `mplus` choose ys
% < = {-~  definition of |(++)|  -}
% <    choose (x:xs) `mplus` choose ys

\vspace{-6mm}
\end{proof}

Now everything is in place to prove the second property.
It suffices to prove on of the following two properties:
< choose . mul = mund . choose . fmap choose
< choose . mul = mund . fmap choose . choose 
Both properties are equivalent due to the naturality of the natural transformation |choose|.
We do a case analysis on the list argument.
We use the laws of Section \ref{sec:background}, utilizing the fact that 
|mu f = f >>= id|.

% \fbox{|choose . mul = mund . choose . fmap choose|}
\begin{theorem}
|choose . mul = mund . choose . fmap choose|
\end{theorem}

\begin{proof}
We prove that the equation |(choose . mul) xs = (mund . choose . fmap choose) xs| holds for every list |xs|.
The proof proceeds by structrual induction on the list |xs|.

\noindent
\mbox{\underline{case |xs = []|}}

<    choose (mul [])
< = {-~  definition of |mul = foldr (++) []|  -}
<    choose []
< = {-~  definition of |choose = foldr (mplus . etand) mzero|  -}
<    mzero
< = {-~  left-identity (\ref{eq:mzero-zero}) with |f = id|  -}
<    mzero >>= id
< = {-~  equation |mu f = f >>= id|  -}
<    mund mzero
< = {-~  definition of |choose|, base case  -}
<    mund (choose [])
< = {-~  definition of |fmap|  -}
<    mund (choose (fmap choose []))

\noindent
\mbox{\underline{case |xs = (x:xs)|}}

<    choose (mul (x:xs))
< = {-~  definition of |mul = foldr (++) []|  -}
<    choose (x ++ mul xs)
< = {-~  distributivity of |choose|  -}
<    choose x `mplus` choose (mul xs)
< = {-~  induction hypothesis  -}
<    choose x `mplus` mund (choose (fmap choose xs))
< = {-~  monad law return-bind (\ref{eq:monad-ret-bind}) with |(>>=)| represented by |mu|  -}
<    mund (etand (choose x)) `mplus` mund (choose (fmap choose xs))
< = {-~  distributivity of |mund| and |mplus| (\ref{eq:mplus-dist}) with |f = id|  -}
<    mund (etand (choose x) `mplus` choose (fmap choose xs))
< = {-~  reformulation  -}
<    mund (mplus . etand) (choose x) (choose (fmap choose xs)))
< = {-~  definition of |choose = foldr (mplus . etand) mzero|  -}
<    mund (choose (choose x : fmap choose xs))
< = {-~  definition of |fmap|  -}
<    mund (choose (fmap choose (x:xs)))

\vspace{-6mm}
\end{proof}

To prove that this morphism is unique, we use the universality of fold.














