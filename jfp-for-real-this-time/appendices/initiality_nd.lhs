\section{Initiality of Lists for Nondeterminism}
\label{app:universality-nondeterminism}

This section shows, with a proof using equational reasoning techniques,
that the |List| monad is the inital lawful instance of |MNondet|.

Therefore, there must be a unique morphism |g :: MNondet m => [a] -> m a| from the |List| monad
to every other lawful instance of nondeterminism which preserves the five equations in Figure \ref{fig:5eqs}.

\begin{figure}[htbp]
  \centering
\begin{align*}
&|g [] = mzero| \tag{1} \\
&|g (x ++ y) = g x `mplus` g y| \tag{2} \\
&|g . etal = etand| \tag{3} \\
&|g . mul = mund . g . fmap g| \tag{4} \\
&|g . mul = mund . fmap g . g| \tag{5}
\end{align*}
  \caption{Properties of morphism |g :: MNondet m => [a] -> m a|.}
  \label{fig:5eqs}
\end{figure}

% And the following two diagrams commute:
% \[\begin{tikzcd}
%     {|[a]|} && {|m a|} && {|[[a]]|} &&&& {|m (m a)|} \\
%     \\
%     & {|a|} & && {|[a]|} &&&& {|m a|}
%     \arrow["{|mul|}", from=1-5, to=3-5]
%     \arrow["{|g . fmap g|}", from=1-5, to=1-9]
%     \arrow["{|fmap g . g|}"', draw=none, from=1-5, to=1-9]
%     \arrow["{|mund|}", from=1-9, to=3-9]
%     \arrow["{|g|}"', from=3-5, to=3-9]
%     \arrow["{|g|}", from=1-1, to=1-3]
%     \arrow["{|etand|}"', from=3-2, to=1-3]
%     \arrow["{|etal|}", from=3-2, to=1-1]
% \end{tikzcd}\]

First, we show that this morphism exists and is the |choose| function.
We prove the four equations in sequence.

\begin{theorem}
|choose [] = mzero|
\end{theorem}
\begin{proof}~
<    choose []
< = {-~  definition of |choose|  -}
<    foldr (mplus . etand) mzero []
< = {-~  definition of |foldr|  -}
<    mzero
\end{proof}

\begin{theorem} \label{eq:A2}
|choose (xs ++ ys) = choose xs `mplus` choose ys|
\end{theorem}

\begin{proof}
The proof proceeds by structural induction on the list |xs|.

\noindent
\mbox{\underline{case |xs = []|}}

<    choose ([] ++ ys)
< = {-~  definition of |(++)|  -}
<    choose ys
< = {-~  Law (\ref{eq:mzero}): identity of |mzero|   -}
<    mzero `mplus` choose ys
< = {-~  definition of |choose|  -}
<    choose [] `mplus` choose ys

% \noindent
% \mbox{\underline{case |xs = [x]|}}
% \wenhao{I think we need to include this case because it is used in the case |xs = (x:xs)|.}

% <    choose ([x] ++ ys)
% < = {-~  definition of |(++)|  -}
% <    choose (x : ys)
% < = {-~  definition of |choose|  -}
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
< = {-~  Law (\ref{eq:mplus-assoc}): associativity of |mplus|  -}
<    (etand x `mplus` choose xs) `mplus` choose ys
< = {-~  definition of |choose|  -}
<    (etand x `mplus` foldr (mplus . etand) mzero xs) `mplus` choose ys
< = {-~  definition of |foldr|  -}
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
< = {-~  Law (\ref{eq:mzero}): identity of |mzero|  -}
<    etand x
\vspace{-6mm}
\end{proof}



For the last two equations, it suffices to prove one of the following two equations:
< choose . mul = mund . choose . fmap choose
< choose . mul = mund . fmap choose . choose
Both properties are equivalent due to the naturality of the natural transformation |choose|.
We do a case analysis on the list argument.
We use the laws of Section \ref{sec:background}, utilizing the fact that per definition
|mu f = f >>= id|\footnote{|mu| is also referred to as the |join| operator.}.

% \fbox{|choose . mul = mund . choose . fmap choose|}
\begin{theorem}
|choose . mul = mund . choose . fmap choose|
\end{theorem}

\begin{proof}
We prove that the equation |(choose . mul) xs = (mund . choose . fmap choose) xs| holds for every list |xs|.
The proof proceeds by structural induction on the list |xs|.

\noindent
\mbox{\underline{case |xs = []|}}

<    choose (mul [])
< = {-~  definition of |mul|  -}
<    choose []
< = {-~  definition of |choose|  -}
<    mzero
< = {-~  Law (\ref{eq:mzero-zero}): left-identity  -}
<    mzero >>= id
< = {-~  definition of |mu|  -}
<    mund mzero
< = {-~  definition of |choose|  -}
<    mund (choose [])
< = {-~  definition of |fmap|  -}
<    mund (choose (fmap choose []))

\noindent
\mbox{\underline{case |xs = (x:xs)|}}

<    choose (mul (x:xs))
< = {-~  definition of |mul|  -}
<    choose (x ++ mul xs)
< = {-~  Theorem \ref{eq:A2}  -}
<    choose x `mplus` choose (mul xs)
< = {-~  induction hypothesis  -}
<    choose x `mplus` mund (choose (fmap choose xs))
< = {-~  Law (\ref{eq:monad-ret-bind}): return-bind with |mu = >>= id|  -}
<    mund (etand (choose x)) `mplus` mund (choose (fmap choose xs))
< = {-~  (\ref{eq:mplus-dist}): right-distributivity  -}
<    mund (etand (choose x) `mplus` choose (fmap choose xs))
< = {-~  reformulation  -}
<    mund (mplus . etand) (choose x) (choose (fmap choose xs)))
< = {-~  definition of |choose|  -}
<    mund (choose (choose x : fmap choose xs))
< = {-~  definition of |fmap|  -}
<    mund (choose (fmap choose (x:xs)))

\vspace{-6mm}
\end{proof}

To prove that |choose| is unique, we use the universality of |foldr|.
\begin{theorem}[Universal Property of |fold|] \label{thm:univ-fold}
For finite lists, the function |g = foldr f v| is unique with the following
equations holding.
\begin{align*}
|g []| &= |v| &  & \\
& &\Longleftrightarrow \hspace{10ex} |g| &= |foldr f v| \\
|g (x:xs)| &= |f x (g xs)| & &
\end{align*}
\end{theorem}

\begin{theorem}[Uniqueness of |choose|]
For any other morphism |g :: MNondet m => [a] -> m a| which satisfies the five equations in Figure \ref{fig:5eqs}, we have |g = choose|.
\end{theorem}

\begin{proof}
Because |choose = foldr (mplus . etand) mzero|, by the universal property of |foldr|, we only need to prove the following two equations:
\begin{enumerate}
\item |g [] = mzero|
\item |g (x:xs) = (mplus . etand) x (g xs)|
\end{enumerate}

The first equation follows directly from Equation (1) in Figure \ref{fig:5eqs}.
For the second equation, we reason as follows:

<    g (x:xs)
< = {-~  definition of |(++)|  -}
<    g ([x] ++ xs)
< = {-~  equation (2) in Figure \ref{fig:5eqs}  -}
<    g [x] `mplus` g xs
< = {-~  definition of  |etal|  -}
<    g (etal x) `mplus` g xs
< = {-~  reformulation  -}
<    (g . etal) x `mplus` g xs
< = {-~  equation (3) in Figure \ref{fig:5eqs}  -}
<    etand x `mplus` g xs
< = {-~  reformulation  -}
<    (mplus . etand) x (g xs)

\end{proof}
