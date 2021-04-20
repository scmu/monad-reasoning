\section{Initiality of |List| for Nondeterminism}
\label{app:universality-nondeterminism}

This section shows, with a proof using equational reasoning techniques,
that the |List| monad is the inital lawful instance of state. 

Therefore, there must be a unique morphism from the |List| monad
to every other lawful instance of nondeterminism. 
To show this morphism exists, we have to make the following two
drawings commute:

\[\begin{tikzcd}
    {[a]} && {m\,a} && {[[a]]} &&&& {m\,(m\, a)} \\
    \\
    & a & && {[a]} &&&& {m\,a}
    \arrow["{\mu_{[]}}", from=1-5, to=3-5]
    \arrow["{|choose . fmap choose|}", from=1-5, to=1-9]
    \arrow["{|fmap choose . choose|}"', draw=none, from=1-5, to=1-9]
    \arrow["{\mu_m}", from=1-9, to=3-9]
    \arrow["{|choose|}"', from=3-5, to=3-9]
    \arrow["{|choose|}", from=1-1, to=1-3]
    \arrow["{\eta_m}"', from=3-2, to=1-3]
    \arrow["{\eta_{[]}}", from=3-2, to=1-1]
\end{tikzcd}\]

The former equality is easy to prove using equational reasoning:

\fbox{|choose . etal = etam|}

<    choose (etal x)
< = {-~  definition of |etal|  -}
<    choose [x]
< = {-~  definition of |choose|  -}
<    foldr (mplus . etam) mzero [x]
< = {-~  evaluation of |foldr|  -}
<    (mplus . etam) x mzero
< = {-~  reformulation  -}
<    etam x `mplus` mzero
< = {-~  identity of |mzero| (\ref{eq:mzero})  -}
<    etam x

For the second proof, we do a case analysis.
We use the laws of Section \ref{sec:background}, utilizing the fact that 
|mu f = f >>= id|.

\fbox{|choose . mul = mum . choose . fmap choose|}

\noindent
\mbox{\underline{case []}}

<    choose (mul [])
< = {-~  definition of |mul = foldr (++) []|  -}
<    choose []
< = {-~  definition of |choose = foldr (mplus . etam) mzero|  -}
<    mzero
< = {-~  left-identity (\ref{eq:mzero-zero}) with |f = id|  -}
<    mum mzero
< = {-~  definition of |choose|, base case  -}
<    mum (choose [])
< = {-~  definition of |fmap|  -}
<    mum (choose (fmap choose []))

\noindent
\mbox{\underline{case (x:xs)}}

<    choose (mul (x:xs))
< = {-~  definition of |mul = foldr (++) []|  -}
<    choose (x ++ mul xs)
< = {-~  definition of |choose|  -}
<    foldr (mplus . etam) mzero (x ++ mul xs)
< = {-~  evaluation of |foldr|  -}
<    (mplus . etam) x (choose (mul xs))
< =  etam x `mplus` choose mul xs
< = {-~  induction hypothesis  -}
<    etam x `mplus` mum (choose (fmap choose xs))
< = {-~  monad law return-bind (\ref{eq:monad-ret-bind})  -}
<    mum (etam (etam x)) `mplus` mum (choose (fmap choose xs))
< = {-~  distributivity of |mum| and |mplus| (\ref{eq:mplus-dist})  -}
<    mum (etam (etam x) `mplus` choose (fmap choose xs))
< =  mum (mplus . etam) (etam x) (choose (fmap choose xs)))
< = {-~  definition of |choose = foldr (mplus . etam) mzero|  -}
<    mum (choose (etam x : fmap choose xs))
< = {-~  definition of |etam = choose . etal|  -}
<    mum (choose (choose (etal x) : fmap choose xs))
< = {-~  definition of |fmap|  -}
<    mum (choose (fmap choose (etal x : xs)))
< = {-~  definition of |etal|  -}
<    mum (choose (fmap choose ([x] : xs)))

\todo{extra brackets :(}

To prove that this morphism is unique, we use the universality of fold.














