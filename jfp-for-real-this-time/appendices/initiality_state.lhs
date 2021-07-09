\section{Initiality of |StateT| for State and Nondeterminism}
\label{app:local-global}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

import Control.Monad.Trans.State.Lazy -- hiding (get, put)

class Monad m => N s m | m -> s where
    getn :: m s
    putn :: s -> m ()
    alphn :: n a -> m a

local :: (N s n) => StateT s m a -> n a
local x = do
    s <- getn
    (x', s') <- alphn (runStateT x s)
    putn s'
    etan x'

etals :: (Monad m) => a -> StateT s m a
etals x = StateT $ \s -> eta (x, s)

etan :: (N s n) => a -> n a
etan = return

eta :: (Monad m) => a -> m a
eta = return 

getls :: (Monad m) => StateT s m s 
getls = StateT (\s -> eta (s, s))

putls :: (Monad m) => s -> StateT s m ()
putls s = StateT (\_ -> eta ((), s))

liftls :: (Monad m) => m a -> StateT s m a
liftls mx = StateT (\s -> mx >>= \x -> eta (x, s))

muls :: (Monad m) => StateT s m (StateT s m a) -> StateT s m a
muls mmx = StateT (\s -> runStateT mmx s >>= \(mx, s1) -> runStateT mx s1)

\end{code}
%endif

This section shows, with a proof using equational reasoning techniques,
that the |StateT| monad is the initial lawful instance for state. 

Therefore, |StateT| must be initial in the category 
$\langle N, \eta_N, \mu_N, get, put, \alpha \rangle$ 
where |etan| and |mun| are the monadic return and join operations, 
|get| and |put| are the two state operations, and
|alph :: M -> N| is a monad morphism.
In Haskell:

< class Monad m => N s m | m -> s where
<     getn :: m s
<     putn :: s -> m ()
<     alphn :: n a -> m a

Objects in this category must satisfy the monad laws, 
the state laws
and the monad transformation laws \todo{ref monad transformer library}:
\begin{alignat}{2}
    &\mbox{\bf alpha-return}:\quad &
    |alph . eta| &= |eta|\mbox{~~,} \label{eq:alpha-ret}\\
    &\mbox{\bf alpha-bind}:~ &
    |alph (m >>= f)| &= |alph m >>= (alph . f)| \mbox{~~.}
    \label{eq:alpha-bind}
\end{alignat}

Additionally, it should satisfy the following interaction law:
\begin{alignat}{2}
    &\mbox{\bf put-alpha}:\quad &
    |put s >> alph m| &= |alph m >>= \x -> put s >> eta x|\mbox{~~.} \label{eq:put-alpha}
\end{alignat}

For |StateT| to be initial, there must be a unique morphism from |StateT| to any other monad |N| in the above category.
This morphism is the |local| function, defined as follows:

< local :: (N s n) => StateT s m a -> n a
< local x = do
<     s         <- getn
<     (x', s')  <- alphn (runStateT x s)
<     putn s'
<     etan x'

First, we prove that there is a morphism from |StateT| to |N|, by showing 
that |local| maps |eta|, |mu|, |get|, |put| and |alph| of |StateT| to the same
functions of |N|.


\fbox{|local . etals = etan|}

% https://q.uiver.app/?q=WzAsMyxbMSwxLCJ8YXwiXSxbMCwwLCJ8U3RhdGVUIHMgbSBhfCJdLFsyLDAsInxOIGF8Il0sWzAsMiwifGV0YW58IiwyXSxbMCwxLCJ8ZXRhbHN8Il0sWzEsMiwibG9jYWwiXV0=
\[\begin{tikzcd}
	{|StateT s m a|} && {|n a|} \\
	& {|a|}
	\arrow["{|etan|}"', from=2-2, to=1-3]
	\arrow["{|etals|}", from=2-2, to=1-1]
	\arrow["{|local|}", from=1-1, to=1-3]
\end{tikzcd}\]

<    local (etals x)
< = {-~  definition of |etals|  -}
<    local (StateT $ \s -> eta (x, s))
< = {-~  definition of |local|  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT (StateT $ \s -> eta (x, s)) s)
<        putn s'
<        etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do  s <- getn
<        (x', s') <- alphn ((\s -> eta (x, s)) s)
<        putn s'
<        etan x'
< = {-~  function application  -}
<    do  s <- getn
<        (x', s') <- alphn (eta (x, s))
<        putn s'
<        etan x'
< = {-~  alpha-return law \ref{eq:alpha-ret}  -}
<    do  s <- getn
<        (x', s') <- eta (x, s)
<        putn s'
<        etan x'
< = {-~  return-bind law \ref{eq:monad-ret-bind} with |(x' = x), (s' = s)|  -}
<    do  s <- getn
<        putn s
<        etan x
< = {-~  get-put law \ref{eq:get-put}  -}
<    etan x


\fbox{|local . muls = mun . fmap local . local|}

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ8U3RhdGVUIHMgbSAoU3RhdGVUIHMgbSBhKXwiXSxbMCwyLCJ8U3RhdGVUIHMgbSBhfCJdLFszLDIsInxOIGF8Il0sWzMsMCwifE4gKE4gYSl8Il0sWzAsMSwifG11bHN8IiwyXSxbMywyLCJ8bXVufCJdLFswLDMsInxsb2NhbCAuIGZtYXAgbG9jYWx8Il0sWzAsMywifGZtYXAgbG9jYWwgLiBsb2NhbHwiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJub25lIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMSwyLCJ8bG9jYWx8IiwyXV0=
\[\begin{tikzcd}
	{|StateT s m (StateT s m a)|} &&& {|n (n a)|} \\
	\\
	{|StateT s m a|} &&& {|n a|}
	\arrow["{|muls|}"', from=1-1, to=3-1]
	\arrow["{|mun|}", from=1-4, to=3-4]
	\arrow["{|local . fmap local|}", from=1-1, to=1-4]
	\arrow["{|fmap local . local|}"', draw=none, from=1-1, to=1-4]
	\arrow["{|local|}"', from=3-1, to=3-4]
\end{tikzcd}\]

<    local (muls mmx)
< = {-~  definition of |muls|  -}
<    local (StateT (\s -> runStateT mmx s >>= \(mx, s') -> runStateT mx s'))
< = {-~  definition of |local|  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT (StateT (\s -> runStateT mmx s >>= \(mx, s1) -> runStateT mx s1)) s)
<        putn s'
<        etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do  s <- getn
<        (x', s') <- alphn ((\s -> runStateT mmx s >>= \(mx, s1) -> runStateT mx s1) s)
<        putn s'
<        etan x'
< = {-~  function application  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT mmx s >>= \(mx, s1) -> runStateT mx s1))
<        putn s'
<        etan x'
< = {-~  alpha-bind law \ref{eq:alpha-bind}  -}
<    do  s <- getn
<        (mx, s1) <- alphn (runStateT mmx s)
<        (x', s') <- alphn (runStateT mx s1)
<        putn s'
<        etan x'
< = {-~  put-put law \ref{eq:put-put}  -}
<    do  s <- getn
<        (mx, s1) <- alphn (runStateT mmx s)
<        (x', s') <- alphn (runStateT mx s1)
<        putn s1 
<        putn s'
<        etan x'
< = {-~  put-alpha law \ref{eq:put-alpha}  -}
<    do  s <- getn
<        (mx, s1) <- alphn (runStateT mmx s)
<        putn s1
<        (x', s') <- alphn (runStateT mx s1)
<        putn s'
<        etan x'
< = {-~  put-get law \ref{eq:put-get}  -}
<    do  s <- getn
<        (mx, s1) <- alphn (runStateT mmx s)
<        putn s1
<        s1 <- getn
<        (x', s') <- alphn (runStateT mx s1)
<        putn s'
<        etan x'
< = {-~  rewrite  -}
<    mun (do  s <- getn
<              (mx, s1) <- alphn (runStateT mmx s)
<               putn s1
<               etan (do  s1 <- getn
<                         (x', s') <- alphn (runStateT mx s1)
<                         putn s'
<                         etan x'
<                    ))
< = {-~  |fmap local mx = mx >> eta . local|  -}
<    mun (fmap local (do  s <- getn
<                         (x', s') <- alphn (runStateT x s)
<                         putn s'
<                         etan x'))
< = {-~  definition of |local|  -}
<    mun (fmap local (local mmx))

\fbox{|local getls = getn|}

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ8U3RhdGVUIHMgbSBhfCJdLFsyLDAsInxOIGF8Il0sWzAsMV0sWzIsMV0sWzAsMSwifGxvY2FsfCJdLFsyLDAsInxnZXRsc3wiXSxbMywxLCJ8Z2V0bnwiLDJdXQ==
\[\begin{tikzcd}
	{|StateT s m a|} && {|n a|} \\
	{} && {}
	\arrow["{|local|}", from=1-1, to=1-3]
	\arrow["{|getls|}", from=2-1, to=1-1]
	\arrow["{|getn|}"', from=2-3, to=1-3]
\end{tikzcd}\]

<    local getls
< = {-~  definition of |getls|  -}
<    local (StateT (\s -> eta (s, s)))
< = {-~  definition of |local|  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT (StateT (\s -> eta (s, s))) s)
<        putn s'
<        etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do  s <- getn
<        (x', s') <- alphn ((\s -> eta (s, s)) s)
<        putn s'
<        etan x'
< = {-~  function application  -}
<    do  s <- getn
<        (x', s') <- alphn (eta (s, s))
<        putn s'
<        etan x'
< = {-~  alpha-return law \ref{eq:alpha-ret}  -}
<    do  s <- getn
<        (x', s') <- eta (s, s)
<        putn s'
<        etan x'
< = {-~  return-bind law \ref{eq:monad-ret-bind} with |(x' = s), (s' = s)|  -}
<    do  s <- getn
<        putn s
<        etan s
< = {-~  get-put law \ref{eq:get-put}  -}
<    do  s <- getn
<        etan s
< = {-~  bind-return law \ref{eq:monad-bind-ret}  -}
<    getn

\fbox{|local . putls = putn|}

% https://q.uiver.app/?q=WzAsNSxbMCwwLCJ8U3RhdGVUIHMgbSBhfCJdLFswLDEsInxzfCJdLFsyLDAsInxuIGF8Il0sWzIsMSwifHN8Il0sWzEsMF0sWzEsMCwifHB1dGxzfCJdLFszLDIsInxwdXRufCIsMl0sWzAsMiwifGxvY2FsfCJdXQ==
\[\begin{tikzcd}
	{|StateT s m a|} & {} & {|n a|} \\
	{|s|} && {|s|}
	\arrow["{|putls|}", from=2-1, to=1-1]
	\arrow["{|putn|}"', from=2-3, to=1-3]
	\arrow["{|local|}", from=1-1, to=1-3]
\end{tikzcd}\]

<    local (putls s0)
< = {-~  definition of |putls|  -}
<    local (StateT (\_ -> eta ((), s0)))
< = {-~  definition of |local|  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT (StateT (\_ -> eta ((), s0))) s)
<        putn s'
<        etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do  s <- getn
<        (x', s') <- alphn ((\_ -> eta ((), s0)) s)
<        putn s'
<        etan x'
< = {-~  function application  -}
<    do  s <- getn
<        (x', s') <- alphn (eta ((), s0))
<        putn s'
<        etan x'
< = {-~  alpha-return law \ref{eq:alpha-ret}  -}
<    do  s <- getn
<        (x', s') <- eta ((), s0)
<        putn s'
<        etan x'
< = {-~  return-bind law \ref{eq:monad-ret-bind} with |(x' = ()), (s' = s0)|  -}
<    do  s <- getn
<        putn s0
<        etan ()
< = {-~  \todo{what law?}  -}
<    do  putn s0
<        etan ()
< = {-~  \todo{what law?}  -}
<    putn s0

\fbox{|local . alphls = alphn|}

% https://q.uiver.app/?q=WzAsMyxbMCwwLCJ8U3RhdGVUIG0gYXwiXSxbMiwwLCJ8biBhfCJdLFsxLDEsInxtIGF8Il0sWzIsMSwifGFscGhufCIsMl0sWzIsMCwifGFscGhsc3wiXSxbMCwxLCJ8bG9jYWx8Il1d
\[\begin{tikzcd}
	{|StateT m a|} && {|n a|} \\
	& {|m a|}
	\arrow["{|alphn|}"', from=2-2, to=1-3]
	\arrow["{|alphls|}", from=2-2, to=1-1]
	\arrow["{|local|}", from=1-1, to=1-3]
\end{tikzcd}\]

<    local (alphls mx)
< = {-~  definition of |alphls|  -}
<    local (StateT (\s -> mx >>= \x -> eta (x, s)))
< = {-~  definition of |local|  -}
<    do  s <- getn
<        (x', s') <- alphn (runStateT (StateT (\s -> mx >>= \x -> eta (x, s))) s)
<        putn s'
<        etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do  s <- getn
<        (x', s') <- alphn ((\s -> mx >>= \x -> eta (x, s)) s)
<        putn s'
<        etan x'
< = {-~  function application  -}
<    do  s <- getn
<        (x', s') <- alphn (mx >>= \x -> eta (x, s))
<        putn s'
<        etan x'
< = {-~  alpha-bind law \ref{eq:alpha-bind}  -}
<    do  s <- getn
<        x <- alphn mx
<        (x', s') <- alphn (eta (x, s))
<        putn s'
<        etan x'
< = {-~  alpha-return law \ref{eq:alpha-ret}  -}
<    do  s <- getn
<        x <- alphn mx
<        (x', s') <- eta (x, s)
<        putn s'
<        etan x'
< = {-~  return-bind law \ref{eq:monad-ret-bind} with |(x' = x), (s' = s)|  -}
<    do  s <- getn
<        x <- alphn mx
<        putn s
<        etan x
< = {-~  put-alpha law \ref{eq:put-alpha}  -}
<    do  s <- getn
<        putn s
<        alphn mx
< = {-~  get-put law \ref{eq:get-put}  -}
<    alphn mx

\todo{prove that this morphism is unique}


















