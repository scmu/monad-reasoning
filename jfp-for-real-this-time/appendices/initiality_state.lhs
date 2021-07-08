\section{Initiality of |StateT| for State and Nondeterminism}
\label{app:local-global}

%if False
\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

import Control.Monad.Trans.State.Lazy hiding (get, put)

class Monad m => MState s m | m -> s where
    get :: m s
    put :: s -> m ()

class MState s m => N s m where
    alph :: n a -> m a

local :: (N s n) => StateT s m a -> n a
local x = do
    s <- get
    (x', s') <- alph (runStateT x s)
    put s'
    etan x'

etals :: (Monad m) => a -> StateT s m a
etals x = StateT $ \s -> return (x, s)

etan :: (N s n) => a -> n a
etan x = return x

\end{code}
%endif

This section shows, with a proof using equational reasoning techniques,
that the |StateT| monad is the inital lawful instance of state. 

Therefore, |StateT| must be initial in the category 
$\langle N, \eta_N, \mu_N, get, put, \alpha$ 
where |eta_N| and |mu_N| are the monadic return and join operations, 
|get| and |put| are the two state operations, and
|alpha :: M -> N| is a monad morphism.

Objects in this category must satisfy the monad laws \ref{}, 
the state laws \ref{} 
and an additional interaction law:

\begin{alignat}{2}
    &\mbox{\bf interaction}:\quad &
    |put s >> alpha m| &= |alpha m >>= \x -> put s >> eta x|\mbox{~~.} \label{eq:interaction}
\end{alignat}

\todo{Check if |StateT| satisfies all these laws}

For |StateT| to be initial, there must be a unique morphism from |StateT| to any other monad |N| in the above category.

\todo{need two extra laws?}

\begin{alignat}{2}
    &\mbox{\bf alpha-return}:\quad &
    |alph . eta| &= |eta|\mbox{~~,} \label{eq:alpha-ret}\\
    &\mbox{\bf alpha-bind}:~ &
    |alph (m >>= f)| &= |alph m >>= (alph . f)| \mbox{~~.}
    \label{eq:alpha-bind}
\end{alignat}

\fbox{|local . etals = etan|}

<    local (etals x)
< = {-~  definition of |etals|  -}
<    local (StateT $ \s -> return (x, s))
< = {-~  definition of |local|  -}
<    do s <- get
<       (x', s') <- alph (runStateT (StateT $ \s -> return (x, s)) s)
<       put s'
<       etan x'
< = {-~  |runStateT . StateT = id|  -}
<    do s <- get
<       (x', s') <- alph ((\s -> return (x, s)) s)
<       put s'
<       etan x'
< = {-~  application  -}
<    do s <- get
<       (x', s') <- alph (return (x, s))
<       put s'
<       etan x'
< = {-~  |alph . return = return| \ref{}  -}
<    do s <- get
<       (x', s') <- return (x, s)
<       put s'
<       etan x'
< = {-~  |(x' = x), (s' = s)|  -}
<    do s <- get
<       put s
<       etan x
< = {-~  get-put law \ref{}  -}
<    etan x


% Therefore, there must be a unique morphism from the |List| monad
% to every other lawful instance of nondeterminism. 
% To show this morphism exists, we have to make the following two
% drawings commute:

% We can interpret programs with state and nondeterminism encoded in the 
% state transformer monad by means of the following |local| function.
% It computes a function that, given an initial state, returns the final value.

% < local :: MStateNondet s m => StateT s m a -> (s -> m a)
% < local x = \s -> fmap fst (runStateT x s)

% We want to prove that our implementation of local state with the |StateT| monad
% is the initial instance of state and nondeterminism.


% < etals :: MStateNondet s m => a -> StateT s m a
% < etals x = StateT $ \s -> return (x, s)

% < muls :: MStateNondet s m => StateT s m (StateT s m a) -> StateT s m a
% < muls mx = StateT $ \s -> runStateT mx s >>= \(x, s') -> runStateT x s' 

% \todo{not sure about |s'|}

% < etast :: MStateNondet s m => a -> (s -> m a)
% < etast x = \s -> return x

% < must :: MStateNondet s m => (s -> m (s -> m a)) -> (s -> m a)
% < must mx = \s -> mx s >>= \f -> f s

% The first property to prove is preservation of the monadic return.

% \[\begin{tikzcd}
% 	{|StateT s m a|} && {|s -> m a|} \\
% 	\\
% 	& |a|
% 	\arrow["{|etals|}", from=3-2, to=1-1]
% 	\arrow["{|etast|}"', from=3-2, to=1-3]
% 	\arrow["{|local|}", from=1-1, to=1-3]
% \end{tikzcd}\]

% \fbox{|local . etals = etast|}

% <    local (etals x)
% < = {-~  definition of |etals|  -}
% <    local (StateT $ \ s -> etam (x, s))
% < = {-~  definition of |local|  -}
% <    fmap (fmap fst) (runStateT (StateT $ \ s -> etam (x, s)))
% < = {-~  |runStateT . StateT = id|  -}
% <    fmap (fmap fst) (\ s -> etam (x, s))
% < = {-~  definition of |fmap|  -}
% <    \ s -> fmap fst (etam (x, s))
% < = {-~  definition of |fmap|  -}
% <    \ s -> etam x
% < = {-~  definition of |must|  -}
% <    etast x

% Secondly, we want to prove that the monadic join operation is also preserved.

% \[\begin{tikzcd}
% 	{|StateT s m (StateT s m a)|} &&& {|s -> m (s -> m a)|} \\
% 	\\
% 	{|StateT s m a|} &&& {|s -> m a|}
% 	\arrow["{|local . fmap local|}", from=1-1, to=1-4]
% 	\arrow["{|fmap local . local|}"', draw=none, from=1-1, to=1-4]
% 	\arrow["{|must|}", from=1-4, to=3-4]
% 	\arrow["{|muls|}", from=1-1, to=3-1]
% 	\arrow["{|local|}", from=3-1, to=3-4]
% \end{tikzcd}\]

% \fbox{|local . muls = must . fmap local . local|}

% <    local (muls mx)
% < = {-~  definition of |muls|  -}
% <    local (StateT $ \s -> runStateT mx s >>= \(x, s') -> runStateT x s')
% < = {-~  definition of |local|  -}
% <    \s0 -> fmap fst (runStateT (StateT $ \s -> runStateT mx s >>= \(x, s') -> runStateT x s') s0)
% < = {-~  |runStateT . StateT = id|  -}
% <    \s0 -> fmap fst (\s -> runStateT mx s >>= \(x, s') -> runStateT x s') s0)
% < = {-~  definition of |fmap|  -}
% <    \s0 -> (\s -> fst (runStateT mx s >>= \(x, s') -> runStateT x s')) s0)
% < = {-~  $\beta$-reduction  -}
% <    \s0 -> fst (runStateT mx s0 >>= \(x, s') -> runStateT x s')
% < = {-~  property: |f (m >>= g) = m >>= f . g| \todo{did I invent this?}  -}
% <    \s0 -> runStateT mx s0 >>= \(x, s') -> fst (runStateT x s')
% < = {-~  call |(x, s') = tup|  -}
% <    \s0 -> runStateT mx s0 >>= \tup -> fst (runStateT (fst tup) (snd tup))
% < = {-~  \todo{not sure + sth wrong with s0 }  -}
% <    \s0 -> runStateT mx s0 >>= \(StateT tup) -> (fmap fst (fst tup)) s0
% < = {-~  property: |fmap f x >>= g = x >>= g . f| \todo{did I invent this?}  -}
% <    \s0 -> fmap fst (runStateT mx s0) >>= \(StateT tup) -> (fmap fst tup) s0
% < = {-~  \todo{not sure}  -}
% <    \s0 -> runStateT (fmap fst (runStateT mx s0)) >>= \tup -> (fmap fst tup) s0
% < =  \s0 -> runStateT (fmap fst (runStateT mx s0)) >>= (\tup -> tup s0) . fmap fst
% < = {-~  property: |fmap f x >>= g = x >>= g . f| \todo{did I invent this?}  -}
% <    \s0 -> fmap (fmap fst) (runStateT (fmap fst (runStateT mx s0))) >>= \tup -> tup s0
% < = {-~  simplification  -}
% <    \s0 -> (\s' -> fmap fst (runStateT (fmap fst (runStateT mx s0)) s')) >>= \tup -> tup s0
% < = {-~  $\beta$-expansion  -}
% <    \s0 -> (\s -> (\s' -> fmap fst (runStateT (fmap fst (runStateT mx s)) s'))) s0 >>= \tup -> tup s0
% < = {-~  definition of |must|  -}
% <    must (\s -> (\s' -> fmap fst (runStateT (fmap fst (runStateT mx s)) s')))
% < = {-~  definition of |local|  -}
% <    must (\s -> local (fmap fst (runStateT mx s)))
% < = {-~  definition of |fmap|  -}
% <    must (fmap local (\s -> fmap fst (runStateT mx s)))
% < = {-~  definition of |local|  -}
% <    must (fmap local (local mx))

























