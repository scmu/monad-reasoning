%if False
\begin{code}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

import Background
import Control.Monad.State.Lazy

\end{code}
%endif
\section{Combination}
\label{sec:combination}

%-------------------------------------------------------------------------------
\subsection{Modeling Multiple States with State}
\label{sec:state}


%----------------------------------------------------------------
%if False
\begin{code}

-- StateT s ~> Free (State s)
newtype SS m a f = SS { unSS :: (m a, [Free (StateF (SS m a f) :+: f) a]) }

runnd :: MNondet m => Free (NondetF :+: f) a -> Free (State (SS m a f) :+: f) a
runnd = undefined

hState' :: Functor f => Free (StateF s :+: f) a -> StateT s (Free f) a-- (s -> Free f (a, s))
hState' = undefined
\end{code}
%endif