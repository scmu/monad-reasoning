\section{Proving |trans| Correct For Given Implementation}

The axiomatic style of reasoning has the significant advantage that a single
proof can be used to cover any implementation which is proven to follow the
required laws. However, this style of proof can be quite laborious. In some
cases, we may be content to simply prove our property for a single, given
implementation. In this section, we provide an alternative proof of the
correctness of |trans| with respect to specific implementations of local and
global state handlers, based on the observation that these handlers as well as
|trans| can be expressed as {\em folds} over the program structure.
We also showcase the power of the fold fusion technique in helping us find
handlers for local state and global state.

In order to express handlers as folds over the program structure, we first
refactor the program structure. More specifically, we'll abstract out the
``free monad'' pattern and provide the state and nondeterminism interfaces as
``algebras''.

\subsection{Composing Handlers}
\begin{code}
  data Free f a where
    Ret :: a             -> Free f a
    Op  :: f (Free f a)  -> Free f a

  data StateF a where
    Get :: (S -> a)  -> StateF a
    Put :: S -> a    -> StateF a
    deriving Functor

  data NondetF a where
    mzero :: NondetF a
    mplus :: NondetF a -> NondetF a -> NondetF a
    deriving Functor
\end{code}
The type |Free StateF a| then represents stateful computations, and similarly the
type |Free NondetF a| represents nondeterministic computations. Computations with
multiple effects can be typed with a sum type |(+)| over types of kind |* -> *|. 
\begin{code}
  data (f + g) a where
    Inl :: f a -> (f + g) a
    Inr :: g a -> (f + g) a
    deriving Functor
\end{code}
The type for programs we defined earlier, |Prog|, is then isomorphic to
|Free (StateF + NondetF)|.
The |(+)| type is morally commutative, associative, and has a zero element
(TODO: folds haven't been introduced yet!):
\begin{code}
comm :: (Functor f, Functor g) => Free (f :+: g) a -> Free (g :+: f) a
comm = fold Val alg
  where alg (Inl f) = Op (Inr f)
        alg (Inr g) = Op (Inl g)

assocl :: (Functor f, Functor g, Functor h)
       => Free (f + (g + h)) a -> Free ((f + g) + h) a
assocl = fold Val alg
  where  alg (Inl f)        = Op (Inl (Inl f))
         alg (Inr (Inl g))  = Op (Inl (Inr g))
         alg (Inr (Inr h))  = Op (Inr h)

assocr :: (Functor f, Functor g, Functor h)
       => Free ((f + g) + h) a -> Free (f + (g + h)) a
assocr = fold Val alg
  where  alg (Inl (Inl f))  = Op (Inl f)
         alg (Inl (Inr g))  = Op (Inr (Inl g))
         alg (Inr h)        = Op (Inr (Inr h))

data Nil a deriving Functor

hNil :: Free Nil a -> a
hNil (Val x) = x
-- other cases cannot occur
\end{code}

\paragraph{Notational conventions}
To avoid getting bogged down in technical details, we introduce some
simplifications. From this point onwards, we assume that the type constructor
|(+)| is implicitly commutative and associative, and has |Nil| as a zero
element; for example, we treat the type
|Free (f + g + Nil) a| as the same type as |Free (g + f) a|, without explicitly
converting between them. We also omit the |Inr| and |Inl| constructors from our
terms. So we shall write |Op (Get (Op (\x -> p x `mplus` q x)))| to mean
|Op (Inl (Get (\x -> Op (Inr (p x `mplus` q x))))) :: Free (StateF + NondetF) a|. 
But due to this notation it might also mean
|Op (Inr (Get (\x -> Op (Inl (p x `mplus` q x))))) :: Free (NondetF + StateF)
a|, or a term of a more complicated type like
|Free (NondetF + (StateF + Nil)) a|. The type of the term will disambiguate our
meaning.

A strength of this encoding is that we can not only write programs with effect sets
composed from smaller effect sets, we can also write the {\em handlers} for these
effect sets compositionally.
The type of a compositional handler indicates that it handles one effect of the
effect set of the program, yielding a new effectful program where the effect set
contains all the remaining effects. The types for compositional state and
nondeterminism handlers can be written as:
\begin{code}
hState   :: Functor f => Free (StateF   + f) a -> (S -> Free f a)
hNondet  :: Functor f => Free (NondetF  + f) a -> Free f [a]
\end{code}
This is a bit reminiscent of a ``linked list'' of effects. Like a linked list, a
``nil'' element is needed to terminate the list; this is provided to us by the
|Nil| type.

\begin{code}
hLocal :: Free (StateF + (NondetF + Nil)) a
hLocal = fmap (hNil . hNondet) . hState  
\end{code}
Later on, we shall prove that this forms a valid implementation of local state
semantics. TODO

Global state semantics can be implemented by simply inverting the order of the
handlers.
\begin{code}
hGlobal :: Free (StateF + (NondetF +Nil)) a
hGlobal = 
\end{code}

From this point onwards, we will omit some technical details where confusion is
unlikely to arise. In particular, we will omit the |Op|, |Inl| and |Inr|
constructors from our programs. For example, when we should write
|Op (Inl (Get (\x -> Op (Inr (p x `mplus` q x)))))| (an instance of the type
|Free (StateF + NondetF) a|), we shall instead write
|Get (\x -> p x `mplus` q x)|, and by this actually mean an element of the type
|Free (StateF + NondetF) a| instead of the type |StateF (NondetF a)|.
Moreover, in our notation the same term is also an instance of
|Free (NondetF + StateF) a|, and of |Free| 

\subsection{Fold and Fold Fusion}
Rather than defining our handlers directly by writing a general recursive
function, we will write them as folds, a type of structural recursion.
\begin{code}
  fold :: Functor f => (a -> r) -> (f r -> r) -> Free f r -> r
  fold gen alg (Ret x) = gen x
  fold gen alg (Op op) = alg (fmap (fold gen al) op)
\end{code}
This more principled approach gives us more leverage when reasoning about our
programs, as certain laws hold for programs defined through fusion.
In particular, we are interested in the {\em fold fusion} law:
\begin{align*}
  |h . fold gen alg| & = |fold gen' alg'| \\
                     & \Uparrow \\
  |h . gen|          & = |gen'| \\
  |h . alg|          & = |alg' . fmap h|
\end{align*}
Informally, this law states that a post-processing step (|h|) following a fold
can, if certain conditions are met, be {\em fused} into the fold.

\begin{code}
hS :: Functor f => Free (StateF :+: f) a -> (S -> Free f (a,s))
hS = fold gen alg
  where  gen x                 = \s -> Val (x,s)
         alg (Inl (Get k  ) )  = \s -> k s s
         alg (Inl (Put t k) )  = \_ -> k t
         alg (Inr p         )  = \s -> Op (fmap ($s) p)
  
hND :: Functor f => Free (NondetF :+: f) a -> Free f [a]
hND = fold gen alg
  where  gen x                    = Val [x]
         alg (Inl Fail         )  = Val []
         alg (Inl (Branch p q) )  = (++) <$> p <*> q
         alg (Inr op           )  = Op op
\end{code}

In local state semantics, nondeterminism dominates state. Our direct
implementation will handle state first, which yields a nondeterministic
computation; this computation is subsequently handled by a straightforward
nondeterminism handler.
