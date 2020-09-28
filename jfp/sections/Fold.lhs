\section{Proving the $\mathit{put}_{\text{R}}$ Transformation Correct For a Given Implementation}
Before we tackle the general proof of correctness of the |putR| transformation
correct, we dip our toes into something a bit more straightforward: showing that
the transformation is correct for specific implementations of global and local
state. This lets us use a somewhat more concrete setting to introduce some
infrastructure needed for the more general proof, as well as demonstrate a case
study of a fold fusion proof (TODO: citation), an elegant and powerful technique
that is interesting in its own right.

In the previous sections we have been mixing syntax and semantics,
which we avoid in this section by defining the program syntax as a free monad
(TODO: citation).
This way we avoid the need for a type-level distinction between programs
with local-state semantics and programs with global-state semantics.
\begin{code}
data Free f a where
  Ret :: a             -> Free f a
  Op  :: f (Free f a)  -> Free f a

instance Functor f => Functor (Free f) where
  fmap f (Ret x) = Ret (f x)
  fmap f (Op  o) = Op (fmap (fmap f) o)

instance Functor f => Monad (Free f) where
  return  = pure
  Ret x >>= g = g x
  Op op >>= g = Op (fmap (>>= g) op)
\end{code}
The state and nondeterminism interfaces are provided as ``algebras''. These are
functors equipped with a constructor for each operation they support.
\begin{code}
  data StateF a where
    Get    :: (S -> a)  -> StateF a
    Put    :: S -> a    -> StateF a
    deriving Functor

  data NondetF a where
    mzero  :: NondetF a
    mplus  :: a -> a -> NondetF a
    deriving Functor
\end{code}
In this encoding, the type |Free StateF a| represents stateful computations, and
similarly the type |Free NondetF a| represents nondeterministic computations.
Note that in this representation, our programs are written in a
continuation-passing style. For instance, where in the previous section we would
have written |put t >> get|, we now write |Op (Put t (Op Get))|.
Computations with multiple effects can be typed with a sum type |(+)| over types
of kind |* -> *|.
\begin{code}
  data (f + g) a where
    Inl :: f a -> (f + g) a
    Inr :: g a -> (f + g) a
    deriving Functor
\end{code}
The type |Free (NondetF + StateF) a| is one way to encode programs which have
both nondeterminism and state as effects. So is |Free (StateF + NondetF) a|, or
more generally |Functor f => Free (StateF + (NondetF + f)) a| (where |f| may
introduce additional effects). 
Where in the previous section we would have written |put t >> mzero|, we now
write |Op (Inr (Put t (Op (Inl mzero)))) :: Free (NondetF + StateF) a|. We will
later introduce notation to make our syntax a bit less noisy.
The |(+)| type is morally commutative, associative, and has a zero element:
\begin{code}
comm    :: (Functor f, Functor g) => Free (f + g) a -> Free (g + f) a
assocl  :: (Functor f, Functor g, Functor h)
        => Free (f + (g + h)) a -> Free ((f + g) + h) a
assocr  :: (Functor f, Functor g, Functor h)
        => Free ((f + g) + h) a -> Free (f + (g + h)) a

data Nil a deriving Functor

hNil    :: Free Nil a -> a
hNil (Ret x) = x
-- other cases cannot occur
\end{code}
This zero element is an empty ``effect set'': a program of type |Free Nil a|
represents a program that computes an |a| without relying on any effects (this
type is commutative with just the type |a|).

With the |Free|-based encoding we can not only write programs
with effect sets composed from smaller effect sets, we can also write the {\em
handlers} for these effect sets compositionally.
For state and nondeterminism, we respectively write the following types for
their ``compositional'' handlers:
\begin{code}
hState   :: Functor f => Free (StateF   + f) a -> (S -> Free f (a,S))
hNondet  :: Functor f => Free (NondetF  + f) a -> Free f (Bag a)
\end{code}
Here the |Bag| type represents a multiset data structure. We give a simple
example implementation:
\begin{code}
  newtype Bag a = Bag [a] deriving Functor

  instance Semigroup (Bag a)  where Bag l <> Bag r  = Bag (l ++ r)

  instance Monoid (Bag a)     where mempty          = Bag []

  instance Eq (Bag a)         where Bag l == Bag r  = sort l == sort r

  singleton :: a -> Bag a
  singleton x = Bag [x]

  elem :: Eq a => a -> Bag a -> Int
  elem x (Bag xs) = length (filter (==x) xs)

  bagFlatten :: Bag (Bag a) -> Bag a
  bagFlatten (Bag bags) = Bag (concat bags)
\end{code}
The type of the |hState| and |hNondet| handlers indicate that they handle one
effect of the effect set of the program, yielding a new effectful program where
the effect set contains all the remaining effects.  This is a bit reminiscent
of a ``linked list'' of effects. Like a linked list, a ``nil'' element is
needed to terminate the list; this is provided to us by the |Nil| type.

For instance, we can compose a handler |hLocal| for local state semantics out of
the ``atomic'' handlers for state and nondeterminism.
We will only be interested in the results of the computation, not the final
states, so the final step of our local state handler is to throw away the state
information (with |fmap fst|).
\begin{code}
hLocal'  :: Free (StateF + (NondetF + Nil)) a -> (S -> Bag (a,S))
hLocal'  = fmap (hNil . hNondet) . hState  
  
hLocal   :: Free (StateF + (NondetF + Nil)) a -> (S -> Bag a)
hLocal   = fmap (fmap fst) . hLocal'
\end{code}
In other words, local state semantics is the semantics where we
nondeterministically choose between different stateful computations. This
matches our intuition of local state semantics: if we can picture stateful,
nondeterministic programs as trees, then local state semantics is the
interpretation of the tree where each result of the (nondeterministic, stateful)
computation corresponds to a path from root to leaf in the tree. One can compute
each of these paths entirely independently from the other paths. 
Later on, we shall prove that this composition forms a valid
implementation of local state semantics.

Global state semantics can be implemented by simply inverting the order of the
handlers: rather than nondeterministically choosing between stateful
computations as local state does, in global state semantics we'll run a
single state through a nondeterministic computation.
Just like with the local state handler, we are not interested in the final state
of the computation, only in the results, so the final step of our handler is a
|fmap fst|.
\begin{code}
hGlobal'  :: Free (NondetF + (StateF + Nil)) a -> (S -> (Bag a,S))
hGlobal'  = fmap hNil . hState . hNondet

hGlobal   :: Free (NondetF + (StateF + Nil)) a -> (S -> Bag a)
hGlobal   = fmap fst . hGlobal'
\end{code}
We argue the correctness of |hLocal| and |hGlobal| (with respect to laws of
respectively local and global state semantics) in~\ref{sec:correctness-handlers}.

%From this point onwards, we will omit some technical details where confusion is
%unlikely to arise. In particular, we will omit the |Op|, |Inl| and |Inr|
%constructors from our programs. For example, when we should write
%|Op (Inl (Get (\x -> Op (Inr (p x `mplus` q x)))))| (an instance of the type
%|Free (StateF + NondetF) a|), we shall instead write
%|Get (\x -> p x `mplus` q x)|, and by this actually mean an element of the type
%|Free (StateF + NondetF) a| instead of the type |StateF (NondetF a)|.
%Moreover, in our notation the same term is also an instance of
%|Free (NondetF + StateF) a|, and of |Free| 

\subsection{Folds and Fold Fusion}
\label{sec:fold-fusion}
(TODO citations)
Rather than defining our handlers directly by writing a general recursive
function, we will write them as folds, a type of structural recursion.
\begin{code}
  fold :: Functor f => (a -> r) -> (f r -> r) -> Free f r -> r
  fold gen alg (Ret x)  = gen x
  fold gen alg (Op op)  = alg (fmap (fold gen alg) op)
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
Moreover, it will soon become apparent that the fold fusion law is not only
helpful in proving two known programs equivalent, but in fact it can often help
in finding a fused program given a composition of two programs. This discovered
program will then be correct by construction.

We can define the state and nondeterminism handlers as folds.
\begin{code}
hState :: Functor f => Free (StateF + f) a -> (S -> Free f (a,S))
hState = fold genState algState
  where
    genState x                 = \ s -> Ret (x,s)
    algState (Inl (Get k))     = \ s -> k s s
    algState (Inl (Put t k))   = \ _ -> k t
    algState (Inr p)           = \ s -> Op (fmap ($s) p)
  
hNondet :: Functor f => Free (NondetF + f) a -> Free f (Bag a)
hNondet = fold genNondet algNondet
  where
    genNondet x                     = Ret (singleton x)
    algNondet (Inl mzero)           = Ret mempty
    algNondet (Inl (p `mplus` q))   = (<>) <$> p <*> q
    algNondet (Inr op)              = Op op
\end{code}
With our atomic handlers defined, we have also gained complete definitions for
|hLocal| and |hGlobal|, as we know how to compose them from the atomic
handlers. 

\subsubsection{A Note on Notation}
Before moving on, we will attempt to simplify our notation a bit, as it is
already becoming apparent that it's getting cumbersome, and this will
only get worse as we start reasoning with it.  For example, to write a ``get''
operator in a program typed with |Free (NondetF + (StateF + NilF)) a| requires
us to write |Inr (Inl (Op (Get k)))|. Even worse,
although we see the types 
|Free (NondetF + (StateF + NilF)) a| and |Free (StateF + (NondetF + NilF)) a| as
morally the same, to convert a value of one of them into the other requires some
tedious type gymnastics.
For instance, if we want |hGlobal| to operate on the same
type of programs as |hLocal|, we need to perform some intermediate transformations:
\begin{code}
hGlobal' :: Free (StateF + (NondetF + Nil)) a -> (S -> (Bag a,S))
hGlobal' = fmap hNil . hState . comm . hNondet . assocr . comm
\end{code}
To avoid getting bogged down in this level of technical detail, we introduce some
simplifications. From this point onwards, we assume that the type constructor
|(+)| is {\em implicitly} commutative and associative, and has |Nil| as a zero
element; for example, we treat the type
|Free (f + g + Nil) a| as the same type as |Free (g + f) a|, without explicitly
converting between them. This includes no longer explicitly using the |hNil|
handler. We also omit the |Inr| and |Inl| constructors from our
terms when we feel it hurts legibility. So we shall write |Op (Get (Op (\x -> p
x `mplus` q x)))| to mean
|Op (Inl (Get (\x -> Op (Inr (p x `mplus` q x))))) :: Free (StateF + NondetF) a|. 
But due to this notation it might also mean
|Op (Inr (Get (\x -> Op (Inl (p x `mplus` q x))))) :: Free (NondetF + StateF) a|,
or a term of a more complicated type like
|Free (NondetF + (StateF + Nil)) a|. This is by design;
the type of the term will disambiguate our meaning.

The |Op| constructor is another tedious bit of notation that we have to write
over and over again every time we want to use an operator in a program. However
we feel it quickly becomes confusing if it is omitted entirely, so instead we
introduce shorthands for our operators: for instance we write |PutOp t k| to mean
|Op (Put t k)|, |p `mplusOp` q| to mean |Op (p `mplus` q)|, etc.

Finally, since we are primarily interested in stateful, nondeterministic
programs, we introduce a type alias for this type of program.
\begin{code}
type Prog a = Free (StateF + NondetF) a
\end{code}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{The $\mathit{put}_{\text{R}}$ Transformation as a Fold}
\label{sec:trans-fold}
Our goal is to prove the |putR| transformation, as introduced in
Section~\ref{sec:chaining} correct. But so far we have not even gotten around
to properly defining it!  Our representation of programs in the free monad
style allows us to express this idea directly as a fold on the type |Prog a|:
\begin{code}
trans :: Prog a -> Prog a
trans = fold Ret algTrans
  where 
    algTrans (Put t k)  = GetOp (\s -> PutOp t k `mplusOp` PutOp s mzeroOp)
    algTrans p          = Op p
\end{code}
What would it mean for |trans| to be ``correct''? Our informal problem
statement was that it should ``transform between local state and global
state semantics''. In other words, running a program |p| under local state
semantics should always produce the exact same result as running the program
|trans p| under global state semantics:
\begin{code}
hGlobal . trans = hLocal
\end{code}
If we can prove that this equation holds, then we have proven |trans| correct,
at least with respect to the specific implementations of local and global
state given in this section.
The core insight of our proof is that this equation can be proven through
fold fusion: |trans| itself is defined as a fold; |hLocal| is not defined as a
single fold, but we can fuse the local state handler into a single fold.
\begin{code}
hGlobal . fold Ret algTrans = fold genLocal algLocal
\end{code}
In other words, we wish to show that local state semantics can be obtained by
fusing a global state ``postprocessing step'' into the |trans| fold.
Proving this equation then becomes as simple as proving the corresponding fusion
conditions:
\begin{code}
hGlobal . Ret                = genLocal 
hGlobal . algTrans           = algLocal . fmap hGlobal
\end{code}

\subsection{Fusing the Local State Handler}
Our first step then is to find implementations for |genLocal| and |algLocal|,
which we do by using fold fusion on |hLocal|.
Recall the (unfolded) definition of |hLocal|:
\begin{code}
hLocal :: Free (StateF + (NondetF + Nil)) a -> (S -> Bag a)
hLocal = fmap (fmap fst) . fmap (hNil . hNondet) . hState  
\end{code}
We apply the simplifications described earlier (and the functor law
|fmap f . fmap g = fmap (f . g)|) to rewrite as:
\begin{code}
hLocal  :: Prog a -> (S -> Bag a)
hLocal  = fmap (fmap fst) . fmap hNondet . hState  
        = fmap (fmap fst . hNondet) . fold genState algState  
\end{code}
We also abbreviate the postprocessing step:
\begin{code}
post = fmap fst . hNondet
\end{code}
Then our fold fusion problem statement becomes
\begin{align*}
  |fmap post . fold genState algState| & = |fold genLocal algLocal| \\
                     & \Uparrow \\
  |fmap post . genState|          & = |genLocal| \\
  |fmap post . algState|          & = |algLocal . fmap (fmap post)|
\end{align*}
We follow this trail to discover definitions for |genLocal| and |algLocal|.
Finding the definition of |genLocal| is merely a matter of unfolding definitions.
\begin{code}
genLocal = fmap post . genState
=== {- unfold |post| -}
genLocal = fmap (fmap fst . hNondet) . genState
=== {- unfold |hNondet|, |genState| -}
genLocal = fmap (fmap fst . fold genNondet algNondet) . (\x s -> Ret (x,s))  
=== {- unfold |(.)|, |fmap|, |fold| -}
genLocal = \x s -> fmap fst (genNondet (Ret (x,s)))  
=== {- unfold |genNondet|, |fmap fst| -}
genLocal = \x _ -> singleton x
\end{code}
Finding |algLocal| is a bit more work. We would like to transform the equation
|fmap (fmap fst . hNondet) . algState = algLocal . fmap (fmap (fmap fst .
hNondet))| into an equation of the form |algLocal m = ?|. We'll do this by
``pattern matching'' on |m|, that is, we will look for a matching right hand
side for each of the following equations.
\begin{code}
algLocal (Put t k)      = ?
algLocal (Get k)        = ?
algLocal mzero          = ?
algLocal (p `mplus` q)  = ?
\end{code}
We begin by applying both sides of the equation to an arbitrary argument, and
then proceed by case analysis on that argument.
\begin{code}
fmap post . algState = algLocal . fmap (fmap post)
=== {- apply both sides to |m|, unfold |(.)| -}
fmap post (algState m) = algLocal (fmap (fmap post) m)
\end{code}
First, we analyze the case |m = Put t k|. The general pattern of this case will
repeat in all other cases: first we unfold definitions, which yields an
application of |algLocal| to a term that is too specific, so we look for a way to
generalize the equation.
\begin{code}
fmap post (algState (Put t k)) = algLocal (fmap (fmap post) (Put t k))
=== {- unfold |algState|, |fmap| -}
fmap post (\ _ -> k t) = algLocal (Put t (fmap post k))
=== {- unfold |fmap| -}
post . (\ _ -> k t) = algLocal (Put t (post . k))
=== {- definition of |(.)| -}
\ _ -> (post . k) t = algLocal (Put t (post . k))
=== {- generalize |post . k| as |k'| -}
\ _ -> k' t = algLocal (Put t k')
\end{code}
Initially the argument to |algLocal|, |Put t (post . k)|, is too
specific to cover all cases, so we massage the other side of the equation until
|post . k| occurs there too, so we can generalize both sides. The cases |m =
Get k| and |m = p `mplus` q| proceed quite similarly.
\begin{code}
fmap post (algState (Get k)) = algLocal (fmap (fmap post) (Get k))
=== {- definition of |algState|, |fmap| -}
fmap post (\ s -> k s s) = algLocal (Get (\ s -> fmap post . k))
=== {- definition of |(.)|, |fmap| -}
\ s -> (post . k s) s = algLocal (Get (\ s -> post . k s))
=== {- $\eta$-expansion on LHS, $\alpha$-renaming on RHS -}
\ s -> ((\ t -> post . k t) s) s = algLocal (Get (\ t -> post . k t))
=== {- generalize |(\t -> post . k t)| as |k'| -}
\ s -> k' s s = algLocal (Get k')
\end{code}
%fmap hNondet (\s -> Op (p s `mplus` q s)) = algLocal (fmap hNondet p `mplus` fmap hNondet q)
%\s -> hNondet (Op (p s `mplus` q s)) = algLocal (hNondet . p `mplus` hNondet . q)
%\s -> hNondet (Op (p s `mplus` q s)) = algLocal (hNondet . p `mplus` hNondet . q)
%\s -> algNondet (fmap hNondet (p s `mplus` q s)) = algLocal (hNondet . p `mplus` hNondet . q)
%\s -> algNondet (hNondet (p s) `mplus` hNondet (q s)) = algLocal (hNondet . p `mplus` hNondet . q)
\begin{code}
fmap post (algState (p `mplus` q)) = algLocal (fmap (fmap post) (p `mplus` q))
=== {- definition |algState|, |fmap| -}
fmap post (\s -> Op (p s `mplus` q s)) = algLocal (fmap post p `mplus` fmap post q)
=== {- definition of |fmap|, |post| -}
\s -> fmap fst (hNondet (Op (p s `mplus` q s))) = algLocal (post . p `mplus` post . q)
=== {- definition of |hNondet| -}
\s -> fmap fst ((hNondet . p) s <> (hNondet . q) s) = algLocal (post . p `mplus` post . q)
=== {- |map| distributes over |(<>)| (proof left as exercise), definition of |post| -}
\s -> (post . p) s <> (post . q) s = algLocal (post . p `mplus` post . q)
=== {- generalize |post . p| as |p'| and |post . q| as |q'| -}
\s -> p' s <> q' s = algLocal (p' `mplus` q')
\end{code}
%\s -> algNondet ((fmap fst . hNondet . p) s `mplus` (fmap fst . hNondet . q) s) = algLocal (fmap fst . hNondet . p `mplus` fmap fst . hNondet . q)
%=== {- generalize |fmap fst . hNondet . p| as |p'| and |fmap fst . hNondet . q| as |q'| -}
%\s -> algNondet (p' s `mplus` q' s) = algLocal (p' `mplus` q')
%=== {-  -}
%\s -> p' s <> q' s = algLocal (p' `mplus` q')
Finally, the case for |m = Fail| is trivial. We find |algLocal Fail = \ _ ->
mempty|. In summary, we deduced the following implementation for |algLocal|:
\begin{code}
algLocal (Put t k)      = \ _ -> k t
algLocal (Get k)        = \ s -> k s s
algLocal mzero          = \ _ -> mempty
algLocal (p `mplus` q)  = \ s -> p s <> q s
\end{code}

Finding our fused local state handler was the last challenge in proving |trans|
correct. All that remains to be done is to prove that the fusion conditions hold:
\begin{code}
hGlobal . Ret                = genLocal 
hGlobal . algTrans           = algLocal . fmap hGlobal
\end{code}
But this proof is entirely trivial. Since there are no unknowns, it is merely a
matter of fully evaluating (after pattern matching) both sides of the equation
and verifying that they produce the same value.

\subsection{Correctness of |hLocal| and |hGlobal|}
\label{sec:correctness-handlers}
The preceding proof rests on the assumption that |hLocal| correctly implements
local state semantics. By that we mean that |hLocal| respects the state,
nondeterminism and local state laws. To give an example, it must be the case
that, for all program contexts |C|,
|hLocal C[put s >> put t] = hLocal C[put t]|. A program context can be seen as a
``program with a hole'', writing |C[p]| means filling in the program |p| into
the context |C|. We elaborate on this concept in~\ref{sec:contextual-equivalence}.
To understand why the handler is, indeed, correct, consider that |hLocal'| is a
homomorphism (a transformation between algebraic structures that preserves
structure) in the algebra defined by the interface of |MStateNondet|. That is,
the algebra is a type constructor |m :: * -> *| along with implementations for
|return|, |(>>=)|, |get|, |put|, |mzero|, |mplus|.
One instance of this algebra is the |Prog| type:
\begin{code}
  instance MState S Prog where
    put t  = PutOp t (Ret ())
    get    = GetOp Ret

  instance MNondet Prog where
    mzero        = mzeroOp
    p `mplus` q  = p `mplusOp` q

  instance MStateNondet S Prog
\end{code}
The semantic domain of the local state handler |hNondet'| is also an instance of
this algebra.
\begin{code}
  newtype DomLocal a = DomLocal { unDomLocal :: S -> Bag (a,S) }

  instance Monad DomLocal where
    return x  = DomLocal (\ s -> singleton (x,s))
    m >>= k   = DomLocal (\ s ->
      bagFlatten $ fmap (\ (x,s) -> unDomLocal (k x) s) (unDomLocal m s))
  
  instance MState S DomLocal where
    put t  = DomLocal (\ _ -> singleton (()  , t))
    get    = DomLocal (\ s -> singleton (s   , s))

  instance MNondet DomLocal where
    mzero        = DomLocal (\ _ -> mempty)
    p `mplus` q  = DomLocal (\ s -> p s <> q s)

  instance MStateNondet S DomLocal
\end{code} % $
It is easy to verify that |hLocal'| not only maps values in |Prog| onto values
in |DomLocal|; it also maps each of the algebra operators in |Prog| onto the
corresponding operator in |DomLocal| (for example,
|DomLocal (hLocal (put s :: Prog a)) = (put s :: DomLocal a)|).
Furthermore, within the |DomLocal| implementation we can easily check that the
state laws, the nondeterminism laws, and the local state laws hold.
So because the algebra operators in |DomLocal| respect the laws, and because
|hLocal'| is a structure-preserving mapping into |DomLocal|, it follows that
|hLocal'| makes |Prog| respect these laws. And since the only difference between
|hLocal| and |hLocal'| is a post-processing step which only unifies more values,
we conclude that |hLocal| is correct.

The argument for the correctness of |hGlobal| is similar, but we need to tackle
one complication: the codomain of |hGlobal'| (the type |S -> (Bag a, S)|) is not
a monad!
This means that we cannot map the bind operator as it occurs in |Prog|
onto such an operator in the global state semantic domain, as no such operator
exists. This is not an issue for those laws that can be readily rephrased in a
continuation-passing style. For instance, we do not prove the law |put s >>
put t = put t| in our codomain (indeed it even does not make sense to
state it), but instead we prove |putD s (putD t k) = putD t k|, where
|putD t k = \ _ -> k t|.
We then argue
that, by homomorphism, the same law holds in |Prog|, and from that we can
easily show that the original formulation with |(>>=)| holds in |Prog|.
The only law that cannot be rewritten in this fashion is the
left-distributivity law~\eqref{eq:bind-mplus-dist}, but this law follows ``for
free'' from the definition of |(>>=)| for |Prog|.
